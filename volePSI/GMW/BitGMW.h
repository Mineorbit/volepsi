#pragma once
#include <vector>
#include "cryptoTools/Circuit/BetaCircuit.h"
#include "cryptoTools/Circuit/Gate.h"
#include <tuple>

namespace osuCrypto
{
    class BitGMW
    {
        public:
        oc::BitVector a;
        oc::BitVector b;
        oc::BitVector c;
        oc::BitVector wireShares;
        int useBeaverCounter;
        long rounds;
        int andsTotal = 0;

        int maxAnds = 0;
        int maxXors = 0;
        int party;
        span<oc::BetaGate> mGates;
        oc::PRNG gmwprng;
        std::vector<oc::BetaGate*> xors;
        std::vector<oc::BetaGate*> ands;
        oc::BetaCircuit* mCircuit;
        void setup(int my_party,oc::BetaCircuit* circuit,oc::Socket* chl)
        {
            mCircuit = circuit;
            gmwprng = oc::PRNG(oc::toBlock(123));
            party = my_party;
            useBeaverCounter = 0;
            // TODO: Insert number of ANDS in circuit
            rounds = circuit->mLevelCounts.size();
            maxAnds = 0;
            maxXors = 0;
            wireShares = oc::BitVector(circuit->mWireCount);
            mGates = circuit->mGates;
            for(int round = 0; round < rounds;round++)
            {
                andsTotal += circuit->mLevelAndCounts[round];
                int xors = circuit->mLevelCounts[round] - circuit->mLevelAndCounts[round];
                maxAnds = std::max((int)maxAnds,(int)circuit->mLevelAndCounts[round]);
                maxXors = std::max((int)maxXors,(int)xors);
            }
            xors.resize(maxXors);
            ands.resize(maxAnds);
            genBeaverTriples(party,andsTotal,chl);
        }

        // Set the input bits of the i th Input to the circuit as given by input vector
        // as_share: the values in oc::BitVector are already shares
        // owner: this party owns the shares (only needed if as_shares = false)
        // if you are setting an input without a share and are not the owner, set input = nullptr, as_share = true, owner = false
        void setInput(int i,oc::BitVector input,bool as_share,bool owner = false,oc::Socket* chl = nullptr)
        {

            oc::BetaBundle b = mCircuit->mInputs[i];
            if(as_share)
            {
                    int j = 0;
                    for(oc::BetaWire wire : b.mWires)
                    {
                        wireShares[wire] = input[j];
                        j++;
                    }
            }else
            {
                    
            for(int i = 0;i<mCircuit->mInputs.size();i++)
            {
                oc::BitVector transmit(b.mWires.size());
                if(owner)
                {
                    oc::BitVector r = oc::BitVector(b.mWires.size());
                    r.randomize(gmwprng);
                    // Create the shares
                    int j = 0;
                    for(oc::BetaWire wire : b.mWires)
                    {
                        // TODO: set random
                        bool self = r[j];
                        bool other = self ^ input[j];
                        wireShares[wire] = self;
                        transmit[j] = other;
                        j++;
                    }
                    cp::sync_wait(chl[0].send(transmit));
                }else
                {
                    cp::sync_wait(chl[0].recv(transmit));
                    int j = 0;
                    for(oc::BetaWire wire : b.mWires)
                    {
                        wireShares[wire] = transmit[j];
                        j++;
                    }
                }
            }
            }
        }

        std::vector<oc::BitVector> run(oc::Socket* chl)
        {
            std::vector<oc::BetaWire> outWireNumbers(std::max(maxXors,maxAnds));

            for(int round = 0; round < rounds;round++)
            {

                auto gates = mGates.subspan(0, mCircuit->mLevelCounts[round]);
                mGates = mGates.subspan(mCircuit->mLevelCounts[round]);
                int level = 0;

                // Seperate gates
                int andNumLayer = 0;
                int xorNumLayer = 0;
                for (auto gate = gates.begin(); gate < gates.end(); ++gate)
                {
                    if(gate->mType == oc::GateType::And)
                    {
                        ands[andNumLayer] = gate;
                        andNumLayer++;
                    }
                    if(gate->mType == oc::GateType::Xor)
                    {
                        xors[xorNumLayer] = gate;
                        xorNumLayer++;
                    }
                    level++;
                }
                oc::BitVector left(std::max(xorNumLayer,andNumLayer));
                oc::BitVector right(std::max(xorNumLayer,andNumLayer));
                oc::BitVector outShares(std::max(xorNumLayer,andNumLayer));
                if(xorNumLayer > 0)
                {
                // Compute Gates in bundle

                for(int i = 0;i<xorNumLayer;i++)
                {
                    auto gate = xors[i];
                    left[i] = wireShares[gate->mInput[0]];
                    right[i] = wireShares[gate->mInput[1]];
                    outWireNumbers[i] = gate->mOutput;
                }
                computeXors(&left,&right,&outShares);
                for(int i = 0;i<xorNumLayer;i++)
                {
                    wireShares[outWireNumbers[i]] = outShares[i];
                }
                }
                if(andNumLayer > 0)
                {
                left.resize(andNumLayer);
                right.resize(andNumLayer);
                for(int i = 0;i<andNumLayer;i++)
                {
                    auto gate = ands[i];
                    left[i] = wireShares[gate->mInput[0]];
                    right[i] = wireShares[gate->mInput[1]];
                    outWireNumbers[i] = gate->mOutput;
                }
                computeAnds(party,&left,&right,&outShares,chl);
                for(int i = 0;i<andNumLayer;i++)
                {
                    wireShares[outWireNumbers[i]] = outShares[i];
                }
                }
            }
            std::vector<oc::BitVector> outputs;
            // get output port from circuit
            for(int i = 0;i<mCircuit->mOutputs.size();i++)
            {

                oc::BetaBundle outport = mCircuit->mOutputs[i];

                oc::BitVector output = oc::BitVector(outport.mWires.size());
                oc::BitVector transmit = oc::BitVector(outport.mWires.size());
                for(int j = 0;j<outport.mWires.size();j++)
                {
                    output[j] = wireShares[outport.mWires[j]];
                }
                // TODO this should maybe be optionally set
                /* Exchange Shares
                if(party == 1)
                {

                    cp::sync_wait(chl[0].recv(transmit));
                    output ^= transmit;
                }else{
                    cp::sync_wait(chl[0].send(output));
                }
                */
                
                outputs.push_back(output);
            }
            return outputs;
            throw "There was no output";
        }
        void genBeaverTriples(int p, long numberAnds,oc::Socket* chl)
        {
            a = oc::BitVector(numberAnds);
            b = oc::BitVector(numberAnds);
            c = oc::BitVector(numberAnds);

            auto u = oc::BitVector(numberAnds);
            auto v = oc::BitVector(numberAnds);
            for(int r = 0;r<=1;r++)
            {
            if(p == r)
            {
                a.randomize(gmwprng);
                oc::SilentOtExtReceiver receiver;

                std::vector<block> messages(numberAnds);
                receiver.configure(numberAnds, 2, 1, SilentSecType::SemiHonest);
                cp::sync_wait(receiver.genSilentBaseOts(gmwprng, *chl, true));
                cp::sync_wait(receiver.silentReceive(a,messages, gmwprng, *chl));

                for(int i = 0;i<numberAnds;i++)
                {
                    u[i] = messages[i].mData[0] & 1;
                }
            }else{

                std::vector<std::array<block, 2>> messages(numberAnds);
                oc::SilentOtExtSender sender;
                sender.configure(numberAnds, 2, 1, SilentSecType::SemiHonest);
                cp::sync_wait(sender.genSilentBaseOts(gmwprng, *chl, true));
                cp::sync_wait(sender.silentSend(messages, gmwprng, *chl));
                for(int i = 0;i<numberAnds;i++)
                {
                    b[i] = (messages[i][0].mData[0] ^ messages[i][1].mData[0]) & 1;
                    v[i] = messages[i][0].mData[0] & 1;
                }
            }
            }

            c = (a&b) ^ u ^ v;
        }
        void computeXors(oc::BitVector* a, oc::BitVector* b, oc::BitVector* o)
        {
            (*o) = (*a) ^ (*b);
        }
        void computeAnds(int p,oc::BitVector* x, oc::BitVector* y, oc::BitVector* z, oc::Socket* chl)
        {
            int numAnds = x->size();
            oc::BitVector aSelect = oc::BitVector(numAnds);
            oc::BitVector bSelect = oc::BitVector(numAnds);
            oc::BitVector cSelect = oc::BitVector(numAnds);
            for(int i = 0; i < numAnds;i++)
            {
                aSelect[i] = a[useBeaverCounter+i];
                bSelect[i] = b[useBeaverCounter+i];
                cSelect[i] = c[useBeaverCounter+i];
            }
            useBeaverCounter += numAnds;
            oc::BitVector ds = aSelect ^ (*x);
            oc::BitVector es = bSelect ^ (*y);
            oc::BitVector od(ds.size());
            oc::BitVector oe(es.size());
            if(p == 0)
            {
                cp::sync_wait(chl[0].send(ds));
                cp::sync_wait(chl[0].send(es));
            }else
            {

                cp::sync_wait(chl[0].recv(od));
                cp::sync_wait(chl[0].recv(oe));
            }
            if(p == 1)
            {
                cp::sync_wait(chl[0].send(ds));
                cp::sync_wait(chl[0].send(es));
            }else
            {

                cp::sync_wait(chl[0].recv(od));
                cp::sync_wait(chl[0].recv(oe));
            }
            if(p==1)
            {
                (*z) = ((ds ^ od)&bSelect)^((es ^ oe)&aSelect)^cSelect;
            }else
            {
                (*z) = ((ds ^ od)&bSelect)^((es ^ oe)&aSelect)^cSelect^((ds ^ od)&(es ^ oe));
            }
        }
    };
}
