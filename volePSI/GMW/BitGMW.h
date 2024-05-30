#pragma once
#include <vector>
#include "cryptoTools/Circuit/BetaCircuit.h"
#include "cryptoTools/Circuit/Gate.h"
#include "coproto/coproto.h"
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

        int maxGates = 0;
        int party;
        span<oc::BetaGate> mGates;
        oc::PRNG gmwprng;
        std::vector<oc::BetaGate*> gatesOfType;
        
        std::vector<oc::BetaWire> outWireNumbers;
        oc::BetaCircuit* mCircuit;
        void setup(int my_party,oc::BetaCircuit* circuit,oc::Socket* chl)
        {
            mCircuit = circuit;
            gmwprng = oc::PRNG(oc::toBlock(123));
            party = my_party;
            useBeaverCounter = 0;
            // TODO: Insert number of ANDS in circuit
            rounds = circuit->mLevelCounts.size();
            wireShares = oc::BitVector(circuit->mWireCount);
            mGates = circuit->mGates;
            int count = 0;
            for(int round = 0; round < rounds;round++)
            {
                auto gates = mGates.subspan(count,mCircuit->mLevelCounts[round]);
                count += mCircuit->mLevelCounts[round];
                int andCount = (int)circuit->mLevelAndCounts[round];
                for (auto gate = gates.begin(); gate < gates.end(); ++gate)
                {
                    
                    if(gate->mType == oc::GateType::Nor || gate->mType == oc::GateType::nb_And)
                    {
                        andCount++;
                    }
                }
                andsTotal += andCount;
                maxGates = std::max((int)maxGates,(int)gates.size());
            }
            gatesOfType.resize(maxGates);
            outWireNumbers.resize(maxGates);
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
                    coproto::sync_wait(chl[0].send(transmit));
                }else
                {
                    coproto::sync_wait(chl[0].recv(transmit));
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
        // Similar to above: owner of output receives the actual output
        oc::BitVector getOutput(int i,bool as_share,bool owner,oc::Socket* chl)
        {
            oc::BetaBundle outport = mCircuit->mOutputs[i];

            oc::BitVector output = oc::BitVector(outport.mWires.size());
            for(int j = 0;j<outport.mWires.size();j++)
            {
                output[j] = wireShares[outport.mWires[j]];
            }
            if(as_share)
            {
                return output;
            }else
            {
                oc::BitVector transmit = oc::BitVector(outport.mWires.size());
                if(owner)
                {
                    coproto::sync_wait(chl[0].recv(transmit));
                    return output^transmit;
                }else{
                    transmit = output;
                    coproto::sync_wait(chl[0].send(transmit));
                    return output;
                }
            }
        }

        void run(oc::Socket* chl)
        {

            for(int round = 0; round < rounds;round++)
            {

                auto gates = mGates.subspan(0, mCircuit->mLevelCounts[round]);
                mGates = mGates.subspan(mCircuit->mLevelCounts[round]);

                // Seperate gates
                auto supportedGateTypes = {oc::GateType::Xor,oc::GateType::And,oc::GateType::nb_And,oc::GateType::Nor};
                for(auto gateType : supportedGateTypes)
                {
                        
                    int gatesOfTypeCount = 0;
                    for (auto gate = gates.begin(); gate < gates.end(); ++gate)
                    {
                   
                        if(gate->mType == gateType)
                        {
                            gatesOfType[gatesOfTypeCount] = gate;
                            gatesOfTypeCount++;
                        }
                    }
                    
                if(gatesOfTypeCount > 0)
                {
                    oc::BitVector left(gatesOfTypeCount);
                    oc::BitVector right(gatesOfTypeCount);
                    oc::BitVector outShares(gatesOfTypeCount);
                    // Compute Gates in bundle

                    for(int i = 0;i<gatesOfTypeCount;i++)
                    {
                        auto gate = gatesOfType[i];
                        left[i] = wireShares[gate->mInput[0]];
                        right[i] = wireShares[gate->mInput[1]];
                        outWireNumbers[i] = gate->mOutput;
                    }
                    switch (gateType)
                    {
                    case oc::GateType::Xor:
                        computeXors(&left,&right,&outShares);
                        break;
                    case oc::GateType::And:
                        computeAnds(party,&left,&right,&outShares,chl);
                        break;
                    case oc::GateType::nb_And:
                        computenbAnds(party,&left,&right,&outShares,chl);
                        break;
                    case oc::GateType::Nor:
                        computeNors(party,&left,&right,&outShares,chl);
                        break;
                    
                    default:
                        throw("ERROR!");
                        break;
                    }
                    for(int i = 0;i<gatesOfTypeCount;i++)
                    {
                        wireShares[outWireNumbers[i]] = outShares[i];
                    }
                }


                }
                }
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
                coproto::sync_wait(receiver.genSilentBaseOts(gmwprng, *chl, true));
                coproto::sync_wait(receiver.silentReceive(a,messages, gmwprng, *chl));

                for(int i = 0;i<numberAnds;i++)
                {
                    u[i] = messages[i].mData[0] & 1;
                }
            }else{

                std::vector<std::array<block, 2>> messages(numberAnds);
                oc::SilentOtExtSender sender;
                sender.configure(numberAnds, 2, 1, SilentSecType::SemiHonest);
                coproto::sync_wait(sender.genSilentBaseOts(gmwprng, *chl, true));
                coproto::sync_wait(sender.silentSend(messages, gmwprng, *chl));
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

        void computeNors(int p,oc::BitVector* x, oc::BitVector* y, oc::BitVector* z, oc::Socket* chl)
        {
            oc::BitVector negx = ~(*x);
            oc::BitVector negy = ~(*y);
            computeAnds(p,&negx,&negy,z,chl);
        }


        void computenbAnds(int p,oc::BitVector* x, oc::BitVector* y, oc::BitVector* z, oc::Socket* chl)
        {
            oc::BitVector negy = ~(*y);
            computeAnds(p,x,&negy,z,chl);
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
                coproto::sync_wait(chl[0].send(ds));
                coproto::sync_wait(chl[0].send(es));
            }else
            {

                coproto::sync_wait(chl[0].recv(od));
                coproto::sync_wait(chl[0].recv(oe));
            }
            if(p == 1)
            {
                coproto::sync_wait(chl[0].send(ds));
                coproto::sync_wait(chl[0].send(es));
            }else
            {

                coproto::sync_wait(chl[0].recv(od));
                coproto::sync_wait(chl[0].recv(oe));
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
