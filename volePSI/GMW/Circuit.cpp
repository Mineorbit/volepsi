#include "Circuit.h"
#include <string>
#include <fstream>
namespace volePSI
{

    BetaCircuit isZeroCircuit(u64 bits,u64 numberInputs)
    {
        

        BetaCircuit cd;

            std::ifstream in;
            std::string filename = "./circuitpsi_"+std::to_string(bits)+"_"+std::to_string(numberInputs)+".bin";
	        in.open(filename, std::ios::in | std::ios::binary);
            if(in.is_open() == false)
            {
            
            



        BetaBundle out(numberInputs);
        std::vector<oc::BetaBundle> inputs;
        for(int i = 0;i<numberInputs;i++)
        {
            inputs.push_back(BetaBundle(bits));
            cd.addInputBundle(inputs[i]);
        }
        
        cd.addOutputBundle(out);
        for(int x = 0;x<numberInputs;x++)
        {
        BetaBundle a = inputs[x];

        u64 step = 1;

        for (u64 i = 0; i < bits; ++i)
            cd.addInvert(a[i]);

        while (step < bits)
        {
            //std::cout << "\n step " << step << std::endl;
            for (u64 i = 0; i + step < bits; i += step * 2)
            {
                //cd.addPrint("a[" + ts(i)+ "] &= a[" +ts(i + step) + "]\n");

                //std::cout << "a[" << i << "] &= a[" << (i + step) << "]" << std::endl;
                cd.addGate(a.mWires[i], a.mWires[i + step], oc::GateType::And, a.mWires[i]);
            }

            step *= 2;
        }
        a.mWires.resize(1);
        cd.mOutputs[0][x] = a.mWires[0];
        }
        
        cd.levelByAndDepth(BetaCircuit::LevelizeType::Reorder);


                in.close();
	            std::ofstream outstream;
	            outstream.open(filename, std::ios::out | std::ios::trunc | std::ios::binary);
                cd.writeBin(outstream);
                outstream.close();
                std::cout << "Circuit written to disk\n";


        }else{
                std::cout << "Reading circuit from disk\n";
                cd.readBin(in);
                in.close();
        }
        return cd;
    }

    void isZeroCircuit_Test()
    {
        u64 n = 128, tt = 100;
        auto cir = isZeroCircuit(n,1);

        {
            oc::BitVector bv(n), out(1);
            cir.evaluate({ &bv, 1 }, { &out,1 }, false);

            if (out[0] != 1)
                throw RTE_LOC;
        }

        oc::PRNG prng(oc::ZeroBlock);

        for (u64 i = 0; i < tt; ++i)
        {
            oc::BitVector bv(n), out(1);
            bv.randomize(prng);
            if (bv.hammingWeight() == 0)
                continue;

            cir.evaluate({ &bv, 1 }, { &out,1 }, false);

            if (out[0] != 0)
                throw RTE_LOC;
        }


    }
}
