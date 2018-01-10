#include "llvm/Pass.h"						//required headers
#include "llvm/IR/Function.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include <string.h>
#include <cstdlib>
#include <iostream>
using namespace llvm;
namespace{
	struct ArithmeticIntensity : public FunctionPass 			//function pass is used for the assignment
	{
		static char ID;
		ArithmeticIntensity() : FunctionPass(ID) {}
		void getAnalysisUsage(AnalysisUsage &AU) const 			//uses the analysis information of LoopInfoWrapperPass
		{
  			AU.addRequired<LoopInfoWrapperPass>();
		}
		int loopNo = 0;							//loop counter to mention it in results
		int flops=0;							//flops counter for each function
		int a=0;							//bytes counter for each function
		void countAI(Loop *L)						//recursive function to evaluate nested loops
		{

			loopNo++;
			int undef_flag=0;					//flag which is set 1 if trip count is undeterminable
			int bb=0;						//just used for easily getting the for.cond block
			int x=0;						//stores trip count value
			int lflops=0,lbytes=0;					//individual loop flop and byte counters 
			for (BasicBlock *B : L->getBlocks()) 		//iterates over every block
			{
				bb++;

       				 for (Instruction &I: *B) 		//iterates over each instruction
       				 {
     				
     					if (bb==1 && (strcmp("icmp",I.getOpcodeName())==0))
       					{
	       						if (llvm::ConstantInt* CI = dyn_cast<llvm::ConstantInt>(I.getOperand(1)))
       					
						{
							if (CI->getBitWidth() <= 32) //retrieves the value of the for loop counter
							{
   								x = CI->getSExtValue();
  							}
						}
						else
						{
							undef_flag=1;
						}
					}
					//checking for flops opcodes
					if((strcmp(I.getOpcodeName(),"fmul")==0) ||(strcmp(I.getOpcodeName(),"fadd")==0) ||(strcmp(I.getOpcodeName(),"fsub")==0) ||(strcmp(I.getOpcodeName(),"fdiv")==0)||(strcmp(I.getOpcodeName(),"frem")==0) )
						lflops=lflops+1;
				//checking for bytes opcodes		
					if ((strcmp(I.getOpcodeName(),"store")==0))
					{
						//retrieves size of the operand reuired for bytes
	  						unsigned y=I.getOperand(0)->getType()->getPrimitiveSizeInBits();
					//bits to byte conversion
							lbytes +=(y/8); 
							if( I.getOperand(0)->getType()->isPtrOrPtrVectorTy())
							{
								lbytes +=8;
							}			
					}
					if ((strcmp(I.getOpcodeName(),"load")==0))
					{
					
	  						unsigned y=I.getType()->getPrimitiveSizeInBits();
						
							lbytes +=(y/8); 
							if( I.getType()->isPtrOrPtrVectorTy())
							{
								lbytes +=8;
							}			
					}	
					if ((strcmp(I.getOpcodeName(),"phi")==0))
					{
					//multiplied by 2 assuming 1 load and 1 store corresponding to phi		
	  						unsigned y=I.getType()->getPrimitiveSizeInBits();
				
							lbytes +=(y*2/8); 
							if( I.getType()->isPtrOrPtrVectorTy())
							{
								lbytes +=8;
							}			
					}
			  	}
			}
			//print required results
       			dbgs() <<"LoopNo= "<<loopNo;
       			if (undef_flag)
       			{
       				dbgs()<<",trip-count=undef";
       				std::cout<<",flops=undef";
				std::cout<<",bytes=undef\n";
			}       			
       			else
       			{
       				flops +=lflops*(x-1);
       				a +=(lbytes)*(x-1);
       				std::cout<<",trip-count="<<x;
       				std::cout<<",flops="<<lflops*x;
				std::cout<<",bytes="<<lbytes*x<<std::endl;
			}
			for (auto *NL : *L)
				countAI(NL);
			
       		}
       		//a function pass function which supports run on every function 			
		bool runOnFunction(Function &F) override 
		{
		//use LoopInfoWrapperPass's analysis results to get all the loops
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			flops=0; 
			a=0;

		//iterates over nested loops recursively	
			for (Loop *L : LI)
				countAI(L);
			
		//iterates over each instruction	
			  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
			  {
			  	Instruction &inst = *I;
    			  				
				if((strcmp(inst.getOpcodeName(),"fmul")==0) ||(strcmp(inst.getOpcodeName(),"fadd")==0) ||(strcmp(inst.getOpcodeName(),"fsub")==0) ||(strcmp(inst.getOpcodeName(),"fdiv")==0)||(strcmp(inst.getOpcodeName(),"frem")==0) )
					flops=flops+1;
				if ((strcmp(inst.getOpcodeName(),"load")==0) )
				{
					//retrieves size of the operand reuired for bytes
	  						unsigned y=inst.getType()->getPrimitiveSizeInBits();
					//bits to byte conversion	 
							a +=(y/8);
							if( inst.getType()->isPtrOrPtrVectorTy())
							{		
									a +=8;
							}
				}
				if ((strcmp(inst.getOpcodeName(),"store")==0) )
				{

	  						unsigned y=inst.getOperand(0)->getType()->getPrimitiveSizeInBits();

							a +=(y/8);
							if( inst.getOperand(0)->getType()->isPtrOrPtrVectorTy())
							{
								a +=8;
							}
				}
				if ((strcmp(inst.getOpcodeName(),"phi")==0) )
				{

	  						unsigned y=inst.getType()->getPrimitiveSizeInBits();
				//multiplied by 2 assuming 1 load and 1 store corresponding to phi
							a +=(y*2/8);
							if( inst.getType()->isPtrOrPtrVectorTy())
							{
								a +=8;
							}
				}				  
			  }
			//print results
			  dbgs()<<"\nfuncname="<<F.getName();
			  if (a==0)
			  	std::cout<<",arithmetic-intensity=undef"<<std::endl;
			  else
			  	std::cout<<",arithmetic-intensity="<<(double)flops/a<<std::endl;
			  return false;
		}
		
	};
}
char ArithmeticIntensity::ID = 'b';
static RegisterPass<ArithmeticIntensity> X("ArithmeticIntensity", "ArithmeticIntensity-1 Pass");
