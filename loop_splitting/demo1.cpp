#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <string.h>
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Dominators.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include <cstdlib>
#include <iostream>
#include <string>
using namespace llvm;
static cl::opt<unsigned>N("loop-partitions", cl::ZeroOrMore, cl::Hidden,cl::desc("Number of partitions"));
namespace
{
	//function pass implementation since function pass is used for this assignment
	struct demo1 : public FunctionPass
	{
		static char ID;
		//specification of function pass id
		demo1() : FunctionPass(ID) {}
		//uses analysis information from the following passes
		void getAnalysisUsage(AnalysisUsage &AU) const 			//uses the analysis information of LoopInfoWrapperPass
		{
  			AU.addRequired<LoopInfoWrapperPass>();
  			AU.addRequiredTransitive<DominatorTreeWrapperPass>();
		}


		bool runOnFunction(Function &F) override 
		{
			if (N==0)
				N=3;
			//some important declarations
			DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
				LoopInfo &Ls = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();		
				LoopInfo *LI=&Ls;
				int bb=0;
				int counter=0;
				SmallVector<Loop *,8> list;
				//DominatorTree DT(F);
	  		for (Loop *TopLevelLoop : *LI)
	    			for (Loop *S : depth_first(TopLevelLoop))
	    				 // We only handle inner-most loops.
	      				if (S->empty())	
	      					list.push_back(S);
	      		for(auto L:list)			
	      		{
	      		//iterates over the innermost loops	
	      		counter++;			//used for vmap functionality
	      		bb=0;				//used to count basicblocks in loop
	      		int lb,ub;			//lower bound and upper bound identifier for the loops
			for (BasicBlock *B : L->getBlocks()) 		//iterates over every block
				{
					bb++;
					int fflag=0;
					//used to deal with both ssa and non ssa form 
	       				 for (Instruction &I: *B) 		//iterates over each instruction
	       				 {
	       				 	//returns the lower bound of a loop in lb
	     					if (bb==1 && (strcmp("phi",I.getOpcodeName())==0))
	       					{
	       						if (llvm::ConstantInt* CI = dyn_cast<llvm::ConstantInt>(I.getOperand(0)))
	       					
							{
								if (CI->getBitWidth() <= 32) //retrieves the value of the for loop counter
								{
									fflag=1;
	   								lb = CI->getSExtValue();
	  							}
							}
						}   
						//returns the upper bound of the loop
						if (bb==1 && (strcmp("icmp",I.getOpcodeName())==0))
	       					{
	       						if (llvm::ConstantInt* CI = dyn_cast<llvm::ConstantInt>(I.getOperand(1)))
	       					
							{
								if (CI->getBitWidth() <= 32) //retrieves the value of the for loop counter
								{
	   								ub = CI->getSExtValue();
	  							}
							}
						}
					}
					//incase the IR is not in SSA form
					if (fflag==0 && bb==1)
					{
						for (BasicBlock *Pred : predecessors(B)) 
						{
						  	for (Instruction &I:*Pred)
								if(strcmp(I.getOpcodeName(),"store")==0)
								{
			       					if (llvm::ConstantInt* CI = dyn_cast<llvm::ConstantInt>(I.getOperand(0)))
			       					
									{
							//retrieves the value of the for loop counter
										if (CI->getBitWidth() <= 32) 
										{
			   								lb = CI->getSExtValue();
			  							}
									}									
								}
						}
					}
				
				}
				//runs for the number of times cloning is required for the loop
				for (unsigned int i = 0; i <N-1 ; i += 1)
				{
	      			//initializations necessary for the cloneLoopWithPreheader	
	      				ValueToValueMapTy VMap;
                		        const Twine NameSuffix;
                        		SmallVector<BasicBlock *,64> Blocks;
                        	//temporary basicblocks created so that the information is not lost
                        	 						
					BasicBlock* BB = L->getLoopPreheader()->getSinglePredecessor();
					if (BB==NULL)
					errs()<<"hhhhhhhhhhhhhhhhhhhh";
					BasicBlock* cc = L->getLoopPreheader();
					BasicBlock* ExitBlock = L->getExitBlock();

					Loop * R=cloneLoopWithPreheader(L->getLoopPreheader(),L->getLoopPreheader(),L,VMap,Twine(counter),LI,&DT,Blocks);					
					VMap[ExitBlock]=cc;
					remapInstructionsInBlocks(Blocks,VMap);
					if(BB!=NULL)
					BB->getTerminator()->replaceUsesOfWith(L->getLoopPreheader(),R->getLoopPreheader());
				//iterates over the basic blocks 	
					int block_no=0;
				//updates the new cloned loop's indexes(upper bound and lower bound)	
					for(BasicBlock *M:R->getBlocks())
					{
						block_no++;
						int flafs=0;
						for (Instruction &K:*M)
						{
							
							if (block_no==1 && (strcmp("icmp",K.getOpcodeName())==0))
							{
								Value *newvalue = ConstantInt::get((&K)->getOperand(1)->getType(),lb+(i+1)*(ub-lb)/N); 
								K.setOperand(1,newvalue);
							}	
							if (block_no==1 && (strcmp("phi",K.getOpcodeName())==0))
							{
								Value *newvalue = ConstantInt::get((&K)->getOperand(0)->getType(),lb+i*(ub-lb)/N); 
								K.setOperand(0,newvalue);
								
								flafs=1;
							}							
							if (flafs==0 && block_no==1)
							{
								BasicBlock *Pred_last;
								for (BasicBlock *Pred : predecessors(M)) 
								{
									Pred_last =Pred;
								}
								for (Instruction &K:*Pred_last)
								if (block_no==1 && (strcmp("store",K.getOpcodeName())==0))
								{
									Value *newvalue = ConstantInt::get((&K)->getOperand(0)->getType(),lb+i*(ub-lb)/N); 
									K.setOperand(0,newvalue);
								}								
							}
						}						
					}						
				}
				//updates the original loop index
				int block_no=0;
					for(BasicBlock *M:L->getBlocks())
					{
						block_no++;
						int flafs=0;
						for (Instruction &K:*M)
						{
							
							if (block_no==1 && (strcmp("icmp",K.getOpcodeName())==0))
							{
								Value *newvalue = ConstantInt::get((&K)->getOperand(1)->getType(),ub); 
								K.setOperand(1,newvalue);
								
							}
							if (block_no==1 && (strcmp("phi",K.getOpcodeName())==0))
							{
								Value *newvalue = ConstantInt::get((&K)->getOperand(0)->getType(),lb+(N-1)*(ub-lb)/N); 
								K.setOperand(0,newvalue);
								
								flafs=1;
							}							
							if (flafs==0 && block_no==1)
							{
								BasicBlock *Pred_last;
								for (BasicBlock *Pred : predecessors(M)) 
								{
									Pred_last =Pred;
								}
								for (Instruction &K:*Pred_last)
								if (block_no==1 && (strcmp("store",K.getOpcodeName())==0))
								{
									Value *newvalue = ConstantInt::get((&K)->getOperand(0)->getType(),lb+(N-1)*(ub-lb)/N); 
									K.setOperand(0,newvalue);
									
							
								}								
							}
						}						
					}				
				}		
			return false;
		}
	};
}
//registering the pass
char demo1::ID = 'a';
static RegisterPass<demo1> X("loop-splitting", "loop-splitting Pass");
