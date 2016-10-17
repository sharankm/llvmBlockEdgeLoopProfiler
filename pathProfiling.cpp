/*
 * Authors: Name(s) <email(s)>
 * 
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/CFG.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <map>
#include <vector> 
#include <algorithm>
#include <list>

using namespace llvm;

 
namespace {

   static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
    std::vector<Type*> printf_arg_types;
    printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
    FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
    Function *func = mod->getFunction("printf");
    if(!func)
      func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
    func->setCallingConv(CallingConv::C);
    return func;
  }


  struct CS201Profiling : public FunctionPass {
  	static char ID;
	LLVMContext *Context;
  	CS201Profiling() : FunctionPass(ID) {}
	std::map<std::string, GlobalVariable* > blockCounterMap;
	std::map<std::string, std::string > loopMap;
	GlobalVariable *BasicBlockPrintfFormatStr = NULL;
	GlobalVariable *BasicBlockHeaderPrintf = NULL;
	GlobalVariable *EdgeHeaderPrintf = NULL;
	GlobalVariable *EdgeValuesPrintfFormatStr = NULL;
	GlobalVariable *LoopHeaderPrintf = NULL;
	GlobalVariable *LoopValuesPrintfFormatStr = NULL;
	std::map<std::string, GlobalVariable* > edgecounterMap;
	std::map<std::string, GlobalVariable* > loopcounterMap;
	Function *printf_func = NULL;

    //----------------------------------
    bool doInitialization(Module &M) {
	Context = &M.getContext();
      const char *finalPrintString = "Block %s count is: %d\n";
      Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
      BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, 		"BasicBlockPrintfFormatStr");
	const char *BlockheaderString = "\nBASIC BLOCK PROFILING:\n";
      Constant *blkheader_format = ConstantDataArray::getString(*Context, BlockheaderString);
      BasicBlockHeaderPrintf = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(BlockheaderString)+1), true, llvm::GlobalValue::PrivateLinkage, blkheader_format, 		"BasicBlockHeaderPrintf");
	const char *EdgeheaderString = "\nEDGE PROFILING:\n";
      Constant *edgeheader_format = ConstantDataArray::getString(*Context, EdgeheaderString);
      EdgeHeaderPrintf = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(EdgeheaderString)+1), true, llvm::GlobalValue::PrivateLinkage, edgeheader_format, 		"EdgeHeaderPrintf");
	const char *edgePrintString = "Edge %s count is: %d\n";
      Constant *edge_values_format = ConstantDataArray::getString(*Context, edgePrintString);
      EdgeValuesPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(edgePrintString)+1), true, llvm::GlobalValue::PrivateLinkage, edge_values_format, 		"EdgeValuesPrintfFormatStr");
	const char *LoopheaderString = "\nLOOP PROFILING:\n";
      Constant *loopheader_format = ConstantDataArray::getString(*Context, LoopheaderString);
      LoopHeaderPrintf = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(LoopheaderString)+1), true, llvm::GlobalValue::PrivateLinkage, loopheader_format, 		"LoopHeaderPrintf");
	const char *loopPrintString = "Loop %s count is: %d\n";
      Constant *loop_values_format = ConstantDataArray::getString(*Context, loopPrintString);
      LoopValuesPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(loopPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, loop_values_format, 		"LoopValuesPrintfFormatStr");
	printf_func = printf_prototype(*Context, &M);
      errs() << "Module: " << M.getName() << "\n";
      return false;
    }

    //----------------------------------
    bool doFinalization(Module &M) {
      return false;
    }
    
    //----------------------------------
    bool runOnFunction(Function &F) override {
	errs() << "\nFunction: " << F.getName() << '\n';
	for(auto &BB: F) {
		BB.setName("b");
	}
	printDominatorSet(F);
	printLoops(F);
	for(auto &BB: F) {
	    std::string current = BB.getName();
		if(current.size() < 5){
		GlobalVariable *bbCounter = NULL;
		bbCounter = new GlobalVariable(*F.getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
		blockCounterMap[BB.getName()] = bbCounter;
		int successorCount = 0;
		for (succ_iterator sit = succ_begin(&BB), E = succ_end(&BB); sit != E; ++sit) {
			successorCount++;
		}
		for (succ_iterator sit = succ_begin(&BB), E = succ_end(&BB); sit != E; ++sit) {
			BasicBlock *successor = *sit;
			std::string next = successor->getName();
			if(next.size() < 5){
				std::string key = current + " -> " + next;
				GlobalVariable *edgeCounter = NULL;
				edgeCounter = new GlobalVariable(*BB.getParent()->getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "edgeCounter");
				edgecounterMap[key] = edgeCounter;
				BasicBlock *split = SplitEdge(&BB, successor, this);
				if(successorCount > 1){
					successor->setName(key);
					split->setName(next);
				
				} else{
					split->setName(key);
				}
			}
		}

		if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())) { 
			addPrintfHeader(BB, Context, BasicBlockHeaderPrintf, printf_func);
          		addValuesPrintf(BB, Context,  BasicBlockPrintfFormatStr, printf_func, blockCounterMap);
			addPrintfHeader(BB, Context, EdgeHeaderPrintf, printf_func);
			addValuesPrintf(BB, Context,  EdgeValuesPrintfFormatStr, printf_func, edgecounterMap);
			addPrintfHeader(BB, Context, LoopHeaderPrintf, printf_func);
			addValuesPrintf(BB, Context,  LoopValuesPrintfFormatStr, printf_func, loopcounterMap);
        	}
		}
      	}

	for(auto &BB: F) {
		runOnBasicBlock(BB);
	}
      return true;
    }

    bool runOnBasicBlock(BasicBlock &BB) {
	std::string blockName = BB.getName();
        errs() << "\nBasicBlock: " << blockName << '\n';
	IRBuilder<> IRB(BB.getFirstInsertionPt());

	if(blockName.size() < 5){
      		Value *loadAddr = IRB.CreateLoad(blockCounterMap[blockName]);
      		Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
      		IRB.CreateStore(addAddr, blockCounterMap[blockName]);
	}

	if(blockName.size() > 5){
      		Value *loadEdge = IRB.CreateLoad(edgecounterMap[blockName]);
      		Value *addEdge = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadEdge);
      		IRB.CreateStore(addEdge, edgecounterMap[blockName]);
	}

      std::string s = loopMap[blockName];
      if(s.size() > 0){
      		Value *ldAddr = IRB.CreateLoad(loopcounterMap[loopMap[blockName]]);
      		Value *aAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), ldAddr);
      		IRB.CreateStore(aAddr, loopcounterMap[loopMap[blockName]]);
      }
      for(auto &I: BB) 
      		errs() << I << "\n";
      return true;
    }

     void printDominatorSet(Function &F){
	typedef std::vector<std::string> StringVector;
	typedef std::map<std::string, StringVector> StringVectorMap;
	StringVector allNodes;
	StringVectorMap predMap;
	StringVectorMap domMap;
	for (Function::iterator BB = F.begin(), e = F.end(); BB != e; ++BB){
		allNodes.push_back(BB->getName());
		StringVector predVector;
		StringVector domVector;
		for (pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; ++PI) {
  			BasicBlock *Pred = *PI;
			predVector.push_back(Pred->getName());
		}
		if(predVector.size() == 0)
			domVector.push_back(BB->getName());		
		else
			domVector = allNodes;
		predMap[BB->getName()] = predVector;
		domMap[BB->getName()] = domVector;
      	}
	
	bool complete = false;
	while(!complete){
		for (Function::iterator BB = F.begin(), e = F.end(); BB != e; ++BB){
			StringVector predVector = predMap[BB->getName()];
			StringVector domVector = domMap[BB->getName()];
			StringVector intersection;
			if(predVector.size() != 0)
			intersection = allNodes;
			for (StringVector::iterator it = predVector.begin(); it!=predVector.end(); ++it) {
				StringVector result;
				StringVector domPred = domMap[*it];
				sort(domPred.begin(), domPred.end());
				set_intersection(domPred.begin(),domPred.end(),intersection.begin(),intersection.end(),back_inserter(result));
				intersection = result;
			}	
			intersection.push_back(BB->getName());
			domMap[BB->getName()] = intersection;	
			if (intersection == domVector)
  				complete = true;
			else
				complete = false;
		}	
	}	

	errs() << "\nDominator Sets:\n";
	for (Function::iterator BB = F.begin(), e = F.end(); BB != e; ++BB){
		StringVector predVector = predMap[BB->getName()];
		StringVector domVector  = domMap[BB->getName()];
		errs() << "Dominator Set of: " << BB->getName() << " => ";
		for (StringVector::iterator it = domVector.begin(); it!=domVector.end(); ++it) {
    			errs() << *it << " ";
		}
		errs() << "\n";
	}
      }

	void printLoops(Function &F){
	    	errs() << "\nLoops:\n";
	    for (Function::iterator BB = F.begin(), e = F.end(); BB != e; ++BB){
		BasicBlock *header;
		BasicBlock *footer;
		bool isLoop = false;
		for (succ_iterator successorIt = succ_begin(BB), E = succ_end(BB); successorIt != E; ++successorIt) {
  			BasicBlock *successor = *successorIt;
			DominatorTree *DT = new DominatorTree();
			DT->recalculate(F);
			if(DT->dominates(successor, BB)){
				header = successor;
				footer = BB;
				isLoop = true;	
			}
		}
		std::string loopString;
		if(isLoop){
			std::map<std::string, std::string> visited_blocks;
			std::map<std::string, std::string> loop_blocks;
		   	traverse(footer, header, visited_blocks, loop_blocks);
			for (std::map<std::string, std::string>::iterator it = loop_blocks.begin(), e = loop_blocks.end(); it != e; ++it){
				errs() << it->first << " ";
				loopString = loopString + it->first + " ";	
			}
			errs() << "\n"; 
		GlobalVariable *loopCounter = NULL;
		loopCounter = new GlobalVariable(*BB->getParent()->getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "loopCounter");
		loopMap[BB->getName()] = loopString;
		loopcounterMap[loopString] = loopCounter;
		}
			
	    }
	    errs() << "\n"; 
	}

	void traverse(BasicBlock *footer, BasicBlock *header,  std::map<std::string, std::string> &visited_blocks, std::map<std::string, std::string> &loop_blocks){
		std::string footerString = footer->getName();
		if(footer->getName() == header->getName()){
			loop_blocks[footerString] = footerString;
		}
		int visited = visited_blocks.count(footerString);
		if(visited != 1 && (footer->getName() != header->getName())){
			visited_blocks[footerString] = footerString;
			bool hasPred = false;
			for (pred_iterator predIt = pred_begin(footer), E = pred_end(footer); predIt != E; ++predIt) {
				BasicBlock *pred = *predIt;
				traverse(pred, header, visited_blocks, loop_blocks);
				hasPred = true;
			}
			if(hasPred){
				loop_blocks[footerString] = footerString;
			}
	
		}

	}


	void addValuesPrintf(BasicBlock& BB, LLVMContext *Context, GlobalVariable *var, Function *printf_func, std::map<std::string, GlobalVariable* > counterMap) {
      		IRBuilder<> builder(BB.getTerminator());
      		Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
      		Constant* indices[] = {zero, zero};
      		Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
		for (std::map<std::string, GlobalVariable* >::iterator it = counterMap.begin(), e = counterMap.end(); it != e; ++it){
			Value *bbc1 = builder.CreateGlobalStringPtr(it->first);			
			Value *bbc2 = builder.CreateLoad(it->second);
      			CallInst *call = builder.CreateCall3(printf_func, var_ref, bbc1, bbc2);
      			call->setTailCall(false);
		} 
 
    	}

	void addPrintfHeader(BasicBlock& BB, LLVMContext *Context, GlobalVariable *var, Function *printf_func) {
      		IRBuilder<> builder(BB.getTerminator());
		Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
		Constant* indices[] = {zero, zero};
		Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
 		CallInst *call = builder.CreateCall(printf_func, var_ref);
      		call->setTailCall(false);
    	}

  };
}

char CS201Profiling::ID = 0;
static RegisterPass<CS201Profiling> X("pathProfiling", "CS201Profiling Pass", false, false);

