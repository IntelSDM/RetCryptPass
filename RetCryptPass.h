#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct RetCryptPass : llvm::PassInfoMixin<RetCryptPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunRetCrypt(llvm::Module& m);

extern llvm::cl::opt<bool> RetCryptEnable;