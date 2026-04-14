#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"

#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

using namespace llvm;

namespace {

class AssumePointerParamsPass : public PassInfoMixin<AssumePointerParamsPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &) {

    LLVMContext &Ctx = M.getContext();

    // declare: void __VERIFIER_assume(i1)
    FunctionCallee Assume =
        M.getOrInsertFunction(
            "__VERIFIER_assume",
            FunctionType::get(Type::getVoidTy(Ctx),
                              {Type::getInt1Ty(Ctx)},
                              false));

    for (Function &F : M) {

      if (F.isDeclaration())
        continue;

      BasicBlock &Entry = F.getEntryBlock();
      IRBuilder<> Builder(&*Entry.getFirstInsertionPt());

      for (Argument &Arg : F.args()) {

        if (!Arg.getType()->isPointerTy())
          continue;

        // create null pointer (works with opaque pointers)
        Value *NullPtr = ConstantPointerNull::get(
            cast<PointerType>(Arg.getType()));

        // p > null
        Value *Cmp = Builder.CreateICmp(CmpInst::Predicate::ICMP_SGT, &Arg, NullPtr);

        // __VERIFIER_assume(p != null)
        Builder.CreateCall(Assume, {Cmp});
      }
    }

    return PreservedAnalyses::none();
  }
};

} // namespace

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {
      LLVM_PLUGIN_API_VERSION,
      "AssumePointerParamsPass",
      LLVM_VERSION_STRING,
      [](PassBuilder &PB) {

        PB.registerPipelineParsingCallback(
            [](StringRef Name,
               ModulePassManager &MPM,
               ArrayRef<PassBuilder::PipelineElement>) {

              if (Name == "assume-pointer-params") {
                MPM.addPass(AssumePointerParamsPass());
                return true;
              }

              return false;
            });
      }};
}
