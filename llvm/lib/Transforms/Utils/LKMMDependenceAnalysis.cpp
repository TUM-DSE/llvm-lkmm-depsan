//===- LKMMDependenceAnalaysis.cpp - LKMM Deps Implementation -------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file implements two passes to determine whether data, addr and ctrl
/// dependencies were preserved according to the Linux kernel memory model.
///
/// The first pass annotates relevant dependencies in unoptimized IR and the
/// second pass verifies that the dependenices still hold in optimized IR.
///
/// Linux kernel memory model:
/// https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/tools/memory-model/Documentation/explanation.txt
///
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LKMMDependenceAnalysis.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/AttributeMask.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>
#include <format>
#include <variant>
#include <iterator>

#define DEBUG_TYPE "lkmm-dep-analyzer"

// This list is complete and will never change
#define FOR_EACH_DEP(DO) \
  DO(Intact) \
  DO(Rising) \
  DO(MayDangle) \
  DO(Dangling) \
  DO(RisingDangling) \
  DO(MayDangleDangling) \
  DO(MayRise) \
  DO(MayRiseRising) \
  DO(MayRiseMayDangle)

#define FOR_EACH_DP(DO)\
  DO(I) \
  DO(R) \
  DO(MD) \
  DO(D) \
  DO(RD) \
  DO(MDD) \
  DO(MR) \
  DO(MRR) \
  DO(MRMD)

#define FOR_RISING_DP(DO)\
  DO(R) \
  DO(RD) \
  DO(MRR) \

#define FOR_DANGLING_DP(DO)\
  DO(D) \
  DO(RD) \
  DO(MDD) \

#define FOR_MAYRISE_DP(DO)\
  DO(MR) \
  DO(MRR) \
  DO(MRMD) \

#define FOR_MAYDANGLE_DP(DO)\
  DO(MD) \
  DO(MDD) \
  DO(MRMD) \

#define MK_COUNTS(NAME) \
  static llvm::TrackingStatistic Num##NAME[3][2][2] = { \
    { \
      { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "0", "[ADDR]["#NAME"] pre-opt count -- duplicate"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "1", "[ADDR]["#NAME"] pre-opt count -- unique") \
      }, { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "2", "[ADDR]["#NAME"] post-opt count -- dublicate"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "3", "[ADDR]["#NAME"] post-opt count -- unique") \
      } \
    }, { \
      { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "4", "[DATA]["#NAME"] pre-opt count -- duplicate"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "5", "[DATA]["#NAME"] pre-opt count -- unique") \
      }, { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "6", "[DATA]["#NAME"] post-opt count -- dublicate"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "7", "[DATA]["#NAME"] post-opt count -- unique") \
      } \
    }, { \
      { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "8", "[CTRL]["#NAME"] pre-opt count -- duplicate"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "9", "[CTRL]["#NAME"] pre-opt count -- unique") \
      }, { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "10", "[CTRL]["#NAME"] post-opt count -- dublicate"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Num" #NAME "11", "[CTRL]["#NAME"] post-opt count -- unique") \
      } \
    } \
  };

FOR_EACH_DEP(MK_COUNTS)
MK_COUNTS(Combined)

#define NumI NumIntact
#define NumR NumRising
#define NumMD NumMayDangle
#define NumD NumDangling
#define NumRD NumRisingDangling
#define NumMDD NumMayDangleDangling
#define NumMR NumMayRise
#define NumMRR NumMayRiseRising
#define NumMRMD NumMayRiseMayDangle

#define MK_STATS(NAME) \
  static llvm::TrackingStatistic Stat##NAME[3][2][3]= { \
    { \
      { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "0", "[ADDR]["#NAME"] pre-opt length -- min"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "1", "[ADDR]["#NAME"] pre-opt length -- max"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "2", "[ADDR]["#NAME"] pre-opt length -- avg") \
      }, { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "3", "[ADDR]["#NAME"] post-opt length -- min"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "4", "[ADDR]["#NAME"] post-opt length -- max"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "5", "[ADDR]["#NAME"] post-opt length -- avg") \
      } \
    }, { \
      { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "6", "[DATA]["#NAME"] pre-opt length -- min"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "7", "[DATA]["#NAME"] pre-opt length -- max"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "8", "[DATA]["#NAME"] pre-opt length -- avg") \
      }, { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "9", "[DATA]["#NAME"] post-opt length -- min"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "10", "[DATA]["#NAME"] post-opt length -- max"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "11", "[DATA]["#NAME"] post-opt length -- avg") \
      } \
    }, { \
      { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "12", "[CTRL]["#NAME"] pre-opt length -- min"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "13", "[CTRL]["#NAME"] pre-opt length -- max"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "14", "[CTRL]["#NAME"] pre-opt length -- avg") \
      }, { \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "15", "[CTRL]["#NAME"] post-opt length -- min"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "16", "[CTRL]["#NAME"] post-opt length -- max"), \
        llvm::TrackingStatistic(DEBUG_TYPE, "Stat" #NAME "17", "[CTRL]["#NAME"] post-opt length -- avg") \
      } \
    } \
  };

MK_STATS(Combined)

#define MAX_SIZE_PER_BUCKET 10000
#define MAX_CHAIN_LENGTH    100
#define MAX_VISITED_LINKS   100000
#define MAX_CHAINS_PER_INST 1000
#define MAX_PREV_STORES     5
#define MAX_PHIS            3

static int OutFD[2] = {2, 2};
static size_t LinksVisited = 0;
static bool Exiting = false;

static std::string Prefix = "LKMM-Def-Out/";

namespace llvm {
// Almost the same as llvm::CloneModule, except we only clone reachable functions and used globals
static void copyComdat(GlobalObject *Dst, const GlobalObject *Src) {
  const Comdat *SC = Src->getComdat();
  if (!SC)
    return;
  Comdat *DC = Dst->getParent()->getOrInsertComdat(SC->getName());
  DC->setSelectionKind(SC->getSelectionKind());
  Dst->setComdat(DC);
}

void saveMiniModule(Function *F, const std::string &OutDir, const std::string &Suffix) {

  Module *M = F->getParent();
  assert(M->isMaterialized() && "Module must be materialized before cloning!");

  std::set<Function *> ReachableFs = getReachableFunctions(F);
  std::set<GlobalVariable *> ReachableGvs = getReachableGlobals(ReachableFs);

  auto VMap = ValueMap<const Value *, WeakTrackingVH>();

  // First off, we need to create the new module.
  std::unique_ptr<Module> New =
      std::make_unique<Module>(M->getModuleIdentifier(), M->getContext());
  New->setSourceFileName(M->getSourceFileName());
  New->setDataLayout(M->getDataLayout());
  New->setTargetTriple(M->getTargetTriple());
  New->setModuleInlineAsm(M->getModuleInlineAsm());

  // Loop over all of the global variables, making corresponding globals in the
  // new module.  Here we add them to the VMap and to the new Module.  We
  // don't worry about attributes or initializers, they will come later.
  //
  for (GlobalVariable *I : ReachableGvs) {
    GlobalVariable *NewGV = new GlobalVariable(
        *New, I->getValueType(), I->isConstant(), I->getLinkage(),
        (Constant *)nullptr, I->getName(), (GlobalVariable *)nullptr,
        I->getThreadLocalMode(), I->getType()->getAddressSpace());
    NewGV->copyAttributesFrom(I);
    VMap[I] = NewGV;
  }

  // Loop over the functions in the module, making external functions as before
  for (Function *I : ReachableFs) {
    Function *NF =
        Function::Create(cast<FunctionType>(I->getValueType()), I->getLinkage(),
                         I->getAddressSpace(), I->getName(), New.get());
    NF->copyAttributesFrom(I);
    VMap[I] = NF;
  }

  // Loop over the aliases in the module
  for (const GlobalAlias &I : M->aliases()) {
    auto *GA = GlobalAlias::create(I.getValueType(),
                                   I.getType()->getPointerAddressSpace(),
                                   I.getLinkage(), I.getName(), New.get());
    GA->copyAttributesFrom(&I);
    VMap[&I] = GA;
  }

  for (const GlobalIFunc &I : M->ifuncs()) {
    // Defer setting the resolver function until after functions are cloned.
    auto *GI =
        GlobalIFunc::create(I.getValueType(), I.getAddressSpace(),
                            I.getLinkage(), I.getName(), nullptr, New.get());
    GI->copyAttributesFrom(&I);
    VMap[&I] = GI;
  }

  // Similarly, copy over function bodies now...
  //
  for (const Function *I : ReachableFs) {
    Function *F = cast<Function>(VMap[I]);

    if (I->isDeclaration()) {
      // Copy over metadata for declarations since we're not doing it below in
      // CloneFunctionInto().
      SmallVector<std::pair<unsigned, MDNode *>, 1> MDs;
      I->getAllMetadata(MDs);
      for (auto MD : MDs)
        F->addMetadata(MD.first, *MapMetadata(MD.second, VMap));
      continue;
    }

    Function::arg_iterator DestI = F->arg_begin();
    for (const Argument &J : I->args()) {
      DestI->setName(J.getName());
      VMap[&J] = &*DestI++;
    }

    SmallVector<ReturnInst *, 8> Returns; // Ignore returns cloned.
    CloneFunctionInto(F, I, VMap, CloneFunctionChangeType::ClonedModule,
                      Returns);

    if (I->hasPersonalityFn())
      F->setPersonalityFn(MapValue(I->getPersonalityFn(), VMap));

    copyComdat(F, I);
  }

  // And aliases
  for (const GlobalAlias &I : M->aliases()) {
    // We already dealt with undefined aliases above.
    GlobalAlias *GA = cast<GlobalAlias>(VMap[&I]);
    if (const Constant *C = I.getAliasee())
      GA->setAliasee(MapValue(C, VMap));
  }

  for (const GlobalIFunc &I : M->ifuncs()) {
    GlobalIFunc *GI = cast<GlobalIFunc>(VMap[&I]);
    if (const Constant *Resolver = I.getResolver())
      GI->setResolver(MapValue(Resolver, VMap));
  }

  // And named metadata....
  for (const NamedMDNode &NMD : M->named_metadata()) {
    NamedMDNode *NewNMD = New->getOrInsertNamedMetadata(NMD.getName());
    for (const MDNode *N : NMD.operands())
      NewNMD->addOperand(MapMetadata(N, VMap));
  }

  // Now that all of the things that global variable initializer can refer to
  // have been created, loop through and copy the global variable referrers
  // over...  We also set the attributes on the global now.
  //
  for (const GlobalVariable *G : ReachableGvs) {
    GlobalVariable *GV = cast<GlobalVariable>(VMap[G]);

    SmallVector<std::pair<unsigned, MDNode *>, 1> MDs;
    G->getAllMetadata(MDs);
    for (auto MD : MDs)
      GV->addMetadata(MD.first, *MapMetadata(MD.second, VMap));

    if (G->isDeclaration())
      continue;

    if (G->hasInitializer())
      GV->setInitializer(MapValue(G->getInitializer(), VMap));

    copyComdat(GV, G);
  }

  std::error_code EC;
  auto OutPath = OutDir + "/" + F->getName().str();
  auto ec = sys::fs::create_directories(OutPath);
  if (ec) {
    errs() << "Could not create output directory: " << ec.message() << "\n";
    return;
  }
  raw_fd_ostream Out(OutPath + "/Mod.ll" + Suffix, EC, sys::fs::OF_None);
  if (EC) {
    errs() << "Could not open file: " << EC.message() << "\n";
    return;
  }

  Out << *New;
}

std::set<Function *> getReachableFunctions(Function *F) {
  std::set<Function *> Out;

  std::set<Function *> WorkSet;
  WorkSet.insert(F);
  while (!WorkSet.empty()) {
    auto It = WorkSet.begin();
    Function *CurrF = *It;
    WorkSet.erase(It);

    if (Out.find(CurrF) != Out.end())
      continue;

    Out.insert(CurrF);

    for (auto &BB : *CurrF) {
      for (auto &I : BB) {
        for (auto &Op : I.operands()) {
          if (auto *CalleeF = dyn_cast<Function>(Op.get())) {
            WorkSet.insert(CalleeF);
          }
        }
      }
    }
  }

  return Out;
}

static bool collectFromGlobal(std::set<GlobalVariable *> &Out, Constant *C, std::set<Function *> &Found) {
  if (auto GV = dyn_cast<GlobalVariable>(C)) {
    auto r = Out.insert(GV);
    // check the initializer for more globals
    if (GV->getName() == "should_skip_vma") {
      errs() << "found fn. inserted? " << r.second << " \n";
    }
    if (GV->hasInitializer() && r.second)
      collectFromGlobal(Out, GV->getInitializer(), Found);

    return r.second;
  }

  bool Changed = false;
  if (auto *CA = dyn_cast<ConstantAggregate>(C)) {
    for (Use &U : CA->operands()) {
        Changed |= collectFromGlobal(Out, dyn_cast<Constant>(U.get()), Found);
    }
  }

  if (auto *CE = dyn_cast<ConstantExpr>(C)) {
    for (Use &U : CE->operands()) {
        Changed |= collectFromGlobal(Out, dyn_cast<Constant>(U.get()), Found);
    }
  }

  if (auto *F = dyn_cast<Function>(C)) {
    Found.insert(F);
  }

  return Changed;
}

std::set<GlobalVariable *> getReachableGlobals(std::set<Function *> &Fs) {
  std::set<GlobalVariable *> Out;
  bool GsChanged = false;

  std::set<Function *> WorkFs = Fs;
  std::set<Function *> Visited;

  std::set<Function *> Found;
  while (!WorkFs.empty()) {
    GsChanged = false;
    Found.clear();
    auto F = WorkFs.begin();
    for (auto &BB : **F) {
      for (auto &I : BB) {
        for (auto &Op : I.operands()) {
          auto *Val = Op.get();
          if (auto *GV = dyn_cast<Constant>(Val)) {
            GsChanged |= collectFromGlobal(Out, GV, Found);
          }
        }
      }
    }
    auto Nh = WorkFs.extract(F);
    auto r = Visited.insert(Nh.value());

    if (!Found.empty()) {
      // check if new globals reference functions
      for (auto *NF : Found) {
        if (Visited.find(NF) != Visited.end()) continue;
        WorkFs.insert(NF);
        Fs.insert(NF);
      }
    }
  }
  return Out;
}

std::string getInstLocString(Instruction *I, bool ViaFile) {
  const DebugLoc &InstDebugLoc = I->getDebugLoc();

  if (!InstDebugLoc)
    return "value with no source code location";

  auto LiAndCol = "::" + std::to_string(InstDebugLoc.getLine()) + ":" +
                  std::to_string(InstDebugLoc.getCol());

  if (ViaFile)
    return InstDebugLoc.get()->getFilename().str() + LiAndCol;

  return (I->getFunction()->getName().str()) + LiAndCol;
}

std::string getInstLocString(const StringRef &F ,const DebugLoc &InstDebugLoc, bool ViaFile) {
  if (!InstDebugLoc)
    return "value with no source code location";

  auto LiAndCol = "::" + std::to_string(InstDebugLoc.getLine()) + ":" +
                  std::to_string(InstDebugLoc.getCol());

  if (ViaFile)
    return InstDebugLoc.get()->getFilename().str() + LiAndCol;

  return (F.str()) + LiAndCol;
}

void setupResultDir(const std::string &OutPath) {

  bool Is;
  if (auto C = sys::fs::is_directory(OutPath, Is)) {
      errs() << "Code: " << C.message() << "\n";
      errs() << "Output directory does not exist: " << OutPath << "\n";
      llvm_unreachable("Invalid output directory. Use -fsanitize-lkmm-dep-checker-outdir=<path>");
  }
  Prefix = OutPath;
  if (OutPath.back() != '/') Prefix += '/';
}

bool dbgLocEq(const std::optional<DebugLoc> &L, const std::optional<DebugLoc> &R) {
  if (!L.has_value() || !R.has_value())
    return false;

  auto LVal = L.value();
  auto RVal = R.value();

  if (!LVal || !RVal)
    return false;

  return LVal.getLine() == RVal.getLine() && LVal.getCol() == RVal.getCol() &&
         LVal.get()->getFilename() == RVal.get()->getFilename();
}

using AnySeg = std::variant<
  SegmentID<0, 1, LKMMSearchPolicy>,
  SegmentID<0, -1, LKMMSearchPolicy>,
  SegmentID<0, 0, LKMMSearchPolicy>,
  SegmentID<1, 1, LKMMSearchPolicy>,
  SegmentID<1, -1, LKMMSearchPolicy>,
  SegmentID<1, 0, LKMMSearchPolicy>,
  SegmentID<-1, 1, LKMMSearchPolicy>,
  SegmentID<-1, -1, LKMMSearchPolicy>,
  SegmentID<-1, 0, LKMMSearchPolicy>>;

template <DepType DT>
static constexpr StringRef calls() {
  if constexpr (DT == DepType::ADDR)
    return "calls_addr_dep";
  if constexpr (DT == DepType::DATA)
    return "calls_data_dep";
  if constexpr (DT == DepType::CTRL)
    return "calls_ctrl_dep";

    llvm_unreachable("Unknown dep type");
}

template <DepType DT>
static constexpr StringRef returns() {
  if constexpr (DT == DepType::ADDR)
    return "returns_addr_dep";
  if constexpr (DT == DepType::DATA)
    return "returns_data_dep";
  if constexpr (DT == DepType::CTRL)
    return "returns_ctrl_dep";

    llvm_unreachable("Unknown dep type");
}


template <DepType DT>
static constexpr StringRef takes() {
  if constexpr (DT == DepType::ADDR)
    return "takes_addr_dep";
  if constexpr (DT == DepType::DATA)
    return "takes_data_dep";
  if constexpr (DT == DepType::CTRL)
    return "takes_ctrl_dep";

    llvm_unreachable("Unknown dep type");
}

template <DepType DT>
static constexpr StringRef is() {
  if constexpr (DT == DepType::ADDR)
    return "is_addr_dep";
  if constexpr (DT == DepType::DATA)
    return "is_data_dep";
  if constexpr (DT == DepType::CTRL)
    return "is_ctrl_dep";

    llvm_unreachable("Unknown dep type");
}

template <DepType DT>
static constexpr StringRef begins() {
  if constexpr (DT == DepType::ADDR)
    return "begins_addr_dep";
  if constexpr (DT == DepType::DATA)
    return "begins_data_dep";
  if constexpr (DT == DepType::CTRL)
    return "begins_ctrl_dep";

    llvm_unreachable("Unknown dep type");
}

template <DepType DT>
static constexpr StringRef ends() {
  if constexpr (DT == DepType::ADDR)
    return "ends_addr_dep";
  if constexpr (DT == DepType::DATA)
    return "ends_data_dep";
  if constexpr (DT == DepType::CTRL)
    return "ends_ctrl_dep";

    llvm_unreachable("Unknown dep type");
}

template <DepType DT>
static constexpr StringRef deps() {
  if constexpr (DT == DepType::ADDR)
    return "Address Dependency";
  if constexpr (DT == DepType::DATA)
    return "Data Dependency";
  if constexpr (DT == DepType::CTRL)
    return "Control Dependency";

    llvm_unreachable("Unknown dep type");
}

static constexpr StringRef DepToStr(const DepType DT) {
  if (DT == DepType::ADDR)
    return "Address Dependency";
  if (DT == DepType::DATA)
    return "Data Dependency";
  if (DT == DepType::CTRL)
    return "Control Dependency";

    llvm_unreachable("Unknown dep type");
}

static bool isLKMMLoad(Instruction *I) {
  if (auto *Existing = I->getMetadata(LLVMContext::MD_annotation)) {
    auto *Tuple = cast<MDTuple>(Existing);
    for (auto &N : Tuple->operands()) {
      if (isa<MDString>(N.get()) &&
          cast<MDString>(N.get())->getString() == "lkmm_load")
        return true;
    }
  }
  if (auto *LI = dyn_cast<LoadInst>(I)) {
    MDNode *Existing = LI->getMetadata(LLVMContext::MD_lkmm_primitive);
    if (LI->isVolatile() && Existing)
      return true;
  }
  return false;
}
static bool isLKMMStore(Instruction *I) {
  if (auto *Existing = I->getMetadata(LLVMContext::MD_annotation)) {
    auto *Tuple = cast<MDTuple>(Existing);
    for (auto &N : Tuple->operands()) {
      if (isa<MDString>(N.get()) &&
          cast<MDString>(N.get())->getString() == "lkmm_store")
        return true;
    }
  }
  if (auto *SI = dyn_cast<StoreInst>(I)) {
    MDNode *Existing = SI->getMetadata(LLVMContext::MD_lkmm_primitive);
    if (SI->isVolatile() && Existing)
      return true;
  }
  return false;
}

raw_fd_ostream &chains(size_t I) {
  static raw_fd_ostream S[2] { raw_fd_ostream(OutFD[0], false, true), raw_fd_ostream(OutFD[1], false, true) } ;
  return S[I];
}

template<int B, int E, typename C>
void removeDuplicates(std::vector<SegmentID<B,E,C>> &Segments) {
  std::sort(Segments.begin(), Segments.end(), SegmentID<B,E,C>::lt);
  auto Res = std::unique(Segments.begin(), Segments.end(), SegmentID<B,E,C>::equal);
  Segments.erase(Res, Segments.end());
}

/// Represents a dependency chain link on LLVM IR level. A dep chain link consists of an IR
/// instruction and the corresponding dep chain level.
///
/// This is private to the current search, as values may have no meaning
/// after other optimisation passes
class LKMMSearchPolicy::DCLink : public DCLinkBase {
public:
  DCLink(Instruction *Val, const DCLevel Lvl, int Depth) : DCLinkBase(Val->getDebugLoc()?Val->getDebugLoc().get():nullptr, Lvl, isLKMMStore(Val), isLKMMLoad(Val), Depth), Val(Val) {}
  ~DCLink() = default;

  DCLink(const DCLink &Other) : DCLinkBase(Other.Loc, Other.Lvl, Other.IsStore, Other.IsLoad, Other.Depth), Val(Other.Val) {}

  Instruction *Val;

  bool isCall() const { return CallInst::classof(Val) && !isLKMMStore(Val) && !isLKMMLoad(Val); }
  bool isRet() const { return ReturnInst::classof(Val); }
  bool isCtrl() const { return BranchInst::classof(Val); }
  bool isBeg() const { return isLKMMLoad(Val); }
  bool isEnd() const { return isLKMMStore(Val); }
  bool isRMW() const { return isLKMMLoad(Val) && isLKMMStore(Val); }

  bool operator==(const DCLinkBase &Other) const override {
    const auto &O = static_cast<const DCLink &>(Other);
    return Val == O.Val && Lvl == O.Lvl && Depth == O.Depth;
  }
};

template<>
void DC<LKMMSearchPolicy>::print() const {
  for (const auto &L : Chain) {
    L.Val->dump();
  }
}

/// Represents a dependency chain link on source level. A dep chain link consists of a
/// source code location, the corresponding dep chain level, and the function call depth.
class LKMMAnnotateDeps::DCLink : public DCLinkBase {

public:
  //DCLink(DebugLoc &Loc, DCLevel Lvl, DCLinkType Type = DCLinkType::VALUE) : DCLinkBase(Loc, Lvl), Depth(0), Type(Type) {}
  ~DCLink() = default;

  // Convenience copy constructor
  DCLink(const LKMMSearchPolicy::DCLink &Other) : DCLinkBase(Other.Loc.value().get(), Other.Lvl, Other.isEnd(), Other.isBeg(), Other.getDepth()), F(Other.Val->getFunction()->getName()), Type(DCLinkType::VALUE) {
    if (Other.isCall()) Type = DCLinkType::CALL;
    if (Other.isRet()) Type = DCLinkType::RETURN;
    if (Other.isCtrl()) Type = DCLinkType::CONTROL;
  }

  bool isVal() const { return Type == DCLinkType::VALUE; }
  bool isCall() const { return Type == DCLinkType::CALL; }
  bool isRet() const { return Type == DCLinkType::RETURN; }
  bool isCtrl() const { return Type == DCLinkType::CONTROL; }
  bool isBeg() const { return IsLoad; }
  bool isEnd() const { return IsStore; }
  bool isRMW() const { return IsLoad && IsStore; }

  bool operator==(const DCLinkBase &Other) const override {
    const auto &O = static_cast<const DCLink &>(Other);
    if (!Loc.has_value() || !O.Loc.has_value())
      return false;
    return Loc.value()->getLine() == O.Loc.value()->getLine() && Loc.value().getCol() == O.Loc.value().getCol() && Depth == O.Depth;
  }

  // Not ok to keep pointers to functions: pro-opt context doesn't exist when verifying
  const StringRef F;
private:
  DCLinkType Type;
};

/// Adds a link to the dependency chain iff the debug location exists and is unique.
/// Returns <false> if the \p Link has no debug location
/// or the location is equal to the latest in the chain.
template<typename Context>
bool DC<Context>::addLink(const typename Context::DCLink &Link, std::optional<int> Arg) {

  // In source level chains, we only add Links with a location.
  // This can happen when declaring local variables.
  // And we do not care about allocas.
  //if constexpr (std::is_same_v<Context, LKMMSearchPolicy>) {
  //  if (!Link.Loc)
  //    return false;
  //}

  if (Chain.empty()) {
    ArgE = Arg;
    Chain.push_back(Link);
    return true;
  }

  if (Link == Chain.back())
    return false;

  ArgB = Arg;
  Chain.push_back(Link);
  return true;
}

/// Convenience specialization.
/// Adds a value to the IR level dependency chain.
template<>
bool DC<LKMMSearchPolicy>::addLink(Instruction *Val, DCLevel Lvl, std::optional<int> Arg) {
  LKMMSearchPolicy::DCLink Link(Val, Lvl, 0);
  return addLink(Link, Arg);
}

/// Inserter for ctrl dependencies.
/// Adds a link at the end of the IR level chain. (front of the vector)
template<>
bool DC<LKMMSearchPolicy>::insertLink(Instruction *Val, DCLevel Lvl, std::optional<int> Arg) {
  LKMMSearchPolicy::DCLink Link(Val, Lvl, 0);

  //if (!Link.Loc)
  //    return false;

  Chain.insert(Chain.begin(), Link);
  ArgE = Arg;
  return true;
}

// No need to check for compatibility, the segment specialization
// should ensure this.
/// Concatenates two IR level dependency chains.
/// Merging must be done before annotation, otherwise we lose access to the instructions.
template<>
DC<LKMMSearchPolicy>::DC(const DC &Beg, const DC &End, int Delta) {

  // keep in mind that the chains are in reverse order
  auto It = Chain.insert(Chain.begin(), End.Chain.begin(), End.Chain.end());
  auto Tmp = Chain.back().getDepth();
  bool AdjBeg = false;
  // Chain: [End.E, ...., End.B]
  if (Delta > 0) {
    if (Tmp != 0) {
      assert(Tmp-Delta >= 0 && "Incompatible chains for concatenation");
      // adjust depth of Beg after insertion
      AdjBeg = true;
    } else {
      // indent entire End chain right
      for (auto &I = It; I != Chain.end(); I++) {
        I->addDepth(Delta);
      }
    }
  }

  It = Chain.insert(Chain.end(), Beg.Chain.begin(), Beg.Chain.end());
  // Chain: [End.E, ...., End.B, Beg.E, ...., Beg.B]
  if (Delta < 0 || AdjBeg) {
    // We know Tmp hasn't changed
    for (auto &I = It; I != Chain.end(); I++) {
      I->addDepth(Tmp-Delta);
    }
  }

  ArgB = Beg.ArgB;
  ArgE = End.ArgE;
}

/// Convenience specialization.
/// One-way copy constructor from an IR level chain, to a source level chain.
template<>
template<>
DC<LKMMAnnotateDeps>::DC(const DC<LKMMSearchPolicy> &Other) {
  for (const auto &Link : Other.Chain) {
    if (!Link.Loc)
      continue;
    if (!Link.Loc.value())
      continue;
    auto NewLink = LKMMAnnotateDeps::DCLink(Link);
    addLink(NewLink);
  }

  // Dbg locations in macro expansions are a bit weird, they might not be unique.
  assert(Chain.size() > 0 && "Attempting to copy a chain with less than 2 links");

  ArgB = Other.ArgB;
  ArgE = Other.ArgE;
}

// All 9 combinations of chain segments.
//
// Pairs (Begin, End) with values: 0=internal, -1=caller, +1=callee.
//  0  0 -> intact                  (trivial)
// -1  0 -> rising                  (arg -> X_ONCE)
// +1  0 -> may dangle              (call -> X_ONCE)
//
//  0 -1 -> dangling                (X_ONCE -> return)
// -1 -1 -> rising & dangling       (arg -> return)
// +1 -1 -> may dangle & dangling   (call -> return)
//
//  0 +1 -> may rise                (X_ONCE -> call)
// -1 +1 -> may rise & rising       (arg -> call)
// +1 +1 -> may rise & may dangle   (call -> call)
//
// WHY:
// There are VERY limited options for combining segments, but potentially infinitely long chains.
// Each intact chain begins and ends with 0 (potentially different pairs though)
// Each +1 end must continue in a -1 begin.
// Each -1 end must continue in a +1 begin.
// A chains absolute, summed up delta at pair N must be smaller or equal to 2N
// (the fastest we can approach 0 is in steps of 2)
//
// FIXME: There is probably integer polynomial wizardry going on that could prove complexity and optimality

template<int B, int E, typename C>
void SegmentID<B, E, C>::makePretty() {
  if constexpr (std::is_same_v<C, LKMMSearchPolicy>) {
    Pretty = "";
    for (auto I = Dc.Chain.crbegin(); I != Dc.Chain.crend(); I++) {
      if (!I->Val)
        continue;
      Pretty += getInstLocString(I->Val->getFunction()->getName(), I->Loc.value(), true);
      if (I != std::prev(Dc.Chain.crend())) {
        Pretty += "\n";
      }
    }
  } else {
    // not needed (tbd)
  }
}


template<int B, int E, typename C>
void SegmentGraph::addSegment(SegmentID<B,E,C> *Seg) {
  Nodes.push_back(std::make_unique<SegmentNode>(Seg));

  if constexpr (B == 0)
    StartSet.push_back(Nodes.back().get());
}

template<int B, int E, typename C>
SegmentNode* SegmentGraph::getSegmentNode(SegmentID<B,E,C> *Seg) {
  for (auto &N : Nodes) {
    if (N->Seg == (void *)Seg)
      return N.get();
  }
  return nullptr;
}

template<int B, int M, int E, typename C>
void SegmentGraph::addEdge(SegmentID<B,M,C> *From, SegmentID<-M,E,C> *To) {
  auto FromN = getSegmentNode(From);
  auto ToN = getSegmentNode(To);

  assert(FromN && "<From> not in graph");
  assert(ToN && "<To> not in graph");

  FromN->Successors.push_back(ToN);
}

template<int FE>
const SegmentID<0,0,LKMMSearchPolicy> mkSeg(const SmallVector<SegmentNode*, 16> &Path) {

  AnySeg Res = *static_cast<SegmentID<0,FE,LKMMSearchPolicy> *>(Path.front()->Seg);

  for (auto *N = Path.begin()+1; N != Path.end(); N++) {
    if ((*N)->E == -1) { // <0, -X> -- <X, -1>
      if ((*N)->B == -1) {
        auto B = get<SegmentID<0, 1, LKMMSearchPolicy>>(Res);
        auto *E = static_cast<SegmentID<-1, -1, LKMMSearchPolicy> *>((*N)->Seg);

        Res = SegmentID<0, -1, LKMMSearchPolicy>(B, *E);
      } else {
        auto B = get<SegmentID<0, -1, LKMMSearchPolicy>>(Res);
        auto *E = static_cast<SegmentID<1, -1, LKMMSearchPolicy> *>((*N)->Seg);

        Res = SegmentID<0, -1, LKMMSearchPolicy>(B, *E);
      }
    } else if ((*N)->E == 1) { // <0, -X> -- <X, 1>
      if ((*N)->B == -1) {
        auto B = get<SegmentID<0, 1, LKMMSearchPolicy>>(Res);
        auto *E = static_cast<SegmentID<-1, 1, LKMMSearchPolicy> *>((*N)->Seg);

        Res = SegmentID<0, 1, LKMMSearchPolicy>(B, *E);
      } else {
        auto B = get<SegmentID<0, -1, LKMMSearchPolicy>>(Res);
        auto *E = static_cast<SegmentID<1, 1, LKMMSearchPolicy> *>((*N)->Seg);

        Res = SegmentID<0, 1, LKMMSearchPolicy>(B, *E);
      }
    } else { // <0, -X> -- <X, 0>
      if ((*N)->B == -1) {
        auto B = get<SegmentID<0, 1, LKMMSearchPolicy>>(Res);
        auto *E = static_cast<SegmentID<-1, 0, LKMMSearchPolicy> *>((*N)->Seg);

        Res = SegmentID<0, 0, LKMMSearchPolicy>(B, *E);
      } else {
        auto B = get<SegmentID<0, -1, LKMMSearchPolicy>>(Res);
        auto *E = static_cast<SegmentID<1, 0, LKMMSearchPolicy> *>((*N)->Seg);

        Res = SegmentID<0, 0, LKMMSearchPolicy>(B, *E);
      }
    }
  }
  return get<SegmentID<0,0,LKMMSearchPolicy>>(Res);
}


void SegmentGraph::enumeratePaths(size_t i, void (*AnnoFn)(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType Type, LKMMAnnotateDeps::DepMap *Result), DepType Type, LKMMAnnotateDeps::DepMap *Result) {
  assert(i > 1 && "Path length must be at least 2");

  for (auto *N : StartSet) {
    SmallVector<SegmentNode*, 16> Path = { };
    SmallVector<SegmentNode*, 16> WorkSet = { N };
    // We track calls, so we limit where we can return to.
    // But on an empty stack we can return to anywhere.
    SmallVector<Function *, 8> CallStack = {};

    SegmentNode *Pop = nullptr;

    while (!WorkSet.empty()) {

      auto *Curr = WorkSet.back();

      if (Curr == Pop) {
        WorkSet.pop_back();
        Path.pop_back();
        continue;
      }

      Path.push_back(Curr);
      WorkSet.pop_back();

      // If we just came to this segment by call, we put the caller on the stack
      if (Curr->B == -1) {
        if (Curr->E == 1) {
           auto *Seg = static_cast<SegmentID<-1, 1, LKMMSearchPolicy> *>(Curr->Seg);
           CallStack.push_back(Seg->getDC().Chain.back().Val->getFunction());
        } else if (Curr->E == -1){
           auto *Seg = static_cast<SegmentID<-1, -1, LKMMSearchPolicy> *>(Path.back()->Seg);
           CallStack.push_back(Seg->getDC().Chain.back().Val->getFunction());
        } else {
           auto *Seg = static_cast<SegmentID<-1, 0, LKMMSearchPolicy> *>(Path.back()->Seg);
           CallStack.push_back(Seg->getDC().Chain.back().Val->getFunction());
        }
      }

      if (Path.back()->E == 0) {
        // We reached a leaf node, annotate the path
        if (Path.front()->E == -1)
          AnnoFn(mkSeg<-1>(Path), Type, Result);
        else
          AnnoFn(mkSeg<1>(Path), Type, Result);

        goto pop;
      }

      if (Path.size() == i) goto pop;

      WorkSet.push_back(Pop);
      for (auto *S : Curr->Successors) {
        // If this segment returns, we only add successors returning to the top of the stack
        if (Curr->E == 1 && !CallStack.empty()) {
          if (Curr->B == 1) {
             auto *Seg = static_cast<SegmentID<1, 1, LKMMSearchPolicy> *>(Curr->Seg);
             if (Seg->getDC().Chain.back().Val->getFunction() == CallStack.back()) {
                WorkSet.push_back(S);
             }
          } else if (Curr->B == -1){
             auto *Seg = static_cast<SegmentID<-1, 1, LKMMSearchPolicy> *>(Path.back()->Seg);
             if (Seg->getDC().Chain.back().Val->getFunction() == CallStack.back()) {
                WorkSet.push_back(S);
             }
          } else {
            llvm_unreachable("Invalid segment type: <0, 1> should not hava a stack");
          }
        }
      }
      if (Curr->E == 1 && !CallStack.empty()) CallStack.pop_back();
      continue;

    pop:
      Path.pop_back();
    }
  }
}


// Try to find dependencies bottom-up.
template <DepType DT>
class BUCtx : public InstVisitor<BUCtx<DT>> {
public:
  constexpr static DepType Type = DT;
  CtxKind getKind() const { return Kind; }

  BUCtx(CtxKind CK)
      : Kind(CK){};

  void runSearch() {
    for (auto &BB : *F) {
      visitBasicBlock(BB);
    }
  }

  // Generic forwarder for all values.
  void visit(Value *V);

  // Helper to add branches to chain
  void handleBranch(BasicBlock *NextBB);

  // Helper for segments that begin with the current function.
  void visitArgument(Argument *A);

  // Probably not needed.
  void visitBasicBlock(BasicBlock &BB);

  // Continues search through mem.
  // Cannot be the end of chain, this is handled in visitBB (Pass 1).
  void visitStore(StoreInst &SI);

  // Potential beginning of a dep chain.
  // May end current search, always continues through mem.
  void visitLoad(LoadInst &LI);

  // Helper function for visitLoad + ctrl.
  void searchInScope(Instruction &B) = delete;

  // Helper function for visitLoad.
  void goThroughMem(LoadInst &LI);

  // Beginning of a "may dangle" segment. End of search.
  // Cannot be the end of a "may rise" segment, this is handled in visitBB (Pass 3).
  void visitCallInst(CallInst &CI);

  // Not needed, we explicitly start from the returned values in visitBB (Pass 2).
  //void visitReturnInst(ReturnInst &ReturnI);

  // Continue search through other instructions.
  void visitUnaryOperator(UnaryOperator &UO);

  void visitBinaryOperator(BinaryOperator &BinOp);

  void visitExtractElementInst(ExtractElementInst &EEI) {};

  void visitInsertElementInst(InsertElementInst &IEI) {};

  void visitShuffleVectorInst(ShuffleVectorInst &SVI) {};

  void visitExtractValueInst(ExtractValueInst &EVI) {};

  void visitInsertValueInst(InsertValueInst &IVI) {};

  // TODO: This should end the search. Pointers to local memory cannot begin chains.
  void visitAllocInst(AllocaInst &AI) {};

  // TODO:
  void visitAtomicCmpXchgInst(AtomicCmpXchgInst &ACXI) {};

  // TODO:
  void visitAtomicRMWInst(AtomicRMWInst &ARMWI) {};

  void visitGetElementPtrInst(GetElementPtrInst &GEP);

  // FIXME: is this "conditional"?
  void visitPHINode(PHINode &PN);

  void visitTruncInst(TruncInst &TI) {};

  void visitZExtInst(ZExtInst &ZI) {};

  void visitSExtInst(SExtInst &SI);

  void visitPtrToIntInst(PtrToIntInst &PTI) {};

  void visitIntToPtrInst(IntToPtrInst &ITPI) {};

  void visitBitCastInst(BitCastInst &BCI) {};

  void visitAddrSpaceCastInst(AddrSpaceCastInst &ASCI) {};

  void visitSelectInst(SelectInst &SI);

  void visitICmpInst(ICmpInst &ICI) {};

  void setF(Function *F) { this->F = F; }

protected:
  // The function the BFS is currently visiting.
  Function *F;

  // The BB the BFS is currently checking.
  BasicBlock *BB;

private:
  const CtxKind Kind;
};

template<DepType DT>
class LKMMSearchPolicy::AnnotCtx : public BUCtx<DT> {

  friend class BUCtx<DT>;
public:

  AnnotCtx(CtxKind Ctx,
      void (* AnnoFn)(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType Type, LKMMAnnotateDeps::DepMap *Result),
      LKMMAnnotateDeps *PrevResult) : BUCtx<DT>(Ctx), Result(new(llvm::LKMMAnnotateDeps::DepMap)), CurrPass(Pass::Known_End), AnnotateFn(AnnoFn), PrevResult(PrevResult) {};

  void (*AnnotateFn)(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType Type, LKMMAnnotateDeps::DepMap *Result);

  LKMMAnnotateDeps *PrevResult;

  void setNewDc(std::unique_ptr<DC> NewDC) {
    CurrDC = std::move(NewDC);
  }

  std::unique_ptr<DC> getDCPtr() {
    return std::move(CurrDC);
  }

  DC &getDc() {
    return *CurrDC;
  }

  auto getResult() { return Result; }

  void populate(DepMap<0,0> *I,
                 DepMap<-1,0> *R,
                 DepMap<1,0> *MD,
                 DepMap<0,-1> *D,
                 DepMap<-1,-1> *RD,
                 DepMap<1,-1> *MDD,
                 DepMap<0,1> *MR,
                 DepMap<-1,1> *MRR,
                 DepMap<1,1> *MRMD) {
#define ASSIGN(Dep) { this->Dep = Dep; }
    FOR_EACH_DP(ASSIGN)
#undef ASSIGN
  }

#define GET(Dep) auto *get##Dep() { return Dep; }
  FOR_EACH_DP(GET)
#undef GET

  void setMSSA(MemorySSA &MSSA) { this->MSSA = &MSSA; }
  MemorySSA &getMSSA() { return *MSSA; }

  void setPDT(PostDominatorTree &PDT) { this->PDT = &PDT; }
  PostDominatorTree &getPDT() { return *PDT; }

  // Only runs once. Annotates ALL segments ending in volatile loads and stores.
  void passOne(Function *NewF) {
    this->F = NewF;

    if constexpr (DT == DepType::CTRL)
      CurrPass = Pass::Known_Cond;
    this->runSearch();
  }

  // Runs on all functions with RetAttr "returns_X_dep".
  // May add more segments with the any attr.
  void passTwo(Function *NewF) {

    this->F = NewF;

    CurrPass = Pass::Known_Ret;

    if constexpr (DT == DepType::CTRL)
      CurrPass = Pass::Any_Call;
    this->runSearch();
  }

  // Runs on all functions with FnAttr "takes_X_dep".
  // May add more segments with the any attr.
  void passThree(Function *NewF) {

    this->F = NewF;

    CurrPass = Pass::Known_Call;

    if constexpr (DT == DepType::CTRL)
      CurrPass = Pass::Any_End;
    this->runSearch();
  }

  void completeSegWithLoad(Instruction *I);

  // Merges all segments to full dependency chains of length Depth.
  void merge(const size_t &Depth) {
    buildTransitiveClosure(Depth);

    //removeDuplicates(*Result);
    DUMP();
    // for (auto I : *Result) {
    //   I.print();
    // }
  }

  template<int B, int E>
  void makeIntactDep() {

    DepMap<B, E> *TypedMap;

    if constexpr (B == 0 && E == 0) {
      TypedMap = I;
    } else if constexpr (B == -1 && E == 0) {
      TypedMap = R;
    } else if constexpr (B == 1 && E == 0) {
      TypedMap = MD;
    } else if constexpr (B == 0 && E == -1) {
      TypedMap = D;
    } else if constexpr (B == -1 && E == -1) {
      TypedMap = RD;
    } else if constexpr (B == 1 && E == -1) {
      TypedMap = MDD;
    } else if constexpr (B == 0 && E == 1) {
      TypedMap = MR;
    } else if constexpr (B == -1 && E == 1) {
      TypedMap = MRR;
    } else if constexpr (B == 1 && E == 1) {
      TypedMap = MRMD;
    }

    if constexpr (B == -1) {
      // Attention! The beginning call instruction _calls_ F. It probably is not in F.
      auto *CallingInstr = cast<CallInst>(CurrDC->Chain.back().Val);
      auto *Caller = CallingInstr->getFunction();

      Caller->addFnAttr(Attribute::get(Caller->getContext(), calls<DT>()));
      this->F->addFnAttr(Attribute::get(this->F->getContext(), takes<DT>()));
      if (CurrDC->ArgB.value() >= 0)
        this->F->addParamAttr(CurrDC->ArgB.value(), Attribute::get(this->F->getContext(), is<DT>()));
    }

    if constexpr (B == 1) {
      // Attention! The beginning return returns to F and
      // definitely returns to it (else everything we just traversed is unreachable).

      auto *Callee = cast<ReturnInst>(CurrDC->Chain.back().Val)->getFunction();
      Callee->addRetAttr(Attribute::get(this->F->getContext(), returns<DT>()));
      // TODO: Warn about external function/intrinsic
    }

    // Endings are already known once we start the appropriate pass.
    // Only do sanity checks here.
    if constexpr (E == -1) {

      // TODO: rebase to newest llvm
      assert(this->F->getAttributes().getRetAttrs().hasAttribute(returns<DT>()) && "Function should not have been passed in Pass 2");
    }

    if constexpr (DT != DepType::CTRL && E == 1) {

      auto *Callee = cast<CallInst>(CurrDC->Chain.front().Val);
      if (Callee->getCalledFunction()) {
        assert(Callee->getCalledFunction()->getAttributes().getFnAttrs().hasAttribute(takes<DT>()) && "Function should not have been passed in Pass 3");
        if (CurrDC->ArgE.value() != -1)
          assert(Callee->getCalledFunction()->getAttributes().getParamAttrs(CurrDC->ArgE.value()).hasAttribute(is<DT>()) && "Argument should not have been passed in Pass 3");
      }
    }

    if constexpr (DT == DepType::CTRL && E == 1) {

      auto *Call = cast<CallInst>(CurrDC->Chain.front().Val);
      if (auto *Callee = Call->getCalledFunction())
        Callee->addFnAttr(Attribute::get(Callee->getContext(), takes<DT>()));
      this->F->addFnAttr(Attribute::get(this->F->getContext(), calls<DT>()));
    }

    assert(getDc().Chain.size() > 0 && "Attempting to complete a segment with less than 2 links");

    // FIXME
    auto Seg = SegmentID<B, E, LKMMSearchPolicy>(getDc());
    TypedMap->push_back(Seg);
    getDCPtr().release();
  }

  enum Pass { Known_End, Known_Ret, Known_Call, Known_Cond, Any_Call, Any_End, Match };

  Pass currPass() const { return CurrPass; }

  void DUMP() {

    chains(this->getKind()) << "*****~~~~~~~~~~" << deps<DT>() << "~~~~~~~~~~*****\n";

#define PRINT_DEPS(Dep) do { \
  chains(this->getKind()) << std::remove_reference_t<decltype(*Dep)>::value_type::Type << ": " << Dep->size() << "\n"; \
  for (auto &Seg : *Dep) { \
    Seg.makePretty(); \
    chains(this->getKind()) << Seg.Pretty << "\n\n"; \
    Num##Dep[this->Type][this->getKind()][1]++; \
  } \
} while (0);
    FOR_EACH_DP(PRINT_DEPS)
#undef PRINT_DEPS

    NumCombined[this->Type][this->getKind()][1] = Result->size();

    StatCombined[this->Type][this->getKind()][0] = [](auto *R){ if (R->size() == 0) {return 0ul;}; size_t tmp = -1; for (const auto &Seg : *R) { tmp = std::min(tmp, Seg.getDC().Chain.size()); } return tmp; }(Result);
    StatCombined[this->Type][this->getKind()][1] = [](auto *R){ if (R->size() == 0) {return 0ul;}; size_t tmp = 0; for (const auto &Seg : *R) { tmp = std::max(tmp, Seg.getDC().Chain.size()); } return tmp; }(Result);
    StatCombined[this->Type][this->getKind()][2] = [](auto *R){ if (R->size() == 0) {return 0ul;}; size_t tmp = 0; for (const auto &Seg : *R) { tmp += Seg.getDC().Chain.size(); } return tmp/R->size(); }(Result);
    chains(this->getKind()) << "Combined:\n";
    for (const auto &Seg : *Result) {
      chains(this->getKind()) << Seg.Pretty << "\n\n";
    }
  }

  void dump() {
    errs() << "Combined:\n";
    for (const auto &Seg : *Result) {
      errs() << Seg.Pretty << "\n\n";
    }
  }

private:
  // Currently tracked DC.
  std::unique_ptr<DC> CurrDC;

  llvm::LKMMAnnotateDeps::DepMap *Result;

  // Current annotation pass
  Pass CurrPass;

  // Pass 1, can never be extended
  IntactDeps_t *I = nullptr;
  RisingDeps_t *R = nullptr;
  MayDangleDeps_t *MD = nullptr;

  // Pass 2 & 3, can be extended by any segment with an even delta (0 or 2)
  DanglingDeps_t *D = nullptr;
  RisingDanglingDeps_t *RD = nullptr;
  MayDangleDanglingDeps_t *MDD = nullptr;
  MayRiseDeps_t *MR = nullptr;
  MayRiseRisingDeps_t *MRR = nullptr;
  MayRiseMayDangleDeps_t *MRMD = nullptr;

  MemorySSA *MSSA = nullptr;
  PostDominatorTree *PDT = nullptr;

  void buildTransitiveClosure(const size_t Depth);
  template<int B, int M, int E>
  std::vector<std::pair<SegmentID<B, M, LKMMSearchPolicy> *, SegmentID<-M, E, LKMMSearchPolicy> *>> match(DepMap<B, M> *Beg, DepMap<-M, E> *End);
};

/// Converts an LLVM IR level chain to a source level chain, and
/// annotates the chain in the IR.
void LKMMAnnotateDepsPass::annotateChain(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType DT, LKMMAnnotateDeps::DepMap *Result) {

    std::string Annot;
    std::string Pretty;

    llvm::SegmentID<0,0,LKMMAnnotateDeps> Ret(Seg);
    assert(!Ret.getDC().Chain.empty() && "Cannot annotate empty chain");

    Function *TopF = nullptr;
    for (auto L : Seg.getDC().Chain) {
      if (L.getDepth() == 0) {
        TopF = L.Val->getFunction();
        break;
      }
    }

    for (auto I = Ret.getDC().Chain.crbegin(); I != Ret.getDC().Chain.crend(); I++) {
      Annot += getInstLocString(I->F, I->Loc.value());
      std::string Mark = "";
      if (TopF && (TopF->getName() == I->F)) Mark = "[T]";

      Pretty += std::string(I->getDepth(), '\t') + Mark + getInstLocString(I->F, I->Loc.value());
      if (I != std::prev(Ret.getDC().Chain.crend())) {
        Annot += "--";
        Pretty += "\n";
      }
    }

    auto AHash = std::hash<std::string>{}(Annot);
    auto HashStr = std::to_string(AHash);
    Pretty = HashStr + ":\n" + Pretty;

    std::string TyB;
    std::string TyE;
    switch (DT) {
      case DepType::ADDR:
        TyB = begins<DepType::ADDR>();
        TyE = ends<DepType::ADDR>();
        break;
      case DepType::DATA:
        TyB = begins<DepType::DATA>();
        TyE = ends<DepType::DATA>();
        break;
      case DepType::CTRL:
        TyB = begins<DepType::CTRL>();
        TyE = ends<DepType::CTRL>();
        break;
    }
    {
      auto I = Seg.getDC().Chain.back();
      MDNode *Meta = MDNode::get(I.Val->getContext(), MDString::get(I.Val->getContext(), HashStr));

      if (auto *Existing = I.Val->getMetadata(TyB)) {
        if (Existing->getNumOperands() > MAX_CHAINS_PER_INST) {
          errs() << "Warning: Instruction has too many dependency chains\n";
        } else
          Meta = llvm::MDNode::concatenate(Existing, Meta);
      }
      I.Val->setMetadata(TyB, Meta);
    }
    {
      auto I = Seg.getDC().Chain.front();
      MDNode *Meta = MDNode::get(I.Val->getContext(), MDString::get(I.Val->getContext(), HashStr));

      if (auto *Existing = I.Val->getMetadata(TyE)) {
        if (Existing->getNumOperands() > MAX_CHAINS_PER_INST) {
          errs() << "Warning: Instruction has too many dependency chains\n";
        } else
          Meta = llvm::MDNode::concatenate(Existing, Meta);
      }
      I.Val->setMetadata(TyE, Meta);
    }
    if (TopF) {
      TopF->addFnAttr(Attribute::get(TopF->getContext(), "is_entry"));
    }

    Ret.setStr(Pretty, DT);
    Result->push_back(Ret);
}

/// Converts an LLVM IR level chain to a source level chain, and
/// optionally checks for annotations from the previous rounds.
void LKMMVerifyDepsPass::addChain(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType DT, LKMMAnnotateDeps::DepMap *Result) {
  std::string Annot;
  std::string Pretty;

  llvm::SegmentID<0,0,LKMMAnnotateDeps> Ret(Seg);
  assert(!Ret.getDC().Chain.empty() && "Cannot annotate empty chain");

  Function *TopF = nullptr;
  for (auto L : Seg.getDC().Chain) {
    if (L.getDepth() == 0) {
      TopF = L.Val->getFunction();
      break;
    }
  }

  for (auto I = Ret.getDC().Chain.crbegin(); I != Ret.getDC().Chain.crend(); I++) {
    Annot += getInstLocString(I->F, I->Loc.value());
    std::string Mark = "";
    if (TopF && (TopF->getName() == I->F)) Mark = "[T]";
    Pretty += std::string(I->getDepth(), '\t') + Mark + getInstLocString(I->F, I->Loc.value());
    if (I != std::prev(Ret.getDC().Chain.crend())) {
      Annot += "--";
      Pretty += "\n";
    }
  }

  /*
  for (auto I = Seg.getDC().Chain.crbegin(); I != Seg.getDC().Chain.crend(); I++) {
    MDNode *Meta = MDNode::get(I->Val->getContext(), MDString::get(I->Val->getContext(), Annot));

    if (auto *Existing = I->Val->getMetadata("addr_dep"))
      Meta = llvm::MDNode::concatenate(Existing, Meta);
    I->Val->setMetadata("addr_dep", Meta);
  }
  */
  auto AHash = std::hash<std::string>{}(Annot);
  auto HashStr = std::to_string(AHash);
  Pretty = HashStr + ":\n" + Pretty;

  Ret.setStr(Pretty, DT);
  Result->push_back(Ret);
}

template <DepType DT>
template <int B, int M, int E>
std::vector<std::pair<SegmentID<B, M, LKMMSearchPolicy> *, SegmentID<-M, E, LKMMSearchPolicy> *>> LKMMSearchPolicy::AnnotCtx<DT>::match(DepMap<B, M> *Beg, DepMap<-M, E> *End) {

  if (!Beg || !End)
    return {};

  using RetTy = std::vector<std::pair<SegmentID<B, M, LKMMSearchPolicy> *, SegmentID<-M, E, LKMMSearchPolicy> *>>;

  RetTy Ret;
  for (auto It = End->begin(); It != End->end(); It++) {
    auto Jt = Beg->begin();
    while (Jt != Beg->end() && !(Jt->isCompatible(*It))) Jt++;
    while (Jt != Beg->end() && Jt->isCompatible(*It)) {
      Ret.push_back({&(*Jt), &(*It)});
      Jt++;
    }
  }

  return Ret;
}

template<DepType DT>
void LKMMSearchPolicy::AnnotCtx<DT>::buildTransitiveClosure(const size_t Depth) {

  LKMMAnnotateDeps::DepMap *IntactDeps = Result;
  SegmentGraph G;


  // Depth 1: Trivial and always needed
  for (auto &Seg : *I) {
    AnnotateFn(Seg, DT, IntactDeps);
  }

  if (Depth == 1)
    return;

  // For all longer chain we build a graph
  // Excluding I
  for (auto &Seg : *R) G.addSegment(&Seg);
  for (auto &Seg : *MD) G.addSegment(&Seg);
  for (auto &Seg : *D) G.addSegment(&Seg);
  for (auto &Seg : *MR) G.addSegment(&Seg);
  for (auto &Seg : *RD) G.addSegment(&Seg);
  for (auto &Seg : *MDD) G.addSegment(&Seg);
  for (auto &Seg : *MRR) G.addSegment(&Seg);
  for (auto &Seg : *MRMD) G.addSegment(&Seg);

#define MATCH_R(DP) do { \
  for (auto &P : match(MR, DP)) { \
    G.addEdge(P.first, P.second); \
  } \
  for (auto &P : match(MRR, DP)) { \
    G.addEdge(P.first, P.second); \
  } \
  for (auto &P : match(MRMD, DP)) { \
    G.addEdge(P.first, P.second); \
  } \
} while(0);

#define MATCH_MD(DP) do { \
  for (auto &P : match(D, DP)) { \
    G.addEdge(P.first, P.second); \
  } \
  for (auto &P : match(RD, DP)) { \
    G.addEdge(P.first, P.second); \
  } \
  for (auto &P : match(MDD, DP)) { \
    G.addEdge(P.first, P.second); \
  } \
} while(0);

  FOR_RISING_DP(MATCH_R);
  FOR_MAYDANGLE_DP(MATCH_MD);

#undef MATCH_R
#undef MATCH_MD


  G.enumeratePaths(Depth, AnnotateFn, DT, IntactDeps);

  return;
}

template<DepType DT>
void BUCtx<DT>::handleBranch(BasicBlock *NextBB) {
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<Type> *)this;
  auto *CurrBB = Ann->getDc().Chain.back().Val->getParent();

  if (auto *BI = dyn_cast<BranchInst>(NextBB->getTerminator())) {
    if (!BI->isConditional())
      return;
    // NOTE: This is one case where we could get false positives.
    // We don't retroactively check if any path breaks the chain,
    // we just know at least one doesn't
    //
    // Example:
    //                 +---NextBB---+
    //                 |     br     | visit(inst) <----+
    //                 +------------+                  |
    //                     /    \                      |
    //            +-------+      +-------+             |
    //            | EMPTY |      | BREAK |         depends on
    //            +-------+      +-------+             |
    //                    \      /                     |
    //                 +---CurrBB---+                  |
    //                 |            | chain.back()-----+
    //                 +------------+
    //

    // [!] If there is a trivial path from one target
    // [!] to the current BB, we add the branch.

    // for (auto *Succ : BI->successors()) {
    //   if (!isPotentiallyReachable(Succ, CurrBB))
    //     continue;
    //   auto *T = Succ;
    //   while (T != CurrBB) {
    //     T = T->getUniqueSuccessor();
    //     if (!T)
    //       return;
    //   }
    //   Ann->getDc().addLink(BI, DCLevel::EMPTY);
    //   // There should be exactly one terminator for the next BB
    //   return;
    // }
    // return;


    // If CurrBB post-dominates NextBB, we add it.
    // May be optimized to selects, which we also handle.
    // If after optimization, the dominance changed, there might be a bug -- hence the link will miss
    if (Ann->getPDT().dominates(CurrBB, NextBB))
      Ann->getDc().addLink(BI, DCLevel::EMPTY);
  }
}

template<DepType DT>
void LKMMSearchPolicy::AnnotCtx<DT>::completeSegWithLoad(Instruction *I) {
  auto Curr = getDCPtr();
  auto Cpy = std::make_unique<DC>(*Curr);

  setNewDc(std::move(Cpy));
  getDc().addLink(I, DCLevel::PTR);
  if (Curr->Chain.front().isRet())
    makeIntactDep<0, -1>();
  else if (Curr->Chain.front().isCall())
    makeIntactDep<0, 1>();
  else
    makeIntactDep<0, 0>();

  setNewDc(std::move(Curr));
}

template <DepType DT>
void BUCtx<DT>::visit(Value *V) {
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;

#define CAP(dep) do { \
  if (Ann->dep->size() > MAX_SIZE_PER_BUCKET) return; \
} while(0);

  FOR_EACH_DP(CAP)
#undef CAP

  LinksVisited++;

  if (std::find_if(Ann->getDc().Chain.begin(), Ann->getDc().Chain.end(),
        [V](const LKMMSearchPolicy::DCLink &L) { return L.Val == V; }) != Ann->getDc().Chain.end()) {
    errs() << "[WARN] Not checking circular dependencies\n";
    return;
  }

  if (Ann->getDc().Chain.size() > MAX_CHAIN_LENGTH) {
    errs() << "[WARN] Chain too long, give up\n";
    return;
  }
  if (LinksVisited > MAX_VISITED_LINKS) {
    if (!Exiting)
      errs() << "[WARN] Too many visited links, give up\n";
    Exiting = true;
    return;
  }

  if (auto *I = dyn_cast<Instruction>(V)) {
    auto *NextBB = I->getParent();
    // Whatever we want to insert, it is in a different BB.
    // We need to check for branches, even for addr & data dependencies
    // because they can be optimized to selects.
    if (!Ann->getDc().Chain.empty() && NextBB != Ann->getDc().Chain.back().Val->getParent()) {
      // If the branch is marked as a loop, we ignore it.
      auto *T = NextBB->getTerminator();
      MDNode *Loop = T->getMetadata(LLVMContext::MD_loop);
      if (Loop) {
        errs() << "[WARN] Not doing loops\n";
        return;
      }
      handleBranch(NextBB);

    }

    InstVisitor<BUCtx<DT>>::visit(I);
  }
  if (auto *A = dyn_cast<Argument>(V)) {
    visitArgument(A);
  }
}

// TODO: avoid back edges
/// Start of search for addr and data dependencies.
/// Mostly the same, except when looking at stores.
template <DepType DT>
void BUCtx<DT>::visitBasicBlock(BasicBlock &BB) {
  this->BB = &BB;
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;

  if (Ann->currPass() == LKMMSearchPolicy::AnnotCtx<DT>::Pass::Known_End) {
    for (auto &I : BB) {
      Value *PtrOrVal = nullptr;

      if constexpr (DT == DepType::ADDR) {
        // Address dependencies end in a volatile load/store
        // with the ptr operand being the end of the chain.
        if (auto *SI = dyn_cast<StoreInst>(&I)) {
          if (!SI->isVolatile())
            continue;
          MDNode *Existing = SI->getMetadata(LLVMContext::MD_lkmm_primitive);
          if (!Existing)
            continue;

          PtrOrVal = SI->getPointerOperand();
        }
        if (auto *LI = dyn_cast<LoadInst>(&I)) {
          if (!LI->isVolatile())
            continue;
          MDNode *Existing = LI->getMetadata(LLVMContext::MD_lkmm_primitive);
          if (!Existing)
            continue;

          PtrOrVal = LI->getPointerOperand();
        }
        if (auto *CI = dyn_cast<CallInst>(&I)) {
          if (isLKMMLoad(CI)) {
            if (CI->isInlineAsm()) {
              if (CI->getNumOperands() < 2) {
                continue;
              }
              PtrOrVal = CI->getArgOperand(0);

            } else {
              PtrOrVal = CI->getArgOperand(0);
            }
          }
          if (isLKMMStore(CI)) {
            PtrOrVal = CI->getArgOperand(0);
          }
        }

        if (PtrOrVal) {

            auto End = std::make_unique<DC<LKMMSearchPolicy>>();
            End->addLink(&I, DCLevel::PTR);
            Ann->setNewDc(std::move(End));
            visit(PtrOrVal);
        }
      }
      if constexpr (DT == DepType::DATA) {
        // Data dependencies end in a volatile store
        // with the data operand being the end of the chain.
        if (isLKMMStore(&I)) {
          if (auto *SI = dyn_cast<StoreInst>(&I)) {
            PtrOrVal = SI->getValueOperand();
          }
          if (auto *CI = dyn_cast<CallInst>(&I)) {
            PtrOrVal = CI->getArgOperand(1);
          }
        }
        if (PtrOrVal) {

          auto Lvl = PtrOrVal->getType()->isPointerTy() ? DCLevel::PTR : DCLevel::PTE;
          auto End = std::make_unique<DC<LKMMSearchPolicy>>();
          End->addLink(&I, Lvl);
          Ann->setNewDc(std::move(End));
          visit(PtrOrVal);
        }
      }
    }
      return;
  } // !Known_End

  if (Ann->currPass() == LKMMSearchPolicy::AnnotCtx<DT>::Pass::Known_Ret) {
    // We also need to track any potential chains from return values.
    // FIXME: Aggregate returns should have an annotation per element.
    if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
      for (auto &Op : RI->operands()) {
        auto End = std::make_unique<DC<LKMMSearchPolicy>>();
        if (Op->getType()->isPointerTy())
          End->addLink(RI, DCLevel::PTR);
        else
          End->addLink(RI, DCLevel::PTE);
        Ann->setNewDc(std::move(End));
        visit(Op);
      }
    }
    return;
  } // !Known_Ret

  if (Ann->currPass() == LKMMSearchPolicy::AnnotCtx<DT>::Pass::Known_Call) {
    for (auto &I : BB) {
    // We also need to track any potential chains from call isntructions.
      if (auto *CI = dyn_cast<CallInst>(&I)) {
        // Only track calls to functions we have seen before.
        if (!CI->getCalledFunction())
          continue;
        if (!CI->getCalledFunction()->getAttributes().hasFnAttr(takes<DT>()))
          continue;

        for (auto &Arg : CI->args()) {
          auto ArgNo = CI->getArgOperandNo(&Arg);
          if (!CI->getCalledFunction()->getAttributes().hasParamAttr(ArgNo, is<DT>()))
              continue;

          auto End = std::make_unique<DC<LKMMSearchPolicy>>();
          // FIXME: this might be wrong
          if (Arg->getType()->isPointerTy())
            End->addLink(&I, DCLevel::PTR, ArgNo);
          else
            End->addLink(&I, DCLevel::PTE, ArgNo);
          Ann->setNewDc(std::move(End));
          visit(Arg);
        }
      }
    }
    return;
  } // !Known_Call

  llvm_unreachable("Unknown Annotation Pass");
}

template <>
void BUCtx<DepType::CTRL>::visitBasicBlock(BasicBlock &BB) {
  constexpr static DepType DT = DepType::CTRL;
  this->BB = &BB;
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;

  // Search is different for control dependencies.
  // First we check all conditionals, if they depend on a volatile load. (so far, so normal)
  // Then we check all volatile stores and calls that don't post-dominate the branch.
  if (Ann->currPass() == LKMMSearchPolicy::AnnotCtx<DT>::Pass::Known_Cond) {
    auto *Term = BB.getTerminator();
    if (auto *BI = dyn_cast<BranchInst>(Term)) {
      if (!BI->isConditional())
        return;

      auto End = std::make_unique<DC<LKMMSearchPolicy>>();
      End->addLink(BI, DCLevel::EMPTY);
      Ann->setNewDc(std::move(End));
      visit(BI->getCondition());
    }
  }
  if (Ann->currPass() == LKMMSearchPolicy::AnnotCtx<DT>::Pass::Any_Call) {
    for (auto &I : BB) {

      if (auto *CI = dyn_cast<CallInst>(&I)) {
        if (isLKMMStore(CI)) continue;

        auto End = std::make_unique<DC<LKMMSearchPolicy>>();
        End->addLink(CI, DCLevel::EMPTY, -1);
        Ann->setNewDc(std::move(End));
        // Add Beg immediatly
        if (!F->hasUseList())
          continue;
        for (auto *Caller : F->users()) {
          if (auto *CallingI = dyn_cast<CallInst>(Caller)) {
            if (CI == CallingI)
              continue;
            if (!CallingI->getFunction()->hasFnAttribute(calls<DT>()))
              continue;

            auto Curr = Ann->getDCPtr();
            auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

            Ann->setNewDc(std::move(Cpy));
            Ann->getDc().addLink(CallingI, DCLevel::EMPTY, -1);
            Ann->template makeIntactDep<-1, 1>();

            Ann->setNewDc(std::move(Curr));
          }
        }
      }
    }
  }
  if (Ann->currPass() == LKMMSearchPolicy::AnnotCtx<DT>::Pass::Any_End) {
    for (auto &I : BB) {

      if (isLKMMStore(&I)) {
        auto End = std::make_unique<DC<LKMMSearchPolicy>>();
        End->addLink(&I, DCLevel::EMPTY);
        Ann->setNewDc(std::move(End));
        // Add Beg immediatly
        if (!F->hasUseList())
          continue;
        for (auto *Caller : F->users()) {
          if (auto *CallingI = dyn_cast<CallInst>(Caller)) {
            if (!CallingI->getFunction()->hasFnAttribute(calls<DT>()))
              continue;

            auto Curr = Ann->getDCPtr();
            auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

            Ann->setNewDc(std::move(Cpy));
            Ann->getDc().addLink(CallingI, DCLevel::EMPTY, -1);
            Ann->template makeIntactDep<-1, 0>();

            Ann->setNewDc(std::move(Curr));
          }
        }
      }
    }
  }
}

template<>
void BUCtx<DepType::CTRL>::visitICmpInst(ICmpInst &ICI) {
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DepType::CTRL> *)this;

  Ann->getDc().addLink(&ICI, DCLevel::PTE);
  for (auto &Op : ICI.operands()) {
    auto Curr = Ann->getDCPtr();
    auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

    Ann->setNewDc(std::move(Cpy));
    visit(Op);
    Ann->setNewDc(std::move(Curr));
  }
}

template <DepType DT>
void BUCtx<DT>::visitArgument(Argument *A) {
  LKMMSearchPolicy::AnnotCtx<DT> *Ann = static_cast<LKMMSearchPolicy::AnnotCtx<DT> *>(this);

  // We found a rising segment!
  // Add a new segment for all call sites of F (likely outside of F)

  if (!F->hasUseList())
    return;

  for (auto *CallingInstr : F->users()) {

    if (auto *CI = dyn_cast<CallInst>(CallingInstr)) {
      if (CI->getFunction() == F)
        continue;

      auto Curr = Ann->getDCPtr();
      auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

      Ann->setNewDc(std::move(Cpy));
      Ann->getDc().addLink(CI, getLastNonEmptyLvl(Curr->Chain), A->getArgNo());

      if (Curr->Chain.front().isRet())
        Ann->template makeIntactDep<-1, -1>();
      else if (Curr->Chain.front().isCall())
        Ann->template makeIntactDep<-1, 1>();
      else
        Ann->template makeIntactDep<-1, 0>();

      Ann->setNewDc(std::move(Curr));
    }
  }
}


template <DepType DT>
void BUCtx<DT>::visitStore(StoreInst &SI) {
// We might end up here because we stored the linking val to mem
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;

  for (auto L = Ann->getDc().Chain.crbegin(); L != Ann->getDc().Chain.crend(); L++) {
    if (L->Lvl == DCLevel::PTE)
      break;
    if (L->Lvl == DCLevel::EMPTY)
      continue;
    return;
  }
  if(!Ann->getDc().addLink(&SI, DCLevel::PTR))
    return;

  auto *Val = SI.getValueOperand();
  visit(Val);
}

template <DepType DT>
void BUCtx<DT>::visitLoad(LoadInst &LI) {
  if (isLKMMLoad(&LI)) {
    // We found an internal beginning!
    LKMMSearchPolicy::AnnotCtx<DT> *Ann = static_cast<LKMMSearchPolicy::AnnotCtx<DT> *>(this);

    Ann->completeSegWithLoad(&LI);
  }
  goThroughMem(LI);
}

template<>
void BUCtx<DepType::CTRL>::searchInScope(Instruction &B) {

  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DepType::CTRL> *)this;
  auto *Cond = cast<BranchInst>(Ann->getDc().Chain.front().Val);

  LKMMSearchPolicy::AnnotCtx<DepType::DATA> DataAC(Ann->getKind(), Ann->AnnotateFn, Ann->PrevResult);
  DataAC.populate(Ann->I, Ann->R, Ann->MD, Ann->D, Ann->RD, Ann->MDD, Ann->MR, Ann->MRR, Ann->MRMD);
  DataAC.setF(Ann->F);

  for (auto &BB: *(Cond->getFunction())) {

    if (Cond == BB.getTerminator())
      continue;

    // bool IsAlwaysReachable = true;
    // bool IsReachableOnce = false;
    // for (auto *Succ: Cond->successors()) {
    //   bool tmp = isPotentiallyReachable(Succ, &BB);
    //   IsAlwaysReachable &= tmp;
    //   IsReachableOnce |= tmp; // false positives!
    // }

    // if (!IsReachableOnce)
    //   continue;
    if (!isPotentiallyReachable(Cond->getParent(), &BB))
      continue;

    if (Ann->getPDT().dominates(&BB, Cond->getParent()))
      continue;

    for (auto &I : BB) {
      if (isLKMMStore(&I)) {
        auto Curr = Ann->getDCPtr();
        auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

        if (auto *_ = dyn_cast<ReturnInst>(&B)) {
          DataAC.setNewDc(std::move(Cpy));
          DataAC.getDc().addLink(&B, getLastNonEmptyLvl(Curr->Chain));
          DataAC.getDc().insertLink(&I, DCLevel::PTE);
          DataAC.makeIntactDep<1, 0>();

          Ann->setNewDc(std::move(Curr));
          continue;
        }

        Ann->setNewDc(std::move(Cpy));
        Ann->getDc().addLink(&B, DCLevel::PTE);
        Ann->getDc().insertLink(&I, DCLevel::PTE);

        if (isLKMMLoad(&B))
          Ann->makeIntactDep<0, 0>();
        else if (isa<CallInst>(&B))
          Ann->makeIntactDep<-1, 0>();
        else
          llvm_unreachable("Unexpected instruction heading ctrl dependency chain");

        Ann->setNewDc(std::move(Curr));
      }
      if (auto *CI = dyn_cast<CallInst>(&I)) {

        auto *Callee = CI->getCalledFunction();
        if (!Callee)
          continue;

        auto Curr = Ann->getDCPtr();
        auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

        if (auto *_ = dyn_cast<ReturnInst>(&B)) {
          Callee->addFnAttr(takes<DepType::DATA>());

          DataAC.setNewDc(std::move(Cpy));
          DataAC.getDc().addLink(&B, getLastNonEmptyLvl(Curr->Chain));
          DataAC.getDc().insertLink(CI, DCLevel::PTE, -1);
          DataAC.makeIntactDep<1, 1>();

          Ann->setNewDc(std::move(Curr));
          continue;
        }

        Ann->setNewDc(std::move(Cpy));
        Ann->getDc().addLink(&B, DCLevel::PTE);
        Ann->getDc().insertLink(CI, DCLevel::BOTH, -1);

        if (auto *_ = dyn_cast<LoadInst>(&B))
          Ann->makeIntactDep<0, 1>();
        else if (auto *_ = dyn_cast<CallInst>(&B))
          Ann->makeIntactDep<-1, 1>();
        else
          llvm_unreachable("Unexpected instruction heading ctrl dependency chain");

        Ann->setNewDc(std::move(Curr));
      }
    }
  }

  return;
}

template <>
void BUCtx<DepType::CTRL>::visitLoad(LoadInst &LI) {
  if (!isLKMMLoad(&LI)) {
    goThroughMem(LI);
    return;
  }

  searchInScope(LI);
}

template <DepType DT>
void BUCtx<DT>::goThroughMem(LoadInst &LI) {

  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;

  Ann->getDc().addLink(&LI, DCLevel::PTE);

  if (!LI.getPointerOperand()->hasUseList())
    return;

  SmallVector<MemoryAccess *, 4> Workset;
  SmallSet<MemoryAccess *, 8> Visited;

  auto &MSSA = Ann->getMSSA();
  auto *Walker = MSSA.getWalker();
  MemoryAccess* def = Walker->getClobberingMemoryAccess(&LI);
  MemoryLocation Loc(MemoryLocation::get(&LI));

  size_t Phis = 0;

  SmallPtrSet<BasicBlock *, 2> LaterBBs;
  for (auto *BB : successors(LI.getParent()))
    LaterBBs.insert(BB);

  if (def)
    Workset.push_back(def);

  // Continue the chain at the last store (in po) that wrote to the same addr-value.
  // Notably not the same location.
  // PHI nodes fan-out the chain.
  while (!Workset.empty()) {
    auto *MA = Workset.pop_back_val();
    if (!Visited.insert(MA).second)
      continue;

    if (MSSA.isLiveOnEntryDef(MA))
      continue;

    if (auto *SD = dyn_cast<MemoryDef>(MA)) {
      auto *SI = dyn_cast_if_present<StoreInst>(SD->getMemoryInst());

      if ((!SI) || (!isPotentiallyReachable(SI, &LI, &LaterBBs)) ||
        (SI->getPointerOperand() != LI.getPointerOperand())) {

        Workset.push_back(Walker->getClobberingMemoryAccess(SD->getDefiningAccess(), Loc));
        continue;
      }

      auto Curr = Ann->getDCPtr();
      auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

      Ann->setNewDc(std::move(Cpy));
      visit(SI);
      Ann->setNewDc(std::move(Curr));
    } else if (auto *PHI = dyn_cast<MemoryPhi>(MA)) {

      Phis++;

      if (Phis > MAX_PHIS) {
        errs() << "[WARN] Too many PHIs, prune\n";
        const auto &Use = PHI->getIncomingValue(0);
        Workset.push_back(Use);
      } else {
        for (const auto &Use : PHI->incoming_values())
          Workset.push_back(cast<MemoryAccess>(&Use));
      }
    }
  }
}

template <DepType DT>
void BUCtx<DT>::visitGetElementPtrInst(GetElementPtrInst &GEP) {

  // GEP is a glorified add
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;

  //assert(getLastNonEmptyLvl(Ann->getDc().Chain) == DCLevel::PTR &&
  //      "Expected a pointer to be the last link in the chain for GEP");

  Ann->getDc().addLink(&GEP, DCLevel::PTR);

  auto Curr = Ann->getDCPtr();

  // Track all indexes
  for (auto &Idx : GEP.indices()) {
    auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);
    Ann->setNewDc(std::move(Cpy));
    visit(Idx);
  }

  // Track the pointer
  Ann->setNewDc(std::move(Curr));
  visit(GEP.getPointerOperand());
}

template <DepType DT>
void BUCtx<DT>::visitPHINode(PHINode &PN) {
  // We know this is control flow, but the generic visit should catch the difference in BBs

  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;
  Ann->getDc().addLink(&PN, getLastNonEmptyLvl(Ann->getDc().Chain));

  auto Curr = Ann->getDCPtr();

  for (auto &In : PN.incoming_values()) {
    auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);
    Ann->setNewDc(std::move(Cpy));
    visit(In.get());
  }

  Ann->setNewDc(std::move(Curr));
}

template <DepType DT>
void BUCtx<DT>::visitCallInst(CallInst &CI) {

  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;

  // This could also be a call to an atomic or asm
  if (isLKMMLoad(&CI)) {
    Ann->completeSegWithLoad(&CI);
    return;
  }

  // We found segments that may dangle!
  // Add a new segment for all returns in the callee.

  Ann->getDc().addLink(&CI, getLastNonEmptyLvl(Ann->getDc().Chain));

  auto *Callee = CI.getCalledFunction();
  if (!Callee)
    return;

  for (auto &BB : *Callee) {
    if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator())) {
      if constexpr (DT == DepType::CTRL) {
        ((LKMMSearchPolicy::AnnotCtx<DepType::CTRL> *)this)->searchInScope(*RI);
      } else {
        auto Curr = Ann->getDCPtr();
        auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

        Ann->setNewDc(std::move(Cpy));
        Ann->getDc().addLink(RI, getLastNonEmptyLvl(Curr->Chain));

        auto &End = Ann->getDc().Chain.front();
        if (End.isRet())
          Ann->template makeIntactDep<1, -1>();
        else if (End.isCall())
          Ann->template makeIntactDep<1, 1>();
        else
          Ann->template makeIntactDep<1, 0>();

        Ann->setNewDc(std::move(Curr));
      }
    }
  }
}

template <DepType DT>
void BUCtx<DT>::visitSelectInst(SelectInst &SI) {

  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;
  Ann->getDc().addLink(&SI, getLastNonEmptyLvl(Ann->getDc().Chain));


  for (auto &Op : SI.operands()) {
    auto Curr = Ann->getDCPtr();
    auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

    Ann->setNewDc(std::move(Cpy));
    visit(Op);
    Ann->setNewDc(std::move(Curr));
  }
}

template <DepType DT>
void BUCtx<DT>::visitUnaryOperator(UnaryOperator &UO) {
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;
  Ann->getDc().addLink(&UO, getLastNonEmptyLvl(Ann->getDc().Chain));
  visit(UO.getOperand(0));
}

template <DepType DT>
void BUCtx<DT>::visitSExtInst(SExtInst &SI) {
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;
  Ann->getDc().addLink(&SI, getLastNonEmptyLvl(Ann->getDc().Chain));
  visit(SI.getOperand(0));
}

template <DepType DT>
void BUCtx<DT>::visitBinaryOperator(BinaryOperator &BinOp) {
  auto *Ann = (LKMMSearchPolicy::AnnotCtx<DT> *)this;
  Ann->getDc().addLink(&BinOp, getLastNonEmptyLvl(Ann->getDc().Chain));


  for (auto &Op : BinOp.operands()) {
    auto Curr = Ann->getDCPtr();
    auto Cpy = std::make_unique<DC<LKMMSearchPolicy>>(*Curr);

    Ann->setNewDc(std::move(Cpy));
    visit(Op);
    Ann->setNewDc(std::move(Curr));
  }
}

class LKMMSearchPolicy::LKMMAnnotator {
public:
  LKMMAnnotator( CtxKind Kind, void (* AnnoFn)(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType DT, LKMMAnnotateDeps::DepMap *Result), LKMMAnnotateDeps *PrevResult = nullptr) :
                    Kind(Kind),
                    AnnoFn(AnnoFn),
                    PrevResult(PrevResult),
                    IntactDeps(std::make_unique<IntactDeps_t>()),
                    RisingDeps(std::make_unique<RisingDeps_t>()),
                    MayDangleDeps(std::make_unique<MayDangleDeps_t>()),
                    DanglingDeps(std::make_unique<DanglingDeps_t>()),
                    RisingDanglingDeps(std::make_unique<RisingDanglingDeps_t>()),
                    MayDangleDanglingDeps(std::make_unique<MayDangleDanglingDeps_t>()),
                    MayRiseDeps(std::make_unique<MayRiseDeps_t>()),
                    MayRiseRisingDeps(std::make_unique<MayRiseRisingDeps_t>()),
                    MayRiseMayDangleDeps(std::make_unique<MayRiseMayDangleDeps_t>()),
                    Stats({}) {};

  template <DepType DT>
  llvm::LKMMAnnotateDeps::DepMap *run(Module &M, ModuleAnalysisManager &AM, bool KeepPrevSegments = false);

private:
  const CtxKind Kind;

  void (* AnnoFn)(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType Type, LKMMAnnotateDeps::DepMap *Result);
  llvm::LKMMAnnotateDeps *PrevResult;

  std::unique_ptr<IntactDeps_t> IntactDeps;
  std::unique_ptr<RisingDeps_t> RisingDeps;
  std::unique_ptr<MayDangleDeps_t> MayDangleDeps;
  std::unique_ptr<DanglingDeps_t> DanglingDeps;
  std::unique_ptr<RisingDanglingDeps_t> RisingDanglingDeps;
  std::unique_ptr<MayDangleDanglingDeps_t> MayDangleDanglingDeps;
  std::unique_ptr<MayRiseDeps_t> MayRiseDeps;
  std::unique_ptr<MayRiseRisingDeps_t> MayRiseRisingDeps;
  std::unique_ptr<MayRiseMayDangleDeps_t> MayRiseMayDangleDeps;

  void saveStats();
  bool updateStats(DepType DT);

  struct Stats {
    size_t Intact;
    size_t Rising;
    size_t MayDangle;
    size_t Dangling;
    size_t RisingDangling;
    size_t MayDangleDangling;
    size_t MayRise;
    size_t MayRiseRising;
    size_t MayRiseMayDangle;
  } Stats;

  void reset(bool Full = true) {
    IntactDeps->clear();
    RisingDeps->clear();
    MayDangleDeps->clear();

    if (Full) {
      DanglingDeps->clear();
      RisingDanglingDeps->clear();
      MayDangleDanglingDeps->clear();
      MayRiseDeps->clear();
      MayRiseRisingDeps->clear();
      MayRiseMayDangleDeps->clear();
    }

    //Stats = {0, 0, 0, 0, 0, 0, 0, 0, 0};
    saveStats();
  }
  SmallVector<DC> DCs;
};

class LKMMVerifier {
public:
  //LKMMVerifier();

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);

private:

};

#define SAVE_STAT(STAT) Stats.STAT = STAT##Deps->size();
void LKMMSearchPolicy::LKMMAnnotator::saveStats() {
  FOR_EACH_DEP(SAVE_STAT);
}

bool LKMMSearchPolicy::LKMMAnnotator::updateStats(DepType DT) {
  bool Changed = false;

#define CMP_AND_PRINT(STAT) \
  do { \
    if ( size_t Diff = STAT##Deps->size() - Stats.STAT ) { \
      Changed = true; \
      errs() << #STAT << " increased by " << Diff << "\n"; \
      Num##STAT[DT][Kind][0] += Diff; \
    } \
    SAVE_STAT(STAT); \
  } while (0);

  FOR_EACH_DEP(CMP_AND_PRINT);
#undef CMP_AND_PRINT

  return Changed;
}
#undef SAVE_STAT

template <DepType DT>
llvm::LKMMAnnotateDeps::DepMap *LKMMSearchPolicy::LKMMAnnotator::run(Module &M, ModuleAnalysisManager &AM, bool KeepPrevSegments) {
  AnnotCtx<DT> AC(Kind, AnnoFn, PrevResult);


  // Ctrl deps can have a data dependency up to the conditional, so we need previously collected segments. EXCEPT <X,0> segments because they would complete data deps which we did already.
  reset(!KeepPrevSegments);

  if (M.empty())
    return AC.getResult();

  AC.populate(IntactDeps.get(), RisingDeps.get(), MayDangleDeps.get(),
              DanglingDeps.get(), RisingDanglingDeps.get(), MayDangleDanglingDeps.get(),
              MayRiseDeps.get(), MayRiseRisingDeps.get(), MayRiseMayDangleDeps.get());

  auto &FAM = AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  for (auto &F : M) {

    // TODO: check?
    if (F.empty())
      continue;

    AC.setMSSA(FAM.getResult<MemorySSAAnalysis>(F).getMSSA());
    AC.setPDT(FAM.getResult<PostDominatorTreeAnalysis>(F));

    // Annotate dependencies ending in volatile loads and stores.
    AC.passOne(&F);
  }

  size_t Depth = 5;
  do {
    Depth--;

    for (auto &F : M) {
      if (F.empty())
        continue;

      AC.setMSSA(FAM.getResult<MemorySSAAnalysis>(F).getMSSA());
      AC.setPDT(FAM.getResult<PostDominatorTreeAnalysis>(F));
      if constexpr (DT == DepType::CTRL) {
        //Annotate dependencies ending in nested calls.
        if (!F.hasFnAttribute(takes<DT>()))
          continue;
      } else {
        //Annotate dependencies ending in returns.
        if (!F.getAttributes().getRetAttrs().hasAttribute(returns<DT>()))
          continue;
      }
      AC.passTwo(&F);
    }

    for (auto &F : M) {
      if (F.empty())
        continue;

      AC.setMSSA(FAM.getResult<MemorySSAAnalysis>(F).getMSSA());
      AC.setPDT(FAM.getResult<PostDominatorTreeAnalysis>(F));
      if constexpr (DT == DepType::CTRL) {
        //Annotate dependencies ending in nested ends.
        if (!F.hasFnAttribute(takes<DT>()))
          continue;
      } else {
        //Annotate dependencies ending in calls.
        if (!F.hasFnAttribute(calls<DT>()))
          continue;
      }
      AC.passThree(&F);
    }

    if constexpr (DT == DepType::CTRL) {
      LKMMSearchPolicy::AnnotCtx<DepType::DATA> DataAC(AC.getKind(), AC.AnnotateFn, AC.PrevResult);
      DataAC.populate(AC.getI(), AC.getR(), AC.getMD(), AC.getD(), AC.getRD(), AC.getMDD(), AC.getMR(), AC.getMRR(), AC.getMRMD());
      // We need to do this after both passTwo and passThree
      for (auto &F : M) {
        if (F.empty())
          continue;

        DataAC.setMSSA(FAM.getResult<MemorySSAAnalysis>(F).getMSSA());
        DataAC.setPDT(FAM.getResult<PostDominatorTreeAnalysis>(F));
        if (!F.getAttributes().getRetAttrs().hasAttribute(returns<DepType::DATA>()))
          continue;
        DataAC.passTwo(&F);
      }
      for (auto &F : M) {
        if (F.empty())
          continue;

        DataAC.setMSSA(FAM.getResult<MemorySSAAnalysis>(F).getMSSA());
        DataAC.setPDT(FAM.getResult<PostDominatorTreeAnalysis>(F));
        if (!F.hasFnAttribute(calls<DepType::DATA>()))
          continue;
        DataAC.passThree(&F);
      }
    }
  } while (updateStats(DT) && Depth);

#define REMOVE_DUP(name) \
  removeDuplicates(*name##Deps.get());
  FOR_EACH_DEP(REMOVE_DUP);
#undef REMOVE_DUP

  AC.merge(12);
  return AC.getResult();
}

PreservedAnalyses LKMMVerifier::run(Module &M, ModuleAnalysisManager &AM) {
  return PreservedAnalyses::all();
}

void LKMMVerifyDepsPass::verifyChain(LKMMAnnotateDeps::DepMap *Pre, LKMMAnnotateDeps::DepMap *Post, Module &M) {

  auto EC = std::error_code();
  auto Name = M.getModuleIdentifier();
  std::replace(Name.begin(), Name.end(), '/', '-');
  Name = Name.substr(0, Name.length()-2);

  auto ModDir = Prefix + Name + "/";
  auto e = sys::fs::is_directory(ModDir);
  if (!e) {
    errs() << "Not a directory [verify]: " << ModDir << "\n";
  }

  auto FileName = "matched_chains.txt";
  auto Matches = raw_fd_ostream(ModDir + FileName, EC, sys::fs::CreationDisposition::CD_OpenAlways, sys::fs::FileAccess::FA_Write, sys::fs::OpenFlags::OF_Append);

  for (auto &Seg : *Pre) {

    auto It = std::find_if(Post->begin(), Post->end(),
        [&Seg](const SegmentID<0,0,LKMMAnnotateDeps> &PostSeg) {

      // Compare beggingin and end first
      return Seg == PostSeg;
    });

    if (It == Post->end()) {
      Matches << raw_fd_ostream::Colors::RED << "Missing chain for [1]:\n";
      Matches << raw_fd_ostream::Colors::RESET << DepToStr(Seg.FinalizedAs) << ": " << Seg.Pretty << "\n\n";
      continue;
    }

    auto Dbg = It;
    bool Matched = false;

    // The segments should be sorted
    while (It != Post->end() && Seg == *It) {

      Matched = true;
      auto Jt = It->getDC().Chain.cbegin();

      for (auto Link = Seg.getDC().Chain.cbegin(); Link != Seg.getDC().Chain.cend(); Link++) {
        auto Tmp = std::find_if(Jt, It->getDC().Chain.cend(),
          [&Link](const LKMMAnnotateDeps::DCLink &PostLink) {
          return Link->Loc == PostLink.Loc;
        });
        if (Tmp == It->getDC().Chain.cend()) {
          if (Link->isCtrl()) {
            Matches << raw_fd_ostream::Colors::YELLOW << "Missing Link:\n";
            Matches << raw_fd_ostream::Colors::RESET << getInstLocString(Link->F, Link->Loc.value(), false) << "\n\n";
          Matched = false;
          }
          continue;
        }
        Jt = Tmp;
      }
      if (Matched)
        break;
      It++;
    }

    if (!Matched) {
      Matches << raw_fd_ostream::Colors::RED << "Missing chain for [2]:\n";
      Matches << raw_fd_ostream::Colors::RESET << DepToStr(Seg.FinalizedAs) << ": " << Seg.Pretty << "\n\n";
      continue;
    }

  //#ifdef LLVM_DEBUG
    Matches << raw_fd_ostream::Colors::GREEN << "Matched:\nPRE-OPT:\n";
    Matches << raw_fd_ostream::Colors::RESET << DepToStr(Seg.FinalizedAs) << ": " << Seg.Pretty;
    Matches << raw_fd_ostream::Colors::GREEN << "\nPOST_OPT:\n";
    Matches << raw_fd_ostream::Colors::RESET << DepToStr(Seg.FinalizedAs) << ": " << Dbg->Pretty << "\n\n";
  //#endif
  }
}

bool LKMMAnnotatePrimitives::getAtomicAnnot(StringRef Name, const StringRef **Attr) {

  auto *Ptr = find(Atomics, Name);
  if (Ptr == adl_end(Atomics))
    return false;

  *Attr = Ptr;
  return true;
}
bool LKMMAnnotatePrimitives::begins(StringRef Name) {

  auto Tmp = Name;
  if (Tmp.back() == '\0')
    Tmp = Tmp.drop_back(1);

  return Tmp.back() == 'b';
}
bool LKMMAnnotatePrimitives::getPrimitiveAnnot(StringRef Name, StringRef *Attr) {

  auto FixedN = Name;
  if (std::strncmp(Name.data(), "__depsan_atomic_xadd", 20) == 0)
    FixedN = xadd;

  for (auto *It = adl_begin(Macros); It != adl_end(Macros); It++) {
    if (std::strncmp(FixedN.data(), It->data(), It->size()) == 0) {
      int drop = FixedN.back() != '\0' ? 2 : 3;
      *Attr = FixedN.drop_back(drop);
      return true;
    }
  }

  return false;
}

bool LKMMAnnotatePrimitives::guessIsStore(CallInst *CI) {

  // Linux' atomic helpers have type F (val, ptr, ...)
  // The inline asm usually has the ptr first
  if (CI->isInlineAsm()) {
    auto *Ty = CI->getFunctionType();
    if (Ty->getNumParams() > 1 && Ty->getNumParams() < 4)
      if (Ty->getParamType(0)->isPointerTy())
        return true;
    return false;
  }

  return false;
  // auto *Callee = CI->getCalledFunction();
  // if (!Callee)
  //   return false;

  // const StringRef *Annot = nullptr;
  // return getAtomicAnnot(Callee->getName(), &Annot);

}
bool LKMMAnnotatePrimitives::guessIsLoad(CallInst *CI) {

  // Linux' atomic helpers have type F (val, ptr, ...)
  // The inline asm usually has the ptr first
  if (CI->isInlineAsm()) {
    auto *Ty = CI->getFunctionType();
    if (Ty->getNumParams() > 0 && !Ty->getReturnType()->isVoidTy())
      if (Ty->getParamType(0)->isPointerTy())
        return true;
    return false;
  }

  return false;
  // auto *Callee = CI->getCalledFunction();
  // if (!Callee)
  //   return false;

  // const StringRef *Annot = nullptr;
  // return getAtomicAnnot(Callee->getName(), &Annot);

}

void LKMMAnnotatePrimitives::transform(Function &F) {

  SmallVector<StringRef, 3> Annotations;

  StringRef Annot;
  StringRef Name;
  for (auto &BB : F) {
    for (auto I = BB.begin(); I != BB.end(); ++I ) {
      if (auto *CI = dyn_cast<CallInst>(&*I)) {
        if(guessIsStore(CI)) {
          CI->addAnnotationMetadata("lkmm_store");
          goto isAsm;
        }
        if(guessIsLoad(CI)) {
          CI->addAnnotationMetadata("lkmm_load");
          goto isAsm;
        }

        auto *Callee = CI->getCalledFunction();
        if (!Callee)
          goto isAsm;
        if (Callee->isIntrinsic()) {
          if (Callee->getIntrinsicID() != Intrinsic::annotation)
            goto isAsm;
          auto *GV = cast<GlobalVariable>(CI->getArgOperand(1));
          assert(GV->hasInitializer() && "Expected initializer");
          auto *CDA = cast<ConstantDataArray>(GV->getInitializer());
          Name = CDA->getAsString();
        } else {
          Name = Callee->getName();
        }
        if (getPrimitiveAnnot(Name, &Annot)) {

          if (!begins(Name)) {
          //auto *It = std::find_if_not(Annotations.begin(), Annotations.end(), [Annot](StringRef A) { return std::strncmp(A.data(), Annot.data(), Annot.size()); });
            assert(std::strncmp(Annotations.back().data(), Annot.data(), Annot.size()) == 0 && "Mismatched annotation");

            // FIXME: remove leftover load agg.tmp if this was an aggExpr?
            // should be taken care of by DCE anyways
            if (Callee->isIntrinsic()) {

              //if (auto *I = dyn_cast<Instruction>(CI->getArgOperand(0)))
              //  I->addAnnotationMetadata("lkmm_load");
              CI->replaceAllUsesWith(CI->getArgOperand(0));
            }

            I = CI->eraseFromParent();
            I--;

            Annot = StringRef();
            Annotations.pop_back();
            continue;
          }
          // _b annotation hopefully
          Annotations.push_back(Annot);
          I = CI->eraseFromParent();
          I--;
          continue;
        }
      }
isAsm:
      if (!Annotations.empty()) {
        //assert(Annot && "Missing annotation");
        auto Anns = std::set<StringRef>(Annotations.begin(), Annotations.end());
        for (auto Annot : Anns) {
          MDNode *Meta = MDNode::get(I->getContext(), MDString::get(I->getContext(), Annot));
          MDNode *Existing = I->getMetadata(LLVMContext::MD_lkmm_primitive);
          if (Existing)
            Meta = MDNode::concatenate(Existing, Meta);
          I->setMetadata(LLVMContext::MD_lkmm_primitive, Meta);
        }
      }
    }
  }
}

//===----------------------------------------------------------------------===//
// The Annotation Pass
//===----------------------------------------------------------------------===//

AnalysisKey LKMMAnnotateDepsPass::Key;

LKMMAnnotateDeps LKMMAnnotateDepsPass::run(Module &M,
                                            ModuleAnalysisManager &AM) {

  auto EC = std::error_code();
  auto Name = M.getModuleIdentifier();
  std::replace(Name.begin(), Name.end(), '/', '-');
  Name = Name.substr(0, Name.length()-2);

  auto ModDir = Prefix + Name + "/";
  auto ec = sys::fs::create_directories(ModDir);
  if (ec) {
    errs() << "Error creating directory " << ModDir << ": " << ec.message() << "\n";
  }

  std::string FileName = "Pre_Segments.txt";
  sys::fs::openFileForWrite(ModDir + FileName, OutFD[0], sys::fs::CreationDisposition::CD_CreateAlways, sys::fs::OF_None);
  FileName = "Post_Segments_.txt";
  sys::fs::openFileForWrite(ModDir + FileName, OutFD[1], sys::fs::CreationDisposition::CD_CreateAlways, sys::fs::OF_None);

  FileName = "Mod_full.ll1";
  auto Opt = raw_fd_ostream(ModDir + FileName, EC, sys::fs::CreationDisposition::CD_CreateAlways);

  LKMMAnnotateDeps Ret;

  {
    auto A = LKMMSearchPolicy::LKMMAnnotator(CK_Annot, &annotateChain);
    Ret.add(DepType::ADDR, A.run<DepType::ADDR>(M, AM));
    Ret.add(DepType::DATA, A.run<DepType::DATA>(M, AM));
    Ret.add(DepType::CTRL, A.run<DepType::CTRL>(M, AM, true));
  }

  Opt << M;
  for (auto &F : M) {
    if (F.hasFnAttribute("is_entry"))
      saveMiniModule(&F, ModDir, "1");
  }

  return Ret;
}

bool LKMMAnnotateDeps::invalidate(Module &, const PreservedAnalyses &PA,
                  ModuleAnalysisManager::Invalidator &) {
  auto PAC = PA.getChecker<LKMMAnnotateDepsPass>();
  return !PAC.preservedWhenStateless();
}

//===----------------------------------------------------------------------===//
// The Verification Pass
//===----------------------------------------------------------------------===//
PreservedAnalyses LKMMVerifyDepsPass::run(Module &M,
                                            ModuleAnalysisManager &AM) {
  auto &Annotations = AM.getResult<LKMMAnnotateDepsPass>(M);
  errs() << "\nvvvvv~~~~~~~~~ LKMMVerifyDepsPass ~~~~~vvvvv\n";

  auto EC = std::error_code();
  auto Name = M.getModuleIdentifier();
  std::replace(Name.begin(), Name.end(), '/', '-');
  Name = Name.substr(0, Name.length()-2);
  auto ModDir = Prefix + Name + "/";
  auto e = sys::fs::is_directory(ModDir);
  if (!e) {
    errs() << "Not a directory: " << ModDir << "\n";
  }

  auto FileName = "Mod_full.ll2";
  auto Opt = raw_fd_ostream(ModDir + FileName, EC, sys::fs::CreationDisposition::CD_CreateAlways);

  auto StatName = "Stats.json";
  auto Stat = raw_fd_ostream(ModDir + StatName, EC, sys::fs::CreationDisposition::CD_CreateAlways);
  {
    auto A = LKMMSearchPolicy::LKMMAnnotator(CK_Ver, &addChain, &Annotations);
    verifyChain(Annotations.IntactDeps[(int)DepType::ADDR], A.run<DepType::ADDR>(M, AM), M);
    verifyChain(Annotations.IntactDeps[(int)DepType::DATA], A.run<DepType::DATA>(M, AM), M);
    verifyChain(Annotations.IntactDeps[(int)DepType::CTRL], A.run<DepType::CTRL>(M, AM, true), M);
  }

  Opt << M;
  for (auto &F : M) {
    if (F.hasFnAttribute("is_entry"))
      saveMiniModule(&F, ModDir, "2");
  }

  errs() << "\n^^^^^~~~~~~~~~ LKMMVerifyDepsPass ~~~~~^^^^^\n";

  PrintStatisticsJSON(Stat);
  return PreservedAnalyses::all();
}

//===----------------------------------------------------------------------===//
// The Annotation Transformation
//===----------------------------------------------------------------------===//

static void annotateAllRec(Function &F, const StringRef &Annot) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      MDNode *Meta = MDNode::get(I.getContext(), MDString::get(I.getContext(), Annot));
      I.setMetadata(LLVMContext::MD_lkmm_primitive, Meta);
      if (auto *CI = dyn_cast<CallInst>(&I)) {
        if (!CI->getCalledFunction())
          continue;

        annotateAllRec(*CI->getCalledFunction(), Annot);
      }
    }
  }
}

PreservedAnalyses LKMMAnnotatePrimitives::run(Module &M,
                                            ModuleAnalysisManager &AM) {

  for (auto &F : M) {
    if (F.empty())
      continue;


    const StringRef *Annot = nullptr;
    if (getAtomicAnnot(F.getName(), &Annot)) {
      annotateAllRec(F, *Annot);
      for (auto *U : F.users()) {
        if (auto *CI = dyn_cast<CallInst>(U)) {
          MDNode *Meta = MDNode::get(CI->getContext(), MDString::get(CI->getContext(), *Annot));
          MDNode *Existing = CI->getMetadata(LLVMContext::MD_lkmm_primitive);
          if (Existing)
            Meta = MDNode::concatenate(Existing, Meta);
          CI->setMetadata(LLVMContext::MD_lkmm_primitive, Meta);

          // if (!CI->getType()->isVoidTy())
          //   CI->addAnnotationMetadata("lkmm_load");
          // CI->addAnnotationMetadata("lkmm_store");
        }
      }
    }

    transform(F);
  }

  return PreservedAnalyses::none();
}

//===----------------------------------------------------------------------===//
// Annotation Removal
// ===----------------------------------------------------------------------===//

void LKMMRemoveAnnotations::transform(Function &F) {

  auto FnAttrs = AttributeSet::get(F.getContext(), {
    Attribute::get(F.getContext(), takes<DepType::ADDR>()),
    Attribute::get(F.getContext(), takes<DepType::DATA>()),
    Attribute::get(F.getContext(), takes<DepType::CTRL>()),
    Attribute::get(F.getContext(), calls<DepType::ADDR>()),
    Attribute::get(F.getContext(), calls<DepType::DATA>()),
    Attribute::get(F.getContext(), calls<DepType::CTRL>()),
  });

  auto RetAttrs = AttributeSet::get(F.getContext(), {
    Attribute::get(F.getContext(), returns<DepType::ADDR>()),
    Attribute::get(F.getContext(), returns<DepType::DATA>()),
    Attribute::get(F.getContext(), returns<DepType::CTRL>())
  });

  auto ParamAttrs = AttributeSet::get(F.getContext(), {
    Attribute::get(F.getContext(), is<DepType::ADDR>()),
    Attribute::get(F.getContext(), is<DepType::DATA>()),
    Attribute::get(F.getContext(), is<DepType::CTRL>())
  });

  F.removeFnAttrs(FnAttrs);
  F.removeRetAttrs(RetAttrs);
  for (size_t Idx=0; Idx < F.arg_size(); Idx++) {
    F.removeParamAttrs(Idx, ParamAttrs);
  }
}

PreservedAnalyses LKMMRemoveAnnotations::run(Module &M,
                                            ModuleAnalysisManager &AM) {

  for (auto &F : M) {
    if (F.empty())
      continue;

    transform(F);
  }

  return PreservedAnalyses::none();
}


} // namespace llvm
