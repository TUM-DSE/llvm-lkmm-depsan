//===- llvm/Transforms/LKMMDependenceAnalysis.h - LKMM Deps -----*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains all declarations / definitions required for LKMM
/// dependence analysis. Implementations live in LKMMDependenceAnalysis.cpp.
///
//===----------------------------------------------------------------------===//

#include <concepts>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <type_traits>
#include <unordered_set>
#include <variant>

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/PassManager.h"

#ifndef LLVM_TRANSFORMS_UTILS_LKMMDEPENDENCEANALYSIS_H
#define LLVM_TRANSFORMS_UTILS_LKMMDEPENDENCEANALYSIS_H

namespace llvm {
  class LKMMAnnotateDeps;


//===----------------------------------------------------------------------===//
// Some helpers
//===----------------------------------------------------------------------===//
void setupResultDir(const std::string &OutPath);

bool dbgLocEq(const DebugLoc &L, const DebugLoc &R);

//===----------------------------------------------------------------------===//
// Some common types
//===----------------------------------------------------------------------===//

// TODO: Reduce
/// Every dep chain link has a DCLevel. The level tracks whether the pointer
/// itself or the pointed-to value, the pointee, is part of the dependency
/// chain.
///
/// PTR   -> we're interested in the pointer itself.  PTE -> we're
/// interested in the pointed-to value.
///
/// BOTH  -> matches PTR __AND__ PTE.
///
/// NORET -> Dep chain doesn't get returned, but calling function should still
/// be made aware of its existence. The calling function then knows that the
/// beginning has been seen, but its dependency chain might have been broken.
///
/// EMPTY -> Empty.
enum class DCLevel { PTR, PTE, BOTH, NORET, EMPTY };

enum Reason { COMPLETE, EXTERN, OVERWRITE, DOUBLE_MEM };

enum DepType { ADDR, DATA, CTRL };

enum CtxKind { CK_Annot, CK_Ver };

class DCLinkBase {
public:
  DCLinkBase(std::optional<DebugLoc> Loc, DCLevel Lvl, bool S, bool L, int Depth)
      : Loc(Loc), Lvl(Lvl), IsStore(S), IsLoad(L), Depth(Depth) {}

  //DCLinkBase(const DCLinkBase &Other) : Loc(Other.Loc), Lvl(Other.Lvl), Depth(Other.Depth) {}
  virtual ~DCLinkBase() = default;

  std::optional<DebugLoc> Loc;
  DCLevel Lvl;

  bool isCall() const;
  bool isRet() const;
  bool isBegin() const;
  bool isEnd() const;
  bool isRMW() const;

  void addDepth(int Delta) { Depth += Delta; }
  int getDepth() const { return Depth; }

  virtual bool operator==(const DCLinkBase &Other) const = 0;

protected:
  bool IsStore;
  bool IsLoad;
  int Depth;
};

/// Represents a dependency chain (segment). A dep chain consists of a beginning, an
/// ending, and a unique chain of links between them.
///
/// We use the names "dependency chain" and "chain segment" interchangeably.
template <typename Context>
struct DC {
  DC() {};

  template <typename T>
  DC<Context>(const DC<T> &Other) = delete;

  DC(const DC &A, const DC &B, int Delta) = delete;

  bool addLink(const typename Context::DCLink &Link, std::optional<int> Arg = std::nullopt);

  bool addLink(Instruction *Val, DCLevel Lvl, std::optional<int> Arg = std::nullopt) = delete;

  bool insertLink(Instruction *Val, DCLevel Lvl, std::optional<int> Arg = std::nullopt) = delete;

  // Links between (including) the beginning and the ending.
  // In reverse order; from the end to the beginning.
  std::vector<typename Context::DCLink> Chain;

  // Both segments begin in a call inst;
  // may dangle: we tracked up to the value of this call in F
  // rises: we tracked up to the begining of F and stored one specific call site (likely not in F)
  bool mayDangle() {
    return Chain.back().isCall() && !ArgB;
  }
  bool rises() {
    return Chain.back().isCall() && ArgB;
  }

  // Segment ends in a call
  // ArgE must have a value
  bool mayRise() {
    return Chain.front().isCall();
  }

  // Segment ends in a return
  bool dangles() {
    return Chain.front().isRet();
  }

  // Chain does not begin or end in the function.
  // The escaping arguments must be annotated.
  std::optional<int> ArgB;
  std::optional<int> ArgE;

  bool operator<(const DC &Other) const {

    if (Chain.size() != Other.Chain.size())
      return Chain.size() < Other.Chain.size();

    for (size_t i = 0; i < Chain.size(); i++) {
      const auto &L = Chain[i];
      const auto &R = Other.Chain[i];

      if (!L.Loc || !R.Loc)
        continue;
      if (!L.Loc.value() || !R.Loc.value())
        continue;

      if (L.Loc.value().getLine() != R.Loc.value().getLine())
        return L.Loc.value().getLine() < R.Loc.value().getLine();
      if (L.Loc.value().getCol() != R.Loc.value().getCol())
        return L.Loc.value().getCol() < R.Loc.value().getCol();
    }

    if (ArgB != Other.ArgB)
      return ArgB < Other.ArgB;

    if (ArgE != Other.ArgE)
      return ArgE < Other.ArgE;

    return false; // equal
  }

  bool operator==(const DC &Other) const {
    return !(*this < Other) && !(Other < *this);
  }

  void print() const = delete;

  class DCHash {
  public:
    std::size_t operator()(const DC &DC) const noexcept {
      return hash_combine(std::hash<decltype(DC.Chain)>{}(DC.Chain), DC.ArgB.value_or(0), DC.ArgE.value_or(0));
    }
  };
};

template <int B, int E>
struct SegmentType {
  static constexpr std::string_view Type;
};

template<> constexpr std::string_view SegmentType<0, 0>::Type = "Intact";
template<> constexpr std::string_view SegmentType<-1, 0>::Type = "Rising";
template<> constexpr std::string_view SegmentType<1, 0>::Type = "May Dangle";
template<> constexpr std::string_view SegmentType<0, -1>::Type = "Dangling";
template<> constexpr std::string_view SegmentType<-1, -1>::Type = "Rising & Dangling";
template<> constexpr std::string_view SegmentType<1, -1>::Type = "May Dangle & Dangling";
template<> constexpr std::string_view SegmentType<0, 1>::Type = "May Rise";
template<> constexpr std::string_view SegmentType<-1, 1>::Type = "May Rise & Rising";
template<> constexpr std::string_view SegmentType<1, 1>::Type = "May Rise & May Dangle";

template <int B, int E, typename C>
class SegmentID {
  // For each segment we need to store:
  // the Pair, the Function, the Arg numbers,
public:
  SegmentID(DC<C> &Dc) : Dc(Dc) {

    // Will throw if we messed up
    if constexpr (B == -1) {
      assert(Dc.ArgB.has_value());
    }
    if constexpr (E == 1) {
      assert(Dc.ArgE.has_value());
    }
  }

  template<typename O>
  SegmentID(const SegmentID<B,E,O> &Other) : Pretty(Other.Pretty), Dc(Other.getDC()) {}

  //SegmentID(SegmentID<B,E,C> &&Other) : Pretty(std::move(Other.Pretty)), Dc(std::move(Other.Dc)) {};
  //SegmentID(SegmentID<B,E,C> &Other) : Pretty(Other.Pretty), Dc(Other.getDC()) {};

  //SegmentID& operator=(const SegmentID<B,E,C> &Other) { Dc = Other.getDC(); return *this; }

  template<int M>
  SegmentID(SegmentID<B,M,C> &Beg, SegmentID<-M,E,C> &End) : Dc(Beg.getDC(), End.getDC(), M) {}

  /// Returns true if [*this*, Other] is a valid segment.
  template<int BO, int EO>
  bool isCompatible(const SegmentID<BO,EO,C> &Other) const {
    // Segments must match at function boundaries
    if constexpr (E == 0 | BO == 0)
      return false;

    // Rising matches MayRise, Dangling matches MayDangle
    if constexpr (E + BO != 0)
      return false;

    // MR/R meet at call instructions, arguments must match
    if constexpr (E == 1) {
      if (this->getArgE() != Other.getArgB())
        return false;

      return dbgLocEq(this->getEnd(), Other.getBegin());
    }

    // D/MD meet at return instructions
    if constexpr (E == -1) {
      return dbgLocEq(this->getEnd(), Other.getBegin());
    }

    llvm_unreachable("Invalid segment combination");
  }

  // To sort
  // (1) Lex. by filename
  // (2) by earliest end loc
  // (3) by earliest beg loc
  // Since we search bottom up, the annotator will insert the segments in roughly this order
  bool operator<(const SegmentID &Other) const {
    auto LEndOpt = this->getEnd();
    auto REndOpt = Other.getEnd();

    if (LEndOpt != REndOpt) {
      if (!LEndOpt)
        return true;
      if (!REndOpt)
        return false;

      auto LEnd = LEndOpt.value();
      auto REnd = REndOpt.value();

      if (!LEnd || !REnd)
        return false;

      auto *LScope = cast_or_null<DIScope>(LEnd->getScope());
      auto *RScope = cast_or_null<DIScope>(REnd->getScope());

      if (LScope != RScope) {
        if (!LScope)
          return true;
        if (!RScope)
          return false;

        if (LScope->getFilename() != RScope->getFilename())
          return LScope->getFilename() < RScope->getFilename();
      }

      if (LEnd.getLine() != REnd.getLine())
        return LEnd.getLine() < REnd.getLine();

      if (LEnd.getCol() != REnd.getCol())
        return LEnd.getCol() < REnd.getCol();
    }

    auto LBeginOpt = this->getBegin();
    auto RBeginOpt = Other.getBegin();

    if (LBeginOpt != RBeginOpt) {
      if (!LBeginOpt)
        return true;
      if (!RBeginOpt)
        return false;

      auto LBegin = LBeginOpt.value();
      auto RBegin = RBeginOpt.value();

      if (LBegin.getLine() != RBegin.getLine())
        return LBegin.getLine() < RBegin.getLine();

      if (LBegin.getCol() != RBegin.getCol())
        return LBegin.getCol() < RBegin.getCol();
    }

    return false;
  }

  bool operator==(const SegmentID &Other) const {
    return !(*this < Other) && !(Other < *this);
  }


  // To remove duplicates
  static bool equal(const SegmentID &LHS, const SegmentID &RHS) {
    if (LHS == RHS)
      return LHS.Dc == RHS.Dc;
    return false;
  }

  static bool lt(const SegmentID &LHS, const SegmentID &RHS) {
    if (LHS < RHS)
      return true;
    if (RHS < LHS)
      return false;
    return LHS.Dc < RHS.Dc;
  }

  void makePretty();
  void setStr(const std::string &Str ,const DepType DT) { Pretty = Str; FinalizedAs = DT;}
  void print() { errs() << Pretty << "\n\n"; };

  // TODO: string_view?
  const std::string_view &getType() const { return Type; }
  const std::optional<DebugLoc> getBegin() const { return Dc.Chain.back().Loc; }
  const std::optional<DebugLoc> getEnd() const { return Dc.Chain.front().Loc; }
  std::optional<int> getArgB() const { return Dc.ArgB; }
  std::optional<int> getArgE() const { return Dc.ArgE; }
  constexpr int getB() const { return B; }
  constexpr int getE() const { return E; }
  constexpr int delta() { return E - B; }

  const DC<C> &getDC() const { return Dc; }
  static constexpr std::string_view Type = SegmentType<B, E>::Type;
  std::string Pretty;
  DepType FinalizedAs;

private:
  DC<C> Dc;
};

//===----------------------------------------------------------------------===//
// Function Reachability Analysis and Module Extraction
//===----------------------------------------------------------------------===//
void saveMiniModule(Function *F, const std::string &OutDir, const std::string &Suffix);

std::set<Function *> getReachableFunctions(Function *F);
std::set<GlobalVariable *> getReachableGlobals(std::set<Function *> &Funcs);

//===----------------------------------------------------------------------===//
// Some helper functions
//===----------------------------------------------------------------------===//

/// Returns a string representation of an instruction's location in the form:
/// <function_name>::<line>:<column>.
///
/// \param I the instruction whose location string should be returned.
/// \param viaFile set to true if the filename should be used instead of the
///  function name
/// \param Entering set to true if the location for a call is being requested
/// which control is entering right now. In that case, line and column info
/// will remain the same, but the function name will be replaced with the
/// called function to make for better reading when outputting broken
/// dependencies.
///
/// \returns a string represenation of \p I's location.
std::string getInstLocString(Instruction *I, bool ViaFile = false);

std::string getInstLocString(const StringRef &F ,const DebugLoc &InstDebugLoc, bool ViaFile = false);

/// _Sorts_ and removes duplicates from the given vector of segments.
template<int B, int E, typename C>
void removeDuplicates(std::vector<SegmentID<B, E, C>> &Segments);

/// \returns the last non-EMPTY lvl in a \p Chain.
///
/// \param Chain the _non-empty_ chain to search.
template <typename C>
DCLevel getLastNonEmptyLvl(std::vector<C> &Chain) {
  for (auto It = Chain.rbegin(); It != Chain.rend(); ++It) {
    if (It->Lvl != DCLevel::EMPTY)
      return It->Lvl;
  }

  //llvm_unreachable("Chain is empty, no non-EMPTY level found");
  return DCLevel::EMPTY; //FIXME
}

//===----------------------------------------------------------------------===//
// The Dependency Analysis
//===----------------------------------------------------------------------===//

class LKMMAnnotateDeps {

public:
  using DC = DC<LKMMAnnotateDeps>;
  using DepMap = std::vector<SegmentID<0,0, LKMMAnnotateDeps>>;

  enum DCLinkType { VALUE, CALL, RETURN, CONTROL };
  class DCLink;

  DepMap *IntactDeps[3];

  // never invalidate this
  bool invalidate(Module &, const PreservedAnalyses &PA,
                  ModuleAnalysisManager::Invalidator &);

  void add(DepType DT, DepMap *Result) { IntactDeps[(int)DT] = Result; };
};

//===----------------------------------------------------------------------===//
// The IR search
//===----------------------------------------------------------------------===//
class LKMMSearchPolicy {
public:
  using DC = DC<LKMMSearchPolicy>;

  template<int B, int E>
  using DepMap = std::vector<SegmentID<B,E, LKMMSearchPolicy>>;

  typedef DepMap<0,0> IntactDeps_t;
  typedef DepMap<-1,0> RisingDeps_t;
  typedef DepMap<1,0> MayDangleDeps_t;
  typedef DepMap<0,-1> DanglingDeps_t;
  typedef DepMap<-1,-1> RisingDanglingDeps_t;
  typedef DepMap<1,-1> MayDangleDanglingDeps_t;
  typedef DepMap<0,1> MayRiseDeps_t;
  typedef DepMap<-1,1> MayRiseRisingDeps_t;
  typedef DepMap<1,1> MayRiseMayDangleDeps_t;

  //std::unique_ptr<llvm::DC<LKMMAnnotateDeps> *> DCs;
  class DCLink;

  template<DepType DT>
  class AnnotCtx;

  class LKMMAnnotator;
};

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

class SegmentNode {
public:
  void *Seg;
  int B, E;
  std::vector<SegmentNode *> Successors;

  template<int SB, int SE, typename C>
  SegmentNode(SegmentID<SB,SE,C> *S) : Seg((void*)S), B(SB), E(SE) {};
};

// Directed (cyclic) graph of segments
// Edges exist only iff two segments match at function boundaries
class SegmentGraph {
public:
  template<int B, int E, typename C>
  void addSegment(SegmentID<B,E,C> *Seg);

  template<int B, int E, typename C>
  SegmentNode* getSegmentNode(SegmentID<B,E,C> *Seg);

  template<int B, int M, int E, typename C>
  void addEdge(SegmentID<B,M,C> *From, SegmentID<-M,E,C> *To);

  void enumeratePaths(size_t i, void (*AnnoFn)(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType Type, LKMMAnnotateDeps::DepMap *Result), DepType Type, LKMMAnnotateDeps::DepMap *Result);

private:
  std::vector<std::unique_ptr<SegmentNode>> Nodes;
  std::vector<SegmentNode*> StartSet;
};

//===----------------------------------------------------------------------===//
// The Annotation Transform
//===----------------------------------------------------------------------===//

class LKMMAnnotatePrimitives : public PassInfoMixin<LKMMAnnotatePrimitives> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  constexpr static StringRef Atomics[] = {
    "atomic_read",
    "atomic_set",
    "atomic_read_acquire",
    "atomic_set_release",
    "atomic_long_read",
    "atomic_long_set",
    "atomic_long_read_acquire",
    "atomic_long_set_release",
    "atomic_add",
    "atomic_sub",
    "atomic_inc",
    "atomic_dec",
    "atomic_and",
    "atomic_andnot",
    "atomic_or",
    "atomic_long_add",
    "atomic_long_sub",
    "atomic_long_inc",
    "atomic_long_dec",
    "atomic_long_and",
    "atomic_long_andnot",
    "atomic_long_or",
    "atomic_fetch_add",
    "atomic_fetch_add_relaxed",
    "atomic_fetch_add_acquire",
    "atomic_fetch_add_release",
    "atomic_long_fetch_add",
    "atomic_long_fetch_add_relaxed",
    "atomic_long_fetch_add_acquire",
    "atomic_long_fetch_add_release",
    "atomic_fetch_inc",
    "atomic_fetch_inc_relaxed",
    "atomic_fetch_inc_acquire",
    "atomic_fetch_inc_release",
    "atomic_long_fetch_inc",
    "atomic_long_fetch_inc_relaxed",
    "atomic_long_fetch_inc_acquire",
    "atomic_long_fetch_inc_release",
    "atomic_fetch_sub",
    "atomic_fetch_sub_relaxed",
    "atomic_fetch_sub_acquire",
    "atomic_fetch_sub_release",
    "atomic_long_fetch_sub",
    "atomic_long_fetch_sub_relaxed",
    "atomic_long_fetch_sub_acquire",
    "atomic_long_fetch_sub_release",
    "atomic_fetch_dec",
    "atomic_fetch_dec_relaxed",
    "atomic_fetch_dec_acquire",
    "atomic_fetch_dec_release",
    "atomic_long_fetch_dec",
    "atomic_long_fetch_dec_relaxed",
    "atomic_long_fetch_dec_acquire",
    "atomic_long_fetch_dec_release",
    "atomic_fetch_and",
    "atomic_fetch_and_relaxed",
    "atomic_fetch_and_acquire",
    "atomic_fetch_and_release",
    "atomic_long_fetch_and",
    "atomic_long_fetch_and_relaxed",
    "atomic_long_fetch_and_acquire",
    "atomic_long_fetch_and_release",
    "atomic_fetch_andnot",
    "atomic_fetch_andnot_relaxed",
    "atomic_fetch_andnot_acquire",
    "atomic_fetch_andnot_release",
    "atomic_long_fetch_andnot",
    "atomic_long_fetch_andnot_relaxed",
    "atomic_long_fetch_andnot_acquire",
    "atomic_long_fetch_andnot_release",
    "atomic_fetch_or",
    "atomic_fetch_or_relaxed",
    "atomic_fetch_or_acquire",
    "atomic_fetch_or_release",
    "atomic_long_fetch_or",
    "atomic_long_fetch_or_relaxed",
    "atomic_long_fetch_or_acquire",
    "atomic_long_fetch_or_release",
    "atomic_add_return",
    "atomic_add_return_relaxed",
    "atomic_add_return_acquire",
    "atomic_add_return_release",
    "atomic_inc_return",
    "atomic_inc_return_relaxed",
    "atomic_inc_return_acquire",
    "atomic_inc_return_release",
    "atomic_long_inc_return",
    "atomic_long_inc_return_relaxed",
    "atomic_long_inc_return_acquire",
    "atomic_long_inc_return_release",
    "atomic_sub_return",
    "atomic_sub_return_relaxed",
    "atomic_sub_return_acquire",
    "atomic_sub_return_release",
    "atomic_long_sub_return",
    "atomic_long_sub_return_relaxed",
    "atomic_long_sub_return_acquire",
    "atomic_long_sub_return_release",
    "atomic_dec_return",
    "atomic_dec_return_relaxed",
    "atomic_dec_return_acquire",
    "atomic_dec_return_release",
    "atomic_long_dec_return",
    "atomic_long_dec_return_relaxed",
    "atomic_long_dec_return_acquire",
    "atomic_long_dec_return_release",
    "atomic_xchg",
    "atomic_xchg_relaxed",
    "atomic_xchg_release",
    "atomic_xchg_acquire",
    "atomic_long_xchg",
    "atomic_long_xchg_relaxed",
    "atomic_long_xchg_release",
    "atomic_long_xchg_acquire",
    "atomic_cmpxchg",
    "atomic_cmpxchg_relaxed",
    "atomic_cmpxchg_acquire",
    "atomic_cmpxchg_release",
    "atomic_long_cmpxchg",
    "atomic_long_cmpxchg_relaxed",
    "atomic_long_cmpxchg_acquire",
    "atomic_long_cmpxchg_release",
    "atomic_sub_and_test",
    "atomic_dec_and_test",
    "atomic_inc_and_test",
    "atomic_add_negative",
    "atomic_long_sub_and_test",
    "atomic_long_dec_and_test",
    "atomic_long_inc_and_test",
    "atomic_long_add_negative",

    "rcu_read_lock",
    "rcu_read_unlock",
    "synchronize_rcu",

    "spin_lock",
    "spin_unlock",
  };

  constexpr static StringRef xadd = "__depsan_atomic_fetch_add_x";
  constexpr static StringRef Macros[] = {
    "__depsan_mb",
    "__depsan_rmb",
    "__depsan_wmb",
    "__depsan_mb_ba",
    "__depsan_mb_aa",
    "__depsan_barrier",
    "__depsan_s_release",
    "__depsan_l_acquire",
    "__depsan_atomic",
    "__depsan_ronce",
    "__depsan_wonce",
    "__depsan_lock",
    "__depsan_unlock",
    "__depsan_rcu_deref",
    "__depsan_rcu_assign",
    "__depsan_rcu_sync",
  };

private:
  void transform(Function &F);
  bool getAtomicAnnot(StringRef Name, const StringRef **Attr);
  bool getPrimitiveAnnot(StringRef Name, StringRef *Attr);
  bool begins(StringRef Name);

  bool guessIsStore(CallInst *CI);
  bool guessIsLoad(CallInst *CI);
};

//===----------------------------------------------------------------------===//
// The Annotation Removal
//===----------------------------------------------------------------------===//

class LKMMRemoveAnnotations : public PassInfoMixin<LKMMRemoveAnnotations> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);

private:
  void transform(Function &F);
};

//===----------------------------------------------------------------------===//
// The Actual Annotation Pass
//===----------------------------------------------------------------------===//

class LKMMAnnotateDepsPass : public AnalysisInfoMixin<LKMMAnnotateDepsPass> {
public:
  static AnalysisKey Key;
  friend AnalysisInfoMixin<LKMMAnnotateDepsPass>;

  typedef LKMMAnnotateDeps Result;
  Result run(Module &M, ModuleAnalysisManager &AM);

private:
  LKMMSearchPolicy Policy;
  static void annotateChain(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType DT, LKMMAnnotateDeps::DepMap *Result = nullptr);
};

//===----------------------------------------------------------------------===//
// The Hook Pass
//===----------------------------------------------------------------------===//

/// A wrapper around LKMMAnnotateDepsPass, that is able to be inserted into
/// the earliest hook point.
class LKMMAnnotateHook : public PassInfoMixin<LKMMAnnotateHook> {
public:
  LKMMAnnotateHook(const std::string OutPath) : OutPath(OutPath) {};

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {

    EnableStatistics(true);
    setupResultDir(OutPath);

    errs() << "\nvvvvv~~~~~~~~~ LKMMAnnotateHook ~~~~~vvvvv\n";
    auto &Annotations = AM.getResult<LKMMAnnotateDepsPass>(M);
    errs() << "\n^^^^^~~~~~~~~~ LKMMAnnotateHook ~~~~~^^^^^\n";
    return PreservedAnalyses::all();
  }

private:
  const std::string OutPath;
};

//===----------------------------------------------------------------------===//
// The Verification Pass
//===----------------------------------------------------------------------===//

class LKMMVerifyDepsPass : public PassInfoMixin<LKMMVerifyDepsPass> {
public:
  typedef LKMMAnnotateDeps Result;
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);

private:
  LKMMSearchPolicy Policy;
  void verifyChain(LKMMAnnotateDeps::DepMap *Pre, LKMMAnnotateDeps::DepMap *Post, Module &M);
  static void addChain(const SegmentID<0,0, LKMMSearchPolicy> &Seg, const DepType DT, LKMMAnnotateDeps::DepMap *Result);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_CUSTOMMEMDEP_H
