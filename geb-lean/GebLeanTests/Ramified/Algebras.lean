import GebLean
import GebLean.Ramified.Algebras

/-!
# Tests for the canonical free-algebra instances

Executable checks over the polyadic binary-word algebra `binWordAlgSig`
(`1 + 2X`) and the binary-tree algebra `treeAlgSig` (`1 + X²`): the constructors
build carrier elements; the flat recurrences `binTail`/`treeLeftChild` and the
ramified monotonic recurrences `binLength`/`treeSize` interpret to the intended
destructor and measure at small inputs; and the numeric equivalence
`natFreeAlgEquiv` round trips `0` and `3`. The higher-order presentation is
exercised through the `Category` instance of `RMRecCat` at each new signature.

The interpretations land in the respective base carriers; the checks convert to
`Nat` via the letter count `binCount` and the node count `treeCount` so that
`#guard` decides `Nat` equalities.
-/

namespace GebLeanTests.Ramified.AlgebrasTest

open GebLean.Ramified CategoryTheory

/-- The number of letters of a binary word (a paramorphism over
`binWordAlgSig`). -/
def binCount (w : FreeAlg binWordAlgSig) : Nat :=
  FreeAlg.recurse (A := binWordAlgSig) (P := Unit)
    (fun b _ _sub rec => match b with
      | none => 0
      | some _ => rec ⟨0, Nat.zero_lt_one⟩ + 1) () w

/-- The number of internal nodes of a binary tree (a paramorphism over
`treeAlgSig`). -/
def treeCount (t : FreeAlg treeAlgSig) : Nat :=
  FreeAlg.recurse (A := treeAlgSig) (P := Unit)
    (fun b _ _sub rec => match b with
      | false => 0
      | true => rec ⟨0, by decide⟩ + rec ⟨1, by decide⟩ + 1) () t

/-- A two-letter binary word `false · true · ε`. -/
def sampleWord : FreeAlg binWordAlgSig := binCons true (binCons false binEmpty)

/-- A binary tree with two internal nodes. -/
def sampleTree : FreeAlg treeAlgSig :=
  treeNode (treeNode treeLeaf treeLeaf) treeLeaf

-- The binary-word constructors build words of the expected length.
#guard binCount binEmpty = 0
#guard binCount sampleWord = 2

-- The binary-tree constructors build trees of the expected node count.
#guard treeCount treeLeaf = 0
#guard treeCount (treeNode treeLeaf treeLeaf) = 1
#guard treeCount sampleTree = 2

/-- The recurrence-argument environment at `[Ω o]` over `binWordAlgSig`. -/
def binMrecEnv (w : FreeAlg binWordAlgSig) :
    ∀ i : Fin ([RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg binWordAlgSig)
        (([RType.omega RType.o] : Ctx RType).get i) :=
  Fin.cons w finZeroElim

/-- The recurrence-argument environment at `[o]` over `binWordAlgSig`. -/
def binFrecEnv (w : FreeAlg binWordAlgSig) :
    ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg binWordAlgSig) (([RType.o] : Ctx RType).get i) :=
  Fin.cons w finZeroElim

/-- The recurrence-argument environment at `[Ω o]` over `treeAlgSig`. -/
def treeMrecEnv (t : FreeAlg treeAlgSig) :
    ∀ i : Fin ([RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg treeAlgSig)
        (([RType.omega RType.o] : Ctx RType).get i) :=
  Fin.cons t finZeroElim

/-- The recurrence-argument environment at `[o]` over `treeAlgSig`. -/
def treeFrecEnv (t : FreeAlg treeAlgSig) :
    ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg treeAlgSig) (([RType.o] : Ctx RType).get i) :=
  Fin.cons t finZeroElim

-- The word length counts the letters: `length (false · true · ε) = 2`.
#guard binCount (binLength.interp (binMrecEnv sampleWord)) = 2

-- The first-letter destructor drops one letter: `tail (false · true · ε)` has
-- one letter.
#guard binCount (binTail.interp (binFrecEnv sampleWord)) = 1

-- The tree-size recurrence rebuilds the tree, preserving the node count.
#guard treeCount (treeSize.interp (treeMrecEnv sampleTree)) = 2

-- The left-child destructor returns the left subtree, with one node.
#guard treeCount (treeLeftChild.interp (treeFrecEnv sampleTree)) = 1

-- The numeric equivalence round trips `0` and `3`.
#guard natFreeAlgEquiv (natFreeAlgEquiv.symm 0) = 0
#guard natFreeAlgEquiv (natFreeAlgEquiv.symm 3) = 3
#guard freeAlgToNat (natFreeAlgEquiv.symm (natFreeAlgEquiv (natToFreeAlg 3))) = 3

/-- A context of the higher-order syntactic category over `binWordAlgSig`. -/
abbrev binCtxO : RMRecCat binWordAlgSig := [RType.o]

/-- A context of the higher-order syntactic category over `treeAlgSig`. -/
abbrev treeCtxO : RMRecCat treeAlgSig := [RType.o]

-- The higher-order presentation instantiates: the `Category` instance of
-- `RMRecCat` fires at each new signature.
example : 𝟙 binCtxO ≫ 𝟙 binCtxO = 𝟙 binCtxO := Category.id_comp _
example : 𝟙 treeCtxO ≫ 𝟙 treeCtxO = 𝟙 treeCtxO := Category.id_comp _

end GebLeanTests.Ramified.AlgebrasTest
