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
The signature morphism `natToBinHom : AlgSigHom natAlgSig binWordAlgSig` (zero
to the empty word, successor to the `false` letter) is exercised through the
carrier transport `freeAlgMap`, the image-point naturality
`recurse_freeAlgMap`, and the clause-wise transported doubling recurrence
`binDouble` evaluated at transported values.

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

/-- The `1 + X → 1 + 2X` signature morphism: zero to the empty word, successor
to the `false` letter. Not label-surjective — `some true` lies outside its
image. -/
def natToBinHom : AlgSigHom natAlgSig binWordAlgSig where
  onB b := match b with | false => none | true => some false
  ar_eq b := by cases b <;> rfl

-- The induced carrier transport sends the numeral `3` to a three-letter word.
#guard binCount (freeAlgMap natToBinHom (natToFreeAlg 0)) = 0
#guard binCount (freeAlgMap natToBinHom (natToFreeAlg 3)) = 3

-- Image-point naturality at a concrete recurrence: the letter count of a
-- transported word is the numeric reading of its source. `recurse_freeAlgMap`
-- reduces the left side to a pulled-back recurrence over `natAlgSig`, whose
-- steps a case split identifies with those of `freeAlgToNat`.
example (t : FreeAlg natAlgSig) :
    binCount (freeAlgMap natToBinHom t) = freeAlgToNat t := by
  unfold binCount freeAlgToNat
  rw [recurse_freeAlgMap]
  refine congrArg (fun g => FreeAlg.recurse g () t) ?_
  funext b q sub rec
  cases b <;> rfl

/-- The doubling step at a letter over `binWordAlgSig`: two `false` letters
onto the recursive result — the clause-wise transport along `natToBinHom` of
the `natAlgSig` doubling step `succ ∘ succ`. -/
def binDoubleStep : RIdent binWordAlgSig [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, binTmCons0 (binTmCons0 (Tm.var 0))⟩ finZeroElim

/-- The clause-wise transported doubling recurrence over `binWordAlgSig`: the
empty word at the nullary label and `binDoubleStep` at the image label
`some false`, with the non-image label `some true` completed by a copy of the
image-letter clause. At transported values the completion never fires
(`recurse_freeAlgMap`). -/
def binDouble : RIdent binWordAlgSig [RType.omega RType.o] RType.o :=
  RIdent.mrec [] RType.o
    (fun i => match i with | none => binLengthZero | some _ => binDoubleStep)

-- The transported doubling identifier interprets correctly at transported
-- values: at the transported numerals `0` and `3` it yields words of `0` and
-- `6` letters.
#guard binCount
  (binDouble.interp (binMrecEnv (freeAlgMap natToBinHom (natToFreeAlg 0)))) = 0
#guard binCount
  (binDouble.interp (binMrecEnv (freeAlgMap natToBinHom (natToFreeAlg 3)))) = 6

/-- A context of the higher-order syntactic category over `binWordAlgSig`. -/
abbrev binCtxO : RMRecCat binWordAlgSig := [RType.o]

/-- A context of the higher-order syntactic category over `treeAlgSig`. -/
abbrev treeCtxO : RMRecCat treeAlgSig := [RType.o]

-- The higher-order presentation instantiates: the `Category` instance of
-- `RMRecCat` fires at each new signature.
example : 𝟙 binCtxO ≫ 𝟙 binCtxO = 𝟙 binCtxO := Category.id_comp _
example : 𝟙 treeCtxO ≫ 𝟙 treeCtxO = 𝟙 treeCtxO := Category.id_comp _

end GebLeanTests.Ramified.AlgebrasTest
