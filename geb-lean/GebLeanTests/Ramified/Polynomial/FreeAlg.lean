import GebLean
import GebLean.Ramified.Polynomial.FreeAlg

/-!
# Tests for `FreeAlg'` and its numeric carrier

Executable checks that the numeric carrier `natToFreeAlg'`/`freeAlgToNat'`
round-trips at a small sample value, and that the transported equivalence
`natFreeAlgEquiv'` agrees with it. Each check goes through a proven
`@[simp]` lemma (`freeAlgToNat'_natToFreeAlg'`, `natFreeAlgEquiv'_natToFreeAlg'`
respectively) rather than kernel reduction of the underlying slice `W`-tree,
whose fold mixes in proof terms that make direct reduction impractical.
-/

namespace GebLeanTests.Ramified.Polynomial.FreeAlg

open GebLean.Ramified.Polynomial

example : freeAlgToNat' (natToFreeAlg' 3) = 3 := by simp

example : natFreeAlgEquiv' (natToFreeAlg' 3) = 3 := by simp

-- The transported equivalence is definitionally the named composite.
example :
    natFreeAlgEquiv'
      = (freeAlgSliceEquiv GebLean.Ramified.natAlgSig).trans GebLean.Ramified.natFreeAlgEquiv :=
  natFreeAlgEquiv'_slice

end GebLeanTests.Ramified.Polynomial.FreeAlg
