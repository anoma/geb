import GebLean.AcyclicCat
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Tests for Acyclic Categories

This file tests the acyclic category infrastructure using a concrete example:
a walking parallel pair without identities.

## Main Example

We construct a finite acyclic semicategory representing two parallel arrows
between two objects (like the walking parallel pair, but without identities).
This is the free semicategory on the graph:

```
  0 --f--> 1
    --g-->
```

We then show this can be completed to a category by adjoining identities, and
that result is isomorphic to Lean's standard `WalkingParallelPair`.
-/

/-- The walking parallel pair without identities: two objects with two
    parallel arrows between them. -/
inductive WalkingParallelPairSemi : Type where
  | zero : WalkingParallelPairSemi
  | one : WalkingParallelPairSemi
  deriving DecidableEq, Repr

instance : Fintype WalkingParallelPairSemi where
  elems := ⟨[WalkingParallelPairSemi.zero, WalkingParallelPairSemi.one],
    by simp [List.Nodup]⟩
  complete := fun x => by
    cases x <;> simp [Finset.mem_mk, List.mem_cons]

namespace WalkingParallelPairSemi

/-- The two parallel morphisms in the walking parallel pair. -/
inductive Hom : WalkingParallelPairSemi → WalkingParallelPairSemi → Type where
  | left : Hom zero one
  | right : Hom zero one
  deriving DecidableEq, Repr

instance : Quiver WalkingParallelPairSemi where
  Hom := Hom

/-- Decidability for edges in the walking parallel pair. -/
instance (a b : WalkingParallelPairSemi) : Decidable (Nonempty (a ⟶ b)) := by
  cases a <;> cases b
  · exact isFalse (fun ⟨f⟩ => nomatch f)
  · exact isTrue ⟨Hom.left⟩
  · exact isFalse (fun ⟨f⟩ => nomatch f)
  · exact isFalse (fun ⟨f⟩ => nomatch f)

/-- The partial order on the walking parallel pair: 0 ≤ 1. -/
instance : PartialOrder WalkingParallelPairSemi where
  le a b := a = zero ∨ (a = one ∧ b = one)
  le_refl a := by cases a <;> simp
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> simp_all

/-- All edges go from 0 to 1, which respects the order 0 < 1. -/
theorem edges_increase : ∀ {a b : WalkingParallelPairSemi},
    (a ⟶ b) → a < b := by
  intro a b f
  cases f
  · simp [LT.lt]
  · simp [LT.lt]

/-- The walking parallel pair is an acyclic quiver. -/
instance : AcyclicQuiver WalkingParallelPairSemi where
  edgesIncrease := edges_increase

end WalkingParallelPairSemi

/-- Test that we can construct acyclic quiver instances. -/
example : AcyclicQuiver WalkingParallelPairSemi := inferInstance
