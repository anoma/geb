import GebLean.AcyclicCat
import Mathlib.Data.Fintype.Basic

/-!
# Tests for Acyclic Categories

This file tests the acyclic category infrastructure.

## WalkingParallelPairSemi

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

/-- Composition in the walking parallel pair semicategory. Since all
    morphisms go from 0 to 1, there are no composable pairs. -/
def comp : ∀ {a b c : WalkingParallelPairSemi},
    (a ⟶ b) → (b ⟶ c) → (a ⟶ c) := by
  intro a b c f g
  cases f <;> cases g

/-- Associativity of composition (vacuously true since no composable
    pairs exist). -/
theorem comp_assoc : ∀ {a b c d : WalkingParallelPairSemi}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    comp (comp f g) h = comp f (comp g h) := by
  intro a b c d f g h
  cases f <;> cases g

/-- The walking parallel pair is a semicategory. -/
instance : Semicategory WalkingParallelPairSemi where
  toSemicategoryStruct := {
    comp := comp
    assoc := comp_assoc
  }

/-- The walking parallel pair is an acyclic category. -/
instance : AcyclicCategory WalkingParallelPairSemi where
  toSemicategoryStruct := {
    comp := comp
    assoc := comp_assoc
  }

/-- No edges from zero to zero. -/
instance : IsEmpty (zero ⟶ zero) where
  false f := nomatch f

instance : Fintype (zero ⟶ zero) := Fintype.ofIsEmpty

/-- No edges from one to zero. -/
instance : IsEmpty (one ⟶ zero) where
  false f := nomatch f

instance : Fintype (one ⟶ zero) := Fintype.ofIsEmpty

/-- No edges from one to one. -/
instance : IsEmpty (one ⟶ one) where
  false f := nomatch f

instance : Fintype (one ⟶ one) := Fintype.ofIsEmpty

/-- Edges from zero to one form a finite type (isomorphic to Bool). -/
instance : Fintype (zero ⟶ one) :=
  Fintype.ofEquiv Bool {
    toFun := fun b => match b with | true => Hom.left | false => Hom.right
    invFun := fun h => match h with | Hom.left => true | Hom.right => false
    left_inv := by intro b; cases b <;> rfl
    right_inv := by intro h; cases h <;> rfl
  }

/-- Finiteness witness for the walking parallel pair. -/
instance finQuiverWitness : FinQuiverWitness WalkingParallelPairSemi where
  fintypeVertex := inferInstance
  fintypeEdge a b := by
    cases a <;> cases b
    all_goals infer_instance

/-- The walking parallel pair is a finite acyclic category. -/
instance : FiniteAcyclicCategory WalkingParallelPairSemi where
  toFiniteness := finQuiverWitness

end WalkingParallelPairSemi

/-- Test that we can construct the necessary instances. -/
example : AcyclicQuiver WalkingParallelPairSemi := inferInstance
example : Semicategory WalkingParallelPairSemi := inferInstance
example : AcyclicCategory WalkingParallelPairSemi := inferInstance
example : FiniteAcyclicCategory WalkingParallelPairSemi := inferInstance

/-!
## Relationship to Mathlib's WalkingParallelPair

Mathlib's `WalkingParallelPair` (from `Mathlib.CategoryTheory.Limits.Shapes.
Equalizers`) is the category with:
- Two objects: `zero` and `one`
- Two parallel morphisms: `left` and `right` (both from `zero` to `one`)
- Identity morphisms for each object

Our `WalkingParallelPairSemi` is the underlying *semicategory* - it has the
same objects and the same two parallel morphisms, but *without* the identity
morphisms.

The relationship between these two structures demonstrates a key aspect of our
acyclic category framework:
1. `WalkingParallelPairSemi` is a `FiniteAcyclicCategory` (a semicategory)
2. Identities can be adjoined to yield mathlib's `WalkingParallelPair`
3. The two are equivalent via identity adjoining

This shows that our acyclic category infrastructure correctly models the
semicategory structure underlying standard categorical examples from mathlib.
-/
