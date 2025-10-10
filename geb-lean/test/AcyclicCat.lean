import GebLean.AcyclicCat
import Mathlib.Data.Fintype.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Equivalence

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
instance : TopologicalOrder WalkingParallelPairSemi where
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
## Categorical Isomorphism with Mathlib's WalkingParallelPair

We adjoin identities to our semicategory and show the result is isomorphic to
mathlib's `WalkingParallelPair`.
-/

open CategoryTheory
open Limits (WalkingParallelPair WalkingParallelPairHom)

/-- The walking parallel pair with identities adjoined. -/
def WalkingParallelPairCat : Type := WalkingParallelPairSemi

namespace WalkingParallelPairCat

/-- Morphisms: extend the semicategory morphisms with identities. -/
inductive Hom : WalkingParallelPairCat → WalkingParallelPairCat → Type
  | ofSemi {a b : WalkingParallelPairSemi} :
      WalkingParallelPairSemi.Hom a b → Hom a b
  | id (a : WalkingParallelPairCat) : Hom a a
  deriving DecidableEq

/-- The left morphism from the semicategory. -/
abbrev left : Hom WalkingParallelPairSemi.zero WalkingParallelPairSemi.one :=
  Hom.ofSemi WalkingParallelPairSemi.Hom.left

/-- The right morphism from the semicategory. -/
abbrev right : Hom WalkingParallelPairSemi.zero WalkingParallelPairSemi.one :=
  Hom.ofSemi WalkingParallelPairSemi.Hom.right

/-- Composition. There are no composable non-identity morphisms in the
    semicategory (all morphisms go from 0 to 1). -/
def comp : {a b c : WalkingParallelPairCat} → Hom a b → Hom b c → Hom a c
  | _, _, _, Hom.id _, g => g
  | _, _, _, f, Hom.id _ => f

/-- Category structure. -/
instance : Category WalkingParallelPairCat where
  Hom := Hom
  id := Hom.id
  comp := comp
  id_comp := by intro _ _ f; cases f <;> rfl
  comp_id := by intro _ _ f; cases f <;> rfl
  assoc := by
    intro W X Y Z f g h
    cases f with
    | id =>
      cases g with
      | id => cases h <;> rfl
      | ofSemi g' =>
        cases h with
        | id => rfl
        | ofSemi h' => cases g' <;> cases h'
    | ofSemi f' =>
      cases g with
      | id =>
        cases h <;> rfl
      | ofSemi g' =>
        -- f' : W.Hom X and g' : X.Hom Y, both in semicategory
        -- Since all semicategory morphisms go 0→1, these can't compose
        cases f' <;> cases g'

/-- Map an object from our category to mathlib's. -/
def toMathlibObj : WalkingParallelPairCat → WalkingParallelPair
  | WalkingParallelPairSemi.zero => WalkingParallelPair.zero
  | WalkingParallelPairSemi.one => WalkingParallelPair.one

/-- Map a morphism from our category to mathlib's. -/
def toMathlibMap : {X Y : WalkingParallelPairCat} →
    Hom X Y → (toMathlibObj X ⟶ toMathlibObj Y)
  | .zero, .one, Hom.ofSemi .left => WalkingParallelPairHom.left
  | .zero, .one, Hom.ofSemi .right => WalkingParallelPairHom.right
  | .zero, .zero, Hom.id .zero => WalkingParallelPairHom.id .zero
  | .one, .one, Hom.id .one => WalkingParallelPairHom.id .one

/-- Functor to mathlib's WalkingParallelPair. -/
def toMathlib : WalkingParallelPairCat ⥤ WalkingParallelPair where
  obj := toMathlibObj
  map := toMathlibMap
  map_id := by intro x; cases x <;> rfl
  map_comp := by
    intro X Y Z f g
    match f, g with
    | Hom.id _, Hom.id _ => cases X <;> rfl
    | Hom.id _, Hom.ofSemi g' => cases g' <;> rfl
    | Hom.ofSemi f', Hom.id _ => cases f' <;> rfl
    | Hom.ofSemi f', Hom.ofSemi g' => cases f' <;> cases g'

/-- Map an object from mathlib's category to ours. -/
def fromMathlibObj : WalkingParallelPair → WalkingParallelPairCat
  | WalkingParallelPair.zero => WalkingParallelPairSemi.zero
  | WalkingParallelPair.one => WalkingParallelPairSemi.one

/-- Map a morphism from mathlib's category to ours. -/
def fromMathlibMap : {X Y : WalkingParallelPair} →
    (X ⟶ Y) → Hom (fromMathlibObj X) (fromMathlibObj Y)
  | .zero, .one, .left => Hom.ofSemi .left
  | .zero, .one, .right => Hom.ofSemi .right
  | .zero, .zero, .id .zero => Hom.id .zero
  | .one, .one, .id .one => Hom.id .one

/-- Functor from mathlib's WalkingParallelPair. -/
def fromMathlib : WalkingParallelPair ⥤ WalkingParallelPairCat where
  obj := fromMathlibObj
  map := fromMathlibMap
  map_id := by intro x; cases x <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> try rfl
    · cases X <;> rfl

/-- The composition toMathlib ∘ fromMathlib is the identity functor. -/
theorem toMathlib_fromMathlib : toMathlib ⋙ fromMathlib = 𝟭 _ := by
  apply Functor.hext
  · intro x; cases x <;> rfl
  · intro x y f
    cases f with
    | ofSemi f' => cases f' <;> rfl  -- only left and right exist (zero → one)
    | id => cases x <;> rfl  -- id case

/-- The composition fromMathlib ∘ toMathlib is the identity functor. -/
theorem fromMathlib_toMathlib : fromMathlib ⋙ toMathlib = 𝟭 _ := by
  apply Functor.hext
  · intro x; cases x <;> rfl
  · intro x y f
    cases f with
    | left => rfl
    | right => rfl
    | id => cases x <;> rfl

/-- The two categories are isomorphic. -/
def isomorphism : WalkingParallelPairCat ≌ WalkingParallelPair where
  functor := toMathlib
  inverse := fromMathlib
  unitIso := eqToIso toMathlib_fromMathlib.symm
  counitIso := eqToIso fromMathlib_toMathlib
  functor_unitIso_comp := by
    intro X
    simp
    cases X <;> rfl

end WalkingParallelPairCat
