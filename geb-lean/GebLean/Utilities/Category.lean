import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Category Theory Utilities

Convenience notation and helpers for working with categories.

## Main definitions

* `HomSet`: The data of a quiver (the Hom type family)
* `homSetOfQuiver`: Extract a `HomSet` from a `Quiver` typeclass instance
* `CompositionalStruct`: Composition of morphisms
* `AssociativityLaw`: Associativity law for composition
* `SemicategoryStruct`: Semicategory structure (composition and associativity)
* `IdentityStruct`: Identity morphisms for each object
* `identityStructOfReflQuiver`: Extract an `IdentityStruct` from a `ReflQuiver`
  typeclass instance
* `IdComp`: Law for composition after an identity
* `CompId`: Law for composition before an identity
* `IdentityLaws`: Identity laws for both directions of composition
* `CategoryOps`: Category operations (composition and identity)
* `categoryOpsOfCategoryStruct`: Extract `CategoryOps` from a `CategoryStruct`
  typeclass
* `CategoryLaws`: Category laws (associativity and identity laws)
* `CategoryData`: Category data (operations and laws)
* `categoryDataOfCategory`: Extract `CategoryData` from a `Category` typeclass
* `≅Cat`: Notation for isomorphisms between categories without explicit
  `Cat.of`
-/

namespace GebLean

open CategoryTheory

universe v u

/-- The data of a quiver: a family of types indexed by pairs of vertices. -/
abbrev HomSet (U : Type u) := U → U → Sort v

/-- Extract a `Quiver` typeclass instance from a `HomSet`. -/
instance {U : Type u} (hs : HomSet.{v, u} U) : Quiver.{v, u} U where
  Hom := hs

/-- Extract the `HomSet` from a `Quiver` typeclass instance. -/
abbrev homSetOfQuiver (U : Type u) [Quiver.{v, u} U] : HomSet.{v, u} U :=
  Quiver.Hom

/-- Compositional structure: composition of morphisms.

Note: Most presentations of category theory put composition in the opposite
order (e.g., `g ∘ f` for `f : a → b` and `g : b → c`). We follow the
convention of Lean's standard libraries, where composition is written
`f ≫ g` or `comp f g`, with the first morphism applied first. -/
abbrev CompositionalStruct {U : Type u} (hs : HomSet.{v, u} U) :=
  ∀ {a b c : U}, hs a b → hs b c → hs a c

/-- Associativity law for composition. -/
abbrev AssociativityLaw {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) :=
  ∀ {a b c d : U} (f : hs a b) (g : hs b c) (h : hs c d),
    comp (comp f g) h = comp f (comp g h)

/-- Semicategory structure: composition and associativity. -/
structure SemicategoryStruct (U : Type u) (hs : HomSet.{v, u} U) where
  /-- Composition of morphisms -/
  comp : CompositionalStruct hs
  /-- Associativity of composition -/
  assoc : AssociativityLaw hs comp

/-- Identity structure: identity morphisms for each object. -/
abbrev IdentityStruct {U : Type u} (hs : HomSet.{v, u} U) :=
  ∀ (a : U), hs a a

/-- Extract a `ReflQuiver` typeclass instance from a `HomSet` with identity
    structure. -/
instance {U : Type u} (hs : HomSet.{v, u} U) (ids : IdentityStruct hs) :
    ReflQuiver U where
  Hom := hs
  id := ids

/-- Extract the `IdentityStruct` from a `ReflQuiver` typeclass instance. -/
abbrev identityStructOfReflQuiver (U : Type u) [ReflQuiver U] :
    IdentityStruct (homSetOfQuiver U) :=
  ReflQuiver.id

/-- Composing any morphism after the identity gives the original morphism. -/
abbrev IdComp {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) :=
  ∀ {a b : U} (f : hs a b), comp (id a) f = f

/-- Composing any morphism before the identity gives the original morphism. -/
abbrev CompId {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) :=
  ∀ {a b : U} (f : hs a b), comp f (id b) = f

/-- Identity laws for both pre- and post-composition with identities. -/
structure IdentityLaws {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop where
  id_comp : IdComp hs comp id
  comp_id : CompId hs comp id

/-- Category operations: composition and identity morphisms. -/
structure CategoryOps {U : Type u} (hs : HomSet.{v, u} U) where
  /-- Composition of morphisms -/
  comp : CompositionalStruct hs
  /-- Identity morphisms -/
  id : IdentityStruct hs

/-- Build a `CategoryStruct` typeclass instance from category operations.
    Note: This only works when the HomSet is in Type (not general Sort). -/
instance {U : Type u} (hs : HomSet.{v + 1, u} U)
    (ops : CategoryOps hs) : CategoryStruct.{v, u} U where
  Hom := hs
  id := ops.id
  comp := ops.comp

/-- Extract the `CategoryOps` from a `CategoryStruct` typeclass instance. -/
abbrev categoryOpsOfCategoryStruct (U : Type u) [CategoryStruct.{v, u} U] :
    CategoryOps (homSetOfQuiver U) where
  comp := CategoryStruct.comp
  id := CategoryStruct.id

/-- Category laws: associativity and identity laws. -/
structure CategoryLaws {U : Type u} (hs : HomSet.{v, u} U)
    (ops : CategoryOps hs) : Prop where
  /-- Associativity of composition -/
  assoc : AssociativityLaw hs ops.comp
  /-- Identity laws -/
  id_laws : IdentityLaws hs ops.comp ops.id

/-- Category data: composition, associativity, identities, and
    identity laws. -/
structure CategoryData (U : Type u) (hs : HomSet.{v, u} U)
    extends CategoryOps hs where
  /-- Category laws -/
  laws : CategoryLaws hs toCategoryOps

namespace CategoryData

variable {U : Type u} {hs : HomSet.{v, u} U}

/-- Associativity law from category data. -/
@[reducible] def assoc (cs : CategoryData U hs) :
    AssociativityLaw hs cs.comp :=
  cs.laws.assoc

/-- Identity laws from category data. -/
@[reducible] def id_laws (cs : CategoryData U hs) :
    IdentityLaws hs cs.comp cs.id :=
  cs.laws.id_laws

end CategoryData

/-- Build a `Category` typeclass instance from category data.
    Note: This only works when the HomSet is in Type (not general Sort). -/
instance {U : Type u} (hs : HomSet.{v + 1, u} U)
    (data : CategoryData U hs) : Category.{v, u} U where
  Hom := hs
  id := data.id
  comp := data.comp
  id_comp := data.laws.id_laws.id_comp
  comp_id := data.laws.id_laws.comp_id
  assoc := data.laws.assoc

/-- Extract the `CategoryData` from a `Category` typeclass instance. -/
abbrev categoryDataOfCategory (U : Type u) [Category.{v, u} U] :
    CategoryData U (homSetOfQuiver U) where
  comp := CategoryStruct.comp
  id := CategoryStruct.id
  laws := {
    assoc := Category.assoc
    id_laws := {
      id_comp := Category.id_comp
      comp_id := Category.comp_id
    }
  }

section EqToHom

variable {C : Type u} [Category.{v, u} C]

/--
Composition of `eqToHom` with its symmetric gives identity.
-/
lemma eqToHom_comp_eqToHom_symm {X Y : C} (p : X = Y) :
    eqToHom p ≫ eqToHom p.symm = 𝟙 X := by
  cases p
  simp

/--
Composition of symmetric `eqToHom` with the original gives identity.
-/
lemma eqToHom_symm_comp_eqToHom {X Y : C} (p : X = Y) :
    eqToHom p.symm ≫ eqToHom p = 𝟙 Y := by
  cases p
  simp

/--
Two morphisms composed with `eqToHom` are equal if and only if
the first morphism composed with the combined equality is equal to the second.
-/
lemma comp_eqToHom_eq_comp_eqToHom {X Y Z W : C}
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y = W) (q : Z = W) :
    f ≫ eqToHom p = g ≫ eqToHom q ↔
    f ≫ eqToHom (p.trans q.symm) = g := by
  constructor
  · intro h
    calc f ≫ eqToHom (p.trans q.symm)
        = f ≫ (eqToHom p ≫ eqToHom q.symm) := by rw [← eqToHom_trans]
      _ = (f ≫ eqToHom p) ≫ eqToHom q.symm := by rw [Category.assoc]
      _ = (g ≫ eqToHom q) ≫ eqToHom q.symm := by rw [h]
      _ = g ≫ (eqToHom q ≫ eqToHom q.symm) := by rw [← Category.assoc]
      _ = g ≫ 𝟙 Z := by rw [eqToHom_comp_eqToHom_symm]
      _ = g := by rw [Category.comp_id]
  · intro h
    calc f ≫ eqToHom p
        = f ≫ (eqToHom (p.trans q.symm) ≫ eqToHom q) := by rw [← eqToHom_trans]
      _ = (f ≫ eqToHom (p.trans q.symm)) ≫ eqToHom q := by rw [Category.assoc]
      _ = g ≫ eqToHom q := by rw [h]

/--
Heterogeneous equality of morphisms is equivalent to equality after postcomposing
with `eqToHom`.
-/
lemma heq_iff_comp_eqToHom {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (p : Y = Z) :
    HEq f g ↔ f ≫ eqToHom p = g := by
  constructor
  · intro h
    cases p
    simp
    exact eq_of_heq h
  · intro h
    cases p
    simp at h
    exact heq_of_eq h

/--
Heterogeneous equality of morphisms is equivalent to equality after precomposing
with `eqToHom`.
-/
lemma heq_iff_eqToHom_comp {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) (p : X = Y) :
    HEq f g ↔ eqToHom p ≫ f = g := by
  constructor
  · intro h
    cases p
    simp
    exact eq_of_heq h
  · intro h
    cases p
    simp at h
    exact heq_of_eq h

/--
Heterogeneous equality of morphisms is equivalent to equality after precomposing
and postcomposing with `eqToHom`.
-/
lemma heq_iff_comp_eqToHom_comp {W X Y Z : C}
    (f : X ⟶ Y) (g : W ⟶ Z) (p : W = X) (q : Y = Z) :
    HEq f g ↔ eqToHom p ≫ f ≫ eqToHom q = g := by
  constructor
  · intro h
    -- f : X ⟶ Y and g : W ⟶ Z with f ≍ g
    -- First use heq_iff_eqToHom_comp to get eqToHom p ≫ f = intermediate
    -- Then use heq_iff_comp_eqToHom to handle the postcomposition
    cases p
    cases q
    simp
    exact eq_of_heq h
  · intro h
    cases p
    cases q
    simp at h
    exact heq_of_eq h

/--
Any `eqToHom` of a reflexive equality is equal to the identity.
By proof irrelevance, all proofs of `X = X` are equal to `rfl`, and
`eqToHom rfl = 𝟙 X`.
-/
lemma eqToHom_refl' {X : C} (p : X = X) : eqToHom p = 𝟙 X := by
  rw [Subsingleton.elim p rfl]
  simp

/--
Any two `eqToHom` terms of reflexive equalities are equal.
-/
lemma eqToHom_refl_eq {X Y : C} (p q : Eq.{u + 1} X Y) :
  Eq (eqToHom.{v, u} p) (eqToHom.{v, u} q) := by
    simp

/--
Proofs of symmetric equalities produce equal `eqToHom` terms.
-/
lemma eqToHom_sym_heq {X Y : C} (p : X = Y) (q : Y = X) :
  eqToHom p ≍ eqToHom q := by
    cases p ; cases q
    simp

lemma eqToHom_sym_eq {X Y : C} (p : X = Y) (q : Y = X) :
  eqToHom p = cast (by rw [p]) (eqToHom q) := by
    cases p ; cases q
    simp

end EqToHom

end GebLean

namespace CategoryTheory

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

end CategoryTheory
