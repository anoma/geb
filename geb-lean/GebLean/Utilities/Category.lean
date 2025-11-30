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
    (comp : CompositionalStruct hs) : Prop :=
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
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop :=
  ∀ {a b : U} (f : hs a b), comp (id a) f = f

/-- Composing any morphism before the identity gives the original morphism. -/
abbrev CompId {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop :=
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

universe v₂ u₂

variable {C : Type u} [Category.{v, u} C]
variable {D : Type u₂} [Category.{v₂, u₂} D]

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

/--
A functor maps `eqToHom` to `eqToHom` of the transported equality.
-/
@[simp]
lemma functor_map_eqToHom (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congrArg F.obj p) := by
  cases p
  simp

/--
A functor maps `eqToHom` of a symmetric equality to `eqToHom` of the symmetric
transported equality.
-/
@[simp]
lemma functor_map_eqToHom_symm (F : C ⥤ D) {X Y : C} (p : Y = X) :
    F.map (eqToHom p.symm) = eqToHom (congrArg F.obj p).symm := by
  cases p
  simp

/--
From HEq of morphisms with the same target, derive an equation with eqToHom.
This is useful for converting HEq hypotheses into equations that tactics like
`cat_disch` can use.
-/
lemma eq_of_heq_eqToHom {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (h : HEq f g)
    (p : X = Y) : f = eqToHom p ≫ g := by
  cases p
  simp [eq_of_heq h]

/--
From HEq of morphisms with the same source, derive an equation with eqToHom.
-/
lemma eq_of_heq_comp_eqToHom {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (h : HEq f g)
    (p : Y = Z) : f ≫ eqToHom p = g := by
  cases p
  simp [eq_of_heq h]

/--
A round-trip through `eqToHom` with an identity in the middle equals the identity.
-/
lemma eqToHom_comp_id_comp_eqToHom {X Y : C} (p : X = Y) (q : Y = X) :
    eqToHom p ≫ 𝟙 Y ≫ eqToHom q = 𝟙 X := by
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl']

/--
When applying F.map to an eqToHom morphism, composed with an eqToHom in the
target type, the result equals the original value if the composed proofs
yield a reflexive equality.
-/
lemma eqToHomMapEqToHomApp {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X) :
    F.map (eqToHom p) (eqToHom q a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant of `eqToHomMapEqToHomApp` where the equality proof for the morphism
uses `.symm`. This handles the case where the morphism `eqToHom p.symm` goes
in the opposite direction.
-/
lemma eqToHomMapEqToHomApp' {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (q : F.obj X = F.obj Y) (a : F.obj X) :
    F.map (eqToHom p.symm) (eqToHom q a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant where the element is from `F.obj Y` and we use the symmetric equality.
For `p : X = Y`, `q : F.obj X = F.obj Y`, and `a : F.obj Y`,
we have `F.map (eqToHom p) (eqToHom q.symm a) = a`.
-/
lemma eqToHomMapEqToHomApp'' {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (q : F.obj X = F.obj Y) (a : F.obj Y) :
    F.map (eqToHom p) (eqToHom q.symm a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
When applying F.map to an eqToHom morphism and an arbitrary eqToHom on
elements, if the element types are equal, the result equals the original.
This handles cases where the equality proofs are complex but the underlying
types are definitionally equal.
-/
lemma eqToHomMapEqToHomAppRefl {E : Type*} [Category E] (F : E ⥤ Type v)
    {X : E} (p : X = X) (q : F.obj X = F.obj X) (a : F.obj X) :
    F.map (eqToHom p) (eqToHom q a) = a := by
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Generalized version that handles arbitrary proof terms by using proof
irrelevance. Given an object `X` of type `T`, a function `f : T → E`,
and proofs that `f X = X'` and `f X = X''`, we can show that
`F.map (eqToHom p) (eqToHom q a) = a` where the proofs `p` and `q` might
be arbitrary (not rfl).

This is needed when `X'` and `X''` are definitionally equal after some
propositional reductions (like `comp_id`) but the proofs inside `eqToHom`
are not definitionally `rfl`.
-/
lemma eqToHomMapEqToHomApp_of_eq {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X)
    (hXY : X = Y) : F.map (eqToHom p) (eqToHom q a) = a := by
  subst hXY
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant that doesn't require `subst` to succeed. Uses proof irrelevance
to handle cases where both sides of the equality are complex expressions.
-/
lemma eqToHomMapEqToHomApp_of_heq {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X)
    (hXY : HEq X Y) : F.map (eqToHom p) (eqToHom q a) = a := by
  cases eq_of_heq hXY
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Most flexible variant: when the eqToHom proofs come from an expression that
can be proven equal by some auxiliary proof `h`, use this lemma.
This uses explicit type casting to make the proof term substitution work.
-/
lemma eqToHomMapEqToHomApp_of_cast {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X)
    (h : X = Y) : F.map (eqToHom p) (eqToHom q a) = a := by
  cases h
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant where we transport from `F.obj X` through `F.obj Y` back to `F.obj X`.
For `p : X = Y`, `q : F.obj X = F.obj Y`, and `a : F.obj X`,
we have `F.map (eqToHom p.symm) (cast q a) = a`.
The type cast `q` transports from `F.obj X` to `F.obj Y`.
-/
lemma eqToHomMapCastSymm {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (q : F.obj X = F.obj Y) (a : F.obj X) :
    F.map (eqToHom p.symm) (cast q a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply, cast_eq]

/--
General lemma: applying F.map to an eqToHom and eqToHom on elements
gives a round-trip result.
Given `p : Y = X`, we have a morphism `eqToHom p : Y ⟶ X` in E.
Applying F gives `F.map (eqToHom p) : F.obj Y → F.obj X`.
Given `q : F.obj X = F.obj Y`, we have `eqToHom q : F.obj X → F.obj Y`.
So the composition is: a : F.obj X → eqToHom q a : F.obj Y
                            → F.map (eqToHom p) (eqToHom q a) : F.obj X

This equals a when q = (congrArg F.obj p).symm.
-/
lemma eqToHomMapEqToHomAppRoundTrip {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (a : F.obj X) :
    F.map (eqToHom p) (eqToHom (congrArg F.obj p).symm a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Symmetric version of round-trip lemma.
Given `p : X = Y`, the map `F.map (eqToHom p.symm) : F.obj X → F.obj Y`
applied to `eqToHom (congrArg F.obj p) a` (where `a : F.obj Y`)
gives back `a`.
-/
lemma eqToHomMapEqToHomAppRoundTrip' {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (a : F.obj Y) :
    F.map (eqToHom p) (eqToHom (congrArg F.obj p.symm) a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

end EqToHom

end GebLean

namespace CategoryTheory

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

end CategoryTheory
