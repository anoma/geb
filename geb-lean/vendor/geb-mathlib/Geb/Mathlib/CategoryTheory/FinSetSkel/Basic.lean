/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.Vector.OfFn
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.Attr.Core

/-!
# `FinSetSkel`: a skeletal category of finite sets with vector morphisms

Objects are natural numbers; a morphism `X ⟶ Y` is a vector of `X.len`
indices into `Fin Y.len`. mathlib's `FintypeCat.Skeleton` has the same
objects up to the evident bijection with ℕ but takes morphisms to be
functions, whose equality is decidable only through
`Classical.choice`. Morphisms here are data: they can be
pattern-matched through `toVec`, serialised through `Repr`, and
compared through `DecidableEq`, all choice-free.

The objects are a one-field structure rather than `ULift ℕ` with `mk`
and `len` as definitions. A definition is opaque at reducible
transparency, so `Fin (mk n).len` would not match a lemma stated at
`Fin X.len` and no `simp` lemma would fire; the repair, marking `mk`
and `len` `@[reducible]`, cannot be confined to this module, and every
downstream construction is stated over `Fin X.len`. A structure
projection reduces by iota, which is available at reducible
transparency, so no reducibility attribute is needed anywhere.

The morphism representation is root-namespace `Vector`, not
`List.Vector`. The evidence runs both ways and is recorded so the
decision is not revisited on one side of it.
`Mathlib/Data/Vector/Defs.lean` says both "Any combination of reducing
the use of `List.Vector` in Mathlib, or modernising its API, would be
welcome" and "Typically, if you are doing programming or verification,
you will primarily use `Vector α n`, and if you are doing mathematics,
you may want to use `List.Vector α n` instead." On axioms
`List.Vector` is the cleaner: its `DecidableEq` is axiom-free where
root `Vector`'s costs `propext` and `Quot.sound`, and its `get_ofFn`
and `ofFn_get` are choice-free where root `Vector`'s are not, which
costs the five declarations of `Mathlib/Data/Vector/OfFn.lean`.
Root `Vector` is chosen because composition is the operation this
category exists to run: composing `f : X ⟶ Y` with `g : Y ⟶ Z` is
`O(X.len)` here and `O(X.len² + X.len · Y.len)` on the list-backed
representation, whose indexing is linear.

The API shape — a named `Hom`, an `ofVec`/`toVec` pair, `@[ext]`, the
`@[simp]` application lemmas, then `attribute [irreducible]` — is
mathlib's own, from `SimplexCategory`. Only the shape is borrowed:
`SimplexCategory.Hom` is a bundled monotone function and its
hom-`DecidableEq` depends on `Classical.choice`.

## Main definitions

* `FinSetSkel` — the objects.
* `FinSetSkel.Hom`, `FinSetSkel.Hom.ofVec`, `FinSetSkel.Hom.toVec` —
  the morphisms and their representation.
* `FinSetSkel.smallCategory` — the category instance.
* `FinSetSkel.ofIdxFun`, `FinSetSkel.toIdxFun` — the correspondence
  with lifted index functions, which the skeleton comparison uses.

## Main statements

* `FinSetSkel.hom_ext` — morphisms agreeing indexwise are equal.
* `FinSetSkel.id_get`, `FinSetSkel.comp_get` — the
  application-normal form for identity and composition.

## Implementation notes

The name records the skeletal model: `Skel` marks this as the skeletal
model of the category of finite sets, parallel to `FintypeCat.Skeleton`.

## References

* [nLabSkeletalCategory] — skeletal categories and the skeleton of a
  category. In the absence of the axiom of choice the entry notes that
  a weak skeleton is the more appropriate notion; the skeletality of
  this category is established in the wrapper module, which is where
  `Classical.choice` is permitted.

## Tags

category, finite set, skeleton, vector, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

/-- An object of the skeletal category of finite sets: a length. -/
@[ext] structure FinSetSkel : Type u where
  /-- The number of elements. -/
  len : ℕ
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprFinSetSkel.repr

namespace FinSetSkel

/-- The empty finite set is the default object. -/
instance inhabited : Inhabited FinSetSkel.{u} := ⟨⟨0⟩⟩

/-- A morphism is a vector of codomain indices, one per domain index.
The `ULift` is outside the vector, so index types stay at `Type 0`. -/
protected def Hom (X Y : FinSetSkel.{u}) : Type u :=
  ULift.{u} (Vector (Fin Y.len) X.len)

namespace Hom

variable {X Y Z : FinSetSkel.{u}}

/-- A morphism from its vector. -/
def ofVec (v : Vector (Fin Y.len) X.len) : FinSetSkel.Hom X Y :=
  ULift.up v

/-- The vector of a morphism. -/
def toVec (f : FinSetSkel.Hom X Y) : Vector (Fin Y.len) X.len := f.down

/-- `toVec` inverts `ofVec`. -/
@[simp] theorem toVec_ofVec (v : Vector (Fin Y.len) X.len) :
    (ofVec v).toVec = v := rfl

/-- `ofVec` inverts `toVec`. Unprovable after the seal, hence stated
here. -/
@[simp] theorem ofVec_toVec (f : FinSetSkel.Hom X Y) :
    ofVec f.toVec = f := rfl

/-- The identity morphism. -/
protected def id (X : FinSetSkel.{u}) : FinSetSkel.Hom X X :=
  ofVec (Vector.ofFnC _root_.id)

/-- Composition of morphisms. -/
protected def comp (f : FinSetSkel.Hom X Y) (g : FinSetSkel.Hom Y Z) :
    FinSetSkel.Hom X Z :=
  ofVec (Vector.ofFnC fun i ↦ g.toVec.get (f.toVec.get i))

/-- A morphism from a lifted index function. -/
def ofIdxFun' (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) :
    FinSetSkel.Hom X Y :=
  ofVec (Vector.ofFnC fun i ↦ (g (ULift.up i)).down)

/-- Pre-instance extensionality, from which `hom_ext` is derived. -/
theorem ext' {f g : FinSetSkel.Hom X Y}
    (h : ∀ i, f.toVec.get i = g.toVec.get i) : f = g :=
  congrArg ULift.up (Vector.ext fun i hi ↦ h ⟨i, hi⟩)

/-- The identity acts as the identity on indices. -/
theorem id_get' (X : FinSetSkel.{u}) (i : Fin X.len) :
    (Hom.id X).toVec.get i = i := Vector.get_ofFnC _ _

/-- Composition acts by composing index lookups. -/
theorem comp_get' (f : FinSetSkel.Hom X Y) (g : FinSetSkel.Hom Y Z)
    (i : Fin X.len) :
    (Hom.comp f g).toVec.get i = g.toVec.get (f.toVec.get i) :=
  Vector.get_ofFnC _ _

/-- A morphism built from an index function acts by that function. -/
theorem ofIdxFun'_get
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) (i : Fin X.len) :
    (ofIdxFun' g).toVec.get i = (g (ULift.up i)).down :=
  Vector.get_ofFnC _ _

end Hom

attribute [irreducible] FinSetSkel.Hom

/-- Objects and vector morphisms form a category. -/
instance smallCategory : SmallCategory FinSetSkel.{u} where
  Hom X Y := FinSetSkel.Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp f := Hom.ext' fun i ↦ by rw [Hom.comp_get', Hom.id_get']
  comp_id f := Hom.ext' fun i ↦ by rw [Hom.comp_get', Hom.id_get']
  assoc f g h := Hom.ext' fun i ↦ by
    rw [Hom.comp_get', Hom.comp_get', Hom.comp_get', Hom.comp_get']

/-- Morphisms agreeing at every index are equal. -/
@[ext] theorem hom_ext {X Y : FinSetSkel.{u}} {f g : X ⟶ Y}
    (h : ∀ i, f.toVec.get i = g.toVec.get i) : f = g := Hom.ext' h

/-- The categorical identity acts as the identity on indices. This
fixes the application-normal form for downstream statements. -/
@[simp] theorem id_get (X : FinSetSkel.{u}) (i : Fin X.len) :
    (𝟙 X : X ⟶ X).toVec.get i = i := Hom.id_get' X i

/-- Categorical composition acts by composing index lookups. This
fixes the application-normal form for downstream statements. -/
@[simp] theorem comp_get {X Y Z : FinSetSkel.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (i : Fin X.len) :
    (f ≫ g).toVec.get i = g.toVec.get (f.toVec.get i) :=
  Hom.comp_get' f g i

/-- Decidable equality of morphisms, pinned to the choice-free route.
Instance search does not unfold the `Hom` definition, so this does not
follow from the category instance; and `instDecidableEqOfLawfulBEq`
inhabits the same class through the choice-dependent
`Vector.instLawfulBEq`, so leaving the instance to search would let a
bump silently change its axioms. -/
instance decidableEqHom (X Y : FinSetSkel.{u}) : DecidableEq (X ⟶ Y) :=
  fun f g ↦ decidable_of_iff (f.toVec = g.toVec)
    ⟨fun h ↦ hom_ext fun i ↦ congrArg (·.get i) h,
     fun h ↦ congrArg Hom.toVec h⟩

/-- Morphisms are serialisable, through their vector. -/
instance reprHom (X Y : FinSetSkel.{u}) : Repr (X ⟶ Y) :=
  ⟨fun f n ↦ reprPrec f.toVec n⟩

/-- A morphism from a lifted index function. -/
def ofIdxFun {X Y : FinSetSkel.{u}}
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) : X ⟶ Y :=
  Hom.ofIdxFun' g

/-- A morphism built from an index function acts by that function. -/
@[simp] theorem ofIdxFun_get {X Y : FinSetSkel.{u}}
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) (i : Fin X.len) :
    (ofIdxFun g).toVec.get i = (g (ULift.up i)).down :=
  Hom.ofIdxFun'_get g i

/-- The lifted index function of a morphism. -/
def toIdxFun {X Y : FinSetSkel.{u}} (f : X ⟶ Y) :
    ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len) :=
  fun i ↦ ULift.up (f.toVec.get i.down)

/-- The index-function correspondence round-trips a morphism. -/
@[simp] theorem ofIdxFun_toIdxFun {X Y : FinSetSkel.{u}} (f : X ⟶ Y) :
    ofIdxFun (toIdxFun f) = f :=
  hom_ext fun i ↦ by simp only [ofIdxFun_get, toIdxFun]

/-- The index-function correspondence round-trips an index function. -/
@[simp] theorem toIdxFun_ofIdxFun {X Y : FinSetSkel.{u}}
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) :
    toIdxFun (ofIdxFun g) = g :=
  funext fun i ↦ by simp only [toIdxFun, ofIdxFun_get]

end FinSetSkel
