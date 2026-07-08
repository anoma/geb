/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Presheaf-domain polynomial functors (constructive core)

A presheaf-domain polynomial functor extends a `SliceDomPFunctor` on the
objects of a category `I` with a contravariant `I`-action on arities: for
each shape `a`, the assignment `i ↦ Direction a i` extends to a presheaf on
`I` via a restriction map `directionRestr a f`. This file is the p.r.a. (parametric
right adjoint) construction restricted to the domain side; the full
categorical packaging appears in sibling modules. Every declaration here is
`Classical.choice`-free; the categorical packaging that pulls in
`Classical.choice` from mathlib is in the sibling `Presheaf.Functor` module.

The design uses the option-(A) fibre encoding: directions over `i` are
`SliceDomPFunctor.Direction a i = Subtype (DirectionOver a i)`, the fibre of
the direction-input map `rCurried a` over `i`. The `directionRestr` field
reindexes these fibres contravariantly.

## Main definitions

* `PresheafDomPFunctorData` — the operations: a `SliceDomPFunctor` with a
  restriction map `directionRestr`.
* `PresheafDomPFunctorData.DirectionRestrId` / `DirectionRestrComp` — named law `Prop`s.
* `PresheafDomPFunctorData.IsFunctorial` — the functor laws bundled.
* `PresheafDomPFunctorData.elemProj` — projection from the presheaf's elements
  `Σ i, Z.obj ⟨i⟩` to the base `I`.
* `PresheafDomPFunctorData.value` — the `Z`-value the assignment gives a
  direction.
* `PresheafDomPFunctorData.IsNatural` — naturality of the direction
  assignment with respect to `directionRestr` and `Z.map`.
* `PresheafDomPFunctorData.obj` — the functor's value on a presheaf `Z`.
* `PresheafDomPFunctorData.elemMap` — the action of a presheaf morphism `α` on
  the categories of elements, `el(Z) ⟶ el(Z')`.
* `PresheafDomPFunctorData.map` — the action on morphisms of input presheaves
  (the bare `NatTrans`).
* `PresheafDomPFunctor` — the bundle: operations with a functoriality proof.
* `PresheafPFunctorData` — the full operations: the dom operations and the
  shape-output map, with the `J`-action `shapeRestr` on shapes and the arity
  reindexing `reindex`.
* `PresheafPFunctorData.ShapeRestrId` / `ShapeRestrComp` / `ReindexNaturality` /
  `ReindexId` / `ReindexComp` — the named `J`-side law `Prop`s. `ReindexId`
  and `ReindexComp` are parameterized on the relevant `shapeRestr` law, whose
  content supplies the non-definitional source-type transport.
* `PresheafPFunctorData.IsFunctorial` — the full functor laws bundled.
* `PresheafPFunctor` — the full bundle: operations with a functoriality proof.
* `PresheafPFunctor.objRestrElt` / `objRestr` — the restriction action of the
  output presheaf on a `J`-morphism, on the dom value and on `F.obj Z`.
* `PresheafPFunctor.objPresheaf` — the output presheaf `T(Z) : Jᵒᵖ ⥤ Type`, a
  `Functor` value with `map_id` / `map_comp` discharged from `isFunctorial`.
* `PresheafPFunctor.mapPresheaf` — the presheaf morphism
  `objPresheaf Z ⟶ objPresheaf Z'` induced by a morphism of input presheaves.

## Main statements

* `PresheafDomPFunctorData.map_id` / `map_comp` — functoriality of the
  domain-restricted action in the input presheaf.
* `PresheafPFunctor.map_objRestr` — the domain map is natural with respect
  to the output presheaf's restriction maps.
* `PresheafPFunctor.objRestrElt_id` / `objRestrElt_comp` — the identity and
  composition laws of the element-level restriction `objRestrElt`.

## Notation

The declaration docstrings use the parametric-right-adjoint notation of
[Weber2007]:

* `T1` — the shape presheaf `j ↦ Shape j` on `J`, with `shapeRestr` as its
  restriction maps.
* `E_T(a)` — the arity presheaf `i ↦ Direction a.1 i` of a shape `a` on `I`,
  with `directionRestr` as its restriction maps.
* `el(T1)` — the category of elements of `T1`: objects are pairs `(j, a)` with
  `a : Shape j`. As `T1` is a presheaf, its elements vary contravariantly, so a
  morphism `(j, a) ⟶ (j', a')` is backed by a `J`-morphism `g : j' ⟶ j` (the
  opposite direction) with `shapeRestr g a = a'`. The arity assignment `a ↦ E_T(a)`
  is therefore contravariant on `el(T1)` (a functor on `el(T1)ᵒᵖ`); `reindex g a`
  is its action, the presheaf morphism `E_T(shapeRestr g a) ⟶ E_T(a)`.

## Implementation notes

The morphism universes of `I` and `J` are named `vI` and `vJ` (via
`[Category.{vI} I]` / `[Category.{vJ} J]`), and every parent and presheaf-functor
argument pins its universes, so no declaration's signature carries an auto-bound
`u_N` variable. `PresheafDomPFunctorData` uses
`extends SliceDomPFunctor.{uA, uB} I` with pinned universes (load-bearing for a
later diamond via `PresheafDomPFunctorData` and `SlicePFunctor`); pinned
references to it elsewhere take the synthesized order
`PresheafDomPFunctorData.{uI, uA, uB, vI}`.

The `@[nolint checkUnivs]` attribute suppresses the
`checkUnivs` warning on the inherited `PFunctor` universes `uA`/`uB`: they are
the two `Type` universes of the `PFunctor` parent and appear only together in
the result `max`, so the linter flags them as a pair that could be unified. The
warning is independent of the morphism universe: naming `vI` does not remove it,
and it fires even on a `Category`-free `PFunctor`-extending structure. This is
the same situation mathlib suppresses in `PFunctor`.

`PresheafPFunctorData` is the diamond
`extends PresheafDomPFunctorData.{uI, uA, uB, vI} I,
SlicePFunctor.{uA, uB, uI, uJ} I J`,
which shares the single `SliceDomPFunctor` parent. The `reindex` laws
`ReindexId` / `ReindexComp` are stated in homogeneous-`Eq` form, parameterized
on a `shapeRestr` law, rather than as bare `Prop`s: comparing `reindex` along
`𝟙` (resp. a composite) with the identity (resp. the composite of `reindex`es)
requires a source-type transport whose target equality
(`shapeRestr (𝟙 j) a = a`, resp. `shapeRestr (h ≫ g) a = shapeRestr h (shapeRestr g a)`)
is `ShapeRestrId` (resp. `ShapeRestrComp`) content, not definitional. They are
therefore parameterized on that law and apply it via `cast`; `IsFunctorial`
supplies the proof from its earlier `shapeRestr_id` / `shapeRestr_comp` fields. A
heterogeneous-`Eq` formulation would avoid the parameter at the cost of
`rw`-convenience and mathlib idiom.

## References

* [Weber2007]
* [nLabParametricRightAdjoint]
* [GambinoHyland2004]
* [GambinoKock2013]

## Tags

polynomial functor, presheaf, parametric right adjoint, p.r.a.,
PFunctor, restriction map
-/

public section

open CategoryTheory

universe uI uJ uA uB uZ u v vI vJ uX

/-- Operations of a presheaf-domain polynomial functor over `I`: a
`SliceDomPFunctor` on `I`'s objects, with the contravariant `I`-action
`directionRestr` making each arity a presheaf on `I`. -/
@[nolint checkUnivs]
structure PresheafDomPFunctorData (I : Type uI) [Category.{vI} I] :
    Type (max (uA + 1) (uB + 1) uI vI)
    extends SliceDomPFunctor.{uA, uB} I where
  /-- The arity-presheaf restriction: for a morphism `i' ⟶ i`, reindex
  directions of shape `a` over `i` to directions over `i'`. -/
  directionRestr : ∀ (a : toPFunctor.A) ⦃i i' : I⦄, (i' ⟶ i) →
      toSliceDomPFunctor.Direction a i → toSliceDomPFunctor.Direction a i'

namespace PresheafDomPFunctorData

/-- `directionRestr` preserves identities. -/
@[expose] def DirectionRestrId {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I) : Prop :=
  ∀ (a : F.A) (i : I), F.directionRestr a (𝟙 i) = id

/-- `directionRestr` reverses composition: `directionRestr a (g ≫ f) = directionRestr a g ∘
directionRestr a f`. -/
@[expose] def DirectionRestrComp {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I) : Prop :=
  ∀ (a : F.A) ⦃i i' i'' : I⦄ (f : i' ⟶ i) (g : i'' ⟶ i'),
      F.directionRestr a (g ≫ f) = F.directionRestr a g ∘ F.directionRestr a f

/-- The arities form presheaves on `I`: `directionRestr` satisfies the functor
laws. -/
structure IsFunctorial {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I) : Prop where
  /-- Identity law for `directionRestr`. -/
  directionRestr_id : F.DirectionRestrId
  /-- Composition law for `directionRestr`. -/
  directionRestr_comp : F.DirectionRestrComp

/-- Total-space projection of a presheaf `Z` on `I` to objects of `I`. -/
@[expose] def elemProj {I : Type uI} [Category.{vI} I] (Z : Iᵒᵖ ⥤ Type uZ) :
    (Σ i : I, Z.obj ⟨i⟩) → I :=
  Sigma.fst

/-- The `Z`-value a slice element `x` over `elemProj Z` gives a direction
`b` of shape `x.1.1` over `i`: the `Z`-value `(x.1.2 b.1).2`, cast along the
compatibility of `x` and the constraint condition on `b` to `Z.obj ⟨i⟩`. -/
@[expose] def value {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I)
    {Z : Iᵒᵖ ⥤ Type uZ} (x : F.toSliceDomPFunctor.Obj (elemProj Z)) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Direction x.1.1 i) : Z.obj ⟨i⟩ :=
  cast (congrArg (fun k : I => Z.obj ⟨k⟩)
    (((F.compatible_iff (elemProj Z) x.1.1 x.1.2).mp x.2 b.1).trans b.2)) (x.1.2 b.1).2

/-- The direction-assignment of `x` is a natural transformation `E_T(a) ⟶ Z`,
where `a := x.1.1`: for every `f : i' ⟶ i` and direction `b` over `i`, the
component assigned to `directionRestr a f b` equals `Z.map f.op` applied to `value x b`. -/
@[expose] def IsNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I)
    {Z : Iᵒᵖ ⥤ Type uZ} (x : F.toSliceDomPFunctor.Obj (elemProj Z)) : Prop :=
  ∀ ⦃i i' : I⦄ (f : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
    F.value x (F.directionRestr x.1.1 f b) = Z.map f.op (F.value x b)

/-- The value of the presheaf-domain functor on `Z`: the `IsNatural` subtype
of the slice object on the total-space projection `elemProj Z`. -/
@[expose] def obj {I : Type uI} [Category.{vI} I] (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I)
    (Z : Iᵒᵖ ⥤ Type uZ) : Type (max uI uZ uA uB) :=
  { x : F.toSliceDomPFunctor.Obj (elemProj Z) // F.IsNatural x }

/-- The shape of an element of `F.obj Z`: its underlying `PFunctor` shape. -/
@[expose, reducible] def obj.shape {I : Type uI} [Category.{vI} I]
    {F : PresheafDomPFunctorData.{uI, uA, uB, vI} I} {Z : Iᵒᵖ ⥤ Type uZ} (x : F.obj Z) : F.A :=
  x.1.1.1

/-- A component of a natural transformation commutes with the reindexing
`cast` along an equality of base points. -/
private theorem app_cast {I : Type uI} [Category.{vI} I] {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : NatTrans Z Z') {k i : I} (e : k = i) (z : Z.obj ⟨k⟩) :
    cast (congrArg (fun k : I => Z'.obj ⟨k⟩) e) (α.app ⟨k⟩ z) =
      α.app ⟨i⟩ (cast (congrArg (fun k : I => Z.obj ⟨k⟩) e) z) := by
  cases e
  rfl

/-- The action of a natural transformation `α : Z ⟶ Z'` on the categories of
elements, `el(Z) ⟶ el(Z')`: `⟨i, z⟩ ↦ ⟨i, α.app ⟨i⟩ z⟩`. It preserves the
base-point projection `elemProj`, so it is a slice morphism over `elemProj`. -/
@[expose] def elemMap {I : Type uI} [Category.{vI} I] {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : NatTrans Z Z') : (Σ i : I, Z.obj ⟨i⟩) → (Σ i : I, Z'.obj ⟨i⟩) :=
  fun p => ⟨p.1, α.app ⟨p.1⟩ p.2⟩

/-- The `Z'`-component the image under `α` of a slice element assigns to a
direction is `α.app` of the `Z`-component the original assigns to it. -/
private theorem value_map {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I)
    {Z Z' : Iᵒᵖ ⥤ Type uZ} (α : NatTrans Z Z')
    (x : F.toSliceDomPFunctor.Obj (elemProj Z)) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Direction (F.toSliceDomPFunctor.map (p' := elemProj Z')
      (elemMap α) rfl x).1.1 i) :
    F.value (F.toSliceDomPFunctor.map (p' := elemProj Z')
      (elemMap α) rfl x) b =
      α.app ⟨i⟩ (F.value x b) :=
  app_cast α (((F.compatible_iff (elemProj Z) x.1.1 x.1.2).mp x.2 b.1).trans b.2) _

/-- Action on a morphism of input presheaves (the bare `NatTrans`). -/
@[expose] def map {I : Type uI} [Category.{vI} I] (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I)
    {Z Z' : Iᵒᵖ ⥤ Type uZ} (α : NatTrans Z Z') :
    F.obj Z → F.obj Z' :=
  fun x => ⟨F.toSliceDomPFunctor.map
    (elemMap α) rfl x.1, by
    intro i i' f b
    simp only [value_map]
    refine (congrArg (fun w => α.app ⟨i'⟩ w) (x.2 f b)).trans ?_
    exact FunctorToTypes.naturality _ _ α f.op _⟩

/-- Functoriality in the input presheaf: the identity transformation acts as
the identity. -/
theorem map_id {I : Type uI} [Category.{vI} I] (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I)
    (Z : Iᵒᵖ ⥤ Type uZ) :
    F.map { app := fun i => 𝟙 (Z.obj i), naturality := fun _ _ _ => rfl } =
      (id : F.obj Z → F.obj Z) := by
  funext x
  exact Subtype.ext (congrFun (F.toSliceDomPFunctor.map_id (elemProj Z)) x.1)

/-- Functoriality in the input presheaf: the vertical composite of
transformations acts as the composite of the actions. -/
theorem map_comp {I : Type uI} [Category.{vI} I] (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I)
    {Z Z' Z'' : Iᵒᵖ ⥤ Type uZ} (α : NatTrans Z Z')
    (β : NatTrans Z' Z'') :
    F.map { app := fun i => α.app i ≫ β.app i, naturality := fun _ _ g =>
        (by rw [← Category.assoc, α.naturality, Category.assoc, β.naturality,
          ← Category.assoc]) } =
      F.map β ∘ F.map α := by
  funext x
  exact Subtype.ext (congrFun (F.toSliceDomPFunctor.map_comp (p := elemProj Z) (p' := elemProj Z')
    (p'' := elemProj Z'')
    (elemMap α)
    (elemMap β)
    rfl rfl) x.1)

end PresheafDomPFunctorData

/-- A presheaf-domain polynomial functor: operations together with a
proof they are functorial. Its action is a functor `(Iᵒᵖ ⥤ Type) ⥤ Type`
(packaged in `Presheaf.Functor`). -/
@[nolint checkUnivs]
structure PresheafDomPFunctor (I : Type uI) [Category.{vI} I] :
    Type (max (uA + 1) (uB + 1) uI vI)
    extends PresheafDomPFunctorData.{uI, uA, uB, vI} I where
  /-- Proof the operations are functorial. -/
  isFunctorial : toPresheafDomPFunctorData.IsFunctorial

attribute [ext] PresheafDomPFunctorData PresheafDomPFunctor

/-- Operations of a presheaf polynomial functor `(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)`:
the dom operations plus the shape-output map `q` (via `SlicePFunctor`), the
`J`-action `shapeRestr` on shapes, and the arity reindexing `reindex`. -/
@[nolint checkUnivs]
structure PresheafPFunctorData (I : Type uI) [Category.{vI} I]
    (J : Type uJ) [Category.{vJ} J] : Type (max (uA + 1) (uB + 1) uI uJ vI vJ)
    extends PresheafDomPFunctorData.{uI, uA, uB, vI} I, SlicePFunctor.{uA, uB, uI, uJ} I J where
  /-- The shape-presheaf restriction: for `g : j' ⟶ j`, reindex shapes over
  `j` to shapes over `j'`. -/
  shapeRestr : ∀ ⦃j j' : J⦄ (_g : j' ⟶ j),
      toSlicePFunctor.Shape j → toSlicePFunctor.Shape j'
  /-- The arity reindexing along a `J`-morphism: a presheaf morphism
  `E_T(shapeRestr g a) ⟶ E_T(a)`. -/
  reindex : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : toSlicePFunctor.Shape j) ⦃i : I⦄,
      toSliceDomPFunctor.Direction (shapeRestr g a).1 i →
        toSliceDomPFunctor.Direction a.1 i

/-- The shape-output-map view of the operations: the shared `SliceDomPFunctor`
together with the shape-output map `q`. The diamond merges the
`SliceDomPFunctor` parent, so this view shares its components with
`toPresheafDomPFunctorData`. -/
add_decl_doc PresheafPFunctorData.toSlicePFunctor

namespace PresheafPFunctorData

/-- `shapeRestr` preserves identities. -/
@[expose] def ShapeRestrId {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) : Prop :=
  ∀ (j : J), F.shapeRestr (𝟙 j) = id

/-- `shapeRestr` reverses composition: `shapeRestr (h ≫ g) = shapeRestr h ∘ shapeRestr g`. -/
@[expose] def ShapeRestrComp {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) : Prop :=
  ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j'),
      F.shapeRestr (h ≫ g) = F.shapeRestr h ∘ F.shapeRestr g

/-- Each `reindex g a` commutes with `directionRestr` (a presheaf morphism
`E_T(shapeRestr g a) ⟶ E_T(a)`): for `f : i' ⟶ i`,
`directionRestr a.1 f ∘ reindex g a = reindex g a ∘ directionRestr (shapeRestr g a).1 f`.
Ordinary fibre maps only; no `shapeRestr` transport. -/
@[expose] def ReindexNaturality {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) : Prop :=
  ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) ⦃i i' : I⦄ (f : i' ⟶ i),
    F.directionRestr a.1 f ∘ F.reindex g a (i := i) =
      F.reindex g a (i := i') ∘ F.directionRestr (F.shapeRestr g a).1 f

/-- `reindex (𝟙 j) a` is the identity, modulo the transport of its source
along `ShapeRestrId` at `j` (`shapeRestr (𝟙 j) a = a`). The transport is the
`cast` of `b` along `congrArg (fun s => Direction s.1 i) (congrFun (hti j) a)`.
Parameterized on the identity law `hti` because that source-type equality is
not definitional. -/
@[expose] def ReindexId {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) (hti : F.ShapeRestrId) : Prop :=
  ∀ ⦃j : J⦄ (a : F.Shape j) ⦃i : I⦄ (b : F.Direction (F.shapeRestr (𝟙 j) a).1 i),
    F.reindex (𝟙 j) a b =
      cast (congrArg (fun s : F.Shape j => F.Direction s.1 i) (congrFun (hti j) a)) b

/-- For `g : j' ⟶ j`, `h : j'' ⟶ j'`,
`reindex (h ≫ g) a = reindex g a ∘ reindex h (shapeRestr g a)` (`g` is the
outer factor), modulo the transport of the source along `ShapeRestrComp`
(`shapeRestr (h ≫ g) a = shapeRestr h (shapeRestr g a)`). The transport is the `cast`
of `b` along `congrArg (fun s => Direction s.1 i) (congrFun (htc g h) a)`.
Parameterized on the composition law `htc` because that source-type equality is
not definitional. -/
@[expose] def ReindexComp {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) (htc : F.ShapeRestrComp) : Prop :=
  ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j') (a : F.Shape j) ⦃i : I⦄
    (b : F.Direction (F.shapeRestr (h ≫ g) a).1 i),
    F.reindex (h ≫ g) a b =
      F.reindex g a (F.reindex h (F.shapeRestr g a)
        (cast (congrArg (fun s : F.Shape j'' => F.Direction s.1 i)
          (congrFun (htc g h) a)) b))

/-- All functor laws: the dom laws plus the `J`-side laws making `T1` a
presheaf and `E_T` a functor on `el(T1)`. The `shapeRestr` laws precede the
`reindex` laws because `reindex_id` / `reindex_comp` are stated relative to
`shapeRestr_id` / `shapeRestr_comp`. -/
structure IsFunctorial {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) : Prop
    extends F.toPresheafDomPFunctorData.IsFunctorial where
  /-- Identity law for `shapeRestr`. -/
  shapeRestr_id : F.ShapeRestrId
  /-- Composition law for `shapeRestr`. -/
  shapeRestr_comp : F.ShapeRestrComp
  /-- `reindex` is a presheaf morphism (commutes with `directionRestr`). -/
  reindex_naturality : F.ReindexNaturality
  /-- Identity law for `reindex`, relative to `shapeRestr_id`. -/
  reindex_id : F.ReindexId shapeRestr_id
  /-- Composition law for `reindex`, relative to `shapeRestr_comp`. -/
  reindex_comp : F.ReindexComp shapeRestr_comp

end PresheafPFunctorData

/-- A presheaf polynomial functor: operations together with a proof they are
functorial. Its action is a functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`. -/
@[nolint checkUnivs]
structure PresheafPFunctor (I : Type uI) [Category.{vI} I]
    (J : Type uJ) [Category.{vJ} J] : Type (max (uA + 1) (uB + 1) uI uJ vI vJ)
    extends PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J where
  /-- Proof the operations are functorial. -/
  isFunctorial : toPresheafPFunctorData.IsFunctorial

attribute [ext] PresheafPFunctorData
  PresheafPFunctor

namespace PresheafPFunctor

/-- The slice element underlying the restriction action of `objPresheaf` on a
`J`-morphism `g`, for a projection `p : X → I`: restrict the shape along
`shapeRestr g` and reindex the direction-assignment along `reindex g`. -/
@[expose] def objRestrElt {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {X : Type uX} {p : X → I}
    ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj p) (hq : F.q x.1.1 = j) :
    F.toSliceDomPFunctor.Obj p :=
  ⟨⟨(F.shapeRestr g ⟨x.1.1, hq⟩).1,
      fun b' => x.1.2 (F.reindex g ⟨x.1.1, hq⟩ (i := F.rCurried _ b') ⟨b', rfl⟩).1⟩,
    (F.compatible_iff _ _ _).mpr fun b' =>
      ((F.compatible_iff _ _ _).mp x.2
        (F.reindex g ⟨x.1.1, hq⟩ (i := F.rCurried _ b') ⟨b', rfl⟩).1).trans
        (F.reindex g ⟨x.1.1, hq⟩ (i := F.rCurried _ b') ⟨b', rfl⟩).2⟩

/-- The component the restricted element assigns to a direction is the component
the original assigns to the direction's `reindex`. -/
private theorem value_objRestrElt {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uZ} ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)) (hq : F.q x.1.1 = j)
    ⦃i : I⦄ (b : F.Direction (F.objRestrElt g x hq).1.1 i) :
    F.value (F.objRestrElt g x hq) b = F.value x (F.reindex g ⟨x.1.1, hq⟩ b) := by
  obtain ⟨b1, rfl⟩ := b
  rfl

/-- The restriction action of `objPresheaf` on a `J`-morphism `g`, at the level
of `F.obj Z`: `objRestrElt` packaged with its naturality, supplied by
`reindex_naturality`. -/
@[expose] def objRestr {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z : Iᵒᵖ ⥤ Type uZ} ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.obj Z) (hq : F.q x.shape = j) : F.obj Z :=
  ⟨F.objRestrElt g x.1 hq, by
    intro i i' f b
    rw [F.value_objRestrElt, F.value_objRestrElt,
      show F.reindex g ⟨x.shape, hq⟩ (F.directionRestr (F.objRestrElt g x.1 hq).1.1 f b)
          = F.directionRestr x.shape f (F.reindex g ⟨x.shape, hq⟩ b) from
        (congrFun (F.isFunctorial.reindex_naturality g ⟨x.shape, hq⟩ f) b).symm]
    exact x.2 f (F.reindex g ⟨x.shape, hq⟩ b)⟩

/-- The underlying value of a direction cast along a shape equality is the
original value, up to the transport of its type along that equality. -/
private theorem cast_val_heq {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {j : J} {s s' : F.Shape j} (h : s = s')
    {i : I} (p : F.Direction s.1 i) :
    (cast (congrArg (fun t : F.Shape j => F.Direction t.1 i) h) p).1 ≍ (p.1 : F.B s.1) := by
  cases h
  rfl

/-- `reindex` sends directions with equal underlying indices (over equal shapes)
to directions with equal underlying indices. -/
private theorem reindex_val_heq {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) ⦃j' j'' : J⦄ (h : j'' ⟶ j')
    {S S' : F.Shape j'} (hSS : S = S')
    ⦃i i' : I⦄ (b : F.Direction (F.shapeRestr h S).1 i) (b' : F.Direction (F.shapeRestr h S').1 i')
    (hb : (b.1 : F.B (F.shapeRestr h S).1) ≍ (b'.1 : F.B (F.shapeRestr h S').1)) :
    (F.reindex h S b).1 ≍ ((F.reindex h S' b').1 : F.B S'.1) := by
  cases hSS
  obtain ⟨bv, rfl⟩ := b
  obtain ⟨bv', rfl⟩ := b'
  cases eq_of_heq hb
  rfl

/-- Two functions into a common type whose domains are equal are heterogeneously
equal when they agree on heterogeneously-equal inputs. A restriction of
`Function.hfunext` to a non-dependent codomain. -/
private theorem heq_fun {α β : Type u} {X : Type v} (h : α = β) {f : α → X} {g : β → X}
    (hfg : ∀ (a : α) (b : β), a ≍ b → f a = g b) : f ≍ g := by
  cases h
  apply heq_of_eq
  funext a
  exact hfg a a HEq.rfl

/-- Identity law for the restriction action: `objRestrElt` along `𝟙 j` is the
identity. -/
theorem objRestrElt_id {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {X : Type uX} {p : X → I} {j : J}
    (x : F.toSliceDomPFunctor.Obj p) (hq : F.q x.1.1 = j) :
    F.objRestrElt (𝟙 j) x hq = x := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := x
  simp only [objRestrElt]
  refine Sigma.ext
    (congrArg Subtype.val (congrFun (F.isFunctorial.shapeRestr_id j) (⟨a, hq⟩ : F.Shape j))) ?_
  refine heq_fun
    (congrArg F.B
      (congrArg Subtype.val (congrFun (F.isFunctorial.shapeRestr_id j) (⟨a, hq⟩ : F.Shape j))))
    ?_
  intro b1 b2 hb
  dsimp only
  rw [F.isFunctorial.reindex_id]
  congr 1
  exact eq_of_heq
    (HEq.trans (F.cast_val_heq (congrFun (F.isFunctorial.shapeRestr_id j) ⟨a, hq⟩) ⟨b1, rfl⟩) hb)

/-- Composition law for the restriction action: `objRestrElt` along a composite
factors as the composite of the actions. -/
theorem objRestrElt_comp {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {X : Type uX} {p : X → I} ⦃j j' j'' : J⦄
    (g : j' ⟶ j) (h : j'' ⟶ j')
    (x : F.toSliceDomPFunctor.Obj p) (hq : F.q x.1.1 = j)
    (hq' : F.q (F.objRestrElt g x hq).1.1 = j') :
    F.objRestrElt (h ≫ g) x hq = F.objRestrElt h (F.objRestrElt g x hq) hq' := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := x
  simp only [objRestrElt]
  refine Sigma.ext
    (congrArg Subtype.val (congrFun (F.isFunctorial.shapeRestr_comp g h) (⟨a, hq⟩ : F.Shape j)))
    ?_
  refine heq_fun
    (congrArg F.B
      (congrArg Subtype.val
        (congrFun (F.isFunctorial.shapeRestr_comp g h) (⟨a, hq⟩ : F.Shape j))))
    ?_
  intro b1 b2 hb
  dsimp only
  rw [F.isFunctorial.reindex_comp]
  congr 1
  apply eq_of_heq
  refine F.reindex_val_heq g rfl _ _ ?_
  refine F.reindex_val_heq h rfl _ _ ?_
  exact HEq.trans
    (F.cast_val_heq (congrFun (F.isFunctorial.shapeRestr_comp g h) ⟨a, hq⟩) ⟨b1, rfl⟩) hb

/-- The output presheaf `T(Z) : Jᵒᵖ ⥤ Type`, built directly as a `Functor`
value. Its fibre over `j` is the subtype of the dom value `F.obj Z` whose
`q`-output index is `j`; its restriction maps are the shape-and-direction
reindex action `objRestr`, whose `map_id` / `map_comp` are discharged
from `F.isFunctorial`. -/
@[expose] def objPresheaf {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (Z : Iᵒᵖ ⥤ Type uZ) :
    Jᵒᵖ ⥤ Type (max uI uZ uA uB) where
  obj j := { z : F.toPresheafDomPFunctorData.obj Z // F.q z.shape = j.unop }
  map g := ↾ fun w => ⟨F.objRestr g.unop w.1 w.2, (F.shapeRestr g.unop ⟨w.1.shape, w.2⟩).2⟩
  map_id j := by
    ext w
    exact Subtype.ext (F.objRestrElt_id w.1.1 w.2)
  map_comp g h := by
    ext w
    apply Subtype.ext
    exact F.objRestrElt_comp g.unop h.unop w.1.1 w.2 (F.shapeRestr g.unop ⟨w.1.shape, w.2⟩).2

/-- Naturality of the dom morphism map with respect to `objPresheaf`'s
`J`-restriction: for `α : NatTrans Z Z'`, the dom `map α` carries the fibre of
`objPresheaf Z` over `j` into that of `objPresheaf Z'` (it preserves the
`q`-output index, the shape being fixed by `SliceDomPFunctor.map_fst`) and
commutes with the shape-and-direction reindex restriction `objRestr g`. The
commutation is the interchange of the postcomposition with `α` (the morphism
action) and the precomposition with `reindex g` (the restriction), needing no
functor law. -/
theorem map_objRestr {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : NatTrans Z Z') ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.toPresheafDomPFunctorData.obj Z) (hq : F.q x.shape = j) :
    F.toPresheafDomPFunctorData.map α (F.objRestr g x hq) =
      F.objRestr g (F.toPresheafDomPFunctorData.map α x) hq :=
  Subtype.ext rfl

/-- The natural transformation `objPresheaf Z ⟶ objPresheaf Z'` induced by a
morphism `α : Z ⟶ Z'` of input presheaves: each component is the dom `map α` on
the underlying element, restricted to the `q`-indexed fibre (the dom map
preserves the output index, the shape being fixed by
`SliceDomPFunctor.map_fst`); naturality is `map_objRestr`. The categorical
wrapper `functor.map` reuses it. -/
@[expose] def mapPresheaf {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : NatTrans Z Z') : NatTrans (F.objPresheaf Z) (F.objPresheaf Z') where
  app X := ↾fun w => (⟨F.toPresheafDomPFunctorData.map α w.1, w.2⟩ : (F.objPresheaf Z').obj X)
  naturality _ _ g := by
    ext w
    exact Subtype.ext (F.map_objRestr α g.unop w.1 w.2)

end PresheafPFunctor
