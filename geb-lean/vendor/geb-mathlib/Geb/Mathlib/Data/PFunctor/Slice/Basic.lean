/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Slice polynomial functors on `Type` (constructive core)

A `PFunctor` is the middle leg of a Gambino–Hyland polynomial diagram
`dom ◀ s ─ Idx ─ fst ▶ A ─ t ▶ cod`. Adding `s : Idx → dom` and
`t : A → cod` yields a polynomial functor `Type/dom → Type/cod`,
defined as a restriction of the interpretation `P.Obj X = Σ a, B a → X`
to `s`-compatible direction assignments, tagged by `t`.

This file is the constructive core: the structures, the compatibility
predicate, the curried constructor, and the object/morphism maps with
their functoriality stated as plain equalities. It names no `Over` and
no `CategoryTheory.Functor`, so it is `Classical.choice`-free. The
categorical packaging is in the sibling `Slice.Functor` module.

## Main definitions

* `SliceDomPFunctor`, `SlicePFunctor` — the structures.
* `SliceDomPFunctor.Compatible` — the direction-compatibility predicate.
* `SliceDomPFunctor.ofCurried` / `sCurried` — the curried constructor and
  the constraint leg in dependently-curried form.
* `SliceDomPFunctor.DirectionOver` / `Direction` — the constraint-leg
  condition on a direction of shape `a`, and the fibre of `sCurried a`
  over `i`.
* `SliceDomPFunctor.Obj` / `map` — the domain-restricted functor's
  object and morphism maps; `map_id` / `map_comp` its functoriality.
* `SlicePFunctor.obj` / `map` — the slice functor `Type/dom → Type/cod`:
  `obj` is the output object's structure map into `cod`, `map` the
  underlying function; `map_w` that it lies over `cod`, `map_id` /
  `map_comp` its functoriality.
* `SlicePFunctor.ShapeOver` / `Shape` — the tag-leg condition and the
  fibre of `t` over `j`.

## Main statements

* `SliceDomPFunctor.compatible_iff` — `Compatible` stated pointwise.
* `SliceDomPFunctor.map_fst` — `map` fixes the shape component.
* `SliceDomPFunctor.map_id` / `map_comp` — functoriality of the
  domain-restricted action.
* `SlicePFunctor.map_w` — the slice morphism lies over `cod`.
* `SlicePFunctor.map_id` / `map_comp` — functoriality of the slice functor.

## Implementation notes

`SliceDomPFunctor.Obj` is a subtype of `PFunctor.Obj`; `map` is
`PFunctor.map` restricted; functoriality reuses
`PFunctor.id_map` / `PFunctor.map_map`. The `SlicePFunctor` interpretation
reuses these — its carrier is `SliceDomPFunctor.Obj` and its `map` the
`SliceDomPFunctor` map — adding only the `t`-tag (`obj`) and the
tag-compatibility (`map_w`); `map_id` / `map_comp` delegate to the
domain-side ones. `SliceDomPFunctor.Obj` and `SlicePFunctor.obj`, both
namespaces' `map`,
`SliceDomPFunctor.ofCurried` / `sCurried` / `DirectionOver` / `Direction`,
and `SlicePFunctor.ShapeOver` / `Shape` are `@[expose]` so the
wrapper and tests can unfold them across the module boundary.

## References

* [GambinoHyland2004]
* [GambinoKock2013]

## Tags

polynomial functor, dependent polynomial functor, slice category,
container, PFunctor
-/

public section

universe uA uB uD uC uX uX' uY uZ

/-- A polynomial functor with a constraint leg `s` assigning each
`(shape, direction)` pair (an element of `PFunctor.Idx`) a `dom`-index. -/
@[nolint checkUnivs]
structure SliceDomPFunctor (dom : Type uD) : Type (max (uA + 1) (uB + 1) uD)
    extends PFunctor.{uA, uB} where
  /-- The constraint leg: each direction is assigned a `dom`-index. -/
  s : toPFunctor.Idx → dom

/-- A `SliceDomPFunctor` with a tag leg `t` assigning each shape a
`cod`-index. -/
@[nolint checkUnivs]
structure SlicePFunctor (dom : Type uD) (cod : Type uC) : Type (max (uA + 1) (uB + 1) uC uD)
    extends SliceDomPFunctor.{uA, uB, uD} dom where
  /-- The tag leg: each shape is assigned a `cod`-index. -/
  t : toPFunctor.A → cod

attribute [ext] SliceDomPFunctor SlicePFunctor

namespace SliceDomPFunctor

/-- A direction assignment `v : F.B a → X` is compatible with a base map
`p : X → dom` when, as functions `F.B a → dom`, `p ∘ v` equals the
constraint leg restricted to shape `a`. Pointwise: `p (v b) = s ⟨a, b⟩`. -/
def Compatible {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) {X : Type uX}
    (p : X → dom) (a : F.A) (v : F.B a → X) : Prop :=
  p ∘ v = F.s ∘ Sigma.mk a

/-- `Compatible` stated pointwise. -/
theorem compatible_iff {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    {X : Type uX} (p : X → dom) (a : F.A) (v : F.B a → X) :
    F.Compatible p a v ↔ ∀ b, p (v b) = F.s ⟨a, b⟩ :=
  funext_iff

/-- Build a `SliceDomPFunctor` from the dependently-curried constraint
leg. -/
@[expose] def ofCurried (P : PFunctor.{uA, uB}) (dom : Type uD)
    (sc : (a : P.A) → P.B a → dom) : SliceDomPFunctor dom where
  toPFunctor := P
  s := fun x => sc x.1 x.2

/-- The constraint leg in dependently-curried form. -/
@[expose] def sCurried {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) (a : F.A)
    (b : F.B a) : dom :=
  F.s ⟨a, b⟩

/-- The constraint-leg condition on a direction of shape `a`: that its
image under `sCurried a` is `i`. Point-free as `(· = i) ∘ sCurried a`. -/
@[expose] def DirectionOver {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    (a : F.A) (i : dom) : F.B a → Prop :=
  (· = i) ∘ F.sCurried a

/-- The directions of shape `a` lying over the base point `i`: the fibre
of `sCurried a` over `i`. -/
@[expose] def Direction {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    (a : F.A) (i : dom) : Type uB :=
  Subtype (F.DirectionOver a i)

/-- Value of the domain-restricted functor on `(X, p)`: the
compatibility subtype of the `PFunctor` interpretation. -/
@[expose] def Obj {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) {X : Type uX}
    (p : X → dom) : Type (max uA uB uX) :=
  { x : F.toPFunctor.Obj X // F.Compatible p x.1 x.2 }

/-- Action on a slice morphism `f` (with `p' ∘ f = p`): `PFunctor.map f`
restricted to the compatibility subtype. -/
@[expose] def map {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    {X : Type uX} {X' : Type uX'}
    {p : X → dom} {p' : X' → dom} (f : X → X') (hf : p' ∘ f = p) :
    F.Obj p → F.Obj p' :=
  fun x => ⟨F.toPFunctor.map f x.1, by
    obtain ⟨⟨a, v⟩, hx⟩ := x
    change p' ∘ (f ∘ v) = F.s ∘ Sigma.mk a
    rw [← Function.comp_assoc, hf]
    exact hx⟩

/-- `map` fixes the shape component. -/
theorem map_fst {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    {X : Type uX} {X' : Type uX'}
    {p : X → dom} {p' : X' → dom} (f : X → X') (hf : p' ∘ f = p)
    (x : F.Obj p) : (F.map f hf x).1.1 = x.1.1 := rfl

/-- Functoriality: identity. -/
theorem map_id {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) {X : Type uX}
    (p : X → dom) : F.map id (by simp) = (id : F.Obj p → F.Obj p) :=
  funext fun x => Subtype.ext (F.toPFunctor.id_map x.1)

/-- Functoriality: composition. -/
theorem map_comp {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {p : X → dom} {q : Y → dom} {r : Z → dom} (f : X → Y) (g : Y → Z)
    (hf : q ∘ f = p) (hg : r ∘ g = q) :
    F.map (g ∘ f) (by rw [← hf, ← hg, Function.comp_assoc]) =
      F.map g hg ∘ F.map f hf :=
  funext fun x => Subtype.ext (F.toPFunctor.map_map f g x.1).symm

end SliceDomPFunctor

namespace SlicePFunctor

/-- The slice functor's value on `(X, p)`, as an object of `Type/cod`: its
structure map into `cod`, the tag leg applied to each shape. The carrier is
the `SliceDomPFunctor` value `F.toSliceDomPFunctor.Obj p`. -/
@[expose] def obj {dom : Type uD} {cod : Type uC} (F : SlicePFunctor.{uA, uB, uD, uC} dom cod)
    {X : Type uX} (p : X → dom) : F.toSliceDomPFunctor.Obj p → cod :=
  fun z => F.t z.1.1

/-- The slice functor's action on a morphism: the `SliceDomPFunctor` morphism
map underlying it. -/
@[expose] def map {dom : Type uD} {cod : Type uC} (F : SlicePFunctor.{uA, uB, uD, uC} dom cod)
    {X : Type uX} {X' : Type uX'} {p : X → dom} {p' : X' → dom} (f : X → X') (hf : p' ∘ f = p) :
    F.toSliceDomPFunctor.Obj p → F.toSliceDomPFunctor.Obj p' :=
  F.toSliceDomPFunctor.map f hf

/-- `map` lies over `cod`: it commutes with the `obj` structure maps. -/
theorem map_w {dom : Type uD} {cod : Type uC} (F : SlicePFunctor.{uA, uB, uD, uC} dom cod)
    {X : Type uX} {X' : Type uX'} {p : X → dom} {p' : X' → dom} (f : X → X') (hf : p' ∘ f = p) :
    F.obj p' ∘ F.map f hf = F.obj p :=
  funext fun z => congrArg F.t (F.toSliceDomPFunctor.map_fst f hf z)

/-- Functoriality: identity. -/
theorem map_id {dom : Type uD} {cod : Type uC} (F : SlicePFunctor.{uA, uB, uD, uC} dom cod)
    {X : Type uX} (p : X → dom) :
    F.map id (by simp) = (id : F.toSliceDomPFunctor.Obj p → F.toSliceDomPFunctor.Obj p) :=
  F.toSliceDomPFunctor.map_id p

/-- Functoriality: composition. -/
theorem map_comp {dom : Type uD} {cod : Type uC} (F : SlicePFunctor.{uA, uB, uD, uC} dom cod)
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {p : X → dom} {q : Y → dom} {r : Z → dom} (f : X → Y) (g : Y → Z)
    (hf : q ∘ f = p) (hg : r ∘ g = q) :
    F.map (g ∘ f) (by rw [← hf, ← hg, Function.comp_assoc]) = F.map g hg ∘ F.map f hf :=
  F.toSliceDomPFunctor.map_comp f g hf hg

/-- The tag-leg condition on a shape: that its image under `t` is `j`.
Point-free as `(· = j) ∘ t`. -/
@[expose] def ShapeOver {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) (j : cod) : F.A → Prop :=
  (· = j) ∘ F.t

/-- The shapes lying over `j`: the fibre of `t` over `j`. -/
@[expose] def Shape {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) (j : cod) : Type uA :=
  Subtype (F.ShapeOver j)

end SlicePFunctor
