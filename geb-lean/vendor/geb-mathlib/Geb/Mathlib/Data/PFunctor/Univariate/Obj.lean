/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Data.PFunctor.Univariate.Basic

set_option doc.verso true in
/-!
# Nodes of a polynomial functor

Lemmas on the interpretation {name}`PFunctor.Obj` of a polynomial functor,
whose elements are nodes: a shape together with a child at each of the
shape's directions. {name}`PFunctor.map` along an injective function is
injective, and a node's child can be read at a direction of any shape proved
equal to the node's shape, the direction transported along the proof.

## Main definitions

* {lit}`PFunctor.Obj.sndOfEq` — the child of a node at a direction of a shape
  equal to the node's shape.

## Main statements

* {lit}`PFunctor.map_injective` — mapping along an injective function is
  injective.
* {lit}`PFunctor.Obj.sndOfEq_congr` — {lit}`sndOfEq` respects equality of
  nodes.
* {lit}`PFunctor.Obj.mk_sndOfEq` — a node is its shape over its
  {lit}`sndOfEq` children.

## Tags

polynomial functor, PFunctor, node, transport
-/
set_option doc.verso true

@[expose] public section

universe uA uB u v

namespace PFunctor

variable {P : PFunctor.{uA, uB}}

/-- {name}`PFunctor.map` along an injective function is injective. -/
theorem map_injective {α : Type u} {β : Type v} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (P.map f) := by
  rintro ⟨a, g⟩ ⟨a', g'⟩ h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj h
  exact congrArg (Sigma.mk a) (funext fun b ↦ hf (congrFun (eq_of_heq h) b))

namespace Obj

/-- The child of a node at a direction of a shape equal to the node's shape:
the direction is transported to the node's shape along the equation. -/
def sndOfEq {α : Type u} (x : P α) {a : P.A} (h : x.fst = a) (b : P.B a) : α :=
  x.snd (cast (congrArg P.B h.symm) b)

/-- {name}`sndOfEq` respects equality of nodes. -/
theorem sndOfEq_congr {α : Type u} {x y : P α} (hxy : x = y) {a : P.A} (hx : x.fst = a)
    (hy : y.fst = a) (b : P.B a) : x.sndOfEq hx b = y.sndOfEq hy b := by
  subst hxy
  rfl

/-- A node is its shape over its {name}`sndOfEq` children. -/
theorem mk_sndOfEq {α : Type u} (x : P α) {a : P.A} (h : x.fst = a) :
    Sigma.mk a (x.sndOfEq h) = x := by
  obtain ⟨a', f⟩ := x
  subst h
  rfl

end Obj

end PFunctor
