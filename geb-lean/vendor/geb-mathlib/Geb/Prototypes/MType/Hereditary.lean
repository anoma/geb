/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.MType.Basic

set_option doc.verso true in
/-!
# Hereditary predicates on coalgebras

A predicate holds hereditarily at an element of a coalgebra
{lit}`c : X → Q.Obj X` when it holds there and, hereditarily, at every child
the coalgebra gives the element. On a W-type the corresponding predicate is
inductive, defined for instance by {name}`SlicePFunctor.W.RecProp` with the
step {lit}`P x ∧ ∀ b, ih b`; on an M-type the trees are not well founded,
and the predicate is coinductive, the greatest fixed point of the operator
{lit}`Φ R x = P x ∧ ∀ b, R ((c x).2 b)`.

## Main definitions

* {lit}`HereditaryAt` — the predicate at every element reached through fewer
  than a given depth of children.
* {lit}`Hereditary` — the predicate at every element reached through
  children.

## Main statements

* {lit}`hereditary_iff` — {lit}`Hereditary` is a fixed point.
* {lit}`hereditary_coinduct` — the coinduction principle: it is the greatest
  fixed point.
* {lit}`hereditary_of_hom` — a predicate holding on the image of a morphism of
  coalgebras holds hereditarily there.
* {lit}`hereditary_mk` — the fixed-point equation at a constructor of the
  M-type.

## Implementation notes

{lit}`Hereditary` constructs the greatest fixed point as the conjunction over
the depths of the iterates of {lit}`Φ` from the true predicate,
{lit}`HereditaryAt c P n`, which states {lit}`P` at every element reached
through fewer than {lit}`n` children; the iterates are defined by dependent
elimination on the W-type of depths, so no coinductive type occurs.
{lit}`Φ` preserves intersections, so the conjunction of its iterates is a
fixed point ({lit}`hereditary_iff`), and every predicate {lit}`R` with
{lit}`R ≤ Φ R` is below it ({lit}`hereditary_coinduct`), which characterise
it as the greatest one.

## References

* \[VanDenBergDeMarchi2007\], Section 2.

## Tags

coinduction, greatest fixed point, M-type, coalgebra, hereditary predicate
-/
set_option doc.verso true

@[expose] public section

universe u v uA uB

namespace Geb.MType

open Depth

variable {Q : PFunctor.{uA, uB}} {X : Type u} (c : X → Q.Obj X) (P : X → Prop)

/-- The predicate {lit}`P` at every element reached from {lit}`x` through
fewer than {lit}`n` children: the {lit}`n`-th iterate from the true
predicate of {lit}`R ↦ fun x ↦ P x ∧ ∀ b, R ((c x).2 b)`, by dependent
elimination on depth. -/
def HereditaryAt : Depth.{uA, uB} → X → Prop :=
  Depth.rec (motive := fun _ ↦ X → Prop) (fun _ ↦ True) fun _ rec x ↦ P x ∧ ∀ b, rec ((c x).2 b)

/-- The predicate {lit}`P` at every element reached from {lit}`x` through
children: the conjunction of the iterates at every depth. -/
def Hereditary (x : X) : Prop := ∀ n, HereditaryAt c P n x

/-- The successor iterate. -/
theorem hereditaryAt_succ (n : Depth.{uA, uB}) (x : X) :
    HereditaryAt c P (succ n) x ↔ P x ∧ ∀ b, HereditaryAt c P n ((c x).2 b) := by
  rw [HereditaryAt, Depth.rec_succ]

/-- {name}`Hereditary` is a fixed point: it holds at an element exactly when
{lit}`P` does and it holds at every child. -/
theorem hereditary_iff (x : X) :
    Hereditary c P x ↔ P x ∧ ∀ b, Hereditary c P ((c x).2 b) := by
  constructor
  · intro h
    exact ⟨((hereditaryAt_succ c P zero x).mp (h (succ zero))).1,
      fun b n ↦ ((hereditaryAt_succ c P n x).mp (h (succ n))).2 b⟩
  · rintro ⟨hp, hc⟩
    exact Depth.induction trivial fun n _ ↦ (hereditaryAt_succ c P n x).mpr ⟨hp, fun b ↦ hc b n⟩

/-- The coinduction principle: a predicate implying {lit}`P` and preserved by
passing to children implies {name}`Hereditary`. With {name}`hereditary_iff`,
{name}`Hereditary` is the greatest fixed point. -/
theorem hereditary_coinduct (R : X → Prop) (h : ∀ x, R x → P x ∧ ∀ b, R ((c x).2 b)) :
    ∀ x, R x → Hereditary c P x := by
  suffices ∀ n x, R x → HereditaryAt c P n x from fun x hx n ↦ this n x hx
  exact Depth.induction (fun _ _ ↦ trivial) fun n ih x hx ↦
    (hereditaryAt_succ c P n x).mpr ⟨(h x hx).1, fun b ↦ ih _ ((h x hx).2 b)⟩

/-- A predicate holding at every element in the image of a morphism of
coalgebras {lit}`f` from {lit}`step` to {lit}`c` holds hereditarily there: the
children of an element of the image are in the image. -/
theorem hereditary_of_hom {Y : Type v} (step : Y → Q.Obj Y) (f : Y → X)
    (hf : ∀ y, c (f y) = Q.map f (step y)) (hP : ∀ y, P (f y)) (y : Y) :
    Hereditary c P (f y) := by
  refine hereditary_coinduct c P (fun x ↦ ∃ y, f y = x) ?_ _ ⟨y, rfl⟩
  rintro _ ⟨y, rfl⟩
  refine ⟨hP y, ?_⟩
  rw [hf y]
  exact fun b ↦ ⟨(step y).2 b, rfl⟩

/-- On the M-type, a predicate of the root layer holds hereditarily at a
constructed element exactly when it holds at that layer and hereditarily at
each of the layer's children. -/
theorem hereditary_mk (L : Q.Obj (M Q) → Prop) (x : Q.Obj (M Q)) :
    Hereditary M.dest (L ∘ M.dest) (M.mk x) ↔
      L x ∧ ∀ b, Hereditary M.dest (L ∘ M.dest) (x.2 b) := by
  refine (hereditary_iff M.dest (L ∘ M.dest) (M.mk x)).trans ?_
  change L (M.mk x).dest ∧ (∀ b, Hereditary M.dest (L ∘ M.dest) ((M.mk x).dest.2 b)) ↔ _
  rw [M.dest_mk]

end Geb.MType
