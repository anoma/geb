/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.MType.Depth
public import Geb.Mathlib.Data.PFunctor.Presheaf.Arrow

set_option doc.verso true in
/-!
# Finite observations of an M-type as a presheaf W-family

The observations of depth {lit}`n` of a tree of a polynomial functor
{lit}`Q` are its truncations below depth {lit}`n`: at depth zero a single
cutoff, and at a successor depth a shape of {lit}`Q` with an observation of
the preceding depth at each of its directions. They form a family of types
over the W-type of depths, obtained as the fibres of the restriction map of
the presheaf W-type of {name}`PFunctor.dependent` on the walking arrow, with
the depths as base: over the zero shape the dependent part has one nullary
shape, and over the successor shape it is {lit}`Q`, each of whose directions
lies over the successor's unique direction. The computation rule of the
fibres, {name}`PFunctor.Dependent.fiberMkEquiv`, then reads
{lit}`Approx Q zero ≃ Unit` and
{lit}`Approx Q (succ n) ≃ Q.Obj (Approx Q n)`.

Truncation forgets the deepest layer, and finite unfolding of a coalgebra
computes the observation of every depth; both are defined by dependent
elimination on depths. Agreement of observations at successive depths is
equality after truncation.

## Main definitions

* {lit}`Approx.family`, {lit}`Approx` — the dependent part and the fibres.
* {lit}`zeroEquiv`, {lit}`succEquiv`, {lit}`cutoff` — the computation rules of
  the fibres and the observation of depth zero.
* {lit}`truncate`, {lit}`Agree`, {lit}`Consistent` — truncation, agreement,
  and agreement at every depth.
* {lit}`corecApprox` — the finite unfoldings of a coalgebra.

## Main statements

* {lit}`truncate_succ` — truncation keeps the shape and truncates the children.
* {lit}`corecApprox_consistent` — the finite unfoldings of a coalgebra agree.

## References

* \[VanDenBergDeMarchi2007\], Section 2.

## Tags

M-type, W-type, presheaf, finite approximation, truncation
-/
set_option doc.verso true

@[expose] public section

universe u uA uB

namespace Geb.MType

open PFunctor.Dependent Depth

variable (Q : PFunctor.{uA, uB})

/-- The dependent part over depths: at zero a single nullary cutoff shape, and
at a successor the polynomial {lit}`Q`, every direction of which lies over the
successor's unique direction. -/
def Approx.family : ∀ b : depthSig.{uA, uB}.A, SliceDomPFunctor.{uA, uB, uB} (depthSig.B b)
  | ⟨false⟩ => ⟨⟨PUnit, fun _ ↦ PEmpty⟩, fun x ↦ nomatch x.2⟩
  | ⟨true⟩ => ⟨Q, fun _ ↦ PUnit.unit⟩

/-- The observations of a tree of {lit}`Q` at depth {lit}`n`: the fibre over
{lit}`n` of the restriction map of the presheaf W-type. -/
abbrev Approx (n : Depth.{uA, uB}) : Type (max uA uB) := Fiber depthSig (Approx.family Q) n

/-- At zero there is a single observation. -/
def zeroEquiv : Approx Q zero ≃ Unit :=
  (fiberMkEquiv depthSig (Approx.family Q) ⟨false⟩ PEmpty.elim).trans
    { toFun := fun _ ↦ ()
      invFun := fun _ ↦ ⟨⟨PUnit.unit, PEmpty.elim⟩, funext fun i ↦ nomatch i⟩
      left_inv := fun ⟨⟨PUnit.unit, _⟩, _⟩ ↦ Subtype.ext
        (congrArg (Sigma.mk PUnit.unit)
          (funext fun i ↦ nomatch i))
      right_inv := fun _ ↦ rfl }

/-- At a successor, an observation is a shape of {lit}`Q` with an observation
of the preceding depth at each of its directions. The redundant index of each
child, the successor's unique direction, is removed. -/
def succEquiv (n : Depth.{uA, uB}) : Approx Q (succ n) ≃ Q.Obj (Approx Q n) :=
  (fiberMkEquiv depthSig (Approx.family Q) ⟨true⟩ fun _ ↦ n).trans
    { toFun := fun x ↦ ⟨x.1.1, fun b ↦ (x.1.2 b).2⟩
      invFun := fun x ↦ ⟨⟨x.1, fun b ↦ ⟨PUnit.unit, x.2 b⟩⟩, rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The unique observation of depth zero. -/
def cutoff : Approx Q zero := (zeroEquiv Q).symm ()

/-- There is only one observation of depth zero. -/
instance : Subsingleton (Approx Q zero) := (zeroEquiv Q).subsingleton

/-- Forget the deepest layer, by dependent elimination on depth. -/
def truncate : ∀ n : Depth.{uA, uB}, Approx Q (succ n) → Approx Q n :=
  Depth.rec (motive := fun n ↦ Approx Q (succ n) → Approx Q n) (fun _ ↦ cutoff Q)
    fun n rec x ↦ (succEquiv Q n).symm (Q.map rec (succEquiv Q (succ n) x))

variable {Q}

/-- Truncation keeps the shape and truncates each child. -/
theorem truncate_succ (n : Depth.{uA, uB}) (x : Approx Q (succ (succ n))) :
    succEquiv Q n (truncate Q (succ n) x) = Q.map (truncate Q n) (succEquiv Q (succ n) x) := by
  simp only [truncate, Depth.rec_succ, Equiv.apply_symm_apply]

/-- Two observations at successive depths agree when truncating the deeper one
gives the shallower one. -/
def Agree {n : Depth.{uA, uB}} (x : Approx Q n) (y : Approx Q (succ n)) : Prop :=
  truncate Q n y = x

/-- A family of observations, one at each depth, agrees at every depth. -/
def Consistent (x : ∀ n : Depth.{uA, uB}, Approx Q n) : Prop :=
  ∀ n, Agree (x n) (x (succ n))

/-- The finite unfoldings of a coalgebra {lit}`step`, by dependent elimination
on depth: the cutoff at zero, and at a successor the shape {lit}`step` gives,
over the unfoldings of the preceding depth. -/
def corecApprox {α : Type u} (step : α → Q.Obj α) : ∀ n : Depth.{uA, uB}, α → Approx Q n :=
  Depth.rec (motive := fun n ↦ α → Approx Q n) (fun _ ↦ cutoff Q)
    fun n rec a ↦ (succEquiv Q n).symm (Q.map rec (step a))

/-- A successor unfolding reads one layer of the coalgebra and unfolds each
child. -/
theorem corecApprox_succ {α : Type u} (step : α → Q.Obj α) (n : Depth.{uA, uB}) (a : α) :
    succEquiv Q n (corecApprox step (succ n) a) = Q.map (corecApprox step n) (step a) := by
  simp only [corecApprox, Depth.rec_succ, Equiv.apply_symm_apply]

/-- The finite unfoldings of a coalgebra agree at every depth. -/
theorem corecApprox_consistent {α : Type u} (step : α → Q.Obj α) (a : α) :
    Consistent fun n ↦ corecApprox step n a := by
  suffices ∀ n a, truncate Q n (corecApprox step (succ n) a) = corecApprox step n a from
    fun n ↦ this n a
  refine Depth.induction (fun _ ↦ rfl) fun n ih a ↦ (succEquiv Q n).injective ?_
  rw [truncate_succ, corecApprox_succ, corecApprox_succ]
  obtain ⟨s, f⟩ := step a
  exact congrArg (Sigma.mk s) (funext fun b ↦ ih (f b))

end Geb.MType
