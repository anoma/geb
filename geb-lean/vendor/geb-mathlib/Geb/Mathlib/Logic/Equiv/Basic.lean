/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Equiv.Basic

/-!
# Eliminators for sections of sigma-type projections

Extensions of `Mathlib.Logic.Equiv.Basic`.

## Main definitions

* `sigmaFstSectionElim` — eliminate a function into a sigma type along
  a proof that it is a section of the first projection, producing a
  dependent function.

## Main statements

* `sigmaFstSectionElim_eq` — `sigmaFstSectionElim` computes the
  inverse direction of `Equiv.piEquivSubtypeSigma`.

## Tags

sigma, section, dependent function, equiv
-/

@[expose] public section

universe u v

/-- Eliminate a function into a sigma type along a proof that it is a
section of the first projection, producing a dependent function (the
inverse direction of mathlib's `Equiv.piEquivSubtypeSigma`
correspondence). -/
def sigmaFstSectionElim {X : Type u} {W : X → Type v}
    (g : (t : X) → Σ e, W e) (sect : ∀ t, (g t).1 = t) (t : X) : W t :=
  Eq.ndrec (g t).2 (sect t)

/-- `sigmaFstSectionElim` computes the inverse direction of
`Equiv.piEquivSubtypeSigma`. -/
theorem sigmaFstSectionElim_eq {X : Type u} {W : X → Type v}
    (g : (t : X) → Σ e, W e) (sect : ∀ t, (g t).1 = t) :
    sigmaFstSectionElim g sect =
      (Equiv.piEquivSubtypeSigma X W).symm ⟨g, sect⟩ := by
  funext t
  simp only [Equiv.piEquivSubtypeSigma, Equiv.coe_fn_symm_mk]
  exact eq_of_heq ((eqRec_heq (sect t) (g t).2).trans (cast_heq _ _).symm)
