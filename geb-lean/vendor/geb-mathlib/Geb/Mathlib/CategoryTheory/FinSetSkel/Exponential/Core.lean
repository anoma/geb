/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core
public import Geb.Mathlib.Logic.Equiv.Fin.Basic
public import Geb.Mathlib.Logic.Equiv.Basic
public import Geb.Mathlib.Data.Fin.Basic

/-!
# The exponential of `FinSetSkel`, over carriers

The exponential object of `Fin m` into `Fin y` is `Fin (y ^ m)`, and
the adjunction's hom-level equivalence is the chain

`(Fin (m * z) → Fin y) ≃ (Fin m × Fin z → Fin y) ≃
 (Fin m → Fin z → Fin y) ≃ (Fin z → Fin m → Fin y) ≃
 (Fin z → Fin (y ^ m))`

stated here over the raw carrier and the explicit projections of the
binary product, never over `⊗` or `◁`: those elaborate through the
`CartesianMonoidalCategory` instance, which depends on
`Classical.choice`. The monoidal restatement is
`FinSetSkel.monoidalClosed`.

## Main definitions

* `FinSetSkel.expEquivIdx` — the hom-level equivalence over index
  functions.
* `FinSetSkel.expEquivHom` — the same over morphisms.

## Main statements

* `FinSetSkel.expEquivIdx_naturality` — naturality of that
  equivalence in the parameter.

## Implementation notes

Two steps of the chain are not the obvious spelling. The domain
transport is `Equiv.arrowCongrLeftC`, mathlib's `Equiv.arrowCongr`
and `Equiv.piCongrLeft` family all depending on `Classical.choice`.
The swap is required because the adjunction `tensorLeft X ⊣ ihom X`
varies in the parameter `Z`, so the result must be a function of
`Fin z`, while `X ⊗ Z` places `X` first and `Equiv.curry` therefore
produces `Fin m` outermost. It is a consequence of which factor the
adjunction is taken in, not of which digit `Fin.pairC` makes high.

## Tags

finite sets, skeleton, exponential, closed, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel

/-- The exponential's hom-level equivalence, over index functions:
the exponent object has length `m`, the parameter object length `z`
and the target length `y`. -/
def expEquivIdx (m z y : ℕ) : (Fin (m * z) → Fin y) ≃ (Fin z → Fin (y ^ m)) :=
  (((Equiv.arrowCongrLeftC (γ := Fin y) (finProdFinEquivC (m := m) (n := z)).symm).trans
      (Equiv.curry (Fin m) (Fin z) (Fin y))).trans
      (Equiv.piComm fun _ : Fin m ↦ fun _ : Fin z ↦ Fin y)).trans
    (Equiv.piCongrRight fun _ ↦ finFunctionFinEquivC)

/-- The exponential's equivalence encodes, for each parameter index,
the function obtained by fixing it. -/
theorem expEquivIdx_apply (m z y : ℕ) (g : Fin (m * z) → Fin y)
    (t : Fin z) :
    expEquivIdx m z y g t = Fin.funEncodeC (fun a ↦ g (Fin.pairC a t)) := rfl

/-- Naturality of the exponential's equivalence in the parameter,
where `φ` is the index function of a morphism into the parameter
object. -/
theorem expEquivIdx_naturality (m z' z y : ℕ) (φ : Fin z' → Fin z)
    (g : Fin (m * z) → Fin y) :
    expEquivIdx m z' y
        (fun i ↦ g (Fin.pairC (Fin.divNatC i) (φ (Fin.modNatC i)))) =
      expEquivIdx m z y g ∘ φ := by
  funext t
  simp only [expEquivIdx_apply, Function.comp_apply, Fin.divNatC_pairC,
    Fin.modNatC_pairC]

/-- The exponential's hom-level equivalence, over morphisms. -/
def expEquivHom (m z y : ℕ) :
    ((mk (m * z) : FinSetSkel.{u}) ⟶ mk y) ≃ ((mk z : FinSetSkel.{u}) ⟶ mk (y ^ m)) :=
  (homEquivIdxFun (mk (m * z)) (mk y)).trans
    ((expEquivIdx m z y).trans (homEquivIdxFun (mk z) (mk (y ^ m))).symm)

end FinSetSkel
