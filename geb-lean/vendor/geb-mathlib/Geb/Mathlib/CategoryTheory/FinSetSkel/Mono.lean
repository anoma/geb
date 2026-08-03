/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core

/-!
# Monomorphisms of `FinSetSkel`

A morphism is a monomorphism exactly when its vector is injective.

## Main statements

* `FinSetSkel.mono_iff_injective` — monomorphisms are the morphisms
  with injective vectors.

## Implementation notes

`CategoryTheory.Mono` and `CategoryTheory.Category` are both
axiom-free, so the statement belongs in the choice-free layer, and
the proof is direct over vectors: the forward direction tests a
morphism against two points, and the reverse is
`FinSetSkel.hom_ext`.

It supplies the hypothesis `Vector.invOfInjective` takes, and so is a
prerequisite of the subobject classifier rather than a free-standing
characterisation.

## Tags

finite sets, skeleton, monomorphism, injective
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel

/-- A morphism is a monomorphism exactly when its vector is
injective. -/
theorem mono_iff_injective {X Y : FinSetSkel.{u}} {f : X ⟶ Y} :
    Mono f ↔ Function.Injective f.toVec.get := by
  constructor
  · intro hm i j hij
    have h : point i ≫ f = point j ≫ f :=
      hom_ext fun t ↦ by rw [comp_get, comp_get, point_get, point_get, hij]
    have hp : (point i : mk 1 ⟶ X) = point j := (cancel_mono f).mp h
    have := congrArg (fun m ↦ (m : mk 1 ⟶ X).toVec.get 0) hp
    simpa only [point_get] using this
  · intro hinj
    constructor
    intro Z g h hgh
    exact hom_ext fun t ↦ hinj (by
      have := congrArg (fun m ↦ (m : Z ⟶ Y).toVec.get t) hgh
      simpa only [comp_get] using this)

end FinSetSkel
