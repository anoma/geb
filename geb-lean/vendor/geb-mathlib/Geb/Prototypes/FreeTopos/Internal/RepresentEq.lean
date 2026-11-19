/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Represent
public import Geb.Prototypes.FreeTopos.RepresentEq

set_option doc.verso true in
/-!
# An equation of the internal language represents an equality

The equation of two terms of one type, a formula, represents the equality of the functions the
terms represent ({name}`Geb.FreeTopos.represents_eq`), a function into the propositions, where
the representation of the terms' type relates each value to at most one value in each direction.
The connectives of the language are definitions built from equations
({lit}`Geb.FreeTopos.Internal.Logic.defs`), so a formula's representation follows from this
and from the representations of the other constructions of the language
({name}`Geb.FreeTopos.Internal.RepC`).

## Main statements

* {lit}`repC_eq` — an equation represents the equality of the functions its sides represent.

## Tags

internal language, logical relation, representation, equality
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts

variable {G : Globals} {n : ℕ} {ds : List PartialHorn.Defn} {ρ : List relTopos.model.Val}
  {S T A B : Type}

/-- An equation represents the equality of the functions its sides represent, where the
representation of the sides' type relates each value to at most one value in each direction. -/
theorem repC_eq {X : Tree} {e : List (Tree × Tree)} {t u : Term} {a : Tree}
    {R : S → B → Prop} {R₁ : T → A → Prop} {F F' : S → T}
    (ht : RepC G n ds ρ t X e a R R₁ F) (hu : RepC G n ds ρ u X e a R R₁ F')
    (ha : ObjVal ρ (unfoldTerm sig ds a) A) (hl : ∀ t x y, R₁ t x → R₁ t y → x = y)
    (hr : ∀ t t' x, R₁ t x → R₁ t' x → t = t') :
    RepC G n ds ρ (Term.eq t u) X e omega R Rep.prop fun s ↦ F s = F' s :=
  let ⟨f, hf, hF⟩ := ht
  let ⟨g, hg, hG⟩ := hu
  ⟨comp (chi (diag a)) (pair f g), compile_eq_iff.mpr ⟨t, u, rfl, f, a, hf, g, hg, rfl⟩, by
    simp (disch := decide) only [diag, chi, comp, pair, idt, unfold_op', List.map_cons,
      List.map_nil]
    exact represents_eq ha hF hG hl hr⟩

end Geb.FreeTopos.Internal

end
