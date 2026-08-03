/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Quotient
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# `FinSetSkel` has binary coequalizers

The coequalizer of a parallel pair of functions between finite sets is
the quotient of the codomain by the equivalence relation the pair
generates; `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`
computes that quotient and proves its universal property. This module
packages it as mathlib's `ColimitCocone (parallelPair f g)`, registers
the per-diagram `HasColimit`, and derives `HasCoequalizers`.

The packaging is where `Classical.choice` enters: `Cofork.ofπ`,
`Cofork.IsColimit.mk` and
`hasCoequalizers_of_hasColimit_parallelPair` each depend on it, while
the construction being packaged does not. This module is allowlisted
for that reason and the construction is separate for the same reason.

## Main definitions

* `FinSetSkel.coequalizerCocone` — the coequalizer as a chosen
  colimit cocone.

## References

* [nLabCoequalizer] — the coequalizer, and the quotient-set
  construction of it in `Set`.

## Tags

category, finite set, coequalizer, colimit
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace FinSetSkel

variable {X Y : FinSetSkel.{u}}

/-- The coequalizer of a parallel pair, as a chosen colimit cocone.
The fold runs once, in the `let`. -/
def coequalizerCocone (f g : X ⟶ Y) : ColimitCocone (parallelPair f g) :=
  let v := Quotient.unionFind f g
  { cocone := Cofork.ofπ (Quotient.π Y v) (Quotient.comp_π f g)
    isColimit :=
      Cofork.IsColimit.mk _ (fun s ↦ Quotient.desc Y v s.π)
        (fun s ↦ Quotient.π_desc f g s.π s.condition)
        (fun s m hm ↦ Quotient.desc_uniq f g s.π m hm) }

/-- Every parallel pair has a colimit. -/
instance hasColimit_parallelPair {f g : X ⟶ Y} :
    HasColimit (parallelPair f g) :=
  ⟨⟨coequalizerCocone f g⟩⟩

/-- The category has binary coequalizers. -/
instance : HasCoequalizers FinSetSkel.{u} :=
  hasCoequalizers_of_hasColimit_parallelPair _

end FinSetSkel
