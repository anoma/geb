import GebLean.Ramified.Characterization
import GebLean.Utilities.ERArith

/-!
# Tests for the elementary characterization

Acceptance examples for `GebLean.Ramified.Characterization`:
`ramified_definability` instantiates on the class of a doubling ER morphism —
an object-sort context and a `SynCatFO` morphism whose collapse denotation
doubles every input exist. Stated in the all-inputs denotational form through
the interpretation lemmas, not kernel reduction on the clocked composite.
The transferred pair is exercised likewise: `collapseKFunctor.map_injective`
applies through the `Faithful` instance, and `ramified_definability_kSim`
instantiates on the `K^sim` encoding of the doubling class.
-/

namespace GebLeanTests.Ramified.CharacterizationTest

open CategoryTheory
open GebLean GebLean.Ramified GebLean.Ramified.Definability

/-- Doubling as an `ERMorN 1 1`: addition applied to the diagonal. -/
def erDouble : ERMorN 1 1 :=
  fun _ => ERMor1.comp ERMor1.addN fun _ => ERMor1.proj 0

/-- The interpretation of `erDouble` doubles the input at every position. -/
theorem erDouble_interp (v : Fin 1 → ℕ) : erDouble.interp v = fun _ => 2 * v 0 := by
  funext j
  simp only [erDouble, ERMorN.interp, ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_proj]
  omega

/-- The interpretation of `erDouble` doubles `3`. -/
example : erDouble.interp (fun _ => 3) 0 = 6 := by rw [erDouble_interp]

/-- `ramified_definability` instantiates on the doubling class: an object-sort
context and a `SynCatFO` morphism whose collapse denotation, read along the
arity identifications, doubles every input exist. Existence is through the
theorem, not kernel reduction on the clocked composite. -/
example :
    ∃ (Γ : ObjCtx 1) (g : Γ.toSynCatFO ⟶ (oCtx 1).toSynCatFO),
      collapseDenotation g
        = arityCongr Γ.objLen_toSynCatFO.symm ((oCtx 1).objLen_toSynCatFO).symm
            (fun v _ => 2 * v 0) := by
  obtain ⟨Γ, g, hg⟩ :=
    ramified_definability (Quotient.mk (erMorNSetoid 1 1) erDouble)
  refine ⟨Γ, g, hg.trans (congrArg (arityCongr _ _) ?_)⟩
  funext v j
  rw [ERMorNQuo.interp_mk, erDouble_interp]

/-- The K-valued soundness functor is faithful: equal `collapseKFunctor`
images force equal `SynCatFO` morphisms, through the `Faithful` instance. -/
example {Γ Δ : SynCatFO} {g h : Γ ⟶ Δ}
    (H : collapseKFunctor.map g = collapseKFunctor.map h) : g = h :=
  collapseKFunctor.map_injective H

/-- `ramified_definability_kSim` instantiates on the `K^sim` encoding of the
doubling class: an object-sort context and a `SynCatFO` morphism whose
collapse denotation, read along the arity identifications, doubles every
input exist. Existence is through the theorem, not kernel reduction on the
clocked composite. -/
example :
    ∃ (Γ : ObjCtx 1) (g : Γ.toSynCatFO ⟶ (oCtx 1).toSynCatFO),
      collapseDenotation g
        = arityCongr Γ.objLen_toSynCatFO.symm ((oCtx 1).objLen_toSynCatFO).symm
            (fun v _ => 2 * v 0) := by
  obtain ⟨Γ, g, hg⟩ :=
    ramified_definability_kSim
      (erToKFunctor.map (Quotient.mk (erMorNSetoid 1 1) erDouble))
  refine ⟨Γ, g, hg.trans (congrArg (arityCongr _ _) ?_)⟩
  change (erToKFunctor_map (Quotient.mk (erMorNSetoid 1 1) erDouble)).hom.interp = _
  rw [erToKFunctor_map_interp, ERMorNQuo.interp_mk]
  funext v j
  rw [erDouble_interp]

end GebLeanTests.Ramified.CharacterizationTest
