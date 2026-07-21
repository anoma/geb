import GebLeanTests.Ramified.Characterization
import GebLean.Ramified.Polynomial.Characterization

/-!
# Tests for the primed elementary characterization

Acceptance examples for `GebLean.Ramified.Polynomial.Characterization`, the
primed mirror of `GebLeanTests/Ramified/Characterization.lean`:
`ramified_definability'` instantiates on the class of the doubling ER morphism
`erDouble` — a primed object-sort context and a `SynCatFO'` morphism whose
primed collapse denotation doubles every input exist. The object map of the
primed soundness functor is pinned at the primed arity, its faithfulness is
resolved by instance search and applied through `map_injective`, and
`ramified_definability_kSim'` instantiates on the `K^sim` encoding of the same
class.
-/

namespace GebLeanTests.Ramified.Polynomial.CharacterizationTest

open CategoryTheory
open GebLean GebLean.Ramified GebLean.Ramified.Polynomial
open GebLeanTests.Ramified.CharacterizationTest (erDouble erDouble_interp)

-- The object map of the primed soundness functor reads the primed arity.
example (Γ' : SynCatFO') : collapseFunctor'.obj Γ' = objLen' Γ' :=
  (objLen_functor_obj Γ').symm

/-- `ramified_definability'` instantiates on the doubling class: a primed
object-sort context and a `SynCatFO'` morphism whose primed collapse
denotation, read along the arity identifications, doubles every input exist.
Existence is through the theorem, not kernel reduction on the clocked
composite. -/
example :
    ∃ (Γ' : ObjCtx' 1) (g' : Γ'.toSynCatFO' ⟶ (oCtx' 1).toSynCatFO'),
      collapseDenotation' g'
        = arityCongr (objLen'_toSynCatFO' Γ').symm (objLen'_toSynCatFO' (oCtx' 1)).symm
            (fun v _ => 2 * v 0) := by
  obtain ⟨Γ', g', hg⟩ := ramified_definability' (Quotient.mk (erMorNSetoid 1 1) erDouble)
  refine ⟨Γ', g', hg.trans (congrArg (arityCongr _ _) ?_)⟩
  funext v j
  rw [ERMorNQuo.interp_mk, erDouble_interp]

-- The primed soundness functor is faithful by instance search.
example : collapseFunctor'.Faithful := inferInstance

/-- The primed K-valued soundness functor is faithful: equal
`collapseKFunctor'` images force equal `SynCatFO'` morphisms. -/
example {Γ' Δ' : SynCatFO'} {g h : Γ' ⟶ Δ'}
    (H : collapseKFunctor'.map g = collapseKFunctor'.map h) : g = h :=
  collapseKFunctor'.map_injective H

/-- `ramified_definability_kSim'` instantiates on the `K^sim` encoding of the
doubling class. -/
example :
    ∃ (Γ' : ObjCtx' 1) (g' : Γ'.toSynCatFO' ⟶ (oCtx' 1).toSynCatFO'),
      collapseDenotation' g'
        = arityCongr (objLen'_toSynCatFO' Γ').symm (objLen'_toSynCatFO' (oCtx' 1)).symm
            (fun v _ => 2 * v 0) := by
  obtain ⟨Γ', g', hg⟩ :=
    ramified_definability_kSim'
      (erToKFunctor.map (Quotient.mk (erMorNSetoid 1 1) erDouble))
  refine ⟨Γ', g', hg.trans (congrArg (arityCongr _ _) ?_)⟩
  change (erToKFunctor_map (Quotient.mk (erMorNSetoid 1 1) erDouble)).hom.interp = _
  rw [erToKFunctor_map_interp, ERMorNQuo.interp_mk]
  funext v j
  rw [erDouble_interp]

end GebLeanTests.Ramified.Polynomial.CharacterizationTest
