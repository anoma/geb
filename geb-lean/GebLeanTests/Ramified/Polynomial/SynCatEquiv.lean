import GebLean
import GebLean.Ramified.Polynomial.SynCatEquiv
import GebLeanTests.Ramified.Polynomial.SynCat

/-!
# Tests for the term-layer syntactic-category equivalence

Executable checks that, over the one-binary-operation presentation `natPres`
on `S := Bool` with its `Nat` standard model
(`GebLeanTests/Ramified/Polynomial/SynCat.lean`), the equivalence
`GebLean.Ramified.Polynomial.synCatSliceEquiv` acts as expected: its functor
carries the primed sum morphism to the legacy sum-morphism class (through
`tmSliceEquiv_op` and `tmSliceEquiv_var`), and its inverse undoes its functor
on that morphism (the unit round trip).
-/

namespace GebLeanTests.Ramified.Polynomial.SynCatEquiv

open GebLean.Ramified GebLean.Ramified.Polynomial CategoryTheory
open GebLeanTests.Ramified.Polynomial.SynCat

/-- The legacy sum term `op true (var 0) (var 1)`, the `tmSliceEquiv` image of
`sumTerm`. -/
def sumTermLegacy : Tm binSig twoCtx true :=
  Tm.op true (Fin.cons (Tm.var 0) (Fin.cons (Tm.var 1) finZeroElim))

/-- The legacy sum-morphism class `twoCtx ⟶ oneCtx`, the expected image of
`sumMor` under the equivalence's functor. -/
abbrev sumMorLegacy :
    (synCatSliceFunctor natPres).obj twoCtx ⟶ (synCatSliceFunctor natPres).obj oneCtx :=
  Quotient.mk _ (Fin.cons sumTermLegacy finZeroElim)

-- The functor carries the primed sum morphism to the legacy sum-morphism class.
example : (synCatSliceEquiv natPres).functor.map sumMor = sumMorLegacy := by
  refine congrArg (Quotient.mk _) (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => j.elim0) i
  change tmSliceEquiv twoCtx true sumTerm = sumTermLegacy
  unfold sumTerm sumTermLegacy
  rw [tmSliceEquiv_op]
  refine congrArg (Tm.op (sig := binSig) (Γ := twoCtx) true) (funext fun k => ?_)
  refine Fin.cases ?_ (fun k1 => Fin.cases ?_ (fun k2 => k2.elim0) k1) k
  · exact tmSliceEquiv_var 0
  · exact tmSliceEquiv_var 1

-- The inverse undoes the functor on the primed sum morphism (unit round trip).
example :
    (synCatSliceEquiv natPres).inverse.map ((synCatSliceEquiv natPres).functor.map sumMor)
      = sumMor := by
  apply congrArg (Quotient.mk _)
  funext i
  exact Equiv.symm_apply_apply _ _

end GebLeanTests.Ramified.Polynomial.SynCatEquiv
