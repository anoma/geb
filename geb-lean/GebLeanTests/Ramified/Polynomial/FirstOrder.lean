import GebLean
import GebLean.Ramified.Polynomial.FirstOrder
import GebLeanTests.Ramified.Polynomial.Ident

/-!
# Tests for the primed first-order sub-theory and inclusion functor

Executable checks over the `1 + X` word algebra `natAlgSig`
(`GebLeanTests.Ramified.Polynomial.IdentTest.A`). The body-level restriction
`Tm'.TowerSorts` is checked on a tower-sorted variable and refuted on an
arrow-sorted one; `RIdent'.FirstOrder` is checked on the predecessor
recurrence `pred'` (`GebLeanTests/Ramified/Polynomial/Ident.lean`, a flat
recurrence at tower sorts) and refuted on an identifier at an arrow sort. The
term translation is checked through `foTm_eval` at the predecessor's
first-order operation term, and the inclusion functor's action on the
corresponding morphism is the `foTm`-translated tuple.

Tower-sort membership is decided through `rTypeSliceEquiv_isTower` and the
legacy `DecidablePred RType.IsTower` instance rather than by kernel reduction
of the underlying slice `W`-trees.
-/

namespace GebLeanTests.Ramified.Polynomial.FirstOrderTest

open GebLean.Ramified GebLean.Ramified.Polynomial CategoryTheory
open GebLeanTests.Ramified.Polynomial.IdentTest (A idZero' idVar' pred' predClauses)

/-- The base object sort is a tower sort. -/
theorem isTower_o : RType'.IsTower RType'.o := by
  rw [rTypeSliceEquiv_isTower, rTypeSliceEquiv_o]
  decide

/-- No arrow sort is a tower sort. -/
theorem not_isTower_arrow : ¬ RType'.IsTower (RType'.arrow RType'.o RType'.o) := by
  rw [rTypeSliceEquiv_isTower, rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]
  decide

-- The body-level restriction holds at a tower-sorted variable.
example : (Tm'.var (sig := defnSig' A 0 finZeroElim) (Γ := [RType'.o]) 0).TowerSorts := by
  rw [Tm'.towerSorts_var]
  exact isTower_o

-- The body-level restriction fails at an arrow-sorted variable.
example : ¬ (Tm'.var (sig := defnSig' A 0 finZeroElim)
    (Γ := [RType'.arrow RType'.o RType'.o]) 0).TowerSorts := by
  rw [Tm'.towerSorts_var]
  exact not_isTower_arrow

/-- The zero clause of the predecessor recurrence is first-order: empty
context, result `o`, and a constructor body at `o`. -/
theorem idZero_fo : idZero'.FirstOrder := by
  unfold idZero'
  rw [RIdent'.firstOrder_defn]
  exact ⟨fun i => i.elim0, isTower_o, ⟨isTower_o, fun e => e.elim0⟩, fun j => j.elim0⟩

/-- The successor clause of the predecessor recurrence is first-order:
context `[o]`, result `o`, and a variable body at `o`. -/
theorem idVar_fo : idVar'.FirstOrder := by
  unfold idVar'
  rw [RIdent'.firstOrder_defn]
  exact ⟨fun i => Fin.cases isTower_o (fun j => j.elim0) i, isTower_o, isTower_o,
    fun j => j.elim0⟩

/-- The predecessor recurrence is first-order: its context `[o]` and result
`o` are tower sorts, and both clauses are first-order. -/
theorem pred_fo : pred'.FirstOrder := by
  change (RIdent'.frec ([] : List RType') RType'.o predClauses).FirstOrder
  rw [RIdent'.firstOrder_frec]
  refine ⟨fun i => Fin.cases isTower_o (fun j => j.elim0) i, isTower_o, fun i => ?_⟩
  cases i with
  | false => exact idZero_fo
  | true => exact idVar_fo

/-- The identity identifier at an arrow sort: an explicit definition whose
context and result are `o -> o`. -/
def idArrow' : RIdent' A [RType'.arrow RType'.o RType'.o] (RType'.arrow RType'.o RType'.o) :=
  RIdent'.defn ⟨0, finZeroElim, Tm'.var 0⟩ finZeroElim

-- An identifier at an arrow sort is not first-order.
example : ¬ idArrow'.FirstOrder := by
  unfold idArrow'
  rw [RIdent'.firstOrder_defn]
  rintro ⟨hΓ, -, -, -⟩
  exact not_isTower_arrow (hΓ 0)

/-- The predecessor restated inside the sub-theory: the morphism tuple
applying the first-order predecessor operation to its context's variable. -/
def foPredTuple : HomTuple' (firstOrderPresentation A) [RType'.o] [RType'.o] :=
  Fin.cons
    (Tm'.op (sig := firstOrderSig A)
      (Sum.inl (Sum.inr ⟨[RType'.o], RType'.o, ⟨pred', pred_fo⟩⟩))
      (fun k => Tm'.var k))
    finZeroElim

/-- The predecessor context `[o]`, as an object of the first-order syntactic
category. -/
abbrev foSrc : SynCat' (firstOrderPresentation A)
    (interpQuotRel' (firstOrderPresentation A)) := [RType'.o]

/-- The predecessor as a morphism `[o] ⟶ [o]` of the first-order syntactic
category. -/
def foPredMor : foSrc ⟶ foSrc := Quotient.mk _ foPredTuple

-- The inclusion functor's action on a first-order morphism is the
-- `foTm`-translated representative tuple.
example : (foInclusion A).map foPredMor
    = Quotient.mk _ (fun i => foTm A (foPredTuple i)) := rfl

-- The translated predecessor term denotes the predecessor's interpretation in
-- the host higher-order standard model (through `foTm_eval`).
example (ρ : (standardModel (higherOrder' A)).Env [RType'.o]) :
    (foTm A (foPredTuple 0)).eval (standardModel (higherOrder' A)) ρ = pred'.interp ρ :=
  (foTm_eval A (foPredTuple 0) ρ).trans
    ((Tm'.eval_op (standardModel (firstOrderPresentation A)) ρ _ _).trans
      (congrArg pred'.interp (funext fun i => Tm'.eval_var _ ρ i)))

end GebLeanTests.Ramified.Polynomial.FirstOrderTest
