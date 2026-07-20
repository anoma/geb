import GebLean
import GebLean.Ramified.Polynomial.Term

/-!
# Tests for the sorted term layer on the slice free monad

Proof-level checks over a two-sorted toy signature (`SortedSig Bool`, one
operation per sort with mixed arity) that `GebLean.Ramified.Polynomial.Tm'.var`
substitutes correctly at each context position
(`GebLean.Ramified.Polynomial.Tm'.var_subst`), and that
`GebLean.Ramified.Polynomial.Tm'.subst_id` and
`GebLean.Ramified.Polynomial.Tm'.subst_subst` instantiate on a concrete term.
-/

namespace GebLeanTests.Ramified.Polynomial.Term

open GebLean.Ramified GebLean.Ramified.Polynomial

/-- A two-sorted signature over `Bool`: operation `false` (result sort
`false`) takes one argument of sort `true`; operation `true` (result sort
`true`) takes two arguments of sort `false`. -/
def twoSortedSig : SortedSig Bool :=
  { Op := Bool
  , arity := fun b => if b then [false, false] else [true]
  , result := fun b => b }

/-- A context of two variables: position `0` at sort `false`, position `1`
at sort `true`. -/
abbrev ctx : Ctx Bool := [false, true]

/-- The subterm `op false (var 1)`, at sort `false`. -/
def sub1 : Tm' twoSortedSig ctx false :=
  Tm'.op (sig := twoSortedSig) (Γ := ctx) false (Fin.cons (Tm'.var 1) finZeroElim)

/-- The term `op true (var 0) sub1`, at sort `true`. -/
def t : Tm' twoSortedSig ctx true :=
  Tm'.op (sig := twoSortedSig) (Γ := ctx) true (Fin.cons (Tm'.var 0) (Fin.cons sub1 finZeroElim))

/-- Substituting the variable at position `0` by a tuple `σ` selects `σ 0`. -/
example (σ : ∀ i : Fin ctx.length, Tm' twoSortedSig ctx (ctx.get i)) :
    (Tm'.var (0 : Fin ctx.length)).subst σ = σ 0 :=
  Tm'.var_subst 0 σ

/-- Substituting the variable at position `1` by a tuple `σ` selects `σ 1`. -/
example (σ : ∀ i : Fin ctx.length, Tm' twoSortedSig ctx (ctx.get i)) :
    (Tm'.var (1 : Fin ctx.length)).subst σ = σ 1 :=
  Tm'.var_subst 1 σ

/-- The right-unit clone law on the concrete term `t`. -/
example : t.subst Tm'.var = t := Tm'.subst_id t

/-- The substitution tuple sending position `0` to `sub1` and position `1` to
`var 1`. -/
def sigma : ∀ i : Fin ctx.length, Tm' twoSortedSig ctx (ctx.get i) :=
  Fin.cons sub1 (Fin.cons (Tm'.var 1) finZeroElim)

/-- The associativity clone law on the concrete term `t`. -/
example :
    (t.subst sigma).subst sigma = t.subst (fun i => (sigma i).subst sigma) :=
  Tm'.subst_subst t sigma sigma

/-- The argument tuple of `sub1`: its single argument at position `0` is
`var 1`. -/
def sub1args :
    ∀ i : Fin (twoSortedSig.arity false).length,
      Tm' twoSortedSig ctx ((twoSortedSig.arity false).get i) :=
  Fin.cons (Tm'.var 1) finZeroElim

/-- The bridge equivalence carries a primed variable term to the legacy
`Tm.var`. -/
example :
    tmSliceEquiv ctx _ (Tm'.var (sig := twoSortedSig) (1 : Fin ctx.length)) =
      Tm.var (sig := twoSortedSig) 1 :=
  tmSliceEquiv_var (sig := twoSortedSig) (Γ := ctx) 1

/-- The bridge equivalence carries a primed operation term to the legacy
`Tm.op` with arguments mapped through the equivalence. -/
example :
    tmSliceEquiv ctx _ (Tm'.op (sig := twoSortedSig) (Γ := ctx) false sub1args) =
      Tm.op (sig := twoSortedSig) false (fun i => tmSliceEquiv ctx _ (sub1args i)) :=
  tmSliceEquiv_op (sig := twoSortedSig) (Γ := ctx) false sub1args

/-- The bridge equivalence intertwines primed substitution with legacy
`Tm.subst` on the concrete term `t`. -/
example :
    tmSliceEquiv ctx _ (t.subst sigma) =
      (tmSliceEquiv ctx _ t).subst (fun i => tmSliceEquiv ctx _ (sigma i)) :=
  tmSliceEquiv_subst t sigma

/-- The transported round trip: the inverse of `tmSliceEquiv` recovers `t`. -/
example : (tmSliceEquiv ctx _).symm (tmSliceEquiv ctx _ t) = t :=
  Equiv.symm_apply_apply (tmSliceEquiv ctx _) t

end GebLeanTests.Ramified.Polynomial.Term
