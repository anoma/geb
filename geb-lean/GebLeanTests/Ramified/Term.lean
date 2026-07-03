import GebLean
import GebLean.Ramified.Term

/-!
# Tests for the sorted term layer with clone laws

Executable checks that, over a one-binary-operation signature on `S := Unit`,
`GebLean.Ramified.Tm.subst` performs the swap substitution on a two-variable
term, and that `GebLean.Ramified.Tm.subst_id` and
`GebLean.Ramified.Tm.subst_subst` instantiate on that concrete term.
-/

namespace GebLeanTests.Ramified.Term

open GebLean.Ramified CategoryTheory

/-- A one-operation signature over `Unit`: a single binary operation. -/
def binSig : SortedSig Unit :=
  { Op := Unit, arity := fun _ => [(), ()], result := fun _ => () }

/-- A context of two variables, both at the single sort. -/
abbrev ctx : Ctx Unit := [(), ()]

/-- The term `op (var 0) (var 1)`. -/
def t01 : Tm binSig ctx () :=
  Tm.op () (Fin.cons (Tm.var 0) (Fin.cons (Tm.var 1) finZeroElim))

/-- The term `op (var 1) (var 0)`. -/
def t10 : Tm binSig ctx () :=
  Tm.op () (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 0) finZeroElim))

/-- The swap substitution: position 0 to `var 1`, position 1 to `var 0`. -/
def swap : ∀ i : Fin ctx.length, Tm binSig ctx (ctx.get i) :=
  Fin.cons (Tm.var 1) (Fin.cons (Tm.var 0) finZeroElim)

/-- Substituting `t01` by the swap tuple yields `t10`. -/
example : t01.subst swap = t10 := by
  refine congrArg (Tm.op (sig := binSig) (Γ := ctx) ()) ?_
  funext e
  refine Fin.cases ?_ (fun j => ?_) e
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact k.elim0

/-- The right-unit clone law on the concrete term. -/
example : t01.subst Tm.var = t01 := Tm.subst_id t01

/-- The associativity clone law on the concrete term. -/
example :
    (t01.subst swap).subst swap = t01.subst (fun i => (swap i).subst swap) :=
  Tm.subst_subst t01 swap swap

end GebLeanTests.Ramified.Term
