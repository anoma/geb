import GebLean
import GebLean.Ramified.Interp

/-!
# Tests for sorted models and the interpretative setoid

Executable checks that, over a one-binary-operation signature on `S := Unit`,
`GebLean.Ramified.Tm.eval` computes in a `Nat` model that reads addition,
that `GebLean.Ramified.Tm.eval_subst` instantiates on a concrete term, and
that `GebLean.Ramified.interpSetoid` relates two syntactically distinct terms
whose interpretations agree (the swapped-argument pair, agreeing by
commutativity of addition). The signature, model, environment, and terms are
`abbrev`s so that evaluation reduces definitionally, exercising the
computability of `Tm.eval`.
-/

namespace GebLeanTests.Ramified.Interp

open GebLean.Ramified CategoryTheory

/-- A one-operation signature over `Unit`: a single binary operation. -/
abbrev binSig : SortedSig Unit :=
  { Op := Unit, arity := fun _ => [(), ()], result := fun _ => () }

/-- A context of two variables, both at the single sort. -/
abbrev ctx : Ctx Unit := [(), ()]

/-- The term `op (var 0) (var 1)`. -/
abbrev t01 : Tm binSig ctx () :=
  Tm.op () (Fin.cons (Tm.var 0) (Fin.cons (Tm.var 1) finZeroElim))

/-- The term `op (var 1) (var 0)`. -/
abbrev t10 : Tm binSig ctx () :=
  Tm.op () (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 0) finZeroElim))

/-- The swap substitution: position 0 to `var 1`, position 1 to `var 0`. -/
def swap : ∀ i : Fin ctx.length, Tm binSig ctx (ctx.get i) :=
  Fin.cons (Tm.var 1) (Fin.cons (Tm.var 0) finZeroElim)

/-- The `Nat` model reading the binary operation as addition. -/
abbrev natModel : SortedModel binSig where
  carrier := fun _ => Nat
  interpOp := fun _ args => args 0 + args 1

/-- A concrete environment: position 0 to `3`, position 1 to `5`. -/
abbrev env : natModel.Env ctx :=
  Fin.cons (3 : Nat) (Fin.cons (5 : Nat) finZeroElim)

/-- The presentation carrying `binSig` and its `Nat` standard model. -/
abbrev natPres : Presentation where
  S := Unit
  sig := binSig
  IsObj := fun _ => True
  alg := natAlgSig
  std := natModel

-- Evaluation reads the environment and adds: `t01` at `[3, 5]` is `8`.
#guard t01.eval natModel env = 8

/-- The semantic clone law on the concrete term. -/
example :
    (t01.subst swap).eval natModel env =
      t01.eval natModel (fun i => (swap i).eval natModel env) :=
  Tm.eval_subst natModel t01 swap env

/-- The swapped-argument terms are related by the interpretative setoid: their
interpretations agree under every environment, by commutativity of addition. -/
example : (interpSetoid natPres ctx ()).r t01 t10 :=
  fun ρ => Nat.add_comm (ρ 0) (ρ 1)

end GebLeanTests.Ramified.Interp
