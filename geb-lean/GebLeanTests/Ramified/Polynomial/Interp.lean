import GebLean
import GebLean.Ramified.Polynomial.Interp

/-!
# Tests for primed evaluation and the interpretative quotient

Proof-level checks over a one-binary-operation signature on `S := Unit` that
`GebLean.Ramified.Polynomial.Tm'.eval` computes in a `Nat` model reading
addition (through the named computation rules `Tm'.eval_op` and `Tm'.eval_var`,
not kernel reduction of the underlying `W`-tree), that
`GebLean.Ramified.Polynomial.Tm'.eval_subst` instantiates on a concrete term,
that `GebLean.Ramified.Polynomial.interpSetoid'` relates two syntactically
distinct terms whose interpretations agree, and that
`GebLean.Ramified.Polynomial.tmSliceEquiv_eval` intertwines primed and legacy
evaluation on a concrete term.
-/

namespace GebLeanTests.Ramified.Polynomial.Interp

open GebLean.Ramified GebLean.Ramified.Polynomial CategoryTheory

/-- A one-operation signature over `Unit`: a single binary operation. -/
abbrev binSig : SortedSig Unit :=
  { Op := Unit, arity := fun _ => [(), ()], result := fun _ => () }

/-- A context of two variables, both at the single sort. -/
abbrev ctx : Ctx Unit := [(), ()]

/-- The argument tuple `(var 0, var 1)`. -/
def args01 : ∀ i : Fin (binSig.arity ()).length, Tm' binSig ctx ((binSig.arity ()).get i) :=
  Fin.cons (Tm'.var 0) (Fin.cons (Tm'.var 1) finZeroElim)

/-- The argument tuple `(var 1, var 0)`. -/
def args10 : ∀ i : Fin (binSig.arity ()).length, Tm' binSig ctx ((binSig.arity ()).get i) :=
  Fin.cons (Tm'.var 1) (Fin.cons (Tm'.var 0) finZeroElim)

/-- The term `op (var 0) (var 1)`. -/
def t01 : Tm' binSig ctx () := Tm'.op (sig := binSig) (Γ := ctx) () args01

/-- The term `op (var 1) (var 0)`. -/
def t10 : Tm' binSig ctx () := Tm'.op (sig := binSig) (Γ := ctx) () args10

/-- The swap substitution: position 0 to `var 1`, position 1 to `var 0`. -/
def swap : ∀ i : Fin ctx.length, Tm' binSig ctx (ctx.get i) :=
  Fin.cons (Tm'.var 1) (Fin.cons (Tm'.var 0) finZeroElim)

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

/-- Evaluation reads the environment through `Tm'.eval_var`. -/
example (ρ : natModel.Env ctx) (i : Fin ctx.length) :
    (Tm'.var (sig := binSig) i).eval natModel ρ = ρ i :=
  Tm'.eval_var natModel ρ i

/-- Evaluation of an operation reduces through `Tm'.eval_op`. -/
example (ρ : natModel.Env ctx) :
    t01.eval natModel ρ = natModel.interpOp () (fun i => (args01 i).eval natModel ρ) :=
  Tm'.eval_op natModel ρ () args01

/-- Evaluation reads the environment and adds: `t01` at `[3, 5]` is `8`,
computed through the named computation rules. -/
example : t01.eval natModel env = 8 := by
  rw [t01, Tm'.eval_op natModel env () args01]
  change Tm'.eval natModel env (args01 0) + Tm'.eval natModel env (args01 1) = 8
  rw [show args01 0 = Tm'.var 0 from rfl, show args01 1 = Tm'.var 1 from rfl,
    Tm'.eval_var, Tm'.eval_var]
  rfl

/-- The semantic clone law on the concrete term. -/
example :
    (t01.subst swap).eval natModel env =
      t01.eval natModel (fun i => (swap i).eval natModel env) :=
  Tm'.eval_subst natModel t01 swap env

/-- The swapped-argument terms are related by the interpretative setoid: their
interpretations agree under every environment, by commutativity of addition. -/
example : (interpSetoid' natPres ctx ()).r t01 t10 := by
  intro ρ
  change Tm'.eval natModel ρ t01 = Tm'.eval natModel ρ t10
  rw [t01, t10, Tm'.eval_op natModel ρ () args01, Tm'.eval_op natModel ρ () args10]
  change Tm'.eval natModel ρ (args01 0) + Tm'.eval natModel ρ (args01 1) =
    Tm'.eval natModel ρ (args10 0) + Tm'.eval natModel ρ (args10 1)
  rw [show args01 0 = Tm'.var 0 from rfl, show args01 1 = Tm'.var 1 from rfl,
    show args10 0 = Tm'.var 1 from rfl, show args10 1 = Tm'.var 0 from rfl]
  simp only [Tm'.eval_var]
  exact Nat.add_comm _ _

/-- Primed evaluation agrees with legacy evaluation across the bridge
equivalence on the concrete term. -/
example (ρ : natModel.Env ctx) :
    (tmSliceEquiv ctx () t01).eval natModel ρ = t01.eval natModel ρ :=
  tmSliceEquiv_eval natModel ρ t01

end GebLeanTests.Ramified.Polynomial.Interp
