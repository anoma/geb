import GebLean.Ramified.Soundness.OneLambda

/-!
# Tests for the simply-typed calculus `1λ(A)`

The bare names `Tm`, `Tm.op`, and `Tm.var` are qualified to `GebLean.Binding`
throughout, since `GebLean.Ramified` carries its own `Tm` (the sorted-signature
term type of `GebLean/Ramified/Term.lean`) that would otherwise shadow the
binder-kit `Tm` used here.
-/

namespace GebLean.Ramified

/-- A closed nullary constant of `oneLambdaSig` elaborates: the zero-constructor
of `natAlgSig` has arity `0`, so `con false` has result `o` and no arguments,
yielding a closed term of sort `o`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con false) (fun j => j.elim0)

/-- The zero-constructor of `natAlgSig` as a closed `oneLambdaSig` term of sort
`o`, reused by the combinator smoke tests below. -/
def olZeroTm : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con false) (fun j => j.elim0)

/-- The `app'`/`lam'`/`boundVar` combinators of `oneLambdaSig` compose: the
closed redex `(λx:o. x) 0` elaborates as a term of sort `o`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  OneLambda.app' (OneLambda.lam' (Binding.Tm.var boundVar)) olZeroTm

/-- The `appSpine` combinator saturates the arity-1 constructor `true` of
`natAlgSig` (result sort `o^1 → o`) with the single argument `0`, yielding a
closed term of sort `o`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  OneLambda.appSpine [RType.o]
    (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true) (fun j => j.elim0))
    (fun i => Fin.cases olZeroTm (fun k => k.elim0) i)

end GebLean.Ramified
