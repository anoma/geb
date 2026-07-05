import Mathlib.Logic.Relation
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

/-- The constant-`0` λ-abstraction at sort `o → o`, living under one binder of
sort `o`: the head redex of the spine reduction below. -/
def olConstZero : Binding.Tm (oneLambdaSig natAlgSig) ([] ++ [RType.o])
    (RType.arrow RType.o RType.o) :=
  OneLambda.lam' (Binding.Tm.var boundVar)

/-- The one-element argument tuple `[0]` for the spine `o → o` applied at `o`. -/
def olSpineArgs : ∀ i : Fin ([RType.o] : List RType).length,
    Binding.Tm (oneLambdaSig natAlgSig) [] (([RType.o] : List RType).get i) :=
  fun i => Fin.cases olZeroTm (fun k => k.elim0) i

/-- A reduction under an application spine: the `beta` redex forming the head of
a one-element `appSpine` contracts, and `reduces_appSpine` lifts that single
step to a `Relation.ReflTransGen`-reduction of the whole spine. Exercises the
congruence closure of `OneLambdaStep` (through `reduces_appSpine`) on a redex
that has no top-level contractum of its own. -/
example :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.appSpine [RType.o]
        (OneLambda.app' (OneLambda.lam' olConstZero) olZeroTm) olSpineArgs)
      (OneLambda.appSpine [RType.o]
        (Binding.instantiate₁ olZeroTm olConstZero) olSpineArgs) :=
  OneLambda.reduces_appSpine [RType.o] _ _ olSpineArgs
    (Relation.ReflTransGen.single (OneLambdaStep.beta olConstZero olZeroTm))

end GebLean.Ramified
