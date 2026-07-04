import GebLean.Ramified.Soundness.Applicative

/-!
# Tests for the applicative binder signatures

The bare names `Tm`, `Tm.op`, and `Tm.var` are qualified to `GebLean.Binding`
throughout: `GebLean.Ramified` carries its own `Tm` (the sorted-signature term
type of `GebLean/Ramified/Term.lean`), which would otherwise shadow the
binder-kit `Tm` used here.
-/

namespace GebLean.Ramified

/-- A closed nullary constant elaborates: the zero-constructor of the `1 + X`
word algebra has arity `0`, so `con o false` has result `o` and no arguments,
yielding a closed term of sort `o`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o false) (fun j => j.elim0)

/-- A `lam` node exercises the binder/argument positions: `lam o o` has result
`o.arrow o` and a single body argument of sort `o` under one binder of sort
`o`; the body is the bound variable, at de Bruijn position `0` of the extended
context `[] ++ [o] = [o]`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.lam RType.o RType.o)
    (fun j => Fin.cases (Binding.Tm.var ⟨⟨0, by decide⟩, rfl⟩) (fun k => k.elim0) j)

/-- The zero-constructor of `natAlgSig` as a closed term of sort `o`, reused by
the combinator smoke tests below. -/
def zeroTm : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o false) (fun j => j.elim0)

/-- The `app'`/`lam'`/`boundVar` combinators compose: the closed redex
`(λx:o. x) 0` elaborates as a term of sort `o`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  app' (lam' (Binding.Tm.var boundVar)) zeroTm

/-- The `appSpine` combinator saturates the arity-1 constructor `true` of
`natAlgSig` (result sort `o^1 → o`) with the single argument `0`, yielding a
closed term of sort `o`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  appSpine [RType.o]
    (Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o true)
      (fun j => j.elim0))
    (fun i => Fin.cases zeroTm (fun k => k.elim0) i)

/-- The zero-constructor of `natAlgSig` at the shifted object sort `Ω o`, a
closed term of sort `Ω o`, used as the recursion argument's subterm below. -/
def omegaZeroTm : Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega RType.o) :=
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con (RType.omega RType.o) false)
    (fun j => j.elim0)

/-- A step-term family for the recurrence over `natAlgSig` at result sort `o`:
the zero-constructor's step is `0`, the successor-constructor's step is the
identity `λx:o. x`. -/
def estepNat : ∀ b : natAlgSig.B,
    Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.replicate (natAlgSig.ar b) RType.o) RType.o) :=
  fun b => match b with
    | false => zeroTm
    | true => lam' (Binding.Tm.var boundVar)

/-- The recursion-argument subterms for the arity-1 constructor `true`: the sole
subterm is `omegaZeroTm`. -/
def recArgsNat : Fin (natAlgSig.ar true) →
    Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega RType.o) :=
  fun _ => omegaZeroTm

/-- A concrete recurrence step over `natAlgSig` at result sort `o`: the redex
`R^o E⃗ (c_true^{Ω o} (Ω-zero))` reduces to `E_true (R^o E⃗ (Ω-zero))`, the
successor step applied to the recursive result on the single subterm. Exercises
`RlmrOStep.recurrence` with the arity-1 constructor, saturating the recurrence
spine and the constructor spine. -/
example :
    RlmrOStep
      (app' (recCombinator estepNat)
        (replicateSpine (natAlgSig.ar true) (RType.omega RType.o)
          (Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.con (RType.omega RType.o) true) (fun j => j.elim0)) recArgsNat))
      (replicateSpine (natAlgSig.ar true) RType.o (estepNat true)
        (fun j => app' (recCombinator estepNat) (recArgsNat j))) :=
  RlmrOStep.recurrence true estepNat recArgsNat

end GebLean.Ramified
