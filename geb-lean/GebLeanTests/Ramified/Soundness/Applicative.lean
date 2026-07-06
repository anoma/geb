import GebLean.Ramified.Soundness.Applicative
import GebLean.Ramified.Examples

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
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o (Or.inl rfl) false)
    (fun j => j.elim0)

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
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o (Or.inl rfl) false)
    (fun j => j.elim0)

/-- The `app'`/`lam'`/`boundVar` combinators compose: the closed redex
`(λx:o. x) 0` elaborates as a term of sort `o`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  app' (lam' (Binding.Tm.var boundVar)) zeroTm

/-- The `appSpine` combinator saturates the arity-1 constructor `true` of
`natAlgSig` (result sort `o^1 → o`) with the single argument `0`, yielding a
closed term of sort `o`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  appSpine [RType.o]
    (Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o (Or.inl rfl) true)
      (fun j => j.elim0))
    (fun i => Fin.cases zeroTm (fun k => k.elim0) i)

/-- The zero-constructor of `natAlgSig` at the shifted object sort `Ω o`, a
closed term of sort `Ω o`, used as the recursion argument's subterm below. -/
def omegaZeroTm : Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega RType.o) :=
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con (RType.omega RType.o) (Or.inr rfl) false)
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
            (RlmrOOp.con (RType.omega RType.o) (Or.inr rfl) true) (fun j => j.elim0)) recArgsNat))
      (replicateSpine (natAlgSig.ar true) RType.o (estepNat true)
        (fun j => app' (recCombinator estepNat) (recArgsNat j))) :=
  RlmrOStep.recurrence true estepNat recArgsNat

/-- The standard-model evaluator computes the zero-constructor's denotation:
`appEval` of the closed nullary constant `c_false^o` is the numeral `0` of the
standard carrier, `natToFreeAlg 0`. Exercises `appEval_con`. -/
example (ρ : ∀ i : Fin ([] : Binding.Ctx RType).length,
    RType.interp (FreeAlg natAlgSig) (([] : Binding.Ctx RType).get i)) :
    appEval (Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o (Or.inl rfl) false)
      (fun j => j.elim0)) ρ = natToFreeAlg 0 := by
  simp only [appEval_con]
  exact congrArg (FreeAlg.mk (A := natAlgSig) false) (funext (fun i => i.elim0))

/-- The standard-model evaluator computes the identity function's denotation:
`appEval` of the closed identity term `λx:o. x` is the identity on the standard
carrier. Exercises `appEval_lam'` and `appEval_var` through the binder. -/
example (ρ : ∀ i : Fin ([] : Binding.Ctx RType).length,
    RType.interp (FreeAlg natAlgSig) (([] : Binding.Ctx RType).get i))
    (v : RType.interp (FreeAlg natAlgSig) RType.o) :
    appEval (lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o)))) ρ v = v := by
  simp only [appEval_lam', appEval_var, envExtend, boundVar, childEnv,
    Binding.Var.appendRight, List.length_nil]
  rw [dif_neg (Nat.not_lt_zero _)]
  exact cast_eq _ _

/-- The Proposition 7 translation elaborates on the monotone-recurrence
identifier `ramAdd` (Leivant III §2.4(2)'s addition): the ramified addition
`o, Ω o → o` translates to an applicative term at the same context and sort.
Exercises the `mrec` case of `prop7Translate` and, through addition's step
functions, the explicit-definition case. -/
example : Binding.Tm (rlmrOSig natAlgSig) [RType.o, RType.omega RType.o] RType.o :=
  prop7Translate ramAdd

/-- The Proposition 7 soundness agreement (Leivant III §4.1, arm `(1)⟹(4)`) holds
on the monotone-recurrence identifier `ramAdd`: at every environment, the
standard-model denotation of the applicative translation `prop7Translate ramAdd`
equals `ramAdd`'s own denotation `RIdent.interp ramAdd`. The acceptance witness
for `prop7Translate_interp`. -/
example (ρ : ∀ i : Fin ([RType.o, RType.omega RType.o] : Binding.Ctx RType).length,
    RType.interp (FreeAlg natAlgSig)
      (([RType.o, RType.omega RType.o] : Binding.Ctx RType).get i)) :
    appEval (prop7Translate ramAdd) ρ = RIdent.interp ramAdd ρ :=
  prop7Translate_interp ramAdd ρ

/-- The Proposition 7 translation elaborates on the flat-recurrence identifier
`ramDstr` (the predecessor): the ramified destructor `o → o` translates to an
applicative term. Exercises the `frec` case of `prop7Translate` at the object
result sort `o` (the `case`/`dstr` realization without η-expansion). -/
example : Binding.Tm (rlmrOSig natAlgSig) [RType.o] RType.o :=
  prop7Translate ramDstr

/-- The Proposition 7 soundness agreement (Leivant III §4.1, arm `(1)⟹(4)`) holds
on the flat-recurrence identifier `ramDstr`: at every environment, the
standard-model denotation of the applicative translation `prop7Translate ramDstr`
equals `ramDstr`'s own denotation `RIdent.interp ramDstr`. Exercises
`prop7Translate_interp` through the `frec` case, spot-checking the
`PolyFix.ind`/defeq reduction of `appEval_caseAtType` end-to-end. -/
example (ρ : ∀ i : Fin ([RType.o] : Binding.Ctx RType).length,
    RType.interp (FreeAlg natAlgSig) (([RType.o] : Binding.Ctx RType).get i)) :
    appEval (prop7Translate ramDstr) ρ = RIdent.interp ramDstr ρ :=
  prop7Translate_interp ramDstr ρ

/-- The Proposition 7 translation elaborates on a flat-recurrence identifier at a
higher, arrow-typed result sort: `ramCase (o → o) : (o → o), (o → o), o → (o → o)`
translates to an applicative term. Exercises the `frec` case together with the
η-expansion of `caseAtType` through the arrow codomain. -/
example :
    Binding.Tm (rlmrOSig natAlgSig)
      ([RType.arrow RType.o RType.o, RType.arrow RType.o RType.o] ++ [RType.o])
      (RType.arrow RType.o RType.o) :=
  prop7Translate (ramCase (RType.arrow RType.o RType.o))

end GebLean.Ramified
