import GebLean.Ramified.Soundness.OneLambdaEval

/-!
# Tests for the standard `1λ(A)` evaluator

Acceptance tests for `oneEval` (task 6.3.9a): the concrete term of a value
evaluates back to the value, and the identity β-redex over that concrete term
evaluates to the value.
-/

namespace GebLean.Ramified

open GebLean.Binding GebLean.Ramified.OneLambda

/-- The concrete term of the zero word evaluates to the zero word: `oneEval`
inverts the `con`-node fold `conc` (Leivant III section 4.2). -/
example : oneEval (conc (natToFreeAlg 0)) finZeroElim = natToFreeAlg 0 :=
  oneEval_conc _ _

/-- The concrete term of a general value evaluates to that value, the acceptance
instance of `oneEval_conc`. -/
example (a : FreeAlg natAlgSig) : oneEval (conc a) finZeroElim = a :=
  oneEval_conc a _

/-- The task-6.3.8 acceptance redex `(λx:o. x) c₀` evaluates to the zero word:
the standard denotation of the identity β-redex over the concrete zero term is
the zero word itself. -/
example :
    oneEval (OneLambda.app'
        (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
        (conc (natToFreeAlg 0))) finZeroElim = natToFreeAlg 0 := by
  simp only [oneEval_app', oneEval_lam']
  rw [oneEval_boundVar_envExtend]
  exact oneEval_conc _ _

/-- The concrete term of the one word evaluates to the one word, a compositional
check exercising `oneEval` on a `con`-headed application spine of depth one. -/
example : oneEval (conc (natToFreeAlg 1)) finZeroElim = natToFreeAlg 1 :=
  oneEval_conc _ _

/-- The β-rule of `1λ(A)` is sound for `oneEval`: the redex `(λx:o. b) N` and its
contractum `b[x := N]` have equal denotation, via `oneEval_instantiate₁` and the
node rules (the denotational payload consumed by step soundness). -/
example (b : Binding.Tm (oneLambdaSig natAlgSig) ([] ++ [RType.o]) RType.o)
    (N : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o) :
    oneEval (OneLambda.app' (OneLambda.lam' b) N) finZeroElim
      = oneEval (Binding.instantiate₁ N b) finZeroElim := by
  rw [oneEval_instantiate₁, oneEval_app', oneEval_lam']
  rfl

/-- Injectivity of `conc` is available as an interface statement (task 6.3.9a):
equal concrete terms come from equal values. -/
example (a b : FreeAlg natAlgSig) (h : conc a = conc b) : a = b := conc_injective h

/-- Step soundness (task 6.3.9b): a `OneLambdaStep`-reduction preserves the
denotation. The β-redex `(λx:o. x) c₀` steps to `c₀`'s concrete term and both
denote the zero word. -/
example :
    oneEval (OneLambda.app'
        (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
        (conc (natToFreeAlg 0))) finZeroElim
      = oneEval (Binding.instantiate₁ (conc (natToFreeAlg 0))
          (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o)))) finZeroElim :=
  oneEval_step (OneLambdaStep.beta (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o)))
    (conc (natToFreeAlg 0))) finZeroElim

/-- Step soundness at a destructor hit: `dstr₀ (c_true a) ⇒ a` preserves the
denotation, a direct instance of `oneEval_step` on `OneLambdaStep.dstrHit`. -/
example (a : Fin (natAlgSig.ar true) → Binding.Tm (oneLambdaSig natAlgSig) [] RType.o) :
    oneEval (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig natAlgSig)
          (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0))
        (OneLambda.replicateSpine (natAlgSig.ar true) RType.o
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true)
            (fun k => k.elim0)) a)) finZeroElim
      = oneEval (a ⟨0, by decide⟩) finZeroElim :=
  oneEval_step (OneLambdaStep.dstrHit ⟨0, by decide⟩ (by decide) a) finZeroElim

/-- Multi-step soundness (task 6.3.9b): `oneEval_reduces` on the reflexive-
transitive lift of the acceptance β-redex evaluates `(λx:o. x) c₀` to the zero
word through the whole reduction sequence. -/
example :
    oneEval (OneLambda.app'
        (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
        (conc (natToFreeAlg 0))) finZeroElim = natToFreeAlg 0 := by
  rw [oneEval_reduces
    (OneLambda.reduces_beta (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o)))
      (conc (natToFreeAlg 0))) finZeroElim,
    oneEval_instantiate₁, oneEval_boundVar_envExtend]
  exact oneEval_conc _ _

end GebLean.Ramified
