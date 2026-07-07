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

end GebLean.Ramified
