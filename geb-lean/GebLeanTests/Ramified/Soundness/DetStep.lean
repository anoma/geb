import GebLean.Ramified.Soundness.DetStep

/-!
# Tests for the deterministic normalization step

Acceptance examples for `detStep` (task 6.4.1): the deterministic step contracts a
rank-1 β-redex to its `instantiate₁` reduct, and is the identity on the normal
concrete word terms. Acceptance example for `detStep_sound` (task 6.4.2): the
step on a non-normal redex is a genuine `OneLambdaStep`.
-/

namespace GebLean.Ramified

open GebLean.Binding GebLean.Ramified.OneLambda

/-- The deterministic step contracts the identity β-redex `(λx:o. x) c₀` at sort
`o ⟶ o` (β-rank `1`) to its `instantiate₁` reduct, asserted through the dispatch
and node equations rather than kernel reduction. -/
example : detStep (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))
    = Binding.instantiate₁ (conc (natToFreeAlg 0))
        (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))) := by
  set f : Binding.Tm (oneLambdaSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
    OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))) with hf
  set x : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o := conc (natToFreeAlg 0) with hx
  have hbf : betaRedexRank f = 0 := by
    rw [hf, betaRedexRank_lam', betaRedexRank_var]
  have hbx : betaRedexRank x = 0 := rfl
  have hrank : betaRedexRank (OneLambda.app' f x) = 1 := by
    rw [betaRedexRank_app', topBetaRank_app', hbf, hbx, hf, isLam_lam']
    simp [RType.ord_arrow, RType.ord_o]
  rw [detStep_eq, if_pos (by rw [hrank]; decide), hrank, detStepAt_app',
    if_neg (by rw [hbf]; decide), if_neg (by rw [hbx]; decide),
    if_pos (by rw [hf]; exact ⟨isLam_lam' _, by simp [RType.ord_arrow, RType.ord_o]⟩),
    hf, appReduct_lam']

/-- The deterministic step is the identity on the concrete term of any free-algebra
value (a `Normal` term), via `detStep_normal`. -/
example (a : FreeAlg natAlgSig) : detStep (conc a) = conc a :=
  detStep_normal (normal_conc a)

/-- The deterministic step is the identity on the concrete term of the zero word,
an acceptance instance of the normal-form fixpoint. -/
example : detStep (conc (natToFreeAlg 0)) = conc (natToFreeAlg 0) :=
  detStep_normal (normal_conc _)

/-- The deterministic step performs one genuine `OneLambdaStep` on the non-normal
identity β-redex `(λx:o. x) c₀` (β-rank `1`), through `detStep_sound` and the rank
lemmas rather than kernel reduction. -/
example : OneLambdaStep
    (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))
    (detStep (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))) := by
  set f : Binding.Tm (oneLambdaSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
    OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))) with hf
  set x : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o := conc (natToFreeAlg 0) with hx
  have hbf : betaRedexRank f = 0 := by
    rw [hf, betaRedexRank_lam', betaRedexRank_var]
  have hbx : betaRedexRank x = 0 := rfl
  have hrank : betaRedexRank (OneLambda.app' f x) = 1 := by
    rw [betaRedexRank_app', topBetaRank_app', hbf, hbx, hf, isLam_lam']
    simp [RType.ord_arrow, RType.ord_o]
  refine detStep_sound (OneLambda.app' f x) fun hnorm => ?_
  obtain ⟨hβ, -⟩ := (normal_iff _).mp hnorm
  exact one_ne_zero (hrank.symm.trans hβ)

end GebLean.Ramified
