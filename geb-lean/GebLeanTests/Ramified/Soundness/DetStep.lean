import GebLean.Ramified.Soundness.DetStep

/-!
# Tests for the deterministic normalization step

Acceptance examples for `detStep` (task 6.4.1): the deterministic step contracts a
rank-1 β-redex to its `instantiate₁` reduct, and is the identity on the normal
concrete word terms. Acceptance example for `detStep_sound` (task 6.4.2): the
step on a non-normal redex is a genuine `OneLambdaStep`. Acceptance examples for
`detIter` and the deterministic clock (task 6.4.4): the iteration is a reduction
sequence, fixes normal terms, and normalizes a small term within its
`lemma12_clock` value.
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

/-- Rank non-increase of the β worker (task 6.4.3): on the rank-`1` identity
redex `(λx:o. x) c₀`, the worker `detStepAt 1` keeps the β-rank at most `1`, via
`betaRedexRank_detStepAt_le` and the rank node equations. -/
example : betaRedexRank (detStepAt 1 (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))) ≤ 1 := by
  set f : Binding.Tm (oneLambdaSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
    OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))) with hf
  set x : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o := conc (natToFreeAlg 0) with hx
  have hbf : betaRedexRank f = 0 := by rw [hf, betaRedexRank_lam', betaRedexRank_var]
  have hbx : betaRedexRank x = 0 := rfl
  have hrank : betaRedexRank (OneLambda.app' f x) = 1 := by
    rw [betaRedexRank_app', topBetaRank_app', hbf, hbx, hf, isLam_lam']
    simp [RType.ord_arrow, RType.ord_o]
  exact betaRedexRank_detStepAt_le 1 _ (le_of_eq hrank)

/-- The deterministic iteration is a reduction sequence (task 6.4.4): the
identity β-redex `(λx:o. x) c₀` reduces to its two-fold `detStep` image, via
`detIter_reduces`. -/
example : Relation.ReflTransGen OneLambdaStep
    (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))
    (detIter 2 (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))) :=
  detIter_reduces 2 _

/-- A normal term is a fixpoint of the deterministic iteration at every count
(task 6.4.4): the concrete term of any free-algebra value is unchanged by
`detIter`, via `detIter_normal_stable`. -/
example (n : ℕ) (a : FreeAlg natAlgSig) : detIter n (conc a) = conc a :=
  detIter_normal_stable n (normal_conc a)

/-- One deterministic rank-elimination cycle (task 6.4.4): from the rank-1
identity β-redex `(λx:o. x) c₀`, at most `Tm.size` iterations of the
deterministic step reach a β-normal term within the height bound, via
`det_cycle` and the rank node equations. -/
example : ∃ k ≤ Tm.size (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0))),
    betaRedexRank (detIter k (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))) = 0 ∧
    Tm.height (detIter k (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0))))
      ≤ 2 ^ Tm.height (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0))) := by
  set f : Binding.Tm (oneLambdaSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
    OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))) with hf
  set x : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o := conc (natToFreeAlg 0) with hx
  have hbf : betaRedexRank f = 0 := by rw [hf, betaRedexRank_lam', betaRedexRank_var]
  have hbx : betaRedexRank x = 0 := rfl
  have hrank : betaRedexRank (OneLambda.app' f x) = 1 := by
    rw [betaRedexRank_app', topBetaRank_app', hbf, hbx, hf, isLam_lam']
    simp [RType.ord_arrow, RType.ord_o]
  obtain ⟨k, hk, hrank', hheight, -⟩ :=
    det_cycle 1 le_rfl (OneLambda.app' f x) (le_of_eq hrank)
  exact ⟨k, hk, by omega, hheight⟩

/-- The deterministic clock (task 6.4.4): the identity β-redex `(λx:o. x) c₀`
normalizes within its `lemma12_clock` value
`(redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)`, the instance of
`detIter_normal` — asserted through the lemmas, not kernel reduction. -/
example : Normal (detIter
    ((redexRank (OneLambda.app'
        (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
        (conc (natToFreeAlg 0))) + 1)
      * tower (redexRank (OneLambda.app'
          (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
          (conc (natToFreeAlg 0))) + 1)
        (Tm.height (OneLambda.app'
          (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
          (conc (natToFreeAlg 0)))))
    (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))) :=
  detIter_normal _

/-- β-normality preservation of the ι worker (task 6.4.3): on the β-normal
saturated destructor redex `dstr₀ c₀`, the ι worker `detIotaStep` keeps the
β-rank at `0`, via `betaRedexRank_detIotaStep`. -/
example : betaRedexRank (detIotaStep (OneLambda.app'
      (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
        (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0))
      (conc (natToFreeAlg 0)))) = 0 :=
  betaRedexRank_detIotaStep _ rfl

/-- Strict size decrease of the ι worker (task 6.4.3): on the β-normal saturated
destructor redex `dstr₀ c₀` (carrying an ι-redex), the ι worker `detIotaStep`
strictly decreases the size, via `size_detIotaStep_lt` and the rank/ι detectors. -/
example : Tm.size (detIotaStep (OneLambda.app'
      (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
        (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0))
      (conc (natToFreeAlg 0))))
    < Tm.size (OneLambda.app'
      (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
        (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0))
      (conc (natToFreeAlg 0))) :=
  size_detIotaStep_lt _ rfl (by rw [hasIota_app']; rfl)

end GebLean.Ramified
