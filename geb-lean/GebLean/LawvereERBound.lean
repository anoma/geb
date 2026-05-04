import GebLean.LawvereER
import GebLean.Utilities.Tower
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Tower Bound for Elementary Recursive Terms

Every `ERMor1 n` term's interpretation is dominated by a fixed-height
tower of twos applied to the context's maximum (plus padding).  This
witnesses that the elementary recursive functions are a strict subset
of the primitive recursive functions — tetration escapes this bound.
-/

namespace GebLean

/-- Maximum entry of a context, returning 0 when empty. -/
def maxCtx {n : ℕ} (ctx : Fin n → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup ctx

/-- Each context entry is bounded by `maxCtx`. -/
theorem le_maxCtx {n : ℕ} (ctx : Fin n → ℕ) (i : Fin n) :
    ctx i ≤ maxCtx ctx :=
  Finset.le_sup (f := ctx) (Finset.mem_univ i)

/-- `2 ≤ maxCtx ctx + 2` holds unconditionally. -/
theorem two_le_maxCtx_plus_two {n : ℕ} (ctx : Fin n → ℕ) :
    2 ≤ maxCtx ctx + 2 := by omega

/-- Bounded sum is dominated by bound times max entry. -/
theorem natBSum_le_mul_max (b : ℕ) (f : ℕ → ℕ) (M : ℕ)
    (h : ∀ i < b, f i ≤ M) : natBSum b f ≤ b * M := by
  induction b with
  | zero => simp [natBSum]
  | succ b ih =>
    change natBSum b f + f b ≤ (b + 1) * M
    have h_fb : f b ≤ M := h b (Nat.lt_succ_self _)
    have h_ih_applied : natBSum b f ≤ b * M :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    calc natBSum b f + f b
        ≤ b * M + M := by omega
      _ = (b + 1) * M := by rw [Nat.succ_mul]

/-- Bounded product is dominated by max entry raised to bound. -/
theorem natBProd_le_pow_max (b : ℕ) (f : ℕ → ℕ) (M : ℕ)
    (h : ∀ i < b, f i ≤ M) : natBProd b f ≤ M ^ b := by
  induction b with
  | zero => simp [natBProd]
  | succ b ih =>
    change natBProd b f * f b ≤ M ^ (b + 1)
    have h_fb : f b ≤ M := h b (Nat.lt_succ_self _)
    have h_ih : natBProd b f ≤ M ^ b :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    calc natBProd b f * f b
        ≤ M ^ b * M := Nat.mul_le_mul h_ih h_fb
      _ = M ^ (b + 1) := by rw [pow_succ]

/-- Consing a bounded element onto a context tail preserves the
ambient max bound. -/
theorem maxCtx_cons_le {n : ℕ} (i : ℕ) (ctx : Fin (n + 1) → ℕ)
    (hi : i ≤ maxCtx ctx) :
    maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx := by
  apply Finset.sup_le
  intro j _
  refine Fin.cases ?_ ?_ j
  · change i ≤ maxCtx ctx
    exact hi
  · intro j'
    change ctx j'.succ ≤ maxCtx ctx
    exact le_maxCtx ctx _

/-- Given a family `g : Fin k → ERMor1 n`, assuming each component
has a tower bound, produce a single uniform height dominating all. -/
theorem ERMor1.finFamily_uniform_tower {k n : ℕ}
    (g : Fin k → ERMor1 n)
    (h : ∀ i : Fin k, ∃ K : ℕ, ∀ ctx : Fin n → ℕ,
      (g i).interp ctx < tower K (maxCtx ctx + 2)) :
    ∃ K : ℕ, ∀ i : Fin k, ∀ ctx : Fin n → ℕ,
      (g i).interp ctx < tower K (maxCtx ctx + 2) := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    intro i
    exact i.elim0
  | succ k ih =>
    have ih' := ih (fun i => g i.succ)
      (fun i => h i.succ)
    obtain ⟨K', hK'⟩ := ih'
    obtain ⟨k_0, hk_0⟩ := h 0
    refine ⟨max K' k_0, ?_⟩
    intro i ctx
    refine Fin.cases ?_ ?_ i
    · exact lt_of_lt_of_le (hk_0 ctx)
        (tower_mono_left (le_max_right _ _) _)
    · intro j
      exact lt_of_lt_of_le (hK' j ctx)
        (tower_mono_left (le_max_left _ _) _)

/-- Every `ERMor1 n` term's interpretation is dominated by a
fixed-height tower applied to the context's maximum plus 2. -/
theorem ERMor1.exists_lt_tower :
    ∀ {n : ℕ} (t : ERMor1 n),
      ∃ k : ℕ, ∀ ctx : Fin n → ℕ,
        t.interp ctx < tower k (maxCtx ctx + 2)
  | _, ERMor1.zero => by
    refine ⟨0, fun ctx => ?_⟩
    change (0 : ℕ) < maxCtx ctx + 2
    omega
  | _, ERMor1.succ => by
    refine ⟨0, fun ctx => ?_⟩
    change (ctx 0).succ < maxCtx ctx + 2
    have h := le_maxCtx ctx 0
    omega
  | _, ERMor1.proj i => by
    refine ⟨0, fun ctx => ?_⟩
    change ctx i < maxCtx ctx + 2
    have h := le_maxCtx ctx i
    omega
  | _, ERMor1.sub => by
    refine ⟨0, fun ctx => ?_⟩
    change ctx 0 - ctx 1 < maxCtx ctx + 2
    have h := le_maxCtx ctx 0
    omega
  | _, ERMor1.comp f g => by
    obtain ⟨k_f, h_f⟩ := f.exists_lt_tower
    have h_g : ∀ i, ∃ K : ℕ, ∀ ctx,
        (g i).interp ctx < tower K (maxCtx ctx + 2) :=
      fun i => (g i).exists_lt_tower
    obtain ⟨K, h_K⟩ := ERMor1.finFamily_uniform_tower g h_g
    refine ⟨k_f + K + 1, fun ctx => ?_⟩
    change f.interp (fun i => (g i).interp ctx) <
      tower (k_f + K + 1) (maxCtx ctx + 2)
    have h_inner_max : maxCtx (fun i => (g i).interp ctx)
        ≤ tower K (maxCtx ctx + 2) := by
      apply Finset.sup_le
      intro i _
      exact Nat.le_of_lt (h_K i ctx)
    have h_f_applied := h_f (fun i => (g i).interp ctx)
    have h_tower_ge_two :
        2 ≤ tower K (maxCtx ctx + 2) :=
      le_trans (two_le_maxCtx_plus_two ctx)
        (self_le_tower K (maxCtx ctx + 2))
    have h_add_two_bound :
        tower K (maxCtx ctx + 2) + 2 ≤
          tower (K + 1) (maxCtx ctx + 2) := by
      change tower K (maxCtx ctx + 2) + 2 ≤
        2 ^ tower K (maxCtx ctx + 2)
      have h_add_le_mul : tower K (maxCtx ctx + 2) + 2 ≤
          2 * tower K (maxCtx ctx + 2) := by omega
      have h_mul_le_pow := two_mul_le_two_pow h_tower_ge_two
      exact le_trans h_add_le_mul h_mul_le_pow
    calc f.interp (fun i => (g i).interp ctx)
        < tower k_f (maxCtx (fun i => (g i).interp ctx)
            + 2) := h_f_applied
      _ ≤ tower k_f (tower K (maxCtx ctx + 2) + 2) :=
          tower_mono_right _ (by omega)
      _ ≤ tower k_f (tower (K + 1) (maxCtx ctx + 2)) :=
          tower_mono_right _ h_add_two_bound
      _ = tower (k_f + K + 1) (maxCtx ctx + 2) :=
          tower_comp _ _ _
  | _, ERMor1.bsum f => by
    obtain ⟨k_f, h_f⟩ := f.exists_lt_tower
    refine ⟨k_f + 3, fun ctx => ?_⟩
    change natBSum (ctx 0) (fun i =>
      f.interp (Fin.cons i (Fin.tail ctx))) <
      tower (k_f + 3) (maxCtx ctx + 2)
    have h_inner : ∀ i < ctx 0,
        f.interp (Fin.cons i (Fin.tail ctx))
          ≤ tower k_f (maxCtx ctx + 2) := by
      intro i hi
      have hi_le : i ≤ maxCtx ctx :=
        le_trans (Nat.le_of_lt hi) (le_maxCtx ctx 0)
      have h_max_le :
          maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx :=
        maxCtx_cons_le i ctx hi_le
      have h_applied := h_f (Fin.cons i (Fin.tail ctx))
      have h_step : f.interp (Fin.cons i (Fin.tail ctx))
          < tower k_f (maxCtx ctx + 2) :=
        lt_of_lt_of_le h_applied
          (tower_mono_right _ (by omega))
      exact Nat.le_of_lt h_step
    have h_sum := natBSum_le_mul_max (ctx 0) _ _ h_inner
    have h_ctx_le : ctx 0 ≤ maxCtx ctx + 2 := by
      have := le_maxCtx ctx 0; omega
    have h_mul_le :
        ctx 0 * tower k_f (maxCtx ctx + 2)
          ≤ (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2) :=
      Nat.mul_le_mul_right _ h_ctx_le
    have h_bound :
        (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2)
          ≤ tower (k_f + 2) (maxCtx ctx + 2) :=
      mul_tower_le_tower_add_two (two_le_maxCtx_plus_two ctx)
    calc natBSum (ctx 0)
            (fun i => f.interp (Fin.cons i (Fin.tail ctx)))
        ≤ ctx 0 * tower k_f (maxCtx ctx + 2) := h_sum
      _ ≤ (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2) :=
          h_mul_le
      _ ≤ tower (k_f + 2) (maxCtx ctx + 2) := h_bound
      _ < tower (k_f + 3) (maxCtx ctx + 2) := by
          change tower (k_f + 2) (maxCtx ctx + 2) <
            2 ^ tower (k_f + 2) (maxCtx ctx + 2)
          exact Nat.lt_two_pow_self
  | _, ERMor1.bprod f => by
    obtain ⟨k_f, h_f⟩ := f.exists_lt_tower
    refine ⟨k_f + 4, fun ctx => ?_⟩
    change natBProd (ctx 0) (fun i =>
      f.interp (Fin.cons i (Fin.tail ctx))) <
      tower (k_f + 4) (maxCtx ctx + 2)
    have h_inner : ∀ i < ctx 0,
        f.interp (Fin.cons i (Fin.tail ctx))
          ≤ tower k_f (maxCtx ctx + 2) := by
      intro i hi
      have hi_le : i ≤ maxCtx ctx :=
        le_trans (Nat.le_of_lt hi) (le_maxCtx ctx 0)
      have h_max_le :
          maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx :=
        maxCtx_cons_le i ctx hi_le
      have h_applied := h_f (Fin.cons i (Fin.tail ctx))
      have h_step : f.interp (Fin.cons i (Fin.tail ctx))
          < tower k_f (maxCtx ctx + 2) :=
        lt_of_lt_of_le h_applied
          (tower_mono_right _ (by omega))
      exact Nat.le_of_lt h_step
    have h_prod := natBProd_le_pow_max (ctx 0) _ _ h_inner
    have h_ctx_le : ctx 0 ≤ maxCtx ctx + 2 := by
      have := le_maxCtx ctx 0; omega
    have h_pow_le :
        tower k_f (maxCtx ctx + 2) ^ (ctx 0)
          ≤ tower k_f (maxCtx ctx + 2) ^ (maxCtx ctx + 2) := by
      apply Nat.pow_le_pow_right
      · exact one_le_tower_of_one_le _ _ (by omega)
      · exact h_ctx_le
    have h_bound :
        tower k_f (maxCtx ctx + 2) ^ (maxCtx ctx + 2)
          ≤ tower (k_f + 3) (maxCtx ctx + 2) :=
      tower_pow_le_tower_add_three
        (two_le_maxCtx_plus_two ctx)
    calc natBProd (ctx 0)
            (fun i => f.interp (Fin.cons i (Fin.tail ctx)))
        ≤ tower k_f (maxCtx ctx + 2) ^ (ctx 0) := h_prod
      _ ≤ tower k_f (maxCtx ctx + 2) ^ (maxCtx ctx + 2) :=
          h_pow_le
      _ ≤ tower (k_f + 3) (maxCtx ctx + 2) := h_bound
      _ < tower (k_f + 4) (maxCtx ctx + 2) := by
          change tower (k_f + 3) (maxCtx ctx + 2) <
            2 ^ tower (k_f + 3) (maxCtx ctx + 2)
          exact Nat.lt_two_pow_self

end GebLean
