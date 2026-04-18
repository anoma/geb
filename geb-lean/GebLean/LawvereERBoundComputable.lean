import GebLean.LawvereERBound
import GebLean.LawvereERArith
import GebLean.Utilities.ERTreeArith
import GebLean.Utilities.SzudzikSeq
import Mathlib.Algebra.BigOperators.Fin

/-!
# Computable Tower Bounds for ER Terms

Constructive counterpart to `ERMor1.exists_lt_tower` from
`GebLean.LawvereERBound`.  A structural function `towerHeight`
produces a tower height from the syntactic shape of any
`ERMor1 n`, with `lt_tower_towerHeight` witnessing that the
interpretation is dominated by `tower (towerHeight t)
(maxCtx ctx + 2)`.

Building on `towerHeight`, `towerER k` is an `ERMor1 1` term
that evaluates to `tower k (ctx 0)`.  `towerBound t` wraps
`towerER` around a context-summing ER term so that
`(towerBound t).interp ctx` dominates `t.interp ctx`
uniformly in `ctx`.

These helpers provide an ER-level bound supplier for
structural recursions on Gödel codes such as
`foldBTLOnCode`.
-/

namespace GebLean

/-- Structural tower-height function on `ERMor1 n` mirroring
the existence argument in `exists_lt_tower`.  Base generators
have height `0`; `comp` adds one level above the uniform bound
on its argument family; `bsum` adds three; `bprod` adds four. -/
def ERMor1.towerHeight : {n : ℕ} → ERMor1 n → ℕ
  | _, ERMor1.zero => 0
  | _, ERMor1.succ => 0
  | _, ERMor1.proj _ => 0
  | _, ERMor1.sub => 0
  | _, ERMor1.comp f g =>
      f.towerHeight +
        (Finset.univ.sup (fun i => (g i).towerHeight)) + 1
  | _, ERMor1.bsum f => f.towerHeight + 3
  | _, ERMor1.bprod f => f.towerHeight + 4

/-- Under `finFamily_uniform_tower_at` with explicit height,
each component is dominated by the same tower.  Proof is a
direct induction analogous to `finFamily_uniform_tower` but
with a concrete, pointwise-supplied height. -/
theorem ERMor1.finFamily_tower_at {k n : ℕ}
    (g : Fin k → ERMor1 n)
    (h : ∀ (i : Fin k) (ctx : Fin n → ℕ),
      (g i).interp ctx <
        tower (g i).towerHeight (maxCtx ctx + 2)) :
    ∀ (i : Fin k) (ctx : Fin n → ℕ),
      (g i).interp ctx <
        tower (Finset.univ.sup
          (fun j => (g j).towerHeight)) (maxCtx ctx + 2) := by
  intro i ctx
  have hle : (g i).towerHeight ≤
      Finset.univ.sup (fun j => (g j).towerHeight) :=
    Finset.le_sup (f := fun j => (g j).towerHeight)
      (Finset.mem_univ i)
  exact lt_of_lt_of_le (h i ctx) (tower_mono_left hle _)

/-- Constructive dominance of `ERMor1.interp` by a fixed
structural tower height.  Mirrors the existence proof
`exists_lt_tower` step-for-step; the only change is the
concrete use of `towerHeight` in place of the witness
supplied by `obtain`. -/
theorem ERMor1.lt_tower_towerHeight :
    ∀ {n : ℕ} (t : ERMor1 n) (ctx : Fin n → ℕ),
      t.interp ctx < tower t.towerHeight (maxCtx ctx + 2)
  | _, ERMor1.zero, ctx => by
      change (0 : ℕ) < maxCtx ctx + 2
      omega
  | _, ERMor1.succ, ctx => by
      change (ctx 0).succ < maxCtx ctx + 2
      have h := le_maxCtx ctx 0
      omega
  | _, ERMor1.proj i, ctx => by
      change ctx i < maxCtx ctx + 2
      have h := le_maxCtx ctx i
      omega
  | _, ERMor1.sub, ctx => by
      change ctx 0 - ctx 1 < maxCtx ctx + 2
      have h := le_maxCtx ctx 0
      omega
  | _, ERMor1.comp f g, ctx => by
      change f.interp (fun i => (g i).interp ctx) <
        tower
          (f.towerHeight +
            (Finset.univ.sup (fun i => (g i).towerHeight)) + 1)
          (maxCtx ctx + 2)
      set K : ℕ :=
        Finset.univ.sup (fun i => (g i).towerHeight) with hK
      have h_K : ∀ (i : Fin _) (ctx' : Fin _ → ℕ),
          (g i).interp ctx' <
            tower K (maxCtx ctx' + 2) := by
        intro i ctx'
        exact ERMor1.finFamily_tower_at g
          (fun j cx => (g j).lt_tower_towerHeight cx) i ctx'
      have h_inner_max : maxCtx (fun i => (g i).interp ctx)
          ≤ tower K (maxCtx ctx + 2) := by
        apply Finset.sup_le
        intro i _
        exact Nat.le_of_lt (h_K i ctx)
      have h_f_applied :=
        f.lt_tower_towerHeight (fun i => (g i).interp ctx)
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
          < tower f.towerHeight
              (maxCtx (fun i => (g i).interp ctx)
                + 2) := h_f_applied
        _ ≤ tower f.towerHeight
              (tower K (maxCtx ctx + 2) + 2) :=
            tower_mono_right _ (by omega)
        _ ≤ tower f.towerHeight
              (tower (K + 1) (maxCtx ctx + 2)) :=
            tower_mono_right _ h_add_two_bound
        _ = tower (f.towerHeight + K + 1) (maxCtx ctx + 2) :=
            tower_comp _ _ _
  | _, ERMor1.bsum f, ctx => by
      change natBSum (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx))) <
        tower (f.towerHeight + 3) (maxCtx ctx + 2)
      set k_f : ℕ := f.towerHeight with hk_f
      have h_inner : ∀ i < ctx 0,
          f.interp (Fin.cons i (Fin.tail ctx))
            ≤ tower k_f (maxCtx ctx + 2) := by
        intro i hi
        have hi_le : i ≤ maxCtx ctx :=
          le_trans (Nat.le_of_lt hi) (le_maxCtx ctx 0)
        have h_max_le :
            maxCtx (Fin.cons i (Fin.tail ctx)) ≤
              maxCtx ctx :=
          maxCtx_cons_le i ctx hi_le
        have h_applied :=
          f.lt_tower_towerHeight (Fin.cons i (Fin.tail ctx))
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
            ≤ (maxCtx ctx + 2) *
                tower k_f (maxCtx ctx + 2) :=
        Nat.mul_le_mul_right _ h_ctx_le
      have h_bound :
          (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2)
            ≤ tower (k_f + 2) (maxCtx ctx + 2) :=
        mul_tower_le_tower_add_two (two_le_maxCtx_plus_two ctx)
      calc natBSum (ctx 0)
              (fun i => f.interp (Fin.cons i (Fin.tail ctx)))
          ≤ ctx 0 * tower k_f (maxCtx ctx + 2) := h_sum
        _ ≤ (maxCtx ctx + 2) *
              tower k_f (maxCtx ctx + 2) := h_mul_le
        _ ≤ tower (k_f + 2) (maxCtx ctx + 2) := h_bound
        _ < tower (k_f + 3) (maxCtx ctx + 2) := by
            change tower (k_f + 2) (maxCtx ctx + 2) <
              2 ^ tower (k_f + 2) (maxCtx ctx + 2)
            exact Nat.lt_two_pow_self
  | _, ERMor1.bprod f, ctx => by
      change natBProd (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx))) <
        tower (f.towerHeight + 4) (maxCtx ctx + 2)
      set k_f : ℕ := f.towerHeight with hk_f
      have h_inner : ∀ i < ctx 0,
          f.interp (Fin.cons i (Fin.tail ctx))
            ≤ tower k_f (maxCtx ctx + 2) := by
        intro i hi
        have hi_le : i ≤ maxCtx ctx :=
          le_trans (Nat.le_of_lt hi) (le_maxCtx ctx 0)
        have h_max_le :
            maxCtx (Fin.cons i (Fin.tail ctx)) ≤
              maxCtx ctx :=
          maxCtx_cons_le i ctx hi_le
        have h_applied :=
          f.lt_tower_towerHeight (Fin.cons i (Fin.tail ctx))
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
            ≤ tower k_f (maxCtx ctx + 2) ^
                (maxCtx ctx + 2) := by
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
        _ ≤ tower k_f (maxCtx ctx + 2) ^
              (maxCtx ctx + 2) := h_pow_le
        _ ≤ tower (k_f + 3) (maxCtx ctx + 2) := h_bound
        _ < tower (k_f + 4) (maxCtx ctx + 2) := by
            change tower (k_f + 3) (maxCtx ctx + 2) <
              2 ^ tower (k_f + 3) (maxCtx ctx + 2)
            exact Nat.lt_two_pow_self

/-- Tower-of-twos as an `ERMor1 1` term.  `towerER k` evaluates
at `![x]` to `tower k x`.  Iterates `expER` with base `2` so
that each successive composition computes one more level of
`2 ^ _`. -/
def ERMor1.towerER : ℕ → ERMor1 1
  | 0 => ERMor1.proj 0
  | k + 1 =>
      ERMor1.comp ERMor1.expER
        (fun i => match i with
          | ⟨0, _⟩ => ERMor1.towerER k
          | ⟨1, _⟩ => ERMor1.twoN 1)

/-- Interpretation of `towerER`: evaluates to `tower k` of the
unique context argument. -/
@[simp] theorem ERMor1.interp_towerER (k : ℕ)
    (ctx : Fin 1 → ℕ) :
    (ERMor1.towerER k).interp ctx = tower k (ctx 0) := by
  induction k with
  | zero =>
      change ctx 0 = tower 0 (ctx 0)
      rw [tower_zero]
  | succ k ih =>
      change ERMor1.expER.interp
          (fun i => match i with
            | ⟨0, _⟩ => (ERMor1.towerER k).interp ctx
            | ⟨1, _⟩ => (ERMor1.twoN 1).interp ctx) =
        tower (k + 1) (ctx 0)
      have hfun :
          (fun i : Fin 2 => match i with
            | ⟨0, _⟩ => (ERMor1.towerER k).interp ctx
            | ⟨1, _⟩ => (ERMor1.twoN 1).interp ctx) =
          ![tower k (ctx 0), 2] := by
        funext i
        match i with
        | ⟨0, _⟩ =>
            change (ERMor1.towerER k).interp ctx =
              (![tower k (ctx 0), 2] : Fin 2 → ℕ) 0
            rw [ih]
            rfl
        | ⟨1, _⟩ =>
            change (ERMor1.twoN 1).interp ctx =
              (![tower k (ctx 0), 2] : Fin 2 → ℕ) 1
            rw [ERMor1.interp_twoN]
            rfl
      rw [hfun, ERMor1.interp_expER]
      change (2 : ℕ) ^ tower k (ctx 0) = tower (k + 1) (ctx 0)
      rw [tower_succ]

/-- Sum of all context entries as an `ERMor1 n` term.
`sumCtxER n` evaluates to the sum of all `ctx i` for
`i : Fin n`.  Dominates `maxCtx ctx` pointwise. -/
def ERMor1.sumCtxER : (n : ℕ) → ERMor1 n
  | 0 => ERMor1.zeroN 0
  | n + 1 =>
      ERMor1.comp ERMor1.addN
        (fun i => match i with
          | ⟨0, _⟩ => ERMor1.proj ⟨0, by omega⟩
          | ⟨1, _⟩ =>
              ERMor1.comp (ERMor1.sumCtxER n)
                (fun j => ERMor1.proj ⟨j.val + 1, by omega⟩))

/-- Interpretation of `sumCtxER`: sums all context entries. -/
theorem ERMor1.interp_sumCtxER :
    ∀ {n : ℕ} (ctx : Fin n → ℕ),
      (ERMor1.sumCtxER n).interp ctx =
        (Finset.univ : Finset (Fin n)).sum ctx
  | 0, _ => by
      change 0 =
        (Finset.univ : Finset (Fin 0)).sum _
      rw [Finset.univ_eq_empty, Finset.sum_empty]
  | n + 1, ctx => by
      change ERMor1.addN.interp
          (fun i => match i with
            | ⟨0, _⟩ => ctx ⟨0, by omega⟩
            | ⟨1, _⟩ => (ERMor1.sumCtxER n).interp
                (fun j => ctx ⟨j.val + 1, by omega⟩)) =
        (Finset.univ : Finset (Fin (n + 1))).sum ctx
      rw [ERMor1.interp_addN]
      change ctx ⟨0, by omega⟩ +
          (ERMor1.sumCtxER n).interp
            (fun j : Fin n => ctx ⟨j.val + 1, by omega⟩) =
        (Finset.univ : Finset (Fin (n + 1))).sum ctx
      rw [ERMor1.interp_sumCtxER
        (fun j : Fin n => ctx ⟨j.val + 1, by omega⟩)]
      rw [Fin.sum_univ_succ (f := ctx)]
      rfl

/-- `maxCtx ctx ≤ sumCtxER.interp ctx` for every context: the
context sum dominates the context maximum. -/
theorem ERMor1.maxCtx_le_interp_sumCtxER {n : ℕ}
    (ctx : Fin n → ℕ) :
    maxCtx ctx ≤ (ERMor1.sumCtxER n).interp ctx := by
  rw [ERMor1.interp_sumCtxER]
  unfold maxCtx
  induction n with
  | zero =>
      rw [Finset.univ_eq_empty, Finset.sup_empty]
      exact Nat.zero_le _
  | succ n ih =>
      rw [Fin.sum_univ_succ (f := ctx)]
      have hsplit :
          (Finset.univ : Finset (Fin (n + 1))).sup ctx =
            max (ctx 0)
              ((Finset.univ : Finset (Fin n)).sup
                (fun j => ctx j.succ)) := by
        rw [show (Finset.univ : Finset (Fin (n + 1))) =
              insert (0 : Fin (n + 1))
                ((Finset.univ : Finset (Fin n)).image
                  Fin.succ) from ?_]
        · rw [Finset.sup_insert, Finset.sup_image]
          rfl
        · ext i
          refine ⟨fun _ => ?_, fun _ => Finset.mem_univ _⟩
          refine Fin.cases ?_ ?_ i
          · exact Finset.mem_insert_self _ _
          · intro j
            refine Finset.mem_insert.mpr (Or.inr ?_)
            exact Finset.mem_image.mpr
              ⟨j, Finset.mem_univ _, rfl⟩
      rw [hsplit]
      have ih' := ih (fun j : Fin n => ctx j.succ)
      exact max_le (by omega)
        (le_trans ih' (by omega))

/-- Upper-bound ER term for an arbitrary ER term: composes
`towerER` of the structural height with the context sum plus
`2`, so that `(towerBound t).interp ctx` dominates
`t.interp ctx` uniformly in `ctx`. -/
def ERMor1.towerBound {n : ℕ} (t : ERMor1 n) : ERMor1 n :=
  ERMor1.comp (ERMor1.towerER t.towerHeight)
    (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.addN
        (fun i => match i with
          | ⟨0, _⟩ => ERMor1.sumCtxER n
          | ⟨1, _⟩ => ERMor1.twoN n))

/-- Correctness of `towerBound`: the interpretation of an ER
term is pointwise dominated by its tower bound. -/
theorem ERMor1.interp_le_towerBound {n : ℕ} (t : ERMor1 n)
    (ctx : Fin n → ℕ) :
    t.interp ctx ≤ (t.towerBound).interp ctx := by
  have hlt := t.lt_tower_towerHeight ctx
  have hle : t.interp ctx ≤
      tower t.towerHeight (maxCtx ctx + 2) :=
    Nat.le_of_lt hlt
  have hmax := ERMor1.maxCtx_le_interp_sumCtxER ctx
  have hmono :
      tower t.towerHeight (maxCtx ctx + 2) ≤
        tower t.towerHeight
          ((ERMor1.sumCtxER n).interp ctx + 2) :=
    tower_mono_right _ (by omega)
  have hle2 : t.interp ctx ≤
      tower t.towerHeight
        ((ERMor1.sumCtxER n).interp ctx + 2) :=
    le_trans hle hmono
  change t.interp ctx ≤
    (ERMor1.towerER t.towerHeight).interp
      (fun (_ : Fin 1) =>
        ERMor1.addN.interp
          (fun i => match i with
            | ⟨0, _⟩ => (ERMor1.sumCtxER n).interp ctx
            | ⟨1, _⟩ => (ERMor1.twoN n).interp ctx))
  rw [ERMor1.interp_towerER]
  change t.interp ctx ≤
    tower t.towerHeight
      (ERMor1.addN.interp
        (fun i => match i with
          | ⟨0, _⟩ => (ERMor1.sumCtxER n).interp ctx
          | ⟨1, _⟩ => (ERMor1.twoN n).interp ctx))
  rw [ERMor1.interp_addN]
  change t.interp ctx ≤
    tower t.towerHeight
      ((ERMor1.sumCtxER n).interp ctx +
        (ERMor1.twoN n).interp ctx)
  rw [ERMor1.interp_twoN]
  exact hle2

end GebLean
