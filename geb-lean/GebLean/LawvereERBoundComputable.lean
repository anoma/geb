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

/-- Structural ER bound expression for the B-W-style iter
combinator at arity `k + 1`.  Slot `0` of the context is the
counter; slots `1..k` are parameters.  At parameters `d` (the
tower depth offset) and `lh` (the loop-height term), the
expression evaluates to `tower (d + 1) (d + 1 + 2 * lh +
2 * sumCtx + 2)`, where `sumCtx` is the sum of all
context entries. -/
def ERMor1.iterAutoBoundExpr (k : ℕ) (d lh : ℕ) :
    ERMor1 (k + 1) :=
  ERMor1.comp (ERMor1.towerER (d + 1))
    (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.addN (fun i => match i with
        | ⟨0, _⟩ =>
            ERMor1.comp ERMor1.addN (fun j => match j with
              | ⟨0, _⟩ => ERMor1.natN (k + 1) (d + 1 + 2 * lh)
              | ⟨1, _⟩ =>
                  ERMor1.comp ERMor1.addN
                    (fun l => match l with
                      | ⟨0, _⟩ => ERMor1.sumCtxER (k + 1)
                      | ⟨1, _⟩ => ERMor1.sumCtxER (k + 1)))
        | ⟨1, _⟩ => ERMor1.natN (k + 1) 2))

/-- Interpretation of `iterAutoBoundExpr`: the bound expression
evaluates to `tower (d + 1)` of an offset linear in the context
sum. -/
theorem ERMor1.interp_iterAutoBoundExpr {k : ℕ}
    (d lh : ℕ) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.iterAutoBoundExpr k d lh).interp ctx =
      tower (d + 1) (d + 1 + 2 * lh + 2 *
        ((ERMor1.sumCtxER (k + 1)).interp ctx) + 2) := by
  unfold ERMor1.iterAutoBoundExpr
  rw [ERMor1.interp_comp, ERMor1.interp_towerER]
  congr 1
  change ERMor1.addN.interp
      (fun i => match i with
        | ⟨0, _⟩ =>
            ERMor1.addN.interp (fun j => match j with
              | ⟨0, _⟩ =>
                  (ERMor1.natN (k + 1) (d + 1 + 2 * lh)).interp
                    ctx
              | ⟨1, _⟩ =>
                  ERMor1.addN.interp
                    (fun l => match l with
                      | ⟨0, _⟩ =>
                          (ERMor1.sumCtxER (k + 1)).interp ctx
                      | ⟨1, _⟩ =>
                          (ERMor1.sumCtxER (k + 1)).interp ctx))
        | ⟨1, _⟩ =>
            (ERMor1.natN (k + 1) 2).interp ctx) =
      d + 1 + 2 * lh + 2 *
        ((ERMor1.sumCtxER (k + 1)).interp ctx) + 2
  rw [ERMor1.interp_addN]
  simp only [ERMor1.interp_addN, ERMor1.interp_natN]
  ring

/-- Structural lower bound on `iterAutoBoundExpr`'s tower
height in terms of the `d` parameter.  The body has shape
`comp (towerER (d + 1)) [...]`, so `towerHeight` exposes
`(towerER (d + 1)).towerHeight + _ + 1`.  Combined with the
auxiliary fact `n ≤ (towerER n).towerHeight` (induction on
`n`), this yields `d ≤ (iterAutoBoundExpr k d lh).
towerHeight`. -/
theorem ERMor1.iterAutoBoundExpr_towerHeight_ge_d
    (k d lh : ℕ) :
    d ≤ (ERMor1.iterAutoBoundExpr k d lh).towerHeight := by
  have htow : ∀ n, n ≤ (ERMor1.towerER n).towerHeight := by
    intro n
    induction n with
    | zero =>
        change 0 ≤ (ERMor1.proj (0 : Fin 1)).towerHeight
        simp [ERMor1.towerHeight]
    | succ n' _ =>
        unfold ERMor1.towerER
        simp only [ERMor1.towerHeight]
        have h1 : (ERMor1.towerER n').towerHeight ≤
            (Finset.univ : Finset (Fin 2)).sup
              (fun i : Fin 2 =>
                (match i with
                  | ⟨0, _⟩ => ERMor1.towerER n'
                  | ⟨1, _⟩ => ERMor1.twoN 1).towerHeight) := by
          have := Finset.le_sup
            (s := (Finset.univ : Finset (Fin 2)))
            (f := fun i : Fin 2 =>
              (match i with
                | ⟨0, _⟩ => ERMor1.towerER n'
                | ⟨1, _⟩ => ERMor1.twoN 1).towerHeight)
            (Finset.mem_univ (⟨0, by omega⟩ : Fin 2))
          exact this
        omega
  unfold ERMor1.iterAutoBoundExpr
  simp only [ERMor1.towerHeight]
  have h_d1 : d + 1 ≤ (ERMor1.towerER (d + 1)).towerHeight :=
    htow (d + 1)
  omega

/-- Each child of a `comp` carries a tower height bounded above
by the `comp`'s own tower height.  Direct from the structural
recursion on `towerHeight`. -/
private theorem ERMor1.towerHeight_le_comp_of_mem
    {n m : ℕ} (f : ERMor1 m) (g : Fin m → ERMor1 n)
    (i : Fin m) :
    (g i).towerHeight ≤ (ERMor1.comp f g).towerHeight := by
  change (g i).towerHeight ≤
      f.towerHeight +
        (Finset.univ.sup (fun j => (g j).towerHeight)) + 1
  have h : (g i).towerHeight ≤
      Finset.univ.sup (fun j => (g j).towerHeight) :=
    Finset.le_sup (f := fun j => (g j).towerHeight)
      (Finset.mem_univ i)
  omega

/-- The head functor of a `comp` carries a tower height bounded
above by the `comp`'s own tower height. -/
private theorem ERMor1.towerHeight_le_comp_head
    {n m : ℕ} (f : ERMor1 m) (g : Fin m → ERMor1 n) :
    f.towerHeight ≤ (ERMor1.comp f g).towerHeight := by
  change f.towerHeight ≤
      f.towerHeight +
        (Finset.univ.sup (fun j => (g j).towerHeight)) + 1
  omega

/-- Structural overhead of `boundedRec`'s tower height: the
contribution from `boundedSearch`, `boundedRecRange`,
`boundedRecPred`, `beta`, `minN`, `natUnpairFst`,
`natUnpairSnd` evaluated at trivial inputs. -/
private def ERMor1.boundedRec_towerHeight_overhead : ℕ :=
  (ERMor1.boundedRec ERMor1.zero
    (ERMor1.proj (k := 2) ⟨0, by omega⟩)
    (ERMor1.zeroN 1)).towerHeight

/-- Predicate's tower height bounded by `searchBody`. -/
private theorem ERMor1.pred_towerHeight_le_searchBody
    {k : ℕ} (pred : ERMor1 (k + 1)) :
    pred.towerHeight ≤
      (ERMor1.searchBody pred).towerHeight := by
  unfold ERMor1.searchBody
  refine le_trans
    (ERMor1.towerHeight_le_comp_of_mem ERMor1.mulN
      (fun j : Fin 2 => match j with
        | ⟨0, _⟩ => ERMor1.comp ERMor1.boolNot
            (fun _ : Fin 1 => ERMor1.bsum pred)
        | ⟨1, _⟩ => pred)
      ⟨1, by omega⟩) ?_
  exact ERMor1.towerHeight_le_comp_of_mem ERMor1.mulN
    (fun i : Fin 2 => match i with
      | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.mulN
          (fun j : Fin 2 => match j with
            | ⟨0, _⟩ => ERMor1.comp ERMor1.boolNot
                (fun _ : Fin 1 => ERMor1.bsum pred)
            | ⟨1, _⟩ => pred)
      | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.succ
          (fun _ : Fin 1 => ERMor1.proj 0))
    ⟨0, by omega⟩

/-- Predicate's tower height bounded by `boundedSearch`. -/
private theorem ERMor1.pred_towerHeight_le_boundedSearch
    {k : ℕ} (bound : ERMor1 k) (pred : ERMor1 (k + 1)) :
    pred.towerHeight ≤
      (ERMor1.boundedSearch bound pred).towerHeight := by
  unfold ERMor1.boundedSearch
  refine le_trans
    (ERMor1.pred_towerHeight_le_searchBody pred) ?_
  refine le_trans
    (?_ : (ERMor1.searchBody pred).towerHeight ≤
      (ERMor1.bsum (ERMor1.searchBody pred)).towerHeight) ?_
  · change _ ≤ _ + 3; omega
  refine le_trans
    (ERMor1.towerHeight_le_comp_head
      (ERMor1.bsum (ERMor1.searchBody pred))
      (ERMor1.consBound bound)) ?_
  refine le_trans
    (ERMor1.towerHeight_le_comp_of_mem ERMor1.sub
      (fun j : Fin 2 => match j with
        | ⟨0, _⟩ => ERMor1.comp
            (ERMor1.bsum (ERMor1.searchBody pred))
            (ERMor1.consBound bound)
        | ⟨1, _⟩ => ERMor1.comp ERMor1.signN
            (fun _ : Fin 1 => ERMor1.comp
              (ERMor1.bsum pred)
              (ERMor1.consBound bound)))
      ⟨0, by omega⟩) ?_
  exact ERMor1.towerHeight_le_comp_of_mem ERMor1.addN
    (fun i : Fin 2 => match i with
      | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.sub
          (fun j : Fin 2 => match j with
            | ⟨0, _⟩ =>
              ERMor1.comp
                (ERMor1.bsum (ERMor1.searchBody pred))
                (ERMor1.consBound bound)
            | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.signN
                (fun _ : Fin 1 => ERMor1.comp
                  (ERMor1.bsum pred)
                  (ERMor1.consBound bound)))
      | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.mulN
          (fun j : Fin 2 => match j with
            | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.boolNot
                (fun _ : Fin 1 => ERMor1.comp ERMor1.signN
                  (fun _ : Fin 1 => ERMor1.comp
                    (ERMor1.bsum pred)
                    (ERMor1.consBound bound)))
            | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.succ
                (fun _ : Fin 1 => bound)))
    ⟨0, by omega⟩

/-- `base.towerHeight` bounded by `boundedRecBaseCheck base`. -/
private theorem ERMor1.base_towerHeight_le_baseCheck
    {k : ℕ} (base : ERMor1 k) :
    base.towerHeight ≤
      (ERMor1.boundedRecBaseCheck base).towerHeight := by
  unfold ERMor1.boundedRecBaseCheck ERMor1.boolEqAt
  refine le_trans
    (?_ : base.towerHeight ≤
      (ERMor1.baseOnCand base).towerHeight) ?_
  · unfold ERMor1.baseOnCand
    exact ERMor1.towerHeight_le_comp_head base _
  exact ERMor1.towerHeight_le_comp_of_mem ERMor1.boolEqNat
    (fun i : Fin 2 => match i with
      | ⟨0, _⟩ =>
        ERMor1.betaOnCand (ERMor1.zeroN (k + 2))
      | ⟨1, _⟩ => ERMor1.baseOnCand base)
    ⟨1, by omega⟩

/-- `step.towerHeight` bounded by `boundedRecStepCheck step`. -/
private theorem ERMor1.step_towerHeight_le_stepCheck
    {k : ℕ} (step : ERMor1 (k + 2)) :
    step.towerHeight ≤
      (ERMor1.boundedRecStepCheck step).towerHeight := by
  refine le_trans
    (?_ : step.towerHeight ≤
      (ERMor1.stepOnCandStep step).towerHeight) ?_
  · unfold ERMor1.stepOnCandStep
    exact ERMor1.towerHeight_le_comp_head step _
  refine le_trans
    (?_ : (ERMor1.stepOnCandStep step).towerHeight ≤
      (ERMor1.boundedRecStepBody step).towerHeight) ?_
  · unfold ERMor1.boundedRecStepBody ERMor1.boolEqAt
    exact ERMor1.towerHeight_le_comp_of_mem ERMor1.boolEqNat
      (fun i : Fin 2 => match i with
        | ⟨0, _⟩ =>
          ERMor1.betaOnCandStep
            (ERMor1.comp ERMor1.succ
              (fun (_ : Fin 1) => ERMor1.proj 0))
        | ⟨1, _⟩ => ERMor1.stepOnCandStep step)
      ⟨1, by omega⟩
  refine le_trans
    (?_ : (ERMor1.boundedRecStepBody step).towerHeight ≤
      (ERMor1.bprod
        (ERMor1.boundedRecStepBody step)).towerHeight) ?_
  · change _ ≤ _ + 4; omega
  unfold ERMor1.boundedRecStepCheck
  exact ERMor1.towerHeight_le_comp_head
    (ERMor1.bprod (ERMor1.boundedRecStepBody step)) _

/-- `boundedRecBaseCheck base.towerHeight` bounded by
`boundedRecPred base step`. -/
private theorem ERMor1.baseCheck_towerHeight_le_pred
    {k : ℕ} (base : ERMor1 k) (step : ERMor1 (k + 2)) :
    (ERMor1.boundedRecBaseCheck base).towerHeight ≤
      (ERMor1.boundedRecPred base step).towerHeight := by
  unfold ERMor1.boundedRecPred
  exact ERMor1.towerHeight_le_comp_of_mem ERMor1.boolAnd
    (fun i : Fin 2 => match i with
      | ⟨0, _⟩ => ERMor1.boundedRecBaseCheck base
      | ⟨1, _⟩ => ERMor1.boundedRecStepCheck step)
    ⟨0, by omega⟩

/-- `boundedRecStepCheck step.towerHeight` bounded by
`boundedRecPred base step`. -/
private theorem ERMor1.stepCheck_towerHeight_le_pred
    {k : ℕ} (base : ERMor1 k) (step : ERMor1 (k + 2)) :
    (ERMor1.boundedRecStepCheck step).towerHeight ≤
      (ERMor1.boundedRecPred base step).towerHeight := by
  unfold ERMor1.boundedRecPred
  exact ERMor1.towerHeight_le_comp_of_mem ERMor1.boolAnd
    (fun i : Fin 2 => match i with
      | ⟨0, _⟩ => ERMor1.boundedRecBaseCheck base
      | ⟨1, _⟩ => ERMor1.boundedRecStepCheck step)
    ⟨1, by omega⟩

/-- The full predicate `boundedRecPred base step` is bounded by
the `boundedRec base step bound` tower height through the chain
`pred ≤ boundedSearch ≤ comp natUnpairFst ≤ betaAtN ≤ boundedRec`.
-/
private theorem ERMor1.pred_towerHeight_le_boundedRec
    {k : ℕ} (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    (ERMor1.boundedRecPred base step).towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight := by
  refine le_trans
    (ERMor1.pred_towerHeight_le_boundedSearch
      (ERMor1.boundedRecRange bound)
      (ERMor1.boundedRecPred base step)) ?_
  refine le_trans
    (?_ : (ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
        (ERMor1.boundedRecPred base step)).towerHeight ≤
      (ERMor1.comp ERMor1.natUnpairFst
        (fun (_ : Fin 1) =>
          ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
            (ERMor1.boundedRecPred base step))).towerHeight) ?_
  · exact ERMor1.towerHeight_le_comp_of_mem
      ERMor1.natUnpairFst
      (fun (_ : Fin 1) =>
        ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
          (ERMor1.boundedRecPred base step))
      ⟨0, by omega⟩
  refine le_trans
    (?_ :
      (ERMor1.comp ERMor1.natUnpairFst
        (fun (_ : Fin 1) =>
          ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
            (ERMor1.boundedRecPred base step))).towerHeight ≤
      (ERMor1.comp ERMor1.beta
        (fun i : Fin 3 => match i with
          | ⟨0, _⟩ =>
            ERMor1.comp ERMor1.natUnpairFst
              (fun (_ : Fin 1) =>
                ERMor1.boundedSearch
                  (ERMor1.boundedRecRange bound)
                  (ERMor1.boundedRecPred base step))
          | ⟨1, _⟩ =>
            ERMor1.comp ERMor1.natUnpairSnd
              (fun (_ : Fin 1) =>
                ERMor1.boundedSearch
                  (ERMor1.boundedRecRange bound)
                  (ERMor1.boundedRecPred base step))
          | ⟨2, _⟩ => ERMor1.proj 0)).towerHeight) ?_
  · exact ERMor1.towerHeight_le_comp_of_mem ERMor1.beta
      (fun i : Fin 3 => match i with
        | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.natUnpairFst
            (fun (_ : Fin 1) =>
              ERMor1.boundedSearch
                (ERMor1.boundedRecRange bound)
                (ERMor1.boundedRecPred base step))
        | ⟨1, _⟩ =>
          ERMor1.comp ERMor1.natUnpairSnd
            (fun (_ : Fin 1) =>
              ERMor1.boundedSearch
                (ERMor1.boundedRecRange bound)
                (ERMor1.boundedRecPred base step))
        | ⟨2, _⟩ => ERMor1.proj 0)
      ⟨0, by omega⟩
  unfold ERMor1.boundedRec
  dsimp only
  exact ERMor1.towerHeight_le_comp_of_mem ERMor1.minN
    (fun i : Fin 2 => match i with
      | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.beta (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ =>
            ERMor1.comp ERMor1.natUnpairFst
              (fun (_ : Fin 1) =>
                ERMor1.boundedSearch
                  (ERMor1.boundedRecRange bound)
                  (ERMor1.boundedRecPred base step))
          | ⟨1, _⟩ =>
            ERMor1.comp ERMor1.natUnpairSnd
              (fun (_ : Fin 1) =>
                ERMor1.boundedSearch
                  (ERMor1.boundedRecRange bound)
                  (ERMor1.boundedRecPred base step))
          | ⟨2, _⟩ => ERMor1.proj 0)
      | ⟨1, _⟩ => bound)
    ⟨0, by omega⟩

/-- `bound.towerHeight` is dominated by the tower height of
`boundedRec base step bound`. -/
private theorem ERMor1.bound_towerHeight_le_boundedRec
    {k : ℕ} (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    bound.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight := by
  unfold ERMor1.boundedRec
  dsimp only
  exact ERMor1.towerHeight_le_comp_of_mem ERMor1.minN
    (fun i : Fin 2 => match i with
      | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.beta (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ =>
            ERMor1.comp ERMor1.natUnpairFst
              (fun (_ : Fin 1) =>
                ERMor1.boundedSearch
                  (ERMor1.boundedRecRange bound)
                  (ERMor1.boundedRecPred base step))
          | ⟨1, _⟩ =>
            ERMor1.comp ERMor1.natUnpairSnd
              (fun (_ : Fin 1) =>
                ERMor1.boundedSearch
                  (ERMor1.boundedRecRange bound)
                  (ERMor1.boundedRecPred base step))
          | ⟨2, _⟩ => ERMor1.proj 0)
      | ⟨1, _⟩ => bound)
    ⟨1, by omega⟩

/-- Closed-form lower bound on
`(boundedRec base step bound).towerHeight`: the max of the three
input arguments' tower heights is dominated by the result.  The
structural overhead `boundedRec_towerHeight_overhead` records the
contribution from `boundedSearch` / `boundedRecRange` /
`boundedRecPred` / `beta` / `minN` / `natUnpairFst` /
`natUnpairSnd` evaluated at trivial inputs and is supplied as a
named constant for downstream reference; the present statement
gives the input-side bound.  Equality does not hold here because
`bound`, `base`, and `step` appear at differing structural depths
in `boundedRec`'s body. -/
theorem ERMor1.boundedRec_towerHeight_le {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    max base.towerHeight
        (max step.towerHeight bound.towerHeight) ≤
      (ERMor1.boundedRec base step bound).towerHeight := by
  refine max_le ?_ (max_le ?_ ?_)
  · refine le_trans
      (ERMor1.base_towerHeight_le_baseCheck base) ?_
    refine le_trans
      (ERMor1.baseCheck_towerHeight_le_pred base step) ?_
    exact ERMor1.pred_towerHeight_le_boundedRec base step bound
  · refine le_trans
      (ERMor1.step_towerHeight_le_stepCheck step) ?_
    refine le_trans
      (ERMor1.stepCheck_towerHeight_le_pred base step) ?_
    exact ERMor1.pred_towerHeight_le_boundedRec base step bound
  · exact ERMor1.bound_towerHeight_le_boundedRec base step bound

/-- B-W-style iter combinator on ER terms with an automatic
structural tower bound.  Composes `boundedRec` against
`iterAutoBoundExpr` and substitutes `count` into slot `0` of
the resulting `(k + 1)`-arity term, yielding a `k`-arity term.
The numeric parameters `d` and `lh` are the tower depth and
loop-height marker used to size the bound. -/
def ERMor1.iterT {k : ℕ}
    (count : ERMor1 k) (step : ERMor1 (k + 2))
    (base : ERMor1 k) (d lh : ℕ) : ERMor1 k :=
  ERMor1.comp
    (ERMor1.boundedRec base step
      (ERMor1.iterAutoBoundExpr k d lh))
    (fun i : Fin (k + 1) =>
      if h : i.val = 0 then count
      else ERMor1.proj ⟨i.val - 1, by
        have := i.isLt; omega⟩)

/-- Conditional correctness for `iterT`.  Whenever the trace of
the unfolded recursion stays under `iterAutoBoundExpr` and the
bound is monotone in the counter slot up to `count`, `iterT`
computes the true `Nat.rec` recursion. -/
theorem ERMor1.interp_iterT_of_bounded {k : ℕ}
    (count : ERMor1 k) (step : ERMor1 (k + 2))
    (base : ERMor1 k) (d lh : ℕ)
    (ctx : Fin k → ℕ)
    (h : ∀ j, j ≤ count.interp ctx →
      Nat.rec (base.interp ctx)
        (fun i prev =>
          step.interp (Fin.cons i (Fin.cons prev ctx))) j ≤
      (ERMor1.iterAutoBoundExpr k d lh).interp
        (Fin.cons j ctx))
    (h_mono : ∀ j, j ≤ count.interp ctx →
      (ERMor1.iterAutoBoundExpr k d lh).interp
        (Fin.cons j ctx) ≤
      (ERMor1.iterAutoBoundExpr k d lh).interp
        (Fin.cons (count.interp ctx) ctx)) :
    (ERMor1.iterT count step base d lh).interp ctx =
      Nat.rec (base.interp ctx)
        (fun j prev =>
          step.interp (Fin.cons j (Fin.cons prev ctx)))
        (count.interp ctx) := by
  unfold ERMor1.iterT
  rw [ERMor1.interp_comp]
  have hsubst :
      (fun i : Fin (k + 1) =>
        ((if h : i.val = 0 then count
          else ERMor1.proj ⟨i.val - 1, by
            have := i.isLt; omega⟩) : ERMor1 k).interp ctx)
        = Fin.cons (count.interp ctx) ctx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · change
        ((if _h : ((0 : Fin (k + 1)) : Fin (k + 1)).val = 0
          then count
          else ERMor1.proj ⟨(0 : Fin (k + 1)).val - 1, by
            have := (0 : Fin (k + 1)).isLt; omega⟩)
              : ERMor1 k).interp ctx =
        (Fin.cons (count.interp ctx) ctx : Fin (k + 1) → ℕ) 0
      rw [Fin.cons_zero]
      simp
    · intro j
      change
        ((if _h : (Fin.succ j).val = 0 then count
          else ERMor1.proj ⟨(Fin.succ j).val - 1, by
            have := (Fin.succ j).isLt; omega⟩)
              : ERMor1 k).interp ctx =
        (Fin.cons (count.interp ctx) ctx : Fin (k + 1) → ℕ)
          j.succ
      rw [Fin.cons_succ]
      have hne : (Fin.succ j).val ≠ 0 := by
        change j.val + 1 ≠ 0
        omega
      simp only [hne, dite_false, ERMor1.interp_proj]
      have hidx : (⟨(Fin.succ j).val - 1, by
            have := (Fin.succ j).isLt; omega⟩ : Fin k) = j := by
        apply Fin.ext
        change (Fin.succ j).val - 1 = j.val
        change j.val + 1 - 1 = j.val
        omega
      rw [hidx]
  rw [hsubst]
  exact ERMor1.interp_boundedRec_of_bounded
    base step (ERMor1.iterAutoBoundExpr k d lh)
    (count.interp ctx) ctx h h_mono

end GebLean
