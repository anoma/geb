import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimER
import GebLean.LawvereERPolynomialBound
import GebLean.Utilities.ComputationalComplexity
import GebLean.Utilities.KSimSzudzikSimrec

/-!
# K^sim polynomial bounds and dominance assembly

K^sim-side proofs supporting the simrec dominance
hypothesis required by `kToER_interp`'s level-2
simrec case.

The principal results are:

- `ConstantOrShiftedProj` — inductive shape for level-0
  K^sim functions.
- `KMor1.level0Shape` — Lemma 1.B from the research doc.
- `KMor1.linearBound` — Lemma 1.A from the research doc.
- `kSimPackedStep_polyBound` /
  `kSimPackedBase_polyBound` — specialized for the
  packed simrec step / base.
- `kSimTowerBound_dominates_inline` — final dominance
  assembly.

The K^sim → ER polynomial-bound bridge originally
scoped as `kToER_polyBound_of_level_one` is deferred to
the call sites in Module C (Tasks 16, 17).  The
deferral is structural rather than expedient: the
simrec case of `kToER` produces a term containing
`ERMor1.boundedRec`, whose value bound is governed by
its `bound` argument and is not polynomial in the
inputs without the dominance hypothesis.  That
hypothesis is precisely what
`kSimPackedStep_polyBound`,
`kSimPackedBase_polyBound`, and
`kSimTowerBound_dominates_inline` build, so the bridge
is constructed at those call sites for the specific
ER terms `kSimPackedBase`, `kSimPackedStep` directly,
using `KMor1.linearBound`'s constants per Lemma 1.A on
the level-≤-1 K^sim children.  For the atomic, `comp`,
and `raise` cases the bridge would amount to
straightforward structural composition of `ofZero`,
`ofSucc`, `ofProj`, `ofComp`, and recursion through
`raise`; those constructions are inlined wherever they
are needed downstream.

See `docs/plans/2026-04-30-er-polynomial-bound-design.md`
(Module C) and
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
(Claims 1, 3, 4).
-/

namespace GebLean

/-- Shape of a level-0 K^sim function: either a constant
`k` or a projection-plus-constant `ctx i + k`.  Lemma
1.B's output type. -/
inductive ConstantOrShiftedProj : ℕ → Type
  | const   {a : ℕ} (k : ℕ) : ConstantOrShiftedProj a
  | shifted {a : ℕ} (i : Fin a) (k : ℕ) :
      ConstantOrShiftedProj a

/-- Interpretation of `ConstantOrShiftedProj`. -/
def ConstantOrShiftedProj.interp :
    {a : ℕ} → ConstantOrShiftedProj a → (Fin a → ℕ) → ℕ
  | _, .const k,        _   => k
  | _, .shifted i k,    ctx => ctx i + k

/-- Linear-bound constants (c, k) for a
`ConstantOrShiftedProj`. -/
def ConstantOrShiftedProj.linearBound :
    {a : ℕ} → ConstantOrShiftedProj a → ℕ × ℕ
  | _, .const k       => (0, k)
  | _, .shifted _ k   => (1, k)

/-- Lemma 1.B: every level-0 K^sim term has interp of
constant or shifted-projection form.  Built by structural
recursion on the K^sim term with level ≤ 0. -/
def KMor1.level0Shape :
    {a : ℕ} → (f : KMor1 a) → f.level ≤ 0 →
      ConstantOrShiftedProj a
  | _, .zero,         _ => .const 0
  | _, .succ,         _ => .shifted 0 1
  | _, .proj i,       _ => .shifted i 0
  | _, .comp f gs,    h =>
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 0 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 0 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      match KMor1.level0Shape f hf with
      | .const k_f       => .const k_f
      | .shifted i k_f   =>
          match KMor1.level0Shape (gs i) (hgs i) with
          | .const c        => .const (c + k_f)
          | .shifted j k_gs => .shifted j (k_gs + k_f)
  | _, .raise _,      h => by
      unfold KMor1.level at h
      omega
  | _, .simrec _ _ _, h => by
      unfold KMor1.level at h
      omega

/-- The level-0 shape's interpretation agrees with the
K^sim term's interpretation. -/
theorem KMor1.level0Shape_interp :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 0) →
      (ctx : Fin a → ℕ) →
      f.interp ctx = (KMor1.level0Shape f h).interp ctx
  | _, .zero,         _, _   => by
      simp [KMor1.level0Shape, ConstantOrShiftedProj.interp]
  | _, .succ,         _, ctx => by
      simp [KMor1.level0Shape, ConstantOrShiftedProj.interp,
        Nat.succ_eq_add_one]
  | _, .proj _,       _, _   => by
      simp [KMor1.level0Shape, ConstantOrShiftedProj.interp]
  | _, .comp f gs,    h, ctx => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 0 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 0 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      have hf_eq := KMor1.level0Shape_interp f hf
        (fun i => (gs i).interp ctx)
      rw [KMor1.interp_comp, KMor1.level0Shape]
      cases hshape : KMor1.level0Shape f hf with
      | const k_f =>
          rw [hshape] at hf_eq
          simp only [ConstantOrShiftedProj.interp] at hf_eq
          simp [ConstantOrShiftedProj.interp, hf_eq]
      | shifted i k_f =>
          rw [hshape] at hf_eq
          simp only [ConstantOrShiftedProj.interp] at hf_eq
          have hgi_eq :=
            KMor1.level0Shape_interp (gs i) (hgs i) ctx
          cases hgshape :
              KMor1.level0Shape (gs i) (hgs i) with
          | const c =>
              rw [hgshape] at hgi_eq
              simp only [hgshape]
              simp only [ConstantOrShiftedProj.interp] at hgi_eq
              simp [ConstantOrShiftedProj.interp, hf_eq,
                hgi_eq]
          | shifted j k_gs =>
              rw [hgshape] at hgi_eq
              simp only [hgshape]
              simp only [ConstantOrShiftedProj.interp] at hgi_eq
              simp [ConstantOrShiftedProj.interp, hf_eq,
                hgi_eq, Nat.add_assoc]
  | _, .raise _,      h, _   => by
      unfold KMor1.level at h; omega
  | _, .simrec _ _ _, h, _   => by
      unfold KMor1.level at h; omega

/-- Lemma 1.A: every level-1 K^sim term is
linear-value-bounded.  Returns `(c, k)` such that
`f.interp ctx ≤ c · sup ctx + k`.

Constants chosen conservatively (factor-of-constant
slack acceptable):
- atomic generators have tight constants;
- `comp f gs` gives `(c_f * max_c, c_f * sum_k + k_f)`
  where `max_c` is the maximum first-component over
  `gs` and `sum_k` is the sum of second-components;
- `raise` reduces to the level-0 shape's bound;
- `simrec` over a level-0 step family bounds by
  `(c_step + 2 * k_step + 1, base_max)`, absorbing the
  per-iteration `k_step` increments into the linear
  coefficient via `n ≤ sup ctx`. -/
def KMor1.linearBound :
    {a : ℕ} → (f : KMor1 a) → f.level ≤ 1 → ℕ × ℕ
  | _, .zero,         _ => (0, 0)
  | _, .succ,         _ => (1, 1)
  | _, .proj _,       _ => (1, 0)
  | _, .comp f gs,    h =>
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 1 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 1 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      let p_f := KMor1.linearBound f hf
      let max_c := Fin.foldr _ (fun i acc =>
        max acc (KMor1.linearBound (gs i) (hgs i)).1) 0
      let sum_k := Fin.foldr _ (fun i acc =>
        acc + (KMor1.linearBound (gs i) (hgs i)).2) 0
      (p_f.1 * max_c, p_f.1 * sum_k + p_f.2)
  | _, .raise f,      h => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      exact (KMor1.level0Shape f hf).linearBound
  | _, .simrec (a := _) (k := k) _ h_fam g_fam, hyp =>
      have hh : ∀ j, (h_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at hyp
        have hsup : Finset.univ.sup
            (fun l => (h_fam l).level) ≤ 0 := by
          have := le_trans (le_max_left _ _)
            (Nat.le_of_succ_le_succ hyp)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j))
          hsup
      have hg : ∀ j, (g_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at hyp
        have hsup : Finset.univ.sup
            (fun l => (g_fam l).level) ≤ 0 := by
          have := le_trans (le_max_right _ _)
            (Nat.le_of_succ_le_succ hyp)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j))
          hsup
      let h_shapes :
          Fin (k + 1) → ConstantOrShiftedProj _ :=
        fun l => KMor1.level0Shape (h_fam l) (hh l)
      let g_shapes :
          Fin (k + 1) →
            ConstantOrShiftedProj _ :=
        fun l => KMor1.level0Shape (g_fam l) (hg l)
      let max_base_const := Fin.foldr _ (fun l acc =>
        max acc (h_shapes l).linearBound.2) 0
      let max_step_c := Fin.foldr _ (fun l acc =>
        max acc (g_shapes l).linearBound.1) 0
      let max_step_k := Fin.foldr _ (fun l acc =>
        max acc (g_shapes l).linearBound.2) 0
      (max_step_c + 2 * max_step_k + 1, max_base_const)

/-- Linear-bound dominance for `ConstantOrShiftedProj`. -/
theorem ConstantOrShiftedProj.linearBound_dominates
    {a : ℕ} (s : ConstantOrShiftedProj a)
    (ctx : Fin a → ℕ) :
    s.interp ctx ≤
      s.linearBound.1 *
        (Finset.univ : Finset (Fin a)).sup ctx +
      s.linearBound.2 := by
  cases s with
  | const k =>
      simp [ConstantOrShiftedProj.interp,
            ConstantOrShiftedProj.linearBound]
  | shifted i k =>
      simp only [ConstantOrShiftedProj.interp,
                 ConstantOrShiftedProj.linearBound]
      have hctx : ctx i ≤
          (Finset.univ : Finset (Fin a)).sup ctx :=
        Finset.le_sup (Finset.mem_univ _)
      omega

/-- Generic max-foldr lemma: for any indexed function
`f : Fin n → ℕ`, `f j ≤ Fin.foldr n (fun i acc => max acc
(f i)) 0` for every `j`. -/
private theorem Fin.foldr_max_ge {n : ℕ}
    (f : Fin n → ℕ) (j : Fin n) :
    f j ≤ Fin.foldr n (fun i acc => max acc (f i)) 0 := by
  induction n with
  | zero => exact j.elim0
  | succ n' ih =>
      simp only [Fin.foldr_succ]
      by_cases hj : j = 0
      · subst hj
        exact le_max_right _ _
      · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
        specialize ih (fun l => f l.succ) j'
        exact le_trans ih (le_max_left _ _)

/-- Generic sum-foldr lemma: for any indexed function
`f : Fin n → ℕ`, `f j ≤ Fin.foldr n (fun i acc => acc +
(f i)) 0` for every `j`. -/
private theorem Fin.foldr_sum_ge {n : ℕ}
    (f : Fin n → ℕ) (j : Fin n) :
    f j ≤ Fin.foldr n (fun i acc => acc + (f i)) 0 := by
  induction n with
  | zero => exact j.elim0
  | succ n' ih =>
      simp only [Fin.foldr_succ]
      by_cases hj : j = 0
      · subst hj
        omega
      · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
        specialize ih (fun l => f l.succ) j'
        omega

/-- Helper for the simrec dominance proof: at iteration
`n`, every entry of `simrecVec` is bounded by
`base_max + n * (1 + step_k)` plus a multiple of
`sup ctx`.  The proof rests on each `g_shape` being a
level-0 `ConstantOrShiftedProj`, hence dominated by
`step_c * max(counter, sup_params, sup_prev) + step_k`. -/
private theorem KMor1.simrecVec_linear_bound_aux
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hh : ∀ j, (h_fam j).level ≤ 0)
    (hg : ∀ j, (g_fam j).level ≤ 0)
    (params : Fin a → ℕ)
    (S : ℕ)
    (hparams : ∀ j, params j ≤ S)
    (base_max : ℕ)
    (hbase_max : ∀ j,
      (KMor1.level0Shape (h_fam j) (hh j)).linearBound.2
        ≤ base_max)
    (step_c step_k : ℕ)
    (hstep_c : ∀ j,
      (KMor1.level0Shape (g_fam j) (hg j)).linearBound.1
        ≤ step_c)
    (hstep_k : ∀ j,
      (KMor1.level0Shape (g_fam j) (hg j)).linearBound.2
        ≤ step_k)
    (n : ℕ) (hn : n ≤ S) :
    ∀ j,
      KMor1.simrecVec h_fam g_fam params n j
        ≤ (step_c + step_k + 1) * S
            + base_max + step_k * n := by
  induction n with
  | zero =>
      intro j
      simp only [KMor1.simrecVec]
      have heq := KMor1.level0Shape_interp
        (h_fam j) (hh j) params
      rw [heq]
      have hdom :=
        ConstantOrShiftedProj.linearBound_dominates
          (KMor1.level0Shape (h_fam j) (hh j)) params
      set s := KMor1.level0Shape (h_fam j) (hh j)
      have hsup_params :
          (Finset.univ : Finset (Fin a)).sup params ≤ S := by
        apply Finset.sup_le
        intro i _
        exact hparams i
      have h_c_le_one : s.linearBound.1 ≤ 1 := by
        cases s with
        | const _ => simp [ConstantOrShiftedProj.linearBound]
        | shifted _ _ =>
            simp [ConstantOrShiftedProj.linearBound]
      have hbase_j := hbase_max j
      change s.interp params ≤ _ at hdom
      have hbound : s.linearBound.1 *
          (Finset.univ : Finset (Fin a)).sup params
          ≤ S := by
        calc s.linearBound.1 *
              (Finset.univ : Finset (Fin a)).sup params
            ≤ 1 *
              (Finset.univ : Finset (Fin a)).sup params := by
              exact Nat.mul_le_mul_right _ h_c_le_one
          _ = (Finset.univ : Finset (Fin a)).sup params := by
              ring
          _ ≤ S := hsup_params
      have : s.interp params ≤ S + base_max := by
        calc s.interp params
            ≤ s.linearBound.1 *
                (Finset.univ : Finset (Fin a)).sup params
              + s.linearBound.2 := hdom
          _ ≤ S + base_max := by
              exact Nat.add_le_add hbound hbase_j
      calc s.interp params
          ≤ S + base_max := this
        _ ≤ (step_c + step_k + 1) * S + base_max
              + step_k * 0 := by
            have : S ≤ (step_c + step_k + 1) * S := by
              have h1 : 1 * S ≤ (step_c + step_k + 1) * S :=
                Nat.mul_le_mul_right _ (by omega)
              omega
            omega
  | succ n ih =>
      intro j
      have hn' : n ≤ S := Nat.le_of_succ_le hn
      have ih' := ih hn'
      simp only [KMor1.simrecVec]
      set s := KMor1.level0Shape (g_fam j) (hg j) with hsdef
      let stepCtx :
          Fin (a + 1 + (k + 1)) → ℕ :=
        fun idx =>
          if h₁ : idx.val < a + 1 then
            if _ : idx.val = 0 then n
            else params ⟨idx.val - 1, by omega⟩
          else
            KMor1.simrecVec h_fam g_fam params n
              ⟨idx.val - (a + 1), by omega⟩
      have heq : (g_fam j).interp stepCtx
          = s.interp stepCtx := by
        rw [hsdef]
        exact KMor1.level0Shape_interp (g_fam j) (hg j) stepCtx
      change (g_fam j).interp stepCtx ≤ _
      rw [heq]
      have hdom :=
        ConstantOrShiftedProj.linearBound_dominates s stepCtx
      have hstep_c_j := hstep_c j
      have hstep_k_j := hstep_k j
      have hctx_bound : ∀ idx,
          stepCtx idx ≤
            (step_c + step_k + 1) * S
              + base_max + step_k * n := by
        intro idx
        by_cases h₁ : idx.val < a + 1
        · simp only [stepCtx, h₁, dite_true]
          by_cases h₂ : idx.val = 0
          · simp only [h₂, dite_true]
            calc n ≤ S := hn'
              _ ≤ (step_c + step_k + 1) * S := by
                  have : 1 * S ≤
                      (step_c + step_k + 1) * S :=
                    Nat.mul_le_mul_right _ (by omega)
                  omega
              _ ≤ (step_c + step_k + 1) * S
                    + base_max + step_k * n := by omega
          · simp only [h₂, dite_false]
            calc params ⟨idx.val - 1, by omega⟩
                ≤ S := hparams _
              _ ≤ (step_c + step_k + 1) * S := by
                  have : 1 * S ≤
                      (step_c + step_k + 1) * S :=
                    Nat.mul_le_mul_right _ (by omega)
                  omega
              _ ≤ (step_c + step_k + 1) * S
                    + base_max + step_k * n := by omega
        · simp only [stepCtx, h₁, dite_false]
          exact ih' _
      have hsup_le :
          (Finset.univ : Finset (Fin (a + 1 + (k + 1)))).sup
            stepCtx
            ≤ (step_c + step_k + 1) * S
                + base_max + step_k * n := by
        apply Finset.sup_le
        intro idx _
        exact hctx_bound idx
      have h_c_le_one : s.linearBound.1 ≤ 1 := by
        cases s with
        | const _ => simp [ConstantOrShiftedProj.linearBound]
        | shifted _ _ =>
            simp [ConstantOrShiftedProj.linearBound]
      have hmul :
          s.linearBound.1 *
            (Finset.univ : Finset (Fin (a + 1 + (k + 1)))).sup
              stepCtx
            ≤ 1 *
            ((step_c + step_k + 1) * S
                + base_max + step_k * n) := by
        calc s.linearBound.1 *
              (Finset.univ : Finset (Fin (a + 1 + (k + 1)))).sup
                stepCtx
            ≤ 1 *
              (Finset.univ : Finset (Fin (a + 1 + (k + 1)))).sup
                stepCtx := by
              exact Nat.mul_le_mul_right _ h_c_le_one
          _ ≤ 1 *
              ((step_c + step_k + 1) * S
                  + base_max + step_k * n) := by
              exact Nat.mul_le_mul_left _ hsup_le
      have hbound :
          s.interp stepCtx ≤
            ((step_c + step_k + 1) * S
                + base_max + step_k * n) + step_k := by
        calc s.interp stepCtx
            ≤ s.linearBound.1 *
                (Finset.univ :
                  Finset (Fin (a + 1 + (k + 1)))).sup stepCtx
              + s.linearBound.2 := hdom
          _ ≤ 1 *
                ((step_c + step_k + 1) * S
                    + base_max + step_k * n)
              + step_k := by
              exact Nat.add_le_add hmul hstep_k_j
          _ = ((step_c + step_k + 1) * S
                  + base_max + step_k * n) + step_k := by
              ring
      calc s.interp stepCtx
          ≤ ((step_c + step_k + 1) * S
                + base_max + step_k * n) + step_k := hbound
        _ = (step_c + step_k + 1) * S
              + base_max + step_k * (n + 1) := by ring

/-- The linear bound dominates the K^sim interp: for all
contexts, `f.interp ctx ≤ c · sup ctx + k`. -/
theorem KMor1.linearBound_dominates :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
      (ctx : Fin a → ℕ),
      f.interp ctx ≤
        (KMor1.linearBound f h).1 *
          (Finset.univ : Finset (Fin a)).sup ctx +
        (KMor1.linearBound f h).2
  | _, .zero,         _, _   => by
      simp [KMor1.linearBound, KMor1.interp]
  | _, .succ,         _, ctx => by
      simp only [KMor1.linearBound, KMor1.interp_succ,
        Nat.succ_eq_add_one]
      have hctx : ctx 0 ≤
          (Finset.univ : Finset (Fin 1)).sup ctx :=
        Finset.le_sup (Finset.mem_univ _)
      omega
  | _, .proj i,       _, ctx => by
      simp only [KMor1.linearBound, KMor1.interp_proj]
      have hctx : ctx i ≤
          (Finset.univ : Finset (Fin _)).sup ctx :=
        Finset.le_sup (Finset.mem_univ _)
      omega
  | a, .comp (b := b) f gs, h, ctx => by
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 1 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 1 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      simp only [KMor1.interp_comp, KMor1.linearBound]
      set p_f := KMor1.linearBound f hf
      set max_c := Fin.foldr b (fun i acc =>
        max acc (KMor1.linearBound (gs i) (hgs i)).1) 0
      set sum_k := Fin.foldr b (fun i acc =>
        acc + (KMor1.linearBound (gs i) (hgs i)).2) 0
      have hmax_c : ∀ i,
          (KMor1.linearBound (gs i) (hgs i)).1 ≤ max_c :=
        fun i =>
          Fin.foldr_max_ge
            (fun j =>
              (KMor1.linearBound (gs j) (hgs j)).1) i
      have hsum_k : ∀ i,
          (KMor1.linearBound (gs i) (hgs i)).2 ≤ sum_k :=
        fun i =>
          Fin.foldr_sum_ge
            (fun j =>
              (KMor1.linearBound (gs j) (hgs j)).2) i
      set ys : Fin b → ℕ := fun i => (gs i).interp ctx
      have hys_bound : ∀ i,
          ys i ≤ max_c *
            (Finset.univ : Finset (Fin a)).sup ctx
            + sum_k := by
        intro i
        have hi := KMor1.linearBound_dominates
          (gs i) (hgs i) ctx
        calc ys i
            ≤ (KMor1.linearBound (gs i) (hgs i)).1 *
                (Finset.univ : Finset (Fin a)).sup ctx
              + (KMor1.linearBound (gs i) (hgs i)).2 := hi
          _ ≤ max_c *
                (Finset.univ : Finset (Fin a)).sup ctx
              + sum_k := by
              have h1 :
                  (KMor1.linearBound (gs i) (hgs i)).1 *
                    (Finset.univ :
                      Finset (Fin a)).sup ctx
                    ≤ max_c *
                    (Finset.univ : Finset (Fin a)).sup ctx :=
                Nat.mul_le_mul_right _ (hmax_c i)
              have h2 :
                  (KMor1.linearBound (gs i) (hgs i)).2
                    ≤ sum_k := hsum_k i
              omega
      have hsup_ys :
          (Finset.univ : Finset (Fin b)).sup ys
            ≤ max_c *
              (Finset.univ : Finset (Fin a)).sup ctx
            + sum_k := by
        apply Finset.sup_le
        intro i _
        exact hys_bound i
      have hf_dom := KMor1.linearBound_dominates f hf ys
      calc f.interp ys
          ≤ p_f.1 *
              (Finset.univ : Finset (Fin b)).sup ys
            + p_f.2 := hf_dom
        _ ≤ p_f.1 *
              (max_c *
                (Finset.univ :
                  Finset (Fin a)).sup ctx + sum_k)
            + p_f.2 := by
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_left _ hsup_ys) _
        _ = p_f.1 * max_c *
              (Finset.univ : Finset (Fin a)).sup ctx
            + (p_f.1 * sum_k + p_f.2) := by ring
  | _, .raise f,      h, ctx => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      simp only [KMor1.linearBound, KMor1.interp_raise]
      rw [KMor1.level0Shape_interp f hf ctx]
      exact ConstantOrShiftedProj.linearBound_dominates _ ctx
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp, ctx => by
      have hh : ∀ j, (h_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at hyp
        have hsup : Finset.univ.sup
            (fun l => (h_fam l).level) ≤ 0 := by
          have := le_trans (le_max_left _ _)
            (Nat.le_of_succ_le_succ hyp)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j))
          hsup
      have hg : ∀ j, (g_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at hyp
        have hsup : Finset.univ.sup
            (fun l => (g_fam l).level) ≤ 0 := by
          have := le_trans (le_max_right _ _)
            (Nat.le_of_succ_le_succ hyp)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j))
          hsup
      simp only [KMor1.linearBound, KMor1.interp_simrec]
      set max_base_const := Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (h_fam l) (hh l)).linearBound.2)
        0 with hmbc_def
      set max_step_c := Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (hg l)).linearBound.1)
        0 with hmsc_def
      set max_step_k := Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (hg l)).linearBound.2)
        0 with hmsk_def
      have hbm : ∀ j,
          (KMor1.level0Shape (h_fam j) (hh j)).linearBound.2
            ≤ max_base_const := fun j =>
        Fin.foldr_max_ge
          (fun l =>
            (KMor1.level0Shape (h_fam l) (hh l)).linearBound.2)
          j
      have hsc : ∀ j,
          (KMor1.level0Shape (g_fam j) (hg j)).linearBound.1
            ≤ max_step_c := fun j =>
        Fin.foldr_max_ge
          (fun l =>
            (KMor1.level0Shape (g_fam l) (hg l)).linearBound.1)
          j
      have hsk : ∀ j,
          (KMor1.level0Shape (g_fam j) (hg j)).linearBound.2
            ≤ max_step_k := fun j =>
        Fin.foldr_max_ge
          (fun l =>
            (KMor1.level0Shape (g_fam l) (hg l)).linearBound.2)
          j
      set S := (Finset.univ : Finset (Fin (a + 1))).sup ctx
        with hSdef
      have hctx0_le_S : ctx 0 ≤ S := by
        rw [hSdef]
        exact Finset.le_sup (Finset.mem_univ _)
      have hparams : ∀ j, ctx (Fin.succ j) ≤ S := by
        intro j
        rw [hSdef]
        exact Finset.le_sup (Finset.mem_univ _)
      have haux := KMor1.simrecVec_linear_bound_aux
        h_fam g_fam hh hg
        (fun j => ctx (Fin.succ j)) S hparams
        max_base_const hbm
        max_step_c max_step_k hsc hsk
        (ctx 0) hctx0_le_S i
      calc KMor1.simrecVec h_fam g_fam
              (fun j => ctx (Fin.succ j)) (ctx 0) i
          ≤ (max_step_c + max_step_k + 1) * S
              + max_base_const + max_step_k * (ctx 0) :=
            haux
        _ ≤ (max_step_c + 2 * max_step_k + 1) * S
              + max_base_const := by
            have hck : max_step_k * (ctx 0)
                ≤ max_step_k * S :=
              Nat.mul_le_mul_left _ hctx0_le_S
            have hcoeff :
                (max_step_c + max_step_k + 1) * S
                  + max_step_k * S
                  = (max_step_c + 2 * max_step_k + 1) * S := by
              ring
            omega

/-- Polynomial bound for the packed simrec base.  Takes
per-component PolyBounds as inputs and produces a
PolyBound on the seqPack of the components. -/
def kSimPackedBase_polyBound {a k : ℕ}
    (h_ER : Fin (k + 1) → ERMor1 a)
    (pb_h : (l : Fin (k + 1)) → ERMor1.PolyBound (h_ER l)) :
    ERMor1.PolyBound (kSimPackedBase h_ER) :=
  let D_of : Fin (k + 1) → ℕ := fun l =>
    (pb_h l).degree + (pb_h l).coefficient
      + (pb_h l).constant + 2
  let D : ℕ :=
    (Finset.univ : Finset (Fin (k + 1))).sup D_of
  let E : ℕ := (D + 5) * 4 ^ (k + 1)
  { degree := E
    coefficient := 3 ^ E
    constant := 0
    bounds := fun ctx => by
      simp only [kSimPackedBase_interp, Nat.add_zero]
      set s := maxCtx ctx with hs_def
      have h_each :
          ∀ v ∈ ((List.finRange (k + 1)).map
                  (fun j => (h_ER j).interp ctx)),
            v ≤ (s + 1 + 1) ^ D := by
        intro v hv
        rcases List.mem_map.mp hv with ⟨l, _, hvl⟩
        have h_pow_shift :=
          ERMor1.PolyBound.le_pow_shift_of_polyBound
            (h_ER l) (pb_h l) ctx
        rw [hvl.symm] at *
        change (h_ER l).interp ctx ≤ (s + 2) ^ D
        have h_dl_le_D :
            D_of l ≤ D := by
          exact Finset.le_sup (f := D_of)
            (Finset.mem_univ l)
        have h_base_pos : 1 ≤ s + 2 := by omega
        have h_pow_mono :
            (s + 2) ^ (D_of l) ≤ (s + 2) ^ D :=
          Nat.pow_le_pow_right h_base_pos h_dl_le_D
        change (h_ER l).interp ctx ≤
          (maxCtx ctx + 2) ^ (D_of l) at h_pow_shift
        rw [hs_def.symm] at h_pow_shift
        exact le_trans h_pow_shift h_pow_mono
      have hlen :
          ((List.finRange (k + 1)).map
            (fun j => (h_ER j).interp ctx)).length
            ≤ k + 1 := by
        simp
      have h_pack :=
        Nat.seqPack_le_seqPackBound
          ((List.finRange (k + 1)).map
            (fun j => (h_ER j).interp ctx))
          k D (s + 1) hlen h_each
      change Nat.seqPack _ ≤ (s + 1 + 2) ^ E at h_pack
      have h_base_le : s + 3 ≤ 3 * (s + 1) := by omega
      have h_pow_le :
          (s + 3) ^ E ≤ (3 * (s + 1)) ^ E :=
        Nat.pow_le_pow_left h_base_le E
      have h_split :
          (3 * (s + 1)) ^ E = 3 ^ E * (s + 1) ^ E := by
        rw [Nat.mul_pow]
      have h_s3_eq : s + 1 + 2 = s + 3 := by ring
      rw [h_s3_eq] at h_pack
      have h_combined :
          Nat.seqPack
              ((List.finRange (k + 1)).map
                (fun j => (h_ER j).interp ctx))
            ≤ 3 ^ E * (s + 1) ^ E := by
        calc Nat.seqPack _
            ≤ (s + 3) ^ E := h_pack
          _ ≤ (3 * (s + 1)) ^ E := h_pow_le
          _ = 3 ^ E * (s + 1) ^ E := h_split
      exact h_combined }

/-- Polynomial bound for the packed simrec step.  Takes
per-component PolyBounds as inputs (where each component
is a step morphism `g_ER l : ERMor1 (a + 1 + (k + 1))`)
and produces a PolyBound on the packed step term
`kSimPackedStep g_ER : ERMor1 (a + 2)`.

The packed step composes seqPack with kSimStepContext, so
the bound combines seqPack's polynomial blow-up with
kSimStepContext's substitution. -/
def kSimPackedStep_polyBound {a k : ℕ}
    (g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (pb_g : (l : Fin (k + 1)) → ERMor1.PolyBound (g_ER l)) :
    ERMor1.PolyBound (kSimPackedStep g_ER) :=
  let D_of : Fin (k + 1) → ℕ := fun l =>
    (pb_g l).degree + (pb_g l).coefficient
      + (pb_g l).constant + 2
  let D : ℕ :=
    (Finset.univ : Finset (Fin (k + 1))).sup D_of
  let E : ℕ := (D + 5) * 4 ^ (k + 1)
  { degree := E
    coefficient := 3 ^ E
    constant := 0
    bounds := fun ctx => by
      simp only [kSimPackedStep_interp, Nat.add_zero]
      set s := maxCtx ctx with hs_def
      set subCtx :
          Fin (a + 1 + (k + 1)) → ℕ :=
        fun idx => (kSimStepContext idx).interp ctx
        with hsub_def
      have h_subCtx_le : ∀ idx, subCtx idx ≤ s := by
        intro idx
        rw [hsub_def]
        unfold kSimStepContext
        by_cases h₀ : idx.val = 0
        · simp only [h₀, dite_true]
          rw [ERMor1.interp_proj]
          rw [hs_def]
          exact le_maxCtx ctx _
        · by_cases h₁ : idx.val < a + 1
          · simp only [h₀, h₁, dite_true, dite_false]
            rw [ERMor1.interp_proj]
            rw [hs_def]
            exact le_maxCtx ctx _
          · simp only [h₀, h₁, dite_false]
            rw [ERMor1.interp_comp]
            set unpackCtx :
                Fin (a + 1) → ℕ :=
              fun j =>
                (if h : j.val = 0 then
                  ERMor1.proj (k := a + 2)
                    ⟨1, by omega⟩
                else
                  ERMor1.proj (k := a + 2)
                    ⟨j.val + 1, by
                      have := j.isLt; omega⟩).interp ctx
              with hu_def
            change (kSimSzudzikUnpackAt a
                (idx.val - (a + 1))).interp unpackCtx ≤ s
            have hu0 : unpackCtx 0 = ctx ⟨1, by omega⟩ := by
              rw [hu_def]
              simp only [Fin.val_zero, dite_true]
              rw [ERMor1.interp_proj]
            have hu_eq :
                unpackCtx =
                  Fin.cons (ctx ⟨1, by omega⟩)
                    (fun j : Fin a =>
                      ctx ⟨j.val + 2, by
                        have := j.isLt; omega⟩) := by
              funext j
              refine Fin.cases ?_ ?_ j
              · exact hu0
              · intro j'
                rw [hu_def]
                have hjne : (Fin.succ j').val ≠ 0 := by
                  simp [Fin.succ]
                simp only [hjne, dite_false]
                rw [ERMor1.interp_proj]
                rw [Fin.cons_succ]
                rfl
            rw [hu_eq]
            rw [kSimSzudzikUnpackAt_interp_eq_seqAt]
            calc Nat.seqAt (ctx ⟨1, by omega⟩)
                  (idx.val - (a + 1))
                ≤ ctx ⟨1, by omega⟩ := Nat.seqAt_le _ _
              _ ≤ s := by
                  rw [hs_def]
                  exact le_maxCtx ctx _
      have h_each :
          ∀ v ∈ ((List.finRange (k + 1)).map
                  (fun j =>
                    (g_ER j).interp subCtx)),
            v ≤ (s + 1 + 1) ^ D := by
        intro v hv
        rcases List.mem_map.mp hv with ⟨l, _, hvl⟩
        have h_pow_shift :=
          ERMor1.PolyBound.le_pow_shift_of_polyBound
            (g_ER l) (pb_g l) subCtx
        change (g_ER l).interp subCtx ≤
          (maxCtx subCtx + 2) ^ (D_of l) at h_pow_shift
        have h_max_sub :
            maxCtx subCtx ≤ s := by
          apply Finset.sup_le
          intro idx _
          exact h_subCtx_le idx
        have h_base_pos : 1 ≤ s + 2 := by omega
        have h_pow_base :
            (maxCtx subCtx + 2) ^ (D_of l)
              ≤ (s + 2) ^ (D_of l) :=
          Nat.pow_le_pow_left (by omega) _
        have h_dl_le_D :
            D_of l ≤ D := by
          exact Finset.le_sup (f := D_of)
            (Finset.mem_univ l)
        have h_pow_mono :
            (s + 2) ^ (D_of l) ≤ (s + 2) ^ D :=
          Nat.pow_le_pow_right h_base_pos h_dl_le_D
        rw [hvl.symm]
        change (g_ER l).interp subCtx ≤ (s + 2) ^ D
        exact le_trans h_pow_shift
          (le_trans h_pow_base h_pow_mono)
      have hlen :
          ((List.finRange (k + 1)).map
            (fun j => (g_ER j).interp subCtx)).length
            ≤ k + 1 := by
        simp
      have h_pack :=
        Nat.seqPack_le_seqPackBound
          ((List.finRange (k + 1)).map
            (fun j => (g_ER j).interp subCtx))
          k D (s + 1) hlen h_each
      change Nat.seqPack _ ≤ (s + 1 + 2) ^ E at h_pack
      have h_base_le : s + 3 ≤ 3 * (s + 1) := by omega
      have h_pow_le :
          (s + 3) ^ E ≤ (3 * (s + 1)) ^ E :=
        Nat.pow_le_pow_left h_base_le E
      have h_split :
          (3 * (s + 1)) ^ E = 3 ^ E * (s + 1) ^ E := by
        rw [Nat.mul_pow]
      have h_s3_eq : s + 1 + 2 = s + 3 := by ring
      rw [h_s3_eq] at h_pack
      have h_combined :
          Nat.seqPack
              ((List.finRange (k + 1)).map
                (fun j => (g_ER j).interp subCtx))
            ≤ 3 ^ E * (s + 1) ^ E := by
        calc Nat.seqPack _
            ≤ (s + 3) ^ E := h_pack
          _ ≤ (3 * (s + 1)) ^ E := h_pow_le
          _ = 3 ^ E * (s + 1) ^ E := h_split
      exact h_combined }

/-- Interp preservation for level-0 K^sim: `kToER` of a
level-0 term has interp matching the K^sim interp.  Base
case of the recursive bootstrap for K^sim_n ⊆ E^{n+1}.

By structural recursion on level-0 KMor1 (zero, succ,
proj, comp).  `raise` and `simrec` cases are vacuous at
level 0. -/
theorem kToER_interp_level_zero :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0)
      (ctx : Fin a → ℕ),
      (kToER f
        (Nat.le_succ_of_le (Nat.le_succ_of_le h))).interp
          ctx = f.interp ctx
  | _, .zero,         _, _   => by
      simp [kToER, KMor1.interp_zero, ERMor1.interp_zeroN]
  | _, .succ,         _, _   => by
      simp [kToER, KMor1.interp_succ, ERMor1.interp_succ]
  | _, .proj _,       _, _   => by
      simp [kToER, KMor1.interp_proj, ERMor1.interp_proj]
  | _, .comp f gs,    h, ctx => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 0 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 0 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      have h_inner :
          (fun i => (kToER (gs i)
              (Nat.le_succ_of_le
                (Nat.le_succ_of_le (hgs i)))).interp ctx)
            = (fun i => (gs i).interp ctx) := by
        funext i
        exact kToER_interp_level_zero (gs i) (hgs i) ctx
      simp only [kToER, ERMor1.interp_comp,
        KMor1.interp_comp]
      rw [h_inner]
      exact kToER_interp_level_zero f hf
        (fun i => (gs i).interp ctx)
  | _, .raise _,      h, _   => by
      unfold KMor1.level at h; omega
  | _, .simrec _ _ _, h, _   => by
      unfold KMor1.level at h; omega

/-- Linear bound on level-0 K^sim's kToER image.  The
constants are given by `level0Shape`'s `linearBound`:
either `(0, k)` (constant) or `(1, k)` (shifted
projection). -/
theorem kToER_linearBound_dominates_level_zero
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0)
    (ctx : Fin a → ℕ) :
    (kToER f
      (Nat.le_succ_of_le (Nat.le_succ_of_le h))).interp
        ctx ≤
      (KMor1.level0Shape f h).linearBound.1 *
        (Finset.univ : Finset (Fin a)).sup ctx +
      (KMor1.level0Shape f h).linearBound.2 := by
  rw [kToER_interp_level_zero f h ctx,
    KMor1.level0Shape_interp f h ctx]
  exact ConstantOrShiftedProj.linearBound_dominates _ ctx

/-- Structural bound on the constant offset of the
level-0 shape's linear bound, in terms of the tower
height of the ER translation: `linearBound.2 ≤
towerHeight + 1`.  Required for A.5.2.2's argument-
inequality proof. -/
private theorem kToER_level0_towerHeight_ge_const :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 0) →
      (KMor1.level0Shape f h).linearBound.2 ≤
        (kToER f
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le h))).towerHeight + 1
  | _, .zero,         _ => by
      simp [kToER, KMor1.level0Shape,
        ConstantOrShiftedProj.linearBound, ERMor1.zeroN,
        ERMor1.towerHeight]
  | _, .succ,         _ => by
      simp [kToER, KMor1.level0Shape,
        ConstantOrShiftedProj.linearBound,
        ERMor1.towerHeight]
  | _, .proj _,       _ => by
      simp [kToER, KMor1.level0Shape,
        ConstantOrShiftedProj.linearBound,
        ERMor1.towerHeight]
  | _, .comp f gs,    h => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 0 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 0 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      have ihf := kToER_level0_towerHeight_ge_const f hf
      have ihgs := fun i =>
        kToER_level0_towerHeight_ge_const (gs i) (hgs i)
      simp only [kToER, KMor1.level0Shape, ERMor1.towerHeight]
      cases hshape_f : f.level0Shape hf with
      | const k_f =>
          rw [hshape_f] at ihf
          simp only [ConstantOrShiftedProj.linearBound] at ihf ⊢
          omega
      | shifted i k_f =>
          rw [hshape_f] at ihf
          simp only [ConstantOrShiftedProj.linearBound] at ihf
          have ihgi := ihgs i
          cases hshape_gi : (gs i).level0Shape (hgs i) with
          | const c =>
              rw [hshape_gi] at ihgi
              simp only [hshape_gi,
                ConstantOrShiftedProj.linearBound]
                at ihgi ⊢
              have hsup_le :
                  (kToER (gs i)
                    (Nat.le_succ_of_le
                      (Nat.le_succ_of_le (hgs i)))).towerHeight
                  ≤ Finset.univ.sup
                      (fun j => (kToER (gs j)
                        (Nat.le_succ_of_le
                          (Nat.le_succ_of_le
                            (hgs j)))).towerHeight) :=
                Finset.le_sup
                  (f := fun j => (kToER (gs j)
                    (Nat.le_succ_of_le
                      (Nat.le_succ_of_le
                        (hgs j)))).towerHeight)
                  (Finset.mem_univ i)
              omega
          | shifted j k_gs =>
              rw [hshape_gi] at ihgi
              simp only [hshape_gi,
                ConstantOrShiftedProj.linearBound]
                at ihgi ⊢
              have hsup_le :
                  (kToER (gs i)
                    (Nat.le_succ_of_le
                      (Nat.le_succ_of_le (hgs i)))).towerHeight
                  ≤ Finset.univ.sup
                      (fun j => (kToER (gs j)
                        (Nat.le_succ_of_le
                          (Nat.le_succ_of_le
                            (hgs j)))).towerHeight) :=
                Finset.le_sup
                  (f := fun j => (kToER (gs j)
                    (Nat.le_succ_of_le
                      (Nat.le_succ_of_le
                        (hgs j)))).towerHeight)
                  (Finset.mem_univ i)
              omega
  | _, .raise _,      h => by
      unfold KMor1.level at h; omega
  | _, .simrec _ _ _, h => by
      unfold KMor1.level at h; omega

/-- For level-1 simrec (level-0 children), the iterated
packed value matches `seqPack` of `KMor1.simrecVec`. -/
private theorem packed_iteration_matches_simrecVec
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (params : Fin a → ℕ) (j : ℕ) :
    Nat.rec
      ((kSimPackedBase (fun l => kToER (h_fam l)
        (Nat.le_succ_of_le
          (Nat.le_succ_of_le (h_h l))))).interp params)
      (fun i prev =>
        (kSimPackedStep (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le (h_g l))))).interp
        (Fin.cons i (Fin.cons prev params)))
      j =
      Nat.seqPack
        ((List.finRange (k + 1)).map
          (fun l =>
            KMor1.simrecVec h_fam g_fam params j l)) := by
  induction j with
  | zero =>
      change (kSimPackedBase _).interp params = _
      rw [kSimPackedBase_interp]
      congr 1
      apply List.map_congr_left
      intro l _
      simp only [KMor1.simrecVec_zero]
      exact kToER_interp_level_zero (h_fam l) (h_h l) params
  | succ n ih =>
      set base_val :=
        (kSimPackedBase (fun l =>
          kToER (h_fam l)
            (Nat.le_succ_of_le
              (Nat.le_succ_of_le (h_h l))))).interp params
        with hbase
      set step_fn :
          ℕ → ℕ → ℕ :=
        fun i prev =>
          (kSimPackedStep (fun l =>
            kToER (g_fam l)
              (Nat.le_succ_of_le
                (Nat.le_succ_of_le (h_g l))))).interp
          (Fin.cons i (Fin.cons prev params))
        with hstep
      set P : ℕ :=
        Nat.rec (motive := fun _ => ℕ) base_val step_fn n
        with hP
      change (kSimPackedStep _).interp
          (Fin.cons (n : ℕ) (Fin.cons P params)) = _
      rw [kSimPackedStep_interp]
      have h_ctx_eq :
          (fun idx : Fin (a + 1 + (k + 1)) =>
              (kSimStepContext idx).interp
                (Fin.cons (n : ℕ)
                  (Fin.cons P params))) =
            fun idx : Fin (a + 1 + (k + 1)) =>
              if h₁ : idx.val < a + 1 then
                if _h₂ : idx.val = 0 then
                  (n : ℕ)
                else
                  params ⟨idx.val - 1, by omega⟩
              else
                KMor1.simrecVec h_fam g_fam params n
                  ⟨idx.val - (a + 1), by omega⟩ := by
        funext idx
        unfold kSimStepContext
        by_cases h₀ : idx.val = 0
        · simp only [h₀, dite_true]
          rw [ERMor1.interp_proj]
          have hlt : (0 : ℕ) < a + 1 := by omega
          simp only [hlt, dite_true]
          rfl
        · by_cases h₁ : idx.val < a + 1
          · simp only [h₀, h₁, dite_true, dite_false]
            rw [ERMor1.interp_proj]
            have hidx_pos : 0 < idx.val := Nat.pos_of_ne_zero h₀
            have hidx_lt_a : idx.val - 1 < a := by omega
            have h_unfold :
                (Fin.cons (n : ℕ)
                  (Fin.cons P params) :
                    Fin (a + 2) → ℕ)
                  ⟨idx.val + 1, by
                    have := idx.isLt; omega⟩ =
                  params ⟨idx.val - 1, by omega⟩ := by
              have h1 :
                  (⟨idx.val + 1, by
                    have := idx.isLt; omega⟩ :
                      Fin (a + 2)) =
                  Fin.succ ⟨idx.val, by omega⟩ := by
                apply Fin.ext; rfl
              rw [h1, Fin.cons_succ]
              have h2 :
                  (⟨idx.val, by omega⟩ : Fin (a + 1)) =
                  Fin.succ ⟨idx.val - 1, hidx_lt_a⟩ := by
                apply Fin.ext
                change idx.val = (idx.val - 1) + 1
                omega
              rw [h2, Fin.cons_succ]
            exact h_unfold
          · simp only [h₀, h₁, dite_false]
            rw [ERMor1.interp_comp]
            set unpackCtx :
                Fin (a + 1) → ℕ :=
              fun j =>
                (if h : j.val = 0 then
                  ERMor1.proj (k := a + 2)
                    ⟨1, by omega⟩
                else
                  ERMor1.proj (k := a + 2)
                    ⟨j.val + 1, by
                      have := j.isLt; omega⟩).interp
                  (Fin.cons (n : ℕ)
                    (Fin.cons P params))
              with hu_def
            change (kSimSzudzikUnpackAt a
                (idx.val - (a + 1))).interp unpackCtx = _
            have hu0 : unpackCtx 0 = P := by
              rw [hu_def]
              simp only [Fin.val_zero, dite_true]
              rw [ERMor1.interp_proj]
              rfl
            have hu_eq :
                unpackCtx = Fin.cons P params := by
              funext j
              refine Fin.cases ?_ ?_ j
              · exact hu0
              · intro j'
                rw [hu_def]
                have hjne : (Fin.succ j').val ≠ 0 := by
                  simp [Fin.succ]
                simp only [hjne, dite_false]
                rw [ERMor1.interp_proj]
                rw [Fin.cons_succ]
                rfl
            rw [hu_eq, kSimSzudzikUnpackAt_interp_eq_seqAt]
            rw [show P = _ from ih]
            have hlen :
                ((List.finRange (k + 1)).map
                  (fun l =>
                    KMor1.simrecVec
                      h_fam g_fam params n l)).length
                  = k + 1 := by
              simp
            have h_idx_lt :
                idx.val - (a + 1) < k + 1 := by
              have := idx.isLt
              omega
            rw [Nat.seqAt_seqPack
              (xs := (List.finRange (k + 1)).map
                (fun l =>
                  KMor1.simrecVec h_fam g_fam params n l))
              (i := idx.val - (a + 1))
              (h := by rw [hlen]; exact h_idx_lt)]
            simp
      rw [h_ctx_eq]
      simp only [KMor1.simrecVec_succ]
      congr 1
      apply List.map_congr_left
      intro l _
      exact kToER_interp_level_zero (g_fam l) (h_g l) _

/-- Structural lower bound on `kSimSzudzikPackList`'s
tower height: the outer `comp succ (comp natPair _)` ensures
the value is at least 2 regardless of the input family. -/
private theorem kSimSzudzikPackList_towerHeight_ge_two :
    ∀ {a k : ℕ} (t : Fin (k + 1) → ERMor1 a),
      2 ≤ (kSimSzudzikPackList t).towerHeight
  | a, 0,     t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      let F : Fin 1 → ℕ := fun _ ↦
        ERMor1.natPair.towerHeight +
          Finset.univ.sup (fun i : Fin 2 ↦
            (match i with
              | ⟨0, _⟩ => t 0
              | ⟨1, _⟩ => ERMor1.zeroN a).towerHeight) + 1
      have hF0 : F 0 ≥ 1 := Nat.le_add_left _ _
      have hsup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      change 2 ≤ 0 + Finset.univ.sup F + 1
      omega
  | a, k + 1, t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      let F : Fin 1 → ℕ := fun _ ↦
        ERMor1.natPair.towerHeight +
          Finset.univ.sup (fun i : Fin 2 ↦
            (match i with
              | ⟨0, _⟩ => t 0
              | ⟨1, _⟩ =>
                  kSimSzudzikPackList (a := a) (k := k)
                    (fun j => t j.succ)).towerHeight) + 1
      have hF0 : F 0 ≥ 1 := Nat.le_add_left _ _
      have hsup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      change 2 ≤ 0 + Finset.univ.sup F + 1
      omega

/-- Strengthened structural lower bound on
`kSimSzudzikPackList`'s tower height: each iteration of the
right-associated `comp natPair` contributes one additional
level, so a system of size `k + 1` packs to a term of tower
height at least `k + 2`. -/
private theorem kSimSzudzikPackList_towerHeight_ge_succ_k :
    ∀ {a k : ℕ} (t : Fin (k + 1) → ERMor1 a),
      k + 2 ≤ (kSimSzudzikPackList t).towerHeight
  | _, 0,     t => kSimSzudzikPackList_towerHeight_ge_two t
  | a, k + 1, t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      let G : Fin 2 → ℕ := fun i ↦
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ =>
              kSimSzudzikPackList (a := a) (k := k)
                (fun j => t j.succ)).towerHeight
      have hG1 : G ⟨1, by omega⟩ =
          (kSimSzudzikPackList (a := a) (k := k)
            (fun j => t j.succ)).towerHeight := rfl
      have hG_le_sup : G ⟨1, by omega⟩ ≤ Finset.univ.sup G :=
        Finset.le_sup (Finset.mem_univ _)
      have hIH := kSimSzudzikPackList_towerHeight_ge_succ_k
        (a := a) (k := k) (fun j => t j.succ)
      let F : Fin 1 → ℕ := fun _ ↦
        ERMor1.natPair.towerHeight +
          Finset.univ.sup G + 1
      have hF0_ge : F 0 ≥ k + 3 := by
        change ERMor1.natPair.towerHeight +
          Finset.univ.sup G + 1 ≥ k + 3
        rw [hG1] at hG_le_sup
        omega
      have hF0_le_sup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      change k + 1 + 2 ≤ 0 + Finset.univ.sup F + 1
      omega

/-- Structural lower bound on `kSimPackedStep`'s tower
height. -/
private theorem kSimPackedStep_towerHeight_ge_two
    {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    2 ≤ (kSimPackedStep g).towerHeight := by
  unfold kSimPackedStep
  exact kSimSzudzikPackList_towerHeight_ge_two _

/-- Strengthened structural lower bound on `kSimPackedStep`'s
tower height: at system size `k + 1` the packed step term has
tower height at least `k + 2`. -/
private theorem kSimPackedStep_towerHeight_ge_succ_k
    {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    k + 2 ≤ (kSimPackedStep g).towerHeight := by
  unfold kSimPackedStep
  exact kSimSzudzikPackList_towerHeight_ge_succ_k _

/-- `kSimSzudzikPackList`'s towerHeight propagates the
maximum child tower height through a constant offset.
The structural recursion adds `natPair.towerHeight + 2`
per layer (`natPair.towerHeight` from the inner
`comp natPair`, +1 from natPair's own outer `comp`, +1
from the outer `comp succ`), so the sup over `l` of
`(t l).towerHeight` enters at the deepest layer and the
offset is independent of `k`. -/
private theorem kSimSzudzikPackList_towerHeight_ge_propagate
    : ∀ {a k : ℕ} (t : Fin (k + 1) → ERMor1 a),
      ERMor1.natPair.towerHeight + 2 +
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun l => (t l).towerHeight) ≤
      (kSimSzudzikPackList t).towerHeight
  | _, 0,     t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      have hsup_eq :
          (Finset.univ : Finset (Fin 1)).sup
            (fun l => (t l).towerHeight) =
          (t 0).towerHeight := by
        rw [show (Finset.univ : Finset (Fin 1)) =
              {(0 : Fin 1)} from rfl]
        simp [Finset.sup_singleton]
      rw [hsup_eq]
      let G : Fin 2 → ℕ := fun i =>
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ => ERMor1.zeroN _).towerHeight
      have hG0 : G ⟨0, by omega⟩ = (t 0).towerHeight := rfl
      have hG_le_sup :
          (t 0).towerHeight ≤ Finset.univ.sup G := by
        rw [← hG0]
        exact Finset.le_sup (Finset.mem_univ _)
      let F : Fin 1 → ℕ := fun _ =>
        ERMor1.natPair.towerHeight + Finset.univ.sup G + 1
      have hF0_le_sup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      change ERMor1.natPair.towerHeight + 2 +
          (t 0).towerHeight ≤ 0 + Finset.univ.sup F + 1
      have hF_val : F 0 =
          ERMor1.natPair.towerHeight +
            Finset.univ.sup G + 1 := rfl
      omega
  | a, k + 1, t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      have hIH :=
        kSimSzudzikPackList_towerHeight_ge_propagate
          (a := a) (k := k) (fun j => t j.succ)
      let G : Fin 2 → ℕ := fun i =>
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ =>
              kSimSzudzikPackList (a := a) (k := k)
                (fun j => t j.succ)).towerHeight
      have hG1 :
          G ⟨1, by omega⟩ =
            (kSimSzudzikPackList (a := a) (k := k)
              (fun j => t j.succ)).towerHeight := rfl
      have hG_le_sup1 :
          (kSimSzudzikPackList (a := a) (k := k)
            (fun j => t j.succ)).towerHeight ≤
            Finset.univ.sup G := by
        rw [← hG1]; exact Finset.le_sup (Finset.mem_univ _)
      have hsup_le_sup_G :
          (Finset.univ : Finset (Fin (k + 2))).sup
              (fun l => (t l).towerHeight) ≤
            Finset.univ.sup G := by
        apply Finset.sup_le
        intro i _
        match i with
        | ⟨0, _⟩ =>
            have h0_eq :
                ((t (⟨0, by omega⟩ : Fin (k + 2)))
                  : ERMor1 a).towerHeight =
                G ⟨0, by omega⟩ := rfl
            rw [h0_eq]
            exact Finset.le_sup (Finset.mem_univ _)
        | ⟨n + 1, h⟩ =>
            have hn : n < k + 1 := by omega
            have hn_eq :
                ((t (⟨n + 1, h⟩ : Fin (k + 2)))
                  : ERMor1 a).towerHeight =
                ((t (⟨n, hn⟩ : Fin (k + 1)).succ)
                  : ERMor1 a).towerHeight := rfl
            rw [hn_eq]
            calc ((t (⟨n, hn⟩ : Fin (k + 1)).succ)
                    : ERMor1 a).towerHeight
                ≤ (Finset.univ : Finset (Fin (k + 1))).sup
                    (fun l => (t l.succ).towerHeight) :=
                  Finset.le_sup
                    (f := fun l : Fin (k + 1) =>
                      (t l.succ).towerHeight)
                    (Finset.mem_univ _)
              _ ≤ (kSimSzudzikPackList (a := a) (k := k)
                    (fun j => t j.succ)).towerHeight := by
                  omega
              _ ≤ Finset.univ.sup G := hG_le_sup1
      let F : Fin 1 → ℕ := fun _ =>
        ERMor1.natPair.towerHeight + Finset.univ.sup G + 1
      have hF0_le_sup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      have hF_val : F 0 =
          ERMor1.natPair.towerHeight +
            Finset.univ.sup G + 1 := rfl
      change ERMor1.natPair.towerHeight + 2 +
          Finset.univ.sup
            (fun l : Fin (k + 2) => (t l).towerHeight) ≤
          0 + Finset.univ.sup F + 1
      omega

/-- Structural propagation corollary for `kSimPackedBase`. -/
private theorem kSimPackedBase_towerHeight_ge_propagate
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a) :
    ERMor1.natPair.towerHeight + 2 +
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l => (h l).towerHeight) ≤
      (kSimPackedBase h).towerHeight := by
  unfold kSimPackedBase
  exact kSimSzudzikPackList_towerHeight_ge_propagate _

/-- Structural propagation corollary for `kSimPackedStep`. -/
private theorem kSimPackedStep_towerHeight_ge_propagate
    {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1.natPair.towerHeight + 2 +
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (ERMor1.comp (g l) kSimStepContext).towerHeight) ≤
      (kSimPackedStep g).towerHeight := by
  unfold kSimPackedStep
  exact kSimSzudzikPackList_towerHeight_ge_propagate _

/-- Strengthened structural lower bound on `kSimPackedBase`'s
tower height, parallel to the Step version. -/
private theorem kSimPackedBase_towerHeight_ge_succ_k
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a) :
    k + 2 ≤ (kSimPackedBase h).towerHeight := by
  unfold kSimPackedBase
  exact kSimSzudzikPackList_towerHeight_ge_succ_k _

/-- Reverse direction of `Fin.foldr_max_ge`: if every element
is bounded by `b`, the foldr-max is bounded by `b`. -/
private theorem Fin.foldr_max_le {n : ℕ}
    (f : Fin n → ℕ) (b : ℕ)
    (hb : ∀ j, f j ≤ b) :
    Fin.foldr n (fun i acc => max acc (f i)) 0 ≤ b := by
  induction n with
  | zero =>
      simp only [Fin.foldr_zero]
      exact Nat.zero_le _
  | succ n' ih =>
      simp only [Fin.foldr_succ]
      apply max_le
      · exact ih (fun l => f l.succ)
          (fun j => hb j.succ)
      · exact hb 0

/-- Combined absorption inequality: the log-sums on the
left-hand side of A.6's calc chain are bounded by the
sum-of-tower-heights expression on the right-hand side.
Combines:
- A.5.2.1 (`kToER_level0_towerHeight_ge_const`) to bound
  the level-0 shape constants by tower heights;
- the structural propagate lemmas
  (`kSimPackedStep_towerHeight_ge_propagate`,
  `kSimPackedBase_towerHeight_ge_propagate`) to absorb
  `sup_l (g_ER l).tH` and `sup_l (h_ER l).tH`;
- the structural `_ge_succ_k` lemmas
  (`kSimPackedStep_towerHeight_ge_succ_k`,
  `kSimPackedBase_towerHeight_ge_succ_k`) to absorb the
  `+k` slack from `Nat.log 2 E ≤ 2k + 5`;
- standard `Nat.log` bounds via `Nat.log_lt_of_lt_pow`. -/
private theorem stepTH_baseTH_dominates_arg
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0) :
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
        0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
        0) + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
        0
    let E : ℕ := 6 * 4 ^ (k + 1)
    let h_ER : Fin (k + 1) → ERMor1 a :=
      fun l => kToER (h_fam l)
        (Nat.le_succ_of_le (Nat.le_succ_of_le (h_h l)))
    let g_ER : Fin (k + 1) →
        ERMor1 (a + 1 + (k + 1)) :=
      fun l => kToER (g_fam l)
        (Nat.le_succ_of_le (Nat.le_succ_of_le (h_g l)))
    Nat.log 2 (CC + 1) +
        Nat.log 2 (KK + Nat.log 2 E + 4) ≤
      (kSimPackedStep g_ER).towerHeight +
        2 * (kSimPackedBase h_ER).towerHeight + 1 := by
  intro CC KK E h_ER g_ER
  set SG := (Finset.univ : Finset (Fin (k + 1))).sup
    (fun l => (g_ER l).towerHeight) with hSG_def
  set SH := (Finset.univ : Finset (Fin (k + 1))).sup
    (fun l => (h_ER l).towerHeight) with hSH_def
  set max_step_c :=
    Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1) 0
    with h_msc_def
  set max_step_k :=
    Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2) 0
    with h_msk_def
  have hCC_eq : CC = max_step_c + 2 * max_step_k + 1 := rfl
  have hKK_eq : KK = Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
      0 := rfl
  have h_msc_le : max_step_c ≤ 1 := by
    apply Fin.foldr_max_le
    intro l
    cases (KMor1.level0Shape (g_fam l) (h_g l)) with
    | const _ => simp [ConstantOrShiftedProj.linearBound]
    | shifted _ _ =>
        simp [ConstantOrShiftedProj.linearBound]
  have h_msk_le : max_step_k ≤ SG + 1 := by
    apply Fin.foldr_max_le
    intro l
    have h_const :
        ((g_fam l).level0Shape (h_g l)).linearBound.2 ≤
        (g_ER l).towerHeight + 1 :=
      kToER_level0_towerHeight_ge_const (g_fam l) (h_g l)
    have h_le : (g_ER l).towerHeight ≤ SG :=
      Finset.le_sup
        (f := fun j => (g_ER j).towerHeight)
        (Finset.mem_univ l)
    omega
  have h_KK_le : KK ≤ SH + 1 := by
    rw [hKK_eq]
    apply Fin.foldr_max_le
    intro l
    have h_const :
        ((h_fam l).level0Shape (h_h l)).linearBound.2 ≤
        (h_ER l).towerHeight + 1 :=
      kToER_level0_towerHeight_ge_const (h_fam l) (h_h l)
    have h_le : (h_ER l).towerHeight ≤ SH :=
      Finset.le_sup
        (f := fun j => (h_ER j).towerHeight)
        (Finset.mem_univ l)
    omega
  have h_log_E : Nat.log 2 E ≤ 2 * k + 5 := by
    change Nat.log 2 (6 * 4 ^ (k + 1)) ≤ 2 * k + 5
    have h6 : (6 : ℕ) ≤ 8 := by omega
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    have h_le : 6 * 4 ^ (k + 1) ≤ 2 ^ (2 * k + 5) := by
      calc 6 * 4 ^ (k + 1)
          ≤ 8 * 4 ^ (k + 1) := Nat.mul_le_mul_right _ h6
        _ = 2 ^ 3 * (2 ^ 2) ^ (k + 1) := by rw [h8, h4]
        _ = 2 ^ (2 * k + 5) := by
            rw [← Nat.pow_mul, ← Nat.pow_add]
            congr 1; ring
    calc Nat.log 2 (6 * 4 ^ (k + 1))
        ≤ Nat.log 2 (2 ^ (2 * k + 5)) := Nat.log_mono_right h_le
      _ = 2 * k + 5 := Nat.log_pow (by omega) _
  have h_CC_lt : CC + 1 < 2 ^ (SG + 3) := by
    have hSG_pow : SG + 1 ≤ 2 ^ SG := by
      have : SG < 2 ^ SG := Nat.lt_two_pow_self
      omega
    have h_pow_eq : (2 : ℕ) ^ (SG + 3) = 2 ^ SG * 8 := by
      rw [pow_add]; ring
    rw [h_pow_eq]
    have h_pow_ge : 2 ^ SG * 8 ≥ (SG + 1) * 8 := by
      exact Nat.mul_le_mul_right _ hSG_pow
    omega
  have h_log_CC : Nat.log 2 (CC + 1) ≤ SG + 2 := by
    have hlt :=
      Nat.log_lt_of_lt_pow (b := 2) (x := SG + 3) (y := CC + 1)
        (by omega) h_CC_lt
    omega
  have h_KK_term_lt : KK + Nat.log 2 E + 4 < 2 ^ (SH + k + 5) := by
    have hSH_pow : SH + 1 ≤ 2 ^ SH := by
      have : SH < 2 ^ SH := Nat.lt_two_pow_self
      omega
    have hk_pow : k + 1 ≤ 2 ^ k := by
      have : k < 2 ^ k := Nat.lt_two_pow_self
      omega
    have h_pow_eq :
        (2 : ℕ) ^ (SH + k + 5) = 2 ^ SH * 2 ^ k * 32 := by
      rw [show SH + k + 5 = SH + (k + 5) from by ring, pow_add,
        show k + 5 = k + 5 from rfl, pow_add]; ring
    have h_prod : (SH + 1) * (k + 1) ≤ 2 ^ SH * 2 ^ k :=
      Nat.mul_le_mul hSH_pow hk_pow
    have h_lin : SH + k + 1 ≤ (SH + 1) * (k + 1) := by
      have h_expand : (SH + 1) * (k + 1) = SH * k + SH + k + 1 := by
        ring
      omega
    rw [h_pow_eq]
    omega
  have h_log_KK : Nat.log 2 (KK + Nat.log 2 E + 4) ≤
      SH + k + 4 := by
    have hlt :=
      Nat.log_lt_of_lt_pow (b := 2) (x := SH + k + 5)
        (y := KK + Nat.log 2 E + 4)
        (by omega) h_KK_term_lt
    omega
  have h_step_propagate :=
    kSimPackedStep_towerHeight_ge_propagate g_ER
  have h_comp_ge : ∀ l : Fin (k + 1),
      (g_ER l).towerHeight + 1 ≤
      (ERMor1.comp (g_ER l) kSimStepContext).towerHeight := by
    intro l
    simp only [ERMor1.towerHeight]
    omega
  set sup_comp :=
    (Finset.univ : Finset (Fin (k + 1))).sup
      (fun l =>
        (ERMor1.comp (g_ER l) kSimStepContext).towerHeight)
    with h_sup_comp_def
  have h_sup_comp_ge_one : 1 ≤ sup_comp := by
    have h_le_sup :
        (ERMor1.comp (g_ER 0) kSimStepContext).towerHeight
          ≤ sup_comp :=
      Finset.le_sup
        (f := fun l =>
          (ERMor1.comp (g_ER l) kSimStepContext).towerHeight)
        (Finset.mem_univ 0)
    have hc := h_comp_ge 0
    omega
  have h_each_le :
      ∀ l : Fin (k + 1), (g_ER l).towerHeight ≤ sup_comp - 1 := by
    intro l
    have h_le_sup :
        (ERMor1.comp (g_ER l) kSimStepContext).towerHeight
          ≤ sup_comp :=
      Finset.le_sup
        (f := fun l =>
          (ERMor1.comp (g_ER l) kSimStepContext).towerHeight)
        (Finset.mem_univ l)
    have hc := h_comp_ge l
    omega
  have h_SG_le : SG ≤ sup_comp - 1 := by
    rw [hSG_def]
    apply Finset.sup_le
    intro l _
    exact h_each_le l
  have h_sup_comp_ge : SG + 1 ≤ sup_comp := by omega
  have h_step_ge_SG : (kSimPackedStep g_ER).towerHeight ≥
      ERMor1.natPair.towerHeight + 3 + SG := by
    omega
  have h_base_ge_k : (kSimPackedBase h_ER).towerHeight ≥
      k + 2 := kSimPackedBase_towerHeight_ge_succ_k h_ER
  have h_base_ge_SH : (kSimPackedBase h_ER).towerHeight ≥
      ERMor1.natPair.towerHeight + 2 + SH :=
    kSimPackedBase_towerHeight_ge_propagate h_ER
  have h_2base : 2 * (kSimPackedBase h_ER).towerHeight ≥
      SH + ERMor1.natPair.towerHeight + k + 4 := by
    -- 2 * max(a, b) ≥ a + b: split via two copies of baseTH.
    omega
  -- LHS bounds in terms of CC and KK (use h_log_CC, h_log_KK).
  -- RHS bounds via h_step_ge_SG, h_2base.
  omega

/-- Uniform linear bound on `KMor1.simrecVec` for level-0
families: each component at iteration `n ≤ S` is bounded
by `CC * S + KK`, with `CC` and `KK` extracted from the
children's `level0Shape.linearBound` via foldr-max. -/
private theorem KMor1.simrecVec_uniform_linear_bound
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (params : Fin a → ℕ)
    (S : ℕ)
    (h_params : ∀ j, params j ≤ S)
    (n : ℕ) (h_n : n ≤ S) :
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
        0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
        0) + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
        0
    ∀ l, KMor1.simrecVec h_fam g_fam params n l ≤
          CC * S + KK := by
  intro CC KK l
  set max_base_const := Fin.foldr (k + 1) (fun l acc =>
    max acc
      (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2) 0
    with h_mbc_def
  set max_step_c := Fin.foldr (k + 1) (fun l acc =>
    max acc
      (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1) 0
    with h_msc_def
  set max_step_k := Fin.foldr (k + 1) (fun l acc =>
    max acc
      (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2) 0
    with h_msk_def
  have hbm : ∀ j,
      (KMor1.level0Shape (h_fam j) (h_h j)).linearBound.2
        ≤ max_base_const := fun j =>
    Fin.foldr_max_ge
      (fun l =>
        (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
      j
  have hsc : ∀ j,
      (KMor1.level0Shape (g_fam j) (h_g j)).linearBound.1
        ≤ max_step_c := fun j =>
    Fin.foldr_max_ge
      (fun l =>
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
      j
  have hsk : ∀ j,
      (KMor1.level0Shape (g_fam j) (h_g j)).linearBound.2
        ≤ max_step_k := fun j =>
    Fin.foldr_max_ge
      (fun l =>
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
      j
  have haux := KMor1.simrecVec_linear_bound_aux
    h_fam g_fam h_h h_g params S h_params
    max_base_const hbm
    max_step_c max_step_k hsc hsk
    n h_n l
  have hck : max_step_k * n ≤ max_step_k * S :=
    Nat.mul_le_mul_left _ h_n
  change KMor1.simrecVec h_fam g_fam params n l
      ≤ (max_step_c + 2 * max_step_k + 1) * S
          + max_base_const
  calc KMor1.simrecVec h_fam g_fam params n l
      ≤ (max_step_c + max_step_k + 1) * S
          + max_base_const + max_step_k * n := haux
    _ ≤ (max_step_c + max_step_k + 1) * S
          + max_base_const + max_step_k * S := by omega
    _ = (max_step_c + 2 * max_step_k + 1) * S
          + max_base_const := by ring

/-- Polynomial bound on the `seqPack` of the (k+1)-tuple
of `simrecVec` components at iteration `n ≤ S`, via
`Nat.seqPack_le_seqPackBound` applied to the per-component
linear bound. -/
private theorem KMor1.simrecVec_seqPack_le_pow
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (params : Fin a → ℕ)
    (S : ℕ)
    (h_params : ∀ j, params j ≤ S)
    (n : ℕ) (h_n : n ≤ S) :
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
        0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
        0) + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
        0
    Nat.seqPack
      ((List.finRange (k + 1)).map
        (fun l =>
          KMor1.simrecVec h_fam g_fam params n l)) ≤
      (CC * S + KK + 2) ^ (6 * 4 ^ (k + 1)) := by
  intro CC KK
  have h_each := KMor1.simrecVec_uniform_linear_bound
    h_fam g_fam h_h h_g params S h_params n h_n
  have h_each_in :
      ∀ v ∈ ((List.finRange (k + 1)).map
              (fun l =>
                KMor1.simrecVec h_fam g_fam params n l)),
        v ≤ ((CC * S + KK) + 1) ^ 1 := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨l, _, hvl⟩
    rw [← hvl, pow_one]
    have hl := h_each l
    exact le_trans hl (Nat.le_succ _)
  have hlen :
      ((List.finRange (k + 1)).map
        (fun l =>
          KMor1.simrecVec h_fam g_fam params n l)).length
        ≤ k + 1 := by simp
  have h_pack :=
    Nat.seqPack_le_seqPackBound
      ((List.finRange (k + 1)).map
        (fun l =>
          KMor1.simrecVec h_fam g_fam params n l))
      k 1 (CC * S + KK) hlen h_each_in
  unfold Nat.seqPackBound at h_pack
  have hexp_eq : (1 + 5) * 4 ^ (k + 1) = 6 * 4 ^ (k + 1) := by
    ring
  rw [hexp_eq] at h_pack
  exact h_pack

/-- Level-1 simrec dominance: the iterated packed value of
`kSimPackedStep` over `kSimPackedBase` is dominated by
`kSimTowerBound`'s closed-form tower at every iteration
counter and parameter context, when both base and step
families consist of level-0 K^sim terms.

The proof composes A.2 (packed-iteration matches seqPack),
A.3 (seqPack ≤ pow), A.4 (pow ≤ tower 2), A.5.1
(tower 2 ≤ tower 3 with log shifts), and A.5.2.2
(stepTH + 2*baseTH + 1 dominates the log-sum). -/
private theorem kSimTowerBound_dominates_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (j : ℕ) (params : Fin a → ℕ) :
    Nat.rec
      ((kSimPackedBase
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le (h_h l))))).interp params)
      (fun i prev =>
        (kSimPackedStep
          (fun l => kToER (g_fam l)
            (Nat.le_succ_of_le
              (Nat.le_succ_of_le (h_g l))))).interp
        (Fin.cons i (Fin.cons prev params)))
      j ≤
      (kSimTowerBound
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le (h_h l))))
        (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le (h_g l))))).interp
        (Fin.cons j params) := by
  set h_ER : Fin (k + 1) → ERMor1 a :=
    fun l => kToER (h_fam l)
      (Nat.le_succ_of_le (Nat.le_succ_of_le (h_h l)))
    with h_ER_def
  set g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
    fun l => kToER (g_fam l)
      (Nat.le_succ_of_le (Nat.le_succ_of_le (h_g l)))
    with g_ER_def
  rw [packed_iteration_matches_simrecVec
        h_fam g_fam h_h h_g params j]
  set sumCtx :=
    (Finset.univ : Finset (Fin (a + 1))).sum
      (Fin.cons j params)
    with hsumCtx_def
  set S := sumCtx with hS_def
  set CC :=
    (Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
      0) +
    2 * (Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
      0) + 1
    with hCC_def
  set KK :=
    Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
      0
    with hKK_def
  set E : ℕ := 6 * 4 ^ (k + 1) with hE_def
  have h_params_le_S : ∀ i, params i ≤ S := by
    intro i
    change params i ≤ Finset.univ.sum (Fin.cons j params)
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h_le : params i ≤ ∑ k, params k :=
      Finset.single_le_sum
        (f := params) (s := Finset.univ)
        (hf := fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  have h_j_le_S : j ≤ S := by
    change j ≤ Finset.univ.sum (Fin.cons j params)
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_zero]
  have h_pack_le := KMor1.simrecVec_seqPack_le_pow
    h_fam g_fam h_h h_g params S h_params_le_S j h_j_le_S
  simp only at h_pack_le
  have h_tower2 :=
    Nat.pow_le_tower_two_with_shift CC S KK E
  have h_tower3 :
      GebLean.tower 2 (CC * S + KK + Nat.log 2 E + 3) ≤
      GebLean.tower 3 (S + Nat.log 2 (CC + 1)
        + Nat.log 2 (KK + Nat.log 2 E + 4) + 2) := by
    have h_eq : CC * S + KK + Nat.log 2 E + 3 =
                CC * S + (KK + Nat.log 2 E + 3) := by ring
    rw [h_eq]
    have h_apply :=
      _root_.Nat.tower_two_le_tower_three_linear CC
        (KK + Nat.log 2 E + 3) S
    have h_arg_eq : Nat.log 2 (KK + Nat.log 2 E + 3 + 1) =
        Nat.log 2 (KK + Nat.log 2 E + 4) := by
      congr 1
    rw [h_arg_eq] at h_apply
    exact h_apply
  have h_combined :
      Nat.log 2 (CC + 1) +
          Nat.log 2 (KK + Nat.log 2 E + 4) ≤
        (kSimPackedStep g_ER).towerHeight +
          2 * (kSimPackedBase h_ER).towerHeight + 1 :=
    stepTH_baseTH_dominates_arg h_fam g_fam h_h h_g
  have h_step_ge_2 : (kSimPackedStep g_ER).towerHeight ≥ k + 2 :=
    kSimPackedStep_towerHeight_ge_succ_k g_ER
  rw [kSimTowerBound_interp]
  rw [ERMor1.interp_sumCtxER]
  -- Final calc chain.
  calc Nat.seqPack _
      ≤ (CC * S + KK + 2) ^ E := h_pack_le
    _ ≤ GebLean.tower 2 (CC * S + KK + 1 + Nat.log 2 E + 2)
        := h_tower2
    _ = GebLean.tower 2 (CC * S + KK + Nat.log 2 E + 3) := by
        congr 1; ring
    _ ≤ GebLean.tower 3 (S + Nat.log 2 (CC + 1)
          + Nat.log 2 (KK + Nat.log 2 E + 4) + 2) :=
        h_tower3
    _ ≤ GebLean.tower ((kSimPackedStep g_ER).towerHeight + 1)
          (S + Nat.log 2 (CC + 1)
            + Nat.log 2 (KK + Nat.log 2 E + 4) + 2) :=
        GebLean.tower_mono_left (by omega) _
    _ ≤ GebLean.tower ((kSimPackedStep g_ER).towerHeight + 1)
          ((kSimPackedStep g_ER).towerHeight + 1
            + 2 * (kSimPackedBase h_ER).towerHeight
            + 2 * (Finset.univ : Finset (Fin (a + 1))).sum
                (Fin.cons j params)
            + 2) := by
        apply GebLean.tower_mono_right
        omega

/-- Interp preservation for level-1 K^sim: at level ≤ 1,
`kToER` produces an ER term whose interp equals the K^sim
interp at every context.  Proved by structural recursion;
the simrec case discharges the dominance hypothesis of
`boundedRec_eq_natRec_of_bounded` via
`kSimTowerBound_dominates_level_one`. -/
private theorem kToER_interp_level_one :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
      (ctx : Fin a → ℕ),
      (kToER f
        (Nat.le_succ_of_le h)).interp ctx = f.interp ctx
  | _, .zero,         _, _   => by
      simp [kToER, KMor1.interp_zero, ERMor1.interp_zeroN]
  | _, .succ,         _, _   => by
      simp [kToER, KMor1.interp_succ, ERMor1.interp_succ]
  | _, .proj _,       _, _   => by
      simp [kToER, KMor1.interp_proj, ERMor1.interp_proj]
  | _, .comp f gs,    h, ctx => by
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 1 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 1 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      have h_inner :
          (fun i => (kToER (gs i)
              (Nat.le_succ_of_le (hgs i))).interp ctx)
            = (fun i => (gs i).interp ctx) := by
        funext i
        exact kToER_interp_level_one (gs i) (hgs i) ctx
      simp only [kToER, ERMor1.interp_comp,
        KMor1.interp_comp]
      rw [h_inner]
      exact kToER_interp_level_one f hf
        (fun i => (gs i).interp ctx)
  | _, .raise f,      h, ctx => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      simp only [kToER, KMor1.interp_raise]
      exact kToER_interp_level_zero f hf ctx
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp, ctx =>
      by
        have h_h : ∀ l, (h_fam l).level ≤ 0 := fun l => by
          unfold KMor1.level at hyp
          have hsup_le : Finset.univ.sup
              (fun j => (h_fam j).level) ≤ 0 := by omega
          exact le_trans
            (Finset.le_sup
              (f := fun j => (h_fam j).level)
              (Finset.mem_univ l))
            hsup_le
        have h_g : ∀ l, (g_fam l).level ≤ 0 := fun l => by
          unfold KMor1.level at hyp
          have hsup_le : Finset.univ.sup
              (fun j => (g_fam j).level) ≤ 0 := by omega
          exact le_trans
            (Finset.le_sup
              (f := fun j => (g_fam j).level)
              (Finset.mem_univ l))
            hsup_le
        set h_ER : Fin (k + 1) → ERMor1 a :=
          fun l => kToER (h_fam l)
            (Nat.le_succ_of_le (Nat.le_succ_of_le (h_h l)))
          with h_ER_def
        set g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
          fun l => kToER (g_fam l)
            (Nat.le_succ_of_le (Nat.le_succ_of_le (h_g l)))
          with g_ER_def
        set recur : ERMor1 (a + 1) :=
          ERMor1.boundedRec
            (kSimPackedBase h_ER)
            (kSimPackedStep g_ER)
            (kSimTowerBound h_ER g_ER)
          with recur_def
        -- Step 1: simplify LHS to the unpack-at-packed form.
        change ((kSimSzudzikUnpackAt a i.val).comp
            (fun j : Fin (a + 1) =>
              if h_eq : j.val = 0 then recur
              else ERMor1.proj (k := a + 1)
                ⟨j.val, by
                  have := j.isLt; omega⟩)).interp ctx = _
        rw [ERMor1.interp_comp]
        -- Step 2: rewrite the inner family as
        -- `Fin.cons (recur.interp ctx) (Fin.tail ctx)`.
        have h_inner :
            (fun j : Fin (a + 1) =>
              (if h_eq : j.val = 0 then recur
              else ERMor1.proj (k := a + 1)
                ⟨j.val, by
                  have := j.isLt; omega⟩).interp ctx) =
            Fin.cons (recur.interp ctx) (Fin.tail ctx) := by
          funext j
          by_cases hj : j.val = 0
          · simp only [hj, dif_pos]
            have hj_eq : j = (0 : Fin (a + 1)) :=
              Fin.ext hj
            rw [hj_eq, Fin.cons_zero]
          · simp only [hj, dif_neg, not_false_eq_true]
            rw [ERMor1.interp_proj]
            obtain ⟨j', rfl⟩ : ∃ j' : Fin a,
                j = Fin.succ j' := by
              refine ⟨⟨j.val - 1, by
                have := j.isLt; omega⟩, ?_⟩
              apply Fin.ext
              change j.val = (j.val - 1) + 1
              omega
            rw [Fin.cons_succ, Fin.tail_def]
        rw [h_inner]
        -- Step 3: apply unpack-at-seqAt.
        rw [kSimSzudzikUnpackAt_interp_eq_seqAt
          (a := a) (i := i.val) (packed := recur.interp ctx)
          (ctx := Fin.tail ctx)]
        -- Step 4: rewrite recur.interp via Fin.cons_self_tail
        -- and apply boundedRec_eq_natRec_of_bounded.
        have hctx_eq :
            ctx = Fin.cons (ctx 0) (Fin.tail ctx) := by
          rw [Fin.cons_self_tail]
        have h_recur_eq :
            recur.interp ctx =
            Nat.rec ((kSimPackedBase h_ER).interp
                (Fin.tail ctx))
              (fun j prev =>
                (kSimPackedStep g_ER).interp
                  (Fin.cons j (Fin.cons prev
                    (Fin.tail ctx))))
              (ctx 0) := by
          rw [recur_def]
          conv_lhs => rw [hctx_eq]
          apply ERMor1.boundedRec_eq_natRec_of_bounded
          · intro j h_j_le
            rw [recur_def] at *
            -- Use kSimTowerBound_dominates_level_one,
            -- specialized to this j.
            have := kSimTowerBound_dominates_level_one
              h_fam g_fam h_h h_g j (Fin.tail ctx)
            change Nat.rec _ _ _ ≤
              (kSimTowerBound h_ER g_ER).interp _
            exact this
          · intro j h_j_le
            -- Monotonicity from kSimTowerBound_mono_counter.
            exact kSimTowerBound_mono_counter
              h_ER g_ER j (ctx 0) (Fin.tail ctx) h_j_le
        rw [h_recur_eq]
        -- Step 5: apply packed_iteration_matches_simrecVec.
        rw [packed_iteration_matches_simrecVec
          h_fam g_fam h_h h_g (Fin.tail ctx) (ctx 0)]
        -- Step 6: apply Nat.seqAt_seqPack.
        have hlen :
            ((List.finRange (k + 1)).map
              (fun l =>
                KMor1.simrecVec h_fam g_fam
                  (Fin.tail ctx) (ctx 0) l)).length
              = k + 1 := by simp
        rw [Nat.seqAt_seqPack
          (xs := (List.finRange (k + 1)).map
            (fun l =>
              KMor1.simrecVec h_fam g_fam
                (Fin.tail ctx) (ctx 0) l))
          (i := i.val)
          (h := by rw [hlen]; exact i.isLt)]
        -- Step 7: rewrite RHS via KMor1.interp_simrec.
        rw [KMor1.interp_simrec]
        -- Final: relate Fin.tail ctx and ctx 0.
        simp [Fin.tail_def]

/-- Linear bound on level-1 K^sim's kToER image.  Direct
composition of `kToER_interp_level_one` and
`KMor1.linearBound_dominates`. -/
theorem kToER_linearBound_dominates_level_one
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
    (ctx : Fin a → ℕ) :
    (kToER f (Nat.le_succ_of_le h)).interp ctx ≤
      (KMor1.linearBound f h).1 *
        (Finset.univ : Finset (Fin a)).sup ctx +
      (KMor1.linearBound f h).2 := by
  rw [kToER_interp_level_one f h ctx]
  exact KMor1.linearBound_dominates f h ctx

end GebLean
