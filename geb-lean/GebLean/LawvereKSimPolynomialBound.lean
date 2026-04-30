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
  | _, 0,     _ => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      omega
  | _, _ + 1, _ => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      omega

/-- Structural lower bound on `kSimPackedStep`'s tower
height. -/
private theorem kSimPackedStep_towerHeight_ge_two
    {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    2 ≤ (kSimPackedStep g).towerHeight := by
  unfold kSimPackedStep
  exact kSimSzudzikPackList_towerHeight_ge_two _

end GebLean
