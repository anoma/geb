import GebLean.LawvereERKSim.Compiler
import GebLean.LawvereERKSim.Top
import GebLean.Utilities.KArith
import GebLean.Utilities.Tower
import GebLean.LawvereKSim
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Runtime bound for `compileER`

This module realises Tourlakis 2018 Corollary 0.1.0.27 specialised
to the ER → URM compiler of T2: every ER morphism's compile-time
URM runtime is dominated by a `tower r (Fin.maxOfNat _ v + offset)`
expression, for explicit `(r, offset) : ℕ × ℕ` computed by ER
structural recursion. The result is consumed downstream by the
`boundExprK` construction and the `erToK` assembly.

## Main definitions

- `boundExprKParams` : `ERMor1 a → ℕ × ℕ` — the per-ER-constructor
  recipe returning the tower height `mu_e` and offset `offset_e`.
- `boundExprK` : `ERMor1 a → KMor1 a` — the level-≤ 2 `K`-morphism
  computing the runtime bound `tower mu_e (Fin.maxOfNat _ v + offset_e)`
  at every context `v`.

## Main statements

- `boundExprKParams_dominates` — joint runtime+value bound:
  `compileER_runtime e v ≤ tower mu_e (Fin.maxOfNat _ v + offset_e)`
  and `e.interp v ≤ tower mu_e (Fin.maxOfNat _ v + offset_e)`.
- `boundExprK_level` — `(boundExprK e).level ≤ 2`.
- `boundExprK_interp` — `(boundExprK e).interp v` equals
  `tower (boundExprKParams e).1 (Fin.maxOfNat _ v + (boundExprKParams e).2)`.
- `boundExprK_dominates` — `compileER_runtime e v ≤ (boundExprK e).interp v`.

## References

- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.27, §0.1.0.42,
  §0.1.0.44.
- Spec: `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`.

## Tags

ertok, runtime-bound, tourlakis, tower
-/

namespace GebLean

/-- Per-ER-constructor recipe returning the tower height `mu_e` and
offset `offset_e` jointly bounding both the URM runtime of
`compileER e` and the ER value `e.interp v` by
`tower mu_e (Fin.maxOfNat _ v + offset_e)`. The constants
follow spec §4.2; the `Fin.maxOfNat`-folds make each composite case
constructive (no `Finset.sup`). -/
def boundExprKParams : {a : ℕ} → ERMor1 a → ℕ × ℕ
  | _, .zero    => (0, 3)
  | _, .succ    => (2, 16)
  | _, .proj _  => (2, 16)
  | _, .sub     => (2, 24)
  | a, .comp (k := k) f gs =>
      let p_f  := boundExprKParams f
      let mu_g := Fin.maxOfNat k
                    (fun i => (boundExprKParams (gs i)).1)
      let o_g  := Fin.maxOfNat k
                    (fun i => (boundExprKParams (gs i)).2)
      (p_f.1 + mu_g + 6, p_f.2 + o_g + 4 * a + k + 8)
  | _, .bsum (k := k) f  =>
      let p_f := boundExprKParams f
      (p_f.1 + 6, p_f.2 + k + LawvereERKSim.compileER_numRegs f + 32)
  | _, .bprod (k := k) f =>
      let p_f := boundExprKParams f
      (p_f.1 + 9, p_f.2 + k + LawvereERKSim.compileER_numRegs f + 44)

/-- Tower-2 absorbs any `c * m` with `c ≤ m`, when `m ≥ 2`.
A `c · m ≤ m · m = m · tower 0 m ≤ tower 2 m` chain, repeatedly
applied across atom cases. -/
private theorem cm_le_tower_two {c m : ℕ} (h_c : c ≤ m) (h_m : 2 ≤ m) :
    c * m ≤ tower 2 m := by
  calc c * m
      ≤ m * m := Nat.mul_le_mul_right m h_c
    _ = m * tower 0 m := by rw [tower_zero]
    _ ≤ tower 2 m := mul_tower_le_tower_add_two h_m

/-- A `(· + ·) 0`-fold of a list mapped by `g` is dominated by `l.length * M`
whenever each summand `g x` is `≤ M`. Variant of `List.sum_le_card_nsmul`
restricted to the `foldl`-form used by `compileER_runtime`. -/
private theorem foldl_map_le_length_mul_aux {α : Type} (g : α → ℕ) (M : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, g x ≤ M) →
      ∀ (acc : ℕ), (l.map g).foldl (· + ·) acc ≤ acc + l.length * M
  | [], _, acc => by simp
  | hd :: tl, h, acc => by
      have h_hd : g hd ≤ M := h hd (List.mem_cons_self)
      have h_tl : ∀ x ∈ tl, g x ≤ M :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hrec := foldl_map_le_length_mul_aux g M tl h_tl (acc + g hd)
      simp only [List.map_cons, List.foldl_cons, List.length_cons]
      have h_step : acc + g hd + tl.length * M
          ≤ acc + (tl.length + 1) * M := by
        have := h_hd
        rw [Nat.add_mul, Nat.one_mul]
        omega
      exact Nat.le_trans hrec h_step

private theorem foldl_map_le_length_mul {α : Type} (l : List α) (g : α → ℕ)
    (M : ℕ) (h : ∀ x ∈ l, g x ≤ M) :
    ((l.map g).foldl (· + ·) 0) ≤ l.length * M := by
  simpa using foldl_map_le_length_mul_aux g M l h 0

/-- Specialised list-sum bound for the `List.finRange k`-driven folds in the
`comp` case of `compileER_runtime`: the fold of `g` over `List.finRange k`
is bounded by `k · Fin.maxOfNat k g`. -/
private theorem foldl_finRange_le_mul_maxOfNat {k : ℕ} (g : Fin k → ℕ) :
    (((List.finRange k).map g).foldl (· + ·) 0) ≤ k * Fin.maxOfNat k g := by
  have h_each : ∀ i ∈ List.finRange k, g i ≤ Fin.maxOfNat k g := by
    intro i _; exact Fin.le_maxOfNat g i
  have := foldl_map_le_length_mul (List.finRange k) g (Fin.maxOfNat k g) h_each
  simpa [List.length_finRange] using this

/-- `Fin.maxOfNat` is monotone in its argument. -/
private theorem Fin.maxOfNat_mono {n : ℕ} {f g : Fin n → ℕ}
    (h : ∀ i, f i ≤ g i) : Fin.maxOfNat n f ≤ Fin.maxOfNat n g := by
  refine Fin.maxOfNat_le (fun j => ?_)
  exact (h j).trans (Fin.le_maxOfNat g j)

/-- Bounded sum is dominated by bound times max entry. Constructive,
no `Classical.choice`. -/
private theorem natBSum_le_mul_max (b : ℕ) (f : ℕ → ℕ) (M : ℕ)
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

/-- Bounded product is dominated by max entry raised to bound. Constructive. -/
private theorem natBProd_le_pow_max (b : ℕ) (f : ℕ → ℕ) (M : ℕ)
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

/-- `tower k m ≥ 2` whenever `m ≥ 2`. -/
private theorem two_le_tower {k m : ℕ} (hm : 2 ≤ m) : 2 ≤ tower k m :=
  hm.trans (self_le_tower k m)

/-- Pointwise monotonicity for `(l.map _).foldl (· + ·) acc`. -/
private theorem foldl_add_mono_aux {α : Type} (f g : α → ℕ) :
    ∀ (l : List α) (acc₁ acc₂ : ℕ),
      acc₁ ≤ acc₂ → (∀ x ∈ l, f x ≤ g x) →
        (l.map f).foldl (· + ·) acc₁
          ≤ (l.map g).foldl (· + ·) acc₂
  | [], _, _, h_acc, _ => by simpa
  | hd :: tl, acc₁, acc₂, h_acc, h => by
      have h_hd : f hd ≤ g hd := h hd (List.mem_cons_self)
      have h_tl : ∀ x ∈ tl, f x ≤ g x :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, List.foldl_cons]
      exact foldl_add_mono_aux f g tl (acc₁ + f hd) (acc₂ + g hd)
              (Nat.add_le_add h_acc h_hd) h_tl

private theorem foldl_add_mono {α : Type} {f g : α → ℕ} (l : List α)
    (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).foldl (· + ·) 0 ≤ (l.map g).foldl (· + ·) 0 :=
  foldl_add_mono_aux f g l 0 0 (Nat.le_refl _) h

/-- Distribute a `(· + ·) 0`-fold of a pointwise sum into a sum of two
folds. Routes through `List.sum_map_add` via the
`foldl (·+·) 0 = sum` equality. -/
private theorem foldl_add_map_split {α : Type} (l : List α) (f g : α → ℕ) :
    ((l.map (fun x => f x + g x)).foldl (· + ·) 0)
      = ((l.map f).foldl (· + ·) 0)
        + ((l.map g).foldl (· + ·) 0) := by
  rw [← List.sum_eq_foldl, ← List.sum_eq_foldl, ← List.sum_eq_foldl,
      List.sum_map_add]

/-- Structural invariant on the recipe: the tower height `mu_e`
returned by `boundExprKParams` is either at least `2`, or the
expression's arity is `0`. Used in the `comp` chain to
discharge the `mu_f ≥ 2` invariant: when `mu_f = 0`, the
arity-zero conclusion forces `k = 0`, which collapses the
`k`-fold glue sum to `0`. -/
private theorem boundExprKParams_mu_ge_two_or_arity_zero :
    ∀ {a : ℕ} (e : ERMor1 a),
      2 ≤ (boundExprKParams e).1 ∨ a = 0 := by
  intro a e
  induction e with
  | zero    => right; rfl
  | succ    => left; simp [boundExprKParams]
  | proj _  => left; simp [boundExprKParams]
  | sub     => left; simp [boundExprKParams]
  | comp _ _ _ _ =>
      left
      simp only [boundExprKParams]
      omega
  | bsum _ _  =>
      left
      simp only [boundExprKParams]
      omega
  | bprod _ _ =>
      left
      simp only [boundExprKParams]
      omega

-- AXIOM_ALLOW: Classical.choice
-- (bsum and bprod cases route through `Fin.cons`/`Fin.tail` simp
-- normalisation which transitively pulls in `Fin.lastCases_castSucc`;
-- accepted exception per `.claude/rules/lean-coding.md` § Accepted
-- exceptions, spec §11.)
/-- Joint runtime+value bound: for every ER morphism `e`, both
`compileER_runtime e v` (the URM steps `compileER` runs for) and
`e.interp v` (the ER value) are dominated by
`tower mu_e (Fin.maxOfNat _ v + offset_e)`, where
`(mu_e, offset_e) = boundExprKParams e`. Proof by structural
induction on `e`. Transcribes Tourlakis 2018 Cor. 0.1.0.27 to the
T2 compiler surface. -/
theorem boundExprKParams_dominates {a : ℕ} (e : ERMor1 a) :
    ∀ (v : Fin a → ℕ),
      LawvereERKSim.compileER_runtime e v ≤
          tower (boundExprKParams e).1
                (Fin.maxOfNat _ v + (boundExprKParams e).2) ∧
      e.interp v ≤
          tower (boundExprKParams e).1
                (Fin.maxOfNat _ v + (boundExprKParams e).2) := by
  induction e with
  | zero    =>
      intro v
      -- params = (0, 3); bound = tower 0 (max + 3) = max + 3.
      -- runtime = 3, interp = 0.
      simp only [LawvereERKSim.compileER_runtime, ERMor1.interp_zero,
        boundExprKParams, tower_zero]
      omega
  | succ    =>
      intro v
      simp only [LawvereERKSim.compileER_runtime, ERMor1.interp_succ,
        boundExprKParams]
      have h_v0 : v 0 ≤ Fin.maxOfNat _ v :=
        Fin.le_maxOfNat v ⟨0, by decide⟩
      have h_m_ge : 2 ≤ Fin.maxOfNat _ v + 16 := by omega
      have h_self : Fin.maxOfNat _ v + 16 ≤ tower 2 (Fin.maxOfNat _ v + 16) :=
        self_le_tower 2 _
      refine ⟨?_, ?_⟩
      · -- 12 + 10·v 0 ≤ 11 · m ≤ m·m ≤ tower 2 m, m = max + 16 ≥ 16.
        have h_lin : 12 + 10 * v 0 ≤ 11 * (Fin.maxOfNat _ v + 16) := by omega
        exact h_lin.trans (cm_le_tower_two (by omega : 11 ≤ _) h_m_ge)
      · -- v 0 + 1 ≤ m ≤ tower 2 m
        exact (by omega : v 0 + 1 ≤ Fin.maxOfNat _ v + 16).trans h_self
  | proj i  =>
      intro v
      simp only [LawvereERKSim.compileER_runtime, ERMor1.interp_proj,
        boundExprKParams]
      have h_vi : v i ≤ Fin.maxOfNat _ v := Fin.le_maxOfNat v i
      have h_m_ge : 2 ≤ Fin.maxOfNat _ v + 16 := by omega
      have h_self : Fin.maxOfNat _ v + 16 ≤ tower 2 (Fin.maxOfNat _ v + 16) :=
        self_le_tower 2 _
      refine ⟨?_, ?_⟩
      · have h_lin : 11 + 10 * v i ≤ 11 * (Fin.maxOfNat _ v + 16) := by omega
        exact h_lin.trans (cm_le_tower_two (by omega : 11 ≤ _) h_m_ge)
      · exact h_vi.trans
          ((by omega : Fin.maxOfNat _ v ≤ Fin.maxOfNat _ v + 16).trans h_self)
  | sub     =>
      intro v
      simp only [LawvereERKSim.compileER_runtime, ERMor1.interp_sub,
        boundExprKParams]
      have h_v0 : v 0 ≤ Fin.maxOfNat _ v :=
        Fin.le_maxOfNat v ⟨0, by decide⟩
      have h_v1 : v 1 ≤ Fin.maxOfNat _ v :=
        Fin.le_maxOfNat v ⟨1, by decide⟩
      have h_m_ge : 2 ≤ Fin.maxOfNat _ v + 24 := by omega
      have h_self : Fin.maxOfNat _ v + 24 ≤ tower 2 (Fin.maxOfNat _ v + 24) :=
        self_le_tower 2 _
      refine ⟨?_, ?_⟩
      · -- 20 + 10·v 0 + 10·v 1 ≤ 21·m ≤ m·m ≤ tower 2 m, m ≥ 24.
        have h_lin :
            20 + 10 * v 0 + 10 * v 1 ≤ 21 * (Fin.maxOfNat _ v + 24) := by omega
        exact h_lin.trans (cm_le_tower_two (by omega : 21 ≤ _) h_m_ge)
      · -- v 0 ∸ v 1 ≤ v 0 ≤ m ≤ tower 2 m
        have h_sub_le : v 0 - v 1 ≤ v 0 := Nat.sub_le _ _
        exact h_sub_le.trans
          (h_v0.trans
            ((by omega : Fin.maxOfNat _ v ≤ Fin.maxOfNat _ v + 24).trans h_self))
  | comp f gs ih_f ih_gs =>
      rename_i k_inner n_outer
      intro v
      simp only [LawvereERKSim.compileER_runtime, ERMor1.interp_comp,
        boundExprKParams]
      -- Abbreviations matching spec §4.2 narrative.
      set muF : ℕ := (boundExprKParams f).1 with hmuF
      set muG : ℕ := Fin.maxOfNat k_inner
                        (fun i => (boundExprKParams (gs i)).1)
        with hmuG
      set offF : ℕ := (boundExprKParams f).2 with hoffF
      set offG : ℕ := Fin.maxOfNat k_inner
                        (fun i => (boundExprKParams (gs i)).2)
        with hoffG
      set m : ℕ := Fin.maxOfNat n_outer v
        + (offF + offG + 4 * n_outer + k_inner + 8) with hm
      -- Numeric facts on `m`.
      have h_m_ge_8 : 8 ≤ m := by rw [hm]; omega
      have h_m_ge_2 : 2 ≤ m := by omega
      have h_offF_le_m : offF ≤ m := by rw [hm]; omega
      have h_offG_le_m : offG ≤ m := by rw [hm]; omega
      have h_k_le_m : k_inner ≤ m := by rw [hm]; omega
      have h_n_le_m : n_outer ≤ m := by rw [hm]; omega
      have h_4n_le_m : 4 * n_outer ≤ m := by rw [hm]; omega
      have h_maxv_le_m : Fin.maxOfNat n_outer v ≤ m := by rw [hm]; omega
      -- Inner family.
      set inner : Fin k_inner → ℕ := fun i => (gs i).interp v with hinner
      -- Per-`gs i` bounds, lifted to base `m`.
      have h_each_gi_rt :
          ∀ i : Fin k_inner,
            LawvereERKSim.compileER_runtime (gs i) v ≤ tower muG m := by
        intro i
        have h_mu_le : (boundExprKParams (gs i)).1 ≤ muG :=
          Fin.le_maxOfNat (fun j => (boundExprKParams (gs j)).1) i
        have h_off_le : (boundExprKParams (gs i)).2 ≤ offG :=
          Fin.le_maxOfNat (fun j => (boundExprKParams (gs j)).2) i
        have h_input_le :
            Fin.maxOfNat n_outer v + (boundExprKParams (gs i)).2 ≤ m := by
          rw [hm]; omega
        calc LawvereERKSim.compileER_runtime (gs i) v
            ≤ tower (boundExprKParams (gs i)).1
                  (Fin.maxOfNat n_outer v + (boundExprKParams (gs i)).2) :=
              (ih_gs i v).1
          _ ≤ tower (boundExprKParams (gs i)).1 m :=
              tower_mono_right _ h_input_le
          _ ≤ tower muG m := tower_mono_left h_mu_le m
      have h_each_gi_val :
          ∀ i : Fin k_inner, (gs i).interp v ≤ tower muG m := by
        intro i
        have h_mu_le : (boundExprKParams (gs i)).1 ≤ muG :=
          Fin.le_maxOfNat (fun j => (boundExprKParams (gs j)).1) i
        have h_off_le : (boundExprKParams (gs i)).2 ≤ offG :=
          Fin.le_maxOfNat (fun j => (boundExprKParams (gs j)).2) i
        have h_input_le :
            Fin.maxOfNat n_outer v + (boundExprKParams (gs i)).2 ≤ m := by
          rw [hm]; omega
        calc (gs i).interp v
            ≤ tower (boundExprKParams (gs i)).1
                  (Fin.maxOfNat n_outer v + (boundExprKParams (gs i)).2) :=
              (ih_gs i v).2
          _ ≤ tower (boundExprKParams (gs i)).1 m :=
              tower_mono_right _ h_input_le
          _ ≤ tower muG m := tower_mono_left h_mu_le m
      -- `Fin.maxOfNat _ inner ≤ tower muG m`.
      have h_maxInner_le : Fin.maxOfNat k_inner inner ≤ tower muG m :=
        Fin.maxOfNat_le (fun i => h_each_gi_val i)
      -- Inner-offset absorption: `Fin.maxOfNat _ inner + offF
      -- ≤ tower muG m + m ≤ 2·tower muG m ≤ m·tower muG m
      -- ≤ tower (muG + 2) m`. Shared by the runtime and value bounds
      -- on `f` at `inner`.
      have h_arg_le :
          Fin.maxOfNat k_inner inner + offF ≤ tower (muG + 2) m := by
        have h_m_le_tower : m ≤ tower muG m := self_le_tower _ _
        have h1 : Fin.maxOfNat k_inner inner + offF ≤ tower muG m + m := by
          omega
        have h2 : tower muG m + m ≤ 2 * tower muG m := by
          have := h_m_le_tower; omega
        have h3 : 2 * tower muG m ≤ m * tower muG m :=
          Nat.mul_le_mul_right _ h_m_ge_2
        have h4 : m * tower muG m ≤ tower (muG + 2) m :=
          mul_tower_le_tower_add_two h_m_ge_2
        exact h1.trans (h2.trans (h3.trans h4))
      -- `tower_comp` rewrites `tower muF (tower (muG + 2) m)` to
      -- `tower (muF + muG + 2) m`. Shared by the runtime and value
      -- chains below.
      have h_tower_collapse :
          tower muF (tower (muG + 2) m) = tower (muF + muG + 2) m := by
        have h := tower_comp muF (muG + 2) m
        have h_idx : muF + (muG + 2) = muF + muG + 2 := by ring
        rw [h_idx] at h
        exact h
      -- Bound `rt(f at inner)` via `ih_f.1` + the shared absorption.
      have h_rt_f_at_inner :
          LawvereERKSim.compileER_runtime f inner ≤
            tower (muF + muG + 2) m := by
        have h_rt :
            LawvereERKSim.compileER_runtime f inner ≤
              tower muF (Fin.maxOfNat k_inner inner + offF) := (ih_f inner).1
        have h_rt' :
            LawvereERKSim.compileER_runtime f inner ≤
              tower muF (tower (muG + 2) m) :=
          h_rt.trans (tower_mono_right _ h_arg_le)
        exact h_tower_collapse ▸ h_rt'
      -- Bound `f.interp inner ≤ tower (muF + muG + 2) m` analogously.
      have h_val_f_at_inner :
          f.interp inner ≤ tower (muF + muG + 2) m := by
        have h_val : f.interp inner ≤
              tower muF (Fin.maxOfNat k_inner inner + offF) := (ih_f inner).2
        have h_val' : f.interp inner ≤
              tower muF (tower (muG + 2) m) :=
          h_val.trans (tower_mono_right _ h_arg_le)
        exact h_tower_collapse ▸ h_val'
      -- Bound `glue ≤ tower (muG + 6) m` via a per-summand bound of
      -- `tower (muG + 4) m`, then `k`-fold absorption. The per-summand
      -- bound case-splits on `n_outer = 0` vs `n_outer ≥ 1`; in the latter, each
      -- `gs i` has arity ≥ 1, forcing `muG ≥ 2` (via the helper) so
      -- that `9·v_total ≤ tower(muG+2) m` absorbs into the five-piece sum.
      have h_glue_bound :
          List.foldl (fun x1 x2 => x1 + x2) 0
              (List.map
                (fun i =>
                  LawvereERKSim.compileER_runtime (gs i) v + 4
                    + 5 * inner i
                    + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                        (List.map v (List.finRange n_outer))
                    + 2 * n_outer)
                (List.finRange k_inner))
            ≤ tower (muG + 6) m := by
        have h_per_summand :
            ∀ i : Fin k_inner,
              (LawvereERKSim.compileER_runtime (gs i) v + 4
                + 5 * inner i
                + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                    (List.map v (List.finRange n_outer))
                + 2 * n_outer) ≤ tower (muG + 4) m := by
          intro i
          -- Individual bounds for the four "small" pieces.
          have h_A : LawvereERKSim.compileER_runtime (gs i) v
              ≤ tower (muG + 2) m :=
            (h_each_gi_rt i).trans (tower_mono_left (by omega) m)
          have h_B : (4 : ℕ) ≤ tower (muG + 2) m :=
            (by omega : (4 : ℕ) ≤ m).trans (self_le_tower _ _)
          have h_C : 5 * inner i ≤ tower (muG + 2) m := by
            have h_5_le_m : 5 ≤ m := by omega
            calc 5 * inner i
                ≤ 5 * tower muG m :=
                  Nat.mul_le_mul_left _ (h_each_gi_val i)
              _ ≤ m * tower muG m :=
                  Nat.mul_le_mul_right _ h_5_le_m
              _ ≤ tower (muG + 2) m :=
                  mul_tower_le_tower_add_two h_m_ge_2
          have h_E : 2 * n_outer ≤ tower (muG + 2) m := by
            have : 2 * n_outer ≤ m := by omega
            exact this.trans (self_le_tower _ _)
          -- Bound for the `9·v_total` piece. Case-split on n_outer = 0.
          have h_D : 9 * List.foldl (fun x1 x2 => x1 + x2) 0
              (List.map v (List.finRange n_outer)) ≤ tower (muG + 2) m := by
            by_cases h_n : n_outer = 0
            · subst h_n
              simp
            · have h_n_pos : 1 ≤ n_outer := Nat.one_le_iff_ne_zero.mpr h_n
              -- `gs i : ERMor1 n_outer` with n_outer ≥ 1 implies muG_i ≥ 2 (helper).
              have h_muG_ge_2 : 2 ≤ muG := by
                have h_gi := boundExprKParams_mu_ge_two_or_arity_zero (gs i)
                rcases h_gi with h_ge | h_zero
                · exact h_ge.trans
                    (Fin.le_maxOfNat (fun j => (boundExprKParams (gs j)).1) i)
                · exact absurd h_zero (Nat.one_le_iff_ne_zero.mp h_n_pos)
              -- 9·v_total ≤ 9·m·m ≤ m·m·m ≤ m·tower 2 m ≤ tower 4 m
              --   ≤ tower(muG+2) m  (uses muG ≥ 2).
              have h_each_v : ∀ j : Fin n_outer, v j ≤ m :=
                fun j => (Fin.le_maxOfNat v j).trans h_maxv_le_m
              have h_vtotal_le_nm :
                  List.foldl (fun x1 x2 => x1 + x2) 0
                    (List.map v (List.finRange n_outer)) ≤ n_outer * m := by
                have := foldl_finRange_le_mul_maxOfNat (k := n_outer) v
                exact this.trans (Nat.mul_le_mul_left _ h_maxv_le_m)
              have h_vtotal_le_mm :
                  List.foldl (fun x1 x2 => x1 + x2) 0
                    (List.map v (List.finRange n_outer)) ≤ m * m :=
                h_vtotal_le_nm.trans (Nat.mul_le_mul_right _ h_n_le_m)
              have h_9_le_m : 9 ≤ m := by omega
              have h_mm_le_t2 : m * m ≤ tower 2 m := by
                calc m * m = m * tower 0 m := by rw [tower_zero]
                  _ ≤ tower 2 m := mul_tower_le_tower_add_two h_m_ge_2
              calc 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                    (List.map v (List.finRange n_outer))
                  ≤ 9 * (m * m) :=
                    Nat.mul_le_mul_left _ h_vtotal_le_mm
                _ ≤ m * (m * m) := Nat.mul_le_mul_right _ h_9_le_m
                _ ≤ m * tower 2 m :=
                    Nat.mul_le_mul_left _ h_mm_le_t2
                _ ≤ tower 4 m := by
                    have := mul_tower_le_tower_add_two (k := 2) h_m_ge_2
                    have h_eq : 2 + 2 = 4 := by ring
                    rw [← h_eq]; exact this
                _ ≤ tower (muG + 2) m :=
                    tower_mono_left (by omega) m
          -- Sum five pieces ≤ 5·tower(muG+2) m ≤ m·tower(muG+2) m
          -- ≤ tower(muG+4) m.
          have h_5_le_m : 5 ≤ m := by omega
          calc LawvereERKSim.compileER_runtime (gs i) v + 4
                + 5 * inner i
                + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                    (List.map v (List.finRange n_outer))
                + 2 * n_outer
              ≤ tower (muG + 2) m + tower (muG + 2) m + tower (muG + 2) m
                  + tower (muG + 2) m + tower (muG + 2) m :=
                Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
                  (Nat.add_le_add h_A h_B) h_C) h_D) h_E
            _ = 5 * tower (muG + 2) m := by ring
            _ ≤ m * tower (muG + 2) m :=
                Nat.mul_le_mul_right _ h_5_le_m
            _ ≤ tower (muG + 4) m := by
                have := mul_tower_le_tower_add_two
                  (k := muG + 2) h_m_ge_2
                have h_eq : muG + 2 + 2 = muG + 4 := by ring
                rw [← h_eq]; exact this
        -- Outer k-fold: ≤ k · tower(muG+4) m ≤ m · _ ≤ tower(muG+6) m.
        have h_fold :
            List.foldl (fun x1 x2 => x1 + x2) 0
                (List.map
                  (fun i =>
                    LawvereERKSim.compileER_runtime (gs i) v + 4
                      + 5 * inner i
                      + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                          (List.map v (List.finRange n_outer))
                      + 2 * n_outer)
                  (List.finRange k_inner))
              ≤ k_inner * tower (muG + 4) m := by
          have h_each_le :
              ∀ x ∈ List.finRange k_inner,
                (LawvereERKSim.compileER_runtime (gs x) v + 4
                  + 5 * inner x
                  + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                      (List.map v (List.finRange n_outer))
                  + 2 * n_outer) ≤ tower (muG + 4) m :=
            fun x _ => h_per_summand x
          have := foldl_map_le_length_mul (List.finRange k_inner)
            (fun i =>
              LawvereERKSim.compileER_runtime (gs i) v + 4
                + 5 * inner i
                + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                    (List.map v (List.finRange n_outer))
                + 2 * n_outer)
            (tower (muG + 4) m) h_each_le
          simpa [List.length_finRange] using this
        calc List.foldl (fun x1 x2 => x1 + x2) 0
                (List.map
                  (fun i =>
                    LawvereERKSim.compileER_runtime (gs i) v + 4
                      + 5 * inner i
                      + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                          (List.map v (List.finRange n_outer))
                      + 2 * n_outer)
                  (List.finRange k_inner))
            ≤ k_inner * tower (muG + 4) m := h_fold
          _ ≤ m * tower (muG + 4) m :=
                Nat.mul_le_mul_right _ h_k_le_m
          _ ≤ tower (muG + 6) m := by
                have := mul_tower_le_tower_add_two
                  (k := muG + 4) h_m_ge_2
                have h_eq : muG + 4 + 2 = muG + 6 := by ring
                rw [← h_eq]; exact this
      -- Case-split on muF (≥ 2 or arity-zero, i.e., k_inner = 0).
      rcases boundExprKParams_mu_ge_two_or_arity_zero f with h_muF_ge | h_k_eq_zero
      · -- muF ≥ 2: standard chain.
        refine ⟨?_, ?_⟩
        · -- Runtime: glue + rt(f at inner) + 2 ≤ target.
          have h_glue' :
              List.foldl (fun x1 x2 => x1 + x2) 0
                  (List.map
                    (fun i =>
                      LawvereERKSim.compileER_runtime (gs i) v + 4
                        + 5 * inner i
                        + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                            (List.map v (List.finRange n_outer))
                        + 2 * n_outer)
                    (List.finRange k_inner))
                ≤ tower (muF + muG + 4) m :=
            h_glue_bound.trans (tower_mono_left (by omega) m)
          have h_rt' :
              LawvereERKSim.compileER_runtime f inner
                ≤ tower (muF + muG + 4) m :=
            h_rt_f_at_inner.trans (tower_mono_left (by omega) m)
          have h_2 : (2 : ℕ) ≤ tower (muF + muG + 4) m := by
            have h_2_le_m : 2 ≤ m := h_m_ge_2
            exact h_2_le_m.trans (self_le_tower _ _)
          calc List.foldl (fun x1 x2 => x1 + x2) 0
                  (List.map
                    (fun i =>
                      LawvereERKSim.compileER_runtime (gs i) v + 4
                        + 5 * inner i
                        + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                            (List.map v (List.finRange n_outer))
                        + 2 * n_outer)
                    (List.finRange k_inner))
                + LawvereERKSim.compileER_runtime f inner + 2
              ≤ tower (muF + muG + 4) m + tower (muF + muG + 4) m
                  + tower (muF + muG + 4) m :=
                Nat.add_le_add (Nat.add_le_add h_glue' h_rt') h_2
            _ = 3 * tower (muF + muG + 4) m := by ring
            _ ≤ m * tower (muF + muG + 4) m :=
                Nat.mul_le_mul_right _ (by omega : 3 ≤ m)
            _ ≤ tower (muF + muG + 6) m := by
                have := mul_tower_le_tower_add_two
                  (k := muF + muG + 4) h_m_ge_2
                have h_eq : muF + muG + 4 + 2 = muF + muG + 6 := by ring
                rw [← h_eq]; exact this
        · -- Value: f.interp inner ≤ tower(muF+muG+2) m ≤ target.
          exact h_val_f_at_inner.trans (tower_mono_left (by omega) m)
      · -- k_inner = 0: glue = 0, inner is Fin.elim0, simpler chain.
        subst h_k_eq_zero
        -- Now k_inner = 0; the fold over List.finRange 0 = [] yields 0.
        have h_glue_zero :
            List.foldl (fun x1 x2 => x1 + x2) 0
                (List.map
                  (fun i =>
                    LawvereERKSim.compileER_runtime (gs i) v + 4
                      + 5 * inner i
                      + 9 * List.foldl (fun x1 x2 => x1 + x2) 0
                          (List.map v (List.finRange n_outer))
                      + 2 * n_outer)
                  (List.finRange 0)) = 0 := by
          simp
        -- muG = Fin.maxOfNat 0 _ = 0.
        have h_muG_zero : muG = 0 := by
          rw [hmuG]; rfl
        -- rt(f at inner) ≤ tower muF (Fin.maxOfNat 0 inner + offF)
        -- = tower muF offF ≤ tower muF m ≤ tower (muF + 6) m.
        refine ⟨?_, ?_⟩
        · rw [h_glue_zero]
          -- Goal: 0 + rt(f at inner) + 2 ≤ tower (muF + muG + 6) m.
          have h_rt_inner :
              LawvereERKSim.compileER_runtime f inner ≤
                tower muF (Fin.maxOfNat 0 inner + offF) := (ih_f inner).1
          have h_max0 : Fin.maxOfNat 0 inner = 0 := rfl
          rw [h_max0, Nat.zero_add] at h_rt_inner
          have h_rt_le_m : LawvereERKSim.compileER_runtime f inner
              ≤ tower muF m :=
            h_rt_inner.trans (tower_mono_right _ h_offF_le_m)
          have h_rt_le_t4 : LawvereERKSim.compileER_runtime f inner
              ≤ tower (muF + muG + 4) m :=
            h_rt_le_m.trans (tower_mono_left (by omega) m)
          have h_2_le_t4 : (2 : ℕ) ≤ tower (muF + muG + 4) m :=
            h_m_ge_2.trans (self_le_tower _ _)
          -- 0 + rt + 2 ≤ 2·tower(muF+muG+4) m ≤ m·_ ≤ tower(muF+muG+6) m.
          calc 0 + LawvereERKSim.compileER_runtime f inner + 2
              = LawvereERKSim.compileER_runtime f inner + 2 := by ring
            _ ≤ tower (muF + muG + 4) m + tower (muF + muG + 4) m :=
                Nat.add_le_add h_rt_le_t4 h_2_le_t4
            _ = 2 * tower (muF + muG + 4) m := by ring
            _ ≤ m * tower (muF + muG + 4) m :=
                Nat.mul_le_mul_right _ h_m_ge_2
            _ ≤ tower (muF + muG + 6) m := by
                have := mul_tower_le_tower_add_two
                  (k := muF + muG + 4) h_m_ge_2
                have h_eq : muF + muG + 4 + 2 = muF + muG + 6 := by ring
                rw [← h_eq]; exact this
        · -- Value: f.interp inner ≤ tower muF offF ≤ tower(muF+muG+6) m.
          have h_val_inner :
              f.interp inner ≤
                tower muF (Fin.maxOfNat 0 inner + offF) := (ih_f inner).2
          have h_max0 : Fin.maxOfNat 0 inner = 0 := rfl
          rw [h_max0, Nat.zero_add] at h_val_inner
          have h_val_le_m : f.interp inner ≤ tower muF m :=
            h_val_inner.trans (tower_mono_right _ h_offF_le_m)
          exact h_val_le_m.trans (tower_mono_left (by omega) m)
  | bsum f ih_f          =>
      rename_i k
      intro v
      simp only [LawvereERKSim.compileER_runtime, ERMor1.interp_bsum,
        boundExprKParams]
      set muF : ℕ := (boundExprKParams f).1 with hmuF
      set offF : ℕ := (boundExprKParams f).2 with hoffF
      set nRegs_f : ℕ := LawvereERKSim.compileER_numRegs f with hnRegs_f
      set m : ℕ := Fin.maxOfNat (k + 1) v + (offF + k + nRegs_f + 32) with hm
      -- Numeric facts on `m`.
      have h_m_ge_32 : 32 ≤ m := by rw [hm]; omega
      have h_m_ge_2 : 2 ≤ m := by omega
      have h_maxv_le_m : Fin.maxOfNat (k + 1) v ≤ m := by rw [hm]; omega
      have h_offF_le_m : offF ≤ m := by rw [hm]; omega
      have h_k_le_m : k ≤ m := by rw [hm]; omega
      have h_nRegs_le_m : nRegs_f ≤ m := by rw [hm]; omega
      have h_v0_le_m : v 0 ≤ m :=
        (Fin.le_maxOfNat v 0).trans h_maxv_le_m
      have h_len_range : (List.range (v 0)).length = v 0 := List.length_range
      -- `mu_f ≥ 2`: `f : ERMor1 (k + 1)` has arity `k + 1 ≠ 0`.
      have h_muF_ge_2 : 2 ≤ muF := by
        rcases boundExprKParams_mu_ge_two_or_arity_zero f with h | h
        · exact h
        · exact absurd h (Nat.succ_ne_zero k)
      -- Per-`i` shorthand and bounds (parameterised by `i ≤ v 0`).
      -- `ctx_f_i j` is dominated by `Fin.maxOfNat (k+1) v` for each `j`.
      have h_ctx_le_max :
          ∀ i, i ≤ v 0 → ∀ j : Fin (k + 1),
            (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)) j
              ≤ Fin.maxOfNat (k + 1) v := by
        intro i hi j
        refine Fin.cases ?_ ?_ j
        · -- j = 0: value is `i ≤ v 0 ≤ Fin.maxOfNat _ v`.
          change i ≤ Fin.maxOfNat (k + 1) v
          exact hi.trans (Fin.le_maxOfNat v 0)
        · intro j'
          change v j'.succ ≤ Fin.maxOfNat (k + 1) v
          exact Fin.le_maxOfNat v j'.succ
      have h_maxCtx_le_maxv :
          ∀ i, i ≤ v 0 →
            Fin.maxOfNat (k + 1)
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
              ≤ Fin.maxOfNat (k + 1) v := by
        intro i hi
        exact Fin.maxOfNat_le (fun j => h_ctx_le_max i hi j)
      -- `ih_f` instantiated at each `ctx_f_i`, with `Fin.maxOfNat _ ctx_f_i + offF ≤ m`.
      have h_rt_f_ctx :
          ∀ i, i ≤ v 0 →
            LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
              ≤ tower muF m := by
        intro i hi
        have h_in_le :
            Fin.maxOfNat (k + 1)
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)) + offF
              ≤ m :=
          (Nat.add_le_add_right (h_maxCtx_le_maxv i hi) offF).trans
            (by rw [hm]; omega)
        exact ((ih_f _).1).trans (tower_mono_right _ h_in_le)
      have h_val_f_ctx :
          ∀ i, i ≤ v 0 →
            f.interp (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
              ≤ tower muF m := by
        intro i hi
        have h_in_le :
            Fin.maxOfNat (k + 1)
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)) + offF
              ≤ m :=
          (Nat.add_le_add_right (h_maxCtx_le_maxv i hi) offF).trans
            (by rw [hm]; omega)
        exact ((ih_f _).2).trans (tower_mono_right _ h_in_le)
      -- `outerSum := Σ_{j<k} (Fin.tail v) j ≤ k · Fin.maxOfNat k (Fin.tail v) ≤ k · m`.
      set outerSum : ℕ :=
        ((List.finRange k).map (Fin.tail v)).foldl (· + ·) 0 with houterSum
      have h_outerSum_le_mm : outerSum ≤ m * m := by
        have h_tail_le_m : ∀ j : Fin k, (Fin.tail v) j ≤ m :=
          fun j => (Fin.le_maxOfNat v j.succ).trans h_maxv_le_m
        have h_max_tail_le_m : Fin.maxOfNat k (Fin.tail v) ≤ m :=
          Fin.maxOfNat_le h_tail_le_m
        have h1 : outerSum ≤ k * Fin.maxOfNat k (Fin.tail v) :=
          foldl_finRange_le_mul_maxOfNat (k := k) (Fin.tail v)
        have h2 : k * Fin.maxOfNat k (Fin.tail v) ≤ k * m :=
          Nat.mul_le_mul_left _ h_max_tail_le_m
        have h3 : k * m ≤ m * m :=
          Nat.mul_le_mul_right _ h_k_le_m
        exact h1.trans (h2.trans h3)
      -- Useful tower-2 baseline `m ≤ tower 2 m` and `m·m ≤ tower 2 m`.
      have h_m_le_t2 : m ≤ tower 2 m := self_le_tower _ _
      have h_mm_le_t2 : m * m ≤ tower 2 m := by
        calc m * m = m * tower 0 m := by rw [tower_zero]
          _ ≤ tower 2 m := mul_tower_le_tower_add_two h_m_ge_2
      -- Intermediate tower bounds used throughout the chain.
      have h_mmm_le_t4 : m * m * m ≤ tower 4 m := by
        calc m * m * m
            = m * (m * m) := by ring
          _ ≤ m * tower 2 m := Nat.mul_le_mul_left _ h_mm_le_t2
          _ ≤ tower 4 m := by
              have := mul_tower_le_tower_add_two (k := 2) h_m_ge_2
              have h_eq : 2 + 2 = 4 := by ring
              rw [← h_eq]; exact this
      have h_mmmm_le_t6 : m * m * m * m ≤ tower 6 m := by
        calc m * m * m * m
            = m * (m * m * m) := by ring
          _ ≤ m * tower 4 m := Nat.mul_le_mul_left _ h_mmm_le_t4
          _ ≤ tower 6 m := by
              have := mul_tower_le_tower_add_two (k := 4) h_m_ge_2
              have h_eq : 4 + 2 = 6 := by ring
              rw [← h_eq]; exact this
      have h_i_le_v0 : ∀ i ∈ List.range (v 0), i ≤ v 0 := by
        intro i hi; exact Nat.le_of_lt (List.mem_range.mp hi)
      ------------------------------------------------------------------
      -- Per-component fold bounds. Each ≤ tower (muF + 4) m.
      -- A covers spec §4.2 bsum's "part 1" (`Σ rt`); E covers "part 2"
      -- (`Σ 5·val`); B, C, D, F together cover "part 3" (constant
      -- per-iteration overhead). D is itself split into D-part1
      -- (`Σ 10·i`) and D-part2 (`Σ 10·outerSum`).
      ------------------------------------------------------------------
      -- A-fold: Σ_i compileER_runtime f ctx_f_i.
      have h_A_fold :
          ((List.range (v 0)).map (fun i =>
            LawvereERKSim.compileER_runtime f
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h_each :
            ∀ i ∈ List.range (v 0),
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                ≤ tower muF m :=
          fun i hi => h_rt_f_ctx i (h_i_le_v0 i hi)
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => LawvereERKSim.compileER_runtime f
            (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))
          (tower muF m) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i =>
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ v 0 * tower muF m := h
          _ ≤ m * tower muF m := Nat.mul_le_mul_right _ h_v0_le_m
          _ ≤ tower (muF + 2) m := mul_tower_le_tower_add_two h_m_ge_2
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      -- B-fold: Σ_i 50. Use m ≥ 32, hence m·m ≥ 1024 ≥ 50.
      have h_B_fold :
          ((List.range (v 0)).map (fun _ : ℕ => 50)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => 50) 50 (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        have h_50_le_mm : 50 ≤ m * m := by
          have h_32_le_mm : 32 * 32 ≤ m * m := Nat.mul_le_mul h_m_ge_32 h_m_ge_32
          omega
        calc ((List.range (v 0)).map (fun _ : ℕ => 50)).foldl (· + ·) 0
            ≤ v 0 * 50 := h
          _ ≤ m * 50 := Nat.mul_le_mul_right _ h_v0_le_m
          _ ≤ m * (m * m) := Nat.mul_le_mul_left _ h_50_le_mm
          _ = m * m * m := by ring
          _ ≤ tower 4 m := h_mmm_le_t4
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      -- C-fold: Σ_i 2·(k + 1). 2·(k+1) ≤ 3m ≤ m·m; v 0·(2·(k+1)) ≤ m·m·m ≤ tower 4 m.
      have h_C_fold :
          ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => 2 * (k + 1)) (2 * (k + 1))
          (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        -- 2·(k+1) = 2k + 2 ≤ 2m + 2 ≤ 2m + m = 3m (since m ≥ 2) ≤ m·m (since m ≥ 3).
        have h_2k1_le_mm : 2 * (k + 1) ≤ m * m := by
          have h_3m_le_mm : 3 * m ≤ m * m :=
            Nat.mul_le_mul_right _ (by omega : 3 ≤ m)
          have h_2k1_le_3m : 2 * (k + 1) ≤ 3 * m := by
            have h_k_plus_1_le_m : k + 1 ≤ m := by omega
            calc 2 * (k + 1) ≤ 2 * m := Nat.mul_le_mul_left _ h_k_plus_1_le_m
              _ ≤ 3 * m := Nat.mul_le_mul_right _ (by omega : 2 ≤ 3)
          exact h_2k1_le_3m.trans h_3m_le_mm
        calc ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl (· + ·) 0
            ≤ v 0 * (2 * (k + 1)) := h
          _ ≤ m * (2 * (k + 1)) := Nat.mul_le_mul_right _ h_v0_le_m
          _ ≤ m * (m * m) := Nat.mul_le_mul_left _ h_2k1_le_mm
          _ = m * m * m := by ring
          _ ≤ tower 4 m := h_mmm_le_t4
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      -- D-fold: Σ_i 10·(i + outerSum). Split via foldl_add_map_split.
      have h_D_part1 :
          ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h_each : ∀ i ∈ List.range (v 0), 10 * i ≤ 10 * v 0 := by
          intro i hi
          exact Nat.mul_le_mul_left _ (h_i_le_v0 i hi)
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => 10 * i) (10 * v 0) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
            ≤ v 0 * (10 * v 0) := h
          _ = 10 * (v 0 * v 0) := by ring
          _ ≤ 10 * (m * m) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul h_v0_le_m h_v0_le_m)
          _ ≤ m * (m * m) := Nat.mul_le_mul_right _ (by omega : 10 ≤ m)
          _ = m * m * m := by ring
          _ ≤ tower 4 m := h_mmm_le_t4
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      have h_D_part2 :
          ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => 10 * outerSum) (10 * outerSum)
          (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl
                (· + ·) 0
            ≤ v 0 * (10 * outerSum) := h
          _ = 10 * (v 0 * outerSum) := by ring
          _ ≤ 10 * (m * (m * m)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul h_v0_le_m h_outerSum_le_mm)
          _ ≤ m * (m * (m * m)) := Nat.mul_le_mul_right _ (by omega : 10 ≤ m)
          _ = m * m * m * m := by ring
          _ ≤ tower 6 m := h_mmmm_le_t6
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      have h_D_split :
          ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
              (· + ·) 0
            = ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
              + ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl
                  (· + ·) 0 := by
        have h := foldl_add_map_split (List.range (v 0))
          (fun i => 10 * i) (fun _ : ℕ => 10 * outerSum)
        have h_eq : (fun i : ℕ => 10 * (i + outerSum))
            = fun i : ℕ => 10 * i + 10 * outerSum := by
          funext i; ring
        rw [h_eq]; exact h
      have h_D_fold :
          ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
              (· + ·) 0
            ≤ 2 * tower (muF + 4) m := by
        rw [h_D_split]
        calc ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
              + ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl
                  (· + ·) 0
            ≤ tower (muF + 4) m + tower (muF + 4) m :=
              Nat.add_le_add h_D_part1 h_D_part2
          _ = 2 * tower (muF + 4) m := by ring
      -- E-fold: Σ_i 5 · f.interp ctx_f_i.
      have h_E_fold :
          ((List.range (v 0)).map (fun i =>
            5 * f.interp
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h_each :
            ∀ i ∈ List.range (v 0),
              5 * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                ≤ 5 * tower muF m := by
          intro i hi
          exact Nat.mul_le_mul_left _ (h_val_f_ctx i (h_i_le_v0 i hi))
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => 5 * f.interp
            (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))
          (5 * tower muF m) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i =>
              5 * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ v 0 * (5 * tower muF m) := h
          _ = 5 * (v 0 * tower muF m) := by ring
          _ ≤ m * (v 0 * tower muF m) :=
              Nat.mul_le_mul_right _ (by omega : 5 ≤ m)
          _ ≤ m * (m * tower muF m) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h_v0_le_m)
          _ ≤ m * tower (muF + 2) m :=
              Nat.mul_le_mul_left _ (mul_tower_le_tower_add_two h_m_ge_2)
          _ ≤ tower (muF + 4) m := by
              have := mul_tower_le_tower_add_two (k := muF + 2) h_m_ge_2
              have h_eq : muF + 2 + 2 = muF + 4 := by ring
              rw [← h_eq]; exact this
      -- F-fold: Σ_i nRegs_f.
      have h_F_fold :
          ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => nRegs_f) nRegs_f (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl (· + ·) 0
            ≤ v 0 * nRegs_f := h
          _ ≤ m * m := Nat.mul_le_mul h_v0_le_m h_nRegs_le_m
          _ ≤ tower 2 m := h_mm_le_t2
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      ------------------------------------------------------------------
      -- Decompose the perIter fold via foldl_add_map_split.
      -- The addend parses as ((((A + B) + C) + D) + E) + F.
      ------------------------------------------------------------------
      have h_perIter_eq :
          ((List.range (v 0)).map (fun i =>
            LawvereERKSim.compileER_runtime f
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + 50 + 2 * (k + 1) + 10 * (i + outerSum)
            + 5 * f.interp
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + nRegs_f)).foldl (· + ·) 0
          = ((List.range (v 0)).map (fun i =>
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 50)).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                5 * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl
                (· + ·) 0 := by
        rw [foldl_add_map_split, foldl_add_map_split, foldl_add_map_split,
            foldl_add_map_split, foldl_add_map_split]
      -- Sum of six component bounds: ≤ 7 · tower (muF + 4) m
      -- (D-fold contributes 2 · _, the other five each 1 · _; total 7 ·).
      have h_perIter_fold_le :
          ((List.range (v 0)).map (fun i =>
            LawvereERKSim.compileER_runtime f
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + 50 + 2 * (k + 1) + 10 * (i + outerSum)
            + 5 * f.interp
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + nRegs_f)).foldl (· + ·) 0
            ≤ 7 * tower (muF + 4) m := by
        rw [h_perIter_eq]
        have : ((List.range (v 0)).map (fun i =>
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 50)).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                5 * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl
                (· + ·) 0
            ≤ tower (muF + 4) m + tower (muF + 4) m + tower (muF + 4) m
              + 2 * tower (muF + 4) m + tower (muF + 4) m
              + tower (muF + 4) m := by
          exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add h_A_fold h_B_fold) h_C_fold) h_D_fold)
            h_E_fold) h_F_fold
        calc ((List.range (v 0)).map (fun i =>
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 50)).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                5 * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl
                (· + ·) 0
            ≤ tower (muF + 4) m + tower (muF + 4) m + tower (muF + 4) m
              + 2 * tower (muF + 4) m + tower (muF + 4) m
              + tower (muF + 4) m := this
          _ = 7 * tower (muF + 4) m := by ring
      ------------------------------------------------------------------
      -- Constant prefix `30 + 10·v 0 ≤ tower (muF + 4) m`.
      ------------------------------------------------------------------
      have h_const_le : (30 + 10 * v 0 : ℕ) ≤ tower (muF + 4) m := by
        calc 30 + 10 * v 0
            ≤ 30 + 10 * m := by
              exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h_v0_le_m) _
          _ ≤ 11 * m := by omega
          _ ≤ m * m := Nat.mul_le_mul_right _ (by omega : 11 ≤ m)
          _ ≤ tower 2 m := h_mm_le_t2
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      ------------------------------------------------------------------
      -- Combine: total ≤ 8 · tower (muF + 4) m ≤ m · _ ≤ tower (muF + 6) m.
      ------------------------------------------------------------------
      refine ⟨?_, ?_⟩
      · -- Runtime side.
        calc (30 + 10 * v 0 +
              ((List.range (v 0)).map (fun i =>
                LawvereERKSim.compileER_runtime f
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                + 50 + 2 * (k + 1) + 10 * (i + outerSum)
                + 5 * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                + nRegs_f)).foldl (· + ·) 0 : ℕ)
            ≤ tower (muF + 4) m + 7 * tower (muF + 4) m :=
              Nat.add_le_add h_const_le h_perIter_fold_le
          _ = 8 * tower (muF + 4) m := by ring
          _ ≤ m * tower (muF + 4) m :=
              Nat.mul_le_mul_right _ (by omega : 8 ≤ m)
          _ ≤ tower (muF + 6) m := by
              have := mul_tower_le_tower_add_two (k := muF + 4) h_m_ge_2
              have h_eq : muF + 4 + 2 = muF + 6 := by ring
              rw [← h_eq]; exact this
      · -- Value side: natBSum (v 0) (fun j => f.interp ctx_f_j) ≤ tower (muF + 6) m.
        have h_each :
            ∀ j, j < v 0 →
              f.interp (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v))
                ≤ tower muF m :=
          fun j hj => h_val_f_ctx j (Nat.le_of_lt hj)
        calc natBSum (v 0)
              (fun j => f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
            ≤ v 0 * tower muF m :=
              natBSum_le_mul_max _ _ _ h_each
          _ ≤ m * tower muF m := Nat.mul_le_mul_right _ h_v0_le_m
          _ ≤ tower (muF + 2) m := mul_tower_le_tower_add_two h_m_ge_2
          _ ≤ tower (muF + 6) m := tower_mono_left (by omega) m
  | bprod f ih_f         =>
      rename_i k
      intro v
      simp only [LawvereERKSim.compileER_runtime, ERMor1.interp_bprod,
        boundExprKParams]
      set muF : ℕ := (boundExprKParams f).1 with hmuF
      set offF : ℕ := (boundExprKParams f).2 with hoffF
      set nRegs_f : ℕ := LawvereERKSim.compileER_numRegs f with hnRegs_f
      set m : ℕ := Fin.maxOfNat (k + 1) v + (offF + k + nRegs_f + 44) with hm
      -- Numeric facts on `m`.
      have h_m_ge_44 : 44 ≤ m := by rw [hm]; omega
      have h_m_ge_2 : 2 ≤ m := by omega
      have h_maxv_le_m : Fin.maxOfNat (k + 1) v ≤ m := by rw [hm]; omega
      have h_offF_le_m : offF ≤ m := by rw [hm]; omega
      have h_k_le_m : k ≤ m := by rw [hm]; omega
      have h_nRegs_le_m : nRegs_f ≤ m := by rw [hm]; omega
      have h_v0_le_m : v 0 ≤ m :=
        (Fin.le_maxOfNat v 0).trans h_maxv_le_m
      have h_len_range : (List.range (v 0)).length = v 0 := List.length_range
      -- `mu_f ≥ 2`: `f : ERMor1 (k + 1)` has arity `k + 1 ≠ 0`.
      have h_muF_ge_2 : 2 ≤ muF := by
        rcases boundExprKParams_mu_ge_two_or_arity_zero f with h | h
        · exact h
        · exact absurd h (Nat.succ_ne_zero k)
      -- Per-`i` context-domination shared with the bsum case.
      have h_ctx_le_max :
          ∀ i, i ≤ v 0 → ∀ j : Fin (k + 1),
            (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)) j
              ≤ Fin.maxOfNat (k + 1) v := by
        intro i hi j
        refine Fin.cases ?_ ?_ j
        · change i ≤ Fin.maxOfNat (k + 1) v
          exact hi.trans (Fin.le_maxOfNat v 0)
        · intro j'
          change v j'.succ ≤ Fin.maxOfNat (k + 1) v
          exact Fin.le_maxOfNat v j'.succ
      have h_maxCtx_le_maxv :
          ∀ i, i ≤ v 0 →
            Fin.maxOfNat (k + 1)
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
              ≤ Fin.maxOfNat (k + 1) v := by
        intro i hi
        exact Fin.maxOfNat_le (fun j => h_ctx_le_max i hi j)
      -- `ih_f` instantiated at each `ctx_f_i`.
      have h_rt_f_ctx :
          ∀ i, i ≤ v 0 →
            LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
              ≤ tower muF m := by
        intro i hi
        have h_in_le :
            Fin.maxOfNat (k + 1)
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)) + offF
              ≤ m :=
          (Nat.add_le_add_right (h_maxCtx_le_maxv i hi) offF).trans
            (by rw [hm]; omega)
        exact ((ih_f _).1).trans (tower_mono_right _ h_in_le)
      have h_val_f_ctx :
          ∀ i, i ≤ v 0 →
            f.interp (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
              ≤ tower muF m := by
        intro i hi
        have h_in_le :
            Fin.maxOfNat (k + 1)
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)) + offF
              ≤ m :=
          (Nat.add_le_add_right (h_maxCtx_le_maxv i hi) offF).trans
            (by rw [hm]; omega)
        exact ((ih_f _).2).trans (tower_mono_right _ h_in_le)
      -- Per-`i` running-product bound `A_i ≤ tower (muF + 3) m` for `i ≤ v 0`.
      -- Routes through `natBProd_le_pow_max` and `tower_pow_le_tower_add_three`.
      have h_A_le_tower_muF_3 :
          ∀ i, i ≤ v 0 →
            natBProd i
                (fun j => f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
              ≤ tower (muF + 3) m := by
        intro i hi
        have h_each :
            ∀ j < i,
              f.interp (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v))
                ≤ tower muF m :=
          fun j hj =>
            h_val_f_ctx j (Nat.le_trans (Nat.le_of_lt hj) hi)
        have h_prod_bound :
            natBProd i
                (fun j => f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
              ≤ (tower muF m) ^ i :=
          natBProd_le_pow_max _ _ _ h_each
        have h_pow_mono : (tower muF m) ^ i ≤ (tower muF m) ^ m :=
          Nat.pow_le_pow_right
            (one_le_tower_of_one_le _ _ (by omega : 1 ≤ m))
            (hi.trans h_v0_le_m)
        have h_pow_to_tower : (tower muF m) ^ m ≤ tower (muF + 3) m :=
          tower_pow_le_tower_add_three h_m_ge_2
        exact h_prod_bound.trans (h_pow_mono.trans h_pow_to_tower)
      -- `outerSum` and the `m·m` tower-baselines reused from the bsum chain.
      set outerSum : ℕ :=
        ((List.finRange k).map (Fin.tail v)).foldl (· + ·) 0 with houterSum
      have h_outerSum_le_mm : outerSum ≤ m * m := by
        have h_tail_le_m : ∀ j : Fin k, (Fin.tail v) j ≤ m :=
          fun j => (Fin.le_maxOfNat v j.succ).trans h_maxv_le_m
        have h_max_tail_le_m : Fin.maxOfNat k (Fin.tail v) ≤ m :=
          Fin.maxOfNat_le h_tail_le_m
        have h1 : outerSum ≤ k * Fin.maxOfNat k (Fin.tail v) :=
          foldl_finRange_le_mul_maxOfNat (k := k) (Fin.tail v)
        have h2 : k * Fin.maxOfNat k (Fin.tail v) ≤ k * m :=
          Nat.mul_le_mul_left _ h_max_tail_le_m
        have h3 : k * m ≤ m * m :=
          Nat.mul_le_mul_right _ h_k_le_m
        exact h1.trans (h2.trans h3)
      have h_m_le_t2 : m ≤ tower 2 m := self_le_tower _ _
      have h_mm_le_t2 : m * m ≤ tower 2 m := by
        calc m * m = m * tower 0 m := by rw [tower_zero]
          _ ≤ tower 2 m := mul_tower_le_tower_add_two h_m_ge_2
      have h_mmm_le_t4 : m * m * m ≤ tower 4 m := by
        calc m * m * m
            = m * (m * m) := by ring
          _ ≤ m * tower 2 m := Nat.mul_le_mul_left _ h_mm_le_t2
          _ ≤ tower 4 m := by
              have := mul_tower_le_tower_add_two (k := 2) h_m_ge_2
              have h_eq : 2 + 2 = 4 := by ring
              rw [← h_eq]; exact this
      have h_mmmm_le_t6 : m * m * m * m ≤ tower 6 m := by
        calc m * m * m * m
            = m * (m * m * m) := by ring
          _ ≤ m * tower 4 m := Nat.mul_le_mul_left _ h_mmm_le_t4
          _ ≤ tower 6 m := by
              have := mul_tower_le_tower_add_two (k := 4) h_m_ge_2
              have h_eq : 4 + 2 = 6 := by ring
              rw [← h_eq]; exact this
      have h_i_le_v0 : ∀ i ∈ List.range (v 0), i ≤ v 0 := by
        intro i hi; exact Nat.le_of_lt (List.mem_range.mp hi)
      ------------------------------------------------------------------
      -- Per-component fold bounds. Folds A, B, C, D-parts, G, H land at
      -- `tower (muF + 4) m`; folds E (Σ 9·A·B) and F (Σ 4·A) land at
      -- `tower (muF + 7) m` after two multiplicative tower steps.
      ------------------------------------------------------------------
      -- A-fold: Σ_i compileER_runtime f ctx_f_i.
      have h_A_fold :
          ((List.range (v 0)).map (fun i =>
            LawvereERKSim.compileER_runtime f
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h_each :
            ∀ i ∈ List.range (v 0),
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                ≤ tower muF m :=
          fun i hi => h_rt_f_ctx i (h_i_le_v0 i hi)
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => LawvereERKSim.compileER_runtime f
            (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))
          (tower muF m) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i =>
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ v 0 * tower muF m := h
          _ ≤ m * tower muF m := Nat.mul_le_mul_right _ h_v0_le_m
          _ ≤ tower (muF + 2) m := mul_tower_le_tower_add_two h_m_ge_2
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      -- B-fold: Σ_i 60.
      have h_B_fold :
          ((List.range (v 0)).map (fun _ : ℕ => 60)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => 60) 60 (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        have h_60_le_mm : 60 ≤ m * m := by
          have h_44_le_mm : 44 * 44 ≤ m * m := Nat.mul_le_mul h_m_ge_44 h_m_ge_44
          omega
        calc ((List.range (v 0)).map (fun _ : ℕ => 60)).foldl (· + ·) 0
            ≤ v 0 * 60 := h
          _ ≤ m * 60 := Nat.mul_le_mul_right _ h_v0_le_m
          _ ≤ m * (m * m) := Nat.mul_le_mul_left _ h_60_le_mm
          _ = m * m * m := by ring
          _ ≤ tower 4 m := h_mmm_le_t4
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      -- C-fold: Σ_i 2·(k+1).
      have h_C_fold :
          ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => 2 * (k + 1)) (2 * (k + 1))
          (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        have h_2k1_le_mm : 2 * (k + 1) ≤ m * m := by
          have h_3m_le_mm : 3 * m ≤ m * m :=
            Nat.mul_le_mul_right _ (by omega : 3 ≤ m)
          have h_2k1_le_3m : 2 * (k + 1) ≤ 3 * m := by
            have h_k_plus_1_le_m : k + 1 ≤ m := by omega
            calc 2 * (k + 1) ≤ 2 * m := Nat.mul_le_mul_left _ h_k_plus_1_le_m
              _ ≤ 3 * m := Nat.mul_le_mul_right _ (by omega : 2 ≤ 3)
          exact h_2k1_le_3m.trans h_3m_le_mm
        calc ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl (· + ·) 0
            ≤ v 0 * (2 * (k + 1)) := h
          _ ≤ m * (2 * (k + 1)) := Nat.mul_le_mul_right _ h_v0_le_m
          _ ≤ m * (m * m) := Nat.mul_le_mul_left _ h_2k1_le_mm
          _ = m * m * m := by ring
          _ ≤ tower 4 m := h_mmm_le_t4
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      -- D-fold: Σ_i 10·(i + outerSum). Split via foldl_add_map_split.
      have h_D_part1 :
          ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h_each : ∀ i ∈ List.range (v 0), 10 * i ≤ 10 * v 0 := by
          intro i hi
          exact Nat.mul_le_mul_left _ (h_i_le_v0 i hi)
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => 10 * i) (10 * v 0) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
            ≤ v 0 * (10 * v 0) := h
          _ = 10 * (v 0 * v 0) := by ring
          _ ≤ 10 * (m * m) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul h_v0_le_m h_v0_le_m)
          _ ≤ m * (m * m) := Nat.mul_le_mul_right _ (by omega : 10 ≤ m)
          _ = m * m * m := by ring
          _ ≤ tower 4 m := h_mmm_le_t4
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      have h_D_part2 :
          ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => 10 * outerSum) (10 * outerSum)
          (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl
                (· + ·) 0
            ≤ v 0 * (10 * outerSum) := h
          _ = 10 * (v 0 * outerSum) := by ring
          _ ≤ 10 * (m * (m * m)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul h_v0_le_m h_outerSum_le_mm)
          _ ≤ m * (m * (m * m)) := Nat.mul_le_mul_right _ (by omega : 10 ≤ m)
          _ = m * m * m * m := by ring
          _ ≤ tower 6 m := h_mmmm_le_t6
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      have h_D_split :
          ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
              (· + ·) 0
            = ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
              + ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl
                  (· + ·) 0 := by
        have h := foldl_add_map_split (List.range (v 0))
          (fun i => 10 * i) (fun _ : ℕ => 10 * outerSum)
          (α := ℕ)
        have h_eq : (fun i : ℕ => 10 * (i + outerSum))
            = fun i : ℕ => 10 * i + 10 * outerSum := by
          funext i; ring
        rw [h_eq]; exact h
      have h_D_fold :
          ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
              (· + ·) 0
            ≤ 2 * tower (muF + 4) m := by
        rw [h_D_split]
        calc ((List.range (v 0)).map (fun i => 10 * i)).foldl (· + ·) 0
              + ((List.range (v 0)).map (fun _ : ℕ => 10 * outerSum)).foldl
                  (· + ·) 0
            ≤ tower (muF + 4) m + tower (muF + 4) m :=
              Nat.add_le_add h_D_part1 h_D_part2
          _ = 2 * tower (muF + 4) m := by ring
      -- E-fold: Σ_i 9 · A_i · B_i. Route through `A_i · B_i = A_{i+1}`,
      -- bounded by `tower (muF + 3) m`.
      have h_E_fold :
          ((List.range (v 0)).map (fun i =>
            9 * natBProd i
                  (fun j => f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
              * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ tower (muF + 7) m := by
        have h_each :
            ∀ i ∈ List.range (v 0),
              9 * natBProd i
                    (fun j => f.interp
                      (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
                * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                ≤ 9 * tower (muF + 3) m := by
          intro i hi
          -- `9 * A_i * B_i = 9 * (A_i * B_i) = 9 * A_{i+1}` (by definitional
          -- reduction of `natBProd (i+1)`).
          have h_lt_v0 : i < v 0 := List.mem_range.mp hi
          have h_succ_le : i + 1 ≤ v 0 := h_lt_v0
          have h_A_succ_bound :
              natBProd (i + 1)
                  (fun j => f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
                ≤ tower (muF + 3) m :=
            h_A_le_tower_muF_3 (i + 1) h_succ_le
          -- Rewrite goal to expose `natBProd (i+1)`.
          have h_eq :
              9 * natBProd i
                    (fun j => f.interp
                      (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
                * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                = 9 * natBProd (i + 1)
                    (fun j => f.interp
                      (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                        (Fin.tail v))) := by
            change 9 * natBProd i _ * f.interp _
              = 9 * (natBProd i _ * f.interp _)
            ring
          rw [h_eq]
          exact Nat.mul_le_mul_left _ h_A_succ_bound
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => 9 * natBProd i
                  (fun j => f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
              * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))
          (9 * tower (muF + 3) m) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i =>
              9 * natBProd i
                    (fun j => f.interp
                      (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
                * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ v 0 * (9 * tower (muF + 3) m) := h
          _ = 9 * (v 0 * tower (muF + 3) m) := by ring
          _ ≤ m * (v 0 * tower (muF + 3) m) :=
              Nat.mul_le_mul_right _ (by omega : 9 ≤ m)
          _ ≤ m * (m * tower (muF + 3) m) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h_v0_le_m)
          _ ≤ m * tower (muF + 5) m :=
              Nat.mul_le_mul_left _ (by
                have := mul_tower_le_tower_add_two (k := muF + 3) h_m_ge_2
                have h_eq : muF + 3 + 2 = muF + 5 := by ring
                rw [← h_eq]; exact this)
          _ ≤ tower (muF + 7) m := by
              have := mul_tower_le_tower_add_two (k := muF + 5) h_m_ge_2
              have h_eq : muF + 5 + 2 = muF + 7 := by ring
              rw [← h_eq]; exact this
      -- F-fold: Σ_i 4 · A_i.
      have h_F_fold :
          ((List.range (v 0)).map (fun i =>
            4 * natBProd i
                  (fun j => f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                      (Fin.tail v))))).foldl (· + ·) 0
            ≤ tower (muF + 7) m := by
        have h_each :
            ∀ i ∈ List.range (v 0),
              4 * natBProd i
                  (fun j => f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
                ≤ 4 * tower (muF + 3) m := by
          intro i hi
          exact Nat.mul_le_mul_left _ (h_A_le_tower_muF_3 i (h_i_le_v0 i hi))
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => 4 * natBProd i
                  (fun j => f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v))))
          (4 * tower (muF + 3) m) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i =>
              4 * natBProd i
                  (fun j => f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                      (Fin.tail v))))).foldl (· + ·) 0
            ≤ v 0 * (4 * tower (muF + 3) m) := h
          _ = 4 * (v 0 * tower (muF + 3) m) := by ring
          _ ≤ m * (v 0 * tower (muF + 3) m) :=
              Nat.mul_le_mul_right _ (by omega : 4 ≤ m)
          _ ≤ m * (m * tower (muF + 3) m) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h_v0_le_m)
          _ ≤ m * tower (muF + 5) m :=
              Nat.mul_le_mul_left _ (by
                have := mul_tower_le_tower_add_two (k := muF + 3) h_m_ge_2
                have h_eq : muF + 3 + 2 = muF + 5 := by ring
                rw [← h_eq]; exact this)
          _ ≤ tower (muF + 7) m := by
              have := mul_tower_le_tower_add_two (k := muF + 5) h_m_ge_2
              have h_eq : muF + 5 + 2 = muF + 7 := by ring
              rw [← h_eq]; exact this
      -- G-fold: Σ_i 9 · B_i = 9 · f.interp ctx_f_i (lands at muF + 4).
      have h_G_fold :
          ((List.range (v 0)).map (fun i =>
            9 * f.interp
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h_each :
            ∀ i ∈ List.range (v 0),
              9 * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                ≤ 9 * tower muF m := by
          intro i hi
          exact Nat.mul_le_mul_left _ (h_val_f_ctx i (h_i_le_v0 i hi))
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun i => 9 * f.interp
            (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))
          (9 * tower muF m) h_each
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun i =>
              9 * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            ≤ v 0 * (9 * tower muF m) := h
          _ = 9 * (v 0 * tower muF m) := by ring
          _ ≤ m * (v 0 * tower muF m) :=
              Nat.mul_le_mul_right _ (by omega : 9 ≤ m)
          _ ≤ m * (m * tower muF m) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h_v0_le_m)
          _ ≤ m * tower (muF + 2) m :=
              Nat.mul_le_mul_left _ (mul_tower_le_tower_add_two h_m_ge_2)
          _ ≤ tower (muF + 4) m := by
              have := mul_tower_le_tower_add_two (k := muF + 2) h_m_ge_2
              have h_eq : muF + 2 + 2 = muF + 4 := by ring
              rw [← h_eq]; exact this
      -- H-fold: Σ_i nRegs_f.
      have h_H_fold :
          ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl (· + ·) 0
            ≤ tower (muF + 4) m := by
        have h := foldl_map_le_length_mul (List.range (v 0))
          (fun _ : ℕ => nRegs_f) nRegs_f (by intro _ _; exact Nat.le_refl _)
        rw [h_len_range] at h
        calc ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl (· + ·) 0
            ≤ v 0 * nRegs_f := h
          _ ≤ m * m := Nat.mul_le_mul h_v0_le_m h_nRegs_le_m
          _ ≤ tower 2 m := h_mm_le_t2
          _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
      ------------------------------------------------------------------
      -- Decompose the perIter fold via foldl_add_map_split.
      -- Addend parses as
      --   ((((((A + B) + C) + D) + E) + F) + G) + H.
      ------------------------------------------------------------------
      have h_perIter_eq :
          ((List.range (v 0)).map (fun i =>
            LawvereERKSim.compileER_runtime f
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + 60 + 2 * (k + 1) + 10 * (i + outerSum)
            + 9 * natBProd i
                (fun j => f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
              * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + 4 * natBProd i
                (fun j => f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
            + 9 * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + nRegs_f)).foldl (· + ·) 0
          = ((List.range (v 0)).map (fun i =>
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 60)).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                9 * natBProd i
                      (fun j => f.interp
                        (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                          (Fin.tail v)))
                  * f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i
                      (Fin.tail v)))).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                4 * natBProd i
                      (fun j => f.interp
                        (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                          (Fin.tail v))))).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                9 * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i
                    (Fin.tail v)))).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl
                (· + ·) 0 := by
        rw [foldl_add_map_split, foldl_add_map_split, foldl_add_map_split,
            foldl_add_map_split, foldl_add_map_split, foldl_add_map_split,
            foldl_add_map_split]
      -- Sum of the eight component bounds. Lift A, B, C, G, H from
      -- (muF + 4) and D from (2·tower (muF + 4)) all to (muF + 7);
      -- then total ≤ 9 · tower (muF + 7) m.
      have h_perIter_fold_le :
          ((List.range (v 0)).map (fun i =>
            LawvereERKSim.compileER_runtime f
              (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + 60 + 2 * (k + 1) + 10 * (i + outerSum)
            + 9 * natBProd i
                (fun j => f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
              * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + 4 * natBProd i
                (fun j => f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
            + 9 * f.interp
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
            + nRegs_f)).foldl (· + ·) 0
            ≤ 9 * tower (muF + 7) m := by
        rw [h_perIter_eq]
        have h_lift : tower (muF + 4) m ≤ tower (muF + 7) m :=
          tower_mono_left (by omega) m
        have h_A' := h_A_fold.trans h_lift
        have h_B' := h_B_fold.trans h_lift
        have h_C' := h_C_fold.trans h_lift
        have h_D' : ((List.range (v 0)).map
            (fun i => 10 * (i + outerSum))).foldl (· + ·) 0
            ≤ 2 * tower (muF + 7) m :=
          h_D_fold.trans
            (Nat.mul_le_mul_left _ h_lift)
        have h_G' := h_G_fold.trans h_lift
        have h_H' := h_H_fold.trans h_lift
        calc ((List.range (v 0)).map (fun i =>
              LawvereERKSim.compileER_runtime f
                (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v)))).foldl
              (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 60)).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => 2 * (k + 1))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i => 10 * (i + outerSum))).foldl
                (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                9 * natBProd i
                      (fun j => f.interp
                        (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                          (Fin.tail v)))
                  * f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i
                      (Fin.tail v)))).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                4 * natBProd i
                      (fun j => f.interp
                        (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                          (Fin.tail v))))).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun i =>
                9 * f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i
                    (Fin.tail v)))).foldl (· + ·) 0
            + ((List.range (v 0)).map (fun _ : ℕ => nRegs_f)).foldl
                (· + ·) 0
            ≤ tower (muF + 7) m + tower (muF + 7) m + tower (muF + 7) m
              + 2 * tower (muF + 7) m + tower (muF + 7) m
              + tower (muF + 7) m + tower (muF + 7) m
              + tower (muF + 7) m :=
              Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
                (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h_A' h_B')
                  h_C') h_D') h_E_fold) h_F_fold) h_G') h_H'
          _ = 9 * tower (muF + 7) m := by ring
      ------------------------------------------------------------------
      -- Constant prefix `40 + 10·v 0 ≤ tower (muF + 7) m`.
      ------------------------------------------------------------------
      have h_const_le : (40 + 10 * v 0 : ℕ) ≤ tower (muF + 7) m := by
        have h_inner : (40 + 10 * v 0 : ℕ) ≤ tower (muF + 4) m := by
          calc 40 + 10 * v 0
              ≤ 40 + 10 * m := by
                exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h_v0_le_m) _
            _ ≤ 11 * m := by omega
            _ ≤ m * m := Nat.mul_le_mul_right _ (by omega : 11 ≤ m)
            _ ≤ tower 2 m := h_mm_le_t2
            _ ≤ tower (muF + 4) m := tower_mono_left (by omega) m
        exact h_inner.trans (tower_mono_left (by omega) m)
      ------------------------------------------------------------------
      -- Combine: total ≤ 10 · tower (muF + 7) m ≤ m · _ ≤ tower (muF + 9) m.
      ------------------------------------------------------------------
      refine ⟨?_, ?_⟩
      · -- Runtime side.
        calc (40 + 10 * v 0 +
              ((List.range (v 0)).map (fun i =>
                LawvereERKSim.compileER_runtime f
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                + 60 + 2 * (k + 1) + 10 * (i + outerSum)
                + 9 * natBProd i
                    (fun j => f.interp
                      (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                        (Fin.tail v)))
                  * f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                + 4 * natBProd i
                    (fun j => f.interp
                      (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j
                        (Fin.tail v)))
                + 9 * f.interp
                    (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) i (Fin.tail v))
                + nRegs_f)).foldl (· + ·) 0 : ℕ)
            ≤ tower (muF + 7) m + 9 * tower (muF + 7) m :=
              Nat.add_le_add h_const_le h_perIter_fold_le
          _ = 10 * tower (muF + 7) m := by ring
          _ ≤ m * tower (muF + 7) m :=
              Nat.mul_le_mul_right _ (by omega : 10 ≤ m)
          _ ≤ tower (muF + 9) m := by
              have := mul_tower_le_tower_add_two (k := muF + 7) h_m_ge_2
              have h_eq : muF + 7 + 2 = muF + 9 := by ring
              rw [← h_eq]; exact this
      · -- Value side: natBProd (v 0) (fun j => f.interp ctx_f_j)
        -- ≤ tower (muF + 3) m ≤ tower (muF + 9) m.
        have h_val_bound :
            natBProd (v 0)
                (fun j => f.interp
                  (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) j (Fin.tail v)))
              ≤ tower (muF + 3) m :=
          h_A_le_tower_muF_3 (v 0) (Nat.le_refl _)
        exact h_val_bound.trans (tower_mono_left (by omega) m)

/-- The level-≤ 2 `K`-morphism realising the runtime bound from
`boundExprKParams`: composes `KMor1.pow2_iter mu_e` with the
single-output addition of `KMor1.maxOver a` and the constant
`KMor1.natK' a offset_e`. Closed form:
`(boundExprK e).interp v = tower mu_e (Fin.maxOfNat _ v + offset_e)`. -/
def boundExprK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  let p := boundExprKParams e
  KMor1.comp
    (KMor1.pow2_iter p.1)
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.add
        (fun i : Fin 2 =>
          match i with
          | ⟨0, _⟩ => KMor1.maxOver _
          | ⟨1, _⟩ => KMor1.natK' _ p.2))

/-- `boundExprK e` has structural level at most 2. The outer
`pow2_iter` and `maxOver` summand each have level ≤ 2; `add` has
level 1; `natK'` has level 0; `comp` takes the maximum without
adding. -/
theorem boundExprK_level {a : ℕ} (e : ERMor1 a) :
    (boundExprK e).level ≤ 2 := by
  -- Outer comp: level = max (pow2_iter.level) (maxOfNat over the singleton).
  unfold boundExprK
  change max ((KMor1.pow2_iter (boundExprKParams e).1).level)
      (Fin.maxOfNat 1 (fun _ : Fin 1 =>
        (KMor1.comp KMor1.add
          (fun i : Fin 2 =>
            match i with
            | ⟨0, _⟩ => KMor1.maxOver a
            | ⟨1, _⟩ => KMor1.natK' a (boundExprKParams e).2)).level)) ≤ 2
  refine Nat.max_le.mpr ⟨KMor1.pow2_iter_level _, ?_⟩
  refine Fin.maxOfNat_le (fun _ => ?_)
  -- Inner comp: max add.level (maxOfNat over the per-index branches).
  change max KMor1.add.level
      (Fin.maxOfNat 2 (fun i : Fin 2 =>
        ((match i with
          | ⟨0, _⟩ => KMor1.maxOver a
          | ⟨1, _⟩ => KMor1.natK' a (boundExprKParams e).2) : KMor1 a).level)) ≤ 2
  refine Nat.max_le.mpr ⟨by decide, ?_⟩
  refine Fin.maxOfNat_le (fun i => ?_)
  match i with
  | ⟨0, _⟩ => exact KMor1.maxOver_level _
  | ⟨1, _⟩ => rw [KMor1.natK'_level]; exact Nat.zero_le _

/-- Interpretation of `boundExprK e` at context `v`: the tower of
height `mu_e := (boundExprKParams e).1` over the offset-shifted
maximum `Fin.maxOfNat _ v + (boundExprKParams e).2`. Mechanical
unfold via the `@[simp]` interp lemmas for `pow2_iter`, `add`,
`maxOver`, and `natK'`. -/
theorem boundExprK_interp {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (boundExprK e).interp v
      = tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2) := by
  unfold boundExprK
  simp only [KMor1.interp_comp, KMor1.interp_pow2_iter,
    KMor1.interp_add, KMor1.interp_maxOver, KMor1.interp_natK']

/-- Runtime side of the joint bound, expressed as a `K`-morphism
interpretation: the URM step count of `compileER e` at `v` is
dominated by `(boundExprK e).interp v`. Combines
`boundExprK_interp` with the first conjunct of
`boundExprKParams_dominates`. -/
theorem boundExprK_dominates {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    LawvereERKSim.compileER_runtime e v ≤ (boundExprK e).interp v := by
  rw [boundExprK_interp]
  exact (boundExprKParams_dominates e v).1

end GebLean
