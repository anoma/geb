import GebLean.LawvereKSim
import GebLean.LawvereKSimPolynomialBound
import GebLean.Utilities.ERAMajorants
import GebLean.Utilities.ERArith
import GebLean.Utilities.Tower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

/-!
# K^sim majorization theorems (Tourlakis 2018 §0.1.0.10)

For every `f : KMor1 a` with `f.level ≤ n` (where `n ≤ 2`),
this module produces a Lean-computable `(r, offset) : ℕ × ℕ`
such that
`∀ v : Fin a → ℕ,
  f.interp v ≤ (ERMor1.A_n_iter r).interp ![vMax v + offset]`.

Three deliverables:

- `KMor1.majorize_one : KMor1 a → f.level ≤ 1 → ℕ × ℕ`
  plus `majorize_by_A_one_iter` (level-≤1 case in A_1).
- `KMor1.majorize : KMor1 a → f.level ≤ 2 → ℕ × ℕ` plus
  `majorize_by_A_two_iter` (level-≤2 case in A_2).
- `KMor1.majorize_by_componentBound` step-5 bridge lemma
  feeding `simultaneousBoundedRec_interp_correct`.

ER-side helpers `sumCtxER`, `sumCtxERPlusOffset` named
composites support the bridge.

See
`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`
and master design §3.4 / §3.5 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
Cross-reference network:
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
-/

namespace GebLean

/-- Maximum of a `Fin a → ℕ` family.  Matches the
`Finset.sup` form returned by
`KMor1.linearBound_dominates`.  Private to this file. -/
private abbrev vMax {a : ℕ} (v : Fin a → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin a)).sup v

/-- For any `i : Fin a`, the entry `v i` is bounded by
`vMax v`.  One-line `Finset.le_sup`. -/
private theorem vMax_apply_le {a : ℕ} (v : Fin a → ℕ)
    (i : Fin a) : v i ≤ vMax v :=
  Finset.le_sup (s := (Finset.univ : Finset (Fin a)))
    (f := v) (Finset.mem_univ i)

/-- If every entry is bounded by `M`, so is `vMax v`.
Wraps `Finset.sup_le`. -/
private theorem vMax_le_of_pointwise {a : ℕ}
    (v : Fin a → ℕ) (M : ℕ) (h : ∀ i, v i ≤ M) :
    vMax v ≤ M :=
  Finset.sup_le (fun i _ => h i)

/-- Maximum-over-cons identity:
`vMax (Fin.cons n v) = max n (vMax v)`. -/
private theorem vMax_cons {a : ℕ} (n : ℕ) (v : Fin a → ℕ) :
    vMax (Fin.cons n v) = max n (vMax v) := by
  apply le_antisymm
  · apply vMax_le_of_pointwise
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]
      exact le_max_left _ _
    · intro j
      simp only [Fin.cons_succ]
      exact le_trans (vMax_apply_le v j) (le_max_right _ _)
  · apply max_le
    · have h := vMax_apply_le (Fin.cons n v) 0
      simpa only [Fin.cons_zero] using h
    · apply vMax_le_of_pointwise
      intro j
      have h := vMax_apply_le (Fin.cons n v) j.succ
      simpa only [Fin.cons_succ] using h

namespace ERMor1

/-- Sum dominates max: `vMax v ≤ (sumCtxER n).interp v`.
Thin wrapper around the pre-existing
`ERMor1.maxCtx_le_interp_sumCtxER` from
`LawvereERBoundComputable.lean`, exposed under the `vMax`
naming for consistency with this module's downstream
consumers.  Master design §3.5. -/
theorem vMax_le_sumCtxER {n : ℕ} (v : Fin n → ℕ) :
    (Finset.univ : Finset (Fin n)).sup v ≤
      (sumCtxER n).interp v :=
  ERMor1.maxCtx_le_interp_sumCtxER v

/-- n-ary sum plus a constant offset:
`(sumCtxERPlusOffset n offset).interp v
  = (∑ i, v i) + offset`.
Master design §3.5 lines 1108-1113.  Step-5 plug-in for
`simultaneousBoundedRec`'s componentBound slot. -/
def sumCtxERPlusOffset (n offset : ℕ) : ERMor1 n :=
  ERMor1.comp ERMor1.addN fun i => match i with
    | ⟨0, _⟩ => sumCtxER n
    | ⟨1, _⟩ => ERMor1.natN n offset

/-- Closed-form interpretation:
`(sumCtxERPlusOffset n offset).interp v
  = (∑ i, v i) + offset`.  Master design §3.5. -/
@[simp] theorem interp_sumCtxERPlusOffset
    (n offset : ℕ) (v : Fin n → ℕ) :
    (sumCtxERPlusOffset n offset).interp v
      = (∑ i, v i) + offset := by
  unfold sumCtxERPlusOffset
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_natN, interp_sumCtxER]

/-- Sum-plus-offset dominates `vMax v + offset`. -/
theorem vMax_add_offset_le_sumCtxERPlusOffset
    {n : ℕ} (offset : ℕ) (v : Fin n → ℕ) :
    (Finset.univ : Finset (Fin n)).sup v + offset
      ≤ (sumCtxERPlusOffset n offset).interp v := by
  rw [interp_sumCtxERPlusOffset, ← interp_sumCtxER]
  exact Nat.add_le_add_right (vMax_le_sumCtxER v) offset

end ERMor1

/-- Adding an offset commutes past a tower (loosely):
`tower b x + d ≤ tower b (x + d)` for all `b, x, d ≥ 0`.
Used by `tower_compose_offsets` to absorb the outer
offset of a `tower a (tower b ... + offset)` shape. -/
private theorem tower_add_offset_le (b x d : ℕ) :
    tower b x + d ≤ tower b (x + d) := by
  induction b with
  | zero => simp only [tower_zero, le_refl]
  | succ b ih =>
      change 2 ^ tower b x + d ≤ 2 ^ tower b (x + d)
      have h_pow_ge : d + 1 ≤ 2 ^ d := by
        have := Nat.lt_two_pow_self (n := d)
        omega
      have h_pos : 1 ≤ 2 ^ tower b x :=
        Nat.one_le_pow _ _ (by omega)
      have h_dle : d ≤ 2 ^ tower b x * d :=
        Nat.le_mul_of_pos_left _ h_pos
      have h_mul : 2 ^ tower b x + d
                     ≤ 2 ^ tower b x * 2 ^ d := by
        calc 2 ^ tower b x + d
            ≤ 2 ^ tower b x + 2 ^ tower b x * d :=
              Nat.add_le_add_left h_dle _
          _ = 2 ^ tower b x * (1 + d) := by ring
          _ ≤ 2 ^ tower b x * 2 ^ d :=
              Nat.mul_le_mul_left _
                (by omega : 1 + d ≤ 2 ^ d)
      calc 2 ^ tower b x + d
          ≤ 2 ^ tower b x * 2 ^ d := h_mul
        _ = 2 ^ (tower b x + d) := by rw [← Nat.pow_add]
        _ ≤ 2 ^ tower b (x + d) :=
            Nat.pow_le_pow_right (by omega) ih

/-- Two-stage tower composition with an outer offset:
`tower a (tower b (x + c) + d) ≤ tower (a + b) (x + c + d)`.
Used in the `comp` case of `majorize_by_A_two_iter` to
telescope two child A_2 bounds. -/
private theorem tower_compose_offsets
    {a b : ℕ} (x c d : ℕ) :
    tower a (tower b (x + c) + d)
      ≤ tower (a + b) (x + c + d) := by
  have h_inner : tower b (x + c) + d
                   ≤ tower b (x + c + d) :=
    tower_add_offset_le b (x + c) d
  have h_outer : tower a (tower b (x + c) + d)
                   ≤ tower a (tower b (x + c + d)) :=
    tower_mono_right a h_inner
  rw [tower_comp] at h_outer
  exact h_outer

/-- Translate a linear bound `c · x + d` into an `A_1^r`
bound, with explicit `r := max (Nat.log 2 (c + 1) + 1)
(Nat.log 2 (d + 2) + 1)`.  Master design §3.4 lines
884-898; Tourlakis 2018 §0.1.0.10. -/
theorem linearBound_le_A_one_iter (c d : ℕ) :
    let r := max (Nat.log 2 (c + 1) + 1)
                 (Nat.log 2 (d + 2) + 1)
    ∀ x, c * x + d ≤ (ERMor1.A_one_iter r).interp ![x] := by
  intro r x
  rw [ERMor1.interp_A_one_iter]
  have h_pow_c : c + 1 ≤ 2 ^ (Nat.log 2 (c + 1) + 1) := by
    have h := Nat.lt_pow_succ_log_self
                (b := 2) (by decide) (c + 1)
    omega
  have h_pow_d : d + 2 ≤ 2 ^ (Nat.log 2 (d + 2) + 1) := by
    have h := Nat.lt_pow_succ_log_self
                (b := 2) (by decide) (d + 2)
    omega
  have h_r1 : 2 ^ (Nat.log 2 (c + 1) + 1)
                ≤ 2 ^ (max (Nat.log 2 (c + 1) + 1)
                           (Nat.log 2 (d + 2) + 1)) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h_r2 : 2 ^ (Nat.log 2 (d + 2) + 1)
                ≤ 2 ^ (max (Nat.log 2 (c + 1) + 1)
                           (Nat.log 2 (d + 2) + 1)) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have h_c : c ≤ 2 ^ r := by
    calc c ≤ c + 1 := by omega
      _ ≤ 2 ^ (Nat.log 2 (c + 1) + 1) := h_pow_c
      _ ≤ 2 ^ r := h_r1
  have h_d : d + 2 ≤ 2 ^ (r + 1) := by
    calc d + 2 ≤ 2 ^ (Nat.log 2 (d + 2) + 1) := h_pow_d
      _ ≤ 2 ^ r := h_r2
      _ ≤ 2 ^ (r + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  have h_pow_pos : 1 ≤ 2 ^ (r + 1) :=
    Nat.one_le_pow _ _ (by omega)
  simp only [Matrix.cons_val_zero]
  have h_mul : c * x ≤ 2 ^ r * x :=
    Nat.mul_le_mul_right _ h_c
  omega

/-- γ.2 closed-form bound: `A_1^k(x) ≤ 2^{k+1} · (x + 1)`.
Master design §3.4 lines 1015-1019. -/
theorem A_one_iter_le_two_pow_succ (k x : ℕ) :
    (ERMor1.A_one_iter k).interp ![x]
      ≤ 2 ^ (k + 1) * (x + 1) := by
  rw [ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have h_succ : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [Nat.pow_succ]; ring
  have h_pow_pos : 1 ≤ 2 ^ k :=
    Nat.one_le_pow _ _ (by omega)
  rw [h_succ]
  ring_nf
  omega

/-- γ.3 cross-family bound: `2^{k+1} · (x + 1) ≤
tower 2 (x + k + 2)`.  Master design §3.4 lines
1027-1029. -/
theorem two_pow_succ_mul_succ_le_tower_two (k x : ℕ) :
    2 ^ (k + 1) * (x + 1) ≤ tower 2 (x + k + 2) := by
  have h_succ_le : x + 1 ≤ 2 ^ (x + 1) :=
    le_two_pow_self (x + 1)
  have h_step1 : 2 ^ (k + 1) * (x + 1)
                   ≤ 2 ^ (k + 1) * 2 ^ (x + 1) :=
    Nat.mul_le_mul_left _ h_succ_le
  have h_step2 : 2 ^ (k + 1) * 2 ^ (x + 1)
                   = 2 ^ (k + x + 2) := by
    rw [← Nat.pow_add]; ring_nf
  have h_step3 : k + x + 2 ≤ 2 ^ (k + x + 2) :=
    le_two_pow_self _
  have h_step4 : 2 ^ (k + x + 2) ≤ 2 ^ (2 ^ (x + k + 2)) := by
    apply Nat.pow_le_pow_right (by omega)
    have heq : k + x + 2 = x + k + 2 := by ring
    rw [← heq]
    exact h_step3
  calc 2 ^ (k + 1) * (x + 1)
      ≤ 2 ^ (k + 1) * 2 ^ (x + 1) := h_step1
    _ = 2 ^ (k + x + 2) := h_step2
    _ ≤ 2 ^ (2 ^ (x + k + 2)) := h_step4
    _ = tower 2 (x + k + 2) := by
        simp only [tower_succ, tower_zero]

/-- Combined cross-family bound: `A_1^k(x) ≤ A_2^2(x + k + 2)`.
Master design §3.4 lines 1015-1029; Tourlakis 2018
§0.1.0.10.  Used by the `raise` case of
`majorize_by_A_two_iter`. -/
theorem A_one_iter_le_A_two_iter_two (k x : ℕ) :
    (ERMor1.A_one_iter k).interp ![x]
      ≤ (ERMor1.A_two_iter 2).interp ![x + k + 2] := by
  rw [ERMor1.interp_A_two_iter]
  simp only [Matrix.cons_val_zero]
  exact le_trans (A_one_iter_le_two_pow_succ k x)
    (two_pow_succ_mul_succ_le_tower_two k x)

/-- γ.5 parametric cross-family bound: when the A_1
exponent depends linearly on `m`, the result still fits
inside an A_2^2 with constant tower height and additive
offset linear in `r_H, r_G`.  Master design §3.4 lines
1027-1029.  Load-bearing for the level-2 simrec case. -/
theorem A_one_iter_linear_le_A_two_iter_two
    (r_H r_G m : ℕ) :
    (ERMor1.A_one_iter (r_H + m * r_G)).interp ![m]
      ≤ (ERMor1.A_two_iter 2).interp
          ![m + r_H + r_G + 2] := by
  rw [ERMor1.interp_A_two_iter]
  simp only [Matrix.cons_val_zero]
  have h_step_a :
      (ERMor1.A_one_iter (r_H + m * r_G)).interp ![m]
        ≤ 2 ^ (r_H + m * r_G + 1) * (m + 1) :=
    A_one_iter_le_two_pow_succ (r_H + m * r_G) m
  have h_int :
      r_H + m * r_G + 1 ≤ (r_H + r_G + 1) * (m + 1) := by
    have h_expand :
        (r_H + r_G + 1) * (m + 1) =
          r_H * m + r_H + m * r_G + r_G + m + 1 := by
      ring
    rw [h_expand]
    omega
  have h_step_b :
      2 ^ (r_H + m * r_G + 1) * (m + 1)
        ≤ 2 ^ ((r_H + r_G + 2) * (m + 1)) := by
    have h_pow := Nat.pow_le_pow_right
                    (show 1 ≤ 2 by omega) h_int
    have h_succ : m + 1 ≤ 2 ^ (m + 1) :=
      le_two_pow_self (m + 1)
    calc 2 ^ (r_H + m * r_G + 1) * (m + 1)
        ≤ 2 ^ ((r_H + r_G + 1) * (m + 1)) * (m + 1) :=
          Nat.mul_le_mul_right _ h_pow
      _ ≤ 2 ^ ((r_H + r_G + 1) * (m + 1))
          * 2 ^ (m + 1) :=
          Nat.mul_le_mul_left _ h_succ
      _ = 2 ^ ((r_H + r_G + 1) * (m + 1) + (m + 1)) := by
          rw [← Nat.pow_add]
      _ ≤ 2 ^ ((r_H + r_G + 2) * (m + 1)) := by
          apply Nat.pow_le_pow_right (by omega)
          have h_eq :
              (r_H + r_G + 2) * (m + 1)
                = (r_H + r_G + 1) * (m + 1) + (m + 1) := by
            ring
          rw [h_eq]
  have h_factor_le :
      r_H + r_G + 2 ≤ 2 ^ (r_H + r_G + 1) := by
    have h_lt : r_H + r_G + 1 < 2 ^ (r_H + r_G + 1) :=
      Nat.lt_two_pow_self
    omega
  have h_step_c :
      (r_H + r_G + 2) * (m + 1)
        ≤ 2 ^ (r_H + r_G + 1) * 2 ^ (m + 1) := by
    calc (r_H + r_G + 2) * (m + 1)
        ≤ 2 ^ (r_H + r_G + 1) * (m + 1) :=
          Nat.mul_le_mul_right _ h_factor_le
      _ ≤ 2 ^ (r_H + r_G + 1) * 2 ^ (m + 1) :=
          Nat.mul_le_mul_left _
            (le_two_pow_self (m + 1))
  have h_step_d :
      2 ^ (r_H + r_G + 1) * 2 ^ (m + 1)
        = 2 ^ (m + r_H + r_G + 2) := by
    rw [← Nat.pow_add]; ring_nf
  have h_outer :
      2 ^ ((r_H + r_G + 2) * (m + 1))
        ≤ 2 ^ (2 ^ (m + r_H + r_G + 2)) := by
    apply Nat.pow_le_pow_right (by omega)
    calc (r_H + r_G + 2) * (m + 1)
        ≤ 2 ^ (r_H + r_G + 1) * 2 ^ (m + 1) := h_step_c
      _ = 2 ^ (m + r_H + r_G + 2) := h_step_d
  have h_tower :
      2 ^ (2 ^ (m + r_H + r_G + 2))
        = tower 2 (m + r_H + r_G + 2) := by
    simp only [tower_succ, tower_zero]
  calc (ERMor1.A_one_iter (r_H + m * r_G)).interp ![m]
      ≤ 2 ^ (r_H + m * r_G + 1) * (m + 1) := h_step_a
    _ ≤ 2 ^ ((r_H + r_G + 2) * (m + 1)) := h_step_b
    _ ≤ 2 ^ (2 ^ (m + r_H + r_G + 2)) := h_outer
    _ = tower 2 (m + r_H + r_G + 2) := h_tower

/-- `A_one_iter` composes additively in the iteration count:
`A_1^a(A_1^b(x)) = A_1^{a+b}(x)`.  Master design §3.4 lines
994-1007 (used implicitly in the M_n closed-form inductive
proof). -/
theorem A_one_iter_compose (a b x : ℕ) :
    (ERMor1.A_one_iter a).interp
        ![(ERMor1.A_one_iter b).interp ![x]]
      = (ERMor1.A_one_iter (a + b)).interp ![x] := by
  rw [ERMor1.interp_A_one_iter, ERMor1.interp_A_one_iter,
      ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have hpa : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by omega)
  have hpb : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by omega)
  have h3 : 2 ^ (a + b) = 2 ^ a * 2 ^ b :=
    Nat.pow_add 2 a b
  have h4 : 2 ^ (a + b + 1) = 2 * (2 ^ a * 2 ^ b) := by
    rw [Nat.pow_succ, h3]; ring
  have h5 : 2 ^ (b + 1) = 2 * 2 ^ b := by
    rw [Nat.pow_succ]; ring
  have h6 : 2 ^ (a + 1) = 2 * 2 ^ a := by
    rw [Nat.pow_succ]; ring
  rw [h3, h4, h5, h6]
  have hdist :
      2 ^ a * (2 ^ b * x + (2 * 2 ^ b - 2))
        = 2 ^ a * 2 ^ b * x
            + 2 ^ a * (2 * 2 ^ b - 2) := by
    ring
  rw [hdist]
  have hbridge :
      2 ^ a * (2 * 2 ^ b - 2)
        = 2 * (2 ^ a * 2 ^ b) - 2 * 2 ^ a := by
    rw [Nat.mul_sub _ (2 * 2 ^ b) 2]
    ring_nf
  rw [hbridge]
  have h2ab_ge : 2 * 2 ^ a ≤ 2 * (2 ^ a * 2 ^ b) := by
    apply Nat.mul_le_mul_left
    have : 2 ^ a * 1 ≤ 2 ^ a * 2 ^ b :=
      Nat.mul_le_mul_left _ hpb
    omega
  omega

/-- `A_1^k` dominates the identity at every `x`:
`x ≤ (A_one_iter k).interp ![x]`.  Used in §6.2's step
bullet to bound the recursion variable `n` by an
`A_1`-iterate. -/
theorem self_le_A_one_iter (k x : ℕ) :
    x ≤ (ERMor1.A_one_iter k).interp ![x] := by
  rw [ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have h_pow_pos : 1 ≤ 2 ^ k :=
    Nat.one_le_pow _ _ (by omega)
  have h_mul : x ≤ 2 ^ k * x :=
    Nat.le_mul_of_pos_left _ h_pow_pos
  omega

/-- `A_1^k` is monotone in the iteration count for fixed
input.  Used in §6.3's simrec bullet to lift the exponent
from `r_H + (v 0) · r_G` to `r_H + (vMax v) · r_G` before
applying §4.5. -/
theorem A_one_iter_mono_left {k₁ k₂ x : ℕ} (h : k₁ ≤ k₂) :
    (ERMor1.A_one_iter k₁).interp ![x]
      ≤ (ERMor1.A_one_iter k₂).interp ![x] := by
  rw [ERMor1.interp_A_one_iter, ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have h_pow_k : 2 ^ k₁ ≤ 2 ^ k₂ :=
    Nat.pow_le_pow_right (by omega) h
  have h_pow_succ : 2 ^ (k₁ + 1) ≤ 2 ^ (k₂ + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h_mul : 2 ^ k₁ * x ≤ 2 ^ k₂ * x :=
    Nat.mul_le_mul_right _ h_pow_k
  have h_pow_pos₁ : 1 ≤ 2 ^ (k₁ + 1) :=
    Nat.one_le_pow _ _ (by omega)
  have h_pow_pos₂ : 1 ≤ 2 ^ (k₂ + 1) :=
    Nat.one_le_pow _ _ (by omega)
  omega

/-- Level-≤1 majorize witness: returns `(r, offset)` such
that `f.interp v ≤ A_1^r (vMax v + offset)`.  Master design
§3.4.  Wrapper around `KMor1.linearBound` plus γ.1.  Offset
is uniformly `0` because γ.1 produces an A_1^r bound with
no input offset. -/
def KMor1.majorize_one : {a : ℕ} → (f : KMor1 a) →
    f.level ≤ 1 → ℕ × ℕ :=
  fun f h =>
    let p := KMor1.linearBound f h
    let r := max (Nat.log 2 (p.1 + 1) + 1)
                 (Nat.log 2 (p.2 + 2) + 1)
    (r, 0)

/-- Level-≤1 majorization (Tourlakis 2018 §0.1.0.10
restricted to level 1).  Master design §3.4. -/
theorem KMor1.majorize_by_A_one_iter
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
    (v : Fin a → ℕ) :
    f.interp v ≤
      (ERMor1.A_one_iter
        (KMor1.majorize_one f h).1).interp
          ![vMax v + (KMor1.majorize_one f h).2] := by
  unfold KMor1.majorize_one
  simp only [Nat.add_zero]
  set p := KMor1.linearBound f h with hp
  have h_dom :
      f.interp v ≤ p.1 * vMax v + p.2 :=
    KMor1.linearBound_dominates f h v
  exact le_trans h_dom (linearBound_le_A_one_iter p.1 p.2 _)

/-- `A_one_iter` is monotone in its input: increasing `x`
weakly increases `(A_one_iter k).interp ![x]`.  Used in the
input-monotonicity step of `simrecVec_le_A_one_iter`. -/
private theorem A_one_iter_mono_input (k : ℕ)
    {x₁ x₂ : ℕ} (hx : x₁ ≤ x₂) :
    (ERMor1.A_one_iter k).interp ![x₁]
      ≤ (ERMor1.A_one_iter k).interp ![x₂] := by
  rw [ERMor1.interp_A_one_iter, ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have h_mul : 2 ^ k * x₁ ≤ 2 ^ k * x₂ :=
    Nat.mul_le_mul_left _ hx
  omega

/-- Closed-form bound on every component of
`KMor1.simrecVec` at step `n`: bounded by
`A_1^{r_H + n*r_G}(max n (vMax params))` whenever the base
and step families admit per-call A_1 bounds with exponents
`r_H` and `r_G` respectively.  Master design lines 985-1007;
Tourlakis 2018 §0.1.0.10 proof of the level-2 case. -/
theorem KMor1.simrecVec_le_A_one_iter
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (_hh : ∀ j, (h_fam j).level ≤ 1)
    (_hg : ∀ j, (g_fam j).level ≤ 1)
    (r_H r_G : ℕ)
    (hbase : ∀ j x,
      (h_fam j).interp x
        ≤ (ERMor1.A_one_iter r_H).interp ![vMax x])
    (hstep : ∀ j y,
      (g_fam j).interp y
        ≤ (ERMor1.A_one_iter r_G).interp ![vMax y])
    (params : Fin a → ℕ) (n : ℕ) :
    ∀ j,
      KMor1.simrecVec h_fam g_fam params n j
        ≤ (ERMor1.A_one_iter (r_H + n * r_G)).interp
            ![max n (vMax params)] := by
  induction n with
  | zero =>
      intro j
      rw [KMor1.simrecVec_zero]
      simp only [Nat.zero_mul, Nat.add_zero]
      have h_zero_max : max 0 (vMax params) = vMax params := by
        omega
      rw [h_zero_max]
      exact hbase j params
  | succ n ih =>
      intro j
      rw [KMor1.simrecVec_succ]
      set stepCtx : Fin (a + 1 + (k + 1)) → ℕ :=
        fun idx =>
          if h₁ : idx.val < a + 1 then
            if _h₂ : idx.val = 0 then
              n
            else
              params ⟨idx.val - 1, by omega⟩
          else
            KMor1.simrecVec h_fam g_fam params n
              ⟨idx.val - (a + 1), by omega⟩
        with hStepCtx
      set M : ℕ := max n (vMax params) with hM
      have h_self_M : M ≤ (ERMor1.A_one_iter
          (r_H + n * r_G)).interp ![M] :=
        self_le_A_one_iter _ _
      have h_ctx_pointwise : ∀ idx, stepCtx idx
          ≤ (ERMor1.A_one_iter
              (r_H + n * r_G)).interp ![M] := by
        intro idx
        simp only [hStepCtx]
        by_cases h₁ : idx.val < a + 1
        · simp only [h₁, dite_true]
          by_cases h₂ : idx.val = 0
          · simp only [h₂, dite_true]
            calc n ≤ M := by simp only [hM]; omega
              _ ≤ _ := h_self_M
          · simp only [h₂, dite_false]
            have h_pl : params ⟨idx.val - 1, by omega⟩
                ≤ vMax params :=
              vMax_apply_le params _
            have h_pM : vMax params ≤ M := by
              simp only [hM]; omega
            exact le_trans (le_trans h_pl h_pM) h_self_M
        · simp only [h₁, dite_false]
          exact le_trans (ih _) (A_one_iter_mono_input _
            (by simp only [hM]; omega))
      have h_vmax_ctx : vMax stepCtx
          ≤ (ERMor1.A_one_iter
              (r_H + n * r_G)).interp ![M] :=
        vMax_le_of_pointwise stepCtx _ h_ctx_pointwise
      have h_step_apply :
          (g_fam j).interp stepCtx
            ≤ (ERMor1.A_one_iter r_G).interp ![vMax stepCtx] :=
        hstep j stepCtx
      have h_input_mono :
          (ERMor1.A_one_iter r_G).interp ![vMax stepCtx]
            ≤ (ERMor1.A_one_iter r_G).interp
                ![(ERMor1.A_one_iter
                    (r_H + n * r_G)).interp ![M]] :=
        A_one_iter_mono_input _ h_vmax_ctx
      have h_compose :
          (ERMor1.A_one_iter r_G).interp
              ![(ERMor1.A_one_iter
                  (r_H + n * r_G)).interp ![M]]
            = (ERMor1.A_one_iter
                (r_G + (r_H + n * r_G))).interp ![M] :=
        A_one_iter_compose r_G (r_H + n * r_G) M
      have h_exp_eq :
          r_G + (r_H + n * r_G) = r_H + (n + 1) * r_G := by
        ring
      have h_M_le :
          M ≤ max (n + 1) (vMax params) := by
        simp only [hM]; omega
      have h_outer_input_mono :
          (ERMor1.A_one_iter
              (r_H + (n + 1) * r_G)).interp ![M]
            ≤ (ERMor1.A_one_iter
                (r_H + (n + 1) * r_G)).interp
                  ![max (n + 1) (vMax params)] :=
        A_one_iter_mono_input _ h_M_le
      calc (g_fam j).interp stepCtx
          ≤ (ERMor1.A_one_iter r_G).interp ![vMax stepCtx] :=
            h_step_apply
        _ ≤ (ERMor1.A_one_iter r_G).interp
              ![(ERMor1.A_one_iter
                  (r_H + n * r_G)).interp ![M]] :=
            h_input_mono
        _ = (ERMor1.A_one_iter
              (r_G + (r_H + n * r_G))).interp ![M] :=
            h_compose
        _ = (ERMor1.A_one_iter
              (r_H + (n + 1) * r_G)).interp ![M] := by
            rw [h_exp_eq]
        _ ≤ (ERMor1.A_one_iter
              (r_H + (n + 1) * r_G)).interp
                ![max (n + 1) (vMax params)] :=
            h_outer_input_mono

/-- Level-≤2 majorize witness: returns `(r, offset)` such
that `f.interp v ≤ A_2^r (vMax v + offset)`.  Structural
recursion on `f`.  Master design §3.4 lines 916-937.

All atomic cases use uniform `r = 2`: tighter atom-level
`r` would force per-case upcasting at every comp/simrec
node.  The simrec offset matches master design lines
1051-1053 exactly: `r_2 = 2`, `offset_2 = r_H + r_G + 2`. -/
def KMor1.majorize : {a : ℕ} → (f : KMor1 a) →
    f.level ≤ 2 → ℕ × ℕ
  | _, .zero,         _ => (2, 2)
  | _, .succ,         _ => (2, 3)
  | _, .proj _,       _ => (2, 2)
  | _, .comp f gs,    h =>
      have hf  : f.level ≤ 2 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i => by
        unfold KMor1.level at h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          (le_trans (le_max_right _ _) h)
      let p_f  := KMor1.majorize f hf
      let r_g  := Fin.foldr _ (fun i acc =>
                    max acc
                      (KMor1.majorize (gs i) (hgs i)).1) 0
      let o_g  := Fin.foldr _ (fun i acc =>
                    max acc
                      (KMor1.majorize (gs i) (hgs i)).2) 0
      (p_f.1 + r_g, p_f.2 + o_g)
  | _, .raise f,      h =>
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact Nat.le_of_succ_le_succ h
      let p := KMor1.majorize_one f hf
      (2, p.1 + 2)
  | _, .simrec _ h_fam g_fam, hyp =>
      have hh : ∀ j, (h_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_left _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j)) this
      have hg : ∀ j, (g_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_right _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j)) this
      let r_H := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (h_fam j) (hh j)).1) 0
      let r_G := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (g_fam j) (hg j)).1) 0
      (2, r_H + r_G + 2)

/-- Level-≤2 majorization theorem (Tourlakis 2018
§0.1.0.10).  Master design §3.4 lines 916-937.  Structural
recursion mirroring `KMor1.majorize`. -/
theorem KMor1.majorize_by_A_two_iter :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
      (v : Fin a → ℕ),
      f.interp v ≤
        (ERMor1.A_two_iter
          (KMor1.majorize f h).1).interp
            ![vMax v + (KMor1.majorize f h).2]
  | _, .zero,         _, v => by
      simp only [KMor1.majorize, KMor1.interp_zero,
        ERMor1.interp_A_two_iter,
        Matrix.cons_val_zero]
      have h_self : vMax v + 2 ≤ tower 2 (vMax v + 2) :=
        self_le_tower 2 _
      omega
  | _, .succ,         _, v => by
      simp only [KMor1.majorize, KMor1.interp_succ,
        ERMor1.interp_A_two_iter,
        Matrix.cons_val_zero]
      have h_self : vMax v + 3 ≤ tower 2 (vMax v + 3) :=
        self_le_tower 2 _
      have h_v0 : v 0 ≤ vMax v := vMax_apply_le v 0
      omega
  | _, .proj i,       _, v => by
      simp only [KMor1.majorize, KMor1.interp_proj,
        ERMor1.interp_A_two_iter,
        Matrix.cons_val_zero]
      have h_self : vMax v + 2 ≤ tower 2 (vMax v + 2) :=
        self_le_tower 2 _
      have h_vi : v i ≤ vMax v := vMax_apply_le v i
      omega
  | _, .raise f,      h, v => by
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact Nat.le_of_succ_le_succ h
      simp only [KMor1.majorize, KMor1.interp_raise]
      set p := KMor1.majorize_one f hf with hp
      have h_dom_one :
          f.interp v ≤
            (ERMor1.A_one_iter p.1).interp ![vMax v + p.2] :=
        KMor1.majorize_by_A_one_iter f hf v
      have h_p2_zero : p.2 = 0 := by
        simp only [hp, KMor1.majorize_one]
      rw [h_p2_zero] at h_dom_one
      simp only [Nat.add_zero] at h_dom_one
      have h_cross :
          (ERMor1.A_one_iter p.1).interp ![vMax v]
            ≤ (ERMor1.A_two_iter 2).interp
                ![vMax v + p.1 + 2] :=
        A_one_iter_le_A_two_iter_two p.1 (vMax v)
      have h_input_eq :
          vMax v + p.1 + 2 = vMax v + (p.1 + 2) := by ring
      rw [h_input_eq] at h_cross
      exact le_trans h_dom_one h_cross
  | _, .comp f gs,    h, v => by
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i => by
        unfold KMor1.level at h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          (le_trans (le_max_right _ _) h)
      simp only [KMor1.majorize, KMor1.interp_comp]
      set p_f := KMor1.majorize f hf with hp_f
      set r_g := Fin.foldr _ (fun i acc =>
                   max acc
                     (KMor1.majorize (gs i) (hgs i)).1) 0
        with hr_g
      set o_g := Fin.foldr _ (fun i acc =>
                   max acc
                     (KMor1.majorize (gs i) (hgs i)).2) 0
        with ho_g
      have h_child : ∀ i,
          (gs i).interp v ≤
            (ERMor1.A_two_iter r_g).interp
              ![vMax v + o_g] := fun i => by
        have h_i :=
          KMor1.majorize_by_A_two_iter (gs i) (hgs i) v
        have h_r_le :
            (KMor1.majorize (gs i) (hgs i)).1 ≤ r_g := by
          simp only [hr_g]
          exact Fin.foldr_max_ge
            (fun j => (KMor1.majorize (gs j) (hgs j)).1) i
        have h_o_le :
            (KMor1.majorize (gs i) (hgs i)).2 ≤ o_g := by
          simp only [ho_g]
          exact Fin.foldr_max_ge
            (fun j => (KMor1.majorize (gs j) (hgs j)).2) i
        rw [ERMor1.interp_A_two_iter] at h_i ⊢
        simp only [Matrix.cons_val_zero] at h_i ⊢
        calc (gs i).interp v
            ≤ tower (KMor1.majorize (gs i) (hgs i)).1
                (vMax v
                  + (KMor1.majorize (gs i) (hgs i)).2) :=
              h_i
          _ ≤ tower r_g
                (vMax v
                  + (KMor1.majorize (gs i) (hgs i)).2) :=
              tower_mono_left h_r_le _
          _ ≤ tower r_g (vMax v + o_g) :=
              tower_mono_right r_g
                (Nat.add_le_add_left h_o_le _)
      have h_compose_max :
          vMax (fun i => (gs i).interp v) ≤
            (ERMor1.A_two_iter r_g).interp
              ![vMax v + o_g] := by
        apply vMax_le_of_pointwise
        intro i
        exact h_child i
      have h_outer :=
        KMor1.majorize_by_A_two_iter f hf
          (fun i => (gs i).interp v)
      rw [ERMor1.interp_A_two_iter] at h_outer
      simp only [Matrix.cons_val_zero] at h_outer
      rw [ERMor1.interp_A_two_iter] at h_compose_max
      simp only [Matrix.cons_val_zero] at h_compose_max
      rw [ERMor1.interp_A_two_iter]
      simp only [Matrix.cons_val_zero]
      calc f.interp (fun i => (gs i).interp v)
          ≤ tower p_f.1 (vMax (fun i => (gs i).interp v)
                          + p_f.2) := h_outer
        _ ≤ tower p_f.1 (tower r_g (vMax v + o_g)
                          + p_f.2) :=
            tower_mono_right _
              (Nat.add_le_add_right h_compose_max _)
        _ ≤ tower (p_f.1 + r_g) (vMax v + o_g + p_f.2) :=
            tower_compose_offsets _ _ _
        _ = tower (p_f.1 + r_g)
              (vMax v + (p_f.2 + o_g)) := by
            congr 1; ring
  | _, .simrec i h_fam g_fam, hyp, v => by
      have hh : ∀ j, (h_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_left _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j)) this
      have hg : ∀ j, (g_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_right _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j)) this
      simp only [KMor1.majorize, KMor1.interp_simrec]
      change KMor1.simrecVec h_fam g_fam (Fin.tail v) (v 0) i
               ≤ _
      set r_H := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (h_fam j)
                       (hh j)).1) 0
        with hr_H
      set r_G := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (g_fam j)
                       (hg j)).1) 0
        with hr_G
      have h_base : ∀ j x,
          (h_fam j).interp x
            ≤ (ERMor1.A_one_iter r_H).interp ![vMax x] := by
        intro j x
        have h_dom :=
          KMor1.majorize_by_A_one_iter (h_fam j) (hh j) x
        have h_r_le :
            (KMor1.majorize_one (h_fam j) (hh j)).1
              ≤ r_H := by
          simp only [hr_H]
          exact Fin.foldr_max_ge
            (fun l => (KMor1.majorize_one (h_fam l)
              (hh l)).1) j
        have h_offset_zero :
            (KMor1.majorize_one (h_fam j) (hh j)).2 = 0 :=
          rfl
        rw [h_offset_zero] at h_dom
        simp only [Nat.add_zero] at h_dom
        exact le_trans h_dom
          (A_one_iter_mono_left h_r_le)
      have h_step : ∀ j y,
          (g_fam j).interp y
            ≤ (ERMor1.A_one_iter r_G).interp ![vMax y] := by
        intro j y
        have h_dom :=
          KMor1.majorize_by_A_one_iter (g_fam j) (hg j) y
        have h_r_le :
            (KMor1.majorize_one (g_fam j) (hg j)).1
              ≤ r_G := by
          simp only [hr_G]
          exact Fin.foldr_max_ge
            (fun l => (KMor1.majorize_one (g_fam l)
              (hg l)).1) j
        have h_offset_zero :
            (KMor1.majorize_one (g_fam j) (hg j)).2 = 0 :=
          rfl
        rw [h_offset_zero] at h_dom
        simp only [Nat.add_zero] at h_dom
        exact le_trans h_dom
          (A_one_iter_mono_left h_r_le)
      have h_simrec_bound :=
        KMor1.simrecVec_le_A_one_iter
          h_fam g_fam hh hg r_H r_G
          h_base h_step (Fin.tail v) (v 0) i
      have h_cons_v : v = Fin.cons (v 0) (Fin.tail v) :=
        (Fin.cons_self_tail v).symm
      have h_max_eq :
          max (v 0) (vMax (Fin.tail v)) = vMax v := by
        conv_rhs => rw [h_cons_v]
        rw [vMax_cons]
      rw [h_max_eq] at h_simrec_bound
      have h_v0 : v 0 ≤ vMax v := vMax_apply_le v 0
      have h_exp_le :
          r_H + (v 0) * r_G ≤ r_H + vMax v * r_G :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_right _ h_v0) _
      have h_lift :
          (ERMor1.A_one_iter (r_H + (v 0) * r_G)).interp
              ![vMax v]
            ≤ (ERMor1.A_one_iter
                (r_H + vMax v * r_G)).interp ![vMax v] :=
        A_one_iter_mono_left h_exp_le
      have h_gamma :=
        A_one_iter_linear_le_A_two_iter_two
          r_H r_G (vMax v)
      rw [ERMor1.interp_A_two_iter]
      simp only [Matrix.cons_val_zero]
      rw [ERMor1.interp_A_two_iter] at h_gamma
      simp only [Matrix.cons_val_zero] at h_gamma
      calc KMor1.simrecVec h_fam g_fam (Fin.tail v) (v 0) i
          ≤ (ERMor1.A_one_iter (r_H + (v 0) * r_G)).interp
              ![vMax v] := h_simrec_bound
        _ ≤ (ERMor1.A_one_iter
              (r_H + vMax v * r_G)).interp ![vMax v] :=
            h_lift
        _ ≤ tower 2 (vMax v + r_H + r_G + 2) := h_gamma
        _ = tower 2 (vMax v + (r_H + r_G + 2)) := by
            congr 1; ring

/-- Step-5 plug-in: combines `majorize_by_A_two_iter` with
`sumCtxERPlusOffset` to produce the dominance hypothesis
shape that
`ERMor1.simultaneousBoundedRec_interp_correct` consumes.
Master design §3.5 lines 1099-1116. -/
theorem KMor1.majorize_by_componentBound
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
    (v : Fin a → ℕ) :
    let p := KMor1.majorize f h
    f.interp v ≤
      (ERMor1.comp (ERMor1.A_two_iter p.1)
        (fun _ : Fin 1 =>
          ERMor1.sumCtxERPlusOffset a p.2)).interp v := by
  intro p
  have h_dom :
      f.interp v ≤
        (ERMor1.A_two_iter p.1).interp ![vMax v + p.2] :=
    KMor1.majorize_by_A_two_iter f h v
  rw [ERMor1.interp_A_two_iter] at h_dom
  simp only [Matrix.cons_val_zero] at h_dom
  rw [ERMor1.interp_comp]
  rw [ERMor1.interp_A_two_iter]
  simp only [ERMor1.interp_sumCtxERPlusOffset]
  have h_sum_dom :
      vMax v + p.2
        ≤ (ERMor1.sumCtxER a).interp v + p.2 :=
    Nat.add_le_add_right (ERMor1.vMax_le_sumCtxER v) _
  rw [ERMor1.interp_sumCtxER] at h_sum_dom
  exact le_trans h_dom (tower_mono_right p.1 h_sum_dom)

end GebLean
