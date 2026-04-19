import GebLean.LawvereERBound
import GebLean.LawvereERInterp
import GebLean.LawvereERQuot
import Mathlib.Data.Nat.Hyperoperation

/-!
# Tetration is Not Elementary Recursive

The tower-bounding theorem from `LawvereERBound.lean` yields a negative
result for tetration.  Since `n ↦ hyperoperation 4 2 n` coincides with
`n ↦ tower n 1`, and no fixed-height tower can dominate it, no
`ERMor1 1` term can compute tetration.  This strengthens the
Ackermann-based non-fullness from Phase 4f.1 by exhibiting a
primitive-recursive-but-not-elementary witness.
-/

namespace GebLean

open CategoryTheory

/-- Tetration of base 2 at height `n`: a tower of `n` twos applied
to 1.  Equivalent to `hyperoperation 4 2 n`. -/
def tetration (n : ℕ) : ℕ := tower n 1

/-- Tetration agrees with `hyperoperation 4 2`. -/
theorem tetration_eq_hyperoperation (n : ℕ) :
    tetration n = hyperoperation 4 2 n := by
  induction n with
  | zero =>
    change (1 : ℕ) = hyperoperation 4 2 0
    rw [show (4 : ℕ) = 1 + 3 from rfl,
      hyperoperation_ge_three_eq_one]
  | succ n ih =>
    change 2 ^ tower n 1 = hyperoperation 4 2 (n + 1)
    rw [hyperoperation_recursion, hyperoperation_three]
    change 2 ^ tower n 1 = 2 ^ hyperoperation 4 2 n
    rw [← ih]
    rfl

/-- Tetration strictly exceeds any fixed-height tower applied to
`(2K + 2) + 2` at argument `2K + 2`. -/
theorem tetration_gt_fixed_tower (K : ℕ) :
    tower K ((2 * K + 2) + 2) ≤ tetration (2 * K + 2) := by
  change tower K (2 * K + 4) ≤ tower (2 * K + 2) 1
  have h_comp : tower (2 * K + 2) 1 =
      tower K (tower (K + 2) 1) := by
    rw [tower_comp]
    congr 1
    omega
  rw [h_comp]
  apply tower_mono_right
  have h_tower_ge_pow : 2 ^ (K + 2) ≤ tower (K + 2) 1 :=
    two_pow_le_tower_one (K + 2)
  have h_pow_ge : 2 * K + 4 ≤ 2 ^ (K + 2) := by
    have h : 2 * (K + 2) ≤ 2 ^ (K + 2) := by
      match K with
      | 0 => decide
      | K + 1 => exact two_mul_le_two_pow (by omega)
    omega
  exact le_trans h_pow_ge h_tower_ge_pow

/-- Tetration is not elementary recursive: no `ERMor1 1` term
computes it. -/
theorem tetration_not_ER :
    ¬ ∃ t : ERMor1 1, ∀ x : ℕ,
      t.interp (fun _ => x) = tetration x := by
  rintro ⟨t, ht⟩
  obtain ⟨K, hK⟩ := t.exists_lt_tower
  have h_maxCtx : maxCtx (fun _ : Fin 1 => 2 * K + 2)
      = 2 * K + 2 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      exact Nat.le_refl _
    · exact le_maxCtx (fun _ : Fin 1 => 2 * K + 2) 0
  have h1 := hK (fun _ => 2 * K + 2)
  rw [ht (2 * K + 2)] at h1
  rw [h_maxCtx] at h1
  have h2 := tetration_gt_fixed_tower K
  omega

/-- The function `(Fin 1 → ℕ) → (Fin 1 → ℕ)` that maps the single
entry to its tetration. -/
def tetrationHom : (Fin 1 → ℕ) → (Fin 1 → ℕ) :=
  fun ctx _ => tetration (ctx 0)

/-- `erInterpFunctor` is not full, witnessed by tetration at
`1 → 1`.  Strengthens `erInterpFunctor_not_full` (Ackermann-based,
Phase 4f.1) with a primitive-recursive-but-not-elementary
witness. -/
theorem erInterpFunctor_not_full_via_tetration :
    ¬ erInterpFunctor.Full := by
  intro hfull
  have hsurj := Functor.map_surjective
    (F := erInterpFunctor)
    (X := (1 : LawvereERCat))
    (Y := (1 : LawvereERCat))
  obtain ⟨f, hf⟩ := hsurj tetrationHom
  obtain ⟨f_raw, hfr⟩ :=
    Quotient.exists_rep (s := erMorNSetoid 1 1) f
  have hinterp : ∀ ctx : Fin 1 → ℕ,
      f_raw.interp ctx = tetrationHom ctx := by
    intro ctx
    have hmap : erInterpFunctor.map f = tetrationHom := hf
    have heq1 : erInterpFunctor.map f =
        ERMorNQuo.interp f := rfl
    rw [heq1, ← hfr] at hmap
    have hctx := congrFun hmap ctx
    simp only [ERMorNQuo.interp, Quotient.lift_mk] at hctx
    exact hctx
  apply tetration_not_ER
  refine ⟨f_raw (0 : Fin 1), ?_⟩
  intro x
  have h := congrFun (hinterp (fun _ => x)) (0 : Fin 1)
  simp only [ERMorN.interp, tetrationHom] at h
  exact h

end GebLean
