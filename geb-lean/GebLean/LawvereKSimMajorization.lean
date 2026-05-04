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

end GebLean
