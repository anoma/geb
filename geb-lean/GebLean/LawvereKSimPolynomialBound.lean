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
- `kToER_polyBound_of_level_one` — bridge to ER
  polynomial bounds.
- `kSimPackedStep_polyBound` /
  `kSimPackedBase_polyBound` — specialized for the
  packed simrec step / base.
- `kSimTowerBound_dominates_inline` — final dominance
  assembly.

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

end GebLean
