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

end GebLean
