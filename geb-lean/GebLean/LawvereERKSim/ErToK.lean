import GebLean.LawvereERKSim.RuntimeBound
import GebLean.Utilities.KSimURMSimulator

/-!
# `erToK` — single-output ER-to-K^sim translator

This module realises the ⊇ direction of Tourlakis 2018
Corollary 0.1.0.44 at `n = 2`: every ER morphism is
representable as a depth-2 K^sim morphism with the same
input/output behaviour. The step-count is bounded by the
runtime-bound recipe from `RuntimeBound.lean`.

## Main definitions

- `erToK` : the single-output translator.

## Main statements

- `erToK_level` : level ≤ 2 for every input ER morphism.
- `erToK_interp` : interp-faithfulness.

## References

- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.44.
- Spec: `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`.

## Tags

ertok, simulator, interp, level
-/

namespace GebLean

/-- Single-output ER-to-K^sim translator: precompose the T3
simulator on `compileER e` with the `(a + 1)`-input fan-in that
supplies `(boundExprK e).interp v` in slot 0 (the step-count
input) and the input projections in slots `1, …, a`. Level ≤ 2
by `erToK_level`; interp-faithful by `erToK_interp`. -/
def erToK : {a : ℕ} → ERMor1 a → KMor1 a := fun {a} e =>
  KMor1.comp
    (KSimURMSimulator.simulate (LawvereERKSim.compileER e))
    (Fin.cons (α := fun _ => KMor1 a) (boundExprK e)
      (fun i : Fin a => KMor1.proj i))

-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc through `KSimURMSimulator.simulate_level`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
/-- `erToK e` has structural level at most 2. The outer `comp`
splits into the simulator head (level ≤ 2 by `simulate_level`)
and the `Fin (a + 1)`-indexed family: slot 0 is `boundExprK e`
(level ≤ 2 by `boundExprK_level`); slots `1, …, a` are
projections (level 0). -/
theorem erToK_level {a : ℕ} (e : ERMor1 a) :
    (erToK e).level ≤ 2 := by
  unfold erToK
  change max ((KSimURMSimulator.simulate
                (LawvereERKSim.compileER e)).level)
      (Fin.maxOfNat (a + 1)
        (fun j : Fin (a + 1) =>
          (Fin.cons (α := fun _ => KMor1 a) (boundExprK e)
            (fun i : Fin a => KMor1.proj i) j).level)) ≤ 2
  refine Nat.max_le.mpr
    ⟨KSimURMSimulator.simulate_level _, ?_⟩
  refine Fin.maxOfNat_le (fun j => ?_)
  refine Fin.cases ?_ ?_ j
  · -- slot 0: `boundExprK e`
    simpa using boundExprK_level e
  · intro i
    -- slot `i.succ`: projection, level 0
    change (KMor1.proj i).level ≤ 2
    exact Nat.zero_le _

-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc through `KSimURMSimulator.simulate_interp`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
/-- Interp-faithfulness of `erToK`: at every context `v`,
`(erToK e).interp v = e.interp v`. Threads `KMor1.interp_comp`,
`KSimURMSimulator.simulate_interp`, and
`LawvereERKSim.compileER_runFor`, discharging the runtime
hypothesis by `boundExprK_dominates`. -/
theorem erToK_interp {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (erToK e).interp v = e.interp v := by
  unfold erToK
  rw [KMor1.interp_comp]
  -- Identify the inner function with `Fin.cons ((boundExprK e).interp v) v`.
  have h_inner :
      (fun j : Fin (a + 1) =>
          (Fin.cons (α := fun _ => KMor1 a) (boundExprK e)
            (fun i : Fin a => KMor1.proj i) j).interp v)
        = Fin.cons (α := fun _ => ℕ) ((boundExprK e).interp v) v := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro i
      simp
  rw [h_inner, KSimURMSimulator.simulate_interp]
  exact LawvereERKSim.compileER_runFor e v
    ((boundExprK e).interp v) (boundExprK_dominates e v)

end GebLean
