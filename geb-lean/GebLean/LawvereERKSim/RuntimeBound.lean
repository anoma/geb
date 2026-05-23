import GebLean.LawvereERKSim.Compiler
import GebLean.LawvereERKSim.Top
import GebLean.Utilities.KArith
import GebLean.Utilities.Tower
import GebLean.LawvereKSim

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

## Main statements

- `boundExprKParams_dominates` (forthcoming) — joint runtime+value
  bound: `compileER_runtime e v ≤ tower mu_e (Fin.maxOfNat _ v + offset_e)`
  and `e.interp v ≤ tower mu_e (Fin.maxOfNat _ v + offset_e)`.

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
      (p_f.1 + mu_g + 6, p_f.2 + o_g + 4 * a + 8)
  | _, .bsum f  =>
      let p_f := boundExprKParams f
      (p_f.1 + 2, p_f.2 + 32)
  | _, .bprod f =>
      let p_f := boundExprKParams f
      (p_f.1 + 7, p_f.2 + 44)

end GebLean
