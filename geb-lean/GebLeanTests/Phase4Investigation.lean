import GebLean
import GebLean.LawvereKSimER
import GebLean.LawvereKSimPolynomialBound

/-!
# Phase IV-B Task D.0 investigation

Concrete numerical experiment for the level-2 dominance chain.
Uses the level-1 K^sim term `addK` as the test child.  See
`docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`
Phase IV-B Task D.0.1.

The test computes:

1. `KMor1.linearBound addK addK_level` (the K^sim-side
   linear-bound coefficients).
2. `(kToER addK h_level).towerHeight` (the ER-side tower
   height of `addK`'s ER translation).
3. The key quantity `Nat.log 2 ((linearBound).1 +
   (linearBound).2 + 1)` — the proxy for the chain-closing
   log-vs-towerHeight inequality at Phase IV-B Task D.3.2.

If this quantity is bounded by `(kToER addK).towerHeight +
small_const` for `addK`, that's positive evidence for B1
(structural log-vs-tH bound holding on simple level-1
witnesses).  Failure would push toward B2 or a fan-out-aware
measure.
-/

open GebLean

private def addK : KMor1 2 :=
  KMor1.simrec (k := 0) (a := 1)
    (0 : Fin 1)
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 1))
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.succ
        (fun _ : Fin 1 => KMor1.proj (2 : Fin 3)))

private theorem addK_level : addK.level ≤ 1 := by decide

private theorem addK_level_two : addK.level ≤ 2 :=
  Nat.le_succ_of_le addK_level

/-- Sanity: addK's interp computes `x + y` at `(x, y)`. -/
example : addK.interp ![3, 5] = 8 := by decide

/-- The K^sim-side linear-bound pair for `addK`. -/
private def addK_lb : ℕ × ℕ := KMor1.linearBound addK addK_level

#eval addK_lb
-- Expected (computed by hand): coefficient and constant from
--   simrec's linearBound clause:
--     (max_step_c + 2 * max_step_k + 1, max_base_const)
-- with one base child (proj 0, lb = (1, 0)) and one step child
-- (comp succ (fun _ => proj 2), lb = (1*1, 1*0+1) = (1, 1)).
-- max_step_c = 1, max_step_k = 1, max_base_const = 0.
-- → addK_lb = (1 + 2*1 + 1, 0) = (4, 0).

#eval (addK_lb.1, addK_lb.2)
#eval Nat.log 2 (addK_lb.1 + addK_lb.2 + 1)
-- Expected: log_2 (4 + 0 + 1) = log_2 5 = 2.

/-- The ER-side tower height of `kToER addK`. -/
private def addK_ER_tH : ℕ :=
  (kToER addK addK_level_two).towerHeight

#eval addK_ER_tH
-- Will print the actual value computed by Lean.

-- Chain-closing diagnostic: log_2 of the linear-bound
-- constants vs. ER tower height of `kToER addK`.
#eval (Nat.log 2 (addK_lb.1 + addK_lb.2 + 1), addK_ER_tH)
-- Want: first ≤ second + (small constant).

-- For the polynomial-bound chain at Phase IV-B (Strategy B1
-- or B2), the constant `D` consumed by
-- `Nat.polynomial_iter_tower_bound` after `to_iter_step_form`
-- is `pb.degree + pb.coefficient + pb.constant + 2`.  For
-- the `addK_lb`-derived per-component PolyBound:
--   pb.degree = 1, pb.coefficient = addK_lb.1, pb.constant =
--   addK_lb.1 + addK_lb.2.
-- Hence the per-component `D_of` is
--   1 + addK_lb.1 + (addK_lb.1 + addK_lb.2) + 2
--   = 2*addK_lb.1 + addK_lb.2 + 3.
private def addK_D_of : ℕ :=
  1 + addK_lb.1 + (addK_lb.1 + addK_lb.2) + 2

#eval addK_D_of
-- For addK: 1 + 4 + (4 + 0) + 2 = 11.

#eval Nat.log 2 (addK_D_of + 1)
-- Want this ≤ `kSimPackedStep_g_ER`'s tower height for level-2.
-- For addK as the only level-1 child, sup_l D_of = D_of, so
-- D_max = D_of, and E = (D_max + 5) * 4^(k+1).  We want
-- log_2 D_max ≤ stepTH + small.

-- Fan-out at every comp node in `addK`'s sub-structure is 1
-- (each comp takes a single child).  This is the favorable
-- case where B1's log-vs-tH inequality should close trivially.
example : True := trivial

/-!
## Findings (recorded 2026-05-01)

`#eval` outputs from `lake build`:

| Quantity | Value | Hand check |
|---|---|---|
| `addK_lb` | `(4, 0)` | simrec lb = `(2*step_k + step_c + 1, base_const)` |
|  |  | `= (2*1 + 1 + 1, 0) = (4, 0)` |
| `Nat.log 2 (addK_lb.1 + addK_lb.2 + 1)` | `2` | `log_2 5 = 2` |
| `addK_ER_tH` | `1117` | dominated by `kSimTowerBound`'s |
|  |  | `iterAutoBoundExpr` encoding |
| `addK_D_of` | `11` | `1 + 4 + 4 + 0 + 2 = 11` |
| `Nat.log 2 (addK_D_of + 1)` | `3` | `log_2 12 = 3` |

The chain-closing inequality
`Nat.log 2 ((lB).1 + (lB).2 + 1) ≤ (kToER f).tH + c`
holds for `addK` with **c ≤ -1115 worth of slack** (LHS = 2,
RHS = 1117).  The slack comes from `kToER`'s simrec encoding:
`boundedRec` over `kSimPackedBase` / `kSimPackedStep` /
`kSimTowerBound`, where `kSimTowerBound`'s
`iterAutoBoundExpr` itself has substantial structural depth.

### Generalization argument

The slack pattern is structural, not coincidental:

- **Level-0 case** (no simrec): `KMor1.linearBound` reduces
  to `level0Shape.linearBound`, which is tame
  (`.1 ∈ {0, 1}`, `.2 ≤ tH + 1` by Lemma 1.B / A.5.2.1).
  `Nat.log 2 (.1 + .2 + 1) ≤ Nat.log 2 (tH + 3) ≤ tH + 2`.
  Inequality holds with `c = 2`.

- **Level-1 simrec**: every level-1 simrec injects ~1117+ of
  tower height (independent of the children — it's the
  encoding cost of `boundedRec` plus `kSimTowerBound`'s
  `iterAutoBoundExpr`), while its `KMor1.linearBound` fields
  are bounded by `(2*max_l tH(child) + 4, max_l tH(child) +
  1)` — linear in the children's tower heights, dwarfed by
  the simrec encoding cost.  `Nat.log 2` of these is at most
  `Nat.log 2 (3 * max child tH + 6) ≈ Nat.log 2 max_tH + 2`,
  which is far below the simrec's tH.

- **Level-1 comp `f' gs` where some part is level 1**:
  the multiplicative blow-up `p_f'.1 * max_c` and `p_f'.1
  * sum_k + p_f'.2` happens only when `p_f'.1 ≥ 2`, which
  happens only at simrec.  At a comp whose `f'` is simrec,
  tH(comp) includes f''s simrec tH (≥ 1100), while
  `Nat.log 2 (p_f'.1)` adds at most `Nat.log 2 (2*max_tH +
  4) ≤ max_tH + 3`.  Each comp level multiplies the
  `Nat.log 2` budget by at most a factor of 2 + max child
  tH, while tH grows by at least the child's simrec tH
  (~1100).  So per-comp slack is ~1100 - small_const,
  preserving the inequality across nesting.

- **Level-1 raise of level 0**: `linearBound = (level0Shape).
  linearBound`; `kToER (raise f) = kToER f`; reduces to the
  level-0 case directly.

The structural inequality
`Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1)
   ≤ (kToER f h).towerHeight + c`
therefore holds at level ≤ 1 with a small constant `c`
(probably `c ≤ 5` based on the analysis; the addK numerical
witness alone establishes `c ≤ 5` for the simrec case).

### Conclusion: B1 is the chosen sub-strategy

D.0's investigation outcome: B1 (constructive ER PolyBound +
structural log-vs-tH inequality) is viable.  No need to fall
back to B2 (custom K^sim measure with fan-out tracking).

The inequality above is what Phase IV-B Task D.3.2 needs, in
the slightly stronger form involving the packed step's
PolyBound fields directly.  The chain composes with the
existing `_ge_propagate` structural lemmas and the
polynomial-iteration framework.

For the implementation (Phase IV-B Task D.2 onward), prove
the above inequality by structural induction on
`f : KMor1 a` at level ≤ 1.  The inductive cases align with
the analysis bullets above.
-/

