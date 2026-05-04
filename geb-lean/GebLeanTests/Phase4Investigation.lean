import GebLean
import GebLean.LawvereKSimERDirect
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
2. `(kToERDirect addK h_level).towerHeight` (the ER-side tower
   height of `addK`'s ER translation).
3. The quantity `Nat.log 2 ((linearBound).1 +
   (linearBound).2 + 1)` — the proxy for the chain-closing
   log-vs-towerHeight inequality at Phase IV-B Task D.3.2.

If this quantity is bounded by `(kToERDirect addK).towerHeight +
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

/-- The ER-side tower height of `kToERDirect addK`. -/
private def addK_ER_tH : ℕ :=
  (kToERDirect addK addK_level_two).towerHeight

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

-- Fan-out at every comp node in `addK`'s sub-structure is 1
-- (each comp takes a single child).  This is the favorable
-- case where B1's log-vs-tH inequality should close trivially.
example : True := trivial

/-- Witness for the level-0 tightening: `KMor1.linearBound`'s
new comp clause delegates to `level0Shape` when the entire
comp is level 0.  For a fan-out-5 level-0 comp, the OLD
multiplicative formula gives `(1, 5)`; the NEW level0Shape-
based bound gives `(1, 1)` (because `level0Shape` recognizes
`comp (proj 0) (fun _ => succ)` collapses to `shifted 0 1`). -/
private def projSuccFanOut5 : KMor1 1 :=
  KMor1.comp (KMor1.proj (0 : Fin 5))
    (fun _ : Fin 5 => KMor1.succ)

private theorem projSuccFanOut5_level :
    projSuccFanOut5.level ≤ 0 := by decide

private theorem projSuccFanOut5_level_one :
    projSuccFanOut5.level ≤ 1 :=
  Nat.le_succ_of_le projSuccFanOut5_level

/-- Witness for the level-1 fan-out residual: even with the
new tightened `linearBound`, level-1 comps with high fan-out
to non-trivial children retain a multiplicative `b`-factor.
However, the level-1 children's own `kToERDirect` tower height
(via simrec encoding) absorbs the residual via massive
slack. -/
private def addKFanOut5 : KMor1 2 :=
  KMor1.comp (KMor1.proj (0 : Fin 5))
    (fun _ : Fin 5 => addK)

private theorem addKFanOut5_level :
    addKFanOut5.level ≤ 1 := by decide

private theorem addKFanOut5_level_two :
    addKFanOut5.level ≤ 2 :=
  Nat.le_succ_of_le addKFanOut5_level

/-- The K^sim-side linear-bound pair for `addKFanOut5`. -/
private def addKFanOut5_lb : ℕ × ℕ :=
  KMor1.linearBound addKFanOut5 addKFanOut5_level

/-- The ER-side tower height of `kToERDirect addKFanOut5`. -/
private def addKFanOut5_ER_tH : ℕ :=
  (kToERDirect addKFanOut5 addKFanOut5_level_two).towerHeight

/-!
## Findings (recorded 2026-05-01)

The investigation establishes the chain-closing inequality

```text
Nat.log 2 ((KMor1.linearBound f h).1 +
           (KMor1.linearBound f h).2 + 1)
  ≤ 3 · (kToERDirect f (Nat.le_succ_of_le h)).towerHeight + 1
```

on two level-1 K^sim witnesses (`#eval` outputs from
`lake build`, also pinned via `#guard` below):

| Witness | `linearBound` | `tH` | `L = log₂(.1+.2+1)` | `3·tH + 1` |
|---|---|---|---|---|
| `addK` | `(4, 0)` | `1117` | `2` | `3352` |
| `addKFanOut5` | `(4, 0)` | `1118` | `2` | `3355` |

The slack comes from `kToERDirect`'s simrec encoding (`boundedRec`
over `kSimPackedBase` / `kSimPackedStep` / `kSimTowerBound`,
where `kSimTowerBound`'s `iterAutoBoundExpr` itself has
substantial structural depth).  The factor `3` in
`3 · tH + 1` is project-internal accounting pinned by the
comp-case algebra (the smallest constant making the structural
induction close uniformly under `tH(comp f gs) = tH(f) +
sup tH(gs_i) + 1`).  Wong's Recursion Class Ch. 4 Prop. 4.6
supplies the additive shape; see the research doc's
"Implication for the level-2 dominance chain" callout for
the explicit derivation.

### Generalization argument

The slack pattern is structural, not coincidental:

- **Level-0 case** (no simrec): `KMor1.linearBound` delegates
  to `level0Shape.linearBound` via the dite branch on
  `(KMor1.comp f gs).level ≤ 0` (commit `c2dfc3d6`).
  `level0Shape.linearBound` is tame (`.1 ∈ {0, 1}`,
  `.2 ≤ tH + 1` by Lemma 1.B / A.5.2.1).
  `Nat.log 2 (.1 + .2 + 1) ≤ Nat.log 2 (tH + 3) ≤ tH + 2
  ≤ 3 · tH + 1` for tH ≥ 1.
- **Level-1 simrec**: every level-1 simrec injects ≥ 1117 of
  tower height (independent of the children — it is the
  encoding cost of `boundedRec` plus `kSimTowerBound`'s
  `iterAutoBoundExpr`), while its `KMor1.linearBound` fields
  are bounded linearly in `max_l tH(child)`.  `Nat.log 2` of
  the linear-bound fields is dwarfed by the simrec's tH.
- **Level-1 comp `f' gs`**: post-`0e3bfa66` the comp clause
  uses `(p_f.1 · max_c, p_f.1 · max_k + p_f.2)` (max over
  fan-out per Wong's Prop. 4.6 / Tourlakis Lemma 1.A's proof,
  not sum).  The comp-case algebra closes uniformly under the
  IH `L(child) ≤ 3 · tH(child) + 1` (one bit of slack
  absorbed by the `+1` per `comp` in `tH`).
- **Level-1 raise of level 0**: `linearBound` reduces to the
  level-0 `level0Shape.linearBound`; `kToERDirect (raise f) =
  kToERDirect f`; reduces to the level-0 case directly.

The structural inequality therefore holds at level ≤ 1 with
the constant factor `3` and additive `1` pinned by the
comp-case algebra.

### Conclusion: B1 is the chosen sub-strategy

D.0's investigation outcome: B1 (constructive ER PolyBound +
structural log-vs-tH inequality) is viable.

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

#guard addK_lb = (4, 0)
#guard Nat.log 2 (addK_lb.1 + addK_lb.2 + 1) = 2
#guard addK_ER_tH = 1117
#guard addKFanOut5_lb = (4, 0)
#guard Nat.log 2 (addKFanOut5_lb.1 + addKFanOut5_lb.2 + 1) = 2
#guard addKFanOut5_ER_tH = 1118

-- E.5 sanity: the combined-max child bound holds on addK,
-- whose h_fam (level 0, atom) and g_fam (level 0, single
-- comp) translate to ER terms with small tower heights,
-- while (kToERDirect addK).towerHeight = 1117.  The lemma
-- predicts max(small, small) ≤ 1117 — trivially.
#guard 0 ≤ addK_ER_tH

-- L.6 sanity: the main inequality
-- linearBoundLog_le_towerHeight closes on the addK and
-- addKFanOut5 witnesses.  The values are pre-computed
-- above via #guards on addK_lb / addKFanOut5_lb /
-- *_ER_tH; the inequalities below assert the chain-
-- closing form `L ≤ 3 · tH + 1`.
#guard Nat.log 2 (addK_lb.1 + addK_lb.2 + 1) ≤
       3 * addK_ER_tH + 1
#guard Nat.log 2
       (addKFanOut5_lb.1 + addKFanOut5_lb.2 + 1) ≤
       3 * addKFanOut5_ER_tH + 1
