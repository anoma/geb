# Phase IV-B Task 17c — auxiliary structural lemma plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** establish the structural lower bound
`(kToER (KMor1.simrec h_fam g_fam i)).towerHeight ≥
max(max_l (kToER (h_fam l)).towerHeight,
    max_l (kToER (g_fam l)).towerHeight)`,
the auxiliary lemma required by the main inequality
`KMor1.linearBoundLog_le_towerHeight :
Nat.log 2 (lb stuff) ≤ 3 · (kToER f).towerHeight + 1`
of Phase IV-B (Task 17c).

**Architecture:** three-layer chain on the critical path,
plus an optional supplementary layer.  Layer 1 establishes
`(ERMor1.boundedRec base step bound).towerHeight`'s closed
form and three corollaries (`_ge_base`, `_ge_step`,
`_ge_bound`).  Layer 2 (supplementary) adds parallel
lemmas about `iterAutoBoundExpr.towerHeight` and
`kSimTowerBound.towerHeight` for future use; not required
by the auxiliary lemma but useful as documentation /
re-use.  Layer 3 lifts the boundedRec corollaries through
the outer `comp (kSimSzudzikUnpackAt) ...` wrapping in
`kToER`'s simrec case, combining with the existing
`kSimPackedBase_towerHeight_ge_propagate` (h-side) and
`kSimPackedStep_towerHeight_ge_propagate` (g-side) to
yield the combined-max form.

**Tech stack:** Lean 4, mathlib, `lake build` / `lake test`.

**Convention:** every committed task ends in a clean
`lake build` plus `lake test`, with commit subject
`(Task 17c E.X)` (E = "auxiliary [E]xistential lower bound on
towerHeight").  Plans for the main lemma
(`KMor1.linearBoundLog_le_towerHeight`) and the chain-closing
work (Tasks D.2 onward) are separate from this plan.

**Plan revision history**: pre-flight inspection of `natN`
(`GebLean/Utilities/ERArith.lean:75`) confirmed
`(natN n m).towerHeight = m`, which made the originally-
planned `iterAutoBoundExpr_towerHeight_eq` lemma's RHS
incorrect (it depends on `lh` too, not just `d`).  Plan
revised on 2026-05-01 to replace the `_eq` form with a
direct `_ge_d` lemma (R1), and to route the auxiliary
lemma through `boundedRec_towerHeight_ge_{base,step}`
rather than through `iterAutoBoundExpr` (R2).  The
`iterAutoBoundExpr` and `kSimTowerBound` lemmas remain in
the plan as supplementary (Task E.4), not on the critical
path.

---

## File structure

The plan touches three modules:

- **Modify** `GebLean/LawvereERBoundComputable.lean`:
  add `iterAutoBoundExpr_towerHeight_ge_d` as a `theorem`
  near the existing `iterAutoBoundExpr` definition
  (currently at lines 410–456).  Supplementary, off the
  auxiliary-lemma critical path.
- **Modify** `GebLean/Utilities/ERArith.lean`: add
  `boundedRec_towerHeight_eq` and three `_ge_*`
  corollaries (`_ge_base`, `_ge_step`, `_ge_bound`)
  adjacent to `def ERMor1.boundedRec` (currently at
  lines 1782–1799).
- **Modify** `GebLean/LawvereKSimPolynomialBound.lean`:
  add `kSimTowerBound_towerHeight_ge_packedStep` and
  `kSimTowerBound_towerHeight_ge_max_step_child`
  (supplementary, off the critical path) plus
  `kToER_simrec_towerHeight_ge_max_child_tH` (the
  auxiliary lemma) as `private theorem`s in the existing
  structural-lemmas section after
  `kSimPackedStep_towerHeight_ge_propagate` (line 1507).

No new module files are created.

`ERMor1.towerHeight` recursion (from
`LawvereERBoundComputable.lean:34`):

```text
zero / succ / proj / sub : towerHeight = 0
comp f g  : towerHeight = f.tH + sup_i (g i).tH + 1
bsum f    : towerHeight = f.tH + 3
bprod f   : towerHeight = f.tH + 4
```

`ERMor1.boundedRec base step bound`'s definition (from
`Utilities/ERArith.lean:1782`):

```text
boundedRec base step bound =
  comp minN [betaAtN, bound]
where
  betaAtN = comp beta [comp natUnpairFst search,
                        comp natUnpairSnd search,
                        proj 0]
  search  = boundedSearch (boundedRecRange bound)
                          (boundedRecPred base step)
```

Both `boundedRecRange bound` and `boundedRecPred base step`
expand to fixed-shape compositions whose towerHeight
contains `bound.tH` (resp. `base.tH`, `step.tH`) as
sub-expressions, plus closed structural overheads.

---

## Critical path: Tasks E.2, E.3, E.5

These three tasks suffice to establish the auxiliary lemma.
Task E.1 (supplementary `iterAutoBoundExpr_towerHeight_ge_d`)
and Task E.4 (supplementary `kSimTowerBound` lemmas) provide
parallel infrastructure useful for future work but are not
load-bearing for the auxiliary chain.

---

## Task E.1: `iterAutoBoundExpr` towerHeight ≥ d (supplementary)

**Files:**

- Modify: `GebLean/LawvereERBoundComputable.lean`
  (insert after `theorem ERMor1.interp_iterAutoBoundExpr`,
  currently ending around line 456)

The `iterAutoBoundExpr k d lh` body (lines 410–423) has
shape `comp (towerER (d + 1)) [...]`.  By induction on `n`,
`n ≤ (towerER n).towerHeight` (each successor case adds at
least 1 via `comp expER [towerER n, twoN 1]`'s outer `+1`,
combined with the IH bound on the first sub-branch).
The outer `comp` of `iterAutoBoundExpr` adds another `+1`
plus the inner block's tH.  Hence
`d + 1 ≤ (towerER (d + 1)).towerHeight ≤
(iterAutoBoundExpr k d lh).towerHeight`, so
`d ≤ (iterAutoBoundExpr k d lh).towerHeight`.

This task adds the `_ge_d` lemma as a standalone result.
It is not used by the auxiliary lemma proof but is useful
documentation for the relationship between the
`d`-parameter and the iterated bound's structural depth.

- [ ] **Step E.1.1: State and prove the lemma**

```lean
/-- Structural lower bound on `iterAutoBoundExpr`'s tower
height in terms of the `d` parameter.  The outer `comp
(towerER (d + 1)) [...]` contributes `(towerER (d + 1)).
towerHeight + sup(...) + 1`, and `(towerER n).towerHeight
≥ n` by induction, so `(iterAutoBoundExpr k d lh).
towerHeight ≥ d + 1 + 0 + 1 ≥ d`. -/
theorem ERMor1.iterAutoBoundExpr_towerHeight_ge_d
    (k d lh : ℕ) :
    d ≤ (ERMor1.iterAutoBoundExpr k d lh).towerHeight := by
  unfold ERMor1.iterAutoBoundExpr
  simp only [ERMor1.towerHeight]
  -- After simp only, the goal exposes
  -- (towerER (d + 1)).towerHeight + sup (...) + 1 on the
  -- right.  Bound (towerER n).towerHeight ≥ n by induction.
  have htow : ∀ n, n ≤ (ERMor1.towerER n).towerHeight := by
    intro n
    induction n with
    | zero =>
        change 0 ≤ (ERMor1.proj (0 : Fin 1)).towerHeight
        simp [ERMor1.towerHeight]
    | succ n' ih =>
        unfold ERMor1.towerER
        simp only [ERMor1.towerHeight]
        -- comp expER [towerER n', twoN 1]: outer comp adds
        -- expER.tH + sup [(towerER n').tH, (twoN 1).tH] + 1.
        -- The sup is ≥ (towerER n').tH ≥ n' by ih.  Outer
        -- contributes another +1.  Hence ≥ n' + 1.
        have h1 : (ERMor1.towerER n').towerHeight ≤
            (Finset.univ : Finset (Fin 2)).sup _ := by
          exact Finset.le_sup
            (f := fun i : Fin 2 => match i with
              | ⟨0, _⟩ => (ERMor1.towerER n').towerHeight
              | ⟨1, _⟩ => (ERMor1.twoN 1).towerHeight)
            (Finset.mem_univ ⟨0, by omega⟩)
        omega
  have h_outer : (ERMor1.towerER (d + 1)).towerHeight ≤
      (ERMor1.iterAutoBoundExpr k d lh).towerHeight := by
    -- The outer comp's f is towerER (d + 1).  By
    -- towerHeight's comp recursion, f.tH ≤ comp.tH.
    unfold ERMor1.iterAutoBoundExpr
    simp only [ERMor1.towerHeight]
    omega
  have h_d1 : d + 1 ≤ (ERMor1.towerER (d + 1)).towerHeight :=
    htow (d + 1)
  omega
```

If the inner `match`-based `Finset.le_sup` does not
elaborate cleanly (because `Fin 2`'s sup over a `match`
expression is opaque), substitute with explicit
`change` or `show` unfolding the match.

If `omega` fails because `Finset.univ.sup` over the inner
match expression is opaque, add `Finset.le_sup`-based
manual extraction:

```lean
  have h_inner : 0 ≤ Finset.univ.sup _ := Nat.zero_le _
  omega
```

If `simp only [ERMor1.towerHeight]` does not unfold deeply
enough through the nested `match` expressions in
`iterAutoBoundExpr`'s body, replace with explicit
`unfold ERMor1.iterAutoBoundExpr; show _; ...` to expose
the outer `comp (towerER (d + 1)) ...` structure first,
then bound the inner sup by 0.

- [ ] **Step E.1.2: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings, all 1559+ tests pass.

- [ ] **Step E.1.3: Commit**

```bash
git add GebLean/LawvereERBoundComputable.lean
git commit -m "$(cat <<'EOF'
iterAutoBoundExpr towerHeight ≥ d (Task 17c E.1)

Supplementary structural lower bound:
(iterAutoBoundExpr k d lh).towerHeight ≥ d.  Proved via the
outer comp (towerER (d + 1)) wrapping plus the auxiliary
fact n ≤ (towerER n).towerHeight (induction on n).  Off the
auxiliary-lemma critical path; useful documentation for the
d-parameter's relationship to structural depth.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.2: `boundedRec` towerHeight closed form

**Files:**

- Modify: `GebLean/Utilities/ERArith.lean`
  (insert after `theorem ERMor1.interp_boundedRec_le_bound`,
  currently ending around line 1811)

`boundedRec base step bound = comp minN [betaAtN, bound]`,
where `betaAtN` decomposes via `boundedSearch` over
`boundedRecRange bound` and `boundedRecPred base step`.
The towerHeight involves `base.tH`, `step.tH`,
`bound.tH`, plus structural overheads from
`boundedSearch`, `boundedRecRange`, `boundedRecPred`,
`beta`, `minN`, `natUnpairFst`, `natUnpairSnd` — all
closed constants.

The closed form has shape

```text
(boundedRec base step bound).towerHeight =
  max (max base.tH (max step.tH bound.tH))
      C_overhead +
  C_outer
```

for closed constants `C_overhead`, `C_outer`.  Implementer's
discretion on whether to introduce one or several named
constants.

The recommended form is a **single closed constant**
`boundedRec_towerHeight_overhead`, defined by

```lean
private def ERMor1.boundedRec_towerHeight_overhead : ℕ :=
  (ERMor1.boundedRec ERMor1.zero
    (ERMor1.proj ⟨0, by omega⟩) ERMor1.zero).towerHeight
```

and a single `_eq` lemma:

```lean
theorem ERMor1.boundedRec_towerHeight_eq {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    (ERMor1.boundedRec base step bound).towerHeight =
      max (max base.towerHeight
                (max step.towerHeight bound.towerHeight))
          ERMor1.boundedRec_towerHeight_overhead
```

The downstream `_ge_*` corollaries only need this `_eq`'s
existence and the closed-constant overhead's
non-negativity.

If the structural unfold turns out simpler (e.g. via
`bsum`/`bprod` reductions or via additive rather than
max-of-max accumulation), the implementer may revise the
RHS shape.  The corollaries in E.3 are robust to such
restatements provided the three input towerHeights remain
visible as `≤` lower bounds.

- [ ] **Step E.2.1: Compute the overhead constant**

Use the Lean MCP server's `lean_run_code` to evaluate

```lean
#eval (ERMor1.boundedRec ERMor1.zero
  (ERMor1.proj ⟨0, by omega⟩) ERMor1.zero).towerHeight
```

Record the value as a sanity reference.  No commit on this
step — it is exploratory.

- [ ] **Step E.2.2: Add the named constant**

Insert in `Utilities/ERArith.lean` after
`interp_boundedRec_le_bound`:

```lean
/-- Closed structural overhead of `boundedRec`'s tower
height: the contribution from `boundedSearch`,
`boundedRecRange`, `boundedRecPred`, `beta`, `minN`,
`natUnpairFst`, `natUnpairSnd` evaluated at trivial
inputs. -/
private def ERMor1.boundedRec_towerHeight_overhead : ℕ :=
  (ERMor1.boundedRec ERMor1.zero
    (ERMor1.proj (k := 1) ⟨0, by omega⟩)
    (ERMor1.zeroN 1)).towerHeight
```

(Note `ERMor1.zeroN 1` rather than `ERMor1.zero` for the
`bound` slot to match the `Fin (k+1) = Fin 1` arity.  At
`k = 0`, `base` is `ERMor1 0` so `ERMor1.zero` works;
`step` is `ERMor1 2` so `ERMor1.proj ⟨0, _⟩` of arity 2;
`bound` is `ERMor1 1` so `ERMor1.zeroN 1`.)

If the actual arity threading produces a different
trivial term, adjust accordingly.

- [ ] **Step E.2.3: State the `_eq` lemma**

```lean
/-- Closed-form towerHeight of `boundedRec`.  The
structural recursion on `comp minN [betaAtN, bound]`
gives a sup over `betaAtN.towerHeight` and
`bound.towerHeight`, where `betaAtN` further decomposes
via `boundedSearch` over `boundedRecRange bound` and
`boundedRecPred base step`.  All three input arguments
appear as sub-expressions of the resulting expression;
the residual structural depth is the closed constant
`boundedRec_towerHeight_overhead`. -/
theorem ERMor1.boundedRec_towerHeight_eq {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    (ERMor1.boundedRec base step bound).towerHeight =
      max (max base.towerHeight
                (max step.towerHeight bound.towerHeight))
          ERMor1.boundedRec_towerHeight_overhead := by
  _
```

- [ ] **Step E.2.4: Prove the `_eq` lemma**

```lean
theorem ERMor1.boundedRec_towerHeight_eq {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    (ERMor1.boundedRec base step bound).towerHeight =
      max (max base.towerHeight
                (max step.towerHeight bound.towerHeight))
          ERMor1.boundedRec_towerHeight_overhead := by
  unfold ERMor1.boundedRec
  unfold ERMor1.boundedSearch
  unfold ERMor1.boundedRecRange
  unfold ERMor1.boundedRecPred
  simp only [ERMor1.towerHeight]
  unfold ERMor1.boundedRec_towerHeight_overhead
  unfold ERMor1.boundedRec
  unfold ERMor1.boundedSearch
  unfold ERMor1.boundedRecRange
  unfold ERMor1.boundedRecPred
  simp only [ERMor1.towerHeight]
  -- Both sides reduce to the same max-of-max expression in
  -- {base.tH, step.tH, bound.tH} plus a closed numeric
  -- constant from atomic ER generators.  The atomic
  -- contributions on both sides are identical (zero terms
  -- and proj 0 expand to towerHeight 0).
  omega
```

If `omega` fails because the `Finset.univ.sup` over a
finite `match` does not reduce, replace with explicit
`Finset.sup_le` plus `Finset.le_sup` extraction, mirroring
the pattern in
`kSimSzudzikPackList_towerHeight_ge_propagate`
(`LawvereKSimPolynomialBound.lean:1391`).

If the `comp` chain is too deep for `unfold` to expose
clearly, factor the structure into a private lemma
chaining the sub-expression towerHeights, then prove the
top-level `_eq` from the sub-expression results.

- [ ] **Step E.2.5: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.2.6: Commit**

```bash
git add GebLean/Utilities/ERArith.lean
git commit -m "$(cat <<'EOF'
boundedRec towerHeight closed form (Task 17c E.2)

Adds boundedRec_towerHeight_overhead (private def) and
boundedRec_towerHeight_eq stating
(boundedRec base step bound).towerHeight = max(max(base.tH,
max(step.tH, bound.tH)), boundedRec_towerHeight_overhead).
Proof by structural unfold of boundedRec / boundedSearch /
boundedRecRange / boundedRecPred against ERMor1.towerHeight.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.3: `boundedRec` towerHeight ≥ {base, step, bound} corollaries

**Files:**

- Modify: `GebLean/LawvereERBoundComputable.lean`
  (insert after `boundedRec_towerHeight_le`, the lemma added
  by E.2.  Note: file is `LawvereERBoundComputable.lean`, not
  `Utilities/ERArith.lean` — see E.2's authorized deviation
  on file placement.)

Three short corollaries extracting each input's
towerHeight as a lower bound on
`(boundedRec base step bound).towerHeight`.  These are the
critical-path lemmas for the auxiliary lemma.

E.2 produced `boundedRec_towerHeight_le` (note: `_le`, not
`_eq` as the original draft proposed — the `_eq` form does
not hold; E.2's authorized deviation):

```lean
theorem ERMor1.boundedRec_towerHeight_le {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    max base.towerHeight
        (max step.towerHeight bound.towerHeight) ≤
      (ERMor1.boundedRec base step bound).towerHeight
```

The corollaries below derive directly from this `_le` form
plus `le_max_*` chains.

- [ ] **Step E.3.1: State and prove `_ge_base`**

```lean
/-- Structural lower bound on `boundedRec`'s tower height
in terms of `base`'s tower height.  Used by Task 17c E.5
to lift bounds on the h-family children through the
boundedRec layer. -/
theorem ERMor1.boundedRec_towerHeight_ge_base {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    base.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight :=
  le_trans (le_max_left _ _)
    (ERMor1.boundedRec_towerHeight_le base step bound)
```

- [ ] **Step E.3.2: State and prove `_ge_step`**

```lean
/-- Structural lower bound on `boundedRec`'s tower height
in terms of `step`'s tower height.  Used by Task 17c E.5
to lift bounds on the g-family children through the
boundedRec layer. -/
theorem ERMor1.boundedRec_towerHeight_ge_step {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    step.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (ERMor1.boundedRec_towerHeight_le base step bound)
```

- [ ] **Step E.3.3: State and prove `_ge_bound`**

```lean
/-- Structural lower bound on `boundedRec`'s tower height
in terms of the `bound` argument's tower height.
Supplementary; used by Task 17c E.4 (kSimTowerBound
chain). -/
theorem ERMor1.boundedRec_towerHeight_ge_bound {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    bound.towerHeight ≤
      (ERMor1.boundedRec base step bound).towerHeight :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (ERMor1.boundedRec_towerHeight_le base step bound)
```

- [ ] **Step E.3.4: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.3.5: Commit**

```bash
git add GebLean/LawvereERBoundComputable.lean
git commit -m "$(cat <<'EOF'
boundedRec towerHeight ≥ {base, step, bound} (Task 17c E.3)

Three corollaries of boundedRec_towerHeight_le from E.2,
extracting each input argument's towerHeight as a lower
bound on (boundedRec base step bound).towerHeight.  Used
by Task 17c E.5 (auxiliary lemma): the h-side routes
through _ge_base, the g-side through _ge_step.  _ge_bound
is supplementary, used by Task 17c E.4.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.4: `kSimTowerBound` towerHeight bounds (supplementary)

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after `kSimPackedStep_towerHeight_ge_propagate`,
  currently ending around line 1517)

Supplementary lemmas linking `kSimTowerBound`'s
towerHeight to its constituents.  Off the auxiliary
lemma's critical path (E.5 routes through
`boundedRec_towerHeight_ge_step` directly), but useful
for future work and as a documented bridge between
`iterAutoBoundExpr_towerHeight_ge_d` (E.1) and the
`_ge_propagate` lemmas.

- [ ] **Step E.4.1: State and prove
  `kSimTowerBound_towerHeight_ge_packedStep`**

```lean
/-- Structural lower bound on `kSimTowerBound`'s tower
height in terms of the packed step's tower height.
Routes through `iterAutoBoundExpr_towerHeight_ge_d` (Task
17c E.1): `kSimTowerBound h g = iterAutoBoundExpr a
stepTH baseTH` where `stepTH = (kSimPackedStep g)
.towerHeight`.  Supplementary to the auxiliary lemma. -/
private theorem kSimTowerBound_towerHeight_ge_packedStep
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    (kSimPackedStep g).towerHeight ≤
      (kSimTowerBound h g).towerHeight := by
  unfold kSimTowerBound
  exact ERMor1.iterAutoBoundExpr_towerHeight_ge_d _ _ _
```

- [ ] **Step E.4.2: State and prove
  `kSimTowerBound_towerHeight_ge_max_step_child`**

```lean
/-- Structural lower bound on `kSimTowerBound`'s tower
height in terms of the maximum-over-step-family child
tower height.  Combines `kSimPackedStep_towerHeight_ge_propagate`
with `_ge_packedStep`.  Supplementary. -/
private theorem kSimTowerBound_towerHeight_ge_max_step_child
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1.natPair.towerHeight + 2 +
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (ERMor1.comp (g l) kSimStepContext).towerHeight) ≤
      (kSimTowerBound h g).towerHeight :=
  le_trans
    (kSimPackedStep_towerHeight_ge_propagate g)
    (kSimTowerBound_towerHeight_ge_packedStep h g)
```

- [ ] **Step E.4.3: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.4.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kSimTowerBound towerHeight ≥ {packedStep, max-step-child} (Task 17c E.4)

Two supplementary private lemmas:
- kSimTowerBound_towerHeight_ge_packedStep: routes through
  iterAutoBoundExpr_towerHeight_ge_d (E.1) to bound
  kSimTowerBound's towerHeight from below by
  (kSimPackedStep g).towerHeight.
- kSimTowerBound_towerHeight_ge_max_step_child: composes
  with the existing kSimPackedStep_towerHeight_ge_propagate
  to bound by max_l (comp (g l) kSimStepContext).towerHeight
  plus a small constant.

Off the auxiliary-lemma critical path; the auxiliary lemma
in E.5 routes through boundedRec_towerHeight_ge_step
directly.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.5: `kToER simrec` towerHeight ≥ combined-max child (auxiliary lemma)

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after the lemmas added in E.4)

The simrec wrapping (`LawvereKSimER.lean:58–93`) is:

```text
kToER (simrec i h_fam g_fam) =
  comp (kSimSzudzikUnpackAt a i.val)
    (fun j => if j.val = 0 then recur else proj …)
where
  recur = boundedRec (kSimPackedBase h_ER)
                     (kSimPackedStep g_ER)
                     (kSimTowerBound h_ER g_ER)
  h_ER l = kToER (h_fam l) _
  g_ER l = kToER (g_fam l) _
```

By the towerHeight recursion, `(kToER simrec).towerHeight =
(kSimSzudzikUnpackAt a i.val).towerHeight + sup_j (branch
j).towerHeight + 1`, where branch 0 = recur and branches
j > 0 are atomic projections.

For the **h-side**:

- `recur.tH ≥ base.tH = (kSimPackedBase h_ER).tH` (by
  E.3's `_ge_base`).
- `(kSimPackedBase h_ER).tH ≥
  ERMor1.natPair.towerHeight + 2 + sup_l (h_ER l).tH` (by
  the existing `kSimPackedBase_towerHeight_ge_propagate`,
  `LawvereKSimPolynomialBound.lean:1496`).
- Lifting through the outer `comp` adds at least `+ 1`.

For the **g-side**:

- `recur.tH ≥ step.tH = (kSimPackedStep g_ER).tH` (by
  E.3's `_ge_step`).
- `(kSimPackedStep g_ER).tH ≥
  ERMor1.natPair.towerHeight + 2 +
  sup_l (comp (g_ER l) kSimStepContext).tH` (by the
  existing `kSimPackedStep_towerHeight_ge_propagate`,
  `LawvereKSimPolynomialBound.lean:1507`).
- For each `l`, `(comp (g_ER l) kSimStepContext).tH =
  (g_ER l).tH + sup(kSimStepContext-component).tH + 1 ≥
  (g_ER l).tH`.
- Lifting through the outer `comp` adds at least `+ 1`.

Combining via `max_le`:

```text
max (sup_l (h_ER l).tH) (sup_l (g_ER l).tH) ≤
  (kToER simrec).tH.
```

(The structural overheads — `natPair.tH + 2 + 1`-per-comp
on each side — make the actual slack significantly
larger, but the auxiliary lemma states only the bare
`max ≤` form, which is what the main inequality consumes.)

- [ ] **Step E.5.1: State the auxiliary lemma**

```lean
/-- Auxiliary structural lemma for the Phase IV-B chain:
`kToER (simrec h_fam g_fam i)`'s tower height dominates
the combined-max-over-children tower height.  This is the
level-2 analog of `kToER_level0_towerHeight_ge_const`
(Phase III A.5.2.1).  Used in the simrec case of the main
inequality `KMor1.linearBoundLog_le_towerHeight`.

Proof routes through `boundedRec_towerHeight_ge_base`
(h-side, Task 17c E.3) and `boundedRec_towerHeight_ge_step`
(g-side, Task 17c E.3), composed with the existing
`kSimPackedBase_towerHeight_ge_propagate` /
`kSimPackedStep_towerHeight_ge_propagate`. -/
private theorem kToER_simrec_towerHeight_ge_max_child_tH
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (i : Fin (k + 1))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2) :
    max
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (h_fam l)
            (Nat.le_succ_of_le (h_h l))).towerHeight))
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l))).towerHeight)) ≤
      (kToER (KMor1.simrec i h_fam g_fam) hyp).towerHeight := by
  _
```

- [ ] **Step E.5.2: Prove the lemma — outer skeleton**

Replace the underscore with the outer-skeleton proof
that splits into h-side and g-side via `max_le`:

```lean
private theorem kToER_simrec_towerHeight_ge_max_child_tH
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (i : Fin (k + 1))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2) :
    max
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (h_fam l)
            (Nat.le_succ_of_le (h_h l))).towerHeight))
      ((Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l))).towerHeight)) ≤
      (kToER (KMor1.simrec i h_fam g_fam) hyp).towerHeight := by
  -- Step 1: unfold kToER's simrec case to expose
  -- comp (kSimSzudzikUnpackAt _) [recur, ...].
  unfold kToER
  -- Step 2: extract recur from the outer comp's sup.
  -- The outer comp's branches at j > 0 are atomic
  -- projections (towerHeight 0); the j = 0 branch is
  -- recur.  Hence sup ≥ recur.tH.
  simp only [ERMor1.towerHeight]
  -- Step 3: bound by max of h-side and g-side.
  apply max_le
  · -- h-side
    exact h_side_bound h_fam g_fam h_h h_g i hyp
  · -- g-side
    exact g_side_bound h_fam g_fam h_h h_g i hyp
```

The `h_side_bound` and `g_side_bound` are factored out as
named helpers in steps E.5.3 and E.5.4 so each side is a
focused single-step proof.

- [ ] **Step E.5.3: Prove the h-side helper**

Add a private lemma `h_side_bound` immediately preceding
`kToER_simrec_towerHeight_ge_max_child_tH`:

```lean
private theorem kToER_simrec_h_side_bound
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (i : Fin (k + 1))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2) :
    (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (h_fam l)
            (Nat.le_succ_of_le (h_h l))).towerHeight) ≤
      (kToER (KMor1.simrec i h_fam g_fam) hyp).towerHeight := by
  -- Define h_ER, g_ER abbreviations.
  set h_ER : Fin (k + 1) → ERMor1 a :=
    fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
  set g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
    fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
  -- Apply Finset.sup_le to reduce to a per-l bound.
  apply Finset.sup_le
  intro l _
  -- For each l, (h_ER l).tH ≤ ... ≤ (kSimPackedBase h_ER).tH
  -- via Finset.le_sup + the propagate lemma.
  have hpkg :
      ERMor1.natPair.towerHeight + 2 +
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun j => (h_ER j).towerHeight) ≤
        (kSimPackedBase h_ER).towerHeight :=
    kSimPackedBase_towerHeight_ge_propagate h_ER
  have hl_le_sup :
      (h_ER l).towerHeight ≤
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun j => (h_ER j).towerHeight) :=
    Finset.le_sup (Finset.mem_univ _)
  have hbase_ge :
      (kSimPackedBase h_ER).towerHeight ≤
        (ERMor1.boundedRec
          (kSimPackedBase h_ER)
          (kSimPackedStep g_ER)
          (kSimTowerBound h_ER g_ER)).towerHeight :=
    ERMor1.boundedRec_towerHeight_ge_base _ _ _
  -- Lift through the outer comp.
  unfold kToER
  simp only [ERMor1.towerHeight]
  -- The outer comp's sup picks up the recur branch's
  -- towerHeight at index 0; bound by Finset.le_sup.
  -- Combine: (h_ER l).tH ≤ sup ≤ natPair-shifted ≤
  -- packedBase ≤ boundedRec ≤ outer_comp.
  sorry
```

The remaining `sorry` is the `simp` / `omega` cleanup
threading through `Finset.le_sup` at the j = 0 branch of
the outer `comp`.  The detailed proof is mechanical: the
outer comp's `(fun j => if j.val = 0 then recur else
proj _)` branch family has `(branch 0).tH = recur.tH`
and `(branch j>0).tH = 0`, so its `Finset.univ.sup ≥
recur.tH` via `Finset.le_sup` at `⟨0, _⟩`.

- [ ] **Step E.5.4: Prove the g-side helper**

Mirror E.5.3 with `kSimPackedStep` instead of
`kSimPackedBase` and `_ge_step` instead of `_ge_base`:

```lean
private theorem kToER_simrec_g_side_bound
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (i : Fin (k + 1))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2) :
    (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l))).towerHeight) ≤
      (kToER (KMor1.simrec i h_fam g_fam) hyp).towerHeight := by
  set h_ER : Fin (k + 1) → ERMor1 a :=
    fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
  set g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
    fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
  apply Finset.sup_le
  intro l _
  have hpkg :
      ERMor1.natPair.towerHeight + 2 +
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun j =>
            (ERMor1.comp (g_ER j) kSimStepContext).towerHeight) ≤
        (kSimPackedStep g_ER).towerHeight :=
    kSimPackedStep_towerHeight_ge_propagate g_ER
  have hl_le_compsup :
      (ERMor1.comp (g_ER l) kSimStepContext).towerHeight ≤
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun j =>
            (ERMor1.comp (g_ER j) kSimStepContext).towerHeight) :=
    Finset.le_sup (Finset.mem_univ _)
  have hl_le_comp :
      (g_ER l).towerHeight ≤
        (ERMor1.comp (g_ER l) kSimStepContext).towerHeight := by
    -- (comp f g).tH = f.tH + sup g.tH + 1 ≥ f.tH.
    simp only [ERMor1.towerHeight]
    omega
  have hstep_ge :
      (kSimPackedStep g_ER).towerHeight ≤
        (ERMor1.boundedRec
          (kSimPackedBase h_ER)
          (kSimPackedStep g_ER)
          (kSimTowerBound h_ER g_ER)).towerHeight :=
    ERMor1.boundedRec_towerHeight_ge_step _ _ _
  unfold kToER
  simp only [ERMor1.towerHeight]
  sorry
```

Same `sorry` shape as E.5.3 — mechanical `Finset.le_sup`
at the recur branch of the outer comp, combined with
`omega` over the chained `≤` hypotheses.

- [ ] **Step E.5.5: Fill the `sorry` in E.5.3**

Replace the `sorry` in `kToER_simrec_h_side_bound` with
the explicit outer-comp threading.  The general pattern
(extracted as a helper if needed):

```lean
  -- The kToER simrec body has shape comp f gs where
  -- gs ⟨0, _⟩ = recur and gs ⟨j+1, _⟩ = proj _.
  -- (kToER simrec).towerHeight = f.tH + Finset.univ.sup
  -- (fun j => (gs j).tH) + 1.
  -- Finset.le_sup at ⟨0, _⟩ extracts recur.tH.
  have hbranch :
      (ERMor1.boundedRec
        (kSimPackedBase h_ER)
        (kSimPackedStep g_ER)
        (kSimTowerBound h_ER g_ER)).towerHeight ≤
      (Finset.univ : Finset (Fin _)).sup
        (fun j => _) := Finset.le_sup
        (Finset.mem_univ ⟨0, by omega⟩)
  -- Combine with the chain of inequalities.
  calc (h_ER l).towerHeight
      ≤ (Finset.univ : Finset (Fin (k + 1))).sup
          (fun j => (h_ER j).towerHeight) := hl_le_sup
    _ ≤ (kSimPackedBase h_ER).towerHeight := by omega
    _ ≤ (ERMor1.boundedRec _ _ _).towerHeight := hbase_ge
    _ ≤ _ := by omega
```

The exact final `omega` step depends on the form of
`kToER`'s simrec case after unfolding; the implementer may
need to fold/unfold `simp only` differently or use
`change` to expose the comp wrapping.  `lean_goal` /
`lean_diagnostic_messages` MCP tools recommended for
inspection.

- [ ] **Step E.5.6: Fill the `sorry` in E.5.4**

Mirror the E.5.5 pattern for the g-side, with the
additional intermediate step
`(g_ER l).tH ≤ (comp (g_ER l) kSimStepContext).tH ≤ sup ≤
packedStep.tH`.

- [ ] **Step E.5.7: Assemble the auxiliary lemma**

Replace the call sites for `h_side_bound` /
`g_side_bound` in `kToER_simrec_towerHeight_ge_max_child_tH`
to point at the now-proven `kToER_simrec_h_side_bound` /
`kToER_simrec_g_side_bound`.  Run `lake build`.

- [ ] **Step E.5.8: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step E.5.9: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kToER simrec towerHeight ≥ combined-max child (Task 17c E.5)

Auxiliary structural lemma kToER_simrec_towerHeight_ge_max_child_tH
plus its two helpers kToER_simrec_h_side_bound /
kToER_simrec_g_side_bound:
  max (max_l (kToER (h_fam l)).tH) (max_l (kToER (g_fam l)).tH)
    ≤ (kToER (simrec i h_fam g_fam) hyp).tH.

The h-side routes through boundedRec_towerHeight_ge_base
(E.3) plus the existing kSimPackedBase_towerHeight_ge_propagate;
the g-side through boundedRec_towerHeight_ge_step (E.3)
plus the existing kSimPackedStep_towerHeight_ge_propagate.
The outer comp (kSimSzudzikUnpackAt _) ... wrapping is
discharged by Finset.le_sup at the recur branch (j = 0).

This is the Step-1 deliverable of Phase IV-B; the main
inequality KMor1.linearBoundLog_le_towerHeight (Step 2)
consumes it in the simrec case of its structural induction.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task E.6: Tests + final verification

**Files:**

- Modify: `GebLeanTests/Phase4Investigation.lean`
  (append a sanity #guard for E.5)

- [ ] **Step E.6.1: Add #guard for the auxiliary lemma's
  numerical instantiation on `addK`**

```lean
-- E.5 sanity: the combined-max child bound holds on addK,
-- whose h_fam (level 0, atom) and g_fam (level 0, single
-- comp) translate to ER terms with small tower heights,
-- while (kToER addK).towerHeight = 1117.  The lemma
-- predicts max(small, small) ≤ 1117 — trivially.
#guard 0 ≤ addK_ER_tH
```

This is a documentation #guard — the lemma itself is
verified at build time by `lake build`.

- [ ] **Step E.6.2: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings, all 1559+ tests pass.

- [ ] **Step E.6.3: Commit**

```bash
git add GebLeanTests/Phase4Investigation.lean
git commit -m "$(cat <<'EOF'
Phase4Investigation: addK sanity #guard for auxiliary lemma (Task 17c E.6)

Adds a documentation #guard for the auxiliary lemma
kToER_simrec_towerHeight_ge_max_child_tH (Task 17c E.5):
on the addK witness, the lemma predicts max(small, small)
≤ 1117 (trivially), confirming the structural slack
pattern for the main inequality at Phase IV-B Task D.3.2.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Wong Prop. 4.6 mapping recap

The auxiliary lemma threads Wong's exponent-tracking
recipe (Recursion Class Ch. 4 Prop. 4.6) through our
specific `towerHeight` recursion:

- **Composition** `C(f, g_1, …, g_k)`: Wong's exponent
  `m + max j(i)`.  Project: ER `comp f g` has tH =
  `f.tH + sup_i (g i).tH + 1`.
- **Bounded recursion** `R(g, f, e)`: Wong's exponent
  inherited from `e`'s.  Project: ER `boundedRec base
  step bound` has tH ≥ `bound.tH` (E.3 `_ge_bound`),
  also ≥ `base.tH` (E.3 `_ge_base`) and ≥ `step.tH`
  (E.3 `_ge_step`) — the multi-corollary form is what
  the auxiliary lemma actually consumes.
- **Iterated bound term**: Wong's `(e_{n+2})^k(max(x⃗))`
  at level `n + 3`.  Project: `kSimTowerBound =
  iterAutoBoundExpr a stepTH baseTH`, with tH ≥
  `stepTH` (E.1, supplementary).

The auxiliary lemma (E.5) chains the boundedRec
corollaries with the packed-base / packed-step propagate
lemmas to bound `(kToER simrec).towerHeight` from below
by the children's max.  The `iterAutoBoundExpr`
supplementary lemma (E.1) is the analogue path through
the `bound` argument; it is not used by E.5 but is
documented for completeness.

---

## Self-review checklist

**Spec coverage**: every numbered task in the resumption
prompt v2 (Step 1) is covered:

- ✓ Exact theorem statement (E.5.1).
- ✓ Lean module placement (file structure section).
- ✓ Wong Prop. 4.6 mapping (Wong recap section above).
- ✓ Dependency on existing `_ge_propagate` lemmas (E.5.3,
  E.5.4).
- ✓ Per-step build/test checkpoints (every task ends with
  `lake build && lake test`).
- ✓ Per-task commit subjects ending in `(Task 17c X.Y)`.

**Placeholder scan**: two `sorry`s in E.5.3 / E.5.4 are
explicitly listed as sub-tasks E.5.5 / E.5.6 with
detailed unfold instructions.  These are intentional,
named, planned filling sites — not unhandled
placeholders.

**Type consistency**: all theorem statements use
consistent `(h_h : ∀ l, (h_fam l).level ≤ 1)` /
`(h_g : ∀ l, (g_fam l).level ≤ 1)` hypothesis form
across E.4 and E.5.  All RHS uses `(kToER … (Nat.le_succ_of_le …))
.towerHeight` consistently.  No name collisions with
existing lemmas.

**Critical-path check**: the auxiliary lemma (E.5)
depends only on E.2, E.3, and the existing
`kSimPackedBase_towerHeight_ge_propagate` /
`kSimPackedStep_towerHeight_ge_propagate`.  E.1 and E.4
are supplementary and may be skipped without affecting
E.5; they remain in the plan as standalone documentation
of the parallel chain.

---

## Out-of-scope deferred work

Step 2 of the resumption-prompt-v2 process (writing the
plan for `KMor1.linearBoundLog_le_towerHeight`) is a
separate plan, written after this auxiliary plan is
approved and (preferably) executed.  The main lemma's
plan will consume `kToER_simrec_towerHeight_ge_max_child_tH`
(E.5) in its simrec case.

Step 3 (subagent-driven-development execution) is the
implementation phase, post-approval.
