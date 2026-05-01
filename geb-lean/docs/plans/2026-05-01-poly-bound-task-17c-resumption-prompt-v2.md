# Phase IV-B (Task 17c) resumption prompt — v2

You are resuming the GebLean K^sim_2 ⊆ ER recursive bootstrap
formalization, mid-Phase-IV-B (Task 17c).  This is **v2** of
the resumption prompt; v1 (`2026-05-01-poly-bound-task-17c-`
`resumption-prompt.md`) is superseded by the literature
re-review and B1' refinements that landed in commits
`c2dfc3d6` through `31b407c5`.

Working directory: `/home/terence/git-workspaces/geb/geb-lean`
Branch: `terence/develop`
HEAD at session start: `31b407c5`
(commits ahead of origin/terence/develop: ~21)

## Step 0: Adversarial document audit (before writing code or plans)

Before doing anything else, run an **adversarial brainstorming +
sequential-thinking** session on the existing documentation, to
catch errors, gaps, or vagueness that would derail the
implementation.  Use the project's `superpowers:brainstorming`
skill explicitly (and `sequential-thinking` MCP if available)
in adversarial mode — i.e., actively try to find what is wrong
or unclear, not what is right.

The documents to audit, in order of importance:

1. `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
   — especially the **Fix B (part 3)** section (around line 581),
   which now (post-`31b407c5`) cites Wong's Prop. 4.6 verbatim.
   Look for: misquoted Wong text, incorrect mapping from Wong's
   exponent `k` to our `towerHeight`, missing edge cases (what
   if a child has tower height 0?), unclear handling of the
   `+1` per `comp` wrapping discrepancy with Wong's measure.

2. `docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`
   — especially the Phase IV-B section (around line 1627
   onward) and the D.0.3 callout (around line 1735).  Look for:
   contradictions with the research doc, places where the plan
   still uses the old "folklore" framing, unclear roadmap for
   the auxiliary lemma, missing pointers between the
   completion plan and the research doc.

3. `docs/plans/2026-04-30-er-polynomial-bound-plan.md` —
   especially R5' (around line 178).  Look for: outdated
   claims that pre-date the max_k fix or the literature
   re-review.

4. `GebLeanTests/Phase4Investigation.lean` — the numerical
   findings file.  Look for: outdated comments, claims that
   don't match the current `linearBound` definition (post-
   max_k), missing witnesses for important cases.

5. `GebLean/LawvereKSimPolynomialBound.lean` — especially the
   `KMor1.linearBound` and `KMor1.linearBound_dominates`
   definitions (lines 188-700ish).  Look for: stale comments,
   mismatch between the `if hcomp_0 : (KMor1.comp f gs).level
   ≤ 0` dite branch and the docstring, places where the
   max_k vs sum_k change might have left dead bookkeeping.

For each finding, decide whether it's:

- (a) a documentation error to fix in place (do it),
- (b) a deeper conceptual gap that requires a brainstorm /
  discussion before proceeding (surface to user),
- (c) a contingent issue that's only relevant under specific
  next-step decisions (note in a "deferred" file, proceed).

Update all relevant documents to be self-consistent BEFORE
moving to step 1.  Commit each substantive document update
individually with a clear message.

## Step 1: After Step 0, write a plan for the auxiliary structural lemma

Use the `superpowers:writing-plans` skill to write an explicit
implementation plan for the auxiliary lemma
`kToER_simrec_towerHeight_ge_max_child_tH` (or the
appropriately-named analog) that the audit may have refined.

The plan should be self-contained and specify:

- The exact theorem statement (with all hypotheses).
- The Lean module(s) where it lives (likely
  `GebLean/LawvereKSimPolynomialBound.lean` or a new
  utility file).
- The Wong Prop. 4.6 mapping (which case gives which
  inductive step).
- The dependency on existing `_ge_propagate` lemmas
  (`kSimSzudzikPackList_towerHeight_ge_propagate`,
  `kSimPackedBase_towerHeight_ge_propagate`,
  `kSimPackedStep_towerHeight_ge_propagate`).
- Per-step build/test checkpoints.

## Step 2: Write a plan for the main lemma

Once the auxiliary lemma is planned, write an analogous plan
for `KMor1.linearBoundLog_le_towerHeight` (the structural
inequality
`Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1)
  ≤ 3 · (kToER f h).towerHeight + 1`).

The plan should specify:

- The constant `c` (target `c = 1` per the
  comp-case-equality analysis in the research doc /
  completion plan).
- The case-by-case proof sketch (atomic, comp at level ≤ 0,
  comp at level 1, raise, simrec).
- The dependency on the auxiliary lemma from Step 1.
- Per-step build/test checkpoints.

## Step 3: Execute via subagent-driven-development

Once both plans are written, use
`superpowers:subagent-driven-development` to execute the
plans task-by-task.  Each task ends in a `lake build` +
`lake test` clean state and a focused commit per the project
convention (commit subject ends in `(Task 17c X.Y)`).

## What's been done

| SHA | Change |
|---|---|
| `f48ecf78` | `ERMor1.PolyBound.ofBoundedRec` builder + test |
| `a9f701f0` | Documented fan-out residual finding |
| `c2dfc3d6` | `linearBound` delegates to `level0Shape` at level-0 comps |
| `b9415d87` | Investigation witness: `addKFanOut5` |
| `0e3bfa66` | **Match Tourlakis Lemma 1.A: `max_k` not `sum_k`** |
| `f0bc59b2` | Plan: literature alignment + simrec auxiliary status |
| `31b407c5` | **Literature re-review: Wong Prop. 4.6 explicit, not folklore** |

Build clean (1521 jobs), all 1559 tests pass at HEAD.

## Key context from the prior session

### The mathematical recipe is now explicit

After re-reading Wong's Recursion Class Ch. 4 chap4.pdf
(verbatim text in the research doc, "Fix B (part 3)"),
Prop. 4.6's inductive proof gives an EXPLICIT exponent-
tracking recipe:

- **Composition `C(f, g_1, …, g_k)`**: exponent =
  `m + max(j(1), …, j(k))`.
- **Bounded recursion `R(g, f, e)`**: exponent inherited
  from `e`.

This maps to our project-side `towerHeight`:

- `comp f g`: `tH = tH(f) + sup_i tH(g_i) + 1`.
- `boundedRec base step bound`: tH inherits from `bound`'s
  tH plus comp/minN/betaAtN wrapping overhead.

### The structural lemma

The auxiliary structural lemma the audit/plan should
target:

```text
tH(kToER (KMor1.simrec h_fam g_fam i)) ≥
  max (max_l tH(kToER (h_fam l)))
      (max_l tH(kToER (g_fam l)))
  + small_const
```

Numerical evidence: `tH(kToER addK) = 1117` while max
child tH is 1, so the lemma's `small_const` likely is at
most a few hundred.  But the proof needs to be structural,
following Wong's recipe through `kToER simrec`'s wrapping:

```text
kToER (simrec h g i) =
  comp (kSimSzudzikUnpackAt a i.val)
       (fun j => if j.val = 0 then recur else proj j)
where
  recur = boundedRec (kSimPackedBase h_ER)
                     (kSimPackedStep g_ER)
                     (kSimTowerBound h_ER g_ER)
  h_ER l = kToER (h_fam l)
  g_ER l = kToER (g_fam l)
```

The `_ge_propagate` lemmas already give:

- `kSimPackedBase_towerHeight_ge_propagate`:
  `baseTH ≥ natPair.tH + 2 + max_h_tH`.
- `kSimPackedStep_towerHeight_ge_propagate`:
  `stepTH ≥ natPair.tH + 2 + max_l tH(comp (g_l) kSimStepContext)`
  ≥ `max_g_tH + tH(kSimStepContext) + 1 + natPair.tH + 2`.

The auxiliary lemma threads these through the `boundedRec
· comp` wrapping using:

- `tH(boundedRec base step bound) ≥ tH(bound) + small`
  (from boundedRec = comp minN [betaAtN, bound]).
- `tH(comp unpackAt (cases recur or proj))
  ≥ tH(recur) + small`.
- `tH(recur) ≥ tH(kSimTowerBound h_ER g_ER) + small`
  (using boundedRec's structure).
- `tH(kSimTowerBound h_ER g_ER)` ≥ ?
  (involves `iterAutoBoundExpr a stepTH baseTH` which
  itself has structure to thread through; needs a
  separate `iterAutoBoundExpr_towerHeight_ge_*` lemma).

### The main lemma

Once the auxiliary is in hand, the main lemma:

```text
∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1),
  Nat.log 2 ((KMor1.linearBound f h).1 +
             (KMor1.linearBound f h).2 + 1)
    ≤ 3 · (kToER f (Nat.le_succ_of_le h)).towerHeight + 1
```

Cases:

- **`zero`**: `lB = (0, 0)`; LHS = 0; tH(zeroN) = 1; 0 ≤ 4. ✓
- **`succ`**: `lB = (1, 1)`; LHS = log₂ 3 = 1; tH = 0; 1 ≤ 1. ✓
- **`proj`**: `lB = (1, 0)`; LHS = log₂ 2 = 1; tH = 0; 1 ≤ 1. ✓
- **comp at level ≤ 0** (dite branch): linearBound is
  `level0Shape`'s; A.5.2.1 gives `.2 ≤ tH + 1`; arithmetic.
- **comp at level 1** (multiplicative max formula):
  `L(comp) ≤ L(f') + max_l L(gs_l) + 2`; IH gives equality.
- **`raise`**: linearBound is `level0Shape`'s; same as the
  comp ≤ 0 case.
- **`simrec`**: uses the auxiliary lemma; `tH(simrec)` is
  huge and dominates linearBound's small linear-in-max-
  child-tH bound.

### Numerical witnesses (from Phase4Investigation.lean)

- `addK` (level 1, simrec): `linearBound = (4, 0)`,
  `tH = 1117`, `L = 2`; inequality `2 ≤ 3·1117 + 1 = 3352`
  holds.
- `projSuccFanOut5` (level 0, fan-out 5): post-tightening
  `linearBound = (1, 1)`, `tH = 1`, `L = 1`; inequality
  `1 ≤ 4`.
- `addKFanOut5` (level 1, fan-out 5 to addK):
  `linearBound = (4, 0)`, `tH = 1118`, `L = 2`; inequality
  `2 ≤ 3·1118 + 1 = 3355`.

### Files to read first

In suggested reading order:

1. This file.
2. `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
   "Fix B (part 3)" section (around line 581) and
   "Implication for the level-2 dominance chain" callout
   (around line 200).
3. `docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`
   Phase IV-B section (line 1627+) and D.0.3 callout
   (line 1735+).
4. `GebLeanTests/Phase4Investigation.lean` for the
   numerical witnesses.
5. `GebLean/LawvereKSimPolynomialBound.lean` lines 188-700
   for the current `KMor1.linearBound` definition and
   `KMor1.linearBound_dominates` proof (post-max_k fix).

## Discipline reminders

- Never commit with `sorry` or `admit`
  (warningAsError = true).
- Each sub-task stands alone — commit individually with
  subject ending `(Task 17c X.Y)` plus body paragraph
  plus Co-Authored-By trailer.
- Banned-word list per CLAUDE.md applies.
- The Phase IV-B main theorem
  (`kSimTowerBound_dominates_inline`) is `theorem` (public);
  the auxiliary structural lemmas can be `private`.
- `lake build` and `lake test`; never `lake env lean` or
  `lake clean`.
- Use Lean MCP tools liberally:
  `mcp__lean-lsp__lean_goal` for goals,
  `mcp__lean-lsp__lean_diagnostic_messages` for errors,
  `mcp__lean-lsp__lean_multi_attempt` for tactic
  experiments,
  `mcp__lean-lsp__lean_local_search` for finding
  existing lemmas,
  `mcp__lean-lsp__lean_loogle` for pattern search.
- When `lean_diagnostic_messages` says "Unknown constant"
  but `#check` works in `lean_run_code`, do a real `lake
  build` — the LSP can be stale.

## What success looks like at session end

- All audit findings from Step 0 either fixed in
  documents or surfaced for user review.
- Plans written via `superpowers:writing-plans` for both
  the auxiliary lemma and the main lemma, committed.
- Implementation via `subagent-driven-development` with
  per-task commits, passing all `lake build` and `lake
  test` after each task.
- The chain-closing inequality at Phase IV-B Task D.3.2
  (the level-2 analog of `stepTH_baseTH_dominates_arg`)
  is reachable: with the main lemma proved, the chain
  closes by routine omega/log arithmetic similar to
  Phase III.

If at any point a sub-step seems harder than expected
(estimated > 200 lines for an individual lemma, or
requires re-design of the chain), pause and surface to
the user.  The goal is steady progress, not heroic
single-session breakthroughs.
