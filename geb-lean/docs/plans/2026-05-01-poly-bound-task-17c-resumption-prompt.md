# Phase IV (Task 17c) resumption prompt — v1 (SUPERSEDED)

> **SUPERSEDED 2026-05-01**: see
> `2026-05-01-poly-bound-task-17c-resumption-prompt-v2.md`.
> The v1 below predates the literature re-review (commits
> `0e3bfa66`, `31b407c5`) and the B1' refinements
> (commits `c2dfc3d6`, `b9415d87`).  Use v2 instead.

You are resuming the GebLean K^sim_2 ⊆ ER recursive bootstrap
formalization, mid-Phase-IV (Task 17c).

Working directory: /home/terence/git-workspaces/geb/geb-lean
Branch: terence/develop

## Direction correction (recorded 2026-05-01)

**Read this section first.**  An earlier draft of this prompt
described Phase IV as a "level-1 mirror of Task A" — i.e., a
Strategy A (linear-bound) chain at level 2.  That direction
was found to be **mathematically inconsistent with Tourlakis
2018 §0.1.0.27 (3)**, which stratifies the K^sim hierarchy's
value bounds: linear at level 1, polynomial at level 2, tower
at level ≥ 3.

The level-1 chain (Phase III, landed) absorbed
`Nat.log 2 (KK + …)` into `stepTH + 2*baseTH` via
`kToER_level0_towerHeight_ge_const`.  At level 1, no analogous
shape lemma can hold: `KMor1.linearBound`'s `comp` clause
produces `(p_f.1 * max_c, p_f.1 * sum_k + p_f.2)` —
multiplicative in children, with a sum-over-fan-out — while
`(kToER (comp f gs)).towerHeight = tH(kToER f) + sup_i tH(kToER
gs_i) + 1` — additive with a sup, no fan-out factor.  No bound
`(KMor1.linearBound f h).2 ≤ 2^((kToER f).tH + c)` for level-1
`f` with fan-out ≥ 2 and any fixed `c` is achievable.

The corrected level-2 chain uses **polynomial bounds** on the
level-1 children, not linear bounds.  Recursion Class Ch. 4
Prop. 4.7 ("the iteration of a linear function is a polynomial
function, yielding the n = 1 case") justifies this; the Lean
realization is `Nat.polynomial_iter_tower_bound` (Module A,
Poly Task 5, landed) combined with `kSimPackedStep_polyBound`
/ `kSimPackedBase_polyBound` (Module C, Poly Task 16, landed).
Module A and B's polynomial-bound infrastructure was built for
exactly this purpose; the level-2 case re-uses it.

References:

- Research doc, "Implication for the level-2 dominance chain"
  callout:
  `docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
- Parent plan R5' (replaces R5):
  `docs/plans/2026-04-30-er-polynomial-bound-plan.md`,
  "Brainstorm refinements (second pass)" section.
- Completion plan Phase IV-B (replaces Phase IV-A):
  `docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`,
  Phase IV section.

## What's been done (commits f065ae51 through 36607e44)

Phases I, II, and III of Task 17b are landed.  Eight commits
ahead of origin/main (plus this resumption prompt) covering the
recursive bootstrap from level-0 up through level-1.

Phase I (level-1 dominance and helpers):

- f065ae51: Plan correction (A.5.0 / A.5.2)
- f05cba65: A.4 (`Nat.pow_le_tower_two_with_shift`)
- 8579b54f: A.5.1 (`Nat.tower_two_le_tower_three_linear`)
- 93906d39: A.5.0 (`kSimSzudzikPackList_towerHeight_ge_propagate`,
  with Base/Step corollaries)
- 75483240: A.2/A.3 (`KMor1.simrecVec_uniform_linear_bound`,
  `KMor1.simrecVec_seqPack_le_pow`)
- bf540ba2: A.5.2.1 (`kToER_level0_towerHeight_ge_const`)
- f12c9f8d: A.5.2.2 (`stepTH_baseTH_dominates_arg`,
  `kSimPackedBase_towerHeight_ge_succ_k`, `Fin.foldr_max_le`)
- b3182bfc: A.6/A.7 (`kSimTowerBound_dominates_level_one`)

Phase II (level-1 interp preservation):

- 7d4891d7: `kToER_interp_level_one`

Phase III (level-1 linear-bound dominance):

- 36607e44: `kToER_linearBound_dominates_level_one`

Build clean (1521 jobs), tests pass.

## What remains

Phase IV-B (Task D in the corrected completion plan) —
`kSimTowerBound_dominates_inline`, the level-2 simrec
dominance lemma.  Routes through polynomial-iteration bounds
(Strategy B) instead of linear-iteration (Strategy A).

Phase V (Tasks E, F, G, H of the completion plan) — tests,
re-exports, parent-plan update, final verification.  After
Phase IV-B closes, these are mostly housekeeping.

## Phase IV-B roadmap

Per the corrected completion plan (Phase IV-B):

### Task D.0: Investigation phase (no code yet)

Two candidate sub-strategies, B1 and B2 (defined in the parent
plan's R5' callout).  D.0 picks one by validating the chain-
closing log-vs-towerHeight inequality on a concrete level-1
test case before drafting ~300+ lines of proof.

- **B1 (constructive ER PolyBound)**: build
  `pb : ERMor1.PolyBound (kToER child)` for each level-1 K^sim
  child by structural recursion on the ER term `kToER child`,
  via per-constructor builders.  Includes a new `ofBoundedRec`
  builder for the embedded `boundedRec` from level-1 simrec.
  The structural log-vs-tH inequality
  `Nat.log 2 (pb.degree + pb.coefficient + pb.constant + 2)
   ≤ tH(kToER child) + small_const` is established by structural
  induction on the constructive build.
- **B2 (custom K^sim measure)**: define a
  `KMor1.linearBoundLog : (f : KMor1 a) → f.level ≤ 1 → ℕ`
  satisfying both `linearBound bound by 2^linearBoundLog` and
  `linearBoundLog ≤ tH + c'`.  Risk: the `comp` case must
  absorb fan-out (`+log_2 fan-out`), which `tH` cannot supply
  (tH is fan-out-agnostic).  May not close.

D.0 outcome determines what new infrastructure is needed at
D.2 (e.g., `ofBoundedRec` for B1).

### Task D.1: Stub the main theorem

`theorem kSimTowerBound_dominates_inline` (public, not
private — Task 14 of the kToER plan needs it).  Same statement
as in Phase IV-A; only the proof strategy changes.

### Task D.2: Build per-component PolyBounds for level-1 children

Per D.0's chosen sub-strategy.  For B1: `ofBoundedRec` (~80-150
lines in Module B) plus `ofKToER : (f : KMor1 a) → f.level ≤ 1
→ ERMor1.PolyBound (kToER f h)` (~100-200 lines in Module C).
For B2: a thin wrapper (~30-50 lines) plus the
`KMor1.linearBoundLog` recursion and its two structural
inequalities (~150-300 lines).

### Task D.3: Apply the packed-step / packed-base PolyBound builders

Plumbing: the per-component PolyBounds from D.2 feed into the
already-built `kSimPackedStep_polyBound` / `kSimPackedBase_polyBound`
(Poly Task 16, landed).  Includes a chain-closing log-vs-tH
lemma for the packed step's PolyBound fields, derived from
D.2's per-component bound and the `_ge_propagate` structural
lemmas (already landed).

### Task D.4: Apply the iter-step-form adapter and the iteration bound

Convert the packed step's PolyBound to the form consumed by
`Nat.polynomial_iter_tower_bound` (Poly Task 5, landed), then
apply.  May require a small adapter for the case where the
packed base is polynomial (not linear) in `sumCtx`; the
existing `Nat.polynomial_iter_tower_bound` requires a linear
base.

### Task D.5: Close the chain into `kSimTowerBound`

Same chain as Phase III's A.6 from line 1955+ onward, but
starting from `tower 2 (linear)` produced by D.4 instead of
the seqPack-pow-tower bound.  The closing inequalities
(`tower_two_le_tower_three_linear`, `tower_mono_left/right`)
are unchanged.

Estimated total: 400-700 lines of new code across D.0–D.5,
plus the new `ofBoundedRec` builder if B1 is chosen.

## Phase II/III lessons that carry over

- `Finset.add_sup` (mathlib) is unknown via `_root_.Finset.add_sup`
  in our `namespace GebLean` context — use a different approach.
  In A.5.2.2 the Nat-subtraction pattern worked: bound `SG ≤
  sup_comp - 1` via `Finset.sup_le` with a per-element bound,
  then `omega` from there.  See commit f12c9f8d's
  `stepTH_baseTH_dominates_arg.h_sup_comp_ge`.
- For `Nat.pow_le_tower_two_with_shift` and
  `Nat.tower_two_le_tower_three_linear` (in
  `Utilities/ComputationalComplexity.lean` under `namespace Nat`),
  invoke as `Nat.pow_le_tower_two_with_shift` directly — Lean
  resolves it correctly.  (Earlier this session we saw a stale-LSP
  "unknown constant" warning that disappeared after a real
  `lake build`; trust `lake build` over LSP for this.)
- When applying a lemma whose conclusion uses internal `let`s,
  give the call site an explicit type annotation matching your
  outer `set` definitions.  See commit b3182bfc's
  `h_combined :  ... ≤ (kSimPackedStep g_ER).towerHeight + ...`
  in `kSimTowerBound_dominates_level_one`.
- `boundedRec_eq_natRec_of_bounded` (in `Utilities/ERArith.lean`
  line 2193) and `kSimTowerBound_mono_counter` (in
  `Utilities/KSimSzudzikSimrec.lean` line 440) are level-agnostic
  and reusable at Phase IV-B's call sites.

## How to start

1. Read `CLAUDE.md` (project conventions: no sorry/admit, no
   banned words, ≤80 char lines, `lake build` / `lake test`
   only, `warningAsError=true`).
2. Read this prompt's "Direction correction" section, then the
   research doc's "Implication for the level-2 dominance chain"
   callout, then R5' in the parent plan.
3. Read the corrected Phase IV-B in
   `docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`.
4. Verify state:
     git log --oneline -10
     lake build
     lake test
   Expected HEAD includes 257bda30 (the original resumption
   prompt) and a follow-up commit revising the plans.  Build
   clean, tests pass.
5. Use `superpowers:executing-plans` skill (or
   `subagent-driven-development` if subagents help).
6. **Tackle Task D.0 first** — the investigation phase.  Pick
   B1 or B2 based on the validation outcome.  Do not draft
   D.1–D.5's code until D.0.3 has documented the chosen
   sub-strategy.
7. If both B1 and B2 fail, surface to the user before
   proceeding.  The mathematical content here is non-trivial;
   we'd rather pause and re-think than commit code on a broken
   chain.

## Lean MCP tools to use liberally

- `mcp__lean-lsp__lean_goal`: inspect goal at position
- `mcp__lean-lsp__lean_diagnostic_messages`: read errors
- `mcp__lean-lsp__lean_multi_attempt`: test tactics without
  editing
- `mcp__lean-lsp__lean_local_search`: find existing lemmas
- `mcp__lean-lsp__lean_loogle`: pattern-search mathlib

When a `lean_diagnostic_messages` says "Unknown constant" but
`#check` works in `lean_run_code`, do a real `lake build` —
the LSP can be stale.

## Discipline reminders

- Never commit with sorry/admit (warningAsError would fail
  anyway).
- Each Phase IV-B sub-task stands alone — commit individually
  when build is clean.  Match the established commit-message
  pattern (subject line ending in "(Task 17c X.Y)" + a body
  paragraph + Co-Authored-By).
- Banned words list per CLAUDE.md applies to commit messages
  and code comments alike.
- The Phase IV-B main theorem (`kSimTowerBound_dominates_inline`)
  is `theorem` (public), unlike Phase III's
  `kSimTowerBound_dominates_level_one` which is `private`.
  Per Phase IV-B Task D.1: "this lemma is public (no private),
  since Task 14 of the kToER plan needs to access it."
