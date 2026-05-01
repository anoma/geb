You are resuming the GebLean K^sim_2 ⊆ ER recursive bootstrap
formalization, mid-Phase-IV (Task 17c).

Working directory: /home/terence/git-workspaces/geb/geb-lean
Branch: terence/develop

## What's been done (commits f065ae51 through 36607e44)

Phases I, II, and III of Task 17b are landed. Eight commits
ahead of origin/main covering the recursive bootstrap from
level-0 up through level-1.

Phase I (level-1 dominance and helpers):

- f065ae51: Plan correction (A.5.0 / A.5.2)
- f05cba65: A.4 (`Nat.pow_le_tower_two_with_shift`)
- 8579b54f: A.5.1 (`Nat.tower_two_le_tower_three_linear`)
- 93906d39: A.5.0 (`kSimSzudzikPackList_towerHeight_ge_propagate`
  + Base/Step corollaries)
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

Phase IV (Task D in the plan) — `kSimTowerBound_dominates_inline`,
the level-2 simrec dominance lemma. Mirrors Phase I's structure
but with level-1 children replacing level-0 children, using
`KMor1.linearBound` (Lemma 1.A) instead of
`KMor1.level0Shape.linearBound` (Lemma 1.B).

Phase V (Tasks E, F, G, H) — tests, re-exports, parent-plan
update, final verification. After Phase IV closes, these are
mostly housekeeping.

## Plan reference (read in full before starting)

Primary plan:
`docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`

Phase IV details: lines 1627–1822 (Task D.1 stub, Task D.2
parallel level-1 simrecVec aux, Task D.3 compose the level-2
chain).

Phase V details: lines 1824 onward (Tasks E–H).

Note the two earlier "Plan correction (2026-04-30, mid-execution)"
callouts on A.5.0 and A.5.2 — those corrections are landed and
no longer relevant to Phase IV directly, but the corrected
arithmetic chain in A.5.2.2 is the template Phase IV's analog
should follow.

## Phase IV roadmap (from the plan plus Phase II/III experience)

The level-2 chain mirrors Phase I.A.6 step for step, with the
following substitutions:

1. **`packed_iteration_matches_simrecVec` analog**: build a
   level-1 version that calls `kToER_interp_level_one` instead
   of `kToER_interp_level_zero`. The current level-0 version
   is at `LawvereKSimPolynomialBound.lean` line 995+.

2. **`KMor1.simrecVec_seqPack_le_pow` analog**: build a level-1
   version using `KMor1.linearBound` constants instead of
   `level0Shape.linearBound`. The current level-0 version is at
   line ~1809; its body relies on
   `KMor1.simrecVec_uniform_linear_bound` (line ~1489), which
   itself needs a level-1 analog (this is plan task D.2,
   ~100–180 lines mirroring lines 342–485 of the current file).

3. **`kToER_level0_towerHeight_ge_const` analog**: a level-1
   version of A.5.2.1 stating
   `(KMor1.linearBound f h).2 ≤ (kToER f).towerHeight + ?` for
   level-≤-1 K^sim terms. This is the trickiest new piece —
   the constant offset for the level-1 case may not be `+1`
   like the level-0 case. Work out the right constant first by
   case analysis on the KMor1 inductive (zero/succ/proj/comp
   are easy; raise reduces to the level-0 case via
   `kToER_level0_towerHeight_ge_const`; simrec is impossible at
   level ≤ 1). The comp case will need the same simp-with-case-
   equation trick used in A.5.2.1's comp case (see commit
   bf540ba2 — adding `simp only [hshape_gi, ...]` after the
   inner `cases` to substitute through the inner `match` in the
   goal).

4. **`stepTH_baseTH_dominates_arg` analog**: level-1 version of
   A.5.2.2. The existing one (line ~1511+) uses the `+1` slack
   from A.5.2.1 throughout; the level-1 version uses whatever
   constant came out of step 3. The arithmetic structure is
   identical (`Nat.log_lt_of_lt_pow`, `Nat.lt_two_pow_self`,
   max-trick on `2*baseTH`), so this should be near-mechanical
   once step 3 is settled.

5. **Main theorem**: `kSimTowerBound_dominates_inline` body —
   mirrors A.6's calc chain (line ~1903+) with level-1 helpers
   substituted. Stub signature is at plan line 1646, but make
   it `theorem` (not `private theorem`) since Task 14 of the
   parent kToER plan needs to access it.

Estimated total: 200–400 lines of new code across these five
helpers.

## Phase II/III lessons that carry over

- `Finset.add_sup` (mathlib) is unknown via `_root_.Finset.add_sup`
  in our `namespace GebLean` context — use a different approach.
  In A.5.2.2 the Nat-subtraction pattern worked: bound `SG ≤
  sup_comp - 1` via `Finset.sup_le` with a per-element bound,
  then `omega` from there. See commit f12c9f8d's
  `stepTH_baseTH_dominates_arg.h_sup_comp_ge`.

- For `Nat.pow_le_tower_two_with_shift` and
  `Nat.tower_two_le_tower_three_linear` (in
  `Utilities/ComputationalComplexity.lean` under `namespace Nat`),
  invoke as `Nat.pow_le_tower_two_with_shift` directly — Lean
  resolves it correctly. (Earlier this session we saw a stale-LSP
  "unknown constant" warning that disappeared after a real
  `lake build`; trust `lake build` over LSP for this.)

- When applying a lemma whose conclusion uses internal `let`s,
  give the call site an explicit type annotation matching your
  outer `set` definitions. See commit b3182bfc's
  `h_combined :  ... ≤ (kSimPackedStep g_ER).towerHeight + ...`
  in `kSimTowerBound_dominates_level_one`.

- `kSimSzudzikUnpackAt_interp_eq_seqAt` (in
  `Utilities/KSimSzudzikSimrec.lean`) and `Nat.seqAt_seqPack`
  (in `Utilities/SzudzikSeq.lean`) are the round-trip lemmas
  that drop layers cleanly in the level-1 simrec case (Phase II).
  Phase IV's main theorem won't need them directly — that
  theorem's content is the dominance inequality, not the interp
  preservation.

- `boundedRec_eq_natRec_of_bounded` (in `Utilities/ERArith.lean`
  line 2193) and `kSimTowerBound_mono_counter` (in
  `Utilities/KSimSzudzikSimrec.lean` line 440) are likewise
  level-agnostic; Phase IV reuses them at the same call-site
  depth as Phase II.

## How to start

1. Read `CLAUDE.md` (project conventions: no sorry/admit, no
   banned words, ≤80 char lines, `lake build` / `lake test`
   only, `warningAsError=true`).

2. Read `docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`
   sections Phase IV (Task D) and Phase V (Tasks E–H) in full.

3. Verify state:
     git log --oneline -10
     lake build
     lake test
   Expected HEAD: 36607e44, build clean, tests pass.

4. Use `superpowers:executing-plans` skill (or
   `subagent-driven-development` if subagents help).

5. Tackle Phase IV step 3 first (the `kToER_level1_*` analog
   of A.5.2.1) — that's where the new mathematical content
   lives. If the right constant offset (`+1`, `+2`, `+linearBound.1`,
   ...) isn't immediately obvious, surface and discuss before
   sinking time into the structural induction.

## Lean MCP tools to use liberally

- mcp__lean-lsp__lean_goal: inspect goal at position
- mcp__lean-lsp__lean_diagnostic_messages: read errors
- mcp__lean-lsp__lean_multi_attempt: test tactics without
  editing
- mcp__lean-lsp__lean_local_search: find existing lemmas
- mcp__lean-lsp__lean_loogle: pattern-search mathlib

When a `lean_diagnostic_messages` says "Unknown constant" but
`#check` works in `lean_run_code`, do a real `lake build` —
the LSP can be stale.

## Discipline reminders

- Never commit with sorry/admit (warningAsError would fail
  anyway).
- Each Phase IV sub-helper stands alone — commit individually
  when build is clean. Match the established commit-message
  pattern (subject line ending in "(Task 17c X.Y)" + a body
  paragraph + Co-Authored-By).
- Banned words list per CLAUDE.md applies to commit messages
  and code comments alike.
- The Phase IV main theorem is `theorem` (public), unlike
  `kSimTowerBound_dominates_level_one` which is `private`.
  Per plan line 1671: "this lemma is public (no private),
  since Task 14 of the kToER plan needs to access it."
