# Phase IV-B Task 17c chain-assembly resumption prompt

You are resuming the GebLean K^sim_2 ⊆ ER recursive bootstrap
formalization to execute the **chain-assembly implementation plan**
that discharges the Phase IV-B headline theorem
`kSimTowerBound_dominates_inline`.

The plan was written and adversarially audited in a prior session;
plan v2 (post-audit) is committed and ready.  This session's job is
to **execute plan v2 via subagent-driven-development**.

## Working directory and starting state

- Working directory: `/home/terence/git-workspaces/geb/geb-lean`
- Branch: `terence/develop`
- HEAD at session start: `bba102fb`
  (commits ahead of origin/terence/develop: ~50)

## The plan to execute

`docs/plans/2026-05-01-poly-bound-task-17c-chain-assembly-plan.md`
(committed at `bba102fb`).

**Tasks** (executed in this order):

1. **D.0.A** — derived-term PolyBound builders in
   `GebLean/LawvereERPolynomialBound.lean` (~13 builders, ~250
   lines).  Multi-commit task: split into atomic-derived batch
   (D.0.A.2: `ofZeroN`/`ofTwoN`/`ofNatN`/`ofPred`/`ofMinN`/`ofAddN`/
   `ofSumCtxER`) and recursive-derived batch (D.0.A.3: `ofExpER`/
   `ofTowerER`/`ofNatUnpairFst`/`ofNatUnpairSnd`/`ofBeta`).
   `ofBprod` (D.0.A.1) optional.
2. **D.0.B** — sharper `to_iter_step_form_log` adapter in
   `GebLean/LawvereERPolynomialBound.lean` (~150 lines, single
   commit).  Critical: chain-breaking fix from audit (uses
   `Nat.log 2 coefficient` instead of `coefficient` in the
   exponent).
3. **D.0.C** — `polynomial_iter_tower_bound_with_pow_base` in
   `GebLean/Utilities/ComputationalComplexity.lean` (~120 lines,
   single commit).
4. **D.2** — `kToER_polyBound_of_level_one` recursive PolyBound
   builder in `GebLean/LawvereKSimPolynomialBound.lean` (~150-300
   lines, single commit).  Consumes D.0.A's builders for the
   simrec case.
5. **D.3.2** — `linearBoundLog_packedStep_le_towerHeight`
   chain-closing log-vs-tH lemma in
   `GebLean/LawvereKSimPolynomialBound.lean` (~80-150 lines,
   single commit).  Consumes the Step-2 main inequality
   `KMor1.linearBoundLog_le_towerHeight` (`LawvereKSimPolynomialBound.lean:1828`).
6. **D.5** — the headline theorem
   `kSimTowerBound_dominates_inline` (public) in
   `GebLean/LawvereKSimPolynomialBound.lean` (~150-300 lines,
   single commit).  Combines D.0.B + D.0.C + D.2 + D.3.2 plus
   the existing `kSimPackedBase_polyBound`/`kSimPackedStep_polyBound`/
   `tower_two_le_tower_three_linear`/`tower_mono_left/right`.
7. **D.6** — read-only final verification.

Total estimated effort: ~700-1200 lines.

## Required workflow

Use **`superpowers:subagent-driven-development`** to execute the
plan task-by-task.  Per the established session pattern:

1. Read the plan file once to extract task text + context.
2. Create TaskCreate todos for D.0.A through D.6.
3. For each task: dispatch implementer subagent, run spec
   reviewer subagent, run code-quality reviewer subagent, address
   issues, mark done.  Don't dispatch multiple implementers in
   parallel.
4. After all tasks: dispatch a final code reviewer for the entire
   D.0–D.6 chain.

## Critical context

### What's already landed

**Step 1 (E.1–E.6) — auxiliary structural lemma**, commits
`eda70eb9`–`cce762e4` plus `479124f6` (docstring polish):

- `kToER_simrec_towerHeight_ge_max_child_tH` (private,
  `LawvereKSimPolynomialBound.lean:1711`).
- `boundedRec_towerHeight_le` + three `_ge_{base,step,bound}`
  corollaries.
- `iterAutoBoundExpr_towerHeight_ge_d`,
  `kSimTowerBound_towerHeight_ge_packedStep` /
  `_ge_max_step_child` (all supplementary).

**Step 2 (L.1–L.6) — main inequality**, commits `3ffd4aa3`–
`4880d884`:

- **Public theorem `KMor1.linearBoundLog_le_towerHeight`**
  (`LawvereKSimPolynomialBound.lean:1828`):
  `Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1) ≤
  3 · (kToER f).towerHeight + 1` for `f.level ≤ 1`.  Consumed by
  D.3.2.
- Private helpers: `linearBoundLog_le_towerHeight_level_zero`,
  `Nat.add_three_lt_two_pow_succ_succ`,
  `Nat.three_mul_add_six_lt_two_pow_three_mul_add_two`.

**Existing infrastructure** (verified by audit):

- `kSimPackedBase_polyBound`, `kSimPackedStep_polyBound` (line
  738+).
- `to_iter_step_form` (`LawvereERPolynomialBound.lean:503`) — the
  EXISTING (loose) adapter.  D.5 uses the new `_log` variant from
  D.0.B, NOT this one.
- `Nat.polynomial_iter_tower_bound`, `tower_two_le_tower_three_linear`,
  `pow_le_tower_two_with_shift`.
- `tower_mono_left`, `tower_mono_right`, `self_le_tower`.
- `kSimPackedStep_towerHeight_ge_succ_k` (private, line 1376).

**Existing per-constructor PolyBound builders** (in
`LawvereERPolynomialBound.lean`):
`ofZero`, `ofSucc`, `ofProj`, `ofSub`, `ofComp`, `ofBsum`,
`ofBoundedRec`.  D.0.A adds the derived-term ones.

### Audit findings already applied to plan v2

**B1 (chain-breaking)**: existing `to_iter_step_form` produces
exponent `degree + coefficient + constant + 2`.  With
`coefficient = 3^E` (from `kSimPackedStep_polyBound`), this is
exponential in `k`, but `stepTH` grows only linearly.  D.0.B
adds the sharper `to_iter_step_form_log` using
`Nat.log 2 (coefficient + 1)` instead.

**B2**: `polynomial_iter_tower_bound` requires linear base, but
`kSimPackedBase_polyBound` is polynomial.  D.0.C adds the
polynomial-base variant.

**B4**: 13 derived-term PolyBound builders are missing.  D.0.A
adds them.

**A1**: D.3.2's algebra step `Nat.log 2 (3^E) = E · Nat.log 2 3`
is FALSE (`Nat.log 2 3 = 1` but `Nat.log 2 (3^E) ≈ 1.585·E`).
Plan v2 corrected to `≤ Nat.log 2 (4^E) = 2E`.

**A2**: D.2's `kSimSzudzikUnpackAt` PolyBound now uses a
factored helper `kSimSzudzikUnpackAt_polyBound (a n : ℕ)` then
specialized at `i.val`, instead of direct `induction i.val`.

**A3**: D.0.A's table now lists all 13 builders explicitly.

## Project conventions (from `CLAUDE.md`)

- Build commands: `lake build` and `lake test`.  **Never** `lake
  env lean` (doesn't pick up project options) or `lake clean`
  (would force mathlib rebuild).
- **No `sorry` or `admit` in committed state**, no warnings, no
  banned words.
  Banned words: "fundamental", "actually", "key" (except
  "key/value"), "insight", "core", "advanced", "complex",
  "complicated", "simple", "advantage", "benefit", "important",
  "challenge", "yes", "wait", "hmm", "sorry", "careful",
  "important", "difficult", "blocked", "incomplete", "future",
  "issue", "problem", "block".
- Line length ≤ 80 characters.
- Constructive only (no `Classical`, no `noncomputable`, no
  `axiom`, no `Quotient.out` / `Quot.out`).
- No emojis.
- Style: dry, formal, mathematical.  Comments explain WHY, not
  WHAT.
- "Minimum code that solves the problem.  Nothing speculative."
  — apply YAGNI ruthlessly.  If a helper turns out unused
  post-implementation, delete or `private` it.

## Discipline reminders from the prior session

- Commit subjects end in `(Task 17c D.X)` per project
  convention.
- Lean's pattern-match definition cannot be partially compiled
  — for any pattern-match recursive proof, all cases must
  compile before commit.  D.2 may face this if the recursive
  builder uses pattern matching.
- The Lean guardrail blocks `git commit --amend` — use new
  commits instead.  When a follow-up polish is needed, do it as
  a NEW commit with subject `(Task 17c D.X follow-up)` or
  similar.
- Implementer subagents may make tactic-level deviations from
  plan sketches if the planned tactic doesn't elaborate;
  accept these provided the theorem statement is unchanged and
  the proof is correct.  Document deviations in the report.
- After each implementer report, run BOTH spec compliance and
  code quality reviews before moving to the next task (per the
  superpowers:subagent-driven-development skill).
- The spec reviewer should check public-vs-private modifiers,
  no-dead-code (unused helpers must be deleted or `private`),
  and that the theorem statement matches the plan exactly.
- The IDE may produce "Imports are out of date" diagnostics
  after edits if the file is open — this is the LSP cache; not
  a build issue.

## Lessons from the prior session — apply forward

- **Avoid the `boundedRec_towerHeight_overhead` pattern**: in
  E.2, an unused `private def` was added "for downstream
  reference" and had to be deleted in a follow-up commit.
  Don't add helpers without immediate consumers.
- **Avoid widening `private` to `theorem`**: in L.3-5, three
  L.1 helpers were unprivatized "for future use" and the
  alternative algebra obviated them; they had to be deleted.
  Same YAGNI principle.
- **Use `change` (not `unfold`) when `let`-bindings interfere**:
  the L.3-5 implementer used `change` to expose `kToER`'s
  simrec body since `unfold` doesn't pierce `let`-bindings
  cleanly.  D.2's recursive simrec case will face the same
  issue.
- **The Lean MCP tools are essential**: use
  `mcp__lean-lsp__lean_goal`, `lean_diagnostic_messages`,
  `lean_multi_attempt`, `lean_local_search`, `lean_run_code`
  liberally for diagnosis.
- **Long algebraic proofs benefit from `set` abbreviations**:
  see the L.3-5 implementer's use of `set p_f`, `set max_c`,
  etc.  Same pattern works for D.5's chain assembly.

## Where the headline theorem fits in the broader goal

The Phase IV-B headline `kSimTowerBound_dominates_inline` is
the load-bearing dependency for kToER Task 14 (`kToER_interp`),
which is in turn required for kToER Task 16/17
(`kToERFunctor` + functor laws).  With this plan completed,
the path to the interpretation-preserving functor
`KSimCat 2 ⥤ ERCat` is:

```text
[NEXT — plan v2] D.0.A → D.0.B → D.0.C → D.2 → D.3.2 → D.5
   ↓
[AFTER] kToER Task 14 — kToER_interp (consumes the headline)
[AFTER] kToER Task 15 — kToERN_interp
[AFTER] kToER Task 16 — kToERFunctor obj/map
[AFTER] kToER Task 17 — functor laws (map_id, map_comp)
[AFTER] kToER Tasks 18-22 — tests + re-export + final verify
   ↓
[GOAL] kToERFunctor : KSimCat 2 ⥤ ERCat with kToER_interp
```

## What success looks like at session end

- All seven tasks (D.0.A, D.0.B, D.0.C, D.2, D.3.2, D.5, D.6)
  committed with subjects ending in `(Task 17c D.X)`.
- `lake build` and `lake test` pass cleanly with no warnings,
  no `sorry`, no `admit`.
- The headline theorem
  `theorem kSimTowerBound_dominates_inline` is public (not
  `private`) at `LawvereKSimPolynomialBound.lean`.
- Final code review passes.

## Escalation triggers

If at any task the implementation exceeds the plan's
upper-bound estimate by more than 50% (e.g. D.0.A grows beyond
375 lines, D.5 beyond 450 lines), pause and surface to the
user.  The chain may need additional helpers, or the proof
strategy may need re-thinking.

If a sub-step in D.5 cannot close due to arithmetic that
depends on `kSimPackedBase_polyBound` / `kSimPackedStep_polyBound`'s
internal field formulas (which are computed expressions, not
opaque numbers), the implementer may need to add a small
field-equality helper that exposes the formula.  Cap any such
helper at ~30 lines.

## Starting actions

1. **Read this prompt file** (you're doing it).
2. **Read** `docs/plans/2026-05-01-poly-bound-task-17c-chain-assembly-plan.md`
   end-to-end before dispatching anything.
3. **Verify** the starting state:
   - `git log --oneline -3` should show `bba102fb` as HEAD.
   - `lake build && lake test` should pass clean (1521 build
     jobs, 1561+ test jobs).
4. **Invoke** `superpowers:subagent-driven-development` with
   the plan file path as argument.
5. **Create TaskCreate todos** for D.0.A through D.6.
6. **Dispatch D.0.A's implementer subagent** first.

Good luck.
