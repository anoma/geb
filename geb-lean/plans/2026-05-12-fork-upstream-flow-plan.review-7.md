# Adversarial review of fork-upstream flow plan (round 7)

## Scope

Round 7 reviews the plan after the round-6 fix to Step
A.4.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Round 6's fix to Step A.4 is in place and empirically
verified against jj 0.41.0. Round 7 introduces three new
serious findings concerning stale, hard-coded counts and
round-number claims that propagate into commit-log
descriptions. Round 7 does not converge.

Counts: 0 blocker, 3 serious, 0 minor.

## Defects

### 1. Step 0b commit description claims round 5 converged

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 0b.

**Defect**: Step 0b instructs the executor to run
`jj describe -m "doc(fork-upstream): add 2026-05-12
design and review rounds 1-5 / Lands the spec ...
together with five rounds of fresh-context adversarial
review. Round 5 converged (zero
blocker/serious/minor)."` That description is now false:
rounds 6 and 7 have run, and the spec change in the
working copy now contains 6+ spec review files plus 6+
plan review files. Executing the step writes a
factually-incorrect claim into the permanent commit log.

**Suggested fix**: parameterise the commit description on
the actual round count at execution time (a shell-
substituted variable derived from `ls
docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.review-*.md
| wc -l`), and replace the hard-coded convergence
assertion with language that does not pin a specific
round number.

### 2. Step 0a expected state cites "the five .review-*.md files"

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 0a (Expected text).

**Defect**: Step 0a tells the executor to verify that the
working copy contains "the spec, the five `.review-*.md`
files, and the process-self-update edits". Empirically
the working-copy change already contains 5 spec reviews
plus 6 plan reviews; round 7 will add another. "Five"
is ambiguous (spec reviews? plan reviews? total?) and in
every reading is now wrong.

**Suggested fix**: state the count parametrically — for
example, "the spec, the spec-review and plan-review
files (one of each per adversarial round), and the
process-self-update edits". Drop the "five" literal.

### 3. Task A intro and Step A.9 description hard-code "10 files"

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Task A intro paragraph and Step A.9 `jj describe` body.

**Defect**: Both the prose and the commit-description
template assert "10 files dated 2026-05-07 onwards" and
"consolidating the 10 files at `plans/`", with the
per-class breakdown "1 pre-cutover, 5 cutover-effecting,
4 current workstream (2026-05-12 and its three
reviews)". At plan finalisation time the
current-workstream count was 4; at round 7 the count is
8, and the total at `plans/` is 14. The Task A intro
explicitly notes immediately below ("≥5 current-
workstream files ... the move is therefore glob-based
rather than enumerated"), making the hard-coded numerals
internally inconsistent with the plan's own dynamic-glob
design.

**Suggested fix**: replace every hard-coded numeral in
Task A's prose and the Step A.9 commit-description
template with shell-substituted values computed at
execution time, or with parametric prose ("every `.md`
file currently at `plans/`").

## Confirmed-correct claims (sample)

- Step A.4's round-6 fix is in place and works. An
  empirical jj 0.41.0 run produced
  `R {plans => docs/superpowers/plans}/<file>.md` for
  each rename; the grep pattern matches.
- `.markdownlint-cli2.jsonc` line 51 contains
  `"docs/superpowers/plans/**",` and line 64 contains
  `"geb-lean/docs/superpowers/plans/**",` (matches Step
  A.1's quoted current state).
- `CLAUDE.md` line 61, 91, 198 and span 114-118 match
  Task A.6's quoted current text verbatim.
- `README.md` line 53 and spans 58-61, 87-89, 93-96
  match Task A.7 and Task 8b' quoted text verbatim.
- `scripts/hooks/block-mutating-git.sh` lines 55-64 and
  335-342 match the quoted source in Tasks 1 and 2.
- `scripts/pre-push.sh` lines 57-63 match the Task 3
  quoted heredoc.
- `docs/process.md` § jj colocated mode lines 200-205
  and 217-220 match Task 6d and 6e's quoted text
  verbatim.
- The date-glob `2026-05-0[1-8]-*.md` excludes
  2026-05-09 and 2026-05-12 files (consistent with Step
  A.5 Test 1 / Test 2 discriminators).
- Existing
  `docs/superpowers/plans/2026-05-09-process-bootstrap-monorepo-plan.md`
  is markdownlint-clean under the proposed config.
