# Adversarial review of fork-upstream flow plan (round 1)

## Scope

Round 1 reviews the plan at
`plans/2026-05-12-fork-upstream-flow-plan.md` against the
converged spec at
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Two serious findings and five minor findings. This round
does not converge.

## Defects

### 1. Bookmark `docs/fork-upstream-flow` is not advanced

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`,
entire Task 1 through Task 8 sequence; specifically the
closing `jj describe -m ... ; jj new -m "wip"` snippets
and the verification in Step 11l.

**Defect**: Each task ends `jj describe` followed by
`jj new -m "wip"`, but no step runs `jj bookmark set
docs/fork-upstream-flow -r @` (or equivalent). `jj
describe` mutates the description of the current change
but does not move bookmarks; `jj new` creates a child
change and also does not move bookmarks. The bookmark
`docs/fork-upstream-flow` currently sits on the spec
change and stays there for the duration of the plan.
Step 11l's revset `main..docs/fork-upstream-flow`
therefore returns only the spec commit after Task 11k
abandons the trailing wip, not the chain of nine commits
the plan claims to produce. The deliverables would not
be on the named topic branch at the end of execution.

**Suggested fix**: append `jj bookmark set
docs/fork-upstream-flow -r @` after each `jj describe`
step, before the following `jj new -m "wip"`.

### 2. Working-copy divergent state is not surfaced

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Task 0a.

**Defect**: `jj status` in this working copy reports the
working-copy change as `(divergent)`. Task 0a's
expected-output prose makes no mention of divergence and
treats the change as a clean non-divergent head. The
divergence is benign (it stems from an earlier `jj split`
that re-used the change_id `tqmusvlq` for the spec
change while the original chore commit at the pushed SHA
also retains that change_id), but a reader of the plan
who runs `jj status` will see the `(divergent)` tag and
will not know whether to proceed or to abandon something
first.

**Suggested fix**: prepend a step that enumerates the
divergent siblings of `tqmusvlq` via `jj log -r
'tqmusvlq'` and either annotates them as benign or
abandons the stale one before Step 0b.

### 3. Exact-text mismatch in Task 6d find block

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 6d (find block).

**Defect**: The "find this text" block in Step 6d does
not match the source line-wrap in `docs/process.md`
§ jj colocated mode. A literal find-replace against the
plan's quote would fail.

**Suggested fix**: re-quote `docs/process.md` § jj
colocated mode verbatim, preserving the source's
line-wrap.

### 4. Exact-text mismatch in Task 6e find block

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 6e (find block).

**Defect**: The plan quotes the current step-4 / step-5
bullets with different line-breaks than the actual
source. A literal find-replace would fail.

**Suggested fix**: re-quote with the source's actual
line-wrap.

### 5. Line-number citation off by two for Task 3

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Task 3 Files block and Step 3c.

**Defect**: The step-6 heredoc actually spans lines
57-63 of `scripts/pre-push.sh`, not 55-62. The quoted
code is correct; only the line range is off.

**Suggested fix**: replace "lines 55-62" with
"lines 57-63" in both locations.

### 6. README contribution-pointers contradiction unaddressed

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Task 8 Step 8b; bears on `README.md` § Contribution
pointers.

**Defect**: Step 8b adds a bullet stating "the local
working copy is a clone of the fork at `rokopt/geb`",
but `README.md` § Contribution pointers step 1 currently
reads "Clone the parent monorepo at
<https://github.com/anoma/geb>". After Task 8, the
README contains two contradictory clone instructions.

**Suggested fix**: extend Task 8 with a step that
distinguishes the single-developer path (clone the fork)
from the external-contributor path (clone upstream),
either by updating step 1 of § Contribution pointers or
by adding an explicit note.

### 7. Step 1f regression test under-specifies pass criterion

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 1f.

**Defect**: Step 1f says "Expected: exit 2, stderr names
the new allowlist (`origin`, `upstream`)". The test
invocation lacks `2>&1` and lacks a `grep` on the
resulting stderr. Other tests in the plan (Step 2d,
Step 11d) use `2>&1` and gate on stderr content
explicitly; the inconsistency makes Step 1f's pass
criterion subjective.

**Suggested fix**: redirect with `2>&1` and pipe through
`grep -F` for the strings the new diagnostic must
contain.

## Confirmed-correct claims (sample)

- The plan's Files-touched and Spec-coverage map cover
  every deliverable listed in the spec's
  § Hook and configuration changes, § Documentation
  changes, § Per-clone `gh` configuration, § Per-repo
  `jj` configuration, and § Testing and verification.
- Task 1's quoted find block matches
  `scripts/hooks/block-mutating-git.sh` lines 335-342
  verbatim.
- Task 2's quoted find block matches
  `scripts/hooks/block-mutating-git.sh` lines 55-64
  verbatim.
- Task 5's quoted hard-rule text matches `CLAUDE.md`
  lines 27-30 verbatim.
- Task 7's quoted gates bullet list matches
  `.claude/rules/ci-and-workflow.md` § Pre-push checklist
  verbatim.
- The plan is markdownlint-clean against
  `.markdownlint-cli2.jsonc`.
- The plan's register sweep against itself returns only
  in-code-block matches (the `grep` commands and one
  meta-reference in the self-review checklist); no prose
  register-list words.
- `gh repo set-default --view` in the current working
  copy exits 0 with empty stdout, matching Step 9a's
  expected pre-fix state and T10's "unset" branch.
- `git remote -v` reports `origin` at
  `ssh://git@github.com/rokopt/geb` and `upstream` at
  `git@github.com:anoma/geb.git`, matching the spec's
  § Remote roles table and the prerequisite for Task 9.
- Task 2's deny-clause logic deliberately excludes the
  `-r` short flag and matches both `--remote upstream`
  and `--remote=upstream`; the design matches the spec's
  § Hook and configuration changes item 2 and the spec's
  T5 / T6 / T9 tests.
- Task 11 covers spec tests T1 through T10 in order.
