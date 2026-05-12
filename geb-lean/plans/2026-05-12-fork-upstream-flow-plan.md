# Fork–upstream flow implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** land the deliverables of
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`
in the geb-lean tree, plus the per-clone operator setup, plus
the acceptance test run.

**Architecture:** mechanical enforcement first, then the
working-time rule file, then the rationale docs, then the
operator-side configuration, then the acceptance test. The
ordering keeps documentation consistent with code at every
commit: rules and docs landing after the hooks they describe
do not lead a reader to expect behaviour that has not yet
shipped.

**Tech stack:** Bash (hook scripts), Markdown (rules, docs),
`jj` 0.41+ (VCS), `gh` (GitHub CLI), `markdownlint-cli2`
(lint).

---

## Spec coverage map

| Spec section | Implementation task(s) |
| --- | --- |
| § Hook and configuration changes — fetch allowlist | Task 1 |
| § Hook and configuration changes — jj push deny clause | Task 2 |
| § Hook and configuration changes — `scripts/pre-push.sh` reminder | Task 3 |
| § Hook and configuration changes — `scripts/check-jj-setup.sh` | (no change, per spec) |
| § Documentation changes — `.claude/rules/fork-upstream-flow.md` | Task 4 |
| § Documentation changes — `CLAUDE.md` | Task 5 |
| § Documentation changes — `docs/process.md` | Task 6 |
| § Documentation changes — `.claude/rules/ci-and-workflow.md` | Task 7 |
| § Documentation changes — `README.md` | Task 8 |
| § Per-clone `gh` configuration | Task 9 |
| § Per-repo `jj` configuration | Task 10 |
| § Testing and verification — T1 to T10 | Task 11 |
| § State at spec time — git-clone precondition wording | inside Task 6 |

Task A is a process self-update (not a spec deliverable):
it normalises the split-plans directory inconsistency
under `docs/process.md` § Process self-update mechanism.
It lands on this workstream's branch but is orthogonal to
the spec's content.

The earlier process-self-update edits to `CLAUDE.md`
§ Hard rules adversarial bullet and `docs/process.md`
§ Adversarial review of specs and plans already landed
in the working copy during the spec's convergent
adversarial-review cycle (round 3 fix). They are not
re-implemented here; Task 5 and Task 6 amend the same
files for orthogonal reasons (fork-upstream content,
not adversarial-review content).

## Files this plan touches

- `.markdownlint-cli2.jsonc` — Task A (switch
  `docs/superpowers/plans/**` catch-all ignore to a
  date-glob pattern parallel to specs).
- `plans/*.md` → `docs/superpowers/plans/*.md` — Task A
  (a glob move that catches every `.md` file currently
  at `plans/`; the file count grows as additional
  review files land during the convergent review loop,
  so the move is glob-based rather than enumerated).
- `CLAUDE.md` — Task A (path references at lines 61,
  91, 114-118 and 198; the spans at lines 114-118 and
  91 are widened by Steps A.6 to enable a clean
  paragraph re-wrap) and Task 5 (Hard rules expansion
  and Pointers table additions).
- `README.md` — Task A (path references at lines 53,
  58-61 and 93-96; the latter two are widened by Step
  A.7 to enable a clean paragraph re-wrap) and Task 8
  (pointers paragraph; § Contribution pointers
  reconciliation).
- `scripts/hooks/block-mutating-git.sh` — Task 1
  (fetch-allowlist expansion) and Task 2 (jj-push deny
  clause).
- `scripts/pre-push.sh` — Task 3 (step-6 reminder line).
- `.claude/rules/fork-upstream-flow.md` — Task 4
  (created; directive working-time reference).
- `docs/process.md` — Task 6 (new § Fork–upstream
  relationship and onboarding additions).
- `.claude/rules/ci-and-workflow.md` — Task 7 (pre-push
  checklist note).
- `.git/config` at the parent `geb/` root — Task 9
  (`gh repo set-default` writes one entry).
- `geb/.jj/repo/config.toml` — Task 10 (`jj config set
  --repo` writes one entry).

Every task ends in a `jj commit` (description set on the
working-copy change before creating a new empty change for
the next task) except Tasks 9 and 10, which mutate
operator-local state rather than tree content. Task 11 is
a verification run; it produces no commits.

## Branch and bookmark

All commits land on bookmark `docs/fork-upstream-flow`
(jj change_id `tqmusvlq`). The branch is based on the
merge commit `dc02dea6` (PR #11's merge, recorded in
the spec's § State at spec time as `@-`). Specific
commit_ids are not pinned here because they drift under
jj's amend / describe flow; the change_id and bookmark
provide stable references.

The current working-copy change already contains the
spec, the spec-review files (one per spec
adversarial-review round through convergence), the plan
and its plan-review files (one per plan
adversarial-review round through convergence), and the
process-self-update edits to `CLAUDE.md` and
`docs/process.md`. The first task below begins by
finalising that change with its description and creating a
new empty change on top for Task 1's edits.

## Task 0: Finalise the current change; open a fresh one

**Files:**

- Confirm working-copy state. No file edits.

- [ ] **Step 0a: Snapshot the current change and verify
  description and bookmark.**

```sh
jj status
jj log -r '@ | @-' --no-graph \
  -T 'change_id.short() ++ " " ++ commit_id.short()
      ++ " " ++ bookmarks ++ " :: "
      ++ description.first_line() ++ "\n"'
```

Expected: `@` is on bookmark `docs/fork-upstream-flow`
with description starting `doc(fork-upstream): add
2026-05-12 design`; `@-` is the merge commit `dc02dea6`
(PR #11's merge — the parent on which the spec change
was based at authoring time; the `main` bookmark may
have moved forward from this point per Op 7 catch-up
operations and is not asserted here). Working copy
contains
the spec, the spec-review files (`*.review-*.md` siblings
of the spec, one per spec adversarial-review round
through convergence), the plan and its plan-review files
(at `plans/`, one per plan adversarial-review round
through convergence), and the process-self-update edits
to `CLAUDE.md` and `docs/process.md`. The exact file
count depends on how many review rounds the convergent
adversarial-review loop required and is not asserted as
a literal here.

- [ ] **Step 0a': Surface the divergent change_id state
  (benign).**

```sh
jj log -r 'change_id(tqmusvlq)' --no-graph \
  -T 'change_id.short() ++ " " ++ commit_id.short()
      ++ " " ++ bookmarks ++ " :: "
      ++ description.first_line() ++ "\n"'
```

Expected: two lines, both with change_id prefix
`tqmusvlq` but distinct commit_ids — one for the spec
change on `docs/fork-upstream-flow`, one for the pushed
chore commit at `chore/axiom-check-fail-mode@origin`
SHA `11a513b9`. The bare-revset form `jj log -r
'tqmusvlq'` errors with `Error: Change ID 'tqmusvlq' is
divergent`; the wrapping function `change_id(...)`
returns all divergent siblings. `jj bookmark list`
reports both bookmarks as `(divergent)`.

The divergence is benign: each bookmark points to a
distinct commit_id, and the rest of the plan refers to
commits by bookmark name (`docs/fork-upstream-flow`,
`chore/axiom-check-fail-mode`) rather than by
change_id, so no operation below is ambiguous. Do not
abandon either commit at this step.

- [ ] **Step 0b: Update the change description to
  reflect the final content of the change.**

Compute the number of spec-review rounds (one
`*.design.review-*.md` file per round) for the
description, then `jj describe` with a here-string so
the variable interpolates:

```sh
n_spec=$(ls docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.review-*.md \
  | wc -l)
jj describe -m "doc(fork-upstream): add 2026-05-12 design and review rounds 1-${n_spec}

Lands the spec at
docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md
together with ${n_spec} rounds of fresh-context
adversarial review; the final round's review file is
the convergence record (zero blocker / serious / minor
defects per docs/process.md § Convergence criterion).

Also lands the plan at
plans/2026-05-12-fork-upstream-flow-plan.md and its
plan-review files (one per plan adversarial-review
round through convergence). The plan and its reviews
are at plans/ at the moment this change was authored;
Task A (in this same workstream) relocates them to
docs/superpowers/plans/.

Includes a process self-update consequent on the
adversarial-review cycle: docs/process.md § Adversarial
review of specs and plans gains categorisation
(blocker / serious / minor / cosmetic-taste),
author-response menu, convergence criterion,
reviewer-tool-surface specification, and loop protocol.
CLAUDE.md § Hard rules adversarial-review bullet and
§ Phase-driven workflow rows updated to match."
```

- [ ] **Step 0c: Open a new empty change on top of the
  spec change for Task A's plan-directory normalisation.**

```sh
jj new -m "wip"
```

This makes `@` an empty child of the spec change. Task A
edits land here.

---

## Task A: Normalise plans → `docs/superpowers/plans/`

Process self-update consequent on a workstream-time
observation that plan files are split between two
directories: `docs/superpowers/plans/` (historical
files dated 2026-03-19 to 2026-05-06, parallel to
`docs/superpowers/specs/`) and `plans/` (files dated
2026-05-07 onwards, created in or around the 2026-05-10
cutover). The split is fixed here per `docs/process.md`
§ Process self-update mechanism by consolidating the
files at `plans/` into the established
`docs/superpowers/plans/` directory. The fork-upstream
design spec is not amended (the move is orthogonal to
its content).

The files to move are every `.md` file currently at
`plans/`. The set is described compositionally rather
than enumerated because the plan-review-loop adds one
file per round through convergence:

- 1 pre-cutover file: `2026-05-07-process-bootstrap-plan.md`.
- 5 cutover-effecting files:
  `2026-05-09-process-bootstrap-monorepo-plan.md` plus
  its four numbered review files (`.review-1.md`
  through `.review-4.md`).
- The current-workstream files:
  `2026-05-12-fork-upstream-flow-plan.md` (this file)
  plus every numbered plan-review file at the same
  prefix. The count of plan-review files equals the
  number of plan adversarial-review rounds and is
  verified at execution time via `ls
  plans/2026-05-12-fork-upstream-flow-plan.review-*.md
  | wc -l`.

The total file count is `ls plans/*.md | wc -l` at
execution time. The move is glob-based and does not
depend on the count.

**Files:**

- Modify: `.markdownlint-cli2.jsonc` lines 51 and 64.
- Move: every `*.md` file currently at `plans/` to
  `docs/superpowers/plans/`. Glob-based; the exact file
  count is the value of `ls plans/*.md | wc -l` at
  execution time.
- Modify: `CLAUDE.md` at lines 61, 91, 114-118 and
  198.
- Modify: `README.md` at lines 53, 58-61 and 93-96.

- [ ] **Step A.1: Update `.markdownlint-cli2.jsonc`
  (config edit; verification deferred to A.5).**

The current `.markdownlint-cli2.jsonc` uses a catch-all
ignore `docs/superpowers/plans/**` (line 51) and its
parent-repo-prefixed mirror at line 64. Under that
config, post-cutover plans at the new location would be
silently ignored. The target config replaces the
catch-all with a date-glob pattern parallel to specs.
A genuinely-discriminating test for the config change
requires the moved files to be in place; verification is
therefore in Step A.5 (after the moves in A.2 and A.3)
rather than here.

Find lines 51 and 64 of `.markdownlint-cli2.jsonc`:

```jsonc
    "docs/superpowers/plans/**",
```

and:

```jsonc
    "geb-lean/docs/superpowers/plans/**",
```

Replace line 51 with two date-glob entries parallel to
the existing spec entries:

```jsonc
    "docs/superpowers/plans/2026-0[1-4]-*.md",
    "docs/superpowers/plans/2026-05-0[1-8]-*.md",
```

Replace line 64 with:

```jsonc
    "geb-lean/docs/superpowers/plans/2026-0[1-4]-*.md",
    "geb-lean/docs/superpowers/plans/2026-05-0[1-8]-*.md",
```

- [ ] **Step A.2: Move every `.md` file at `plans/` to
  `docs/superpowers/plans/` (glob-based).**

Record the count for use by Step A.4:

```sh
n=$(ls plans/*.md | wc -l)
echo "moving $n files"
mv plans/*.md docs/superpowers/plans/
```

The glob expansion captures the pre-cutover, the
cutover-effecting, and the current-workstream sets
(including any review files added by the convergent
review loop after this plan was authored). After this
step, the plan file you are executing exists at
`docs/superpowers/plans/2026-05-12-fork-upstream-flow-plan.md`.
The executor's in-memory copy of the task list is
unaffected.

- [ ] **Step A.3: Confirm `plans/` is empty of `.md`
  files.**

```sh
ls plans/*.md 2>&1
echo "exit=$?"
```

Expected: `ls: cannot access 'plans/*.md': No such file
or directory` and exit 2. If any `.md` files remain at
`plans/`, the glob in A.2 did not catch them and the
executor halts to investigate.

- [ ] **Step A.4: Verify the moves with jj's rename
  detection.**

```sh
jj diff -r @ --summary | grep -c '^R {plans => docs/superpowers/plans}/'
```

Expected: a single line of stdout, printing the value
of `$n` that Step A.2 recorded. Each move appears as a
`R {plans => docs/superpowers/plans}/<file>.md` rename
entry — jj 0.41.0 formats renames with the old and new
path-prefixes brace-expanded inside a single token,
not as two whitespace-separated paths. The
`.markdownlint-cli2.jsonc` modification appears as a
separate `M` entry not counted here.

If the count does not match `$n`, inspect the full
diff to see which moves jj did not detect as renames:

```sh
jj diff -r @ --summary
```

Likely cause if mismatched: a content hash collision
that defeated rename detection (file shows up as
`A docs/superpowers/plans/<file>.md` +
`D plans/<file>.md` instead of a single `R` entry). In
that case the move still happened correctly at the
filesystem level and the executor proceeds to Step A.5.

- [ ] **Step A.5: Verify lint behaviour at the new
  location.**

Test 1: a post-cutover plan at the new location is
linted (NOT ignored). Note the absence of the `:`
literal-path prefix — that prefix would bypass the
`ignores` array entirely and produce false positives
that do not verify the config change.

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  'docs/superpowers/plans/2026-05-12-fork-upstream-flow-plan.md' \
  2>&1 | tail -3
```

Expected post-fix: `Linting: 1 file(s)` followed by
`Summary: 0 error(s)`. (Pre-fix, under the catch-all
ignore `docs/superpowers/plans/**`, the same invocation
would produce `Linting: 0 file(s)` / `Summary: 0
error(s)`; the discriminator is the file-count.)

Test 2: a pre-cutover plan at the new location is
ignored:

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  'docs/superpowers/plans/2026-05-07-process-bootstrap-plan.md' \
  2>&1 | tail -3
```

Expected: `Linting: 0 file(s)`, then `Summary: 0 error(s)`.
(The date-glob ignore excludes the file from the globbed
file set.)

Test 3: lint over the entire new directory's post-cutover
content:

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs 'docs/superpowers/plans/2026-05-09-*' \
              'docs/superpowers/plans/2026-05-12-*' \
  2>&1 | tail -3
```

Expected: `Summary: 0 error(s)`.

- [ ] **Step A.6: Update `CLAUDE.md` references.**

Find line 61 (Phase-driven workflow table row):

```markdown
| Plan | `superpowers:writing-plans` at `plans/` |
```

Replace with:

```markdown
| Plan | `superpowers:writing-plans` at `docs/superpowers/plans/` |
```

Find line 91 (Repo structure bullet):

```markdown
- `plans/` — workstream plans, one per dated topic.
```

Replace with:

```markdown
- `docs/superpowers/plans/` — workstream plans, one per
  dated topic; parallel to `docs/superpowers/specs/`.
```

Find lines 114-118 (replacing a five-line span so the
paragraph re-wraps cleanly after the path swap):

```markdown
topic branch. Specs live at
`docs/superpowers/specs/<date>-<topic>-design.md`; plans at
`plans/<date>-<topic>-plan.md`. Adversarial-review iterations
and self-review fixes are commits on the same branch. The
merge-commit cutover lands them on `main`.
```

Replace with:

```markdown
topic branch. Specs live at
`docs/superpowers/specs/<date>-<topic>-design.md`; plans at
`docs/superpowers/plans/<date>-<topic>-plan.md`.
Adversarial-review iterations and self-review fixes are
commits on the same branch. The merge-commit cutover lands
them on `main`.
```

Find line 198 (Pointers table row):

```markdown
| `plans/2026-05-09-process-bootstrap-monorepo-plan.md` | Refactor plan |
```

Replace with:

```markdown
| `docs/superpowers/plans/2026-05-09-process-bootstrap-monorepo-plan.md` | Refactor plan |
```

Then lint and register-sweep `CLAUDE.md` to catch any
markdownlint or register-list regression introduced by
the four edits above:

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs ':CLAUDE.md' 2>&1 | tail -3
grep -niE "\b(key|important|core|advanced|complex|complicated|simple|advantage|benefit|fundamental|actually|insight|challenge|hmm|careful|difficult|future|crucial|essential|critical)\b" \
  CLAUDE.md | grep -v "value-laden adjectives"
```

Expected: `Summary: 0 error(s)` from the lint; the
register grep returns no output (the one match on the
style-rule line that enumerates forbidden words as
content is removed by the
`grep -v "value-laden adjectives"` filter).

- [ ] **Step A.7: Update `README.md` references.**

Find line 53:

```markdown
- [`plans/2026-05-09-process-bootstrap-monorepo-plan.md`](plans/2026-05-09-process-bootstrap-monorepo-plan.md)
```

Replace with:

```markdown
- [`docs/superpowers/plans/2026-05-09-process-bootstrap-monorepo-plan.md`](docs/superpowers/plans/2026-05-09-process-bootstrap-monorepo-plan.md)
```

Find lines 58-61 (replacing a four-line span so the
paragraph re-wraps cleanly after the path swap):

```markdown
Workstream-specific specs live under
[`docs/superpowers/specs/`](docs/superpowers/specs); their
plans live under [`plans/`](plans). The topological index links
to each active workstream by name.
```

Replace with:

```markdown
Workstream-specific specs live under
[`docs/superpowers/specs/`](docs/superpowers/specs); their
plans live under
[`docs/superpowers/plans/`](docs/superpowers/plans). The
topological index links to each active workstream by name.
```

Find lines 93-96 (replacing a four-line span so the
numbered-list item re-wraps cleanly):

```markdown
3. Brainstorm a workstream and write a spec under
   `docs/superpowers/specs/<date>-<topic>.md`, then a plan
   under `plans/<date>-<topic>-plan.md`. Both are tracked
   with adversarial review cycles.
```

Replace with:

```markdown
3. Brainstorm a workstream and write a spec under
   `docs/superpowers/specs/<date>-<topic>.md`, then a plan
   under `docs/superpowers/plans/<date>-<topic>-plan.md`.
   Both are tracked with adversarial review cycles.
```

Then lint and register-sweep `README.md`:

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs ':README.md' 2>&1 | tail -3
grep -niE "\b(key|important|core|advanced|complex|complicated|simple|advantage|benefit|fundamental|actually|insight|challenge|hmm|careful|difficult|future|crucial|essential|critical)\b" \
  README.md
```

Expected: `Summary: 0 error(s)` from the lint; the
register grep returns no output.

- [ ] **Step A.8: Verify no stale `plans/` references
  remain in committed Markdown.**

Two complementary checks. First, a positive check: each
of the seven file:line edits in A.6 and A.7 should now
contain `docs/superpowers/plans/` rather than the bare
`plans/`. Verify with a precise grep that any remaining
bare `plans/` reference in the touched files is flagged:

```sh
grep -nE \
  '\| `plans/|`plans/|]\(plans/|^plans/|\s\`plans/|under `plans/|under \[`plans/|at `plans/' \
  CLAUDE.md README.md docs/process.md .claude/rules/*.md \
  2>&1
echo "exit=$?"
```

Expected: exit 1, no output. The alternation covers:
table-cell paths (`| \`plans/`), inline-code paths
(`` `plans/ ``), Markdown link targets (`](plans/`),
line-start references (`^plans/`), spaced-backtick
references (`` \`plans/ ``), and the "under" and "at"
prepositional forms.

Second, a positive count check: each touched file should
contain at least the expected number of
`docs/superpowers/plans/` literal matches (CLAUDE.md has
four edits ⇒ at least four matches; README.md has three
edits ⇒ at least three matches):

```sh
echo -n "CLAUDE.md  : "
grep -cF 'docs/superpowers/plans/' CLAUDE.md
echo -n "README.md  : "
grep -cF 'docs/superpowers/plans/' README.md
```

Expected: CLAUDE.md count ≥ 4; README.md count ≥ 3.
(The count is `≥` rather than `==` because either file
may also contain `docs/superpowers/plans/` references
that were not edited by Task A.) If either count is
below the threshold, an edit was skipped or wrote the
wrong text; re-read the relevant Step A.6 or A.7
sub-edit.

- [ ] **Step A.9: Set description, advance bookmark,
  open the next change.**

The commit message uses compositional prose (no numeric
counts) so that the message is correct whether or not
jj's rename detection caught every move — Step A.4
admits a benign collision path in which some moves
appear as `D` + `A` rather than `R`, and counts derived
from the `R`-rename pattern would undercount in that
case.

```sh
jj describe -m "chore(process): normalise plans/ to docs/superpowers/plans/

Consequent on a workstream-time observation that plan
files were split between docs/superpowers/plans/
(historical files dated 2026-03-19 to 2026-05-06) and
plans/ (files dated 2026-05-07 onwards, created in or
around the 2026-05-10 cutover). The split is fixed here
per docs/process.md § Process self-update mechanism by
consolidating every .md file then at plans/ into the
established docs/superpowers/plans/ directory: the
pre-cutover 2026-05-07-process-bootstrap-plan.md, the
cutover-effecting 2026-05-09-process-bootstrap-monorepo-
plan.md and its four review files, and the current
workstream's 2026-05-12-fork-upstream-flow-plan.md plus
every plan-review file at the same prefix. CLAUDE.md
and README.md path references update.
.markdownlint-cli2.jsonc switches the
docs/superpowers/plans/** catch-all ignore to a
date-glob pattern parallel to docs/superpowers/specs/,
so post-cutover plans are lint-enforced at the new
location."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 1: Allow `git fetch upstream` in the bare-`git` allowlist

**Files:**

- Modify: `scripts/hooks/block-mutating-git.sh` lines
  335-342 (1-positional `fetch` arm) and lines 340 (deny
  message).
- Test: command-line invocation per spec T3.

- [ ] **Step 1a: Write the failing test (T3 from the
  spec).**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git fetch upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected after Task 1: exit 0, no stderr output.

- [ ] **Step 1b: Run the test now and confirm it fails.**

The same command as Step 1a. Expected NOW (before the
fix): exit 2, with stderr line
`block-mutating-git: blocked \`git fetch upstream\``
and an `only 'git fetch origin' is on the allowlist`
reason.

- [ ] **Step 1c: Edit the 1-positional arm of the
  `fetch` case to accept both `origin` and `upstream`.**

Find lines 335-342 of `scripts/hooks/block-mutating-git.sh`,
which look like:

```bash
      1)
        # `git fetch origin` — only the literal remote name "origin" is allowed.
        if [[ "${positionals[0]}" == "origin" ]]; then
          exit 0
        fi
        deny "only 'git fetch origin' is on the allowlist; other remotes are blocked" \
             "jj git fetch --remote origin"
        ;;
```

Replace with:

```bash
      1)
        # `git fetch origin` or `git fetch upstream` — both literal
        # remote names are on the allowlist. The two-positional
        # `refs/pull/*/head:*` form below remains restricted to origin.
        case "${positionals[0]}" in
          origin|upstream)
            exit 0
            ;;
        esac
        deny "only 'git fetch origin' and 'git fetch upstream' are on the allowlist; other remotes are blocked" \
             "jj git fetch --remote <origin|upstream>"
        ;;
```

- [ ] **Step 1d: Run the test again, confirm it now
  passes.**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git fetch upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected: exit 0, no stderr.

- [ ] **Step 1e: Run a regression: confirm `git fetch
  origin` still passes.**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git fetch origin"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected: exit 0.

- [ ] **Step 1f: Run a regression: confirm
  `git fetch some-other-remote` is still denied with
  the updated allowlist diagnostic.**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git fetch foobar"}}' \
  | bash scripts/hooks/block-mutating-git.sh 2>&1 \
  | tee /dev/stderr \
  | grep -F "origin" \
  | grep -F "upstream"
echo "pipe-exit=${PIPESTATUS[*]}"
```

Expected: hook exit 2 (first element of pipe-exit), and
both `grep -F "origin"` and `grep -F "upstream"` exit 0
(non-empty stderr line matched both literals). The deny
diagnostic must mention both allowlisted remotes.

- [ ] **Step 1g: Set the description for this change
  and open a new one for Task 2.**

```sh
jj describe -m "feat(hook): allow 'git fetch upstream' in bare-git allowlist

Extends the 1-positional fetch arm of
scripts/hooks/block-mutating-git.sh to accept 'upstream'
in addition to 'origin'. The 2-positional
refs/pull/*/head:* form remains restricted to origin
(no analogous upstream-PR fetch use case)."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 2: Deny `jj git push --remote upstream` and `--remote=upstream`

**Files:**

- Modify: `scripts/hooks/block-mutating-git.sh` lines
  55-64 (jj pass-through block at top of the file).
- Test: command-line invocation per spec T5, T6, T9.

- [ ] **Step 2a: Write the failing tests (T5 and T9
  from the spec).**

Test T5 (space-separated form):

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected after Task 2: exit 2, stderr names the spec
path.

Test T9 (equals-form):

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote=upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected after Task 2: exit 2, stderr names the spec
path.

- [ ] **Step 2b: Run both tests now and confirm they
  fail (pass-through exits 0).**

Both invocations above. Expected NOW: exit 0, no stderr
output. The jj pass-through clause currently lets every
`jj git ...` through.

- [ ] **Step 2c: Edit the jj pass-through block to add
  a deny clause for `--remote upstream` and
  `--remote=upstream` on `jj git push`.**

Find lines 55-64 of `scripts/hooks/block-mutating-git.sh`,
which look like:

```bash
# ---------------------------------------------------------------------------
# jj git stripping: if .jj/ exists, allow jj-mediated git interop outright.
# ---------------------------------------------------------------------------

if jj root > /dev/null 2>&1; then
  # If the first token is "jj" and the second is "git", pass through.
  if [[ "${tokens[0]:-}" == "jj" && "${tokens[1]:-}" == "git" ]]; then
    exit 0
  fi
fi
```

Replace with:

```bash
# ---------------------------------------------------------------------------
# jj git stripping: if .jj/ exists, allow jj-mediated git interop outright —
# EXCEPT for `jj git push --remote upstream` (and equals-form), which is
# denied because upstream receives commits only via PRs opened from origin.
# See docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md
# § Invariants and § Op 4. The `-r` short form is NOT matched: in jj 0.41
# `-r` resolves to `--revisions`, not `--remote`; matching it here would
# produce a false positive on a revset literally named `upstream`.
# ---------------------------------------------------------------------------

if jj root > /dev/null 2>&1; then
  if [[ "${tokens[0]:-}" == "jj" && "${tokens[1]:-}" == "git" ]]; then
    if [[ "${tokens[2]:-}" == "push" ]]; then
      # Scan tokens[3..] for an upstream-selecting `--remote` argument.
      i=3
      while [[ $i -lt ${#tokens[@]} ]]; do
        tok="${tokens[i]}"
        next="${tokens[i+1]:-}"
        if [[ "$tok" == "--remote" && "$next" == "upstream" ]]; then
          {
            printf 'block-mutating-git: blocked `jj git push --remote upstream`\n'
            printf '  reason: upstream receives commits only via PRs opened from origin\n'
            printf '  see: docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md\n'
            printf '  use: gh pr create --repo anoma/geb --base main --head rokopt:<branch>\n'
          } >&2
          exit 2
        fi
        if [[ "$tok" == "--remote=upstream" ]]; then
          {
            printf 'block-mutating-git: blocked `jj git push --remote=upstream`\n'
            printf '  reason: upstream receives commits only via PRs opened from origin\n'
            printf '  see: docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md\n'
            printf '  use: gh pr create --repo anoma/geb --base main --head rokopt:<branch>\n'
          } >&2
          exit 2
        fi
        i=$((i+1))
      done
    fi
    exit 0
  fi
fi
```

The deny here is hand-rolled (not via the `deny`
function defined later in the file) because that
function references `$subcommand` and `$sub_args`,
which are computed by the bare-`git` parser further
down. The jj guard runs before that parser.

- [ ] **Step 2d: Run T5 and T9 again and confirm both
  pass (exit 2, stderr names the spec).**

Both invocations as in Step 2a.

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh 2>&1
echo "exit=$?"
```

Expected: exit 2; stderr contains
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote=upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh 2>&1
echo "exit=$?"
```

Expected: exit 2; stderr contains the same spec path.

- [ ] **Step 2e: Run regression T6 (jj fetch upstream
  still passes) and a push-to-origin regression.**

T6:

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git fetch --remote upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected: exit 0, no stderr.

Push to origin regression:

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote origin -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected: exit 0, no stderr.

Revset-`upstream` false-positive regression (deliberate
inclusion to test that `-r upstream` is NOT matched):

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote origin -r upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected: exit 0, no stderr. (The token `upstream` here
is the value of `-r/--revisions`, not `--remote`.)

- [ ] **Step 2f: Set description and open the next
  change.**

```sh
jj describe -m "feat(hook): deny jj git push --remote upstream

Adds a guard at the top of scripts/hooks/block-mutating-git.sh
that denies 'jj git push --remote upstream' and
'jj git push --remote=upstream' (both forms) with exit 2
and a diagnostic naming the spec path.

The short flag -r is deliberately not matched: in jj 0.41
-r resolves to --revisions, not --remote; matching it would
produce a false positive on a revset literally named
'upstream'. See spec § Hook and configuration changes for
the design and § Testing T5/T6/T9 for the test surface."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 3: Add the push-target reminder to step 6 of `pre-push.sh`

**Files:**

- Modify: `scripts/pre-push.sh` lines 57-63 (the step-6
  heredoc).
- Test: a one-line grep.

- [ ] **Step 3a: Write the failing test (grep the file
  for the new reminder line).**

```sh
grep -F "push target is \`origin\`, not \`upstream\`" \
  scripts/pre-push.sh
echo "exit=$?"
```

Expected after Task 3: exit 0 with one line of output.

- [ ] **Step 3b: Run the test now and confirm it
  fails.**

Same command. Expected NOW: exit 1, no output.

- [ ] **Step 3c: Edit the step-6 heredoc to add the
  reminder.**

Find lines 57-63 of `scripts/pre-push.sh`:

```bash
# Step 6: user-driven gates (reminders, not mechanical checks).
step "Step 6: user-driven gates (reminders)"
cat <<'EOF'
Confirm before pushing:
  - lean4:golf and lean4:review ran on changed Lean code.
  - User reviewed the diff line-by-line.
EOF
```

Replace with:

```bash
# Step 6: user-driven gates (reminders, not mechanical checks).
step "Step 6: user-driven gates (reminders)"
cat <<'EOF'
Confirm before pushing:
  - lean4:golf and lean4:review ran on changed Lean code.
  - User reviewed the diff line-by-line.
  - The push target is `origin`, not `upstream`. Upstream
    receives commits only via PRs from origin
    (see docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md
     § Operations).
EOF
```

- [ ] **Step 3d: Run the test again, confirm it now
  passes.**

Same `grep -F ...` command. Expected: exit 0 with one
line.

- [ ] **Step 3e: Set description and open the next
  change.**

```sh
jj describe -m "chore(pre-push): add push-target reminder for fork-upstream flow

Step 6 of scripts/pre-push.sh now reminds the operator that
the push target is origin, not upstream. The mechanical
denial of upstream pushes lives in
scripts/hooks/block-mutating-git.sh; this is the
human-readable companion."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 4: Create `.claude/rules/fork-upstream-flow.md`

**Files:**

- Create: `.claude/rules/fork-upstream-flow.md`.
- Test: markdownlint + register sweep.

- [ ] **Step 4a: Write the rule file.**

Content of `.claude/rules/fork-upstream-flow.md` (full
file, exactly as below; the outer fence uses four
backticks so the file's content can contain inner
three-backtick fences):

````markdown
# Fork–upstream flow rules

This file is the working-time reference for the
fork–upstream flow. The rationale layer lives in
`docs/process.md` § Fork–upstream relationship; the
design spec is at
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.

## Invariants

- **Fork-first.** Push every local commit to `origin`
  before any further interaction with `upstream`.
- **No direct push to upstream.** Send commits to
  `upstream` only through merged pull requests opened
  from `origin`. The mechanical denial lives in
  `scripts/hooks/block-mutating-git.sh`.
- **Merge-commit strategy on synchronising PRs.** Every
  pull request that updates `origin/main` or
  `upstream/main` uses the merge-commit strategy
  (`gh pr merge --merge`). Squash and rebase rewrite
  history and break the append-only and
  fast-forward-sync contracts.
- **Append-only on both default branches.** Never
  rewrite the history of `origin/main` or
  `upstream/main`.
- **No `origin/main` movement while an upstream PR is
  open.** Pause topic-branch merges into `origin/main`
  between opening an upstream PR (Op 4) and the
  resulting sync (Op 6).
- **Lockstep after merge.** After an upstream PR
  merges, fast-forward `origin/main` to
  `upstream/main` before opening any further upstream
  PRs.

## Remote roles

| Remote | URL | Role |
| --- | --- | --- |
| origin | `ssh://git@github.com/rokopt/geb` | Daily fork; push target for topic branches. |
| upstream | `git@github.com:anoma/geb.git` | Canonical repository; PR target only. |

## Operations

### Op 1 — Push a topic branch to the fork

```sh
bash scripts/pre-push.sh
jj git push --remote origin -b <bookmark>
```

For the PR that follows, ignore the "Create a pull
request" URL printed by `jj git push` (it defaults to
upstream); use `gh pr create --base main --head <branch>`
with `gh repo set-default rokopt/geb` configured.

### Op 2 — Fetch from upstream

```sh
jj git fetch --remote upstream
```

### Op 3 — Synchronise fork main from upstream

Fast-forward case (`origin/main` is purely behind):

```sh
jj git fetch --remote upstream
jj bookmark set main -r main@upstream
bash scripts/pre-push.sh
jj git push --remote origin -b main
```

Divergence case (both have unique commits):

```sh
jj git fetch --remote upstream
jj new main@origin main@upstream \
  -m "chore(sync): merge upstream/main into origin/main"
jj bookmark create chore/upstream-sync-<date> -r @
# resolve conflicts via editing or `jj resolve`;
# verify with `jj status` that no conflict markers remain
bash scripts/pre-push.sh
jj git push --remote origin -b chore/upstream-sync-<date>
```

Open an internal PR against `origin/main` and merge
with `--merge`.

### Op 4 — Open a cross-repository PR to upstream

```sh
gh pr create \
  --repo anoma/geb \
  --base main \
  --head rokopt:<branch-name> \
  --title '<user-authored title>' \
  --body  '<user-authored body>'
```

Title and body are authored by the user (no
LLM-drafted text in user-facing channels). The
invocation is gated by the user-line-by-line-review
rule (`CLAUDE.md` § Hard rules).

### Op 5 — Merge the upstream PR

```sh
gh pr merge <pr-number> --repo anoma/geb --merge
```

Use `--merge` (merge-commit strategy). Requires that
the authenticated `gh` context satisfies the upstream
branch-protection ruleset.

### Op 6 — Synchronise fork main back after upstream merge

```sh
jj git fetch --remote upstream
jj bookmark set main -r main@upstream
bash scripts/pre-push.sh
jj git push --remote origin -b main
```

Falls back to Op 3's divergence branch if
`origin/main` moved during the upstream PR's open
window.

### Op 7 — Propagate upstream movement to open topic branches

```sh
jj git fetch --remote origin
jj rebase -s <topic-branch-base> -d main@origin
```

Rebase each topic branch onto the new `origin/main`.
Pushed branches undergo line-by-line review for the
force-update.
````

- [ ] **Step 4b: Lint the new file.**

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs ':.claude/rules/fork-upstream-flow.md'
echo "exit=$?"
```

Expected: exit 0, `Summary: 0 error(s)`.

- [ ] **Step 4c: Register-sweep the new file.**

```sh
grep -niE "\b(key|important|core|advanced|complex|complicated|simple|advantage|benefit|fundamental|actually|insight|challenge|hmm|careful|difficult|future|crucial|essential|critical)\b" \
  .claude/rules/fork-upstream-flow.md
echo "exit=$?"
```

Expected: exit 1, no output.

- [ ] **Step 4d: Set description and open the next
  change.**

```sh
jj describe -m "doc(fork-upstream): add .claude/rules/fork-upstream-flow.md

New always-loaded rules file recording the fork-upstream
flow invariants, the remote roles table, and the seven
operations with their command sequences. Rationale layer
is in docs/process.md § Fork-upstream relationship
(Task 6 of the plan); design spec is at
docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 5: Update `CLAUDE.md` (Hard rules + Pointers)

**Files:**

- Modify: `CLAUDE.md` § Hard rules (the
  "No `git push` without user line-by-line review"
  rule).
- Modify: `CLAUDE.md` § Pointers table.
- Test: markdownlint + register sweep.

- [ ] **Step 5a: Read the current Hard rule wording.**

```sh
grep -n "git push" CLAUDE.md | head -5
```

Expected: locates the existing rule line.

- [ ] **Step 5b: Edit the Hard rule to explicitly name
  both remotes and the upstream-PR-only policy.**

Find the current first hard rule in `CLAUDE.md`:

```markdown
- No `git push` without user line-by-line review. The same
  human-gate rule applies to `gh` write operations
  (`gh pr create`, `gh pr merge`, `gh release create`,
  `gh issue create`, `gh issue close`, etc.).
```

Replace with:

```markdown
- No `jj git push` to `origin` without user
  line-by-line review. No direct push to `upstream` at
  all; `upstream` receives commits only through merged
  pull requests opened from `origin`. The same
  human-gate rule applies to `gh` write operations
  (`gh pr create`, `gh pr merge`, `gh release create`,
  `gh issue create`, `gh issue close`, etc.). The
  mechanical denial of direct upstream pushes lives in
  `scripts/hooks/block-mutating-git.sh`; see
  `.claude/rules/fork-upstream-flow.md` and
  `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.
```

- [ ] **Step 5c: Add Pointers-table rows for the new
  rule file and the new spec.**

Find the Pointers table (near the bottom of
`CLAUDE.md`; search for the line starting with
`| Path | Content |`). Add two rows in the same style
as the existing rows:

```markdown
| `.claude/rules/fork-upstream-flow.md` | Working-time rules for fork–upstream flow |
| `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md` | Design spec for fork–upstream flow |
```

- [ ] **Step 5d: Lint the file.**

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs ':CLAUDE.md'
echo "exit=$?"
```

Expected: exit 0.

- [ ] **Step 5e: Register-sweep the file.**

```sh
grep -niE "\b(key|important|core|advanced|complex|complicated|simple|advantage|benefit|fundamental|actually|insight|challenge|hmm|careful|difficult|future|crucial|essential|critical)\b" \
  CLAUDE.md
```

Expected: only the pre-existing line that lists those
words as a style rule (around line 75 of `CLAUDE.md`).
No other hits.

- [ ] **Step 5f: Set description and open the next
  change.**

```sh
jj describe -m "doc(fork-upstream): expand CLAUDE.md push rule and add Pointers rows

The first Hard rule now names origin and upstream
explicitly and states the upstream-PR-only policy. The
Pointers table gains rows for
.claude/rules/fork-upstream-flow.md and the
fork-upstream design spec."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 6: Update `docs/process.md`

**Files:**

- Modify: `docs/process.md` — add new
  § Fork–upstream relationship after § Repository
  structure.
- Modify: `docs/process.md` § jj colocated mode — add
  the `git clone` precondition note and two new
  onboarding steps.

- [ ] **Step 6a: Locate the insertion point for the new
  section.**

```sh
grep -n "^## " docs/process.md | head -10
```

Expected: locates `## Repository structure` (around
line 10) and the immediately following section. The new
section goes after `## Repository structure` and before
the next level-2 (`##`) heading.

- [ ] **Step 6b: Insert the new § Fork–upstream
  relationship section.**

Add the following section text after § Repository
structure, before the next section:

```markdown
## Fork–upstream relationship

The local working copy is a clone of the fork at
`rokopt/geb` ("origin"), itself a fork of the canonical
repository at `anoma/geb` ("upstream"). Both are
administered by the same operator. Daily work pushes to
the fork; upstream receives commits only through merged
pull requests opened from the fork.

### Remote roles

| Remote | URL | Role |
| --- | --- | --- |
| origin | `ssh://git@github.com/rokopt/geb` | Daily fork; push target for topic branches. |
| upstream | `git@github.com:anoma/geb.git` | Canonical repository; PR target only. |

### Invariants

The fork-first push rule, the no-direct-push-to-upstream
rule, the merge-commit-strategy-on-synchronising-PRs
rule, the append-only-on-both-default-branches rule, and
the lockstep-after-merge rule are recorded in directive
form in `.claude/rules/fork-upstream-flow.md`. The
mechanical denial of direct upstream pushes lives in
`scripts/hooks/block-mutating-git.sh`.

The full design and reasoning are at
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.
```

- [ ] **Step 6c: Locate the onboarding sequence in
  § jj colocated mode.**

```sh
grep -n "jj git init --colocate" docs/process.md
```

Expected: locates the existing step 1.

- [ ] **Step 6d: Add the precondition note at the top
  of the onboarding sequence.**

Read the current text at `docs/process.md` lines
200-205. The sequence currently begins with (verbatim):

````markdown
A new developer onboards with this exact sequence, run from the
parent `geb/` root. Per-repo configuration is set before the
first `jj git fetch --remote origin` so the fetch applies the
`fetch-tags` pattern:

1. `jj git init --colocate`.
````

Replace lines 200-205 with (verbatim; preserve the
80-character line-wrap):

````markdown
A new developer onboards with this exact sequence, run from the
parent `geb/` root. The sequence assumes the working copy was
created by `git clone ssh://git@github.com/rokopt/geb.git geb`,
which registers `origin` as a git remote pointing at
`rokopt/geb` and places `geb/` as the parent of `geb-lean/`. If
`origin` is absent, register it with `git remote add origin
ssh://git@github.com/rokopt/geb` before continuing. Users who
prefer `jj git clone --colocate` arrive at an equivalent state
but skip step 1 (`jj git init --colocate`) and continue from
step 2. Per-repo configuration is set before the first
`jj git fetch --remote origin` so the fetch applies the
`fetch-tags` pattern:

1. `jj git init --colocate`.
````

- [ ] **Step 6e: Add the new onboarding steps.**

The current sequence is (paraphrased):

1. `jj git init --colocate`
2. Per-repo configuration (`git.private-commits`,
   `remotes.origin.fetch-tags`)
3. Per-developer signing and identity
4. `jj git fetch --remote origin`
5. `bash geb-lean/scripts/check-jj-setup.sh`

Add (a) into step 2's bullet list as a sibling, and (b)
as a new step 5 (renumbering the verification to step
6):

Find the step-2 bullet list, which currently lists:

```markdown
2. Per-repo configuration:
   - `jj config set --repo git.private-commits 'conflicts()'`
   - `jj config set --repo remotes.origin.fetch-tags
     'glob:cutover-*'`
```

Add the recommended-but-not-enforced
`remotes.upstream.fetch-tags` line as a third sibling:

```markdown
2. Per-repo configuration:
   - `jj config set --repo git.private-commits 'conflicts()'`
   - `jj config set --repo remotes.origin.fetch-tags
     'glob:cutover-*'`
   - `jj config set --repo remotes.upstream.fetch-tags
     'glob:cutover-*'` (recommended; mirrors the origin
     entry for a later cutover-tag propagation. Not
     enforced by `check-jj-setup.sh`.)
```

Find step 4 and step 5 at `docs/process.md` lines
217-220 (which is the `check-jj-setup.sh` verification).
Insert a new step between them.

Current sequence ends with (verbatim):

````markdown
4. `jj git fetch --remote origin` to mirror bookmarks into jj's
   view.
5. `bash geb-lean/scripts/check-jj-setup.sh` to verify the
   configuration.
````

Replace lines 217-220 with (verbatim):

````markdown
4. `jj git fetch --remote origin` to mirror bookmarks into jj's
   view.
5. `gh repo set-default rokopt/geb` to direct `gh` default-base
   commands at the fork. See
   `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`
   § Per-clone `gh` configuration for rationale and reversal.
6. `bash geb-lean/scripts/check-jj-setup.sh` to verify the
   configuration.
````

- [ ] **Step 6f: Lint and register-sweep
  `docs/process.md`.**

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs ':docs/process.md'
echo "exit=$?"
```

Expected: exit 0.

```sh
grep -niE "\b(key|important|core|advanced|complex|complicated|simple|advantage|benefit|fundamental|actually|insight|challenge|hmm|careful|difficult|future|crucial|essential|critical)\b" \
  docs/process.md | grep -vE "signing\.key|globs.*key"
```

Expected: no output beyond pre-existing technical-term
matches (the `grep -v` filter excludes them).

- [ ] **Step 6g: Set description and open the next
  change.**

```sh
jj describe -m "doc(fork-upstream): add Fork-upstream § to process.md and extend onboarding

docs/process.md gains a new § Fork-upstream relationship
after § Repository structure, with the remote roles
table and pointers to the new rules file and design
spec. § jj colocated mode gains a precondition note
(git clone vs jj git clone --colocate), a recommended
remotes.upstream.fetch-tags step, and a
gh repo set-default rokopt/geb step. The
check-jj-setup.sh verification step renumbers
accordingly."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 7: Update `.claude/rules/ci-and-workflow.md`

**Files:**

- Modify: `.claude/rules/ci-and-workflow.md` Pre-push
  checklist subsection.

- [ ] **Step 7a: Locate the pre-push-checklist
  reminders block.**

```sh
grep -n "user-driven gates" .claude/rules/ci-and-workflow.md
```

Expected: locates the bullet list of step-6 reminders.

- [ ] **Step 7b: Add the push-target reminder line.**

The current bullet list (paraphrased) reads:

```markdown
The script additionally surfaces user-driven gates as
reminders:

- `lean4:golf` and `lean4:review` ran on changed Lean code;
- line-by-line user diff review of every change about to be
  pushed.
```

Add a third bullet:

```markdown
The script additionally surfaces user-driven gates as
reminders:

- `lean4:golf` and `lean4:review` ran on changed Lean code;
- line-by-line user diff review of every change about to be
  pushed;
- the push target is `origin`, not `upstream`. Upstream
  receives commits only via PRs opened from origin (see
  `.claude/rules/fork-upstream-flow.md` and
  `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`).
```

- [ ] **Step 7c: Lint and register-sweep.**

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs ':.claude/rules/ci-and-workflow.md'
echo "exit=$?"
```

Expected: exit 0.

- [ ] **Step 7d: Set description and open the next
  change.**

```sh
jj describe -m "doc(ci-workflow): add push-target reminder to pre-push checklist

.claude/rules/ci-and-workflow.md § Pre-push checklist
gains a third user-driven-gate bullet reminding the
operator that the push target is origin, not upstream.
The mechanical denial of upstream pushes lives in
scripts/hooks/block-mutating-git.sh; the line in
scripts/pre-push.sh is the human-readable companion."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 8: Update `README.md`

**Files:**

- Modify: `README.md` § Pointers to upstream and
  sibling projects.

- [ ] **Step 8a: Locate the existing pointers
  section.**

```sh
grep -n "Pointers to upstream" README.md
```

Expected: locates the section heading.

- [ ] **Step 8b: Add the fork–upstream paragraph.**

Read the current section text (it has paragraphs about
`geb-mathlib` and the library dependencies). Add a new
paragraph as the first bullet/paragraph in the section
(i.e., before the existing `geb-mathlib` paragraph):

```markdown
- The canonical repository for this monorepo is
  `anoma/geb`. The local working copy is a clone of the
  fork at `rokopt/geb`. Daily work pushes to the fork;
  upstream receives commits only through merged pull
  requests opened from the fork. The flow's invariants,
  operations, and mechanical enforcement are recorded in
  [`.claude/rules/fork-upstream-flow.md`](.claude/rules/fork-upstream-flow.md);
  the design spec is at
  [`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`](docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md).
```

- [ ] **Step 8b': Reconcile § Contribution pointers
  step 1.**

`README.md` § Contribution pointers step 1 (lines
87-89) currently reads (verbatim):

````markdown
1. Clone the parent monorepo at
   <https://github.com/anoma/geb>; `geb-lean/` is a
   subdirectory.
````

After Step 8b's addition the README would contain two
contradictory clone instructions (one paragraph says
clone the fork; this step says clone upstream). Replace
lines 87-89 with (verbatim):

````markdown
1. Clone the fork at <https://github.com/rokopt/geb>
   (single-developer entry path) or the canonical
   repository at <https://github.com/anoma/geb>
   (external-contributor entry path); `geb-lean/` is a
   subdirectory in either case. The flow recorded in
   [`.claude/rules/fork-upstream-flow.md`](.claude/rules/fork-upstream-flow.md)
   assumes the fork.
````

- [ ] **Step 8c: Lint and register-sweep.**

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs ':README.md'
echo "exit=$?"
```

Expected: exit 0.

```sh
grep -niE "\b(key|important|core|advanced|complex|complicated|simple|advantage|benefit|fundamental|actually|insight|challenge|hmm|careful|difficult|future|crucial|essential|critical)\b" \
  README.md
```

Expected: no output.

- [ ] **Step 8d: Set description and prepare for
  Task 9.**

```sh
jj describe -m "doc(fork-upstream): record fork-upstream relationship in README.md

README.md § Pointers to upstream and sibling projects
gains a paragraph identifying anoma/geb as the canonical
repository and rokopt/geb as the local fork, with
pointers to the rules file and design spec."
jj bookmark set docs/fork-upstream-flow -r @
jj new -m "wip"
```

---

## Task 9: Operator config — `gh repo set-default rokopt/geb`

**Files:**

- Mutates `.git/config` at the parent `geb/` root
  (per-clone state, not tracked content). No commit.

- [ ] **Step 9a: Verify the current state (T10 before
  fix).**

```sh
gh repo set-default --view
echo "exit=$?"
```

Expected (current state): exit 0, empty stdout.

- [ ] **Step 9b: Set the default.**

```sh
gh repo set-default rokopt/geb
```

Expected: confirmation line, exit 0.

- [ ] **Step 9c: Verify with T10.**

```sh
gh repo set-default --view
echo "exit=$?"
```

Expected: exit 0, stdout exactly `rokopt/geb`.

- [ ] **Step 9d: Verify the underlying git config
  entry.**

```sh
git config --get remote.origin.gh-resolved
echo "exit=$?"
```

Expected: exit 0, stdout exactly `base`.

- [ ] **Step 9e: No commit. Working copy unchanged.**

Confirm:

```sh
jj diff -r @ --summary
```

Expected: no output (working copy clean against the
empty `wip` change).

---

## Task 10: Operator config — `remotes.upstream.fetch-tags`

**Files:**

- Mutates `geb/.jj/repo/config.toml` (per-clone state).
  No commit.

- [ ] **Step 10a: Verify current state.**

```sh
jj config list --repo remotes.upstream.fetch-tags
echo "exit=$?"
```

Expected: exit 1 (config not set) OR a line showing the
existing value. The recommended target value is
`glob:cutover-*`.

- [ ] **Step 10b: Set the config.**

```sh
jj config set --repo remotes.upstream.fetch-tags 'glob:cutover-*'
```

Expected: no error.

- [ ] **Step 10c: Verify the new value.**

```sh
jj config list --repo remotes.upstream.fetch-tags
```

Expected: stdout
`remotes.upstream.fetch-tags = "glob:cutover-*"`.

- [ ] **Step 10d: Run `check-jj-setup.sh` to confirm it
  still passes (the script does not assert this entry,
  but should not fail).**

```sh
bash scripts/check-jj-setup.sh
echo "exit=$?"
```

Expected: exit 0, output `check-jj-setup: OK`.

- [ ] **Step 10e: No commit.**

---

## Task 11: Acceptance test run (T1–T10)

**Files:**

- Runs T1–T10 from the spec. No edits, no commits.

- [ ] **Step 11a: T1 — both remotes registered.**

```sh
jj git remote list
```

Expected: two lines, one starting with `origin`, one
with `upstream`.

- [ ] **Step 11b: T2 — `check-jj-setup.sh` passes.**

```sh
bash scripts/check-jj-setup.sh
echo "exit=$?"
```

Expected: exit 0 with line `check-jj-setup: OK`.

- [ ] **Step 11c: T3 — hook permits `git fetch
  upstream`.**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git fetch upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected: exit 0, no stderr.

- [ ] **Step 11d: T4 (regression) — hook denies
  `git push upstream`.**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git push upstream main"}}' \
  | bash scripts/hooks/block-mutating-git.sh 2>&1
echo "exit=$?"
```

Expected: exit 2; stderr contains
`block-mutating-git: blocked` and a `jj equivalent:`
line.

- [ ] **Step 11e: T5 — hook denies
  `jj git push --remote upstream`.**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh 2>&1
echo "exit=$?"
```

Expected: exit 2; stderr names the spec path.

- [ ] **Step 11f: T6 — hook permits
  `jj git fetch --remote upstream`.**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git fetch --remote upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
echo "exit=$?"
```

Expected: exit 0, no stderr.

- [ ] **Step 11g: T7 — `jj git fetch --remote upstream`
  succeeds.**

```sh
jj git fetch --remote upstream
git branch -r | grep '^  upstream/main$'
echo "exit=$?"
```

Expected: first command exit 0; second command prints
one line and exits 0.

- [ ] **Step 11h: T8 — `gh` permissions probe.**

```sh
gh api repos/anoma/geb --jq '.permissions'
gh api repos/anoma/geb/branches/main --jq '.protected'
```

Expected: a JSON permissions object with at minimum
`pull=true`; the second call prints `true`.

- [ ] **Step 11i: T9 — hook denies
  `jj git push --remote=upstream` (equals-form).**

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote=upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh 2>&1
echo "exit=$?"
```

Expected: exit 2; stderr names the spec path.

- [ ] **Step 11j: T10 — `gh repo set-default --view`
  returns `rokopt/geb`.**

```sh
gh repo set-default --view
echo "exit=$?"
```

Expected: exit 0, stdout exactly `rokopt/geb`.

- [ ] **Step 11k: Abandon the empty wip change.**

The final `jj new -m "wip"` from Task 8 is an empty
change with no edits. Abandon it:

```sh
jj abandon @
```

Expected: the change is abandoned; `@` returns to the
README change.

- [ ] **Step 11l: Confirm branch state.**

```sh
jj log -r 'main..docs/fork-upstream-flow' --no-graph \
  -T 'change_id.short() ++ " " ++ commit_id.short()
      ++ " :: " ++ description.first_line() ++ "\n"'
```

Expected: a linear sequence of ten commits (Tasks 0, A,
1, 2, 3, 4, 5, 6, 7, 8) on top of `main`, all with
sensible descriptions and no remaining `wip` lines.

---

## Self-review checklist (already run by plan author)

- **Spec coverage:** every section of
  `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`
  in § Hook and configuration changes, § Documentation
  changes, § Per-clone `gh` configuration, § Per-repo
  `jj` configuration, and § Testing and verification
  maps to a task above. § State at spec time facts are
  inputs, not deliverables.
- **Placeholder scan:** no TBD / TODO / "fill in" /
  "similar to Task N" / "add appropriate error handling"
  in the steps above. Every step that changes code
  shows the code.
- **Type/method consistency:** the deny-clause names
  used in Task 2 (`--remote upstream`,
  `--remote=upstream`) match the spec's T5 and T9
  expected inputs. The bookmark names used
  (`docs/fork-upstream-flow`,
  `chore/upstream-sync-<date>`) are consistent across
  Tasks 0, 4, and the rule file. The grep filter on
  register sweeps consistently excludes `signing.key`
  and `globs key` (pre-existing technical-term hits) so
  the verification is repeatable.
- **Out-of-scope reminder:** Tasks 1–8 land in tree
  state and are commits on `docs/fork-upstream-flow`.
  Tasks 9–10 are operator-local config (not commits).
  Task 11 is verification (not a commit).
