# geb-lean process-bootstrap implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land the structural process refactor specified in
`docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`,
then retire `.session/` once every legacy workstream entry has
been triaged.

**Architecture:** The refactor is partitioned into two
milestones. Milestone A is bounded structural work
(`CLAUDE.md` split, `.claude/rules/`, hooks, scripts, CI
additions, `LICENSE`, `README.md` rewrite, `TODO.md`,
`docs/process.md`, `docs/index.md`,
`docs/lean-resources.md`, `jj` colocated initialisation,
cutover commit and signed tag, `integration` branch,
GitHub Rulesets). Milestone B is open-ended `.session/`
triage plus the report-only → fail-mode flip of the
axiom-check CI job.

**Tech stack:** Lean 4 + Lake (existing build), `jj` 0.41+
(VCS), `markdownlint-cli2` (markdown lint),
`scripts/check-axioms.sh` (vendored derivative of the
`lean4-skills` plugin's `check_axioms_inline.sh`),
`scripts/hooks/*.sh` (Bash, `jq` for JSON parsing in the
PreToolUse hook), GitHub Actions (CI), GitHub Rulesets
(branch and tag protection).

---

## Reading order for the implementer

Before starting Task A1, read:

1. `docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`
   end-to-end. The spec is authoritative on every design
   decision; this plan only sequences the implementation.
2. `CLAUDE.md` (the existing one) for the prose register and
   the forbidden-word list. Persistent prose written by this
   plan must respect that list.
3. `docs/superpowers/specs/2026-05-07-process-bootstrap-design.review-15.md`,
   `.review-16.md`, `.review-17.md`, and `.review-jj-0.41.md`
   to confirm closed decisions. Do not re-litigate these.

The plan's tasks reference spec sections by name (e.g.
"§ jj setup", "§ Hooks") rather than reproducing the spec's
content. Each task's verification signal is named explicitly.

---

## Closed decisions reproduced verbatim from the hand-off

The plan respects these without re-litigation:

- Layered `CLAUDE.md` ≤ 200 lines plus rule files in
  `.claude/rules/`.
- `jj` 0.41 colocated mode with
  `git.private-commits = "conflicts()"` and
  `remotes.origin.fetch-tags = "glob:cutover-*"`, both
  per-repo.
- Default-deny `block-mutating-git` PreToolUse hook with
  closed allowlists. **Tag operations are user-direct and
  NOT allowlisted.**
- `check-signing-key` SessionStart hook.
- Cutover commit + signed git tag (`cutover-2026-MM-DD`) +
  GitHub Rulesets (Tag protection rules a deprecated
  fallback).
- Append-only `main` from cutover forward, verified by
  `git log --first-parent origin/main`.
- Apache 2.0 `LICENSE`; no per-file copyright headers.
- `moreLeanArgs = ["-DwarningAsError=true"]` preserved.
- `axiom_check` job initially in report-only mode; flipped
  to fail-mode in Milestone B.
- Adversarial review precedes user review for all specs and
  plans.
- `remotes.<name>.fetch-tags` is experimental; the spec
  documents the fallback (explicit raw-git refspec form +
  matching allowlist entry + on-boarding step). The plan
  references but does not duplicate that fallback.

---

## Hook-wiring discipline (load-bearing for the plan's order)

Task A27 wires `.claude/settings.json`, which activates the
`block-mutating-git` PreToolUse hook for subsequent
sessions (and possibly the same session). The hook denies
`git add`, `git commit`, `git switch`, and every other
mutating raw-git form. Therefore A27 is the **final
Claude-direct commit-producing task** in Milestone A.

- Tasks A1 through A23 land their commits with plain
  `git add` / `git commit` because the hook is unwired
  through that range.
- A24 is user-direct (`jj git init --colocate`). After A24
  the working tree has both `.git/` and `.jj/`.
- A25 (`pre-push.sh`) is the last `git add` / `git commit`
  step before A27.
- A26 (the `conflicts()` smoke test) is non-commit-producing.
- A27 lands the settings file with `git add` /
  `git commit`. After this task lands, no further
  Claude-direct `git add` / `git commit` is permitted in
  the same session.
- A28 onward is non-commit-producing (verification) or
  user-direct (push, signed tag, follow-up doc commit on a
  topic branch via `jj describe`, GitHub UI).

This ordering is the resolution of the cycle-1 review's
blocker B1 and is mandatory.

---

## User-direct steps (Claude must NOT attempt)

These tasks are performed by the user in the user's own
terminal, outside Claude Code. The `block-mutating-git`
PreToolUse hook only sees Claude's tool invocations, so
user-direct steps are not gated by the hook; the human-gate
convention applies instead.

- Task A24: `jj git init --colocate` and the
  `jj config set` on-boarding sequence.
- Task A29: pushing the topic branch's merge commit to
  `main` (the cutover commit).
- Task A30: creating, signing, and pushing the
  `cutover-YYYY-MM-DD` tag.
- Task A31: creating the follow-up topic branch
  `docs/cutover-sha-record`, committing the SHA into
  `docs/process.md` via `jj describe`, pushing, opening a
  PR, merging.
- Task A32: pushing the `integration` bookmark to the
  remote.
- Task A33: configuring GitHub Rulesets (Repository
  settings → Rules → Rulesets) for `main` and for the tag
  pattern `cutover-*`.
- Milestone B: per-workstream triage decisions (Claude
  surfaces a proposed classification; the user confirms or
  amends).

Every other task is performed by Claude.

---

## Milestone A — process bootstrap

Tasks A1 through A34 land the structural refactor. Each
task is one self-contained edit set with one verification
signal. Sequence dependencies are named in the **Depends
on:** line of each task. Run `lake build && lake test`
after every task that touches anything Lake compiles; run
`markdownlint-cli2 '**/*.md'` against any `.md` file the
task creates or modifies.

### Task A1: Create the topic branch

**Files:** none (VCS only).

**Depends on:** nothing.

- [ ] **Step 1: Create the topic branch.**

```sh
git switch -c chore/process-refactor
```

- [ ] **Step 2: Confirm baseline build is clean.**

```sh
lake build
lake test
```

Expected: both succeed without warnings.

- [ ] **Step 3: No commit yet.** The branch exists in the
  working tree only. Subsequent tasks land their own
  commits.

**Verification:** `git status` shows the branch is checked
out; `lake build` and `lake test` succeed.

---

### Task A2: Add `lintDriver = "batteries/runLinter"` to `lakefile.toml`

**Files:** modify `lakefile.toml`.

**Depends on:** A1.

- [ ] **Step 1: Add the lintDriver field.**

Edit `lakefile.toml` to add a new top-level line after the
`testDriver = "GebLeanTests"` line:

```toml
lintDriver = "batteries/runLinter"
```

- [ ] **Step 2: Verify `lake lint` runs.**

```sh
lake lint
```

Expected: exits 0 with no diagnostics.

- [ ] **Step 3: Positively verify the linter is wired.**

Introduce a deliberate violation in a scratch
`GebLean/Utilities/_LintProbe.lean` file containing a
single unused `set_option` or an unused `let`-binding that
trips `linter.unusedVariables`. Run `lake lint`; expected:
the linter flags the file. Delete the scratch file; run
`lake lint` again; expected: quiet.

- [ ] **Step 4: Confirm no probe file remains, then commit.**

```sh
test ! -f GebLean/Utilities/_LintProbe.lean
git add lakefile.toml
git commit -m "chore(lake): wire batteries/runLinter as lintDriver"
```

The `test ! -f` check is a hard gate: if the probe file is
still present, abort the commit and re-run step 3's
deletion before retrying.

**Verification:** `lake lint` is quiet on the current
source; the deliberate-violation probe was flagged then
removed; the committed diff contains only `lakefile.toml`.

---

### Task A3: Confirm `.markdownlint-cli2.jsonc` is present and clean

**Files:** verify (and if absent, author)
`.markdownlint-cli2.jsonc`.

**Depends on:** A1.

- [ ] **Step 1: Precondition check.**

```sh
test -f .markdownlint-cli2.jsonc
```

If the file is absent, author it per spec
§ `.markdownlint-cli2.jsonc` (close to markdownlint
defaults; MD013 line-length checks exempted for tables
and code blocks; ignores `.lake/`, `.jj/`, `node_modules/`)
and commit it on this task. If the file is present, no
edit is needed.

- [ ] **Step 2: Run markdownlint against the whole tree.**

```sh
markdownlint-cli2 '**/*.md'
```

Expected: zero violations against files inside the project
scope. If any appear in pre-existing files outside
`.session/`, surface them to the user; do not silently
rewrite unrelated material.

**Verification:** the file exists; the lint command exits
0 (or only flags pre-existing material outside the
refactor's scope, which is surfaced to the user rather
than auto-fixed).

---

### Task A4: Add `markdown-lint.yml` GitHub Actions workflow

**Files:** create `.github/workflows/markdown-lint.yml`.

**Depends on:** A3.

- [ ] **Step 1: Resolve the action SHAs.**

Look up the latest released SHA for `actions/checkout` and
for `DavidAnson/markdownlint-cli2-action`. Use SHAs, not
tags. Record both resolved SHAs in the workflow file's
`uses:` fields.

- [ ] **Step 2: Author the workflow.**

```yaml
name: markdown-lint

on:
  push:
    branches: [main]
  pull_request:

jobs:
  markdown-lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@<SHA-1>
      - uses: DavidAnson/markdownlint-cli2-action@<SHA-2>
        with:
          globs: '**/*.md'
          config: '.markdownlint-cli2.jsonc'
```

The two `<SHA-N>` placeholders are replaced with resolved
SHAs. The `with:` block names `globs` and `config`
explicitly so the action passes both unexpanded to the
underlying binary; this avoids shell pre-expansion of
globs that would bypass the config's `ignores` list.

`integration` is intentionally omitted from the trigger
list at this point: that branch is initialised at A32
(post-cutover). When it lands, A32's verification
re-tests the workflow against the new branch.

- [ ] **Step 3: Verify no `<SHA-N>` placeholder remains.**

```sh
! grep -n '<SHA-' .github/workflows/markdown-lint.yml
```

Expected: the negation succeeds (no placeholders found).
If any remain, abort and resolve before committing.

- [ ] **Step 4: Commit.**

```sh
git add .github/workflows/markdown-lint.yml
git commit -m "ci: add markdown-lint workflow"
```

**Verification:** the workflow file is YAML-valid; both
SHAs are committed verbatim (no `<SHA-N>` strings remain).

---

### Task A5: Add `LICENSE` (Apache 2.0)

**Files:** create `LICENSE`.

**Depends on:** A1.

- [ ] **Step 1: Write `LICENSE`.**

Copy the standard Apache 2.0 text verbatim from
`https://www.apache.org/licenses/LICENSE-2.0.txt`. The
text is unmodified.

- [ ] **Step 2: Commit.**

```sh
git add LICENSE
git commit -m "chore: add Apache 2.0 LICENSE"
```

**Verification:** the file's first non-blank line reads
`Apache License` (with the canonical leading whitespace
preserved); the file matches the canonical text
byte-for-byte (or after normalising line endings to LF).

---

### Task A6: Create `scripts/` and `scripts/hooks/` directories

**Files:** create `scripts/` and `scripts/hooks/`.

**Depends on:** A1.

- [ ] **Step 1: Make the directories.**

```sh
mkdir -p scripts/hooks
```

- [ ] **Step 2: No standalone commit yet.** The directories
  carry no content of their own; the next tasks add files
  and commit them in their own diffs.

**Verification:** `ls -d scripts scripts/hooks` returns
both paths.

---

### Task A7: Vendor `scripts/check-axioms.sh`

**Files:** create `scripts/check-axioms.sh`.

**Depends on:** A6.

- [ ] **Step 1: Resolve the upstream source.**

The upstream is the `lean4-skills` plugin's
`check_axioms_inline.sh`. Find the file under
`/home/terence/.claude/plugins/cache/lean4-skills/...`
(present at session start per the SessionStart message).
Record the source URL and commit SHA in the vendored
file's header comment.

- [ ] **Step 2: Vendor the script with the modification.**

The local modifications:

- Allowlist reduced to `propext`, `Quot.sound`,
  `quot.sound` (drop `Classical.choice` from upstream's
  allowlist).
- The `AXIOM_ALLOW` comment-scanning behaviour described
  in the spec § Auxiliary scripts.
- A header comment recording the upstream URL, upstream
  SHA, and the diff against upstream so subsequent
  re-vendoring can detect drift.

The exact body content is the upstream script with the
allowlist constant changed. Reference: spec § Auxiliary
scripts → "scripts/check-axioms.sh" for the AXIOM_ALLOW
syntax (single-line `--` comment of the form
`-- AXIOM_ALLOW: <axiom-name> (rationale text)` placed
before the declaration's docstring, scanned up through
adjacent `--` and through any preceding `/-- ... -/`
docstring).

- [ ] **Step 3: Make it executable.**

```sh
chmod +x scripts/check-axioms.sh
```

- [ ] **Step 4: Smoke-test the script.**

```sh
bash scripts/check-axioms.sh GebLean/ test/
```

Expected: the script runs to completion. In report-only
mode (no CI gating yet) the output may list many flagged
declarations because mathlib transitively introduces
`Classical.choice`; that is the documented current state.
What matters at this step: the script runs, emits its
output, and exits with a defined code.

- [ ] **Step 5: Commit.**

```sh
git add scripts/check-axioms.sh
git commit -m "chore(scripts): vendor check-axioms.sh from lean4-skills"
```

**Verification:** the script is executable; running it
produces output; the header comment records the upstream
URL and SHA.

---

### Task A8: Author `scripts/check-jj-setup.sh`

**Files:** create `scripts/check-jj-setup.sh`.

**Depends on:** A6.

- [ ] **Step 1: Author the script.**

Three anchored-string assertions per the spec § jj setup:

- (a) `jj config list --repo git.private-commits` output
  equals `conflicts()` exactly (anchored, not substring).
- (b) `jj config list --repo remotes.origin.fetch-tags`
  output equals `glob:cutover-*` exactly (anchored).
- (c) at least one of `jj config get signing.behavior` or
  `git config --get commit.gpgsign` returns a value
  indicating signing is active.

Each failure exits non-zero with a message pointing the
developer at `docs/process.md` § jj colocated mode.

The cutover-tag local presence is **not** asserted (the
script must succeed pre-cutover too).

- [ ] **Step 2: Make it executable.**

```sh
chmod +x scripts/check-jj-setup.sh
```

- [ ] **Step 3: Smoke-test by direct invocation.**

Run the script in the current repository (which is not
yet jj-initialised). Expected: it exits non-zero with a
diagnostic message. The script's positive path (zero exit
after on-boarding) is verified at A24.

- [ ] **Step 4: Commit.**

```sh
git add scripts/check-jj-setup.sh
git commit -m "chore(scripts): add check-jj-setup.sh"
```

**Verification:** the script runs, emits a diagnostic, and
exits non-zero in a non-jj-initialised state; the
diagnostic names `docs/process.md`.

---

### Task A9: Author `scripts/hooks/block-mutating-git.sh`

**Files:** create `scripts/hooks/block-mutating-git.sh`.

**Depends on:** A6.

- [ ] **Step 1: Author the hook script.**

Behaviour per the spec § Hooks:

- Reads JSON from stdin.
- Default-deny with closed allowlists.
- If `.jj/` exists in `CLAUDE_PROJECT_DIR`, strips
  `jj git X` forms from the inspected command (so jj's
  git interop works).
- Read-only subcommand allowlist as in spec.
- `git config` allowlist limited to `--get`, `--list`,
  `--get-all`.
- `git fetch` allowlist: bare `git fetch`,
  `git fetch origin`, `git fetch origin
  refs/pull/*/head:*` (literal-token equality after argv
  parsing).
- `git clone` rule: target argument resolved to absolute
  path must not equal `$PWD` and must not have `$PWD` as a
  prefix.
- Short-form / long-form flag canonicalisation.
- **No tag-push or tag-creation allowlist entry** (tag
  operations are user-direct).
- On deny: prints translation message to stderr and exits 2.
- On allow: exits 0.

The spec contains the full list of allowlisted read-only
subcommands and the exact stderr message wording. Refer
to spec § Hooks → "Read-only subcommand allowlist" and
"On block".

- [ ] **Step 2: Make it executable.**

```sh
chmod +x scripts/hooks/block-mutating-git.sh
```

- [ ] **Step 3: Commit (without smoke tests yet).**

```sh
git add scripts/hooks/block-mutating-git.sh
git commit -m "chore(hooks): add block-mutating-git.sh"
```

**Verification:** the script is executable; a syntax check
(`bash -n scripts/hooks/block-mutating-git.sh`) succeeds.
The behavioural smoke tests are A10.

---

### Task A10: Smoke-test `block-mutating-git.sh` by direct invocation

**Files:** none (the hook test cases are recorded in this
task's body and re-runnable by copy-paste; no separate
test runner is authored, per spec § "Open questions"
deferring `scripts/hooks/tests/`).

**Depends on:** A9.

- [ ] **Step 1: Run each of the five required cases.**

Required cases per spec verification item 12, fed to the
hook by JSON-stdin in the format Claude Code's PreToolUse
hooks expect. The exact JSON shape lives in spec § Hooks;
the structure for each case is `{"tool_name": "Bash",
"tool_input": {"command": "<the-command>"}}`. Each case
runs:

```sh
echo '<json>' | bash scripts/hooks/block-mutating-git.sh; \
  echo "exit=$?"
```

Required cases and expected exit codes:

- (a) `git commit -m '...'` → 2 (denied; default deny).
- (b) `jj git push --remote origin -b feat/x` → 0
  (allowed; `jj git X` forms are stripped from scope).
- (c) `git status` → 0 (allowed read-only subcommand).
- (d) `git checkout -b new-branch` → 2 (denied mutating
  subcommand).
- (e) `git push origin
  'refs/tags/v1.0.0:refs/tags/v1.0.0'` → 2 (denied; no
  tag-push allowlist entry).

- [ ] **Step 2: Confirm every case matches expectation.**

If any case's actual exit differs from expected, diagnose
in the hook script, fix, and re-run all five before
proceeding. No commit is needed unless the hook script
itself was edited (in which case the commit message is
`fix(hooks): adjust block-mutating-git.sh per smoke test`).

**Verification:** all five cases match expectation. The
five lines of output are captured and pasted into the
A28 verification report.

---

### Task A11: Author `scripts/hooks/check-signing-key.sh`

**Files:** create `scripts/hooks/check-signing-key.sh`.

**Depends on:** A6.

- [ ] **Step 1: Author the hook script.**

Behaviour per spec § Hooks → `check-signing-key.sh`:

1. Query `git config --get commit.gpgsign`; if `true`,
   git-side signing is active.
2. Query `jj config get signing.behavior`; if `own` or
   `force`, jj-side signing is active.
3. If either is active, dispatch on the configured
   backend (`gpg`, `ssh`) and warm the appropriate agent.
   For `gpg`: query
   `gpg-connect-agent 'keyinfo --list' /bye | grep -q ' 1 '`;
   if not cached, run
   `echo warm | gpg --clearsign >/dev/null` to seed the
   cache via pinentry.
4. Exit 0 either way (never denies session start).

- [ ] **Step 2: Make it executable.**

```sh
chmod +x scripts/hooks/check-signing-key.sh
```

- [ ] **Step 3: Smoke-test.**

```sh
bash scripts/hooks/check-signing-key.sh
```

Expected: exits 0. If signing is configured locally, gpg
or ssh agent activity may follow; if not, the script
exits 0 silently.

- [ ] **Step 4: Commit.**

```sh
git add scripts/hooks/check-signing-key.sh
git commit -m "chore(hooks): add check-signing-key.sh"
```

**Verification:** the script exits 0; `bash -n` syntax
check passes.

---

### Task A12: Update `.gitignore` to permit committed `.claude/` paths

**Files:** modify `.gitignore`.

**Depends on:** A1.

- [ ] **Step 1: Replace the bulk `.claude` ignore.**

The existing `.gitignore` has `/.claude` which excludes
the whole directory. The spec requires committing
`.claude/settings.json` and the four `.claude/rules/*.md`
files. Replace `/.claude` with explicit unignore entries
that allow those committed paths while excluding
everything else under `.claude/`. Suggested form:

```text
/.claude/*
!/.claude/rules/
!/.claude/settings.json
```

The `!/.claude/rules/` line keeps the directory tracked;
the rule files are added in subsequent tasks. Existing
entries (`/.lake`,
`/.github/copilot-instructions.md`,
`/docs/.claude`, `.remember`) are preserved.

- [ ] **Step 2: Confirm `git status` reflects the intent.**

```sh
git status
```

Expected: `.claude/settings.local.json`,
`.claude/docs/`, `.claude/memory/`, `.claude/tools/`
remain ignored; `.claude/rules/` and `.claude/settings.json`
become visible (currently both empty / absent).

- [ ] **Step 3: Commit.**

```sh
git add .gitignore
git commit -m "chore(gitignore): whitelist committed .claude paths"
```

**Verification:** `git check-ignore -v
.claude/settings.json` returns nothing (path is not
ignored); `git check-ignore -v
.claude/settings.local.json` shows the path is ignored.

---

### Task A13: Add `axiom_check` job to `lean_action_ci.yml` (report-only)

**Files:** modify `.github/workflows/lean_action_ci.yml`.

**Depends on:** A7.

- [ ] **Step 1: Resolve action SHAs for any new uses.**

The job uses `actions/upload-artifact` for the artefact
upload. Look up the latest released SHA and use it
verbatim — write the resolved SHA into the workflow
file directly, without an intermediate `<SHA>`
placeholder. (A4's authoring template uses placeholders
because it adds two new actions and benefits from a
draft-then-resolve flow; A13 adds only one and the
direct-resolve approach is cleaner.)

- [ ] **Step 2: Add the job.**

The job runs `bash scripts/check-axioms.sh GebLean/ test/`
after the main build job has populated `.lake/`. **Report-
only**: the job's exit code does not gate the workflow,
but its stdout is uploaded as a CI artefact.

The job runs on every PR and every push to `main`.
`integration` is omitted from the trigger list pending
A32's branch initialisation.

- [ ] **Step 3: Commit.**

```sh
git add .github/workflows/lean_action_ci.yml
git commit -m "ci: add axiom_check job in report-only mode"
```

**Verification:** the workflow file is YAML-valid; the
job-name is `axiom_check`; the step executes the
vendored script; the `actions/upload-artifact` SHA is
committed verbatim (not a tag).

---

### Task A14: Author `.claude/rules/lean-disciplines.md`

**Files:** create `.claude/rules/lean-disciplines.md`.

**Depends on:** A12.

- [ ] **Step 1: Author the file.**

No `paths:` frontmatter (loaded unconditionally). Content
sections per spec § `.claude/rules/lean-disciplines.md`:

1. Hole-marking discipline.
2. Constructive-only Lean code.
3. Literature-citation discipline.
4. Bottom-up named-composite discipline for categorical
   equivalences.
5. Non-negotiable interfaces for categories formalising
   pre-existing mathematical objects.

The spec carries the full prose for each section; render
it into the file verbatim, observing the 80-character
line limit and the forbidden-word list.

- [ ] **Step 2: Markdown-lint the file.**

```sh
markdownlint-cli2 .claude/rules/lean-disciplines.md
```

Expected: zero violations.

- [ ] **Step 3: Commit.**

```sh
git add .claude/rules/lean-disciplines.md
git commit -m "doc(rules): add lean-disciplines unconditionally-loaded rule"
```

**Verification:** the file exists, has no `paths:`
frontmatter, and is markdownlint-clean.

---

### Task A15: Author `.claude/rules/lean-coding.md`

**Files:** create `.claude/rules/lean-coding.md`.

**Depends on:** A12.

- [ ] **Step 1: Author the file.**

YAML frontmatter:

```yaml
paths:
  - "**/*.lean"
```

Content sections per spec § `.claude/rules/lean-coding.md`:

1. Build discipline.
2. Comment and docstring rules.
3. Lean idioms.
4. `lean4` skill mapping.
5. Universe and variable hygiene.
6. No copyright or author headers in source files.
7. Reminder of unconditionally-loaded disciplines.

- [ ] **Step 2: Markdown-lint the file.**

```sh
markdownlint-cli2 .claude/rules/lean-coding.md
```

- [ ] **Step 3: Commit.**

```sh
git add .claude/rules/lean-coding.md
git commit -m "doc(rules): add lean-coding path-scoped rule"
```

**Verification:** file exists with `paths:` frontmatter
matching `**/*.lean`; markdownlint-clean.

---

### Task A16: Author `.claude/rules/markdown-writing.md`

**Files:** create `.claude/rules/markdown-writing.md`.

**Depends on:** A12.

- [ ] **Step 1: Author the file.**

YAML frontmatter:

```yaml
paths:
  - "**/*.md"
```

Content sections per spec § `.claude/rules/markdown-writing.md`:

1. Markdownlint cleanliness.
2. Prose register.
3. No development-history references.
4. Generic user references.
5. No LLM-drafted user-facing text.
6. Line length ≤ 80 characters.
7. No emojis.
8. Link conventions.

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 .claude/rules/markdown-writing.md
```

- [ ] **Step 3: Commit.**

```sh
git add .claude/rules/markdown-writing.md
git commit -m "doc(rules): add markdown-writing path-scoped rule"
```

**Verification:** file exists with `paths:` frontmatter
`**/*.md`; markdownlint-clean.

---

### Task A17: Author `.claude/rules/ci-and-workflow.md`

**Files:** create `.claude/rules/ci-and-workflow.md`.

**Depends on:** A12.

- [ ] **Step 1: Author the file.**

YAML frontmatter:

```yaml
paths:
  - ".github/workflows/**"
  - "scripts/**"
```

Content sections per spec § `.claude/rules/ci-and-workflow.md`:

1. Workflow conventions (SHA-pinning policy).
2. Pre-push checklist.
3. Hook-script conventions.
4. Commit-message convention.

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 .claude/rules/ci-and-workflow.md
```

- [ ] **Step 3: Commit.**

```sh
git add .claude/rules/ci-and-workflow.md
git commit -m "doc(rules): add ci-and-workflow path-scoped rule"
```

**Verification:** file exists with the two-glob `paths:`
frontmatter; markdownlint-clean.

---

### Task A18: Author `docs/process.md`

**Files:** create `docs/process.md`.

**Depends on:** A14, A15, A16, A17.

- [ ] **Step 1: Author the file.**

Sections per spec § `docs/process.md` — eighteen
sections, each a short paragraph (5–10 lines),
index-shaped:

1. Repository structure.
2. Phase-driven workflow.
3. Adversarial review of specs and plans.
4. Order of artefact production.
5. Verify agent claims against authoritative sources.
6. Constructive-only Lean code.
7. `main` / `integration` / topic-branch model.
8. `jj` colocated mode (with the `git clean -xdf`
   warning and the `.jj/.gitignore` self-exclusion fact).
9. Comment and docstring style.
10. Markdownlint discipline.
11. No LLM-drafted user-facing text.
12. Generic user references.
13. Process self-update mechanism.
14. GebLean-specific: literature-citation discipline.
15. GebLean-specific: bottom-up named-composite discipline.
16. GebLean-specific: non-negotiable interfaces.
17. GebLean-specific: relationship to geb-mathlib.
18. GebLean-specific: no per-file copyright or author
    headers.

§ 8 also documents the explicit
`git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
fallback for the case where
`remotes.origin.fetch-tags` is removed or its semantics
change in a subsequent jj release (per spec § jj setup).

§ 2 (Phase-driven workflow) names the project's
available MCP servers alongside the skill list, so
plan-time and brainstorming-time consumers know which
external knowledge sources Claude can reach. Match
CLAUDE.md § 11's MCP sub-list (Task A23) so the two
inventories stay in sync. Each MCP entry is one line:
the MCP's name, a one-clause role description, and the
upstream URL.

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 docs/process.md
```

- [ ] **Step 3: Commit.**

```sh
git add docs/process.md
git commit -m "doc: add docs/process.md rationale layer"
```

**Verification:** the file exists; markdownlint-clean; all
eighteen sections are present.

---

### Task A19: Author `docs/index.md`

**Files:** create `docs/index.md`.

**Depends on:** A1.

- [ ] **Step 1: Author the file.**

Topological-narrative entries per spec § `docs/index.md`,
covering at least:

- Quivers, semicategories, acyclic categories.
- Category-judgment encodings.
- Polynomial / W- / M-types and PFunctors.
- Profunctors and end machinery.
- Internal-presheaf Grothendieck equivalence.
- PshRelEdge and edge-of-presheaf machinery.
- Tree calculus Phase 2.
- K^sim hierarchy and ER ↔ K^sim_2 equivalence.
- CSLib integration.

Per the spec, the backfill is *adequate*, not exhaustive:
each entry names the workstream, source-tree paths,
central concepts, dependencies on other entries, and
pointers to `docs/research/` and `docs/superpowers/`
artefacts where applicable.

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 docs/index.md
```

- [ ] **Step 3: Commit.**

```sh
git add docs/index.md
git commit -m "doc: add docs/index.md topological narrative"
```

**Verification:** the file exists; markdownlint-clean;
each listed area has at least the four named fields.

---

### Task A20: Author `docs/lean-resources.md`

**Files:** create `docs/lean-resources.md`.

**Depends on:** A1.

- [ ] **Step 1: Lift the link list from the existing
  `CLAUDE.md`.**

The existing `CLAUDE.md` § "Lean 4 Library and Categorical
Theory Resources" carries the link list. Move it verbatim
into `docs/lean-resources.md`, preserving topic
organisation. The current `CLAUDE.md` will be rewritten
in Task A23 and will not retain the lifted content; the
new `CLAUDE.md` § Pointers links to
`docs/lean-resources.md`.

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 docs/lean-resources.md
```

- [ ] **Step 3: Commit.**

```sh
git add docs/lean-resources.md
git commit -m "doc: lift mathlib resource list into docs/lean-resources.md"
```

**Verification:** the file exists; markdownlint-clean;
the topic organisation matches the source.

---

### Task A21: Author `TODO.md`

**Files:** create `TODO.md`.

**Depends on:** A1.

- [ ] **Step 1: Author the skeleton.**

Format per spec § `TODO.md` format. Two top-level
sections:

- `## Active in geb-lean`
- `## To be done in geb-mathlib (not pending here)`

The first section is initially populated with a single
entry for the present refactor itself. The entry's
**Status** field is `executing`; a one-line note records
that the status advances to
`awaiting-Milestone-B-completion` once Milestone A is
signed off (A34) and that the entry is removed from
`TODO.md` once Milestone B concludes. The entry's
**Spec** and **Plan** fields point at this refactor's
spec and plan respectively. Other workstream entries are
added during Milestone B as triage classifies them.

The second section is initially empty with the spec's
exact disclaimer text. Render it verbatim from spec
§ `TODO.md` format (the paragraph beginning *"Items
intentionally deferred ..."* and ending *"... pending in
the present repository."*).

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 TODO.md
```

- [ ] **Step 3: Commit.**

```sh
git add TODO.md
git commit -m "doc: add TODO.md repository-root index"
```

**Verification:** the file exists with both top-level
sections; markdownlint-clean; the active-section entry
records the status-advancement note.

---

### Task A22: Rewrite `README.md`

**Files:** rewrite `README.md`.

**Depends on:** A5, A18, A19, A20, A21.

- [ ] **Step 1: Replace `README.md` with the new
  content.**

Sections per spec § `README.md` rewrite:

1. Project name and one-paragraph identity.
2. Status.
3. Dependencies.
4. License (Apache 2.0).
5. Index of project documentation (links to
   `docs/index.md`, `docs/process.md`,
   `docs/lean-resources.md`, this refactor's spec / plan).
6. Index of project processes (link to `CLAUDE.md`,
   one-line listing of `.claude/rules/*.md`).
7. Contribution pointers.
8. Pointers to `geb-mathlib`, mathlib4, CSLib.

Length target ~150 lines.

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 README.md
```

- [ ] **Step 3: Commit.**

```sh
git add README.md
git commit -m "doc: rewrite README in new index pattern"
```

**Verification:** the file exists; under ~170 lines;
markdownlint-clean.

---

### Task A23: Rewrite `CLAUDE.md` to ≤ 200 lines

**Files:** rewrite `CLAUDE.md`.

**Depends on:** A14, A15, A16, A17, A18, A19, A20, A21.

- [ ] **Step 1: Author the new CLAUDE.md.**

Per the spec's per-section line budget (target ~180
lines), sections in the order specified:

1. Project header and one-paragraph identity.
2. Project status.
3. Hard rules — must not violate.
4. Phase-driven workflow.
5. Style guidelines.
6. Repo structure.
7. Constructive-only Lean code.
8. Specs and plans live on the feature branch.
9. GebLean-specific disciplines.
10. Cross-reference to file-edit-only Lean rules.
11. Tooling.
12. When to consider creating a project-specific skill.
13. Pointers.

§ 11 (Tooling) names the project's available MCP
servers as a sub-list (one line each), so the new
CLAUDE.md inventories the resources Claude can reach at
session start. As of plan-authoring time, the available
MCPs include:

- `arxiv-mcp-server` (search arXiv papers; useful
  during brainstorming, spec-writing, plan-writing, and
  adversarial fact-checking of literature claims):
  `https://github.com/blazickjp/arxiv-mcp-server`.
- `memory` (model-context-protocol knowledge-graph
  representation of persistent memory; potentially
  useful at any phase):
  `https://github.com/modelcontextprotocol/servers/tree/main/src/memory`.
- `MCP Solver` (constraint solving, SMT solving, and
  other proof-search techniques; potentially useful
  during Lean / Geb planning and development):
  `https://github.com/szeider/mcp-solver`.

If the draft exceeds 200 lines, apply the priority order
for cuts per spec § "Priority order for cuts":

1. Move the banned-word example list out of CLAUDE.md
   (it lives canonically in
   `.claude/rules/markdown-writing.md` already).
2. Compress the phase-driven workflow table to one line
   per phase.
3. Move tooling-detail bullets to `docs/process.md`.

The previous link-list content has been lifted to
`docs/lean-resources.md` (Task A20). The Pointers
section references it.

- [ ] **Step 2: Verify the line count.**

```sh
wc -l CLAUDE.md
```

Expected: ≤ 200 lines.

- [ ] **Step 3: Markdown-lint.**

```sh
markdownlint-cli2 CLAUDE.md
```

- [ ] **Step 4: Commit.**

```sh
git add CLAUDE.md
git commit -m "doc: rewrite CLAUDE.md as slim always-on layer"
```

**Verification:** `wc -l CLAUDE.md` shows ≤ 200; the file
is markdownlint-clean; section 9 names the three
GebLean-specific disciplines (literature citations,
bottom-up named composites, non-negotiable interfaces).

---

### Task A24: User-direct — initialise jj colocated and run on-boarding

**Files:** none (per-developer local state outside the
repository).

**Depends on:** A8.

This task is performed by the **user** in the user's own
terminal, outside Claude Code. Claude must not attempt
the commands.

- [ ] **Step 1 (user-direct): `jj git init --colocate`.**

```sh
jj git init --colocate
```

Expected: jj 0.41 prints "Done importing changes from the
underlying Git repo." and "Initialized repo in '.'". The
runtime hint about `git clean -xdf` is no longer printed
in jj 0.41 (the warning is documented in
`docs/process.md` § jj instead).

- [ ] **Step 2 (user-direct): set per-repo configuration
  before the first fetch.**

```sh
jj config set --repo git.private-commits 'conflicts()'
jj config set --repo remotes.origin.fetch-tags 'glob:cutover-*'
```

- [ ] **Step 3 (user-direct): set per-developer
  signing/identity at user level.**

```sh
jj config set --user user.name '<name>'
jj config set --user user.email '<email>'
jj config set --user signing.behavior 'own'
jj config set --user signing.backend 'gpg'        # or 'ssh'
jj config set --user signing.key '<key id>'
```

- [ ] **Step 4 (user-direct): first fetch.**

```sh
jj git fetch --remote origin
```

The fetch-tags pattern from step 2 takes effect on this
invocation.

- [ ] **Step 5 (user-direct): run the verifier.**

```sh
bash scripts/check-jj-setup.sh
```

Expected: exits 0. If non-zero, follow the diagnostic
back to the corresponding `jj config set` step.

**Verification:** `bash scripts/check-jj-setup.sh` exits
0; `jj config path --repo` prints a path under the user
config directory (per jj 0.38+'s relocation), not under
`.jj/`.

---

### Task A25: Author `scripts/pre-push.sh`

**Files:** create `scripts/pre-push.sh`.

**Depends on:** A2, A7, A8, A24.

- [ ] **Step 1: Author the script.**

Behaviour per spec § Auxiliary scripts → "scripts/pre-push.sh":

1. `bash scripts/check-jj-setup.sh` (fail fast on
   unconfigured setup).
2. `lake test` (which builds `GebLean` and `GebLeanTests`
   as the test driver's dependency graph).
3. `lake lint`.
4. `markdownlint-cli2 --config .markdownlint-cli2.jsonc
   '**/*.md'`.
5. `bash scripts/check-axioms.sh GebLean/ test/ || true`
   (informational pre-Milestone-B, mirroring the
   axiom_check CI job's report-only mode; the `|| true`
   suffix is removed at Milestone B item B5 when the CI
   job flips to fail-mode).
6. On-screen reminders for user-driven gates:
   `lean4:golf` and `lean4:review` ran on changed Lean
   code; user reviewed the diff line-by-line.

The script is by-convention only (no automatic-invocation
hook); the rule "run pre-push.sh before every push" is
encoded in `CLAUDE.md` and `docs/process.md`. The
`lake lint` invocation depends on the lakefile change
from Task A2 having landed.

If a subsequent lakefile addition introduces a target
outside the test driver's dependency graph, this script
must be amended to add `lake build` explicitly. A comment
in the script records this constraint.

- [ ] **Step 2: Make it executable.**

```sh
chmod +x scripts/pre-push.sh
```

- [ ] **Step 3: Smoke-test.**

```sh
bash scripts/pre-push.sh
```

Expected: each step runs; the script exits 0 if every
step passes. The first step (`check-jj-setup.sh`) returns
0 because A24 has just been completed.

- [ ] **Step 4: Commit.**

```sh
git add scripts/pre-push.sh
git commit -m "chore(scripts): add pre-push.sh manual checklist"
```

**Verification:** the script is executable and runs to
completion; each named step is invoked; exit code is 0.

---

### Task A26: Smoke-test the `conflicts()` push semantics

**Files:** none (this is a behavioural verification of
the `git.private-commits = "conflicts()"` per-repo
setting).

**Depends on:** A24.

This task verifies the spec's claim (§ jj setup) that
"resolving a conflict locally and then pushing succeeds
without `--allow-private`, since the offending commit is
no longer in `conflicts()` at push time."

- [ ] **Step 1: Manufacture a conflict on a throwaway jj
  bookmark.**

Use a fresh tracked in-repo probe file at
`docs/.conflict-probe.md`. Writing to `/tmp/` would not
work: jj records changes to the working copy only, and
`/tmp/` paths are outside the working copy. Create two
divergent revisions whose only change is a write to the
in-repo probe file:

```sh
jj new -r main
echo 'A' > docs/.conflict-probe.md
jj describe -m "probe: A"
jj bookmark create chore/conflict-probe-a -r @
jj new -r main
echo 'B' > docs/.conflict-probe.md
jj describe -m "probe: B"
jj bookmark create chore/conflict-probe-b -r @
jj rebase -s chore/conflict-probe-b -d chore/conflict-probe-a
jj log -r 'conflicts()'
```

After the rebase, `jj log -r 'conflicts()'` should list
the merged revision. If it is empty, jj did not see a
working-copy change; re-confirm `jj st` shows the probe
file modified after each `echo` and before each
`jj describe`.

- [ ] **Step 2: Confirm the push refuses while the
  conflict is unresolved.**

```sh
jj git push --remote origin -b chore/conflict-probe-b
```

Expected: jj refuses with a `private-commits` diagnostic.
**Do not pass `--allow-private`.**

- [ ] **Step 3: Resolve the conflict.**

Edit the conflicted file to a single resolved value;
`jj squash` or `jj describe` the resolution; confirm
`jj log -r 'conflicts()'` no longer includes the
revision.

- [ ] **Step 4: Push and confirm success.**

```sh
jj git push --remote origin -b chore/conflict-probe-b
```

Expected: the push succeeds without `--allow-private`,
confirming the spec's assertion.

- [ ] **Step 5 (clean-up): delete the throwaway
  bookmarks locally and on the remote, and remove the
  probe file.**

```sh
jj bookmark delete chore/conflict-probe-a
jj bookmark delete chore/conflict-probe-b
jj git push --remote origin --deleted
rm -f docs/.conflict-probe.md
```

`--deleted` pushes all locally deleted bookmarks (both
probes covered by the prior `jj bookmark delete`
invocations); explicit `--bookmark X` flags are not
combined with `--deleted` (jj 0.41 treats the
combination as redundant). The probe file is removed
from the working copy so it does not appear in any
subsequent revision.

- [ ] **Step 6: No commit is produced by this task.**

The throwaway bookmarks and revisions are not retained.
If empirical observation contradicts the spec's
expectation (i.e. the resolved push does not succeed
without `--allow-private`), surface to the user
immediately with the recorded session output; the spec's
wording would need amendment.

**Verification:** the resolved push succeeded without
`--allow-private`; `jj log -r 'conflicts()'` is empty
after step 3; both throwaway bookmarks have been
deleted locally and remotely.

---

### Task A27: Wire `.claude/settings.json`

**Files:** create `.claude/settings.json`.

**Depends on:** A9, A11, A12, A23, A25, A26.

This is the **final Claude-direct commit-producing task**
in Milestone A. After this task lands, no further
`git add` / `git commit` from Claude is permitted in the
same session; subsequent commit-producing work is either
user-direct or routed through `jj describe`.

- [ ] **Step 1: Author the settings file.**

The file wires both hooks. Reference: spec § Hooks for
the required fields. The two hooks named are:

- PreToolUse: `scripts/hooks/block-mutating-git.sh`.
- SessionStart: `scripts/hooks/check-signing-key.sh`.

Use `${CLAUDE_PROJECT_DIR}` for the script paths so the
file is portable across worktrees.

- [ ] **Step 2: Commit.**

```sh
git add .claude/settings.json
git commit -m "chore(claude): wire block-mutating-git and check-signing-key hooks"
```

**Verification:** the file is JSON-parseable
(`python3 -c "import json,
sys; json.load(open('.claude/settings.json'))"` succeeds);
both hook script paths resolve.

---

### Task A28: Run the Milestone A verification checklist

**Files:** none.

**Depends on:** A1 through A27.

- [ ] **Step 1: Run every mechanically-checkable item
  (1–14) from spec § Milestone A — verification
  checklist.**

Each item is a separate command or inspection. Record
pass/fail for each.

```sh
# 1
lake build && lake test
# 2
markdownlint-cli2 '**/*.md'
# 3
bash scripts/check-axioms.sh GebLean/ test/
# 4
lake lint
# 5
test "$(wc -l < CLAUDE.md)" -le 200
# 6
ls .claude/rules/lean-disciplines.md \
   .claude/rules/lean-coding.md \
   .claude/rules/markdown-writing.md \
   .claude/rules/ci-and-workflow.md
# 7
ls docs/process.md docs/index.md docs/lean-resources.md
# 8
test -f TODO.md
# 9
test -f LICENSE
# 10
test -f README.md
# 11
jj config list --repo git.private-commits          # equals conflicts()
jj config list --repo remotes.origin.fetch-tags    # equals glob:cutover-*
jj config path --repo                              # path under user config dir
# 12
# Re-run the five A10 cases inline; capture exit codes 2,0,0,2,2.
# 13
test -f .github/workflows/markdown-lint.yml
# 14
ls scripts/check-axioms.sh scripts/check-jj-setup.sh \
   scripts/pre-push.sh \
   scripts/hooks/block-mutating-git.sh \
   scripts/hooks/check-signing-key.sh
```

Item 4 also requires re-running the deliberate-violation
positive test from Task A2 step 3 to confirm `lake lint`
is still actively flagging violations.

Item 11's "anchored, not substring" requirement is the
behaviour `scripts/check-jj-setup.sh` already enforces;
running the script again here is sufficient.

The `conflicts()` push smoke test (A26) is also part of
the verification record; reference its session output
captured at A26.

- [ ] **Step 2: Surface results to the user.**

Report each item with pass/fail. If any item fails,
diagnose, fix (via user-direct edits if a `git commit` is
required, since the hook is wired), and re-run; do not
proceed to A29 until all items pass.

**Verification:** all fourteen items pass; the A10
smoke-test re-run output and the A26 conflict-push output
are recorded.

---

### Task A29: User-direct — push topic branch and merge to `main` via merge commit

**Files:** none (VCS only).

**Depends on:** A28.

This task is performed by the **user**.

- [ ] **Step 1 (user-direct): line-by-line diff review.**

```sh
git log --first-parent main..chore/process-refactor
git diff main..chore/process-refactor
```

The user reviews the diff in full before pushing.

- [ ] **Step 2 (user-direct): push the topic branch.**

```sh
jj git push --remote origin -b chore/process-refactor
```

- [ ] **Step 3 (user-direct): open the PR and merge to
  `main` via a normal merge commit.**

The merge form is a **normal merge commit** per spec
§ Branch model (no fast-forward); fast-forward is
technically also append-only but contradicts the spec's
specific direction. The merge commit on `main` is the
**cutover commit**.

- [ ] **Step 4 (user-direct): record the cutover SHA.**

After the merge, capture the SHA of the merge commit on
`main`. Save the SHA temporarily; A31 records it in
`docs/process.md` § Branch model.

**Verification:** `git log --first-parent origin/main`
shows the merge commit at the tip; the SHA is recorded.

---

### Task A30: User-direct — create and push the signed cutover tag

**Files:** none (VCS only).

**Depends on:** A29.

This task is performed by the **user**. Signed-tag
operations are inherently tied to the user's gpg key and
identity.

- [ ] **Step 1 (user-direct): verify no pre-existing
  `cutover-*` tag is present locally.**

```sh
git tag --list 'cutover-*'
```

Expected: prints zero lines. If any stray tags from
earlier attempts exist, resolve them first per spec
verification item 17.

- [ ] **Step 2 (user-direct): create the signed tag at
  the cutover commit's SHA.**

```sh
git tag -s cutover-2026-MM-DD <SHA> \
  -m "Process bootstrap cutover"
```

`MM-DD` resolves to the merge date in the developer's
local timezone.

- [ ] **Step 3 (user-direct): re-confirm exactly one
  matching tag exists.**

```sh
git tag --list 'cutover-*'
```

Expected: prints exactly one line (the just-created tag).
This step is the mutual-exclusion guarantee that step 4's
wildcard refspec push form is safe (per spec
verification item 17, "exactly one line").

- [ ] **Step 4 (user-direct): push the tag using an
  unambiguous form.**

Either:

```sh
git push origin tag cutover-2026-MM-DD
```

or:

```sh
git push origin 'refs/tags/cutover-*:refs/tags/cutover-*'
```

The bare-name form `git push origin cutover-2026-MM-DD`
is avoided per spec verification item 17. The wildcard
form is safe **only because** step 3 has confirmed
exactly one matching local tag.

**Verification:** `git ls-remote --tags origin
cutover-2026-MM-DD` returns one line matching the SHA
recorded at A29 step 4.

---

### Task A31: User-direct — record the cutover SHA via follow-up topic branch

**Files:** modify `docs/process.md` (on a follow-up
topic branch).

**Depends on:** A29, A30.

This task is performed by the **user** via a follow-up
topic branch (`docs/cutover-sha-record`); the commit on
`main` lands as a merge commit per spec § Branch model.

- [ ] **Step 1 (user-direct): create the follow-up topic
  branch.**

```sh
jj new -r main
jj bookmark create docs/cutover-sha-record -r @
```

- [ ] **Step 2 (user-direct): edit `docs/process.md`
  § Branch model.**

Insert the cutover commit's SHA into the section. The
tag is the authoritative record (spec verification
item 17); the SHA in `docs/process.md` is a navigation
aid only.

- [ ] **Step 3 (user-direct): describe and push.**

```sh
jj describe -m "doc: record cutover SHA in docs/process.md"
jj git push --remote origin -b docs/cutover-sha-record
```

- [ ] **Step 4 (user-direct): open PR and merge to
  `main`.**

The merge form is a **normal merge commit**.

**Verification:** `docs/process.md` § Branch model
carries the SHA; the SHA matches `git ls-remote --tags
origin cutover-2026-MM-DD`; `git log --first-parent
origin/main` shows the new merge commit on top of the
cutover commit, with append-only invariant intact.

---

### Task A32: User-direct — `integration` branch and CI triggers

**Files:** modify `.github/workflows/markdown-lint.yml`
and `.github/workflows/lean_action_ci.yml` (on a
follow-up topic branch); create the `integration`
bookmark.

**Depends on:** A29, A31.

This task is performed by the **user**. It bundles the
integration-branch creation with the CI-trigger update
so that no further session is required to make CI fire
on `integration` pushes.

- [ ] **Step 1 (user-direct): create the
  CI-trigger-update topic branch.**

```sh
jj new -r main
jj bookmark create ci/integration-trigger -r @
```

- [ ] **Step 2 (user-direct): edit both workflows to
  include `integration` in the push trigger.**

In `.github/workflows/markdown-lint.yml` and
`.github/workflows/lean_action_ci.yml`, change the
`on.push.branches:` field from `[main]` to
`[main, integration]`. No other workflow content
changes.

- [ ] **Step 3 (user-direct): describe, push, open PR,
  merge.**

```sh
jj describe -m "ci: trigger workflows on integration pushes"
jj git push --remote origin -b ci/integration-trigger
```

The merge to `main` is a normal merge commit per spec
§ Branch model.

- [ ] **Step 4 (user-direct): regenerate `integration`
  as fan-in of the new `main` plus all currently-active
  topic branches.**

```sh
jj git fetch --remote origin
jj new \
  'main |
   (bookmarks(glob:"feat/*") ~ ::main) |
   (bookmarks(glob:"fix/*") ~ ::main) |
   (bookmarks(glob:"refactor/*") ~ ::main) |
   (bookmarks(glob:"chore/*") ~ ::main) |
   (bookmarks(glob:"docs/*") ~ ::main) |
   (bookmarks(glob:"bump/*") ~ ::main)' \
  -m "integration: fan-in @ $(date -I)"
jj bookmark set integration -r @
```

Post-cutover-and-CI-trigger-merge the active-topic-branch
set is empty; the integration revision equals `main`'s
tip until subsequent topic branches appear.

- [ ] **Step 5 (user-direct): push the bookmark.**

```sh
jj git push --remote origin -b integration
```

The CI workflows (now including `integration` in their
trigger lists) fire on this push.

**Verification:** `git ls-remote origin integration`
returns one line matching the integration revision; the
revision is at-or-after the most recent `main` SHA;
both workflows' Actions tabs show a run for the
integration push.

---

### Task A33: User-direct — configure GitHub repository protection Rulesets

**Files:** none (configured in GitHub UI).

**Depends on:** A30.

This task is performed by the **user** in the GitHub web
UI under Repository settings → Rules → Rulesets.

- [ ] **Step 1 (user-direct): create the `main` branch
  Ruleset.**

Forbid force-pushes and branch deletion on `main`.

- [ ] **Step 2 (user-direct): create the `cutover-*` tag
  Ruleset.**

Forbid deletion of tags matching `cutover-*`. (Tag
protection rules under Settings → Tags are a deprecated
alternative still available on most repositories;
either mechanism suffices, but the Ruleset is
preferred.)

**Verification:** the user confirms both Rulesets appear
in the repository's Rules listing and are scoped to the
correct refs.

---

### Task A34: Surface Milestone A completion to the user

**Files:** none.

**Depends on:** A31, A32, A33.

- [ ] **Step 1: Compile the Milestone A status report.**

For each of the seventeen verification items
(1–14 mechanical, 15 adversarial review, 16 user
sign-off, 17 cutover tag + 17a Rulesets), report status.

- [ ] **Step 2: Surface to the user.**

The user reviews the final state and either confirms
Milestone A is complete (item 16) or directs further
work. Item 16 is the gate for moving to Milestone B.

**Verification:** the user has explicitly confirmed
Milestone A is complete.

---

## Milestone B — `.session/` retirement

Milestone B is open-ended. It does not gate Milestone A
sign-off. All Milestone B commit-producing tasks use
`jj describe` rather than `git add` / `git commit`,
since the hook is wired from A27 forward.

### Task B1: Add the transitional pointer to `.session/README.md`

**Files:** modify `.session/README.md`.

**Depends on:** A34.

- [ ] **Step 1: Prepend the post-Milestone-A note.**

Add the spec's exact transitional header to the top of
the existing `.session/README.md` content (per spec
§ "Transitional state during Milestone A → Milestone B"):

```markdown
> **Note (post-Milestone-A)**: `TODO.md` at the
> repository root is now the source of truth for active
> work. The contents below are legacy entries pending
> triage. See `docs/process.md` § Workstream triage
> method for the migration scheme. The directory will be
> removed at Milestone B.
```

- [ ] **Step 2: Markdown-lint.**

```sh
markdownlint-cli2 .session/README.md
```

- [ ] **Step 3: Commit via jj describe.**

```sh
jj new -r main
jj describe -m "doc(session): add post-Milestone-A transitional note"
```

The push is user-direct.

**Verification:** the file's first non-blank line is the
transitional note; markdownlint-clean.

---

### Task B2: Triage every `.session/workstreams/*.md`

**Files:** modify (many) `.session/workstreams/*.md`,
`TODO.md`, `docs/index.md`; delete
`.session/workstreams/*.md` entries per disposition.

**Depends on:** B1.

This task is open-ended. Each
`.session/workstreams/<name>.md` file is a sub-task.
Approximately 78 files exist as of spec drafting.

For each file, apply the spec's triage template (§ Triage
execution) verbatim. The summary:

> Read the file. Cross-reference against `git log` for
> any commits referencing the workstream's topic,
> against current source-tree state, and against the
> Claude-harness task list. Before deletion, run
> `grep -r '.session/<name>'` across `docs/superpowers/`,
> `docs/`, `README.md`, and `CLAUDE.md` to find inbound
> references; either update each reference to point at
> the new home or migrate the referenced content first.
> Propose a classification (one of `live` /
> `live-deferred-to-geb-mathlib` / `completed` /
> `superseded` / `abandoned` / `unclear`) with a
> one-sentence justification. Surface to user for
> confirmation. On confirmation, perform the
> disposition.

Disposition by label per spec § Workstream triage method:

- `live` → migrate to `TODO.md` § Active in geb-lean.
- `live-deferred-to-geb-mathlib` → migrate to `TODO.md`
  § To be done in geb-mathlib.
- `completed` → describe in `docs/index.md` if not
  already; delete `.session/` entry.
- `superseded` → delete `.session/` entry; preserve any
  non-obvious "why superseded" notes in the surviving
  approach's spec / plan.
- `abandoned` → delete `.session/` entry.
- `unclear` → surface explicitly for user decision; do
  not auto-classify.

Each file is one sub-task. Surface the proposed
classification to the user; on confirmation, perform the
disposition; describe each disposition individually via
`jj describe -m "doc(triage): <name> classified as
<label>"` on a Milestone-B topic branch.

**Verification (cumulative):** every file under
`.session/workstreams/` has been triaged with user
confirmation; the directory listing shrinks to empty.

---

### Task B3: Reset the Claude-harness task list

**Files:** none (harness state, not in the working
tree).

**Depends on:** B2.

- [ ] **Step 1: Reset the task list per spec item B5.**

Keep:

- Brainstorming-tracking tasks #534–#542.
- The plan's tasks (this file's tasks).
- Tasks of currently-`live` workstreams (post-triage).

Archive or delete everything else.

**Verification:** the harness task list shows only the
preserved categories.

---

### Task B4: Remove the `.session/` directory

**Files:** delete `.session/` (recursive).

**Depends on:** B2.

- [ ] **Step 1: Confirm the directory is empty of
  workstream content.**

```sh
ls .session/workstreams/
```

Expected: empty (every entry triaged in B2).

- [ ] **Step 2: Remove the directory via the working
  copy.**

The raw `git rm -rf .session/` form is denied by the
`block-mutating-git` hook; use the working-copy form
recognised by jj instead:

```sh
jj new -r main
rm -rf .session/
jj describe -m "chore(session): retire .session directory at Milestone B"
```

This includes the `.session/README.md` (with its
transitional note) and any `.session/docs/` content;
per the spec, the entire directory is removed.

The push is user-direct.

**Verification:** the directory does not exist; `jj
status` reflects the deletion as part of the working
copy.

---

### Task B5: Flip `axiom_check` to fail-mode

**Files:** modify `.github/workflows/lean_action_ci.yml`
(via a Milestone-B topic branch).

**Depends on:** B2 (each touched Lean file gets its
`AXIOM_ALLOW` annotations during triage; the
report-only output should shrink toward empty as triage
progresses).

- [ ] **Step 1: Confirm report-only output is empty.**

Re-run the report-only job once locally:

```sh
bash scripts/check-axioms.sh GebLean/ test/
```

Expected: zero non-allowlisted axioms remain
unannotated. If any remain, surface them; either
annotate (with
`AXIOM_ALLOW: <axiom> (rationale)`) or refactor before
flipping.

- [ ] **Step 2: Edit the workflow.**

Remove the report-only stanza; the job's exit code now
gates the workflow. The failure condition: any
non-allowlisted axiom (anything other than `propext`,
`Quot.sound`, `quot.sound`) appears in the closure of
any declaration without a matching `AXIOM_ALLOW`
comment.

- [ ] **Step 2b: Drop the `|| true` suffix in
  `scripts/pre-push.sh`.**

The axiom-check step in `scripts/pre-push.sh` was
authored at A25 with `|| true` so that pre-push did not
fail pre-Milestone-B. Now that the CI job is in
fail-mode, the local pre-push should also gate on the
script's exit code. Remove the `|| true` suffix from
the relevant line.

- [ ] **Step 3: Describe and push via topic branch.**

```sh
jj new -r main
jj bookmark create ci/axiom-check-fail-mode -r @
jj describe -m "ci: flip axiom_check from report-only to fail-mode"
jj git push --remote origin -b ci/axiom-check-fail-mode
```

The PR and merge are user-direct.

**Verification:** the workflow runs against the current
tree and passes; introducing an unannotated
`Classical.choice`-dependent declaration in a scratch
file causes the job to fail (smoke test, then revert).

---

### Task B6: Surface Milestone B completion to the user

**Files:** none.

**Depends on:** B3, B4, B5.

- [ ] **Step 1: Compile the Milestone B status report.**

Items B1 through B7 (per spec § Milestone B), with
status for each.

- [ ] **Step 2: Surface to the user.**

The user reviews the final state and either confirms
Milestone B is complete (item B6) or directs further
work.

**Verification:** the user has explicitly confirmed
Milestone B is complete.

---

## Plan summary

| Milestone | Tasks | Notes |
| --- | --- | --- |
| A | A1 – A34 | Structural refactor; A1 – A23 are Claude-direct git-add+git-commit (hook unwired); A24 is user-direct jj on-boarding; A25 is the last Claude-direct commit before A27; A26 is a non-commit conflict-push smoke test; A27 wires the hook (final Claude-direct commit); A28 verifies; A29–A33 are user-direct VCS / GitHub UI; A34 surfaces. |
| B | B1 – B6 | Triage and retirement; open-ended (~78 workstream entries, each one user-confirmed sub-task). All commit-producing B-tasks use `jj describe` since the hook is wired. |

**Sequence dependencies (load-bearing):**

- A2 (lake lintDriver) precedes A25 (pre-push uses
  `lake lint`).
- A6 (`scripts/`) precedes A7, A8, A9, A11.
- A9 (`block-mutating-git.sh`) precedes A10 (smoke
  tests) and A27 (`settings.json`).
- A12 (`.gitignore`) precedes A14–A17 and A27.
- A14–A17 (rule files) precede A18 (`docs/process.md`)
  and A23 (`CLAUDE.md` rewrite).
- A19, A20, A21 precede A22 (`README.md` rewrite).
- A24 (jj init, user-direct) precedes A25 (`pre-push.sh`
  smoke test) and A26 (conflicts() smoke test).
- A23, A25, A26 precede A27 (settings wiring, final
  Claude-direct commit).
- A27 precedes A28 (verification).
- A28 precedes A29 (push topic branch + cutover merge).
- A29 precedes A30 (cutover tag) and A31 (record SHA on
  follow-up topic branch).
- A32 (integration branch)'s technical dependencies are
  A29 and A31; A32 is placed in this position for
  ordering coherence rather than because of any
  additional technical dependency on A30.
- A30 precedes A33 (Rulesets) — the tag must exist
  before the tag-protection Ruleset can target it.
- A31, A32, A33 precede A34.
- A34 precedes B1 (no Milestone-B work begins until the
  user confirms Milestone A).
- B2 precedes B3, B4, B5.

**User-direct steps:** A24, A29, A30, A31, A32, A33,
plus the per-workstream confirmations and pushes in
B1–B5.
