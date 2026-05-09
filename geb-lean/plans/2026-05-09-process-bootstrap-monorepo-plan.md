# geb-lean process-bootstrap implementation plan (monorepo-aware)

> **Supersedes**:
> [`2026-05-07-process-bootstrap-plan.md`](2026-05-07-process-bootstrap-plan.md).
> The 2026-05-07 plan assumed geb-lean was a standalone git repo; this
> revision incorporates the monorepo-subdirectory reality per the
> [2026-05-09 monorepo-aware design](../docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md).
>
> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land the structural process refactor specified in
`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`,
then retire `.session/` once every legacy workstream entry has
been triaged.

**Architecture:** Two-milestone refactor in a multi-language
monorepo (`geb/` containing `geb-agda/`, `geb-idris/`, `geb-lean/`,
plus a top-level Common Lisp project). Milestone A is structural
work scoped to (a) cross-cutting infrastructure on the parent
`geb/` repo (CI workflows, `.gitignore`, jj colocated init,
GitHub Rulesets, signed cutover tag) and (b) content under
`geb-lean/` (`CLAUDE.md`, `.claude/rules/`, scripts, lakefile,
docs/superpowers/, plans/, GebLean source). Milestone B is
open-ended `.session/` triage plus the report-only → fail-mode
flip of the axiom-check CI job. Other subprojects (`geb-agda/`,
`geb-idris/`, `src/`, `test/`, parent README, parent LICENSE)
are not modified.

**Tech stack:** Lean 4 + Lake (existing build), `jj` 0.41+
(VCS, colocated at parent), `markdownlint-cli2` 0.18.x+ (markdown
lint), `scripts/check-axioms.sh` (vendored derivative of the
`lean4-skills` plugin's `check_axioms_inline.sh`),
`scripts/hooks/*.sh` (Bash, `jq` for JSON parsing in the
PreToolUse hook), GitHub Actions (CI, at parent level), GitHub
Rulesets (branch and tag protection on parent's `main` /
`cutover-*`).

---

## Reading order for the implementer

Before starting Task C1, read:

1. `docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`
   end-to-end. The spec is authoritative on every design
   decision; this plan only sequences the implementation.
2. `docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`
   and its review logs (`.review-15.md`, `.review-16.md`,
   `.review-17.md`, `.review-jj-0.41.md`) for closed-decision
   history.
3. The 2026-05-09 spec's review logs under
   `docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.review-*.md`
   to confirm converged decisions. Do not re-litigate these.
4. `CLAUDE.md` (the existing one) for the prose register and
   the forbidden-word list. All persistent prose written by
   this plan must respect that list.

The plan's tasks reference spec sections by name (e.g.
"§ jj setup", "§ Hooks") rather than reproducing the spec's
content. Each task's verification signal is named explicitly.

---

## Closed decisions reproduced verbatim from the hand-off

The plan respects these without re-litigation:

- Layered `CLAUDE.md` ≤ 200 lines plus rule files in
  `geb-lean/.claude/rules/`.
- `jj` 0.41 colocated mode at the **parent `geb/` root**
  with `git.private-commits = "conflicts()"` and
  `remotes.origin.fetch-tags = "glob:cutover-*"`, both
  per-repo.
- Default-deny `block-mutating-git` PreToolUse hook with
  closed allowlists. **Tag operations are user-direct and
  NOT allowlisted.**
- `check-signing-key` SessionStart hook.
- Cutover commit + signed git tag (`cutover-2026-MM-DD`)
  on the **parent's** `main` / tag namespace + GitHub
  Rulesets at the parent.
- Append-only `main` from cutover forward, applying to
  the **parent's** `main` (binding all subprojects).
- Parent `geb/LICENSE` is GPLv3; the `geb-lean/LICENSE`
  (Apache 2.0) committed at the prior in-flight A5
  (`079302ae`) is **removed** in cleanup task C1
  (`C-license-rm`). References point at `../LICENSE`.
- Parent `geb/README.md` is untouched by this refactor
  except for a short pointer-to-`geb-lean/README.md`
  paragraph; a new `geb-lean/README.md` is authored
  from scratch.
- `moreLeanArgs = ["-DwarningAsError=true"]` preserved
  in `geb-lean/lakefile.toml`.
- `axiom_check` job initially in report-only mode; flipped
  to fail-mode in Milestone B item B7.
- Adversarial review precedes user review for all specs and
  plans.
- `remotes.<name>.fetch-tags` is experimental; the spec
  documents the fallback (explicit raw-git refspec form +
  matching allowlist entry + on-boarding step). The plan
  references but does not duplicate that fallback.
- New MCPs (`arxiv-mcp-server`, `memory`, `MCP Solver`)
  are recorded in `CLAUDE.md` § Tooling and in
  `docs/process.md`.
- Promoted CI workflows live at `geb/.github/workflows/`
  with `paths: ['geb-lean/**']` filters and
  `lake-package-directory: geb-lean` / top-level
  `defaults.run.working-directory: geb-lean` for the
  workflow level.
- `markdownlint-cli2` invoked with `--no-globs` and a
  quoted glob argument (single quotes load-bearing).
- `block-mutating-git.sh` uses `jj root` (exit 0) rather
  than `[[ -d $CLAUDE_PROJECT_DIR/.jj ]]` for `.jj/`
  discovery (per cleanup task C5 / `C-hook-amend`).

---

## Hook-wiring discipline (load-bearing for the plan's order)

Task A27 wires `geb-lean/.claude/settings.json`, which
activates the `block-mutating-git` PreToolUse hook for
subsequent sessions (and possibly the same session). The
hook denies `git add`, `git commit`, `git switch`, and
every other mutating raw-git form. Therefore A27 is the
**final Claude-direct commit-producing task** in Milestone A.

- Cleanup tasks C1 through C6 land their commits with
  plain `git add` / `git commit` because the hook is
  unwired through that range.
- Tasks A1 through A23 likewise use `git add` /
  `git commit` directly.
- A24 is user-direct (`jj git init --colocate` at parent).
  After A24 the working tree has both `.git/` and `.jj/`.
- A25 (`pre-push.sh`) is the last `git add` / `git commit`
  step before A27.
- A26 (the `conflicts()` smoke test) is non-commit-producing.
- A27 lands the settings file with `git add` / `git commit`.
  After this task lands, no further Claude-direct
  `git add` / `git commit` is permitted in the same session.
- A28 onward is non-commit-producing (verification) or
  user-direct (push, signed tag, follow-up doc commit on a
  topic branch via `jj describe`, GitHub UI).

---

## User-direct steps (Claude must NOT attempt)

These tasks are performed by the user in their own terminal,
outside Claude Code. The `block-mutating-git` PreToolUse hook
only sees Claude's tool invocations; user-direct steps are not
gated by the hook — the human-gate convention applies.

- Task A24: `jj git init --colocate` at parent `geb/` root
  and the `jj config set` on-boarding sequence.
- Task A29: pushing the topic branch's merge commit to
  parent's `main` (the cutover commit).
- Task A30: creating, signing, and pushing the
  `cutover-YYYY-MM-DD` tag on the parent.
- Task A31: creating the follow-up topic branch
  `docs/cutover-sha-record`, committing the SHA into
  `docs/process.md` via `jj describe`, pushing, opening
  a PR, merging (on parent).
- Task A32: pushing the `integration` bookmark to the
  parent remote.
- Task A33: configuring GitHub Rulesets (Repository
  settings → Rules → Rulesets) for parent's `main` and
  for the tag pattern `cutover-*`.
- Milestone B: per-workstream triage decisions (Claude
  surfaces proposed classifications; the user confirms
  or amends).

Every other task is performed by Claude.

---

## Cleanup tasks (preceding the plan's main sequence)

Tasks C1–C6 revert or repair in-flight changes from the
prior `chore/process-refactor` branch that are incompatible
with the monorepo-aware design. All cleanup tasks use
plain `git add` / `git commit` (hook not yet wired).

### Task C1: `C-license-rm` — remove `geb-lean/LICENSE`

**Files:** delete `geb-lean/LICENSE`.

**Depends on:** nothing (first cleanup task).

**Ordering constraint:** before any task that reads the
file-layout as definitive.

The file at `geb-lean/LICENSE` (Apache 2.0; committed as
in-flight `079302ae`) is inconsistent with the monorepo
design: geb-lean inherits the parent `geb/LICENSE` (GPLv3).
References to the licence point at `../LICENSE`.

- [ ] **Step 1: Delete the file.**

  Run from the `geb-lean/` working directory:

  ```sh
  git rm LICENSE
  ```

- [ ] **Step 2: Verify the file is gone and the parent
  licence exists.**

  ```sh
  test ! -f LICENSE
  test -f ../LICENSE
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git commit -m \
    "chore: remove geb-lean/LICENSE; geb-lean inherits ../LICENSE (GPLv3)"
  ```

**Verification:** `test ! -f geb-lean/LICENSE` passes;
`test -f geb/LICENSE` passes.

---

### Task C2: `C-workflow-rm` — remove `geb-lean/.github/workflows/markdown-lint.yml`

**Files:** delete `geb-lean/.github/workflows/markdown-lint.yml`.

**Depends on:** C1.

**Ordering constraint:** before the parent-level
`markdown-lint.yml` authoring (plan task A4).

The file was committed at `3d27311f` at the wrong location
(inside `geb-lean/.github/`). The parent-level workflow
(authored at plan task A4) supersedes it.

- [ ] **Step 1: Delete the file.**

  ```sh
  git rm .github/workflows/markdown-lint.yml
  ```

- [ ] **Step 2: Verify removal.**

  ```sh
  test ! -f .github/workflows/markdown-lint.yml
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git commit -m \
    "ci: remove geb-lean-local markdown-lint.yml (superseded by parent)"
  ```

**Verification:** the file does not exist at
`geb-lean/.github/workflows/markdown-lint.yml`.

---

### Task C3: `C-gitignore-revert` — remove `.claude`-related patterns from `geb-lean/.gitignore`

**Files:** modify `geb-lean/.gitignore`.

**Depends on:** C1.

**Ordering constraint:** before the parent `.gitignore`
edit (plan task A12).

The in-flight commit `69123dd0` added `/.claude/*`,
`!/.claude/rules/`, `!/.claude/settings.json`, and these
patterns together with the pre-existing `/docs/.claude`
entry are all `.claude`-related. Per the monorepo design,
all `.claude/`-path ignore and unignore decisions are
consolidated in the parent `geb/.gitignore`. Remove every
`.claude`-related pattern from `geb-lean/.gitignore`.

- [ ] **Step 1: Remove the four patterns.**

  Edit `geb-lean/.gitignore` to remove these lines:

  ```text
  /.claude/*
  !/.claude/rules/
  !/.claude/settings.json
  /docs/.claude
  ```

  Preserve all other entries unchanged (`.lake`,
  `.github/copilot-instructions.md`, `.remember`).

- [ ] **Step 2: Verify no `.claude` patterns remain.**

  ```sh
  ! grep '\.claude' .gitignore
  ```

  Expected: the negation succeeds (no matches).

- [ ] **Step 3: Commit.**

  ```sh
  git add .gitignore
  git commit -m \
    "chore(gitignore): remove .claude patterns from geb-lean .gitignore"
  ```

**Verification:** `grep '\.claude' geb-lean/.gitignore`
returns nothing (exit 1 from grep, matched by negation);
the remaining entries are intact.

---

### Task C4: `C-markdownlint-config-rewrite` — rewrite `.markdownlint-cli2.jsonc`

**Files:** modify `geb-lean/.markdownlint-cli2.jsonc`.

**Depends on:** C1.

**Ordering constraint:** before A3 (markdownlint
verification), which is the first task to rely on the
correct config.

The current file (committed at `aeae31f9`) carries a
top-level `"globs"` key and an `ignores` array lacking
both `geb-lean/`-prefixed forms and `.session/**`. Rewrite
it per spec § `.markdownlint-cli2.jsonc`:

- Remove the `"globs"` key entirely.
- Replace the `ignores` array with both unprefixed and
  `geb-lean/`-prefixed forms for each generated directory.
- Preserve the `config` key (`default: true`, `MD013`
  table/code-block exemptions).
- Omit `.jj/**` from `ignores` (jj manages its own
  git-visibility; absence is intentional per spec).

- [ ] **Step 1: Rewrite the file.**

  Replace the file contents with:

  ```jsonc
  // Shared markdownlint configuration for geb-lean.
  // Picked up by both `markdownlint-cli2` (CLI / CI) and
  // the VSCode markdownlint extension when the workspace
  // is opened at this directory.
  //
  // No top-level "globs" key: callers pass glob args on
  // the CLI. Omitting "globs" prevents unintended glob
  // union when CLI globs are passed alongside this config.
  //
  // Ignores: both unprefixed (pre-push.sh CWD=geb-lean/)
  // and geb-lean/-prefixed (CI CWD=geb/) forms are listed.
  // Each invocation triggers exactly one set; the other
  // matches nothing (harmless).
  //
  // .jj/ is not listed: jj manages its own git-visibility
  // via the self-contained .jj/.gitignore it creates at
  // jj git init --colocate. Listing .jj/ here would
  // suppress linting of any markdown jj later exposes.
  {
    "config": {
      "default": true,
      "MD013": {
        "tables": false,
        "code_blocks": false
      }
    },
    "ignores": [
      ".lake/**",
      "node_modules/**",
      ".session/**",
      ".claude/memory/**",
      ".claude/docs/**",
      ".claude/tools/**",
      "geb-lean/.lake/**",
      "geb-lean/node_modules/**",
      "geb-lean/.session/**",
      "geb-lean/.claude/memory/**",
      "geb-lean/.claude/docs/**",
      "geb-lean/.claude/tools/**"
    ]
  }
  ```

- [ ] **Step 2: Confirm no `"globs"` key remains.**

  ```sh
  ! grep '"globs"' .markdownlint-cli2.jsonc
  ```

- [ ] **Step 3: Verify both forms are present.**

  ```sh
  grep '"\.lake\/\*\*"' .markdownlint-cli2.jsonc
  grep '"geb-lean/\.lake\/\*\*"' .markdownlint-cli2.jsonc
  ```

- [ ] **Step 4: Commit.**

  ```sh
  git add .markdownlint-cli2.jsonc
  git commit -m \
    "chore(markdownlint): rewrite config per monorepo-aware spec"
  ```

**Verification:** no `"globs"` key; both unprefixed and
`geb-lean/`-prefixed `ignores` entries are present;
`.jj/**` is absent.

---

### Task C5: `C-hook-amend` — amend `block-mutating-git.sh` to use `jj root`

**Files:** modify
`geb-lean/scripts/hooks/block-mutating-git.sh`.

**Depends on:** C1.

**Ordering constraint:** must precede A27 (hook wiring).
Per spec § Hooks, the existing committed hook (at
`125c6d4e`) uses `[[ -d $CLAUDE_PROJECT_DIR/.jj ]]`,
which fails when `.jj/` is at the parent `geb/` rather
than at `geb-lean/`. Amend to use `jj root` (exit 0 =
jj is initialised somewhere up the tree), which is
portable regardless of `.jj/` placement.

- [ ] **Step 1: Edit the discovery condition.**

  Find the line containing `[[ -d $CLAUDE_PROJECT_DIR/.jj ]]`
  and replace the discovery logic with a `jj root`
  invocation:

  ```bash
  if jj root > /dev/null 2>&1; then
    # jj is initialised; strip jj git X forms
    ...
  fi
  ```

  The rest of the hook script (allowlists, deny logic,
  stderr messages) is unchanged.

- [ ] **Step 2: Syntax check.**

  ```sh
  bash -n scripts/hooks/block-mutating-git.sh
  ```

- [ ] **Step 3: Run the five smoke-test cases.**

  Feed synthesised JSON-stdin payloads in the format
  Claude Code's PreToolUse hook expects:
  `{"tool_name": "Bash", "tool_input": {"command": "<cmd>"}}`.
  For case (b) to produce exit 0, the working directory
  must be inside a jj-initialised tree. If jj is not yet
  initialised at the parent (A24 is user-direct and
  runs later), run the smoke test in the existing tree
  after temporarily setting `CLAUDE_PROJECT_DIR` to any
  directory with a `.jj/` subdirectory, or defer to
  verification checklist item 12 after A24 completes.
  Record expected exit codes:

  - (a) `git commit -m '...'` → 2 (denied, default-deny).
  - (b) `jj git push --remote origin -b feat/x` → 0
    (allowed, `jj git X` forms stripped).
  - (c) `git status` → 0 (allowed read-only subcommand).
  - (d) `git checkout -b new-branch` → 2 (denied mutating
    subcommand).
  - (e) `git push origin 'refs/tags/v1.0.0:refs/tags/v1.0.0'`
    → 2 (denied, no tag-push allowlist entry).

- [ ] **Step 4: Commit.**

  ```sh
  git add scripts/hooks/block-mutating-git.sh
  git commit -m \
    "fix(hooks): use jj root for .jj/ discovery in block-mutating-git.sh"
  ```

**Verification:** `bash -n` succeeds; all five smoke-test
cases produce the expected exit codes.

---

### Task C6: `C-lean-action-ci-promote` — move `lean_action_ci.yml` to parent

**Files:** move `geb-lean/.github/workflows/lean_action_ci.yml`
to `geb/.github/workflows/lean_action_ci.yml` via `git mv`.

**Depends on:** C2.

**Ordering constraint:** before the main plan's CI
verification task (A28). The `axiom_check` job addition
is a separate main-plan task (A13), not part of this
cleanup.

The file `geb-lean/.github/workflows/lean_action_ci.yml`
must move to `geb/.github/workflows/lean_action_ci.yml`
and gain:

- `paths: ['geb-lean/**']` filter on `push` and
  `pull_request` triggers.
- Top-level (workflow-level) `defaults.run.working-directory: geb-lean`
  key (applies to all `run:` steps in all jobs; does NOT
  affect `uses:` steps).
- `lake-package-directory: geb-lean` input to the
  `leanprover/lean-action@v1` step.
- Retained `actions/checkout` SHA-pin from the in-flight
  version (`de0fac2e4500dabe0009e67214ff5f5447ce83dd`
  or the latest SHA at plan-execution time).

- [ ] **Step 1: Read the existing file.**

  ```sh
  cat .github/workflows/lean_action_ci.yml
  ```

- [ ] **Step 2: Move the file to the parent level.**

  Run from `geb-lean/`:

  ```sh
  git mv .github/workflows/lean_action_ci.yml \
    ../.github/workflows/lean_action_ci.yml
  ```

  Both the deletion and the new path are staged
  automatically by `git mv`.

- [ ] **Step 3: Edit the file at its new path.**

  Open `geb/.github/workflows/lean_action_ci.yml`
  and apply the three changes. The `on:` block gains the
  `paths` filter:

  ```yaml
  on:
    push:
      branches: [main]
      paths: ['geb-lean/**']
    pull_request:
      paths: ['geb-lean/**']
  ```

  The workflow-level `defaults` key:

  ```yaml
  defaults:
    run:
      working-directory: geb-lean
  ```

  The `leanprover/lean-action@v1` step in the `build`
  job gains the input:

  ```yaml
  with:
    lake-package-directory: geb-lean
  ```

  All other content (job name, step names, SHA pins,
  cache configuration) is carried forward unchanged.

- [ ] **Step 4: Stage the edits and YAML validity check.**

  ```sh
  git add ../.github/workflows/lean_action_ci.yml
  python3 -c \
    "import yaml, sys; yaml.safe_load(open('../.github/workflows/lean_action_ci.yml'))"
  ```

- [ ] **Step 5: Commit both changes together.**

  At this point the index contains both the rename (deletion
  at the old path + addition at the new path, from Step 2)
  and the content edits (Step 4). Commit:

  ```sh
  git commit -m \
    "ci: promote lean_action_ci.yml to parent with geb-lean path filter"
  ```

**Verification:** `geb-lean/.github/workflows/lean_action_ci.yml`
does not exist; `geb/.github/workflows/lean_action_ci.yml`
exists, is YAML-valid, contains `paths: ['geb-lean/**']`,
`lake-package-directory: geb-lean`, and a workflow-level
`defaults.run.working-directory: geb-lean` key.
Confirm both the rename and the edits landed:

```sh
git log --stat HEAD~1..HEAD
git ls-files --error-unmatch \
  ../.github/workflows/lean_action_ci.yml
```

---

## Milestone A — process bootstrap

Tasks A1 through A34 land the structural refactor. Each
task is one self-contained edit set with one verification
signal. Sequence dependencies are named in the **Depends
on:** line of each task. Run `lake build && lake test`
after every task that touches anything Lake compiles; run
`markdownlint-cli2 --config .markdownlint-cli2.jsonc
--no-globs '<glob>'` against any `.md` file the task
creates or modifies.

### Task A1: Confirm topic branch and baseline build

**Files:** none (VCS state and build verification only).

**Depends on:** C1–C6 complete.

The branch `chore/process-refactor` was created in the
prior in-flight work. This task confirms the baseline is
clean before main-sequence tasks begin.

- [ ] **Step 1: Confirm branch.**

  ```sh
  git status
  ```

  Expected: `On branch chore/process-refactor`,
  working tree clean.

- [ ] **Step 2: Confirm baseline build.**

  ```sh
  lake build
  lake test
  ```

  Expected: both succeed without warnings.

**Verification:** `git status` shows correct branch; build
and test pass.

---

### Task A2: Verify `lintDriver` and `lake lint` (verification-only)

**Files:** no edit needed.

**Depends on:** A1.

The in-flight commit `00284252` already added
`lintDriver = "batteries/runLinter"` to
`geb-lean/lakefile.toml` and committed
`geb-lean/scripts/nolints.json`. This task verifies the
state is correct; no re-authoring is needed.

- [ ] **Step 1: Confirm `lintDriver` line is present.**

  ```sh
  grep 'lintDriver' lakefile.toml
  ```

  Expected: prints `lintDriver = "batteries/runLinter"`.

- [ ] **Step 2: Run `lake lint`.**

  ```sh
  lake lint
  ```

  Expected: exits 0 (baseline pinned by `nolints.json`).

- [ ] **Step 3: Positive verification.**

  Introduce a deliberate violation in a scratch
  `GebLean/Utilities/_LintProbe.lean` file (e.g. an
  unused `set_option` or an unused `let`-binding that
  trips `linter.unusedVariables`). Run `lake lint`;
  expected: the linter flags the file. Delete the scratch
  file; run `lake lint` again; expected: quiet.

- [ ] **Step 4: Confirm no probe file remains.**

  ```sh
  test ! -f GebLean/Utilities/_LintProbe.lean
  ```

  No commit is needed (the lintDriver line and
  `nolints.json` already exist).

**Verification:** `lake lint` is quiet on the current
source; the deliberate-violation probe was flagged then
removed.

---

### Task A3: Verify `.markdownlint-cli2.jsonc` post-C4

**Files:** verify only (C4 rewrote the file).

**Depends on:** C4.

This task confirms the post-cleanup config is correct and
passes a lint run against the plan's own newly authored
file.

- [ ] **Step 1: Confirm no `"globs"` key.**

  ```sh
  ! grep '"globs"' .markdownlint-cli2.jsonc
  ```

- [ ] **Step 2: Run markdownlint against this plan.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'plans/2026-05-09-process-bootstrap-monorepo-plan.md'
  ```

  Expected: zero violations. Surface any pre-existing
  findings in other files to the user rather than
  auto-fixing.

**Verification:** the command exits 0 on the plan file;
no `"globs"` key is present in the config.

---

### Task A4: Author `geb/.github/workflows/markdown-lint.yml`

**Files:** create `geb/.github/workflows/markdown-lint.yml`.

**Depends on:** C2, C4, A3.

The parent-level `markdown-lint.yml` workflow replaces the
geb-lean-local one removed at C2. Per spec § CI changes,
it uses `run:` steps rather than the `DavidAnson/markdownlint-cli2-action`
action, because the action does not expose a `--no-globs`
equivalent input.

- [ ] **Step 1: Author the workflow.**

  Create `geb/.github/workflows/markdown-lint.yml`:

  ```yaml
  name: markdown-lint

  on:
    push:
      branches: [main]
      paths:
        - 'geb-lean/**/*.md'
        - 'geb-lean/.markdownlint-cli2.jsonc'
    pull_request:
      paths:
        - 'geb-lean/**/*.md'
        - 'geb-lean/.markdownlint-cli2.jsonc'

  jobs:
    markdown-lint:
      runs-on: ubuntu-latest
      steps:
        - uses: actions/checkout@<SHA>
        - name: Install markdownlint-cli2
          run: npm install -g 'markdownlint-cli2@^0.18.0'
        - name: markdownlint
          run: |
            markdownlint-cli2 \
              --config geb-lean/.markdownlint-cli2.jsonc \
              --no-globs \
              'geb-lean/**/*.md'
  ```

  The `<SHA>` placeholder for `actions/checkout` must be
  resolved to a 40-hex-char commit SHA (not a tag reference)
  before committing. Use the same SHA as the `lean_action_ci.yml`
  file if already resolved, or fetch the latest release SHA
  from <https://github.com/actions/checkout/releases>.

  `integration` is intentionally omitted from the trigger
  list at this point; it is added at A32 post-cutover.

  **Note on spec divergence**: spec § CI changes states
  "both steps are `run:` steps," referring to the
  markdownlint invocation replacing the prior
  `DavidAnson/markdownlint-cli2-action@<SHA>` `uses:`
  step. The workflow still requires the standard
  `actions/checkout@<SHA>` `uses:` step at the top so
  that subsequent `run:` steps can access the repository
  contents. The spec's prose describes the markdownlint
  *invocation* as a `run:` step; the checkout step is a
  separate, required `uses:` step. The template above
  (three steps: checkout + two `run:` steps) is
  authoritative; the spec's two-step framing is loose.

- [ ] **Step 2: Resolve the `<SHA>` placeholder.**

  Run from `geb-lean/` CWD:

  ```sh
  test -f ../.github/workflows/markdown-lint.yml \
    && ! grep -n '<SHA>' \
         ../.github/workflows/markdown-lint.yml
  ```

  The first clause asserts the file exists at the parent
  level. The second asserts no `<SHA>` placeholder remains.
  Expected: exits 0 with no output.

- [ ] **Step 3: YAML validity check.**

  ```sh
  python3 -c \
    "import yaml, sys; yaml.safe_load(open(\
    '../.github/workflows/markdown-lint.yml'))"
  ```

- [ ] **Step 4: Commit.**

  ```sh
  git -C .. add .github/workflows/markdown-lint.yml
  git -C .. commit -m "ci: add markdown-lint workflow at parent level"
  ```

**Verification:** the file exists at
`geb/.github/workflows/markdown-lint.yml`; no `<SHA>`
placeholder remains (`test -f ../.github/workflows/markdown-lint.yml
&& ! grep -n '<SHA>' ../.github/workflows/markdown-lint.yml`
exits 0 with no output from `geb-lean/` CWD); YAML-valid;
the `paths:` filter covers `geb-lean/**/*.md`.

---

### Task A5: Create `geb-lean/.claude/rules/` directory

**Files:** create `geb-lean/.claude/rules/` directory.

**Depends on:** C3.

After cleanup task C3, `geb-lean/.gitignore` contains no
`.claude`-related patterns. The parent `geb/.gitignore`
must also be updated (Task A12) before committed files
under `.claude/rules/` become trackable. This task creates
the directory in preparation; the rule files (A14–A17) land
after A12.

- [ ] **Step 1: Create the directory.**

  ```sh
  mkdir -p .claude/rules
  ```

- [ ] **Step 2: No standalone commit yet.** The directory
  carries no content of its own; subsequent tasks add files
  and commit them.

**Verification:** `ls -d .claude/rules` returns the path.

---

### Task A6: Verify `scripts/` and `scripts/hooks/` directories

**Files:** verification only.

**Depends on:** A1.

The in-flight commit `00284252` bundled the `scripts/`
directory creation alongside the lakefile change. This task
confirms both directories exist.

- [ ] **Step 1: Verify existence.**

  ```sh
  ls -d scripts scripts/hooks
  ```

  Expected: both paths returned.

- [ ] **Step 2: No commit needed.** The directories exist
  from the in-flight work.

**Verification:** `ls -d scripts scripts/hooks` succeeds.

---

### Task A7: Verify `scripts/check-axioms.sh` (in-flight)

**Files:** verify `geb-lean/scripts/check-axioms.sh`.

**Depends on:** A6.

The in-flight commit `6bbd7d75` vendored this script.
This task verifies it is executable, has the correct
allowlist, and runs.

- [ ] **Step 1: Confirm the file is executable.**

  ```sh
  test -x scripts/check-axioms.sh
  ```

- [ ] **Step 2: Confirm the allowlist.**

  ```sh
  grep 'ALLOW_LIST\|allowlist\|propext\|Quot\.sound' \
    scripts/check-axioms.sh | head -5
  ```

  Expected: the allowlist contains `propext`, `Quot.sound`,
  `quot.sound` and does NOT contain `Classical.choice`.

- [ ] **Step 3: Smoke-test.**

  ```sh
  bash scripts/check-axioms.sh GebLean/ test/
  ```

  Expected: the script runs to completion and exits with a
  defined code. In report-only mode the output may list
  many flagged declarations; this is the documented current
  state.

- [ ] **Step 4: Confirm the header comment records upstream.**

  ```sh
  head -20 scripts/check-axioms.sh
  ```

  Expected: a header comment recording the upstream source
  URL and local modification description.

**Verification:** executable; allowlist correct;
smoke-test runs; header present.

---

### Task A8: Verify `scripts/check-jj-setup.sh` (in-flight)

**Files:** verify `geb-lean/scripts/check-jj-setup.sh`.

**Depends on:** A6.

The in-flight commit `e6340e29` authored this script.
This task verifies it exits non-zero in a non-jj-initialised
state and that its three assertions use `jj root`-based
discovery per the spec.

- [ ] **Step 1: Confirm executable.**

  ```sh
  test -x scripts/check-jj-setup.sh
  ```

- [ ] **Step 2: Smoke-test in non-jj state.**

  ```sh
  bash scripts/check-jj-setup.sh
  ```

  Expected: exits non-zero with a diagnostic message naming
  `docs/process.md`.

- [ ] **Step 3: Check the three assertion points.**

  Review the script to confirm it asserts:

  - (a) `jj config list --repo git.private-commits`
    output stripped to bare value equals `conflicts()`
    (anchored, not substring).
  - (b) `jj config list --repo remotes.origin.fetch-tags`
    output stripped to bare value equals `glob:cutover-*`
    (anchored).
  - (c) at least one of `jj config get signing.behavior`
    or `git config --get commit.gpgsign` returns a value
    indicating signing is active.

**Verification:** executable; exits non-zero with diagnostic
naming `docs/process.md`; three assertions present.

---

### Task A9: Verify `scripts/hooks/block-mutating-git.sh` (post-C5)

**Files:** verify `geb-lean/scripts/hooks/block-mutating-git.sh`.

**Depends on:** C5.

After cleanup task C5, the hook uses `jj root` for `.jj/`
discovery. This task runs the syntax check and re-confirms
the five smoke-test cases per verification checklist item 12.

- [ ] **Step 1: Syntax check.**

  ```sh
  bash -n scripts/hooks/block-mutating-git.sh
  ```

- [ ] **Step 2: Run the five required cases.**

  ```sh
  echo '{"tool_name":"Bash","tool_input":{"command":"git commit -m x"}}' \
    | bash scripts/hooks/block-mutating-git.sh; echo "exit=$?"
  echo '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote origin -b feat/x"}}' \
    | bash scripts/hooks/block-mutating-git.sh; echo "exit=$?"
  echo '{"tool_name":"Bash","tool_input":{"command":"git status"}}' \
    | bash scripts/hooks/block-mutating-git.sh; echo "exit=$?"
  echo '{"tool_name":"Bash","tool_input":{"command":"git checkout -b new-branch"}}' \
    | bash scripts/hooks/block-mutating-git.sh; echo "exit=$?"
  echo '{"tool_name":"Bash","tool_input":{"command":"git push origin refs/tags/v1.0.0:refs/tags/v1.0.0"}}' \
    | bash scripts/hooks/block-mutating-git.sh; echo "exit=$?"
  ```

  Expected exits: 2, 0, 0, 2, 2 respectively. Case (b)
  requires the CWD to be inside a jj-initialised tree; if
  jj is not yet initialised at the parent (A24 is later),
  run this case after A24 or set `CLAUDE_PROJECT_DIR` to
  any directory with a `.jj/` subdirectory. Record the five
  outputs for the A28 verification report.

**Verification:** syntax check passes; all five cases match
expectation.

---

### Task A10: Smoke-test `check-signing-key.sh` (in-flight)

**Files:** verify `geb-lean/scripts/hooks/check-signing-key.sh`.

**Depends on:** A6.

The in-flight commit `813d70b7` authored this script.

- [ ] **Step 1: Confirm executable.**

  ```sh
  test -x scripts/hooks/check-signing-key.sh
  ```

- [ ] **Step 2: Smoke-test.**

  ```sh
  bash scripts/hooks/check-signing-key.sh
  echo "exit=$?"
  ```

  Expected: exits 0. If signing is configured locally,
  gpg or ssh agent activity may follow; if not, the script
  exits 0 silently.

- [ ] **Step 3: Syntax check.**

  ```sh
  bash -n scripts/hooks/check-signing-key.sh
  ```

**Verification:** executable; exits 0; `bash -n` passes.

---

### Task A11: (Merged into A6–A10 above)

Task A11 from the 2026-05-07 plan (`check-signing-key.sh`
authoring) is already covered by the in-flight commit
`813d70b7` and the verification in Task A10 above. No
separate task is needed.

---

### Task A12: Update parent `geb/.gitignore` to permit committed `.claude/` paths

**Files:** modify `geb/.gitignore`.

**Depends on:** C3, A5.

The parent `geb/.gitignore` currently has `.claude` (no
slash, line 7), which blanket-ignores all `.claude/`
directories everywhere in the monorepo. Per spec
§ `.gitignore` change at the parent, replace it with
explicit patterns that permit `geb-lean/.claude/settings.json`
and `geb-lean/.claude/rules/` while keeping the sibling
subprojects' `.claude/` ignored.

- [ ] **Step 1: Edit `geb/.gitignore`.**

  Find the line `.claude` (no slash) and replace it with:

  ```gitignore
  /.claude/
  geb-agda/.claude
  geb-idris/.claude
  /geb-lean/.claude/*
  !/geb-lean/.claude/rules/
  !/geb-lean/.claude/settings.json
  ```

  All other lines in the parent `.gitignore` are preserved.

- [ ] **Step 2: Verify from the parent root.**

  Run from `geb/`:

  ```sh
  git check-ignore -v geb-lean/.claude/settings.json
  git check-ignore -v geb-lean/.claude/rules/lean-coding.md
  git check-ignore -v geb-lean/.claude/settings.local.json
  ```

  Expected:
  - First two: no output (not ignored).
  - Third: shows ignored via
    `/geb-lean/.claude/*` pattern.

- [ ] **Step 3: Commit from the parent root.**

  ```sh
  git -C .. add .gitignore
  git -C .. commit -m \
    "chore(gitignore): permit geb-lean/.claude/{rules/,settings.json}"
  ```

**Verification:** the three `git check-ignore` tests
produce the expected results.

---

### Task A13: Add `axiom_check` job to `lean_action_ci.yml` (report-only)

**Files:** modify `geb/.github/workflows/lean_action_ci.yml`.

**Depends on:** C6, A7.

Add the `axiom_check` job after the existing `build` job.
Per spec § CI changes, the job runs in report-only mode
(`--exit-zero-on-findings`) and uploads a CI artefact.

- [ ] **Step 1: Resolve `actions/upload-artifact` SHA.**

  Look up the latest SHA for `actions/upload-artifact@v4`
  at <https://github.com/actions/upload-artifact/releases>
  and write it directly into the workflow file (no
  `<SHA>` placeholder — use the resolved 40-hex-char hash).

- [ ] **Step 2: Add the job.**

  Append to `geb/.github/workflows/lean_action_ci.yml`:

  ```yaml
  axiom_check:
    runs-on: ubuntu-latest
    needs: [build]
    steps:
      - uses: actions/checkout@<checkout-SHA>
      - name: Run axiom check (report-only)
        run: |
          bash scripts/check-axioms.sh --exit-zero-on-findings \
            GebLean/ test/ \
            | tee axiom-check-report.txt
      - name: Upload axiom-check report
        uses: actions/upload-artifact@<upload-SHA>
        with:
          name: axiom-check-report
          path: geb-lean/axiom-check-report.txt
          if-no-files-found: error
  ```

  Both `<checkout-SHA>` and `<upload-SHA>` are replaced
  with resolved 40-hex-char SHAs. The `run:` steps inherit
  `defaults.run.working-directory: geb-lean` from the
  workflow level, so `bash scripts/check-axioms.sh` runs
  from `geb-lean/` and `axiom-check-report.txt` is written
  there. The upload `path:` references the repo-root-relative
  form `geb-lean/axiom-check-report.txt`.

- [ ] **Step 3: YAML validity check.**

  ```sh
  python3 -c \
    "import yaml, sys; yaml.safe_load(open(\
    '../.github/workflows/lean_action_ci.yml'))"
  ```

- [ ] **Step 4: Commit.**

  ```sh
  git -C .. add .github/workflows/lean_action_ci.yml
  git -C .. commit -m "ci: add axiom_check job in report-only mode"
  ```

**Verification:** the workflow file is YAML-valid;
`axiom_check` job declares `needs: [build]`; both action
SHAs are 40-hex-char commit IDs (not tag refs); the step
uses `--exit-zero-on-findings`.

---

### Task A14: Author `geb-lean/.claude/rules/lean-disciplines.md`

**Files:** create `geb-lean/.claude/rules/lean-disciplines.md`.

**Depends on:** A12.

- [ ] **Step 1: Author the file.**

  No `paths:` frontmatter (loaded unconditionally per spec
  § `.claude/rules/lean-disciplines.md`). Content sections:

  1. Hole-marking discipline.
  2. Constructive-only Lean code.
  3. Literature-citation discipline.
  4. Bottom-up named-composite discipline for categorical
     equivalences.
  5. Non-negotiable interfaces for categories formalising
     pre-existing mathematical objects.

  The spec carries the full prose for each section; render
  it into the file observing the 80-character line limit
  and the forbidden-word list.

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    '.claude/rules/lean-disciplines.md'
  ```

  Expected: zero violations.

- [ ] **Step 3: Commit.**

  ```sh
  git add .claude/rules/lean-disciplines.md
  git commit -m \
    "doc(rules): add lean-disciplines unconditionally-loaded rule"
  ```

**Verification:** the file exists, has no `paths:`
frontmatter, and is markdownlint-clean.

---

### Task A15: Author `geb-lean/.claude/rules/lean-coding.md`

**Files:** create `geb-lean/.claude/rules/lean-coding.md`.

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

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    '.claude/rules/lean-coding.md'
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git add .claude/rules/lean-coding.md
  git commit -m "doc(rules): add lean-coding path-scoped rule"
  ```

**Verification:** file exists with `paths:` frontmatter
matching `**/*.lean`; markdownlint-clean.

---

### Task A16: Author `geb-lean/.claude/rules/markdown-writing.md`

**Files:** create `geb-lean/.claude/rules/markdown-writing.md`.

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
  9. No nested `CLAUDE.md` files (per spec § CLAUDE.md
     content); per-area instructions go in
     `.claude/rules/<name>.md` with `paths:` frontmatter.

  Item 9 must appear as a standalone top-level item, not
  as a sub-bullet of item 8.

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    '.claude/rules/markdown-writing.md'
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git add .claude/rules/markdown-writing.md
  git commit -m "doc(rules): add markdown-writing path-scoped rule"
  ```

**Verification:** file exists with `paths:` frontmatter
`**/*.md`; the no-nested-`CLAUDE.md` rule appears as a
standalone top-level item (item 9), not as a sub-bullet
of item 8; markdownlint-clean.

---

### Task A17: Author `geb-lean/.claude/rules/ci-and-workflow.md`

**Files:** create `geb-lean/.claude/rules/ci-and-workflow.md`.

**Depends on:** A12.

- [ ] **Step 1: Author the file.**

  YAML frontmatter:

  ```yaml
  paths:
    - ".github/workflows/**"
    - "scripts/**"
  ```

  Content sections per spec § `.claude/rules/ci-and-workflow.md`:

  1. Workflow conventions (SHA-pinning policy; note that
     the active CI workflows live at the parent
     `geb/.github/workflows/` level and are path-filtered
     to `geb-lean/**`; `update.yml` and `create-release.yml`
     remain inert at `geb-lean/.github/workflows/`).
  2. Pre-push checklist.
  3. Hook-script conventions.
  4. Commit-message convention.

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    '.claude/rules/ci-and-workflow.md'
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git add .claude/rules/ci-and-workflow.md
  git commit -m "doc(rules): add ci-and-workflow path-scoped rule"
  ```

**Verification:** file exists with the two-glob `paths:`
frontmatter; markdownlint-clean.

---

### Task A18: Author `geb-lean/docs/process.md`

**Files:** create `geb-lean/docs/process.md`.

**Depends on:** A14, A15, A16, A17.

- [ ] **Step 1: Author the file.**

  Eighteen sections (each ~5–10 lines), index-shaped,
  per spec § `docs/process.md`:

  1. Repository structure (geb-lean is a subdirectory;
     jj colocated at parent; hooks at `geb-lean/scripts/hooks/`;
     CI at `geb/.github/workflows/`; pre-push is
     geb-lean-scoped).
  2. Phase-driven workflow (includes the MCP server list:
     `arxiv-mcp-server`, `memory`, `MCP Solver` — one line
     each with role description and upstream URL).
  3. Adversarial review of specs and plans.
  4. Order of artefact production.
  5. Verify agent claims against authoritative sources.
  6. Constructive-only Lean code.
  7. `main` / `integration` / topic-branch model.
  8. `jj` colocated mode (at parent `geb/` root;
     `git clean -xdf` warning; `.jj/.gitignore`
     self-exclusion; the explicit
     `git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
     fallback if `fetch-tags` is removed in a later jj
     release; the on-boarding sequence reproduced verbatim).
  9. Comment and docstring style.
  10. Markdownlint discipline (records rationale for each
      override in `.markdownlint-cli2.jsonc`).
  11. No LLM-drafted user-facing text.
  12. Generic user references.
  13. Process self-update mechanism.
  14. GebLean-specific: literature-citation discipline.
  15. GebLean-specific: bottom-up named-composite discipline.
  16. GebLean-specific: non-negotiable interfaces.
  17. GebLean-specific: relationship to geb-mathlib.
  18. GebLean-specific: no per-file copyright or author
      headers.

  § 2's MCP list must stay in sync with `CLAUDE.md`
  § Tooling (Task A23).

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'docs/process.md'
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git add docs/process.md
  git commit -m "doc: add docs/process.md rationale layer"
  ```

**Verification:** the file exists; markdownlint-clean;
all eighteen sections are present.

---

### Task A19: Author `geb-lean/docs/index.md`

**Files:** create `geb-lean/docs/index.md`.

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
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'docs/index.md'
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git add docs/index.md
  git commit -m "doc: add docs/index.md topological narrative"
  ```

**Verification:** the file exists; markdownlint-clean;
each listed area has at least the four named fields
(workstream name, source-tree paths, central concepts,
dependencies).

---

### Task A20: Author `geb-lean/docs/lean-resources.md`

**Files:** create `geb-lean/docs/lean-resources.md`.

**Depends on:** A1.

- [ ] **Step 1: Lift the link list from existing `CLAUDE.md`.**

  The existing `CLAUDE.md` § "Lean 4 Library and
  Categorical Theory Resources" carries the link list.
  Move it verbatim into `docs/lean-resources.md`,
  preserving topic organisation. The current `CLAUDE.md`
  will be rewritten in Task A23 and will not retain the
  lifted content; the new `CLAUDE.md` § Pointers links
  to `docs/lean-resources.md`.

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'docs/lean-resources.md'
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git add docs/lean-resources.md
  git commit -m "doc: lift mathlib resource list into docs/lean-resources.md"
  ```

**Verification:** the file exists; markdownlint-clean;
the topic organisation matches the source.

---

### Task A21: Author `geb-lean/TODO.md`

**Files:** create `geb-lean/TODO.md`.

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
  signed off (A34), and that the entry is removed from
  `TODO.md` once Milestone B concludes. The entry's
  **Spec** and **Plan** fields point at this refactor's
  spec and plan respectively.

  The second section is initially empty with the spec's
  exact disclaimer text (the paragraph beginning "Items
  intentionally deferred…").

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'TODO.md'
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

### Task A22: Author `geb-lean/README.md` and update parent `geb/README.md`

**Files:** create `geb-lean/README.md`;
modify `geb/README.md`.

**Depends on:** C1, A18, A19, A20, A21.

Two sub-tasks:

**A22a: New `geb-lean/README.md`.**

- [ ] **Step 1: Author the file from scratch.**

  Sections per spec § `README.md`:

  1. Project name and one-paragraph identity (opens with a
     framing line that geb-lean is a subproject of the
     geb/ monorepo; points at `../README.md` and
     `../LICENSE`).
  2. Status ("Active experimentation; process refactor
     of 2026-05-09 in effect.").
  3. Dependencies (mathlib + CSLib at pinned versions;
     pointer to `lakefile.toml`).
  4. Licence (GNU General Public License version 3;
     see `../LICENSE`).
  5. Index of project documentation (links to
     `docs/index.md`, `docs/process.md`,
     `docs/lean-resources.md`, this refactor's spec / plan).
  6. Index of project processes (link to `CLAUDE.md`;
     one-line descriptions of `.claude/rules/*.md` files).
  7. Contribution pointers.
  8. Pointers to `geb-mathlib`, mathlib4, CSLib.

  Length target ~150 lines.

- [ ] **Step 2: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'README.md'
  ```

- [ ] **Step 3: Commit.**

  ```sh
  git add README.md
  git commit -m "doc: add geb-lean/README.md in new index pattern"
  ```

**A22b: Pointer paragraph in parent `geb/README.md`.**

- [ ] **Step 4: Add the pointer near the top of
  `geb/README.md`.**

  After the title and any tagline, before the first body
  section, insert approximately three to five lines per
  spec § `README.md`:

  ```markdown
  The Lean formalisation of this project lives in `geb-lean/`;
  see [`geb-lean/README.md`](geb-lean/README.md). The material
  below documents the original implementation; the geb-lean
  subproject is the active development home for the Lean
  formalisation of this project.
  ```

- [ ] **Step 5: Markdown-lint the parent README.**

  ```sh
  markdownlint-cli2 \
    --config geb-lean/.markdownlint-cli2.jsonc \
    --no-globs \
    'geb-lean/../README.md'
  ```

  (Run from the parent `geb/` root, or adapt the path.)

- [ ] **Step 6: Commit.**

  ```sh
  git -C .. add README.md
  git -C .. commit -m "doc: add geb-lean pointer near top of geb/README.md"
  ```

**Verification:** `geb-lean/README.md` exists, is under
~150 lines (spec target; flexible up to ~170 if content
scope demands), and is markdownlint-clean. `geb/README.md`
carries the pointer paragraph near the top and is
markdownlint-clean.

---

### Task A23: Rewrite `geb-lean/CLAUDE.md` to ≤ 200 lines

**Files:** rewrite `geb-lean/CLAUDE.md`.

**Depends on:** A14, A15, A16, A17, A18, A19, A20, A21.

- [ ] **Step 1: Author the new CLAUDE.md.**

  Per the spec's per-section line budget (target ~187
  lines), sections in order:

  1. Project header and one-paragraph identity.
  2. Repository structure note (geb-lean/ is a subdirectory
     of the geb/ monorepo; cross-cutting infrastructure at
     the parent level; per spec § CLAUDE.md content).
  3. Project status.
  4. Hard rules — must not violate.
  5. Phase-driven workflow.
  6. Style guidelines.
  7. Repo structure.
  8. Constructive-only Lean code.
  9. Specs and plans live on the feature branch.
  10. GebLean-specific disciplines (three: literature
      citations, bottom-up named composites, non-negotiable
      interfaces).
  11. Cross-reference to file-edit-only Lean rules.
  12. Tooling (including MCP servers sub-list: one line
      each for `arxiv-mcp-server`, `memory`, `MCP Solver`).
  13. When to consider creating a project-specific skill.
  14. Pointers (navigation links to `docs/process.md`,
      `.claude/rules/`, `docs/index.md`,
      `docs/lean-resources.md`, and this refactor's spec
      and plan paths).

  If the draft exceeds 200 lines, apply the priority order
  for cuts per spec § "Priority order for cuts":

  1. Move the banned-word example list out of CLAUDE.md.
  2. Compress the phase-driven workflow table to one line
     per phase.
  3. Move tooling-detail bullets to `docs/process.md`.

  The previous link-list content has been lifted to
  `docs/lean-resources.md` (Task A20).

- [ ] **Step 2: Verify the line count.**

  ```sh
  wc -l CLAUDE.md
  ```

  Expected: ≤ 200 lines.

- [ ] **Step 3: Markdown-lint.**

  ```sh
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'CLAUDE.md'
  ```

- [ ] **Step 4: Commit.**

  ```sh
  git add CLAUDE.md
  git commit -m "doc: rewrite CLAUDE.md as slim always-on layer (≤ 200 lines)"
  ```

**Verification:** `wc -l CLAUDE.md` shows ≤ 200; the file
is markdownlint-clean; section 10 names the three
GebLean-specific disciplines; the "Repository structure
note" section is present after the header.

---

### Task A24: User-direct — initialise jj colocated at parent and run on-boarding

**Files:** none (per-developer local state outside the
repository).

**Depends on:** A8.

This task is performed by the **user** in their own terminal,
outside Claude Code. Claude must not attempt the commands.
The jj initialisation runs at the **parent `geb/` root**,
not at `geb-lean/`.

- [ ] **Step 1 (user-direct): navigate to parent and
  initialise jj.**

  ```sh
  cd /home/terence/git-workspaces/geb
  jj git init --colocate
  ```

  Expected: jj 0.41 prints "Done importing changes from the
  underlying Git repo." and "Initialized repo in '.'". The
  `git clean -xdf` warning is not printed in jj 0.41 (it
  is documented in `docs/process.md` § jj instead).

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
  jj config set --user signing.backend 'gpg'   # or 'ssh'
  jj config set --user signing.key '<key id>'
  ```

- [ ] **Step 4 (user-direct): first fetch.**

  ```sh
  jj git fetch --remote origin
  ```

  The `fetch-tags` pattern from step 2 takes effect on
  this invocation.

- [ ] **Step 5 (user-direct): run the verifier.**

  From anywhere under `geb/`:

  ```sh
  bash geb-lean/scripts/check-jj-setup.sh
  ```

  Expected: exits 0. If non-zero, follow the diagnostic
  back to the corresponding `jj config set` step.

**Verification:** `bash geb-lean/scripts/check-jj-setup.sh`
exits 0; `jj config path --repo` prints a path under the
user config directory (per jj 0.38+'s relocation), not
under `.jj/`.

---

### Task A25: Author `geb-lean/scripts/pre-push.sh`

**Files:** create `geb-lean/scripts/pre-push.sh`.

**Depends on:** A2, A7, A8, A24.

- [ ] **Step 1: Author the script.**

  Behaviour per spec § Auxiliary scripts → "scripts/pre-push.sh":

  1. `bash scripts/check-jj-setup.sh` (fail fast on
     unconfigured setup).
  2. `lake test` (builds `GebLean` and `GebLeanTests`).
  3. `lake lint`.
  4. `markdownlint-cli2 --config .markdownlint-cli2.jsonc \
     --no-globs '**/*.md'`
     (single quotes around `'**/*.md'` are load-bearing).
  5. `bash scripts/check-axioms.sh GebLean/ test/ || true`
     (informational pre-Milestone-B; `|| true` removed at
     Milestone B item B5).
  6. On-screen reminders for user-driven gates:
     `lean4:golf` and `lean4:review` ran on changed Lean
     code; user reviewed the diff line-by-line.

  A comment in the script records: "If a subsequent lakefile
  addition introduces a target outside the test driver's
  dependency graph, add `lake build` explicitly before
  `lake test`."

- [ ] **Step 2: Make it executable.**

  ```sh
  chmod +x scripts/pre-push.sh
  ```

- [ ] **Step 3: Smoke-test.**

  ```sh
  bash scripts/pre-push.sh
  ```

  Expected: each step runs; the script exits 0 if every
  step passes. Step 1 (`check-jj-setup.sh`) returns 0
  because A24 has just been completed.

- [ ] **Step 4: Commit.**

  ```sh
  git add scripts/pre-push.sh
  git commit -m "chore(scripts): add pre-push.sh manual checklist"
  ```

**Verification:** the script is executable; runs to
completion; each named step is invoked; exit code is 0.

---

### Task A26: Smoke-test the `conflicts()` push semantics

**Files:** none (behavioural verification of the
`git.private-commits = "conflicts()"` per-repo setting).

**Depends on:** A24.

This task verifies the spec's claim (§ jj setup) that
resolving a conflict locally and then pushing succeeds
without `--allow-private`.

- [ ] **Step 1: Manufacture a conflict on a throwaway
  jj bookmark.**

  Use a fresh tracked in-repo probe file
  `geb-lean/docs/.conflict-probe.md` (writing to `/tmp/`
  would not work; jj records changes to the working copy
  only). Create two divergent revisions:

  ```sh
  jj new -r main
  echo 'A' > geb-lean/docs/.conflict-probe.md
  jj describe -m "probe: A"
  jj bookmark create chore/conflict-probe-a -r @
  jj new -r main
  echo 'B' > geb-lean/docs/.conflict-probe.md
  jj describe -m "probe: B"
  jj bookmark create chore/conflict-probe-b -r @
  jj rebase -s chore/conflict-probe-b -d chore/conflict-probe-a
  jj log -r 'conflicts()'
  ```

- [ ] **Step 2: Confirm the push refuses while unresolved.**

  ```sh
  jj git push --remote origin -b chore/conflict-probe-b
  ```

  Expected: jj refuses with a `private-commits` diagnostic.
  Do not pass `--allow-private`.

- [ ] **Step 3: Resolve the conflict.**

  Edit the conflicted file to a single resolved value;
  `jj squash` or `jj describe` the resolution; confirm
  `jj log -r 'conflicts()'` no longer includes the revision.

- [ ] **Step 4: Push and confirm success.**

  ```sh
  jj git push --remote origin -b chore/conflict-probe-b
  ```

  Expected: push succeeds without `--allow-private`.

- [ ] **Step 5: Clean up.**

  ```sh
  jj bookmark delete chore/conflict-probe-a
  jj bookmark delete chore/conflict-probe-b
  jj git push --remote origin --deleted
  rm -f geb-lean/docs/.conflict-probe.md
  ```

- [ ] **Step 6: No commit produced by this task.**

  If empirical observation contradicts the spec's
  expectation, surface to the user immediately with the
  recorded session output; the spec's wording would need
  amendment.

**Verification:** the resolved push succeeded without
`--allow-private`; `jj log -r 'conflicts()'` is empty
after step 3; both throwaway bookmarks deleted.

---

### Task A27: Wire `geb-lean/.claude/settings.json`

**Files:** create `geb-lean/.claude/settings.json`.

**Depends on:** C5, A9, A10, A12, A23, A25, A26.

This is the **final Claude-direct commit-producing task**
in Milestone A. After this task lands, no further
`git add` / `git commit` from Claude is permitted in the
same session; subsequent commit-producing work is either
user-direct or routed through `jj describe`.

- [ ] **Step 1: Author the settings file.**

  The file wires both hooks per spec § Hooks.
  Use `${CLAUDE_PROJECT_DIR}` for the script paths so the
  file is portable across worktrees. The
  `geb-lean/.claude/settings.json` path (not the parent's
  `.claude/`) is the committed location per spec § Hooks.

  Content skeleton (verify the exact field names against the
  Claude Code `settings.json` documentation at execution
  time; if the schema has changed, use the documented form
  and note the deviation):

  ```json
  {
    "hooks": {
      "PreToolUse": [
        {
          "matcher": "Bash",
          "hooks": [
            {
              "type": "command",
              "command":
                "${CLAUDE_PROJECT_DIR}/scripts/hooks/block-mutating-git.sh"
            }
          ]
        }
      ],
      "SessionStart": [
        {
          "hooks": [
            {
              "type": "command",
              "command":
                "${CLAUDE_PROJECT_DIR}/scripts/hooks/check-signing-key.sh"
            }
          ]
        }
      ]
    }
  }
  ```

  The `$schema` URL (`https://json.schemastore.org/claude-code-settings.json`)
  may be added as a top-level field if the Claude Code
  documentation confirms it is valid at execution time;
  omit it if uncertain to avoid a spurious schema-validation
  error.

- [ ] **Step 2: Commit.**

  ```sh
  git add .claude/settings.json
  git commit -m \
    "chore(claude): wire block-mutating-git and check-signing-key hooks"
  ```

**Verification:**

- (a) The file is JSON-parseable:

  ```sh
  python3 -c "import json; json.load(open('.claude/settings.json'))"
  ```

- (b) Both hook script paths are present:

  ```sh
  python3 -c "
  import json
  s = json.load(open('.claude/settings.json'))
  hooks = s['hooks']
  pre = hooks['PreToolUse'][0]['hooks'][0]['command']
  sess = hooks['SessionStart'][0]['hooks'][0]['command']
  assert 'block-mutating-git.sh' in pre, pre
  assert 'check-signing-key.sh' in sess, sess
  print('hook paths ok')
  "
  ```

- (c) Re-run the five `block-mutating-git.sh` smoke-test
  cases as documented in C5's body and as enumerated in
  spec verification matrix item 12 (cases (a)-(e)) to
  confirm the hook fires correctly via the wired settings.
  The five cases are defined in Task A9 (not A10; A10
  covers `check-signing-key.sh`).

---

### Task A28: Run the Milestone A verification checklist

**Files:** none.

**Depends on:** C1–C6, A1 through A27.

- [ ] **Step 1: Run every mechanically-checkable item
  (1–14) from spec § Milestone A — verification checklist.**

  ```sh
  # 1 — lake build and test
  lake build && lake test
  # 2 — markdownlint on refactor-authored files
  markdownlint-cli2 \
    --config .markdownlint-cli2.jsonc \
    --no-globs \
    'CLAUDE.md' \
    '.claude/rules/*.md' \
    'docs/process.md' \
    'docs/index.md' \
    'docs/lean-resources.md' \
    'TODO.md' \
    'README.md'
  # 3 — check-axioms.sh runs to completion
  bash scripts/check-axioms.sh GebLean/ test/
  # 4 — lake lint quiet; positive probe
  lake lint
  # (introduce and remove a deliberate violation per A2 step 3)
  # 5 — CLAUDE.md line count
  test "$(wc -l < CLAUDE.md)" -le 200
  # 6 — rule files exist
  ls .claude/rules/lean-disciplines.md \
     .claude/rules/lean-coding.md \
     .claude/rules/markdown-writing.md \
     .claude/rules/ci-and-workflow.md
  # 7 — docs files exist
  ls docs/process.md docs/index.md docs/lean-resources.md
  # 8 — TODO.md exists with both sections
  test -f TODO.md
  # 9 — geb-lean README exists; parent README has pointer
  test -f README.md
  grep -q 'geb-lean/README.md' ../README.md
  # 10 — gitignore verification (run from geb/ root)
  git -C .. check-ignore -v geb-lean/.claude/settings.json
  git -C .. check-ignore -v geb-lean/.claude/rules/lean-coding.md
  git -C .. check-ignore -v geb-lean/.claude/settings.local.json
  # 11 — jj configuration
  bash scripts/check-jj-setup.sh
  # 12 — hook smoke tests (re-run five A9 cases)
  # (see Task A9 step 2 commands)
  # 13 — parent workflow files exist and are correct
  ls ../.github/workflows/markdown-lint.yml \
     ../.github/workflows/lean_action_ci.yml
  grep 'geb-lean/\*\*' ../.github/workflows/lean_action_ci.yml
  grep 'axiom_check' ../.github/workflows/lean_action_ci.yml
  # 14 — scripts exist and are executable
  ls scripts/check-axioms.sh scripts/check-jj-setup.sh \
     scripts/pre-push.sh \
     scripts/hooks/block-mutating-git.sh \
     scripts/hooks/check-signing-key.sh
  ```

  For item 10, expected results:

  - First two `git check-ignore` calls: no output (not
    ignored).
  - Third: shows ignored via `/geb-lean/.claude/*` pattern.

  For item 12, the five smoke-test cases from Task A9
  are re-run; record pass/fail.

- [ ] **Step 2: Surface results to the user.**

  Report each item with pass/fail. If any item fails,
  diagnose, fix (via user-direct edits if a `git commit`
  is required, since the hook is wired), and re-run; do
  not proceed to A29 until all items pass.

**Verification:** all fourteen items pass; the A9
smoke-test re-run output and the A26 conflict-push output
are recorded.

---

### Task A29: User-direct — push topic branch and merge to `main` via merge commit

**Files:** none (VCS only).

**Depends on:** A28.

This task is performed by the **user** at the parent
`geb/` root.

- [ ] **Step 1 (user-direct): line-by-line diff review.**

  ```sh
  git log --first-parent main..chore/process-refactor
  git diff main..chore/process-refactor
  ```

- [ ] **Step 2 (user-direct): push the topic branch.**

  ```sh
  jj git push --remote origin -b chore/process-refactor
  ```

- [ ] **Step 3 (user-direct): open the PR and merge to
  `main` via a normal merge commit.**

  The merge form is a **normal merge commit** per spec
  § Branch model (no fast-forward). The merge commit on
  the parent's `main` is the **cutover commit**.

- [ ] **Step 4 (user-direct): record the cutover SHA.**

  After the merge, capture the SHA. Save temporarily;
  A31 records it in `docs/process.md` § Branch model.

**Verification:** `git log --first-parent origin/main`
shows the merge commit at the tip; the SHA is recorded.

---

### Task A30: User-direct — create and push the signed cutover tag

**Files:** none (VCS only).

**Depends on:** A29.

This task is performed by the **user**. Run at the parent
`geb/` root.

- [ ] **Step 1 (user-direct): verify no pre-existing
  `cutover-*` tag is present.**

  ```sh
  git tag --list 'cutover-*'
  ```

  Expected: prints zero lines.

- [ ] **Step 2 (user-direct): create the signed tag.**

  ```sh
  git tag -s cutover-2026-MM-DD <SHA> \
    -m "Process bootstrap cutover"
  ```

- [ ] **Step 3 (user-direct): re-confirm exactly one
  matching tag exists.**

  ```sh
  git tag --list 'cutover-*'
  ```

  Expected: prints exactly one line.

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
  is avoided per spec verification item 17.

**Verification:** `git ls-remote --tags origin
cutover-2026-MM-DD` returns one line matching the SHA
recorded at A29 step 4.

---

### Task A31: User-direct — record the cutover SHA via follow-up topic branch

**Files:** modify `geb-lean/docs/process.md` (on a
follow-up topic branch at parent).

**Depends on:** A29, A30.

This task is performed by the **user** via a follow-up
topic branch (`docs/cutover-sha-record`).

- [ ] **Step 1 (user-direct): create the follow-up topic
  branch.**

  ```sh
  jj new -r main
  jj bookmark create docs/cutover-sha-record -r @
  ```

- [ ] **Step 2 (user-direct): edit `docs/process.md`
  § Branch model.**

  Insert the cutover commit's SHA into the section.
  The tag is the authoritative record; the SHA in
  `docs/process.md` is a navigation aid only.

- [ ] **Step 3 (user-direct): describe and push.**

  ```sh
  jj describe -m "doc: record cutover SHA in docs/process.md"
  jj git push --remote origin -b docs/cutover-sha-record
  ```

- [ ] **Step 4 (user-direct): open PR and merge to `main`.**

  Normal merge commit.

**Verification:** `docs/process.md` § Branch model carries
the SHA; SHA matches `git ls-remote --tags origin
cutover-2026-MM-DD`; `git log --first-parent origin/main`
shows the new merge commit on top of the cutover commit.

---

### Task A32: User-direct — `integration` branch and CI triggers

**Files:** modify `geb/.github/workflows/markdown-lint.yml`
and `geb/.github/workflows/lean_action_ci.yml` (on a
follow-up topic branch); create the `integration` bookmark.

**Depends on:** A29, A31.

This task is performed by the **user**.

- [ ] **Step 1 (user-direct): create the
  CI-trigger-update topic branch.**

  ```sh
  jj new -r main
  jj bookmark create ci/integration-trigger -r @
  ```

- [ ] **Step 2 (user-direct): edit both workflows to
  include `integration` in the push trigger.**

  In `geb/.github/workflows/markdown-lint.yml` and
  `geb/.github/workflows/lean_action_ci.yml`, change
  `on.push.branches:` from `[main]` to
  `[main, integration]`.

- [ ] **Step 3 (user-direct): describe, push, open PR,
  merge.**

  ```sh
  jj describe -m "ci: trigger workflows on integration pushes"
  jj git push --remote origin -b ci/integration-trigger
  ```

  Merge to `main` via normal merge commit.

- [ ] **Step 4 (user-direct): regenerate `integration`
  as fan-in of `main` plus all active topic branches.**

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

- [ ] **Step 5 (user-direct): push the bookmark.**

  ```sh
  jj git push --remote origin -b integration
  ```

  The CI workflows (now including `integration` in their
  trigger lists) fire on this push.

**Verification:** `git ls-remote origin integration`
returns one line; both workflows' Actions tabs show a run
for the integration push.

---

### Task A33: User-direct — configure GitHub repository protection Rulesets

**Files:** none (configured in GitHub UI at parent).

**Depends on:** A30.

This task is performed by the **user** in the GitHub web
UI under Repository settings → Rules → Rulesets (on the
parent repo `<owner>/geb`).

- [ ] **Step 1 (user-direct): create the `main` branch
  Ruleset.**

  Forbid force-pushes and branch deletion on `main`.

- [ ] **Step 2 (user-direct): create the `cutover-*` tag
  Ruleset.**

  Forbid deletion of tags matching `cutover-*`. (Tag
  protection rules under Settings → Tags are a deprecated
  alternative; either mechanism suffices, but the Ruleset
  is preferred.)

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
  the existing `.session/README.md` content:

  ```markdown
  > **Note (post-Milestone-A)**: `TODO.md` at the
  > repository root is now the source of truth for active
  > work. The contents below are legacy entries pending
  > triage. See `docs/process.md` § Workstream triage
  > method for the migration scheme. The directory will be
  > removed at Milestone B.
  ```

- [ ] **Step 2: Markdown-lint.**

  The `.markdownlint-cli2.jsonc` config lists `.session/**`
  in its `ignores` array, so the standard invocation would
  silently skip this file. Use an explicit invocation that
  bypasses the ignore for this single file:

  ```sh
  markdownlint-cli2 --no-globs '.session/README.md'
  ```

  (No `--config` flag: the bare invocation applies only
  the built-in defaults, which is sufficient for checking
  that the prepended blockquote does not introduce lint
  violations.)

- [ ] **Step 3: Commit via jj describe.**

  ```sh
  jj new -r main
  jj bookmark create docs/session-milestone-a-note -r @
  jj describe -m \
    "doc(session): add post-Milestone-A transitional note"
  ```

  The user then runs from the parent `geb/` working tree:

  ```sh
  jj git push --remote origin \
    -b docs/session-milestone-a-note
  ```

**Verification:** the file's first non-blank line is the
transitional note; markdownlint-clean via the explicit
`markdownlint-cli2 --no-globs '.session/README.md'`
invocation (the standard config-based invocation skips
this path due to the `.session/**` ignore entry).

---

### Task B2: Triage every `.session/workstreams/*.md`

**Files:** modify (many) `.session/workstreams/*.md`,
`TODO.md`, `docs/index.md`; delete `.session/workstreams/*.md`
entries per disposition.

**Depends on:** B1.

This task is open-ended. Each `.session/workstreams/<name>.md`
file is a sub-task. Approximately 78 files exist as of spec
drafting.

For each file, apply the spec's triage template
(§ Triage execution) verbatim:

> Read the file. Cross-reference against `git log` for
> any commits referencing the workstream's topic, against
> current source-tree state, and against the Claude-harness
> task list. Before deletion, run
> `grep -r '.session/<name>'` across `docs/superpowers/`,
> `docs/`, `README.md`, and `CLAUDE.md` to find inbound
> references; either update each reference to point at
> the new home or migrate the referenced content first.
> Propose a classification (one of `live` /
> `live-deferred-to-geb-mathlib` / `completed` /
> `superseded` / `abandoned` / `unclear`) with a
> one-sentence justification. Surface to user for
> confirmation. On confirmation, perform the disposition.

Disposition by label:

- `live` → migrate to `TODO.md` § Active in geb-lean.
- `live-deferred-to-geb-mathlib` → migrate to `TODO.md`
  § To be done in geb-mathlib.
- `completed` → describe in `docs/index.md` if not already;
  delete `.session/` entry.
- `superseded` → delete `.session/` entry; preserve any
  non-obvious "why superseded" notes in the surviving
  approach's spec / plan.
- `abandoned` → delete `.session/` entry.
- `unclear` → surface explicitly for user decision; do
  not auto-classify.

Each file is one sub-task. Describe each disposition
individually via `jj describe -m "doc(triage): <name>
classified as <label>"` on a Milestone-B topic branch.

**Verification (cumulative):** every file under
`.session/workstreams/` has been triaged with user
confirmation; the directory listing shrinks to empty.

---

### Task B3: Reset the Claude-harness task list

**Files:** none (harness state, not in the working tree).

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

- [ ] **Step 2: Remove the directory via the working copy.**

  The raw `git rm -rf .session/` form is denied by the
  `block-mutating-git` hook; use the working-copy form
  recognised by jj:

  ```sh
  jj new -r main
  jj bookmark create chore/session-retire -r @
  rm -rf .session/
  jj describe -m \
    "chore(session): retire .session directory at Milestone B"
  ```

  This includes `.session/README.md` and any
  `.session/docs/` content.

  The user then runs from the parent `geb/` working tree:

  ```sh
  jj git push --remote origin -b chore/session-retire
  ```

**Verification:** the directory does not exist; `jj status`
reflects the deletion as part of the working copy.

---

### Task B5: Flip `axiom_check` to fail-mode

**Files:** modify `geb/.github/workflows/lean_action_ci.yml`
(via a Milestone-B topic branch).

**Depends on:** B2 (each touched Lean file gets its
`AXIOM_ALLOW` annotations during triage; the report-only
output should shrink toward empty as triage progresses).

- [ ] **Step 1: Confirm report-only output is empty.**

  ```sh
  bash scripts/check-axioms.sh GebLean/ test/
  ```

  Expected: zero non-allowlisted axioms remain unannotated.
  If any remain, annotate (with
  `AXIOM_ALLOW: <axiom> (rationale)`) or refactor before
  flipping.

- [ ] **Step 2: Edit the workflow.**

  Remove the `--exit-zero-on-findings` flag from the
  `axiom_check` job's `run:` step; the job's exit code
  now gates the workflow. The failure condition: any
  non-allowlisted axiom (anything other than `propext`,
  `Quot.sound`, `quot.sound`) appears in the closure of
  any declaration without a matching `AXIOM_ALLOW`
  comment.

- [ ] **Step 2b: Drop the `|| true` suffix in
  `scripts/pre-push.sh`.**

  The axiom-check step in `scripts/pre-push.sh` was
  authored at A25 with `|| true` so that pre-push did
  not fail pre-Milestone-B. Remove the `|| true` suffix
  from the relevant line.

- [ ] **Step 3: Describe and push via topic branch.**

  ```sh
  jj new -r main
  jj bookmark create ci/axiom-check-fail-mode -r @
  jj describe -m \
    "ci: flip axiom_check from report-only to fail-mode"
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

  All Milestone B items (plan tasks B1–B6, corresponding
  to spec items B1–B7; the spec's B5 is this plan's B3,
  and the spec's B7 axiom-check fail-mode flip is this
  plan's B5), with status for each.

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
| Cleanup | C1–C6 | Prereq reverts/repairs; all Claude-direct git-add+git-commit. |
| A | A1–A34 | Structural refactor; C1–C6 and A1–A23 are Claude-direct git-add+git-commit (hook unwired); A24 is user-direct jj on-boarding at parent; A25 is the last Claude-direct commit before A27; A26 is a non-commit conflict-push smoke test; A27 wires the hook (final Claude-direct commit); A28 verifies; A29–A33 are user-direct VCS / GitHub UI; A34 surfaces. |
| B | B1–B6 | Triage and retirement; open-ended (~78 workstream entries, each one user-confirmed sub-task). All commit-producing B-tasks use `jj describe` since the hook is wired. |

**Sequence dependencies (load-bearing):**

- C3 precedes A5 and A12.
- C4 precedes A3 and A4.
- C5 precedes A9 and A27.
- C6 precedes A13 and A28.
- A2 (lintDriver verification) precedes A25 (pre-push uses
  `lake lint`).
- A6 (scripts/ dirs) precedes A7, A8, A9, A10.
- A12 (parent `.gitignore`) precedes A14–A17 and A27.
- A14–A17 (rule files) precede A18 (`docs/process.md`)
  and A23 (`CLAUDE.md` rewrite).
- A19, A20, A21 precede A22 (`README.md` rewrite).
- A24 (jj init, user-direct at parent) precedes A25
  (`pre-push.sh` smoke test) and A26 (conflicts() smoke
  test).
- A23, A25, A26 precede A27 (settings wiring, final
  Claude-direct commit).
- A27 precedes A28 (verification).
- A28 precedes A29 (push topic branch + cutover merge).
- A29 precedes A30 (cutover tag) and A31 (record SHA).
- A32 (integration branch)'s technical dependencies are
  A29 and A31.
- A30 precedes A33 (Rulesets — the tag must exist before
  the tag-protection Ruleset can target it).
- A31, A32, A33 precede A34.
- A34 precedes B1 (no Milestone-B work begins until the
  user confirms Milestone A).
- B2 precedes B3, B4, B5.

**User-direct steps:** A24, A29, A30, A31, A32, A33,
plus the per-workstream confirmations and pushes in
B1–B5.
