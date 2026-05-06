# CSLib Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add CSLib (`leanprover/cslib`) as a Lake dependency of the
GebLean project, parallel to mathlib, with documented search guidance
and reference memory; verify the dependency resolves and compiles.

**Architecture:** Mechanical integration — single feature branch in a
worktree, single commit on the branch, fast-forward into `main`. No
GebLean code uses CSLib in this commit; the smoke test that exercises
URM is throwaway. The CSLib pin is `v4.29.0-rc6`, matching our Lean
toolchain exactly.

**Tech Stack:** Lean 4 (`v4.29.0-rc6`), Lake, mathlib (transitive
shared dep), CSLib, markdownlint-cli2, `gh`.

**Spec:** `docs/superpowers/specs/2026-05-06-cslib-integration-design.md`.

---

## File-level structure

- `lakefile.toml` — modify to add the CSLib `[[require]]`.
- `lake-manifest.json` — modify (resolver-driven) to record the
  resolved CSLib entry plus any transitive cascading.
- `CLAUDE.md` — modify the external-deps line, the search guidance,
  and add the CSLib resources subsection.
- `reference_cslib.md` — create the reference memory file under the
  project's memory directory (absolute path in Task 9).
- `MEMORY.md` — modify to add the CSLib pointer.
- `.session/workstreams/cslib-integration.md` — create at Task 1,
  delete at Task 11 (active-workstream tracker).
- Smoke test (transient, name in Task 6) — create, build, delete.

---

## Task 1: Set up worktree and workstream tracker

**Files:**

- Create (worktree): branch `cslib-integration` based on `main`
- Create: `.session/workstreams/cslib-integration.md`

- [ ] **Step 1: Verify clean working tree on `main` before forking**

Run from the project root:

```bash
git status --short && git log --oneline -1
```

Expected: empty `git status`; HEAD points to a commit whose message
starts with `Add CSLib integration design spec` (the spec commit). If
either fails, surface to the user — do not proceed.

- [ ] **Step 2: Create worktree via EnterWorktree**

Use the `EnterWorktree` tool with branch name `cslib-integration`.
Lean's auto-naming is acceptable; the **branch** name must be
`cslib-integration` (the worktree directory name does not matter).

After this step, all subsequent commands run from the new worktree's
working directory.

- [ ] **Step 3: Verify the worktree branch and HEAD**

```bash
git branch --show-current
git log --oneline -1
```

Expected: branch is `cslib-integration`, HEAD is the spec commit.

- [ ] **Step 4: Create the workstream tracker file**

Create `.session/workstreams/cslib-integration.md` with content:

```markdown
# CSLib Integration

Active workstream tracker. Remove this file after the integration
commit is merged into `main`.

- Spec: `docs/superpowers/specs/2026-05-06-cslib-integration-design.md`
- Plan: `docs/superpowers/plans/2026-05-06-cslib-integration.md`
- Branch: `cslib-integration`

## Status

In progress. The plan is the source of truth for the active task.
```

- [ ] **Step 5: Verify the file exists**

```bash
ls -1 .session/workstreams/cslib-integration.md
```

Expected: the path is printed.

(No commit yet — the workstream tracker is not committed; it is
removed in the final task.)

---

## Task 2: Establish baseline build

**Files:** none modified.

This task records that `lake build` and `lake test` are clean before
the CSLib require is added, so a later regression can be attributed
to the integration.

- [ ] **Step 1: Populate the mathlib cache**

```bash
lake exe cache get
```

Expected: cache fetch completes (output mentions
"Decompressing N files" or "Nothing to download"). Time-box: under
one minute on a warm cache.

- [ ] **Step 2: Run baseline `lake build`**

```bash
lake build
```

Expected: completes without errors, without warnings, and without
`sorry`/`admit` messages. If any of these surface, surface the
failure to the user — do not proceed (the failure is unrelated to
CSLib).

- [ ] **Step 3: Run baseline `lake test`**

```bash
lake test 2>&1 | tee /tmp/cslib-baseline-test.log
```

Inspect `/tmp/cslib-baseline-test.log` and record the test count
(look for the summary line, e.g. "All N tests passed"). Note the
number; it is the baseline used in the §5 verification gate of the
spec.

If any test fails, surface to the user — do not proceed.

---

## Task 3: Add CSLib `[[require]]` to lakefile.toml

**Files:**

- Modify: `lakefile.toml`

- [ ] **Step 1: Read the current lakefile.toml**

```bash
grep -n require lakefile.toml
```

Identify the line block that holds the existing
`[[require]] name = "mathlib" scope = "leanprover-community"`.

- [ ] **Step 2: Append the CSLib require block**

Insert this block immediately after the existing mathlib `[[require]]`
block (preserving the surrounding blank lines):

```toml
[[require]]
name = "cslib"
scope = "leanprover"
rev = "v4.29.0-rc6"
```

- [ ] **Step 3: Verify the edit**

```bash
grep -A 3 'name = "cslib"' lakefile.toml
```

Expected: the four lines above are printed.

(No commit yet — the manifest update in Task 4 is the natural commit
boundary, but Task 8 holds the single integration commit.)

---

## Task 4: Resolve CSLib via `lake update cslib`

**Files:**

- Modify: `lake-manifest.json` (resolver-driven)

- [ ] **Step 1: Capture the pre-update manifest mathlib rev**

```bash
jq -r '.packages[] | select(.name=="mathlib") | .rev' \
  lake-manifest.json > /tmp/cslib-pre-mathlib-rev.txt
cat /tmp/cslib-pre-mathlib-rev.txt
```

Note the rev printed. It is the comparison point for Step 3.

- [ ] **Step 2: Run `lake update cslib`**

```bash
lake update cslib
```

Expected: completes without error; `lake-manifest.json` now contains
a `cslib` entry. If the command errors out, surface to the user.

- [ ] **Step 3: Inspect the manifest diff**

```bash
git diff lake-manifest.json | head -120
```

Required: a new `cslib` package entry has been added, with `inputRev =
"v4.29.0-rc6"` and a concrete `rev`. Allowed: `mathlib` rev (and any of
its transitive deps: `batteries`, `aesop`, `Qq`, `proofwidgets`,
`plausible`) may have moved, if the resolver chose to bump them for
compatibility with cslib's master pin. Forbidden: any other unrelated
package moves. If forbidden churn appears, surface to the user.

- [ ] **Step 4: If mathlib rev moved, repopulate the cache**

Compare the post-update mathlib rev against
`/tmp/cslib-pre-mathlib-rev.txt`:

```bash
NEW=$(jq -r '.packages[] | select(.name=="mathlib") | .rev' \
  lake-manifest.json)
OLD=$(cat /tmp/cslib-pre-mathlib-rev.txt)
echo "OLD=$OLD"; echo "NEW=$NEW"
```

If `NEW != OLD`, run:

```bash
lake exe cache get
```

Otherwise skip the cache repopulation.

---

## Task 5: Verify build after CSLib is added

**Files:** none modified.

- [ ] **Step 1: Run `lake build`**

```bash
lake build
```

Expected: completes without errors, without warnings. The first
build will compile CSLib from source (CSLib has no equivalent of
mathlib's cache server); time-box: up to twenty minutes.

If the build fails:

1. If the failure is in *our* code unrelated to CSLib imports, fix
   that first; the rest of the recovery assumes the failure is
   inside the CSLib import chain.
2. If the failure is a mathlib API mismatch surfaced inside CSLib,
   run `lake update mathlib`, inspect the manifest diff, and re-run
   `lake exe cache get` if mathlib moved, then re-run `lake build`.
3. If `lake update mathlib` then breaks our own code, run
   `git checkout -- lake-manifest.json`, re-run `lake update cslib`,
   and surface the conflict to the user (this is the
   "abort and surface" trigger).
4. If the build still fails inside CSLib after a forward mathlib
   bump, surface to the user.

- [ ] **Step 2: Run `lake test`**

```bash
lake test 2>&1 | tee /tmp/cslib-post-test.log
```

Compare the test-count summary to `/tmp/cslib-baseline-test.log`. The
counts must match exactly. If they differ, surface to the user — a
silent change in test discovery would be a yellow flag.

---

## Task 6: Smoke test (write, build, delete)

**Files:**

- Create then delete (transient):
  `GebLean/_CslibSmokeTest.lean`

The leading underscore ensures the file is never confused for a
deliverable module and is alphabetically grouped at the top of any
directory listing for deletion.

- [ ] **Step 1: Write the smoke test file**

Create `GebLean/_CslibSmokeTest.lean` with this exact content:

```lean
-- Transient CSLib integration smoke test. Not committed.
import Cslib.Computability.URM.Defs
import Cslib.Foundations.Data.HasFresh

open Cslib

#check (URM.Instr : Type)
#check (URM.Regs : Type)

-- Behavioural check: read register 5 of the all-zero state.
example : URM.Regs.read URM.Regs.zero 5 = 0 := by
  simp [URM.Regs.read, URM.Regs.zero]

-- Behavioural check: write 7 to register 0, then read it back.
example : URM.Regs.read (URM.Regs.write URM.Regs.zero 0 7) 0 = 7 := by
  simp [URM.Regs.read, URM.Regs.write, Function.update]

-- HasFresh is a typeclass; print its universe-polymorphic signature.
#check @HasFresh
```

- [ ] **Step 2: Build the smoke test file**

```bash
lake build GebLean._CslibSmokeTest
```

Expected: the file compiles cleanly. The two `example` proofs close
without "unsolved goals". The `#check`s elaborate without errors.

If a proof fails, the spec authorises a verification finding —
substitute one of `:= rfl`, `:= by decide`, or
`:= by simp [URM.Regs.read, URM.Regs.write]` and retry. If none
work, surface to the user with the actual error message.

If `import Cslib.Computability.URM.Defs` produces a module-system
diagnostic (CSLib uses `module`/`public import`), prepend `module`
to the smoke file's first line, retry, and document the
substitution.

- [ ] **Step 3: Delete the smoke test file**

```bash
rm GebLean/_CslibSmokeTest.lean
```

- [ ] **Step 4: Verify the tree is clean**

```bash
git status --short
```

Expected: only `lakefile.toml` and `lake-manifest.json` are listed
as modified. No new files. If the smoke file appears, the deletion
failed — re-attempt and re-verify.

- [ ] **Step 5: Re-build to confirm the deletion did not break the build**

```bash
lake build
```

Expected: clean build. (This will be a no-op if the build cache
recognises the workspace state; if it recompiles GebLean, that is
fine.)

---

## Task 7: Update CLAUDE.md

**Files:**

- Modify: `CLAUDE.md`

Three edits, all additive. The exact replacement strings are listed
verbatim; do not rewrite them.

- [ ] **Step 1: Edit Project Notes external-deps line**

Locate the line in `CLAUDE.md`:

```text
- External deps: mathlib and related tools are pinned in
  `lake-manifest.json`; see `lean-toolchain` for the toolchain.
```

Replace it with:

```text
- External deps: mathlib, CSLib, and related tools are pinned in
  `lake-manifest.json`; see `lean-toolchain` for the toolchain.
  CSLib tracks Lean toolchain RCs via tagged releases; bump the
  CSLib pin deliberately when the GebLean toolchain bumps.
```

- [ ] **Step 2: Edit search guidance**

Locate the "### Searchable" subsection of "## Lean 4 Library and
Categorical Theory Resources". Immediately under its existing
bullets (`Loogle`, `Reservoir`), insert:

```markdown
- The remote-index search tools (Loogle, `lean_leansearch`,
  `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise`)
  index mathlib + Lean core + batteries; **none currently index
  CSLib**. For CSLib content, use the CSLib API docs site
  (<https://api.cslib.io/docs/>) or grep the CSLib source under
  `.lake/packages/cslib/Cslib/`.
- When introducing a new computational construct (register
  machine, Turing machine, automaton, λ-calculus variant,
  programming-language semantics, etc.), search CSLib first, just
  as we search mathlib for general mathematical concepts.
```

- [ ] **Step 3: Add the CSLib resources subsection**

Locate "### General mathematics" (the subsection immediately under
"## Lean 4 Library and Categorical Theory Resources" that links to
the mathlib overview). Immediately *before* it, insert this new
subsection:

```markdown
### CSLib

- [Homepage](https://www.cslib.io/) and
  [whitepaper (arXiv:2602.04846)](https://arxiv.org/abs/2602.04846)
- [API docs](https://api.cslib.io/docs/)
- [Repository](https://github.com/leanprover/cslib)
- Top-level directory layout under `Cslib/` (snapshot at
  `v4.29.0-rc6`; verify against the pinned tag when bumping):
  - `Algorithms/` — algorithm/data-structure formalizations.
  - `Computability/` — `Automata/`, `Languages/`, `Machines/`,
    `URM/` (Unlimited Register Machine; namespace `Cslib.URM`).
  - `Foundations/` — `Combinatorics/`, `Control/`, `Data/`,
    `Lint/`, `Logic/`, `Semantics/` (including `LTS/` and
    `FLTS/`), `Syntax/`.
  - `Languages/` — `Boole/`, `CCS/`, `CombinatoryLogic/`,
    `LambdaCalculus/`.
  - `Logics/` — `HML/`, `LinearLogic/`. (Plural directory name.)
- Constructive discipline: importing CSLib is fine in the same
  sense that importing mathlib is fine, but the project rule that
  bans `Classical`, `noncomputable`, and `axiom` applies to any
  *transitive* axiom dependency too: a GebLean term that depends
  on a CSLib (or mathlib) lemma using `Classical.choice` will
  surface that axiom under `#print axioms`. For results that must
  remain constructive, run `#print axioms` and refactor if a
  non-pure axiom appears. Cross-reference:
  `feedback_mathlib_choice_in_functor_cat.md`.
- Reuse discipline: prefer CSLib typeclasses and abstract
  structures (e.g. `LTS`, `HasFresh`) over reaching into concrete
  instances, so internal CSLib changes do not break our code.
```

- [ ] **Step 4: Run markdownlint and fix**

```bash
markdownlint-cli2 README.md CLAUDE.md \
  .github/copilot-instructions.md \
  docs/superpowers/specs/2026-05-06-cslib-integration-design.md \
  docs/superpowers/plans/2026-05-06-cslib-integration.md
```

Expected: `0 error(s)`. If errors are reported, fix them inline and
re-run. Common fixers:

- MD013 line-length: rewrap to 80 columns.
- MD007 list-indent: align nested list bullets to two-space indent.
- MD060 table-style: ensure pipe-separator rows have spaces.

Do not silence warnings via inline disables.

---

## Task 8: Commit on the feature branch

**Files:** none modified.

The integration is one logical change: the lakefile, manifest, and
CLAUDE.md updates land in a single commit. Memory files live outside
the repo and are not part of this commit (Task 9).

- [ ] **Step 1: Confirm the staged files**

```bash
git status --short
```

Expected: exactly three modified files:

- `lakefile.toml`
- `lake-manifest.json`
- `CLAUDE.md`

If any other file is listed (smoke test, leftover scratch), stop and
restore it.

- [ ] **Step 2: Stage explicitly**

```bash
git add lakefile.toml lake-manifest.json CLAUDE.md
```

Do not use `git add -A` or `git add .`.

- [ ] **Step 3: Commit**

```bash
git commit -m "$(cat <<'EOF'
Add CSLib as a Lake dependency

Pin CSLib (leanprover/cslib) to tag v4.29.0-rc6, matching our Lean
toolchain. Update CLAUDE.md to direct future search-before-introducing
guidance to CSLib alongside mathlib, and add a CSLib resources section.
No GebLean module uses CSLib yet; migration of existing constructions
to CSLib equivalents is a per-workstream decision, not part of this
integration.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

- [ ] **Step 4: Push the branch with upstream tracking**

```bash
git push -u origin cslib-integration
```

The `-u` is required on first push to set the upstream ref.

---

## Task 9: Memory file and `MEMORY.md` update

**Files:**

- Create: `~/.claude/projects/-home-terence-git-workspaces-geb/memory/reference_cslib.md`
- Modify: `~/.claude/projects/-home-terence-git-workspaces-geb/memory/MEMORY.md`

These files are outside the repo and are not committed.

- [ ] **Step 1: Write the reference memory file**

Create `~/.claude/projects/-home-terence-git-workspaces-geb/memory/reference_cslib.md`
with this exact content:

```markdown
---
name: CSLib pin, layout, and search guidance
description: CSLib pin, docs URL, and search tool coverage caveat
type: reference
---

CSLib (the Lean Computer Science Library, `leanprover/cslib`) is a
Lake dependency of this project, pinned in `lakefile.toml`.

- **Pin**: tag `v4.29.0-rc6` — the only `v4.29.0-*` tag whose
  `lean-toolchain` matches ours. Bump deliberately when the GebLean
  toolchain bumps.
- **Docs**: <https://api.cslib.io/docs/>.
- **Repository**: <https://github.com/leanprover/cslib>.
- **Top-level layout under `Cslib/`** (snapshot at `v4.29.0-rc6`):
  - `Algorithms/` — algorithm/data-structure formalizations.
  - `Computability/` — `Automata/`, `Languages/`, `Machines/`,
    `URM/` (Unlimited Register Machine; namespace `Cslib.URM`).
  - `Foundations/` — `Combinatorics/`, `Control/`, `Data/`, `Lint/`,
    `Logic/`, `Semantics/` (including `LTS/` and `FLTS/`),
    `Syntax/`.
  - `Languages/` — `Boole/`, `CCS/`, `CombinatoryLogic/`,
    `LambdaCalculus/`.
  - `Logics/` — `HML/`, `LinearLogic/` (plural directory name).
- **Search guidance**: the remote-index search tools (Loogle,
  `lean_leansearch`, `lean_leanfinder`, `lean_state_search`,
  `lean_hammer_premise`) index mathlib + Lean core + batteries;
  **none currently index CSLib**. Use the docs site or grep
  `.lake/packages/cslib/Cslib/`.
- **Bump procedure**: CSLib release tags follow Lean toolchain RCs
  one-for-one. After a GebLean toolchain bump, update the CSLib
  `rev` in `lakefile.toml` to the matching CSLib tag, run
  `lake update cslib`, and re-run the smoke test from the
  integration spec to confirm the URM/Foundations imports still
  elaborate.
```

- [ ] **Step 2: Add a MEMORY.md entry**

Append a new top-level section to
`~/.claude/projects/-home-terence-git-workspaces-geb/memory/MEMORY.md`:

```markdown
## CSLib

- [CSLib pin, layout, and search guidance](reference_cslib.md) — pin
  `v4.29.0-rc6`, docs at <https://api.cslib.io/docs/>.
```

Place it after the existing top-level sections; do not reorder
existing content.

- [ ] **Step 3: Run markdownlint on both memory files**

```bash
MEMDIR=~/.claude/projects/-home-terence-git-workspaces-geb/memory
markdownlint-cli2 "$MEMDIR/reference_cslib.md" "$MEMDIR/MEMORY.md"
```

Expected: `0 error(s)`. Fix any errors inline and re-run.

---

## Task 10: Surface to user for review

**Files:** none modified.

- [ ] **Step 1: Compile a review hand-off summary**

Surface to the user, in chat:

- The branch name (`cslib-integration`) and the commit hash.
- The commit message (one-line).
- Confirmation that `lake build` and `lake test` are clean.
- Confirmation that `git status` is clean.
- Confirmation that the smoke test (Task 6) passed before deletion.
- Pointers to the spec and plan files.
- The exact merge command(s) the user would run after approving:

  ```bash
  git checkout main
  git merge --ff-only cslib-integration
  git push origin main
  ```

  (Or, if `main` has advanced: rebase
  `cslib-integration` onto `main`, re-run `lake build` and
  `lake test`, then merge.)

- [ ] **Step 2: Wait for user approval**

Stop here. Do not proceed to Task 11 until the user explicitly
approves merging. (User instructions during the chat may include
amendments; apply them and re-surface if needed.)

---

## Task 11: Merge into `main` and clean up

**Files:**

- Modify: `main` branch HEAD
- Delete: `.session/workstreams/cslib-integration.md`
- Delete: branch `cslib-integration`
- Delete: the worktree

This task runs only after explicit user approval at Task 10.

- [ ] **Step 1: Determine integration mode (fast-forward or rebase)**

```bash
git fetch origin main
git rev-list --count main..origin/main
```

If the count is `0`, `main` has not advanced; fast-forward is
possible. Continue with Step 2.

If the count is non-zero, `main` advanced. Rebase:

```bash
git rebase origin/main
lake build
lake test
```

Both `lake build` and `lake test` must pass after the rebase. If
either fails, abort the rebase (`git rebase --abort`) and surface
to the user — do not force-push, do not weaken the integration.

- [ ] **Step 2: Switch to `main` and merge**

Exit the worktree (or use a fresh shell on the main checkout) and
run:

```bash
git checkout main
git pull --ff-only origin main
git merge --ff-only cslib-integration
```

Expected: fast-forward succeeds. `git log --oneline -3` should now
show the integration commit at HEAD.

- [ ] **Step 3: Push `main`**

```bash
git push origin main
```

- [ ] **Step 4: Delete the feature branch (local and remote)**

```bash
git branch -d cslib-integration
git push origin --delete cslib-integration
```

The lowercase `-d` is required (not `-D`). If `-d` refuses with
"not fully merged", do not escalate to `-D`; surface to the user
to investigate.

- [ ] **Step 5: Remove the worktree**

Use the `ExitWorktree` tool with `action: "remove"`. The worktree
must have no uncommitted changes; if it does, surface and stop.

- [ ] **Step 6: Remove the workstream tracker**

```bash
rm .session/workstreams/cslib-integration.md
```

CSLib is now a standing dependency, not an active workstream.

- [ ] **Step 7: Final verification on `main`**

```bash
git status --short
lake build
lake test
```

Expected: clean tree, clean build, clean tests. The integration is
complete.

---

## Verification gate (final, mirrors spec §9)

Before marking the integration done, all of these must hold:

- `lake build` clean (no warnings, no `sorry`, no `admit`).
- `lake test` clean and the test count matches the Task 2 baseline.
- `markdownlint-cli2` clean on the project markdown set
  (`README.md`, `CLAUDE.md`, `.github/copilot-instructions.md`,
  `docs/superpowers/specs/2026-05-06-cslib-integration-design.md`,
  `docs/superpowers/plans/2026-05-06-cslib-integration.md`) and on
  the new memory file (`reference_cslib.md`) and `MEMORY.md`.
- `git status` clean (no leftover smoke files, no leftover
  workstream tracker).
- The new memory file and `MEMORY.md` entry exist and are
  consistent.
- One commit on the feature branch covering the lakefile +
  `CLAUDE.md` change (single logical change). Memory files, living
  outside the repo, are saved separately.
- The CSLib docs URL (<https://api.cslib.io/docs/>) returns HTTP
  200 (a one-time HEAD check, sanity).
