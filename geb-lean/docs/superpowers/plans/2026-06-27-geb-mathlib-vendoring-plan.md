# geb-mathlib Vendoring Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
## Contents

- [Global Constraints](#global-constraints)
- [File Structure](#file-structure)
  - [Task 1: Vendor the `Geb` source, wire the library, apply the back-port patch](#task-1-vendor-the-geb-source-wire-the-library-apply-the-back-port-patch)
  - [Task 2: Smoke test importing the vendored module](#task-2-smoke-test-importing-the-vendored-module)
  - [Task 3: Refresh script](#task-3-refresh-script)
  - [Task 4: Back-port notes document](#task-4-back-port-notes-document)
  - [Task 5: Refresh CI workflow (parent monorepo level)](#task-5-refresh-ci-workflow-parent-monorepo-level)
  - [Task 6: Documentation reconciliation](#task-6-documentation-reconciliation)
- [Final verification](#final-verification)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let `geb-lean` build on curated `geb-mathlib` code by vendoring
its `Geb` library source, back-porting it to this repository's toolchain
with a hand-authored patch, and refreshing it on demand and on a schedule
via a continuous-integration workflow that opens a pull request on success
and an issue on failure.

**Architecture:** The `Geb/` source subtree is mirrored under
`vendor/geb-mathlib/`; a `lean_lib` maps it so imports read identically to
how they read in `geb-mathlib`; a single `git apply` patch adapts the two
consumed modules to compile on `v4.29.0-rc6`; a refresh script and a
parent-level GitHub Actions workflow reproduce and update the copy.

**Tech Stack:** Lean 4 / Lake (`v4.29.0-rc6`), `git apply`, Bash, GitHub
Actions (`peter-evans/create-pull-request`, `gh`), `markdownlint-cli2`,
`doctoc`.

## Global Constraints

- Toolchain is `leanprover/lean4:v4.29.0-rc6`; do not bump it.
- `geb-lean` keeps package-level `moreLeanArgs = ["-DwarningAsError=true"]`;
  the vendored library inherits it (no relaxation).
- The vendored library is linted, not excluded. `lake lint` names
  modules, not a lib, so the refresh lints the vendored modules computed
  from the `.lean` files on disk — generic, no hardcoded paths (see
  Task 5 for the exact command). Bare `lake lint` covers only the default
  `GebLean` target.
- `scripts/check-axioms.sh` is NOT run on `vendor/`: the vendored files'
  `module` keyword rejects the `#print axioms` the script appends.
  Vendored axiom hygiene rests instead on the build under
  `-DwarningAsError=true` (which rejects `sorry`) and on vendored content
  importing only mathlib (where `Classical.choice` is accepted) plus
  upstream curation.
- No automated code rewriting: adaptation is the hand-authored patch
  `scripts/geb-mathlib-backport.patch`; failures stop the refresh and file
  an issue.
- No LLM-drafted text in user-facing channels: the workflow's pull-request
  and issue body prose is user-authored; leave a marked placeholder for the
  user, interpolating only non-prose fields.
- Vendored upstream files preserve their Apache-2.0 notices verbatim; the
  vendored tree carries a copy of `geb-mathlib`'s `LICENSE`; each
  patch-modified file carries a change notice.
- Before any commit that touches a `.lean` file, run
  `bash scripts/pre-commit.sh` (runs `lake test` then `lake lint`).
- Every committed Markdown file with more than one `##` heading carries a
  `doctoc` table of contents and is `markdownlint-cli2`-clean.
- Pin source: `geb-mathlib` at commit
  `5aad21329e2b0f1b4dc508b0104894e3f8701804` (branch `main`).
- Execute on the existing topic branch `feat/geb-mathlib-vendoring` (the
  spec already lives there). Commits use `jj commit -m "…"`, not
  `git commit`: this repo uses `jj` in colocated mode and raw mutating
  `git` is gated. `jj` snapshots the whole working copy, so finish a task
  before committing it. `git clone`/`checkout`/`apply` against the throwaway
  temp clone or inside the refresh script are fine (they do not mutate this
  repo's history) and may prompt for approval.
- The vendored `lean_lib Geb` globs the whole namespace
  (`globs = ["Geb.*"]`) — no `geb-mathlib` subdirectory is named. Ordinary
  `lake build` / `lake test` (default `GebLean` targets) compile only the
  vendored modules `geb-lean` imports, on demand. The refresh workflow
  additionally runs `lake build Geb` and lints the vendored modules
  (computed from disk) over the whole vendored library. The back-port
  patch must keep every globbed module compiling.

---

## File Structure

- `vendor/geb-mathlib/Geb.lean` and `vendor/geb-mathlib/Geb/**` — the
  mirrored `Geb` namespace (top-level index plus 8 `.lean` files and
  `.gitkeep`s); the `Geb` index and the two `Slice` leaves are adapted by
  the patch.
- `vendor/geb-mathlib/LICENSE` — verbatim copy of `geb-mathlib`'s licence.
- `vendor/geb-mathlib/PROVENANCE.md` — source commit and patch commit.
- `scripts/geb-mathlib-backport.patch` — the back-port diff.
- `scripts/refresh-geb-mathlib.sh` — clone, wipe, copy, provenance,
  `git apply`.
- `lakefile.toml` — adds one `lean_lib` for the vendored source.
- `GebLeanTests/Vendor/GebMathlibSmoke.lean` — smoke test.
- `docs/geb-mathlib-backport-notes.md` — human notes on patch categories.
- `../.github/workflows/geb-mathlib-refresh.yml` — refresh workflow at the
  parent monorepo level (path-scoped to `geb-lean/**`).
- `docs/process.md`, `TODO.md`, `CLAUDE.md`, `docs/lean-resources.md` —
  reconciliation pointers.

---

### Task 1: Vendor the `Geb` source, wire the library, apply the back-port patch

**Files:**

- Create: `vendor/geb-mathlib/Geb/**` (copied), `vendor/geb-mathlib/LICENSE`,
  `vendor/geb-mathlib/PROVENANCE.md`, `scripts/geb-mathlib-backport.patch`
- Modify: `lakefile.toml` (add one `[[lean_lib]]`)

**Interfaces:**

- Produces: the modules `Geb.Mathlib.Data.PFunctor.Slice.Basic` and
  `Geb.Mathlib.Data.PFunctor.Slice.Functor`, importable from any `geb-lean`
  module, compiling under `v4.29.0-rc6`. `Slice.Basic` exports
  `SliceDomPFunctor`, `SlicePFunctor`, and (under `@[expose]`)
  `SliceDomPFunctor.obj`/`map`. The smoke test (Task 2) consumes these.
- Produces: `scripts/geb-mathlib-backport.patch`, consumed by Task 3.

- [ ] **Step 1: Copy the pristine `Geb/` subtree at the pinned commit**

```bash
cd /home/terence/git-workspaces/geb/geb-lean
TMP=$(mktemp -d)
git clone https://github.com/rokopt/geb-mathlib.git "$TMP/gm"
git -C "$TMP/gm" checkout 5aad21329e2b0f1b4dc508b0104894e3f8701804
mkdir -p vendor/geb-mathlib
cp "$TMP/gm/Geb.lean" vendor/geb-mathlib/Geb.lean
cp -R "$TMP/gm/Geb" vendor/geb-mathlib/Geb
cp "$TMP/gm/LICENSE" vendor/geb-mathlib/LICENSE
# Keep a pristine copy of the vendored Lean sources for the diff in Step 8.
mkdir -p "$TMP/pristine"
cp "$TMP/gm/Geb.lean" "$TMP/pristine/Geb.lean"
cp -R "$TMP/gm/Geb" "$TMP/pristine/Geb"
```

Run Steps 1-8 in a single shell so `$TMP` persists.

Expected: `vendor/geb-mathlib/Geb.lean` (the namespace index) and
`vendor/geb-mathlib/Geb/Mathlib/Data/PFunctor/Slice/{Basic,Functor}.lean`
exist, plus the `Cslib.lean`, `Internal.lean`, `Mathlib.lean`,
`Mathlib/Data.lean`, `Mathlib/Data/PFunctor.lean`, and
`Mathlib/Data/PFunctor/Slice.lean` index files. `GebMeta`/`GebTests` are
not copied.

- [ ] **Step 2: Write the provenance file**

```bash
cat > vendor/geb-mathlib/PROVENANCE.md <<'EOF'
# Vendored geb-mathlib provenance

- Source: https://github.com/rokopt/geb-mathlib
- Source commit: 5aad21329e2b0f1b4dc508b0104894e3f8701804
- Back-port patch: scripts/geb-mathlib-backport.patch (see git log for its
  commit)
- The files under `Geb/` are an unmodified mirror of the source commit
  except where `scripts/geb-mathlib-backport.patch` changes them; modified
  files carry a change notice in their header comment.
EOF
```

- [ ] **Step 3: Add the vendored `lean_lib` to `lakefile.toml`**

Append at the **end of the file**, after the trailing
`[lean_lib.leanOptions]` sub-table (which belongs to `GebLeanTests`).
Inserting the new `[[lean_lib]]` before that sub-table would re-assign
`[lean_lib.leanOptions]` to `Geb` and silently drop `GebLeanTests`'s
`linter.hashCommand` setting.

```toml
# Vendored geb-mathlib source. `globs = ["Geb.*"]` covers the whole
# vendored namespace, naming no geb-mathlib subdirectory, so the wiring
# tracks geb-mathlib's growth. The package's hard warningAsError and
# leanOptions are inherited (no per-lib override).
[[lean_lib]]
name = "Geb"
srcDir = "vendor/geb-mathlib"
globs = ["Geb.*"]
```

The lib's default root is the module `Geb`, satisfied by the vendored
`Geb.lean` (Step 1, with its `import GebMeta` removed in Step 6). The
build gate in Step 7 (`lake build Geb`) confirms the wiring.

- [ ] **Step 4: Run the build to verify it FAILS pre-patch**

Run: `lake build Geb`
Expected: FAIL. The vendored `Geb` index `import GebMeta` (not vendored)
and `Basic.lean`'s `set_option linter.checkUnivs false in` (an option
absent in `v4.29.0-rc6`) both break. This confirms adaptation is needed.

- [ ] **Step 5: Apply the back-port edits to the `Geb` index and `Slice/Basic.lean`**

In `vendor/geb-mathlib/Geb.lean`, delete the line `import GebMeta` (the
`GebMeta` library is not vendored).

In `vendor/geb-mathlib/Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`, delete
the two occurrences of the line

```lean
set_option linter.checkUnivs false in
```

but KEEP the two `@[nolint checkUnivs]` attribute lines (each just above
its structure): the `linter.checkUnivs` *option* is gone in v4.29, but
the universe linter still fires, and `@[nolint checkUnivs]` is the
v4.29-compatible suppression. So strip only the `set_option … in` lines.
Add a one-line change notice under each modified file's licence header:

```lean
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
```

- [ ] **Step 6: Apply the back-port edits to `Slice/Functor.lean`**

In `vendor/geb-mathlib/Geb/Mathlib/Data/PFunctor/Slice/Functor.lean`:

1. Delete every occurrence of the identifier `ConcreteCategory.hom`
   together with its trailing space, in the bodies of `over_hom_comp`,
   `domFunctor`, `tagTriangle`, `functor_obj`, and `functor_map`. For
   example `F.obj (ConcreteCategory.hom Y.hom)` becomes `F.obj (Y.hom)`.
2. Replace the `over_hom_comp` proof body

   ```lean
     funext z
     rw [Function.comp_apply, ← ConcreteCategory.comp_apply, Over.w g]
   ```

   with

   ```lean
     funext z
     exact congrFun (Over.w g) z
   ```

3. Change **both** occurrences of "read through `ConcreteCategory.hom`" —
   in the module docstring's Implementation-notes section and in the
   `over_hom_comp` docstring — to "read as functions", so no
   `ConcreteCategory.hom` text survives (the Final-verification grep
   checks this).
4. Add the same change-notice comment under the licence header:

   ```lean
   -- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
   ```

- [ ] **Step 7: Build and lint the whole vendored library**

```bash
lake build Geb
# Lint every vendored module — list computed from disk, no hardcoded
# paths (lake lint names modules, not a lib). `--` separates lake's args.
VMODS=$(cd vendor/geb-mathlib && find . -name '*.lean' -printf '%P\n' \
  | sed 's|\.lean$||; s|/|.|g' | tr '\n' ' ')
lake lint -- $VMODS
```

Expected: `lake build Geb` (the whole vendored library) succeeds, and
`lake lint -- $VMODS` is clean. Do NOT run `scripts/check-axioms.sh` on
`vendor/`: the vendored files' `module` keyword rejects the
`#print axioms` it appends (axiom hygiene comes from the build under
`-DwarningAsError=true`, which rejects `sorry`, plus mathlib-only imports
where `Classical.choice` is accepted). If `lake lint` flags a vendored
module, that is the build-and-issue path in miniature: add the minimal
suppression (e.g. a `@[nolint <name>]` attribute), fold it into the patch
in Step 8, and record it as a category in Task 4's notes.

- [ ] **Step 8: Generate the back-port patch as a real `git diff`**

Generate the patch in a throwaway git repo so the `a/` and `b/` paths are
symmetric and `git apply -p1` from the package root lands on
`vendor/geb-mathlib/` (this realises the spec's "generated as the
`git diff`"). Hand-rolled `diff | sed` is avoided: rewriting the paths by
substring corrupts one side.

```bash
WORK="$TMP/work"
mkdir -p "$WORK/vendor/geb-mathlib"
git -C "$WORK" init -q
cp "$TMP/pristine/Geb.lean" "$WORK/vendor/geb-mathlib/Geb.lean"   # pristine baseline
cp -R "$TMP/pristine/Geb" "$WORK/vendor/geb-mathlib/Geb"
git -C "$WORK" add -A
git -C "$WORK" -c user.email=ci@local -c user.name=ci commit -qm pristine
cp vendor/geb-mathlib/Geb.lean "$WORK/vendor/geb-mathlib/Geb.lean"  # adapted overlay
rm -rf "$WORK/vendor/geb-mathlib/Geb"
cp -R vendor/geb-mathlib/Geb "$WORK/vendor/geb-mathlib/Geb"
git -C "$WORK" diff > scripts/geb-mathlib-backport.patch
PATCHABS="$(pwd)/scripts/geb-mathlib-backport.patch"
# Verify: the patch re-applies to a fresh pristine copy and reproduces the
# adapted sources exactly.
rm -rf "$WORK/verify" && mkdir -p "$WORK/verify/vendor/geb-mathlib"
git -C "$WORK/verify" init -q   # own git repo so `git apply` lands here, not in $WORK
cp "$TMP/pristine/Geb.lean" "$WORK/verify/vendor/geb-mathlib/Geb.lean"
cp -R "$TMP/pristine/Geb" "$WORK/verify/vendor/geb-mathlib/Geb"
( cd "$WORK/verify" && git apply -p1 "$PATCHABS" )
diff -ruq "$WORK/verify/vendor/geb-mathlib" vendor/geb-mathlib \
  --exclude=LICENSE --exclude=PROVENANCE.md \
  && echo "patch re-applies and reproduces the adapted sources"
```

Expected: `scripts/geb-mathlib-backport.patch` contains only the `Geb.lean`
(GebMeta-import drop), `Slice/Basic.lean`, and `Slice/Functor.lean` hunks
(plus the change-notice lines), and the verify step prints its success
message. Task 3's refresh script applies this same patch with
`git apply -p1` from the package root.

- [ ] **Step 9: Commit**

```bash
bash scripts/pre-commit.sh
jj commit -m "feat(deps): vendor geb-mathlib Geb slice source with back-port patch"
```

Expected: `pre-commit.sh` (`lake test` then `lake lint`) passes. (`jj`
snapshots all working-copy changes; no `git add` is needed.)

---

### Task 2: Smoke test importing the vendored module

**Files:**

- Create: `GebLeanTests/Vendor/GebMathlibSmoke.lean`
- Modify: `GebLeanTests.lean` (add the import so `lake test` includes it)

**Interfaces:**

- Consumes: `Geb.Mathlib.Data.PFunctor.Slice.Basic` from Task 1
  (`SliceDomPFunctor`, with `@[expose] obj`/`map`).

- [ ] **Step 1: Write the smoke test**

Create `GebLeanTests/Vendor/GebMathlibSmoke.lean`:

```lean
import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-! Smoke test: the vendored geb-mathlib `Slice` core is importable and
its declarations are usable under `v4.29.0-rc6`. Replace with a genuine
ported import once `geb-lean` consumes curated content directly. -/

#check @SliceDomPFunctor.obj
#check @SliceDomPFunctor.map

example (dom : Type) (F : SliceDomPFunctor dom) {X : Type} (p : X → dom)
    (a : F.A) (v : F.B a → X) :
    F.Compatible p a v ↔ ∀ b, p (v b) = F.s ⟨a, b⟩ :=
  F.compatible_iff p a v
```

- [ ] **Step 2: Register it in the test target**

In `GebLeanTests.lean`, add:

```lean
import GebLeanTests.Vendor.GebMathlibSmoke
```

- [ ] **Step 3: Run the test to verify it builds and passes**

Run: `lake test`
Expected: PASS, with `GebLeanTests.Vendor.GebMathlibSmoke` compiled (this
exercises copy → patch → build → import end to end, and the classic-import
of a module-system file, which the spike confirmed builds on v4.29).

- [ ] **Step 4: Commit**

```bash
bash scripts/pre-commit.sh
jj commit -m "test(deps): smoke-test the vendored geb-mathlib import"
```

---

### Task 3: Refresh script

**Files:**

- Create: `scripts/refresh-geb-mathlib.sh`

**Interfaces:**

- Consumes: `scripts/geb-mathlib-backport.patch` from Task 1.
- Produces: a script the CI workflow (Task 5) invokes; exit code 0 on a
  clean refresh, non-zero (with a message) when the patch fails to apply.

- [ ] **Step 1: Write the refresh script**

Create `scripts/refresh-geb-mathlib.sh`:

```bash
#!/usr/bin/env bash
# Refresh vendor/geb-mathlib from upstream and re-apply the back-port patch.
# Usage: scripts/refresh-geb-mathlib.sh [<source-rev>]   (default: main)
set -euo pipefail

REPO_URL="https://github.com/rokopt/geb-mathlib.git"
SRC_REV="${1:-main}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"   # geb-lean package root
VENDOR="$ROOT/vendor/geb-mathlib"
PATCH="$ROOT/scripts/geb-mathlib-backport.patch"
[ -f "$PATCH" ] || { echo "error: back-port patch not found: $PATCH" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git clone --quiet "$REPO_URL" "$TMP/gm"
git -C "$TMP/gm" checkout --quiet "$SRC_REV"
SRC_SHA="$(git -C "$TMP/gm" rev-parse HEAD)"
PATCH_SHA="$(git -C "$ROOT" log -1 --format=%H -- "$PATCH" 2>/dev/null || echo unknown)"

# Complete overwrite of the Geb namespace (no orphaned files).
rm -f "$VENDOR/Geb.lean"; rm -rf "$VENDOR/Geb"
cp "$TMP/gm/Geb.lean" "$VENDOR/Geb.lean"
cp -R "$TMP/gm/Geb" "$VENDOR/Geb"
cp "$TMP/gm/LICENSE" "$VENDOR/LICENSE"

cat > "$VENDOR/PROVENANCE.md" <<EOF
# Vendored geb-mathlib provenance

- Source: $REPO_URL
- Source commit: $SRC_SHA
- Back-port patch: scripts/geb-mathlib-backport.patch (commit $PATCH_SHA)
- The files under \`Geb/\` are an unmodified mirror of the source commit
  except where the back-port patch changes them.
EOF

# Apply the back-port patch. `git apply` resolves patch paths from the
# repo root, not the CWD subdir, so run from the git root with
# --directory; a rejection is a hard, reportable failure (set -e).
GIT_ROOT="$(git -C "$ROOT" rev-parse --show-toplevel)"
REL="$(realpath --relative-to="$GIT_ROOT" "$ROOT")"
( cd "$GIT_ROOT" && git apply -p1 --directory="$REL" "$PATCH" )
echo "Refreshed vendor/geb-mathlib to $SRC_SHA and applied back-port patch."
```

- [ ] **Step 2: Make it executable**

```bash
chmod +x scripts/refresh-geb-mathlib.sh
```

- [ ] **Step 3: Run it at the pinned revision and verify reproduction**

```bash
scripts/refresh-geb-mathlib.sh 5aad21329e2b0f1b4dc508b0104894e3f8701804
git status --short vendor/geb-mathlib
lake build Geb
```

Expected: `git status` shows no change to the `Geb.lean` index or `Geb/`
tree (the refresh reproduces the committed adapted state; only
`PROVENANCE.md` may differ if the patch commit hash changed), and
`lake build Geb` is green. If `git apply`
reports a path or `-p` mismatch, adjust the `-p1` level / working directory
in the script until a clean refresh reproduces the committed tree; this is
the gate that finalises the apply convention left open in Task 1 Step 8.

- [ ] **Step 4: Commit**

```bash
jj commit -m "feat(deps): add geb-mathlib refresh script (clone, copy, patch)"
```

---

### Task 4: Back-port notes document

**Files:**

- Create: `docs/geb-mathlib-backport-notes.md`

- [ ] **Step 1: Write the notes document**

Create `docs/geb-mathlib-backport-notes.md`:

```markdown
# geb-mathlib back-port notes

These notes catalogue the categories of change in
`scripts/geb-mathlib-backport.patch`, which adapts the vendored
`geb-mathlib` `Geb` source (mathlib `v4.32.0-rc1`) to compile under this
repository's `v4.29.0-rc6`. When a refresh fails, check whether the new
failure matches a category below (extend the corresponding hunk) or is
genuinely new (decide the adaptation, add a category here).

## Categories

### 1. `GebMeta` not vendored

- Upstream cause: the `Geb` index imports `GebMeta`, a separate library
  not vendored (its `@[env_linter]` would mis-audit `geb-lean`).
- v4.29 symptom: `unknown module GebMeta` building the `Geb` index.
- Adaptation: delete the `import GebMeta` line from `Geb.lean`.

### 2. `linter.checkUnivs` configuration absent in v4.29

- Upstream cause: `geb-mathlib` suppresses the `linter.checkUnivs`
  universe linter on its `Slice` structures.
- v4.29 symptom: `Unknown option 'linter.checkUnivs'`.
- Adaptation: delete the `set_option linter.checkUnivs false in` lines;
  keep the `@[nolint checkUnivs]` attributes (the universe linter still
  fires on the structures, and `nolint` is the v4.29-compatible
  suppression).

### 3. `ConcreteCategory` redesign (mathlib pull request 34741)

- Upstream cause: the post-`HasForget` `ConcreteCategory` adds the
  `ConcreteCategory.hom` accessor and `ConcreteCategory.comp_apply`; in
  v4.29 an `Over` base map is already a function.
- v4.29 symptom: `Unknown identifier 'ConcreteCategory.hom'` /
  `'ConcreteCategory.comp_apply'`.
- Adaptation: drop the `ConcreteCategory.hom` wrapper (and its two
  docstring mentions); rewrite the `over_hom_comp` proof to
  `exact congrFun (Over.w g) z`.

## The hard wall

When a vendored module depends on a mathlib definition or theorem that
does not exist in `v4.29.0-rc6` (a genuinely new result, not a rename),
no patch hunk can supply it and `sorry`/`admit` are banned. Such a module
is dropped from the vendored copy via the refresh script's exclusion list
until either `geb-lean` is forward-migrated to `v4.32.0-rc1` or the
consuming exploration is deferred.

## Tooling notes

- Linting: `lake lint Geb` (a lib name) is not a valid invocation —
  `lake lint` names modules. The refresh lints the vendored modules
  computed from the `.lean` files on disk: `lake lint -- $VMODS` where
  `VMODS=$(cd vendor/geb-mathlib && find . -name '*.lean' -printf '%P\n'
  | sed 's|\.lean$||; s|/|.|g')`. This stays generic as the namespace
  grows.
- Axiom check: `scripts/check-axioms.sh` cannot scan the vendored files
  (it appends `#print axioms`, which the `module` keyword rejects), so it
  is not run on `vendor/`. Vendored axiom hygiene rests on the build
  under `-DwarningAsError=true` (rejects `sorry`) plus mathlib-only
  imports (where `Classical.choice` is accepted) and upstream curation.
- Category 2 above retains the `@[nolint checkUnivs]` attributes: only
  the `set_option linter.checkUnivs false in` lines are stripped; the
  `nolint` attributes remain the suppression the universe linter needs.
```

- [ ] **Step 2: Add a table of contents and verify markdown cleanliness**

```bash
npx doctoc --title '## Contents' docs/geb-mathlib-backport-notes.md
# If doctoc inserts the TOC above the H1, move the H1 to the top (see the
# sibling specs for the H1-then-TOC ordering).
npx markdownlint-cli2 docs/geb-mathlib-backport-notes.md
```

Expected: `markdownlint-cli2` reports `0 error(s)`.

- [ ] **Step 3: Commit**

```bash
jj commit -m "doc(deps): add geb-mathlib back-port notes"
```

---

### Task 5: Refresh CI workflow (parent monorepo level)

**Files:**

- Create: `../.github/workflows/geb-mathlib-refresh.yml` (at the parent
  `geb/` repo root, alongside `lean_action_ci.yml`)

**Interfaces:**

- Consumes: `scripts/refresh-geb-mathlib.sh` from Task 3.

- [ ] **Step 1: Write the workflow**

Create `../.github/workflows/geb-mathlib-refresh.yml`. Model it on
`geb-mathlib`'s `jj-bump.yml`. Pin every third-party action to a commit SHA
with a tag comment (reuse the SHAs already pinned in the sibling repo's
workflows). Leave the pull-request and issue body prose as a clearly
marked placeholder for the user to author (no LLM-drafted user-facing
text); interpolate only non-prose fields (source revision, run URL, step
outcome).

```yaml
name: geb-mathlib refresh

on:
  workflow_dispatch:
  schedule:
    - cron: '0 18 * * 1'   # weekly; tune as desired

concurrency:
  group: geb-mathlib-refresh
  cancel-in-progress: false

permissions:
  contents: write
  pull-requests: write
  issues: write

defaults:
  run:
    working-directory: geb-lean
    shell: bash

jobs:
  refresh:
    # origin-only: never run in the canonical upstream repository.
    if: ${{ github.repository_owner == 'rokopt' }}
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0  # v7.0.0
      - uses: leanprover/lean-action@v1  # matches geb-lean's lean_action_ci.yml
        with:
          lake-package-directory: geb-lean
          auto-config: false
      - name: Refresh and re-apply the back-port patch
        id: refresh
        run: bash scripts/refresh-geb-mathlib.sh
      - name: Build, test, and lint the whole vendored lib
        run: |
          lake build Geb
          lake test
          # Lint every vendored module (list computed from disk, generic).
          VMODS=$(cd vendor/geb-mathlib && find . -name '*.lean' -printf '%P\n' \
            | sed 's|\.lean$||; s|/|.|g' | tr '\n' ' ')
          lake lint -- $VMODS
      - name: Open or update the refresh pull request
        if: success()
        uses: peter-evans/create-pull-request@5f6978faf089d4d20b00c7766989d076bb2fc7f1  # v8.1.1
        with:
          branch: auto-refresh-geb-mathlib
          base: main
          title: 'chore(deps): refresh vendored geb-mathlib'
          # USER-AUTHORED: replace the body below with user-written prose.
          body: |
            <user-authored: describe the refresh; interpolate only
            non-prose fields such as the source revision>
      - name: File an issue on failure
        if: failure()
        env:
          GH_TOKEN: ${{ github.token }}
        run: |
          # Ensure the dedupe label exists (gh issue create errors otherwise).
          gh label create geb-mathlib-refresh --force >/dev/null 2>&1 || true
          # Dedupe: only open an issue if no open one already exists.
          existing=$(gh issue list --label geb-mathlib-refresh --state open \
                      --json number --jq 'length')
          if [ "$existing" = "0" ]; then
            gh issue create --label geb-mathlib-refresh \
              --title 'geb-mathlib refresh failed' \
              --body '<user-authored: failure triage prose; the run URL is '"$GITHUB_SERVER_URL/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID"'>'
          fi
```

- [ ] **Step 2: Validate the workflow YAML**

```bash
# If actionlint is available:
command -v actionlint >/dev/null && actionlint ../.github/workflows/geb-mathlib-refresh.yml
# Otherwise confirm it parses as YAML:
python3 -c "import yaml,sys; yaml.safe_load(open('../.github/workflows/geb-mathlib-refresh.yml'))" \
  && echo "YAML OK"
```

Expected: `actionlint` clean (or `YAML OK`). The workflow cannot be fully
exercised locally; it is reviewed, not executed, at this stage.

- [ ] **Step 3: HUMAN GATE — user authors the PR/issue body prose**

Pause for the user to replace the two `<user-authored: ...>` placeholders
with their own prose. Do not draft this text. This is required by the
no-LLM-drafted-user-facing-text rule.

- [ ] **Step 4: Commit**

```bash
# The workflow lives at the parent repo level; jj tracks the whole geb
# monorepo, so this commits it from the geb-lean working directory.
jj commit -m "ci(deps): add geb-mathlib refresh workflow"
```

---

### Task 6: Documentation reconciliation

**Files:**

- Modify: `docs/process.md` (§ "Relationship to geb-mathlib"), `TODO.md`,
  `CLAUDE.md` (§ Tooling), `docs/lean-resources.md`

- [ ] **Step 1: Reconcile `docs/process.md`**

In `docs/process.md` § "Relationship to geb-mathlib", add a paragraph
recording that `geb-lean` now vendors curated `geb-mathlib` source under
`vendor/geb-mathlib/` (a toolchain bridge, not a namespace split),
refreshed by `scripts/refresh-geb-mathlib.sh` and the parent-level
`geb-mathlib-refresh.yml` workflow, and that the earlier
"replacing the local copy with an import" framing is superseded by this
vendoring approach for as long as `geb-lean` lags `geb-mathlib`'s
toolchain. Cross-reference the spec
`docs/superpowers/specs/2026-06-27-geb-mathlib-vendoring-design.md`.

- [ ] **Step 2: Check `TODO.md`**

Scan `TODO.md` "to be done in geb-mathlib" entries; where any assumes an
external import rather than vendoring, add a one-line note pointing at the
vendoring mechanism. Make no change if none assume it.

- [ ] **Step 3: Add pointers in `CLAUDE.md` and `docs/lean-resources.md`**

In `CLAUDE.md` § Tooling, add one bullet: vendored `geb-mathlib` source
lives under `vendor/geb-mathlib/`, refreshed via
`scripts/refresh-geb-mathlib.sh`; see
`docs/geb-mathlib-backport-notes.md`. Add a parallel pointer in
`docs/lean-resources.md`.

- [ ] **Step 4: Verify markdown cleanliness and commit**

```bash
npx doctoc --update-only docs/process.md CLAUDE.md docs/lean-resources.md TODO.md
npx markdownlint-cli2 docs/process.md CLAUDE.md docs/lean-resources.md TODO.md
jj commit -m "doc(deps): reconcile docs with geb-mathlib vendoring"
```

Expected: `markdownlint-cli2` reports `0 error(s)`; `doctoc` leaves the
TOCs unchanged or updates them in place.

---

## Final verification

- [ ] Run the full pre-push checklist: `bash scripts/pre-push.sh`. Expected:
  `lake test`, `lake lint`, `doctoc --check`, `markdownlint-cli2`, and
  `scripts/check-axioms.sh` all pass.
- [ ] Confirm `lake build Geb` is green and the vendored modules lint
  clean via `lake lint -- $VMODS` (module list computed from disk).
- [ ] Confirm `git grep -n "ConcreteCategory.hom" vendor/geb-mathlib` and
  `git grep -n "import GebMeta" vendor/geb-mathlib` are both empty (the
  patch removed every occurrence).
- [ ] Confirm the smoke test built: `lake test` lists
  `GebLeanTests.Vendor.GebMathlibSmoke`.
