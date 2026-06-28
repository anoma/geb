# Axiom-hygiene linter (metaprogramming) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace `scripts/check-axioms.sh` with a Lean `collectAxioms`
env_linter (`GebLeanMeta`), invoked as build-time `#lint only` gates over
`GebLean`, `GebLeanTests`, and the vendored `Geb` tree.

**Architecture:** A `module`-system library `GebLeanMeta` registers
`@[env_linter disabled] detectNonstandardAxiom` on `Lean.collectAxioms`
with the fixed permitted set `{propext, Quot.sound, Classical.choice}`. A
second library `GebLeanAxiomChecks` holds one check file per package, each
running `#lint only detectNonstandardAxiom in <Pkg>` so a forbidden axiom
fails `lake build`. Scripts and CI build `GebLeanAxiomChecks` and run a
behavior smoke test in place of the deleted bash script.

**Tech Stack:** Lean 4 (`v4.29.0-rc6`), Lake, Batteries linter framework,
`Lean.collectAxioms`, bash, GitHub Actions, `jj` VCS.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.29.0-rc6`; mathlib/cslib
  `v4.29.0-rc6`. Use only API present at this toolchain (verified:
  `collectAxioms`, Batteries `Linter`, `@[env_linter disabled]`,
  `#lint only <linter> in <pkg>`).
- Build commands: use `lake build` / `lake test` only. Never
  `lake clean`. Never `lake env lean` to build project files (it is used
  only inside the smoke test, on throwaway fixtures that set no lakefile
  options).
- No `noncomputable` anywhere; `Classical.choice` accepted in proofs.
- No copyright/author headers in native source files (vendored files keep
  theirs).
- Every native `.lean` file has a `/-! ... -/` module docstring after
  imports; every `def` has a `/-- ... -/` docstring.
- New/edited `.md` files must pass
  `markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs <file>`
  (prose lines ≤ 80 chars; tables/code blocks exempt).
- Commit messages: `<type>(<scope>): <subject>`, imperative present, no
  capitalised first letter, no trailing period, subject ≤ 72 chars.
  Append `Co-Authored-By: Claude Opus 4.8 (1M context)
  <noreply@anthropic.com>`.
- VCS is `jj` (colocated at parent `geb/`). Raw mutating `git` is
  blocked; commit with `jj commit -m '<msg>'` / `jj describe`. Do not
  `jj git push` (user-gated). Avoid bash process substitution
  (`<(...)`); write intermediate output to a `/tmp` file.
- Generic user references in committed text ("the user" / "they").
- Work occurs on bookmark `feat/axiom-linter-metaprogramming` (already
  created off `main`; the design spec is its first commit).

---

### Task 1: The `GebLeanMeta` linter, with smoke test

**Files:**

- Create: `GebLeanMeta.lean`
- Create: `scripts/tests/test-axiom-linter.sh`
- Modify: `lakefile.toml` (add the `GebLeanMeta` lean_lib)

**Interfaces:**

- Produces: library `GebLeanMeta`; namespace `GebLeanMeta` with
  `permittedAxioms : NameSet`,
  `offendingAxioms (used : Array Name) : Array Name`, and the registered
  linter short-name `detectNonstandardAxiom` (usable in
  `#lint only detectNonstandardAxiom`).

- [ ] **Step 1: Write the failing smoke test**

Create `scripts/tests/test-axiom-linter.sh`:

```bash
#!/usr/bin/env bash
#
# scripts/tests/test-axiom-linter.sh
#
# Smoke test for the GebLeanMeta.detectNonstandardAxiom env_linter.
# Stages throwaway fixtures in a temp directory: a violating one (a
# theorem proved via a custom axiom) that the linter must reject, a
# clean one it must accept, and a Classical.choice one it must accept
# (geb-lean permits Classical.choice project-wide). Nothing
# axiom-violating is committed.
#
# The fixtures live outside the package, so the linter is run on them
# with `lake env lean`; they set no lakefile options, so the spurious
# diagnostics `lake env lean` can otherwise produce do not arise.
#
# Exit 0 if all scenarios behave; non-zero otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
failed=0

cat > "$tmp/Bad.lean" <<'EOF'
import GebLeanMeta
import Batteries.Tactic.Lint
axiom badAx : (1 : Nat) = 2
theorem usesBad : (1 : Nat) = 2 := badAx
#lint only detectNonstandardAxiom
EOF

cat > "$tmp/Good.lean" <<'EOF'
import GebLeanMeta
import Batteries.Tactic.Lint
theorem fine : True := True.intro
#lint only detectNonstandardAxiom
EOF

cat > "$tmp/Choice.lean" <<'EOF'
import GebLeanMeta
import Batteries.Tactic.Lint
theorem usesChoice : True :=
  (Classical.em True).elim (fun _ => trivial) (fun _ => trivial)
#lint only detectNonstandardAxiom
EOF

out_bad="$(lake env lean "$tmp/Bad.lean" 2>&1)"
rc_bad=$?
if [[ "$rc_bad" -eq 0 ]]; then
  echo "FAIL: linter accepted a declaration using a non-standard axiom" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi
if ! grep -qF 'badAx' <<<"$out_bad"; then
  echo "FAIL: violation output did not name the offending axiom 'badAx'" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi

out_good="$(lake env lean "$tmp/Good.lean" 2>&1)"
rc_good=$?
if [[ "$rc_good" -ne 0 ]]; then
  echo "FAIL: linter rejected clean code" >&2
  echo "  output: $out_good" >&2
  failed=1
fi

out_choice="$(lake env lean "$tmp/Choice.lean" 2>&1)"
rc_choice=$?
if [[ "$rc_choice" -ne 0 ]]; then
  echo "FAIL: linter rejected Classical.choice (permitted project-wide)" >&2
  echo "  output: $out_choice" >&2
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  echo "test-axiom-linter: FAIL" >&2
  exit 1
fi
echo "test-axiom-linter: ok"
exit 0
```

- [ ] **Step 2: Run the smoke test to verify it fails**

Run: `bash scripts/tests/test-axiom-linter.sh`
Expected: FAIL (every fixture errors — `unknown module GebLeanMeta` /
unknown identifier `detectNonstandardAxiom` — so `Bad.lean` exits
non-zero without naming `badAx`, and `Good.lean`/`Choice.lean` exit
non-zero).

- [ ] **Step 3: Write `GebLeanMeta.lean`**

Create `GebLeanMeta.lean`:

```lean
module

public meta import Lean.Util.CollectAxioms
public meta import Batteries.Tactic.Lint.Basic

/-!
# Axiom-hygiene linter

`detectNonstandardAxiom` is an `@[env_linter]` (registered `disabled`,
so it is not in the default `lake lint` set) that reports any
declaration depending on an axiom outside the permitted set
`{propext, Quot.sound, Classical.choice}`. It is built on
`Lean.collectAxioms` (core Lean), the same primitive `#print axioms`
uses. The module lives outside the `GebLean`, `GebLeanTests`, and `Geb`
namespaces so the linter does not audit its own metaprogramming code.
The `GebLeanAxiomChecks` library invokes it over each package via
`#lint only detectNonstandardAxiom in <Pkg>`.

`Classical.choice` is permitted project-wide: mathlib is classical from
its foundations, and the project-wide ban on `noncomputable` (enforced
by `lake build` under `-DwarningAsError`) is the independent guarantee
that `Classical.choice` reaches no computational content.

## References

- `Lean/Util/CollectAxioms.lean` (core Lean) — `collectAxioms`.
- `Batteries/Tactic/Lint/Basic.lean` — the `Linter` interface and the
  `@[env_linter]` attribute.
- Adapted from `geb-mathlib`'s `GebMeta.lean` (transcription); the
  per-module `Classical.choice` allowlist is dropped, since `geb-lean`
  permits it project-wide.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace GebLeanMeta

/-- Axioms permitted project-wide: `propext`, `Quot.sound`, and
`Classical.choice`. -/
def permittedAxioms : NameSet :=
  ((({} : NameSet).insert ``propext).insert ``Quot.sound).insert
    ``Classical.choice

/-- The elements of `used` not in `permittedAxioms`. -/
def offendingAxioms (used : Array Name) : Array Name :=
  used.filter (!permittedAxioms.contains ·)

/-- Flags a declaration depending on an axiom outside `permittedAxioms`.
Registered `disabled` so it runs only via explicit
`#lint only detectNonstandardAxiom`. -/
@[env_linter disabled] def detectNonstandardAxiom : Linter where
  test declName := do
    let bad := offendingAxioms (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on permitted axioms."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true

end GebLeanMeta
```

- [ ] **Step 4: Add the `GebLeanMeta` library to `lakefile.toml`**

Append after the existing `Geb` `[[lean_lib]]` block (the last one in
the file):

```toml
# Axiom-hygiene linter (metaprogramming). Module-system library, outside
# the GebLean/GebLeanTests/Geb namespaces; not audited by the gates.
[[lean_lib]]
name = "GebLeanMeta"
```

- [ ] **Step 5: Build the library**

Run: `lake build GebLeanMeta`
Expected: builds with no errors or warnings.

- [ ] **Step 6: Run the smoke test to verify it passes**

Run: `bash scripts/tests/test-axiom-linter.sh`
Expected: prints `test-axiom-linter: ok` and exits 0.

- [ ] **Step 7: Commit**

```bash
chmod +x scripts/tests/test-axiom-linter.sh
jj describe -m "feat(meta): add collectAxioms env_linter GebLeanMeta

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

### Task 2: The `GebLeanAxiomChecks` build-time gates

**Files:**

- Create: `GebLeanAxiomChecks.lean`
- Create: `GebLeanAxiomChecks/Unit.lean`
- Create: `GebLeanAxiomChecks/Native.lean`
- Create: `GebLeanAxiomChecks/Tests.lean`
- Create: `GebLeanAxiomChecks/Vendored.lean`
- Modify: `lakefile.toml` (add the `GebLeanAxiomChecks` lean_lib)

**Interfaces:**

- Consumes: `GebLeanMeta` (`offendingAxioms`, the `detectNonstandardAxiom`
  linter short-name); the `GebLean`, `GebLeanTests`, and `Geb` libraries.
- Produces: library `GebLeanAxiomChecks`. A clean
  `lake build GebLeanAxiomChecks` certifies that every declaration in
  `GebLean.*`, `GebLeanTests.*`, and `Geb.*` depends only on permitted
  axioms.

- [ ] **Step 1: Write the unit tests for the pure classifier**

Create `GebLeanAxiomChecks/Unit.lean`:

```lean
import GebLeanMeta

/-! # Unit tests for `GebLeanMeta.offendingAxioms`

Example-based checks of the pure axiom classifier behind the
`detectNonstandardAxiom` linter.
-/

open Lean GebLeanMeta

-- Permitted axioms produce no offenders.
#guard offendingAxioms #[``propext, ``Quot.sound] == #[]
#guard offendingAxioms #[``Classical.choice] == #[]
-- `sorryAx` is reported.
#guard offendingAxioms #[``sorryAx] == #[``sorryAx]
-- Mixed input: only the non-standard axiom survives.
#guard offendingAxioms #[``propext, ``Classical.choice, ``sorryAx]
  == #[``sorryAx]
```

- [ ] **Step 2: Write the three package gates**

Create `GebLeanAxiomChecks/Native.lean`:

```lean
import Batteries.Tactic.Lint
import GebLean
import GebLeanMeta

/-! # Axiom-hygiene gate for `GebLean.*` -/

#lint only detectNonstandardAxiom in GebLean
```

Create `GebLeanAxiomChecks/Tests.lean`:

```lean
import Batteries.Tactic.Lint
import GebLeanTests
import GebLeanMeta

/-! # Axiom-hygiene gate for `GebLeanTests.*` -/

#lint only detectNonstandardAxiom in GebLeanTests
```

Create `GebLeanAxiomChecks/Vendored.lean`:

```lean
import Batteries.Tactic.Lint
import Geb
import GebLeanMeta

/-! # Axiom-hygiene gate for the vendored `Geb.*` tree -/

#lint only detectNonstandardAxiom in Geb
```

- [ ] **Step 3: Write the umbrella**

Create `GebLeanAxiomChecks.lean`:

```lean
import GebLeanAxiomChecks.Unit
import GebLeanAxiomChecks.Native
import GebLeanAxiomChecks.Tests
import GebLeanAxiomChecks.Vendored

/-! # Axiom-hygiene gates

Building this library runs `GebLeanMeta.detectNonstandardAxiom` over
`GebLean.*`, `GebLeanTests.*`, and the vendored `Geb.*` tree via
`#lint only` gates. A non-standard axiom dependency fails the build.
-/
```

- [ ] **Step 4: Add the `GebLeanAxiomChecks` library to `lakefile.toml`**

Append after the `GebLeanMeta` block from Task 1:

```toml
# Axiom-hygiene gates: building this library runs the env_linter over
# GebLean, GebLeanTests, and the vendored Geb tree. Separate from
# GebLeanTests to avoid an import cycle for the GebLeanTests self-check.
# hashCommand is disabled so the `#lint`/`#guard` commands are allowed.
[[lean_lib]]
name = "GebLeanAxiomChecks"
roots = ["GebLeanAxiomChecks"]

[lean_lib.leanOptions]
linter.hashCommand = false
```

- [ ] **Step 5: Build the gates on the current tree**

Run: `lake build GebLeanAxiomChecks`
Expected: builds with no errors. (This transitively builds `GebLean`,
`GebLeanTests`, `Geb`, and `GebLeanMeta`, then runs the three gates. A
clean build means no current declaration in any of the three packages
uses a forbidden axiom.)

- [ ] **Step 6: Verify the gate actually rejects a bad axiom**

Temporarily append to `GebLeanTests/Basic.lean`:

```lean
axiom scratchBadAxiom : (0 : Nat) = 1
theorem scratchUsesBad : (0 : Nat) = 1 := scratchBadAxiom
```

Run: `lake build GebLeanAxiomChecks`
Expected: FAIL — the `Tests` gate reports
`scratchUsesBad depends on non-standard axiom(s): [scratchBadAxiom]`.

Then revert the two lines from `GebLeanTests/Basic.lean` and rebuild:

Run: `lake build GebLeanAxiomChecks`
Expected: PASS (clean).

- [ ] **Step 7: Commit**

```bash
jj describe -m "feat(meta): add GebLeanAxiomChecks build-time gates

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

### Task 3: Wire scripts and delete the bash check

**Files:**

- Modify: `scripts/pre-push.sh` (replace Step 6)
- Modify: `scripts/pre-commit.sh` (add gate-build step)
- Delete: `scripts/check-axioms.sh`

**Interfaces:**

- Consumes: `lake build GebLeanAxiomChecks` (Task 2),
  `scripts/tests/test-axiom-linter.sh` (Task 1).

- [ ] **Step 1: Replace Step 6 in `scripts/pre-push.sh`**

Replace this block:

```bash
# Step 6: axiom check. A non-allowlisted axiom dependency fails the
# push.
step "Step 6: scripts/check-axioms.sh"
bash scripts/check-axioms.sh GebLean/ GebLeanTests/
```

with:

```bash
# Step 6: axiom hygiene. Building GebLeanAxiomChecks runs the
# GebLeanMeta.detectNonstandardAxiom env_linter over GebLean,
# GebLeanTests, and the vendored Geb tree; a non-standard axiom fails
# the build. The smoke test guards the linter's own behaviour.
step "Step 6a: lake build GebLeanAxiomChecks"
lake build GebLeanAxiomChecks
step "Step 6b: scripts/tests/test-axiom-linter.sh"
bash scripts/tests/test-axiom-linter.sh
```

- [ ] **Step 2: Add a gate-build step to `scripts/pre-commit.sh`**

After the `lake lint` block (the current Step 2), append:

```bash
# Step 3: axiom-hygiene gates. Building GebLeanAxiomChecks runs the
# GebLeanMeta.detectNonstandardAxiom env_linter over GebLean,
# GebLeanTests, and the vendored Geb tree; a non-standard axiom fails
# the build.
step "Step 3: lake build GebLeanAxiomChecks"
lake build GebLeanAxiomChecks
```

Update the closing line `printf '\npre-commit: Lean triad passed.\n'` to:

```bash
printf '\npre-commit: Lean checks passed.\n'
```

Also fix the stale `check-axioms.sh` reference in the `pre-commit.sh`
header comment. Replace:

```bash
# `scripts/pre-push.sh` superset (markdownlint, doctoc,
# check-axioms.sh, user-driven gates) is still mandatory before push.
```

with:

```bash
# `scripts/pre-push.sh` superset (markdownlint, doctoc, axiom-gate
# build, smoke test, user-driven gates) is still mandatory before push.
```

- [ ] **Step 3: Delete the bash script**

```bash
jj file untrack scripts/check-axioms.sh 2>/dev/null || rm -f scripts/check-axioms.sh
```

(If `jj file untrack` is unavailable, `rm -f scripts/check-axioms.sh`;
`jj` snapshots the deletion.)

- [ ] **Step 4: Confirm no script references remain**

Run:
`grep -rn "check-axioms" scripts/ 2>/dev/null || echo "no references"`
Expected: `no references`.

- [ ] **Step 5: Run the checks**

Run: `bash scripts/pre-commit.sh`
Expected: ends with `pre-commit: Lean checks passed.`

Run: `bash scripts/pre-push.sh`
Expected: reaches `Step 6b` cleanly and prints
`test-axiom-linter: ok`, then the Step 7 user-gate reminders and
`pre-push: all mechanical steps passed.`

- [ ] **Step 6: Commit**

```bash
jj describe -m "refactor(meta): drive axiom check from GebLeanAxiomChecks

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

### Task 4: Wire the parent CI workflow

**Files:**

- Modify: `../.github/workflows/lean_action_ci.yml` (path from
  `geb-lean/`: `/home/terence/git-workspaces/geb/.github/workflows/lean_action_ci.yml`)

**Interfaces:**

- Consumes: `lake build GebLeanAxiomChecks`,
  `scripts/tests/test-axiom-linter.sh`.

- [ ] **Step 1: Replace the axiom-check step and artifact upload**

In the `build` job, replace this block:

```yaml
      - name: Run axiom check
        run: |
          bash scripts/check-axioms.sh \
            GebLean/ GebLeanTests/ \
            | tee axiom-check-report.txt
      - name: Upload axiom-check report
        uses: actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a
        with:
          name: axiom-check-report
          path: geb-lean/axiom-check-report.txt
          if-no-files-found: error
```

with:

```yaml
      - name: Build axiom-hygiene gates
        run: lake build GebLeanAxiomChecks
      - name: Axiom-linter smoke test
        run: bash scripts/tests/test-axiom-linter.sh
```

- [ ] **Step 2: Validate the YAML**

Run (writes to a temp file; no process substitution):

```bash
python3 -c "import yaml,sys; yaml.safe_load(open('../.github/workflows/lean_action_ci.yml')); print('yaml ok')"
```

Expected: `yaml ok`. Confirm by eye that no `check-axioms`,
`axiom-check-report`, or `upload-artifact` lines remain in the file.

- [ ] **Step 3: Commit**

```bash
jj describe -m "ci: build axiom gates instead of running check-axioms.sh

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

### Task 5: Update living documentation

**Files:**

- Modify: `CLAUDE.md`
- Modify: `.claude/rules/lean-coding.md`
- Modify: `.claude/rules/ci-and-workflow.md`
- Modify: `docs/geb-mathlib-backport-notes.md`
- Modify: `docs/lean-resources.md`
- Modify: `TODO.md`

Historical artifacts under `docs/superpowers/specs/`,
`docs/superpowers/plans/`, `docs/plans/`, and `docs/research/` are not
edited.

- [ ] **Step 1: `CLAUDE.md` — Constructive-only section**

Replace:

```markdown
- `scripts/check-axioms.sh` (vendored from `lean4-skills`) is part
  of the pre-push checklist and runs in CI. It rejects `sorryAx`
  and any non-standard axiom; `propext`, `Quot.sound`, and
  `Classical.choice` are accepted. The lighter pre-commit
  checklist (`scripts/pre-commit.sh`) does not run the axiom
  check; see Rules above.
```

with:

```markdown
- Axiom hygiene is enforced by `GebLeanMeta.detectNonstandardAxiom`,
  an `@[env_linter]` built on `Lean.collectAxioms`. It rejects
  `sorryAx` and any non-standard axiom; `propext`, `Quot.sound`, and
  `Classical.choice` are accepted. The `GebLeanAxiomChecks` library
  invokes it over `GebLean`, `GebLeanTests`, and the vendored `Geb`
  tree via `#lint only` gates; building that library
  (`lake build GebLeanAxiomChecks`) is part of the pre-commit and
  pre-push checklists and runs in CI.
```

- [ ] **Step 2: `CLAUDE.md` — Pre-commit Lean triad rule**

In the `**Pre-commit Lean triad.**` bullet, apply two replacements.

Replace:

```markdown
  `.lean` file, run `bash scripts/pre-commit.sh` (`lake test` and
  `lake lint`; `lake build` is currently subsumed by `lake test`'s
```

with:

```markdown
  `.lean` file, run `bash scripts/pre-commit.sh` (`lake test`,
  `lake lint`, and `lake build GebLeanAxiomChecks`; `lake build` is
  otherwise subsumed by `lake test`'s
```

Replace:

```markdown
  `scripts/pre-push.sh` remains the full superset (markdownlint,
  doctoc, axiom check, user-driven gates) and is mandatory before
```

with:

```markdown
  `scripts/pre-push.sh` remains the full superset (markdownlint,
  doctoc, axiom-gate build, smoke test, user-driven gates) and is
  mandatory before
```

- [ ] **Step 3: `CLAUDE.md` — Tooling Linters line**

Replace:

```markdown
- Linters: `markdownlint-cli2`, `lake lint`,
  `scripts/check-axioms.sh`.
```

with:

```markdown
- Linters: `markdownlint-cli2`, `lake lint`,
  `GebLeanMeta.detectNonstandardAxiom` (via
  `lake build GebLeanAxiomChecks`).
```

- [ ] **Step 4: `.claude/rules/lean-coding.md` — axiom-audit subsection**

Replace:

```markdown
#### Axiom audit and the `AXIOM_ALLOW` mechanism

`scripts/check-axioms.sh` accepts `propext`, `Quot.sound`, and
`Classical.choice`; it rejects `sorryAx` and any other
non-standard axiom. Because `Classical.choice` is accepted
project-wide, it no longer needs per-declaration annotation. The
`-- AXIOM_ALLOW: <axiom> (rationale)` mechanism (a comment
immediately above a declaration or inside its `/-- … -/`
docstring, which suppresses that axiom from the failure output)
remains available should the project ever need to allow a
*different* non-standard axiom on an individual basis. Any
`-- AXIOM_ALLOW: Classical.choice` comments predating this policy
(e.g. in `KSimURMSimulator.lean`) are now redundant and may be
removed when those files are next touched.
```

with:

```markdown
#### Axiom audit

`GebLeanMeta.detectNonstandardAxiom` (an `@[env_linter]` built on
`Lean.collectAxioms`) accepts `propext`, `Quot.sound`, and
`Classical.choice`; it rejects `sorryAx` and every other non-standard
axiom. It is invoked over `GebLean`, `GebLeanTests`, and the vendored
`Geb` tree by the `GebLeanAxiomChecks` library's
`#lint only detectNonstandardAxiom in <Pkg>` gates, so a forbidden
axiom fails `lake build GebLeanAxiomChecks`. The permitted set is
fixed in `GebLeanMeta.lean`; permitting any further non-standard axiom
means editing that set there (there is no per-declaration comment
escape hatch).
```

- [ ] **Step 5: `.claude/rules/lean-coding.md` — Lake/build workflow**

In the `## Lake / build workflow` section, apply two replacements.

Replace:

```markdown
  (which subsumes `lake build` against current lakefile targets)
  followed by `lake lint`. Catching `lake lint` regressions at
```

with:

```markdown
  (which subsumes `lake build` against current lakefile targets)
  followed by `lake lint`, then `lake build GebLeanAxiomChecks`.
  Catching `lake lint` regressions at
```

Replace:

```markdown
  Lean triad, plus `doctoc --check`, `markdownlint-cli2`,
  `scripts/check-axioms.sh`, and user-driven-gate reminders) and
  is mandatory before every push, regardless of which file types
  changed.
```

with:

```markdown
  Lean triad, plus `doctoc --check`, `markdownlint-cli2`,
  `lake build GebLeanAxiomChecks`,
  `scripts/tests/test-axiom-linter.sh`, and user-driven-gate
  reminders) and is mandatory before every push, regardless of
  which file types changed.
```

- [ ] **Step 6: `.claude/rules/ci-and-workflow.md` — Pre-commit checklist**

Replace:

```markdown
1. `lake test` succeeds (builds `GebLean` and `GebLeanTests` via
   the test driver's dependency graph; explicit `lake build` is
   redundant against current lakefile targets — see § Pre-push
   checklist below).
2. `lake lint` quiet.
```

with:

```markdown
1. `lake test` succeeds (builds `GebLean` and `GebLeanTests` via
   the test driver's dependency graph; explicit `lake build` is
   redundant against current lakefile targets — see § Pre-push
   checklist below).
2. `lake lint` quiet.
3. `lake build GebLeanAxiomChecks` succeeds (runs the
   `GebLeanMeta.detectNonstandardAxiom` env_linter over `GebLean`,
   `GebLeanTests`, and the vendored `Geb` tree).
```

- [ ] **Step 7: `.claude/rules/ci-and-workflow.md` — Pre-push checklist**

Replace:

```markdown
6. `bash scripts/check-axioms.sh GebLean/ GebLeanTests/` quiet.
   A non-allowlisted axiom dependency fails the push; CI repeats
   the check via the `axiom_check` job in
   `geb/.github/workflows/lean_action_ci.yml`.
```

with:

```markdown
6. `lake build GebLeanAxiomChecks` succeeds, then
   `bash scripts/tests/test-axiom-linter.sh` passes. The
   `GebLeanAxiomChecks` library runs the
   `GebLeanMeta.detectNonstandardAxiom` env_linter over `GebLean`,
   `GebLeanTests`, and the vendored `Geb` tree via `#lint only`
   gates; a non-standard axiom dependency fails the build. CI
   repeats the build and smoke test in
   `geb/.github/workflows/lean_action_ci.yml`.
```

- [ ] **Step 8: `docs/geb-mathlib-backport-notes.md` — axiom-check note**

Replace:

```markdown
- Axiom check: `scripts/check-axioms.sh` cannot scan the vendored files
  (it appends `#print axioms`, which the `module` keyword rejects), so it
  is not run on `vendor/`. Vendored axiom hygiene rests on the build
  under `-DwarningAsError=true` (rejects `sorry`) plus mathlib-only
  imports (where `Classical.choice` is accepted) and upstream curation.
```

with:

```markdown
- Axiom check: the `GebLeanMeta.detectNonstandardAxiom` env_linter
  scans the vendored `Geb.*` tree via the
  `GebLeanAxiomChecks/Vendored.lean` gate
  (`#lint only detectNonstandardAxiom in Geb`), so a patch-introduced
  non-standard axiom fails `lake build GebLeanAxiomChecks`. This
  complements the build under `-DwarningAsError=true` (which rejects
  `sorry`). `propext`, `Quot.sound`, and `Classical.choice` are
  accepted; everything else is fatal.
```

- [ ] **Step 9: `docs/lean-resources.md` — constructivity advice**

Replace:

```markdown
  surface that axiom under `#print axioms`. For results that must
  remain constructive, run `#print axioms` and refactor if a
  non-pure axiom appears.
```

with:

```markdown
  surface that axiom under `#print axioms`. For ad-hoc checks, run
  `#print axioms` and refactor if a non-pure axiom appears; the
  `GebLeanMeta.detectNonstandardAxiom` env_linter (via
  `lake build GebLeanAxiomChecks`) is the systematic gate.
```

- [ ] **Step 10: `TODO.md` — drop AXIOM_ALLOW references**

Apply two replacements.

Replace:

```markdown
on `main`; T5 on `feat/t5-equivalence` pending PR. Axiom
  envelope is `[propext, Quot.sound]` after AXIOM_ALLOW
  suppression of the standing `Fin.lastCases_castSucc`
  exception.
```

with:

```markdown
on `main`; T5 on `feat/t5-equivalence` pending PR. Axiom
  envelope is `[propext, Quot.sound, Classical.choice]`
  (`Fin.lastCases_castSucc` contributes `Classical.choice`,
  accepted project-wide).
```

Replace:

```markdown
  pending PR. The whole sub-project's axiom envelope is
  `[propext, Quot.sound]` after AXIOM_ALLOW suppression.
```

with:

```markdown
  pending PR. The whole sub-project's axiom envelope is
  `[propext, Quot.sound, Classical.choice]`.
```

- [ ] **Step 11: Markdownlint the edited docs**

Run:

```bash
markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs \
  CLAUDE.md .claude/rules/lean-coding.md \
  .claude/rules/ci-and-workflow.md docs/geb-mathlib-backport-notes.md \
  docs/lean-resources.md TODO.md
```

Expected: `Summary: 0 error(s)`. Fix any line-length (MD013, 80) or
other findings by re-wrapping prose.

- [ ] **Step 12: Confirm no stale references remain**

Run:

```bash
grep -rnE "check-axioms|AXIOM_ALLOW" CLAUDE.md .claude/rules/ docs/ TODO.md README.md \
  | grep -v "docs/superpowers/" | grep -v "docs/plans/" | grep -v "docs/research/" \
  || echo "no live references"
```

Expected: `no live references`.

- [ ] **Step 13: Commit**

```bash
jj describe -m "doc(meta): document the collectAxioms linter; drop AXIOM_ALLOW

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

### Task 6: Remove stale `AXIOM_ALLOW` source comments

Dropping the `AXIOM_ALLOW` mechanism leaves inert
`-- AXIOM_ALLOW: Classical.choice` annotation comments in five source
files that now reference a removed mechanism. They are pure comments
(no effect on the new linter, which permits `Classical.choice`
project-wide regardless), so removing them is safe and completes the
mechanism's removal.

**Files:**

- Modify: `GebLean/Utilities/KSimURMSimulator.lean` (5 blocks)
- Modify: `GebLean/LawvereERKSim/ErToK.lean` (2 blocks)
- Modify: `GebLean/LawvereERKSim/RuntimeBound.lean` (1 block)
- Modify: `GebLean/LawvereERKSim/Equivalence.lean` (7 blocks)
- Modify: `GebLean/LawvereERKSim/ErToKFunctor.lean` (8 blocks)

- [ ] **Step 1: Locate every annotation block**

Run:
`grep -rn "AXIOM_ALLOW" GebLean/ --include="*.lean"`
Expected: the 23 occurrences across the five files above.

- [ ] **Step 2: Delete each annotation block**

Each annotation is a contiguous run of comment lines: a first line
matching `-- AXIOM_ALLOW:` followed by zero or more `--` continuation
lines (the run ends at the first non-`--` line or blank line). Delete
the whole run in each of the five files. Example — in
`GebLean/LawvereERKSim/ErToK.lean` delete:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via mathlib's
-- Fin.lastCases_castSucc through `KSimURMSimulator.simulate_level`;
-- see .claude/rules/lean-coding.md § Accepted exceptions).
```

Leave the surrounding blank line and the declaration that followed the
annotation untouched. Do not remove any comment that does not begin
with `-- AXIOM_ALLOW:`.

- [ ] **Step 3: Confirm removal**

Run:
`grep -rn "AXIOM_ALLOW" GebLean/ --include="*.lean" || echo "none"`
Expected: `none`.

- [ ] **Step 4: Rebuild to confirm the edits are comment-only**

Run: `lake build GebLeanAxiomChecks`
Expected: PASS (the five files still compile; the gates still pass).

- [ ] **Step 5: Commit**

```bash
jj describe -m "refactor(meta): drop inert AXIOM_ALLOW source comments

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

### Task 7: Final verification

**Files:** none (verification only).

- [ ] **Step 1: Full pre-push run**

Run: `bash scripts/pre-push.sh`
Expected: all mechanical steps pass, including `Step 6a`
(`lake build GebLeanAxiomChecks`) and `Step 6b`
(`test-axiom-linter: ok`); ends with
`pre-push: all mechanical steps passed.`

- [ ] **Step 2: Confirm the linter binds the vendored tree**

Temporarily append to a vendored file under `vendor/geb-mathlib/Geb/`
(for example the first `Geb/Internal/...lean` module) a scratch
declaration using a custom axiom, matching that file's module syntax:

```lean
axiom scratchVendorAx : (0 : Nat) = 1
theorem scratchVendorUses : (0 : Nat) = 1 := scratchVendorAx
```

Run: `lake build GebLeanAxiomChecks`
Expected: FAIL — the `Vendored` gate names `scratchVendorAx`. Then
revert the scratch lines and rebuild: PASS.

(This confirms the vendored-coverage goal that motivated the design.)

- [ ] **Step 3: Confirm no `sorry`/`admit` and clean tree**

Run: `jj diff --stat`
Expected: the diff contains `GebLeanMeta.lean`,
`GebLeanAxiomChecks*.lean`, `scripts/tests/test-axiom-linter.sh`,
`lakefile.toml`, the two scripts, the CI workflow, the docs, and the
deletion of `scripts/check-axioms.sh`; no scratch axioms remain.

- [ ] **Step 4: Advance the bookmark**

```bash
jj bookmark set feat/axiom-linter-metaprogramming -r @-
```

(Points the bookmark at the last committed change; `@` is the empty
working copy on top.)

---

## Self-Review

**Spec coverage:**

- Linter on `collectAxioms`, fixed permitted set, `disabled` → Task 1.
- Build-time gates over `GebLean`/`GebLeanTests`/`Geb` → Task 2.
- Vendored-tree coverage (the motivating gap) → Task 2 (Vendored gate),
  Task 7 Step 2 (verification).
- Delete `scripts/check-axioms.sh`; no `lintDriverArgs`/`lake lint`
  change → Task 3 (and absence of any such step elsewhere).
- Smoke test with inverted `Classical.choice` fixture → Task 1.
- Scripts (pre-commit build-time enforcement, pre-push) → Task 3.
- Parent CI step + artifact-upload removal → Task 4.
- Living-doc updates; drop `AXIOM_ALLOW`; historical files untouched →
  Task 5. (`docs/process.md`/`README.md` carry no axiom-check or
  `AXIOM_ALLOW` text, so they are intentionally not edited.)
- Remove inert `AXIOM_ALLOW` source comments in five `GebLean/` files →
  Task 6.
- Final verification (full pre-push, vendored-tree inject/revert, clean
  tree, bookmark advance) → Task 7.

**Placeholder scan:** No `TBD`/`TODO`/"handle edge cases"; every code and
doc step shows exact content or an exact old→new replacement.

**Type consistency:** `permittedAxioms : NameSet`,
`offendingAxioms (used : Array Name) : Array Name`, and the linter
short-name `detectNonstandardAxiom` are used identically in Tasks 1, 2,
and the docs. `lake build GebLeanAxiomChecks` is the single invocation
form across scripts, CI, and docs.
