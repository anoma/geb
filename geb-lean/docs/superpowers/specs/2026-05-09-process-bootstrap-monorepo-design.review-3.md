# Adversarial review cycle 3 — 2026-05-09 process-bootstrap monorepo spec

**Reviewer**: fresh-context agent (Claude Sonnet 4.6).
**Spec read**: `2026-05-09-process-bootstrap-monorepo-design.md` only.
**Prior review logs**: not read (per review protocol).

---

## Summary

Findings: **0 blockers / 2 serious / 4 minor / 0 cosmetic-taste**.

The spec has converged substantially across prior cycles. Two serious
findings remain: a direct factual contradiction between the committed
`.markdownlint-cli2.jsonc` artefact and the spec's description of that
artefact (§ .markdownlint-cli2.jsonc), and a logical contradiction in the
`axiom_check` CI job description (called "parallel to build/test/lint" but
required to run sequentially after the build job). Four minor findings
address unresolved implementation gaps.

---

## Blockers

None.

---

## Serious

### S1 — `.markdownlint-cli2.jsonc` description contradicts committed file

**Location**: § .markdownlint-cli2.jsonc (lines ~1186–1204).

The spec states: *"The current configuration committed alongside this spec
[has] only `config` and `ignores` keys — no top-level `globs` key"* and
gives the ignores as
`["geb-lean/.lake/**", "geb-lean/.jj/**",
"geb-lean/node_modules/**", "geb-lean/.session/**"]`.

The file actually committed (introduced at `aeae31f9`) contains:

- A `"globs": ["**/*.md"]` key — contradicting "no top-level `globs` key".
- `"ignores": [".lake/**", ".jj/**", "node_modules/**"]` — lacking
  the `geb-lean/` prefix on every pattern, and lacking `.session/**`.

**Impact**: the spec's stated rationale for omitting `globs` ("prevents
unintended glob union when CLI globs are passed") is correct and the file
should not have the key. But since the file exists with a `globs` key, the
pre-push invocation in § Auxiliary scripts (`markdownlint-cli2 --config
.markdownlint-cli2.jsonc '**/*.md'`) does not use `--no-globs`; running it
from `geb-lean/` would cause `**/*.md` to be expanded twice (from the CLI
arg and from the config's `globs` field), scanning every `.md` file twice.
The CI invocation does use `--no-globs` and is therefore unaffected. The
divergence between the spec's description and the committed artefact means
the plan must include a cleanup step for `.markdownlint-cli2.jsonc` (remove
`globs`, add `geb-lean/` prefix to all ignores, add `.session/**`) that is
not currently enumerated in the spec. Without this, verification matrix
item 2 (markdownlint check quiet on refactored files) may behave
differently than specified depending on CWD.

**Required fix**: either add an explicit cleanup task for
`.markdownlint-cli2.jsonc` to the spec's enumeration of cleanup tasks, or
correct the spec's description to match the actual committed file and
explain the pre-push `--no-globs` gap.

---

### S2 — `axiom_check` CI job described as both parallel and sequential

**Location**: § CI changes (lines ~1122–1125).

The spec states: *"The new `axiom_check` job (parallel to the existing
build / test / lint jobs), running
`bash scripts/check-axioms.sh GebLean/ test/` **after the main build job
has populated `.lake/`**."*

A GitHub Actions job cannot be both parallel to the `build` job and run
after the `build` job has populated `.lake/`. If `axiom_check` requires
`.lake/` (the build artefact), it must declare `needs: [build]`, which
makes it strictly sequential to `build`. It may be parallel to other jobs
that also declare `needs: [build]`, but it is not parallel to `build`
itself.

**Impact**: an implementer following the spec literally would produce
either: (a) a job that runs in parallel with `build` and therefore fails
because `.lake/` does not yet exist when `check-axioms.sh` runs; or (b) a
job that correctly declares `needs: [build]` but contradicts the spec's
"parallel" characterisation. Verification matrix item 13 does not mention
the `needs:` dependency, leaving a gap.

**Required fix**: replace "parallel to the existing build / test / lint
jobs" with "sequential after the `build` job (declared via `needs: [build]`);
parallel to any other jobs that also depend on `build`". Update
verification matrix item 13 accordingly.

---

## Minor

### M1 — `axiom_check` report-only mechanism not specified

**Location**: § CI changes (lines ~1126–1127).

The spec says the job "does not fail the build" and "uploads the output as
a CI artefact" in report-only mode, but does not specify the mechanism
that prevents build failure. Two options exist: pass `--report-only`
(equivalently `--exit-zero-on-findings`) to the script, or add
`continue-on-error: true` to the job in the workflow YAML. The spec gives
the bare invocation `bash scripts/check-axioms.sh GebLean/ test/` without
either flag. If neither mechanism is added, the job fails CI on the first
run (because every declaration using mathlib is flagged). The
`actions/upload-artifact` step for the artefact upload is similarly
unspecified (no SHA pin mentioned, no step structure described).

**Required fix**: specify `--report-only` (or `--exit-zero-on-findings`)
in the CI invocation, and add a note that the upload step uses
`actions/upload-artifact@v4` (SHA-pinned per project policy).

---

### M2 — `defaults.run.working-directory` scope ambiguous

**Location**: § CI changes (lines ~1119–1121); verification matrix item 13.

The spec says "`defaults.run.working-directory: geb-lean` is used" for
`run:` steps "in the same workflow (e.g., the `axiom_check` job)". In
GitHub Actions, `defaults.run.working-directory` may be set at workflow
level (affecting all jobs' `run:` steps) or at individual job level
(affecting only that job's `run:` steps). The spec does not say which
scope is intended. If set at workflow level, any checkout or setup `run:`
steps that require repo root as CWD would break; if set at individual
`axiom_check` job level, those steps are unaffected. The plan needs to
know which scope to use.

**Required fix**: specify whether `defaults.run.working-directory: geb-lean`
is at workflow level or at the `axiom_check` job level.

---

### M3 — `pre-push.sh` markdownlint invocation lacks `--no-globs`

**Location**: § Auxiliary scripts (line ~1768); § .claude/rules/
ci-and-workflow.md (line ~729–731).

The `pre-push.sh` invocation is:
`markdownlint-cli2 --config .markdownlint-cli2.jsonc '**/*.md'`.
The CI invocation explicitly adds `--no-globs`. The spec's rationale for
`--no-globs` ("prevents unintended glob union when CLI globs are passed")
applies equally to the pre-push invocation. The pre-push invocation as
written gives different behaviour from CI if the config has a `globs` key
(see S1). Even if S1 is fixed (globs key removed from config), retaining
`--no-globs` in the pre-push invocation would guard against future config
edits that inadvertently re-add a `globs` key.

**Required fix**: add `--no-globs` to the `pre-push.sh` markdownlint
invocation to match CI behaviour and guard against config drift.

---

### M4 — `block-mutating-git.sh` amendment not enumerated as a named task

**Location**: § Hooks (lines ~1537–1543).

The spec correctly identifies that the current `block-mutating-git.sh`
(commit `125c6d4e`) checks `[[ -d $CLAUDE_PROJECT_DIR/.jj ]]` rather than
invoking `jj root`, and that *"the new plan's cleanup task amends this
hook script before task A27 wires it into `.claude/settings.json`."* The
amendment is described at § Hooks (use `jj root` exit code) and at §
Empirical verifications (line ~2019). However, the spec's enumeration of
in-flight commits needing cleanup (`A2`, `A4`, `A5`, `A9`, `A12`) in the
preamble identifies A9 only as "hook needs `.jj/` check amendment" without
explicitly recording that this amendment is a named task that must land
before A27. The verification matrix item 12 case (b) depends on the
amendment landing; nothing in the checklist references this dependency
explicitly.

**Required fix**: add a note to § Hooks (or to the verification matrix
item 12) stating that the `jj root` amendment must land before the hook is
wired (before task A27), so the plan author cannot reorder those steps.

---

## Cosmetic-taste

None.

---

## Cross-check notes (no finding)

The following claims were verified against primary sources and found
correct:

- `leanprover/lean-action@v1` supports `lake-package-directory` as a
  documented input (verified against `action.yml`). The spec's description
  is accurate.
- `batteries/runLinter` reads `scripts/nolints.json` by that exact
  relative path (verified against `runLinter.lean` line 133). The spec's
  listing of `geb-lean/scripts/nolints.json` is accurate.
- `jj config list --repo` is a valid flag on jj 0.41 (verified
  empirically). The `check-jj-setup.sh` anchored-match approach is correct.
- `jj root` (no arguments) walks up from CWD to `.jj/` and exits 0 when
  found (spec claim; the committed `check-jj-setup.sh` uses it correctly).
- The parent `geb/.gitignore` has `.claude` on line 7; negation patterns
  in `geb-lean/.gitignore` cannot override a parent pattern that matches a
  directory. The spec's "functionally inert" characterisation is correct.
- `jj config list --repo` output format is
  `git.private-commits = "conflicts()"` with quotes; the `check-jj-setup.sh`
  sed extraction is correct.
- `quot.sound` and `Quot.sound` both appear in Lean's axiom output as
  variants for the same quotient soundness axiom; the dual listing in the
  allowlist is intentional and consistent with the vendored script.
- GPLv3 (parent licence) is compatible with Apache 2.0 (mathlib/CSLib)
  for the combination as specified: the final work is GPLv3; Apache 2.0
  files preserve their per-file notices. The licence claim is coherent.
- `jj git push` has lease-protected push semantics by default in jj 0.41
  (confirmed in jj docs; spec claim is accurate for `integration` force-push).
- `jj 0.41` has no `tag` subcommand under `jj git` (spec claim; consistent
  with user-direct tag operations framing).
- The `fetch-tags` config option is marked experimental in jj 0.41 docs;
  the spec correctly acknowledges this and documents the fallback.
