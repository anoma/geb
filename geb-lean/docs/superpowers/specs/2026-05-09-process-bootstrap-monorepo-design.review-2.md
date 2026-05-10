# Adversarial review cycle 2 — 2026-05-09 process-bootstrap monorepo spec

**Reviewer**: fresh-context Agent.
**Spec under review**:
`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`.
**Convergence threshold**: zero blocker / serious / minor findings
(cosmetic-taste excluded).

## Summary

Two blockers, two serious findings, and five minor findings. The spec is
well-structured and thorough, but three categories of defect emerged: (1)
a markdownlint configuration interaction causes the CI markdown-lint
workflow and verification matrix item 2 to scan far more files than
intended and fail against existing `.session/` and `docs/` markdown
files; (2) an internal contradiction about which CI workflows live at the
parent level; (3) the existing `block-mutating-git.sh` hook uses a
`$CLAUDE_PROJECT_DIR/.jj` directory check rather than the `jj root`
invocation the spec describes, causing `jj git` commands to be blocked
when `.jj/` is at the parent rather than at `geb-lean/`; and (4) the
`defaults.run.working-directory` CI key likely does not apply to `uses:`
action steps, leaving the promoted `lean_action_ci.yml` running `lake`
from the parent root.

## Blocker findings

### B1: Markdown-lint CI and verification item 2 will fail on existing files

**Location**: § CI changes (approx. lines 1139–1153);
§ .markdownlint-cli2.jsonc (approx. lines 1155–1166);
§ Verification — Milestone A checklist item 2.

The `.markdownlint-cli2.jsonc` config contains a top-level
`"globs": ["**/*.md"]` field. Per the `markdownlint-cli2` documentation
(and confirmed empirically), command-line glob arguments and the config
file's `globs` field are **additive** — command-line globs do not suppress
the config file's globs. Consequently, the parent-level CI invocation

```yaml
globs: 'geb-lean/**/*.md'
config: 'geb-lean/.markdownlint-cli2.jsonc'
```

produces an effective scan of
`geb-lean/**/*.md ∪ **/*.md = **/*.md` from the `geb/` root working
directory, scanning the entire monorepo. Additionally, the config's
`"ignores": [".lake/**", ".jj/**", "node_modules/**"]` are relative to
the working directory (`geb/`), so they do not exclude
`geb-lean/.lake/**`. The same issue affects verification matrix item 2
(`markdownlint-cli2 --config geb-lean/.markdownlint-cli2.jsonc
'geb-lean/**/*.md' is quiet`): empirical testing shows 1582 lint errors
from files in `geb-lean/.session/`, `geb-lean/docs/`, and
`geb-lean/.lake/` when run from `geb/`. Verification item 2 cannot pass
during Milestone A (when `.session/` still exists) without resolving
this.

The root cause is twofold: the config's `globs` field should not contain
`**/*.md` (it should be absent, reserved for standalone invocations from
`geb-lean/`), and the ignores should include `geb-lean/.lake/**` and
`geb-lean/.session/**` for the parent-level scan. The parent-level CI
workflow should pass `--no-globs` (which suppresses the config's
`globs` field when CLI globs are given) or the config's `globs` field
should be removed. Additionally, the `.markdownlint-cli2.jsonc` should
add `.session/**` to the `ignores` (the directory exists during Milestone
A), and the existing `docs/*.md` lint errors (MD060, MD013 violations in
`bicategorical-correspondence.md`, `categories-as-copresheaves.md`, and
others) must either be fixed or the scope of verification item 2 must be
narrowed to new-artefact files only. The spec says the refactor is
infrastructure-only and does not rewrite existing docs; if verification
item 2 requires all existing `.md` files to be clean, that is an
unstated scope expansion.

**Recommended fix**: remove `"globs"` from `.markdownlint-cli2.jsonc`;
add `.session/**` and `geb-lean/.lake/**` to the config's `"ignores"`;
specify `--no-globs` in the parent-level CI workflow invocation; narrow
verification item 2 to "new refactor artefacts only" or explicitly scope
the existing-file lint sweep as a separate sub-task.

### B2: CLAUDE.md tooling section contradicts file layout on update.yml placement

**Location**: § CLAUDE.md content, item 12, Tooling sub-bullet
(approx. lines 473–474).

The spec states: "CI (`lean_action_ci.yml`, `update.yml`,
`markdown-lint.yml` — the last two at the parent level)". "The last two"
refers to `update.yml` and `markdown-lint.yml`. However, § New file and
directory layout explicitly marks `update.yml` as "(existing; inert;
unchanged)" under `geb-lean/.github/workflows/`, and § CI changes states
"`update.yml` and `create-release.yml` remain inert at
`geb-lean/.github/workflows/`". Only `lean_action_ci.yml` and
`markdown-lint.yml` move to the parent level; `update.yml` stays at
`geb-lean/`. The parenthetical is factually wrong.

**Recommended fix**: change the parenthetical to
"`lean_action_ci.yml` and `markdown-lint.yml` at the parent level;
`update.yml` inert at `geb-lean/.github/workflows/`".

## Serious findings

### S1: block-mutating-git.sh uses .jj dir check, not jj root, when .jj/ is at parent

**Location**: § Hooks (approx. lines 1481–1490); Verification item 12 case (b).

The spec describes `block-mutating-git.sh` as using "`jj root` (run with
no arguments; walks up from CWD to find `.jj/`; portable across whether
`.jj/` is at the parent or at `geb-lean/`)" to decide whether to strip
`jj git X` invocations. The existing code does not do this: it checks
`[[ -d "$project_dir/.jj" ]]` where `project_dir = ${CLAUDE_PROJECT_DIR:-$PWD}`.
When `CLAUDE_PROJECT_DIR` is `geb-lean/` and `.jj/` is at the parent
`geb/` (the state after `jj git init --colocate` at the parent), the
directory check finds no `.jj/` and the jj-stripping path is skipped. A
subsequent `jj git push --remote origin -b feat/x` is then tokenised
by the hook: the token `git` is found at position 1, `push` becomes the
subcommand, and the hook blocks it with exit 2 — failing verification
item 12 case (b) and blocking all legitimate jj git operations in Claude
sessions.

The spec knows about this discrepancy (the review instructions name A9
as "needs `.jj/` check amendment") but describes the hook in the
present tense as already using `jj root`. An implementor reading the
spec in isolation would not know the existing code needs changing.

**Recommended fix**: the spec should explicitly state that the existing
hook's `.jj/` directory check must be replaced with a `jj root`
invocation as part of the cleanup task, or add a note that the described
behaviour is the target state and the plan must amend the hook.

### S2: defaults.run.working-directory does not apply to uses: steps in GitHub Actions

**Location**: § CI changes (approx. lines 1101–1108); Verification
item 13.

The spec says the promoted `lean_action_ci.yml` gains
`defaults.run.working-directory: geb-lean`. In GitHub Actions,
`defaults.run.working-directory` applies to `run:` shell steps but does
**not** apply to `uses:` steps (composite or JavaScript actions). The
existing `lean_action_ci.yml` uses `uses: leanprover/lean-action@v1`
with a `script:` input. When the action internally runs `lake build` and
`lake test` via that script, it executes in `$GITHUB_WORKSPACE` (the
checkout root, `geb/`), not in `geb-lean/`. The `lakefile.toml` is in
`geb-lean/`, so `lake build` at `geb/` would fail with "no such file
or directory" or silently build nothing. Verification item 13 may pass
(the file exists and has the right path filter) while the actual Lean
build silently fails or produces garbage output.

The spec should verify whether `leanprover/lean-action@v1` accepts a
`working-directory:` input (some actions do), or restructure the
promoted workflow to use an explicit `cd geb-lean &&` prefix in a
`run:` step, or add `env: GITHUB_WORKSPACE: ${{ github.workspace }}/geb-lean`.

**Recommended fix**: before specifying `defaults.run.working-directory`,
confirm that `leanprover/lean-action@v1` respects it or accepts a
`working-directory:` input. If not, replace `uses: leanprover/lean-action`
with an equivalent `run:` step that changes into `geb-lean/` explicitly.
Document this in the spec so the plan author implements it correctly.

## Minor findings

### M1: TODO.md template contains a 96-character prose line that fails MD013

**Location**: § TODO.md format, code block (approx. line 893).

The template code block in the spec contains:

```text
new repository, where the curated context there applies. **None of the
items in this section are
```

That first line is 96 characters when the template is materialised as
prose in an actual `TODO.md` file (outside a code block). Since
`TODO.md` is a markdown file subject to `markdownlint-cli2` and the
project's 80-character line-length rule, the instantiated file will fail
MD013. The line is inside a code block in the spec itself (exempt), but
the file produced from the template is not.

**Recommended fix**: wrap the sentence at ≤ 80 characters in the
template text, e.g., break at "applies." and start "**None of the items
in this section are pending..." on the next line.

### M2: Parent README pointer uses forward-looking language

**Location**: § README.md (approx. lines 1015–1019).

The spec's proposed parent README pointer reads: "…which will eventually
replace it." The project's documented style rule (CLAUDE.md) forbids
writing future-state claims in persistent documentation. The spec also
says "state the supersession-direction without prescribing timing", which
this formulation contradicts by prescribing the outcome ("replace").

**Recommended fix**: use a present-tense status statement, e.g.,
"…which is the active development home for the Lean formalization."

### M3: geb-lean/.gitignore described as "unchanged" but A12 already modified it

**Location**: § New file and directory layout (approx. line 259);
§ .gitignore change at the parent (approx. line 1192).

The spec's file layout marks `geb-lean/.gitignore` as "(existing;
unchanged)". However, commit `69123dd0` (`chore(gitignore): whitelist
committed .claude paths`) already modified `geb-lean/.gitignore` by
adding `/.claude/*`, `!/.claude/rules/`, and `!/.claude/settings.json`.
Those negations are functionally inert because the parent `geb/.gitignore`
still has the blanket `.claude` pattern at line 7, which overrides them
(`git check-ignore` confirms `geb-lean/.claude/settings.json` is ignored
via `geb/.gitignore:7`). The spec does not state that the A12 changes to
`geb-lean/.gitignore` should be reverted as part of the cleanup task.

**Recommended fix**: add an explicit statement in the cleanup task (or
the `.gitignore` section) that `geb-lean/.gitignore` is to be reverted to
its pre-A12 state (the three added lines removed) once the parent
`.gitignore` receives the fix. This makes "unchanged" accurate and avoids
confusing duplication.

### M4: check-axioms.sh header lacks commit SHA despite spec claiming it is recorded

**Location**: § Auxiliary scripts (approx. lines 1645–1648).

The spec says the vendored `check-axioms.sh` "carries a header comment
recording the exact upstream source URL and commit SHA from which it was
copied". The actual file's header reads "(No commit SHA recorded in the
plugin manifest; re-vendor by diffing against the on-disk path above
with the same version string 4.4.9.)". The SHA is absent by necessity
(the plugin manifest does not expose it), but the spec's claim that the
SHA is recorded is currently false.

**Recommended fix**: update the spec's description to accurately reflect
what the header contains: the source URL, the plugin version string, and
instructions for re-vendoring by diff — but not a commit SHA (since the
manifest does not supply one). Alternatively, retrieve and record the
SHA explicitly before committing the spec.

### M5: Verification item 14 does not specify the smoke-test form for check-signing-key.sh

**Location**: § Verification — Milestone A checklist item 14.

Verification item 14 says `check-signing-key.sh` "pass[es] a smoke-test
invocation" but does not specify what that invocation is. Unlike
`block-mutating-git.sh` (item 12 gives five explicit test cases with
expected exit codes) and `check-jj-setup.sh` (item 14 gives two cases:
unconfigured clone returns non-zero; post-onboarding returns zero),
`check-signing-key.sh` has no test case defined. Since the script always
exits 0 and only warms an agent, verification is ambiguous.

**Recommended fix**: specify the smoke-test explicitly: e.g., "invoke the
script directly; it must exit 0 and print no error output to stderr;
if a signing key is configured, it must not produce a passphrase-agent
error".

## Cosmetic-taste (NOT counted toward convergence)

None.
