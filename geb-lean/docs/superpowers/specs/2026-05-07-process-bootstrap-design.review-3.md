# Adversarial review cycle 3 — author responses

Review dispatched: fresh-context Agent reading only the spec (not
prior cycles' responses).

## Serious

### S1 — `git fetch` allowlist hand-waved on `--tags`, `--prune-tags`, arbitrary refspecs

**Response: fixed.** Replace the prose-described allowlist with a
**closed enumerated set**: bare `git fetch`, `git fetch origin`,
`git fetch origin refs/pull/*/head:*` (the `gh pr checkout`
form). Everything else (`--tags`, `--prune`, `--prune-tags`,
arbitrary refspecs) is blocked; the hook prints `use jj git fetch
instead`. `jj git fetch` covers tag fetch and prune-equivalent
behaviour through its own bookmark-state update.

### S2 — `lake test` already implies `lake build`

**Response: fixed.** Verified against existing `CLAUDE.md`:
*"The test driver is configured as a library, so tests run during
the build process."* `pre-push.sh` is amended to drop the
redundant `lake build` invocation; running `lake test` alone
covers both.

### S3 — `weak.linter.flexible = true` adoption may break build under warnings-as-errors

**Response: fixed.** Drop `weak.linter.flexible = true` from the
lakefile additions in this refactor. The `flexible` linter flags
overly-permissive tactic uses across substantial existing code;
under the preserved `moreLeanArgs = ["-DwarningAsError=true"]`
each warning becomes a build break. Adoption is deferred to a
separate cleanup workstream that can survey warnings and fix or
document each one.

### S4 — No positive verification that `lake lint` actually checks anything

**Response: fixed.** Verification item 4 is amended: "`lake lint`
is quiet on the current source AND, when a deliberate
violation is introduced (e.g. an unused `set_option` or a
`linter.unusedVariables`-tripping let-binding), `lake lint`
flags it. The violation is then removed and `lake lint` returns
to quiet." This positive-verification step ensures `lintDriver`
is actually wired.

### S5 — CSLib transitive `Classical.choice` would explode CI on day 1

**Response: fixed.** The `axiom_check` job lands in
**report-only mode** at first: it runs `check-axioms.sh` and
reports the output as a CI artefact, but does not fail the build.
A separate Milestone A item adds the initial `AXIOM_ALLOW`
comments to existing source — these are appended above each
flagged declaration as the first encounter touches it (no
mass-rewrite; the existing-file rule from non-goals is preserved
because each `AXIOM_ALLOW` comment lands when its file is
otherwise being edited or as a tracked Milestone-A backlog
item). Once the report is empty, `axiom_check` flips to
fail-mode. The flip is a separate verification gate at Milestone
A completion.

### S6 — `bookmarks("feat/*")` depends on default jj string-pattern config

**Response: fixed.** Use explicit `glob:"feat/*"` in the revset
one-liners. Defensive against `revsets.string-pattern`
configuration overrides at the user level. Update both the
fan-in revset and the mass-rebase revset.

### S7 — `private-commits` rationale conflates "already on remote" with "immutable"

**Response: fixed.** Amend the jj setup section to cite both
exemption conditions explicitly: commits already on the remote
AND commits in the `immutable_heads()` revset (which by default
covers `trunk()` ancestors but is configurable). Both are
exemptions from `private-commits`.

### S8 — Cutover SHA recorded in `main` is self-attesting under force-push

**Response: fixed (acknowledge dependency on branch
protection).** The append-only verification depends on GitHub's
branch protection rules being configured on `main`: (a) no
force-pushes, (b) no branch deletion. These are configured at
Milestone A and verified as a new checklist item. With branch
protection in place, the recorded cutover SHA in
`docs/process.md` is trustworthy because the path that would
allow tampering (force-push of `main`) is closed at the remote.

A signed git tag at the cutover commit (e.g.
`cutover-2026-MM-DD`) is added as belt-and-braces: tags are
independent of branch state, and tag deletion is also closed by
branch-protection rules.

### S9 — `markdown-lint.yml` glob expansion may not honour `.markdownlint-cli2.jsonc` ignores

**Response: fixed.** The `markdown-lint.yml` workflow is amended
to pass `--config .markdownlint-cli2.jsonc` explicitly to the
action and to invoke with the action's `globs` parameter (which
the action passes unexpanded to the underlying binary), not via
shell glob expansion. Documentation in
`.claude/rules/ci-and-workflow.md` notes this dependency.

## Minor

### M1 — `clone` allowlist may clobber `.jj/` if invoked into `.`

**Response: fixed.** The hook spec is amended: `clone` is
allowed only when its target argument is a non-`.` directory
(i.e. creates a new directory; does not clobber the current
working tree). `git clone . <other>` and `git clone <url> .` are
blocked.

### M2 — `AXIOM_ALLOW` comment syntax under-specified

**Response: fixed.** Specify: an `AXIOM_ALLOW` comment is a
single-line `--` comment of the form
`-- AXIOM_ALLOW: <axiom-name> (rationale text)`, placed
immediately above the declaration it applies to with no
intervening blank lines. The script associates it with the next
top-level (column-0) declaration.

### M3 — `.session/README.md` not addressed during transition

**Response: fixed.** During Milestone A → B transition,
`.session/README.md` is amended once to add a header pointer
("`TODO.md` is now the source of truth for active work; the
contents below are legacy entries pending triage. See
`docs/process.md` § Workstream triage for the migration
method."). The README is removed along with the directory at
Milestone B item B4.

### M4 — Skills in tooling list lack always-loaded vs phase-default markers

**Response: fixed.** The phase-driven-workflow table in
CLAUDE.md is amended to mark each entry: `(phase-default)` for
skills invoked at a phase, `(always-loaded)` reserved for
`CLAUDE.md` and `.claude/rules/lean-disciplines.md` (which are
not skills but layers — the table omits them; they live in
their own files).

### M5 — `markdownlint-cli2.jsonc` config-file auto-discovery dependency unstated

**Response: fixed.** The CI workflow passes
`--config .markdownlint-cli2.jsonc` explicitly (rolling into
S9's resolution). `.claude/rules/ci-and-workflow.md`
documents the explicit-config policy.

### M6 — `lean4:checkpoint` interaction with warnings-as-errors unstated

**Response: fixed.** Add a one-line note in the `lean4` skill
mapping (`lean-coding.md` § 4): "`lean4:checkpoint` produces
ordinary commits and is therefore subject to the same
warnings-as-errors gate as any commit; checkpoints with `sorry`
are not committable."

## Cosmetic-taste

### C1 — "value-laden adjectives" framing is colloquial

**Response: rejected (cosmetic-taste).** The framing is the
project's existing wording (carried over from the current
`CLAUDE.md`). The full banned-word list is precise; the framing
is intentionally accessible.

### C2 — 80-char line-length manual rule vs MD013 deferred

**Response: fixed.** The 80-char rule lives in
`.claude/rules/markdown-writing.md` § Line length as a project
convention; `.markdownlint-cli2.jsonc` enforces it via MD013 at
the CI level. The two are aligned; the spec's earlier "deferred"
language about MD013 referred to *line-length-related* false-
positives (e.g. URLs in tables) which we exempt via the
`code_blocks: false`, `tables: false` MD013 settings — not to
the 80-char rule itself.

### C3 — `docs/lean-resources.md` "public-facing" framing unclear

**Response: fixed.** Rephrase as "repository-internal reference
document, available to anyone with read access to the
repository." No GitHub Pages dependency.
