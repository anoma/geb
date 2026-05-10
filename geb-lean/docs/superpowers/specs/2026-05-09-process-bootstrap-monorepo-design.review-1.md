# Adversarial review cycle 1 — 2026-05-09 process-bootstrap monorepo spec

**Reviewer**: fresh-context Agent.
**Spec under review**:
`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`.
**Convergence threshold**: zero blocker / serious / minor findings
(cosmetic-taste excluded).

## Summary

Three blockers, three serious findings, three minor findings. The
most consequential are a wrong license claim that propagates through
every licence-governance section of the spec (B1); a factual error
about `lintDriver` already being present in `lakefile.toml` that the
spec calls absent (B2); and a direct contradiction between
verification item A3 (passes only when the axiom script reports
nothing) and the CI section (which explicitly puts the axiom job in
report-only mode at Milestone A, before any annotation has been done,
because practically every declaration will be flagged). The serious
findings include a residual monorepo confusion: the
`geb-lean/` directory-layout diagram still shows `.git/` as an
existing entry (geb-lean is a monorepo subdirectory and has no
`.git/` of its own), and the spec silently creates a
parent-level `markdown-lint.yml` while ignoring an existing
`geb-lean/.github/workflows/markdown-lint.yml` that would produce
duplicate CI. The spec is otherwise well-structured and substantially
correct on jj, gitignore patterns, hook design, and branch-model
mechanics.

## Blocker findings

### B1: Parent `geb/LICENSE` is GPLv3, not Apache 2.0

**Location**: § Repository structure, line 65; § Goals item 9,
lines 168–171; § `.claude/rules/lean-coding.md`, lines 631–637;
`docs/process.md` section 18, lines 785–790; § README.md item 4,
line 1029; § References, line 1907.

The spec asserts in every licence-governance passage that the parent
`geb/LICENSE` is Apache 2.0 and that geb-lean content is covered
under it. The actual `geb/LICENSE` file is GPLv3. Additionally,
`geb-lean/` already has its own Apache 2.0 `LICENSE` file (distinct
from the parent's), which the spec does not mention or address in
goal 9's "no `geb-lean/LICENSE` is created" statement. Directing the
new `README.md` and `lean-coding.md` to point at `../LICENSE` for
licence coverage would point readers at a GPLv3 licence, which is
incorrect for geb-lean's Apache 2.0 content.

**Recommended fix**: Correct the parent licence claim to GPLv3.
Acknowledge that `geb-lean/` has its own Apache 2.0 `LICENSE`
(existing; unchanged) that governs geb-lean content; update all
licence-governance passages to reference `geb-lean/LICENSE` rather
than `../LICENSE`, and remove the incorrect "geb-lean uses [the
parent licence] transitively" wording.

### B2: `lintDriver` is already present in `lakefile.toml`

**Location**: § Lakefile changes, line 1066–1068.

The spec states: "`lintDriver = \"batteries/runLinter\"`. Verified
against `lakefile.toml`: this is currently absent." The actual
`lakefile.toml` has `lintDriver = "batteries/runLinter"` on
line 6; it is not absent. If the plan adds the line a second time,
the result is a duplicate key that will produce a parse error or
silent override depending on TOML semantics, and verification item
A4 (which checks that `lake lint` works) will be confounded.

**Recommended fix**: Correct the claim to note that `lintDriver` is
already present and that no lakefile change is needed for that
setting. Remove the plan task that adds it, or restate the task as
a verification-only step confirming the setting is present and
active.

### B3: Verification item A3 contradicts the report-only CI mode

**Location**: Verification checklist item A3, line 1825; CI
changes section on the `axiom_check` job, lines 1100–1117;
Auxiliary scripts section, lines 1663–1667.

Item A3 reads: "`bash scripts/check-axioms.sh GebLean/ test/`
reports no non-allowlisted axioms." This is a hard passing condition
at Milestone A. The CI changes section states the `axiom_check` job
lands in report-only mode because "CSLib (a peer dependency) and
mathlib both transitively introduce `Classical.choice` into the
closure of practically every GebLean declaration; flipping the job
to fail-mode on day 1 would break CI universally." The Auxiliary
scripts section separately describes a "CI fails unless every flagged
declaration has either an `AXIOM_ALLOW` comment or no axiom
dependency outside the (reduced) allowlist" condition — which is
the fail-mode condition, not the report-only condition. Item A3
cannot be satisfied at Milestone A unless either every declaration
has already been annotated (which the spec defers to Milestone B)
or A3's passing condition is wrong.

**Recommended fix**: Restate item A3 as a smoke-test condition:
the script runs, produces a report, and exits 0 (or the script
infrastructure works end-to-end). Move the "reports no
non-allowlisted axioms" condition to Milestone B item B7, alongside
the axiom-job flip to fail-mode. Correct the Auxiliary scripts
section's "CI fails unless..." sentence to be conditional on
fail-mode (i.e. post-Milestone-B).

## Serious findings

### S1: `geb-lean/` layout diagram shows `.git/` as an existing entry

**Location**: § New file and directory layout, line 257.

The directory tree for `geb-lean/` includes the line
`├── .git/ (existing; unchanged)`. `geb-lean/` is a subdirectory
of the geb/ monorepo; it has no `.git/` of its own — the git state
is in `geb/.git/` at the parent. The spec opens by saying it
"incorporates the monorepo-subdirectory reality," but this vestige
contradicts that claim and would mislead an implementer checking
their working tree against the spec diagram.

**Recommended fix**: Remove the `.git/` entry from the `geb-lean/`
layout diagram. Optionally add `geb/.git/ (existing; unchanged)` to
the parent layout diagram if an anchoring entry is wanted.

### S2: Existing `geb-lean/.github/workflows/markdown-lint.yml` not addressed

**Location**: § New file and directory layout, lines 259–262 (the
`geb-lean/.github/workflows/` subtree); § CI changes, line 1122.

The spec creates `geb/.github/workflows/markdown-lint.yml` (new, at
the parent level, path-filtered). The `geb-lean/.github/workflows/`
directory already contains a `markdown-lint.yml`. The spec's
`geb-lean/` layout diagram lists `update.yml` and
`create-release.yml` as inert-unchanged entries but omits the
existing `markdown-lint.yml`. Without explicit disposition, the
existing file would remain, producing two markdown-lint workflows:
a parent-level one (path-filtered to `geb-lean/**`) and a
geb-lean-level one (unflitered `**/*.md`), running redundantly on
every push.

**Recommended fix**: Add `geb-lean/.github/workflows/markdown-lint.yml`
to the layout diagram with the disposition `(- removed; superseded
by parent-level workflow)`. Add a corresponding plan step to delete
it before creating the parent-level workflow.

### S3: `ci-and-workflow.md` path filter misses parent-level CI files

**Location**: § `.claude/rules/ci-and-workflow.md`, lines 695–699.

The YAML frontmatter specifies `paths: [".github/workflows/**",
"scripts/**"]`. `CLAUDE_PROJECT_DIR` is `geb-lean/`; these paths
resolve to `geb-lean/.github/workflows/**` and
`geb-lean/scripts/**`. The primary CI files after this refactor
(`lean_action_ci.yml`, `markdown-lint.yml`) live at
`geb/.github/workflows/` — outside `geb-lean/` — and are therefore
outside the path rule's scope. A developer editing those files will
not have the CI conventions loaded automatically from this rule.

**Recommended fix**: Either add a note in the spec (and in the
rule's own header) that it covers geb-lean-scoped files only and
that parent-level workflow edits should be done with `docs/process.md`
as the reference; or add a second path `"../.github/workflows/**"`
if Claude Code's path-scoping supports relative paths outside the
project root (verify before adopting). Document whichever choice is
made so the gap is explicit rather than silent.

## Minor findings

### M1: "future-direction" in the spec'd `geb/README.md` text

**Location**: § README.md, line 1003.

The spec provides a draft pointer for `geb/README.md` reading
"The active and future-direction code of this project lives in
`geb-lean/`…". "Future" appears on the forbidden-word list in
`CLAUDE.md`; the draft text will become committed content and
therefore falls under the project's prose-register rule.

**Recommended fix**: Rephrase to avoid "future", e.g. "The Lean
formalisation work of this project lives in `geb-lean/`…" or
similar direct description.

### M2: `blocked-on-X` status label uses a forbidden word

**Location**: § TODO.md format, line 864.

The `TODO.md` entry template lists `blocked-on-X` as a permitted
status value. "Blocked" appears in the forbidden-word list in
`CLAUDE.md`. The `TODO.md` is a committed document; its template
(and populated entries) fall under the prose-register rule.

**Recommended fix**: Replace `blocked-on-X` with a term not on the
forbidden list, such as `waiting-on-X` or `pending-X`, throughout
the `TODO.md` format definition and any usage in `docs/process.md`.

### M3: "Future" used as a plain temporal adjective in spec prose

**Location**: Lines 211, 1420, 1629, 1683, 1923.

Five passages in the spec use "future" as a plain temporal adjective
("future edits", "future versions", "future re-vendoring", "future
lakefile addition", "future jj version"). The spec itself is a
committed document subject to the forbidden-word rule. The uses are
natural and the meaning is clear without the word in each case.

**Recommended fix**: Rephrase each occurrence to remove "future",
e.g. "rules bind subsequent edits", "later versions", "on
re-vendoring", "should a lakefile addition introduce…", "should a
later jj version change this behaviour".

## Cosmetic-taste (NOT counted toward convergence)

None.
