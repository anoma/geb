# Adversarial review of fork-upstream flow spec (round 3)

## Scope

Round 3 reviews:

- The whole spec at
  `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.
- The new § Adversarial review of specs and plans in
  `docs/process.md`.
- The new adversarial-review bullet in `CLAUDE.md` § Hard
  rules and the two Adversarial-review rows in `CLAUDE.md`
  § Phase-driven workflow.

The convergence criterion for this workstream is zero
blocker, zero serious, and zero minor findings;
cosmetic-taste findings may remain.

## Summary

Four defects identified: zero blocker, two serious, two
minor. The serious findings concern an onboarding-sequence
gap that the round-2 fix relocates rather than closes, and
a CLAUDE.md vs `docs/process.md` redirection that points at
a section heading that does not yet exist. The minor
findings concern restated context that drifts from the
authoritative source. This round does not converge.

## Defects

### 1. Onboarding sequence assumes a pre-existing `origin` git remote

**Severity**: Serious.

**Where**:
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`
lines 432-437 (§ Per-clone `gh` configuration, "Properties
to note") and lines 477-483 (§ Documentation changes,
`docs/process.md` bullet); together with `docs/process.md`
lines 186-208 (§ jj colocated mode onboarding sequence).

**Defect**: The spec pins the new
`gh repo set-default rokopt/geb` step "immediately after the
first `jj git fetch --remote origin` (so that the `origin`
remote URL is in place when `gh` resolves it)". The
"Properties to note" section reinforces this: "Prerequisite:
the `origin` git remote exists and its URL points at
`rokopt/geb`." But the onboarding sequence in
`docs/process.md` § jj colocated mode (the section the spec
edits) contains no step that adds the `origin` git remote.
The sequence as written is: `jj git init --colocate`,
per-repo configuration, per-developer signing, then
`jj git fetch --remote origin`. `jj git init --colocate`
does not configure an `origin` URL on its own. A new
developer following the documented sequence verbatim hits
a fetch failure at step 4, well before reaching the new
`gh repo set-default` step. Round 2's defect 1 raised the
same class of issue and was nominally addressed by pinning
position, but the prerequisite (the git remote itself
being configured) is still unsatisfied by the surrounding
sequence.

**Suggested fix**: in the spec's § Documentation changes
bullet for `docs/process.md`, add a prior onboarding step
that registers the `origin` git remote (for example,
`git remote add origin ssh://git@github.com/rokopt/geb`,
or a `git clone` predecessor that obviates
`jj git init --colocate`), and state the precondition for
`jj git fetch --remote origin` explicitly.

### 2. CLAUDE.md cross-reference lists subsection names that do not match

**Severity**: Minor.

**Where**: `CLAUDE.md` lines 43-46.

**Defect**: The new hard-rule bullet references
"`docs/process.md` § Adversarial review of specs and plans
for the categorisation, author-response, and loop
protocol." The actual section heading in `docs/process.md`
is "Adversarial review of specs and plans" (line 45), which
matches. The subordinate headings the bullet alludes to are
"Defect categorisation", "Author response", and "Loop", but
the bullet writes "categorisation, author-response, and
loop protocol". The hyphenation "author-response" differs
from the actual heading "Author response", and "loop
protocol" collapses two distinct subheadings ("Loop", and
the implicit "protocol" idea spread across § Reviewer
protocol). A reader searching for "author-response" by
literal string in the target file will not find it.

**Suggested fix**: change the bullet to reference the
section as a whole without listing subsections, or align
the subsection names exactly (`§ Reviewer protocol`,
`§ Defect categorisation`, `§ Author response`,
`§ Convergence criterion`, `§ Loop`).

### 3. § Adversarial review section does not pin reviewer tool surface

**Severity**: Serious.

**Where**: `docs/process.md` lines 51-58 (§ Reviewer
protocol).

**Defect**: The section says a reviewer is a "new
general-purpose `Agent` invocation per round … that reads
only the artefact at the given path and its cited sources".
"Cited sources" is the artefact author's choice of what to
cite; a reviewer told to read "only" those sources cannot
verify claims about files the spec does not cite (for
example, `scripts/pre-push.sh` and
`.markdownlint-cli2.jsonc`, both referenced indirectly by
the spec under review). The section also does not state
whether the reviewer may invoke read-only Bash, `gh`, `jj`,
or LSP/MCP tools to verify factual claims, nor whether
mutating operations are forbidden. A reviewer dispatched
under this protocol could either be too narrow (no tool
use) or too broad (mutating operations), depending on
interpretation.

**Suggested fix**: specify that the reviewer reads the
artefact, its cited sources, and any file or remote
resource needed to verify a factual claim in the artefact;
and that the reviewer may invoke read-only operations only
(no mutating Bash, `git`, `jj`, `gh`, or file-write tool
use).

### 4. Round-2 pre-spec-bullet fix introduces a forward dependency

**Severity**: Minor.

**Where**:
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`
lines 78-87 (§ State at spec time, last bullet) and lines
33-35 (preamble describing what "Pre-spec" prefixes mean).

**Defect**: The preamble says items prefixed "Pre-spec"
describe behaviour "that the spec's Hook and configuration
changes section narrows." The last bullet of § State at
spec time describes the GitHub server-side "Create a pull
request" URL, and closes with: "The spec does not narrow
this behaviour; instead, § Per-clone `gh` configuration
introduces an alternative PR-creation path
(`gh pr create`) that the operator uses in place of the
printed URL when the PR's intended base is the fork." This
bullet is not prefixed "Pre-spec" — so the preamble's
contract is not directly violated — but it sits in the
same list as the explicitly Pre-spec-prefixed items and
reads as the same kind of item. A reader scanning the list
cannot tell at a glance which items are inputs the spec
narrows (the Pre-spec ones) and which are inputs the spec
leaves alone (this last one).

**Suggested fix**: either prefix the bullet with a label
that contrasts with "Pre-spec" (for example, "External
fact:"), or move the bullet out of § State at spec time
into its own paragraph in § Per-clone `gh` configuration.

## Confirmed-correct claims (sample)

- `jj git push --remote` has no documented short form;
  `-r` resolves to `--revisions`. Verified by
  `jj git push --help`.
- `gh repo set-default --view` exits 0 with empty stdout
  when no default is set in the current clone. Verified by
  direct invocation.
- `git remote -v` shows `origin` at
  `ssh://git@github.com/rokopt/geb` and `upstream` at
  `git@github.com:anoma/geb.git`. Verified by direct
  invocation.
- `jj git remote list` shows both `origin` and `upstream`
  with the same URLs. Verified by direct invocation.
- The pre-tool hook today permits
  `jj git push --remote upstream` (exit 0); the spec's
  deny clause is a real behaviour change. Verified by
  direct hook invocation.
- `git fetch upstream` is denied today under the existing
  one-positional allowlist (`origin` only). Verified by
  direct hook invocation; consistent with the spec's
  § State at spec time and § Hook and configuration
  changes.
- The new `CLAUDE.md` § Hard rules bullet's convergence-
  threshold restatement (zero blocker, zero serious, zero
  minor) matches `docs/process.md` § Convergence criterion.
  The two are consistent.
- The new § Phase-driven workflow rows for "Adversarial
  review (spec)" and "Adversarial review (plan)" are
  consistent with the rest of the table's column structure
  and with the convergence threshold restated in § Hard
  rules.
- Op 5 prose accurately describes the partial-probe status
  of T8 after the round-1 fix.
- Op 7 (topic-branch propagation) is covered as an
  Operation rather than only as an Out-of-scope item,
  closing round-1 defect 4.
