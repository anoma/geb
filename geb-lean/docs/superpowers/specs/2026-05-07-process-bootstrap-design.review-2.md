# Adversarial review cycle 2 — author responses

Review dispatched: fresh-context Agent reading only the spec (the
spec only — not the cycle-1 responses) at
`docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`.

## Blockers

### B1 — Commit type vs branch prefix mismatch (`doc` singular vs `docs/` plural)

**Finding.** Branch prefixes use `docs/<topic>` (plural); mathlib's
commit-message convention uses `doc:` (singular). Spec does not
state both forms explicitly.

**Response: fixed.** Spec's `.claude/rules/ci-and-workflow.md`
section is amended: branch prefix is `docs/<topic>` (plural,
project-local convention); commit-message type is `doc:`
(singular, mathlib-mandated). Both are documented.

### B2 — "Under 200 lines" misrepresented as a "threshold"

**Finding.** Spec phrases the 200-line figure as "the threshold
above which adherence drops"; Anthropic's docs only call it a
"target."

**Response: fixed.** Replace "threshold above which adherence
drops" with "target per Anthropic's recommendation; longer files
consume more context and reduce adherence" (the docs' own
wording, paraphrased).

### B3 — Nested CLAUDE.md auto-discovery is silent in the spec

**Finding.** Anthropic auto-discovers `CLAUDE.md` and
`CLAUDE.local.md` files in subdirectories. The spec is silent;
a contributor adding `GebLean/Utilities/CLAUDE.md` would silently
bypass the rule-priority structure of `.claude/rules/`.

**Response: fixed.** Spec gains an explicit rule: nested
`CLAUDE.md` and `CLAUDE.local.md` files are forbidden outside the
repository root. Per-area instructions go in
`.claude/rules/<name>.md` with `paths:` frontmatter. The rule is
stated in the spec's CLAUDE.md content section and replicated in
`.claude/rules/markdown-writing.md`.

### B4 — `signing.behavior = "own"` (withdrawn by reviewer)

**Response: noted.** The reviewer's verification confirmed `own`
is a valid jj signing-behavior value (the four are `drop`,
`keep`, `own`, `force`); the reviewer demoted this to a
non-finding. No change required.

### B5 — No-copyright-headers rule contradicts the lean-coding.md template

**Finding.** Existing project rule: "Don't write copyright notices
or author notices." New spec's `lean-coding.md` § 6 adopts
mathlib's "copyright header and `Authors:` line" template. This
is a contradiction; the spec does not acknowledge it.

**Response: fixed.** The existing no-headers rule is preserved;
the mathlib header template is **dropped** from
`lean-coding.md`. Apache 2.0 §4 (a)–(d) does not require per-file
copyright headers — the repository-level `LICENSE` is sufficient
for compliance, and §4(c)'s "retain notices from the Work"
requirement applies only to notices that exist in the upstream
work being incorporated; for original GebLean code, no per-file
notices are required to be retained. If we later vendor code from
upstream mathlib or `lean4-skills` that carries per-file
copyright notices, those notices are preserved verbatim per
§4(c) (the no-headers rule does not apply to vendored
upstream content).

`docs/process.md` § Markdownlint discipline gains a sub-section
on the no-headers convention with rationale.

## Serious

### S1 — Revset has no jj-version pin / regression test

**Finding.** The revset one-liners are pinned to jj 0.40 only;
syntax could break under bumps.

**Response: fixed.** Add an explicit note in the Branch model
section: the revset syntax is verified against jj 0.40; on
toolchain bumps, re-verify the one-liners against the new jj
version as part of the bump procedure. The revset is short enough
that the verification is a copy-paste check.

### S2 — `private-commits = "conflicts()"` semantics under-specified

**Finding.** Spec does not state that the protection is at-push-
time (the revset evaluates at push, not at conflict creation), and
does not state that already-pushed commits are exempt.

**Response: fixed.** Amend the jj setup section: the
`private-commits` revset is evaluated **at push time**. Commits
that have been resolved before push are no longer in `conflicts()`
and are eligible for push. Already-pushed commits are exempt per
jj's documentation
(<https://docs.jj-vcs.dev/latest/config/>).

### S3 — `axiom_check` job under-specified for transitive vs direct axioms

**Finding.** Spec does not say what the axiom check does when
mathlib transitively introduces `Classical.choice`. Per-file
`AXIOM_ALLOW` mechanism is mentioned but its semantics are
unclear.

**Response: fixed.** Amend the Auxiliary scripts section:
`scripts/check-axioms.sh` flags every non-allowlisted axiom in
the closure of every checked declaration — including
transitively-introduced ones. The first-pass behaviour is
therefore "loud": every declaration that depends on
`Classical.choice` (almost any mathlib-using declaration) is
flagged. The per-file `AXIOM_ALLOW` comment is the
disambiguation mechanism: a comment of the form
`-- AXIOM_ALLOW: Classical.choice (transitive via Mathlib.X)`
above a declaration tells the script to treat that axiom as
allowed for that specific declaration. This is explicit
acknowledgement: every transitive `Classical.choice` is opt-in
per declaration, not a silent project-wide allowance. CI fails
unless every flagged declaration has an `AXIOM_ALLOW` comment or
the axiom is genuinely on the (reduced) allowlist.

The script's behaviour for direct (in-`GebLean/`) `Classical.choice`
remains: forbidden absent an explicit allowlist comment.

### S4 — `update.yml` "preserved" vs "open question" contradiction

**Finding.** The file-layout diagram lists `update.yml` as
"(existing; unchanged)"; the open-questions section lists
`update.yml` adjustment as a deferred decision.

**Response: fixed.** Resolve to "preserved as-is unless drift is
discovered during plan execution." Drop the `update.yml` entry
from the open-questions section.

### S5 — `gh repo clone` invokes `git clone`, not `git fetch`

**Finding.** Allowlist documents `gh repo clone` under `git fetch`
forms; `gh repo clone` actually invokes `git clone`, which is
absent from both the read-only-form and `git fetch` allowlists.

**Response: fixed.** Add `clone` to the read-only-form allowlist
in the `block-mutating-git` hook spec. (`git clone` does not
mutate the current repository; it creates a new one, so blocking
it serves no purpose. Remove the `gh repo clone` justification
from the `git fetch` allowlist line.)

### S6 — `check-axioms.sh` vendored source not pinned

**Finding.** Spec does not record the source commit SHA from
which `check-axioms.sh` is vendored; future re-vendoring may drift
silently.

**Response: fixed.** Amend the Auxiliary scripts section: the
vendored `check-axioms.sh` carries a header comment recording the
exact upstream source URL and commit SHA from which it was
copied, plus the local modifications (the `Classical.choice`
allowlist exclusion). The plan inserts this header at vendoring
time.

### S7 — Developer onboarding for `.jj/repo/config.toml` not specified

**Finding.** New developers cloning the repository must author
their own `[user]` and `[signing]` blocks; spec does not say where
they learn this.

**Response: fixed.** `docs/process.md` § jj colocated mode (per
`docs/process.md` index entry 8) gains an "On-boarding for new
developers" sub-section that reproduces the
`.jj/repo/config.toml` template, names the placeholder fields the
developer must replace, and describes the failure mode if the
`[signing]` block is omitted (commits push unsigned, which
violates the project's signing convention but does not produce a
build error). The README.md also points new developers at this
sub-section.

### S8 — Docstring requirements stricter than mathlib's

**Finding.** Spec mandates docstrings on every `def`, `structure`,
`class`, `instance`, and major theorem; mathlib's actual rule
treats `instance` docstrings as encouraged-not-required.

**Response: fixed (acknowledge stricter-than-mathlib).** Spec's
`lean-coding.md` § 2 is amended to note: "this project is
stricter than mathlib on `instance` docstrings (mathlib treats
them as encouraged; we require them) because we want every
typeclass instance to be searchable by docstring." Rationale
recorded; no policy change.

## Minor

### M1 — "Anthropic memory architecture" overstates the source

**Response: fixed.** Rename the references-section entry to
"Anthropic `CLAUDE.md` documentation."

### M2 — `.jj/.gitignore` self-creation claim relies on empirical observation

**Response: fixed.** Amend the empirical-verifications appendix:
include the exact command (`jj git init --colocate` in a fresh
git repository) and the observed `.jj/.gitignore` byte count (3
bytes, contents `/*\n`). If a future jj version changes this
behaviour, the manual fallback (`echo '/*' > .jj/.gitignore` per
the documented colocated-conversion procedure) remains
applicable; document that fallback in `docs/process.md` § jj.

### M3 — `markdownlint-cli2-action` is not SHA-pinned in the spec

**Response: fixed.** Amend the CI changes section: the
`markdown-lint.yml` workflow uses
`DavidAnson/markdownlint-cli2-action` SHA-pinned to a specific
commit (the plan resolves the SHA at workflow-authoring time;
the spec mandates SHA-pinning rather than tag-pinning per the
project's general action-pinning policy).

### M4 — Stale-prone counts ("78", "533")

**Response: fixed.** Replace remaining precise counts with
"approximately" qualifiers in the Context section (lines 22-24)
and triage section.

### M5 — `git reflog show main` is local; verification should be remote

**Response: fixed.** Amend verification item 17: the check is
`git log --first-parent main` from the cutover SHA forward,
asserting every commit is either a fast-forward or a normal
merge commit. The remote is the source of truth; the local
reflog is unreliable.

### M6 — "Always-on skills" phrasing conflates load-on-demand with always-loaded

**Response: fixed.** Distinguish in the Tooling section:
*phase-default skills* are skills that should be invoked at
specific phases of work (these load on demand, not at session
start); *always-loaded* refers only to `CLAUDE.md` and the
`.claude/rules/*.md` files without `paths:` frontmatter.

## Cosmetic-taste

### C1 — Triage estimate would help plan calibration

**Response: rejected (cosmetic-taste).** Triage time depends on
user availability for surface-and-confirm; a target estimate
would be a guess and would create false expectations. The
open-ended characterisation is honest.

### C2 — Section-spacing budget high uncertainty

**Response: rejected (cosmetic-taste).** The ~50-line spacing
budget is conservative; if it overruns, the spec's priority-cut
order applies. Tightening the budget by trial-and-error during
authoring is not better than admitting up-front uncertainty.

### C3 — Verification item 5 redundancy

**Response: fixed.** Trim item 5 wording to remove the parenthetical
"(per Anthropic's adherence guideline)" that B2's response also
records.
