# Adversarial review cycle 1 — author responses

Review dispatched: fresh-context Agent reading only
`docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`.

This file records the author's response to every finding. Responses
are categorised:

- **fixed** — edit applied to the spec.
- **deferred (with rationale)** — finding acknowledged; addressed by
  the implementation plan rather than the spec.
- **rejected (cosmetic-taste)** — finding noted as stylistic
  preference; spec retains its current form.

## Blockers

### B1 — Warnings-as-errors enforcement is hand-waved

**Finding.** The spec defers warnings-as-errors enforcement to the
plan's "first-touch task" and admits uncertainty between two
mechanisms; the headline "no `sorry` in commits" rule depends on
this load-bearing mechanism being live, which the spec does not
verify.

**Response: fixed.** Verified empirically against
`lakefile.toml:6`: the existing project already sets
`moreLeanArgs = ["-DwarningAsError=true"]`. This is a Lean kernel-
level flag that promotes the `declaration uses 'sorry'` warning
(and every other warning-class diagnostic) into a build error. The
mechanism is live today; the spec's job is to *preserve* it, not
to discover it. The spec is rewritten to:

1. Quote the existing `moreLeanArgs` setting and identify it as
   the load-bearing mechanism for the `sorry`-in-commits rule.
2. State that the refactor preserves this setting.
3. Drop the "first-touch task verifies and adds if absent"
   language; preservation is sufficient.

### B2 — Self-witnessing verification (item 18) is circular

**Finding.** "The refactor's own work has been performed on a topic
branch and merged into `main` via a normal merge commit,
demonstrating that the new branch model works" is logically
circular: the new branch model only takes effect once the refactor
lands; before then, `main` has no append-only invariant to test.

**Response: fixed.** The notion of "append-only `main`" applies
forward from a declared cutover commit. The spec is rewritten to:

1. Define the cutover as the merge commit on `main` that lands the
   refactor's topic branch (`chore/process-refactor` or similar).
2. State that the append-only invariant binds commits whose first
   parent is at or after the cutover.
3. Replace verification item 18 with: "from the cutover commit
   forward, no force-push has touched `main` and every change to
   `main` is a fast-forward or normal merge commit." This is
   verifiable by `git reflog show main` against the cutover SHA.

### B3 — Workstream triage is unbounded and gates refactor completion

**Finding.** Triage of 78 workstreams plus 533 harness tasks is the
spec's largest activity, requires per-item user confirmation, and
is gated by item 15 of verification. Refactor completion becomes
contingent on user throughput rather than mechanical work.

**Response: fixed.** Triage is split out as a separate post-bootstrap
milestone with its own definition of done. The spec is rewritten
to:

1. Introduce **two milestones**:
   - **Milestone A — Process bootstrap complete** (verification
     items 1–14, 16–18). All structural changes; no triage required.
   - **Milestone B — `.session/` retired** (former item 15).
     A separate post-bootstrap milestone whose completion does not
     gate Milestone A.
2. State that during the period after Milestone A and before
   Milestone B, `.session/` and `TODO.md` coexist; `CLAUDE.md`
   documents the transitional arrangement.
3. Acknowledge in the spec that triage of historical workstreams
   is open-ended and may take many sessions; the plan does not
   try to bound its duration.

### B4 — CLAUDE.md ≤200-line target is unverified for content density

**Finding.** 13 sections, several densely sub-bulleted, may not fit
in 200 lines; spec offers no estimate, fallback, or priority order
for cuts.

**Response: fixed.** The spec is rewritten to:

1. Provide a **per-section line budget** summing to ~180 lines
   (under the 200 cap, with margin):
   - Header + identity: 5
   - Project status: 5
   - Hard rules (~10 bullets): 22
   - Phase-driven workflow table: 18
   - Style guidelines (with banned-word pointer to
     `markdown-writing.md`): 8
   - Repo structure: 8
   - Constructive-only Lean code: 6
   - Specs and plans on the feature branch: 7
   - GebLean-specific disciplines (one paragraph each, three
     items): 18
   - Cross-reference for spec/plan authorship: 4
   - Tooling: 18
   - Skill-creation pointer: 4
   - Pointers: 8
   - Section spacing: ~50
2. Position the 200-line figure as a **target with rationale**
   (Anthropic's documentation cites 200 lines as the threshold
   above which adherence drops), not a hard cap.
3. State the priority order for cuts if the budget is exceeded:
   first move banned-word list to `markdown-writing.md` (spec
   already plans this), second compress phase-driven workflow
   table to 1-line-per-phase, third move tooling-detail to
   `docs/process.md`.

### B5 — `.claude/rules/*.md` activation semantics are misstated

**Finding.** Path-scoped rules trigger on Read tool calls, not
"open in editor." The spec's cross-reference from CLAUDE.md does
not pull path-scoped content into context. The Lean disciplines
that must apply during spec/plan authorship cannot reside in a
`paths:`-scoped file and rely on cross-reference alone.

**Response: fixed.** This is a substantive design change. The spec
is rewritten to split `.claude/rules/lean-coding.md` into two
files:

1. **`.claude/rules/lean-disciplines.md`** — *no `paths:`
   frontmatter* (loaded unconditionally, like CLAUDE.md but in a
   separate file). Contains the project-specific Lean disciplines
   that must apply during spec/plan authorship as well as during
   `.lean` file edits:
   - Literature-citation discipline.
   - Bottom-up named-composite discipline.
   - Non-negotiable interfaces.
   - Hole-marking discipline (`_` / `sorry` / `admit`).
2. **`.claude/rules/lean-coding.md`** — *`paths: ["**/*.lean"]`*
   (loaded only when `.lean` files are read). Contains rules that
   genuinely apply only when editing Lean source:
   - Build discipline (`lake build`/`lake test`, etc.).
   - Mathlib comment / docstring rules.
   - Lean idioms (`@[ext]`, `extends` semantics, etc.).
   - `lean4` skill-mapping table.
   - Universe / variable hygiene.
   - Style header template.
   - Constructive-only Lean code (file-level repetition of
     `lean-disciplines.md` so it surfaces during file reads).
3. CLAUDE.md item 9 ("GebLean-specific disciplines") becomes a
   one-line *index* pointing at `lean-disciplines.md` (which is
   loaded unconditionally; the index is for human readers of
   CLAUDE.md).
4. Cross-reference at item 10 of CLAUDE.md is rewritten:
   `lean-disciplines.md` is always in context, so no manual
   "consult" instruction is needed; the cross-reference now
   points only at `lean-coding.md` for cases where it would not
   otherwise load (rare).

## Serious

### S1 — Revset syntax in `regenerate-integration.sh` is malformed

**Finding.** The quoted revset `main | bookmarks(glob:"feat/*") ~ ::main | …` is missing parens and is parse-ambiguous.

**Response: fixed.** Rewrite the revset block as full
parenthesised form for all six prefixes; the operator-precedence
intent is bookmark-selection then ancestor-exclusion then union.
Also, drop the redundant `glob:` prefix per jj revset
documentation: an unprefixed string literal already matches as a
glob pattern in `bookmarks(...)`.

### S2 — `private-commits = "conflicts()"` does not prevent leaked-conflict-directory case

**Finding.** The spec claims the setting prevents
`.jjconflict-base-*/` / `.jjconflict-side-*/` directory leakage to
the GitHub remote; this conflates jj's commit-level conflict state
with working-copy materialisation that a `git add` could pick up.
Such a `git add` is already prevented by `block-mutating-git`, so
the justification is misdirected.

**Response: fixed.** Drop the directory-leakage justification.
Restate `private-commits = "conflicts()"` as: "refuses to push any
commit (and its descendants) that has conflict state, preventing
unintentional propagation of in-flight conflicts to remote
collaborators." Cite the jj config docs.

### S3 — `check-signing-key.sh` queries git config but jj signing config is independent

**Finding.** Lines 766–769 set `jj`-side signing config; lines
850–856 query `git config commit.gpgsign` to decide whether to
warm gpg-agent. Independent settings; the hook can skip warming
even when jj is signing.

**Response: fixed.** Hook implementation should query both:
`git config --get commit.gpgsign` AND `jj config get
signing.behavior`. If either indicates signing is active, warm the
appropriate agent. The spec's hook-implementation section is
rewritten accordingly.

### S4 — `pre-push.sh` references `lake lint` but lakefile may lack `lintDriver`

**Finding.** Spec admits `lintDriver` may not be set; pre-push
script bakes in `lake lint` regardless.

**Response: fixed.** Verified against `lakefile.toml`: the
existing file does NOT set `lintDriver`. The spec is rewritten so
that `pre-push.sh` calls `lake lint` only after the lakefile
modification (adding `lintDriver = "batteries/runLinter"`) has
landed. The plan ordering enforces this dependency.

### S5 — `regenerate-integration.sh` and `rebase-topics.sh` duplicate jj built-ins

**Finding.** Both scripts wrap single `jj` invocations; an
in-`docs/process.md` documented one-liner is preferable.

**Response: fixed (partial).** Drop both scripts. Document the
fan-in-merge sequence and the mass-rebase command in
`docs/process.md` § Branch model as canonical sequences. Update
verification item 14 to remove the script names. Update file
layout (Section 5) to remove the script files.

Remaining scripts (`check-axioms.sh`, `pre-push.sh`,
`block-mutating-git.sh`, `check-signing-key.sh`) are kept because
none reduces to a single command.

### S6 — `pre-push.sh` is not invoked by anything mechanical

**Finding.** No hook installs `pre-push.sh` to run automatically;
spec does not say it is manual.

**Response: fixed.** Declare `pre-push.sh` as a **manual checklist
runner** invoked explicitly by the user before each push (e.g.
`bash scripts/pre-push.sh && jj git push --remote origin -b
<bookmark>`). The CLAUDE.md tooling section and `docs/process.md`
both document this. No automatic-invocation hook is installed
(verified: jj 0.40 does not have a documented `pre-push` hook
mechanism that fires on `jj git push`).

### S7 — `--prune` block in `block-mutating-git` lacks rationale

**Finding.** Hook blocks `git fetch --prune` without explaining
why or how jj keeps remote-tracking refs in sync.

**Response: fixed.** The hook spec is amended: `--prune` is
blocked because it deletes git's remote-tracking refs in
`.git/refs/remotes/`, which jj's bookmark-tracking state mirrors;
in-place pruning by raw git can desync jj's view. `jj git fetch`
performs its own remote-tracking-state update on each invocation,
so the prune-equivalent effect is available through jj.

### S8 — mathlib commit convention adoption ignores existing mid-stream history

**Finding.** Spec adopts mathlib's `<type>(<scope>): <subject>`
form forward; existing `git log` shows mixed-form messages. No
cutover marker.

**Response: fixed.** Document the cutover in the spec: the
commit-message convention applies to commits whose first parent
is at or after the refactor's cutover commit (same cutover defined
in B2's response). Pre-cutover commit messages remain as they are.

### S9 — "Empty lines inside declarations are lint-discouraged" is unsupported by cited source

**Finding.** Cited `https://leanprover-community.github.io/contribute/doc.html` does not contain this rule.

**Response: fixed.** Drop the claim from the spec. (If a
mathlib-internal lint discourages empty lines in declarations, it
will be picked up by `lake lint`; the spec does not need to
restate it.)

### S10 — 200-line CLAUDE.md target is conflated with auto-MEMORY threshold

**Finding.** Anthropic's docs distinguish CLAUDE.md (target: under
200 lines for adherence) from MEMORY.md (auto-memory; same
threshold but different mechanism). Spec elevates the figure to a
hard verification gate.

**Response: fixed.** Reword verification item 5 from "≤ 200 lines"
to "under 200 lines, per Anthropic's adherence guideline." This is
a target with documented rationale, not a hard cap. The per-section
line budget (B4 response) demonstrates feasibility.

## Minor

### M1 — "jj 0.40+" lease-protection version qualifier is unverified

**Response: fixed.** Drop the version qualifier; jj's lease-on-
push behavior is always-on per the bookmarks documentation. The
0.40 floor is retained for unrelated reasons (the verified
features the spec relies on are documented in 0.40+).

### M2 — Banned-words list is shorter than the existing CLAUDE.md's

**Response: fixed.** The canonical list lives in
`.claude/rules/markdown-writing.md`. CLAUDE.md § Style guidelines
gives a short example with a pointer to the full list. The
canonical list extends the existing 30-word set with any
additional adjectives caught by the new prose-tone rule.

### M3 — Authoring header is itself a development-history reference

**Response: rejected (cosmetic-taste, with rationale).** The spec
is the artefact that institutes the rule; the authoring header
applies to *this one* spec for traceability of provenance during
the refactor's own adversarial review cycle. Future specs
authored under the new regime omit this header. The header is
removed from any spec authored after Milestone A.

### M4 — Bookkeeping on workstream / harness counts

**Response: fixed.** Use "approximately" qualifiers where the
counts may drift before plan execution. Cross-reference between
Context and Workstream-triage sections.

### M5 — `.markdownlint-cli2.jsonc` rules deferred but spec must be clean

**Response: fixed.** State explicitly that the configuration is
iterated until clean against the refactor's own artefacts; the
final overrides are recorded in `docs/process.md` § Markdownlint.
The current configuration (in this very repository, alongside this
spec) exempts MD013 for tables and code blocks.

### M6 — `.claude/rules/` vs `.claude/rules/*.md` inconsistency

**Response: fixed.** Standardise on `.claude/rules/` for the
directory and `.claude/rules/<name>.md` (or the wildcard) for
specific files.

### M7 — Allowlist semantics phrasing

**Response: fixed.** Rephrase to "with the allowlist reduced to
`propext`, `Quot.sound`, `quot.sound`" instead of "excludes
`Classical.choice` from the allowlist."

## Cosmetic-taste

### C1 — Order-of-artefact-production diagram repeats material in `docs/process.md` § 4

**Response: rejected (cosmetic-taste).** The spec is intended to
be self-contained; the diagram in the spec defines the order, and
`docs/process.md` § 4 references back. Single source of truth;
duplication is verbal recap, not content drift.

### C2 — "Apache 2.0 (matching mathlib)" lacks primary-source link

**Response: fixed.** Add a citation:
`https://github.com/leanprover-community/mathlib4/blob/master/LICENSE`.

### C3 — Six branch prefixes for a single-developer experimental repo unjustified

**Response: rejected (cosmetic-taste).** The taxonomy is adopted
verbatim from the geb-mathlib design specifically because
consistency between the two repositories is a goal of the
refactor. A reduced taxonomy here would create a divergence the
user would have to rebridge later.

## Verification-log addenda

The reviewer's verification log noted:

- **No `git clean -xdf` warning in upstream jj docs.** The warning
  message was observed empirically during the brainstorm session
  (the hint was printed by `jj git init --colocate` itself at
  iteration time, captured in the shell session). The spec's
  citation is therefore "verified empirically against jj 0.40
  output," not "verified against the docs page" — clarify in the
  spec.
- **Default unprefixed string in revsets matches as glob.** Drop
  the redundant `glob:` prefix from the documented one-liner per
  S5's response.
