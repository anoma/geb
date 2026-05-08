# Adversarial review cycle 1 — author responses (plan)

Review dispatched: fresh-context Agent against
`plans/2026-05-07-process-bootstrap-plan.md` cycle-0 draft.
**Reviewer's executive summary**: *"The plan is structurally
sound and tracks the spec well, but it contains one
execution-fatal blocker: from Task A13 onward, the
`block-mutating-git` PreToolUse hook will deny every
`git add` / `git commit` / `git switch` invocation that the
plan explicitly tells Claude to run."*

## Blocker

### B1 — Hook denies the plan's own subsequent commits

**Finding.** Task A13 wires `.claude/settings.json`, which
activates `block-mutating-git` for subsequent sessions
(and possibly the same session). Tasks A14–A24, A26, A30
all instruct Claude to run `git add` + `git commit`. Once
the hook is wired, those calls are denied.

**Response: fixed.** Reordered Milestone A so that the
settings-wiring task is the *final* Claude-direct
commit-producing task, performed immediately before
Milestone A verification. All earlier tasks complete their
`git add` / `git commit` steps with the hook unwired. After
the new A27 (settings wiring), no Claude-direct
commit-producing steps remain — A29–A33 are either
user-direct (`git`/`jj` push, signed tag, GitHub UI) or
post-cutover commits routed through `jj describe` after the
user has run `jj git init --colocate` at A25.

The previous A13 (settings wiring) is now A27. Tasks A14
through A26 have been renumbered as A13–A25 (with
intermediate user-direct A24 = jj on-boarding) so the
plan's task numbers remain monotonic.

## Serious

### S1 — Missing `private-commits = "conflicts()"` push smoke test

**Finding.** Spec § jj setup explicitly assigns the
"manufacture a conflict; resolve it; push" verification to
the plan. The plan had no such task.

**Response: fixed.** Added new task A26
(`Smoke-test the conflicts() push semantics`) that
manufactures a conflict on a throwaway jj revision,
resolves it, and confirms `jj git push --remote origin -b
<throwaway>` succeeds without `--allow-private`. The task
is purely behavioural verification; it is not a
commit-producing task. Placed between A25 (`pre-push.sh`)
and A27 (settings wiring) so it benefits from the
already-initialised jj setup.

### S2 — `.markdownlint-cli2.jsonc` precondition treated as already-present

**Finding.** Task A3 said "verify; no edit unless lint
reveals a defect." The file does exist at session start
(verified empirically), but the plan should not silently
defer if it is missing.

**Response: fixed.** A3 now contains an explicit
precondition check: if `.markdownlint-cli2.jsonc` is
absent, author it per spec § `.markdownlint-cli2.jsonc`
before proceeding.

### S3 — `integration` branch referenced in CI workflows but never created

**Finding.** A4's `markdown-lint.yml` and A14's
`axiom_check` CI step both list `integration` in their
`branches:` triggers. No task creates or pushes the
`integration` branch.

**Response: fixed.** Added new task A22
(`Initialise the integration branch`) post-A21 (CLAUDE.md)
and pre-A23 (CLAUDE.md was A24). The task creates
`integration` as a fan-in revset of `main` plus the present
topic branch using the `jj new` revset incantation from
spec § Branch model, sets the `integration` bookmark, and
defers the actual push to a user-direct sub-step (push is
user-gate per CLAUDE.md hard rule).

### S4 — Action-SHA placeholders not enforced

**Finding.** Tasks A4 and A14 use `<SHA>` placeholders
without an enforcement step that the committed file
contains a real SHA.

**Response: fixed.** Both A4 and A14 now have an explicit
"verify no `<SHA>` placeholder strings remain" step that
runs `grep -n '<SHA>' <workflow-file>` and rejects the
commit if any match is found.

### S5 — A29 narrative on tag listing mutual-exclusion

**Finding.** The plan's A29 (signed tag) text could
emphasise more clearly that the wildcard refspec push form
is safe only because step 1 verifies zero pre-existing
`cutover-*` tags and step 3 verifies exactly one new tag.

**Response: fixed.** A29 (now A30) step 4's prose tightened
to cross-reference the spec's verification item 17
"exactly one line" guarantee and to re-emphasise that any
stray `cutover-*` tag must be resolved at step 1.

### S6 — A26 (`pre-push.sh`) smoke test predates A25 (jj init)

**Finding.** A26 step 1 invokes `bash
scripts/check-jj-setup.sh`, which exits non-zero pre-A25.
A26 was listed as depending only on A2/A7/A8, not A25, so
the smoke test would always fail at that point.

**Response: fixed.** A26 (now A25) `Depends on:` line
extended to include A24 (the new number for jj init). The
smoke test now expects zero exit, since the precondition
guarantees jj is initialised.

### S7 — A30 commit on `main` violates append-only

**Finding.** A30 said "Commit on `main` (or via a
follow-up topic branch per the user's preference)". The
spec § Branch model says topic branches land via merge
commits; direct commits on `main` violate the append-only
invariant.

**Response: fixed.** A30 (now A32) instructs the user to
create a follow-up topic branch (`docs/cutover-sha-record`),
edit `docs/process.md`, push the branch, open a PR, and
land it via a merge commit. The follow-up commit is via
`jj describe` (post-A24 jj is initialised); the merge is
user-direct per the existing user-gate convention.

## Minor

### M1 — Forbidden-word "block" used as verb in plan prose

**Finding.** Several lines use "block" as a regular verb
in narrative prose (e.g. "On block: prints translation
message"). The technical script name `block-mutating-git`
is exempt; verbal uses are not.

**Response: fixed.** Replaced narrative "block" → "deny"
or "reject" throughout. Script-name occurrences and the
review category-name `blocker` retained verbatim.

### M2 — Five lines exceed 80 characters

**Finding.** Lines flagged. Most are tables (exempt per
config) but a few are narrative.

**Response: fixed.** Re-wrapped narrative lines to ≤80
characters. Re-ran `markdownlint-cli2` to confirm zero
violations remain.

### M3 — Plan summary task numbering

**Finding.** Plan summary table said "Tasks A1–A32" but
the structural decomposition leaves room for confusion.

**Response: fixed.** Plan summary updated to reflect the
post-cycle-1 numbering (A1 through A33 in Milestone A; B1
through B6 in Milestone B); the table cell explicitly
calls out the user-direct vs. Claude-direct split.

### M4 — A22 status nuance

**Finding.** A22 (now A23 after S3 insertion) says the
refactor's TODO entry status is `executing`, but that
status applies only mid-Milestone-A; once A33 (Milestone-A
sign-off) lands, the entry's status changes.

**Response: fixed.** A23 now specifies the entry's initial
status as `executing` with a one-line note that it
advances to `awaiting-Milestone-B-completion` after
Milestone A sign-off and is removed from `TODO.md` after
Milestone B (when its triage and follow-up work conclude).

### M5 — A10 hook-test runner not in the spec's directory layout

**Finding.** Spec § "New file and directory layout" lists
`scripts/hooks/{block-mutating-git.sh,
check-signing-key.sh}` only; spec § "Open questions"
explicitly defers `scripts/hooks/tests/` smoke-test
infrastructure. The plan's A10 introduced the deferred
directory.

**Response: fixed.** A10 now performs the five
verification cases inline (using `bash -c` heredocs to
feed JSON-stdin to the hook script) without authoring a
test runner under `scripts/hooks/tests/`. The cases are
recorded in the task's body so an executor can re-run
them by copy-paste; spec verification item 12 still
passes because verification is by direct invocation, not
via a separate runner.

### M6 — Word "future" in A19 prose

**Finding.** The phrase "before jj 1.0" reads as a
forecast of the kind the project's style discipline tries
to avoid; it is also adjacent to the forbidden word
"future".

**Response: fixed.** The plan's narrative no longer
contains the word "future" anywhere (verified by `grep
-iw 'future' plans/2026-05-07-process-bootstrap-plan.md`).
A19 reword: "in the event that
`remotes.origin.fetch-tags` is removed or its semantics
change in a subsequent jj release".

### M7 — A2 deliberate-violation probe lacks a cleanup gate

**Finding.** A2 step 3 creates
`GebLean/Utilities/_LintProbe.lean`, runs the linter, and
deletes the file. No commit-time gate confirms the file
is gone.

**Response: fixed.** A2 step 4 (commit) now contains an
explicit "confirm no `_LintProbe.lean` remains" check
before staging and committing.

### M8 — A28 merge-form ambiguity

**Finding.** A28 said "merge form is the user's choice
(merge commit or fast-forward)". Spec § Branch model says
"topic branches land via normal merge commits".

**Response: fixed.** A28 (now A29) wording tightened to
"the merge is a normal merge commit per spec § Branch
model" with no fast-forward fallback option. The
pre-cutover history exemption from append-only does not
apply to the merge that creates the cutover commit
itself.

## Cosmetic-taste

### C1 — Closed-decisions list duplicates the hand-off

**Finding.** The plan reproduces ~20 lines of closed
decisions verbatim from the hand-off prompt.

**Response: rejected (cosmetic-taste).** The reviewer
themselves marked this as "at most a cosmetic-taste
finding". The duplication exists as a defensive index for
the executor; the alternative (a one-line pointer) saves
~20 lines but loses the reader's ability to skim the
constraints without leaving the plan.

### C2 — Plan summary table cell width

**Finding.** Plan summary table's `notes` column rows are
wide.

**Response: rejected (cosmetic-taste).** Tables are
exempt from MD013 per `.markdownlint-cli2.jsonc`'s
`code_blocks: false, tables: false` configuration.
Splitting the column would interrupt the reader's
left-to-right scan without adding information.

## Convergence assessment

The cycle-1 fixes are material. One blocker, seven
serious, six minor findings were applied; one minor was
rejected (M1's narrative-vs-script-name distinction was
agreed); two cosmetic-taste findings rejected with
rationale the reviewer themselves agreed with.

Per the spec's "no fixed cycle cap; iterate until
convergence after material edits" rule, one further
fresh-context cycle is appropriate before resurfacing to
the user. Cycle 2 to be dispatched against the
post-cycle-1 plan.
