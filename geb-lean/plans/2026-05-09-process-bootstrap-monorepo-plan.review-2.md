# geb-lean process-bootstrap plan — adversarial review cycle 2

**Reviewer**: fresh-context agent (Claude Sonnet 4.6).
**Artefact reviewed**:
`plans/2026-05-09-process-bootstrap-monorepo-plan.md`.
**Spec cross-checked against**:
`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`.

---

## Finding B-1 — Blocker

**Location**: Task A4, Step 2 (resolve `<SHA>` placeholder).

**Description**: The workflow template in A4 Step 1 uses the placeholder
`actions/checkout@<SHA>` (angle-bracket `<SHA>`, no dash). The grep
assertion in Step 2 tests for `'<SHA-'` (with a trailing dash):

```sh
! grep -n '<SHA-' ../.github/workflows/markdown-lint.yml
```

The pattern `'<SHA-'` does not match `'<SHA>'`. The command
exits 0 (no match found) even when the placeholder is still present
in the file. An implementer following the steps would receive a false
green and commit an unresolved SHA into the workflow.

**Fix**: change the grep pattern to `'<SHA>'` (or `'<SHA[->]'` if the
intent is to catch both forms).

---

## Finding S-1 — Serious

**Location**: Spec § CI changes vs. Task A4 Step 1 template.

**Description**: The spec states: "This workflow contains no third-party
`uses:` action references; both steps are `run:` steps." The plan's A4
template includes a third step `- uses: actions/checkout@<SHA>` before
the two `run:` steps. The spec's yaml code block shows only the two
`run:` steps without the checkout step.

Without `actions/checkout`, the working tree would not be present in
the runner and `markdownlint-cli2` would fail to find any files. The
plan's template is therefore functionally correct in adding the
checkout step, but the spec's description is incorrect (it says "both
steps are `run:` steps"; there are actually three steps).

An implementer who reads the spec's statement ("both steps are `run:`
steps") could delete the checkout step from the plan's template or flag
the plan as a spec deviation, breaking CI.

**Fix**: the spec should be corrected; alternatively the plan should
note the deviation explicitly ("the spec's prose omits the required
`actions/checkout` step; the template here is authoritative").

---

## Finding M-1 — Minor

**Location**: Task A27, Verification step (c).

**Description**: Step (c) reads "Re-run the five A10 smoke-test cases
to confirm the hook fires correctly via the wired settings." Task A10
covers `check-signing-key.sh` and does not define the five
smoke-test cases. The five JSON-stdin smoke-test cases for
`block-mutating-git.sh` are defined in Task A9, not A10.

The A28 verification checklist (item 12) correctly references Task A9:
"re-run five A9 cases." The A27 reference is inconsistent.

**Fix**: change "A10 smoke-test cases" to "A9 smoke-test cases" in A27
verification step (c).

---

## Finding M-2 — Minor

**Location**: Task B6, Step 1.

**Description**: B6 Step 1 reads "Items B1 through B7 (per spec
§ Milestone B), with status for each." The plan's Milestone B tasks
are numbered B1 through B6 (the plan's B5 covers the axiom-check flip,
which is spec item B7; the plan's B3 covers the harness reset, which
is spec item B5). Directing the implementer to compile a "B1 through
B7" report is inconsistent with the plan's own task numbering.

**Fix**: either map each spec item to its plan-task equivalent in B6
Step 1, or say "all Milestone B items (plan tasks B1–B6, corresponding
to spec items B1–B7)".

---

## Finding M-3 — Minor

**Location**: Tasks B1 Step 3 and B4 Step 2 (jj commit workflow).

**Description**: Both tasks create a jj commit via `jj new -r main`
followed by `jj describe -m "..."`, then state "The push is
user-direct." Neither task creates a bookmark (no `jj bookmark create`
command). Without a named bookmark, the user cannot push the commit
via `jj git push --remote origin -b <name>`. The commit would be an
anonymous revision with no push target.

Task B2 entry 6 correctly creates a per-entry bookmark. Tasks B1 and
B4 omit this step.

**Fix**: add `jj bookmark create <name> -r @` after each `jj describe`
in B1 Step 3 and B4 Step 2, and name the bookmark in each task
(e.g., `docs/session-milestone-a-note` for B1;
`chore/session-retire` for B4).

---

## Summary

| Severity | Count | Top item |
| --- | --- | --- |
| Blocker | 1 | A4 Step 2 grep pattern `'<SHA-'` does not match `'<SHA>'` |
| Serious | 1 | Spec says "both steps are `run:` steps" but plan correctly adds `actions/checkout`; spec/plan divergence |
| Minor | 3 | A27 verification (c) wrong task reference (A10 → A9); B6 uses spec item numbers (B1–B7) not plan task numbers (B1–B6); B1/B4 omit bookmark creation for user-direct push |
| Cosmetic-taste | 0 | — |
