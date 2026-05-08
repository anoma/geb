# Adversarial review cycle 2 — author responses (plan)

Review dispatched: fresh-context Agent against the
post-cycle-1 plan. Cycle-1 fixes verified in
`plan.review-1.md`. **Reviewer's executive summary**:
*"The cycle-1 fixes are largely applied correctly ...
However, the new A26 conflict-probe procedure is
structurally broken (writes to /tmp/, never modifies a
tracked file, so produces no conflict), B4 step 2
dangerously mixes a denied command and the correct command
in a way an executor could misread, and pre-push.sh's
smoke test (A25 step 3) inherits a spec-level tension
between report-only `check-axioms.sh` and the requirement
that pre-push exit 0."*

## Blocker

### B-new-1 — A26 manufactures no conflict (writes to `/tmp/`)

**Finding.** Task A26's shell commands wrote `echo 'A' >
/tmp/conflict-probe-a.md` and `echo 'B' >
/tmp/conflict-probe-a.md`. `/tmp/` is outside the jj
working copy, so the two `jj describe` invocations
produced empty revisions; the subsequent `jj rebase`
produced no conflict.

**Response: fixed.** A26 step 1 rewritten to use a
tracked in-repo probe file
(`docs/.conflict-probe-a.md`, fresh tracked file under
the existing `docs/` directory). The two divergent
revisions write `'A'` and `'B'` into the same in-repo
path; `jj st` confirms each revision sees the change;
the rebase manufactures a real conflict. Step 5
(clean-up) deletes the probe file as part of the final
working copy.

## Serious

### S-new-1 — B4 step 2 mixes denied and allowed commands in one runnable block

**Finding.** The shell block read `jj new -r main` then
`git rm -rf .session/   # rejected by hook; use the
next form instead`. An automation copy-pasting the
block would attempt the denied form before reading the
prose comment.

**Response: fixed.** The denied form is removed from any
runnable code block. The narrative now reads:

> The raw `git rm -rf .session/` form is denied by the
> `block-mutating-git` hook; use the working-copy form
> recognised by jj instead.

followed by a single shell block containing only the
allowed form. There is no executable copy-paste hazard.

### S-new-2 — pre-push.sh exit-0 expectation vs. check-axioms.sh

**Finding.** A7 step 4 documents that `check-axioms.sh`
"may list many flagged declarations because mathlib
transitively introduces `Classical.choice`." A25 step 3
asserts pre-push.sh "exits 0 if every step passes." If
`check-axioms.sh` exits non-zero on findings (which the
spec implies — the script "fails unless every flagged
declaration has either an `AXIOM_ALLOW` comment or no
axiom dependency outside the allowlist"), pre-push.sh
deterministically fails until Milestone B.

The spec § CI changes resolves this for CI by running
the job in "report-only mode": the workflow ignores the
script's exit code and uploads the output as an
artefact. The spec § Auxiliary scripts (pre-push.sh)
does not specify the same suppression for pre-push.

**Response: fixed.** Resolved at the plan level (no spec
amendment needed) by treating pre-push.sh's
axiom-check invocation as informational pre-Milestone-B,
mirroring the CI report-only mode:

```sh
bash scripts/check-axioms.sh GebLean/ test/ || true
```

The `|| true` suffix is dropped at Milestone B item B5
(axiom_check fail-mode flip), at which point pre-push.sh
gates on the exit code in step with CI. A25 step 1 now
documents this suppression and the B5-flip plan; B5 step
2 has a corresponding edit to pre-push.sh recorded.

This is consistent with the spec's overall intent: the
axiom-check is informational repository-wide until
B5, then becomes load-bearing.

## Minor

### M-new-1 — Sequence-dependency narrative omits A31 for A32

**Finding.** Plan summary said "A30 precedes A32 ...
though the technical dependency is only on A29". A32's
`Depends on:` line names `A29, A31`. The narrative
omitted A31.

**Response: fixed.** Plan summary updated to read:

> A32's technical dependencies are A29 and A31. A32 is
> placed after A33's prerequisites for ordering
> coherence, not because of an additional technical
> dependency on A30 itself.

### M-new-2 — A26 cleanup combines `--bookmark X --deleted`

**Finding.** In jj 0.41, `--deleted` pushes all locally
deleted bookmarks without taking explicit
`--bookmark` arguments. Combining is redundant (and
under some readings of the docs, an error rather than a
no-op).

**Response: fixed.** A26 step 5 simplified to a single
form that pushes both deletions explicitly:

```sh
jj git push --remote origin --deleted
```

Since steps prior have run `jj bookmark delete` on both
probe bookmarks, `--deleted` covers both. The
double-`--bookmark` form is removed.

### M-new-3 — A13 placeholder grep is vacuous

**Finding.** A13 step 1 says "use it verbatim" (no
placeholder mentioned), so the step-3 grep
`! grep -n '<SHA-' ...` cannot fail on the executor's
own output. The check adds no enforcement.

**Response: fixed.** A13's step 3 placeholder check is
removed. Step 1 retains the SHA-pinning instruction;
A4 retains its placeholder-check (since A4's authoring
template literally uses `<SHA-N>` placeholders that
must be resolved). The asymmetry between A4 and A13 is
intentional and recorded in A13's step 1 prose.

## Cosmetic-taste

None new.

## Convergence assessment

The cycle-2 fixes are material: one blocker (the
conflict-probe didn't manufacture a conflict, which would
have invalidated the spec's `private-commits = "conflicts()"`
verification), two serious findings, three minor. All
addressed.

Per the spec's "no fixed cycle cap; iterate until
convergence after material edits" rule, one further
fresh-context cycle is appropriate to confirm the
cycle-2 fixes are clean.

Cycle 3 to be dispatched against the post-cycle-2 plan.
