# T5 equivalence plan — adversarial review round 1

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings](#findings)
  - [S1 — Task 0 omits the spec-mandated §6.1 motive-elaboration stub](#s1--task-0-omits-the-spec-mandated-61-motive-elaboration-stub)
  - [M1 — Topic-branch tip identifier is stale](#m1--topic-branch-tip-identifier-is-stale)
  - [M2 — Task 0 omits `lake test` baseline](#m2--task-0-omits-lake-test-baseline)
  - [M3 — Fallback `lakefile.toml` mutation is under-specified](#m3--fallback-lakefiletoml-mutation-is-under-specified)
  - [M4 — Scratch-file location diverges from spec](#m4--scratch-file-location-diverges-from-spec)
  - [N1 — Step 6 references a "section appended in Step 5" but Step 5 emits a `namespace`](#n1--step-6-references-a-section-appended-in-step-5-but-step-5-emits-a-namespace)
  - [N2 — Umbrella `ErToKFunctor` bullet stale across T5.A.1 / T5.A.2 commits](#n2--umbrella-ertokfunctor-bullet-stale-across-t5a1--t5a2-commits)
  - [N3 — Task 2 Step 4 parenthetical char count is informational only](#n3--task-2-step-4-parenthetical-char-count-is-informational-only)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

Round-1 adversarial review of the T5 equivalence implementation
plan
([`2026-05-25-step-t5-equivalence-plan.md`](2026-05-25-step-t5-equivalence-plan.md))
against the 3-round-converged spec
([`2026-05-25-step-t5-equivalence-design.md`](../specs/2026-05-25-step-t5-equivalence-design.md)),
the existing source surface
(`GebLean/LawvereERKSim/ErToKFunctor.lean`,
`GebLean/LawvereKSimER.lean:336–571`,
`GebLean/LawvereKSimDCatInterp.lean`,
`GebLean/LawvereERInterp.lean`,
`GebLean/LawvereERKSim.lean`), mathlib
(`Mathlib/CategoryTheory/Equivalence.lean` under the project pin),
the project rules
(`CLAUDE.md`, `.claude/rules/lean-coding.md`,
`.claude/rules/markdown-writing.md`,
`.claude/rules/ci-and-workflow.md`,
`.claude/rules/fork-upstream-flow.md`), the axiom-check pipeline
(`scripts/check-axioms.sh`), and the four mathlib contribution
guides.

Verdict: PARTIAL — 0 blockers, 1 serious, 4 minor, 3 nits. The
plan implements every spec §4 declaration with full code, every
proof-shape transcription is faithful to spec §6, every command
respects the project's banned-form list, and every commit-message
subject conforms to the mathlib commit-style guide. The single
serious finding is a coverage gap in Task 0 (T5.0): the spec §5
explicitly enumerates three stub `example` blocks for T5.0
baseline verification (§6.3 proof shape, §6.7 instance form, and
§6.1 motive-elaboration shape), but the plan delivers only two
(§6.3 and §6.7). The §6.1 motive elaboration is precisely the
case the spec spends prose justifying as elaboration-fragile;
omitting it from T5.0 defeats the purpose of having T5.0 as a
fast-fail gate.

## Methodology

1. Read the plan end-to-end.
2. Read the spec end-to-end; cross-checked spec §4 (declarations)
   and spec §5 (steps) against plan tasks 0–5.
3. Read the existing source the plan modifies:
   - `GebLean/LawvereERKSim/ErToKFunctor.lean` (T4 surface),
   - `GebLean/LawvereKSimER.lean:336–571` (kToER mirror),
   - `GebLean/LawvereKSimDCatInterp.lean` (kInterpFunctor +
     `KMorNQuo.interp`),
   - `GebLean/LawvereERInterp.lean` (erInterpFunctor + faithful
     instance),
   - `GebLean/LawvereERKSim.lean` (umbrella).
4. Opened `Mathlib/CategoryTheory/Equivalence.lean` at the
   project pin and verified:
   - line 85: `structure Equivalence ... where mk' ::` — the raw
     constructor is `Equivalence.mk'`, confirmed;
   - the unitIso direction is `𝟭 C ≅ functor ⋙ inverse` (so
     supplying `erToKKToErIso.symm` is correct);
   - the counitIso direction is `inverse ⋙ functor ≅ 𝟭 D` (so
     supplying `kToErErToKIso` is correct);
   - line 99–101: the autoparam is
     `functor_unitIso_comp ... := by cat_disch`;
   - line 351: `protected def mk` is the smart constructor that
     replaces the unit via `adjointifyη η ε`;
   - lines 630 / 632: `Equivalence.isEquivalence_functor` and
     `Equivalence.isEquivalence_inverse` exist as named globals
     with the projection signatures the plan calls.
5. Read `scripts/check-axioms.sh`'s AXIOM_ALLOW scanning section
   (lines 214–269): the pattern
   `-- AXIOM_ALLOW: <axiom-name>` is matched on `--` comments
   immediately preceding the declaration (or inside its `/-- -/`
   docstring), with a blank-line break. The plan's AXIOM_ALLOW
   comment placement (immediately before the docstring) matches
   the existing convention used in
   `ErToKFunctor.lean` lines 55, 65, 73, 88, 116, 139.
6. Spot-checked each commit-message subject for compliance with
   `https://leanprover-community.github.io/contribute/commit.html`:
   imperative present tense, lowercase first letter after the
   scope prefix, no trailing period, ≤ 72 chars including prefix.
7. Cross-checked the module-docstring section order in plan
   Task 3 Step 1 against the spec's §3 closing paragraph and
   `.claude/rules/lean-coding.md` § Documentation.
8. Verified each task's `bash` block for:
   - No `lake env lean` (banned).
   - No `lake clean` (banned).
   - No bash process substitution `<(...)` / `>(...)`.
   - `jj commit -m` (not `jj describe @-`).
   - Bookmark advance via `jj bookmark move ... --to @-`.
   - `bash scripts/check-axioms.sh` invocation.
9. Inspected the live `feat/t5-equivalence` bookmark via
   `jj show feat/t5-equivalence` to verify the plan's claim about
   its commit ID.

## Findings

### S1 — Task 0 omits the spec-mandated §6.1 motive-elaboration stub

**Spec reference.** Spec §5 second-from-last paragraph:

> The stub contains: one `example` block implementing §6.3's
> proof shape against a placeholder pair of functors with the
> same interface as `erToKFunctor` / `kToERFunctor`; one
> `example` block instantiating §6.7's two explicit instance
> declarations against a placeholder `Equivalence` value; one
> `example` block for §6.1's `Quotient.inductionOn`
> motive-elaboration shape.

**Plan state.** Task 0 contains Step 3–4 (§6.3 stub) and
Step 5–6 (§6.7 stub). It contains no §6.1 stub.

**Why this matters.** Spec §6.1 itself spends a long paragraph
(spec lines 343–357) explaining why the lift function inside
the motive's `Quotient.liftOn` application is spelled out
explicitly rather than left as a second underscore:

> The reason for spelling out the lift function rather than
> leaving it as a second underscore: elaboration of two
> underscores in the motive's `Quotient.liftOn` application
> position can fail under the current pin (the engine cannot
> infer both the lift function and its well-definedness
> compatibility proof from the expected motive type alone).
> Spelling out the lift function unambiguously fixes the
> elaboration; T5.0 baseline verifies this.

The last sentence — "T5.0 baseline verifies this" — is the
contract that T5.0 must contain a stub exercising §6.1's
motive. Without that stub, the §6.1 fragility predicted by the
spec is not caught until Task 1 Step 3 attempts the real
theorem against the real `unfold erToKFunctor_map` goal, at
which point an elaboration failure forces a halt **after**
T5.A.1 begins rather than at T5.0 (the spec-intended
fast-fail boundary).

**Fix.** Add a Step 4.5 (or relabel) to Task 0 that:

1. Constructs an `example` block whose body opens with
   `unfold erToKFunctor_map`, then applies
   `refine Quotient.inductionOn (motive := ...) e ?_` with the
   spec's explicit lift-function spelled out (matching the form
   in spec §6.1 lines 304–315 / plan Task 1 Step 3 lines
   361–376), and discharges the remaining goal with
   `intro rec; sorry` (the body of the proof is irrelevant —
   only motive elaboration is being checked).
2. Type-checks the augmented buffer via the lean-lsp MCP.
3. Halts on failure with the same semantics as Steps 4 / 6.

Since this stub `unfold`s the real `erToKFunctor_map`, it
requires the same imports already present in plan Task 0
Step 3 (which includes `GebLean.LawvereERKSim.ErToKFunctor`)
— no new dependency.

The `sorry` inside an `example` in a stub buffer is acceptable
because the stub is never committed (per plan Task 0 Step 7);
the committed-code prohibition on `sorry` does not apply.

### M1 — Topic-branch tip identifier is stale

**Plan reference.** "Topic branch" section, line 73–75:

> All commits land on bookmark `feat/t5-equivalence` (already
> created and pointing at the spec convergence commit
> `75ecc025`).

**Actual state.** `jj show feat/t5-equivalence` reports
commit ID `b4e20d1af5575c294ba946c3b8c50310b1ddd6e9` (the plan-
writing commit, change `konznknx`, message
`docs(equivalence): write T5 implementation plan`). The
bookmark has already advanced past `75ecc025` to include the
plan commit itself.

**Why this matters.** The implementer who reads "pointing at
the spec convergence commit `75ecc025`" and then runs
`jj log -r feat/t5-equivalence` will see `b4e20d1a` and may
attempt to "fix" the bookmark, potentially destroying the plan
commit. The behaviour the plan intends is "start the next
implementation commit on top of whatever the bookmark currently
points to", which is what happens naturally.

**Fix.** Replace the parenthetical with a state-agnostic
statement, e.g. "already created; the implementer advances it
forward via `jj bookmark move feat/t5-equivalence --to @-`
after each commit". Drop the SHA reference.

### M2 — Task 0 omits `lake test` baseline

**Spec reference.** Spec §10's pre-commit checklist requires
`lake test` succeeds (item 5). Plan Task 0 runs `lake build`
(Step 1) and `bash scripts/check-axioms.sh` (Step 2) only.

**Why this matters.** A pre-existing test failure on the
T5.0 baseline (e.g., from any stale state on the topic branch)
would only surface during Task 5 Step 7's `lake test`. Task 0
exists precisely to make such failures surface before any
commit lands.

**Fix.** Add a Step 2.5 (or extend Step 2) to Task 0 to run
`lake test` and confirm success on the fresh baseline.

### M3 — Fallback `lakefile.toml` mutation is under-specified

**Plan reference.** Task 0 Step 4 fallback:

> Alternative if the MCP is unavailable: temporarily place the
> stub at `GebLean/Scratch/T5Stubs.lean` (creating the
> `Scratch/` directory if it does not exist), add it to a
> local `lakefile.toml` `lean_lib` target, run `lake build`,
> then delete the file and lakefile entry.

Task 0 Step 7 (clean-up) says:

> ```bash
> # manually revert the lakefile.toml lean_lib addition
> ```

**Why this matters.** "Add it to a local `lakefile.toml`
`lean_lib` target" is not a copy-pasteable instruction. The
project's `lakefile.toml` likely declares one or more
`lean_lib` blocks; "add to" could mean (a) extend an existing
target's `globs`, (b) add a new target, or (c) add a `roots`
entry. The plan does not bind to a specific shape, so two
implementers would produce different patches. Also, "manually
revert" risks leaving a residue under version control.

**Fix.** Either (i) commit to one specific lakefile edit (e.g.
a new `lean_lib` block with name `Scratch` and root
`Scratch.T5Stubs`, with literal text), or (ii) demote the
fallback to "use a temporary file path outside the project
tree and invoke `lake env lean` on it" — but this latter path
collides with the project's hard ban on `lake env lean`, so
(i) is the more workable instruction. Alternatively (iii) drop
the fallback entirely on the basis that the lean-lsp MCP is
assumed available in the SDD subagent's environment; if it
isn't, halt T5.0 and surface that as a tooling-pre-condition
issue rather than working around it inside the task.

### M4 — Scratch-file location diverges from spec

**Spec reference.** Spec §5 third bullet (operational
semantics):

> The stub lives in a scratch file at
> `/tmp/t5-equivalence-stubs.lean` (or equivalent), outside
> the committed Lean source tree.

**Plan reference.** Task 0 Step 4 fallback uses
`GebLean/Scratch/T5Stubs.lean`, *inside* the project tree.

**Why this matters.** The spec explicitly placed the stub
outside the project tree; the plan moves it inside. Both
choices are defensible (project-internal lets `lake build`
work without `lake env lean`; `/tmp` is closer to "this is
truly ephemeral"), but the divergence should be reconciled
either by amending the spec (a `.review-4.md` follow-up) or by
moving the plan back to `/tmp`. Note also that
`.claude/rules/lean-coding.md` § Lake / build workflow says
"place experiments inside the codebase, not under `/tmp`",
which favours the plan's choice — but this then makes the
spec text itself stale.

**Fix.** Either (i) align the plan with the spec by moving the
fallback to `/tmp` (and accept that the fallback path will
also need a non-lake build mechanism), or (ii) amend the spec
in a follow-up to match the plan's project-internal location
and cite `.claude/rules/lean-coding.md` § Lake / build
workflow as rationale.

### N1 — Step 6 references a "section appended in Step 5" but Step 5 emits a `namespace`

**Plan reference.** Task 0 Step 5 emits a snippet beginning
`namespace GebLean` and ending `end GebLean`, with a `section
InstanceStub` / `end InstanceStub` inside it. Task 0 Step 6
describes the buffer as "the §6.3 stub from Step 3 plus the
§6.7 section appended in Step 5".

**Why this matters.** Re-opening `namespace GebLean` is
permitted in Lean 4; the resulting buffer has two `namespace
GebLean ... end GebLean` blocks. This typechecks. The wording
nit is harmless to the build, but a careful implementer may
collapse the two `namespace GebLean` blocks into one for
tidiness and accidentally drop the second `end GebLean`,
producing a syntax error. The plan would benefit from saying
explicitly that the Step 5 snippet is appended **verbatim**
and produces two parallel `namespace GebLean` blocks (or:
have Step 5 omit the outer `namespace`/`end` markers, since
they are redundant with Step 3's).

**Fix.** Have Step 5 drop its `namespace GebLean ... end
GebLean` wrapper (the `section InstanceStub` is sufficient),
since it is appended into a buffer whose Step 3 already opens
the namespace.

### N2 — Umbrella `ErToKFunctor` bullet stale across T5.A.1 / T5.A.2 commits

**Plan reference.** Task 5 Step 5:

> (Replace the existing `ErToKFunctor` bullet body in
> place — add the two new sentence fragments about
> `erToKFunctor_map_interp` and `erToKFunctor_comp_kInterpFunctor`
> — and add the new `Equivalence` bullet after it.)

**Why this matters.** Between T5.A.1's commit (which adds
`erToKFunctor_map_interp`) and T5.C's commit (which updates
the umbrella bullet), the `ErToKFunctor` bullet in
`LawvereERKSim.lean` is stale (the new theorems exist but the
bullet does not mention them). Spec §10 *Umbrella update*
acknowledges this and routes the umbrella change through
T5.C, so the staleness is by design — but a reviewer who
inspects the T5.A.1 / T5.A.2 commits in isolation will see a
discrepancy. The plan should note this explicitly so that the
SDD subagent does not, on its own, decide to update the
umbrella in T5.A.1 (breaking the per-task scope discipline).

**Fix.** Add one sentence to plan Task 1 Step 6 (or to plan
"Topic branch" preamble): "The umbrella docstring's
`ErToKFunctor` bullet remains intentionally unchanged in
T5.A.1 / T5.A.2; the umbrella update rides on T5.C per
spec §10."

### N3 — Task 2 Step 4 parenthetical char count is informational only

**Plan reference.** Task 2 Step 4 ends:

> (Subject `add erToKFunctor_comp_kInterp` is 33 chars; with
> the `feat(ertok):` prefix plus separating space (13 chars),
> total 46 chars, well under the ≤ 72-char target.)

**Why this matters.** Informational commit-message arithmetic
in a checklist step is a small style nit: such inline
counting tends to drift out of sync if the subject is edited.
The figure is correct as of the current subject, and the
≤72-char constraint is the binding one. The plan would be
cleaner if this parenthetical were dropped (or moved to a
plan-level "Commit message conventions" preamble that simply
states the ≤72-char rule applies to all five commit
subjects). No correctness impact; recording for stylistic
hygiene only.

**Fix.** Drop the parenthetical, or move the convention to a
single preamble.

## Convergence verdict

PARTIAL — 0 blockers, 1 serious (S1), 4 minor (M1–M4), 3 nits
(N1–N3). Re-dispatch after addressing S1 (mandatory) and
M1–M4 (recommended). Nits N1–N3 are optional polish.

The plan is structurally sound: every spec §4 declaration has
a corresponding plan task with full code; every proof-shape
transcription matches spec §6; every command respects the
project's banned-form list; every commit-message subject
conforms to mathlib conventions and stays under 72 chars;
every AXIOM_ALLOW comment matches the spec §7 convention and
the `scripts/check-axioms.sh` scanning pattern; the mathlib
API name verification (`Equivalence.mk'`,
`isEquivalence_functor`, `isEquivalence_inverse`, the
`unitIso` / `counitIso` directions) was redone at this round
against `Mathlib/CategoryTheory/Equivalence.lean` at the
project's current pin, with no surprises. The single serious
finding (S1) is a strict spec-coverage gap that defeats the
fast-fail purpose of T5.0; the minor findings are
cross-document staleness (M1, M4), a missed baseline check
(M2), and an under-specified fallback path (M3).
