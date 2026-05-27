# Post-T4 handoff — T4 landing summary + T5 brainstorming

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Where we are](#where-we-are)
- [T4 actually-landed surface](#t4-actually-landed-surface)
- [T5 scope (the final equivalence-packaging phase)](#t5-scope-the-final-equivalence-packaging-phase)
  - [T5-A — Two small named-composite tasks (warm-up)](#t5-a--two-small-named-composite-tasks-warm-up)
  - [T5-B — Natural isomorphisms](#t5-b--natural-isomorphisms)
  - [T5-C — Equivalence packaging](#t5-c--equivalence-packaging)
- [Policy decisions to carry forward](#policy-decisions-to-carry-forward)
- [T4 axiom hygiene](#t4-axiom-hygiene)
- [Known T4 follow-ups (low priority; not blocking T5)](#known-t4-follow-ups-low-priority-not-blocking-t5)
- [Workflow](#workflow)
  - [Step A — Brainstorming + spec writing](#step-a--brainstorming--spec-writing)
  - [Step B — Spec adversarial review to convergence](#step-b--spec-adversarial-review-to-convergence)
  - [Step C — User reviews spec](#step-c--user-reviews-spec)
  - [Step D — Plan writing](#step-d--plan-writing)
  - [Step E — Plan adversarial review to convergence](#step-e--plan-adversarial-review-to-convergence)
  - [Step F — User reviews plan](#step-f--user-reviews-plan)
  - [Step G — Implementation via subagent-driven development](#step-g--implementation-via-subagent-driven-development)
- [Operational rules (carry forward from T4)](#operational-rules-carry-forward-from-t4)
- [Resumption prompt](#resumption-prompt)
- [References](#references)

<!-- END doctoc -->

Handoff for the next and final workstream of the ER ↔ K^sim_2
equivalence project. T4 (runtime bound, `erToK` assembly, and
`erToKFunctor`) merged to `main@origin` via PR #201. The
forward functor `erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat
2` is now landed alongside the previously-landed
`kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat`. T5 packages
the categorical equivalence
`LawvereERCat ≌ LawvereKSimDCat 2`.

## Where we are

The ER ↔ K^sim_2 categorical equivalence project decomposes
into a forward direction (`kToER`, complete), a reverse
direction (`erToK`, complete), and a final equivalence
packaging (T5, pending). Status at 2026-05-25:

| Workstream | Description | Status |
| --- | --- | --- |
| kToER (Steps 0–5) | Structural-induction proof of `K^sim_2 ⊆ ER` plus `kToERFunctor` | Complete |
| T1 (≈ Step 7) | URM kernel `GebLean/Utilities/ZeroTestURM.lean` | Complete |
| T2 (≈ Steps 6+8) | ER → URM compiler + `compileER_runFor` in `GebLean/LawvereERKSim/` | Complete |
| Followup #654 | Deferred cleanups (naming, refactor, private re-evaluation) | Partial (sub-tasks A–F, M, N complete; G–L pending) |
| T3 (≈ Step 9) | K^sim simulator (`simulate` + `simulate_interp` + `simulate_level`) | Complete |
| T4 (Step 10) | Runtime bound + `erToK` assembly + `erToKFunctor` | Complete (PR #201) |
| T5 (Step 11) | Strict equivalence `LawvereERCat ≌ LawvereKSimDCat 2` | Pending |

Binding documents for the landed work:

- Master research design:
  [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md).
- Master ER-to-K spec (T1 + T2 + T3 + T4):
  [`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](../specs/2026-05-16-er-to-k-via-cslib-urm-design.md).
- T2 plan:
  [`docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`](2026-05-17-step-t2-er-to-urm-compiler.md).
- T3 spec (4-round adversarial-converged):
  [`docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md).
- T3 plan (9-round adversarial-converged):
  [`docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).
- T4 spec (5-round adversarial-converged):
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../specs/2026-05-22-step-t4-runtime-bound-design.md).
- T4 plan (5-round adversarial-converged):
  [`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](2026-05-22-step-t4-runtime-bound-plan.md).
- Post-T3 handoff:
  [`docs/superpowers/plans/2026-05-22-post-t3-handoff.md`](2026-05-22-post-t3-handoff.md).
- T4 Tasks 5–8 handoff (historical, in-T4):
  [`docs/superpowers/plans/2026-05-23-step-t4-tasks-5-8-handoff.md`](2026-05-23-step-t4-tasks-5-8-handoff.md).
- T4 Tasks 9–15 handoff (historical, in-T4):
  [`docs/superpowers/plans/2026-05-23-step-t4-tasks-9-15-handoff.md`](2026-05-23-step-t4-tasks-9-15-handoff.md).

## T4 actually-landed surface

Public T4 surface available for T5 consumption (all under
`namespace GebLean`):

| Declaration | Location | Type / role |
| --- | --- | --- |
| `boundExprKParams` | `GebLean/LawvereERKSim/RuntimeBound.lean` | `{a : ℕ} → ERMor1 a → ℕ × ℕ`; per-ER-constructor recipe returning `(mu_e, offset_e)`. |
| `boundExprKParams_dominates` | `RuntimeBound.lean` | Joint runtime+value bound (AXIOM_ALLOW: Classical.choice). |
| `boundExprK` | `RuntimeBound.lean` | `{a : ℕ} → ERMor1 a → KMor1 a`; level ≤ 2 K-morphism whose interp is `tower mu_e (Fin.maxOfNat _ v + offset_e)`. |
| `boundExprK_level`, `boundExprK_interp`, `boundExprK_dominates` | `RuntimeBound.lean` | Level bound, closed-form interp, runtime domination. |
| `erToK` | `GebLean/LawvereERKSim/ErToK.lean` | `{a : ℕ} → ERMor1 a → KMor1 a`; single-output translator. |
| `erToK_level`, `erToK_interp` | `ErToK.lean` | Level ≤ 2 and interp-faithfulness (both AXIOM_ALLOW: Classical.choice via `simulate_*`). |
| `erToKN` | `GebLean/LawvereERKSim/ErToKFunctor.lean` | `{n m : ℕ} → ERMorN n m → KMorN n m`; multi-output extension. |
| `erToKN_interp`, `erToKN_level`, `erToKN_compat_extEq` | `ErToKFunctor.lean` | Componentwise interp / level lemmas and ext-eq compatibility (AXIOM_ALLOW). |
| `erToKFunctor_map` | `ErToKFunctor.lean` | `{n m : ℕ} → ERMorNQuo n m → KSimMor 2 n m`; quotient lift via `Quotient.liftOn` (AXIOM_ALLOW). |
| `erToKFunctor_map_id`, `erToKFunctor_map_comp` | `ErToKFunctor.lean` | Functor laws (AXIOM_ALLOW). |
| `erToKFunctor` | `ErToKFunctor.lean` | `CategoryTheory.Functor LawvereERCat (LawvereKSimDCat 2)`; the assembled functor. |

`erToK_interp` is the central interp-faithfulness theorem at
the raw-`KMor1` level: `(erToK e).interp v = e.interp v`. Its
quotient-level and functor-level companions (see
[T5-A](#t5-a--two-small-named-composite-tasks-warm-up)) are
intentionally not part of T4 — they belong at the start of T5.

T4 absorbed the original step decomposition's separate "T4
runtime bound" and "T5 `erToK` assembly + functor" phases. The
master ER-to-K spec's §11 step decomposition has been
re-numbered to reflect this.

## T5 scope (the final equivalence-packaging phase)

T5 packages the categorical equivalence
`LawvereERCat ≌ LawvereKSimDCat 2`. It consists of three
sub-phases:

### T5-A — Two small named-composite tasks (warm-up)

Per the project's bottom-up named-composite discipline
(`.claude/rules/lean-coding.md` § Bottom-up named-composite
discipline for categorical equivalences), the equivalence
cannot be built without first having both functors' interp
preservation theorems available as named composites at both
the quotient and functor levels. The K → ER direction landed
these in `LawvereKSimER.lean:488` (`kToERFunctor_map_interp`)
and `:538` (`kToERFunctor_comp_erInterpFunctor`) during the
original kToER work. T4 did not produce the ER → K
counterparts, because they are equivalence-prerequisites, not
runtime-bound concerns. T5 begins by closing this asymmetry:

1. **`erToKFunctor_map_interp`** (≈ 15 Lean lines): quotient-
   level interp preservation
   `(erToKFunctor_map e).hom.interp = e.interp` for every
   `e : ERMorNQuo n m`. Proof shape: `Quotient.inductionOn` on
   the ER quotient witness, reducing via `funext` and
   `erToKN_interp` to extensional equality of the underlying
   per-slot interps. Mirror:
   `kToERFunctor_map_interp` at `LawvereKSimER.lean:488–520`.

2. **`erToKFunctor_comp_kInterpFunctor`** (≈ 10 Lean lines):
   functor-level strict equality
   `erToKFunctor ⋙ kInterpFunctor = erInterpFunctor`. Proof
   shape: `CategoryTheory.Functor.ext` with object identity
   by `rfl` and morphism equality discharged by
   `erToKFunctor_map_interp` per the mirror at
   `LawvereKSimER.lean:538–547`.

These two tasks should land before T5-B begins.

### T5-B — Natural isomorphisms

Strict natural isomorphisms in both directions:

- `kToErErToKIso : kToERFunctor ⋙ erToKFunctor ≅ 𝟙 (LawvereKSimDCat 2)`
- `erToKKToErIso : erToKFunctor ⋙ kToERFunctor ≅ 𝟙 LawvereERCat`

Both are natural isomorphisms of functors `C ⥤ C` whose
component at object `n` is the identity of `n` (since
`erToKFunctor.obj n = n` and `kToERFunctor.obj n = n` both
hold by `rfl`). The morphism-level naturality squares reduce
via `erToK_interp` and the existing `kToER_interp` (plus the
T5-A interp-preservation lemmas) to equality of the
round-tripped morphism classes — both sides agreeing on every
context.

The spec phase will need to decide whether to express these
as `Iso` objects, `IsIso` instances, or both, and whether to
state naturality squares first as separate `@[simp]` lemmas
or directly inside the iso construction.

### T5-C — Equivalence packaging

The packaged
`erToKKToErEquivalence : LawvereERCat ≌ LawvereKSimDCat 2`
(or analogous name) assembling T5-B's two isomorphisms into a
`CategoryTheory.Equivalence`. The `unitIso` and `counitIso`
slots draw from T5-B; the `functor_unitIso_comp` triangle
identity is the remaining proof obligation.

This is the categorical-equivalence statement of Tourlakis
2018 Corollary 0.1.0.44 at `n = 2`, the headline result the
project has been building toward.

## Policy decisions to carry forward

From T3 and T4, two static-analysis policy decisions remain
in effect:

1. **Constructive `KMor1.level`** — the level function uses
   `Fin.maxOfNat` over `Finset.univ.sup` to keep level
   computation `Classical.choice`-free outside the
   accepted `Fin.lastCases_castSucc` exception.
   [`.claude/rules/lean-coding.md`](../../../.claude/rules/lean-coding.md) §
   Accepted exceptions.

2. **AXIOM_ALLOW: Classical.choice** — declarations whose
   proofs route through mathlib's `Fin.lastCases_castSucc`
   (typically via `Fin.cons`/`Fin.tail` simp normalisations
   in proofs about `simulate_interp`, `simulate_level`, and
   downstream consumers like `erToK_interp`) carry an
   explicit `-- AXIOM_ALLOW: Classical.choice (rationale)`
   comment immediately above the declaration. The
   `scripts/check-axioms.sh` audit recognises and suppresses
   these from the failure output. T5 will inherit this
   suppression on declarations transitively depending on
   `erToK_interp`.

## T4 axiom hygiene

Across the three T4 modules:

| File | Declarations | AXIOM_ALLOW required |
| --- | --- | --- |
| `RuntimeBound.lean` | 6 public | 1 (`boundExprKParams_dominates`) |
| `ErToK.lean` | 3 | 2 (`erToK_level`, `erToK_interp`) |
| `ErToKFunctor.lean` | 8 | 6 (every `erToKN_*` / `erToKFunctor*` except the `def`s) |

`scripts/check-axioms.sh` reports clean envelope `[propext,
Quot.sound]` after the AXIOM_ALLOW suppressions. T5 will
inherit Classical.choice on every declaration that calls
through `erToK_interp` or any of the `erToKN_*` /
`erToKFunctor_map_*` lemmas. Plan accordingly.

## Known T4 follow-ups (low priority; not blocking T5)

The T4 holistic review surfaced one defer-OK refactoring
candidate:

- **`bsum`/`bprod` context-domination boilerplate.** Two
  nearly identical scaffolds (~200 LOC duplication) inside
  `boundExprKParams_dominates`'s `bsum` and `bprod` cases.
  Belongs on follow-up branch #654 per the one-concern-per-
  branch rule; existing sub-tasks G–L on that branch already
  cover related refactoring of the T2 bsum/bprod scaffolds.
  T5 does not depend on this.

## Workflow

The full T5 workflow follows the project's standard
spec-then-plan-then-implement cycle. Each phase is gated by
adversarial review to convergence and explicit user review.

### Step A — Brainstorming + spec writing

**Skills**: `superpowers:brainstorming` (always-on for any
creative work) combined with `sequential-thinking` for
careful design reasoning.

**Goal**: produce a T5 design spec at
`docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`
covering all three sub-phases (T5-A, T5-B, T5-C). The spec
must commit to: declaration names and signatures; the proof
shape for each obligation (with reference to the kToER mirror
when applicable); axiom budget per declaration; the file
layout (likely a new `GebLean/LawvereERKSim/Equivalence.lean`
or splitting across two files); test plan if any
runtime-evaluable `#guard`s remain viable at this layer;
scope guardrails identifying what is and is not in T5.

**Inputs** (binding for T5 brainstorming):

- This handoff document.
- T4 spec at
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../specs/2026-05-22-step-t4-runtime-bound-design.md)
  — for the actually-landed shape of T4's surface.
- T4 plan at
  [`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](2026-05-22-step-t4-runtime-bound-plan.md)
  — for patterns surfaced during T4 execution.
- T4 landing surface (see [T4 actually-landed
  surface](#t4-actually-landed-surface) above).
- Mirror code: `GebLean/LawvereKSimER.lean` lines 336–571,
  especially `kToERN`, `kToERN_compat_extEq`,
  `kToERFunctor_map_interp` (line 488),
  `kToERFunctor_comp_erInterpFunctor` (line 538).
- The two interp functors: `kInterpFunctor` at
  `GebLean/LawvereKSimDCatInterp.lean:67–79`,
  `erInterpFunctor` at `GebLean/LawvereERInterp.lean` (search
  for the `Functor` declaration).
- Master research design's §11 categorical-iso framing:
  [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md).
- Master ER-to-K spec's §11 (categorical iso) forward-looking
  content; carry over what still applies.
- The project's bottom-up named-composite discipline rule in
  [`.claude/rules/lean-coding.md`](../../../.claude/rules/lean-coding.md).
- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.44 (the
  equivalence statement).

Begin by reading these inputs end-to-end, then invoke
`superpowers:brainstorming` and work through the design with
the user one question at a time. Do not draft Lean code at
this stage; the spec is the deliverable. The note about the
two T5-A named-composite tasks at the *beginning* of the
implementation should appear in the spec's step decomposition
and scope sections.

### Step B — Spec adversarial review to convergence

Per `docs/process.md` § Adversarial review: dispatch
fresh-context `Agent` reviewers in rounds, capturing each
round's findings in
`docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.review-N.md`.
Apply fixes between rounds. Continue until a round reports
zero blockers and zero serious findings (the standard
convergence gate). Expect 3–5 rounds based on T1–T4
precedent.

The adversarial review must check: (1) the four mathlib
upstream guides (commit, style, naming, doc) are honoured;
(2) every named construction has a citation; (3) the spec
matches the actually-landed T4 surface (no stale type names
or signatures); (4) the proof shapes for T5-A/B/C are
sound (per the mirror), with explicit failure modes
identified.

### Step C — User reviews spec

Hand the converged spec to the user for review. Apply any
follow-up edits requested. Only proceed to plan-writing once
the user has explicitly approved the spec.

### Step D — Plan writing

**Skill**: `superpowers:writing-plans`.

Produce a T5 implementation plan at
`docs/superpowers/plans/2026-05-25-step-t5-equivalence-plan.md`
breaking T5 into discrete tasks suitable for
`superpowers:subagent-driven-development` dispatch. Each task
must be ≤ 200 LOC of Lean and have a clear binding spec
section.

T5-A's two named-composite tasks should be Tasks 1 and 2 of
the plan (immediately after Task 0 baseline verification).
T5-B's natural-isomorphism work follows as Tasks 3–N.
T5-C's equivalence assembly is the final task(s).

### Step E — Plan adversarial review to convergence

Mirror Step B's process at the plan level. Capture
`.review-N.md` files; apply fixes; reach zero-blocker /
zero-serious convergence.

### Step F — User reviews plan

Hand the converged plan to the user. Apply follow-up edits.
Only proceed to implementation once the user explicitly
approves the plan.

### Step G — Implementation via subagent-driven development

**Skill**: `superpowers:subagent-driven-development`.

Execute the plan task-by-task per the SDD protocol:

1. Dispatch one focused implementer subagent per task,
   providing the full task text plus the binding spec
   section.
2. After each implementer reports DONE, dispatch the
   spec-compliance reviewer and the code-quality reviewer in
   sequence (or combined for small tasks).
3. Apply reviewer feedback; re-dispatch as needed.
4. Commit per-task on the topic branch via `jj commit -m`.
5. After all tasks land, dispatch a fresh-context holistic
   final code reviewer over the full T5 diff.
6. Apply final review fixes; close T5; hand off to the user
   for the PR-creation phase.

Use `jj commit -m` (not `jj describe @-`) — the latter is
error-prone when @ is non-empty. The T4 execution session
documented this pitfall.

## Operational rules (carry forward from T4)

- **Working directory**: `/home/terence/git-workspaces/geb/geb-lean`.
- **No `jj git push` without user line-by-line review**.
- **No raw mutating `git` subcommands** (use `jj`).
- **Build with `lake build`. Never `lake env lean`. Never
  `lake clean`.**
- **Avoid bash process substitution `<(...)`/`>(...)`** (they
  trigger manual approval prompts).
- **Markdown lint clean**: run `markdownlint-cli2` on any
  `.md` files touched before committing.
- **doctoc regeneration** on any `.md` with more than one
  `##` heading.
- **Topic branch per concern**: keep T5 on a single topic
  branch (e.g. `feat/equivalence` or `feat/t5-equivalence`);
  refactoring discovered during T5 goes to a separate
  branch.
- **No noncomputable; minimise Classical.choice** to the
  `Fin.lastCases_castSucc` AXIOM_ALLOW exception.
- **Subagent dispatch** is mandatory for each implementation
  task per the SDD plan.

## Resumption prompt

Paste this verbatim into the next Claude Code session:

```text
Begin T5 — the final phase of the ER ↔ K^sim_2 equivalence
project. T5 packages the categorical equivalence
LawvereERCat ≌ LawvereKSimDCat 2 from the now-landed
erToKFunctor (T4) and kToERFunctor (kToER work).

Read the post-T4 handoff first:

  docs/superpowers/plans/2026-05-25-post-t4-handoff.md

That document is the binding handoff. It contains: the
landed T4 surface, the T5 scope split into three sub-phases
(T5-A two small named-composite tasks, T5-B natural
isomorphisms, T5-C equivalence packaging), the binding
inputs, the policy decisions to carry forward, and the
operational rules.

The workflow proceeds in the project's standard
spec-then-plan-then-implement cycle, gated by adversarial
review and explicit user review at each phase:

  Step A — Spec writing via superpowers:brainstorming +
           sequential-thinking. Output:
           docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md.
  Step B — Spec adversarial review to convergence (fresh-
           context Agent rounds; capture .review-N.md files;
           apply fixes; expect 3–5 rounds).
  Step C — User reviews spec.
  Step D — Plan writing via superpowers:writing-plans.
           Output:
           docs/superpowers/plans/2026-05-25-step-t5-equivalence-plan.md.
           T5-A's two named-composite tasks
           (erToKFunctor_map_interp and
           erToKFunctor_comp_kInterpFunctor) are the first
           tasks of the plan, immediately after the baseline
           verification task.
  Step E — Plan adversarial review to convergence.
  Step F — User reviews plan.
  Step G — Implementation via
           superpowers:subagent-driven-development. One
           focused implementer subagent per task, followed by
           spec-compliance and code-quality reviewers; commit
           per-task via `jj commit -m`; after all tasks land,
           dispatch a holistic final review over the full T5
           diff.

Start with Step A. Begin by reading the handoff document and
the binding inputs it lists, then invoke
superpowers:brainstorming and work through the T5 design
with the user one question at a time. Do not draft Lean code
at this stage; the spec is the deliverable.

Operational rules (carry forward from T4):
  - Working directory: /home/terence/git-workspaces/geb/geb-lean
  - Build with `lake build` only.
  - No `jj git push` without user line-by-line review.
  - No raw mutating `git` subcommands.
  - Markdown lint clean before commits touching .md files.
  - Avoid bash process substitution.
  - `jj commit -m` for the per-task commit pattern (not
    `jj describe @-`).
```

## References

- T4 spec:
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../specs/2026-05-22-step-t4-runtime-bound-design.md).
- T4 plan:
  [`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](2026-05-22-step-t4-runtime-bound-plan.md).
- T4 Tasks 5–8 handoff:
  [`docs/superpowers/plans/2026-05-23-step-t4-tasks-5-8-handoff.md`](2026-05-23-step-t4-tasks-5-8-handoff.md).
- T4 Tasks 9–15 handoff:
  [`docs/superpowers/plans/2026-05-23-step-t4-tasks-9-15-handoff.md`](2026-05-23-step-t4-tasks-9-15-handoff.md).
- Master ER-to-K spec (updated 2026-05-25):
  [`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](../specs/2026-05-16-er-to-k-via-cslib-urm-design.md).
- Master research design:
  [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md).
- Post-T3 handoff (the structural precedent for this
  document):
  [`docs/superpowers/plans/2026-05-22-post-t3-handoff.md`](2026-05-22-post-t3-handoff.md).
- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.44:
  `.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`.
