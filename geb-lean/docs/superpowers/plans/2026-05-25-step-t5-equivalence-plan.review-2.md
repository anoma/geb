# T5 equivalence plan — adversarial review round 2

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings — round-1 status](#findings--round-1-status)
  - [S1 — RESOLVED in placement; NEW BLOCKER B1 surfaced by the stub itself](#s1--resolved-in-placement-new-blocker-b1-surfaced-by-the-stub-itself)
  - [M1 — RESOLVED](#m1--resolved)
  - [M2 — RESOLVED](#m2--resolved)
  - [M3 — RESOLVED in prose; residual inconsistency M3'](#m3--resolved-in-prose-residual-inconsistency-m3)
  - [M4 — RESOLVED in prose; residual inconsistency M3'](#m4--resolved-in-prose-residual-inconsistency-m3)
  - [N1 — RESOLVED](#n1--resolved)
  - [N2 — RESOLVED](#n2--resolved)
  - [N3 — RESOLVED](#n3--resolved)
- [New findings](#new-findings)
  - [B1 — §6.1 motive anonymous-constructor needs explicit type ascription](#b1--61-motive-anonymous-constructor-needs-explicit-type-ascription)
  - [B2 — §6.3 proof-shape stub does not elaborate under the current pin](#b2--63-proof-shape-stub-does-not-elaborate-under-the-current-pin)
  - [M3' — Task 0 "Files:" still describes the now-removed fallback](#m3--task-0-files-still-describes-the-now-removed-fallback)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

Round-2 adversarial review of the revised T5 equivalence
implementation plan
([`2026-05-25-step-t5-equivalence-plan.md`](2026-05-25-step-t5-equivalence-plan.md))
against the 3-round-converged spec
([`2026-05-25-step-t5-equivalence-design.md`](../specs/2026-05-25-step-t5-equivalence-design.md))
and the round-1 review
([`2026-05-25-step-t5-equivalence-plan.review-1.md`](2026-05-25-step-t5-equivalence-plan.review-1.md)).

Verdict: BLOCK — 2 blockers, 0 serious, 1 minor, 0 nits.
Round-1 findings S1, M1, M2, N1, N2, N3 are addressed and pass
re-verification. Round-1 M3 and M4 are addressed in prose but
have left a residual cross-section inconsistency in Task 0's
"Files:" preamble (recorded as M3'). The round-1 review's
S1 fix introduced the §6.1 motive-elaboration stub verbatim
into Task 0 Step 6 and into Task 1 Step 3; round-2 ran the
stub through `mcp__lean-lsp__lean_run_code` and found it
fails to elaborate (`invalid {...} notation, expected type
is not known`). Separately, the §6.3 proof-shape stub
(Task 0 Step 3, mirrored in Task 3 Step 3) was run through
the MCP and also fails: the `simp only [..., eqToHom_refl,
Category.comp_id, Category.id_comp, ...]` set does not
discharge the `eqToHom` transports introduced by
`CategoryTheory.Functor.ext`, leaving the post-`simp` goal
shape incompatible with the subsequent `change` step. These
are precisely the failure modes T5.0 was created to surface
**before** any commit lands — so the plan would in fact halt
the implementer at T5.0 Step 4 (or Step 7) rather than commit
broken code. Nonetheless the plan as written prescribes Lean
code that does not type-check; the literal snippets must be
amended before implementation begins.

## Methodology

1. Read the revised plan end-to-end.
2. Read the round-1 review end-to-end; tagged each round-1
   finding (S1, M1–M4, N1–N3) and located the corresponding
   section in the revised plan.
3. Re-read the spec §5 (operational semantics), §6 (proof
   shapes), §10 (operational notes) end-to-end and cross-checked
   against the revised plan.
4. Re-read the existing on-disk source that the plan modifies:
   - `GebLean/LawvereERKSim/ErToKFunctor.lean` (T4 surface),
   - `GebLean/LawvereKSimER.lean:336–571` (kToER mirror),
   - `GebLean/LawvereKSimDCatInterp.lean` (kInterpFunctor +
     `KMorNQuo.interp`),
   - `GebLean/LawvereERInterp.lean` (erInterpFunctor +
     `Faithful` instance),
   - `GebLean/LawvereERKSim.lean` (umbrella).
5. Ran the §6.1 motive-elaboration stub (plan Task 0 Step 6
   snippet, verbatim) through `mcp__lean-lsp__lean_run_code`
   under the project's mathlib pin. Result: ERROR `invalid
   {...} notation, expected type is not known` at the
   anonymous-constructor `{ hom := ..., depth_witness := ... }`
   inside the motive. Re-ran with the same code but with the
   anonymous constructor wrapped in `(... : KSimMor 2 n m)`;
   result: success (warning about `⋯` from the `sorry` body,
   as expected). The anonymous-constructor type annotation is
   the missing piece.
6. Ran the §6.3 proof-shape stub (plan Task 0 Step 3 snippet,
   verbatim) through `mcp__lean-lsp__lean_run_code`. Result:
   ERROR `'change' tactic failed, pattern ... is not
   definitionally equal to target ... erInterpFunctor.map
   (eqToHom ⋯ ≫ e ≫ eqToHom ⋯)`. The `simp only` set does
   not eliminate the two `eqToHom` transports introduced by
   `Functor.ext` (despite the `eqToHom_refl`, `Category.id_comp`,
   `Category.comp_id` arguments present in the `simp only`
   call — the linter reported all three as unused). Re-ran with
   `dsimp` first; result: `simp made no progress`. Re-ran with
   `show kToERFunctor.map (erToKFunctor.map e) = eqToHom rfl
   ≫ e ≫ eqToHom rfl`; result: `show` succeeds, confirming the
   `eqToHom`s are `eqToHom rfl`, but the subsequent `rw
   [eqToHom_refl, eqToHom_refl, Category.id_comp,
   Category.comp_id]` and then `rw
   [kToERFunctor_comp_erInterpFunctor]` fails with a motive-
   type-correctness error. The §6.3 proof shape needs revision.
7. Ran `jj log -r feat/t5-equivalence`. Confirmed the
   bookmark points at `54134ca2` (change `oyktuwyp`,
   `docs(equivalence): apply T5 plan round-1 adversarial-
   review fixes`). The plan's "Topic branch" section no longer
   names a SHA, so M1 stands resolved.
8. Spot-checked each remaining round-1 finding against the
   revised plan:
   - M2: Task 0 Step 2.5 runs `lake test` — present.
   - N1: Step 5 snippet now contains only `section InstanceStub`
     inside the surrounding namespace; Step 5 prose
     ("remove that trailing line before appending") makes the
     buffer-management explicit — present.
   - N2: "Topic branch" section now contains the sentence about
     the intentional umbrella-bullet staleness across T5.A.1 /
     T5.A.2 — present.
   - N3: Task 2 Step 4 no longer contains the char-count
     parenthetical (replaced with "Verify the subject fits
     within the ≤ 72-char target") — present.
9. Re-read the four mathlib upstream guides (commit, style,
   naming, doc) via WebFetch on
   `https://leanprover-community.github.io/contribute/index.html`
   and linked sub-pages; cross-checked against the revised plan's
   commit-message subjects, declaration naming (`erToKFunctor_map_interp`,
   `erToKFunctor_comp_kInterpFunctor`, etc.), and docstring
   structure. No new violations.
10. Re-checked the buffer-management instructions across Task 0
    Steps 3, 5, 6, 7. The resulting buffer should be: one
    `namespace GebLean` opening (from Step 3), three example
    blocks (the §6.3 example from Step 3, the `section
    InstanceStub` from Step 5, and the §6.1 example from
    Step 6), and one `end GebLean` closing (re-added at the
    end per Step 5's "remove trailing `end GebLean` …
    re-add a single `end GebLean`" instruction; Step 6's
    "Append the following snippet to the buffer immediately
    before the final `end GebLean`" further makes clear that
    the §6.1 stub is inserted before the closing). Single
    well-formed wrapping confirmed.

## Findings — round-1 status

### S1 — RESOLVED in placement; NEW BLOCKER B1 surfaced by the stub itself

The plan now contains the §6.1 motive-elaboration stub at
Task 0 Step 6, with the spelled-out lift function and
`intro rec; sorry` body, plus a Step 7 that re-runs the
combined buffer through the MCP. Placement and intent
match the round-1 fix recommendation.

However, round-2 ran the stub through the MCP and found it
does not elaborate; see B1 below. This is not a regression
caused by the round-1 fix — the same code appears in Task 1
Step 3, where it was already present in round 1 (round 1 did
not run that snippet). The S1 fix is the right shape; the
underlying Lean code needs revision before either the stub
or the real theorem will type-check.

### M1 — RESOLVED

The "Topic branch" section now reads:

> All commits land on bookmark `feat/t5-equivalence` (already
> created during the spec/plan phase). The implementer advances
> the bookmark after each `jj commit` via `jj bookmark move
> feat/t5-equivalence --to @-`.

No SHA reference. State-agnostic. Matches the round-1 fix
recommendation.

### M2 — RESOLVED

Task 0 now has Step 2.5:

> Run: `lake test`
> Expected: succeeds with no failures. Surfaces any pre-existing
> test-suite breakage at the T5.0 boundary rather than at Task 5
> Step 7 (where it would have to halt mid-implementation).

Matches the round-1 fix recommendation.

### M3 — RESOLVED in prose; residual inconsistency M3'

Task 0 Step 4 now reads:

> If the lean-lsp MCP is unavailable in the SDD subagent's
> environment: HALT and surface that as a tooling-pre-condition
> issue. Do not attempt to substitute `lake env lean` (banned by
> CLAUDE.md) or to commit a scratch source file inside the
> project tree.

This closes the round-1 M3 concern (no underspecified
`lakefile.toml` mutation). However, the "Files:" preamble at
the top of Task 0 still mentions a `GebLean/Scratch/T5Stubs.lean`
fallback — see M3' below.

### M4 — RESOLVED in prose; residual inconsistency M3'

The MCP-only path is the only path described in Steps 3, 4, 5,
6, 7. No in-tree scratch path appears in the operational
steps. The spec's `/tmp/...` path is harmless once no on-disk
artifact is produced.

### N1 — RESOLVED

Task 0 Step 5 snippet now begins with the comment

> Append the following snippet (verbatim, without an outer
> `namespace GebLean`/`end GebLean` wrapper — the buffer from
> Step 3 already opens that namespace and does not close it
> until the very end) to the in-memory buffer:

and the snippet itself contains only `section InstanceStub`
… `end InstanceStub`. Step 5's closing prose

> The Step 3 buffer ends with `end GebLean`; **remove that
> trailing line before appending** this snippet, and re-add a
> single `end GebLean` at the very end of the combined buffer.
> The result has one `namespace GebLean ... end GebLean` block
> wrapping both stubs.

makes the buffer-management explicit. Round-1 N1 stands
resolved.

### N2 — RESOLVED

The "Topic branch" section now contains:

> The umbrella docstring's `ErToKFunctor` bullet remains
> intentionally unchanged across the T5.A.1 / T5.A.2 commits;
> per spec §10 *Umbrella update*, the umbrella edit rides on
> T5.C, so the SDD subagent must not update the umbrella in
> T5.A.1 / T5.A.2 (doing so would break per-task scope
> discipline).

Matches the round-1 fix recommendation.

### N3 — RESOLVED

Task 2 Step 4 no longer carries the inline char-count
parenthetical. It now reads simply:

> Verify the subject fits within the ≤ 72-char target before
> running `jj commit`.

Matches the round-1 fix recommendation.

## New findings

### B1 — §6.1 motive anonymous-constructor needs explicit type ascription

**Locations.** Plan Task 0 Step 6 (the §6.1 motive-elaboration
stub); plan Task 1 Step 3 (the real theorem body, with
identical motive). Spec §6.1 lines 304–315.

**Symptom.** Run via `mcp__lean-lsp__lean_run_code`:

```text
error: invalid {...} notation, expected type is not known
  --> line 22, column 13
```

The error points at the anonymous constructor
`{ hom := Quotient.mk (kMorNSetoid n m) (erToKN rec),
   depth_witness := Quotient.mk _ { rep := ..., rep_level := ...,
   rep_eq := rfl } }` inside the motive's `Quotient.liftOn`
lift-function argument. The motive position does not propagate
an expected type to the inner anonymous-constructor block.

**Reproduction.** The minimal snippet — exactly the plan's
Task 1 Step 3 body lifted into an `example` (no further
context) — was run against the project pin via the MCP and
failed.

**Fix that works.** Wrapping the anonymous constructor in a
type ascription `(... : KSimMor 2 n m)` lets the stub
elaborate. Concretely, replace

```lean
          (fun rec =>
            { hom := Quotient.mk (kMorNSetoid n m) (erToKN rec),
              depth_witness := Quotient.mk _
                { rep := erToKN rec,
                  rep_level := fun i => erToKN_level rec i,
                  rep_eq := rfl } })
```

with

```lean
          (fun rec =>
            ({ hom := Quotient.mk (kMorNSetoid n m) (erToKN rec),
               depth_witness := Quotient.mk _
                 { rep := erToKN rec,
                   rep_level := fun i => erToKN_level rec i,
                   rep_eq := rfl } } : KSimMor 2 n m))
```

both in plan Task 0 Step 6 and in plan Task 1 Step 3 (and,
since the spec source is the binding text, also in spec §6.1
lines 308–313 via a spec follow-up review).

**Why this is a blocker.** The implementer following the plan
verbatim will hit the failure at Task 0 Step 4 / Step 7
(T5.0's stub-MCP check), and per the plan's HALT clause:

> If type-check fails: HALT. Do not proceed to T5.A.1. File a
> finding, revise the spec, dispatch a new adversarial-review
> round.

So no broken code reaches a commit — but the plan as written
prescribes Lean snippets that do not type-check, which is a
plan-quality blocker. Round-1's mention that "T5.0 baseline
verifies this" is now load-bearing: the verification fails;
the plan must be amended.

**Note on memory.** Project memory's `## Idris2 let binding
opacity in proofs` (carried over to Lean in spirit) and `##
"show X from e" vs type ascription` both record analogous
failure modes where the elaborator needs explicit type
information at anonymous-constructor positions. This is a
well-known pattern; the round-1 fix simply transcribed the
spec's text without running it.

### B2 — §6.3 proof-shape stub does not elaborate under the current pin

**Locations.** Plan Task 0 Step 3 (the §6.3 proof-shape
stub); plan Task 3 Step 3 (the real theorem
`erToKFunctor_comp_kToERFunctor`, with the same proof shape).
Spec §6.3 lines 384–404.

**Symptom.** Run via `mcp__lean-lsp__lean_run_code`:

```text
error: 'change' tactic failed, pattern
  (kToERFunctor ⋙ erInterpFunctor).map (erToKFunctor.map e)
    = erInterpFunctor.map e
is not definitionally equal to target
  erInterpFunctor.map (kToERFunctor.map (erToKFunctor.map e))
    = erInterpFunctor.map (eqToHom ⋯ ≫ e ≫ eqToHom ⋯)
```

with three warnings: `eqToHom_refl`, `Category.comp_id`, and
`Category.id_comp` are reported as unused inside the `simp only`
set. The transports introduced by `CategoryTheory.Functor.ext`
on the RHS (`eqToHom ⋯ ≫ e ≫ eqToHom ⋯`) are not eliminated
by the `simp only` set as listed.

**Probing.** Re-running with `show kToERFunctor.map
(erToKFunctor.map e) = eqToHom rfl ≫ e ≫ eqToHom rfl` succeeds
(confirming the two `eqToHom`s are `eqToHom rfl`), but the
subsequent `rw [eqToHom_refl, ..., kToERFunctor_comp_erInterpFunctor]`
fails with a motive-type-correctness error: the rewrite of
the *functor* equality `kToERFunctor ⋙ erInterpFunctor =
kInterpFunctor` would change the functor occurring in
`(kToERFunctor ⋙ erInterpFunctor).map (erToKFunctor.map e)
= erInterpFunctor.map e`, but the equation's RHS depends on
`erInterpFunctor`'s object map, so the motive abstraction
fails.

**Why this matters.** Spec §11.3 ("Faithfulness chain sound")
explicitly committed: "verify that the two `rw`s commute with
the surface `(F ⋙ G).map _` rewriting; flag any gap." The
gap exists. Spec §6.3's reasoning ("after the two `rw`s, the
goal reduces to `erInterpFunctor.map e = erInterpFunctor.map e`,
closed by `rfl` from the last `rw`") is correct in the abstract
but the literal tactic sequence does not produce that
reduction.

**Fix candidates (not bound — spec amendment required).**

1. Manually unfold or normalise the `eqToHom rfl`s before the
   `apply erInterpFunctor.map_injective` step (e.g.
   `simp only [eqToHom_refl, Category.id_comp, Category.comp_id]`
   alone does nothing here; perhaps `dsimp only [Functor.id_obj,
   Functor.comp_obj]` first, then the simp set; or a manual
   `show`).
2. Rewrite the proof via `Functor.congr_hom` to introduce
   `eqToHom` transports explicitly, then collapse them.
3. Use `congr 1` after `apply erInterpFunctor.map_injective`
   to peel back to a `Functor.map`-of-`Functor.map` equation
   and then apply the underlying interp preservation directly
   (bypassing `change` + `rw` on the composite-functor equality).

The spec-level fix is to amend §6.3 (and §6.4 symmetrically)
with a tactic sequence that actually elaborates. The plan
inherits whatever the spec produces.

**Why this is a blocker.** As with B1, the implementer hitting
this failure at Task 0 Step 4 (or Task 3 Step 4) would HALT
per the plan's stated halting policy. No bad code commits.
But the plan-as-written prescribes a tactic sequence that
does not type-check; the plan-quality bar is unmet.

### M3' — Task 0 "Files:" still describes the now-removed fallback

**Location.** Plan Task 0, lines 110–113:

> **Files:**
>
> - No on-disk artifact when the lean-lsp MCP is used
>   (recommended). Fallback path uses a temporary
>   `GebLean/Scratch/T5Stubs.lean` deleted before the task
>   completes; nothing is committed either way.

**Inconsistency.** Step 4's prose closes the fallback path
("HALT and surface that as a tooling-pre-condition issue. Do
not attempt to … commit a scratch source file inside the
project tree."). The "Files:" preamble, however, still names
`GebLean/Scratch/T5Stubs.lean` as the fallback location. A
careful implementer reading the preamble first may attempt the
scratch path before reading Step 4's HALT clause.

**Fix.** Replace the preamble bullet with:

> - No on-disk artifact. T5.0 verifies the spec's stubs via
>   `mcp__lean-lsp__lean_run_code`; nothing is written under
>   the project tree. If the MCP is unavailable, HALT per
>   Step 4.

**Severity.** Minor — does not change the binding behaviour
(Step 4 dominates), but a reviewer scanning the preamble would
wrongly conclude that M3 was not resolved.

## Convergence verdict

BLOCK — 2 blockers (B1, B2), 0 serious, 1 minor (M3'), 0 nits.

Round-1 findings S1, M1, M2, N1, N2, N3 are resolved.
Round-1 M3 and M4 are resolved in operational prose; the
residual M3' is a leftover preamble bullet inconsistent with
Step 4. The two blockers are Lean-elaboration failures in the
plan's literal snippets, exposed by running them through
`mcp__lean-lsp__lean_run_code`:

- B1 (§6.1 motive's anonymous constructor needs `: KSimMor 2 n m`)
  is a localised plan-text fix.
- B2 (§6.3 / §6.4 `simp only` does not discharge the `eqToHom`
  transports as advertised, blocking the subsequent `change`/
  `rw` chain) is a spec-level fix; the spec needs an
  amendment round before the plan can settle.

Per CLAUDE.md and `docs/process.md` § Adversarial review, BLOCK
re-dispatches the spec for amendment and the plan for re-write
of Tasks 0 and 1 (B1) and Task 3 (B2). A round-3 plan review
will be needed after those amendments land.

Re-dispatch order suggested:

1. Spec amendment round (`.review-4.md` on the spec) to fix
   §6.1 motive type ascription and §6.3 / §6.4 proof-shape
   tactic sequence; both fixes should be MCP-verified before
   the amendment commits.
2. Plan re-revision (carrying the spec fixes into Task 0
   Step 6, Task 1 Step 3, Task 3 Steps 3 / 5; also fixing M3').
3. Round-3 plan adversarial review.
