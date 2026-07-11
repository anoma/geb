# Ramified Phase 7 handoff (2026-07-11, sub-phase 6.5 complete)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Where the workstream stands](#where-the-workstream-stands)
- [Next steps for the resuming session](#next-steps-for-the-resuming-session)
- [Deferred-ticket list (carried forward; none blocking)](#deferred-ticket-list-carried-forward-none-blocking)
- [Documentation map](#documentation-map)
- [Process constraints (unchanged; honor these)](#process-constraints-unchanged-honor-these)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: sub-phase 6.5 (the collapse packaging) is COMPLETE and merged
to `main` (PR #250: `feat/ramified-p6.5-collapse-functor`, Tasks 6.5a
and 6.5b plus a final-review documentation commit). Phase 6 is
thereby fully delivered. The immediate next action for the resuming
session is **Phase 7** (section "Next steps"), the workstream's final
phase; its Task 7.3 documents the completion of the workstream. This
note is the durable record; the session-local ledger and per-task
reports live under `.superpowers/sdd/` at the monorepo root and are
not committed, so everything needed to resume is restated here.

## Where the workstream stands

Master plan
(`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`):
Phases 1-5 and Phase 6 (sub-phases 6.1-6.5) are merged. Every phase
except 7 is complete. Sub-phase 6.5 delivered, on one branch (7
review-gated commits, fresh implementer per task, two-verdict review
per task, whole-branch final review, axiom gate green throughout),
all in `GebLean/Ramified/Soundness/Collapse.lean` (plus one public
evaluation lemma in `NormStepER.lean`, index wiring, and tests):

- **The domain category** (Task 6.5a): `isObjCtx` (the object-sort
  context property), `SynCatFO` (its `ObjectProperty.FullSubcategory`
  over `RMRecCat natAlgSig`), the bridge `SynCatFO.toObjCtx : SynCatFO
  → Σ n, ObjCtx n` with `objLen`, and `collapseDenotation` — the
  Phase 5 `ramifiedDenotation` read through the bridge (`collapseHom`,
  a single `cast` along `toObjCtx_toCtx`) — with the laws
  `collapseDenotation_id` / `collapseDenotation_comp`.
- **The functor** (Task 6.5b): **`collapseFunctor : SynCatFO ⥤
  LawvereERCat`** with **`instance : collapseFunctor.Faithful`**. The
  morphism map routes each of the `objLen Δ` codomain components
  through the term-level extension of the 6.1 translation
  (`hoTermModel` / `hoTmTranslate`, bottoming out at `prop7Translate`
  at every identifier leaf, with agreement `hoTmTranslate_interp`)
  into the 6.4 atomic landing `collapseERN`, tupled by
  `collapseTupleER`; the tupling lemma `collapseTupleER_interp` lifts
  the per-component `collapseERN_interp` to `ramifiedDenotation` of
  the source morphism. Well-definedness on the interp-quotient
  hom-sets and `Faithful` both close through
  `ramifiedDenotation_injective` (environments over object-sort
  contexts are determined by their numeric readings).
- **Public-surface extension**: `appEval_sourceApps` (with
  `ofFnOmegaEnv`) in `NormStepER.lean` — the one place 6.5 needed
  more than the landed capstones; added as a public evaluation lemma
  rather than reaching into internals.
- **Tests** (`GebLeanTests/Ramified/Soundness/Collapse.lean`):
  the doubling acceptance `example` — `collapseFunctor` on the
  Phase 2 doubling morphism yields an `ERMorN` whose interp equals
  the doubling denotation at all inputs, with values 0/2/6 at inputs
  0/1/3 — and a faithfulness-injectivity `example` on the doubling
  hom-set, both proved from the interpretation lemmas (no `#guard`).
- `lean_verify` on the capstones (`collapseFunctor`, the `Faithful`
  instance, `collapseTupleER_interp`, `appEval_sourceApps`): axioms
  exactly `propext`, `Classical.choice`, `Quot.sound`.
- Hygiene confirmed by the whole-branch review: 6.5 consumes exactly
  the public 6.4 capstone interfaces; the correction-5 budget slot
  appears nowhere in 6.5's statements or proofs.

Execution notes a resuming session should know:

- The functor's `map_id` / `map_comp` consume
  `ramifiedDenotation_id` / `_comp` after rewriting by
  `collapseHom_id` / `_comp` — the decomposed constituents of the
  6.5a laws, adjudicated at final review as the correct altitude.
  The wrapper laws `collapseDenotation_id` / `_comp` remain the
  pinned public interface; `collapseDenotation_comp` currently has
  no consumer (Phase 7 is its expected first consumer; if Phase 7
  composes with these laws, sketch consumption at the
  `ramifiedDenotation` level).
- The plan's symbolic acceptance form (`2 * v 0`) foundered on the
  recorded `Fin.cases` / `PolyFix.ind` non-reduction friction; the
  committed all-inputs denotational form was adjudicated stronger
  and endorsed at final review.

## Next steps for the resuming session

1. **Phase 7** (NOT gated; no new spec, brainstorm, or sub-plan
   needed). Tasks 7.1-7.3 are fully step-elaborated in the master
   plan § "Phase 7 — assembly": create
   `GebLean/Ramified/Characterization.lean` (+ tests, index wiring).
   - 7.1: `ramified_definability` — for every `f : (n :
     LawvereERCat) ⟶ m` there exist `Γ : ObjCtx n` and `g : Γ ⟶
     oCtx m` with `collapseDenotation g = f` (spec s6.1 verbatim
     modulo the recorded name mapping and arity bookkeeping) — from
     the Phase 5 family (`erMor_ramified_definable`,
     `Definability/Top.lean`, multi-output assembled componentwise)
     and the Phase 6 collapse artifacts. The module docstring states
     the pair — `collapseFunctor` well-defined and faithful;
     `ramified_definability` — as the denotational form of Theorem
     14 items (1)-(2) relative to `LawvereERCat` (Leivant III
     section 6, p. 227); the categorical packaging (spec open
     question 7) is **not** asserted — no equivalence-of-categories
     claim.
   - 7.2: transfer of both statements across `erKSimEquiv :
     LawvereERCat ≌ LawvereKSimDCat 2`
     (`GebLean/LawvereERKSim/Equivalence.lean:183`; strict
     round-trip equalities at `:96` / `:126` shorten the transport),
     via `erToKFunctor` / `kToERFunctor`.
   - 7.3: the area doc `docs/areas/ramified-recurrence.md` (what
     exists, module map, statement inventory, deferred items
     pointing at spec s9-s10), the `docs/index.md` workstream entry,
     and spec/plan supersession reconciliation — this task is the
     workstream-completion documentation.
   Execute via subagent-driven development on a fresh topic branch
   off `main` (the master plan names `feat/ramified-p7-assembly`).
2. **Adjustments to the plan text, already earned:**
   - Task 7.1 Step 1's failing tests (the doubling `example` and a
     faithfulness `example`) already exist — delivered by 6.5b in
     `GebLeanTests/Ramified/Soundness/Collapse.lean`. Step 1 should
     begin from a failing `example` for `ramified_definability`
     itself (e.g. definability of the doubling ER morphism) rather
     than re-creating the delivered pair; the symbolic-form caveat
     above applies.
   - The Decision-2 hygiene check (recorded at the 6.4 closeout):
     the final theorem must never mention `Represents` or `appEval`
     — the denotational anchoring stays internal. Check the
     statements of 7.1 and 7.2 against this before committing.
3. **After Phase 7 merges**: the workstream is complete. The
   completion record is Task 7.3's area doc and index entry; the
   closing session should also write the final workstream note if
   anything beyond 7.3's artifacts needs recording (deferred-ticket
   list below; correction-5's standing consequence).

## Deferred-ticket list (carried forward; none blocking)

From sub-phase 6.4 (unchanged): child-descent inequality
deduplication (three private copies; the public
`argCode_lt_of_shape_one` family in `CodeTm.lean` is the natural
home); `pair_le_pair` duplicates a private lemma in
`GebLean/PLang/BTPair.lean`; `clockERN` / `budgetERN` duplicate the
unary composite trees (parameterized combinator, or unary as the
`a = 1` instance); `interp_comp_singleton` / `interp_comp_three`
promotion on a second consumer; `natBProd_le_one_of_body_le_one_of_lt`
homing beside its `ERArith` sibling; the `NormStepER.lean` pure-move
split at the clocked-iteration seam; `sourceApps` pure move beside
`Ramified.sourceApp`.

Added by sub-phase 6.5: the Phase-5-subject helpers homed in
`Collapse.lean` (`Hom.eval_id`, `ramifiedDenotation_id` / `_comp` /
`_apply` / `_injective`, `objFromNat_objToNat`) relocate to
`Definability` / `SynCat` when Phase 7 provides the second consumer;
`interp_transport_arrow_apply` (`NormStepER.lean`, private) twins
`OmegaShift.lean`'s `cast_arrow_apply` — unification is a cross-file
refactor; `singletonEnv` migration candidate beside the `Binding`
kit; a `private`-marking pass over `Collapse.lean`'s file-local
plumbing (`singleton_get`, `joinEnv_nil`, the `cast_hom_*` pair).

## Documentation map

- Master plan (Phase 7's full task elaborations):
  `docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`.
- Parent Phase-6 sub-plan (historical; all sub-phases executed):
  `docs/superpowers/plans/2026-07-04-ramified-p6-soundness-subplan.md`.
- Spec (s6.1 fixes Phase 7's statements; s9-s10 the deferred items):
  `docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
- 6.4 spec and plan (amended for correction 5; the budget-slot
  record): `docs/superpowers/specs/2026-07-07-ramified-p6.4-normalizer-design.md`,
  `docs/superpowers/plans/2026-07-07-ramified-p6.4-normalizer-subplan.md`.
- Prior handoffs (historical): the 6.5 gate at
  `docs/superpowers/notes/2026-07-10-ramified-p6.5-handoff.md`
  (contains correction 5's durable record, including its standing
  consequence for rank-uniform normalizers).
- Workstream narrative: `docs/index.md`.

## Process constraints (unchanged; honor these)

- No `jj git push` without user line-by-line review; no raw mutating
  git; `jj` for all state mutation; no LLM-drafted PR titles/bodies.
- Pre-commit Lean triad before every `.lean` commit;
  `markdownlint-cli2` + doctoc for `.md`; `scripts/pre-push.sh` before
  any push.
- Constructive-only: no `noncomputable`/`sorry`/`admit`/new axioms in
  commits; `Classical.choice` accepted in proofs; `lean_verify` the
  capstones (`propext`, `Classical.choice`, `Quot.sound` only).
- Commit messages `<type>(<scope>): <subject>` imperative lowercase
  no-period ≤72, trailer `Co-Authored-By:` with the drafting model's
  own name `<noreply@anthropic.com>`.
- Subagent-driven pattern: fresh implementer per task, two-verdict
  per-task reviews, controller re-verifies repo-factual claims,
  commit-first discipline, controller-salvage on dead dispatches,
  ledger appends to `.superpowers/sdd/progress.md`.
