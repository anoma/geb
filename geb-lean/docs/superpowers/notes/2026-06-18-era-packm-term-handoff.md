# Handoff / resume: Era `packM`-as-term (Corollary 3.6 transcription)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [What this is](#what-this-is)
- [Governing discipline (do not deviate)](#governing-discipline-do-not-deviate)
- [Read these (the full scope, in order)](#read-these-the-full-scope-in-order)
- [Done (committed, axiom-clean, both reviews passed)](#done-committed-axiom-clean-both-reviews-passed)
- [Status: packM-as-term sub-project complete](#status-packm-as-term-sub-project-complete)
- [Resume point (next work) — Task 6.4d onward](#resume-point-next-work--task-64d-onward)
- [How to continue](#how-to-continue)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This is the versioned entry point for resuming the `packM`-as-term
sub-project across sessions. (It lives in `docs/` deliberately: the
`.remember/` directory is owned by the remember plugin and is overwritten
on restart, so it is not safe for durable handoffs.)

## What this is

Formalising, in Lean 4 (`geb-lean`), the realisation of the packed
witness `packM` of arXiv:2407.12928 (Lemma 3.3) as an `Era` arithmetic
term, faithfully transcribing that paper's Corollary 3.6 (which uses
Lemma 3.5). This unblocks `eraCount`/`eraCount_eval` and through them the
parent Era-completeness Tasks 6.4d, 6.4e, 6.5, 6.6 and Phase 7
(`era_complete` + the K-sim-2 corollary).

Branch: `feat/era-packm-term` (off `main`). VCS is `jj` (colocated). All
work is committed there; nothing is pushed (push needs user
line-by-line review). The bookmark `feat/era-packm-term` tracks the tip.

## Governing discipline (do not deviate)

- Transcribe what the papers do; invent no parallel machinery. When a
  "design question" seems to arise, first read what the paper says — the
  paper supplies the architecture. The mapping note is the contract for
  what each Lean object must equal in the paper.
- Execution is subagent-driven: one implementer subagent per task, then
  an independent spec-compliance review and a code-quality review, then
  the controller commits (implementers never commit). Reviews must avoid
  the `lean-lsp` MCP (it hangs under concurrent use); reviewers use
  `lake build` + `check-axioms.sh` + reading code only.
- Every commit: `lake build <module>`, `bash scripts/pre-commit.sh`
  (lake test + lake lint), `bash scripts/check-axioms.sh <file>` — all
  green, only `propext`/`Quot.sound`/`Classical.choice`, no `sorry`.
- jj flow per task: edit in `@`; `jj describe -m "<conventional msg>"`;
  `jj new`; `jj bookmark set feat/era-packm-term -r @-`. Commit subjects
  are imperative, lowercase, no trailing period, under ~72 chars.
- Constructive-only (no `noncomputable`); ℤ is used only as a proof-side
  reflection (`ZMonomial.eval`); terms stay ℕ-valued.

## Read these (the full scope, in order)

- Spec: `docs/superpowers/specs/2026-06-17-era-packm-term-design.md`.
- Plan: `docs/superpowers/plans/2026-06-18-era-packm-term-plan.md`
  (Phases A–E; B/C/D were refined at execution — the notes below
  supersede the plan's sketch where they differ).
- Phase B construction note (Lemma 3.5):
  `docs/superpowers/notes/2026-06-18-era-phaseB-sepReduce-design.md`.
- Lean-to-paper mapping (audit + the term-layer architecture, incl. the
  `k+f` count cube):
  `docs/superpowers/notes/2026-06-18-era-packm-term-paper-mapping.md`.
- Paper P1: `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`
  (extract: `pdftotext <pdf> /tmp/era2407.txt`; § 4 ≈ lines 360–820).
- Lean files in play: `GebLean/Utilities/EraSepReduce.lean` (Phases
  A, B) and `GebLean/EraHistCodeTerm.lean` (Phases C, D, E).

## Done (committed, axiom-clean, both reviews passed)

- Spec + plan committed; two adversarial review rounds (BLOCKER closed,
  MAJOR + MINORs fixed).
- Phase A (signed ℤ-`ZMonomial` reflection of the `diophOf` predicate):
  A1 `ZMonomial`+denotations; A2 `mul`; A2b `extractCubeDegree` plus
  `IsVarProduct`/`CoeffVarProduct`/`BasePaired` (and `diophOf_*`
  capstones) — the original BLOCKER (cube-degree trapped in `coeff`)
  closed; A3 `SimpleMonomial`/`SimpleSum.toZ`; A4 `SosSystem.toZ` (with
  `negDouble`, `SosTerm.cast_sqDist`).
- Phase B (Lemma 3.5, in EraSepReduce): B0 index layer
  (`chainIdx`/`cubeSlot`/`chainSlot`/`castAddEmb`); B1 `ZMonomial.weaken`;
  B2 `chainEqList`/`chainEqs`/`chainSub`/`maxCubeDegree`; B3 `sepReduce`
  with `sepReduce_degree` (needs `PolyExpZero`); B4a
  `sepReduce_eval_split` and `chainEqs_zero_imp_chainHolds`; B4b
  `sepReduce_sound` and `sepReduce_unique`. Lemma 3.5 complete.
- Phase C (in EraHistCodeTerm): C1 `ZMonomial.cubeFactor` (separable
  normal form, separability hyps dischargeable by
  `CoeffVarProduct`/`BasePaired`); C2a `ZMonomial.eraMonoCubeSum` and
  `weight_mixedRadix_factor` (the ℕ cube-sum factorisation).
- Term-construction design spike done; result recorded in the mapping
  note (the `k+f` count cube is paper-dictated by Cor 3.6, not a choice).
- Phase C2t/D (term layer, in EraHistCodeTerm): C2t-gate `sepReduce_separable`
  (#957, in EraSepReduce, with `ETm.ConstOnImage` and `ZMonomial.cubeRegroup`);
  C2t-term `ETm.paramProject`/`cubeConstTerm`/`cubeBaseTerm`/`eraMonoTerm` (#958);
  D1 `eraConstPart` (Eq 7, #959); D2 `packM_term` (Eq 8, signed partition + ℤ
  non-underflow, #960); D3 `eraCount`/`eraCount_eval` (#961).
- Phase E (count preservation, in EraHistCodeTerm): E1 `eraTheta`/`eraW` plus the
  reindexing foundations `cubeRegroup_append_eq` and the cube-product split (#962);
  E2 `reducedCount_eq` (Lemma-3.5 fibre collapse) + `predCount_side_eq` (shell
  bridge, #963); E3 `eraCountPred`/`eraCountPred_eval` (the public combinator,
  with the slot-moving `diophOf` reindex `reindexEmb`/`reindexCtx`/`reindexSys`,
  #964). Each task: an implementer plus independent spec and quality reviews,
  axiom-clean, committed; final whole-branch review passed (merge-ready after the
  three documentation/cosmetic minors, since fixed).

## Status: packM-as-term sub-project complete

All of Task 6.4c is done. `eraCountPred τ : ETm n` realises, for any
`diophOf`-encoded predicate `τ`, the count of vanishing (output slot plus
witness) assignments of the Diophantine system as a constructive `Era`
arithmetic term (`eraCountPred_eval`, arXiv:2407.12928 Corollary 3.6 /
Theorem 3.4). Branch `feat/era-packm-term`, nine session commits
`f32156c..30ac6fe` on top of the Phase A/B/C work; build clean, axiom-clean
(`propext`/`Quot.sound`/`Classical.choice`), no `noncomputable`. Nothing is
pushed (push needs user line-by-line review).

## Resume point (next work) — Task 6.4d onward

The parent Phase 6-7 plan resumes at Task 6.4d. The one deferred obligation
from this sub-project, to be discharged where 6.4d/6.4e consume the count:

- The `solCount` corollary: collapse the `diophOf` unique-witness fibre (via
  `diophOf_unique`, `EraDiophantine.lean`) so `eraCountPred_eval`'s count over
  (output slot + witnesses) becomes a count over the output slot alone. The
  route mirrors `reducedCount_eq`'s `card_nbij'` fibre argument with the
  `diophOf` witness in place of the chain witness; `eraBaseBound`/
  `reindexSys_coord_bound`/`reindexCtx` are reusable and no new reindex
  machinery is needed. See task #964's report for the detailed sketch.

## How to continue

Re-read the parent Phase 6-7 sub-plan and confirm the branch tip
(`jj log -r feat/era-packm-term`; tip `30ac6fe5`). Resume at Task 6.4d via
the subagent-driven loop: dispatch an implementer with the full task text plus
the paper anchor, then spec review, then quality review (all `lean-lsp`-free),
then commit. Keep "first read the paper" as the discipline.
