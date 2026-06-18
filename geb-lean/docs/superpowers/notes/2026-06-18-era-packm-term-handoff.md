# Handoff / resume: Era `packM`-as-term (Corollary 3.6 transcription)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [What this is](#what-this-is)
- [Governing discipline (do not deviate)](#governing-discipline-do-not-deviate)
- [Read these (the full scope, in order)](#read-these-the-full-scope-in-order)
- [Done (committed, axiom-clean, both reviews passed)](#done-committed-axiom-clean-both-reviews-passed)
- [Resume point (next work) — task list IDs](#resume-point-next-work--task-list-ids)
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

## Resume point (next work) — task list IDs

Remaining is the term layer plus count preservation, all in
`GebLean/EraHistCodeTerm.lean`, all transcription of P1 Eqs (7),(8) /
Cor 3.6 with the representation plumbing the mapping note specifies:

1. C2t-gate (task #957): three pipeline-threaded predicates over
   `(sepReduce s).2` — `coeff.IsVarProduct`, residual cube-free
   (`extractCubeDegree.2 = 0`), cube-`expCoeff` `ctx`-independent —
   discharging `eraMonoCubeSum`'s separability hypotheses. The gate.
2. C2t-term (#958): `ETm.paramProject` (with eval; strengthen `coeff` to
   `ETm p`), `cubeConstTerm`/`cubeBaseTerm`, `eraMonoTerm` (with eval).
   Use the `k+f` cube via `(p+k)+f = p+(k+f)` re-association.
3. D1 (#959): `eraConstPart` (Eq 7) with eval.
4. D2 (#960): `packM_term` (Eq 8) — positive/negative `List.filter`
   partition by `ZMonomial.sign` into minuend/subtrahend of one `etsub`;
   prove `eval = packM` and non-underflow by descending a ℤ identity
   from `packM ≥ 0`. Hardest proof of the phase.
5. D3 (#961): `eraCount` with `eraCount_eval` — `eraCountOfPack k
   packM_term tTerm wTerm`, count over the `k+f` cube.
6. E1 (#962) `eraTheta`/`eraW` from `eraMajorant`; E2 (#963)
   `reducedCount_eq` plus shell-empty bridge (`#{(a,b):R=0}=#{a:P=0}` via
   `sepReduce_sound`/`unique`, then side `max(t,θ)` to side `t`); E3
   (#964) `eraCountPred` (with eval, and the `diophOf`
   `Fin (n+1+witArity)` index reconciliation) — closes parent Task 6.4c.

Then the parent Phase 6-7 plan resumes at 6.4d onward.

## How to continue

Re-read the spec, plan, the two notes, and this file. Confirm the branch
tip (`jj log -r feat/era-packm-term`). Start the next pending task (#957)
via the subagent-driven loop: dispatch an implementer with the full task
text plus the mapping-note paper anchor, then spec review, then quality
review (all `lean-lsp`-free), then commit. Keep "first read the paper" as
the discipline.
