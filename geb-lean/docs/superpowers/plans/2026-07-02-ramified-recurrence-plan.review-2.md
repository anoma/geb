# Ramified recurrence plan review, round 2

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Fix verification (round 1)](#fix-verification-round-1)
- [Major findings](#major-findings)
  - [R2-M1: Task 5.0 contradicts the R1-M2 fix (stale third site)](#r2-m1-task-50-contradicts-the-r1-m2-fix-stale-third-site)
  - [R2-M2: Phase 6's declared dependencies omit Phase 3 and the Phase 5 sub-plan](#r2-m2-phase-6s-declared-dependencies-omit-phase-3-and-the-phase-5-sub-plan)
- [Minor findings](#minor-findings)
  - [R2-m1: file structure table stale against the R1-B1 fix](#r2-m1-file-structure-table-stale-against-the-r1-b1-fix)
  - [R2-m2: Task 7.1's `#guard` on the collapse image violates the pitfall rule](#r2-m2-task-71s-guard-on-the-collapse-image-violates-the-pitfall-rule)
- [Nit findings](#nit-findings)
  - [R2-N1: naming-rule commentary inside a binding docstring](#r2-n1-naming-rule-commentary-inside-a-binding-docstring)
  - [R2-N2: decision 5 attributes s6.1 names to "the spec's s4.2 sketch names"](#r2-n2-decision-5-attributes-s61-names-to-the-specs-s42-sketch-names)
  - [R2-N3: generic `SynCatFO` docstring asserts instantiation-specific content](#r2-n3-generic-syncatfo-docstring-asserts-instantiation-specific-content)
- [Verification coverage](#verification-coverage)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Verdict: NOT CONVERGED (0 blocker, 2 major, 2 minor, 3 nit).

Document under review:
`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md` at
commit `81b22fe18` ("docs(plans): address ramified-recurrence plan
review round 1"). Reviewed against the user-approved spec
(`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`),
the round-1 review, `CLAUDE.md`, `.claude/rules/lean-coding.md`,
`.claude/rules/markdown-writing.md`, the mathlib naming and style
guides (re-fetched this round), the round-1 fix diff
(`594bf5017..81b22fe18`), and the repository sources at the current
pin (`v4.29.0-rc6`).

## Fix verification (round 1)

| Round-1 ID | Status | Note |
| --- | --- | --- |
| R1-B1 | resolved | `QuotRel` parameter restored through Tasks 1.3/1.4/1.5, 2.2, 4.1, Phase 6; residual table staleness is R2-m1 |
| R1-M1 | resolved | how-to bullet and Phase 1 map row agree (G1-G4 before Phase 1; G3 decisive); no third inconsistent gate site found |
| R1-M2 | partially resolved | map row and how-to updated to "2, 3"; Task 5.0 Step 1 left stale — see R2-M1 |
| R1-M3 | resolved with regression | `SynCatFO`/`collapseDenotation`/`collapseFunctor` moved to Phase 6 `Collapse.lean`; deliverable restated over `RMRecCat natAlgSig`; the move left Phase 6's dependency row incomplete — see R2-M2 |
| R1-M4 | resolved | `instance : collapseFunctor.Faithful` in the Phase 6 binding block; Task 7.1 consumes it |
| R1-m1 | resolved | `GebLean/LawvereGodelTLemma16.lean` named explicitly in G2 Step 2 |
| R1-m2 | resolved | binders renamed to `sig` in Tasks 1.3/1.4; the escape-clause extension was not made but is moot with no illegal binder remaining |
| R1-m3 | resolved | `IsObj` everywhere (grep: no lowercase `isObj` remains); residual docstring commentary is R2-N1 |
| R1-m4 | resolved | `chore(ramified): spike syntax layer, A versus B (throwaway)` |
| R1-m5 | resolved | triad exemption for the spike branch plus the blocker-checkpoint discipline recorded in Global constraints |
| R1-m6 | resolved | `natAlgSig` removed from the `Algebras.lean` row |
| R1-m7 | resolved | `dstrCaseSig` fixed as a `SortedSig` summand with both translation directions specified |
| R1-N1 | resolved | `CategoryData` :199, `CategoryOfData` :222 |
| R1-N2 | resolved | metaphors replaced; grep confirms no "load-bearing" remains |

## Major findings

### R2-M1: Task 5.0 contradicts the R1-M2 fix (stale third site)

Location: Task 5.0, Step 1.

Evidence: Step 1 reads "write the sub-plan after Phase 2 lands (its
branch stacks after Phase 4 in the review queue, but its content
depends on Phase 2 only)". The R1-M2 fix changed the how-to bullet
to "The Phase 5 sub-plan is written after Phases 2 and 3 land (it
consumes the example ladder and `natFreeAlgEquiv`)" and the phase
map row to "2, 3", and Task 5.5's binding interface consumes
`natFreeAlgEquiv` (Phase 3, `Algebras.lean`). Task 5.0 was not
updated: an executor asking when the Phase 5 sub-plan may be
written, and what its content depends on, receives opposite answers
from Task 5.0 and from the two fixed sites. This is the same defect
class R1-M1 rated major.

Required fix: align Task 5.0 Step 1 with the fixed sites ("after
Phases 2 and 3 land"; content depends on Phases 2 and 3 — the
example ladder and `natFreeAlgEquiv`).

### R2-M2: Phase 6's declared dependencies omit Phase 3 and the Phase 5 sub-plan

Location: phase map row for Phase 6; "How to work this plan" phase
order bullet; Task 6.0 Step 1; Phase 6 "Final boundary item" block.

Evidence: the R1-M3 fix moved `SynCatFO`, `collapseDenotation`, and
`collapseFunctor` into Phase 6 (`Soundness/Collapse.lean`). The
moved block consumes artifacts Phase 6 does not declare:

- `SynCatFO`'s docstring and the `collapseDenotation` comment both
  read the standard-model interpretation "through `natFreeAlgEquiv`
  into `(Fin n → ℕ) → (Fin m → ℕ)`" — `natFreeAlgEquiv` is a
  Phase 3 artifact (`Algebras.lean`, Task 3.1).
- The `collapseDenotation` comment states "The exact argument
  bookkeeping (the `ObjCtx` coercion of Task 5.5) is fixed by the
  Phase 5 sub-plan; this phase's sub-plan states the signature
  against it" — so the Phase 6 sub-plan cannot state that signature
  until the Phase 5 sub-plan (Task 5.0) has converged, and
  `ObjCtx` itself is a Phase 5 artifact (`Definability/Top.lean`).

The phase map row says "Depends on: 2; G1, G2, G4" and the how-to
bullet says the Phase 6 sub-plan "is written after gates G1/G2/G4
have closed and Phase 2 has landed"; neither mentions Phase 3 or
the Phase 5 sub-plan. An executor following the declared
dependencies would write the Phase 6 sub-plan and begin
`Collapse.lean` with `natFreeAlgEquiv` nonexistent and the `ObjCtx`
bookkeeping unfixed. This is the defect class of R1-M2, introduced
by the R1-M3 fix.

Required fix: add Phase 3 to Phase 6's dependency row and to the
how-to sentence, and state where Phase 6's sub-plan waits on the
Phase 5 sub-plan (Task 5.0 convergence) for the `collapseDenotation`
signature — or restructure the boundary item so Phase 6's collapse
packaging consumes only declared dependencies (e.g. fix the
denotation bookkeeping in this plan rather than in the Phase 5
sub-plan).

## Minor findings

### R2-m1: file structure table stale against the R1-B1 fix

Location: file structure table, `GebLean/Ramified/Term.lean` and
`GebLean/Ramified/Interp.lean` rows.

Evidence: the R1-B1 fix added `QuotRel` to Task 1.3 (`Term.lean`)
and `interpQuotRel` to Task 1.4 (`Interp.lean`), and the fix updated
the `Algebras.lean`, `Soundness/*.lean`, and `Characterization.lean`
rows — but not the Phase 1 rows. The `Term.lean` row still reads
"`Tm`, `var`, `op`, `subst`, clone laws, `eval`" (no `QuotRel`) and
the `Interp.lean` row reads "`SortedModel`, `Presentation`,
`standardModel`, `interpSetoid`" (no `interpQuotRel`). Additionally
the `Term.lean` row lists `eval`, but `Tm.eval` is produced by
Task 1.4 in `Interp.lean` (it takes `M : SortedModel sig`, which is
defined there); the table and the task assignment contradict each
other. Decision 5 declares naming and file structure "fixed in the
next section", so the table is binding.

Required fix: add `QuotRel` to the `Term.lean` row, add
`interpQuotRel` to the `Interp.lean` row, and move `eval` to the
`Interp.lean` row (or move `Tm.eval` into Task 1.3 and reconcile the
`SortedModel` dependency).

### R2-m2: Task 7.1's `#guard` on the collapse image violates the pitfall rule

Location: Task 7.1, Step 1; Global constraints, "Known pitfalls".

Evidence: Step 1 prescribes "`collapseFunctor` on the Phase 2
doubling morphism yields an ER morphism interpreting as doubling
(`#guard` at small values through the quotient)". The pitfalls
section (binding on executors) forbids `#guard` on heavy composite
interpretations because such composites "expand symbolically"
regardless of input size, directing executors to proven `@[simp]`
lemmas or `example : ... := rfl` instead. `collapseFunctor` must be
computable (no `noncomputable`), so its morphism map produces the
`ERMorN` from the route T/L substance — a normalizer- or
simulator-clocked construction, exactly the composite class the
pitfall names (the project-memory precedent is
`(ERMor1.tuplePack 1).interp` failing to kernel-reduce). The step
as written risks prescribing a non-terminating test.

Required fix: state the test via the interpretation-equality lemma
the Phase 6 route provides (an `example`/theorem that the image's
interpretation equals the collapse denotation, applied at small
values), or record why the specific image of doubling is expected
to kernel-reduce.

## Nit findings

### R2-N1: naming-rule commentary inside a binding docstring

Location: Task 2.1 interface block, `RType.IsObj` docstring.

Evidence: "(paper section 2.3; UpperCamelCase per the mathlib
naming rule for Prop-valued definitions)". The parenthetical is
process commentary about the identifier's casing, not a description
of the object; interface blocks are binding for semantic content,
and an executor will transcribe it into the committed docstring,
where it fails "document only the persistent" (the rule's
application is visible from the name itself).

Required fix: move the naming-rule note into plan prose (it already
exists in the R1-m3 record) and keep the docstring mathematical.

### R2-N2: decision 5 attributes s6.1 names to "the spec's s4.2 sketch names"

Location: "Decisions fixed by this plan", decision 5.

Evidence: the list "(`SortedSig`, `Tm`, `standardModel`,
`interpSetoid`, `QuotRel`, `SynCat`, `RType`, `higherOrder`,
`SynCatFO`, `collapseFunctor`, `ramified_definability`)" is
introduced as "The spec's s4.2 sketch names". `SynCatFO`,
`collapseFunctor`, and `ramified_definability` appear in spec s6.1,
not s4.2.

Required fix: cite "s4.2 and s6.1 sketch names" (or split the list).

### R2-N3: generic `SynCatFO` docstring asserts instantiation-specific content

Location: Phase 6 "Final boundary item" block, `SynCatFO` docstring.

Evidence: `SynCatFO (P : Presentation) (r : QuotRel P.sig)` is
generic in `P`, but its docstring asserts "morphisms denote numeric
functions through `natFreeAlgEquiv`", which holds only at the
`higherOrder natAlgSig` instantiation (a general `P`'s carrier is
not `ℕ`).

Required fix: state the copy-of-the-carrier fact generically and
attach the `natFreeAlgEquiv` reading to the instantiation (the
`collapseDenotation` comment already carries it).

## Verification coverage

Checked and found correct (not repeated as findings):

- `QuotRel` well-formedness: `(rel Γ s) t t'` elaborates via
  mathlib's `CoeFun (Setoid α) (fun _ ↦ α → α → Prop)`
  (`Mathlib/Data/Quot.lean:35` at the pin); the `(rel Δ _)` sort
  argument is inferable from `σ i : Tm sig Δ (Γ.get i)`; the
  two-sided congruence shape is sufficient for Task 1.5's assembly
  (quotient composition well-definedness needs exactly two-sided
  substitution congruence; the category and chosen-product laws
  hold strictly pre-quotient via `subst_id`/`subst_subst` and
  componentwise pairing, so no further congruence field is needed);
  the interpretative instantiation's `subst_congr` is dischargeable
  from `eval_subst` as Task 1.4 claims.
- `SynCat`/`RMRecCat` arity consistency: every occurrence is
  two-argument or routed through the two-argument `RMRecCat` abbrev
  (Tasks 1.5, 2.2 Step 3, 2.3, 3.2, 4.1 `foInclusion`, 5.5, the
  Phase 6 block, Tasks 7.1/7.2); `interpQuotRel _` in the
  `collapseFunctor` signature is inferable by unification with
  `SynCatFO`'s expected argument.
- `IsObj` rename complete: grep finds no lowercase `isObj` anywhere
  in the plan, including test descriptions and the `ObjCtx`
  docstring; `constructorSig`/`dstrCaseSig` arguments and the
  `Presentation` field align.
- Names introduced or changed since round 1, against the re-fetched
  naming guide: `QuotRel` (structure, UpperCamelCase), `subst_congr`
  (proof-valued field, snake_case), `interpQuotRel` (term-valued
  def, lowerCamelCase), `RType.IsObj` and the `Presentation.IsObj`
  field (Prop-valued, UpperCamelCase per "functions are named the
  same way as their return values"), `SynCatFO` (Type-valued def,
  UpperCamelCase; the acronym cased as a group),
  `instance : collapseFunctor.Faithful` (generalized dot notation
  on a `Functor`-typed term, mathlib idiom) — all conform.
- Repository names newly load-relevant this round exist at the pin:
  `erToKFunctor` (`GebLean/LawvereERKSim/ErToKFunctor.lean:182`),
  `kToERFunctor` (`GebLean/LawvereKSimER.lean:384`), `ERMorN` /
  `erMorNSetoid` (`GebLean/LawvereERQuot.lean`).
- Gate ordering after the R1-M1 fix: the how-to bullet, the Phase 1
  map row, Task 6.0 Step 1, and the Phase 0 preamble are mutually
  consistent (Phase 5's row dropping the gate clause is subsumed by
  Phase 1's); the remaining Task 5.0 contradiction (R2-M1) concerns
  the Phase 3 dependency, not gates.
- The R1-M3 restatement: the Phase 6 substance paragraph is now
  stated over `RMRecCat natAlgSig` tuples, and the file structure
  table's `Soundness` row, the Phase 6 block, and Task 7.1's
  consumes/produces split agree on the `Collapse.lean` contents.
- The R1-m5 exemption is scoped to the never-pushed spike branch
  and preserves an inspectable checkpoint discipline; it does not
  weaken the triad elsewhere.
- Task 5.2's revised deliverable matches spec s4.2's summand sketch
  and s4.3's reduction-between-variants reading, with `AlgSig` in
  place of the spec's provisional `PolyFunctorData` consistently
  with decision 5 and `constructorSig`.
- Commit messages added or changed by the fix (`chore(ramified):
  spike syntax layer, A versus B (throwaway)`) are imperative,
  lowercase, in-list; the plan's `docs(...)` type matches this
  repository's established convention on `main` (accepted in
  round 1).
- Markdownlint/doctoc invocations and the jj spike-abandon sequence
  are unchanged from the forms round 1 verified.
