# Ramified recurrence plan review, round 1

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Blocker findings](#blocker-findings)
  - [R1-B1: `SynCat` drops the spec's quotient-relation parameter](#r1-b1-syncat-drops-the-specs-quotient-relation-parameter)
- [Major findings](#major-findings)
  - [R1-M1: gate-ordering contradiction between how-to text and map](#r1-m1-gate-ordering-contradiction-between-how-to-text-and-map)
  - [R1-M2: Phase 5 dependency omits Phase 3 (`natFreeAlgEquiv`)](#r1-m2-phase-5-dependency-omits-phase-3-natfreealgequiv)
  - [R1-M3: Phase 6 deliverable is stated via a Phase 7 artifact](#r1-m3-phase-6-deliverable-is-stated-via-a-phase-7-artifact)
  - [R1-M4: no faithfulness artifact in Task 7.1's binding interface](#r1-m4-no-faithfulness-artifact-in-task-71s-binding-interface)
- [Minor findings](#minor-findings)
  - [R1-m1: G2 Step 2 measure references imply the wrong file](#r1-m1-g2-step-2-measure-references-imply-the-wrong-file)
  - [R1-m2: `Σ` is not a legal Lean 4 identifier in binding blocks](#r1-m2-%CF%83-is-not-a-legal-lean-4-identifier-in-binding-blocks)
  - [R1-m3: `RType.isObj` violates the Prop-valued naming rule](#r1-m3-rtypeisobj-violates-the-prop-valued-naming-rule)
  - [R1-m4: `spike(ramified)` commit type is out of the allowed list](#r1-m4-spikeramified-commit-type-is-out-of-the-allowed-list)
  - [R1-m5: the pre-commit triad forbids blocked-spike checkpoints](#r1-m5-the-pre-commit-triad-forbids-blocked-spike-checkpoints)
  - [R1-m6: file structure table places `natAlgSig` in two files](#r1-m6-file-structure-table-places-natalgsig-in-two-files)
  - [R1-m7: Task 5.2's `dstrCaseSig` realization is ambiguous](#r1-m7-task-52s-dstrcasesig-realization-is-ambiguous)
- [Nit findings](#nit-findings)
  - [R1-N1: `CategoryData` line reference off](#r1-n1-categorydata-line-reference-off)
  - [R1-N2: "load-bearing" metaphor in plan prose](#r1-n2-load-bearing-metaphor-in-plan-prose)
- [Verification coverage](#verification-coverage)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Verdict: NOT CONVERGED (1 blocker, 4 major, 7 minor, 2 nit).

Document under review:
`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`.
Reviewed against the user-approved spec
(`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`),
`CLAUDE.md`, `.claude/rules/lean-coding.md`,
`.claude/rules/markdown-writing.md`, the mathlib naming and style
guides (re-fetched this round), and the repository sources at the
current pin (`leanprover/lean4:v4.29.0-rc6`, confirmed against
`lean-toolchain` and `lakefile.toml`).

## Blocker findings

### R1-B1: `SynCat` drops the spec's quotient-relation parameter

Location: Task 1.5, interface block and assembly plan.

Evidence: the plan's binding interface, marked "from spec s4.2",
reads:

```lean
-- SynCat (P : Presentation) : Type       -- := Ctx P.S
-- instance : Category (SynCat P)         -- Hom = tuples of terms
--                                        --   modulo interpSetoid;
```

The spec's s4.2 declares the construction relation-parametric and
states this in prose, not merely in the sketch: "The quotient
relation is a parameter of the construction, instantiated in this
workstream with the interpretative setoid; the deferred equational
workstream (section 9) re-instantiates the same construction with a
`Derivable`-style relation", with the sketch signature
`SynCat (Σ : SortedSig S) (r : QuotRel Σ)`. Spec s9's deferred
workstream depends on that parameter ("re-instantiate the
section-4.2 syntactic-category construction with a
`Derivable`-style relation"). The plan hard-wires `interpSetoid`
into the `Category` instance, removes the relation parameter, and
records no decision superseding the spec on this point (decisions
1-7 do not mention it). Interface blocks are declared "binding for
names, arities, and semantic content", so this is not an
elaboration-time adjustment.

Required fix: restore the quotient relation as a parameter of the
generic construction (e.g. `SynCat (P : Presentation)
(r : QuotRel P.sig)` or the spec's own shape), with the
interpretative setoid as the in-scope instantiation — or, if the
plan intends to specialize, add an explicit numbered decision with
justification and a spec-reconciliation step; silent deviation from
spec s4.2 prose is not admissible.

## Major findings

### R1-M1: gate-ordering contradiction between how-to text and map

Location: "How to work this plan", Phase order bullet, versus the
phase map.

Evidence: the how-to bullet states "Phase 0 gates G1-G4 close
before any Phase 1 commit (G5 is non-blocking)". The phase map row
for Phase 1 states "Depends on: G3" only, and the Phase 5 row
separately restates "G1-G4 closed", showing the "Depends on" column
is used for gate closure elsewhere. An executor asking whether
Phase 1 may begin while the G1 literature investigation is pending
receives opposite answers from the two places.

Required fix: make the two agree. Either Phase 1 is blocked on G3
only (change the how-to bullet to say G3 closes before any Phase 1
commit, with G1/G2/G4 blocking Phases 5/6 as the map has it), or
all of G1-G4 block Phase 1 (change the Phase 1 map row). One
reading must be chosen and stated in both places.

### R1-M2: Phase 5 dependency omits Phase 3 (`natFreeAlgEquiv`)

Location: phase map row for Phase 5; "How to work this plan";
Task 5.5.

Evidence: the phase map declares Phase 5 "Depends on: 2; G1-G4
closed (branch stacked after 4)" and the how-to bullet says "The
Phase 5 sub-plan is written after Phase 2 lands (it consumes the
example ladder)". But Task 5.5's binding interface consumes a
Phase 3 artifact: "ramifiedDenotation: standard-model
interpretation read through `natFreeAlgEquiv` (Phase 3)", and
Task 3.1 itself calls `natFreeAlgEquiv` "the numeric glue the
Phase 5/7 statements against LawvereERCat compose with". Phases 3
and 4 "may be developed ... in parallel branches", so "stacked
after 4" does not by itself guarantee Phase 3 is in Phase 5's
ancestry, and the sub-plan writer is told to start after Phase 2
when a consumed artifact shape lands only in Phase 3.

Required fix: add Phase 3 to Phase 5's dependency row, and state
that the Phase 5 sub-plan is written after Phases 2 and 3 land (or
move `natFreeAlgEquiv` into a phase Phase 5 already depends on).

### R1-M3: Phase 6 deliverable is stated via a Phase 7 artifact

Location: Phase 6, "Deliverable either route" paragraph; file
structure table.

Evidence: the deliverable reads "for every morphism of
`SynCatFO (higherOrder natAlgSig)`, an `ERMorN` whose
interpretation equals the morphism's collapse denotation". But
`SynCatFO` is created in Task 7.1 (`Characterization.lean`,
Phase 7, per the file structure table), and Phase 7 depends on
Phases 5 and 6. As written, the Phase 6 sub-plan's boundary
statement names a declaration that cannot exist when Phase 6
executes.

Required fix: either state the Phase 6 deliverable directly over
the Phase 2 artifacts (for every tuple of terms between object-sort
contexts of `RMRecCat natAlgSig`, an `ERMorN` with matching
denotation), or move the `SynCatFO` definition into Phase 6 (or
earlier) and update the file structure table accordingly.

### R1-M4: no faithfulness artifact in Task 7.1's binding interface

Location: Task 7.1, interface block and Step 2.

Evidence: spec s6.1's first statement is "`collapseFunctor`
well-defined and faithful", and the plan's goal repeats it. Task
7.1's binding interface block contains only `SynCatFO`,
`collapseFunctor`, and `ramified_definability`; Step 2's implement
list ("`SynCatFO` ..., `collapseDenotation`, `collapseFunctor` ...,
`ramified_definability` ...") likewise names no faithfulness
declaration. Step 1's "faithfulness `example` on a pair of
distinct-denotation morphisms" is a test on one pair, not the
statement. Well-definedness is discharged by the functor's
construction, but faithfulness is a theorem that must exist as a
named artifact for the spec's statement 1 to be formalized.

Required fix: add the faithfulness statement to Task 7.1's binding
interface (e.g. `instance : collapseFunctor.Faithful` via mathlib's
`CategoryTheory.Functor.Faithful`, or an equivalent named theorem)
and to Step 2's implement list.

## Minor findings

### R1-m1: G2 Step 2 measure references imply the wrong file

Location: Task G2, Step 2.

Evidence: "Compare `GodelTTerm.lh` (:22), `.d` (:42), `.G` (:61),
`.bracketLevel*` (:95-:131)" gives bare line numbers whose only
antecedent file is Step 1's `GebLean/LawvereGodelTReduces.lean`.
The declarations actually live in
`GebLean/LawvereGodelTLemma16.lean` (verified: `GodelTTerm.lh` at
:22, `.d` at :42, `.G` at :61, `bracketLevelAppGen` :95,
`bracketLevelAppIter` :110, `bracketLevel` :131 of that file);
`LawvereGodelTReduces.lean:95` is `Reduces.Star`, not a measure.

Required fix: name `GebLean/LawvereGodelTLemma16.lean` explicitly
in Step 2.

### R1-m2: `Σ` is not a legal Lean 4 identifier in binding blocks

Location: Task 1.3 and Task 1.4 interface blocks.

Evidence: the blocks bind signatures such as
`structure SortedModel (Σ : SortedSig S)` and
`Tm.op : (o : Σ.Op) → ...`. Lean 4 rejects `Σ` as a binder name
(verified this round: `structure Foo (Σ : Nat)` elaborates to
"unexpected token 'Σ'; expected '_' or identifier" at the current
pin). The plan's escape clause covers only "implicit-argument
placement and universe annotations", not binder renames, so the
binding blocks as written cannot be transcribed.

Required fix: rename the signature binder in the interface blocks
(e.g. `Sg`, `sig`, or a letter per the style guide's variable
conventions) and extend the escape clause to cover binder names.

### R1-m3: `RType.isObj` violates the Prop-valued naming rule

Location: Task 2.1 interface block (also `Presentation.isObj`,
Task 1.4; `constructorSig`'s `isObj` argument, Task 1.2).

Evidence: `def RType.isObj : RType → Prop`. The mathlib naming
guide (re-fetched this round) puts `Prop`- and `Sort`-valued
definitions in `UpperCamelCase` ("Functions are named the same way
as their return values"; `Prop`s in `UpperCamelCase`), as in
`Nat.Prime`, `Function.Injective`. The plan itself follows that
rule two phases later with `RIdent.FirstOrder : ... → Prop`
(Task 4.1), so the two binding names are mutually inconsistent.

Required fix: rename to `RType.IsObj` (and align the
`Presentation` field and helper arguments, or record a deliberate
field-naming exception).

### R1-m4: `spike(ramified)` commit type is out of the allowed list

Location: Task G3, Step 1 command block.

Evidence: `jj new -m "spike(ramified): syntax-layer spike A vs B
(throwaway)" <tip>`. The commit-message convention bound by the
plan's own global constraints and `.claude/rules/lean-coding.md`
fixes the type list `feat | fix | doc | style | refactor | test |
chore | perf | ci`; `spike` is not in it. The guides bind all
commit messages; no exemption for throwaway branches is recorded.

Required fix: use an in-list type (e.g. `chore(ramified): spike
syntax layer, A versus B (throwaway)`), or record an explicit
exemption for never-pushed spike commits in the plan's global
constraints.

### R1-m5: the pre-commit triad forbids blocked-spike checkpoints

Location: Global constraints; Task G3 spike target paragraph.

Evidence: the global constraints require the pre-commit triad
"before every commit touching a `.lean` file", with no spike
exemption. Task G3 says "each spike stops at two working days'
effort or at a demonstrated blocker, whichever is first; partial
completion is itself evidence". A spike stopped at a demonstrated
blocker generally does not compile (the plan's own placeholder
policy makes unfilled holes elaboration errors), so its state can
never be committed on the spike branch under the constraint, and
Step 5's fragment extraction is the only preservation path — which
the plan does not acknowledge as the consequence.

Required fix: state the resolution: either exempt the throwaway
spike branch from the triad (it is abandoned, never merged), or
instruct that blocker states are checkpointed with the failing
fragment commented out and the blocker recorded inline.

### R1-m6: file structure table places `natAlgSig` in two files

Location: File structure table.

Evidence: the `GebLean/Ramified/AlgSig.lean` row lists "`AlgSig`,
`FreeAlg`, `natAlgSig`" (Phase 1) and the
`GebLean/Ramified/Algebras.lean` row lists "`natAlgSig`,
`binWordAlgSig`, `treeAlgSig`, ..." (Phase 3). Task 3.1's block
says "natAlgSig is Phase 1's; this task adds:", contradicting the
Algebras.lean row.

Required fix: remove `natAlgSig` from the Algebras.lean row (or
replace it with a note that the instantiations cover it).

### R1-m7: Task 5.2's `dstrCaseSig` realization is ambiguous

Location: Task 5.2 deliverable.

Evidence: "`dstrCaseSig` (spec s4.2 sketch) realized as derived
identifiers; the two-way definability reduction between the
flat-recurrence presentation and the destructor/case presentation
... as interpretation-preserving translations". The spec sketch
declares `dstrCaseSig : SortedSig S` — a signature summand, i.e. a
presentation ingredient. If `dstr`/`case` exist only as derived
identifiers inside the flat presentation, the destructor/case
presentation is not an object and the "two-way reduction between
presentations" has nothing to translate from. One consistent
reading exists (the summand exists as a signature; one direction
realizes its operations as derived identifiers; the other realizes
flat recurrence over the summand), but the deliverable does not say
which structure the sub-plan must produce.

Required fix: state whether `dstrCaseSig` is produced as a
`SortedSig` summand (per the spec sketch) with translations in both
directions, and what "realized as derived identifiers" binds the
sub-plan to.

## Nit findings

### R1-N1: `CategoryData` line reference off

Location: Task 1.5 assembly plan.

Evidence: "(`CategoryData`, `CategoryOfData` at :222)" in
`GebLean/Utilities/Category.lean`. `CategoryOfData` is at :222;
`CategoryData` is at :199.

Required fix: cite ":199/:222" or drop the shared line number.

### R1-N2: "load-bearing" metaphor in plan prose

Location: Task 1.3 Step 2 ("The clone laws are the load-bearing
content"); Task G3 Step 5 ("the abandoned branch is not
load-bearing").

Evidence: `CLAUDE.md` § Style guidelines: "Avoid colloquialisms
and metaphors." "Load-bearing" is a structural-engineering
metaphor; neither the spec nor the repository docs use it.

Required fix: replace with literal phrasing (e.g. "the clone laws
are the content the syntactic category's composition depends on";
"no downstream artifact depends on the abandoned branch").

## Verification coverage

Checked and found correct (not repeated as findings):

- Spec s6.1 fidelity: both statements targeted at `LawvereERCat`;
  `ramified_definability` an existential over object-sort contexts,
  fullness explicitly denied; K^sim_2 transfer at statement level.
- Spec s6.2 chain (Tasks 5.1-5.5), including the arity remark
  (componentwise assembly, clock over all inputs) and the eq. (8)
  `Omega(eta -> eta)` input sort.
- Spec s6.3 two-precondition gate realized as G1 (published bridge
  only) and G2 (clause-by-clause audit), G2 conditional on G1;
  route L matches spec steps 1-3 plus the s6.4 landing; G4 after
  G1/G2 with the spec's default landing.
- Spec s7 spikes: throwaway, both A and B, monadic first-order
  target over `1 + X`, before any Phase 1 representation commit;
  C recorded as convergence target; B as equivocal-evidence
  default.
- Spec s8 items 1-7 map one-to-one onto Phases 1-7.
- Open questions: 1 (G1), 2 (G4), 4 (G3 / decision 7),
  5 (decision 6 / G3), 6 (G5) assigned; 3 and 7 asserted nowhere
  (Tasks 2.3 and 7.1 explicitly decline them).
- No withdrawn content smuggled in: no machine-free routes, no
  equational presentation, no first-order complexity claims, no
  separate first-order implementations (Phase 4 restricts the
  signature, not the objects), no equivalence-of-categories
  packaging.
- Repository ground truth (all verified at the stated lines):
  `compileER` Compiler.lean:1590; `compileER_pre_stop_correct`
  Top.lean:55 and `compileER_runFor` Top.lean:89 with the quoted
  statement shapes; `boundExprKParams_dominates`
  RuntimeBound.lean:225 quoted verbatim; `tower` Tower.lean:17 with
  the quoted equations; ZeroTestURM.lean:89/122/143/155/179/254
  (`URMInstr` constructors, `URMProgram` fields including
  `inputRegs_inj` and `outputReg_not_input`, `URMState`, `step`,
  `runFor`, `init`); `simulate` KSimURMSimulator.lean:544,
  `simulate_interp` :948, `simulate_level` :961; `erKSimEquiv`
  Equivalence.lean:183 with round-trip equalities :96/:126;
  `erMorNSetoid` LawvereERQuot.lean:23; `ERMor1` LawvereER.lean:36
  and `.interp` :82; `KMor1.simrec` LawvereKSim.lean:50 and
  `simrecVec` LawvereKSimInterp.lean:66; `quotientFunctor`
  SetoidCat.lean:137; `PolyFunctorBetweenCat` Polynomial.lean:956;
  `PolyEndo` PolyAlg.lean:55; `PolyFix` :176; `polyFixFold` :359;
  `polyFixAlg_isInitial` :533; `polyBetweenCoprod`
  PolyUMorph.lean:422; `algCoprodDesc` PolyAlgUMorph.lean:418;
  `GodelTTerm` LawvereGodelTTerm.lean:26; `GodelTType.level`
  LawvereGodelT.lean:47; `GodelTTerm.Reduces` Reduces.lean:21,
  `Star` :95, `Equiv` :122; the Lemma 16 family
  (`majorizes_redP_zero` :440, `majorizes_redP_succ` :466,
  `majorizes_redK` :527, `majorizes_redDisc_zero` :582,
  `majorizes_redDisc_succ` :652, `majorizes_redTreeIter_leaf` :823,
  `dominates_app` :926, `majorizes_redIter_zero` :1355,
  `majorizes_redIter_succ` :1413, `majorizes_redTreeIter_node`
  :1818) and closure lemmas (:905-:1101); `Era.Tm.subst_id` /
  `subst_subst` Era.lean:88/:96. Toolchain and mathlib/cslib pins
  match `lean-toolchain` / `lakefile.toml` (`v4.29.0-rc6`).
- Internal name coherence across phases for `AlgSig`, `natAlgSig`,
  `higherOrder`, `RMRecCat`, `kappaHat`, `ramTwoPow`, `ObjCtx`,
  `oCtx`, `collapseDenotation`, `natFreeAlgEquiv` (modulo R1-M2).
- Glossary vocabulary: "critical arguments" appears only where the
  paper's term is being named; the Omega-license phrasing matches
  the spec's glossary; parameters / recurrence argument / subterms /
  recursive results / step functions used per the glossary.
- Mathematical assertions beyond the spec: the eq. (4) constraint
  as `mrec` indices with strictly-above derived via coercions
  matches the spec's orientation section; the `tower` equations
  quoted for the `ramTwoPow` alignment match Tower.lean, with the
  exact correspondence hedged as the lemma to state; the
  `standardModel`-as-data refactor is sound (a generic
  `standardModel` construction over an abstract sort type is not
  definable; the field plus `higherOrder`-supplied construction
  realizes the spec's intent) and is documented in the interface.
- Process commands: pre-commit triad and pre-push invocations,
  `markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs`,
  doctoc usage, and the jj spike-abandon sequence (revset
  `docs/...-approaches..spike/ramified-syntax`, bookmark delete)
  are correct for this repository (modulo R1-m4/R1-m5).
