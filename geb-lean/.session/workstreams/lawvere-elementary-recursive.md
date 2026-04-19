# Workstream: Lawvere Theory of Elementary Recursive Functions

## Status

Phase 0 design complete.  Phase 1 complete: see
`GebLean/LawvereER.lean` for the inductive term type,
interpretation, computation lemmas, `ERMorN` tuple type,
and identity/composition, plus `GebLeanTests/LawvereER.lean`
for the `#guard` sanity tests.  Phase 2 complete: see
`GebLean/LawvereERQuot.lean` for the extensional-equality
setoid, quotient type `ERMorNQuo`, lifted identity and
composition, category laws, and the `Category` instance on
`LawvereERCat`, plus `GebLeanTests/LawvereERQuot.lean` for
sanity tests.  Phase 3 complete: see
`GebLean/LawvereERQuot.lean` for the
`HasChosenFiniteProducts` instance (terminal,
projections, pairing, product laws) and
`GebLean/LawvereERInterp.lean` for
`erInterpFunctor` and its `Faithful` instance.
Phase 4a complete: see `GebLean/LawvereERLex.lean`
for `ERBoolPred`, `LexObj`, the subtype-plus-quotient
morphism construction, category laws, and the
`Category` instance on `LawvereERLexCat`.
Phase 4b complete: see `GebLean/LawvereERBool.lean`
for `boolNot`, `boolAnd`, `subSwap`, and `boolEqNat`
ER terms with `@[simp]` interpretation lemmas and
Boolean closure properties; `GebLean/LawvereER.lean`
extended with `zeroN`, `oneN` constants and the
`natBSum_const` arithmetic helper.  Phase 4c
complete: see `GebLean/LawvereERLex.lean` extended
with `ERBoolPred.and`, `LexObj.terminal`,
`LexObj.prod`, projections `pi1`/`pi2`, pairing,
universal-property theorems, and the
`HasChosenFiniteProducts LawvereERLexCat` instance.
Phase 4d complete: see `GebLean/LawvereERLex.lean`
extended with `ERBoolPred.alwaysTrueN`,
`ERBoolPred.andSameArity`, `ERBoolPred.allEq`
(componentwise equality predicate),
`LexObj.equalizer`, equalizer inclusion morphism,
equalization theorem, and the raw/quotient lift
constructions with the universal-property
theorems `equalizerLift_map` and
`equalizerLift_uniq`; `GebLean/LawvereERBool.lean`
extended with `ERMor1.boolEqAt`.
Phase 4d.2 complete: refactored `LexObj.pred` to
use the quotient `ERBoolPredE` (extensionally
equal predicates yield equal objects) and built
`HasChosenEqualizers` and `HasChosenFiniteLimits`
instances on `LawvereERLexCat` without
`Quotient.out` or `Classical.choice`.  Key
ingredients in `LawvereERLex.lean`: `ERBoolPredE`
quotient with `eval`/`eval_le_one`/`eval_injective`
(extensionality); `ERBoolPredE.alwaysTrue`/
`andSameArity`/`and`/`allEq` quotient combinators;
`equalizerPred_wd` showing the combined
`a.pred ⊓ allEq f g` is well-defined modulo
morphism representatives; `LexObj.equalizerQ`
(chosen equalizer object via `Quotient.liftOn₂`
on quotient morphisms); `equalizerQMap`,
`equalizerQLiftQuo` (using `Quotient.hrecOn` for
the dependent `heq` parameter), and the
universal-property theorems.
`GebLean/Utilities/ComputableLimits.lean` extended
with `ChosenEqualizer`, `HasChosenEqualizers`, and
`HasChosenFiniteLimits` classes.
Phase 4d.3 complete: see
`GebLean/Utilities/ComputableLimits.lean` further
extended with `chosenEqualizerIsLimit`,
`chosenEqualizerToHasLimit`,
`chosenToHasEqualizers`, and
`chosenToHasFiniteLimits`.  These derive Mathlib's
`Limits.HasEqualizers` and `Limits.HasFiniteLimits`
from our `Type`-valued chosen versions, validating
that the chosen-finite-limit definitions correctly
present the standard categorical notions.
Phase 4e complete: see `GebLean/LawvereERDelta.lean`
for the embedding `erDeltaFunctor : LawvereERCat ⥤
LawvereERLexCat` (sending arity `n` to the
trivially-cut-out object `(n, ⊤)`), with `Faithful`
and `Full` instances and a `PreservesFiniteProducts`
instance derived from preservation of binary
products and the terminal.  Object preservation is
on the nose: `Δ.obj 0 = LexObj.terminal` (rfl) and
`Δ.obj (n + m) = LexObj.prod (Δ.obj n) (Δ.obj m)`
(via `ERBoolPredE.eval_injective` from Phase 4d.2).
All of Phase 4 is now complete.
Phase 4f.1 complete: see `GebLean/LawvereERPrimrec.lean`
for the structural-recursion translation
`ERMor1.toPrimrec'` showing every elementary recursive
term's interpretation is `Nat.Primrec'`, and
`GebLean/LawvereERInterp.lean` for
`erInterpFunctor_not_full` deriving non-fullness
from Mathlib's `not_primrec₂_ack`.  The positive
side of the story is recorded in
`GebLean/LawvereERArith.lean`, which defines
`ERMor1.expER = bprod (proj 1)` with interpretation
`y ^ n` and the supporting `natBProd_const` helper.
Phase 4f.2 complete: see `GebLean/Utilities/Tower.lean` for
the `tower k x = 2^^k(x)` function with monotonicity,
composition, and multiplicative / power bounds;
`GebLean/LawvereERBound.lean` for the structural theorem
`ERMor1.exists_lt_tower` (every ER term is dominated by
some fixed-height tower applied to `maxCtx + 2`); and
`GebLean/LawvereERTetration.lean` for the corollary
`tetration_not_ER` (no `ERMor1 1` term computes tetration)
and the derived non-fullness theorem
`erInterpFunctor_not_full_via_tetration`.  This witnesses
the primrec / elementary gap, strengthening Phase 4f.1's
Ackermann-based non-fullness.

Phase 4g.1 complete: see `GebLean/LawvereTreeER.lean` for the
`TreeMor1` inductive with 5 constructors (leaf, branch, proj,
comp, fold), `foldDepth` by structural recursion, `toBTMor1`
translation, and the depth-tiered subtypes `TreeERMor1_0` /
`TreeERMor1_1` / `TreeERMor1` with smart constructors and
mutumorphism exposure via `mutuFold`;
`GebLean/LawvereTreeERQuot.lean` for the quotient category
`LawvereTreeERCat` with `HasChosenFiniteProducts`; and
`GebLean/LawvereTreeERInterp.lean` for the faithful
interpretation functor `treeErInterpFunctor` and the faithful
inclusion `treeErInclusion` into `LawvereBTQuotObj`.

Phase 4g.2 Stage α (Layer 1: generic Lean arithmetic) complete:
see `GebLean/Utilities/SzudzikSeq.lean` for `Nat.seqPack` /
`Nat.seqAt` (list-to-ℕ encoding via iterated right-associated
Szudzik pairing, with round-trip theorem), `Nat.treeFoldOnCode`
(course-of-values recursion on a Gödel code, proved equal to
`BT.fold` via the `PolyFreeM` induction pattern), and
`Nat.tupleRecN` (finite-arity mutumorphism).  `GebLeanTests/
Utilities/SzudzikSeq.lean` exercises each primitive via
`#guard`.  Stages β (tree-ER syntactic arithmetic in
`GebLean/LawvereTreeERArith.lean`) and γ (isomorphism in
`GebLean/LawvereTreeERLawvereEquiv.lean`) remain; the
task-by-task plan is at
`docs/superpowers/plans/2026-04-15-lawvere-treeer-subproject-4g2.md`
(local, gitignored) and the design spec is at
`docs/superpowers/specs/2026-04-15-lawvere-treeer-subproject-4g2-design.md`.
Phase 4g.2 Stage β Task 6 complete: see
`GebLean/LawvereTreeERArith.lean` for the substrate primitive
`TreeERMor1.treeFoldOnCode : TreeERMor1_0 0 → TreeERMor1_0 2
  → TreeERMor1_1 1` packaging course-of-values recursion on a
BT input, with the `@[simp]` agreement theorem
`TreeERMor1.treeFoldOnCode_interp` linking interpretation to
`Nat.treeFoldOnCode` via `encodeBT` / `decodeBT`.  The
extracted `BT.ind` structural induction principle lives in
`GebLean/LawvereBTInterp.lean` (alongside `BT.cases`), along
with `finAppend_fin1_left` / `finAppend_fin1_right` simp
lemmas in `GebLean/LawvereBT.lean`.  Stage β was reordered so
that `treeFoldOnCode` (previously Task 10) precedes the
arithmetic primitives that depend on it (`succOnCode`,
`subOnCode`, `szudzikPair`, `szudzikUnpair`, `bsumOnCode`,
`bprodOnCode`, now Tasks 7–10 plus Task 11's
`mutuFoldViaPair`).  Phase 4g.2 Stage β Task 7 complete: see
`GebLean/Utilities/SzudzikSeq.lean` for
`Nat.mutuTreeFoldOnCode` (multi-slot course-of-values on a
code) with correctness vs `BT.fold` over the `Fin m → α`
carrier, and `GebLean/LawvereTreeERArith.lean` for
`TreeERMor1.mutuFoldOnCode : ∀ m, (Fin m →
TreeERMor1_0 1) → (Fin m → TreeERMor1_0 (m + m)) → Fin m →
TreeERMor1_1 1` with its `@[simp]` agreement theorem.
Stage β's plan was then restructured and ultimately
**superseded** after extensive analysis.  The sequence of
discoveries:

1. A direct `succOnCode` attempt (original Task 8) confirmed
   a Szudzik-polynomial barrier at depth 1.  A register-
   machine simulation blueprint (Task 9) built in commits
   `a744a036` / `8eb7d38d` extended the substrate but still
   required a depth-0 Szudzik step that could not be built.
2. Bibliography check of Leivant 1999 (at
   `.claude/docs/ramified-recurrence-computational-complexity-iii.pdf`)
   revealed that first-order polyadic ramified recurrence
   (what our `TreeMor1` fragment captures at any depth)
   equals **polynomial time**, not E₃, per references [4]
   (Bellantoni-Cook 1992) and [24] (Leivant 1994).  The
   original design decision D2's attribution of "depth-2
   fold = E₃" to Beckmann-Weiermann 2000 was incorrect —
   B-W 2000 is not cited in Leivant's 1999 paper.  Leivant's
   main result (higher-order ramified = E₃) requires type-
   level structure not present in our first-order
   `TreeMor1`.
3. Research on B-W 2000 (agent `a7d9d0a2bf23f09f6`) confirmed
   that their T* fragment requires higher-order types with
   ground-`N`-applied recursors.  Research on LOOP programs
   on trees (agent `af63fb16c4bef6c83`) confirmed that
   existing Meyer-Ritchie Grzegorczyk results transport to
   trees only under chain / size encodings, and require
   separate formalization.
4. Per the user's direction, a two-sorted design resolves
    the obstruction: keep ℕ arithmetic on a ℕ sort (using
    `LawvereER`'s E₃-generating set as-is), keep BT
    structural operations on a BT sort (poly-time on tree
    size, a subset of E₃), bridge them with explicit
    `encodeBT`/`decodeBT` morphisms.  The combined theory has
    class E₃ by construction.  The relationship with
    `LawvereER` is a **categorical equivalence**, not an on-
    the-nose isomorphism — "same computational strength,
    different representations" is precisely the content of
    equivalence.  Labeled trees (with ℕ at leaves) emerge
    naturally; unlabeled and finite-alphabet trees are
    decidable subobjects in the lex completion.

Phase 4g.2's pre-supersession artifacts (Tasks 1–7's Layer 1
infrastructure in `GebLean/Utilities/SzudzikSeq.lean`, Task 6's
`TreeERMor1.treeFoldOnCode` substrate in
`GebLean/LawvereTreeERArith.lean`, Task 7's `mutuFoldOnCode`,
Task 9's register-machine blueprint in
`GebLean/Utilities/RegisterMachine.lean` and the `simulateRM`
combinator) remain in the codebase as preserved research
infrastructure — they are parallel developments to the new
`LawvereNatBT` sub-project and not directly used by it.  The
Phase 4g.1 `LawvereTreeERCat` single-sort unlabeled theory
also remains as a parallel development and embeds into
`LawvereNatBT` as the "all leaves labeled 0" decidable
subobject.

### New sub-project: `LawvereNatBT` (supersedes 4g.2)

Design spec:
`docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`
(local, gitignored).

Implementation plan:
`docs/superpowers/plans/2026-04-17-lawvere-natbt.md` (local,
gitignored).  25 tasks across three stages:

* **Stage α** (Tasks 1–10): base theory.  `BTL` labeled tree
    type; `NatBTMor1` two-sort term inductive; interpretation;
    `NatBTMorN` tuples; extensional-equality quotient
    `NatBTMorNQuo`; `Category LawvereNatBTCat`;
    `HasChosenFiniteProducts`; interp functor into `Type`;
    Stage α tests.
* **Stage β** (Tasks 11–20): three-stage factorization
    `LawvereERCat ≅ LawvereNatBTPureCat ≃ LawvereNatBT0Cat ≃
    LawvereNatBTCat`.  The four categories (in current
    code/naming) are:
  * **`LawvereNatBTCat`** ("TreeER") — the two-sort base.
  * **`LawvereNatBT0Cat`** ("Tree0ER") — `FullSubcategory` on
    `m = 0` objects.  Hom-sets inherit from parent and may
    contain morphism classes whose representatives use
    `encodeBT`/`foldBTNat` internally.
  * **`LawvereNatBTPureCat`** ("TreeNatER") — strict-ER
    fragment: morphism classes containing some representative
    whose every sub-term is in the strict-ER fragment.  Hom-set
    carriers are 1-1 with `ERMorNQuo`.
  * **`LawvereERCat`** ("NatER") — the existing ℕ-only theory.
  
    Tasks:
  * Task 11 (DONE, commit `4f806f6d`): `LawvereNatBT0Cat`
      `FullSubcategory` with restricted
      `HasChosenFiniteProducts`.
  * Task 12: originally ER-derived `Nat.pair`/`Nat.unpair` only;
      now restructured as the "ER-Primrec" mini-phase — a
      chain of sub-tasks 12a-12f building derived ER
      primitives culminating in `ERMor1.natRec`, the
      Wikipedia-literal primitive-recursion combinator built
      via Gödel β-function and bounded search.  Detailed
      design:
      `docs/superpowers/specs/2026-04-17-er-primrec-design.md`
      (local, gitignored).  The mini-phase renames
      `Utilities/ERTreeArith.lean` → `Utilities/ERArith.lean`
      (Task 12a) and adds `ERMor1.div`, `ERMor1.mod` (12b),
      `ERMor1.beta` + `Nat.beta_exists` (12c),
      `ERMor1.boundedSearch` (12d), `ERMor1.natRec` + the
      `Nat.rec` correctness theorem (12e), and showcase
      applications `ERMor1.natAdd`/`natMul`/`factorial` (12f).
      Task 12 of the original plan (`natPair`/`natUnpair`/
      `natSqrt`, already complete at commit `29553fd0`)
      becomes the landed starting point for this mini-phase.
  * Task 13: re-creates `Utilities/ERTreeArith.lean` with
      BTL-specific ER tools on top of `natRec`.  `Nat.
      foldBTLOnCode` (Task 13 Part 1, already DONE at commit
      `3eebf595`) remains in `Utilities/SzudzikSeq.lean`.
      `ERMor1.foldBTLOnCode` (Task 13 Part 2) is defined via
      `natRec` plus parity-based case analysis on the code.
      Also provides `ERMor1.btlEncodeLeaf`,
      `ERMor1.btlEncodeNode` supporting primitives.
  * Task 14: `NatBTMor1.toER` and `NatBTMor1.toER_bt`
      (mutually recursive structural back-translation), with
      extensional correctness.  In new
      `GebLean/LawvereNatBTBackTrans.lean`.  This is the
      substrate of Stage 2's equivalence.
  * Task 15: `LawvereNatBTPureCat` thin wrapper around
      `LawvereERCat`, with on-the-nose Stage 3 iso
      `natBTPureEquivalence`.  In new
      `GebLean/LawvereNatBTPure.lean`.
  * Task 16: Stage 1 essential surjectivity via Szudzik on
      objects (`natBTPack`/`natBTUnpack`/`natBTIsoPack`).
      Packages as `natBTSubInclEquiv : LawvereNatBT0Cat ≌
      LawvereNatBTCat`.  In new
      `GebLean/LawvereNatBTEquiv.lean`.
  * Task 17: Stage 2 equivalence
      (`natBTPureTree0Equiv : LawvereNatBTPureCat ≌
      LawvereNatBT0Cat`) via `naturalInclusion`/`backTranslate`
      pair using Task 14's back-translation.
  * Task 18: Compose three stages into
      `natBTEquivalence : LawvereERCat ≌ LawvereNatBTCat`.
  * Task 19: Transport Phase 4f.1 Ackermann non-fullness and
      Phase 4f.2 tetration non-elementarity across the
      equivalence.
  * Task 20: Register Stage β + tests.
  
    The three-stage factorization keeps Szudzik encoding work
    in two distinct places:
  * **Stage 1** uses NatBT-internal `encodeBT`/`decodeBT`
      generators only (no ER-side work).
  * **Stage 2** uses ER-derived Szudzik primitives (Tasks
      12-13) plus the back-translation (Task 14) — the
      substantive new work that Phase 4g.2's preserved
      `Utilities/SzudzikSeq.lean` infrastructure provides
      Layer-1 ingredients for.
  
    Tasks 12, 13, 14, 17, 18 are flagged proof-heavy.  Tasks 15,
    16, 19 are moderate.
* **Stage γ** (Tasks 21–24): lex completion
    `LawvereNatBTLexCat` with decidable subobjects; unlabeled
    and finite-alphabet tree subtypes; faithful embedding
    `LawvereTreeER ↪ LawvereNatBT`; Stage γ tests.
* **Finalization** (Task 25): workstream tracker update.

Progress so far (as of end of this session):

* **Task 1 complete** (commits `24f0fd18`, `990b63a4`):
    `GebLean/LawvereNatBT.lean` with `BTL` inductive,
    `BTL.fold` catamorphism, `BTL.encode`, `BTL.decode`, and
    round-trip theorems `BTL.decode_encode`,
    `BTL.encode_decode`.  Module registered in `GebLean.lean`.
* **Task 2 complete** (commit `104e52b1`): `NatBTSort`
    discriminator, `NatBTSort.carrier`, and `NatBTMor1`
    two-sort term inductive with all 14 specified
    constructors (zero, succ, natProj, sub, compNat, bsum,
    bprod, leafBT, nodeBT, btProj, compBT, foldBTNat,
    foldBTBT, encodeBT, decodeBT).
* **Stage α complete** (commits `49359feb..193563a6`,
    nine commits including the bsum/bprod/foldBTNat
    signature-fix preamble): `NatBTMor1.interp` plus
    per-constructor `@[simp]` lemmas (Task 3); `NatBTMorN`
    tuples with id, comp, and interp lemmas (Task 4);
    extensional-equality setoid (Task 5); `NatBTMorNQuo`
    quotient with composition well-definedness and the
    three category laws (Task 6); `Category LawvereNatBTCat`
    instance (Task 7); `HasChosenFiniteProducts
    LawvereNatBTCat` with `terminal`, `fst`, `snd`, `pair`,
    universal properties (Task 8); `natBTInterpFunctor :
    LawvereNatBTCat ⥤ Type` with `Faithful` (Task 9); and
    Stage α tests (Task 10).

* **Stage β Task 11 complete** (commit `4f806f6d`):
  `GebLean/LawvereNatBT0.lean` defines `isNatBT0`, the
  `LawvereNatBT0Cat` `FullSubcategory`, the `natBT0Inclusion`
  functor (with full + faithful auto-instances), and
  `HasChosenFiniteProducts LawvereNatBT0Cat` with
  `lawvereNatBT0Terminal` and `lawvereNatBT0Product`.  Module
  registered in `GebLean.lean`.
* **Stage β original Task 12 complete** (commit `29553fd0`):
  `GebLean/Utilities/ERTreeArith.lean` has `ERMor1.natPair`,
  `ERMor1.natUnpairFst`, `ERMor1.natUnpairSnd`, `ERMor1.natSqrt`
  plus helpers `mulN`/`addN`/`signN`/`ltN`/`leN`/`condN`.  Each
  carries `@[simp]`-marked correctness theorems.
* **Stage β original Task 13 Part 1 complete** (commit
  `3eebf595`): `GebLean/Utilities/SzudzikSeq.lean` extended
  with `Nat.foldBTLOnCode` (course-of-values BTL fold on a
  Gödel code), plus parity reduction lemmas and
  `Nat.foldBTLOnCode_encode` correctness linking to `BTL.fold`.
* **Stage β original Task 13 Part 2 obstructed → redesigned**:
  `ERMor1.foldBTLOnCode` requires a primitive-recursion
  combinator in Wikipedia-literal ER, which does not follow
  directly from the 7 ER generators.  Redesigned as the
  "ER-Primrec" mini-phase (Tasks 12a-12f in the spec
  `docs/superpowers/specs/2026-04-17-er-primrec-design.md`
  and the plan
  `docs/superpowers/plans/2026-04-17-er-primrec.md`).
  
  Further refinement within the mini-phase: the originally-
  proposed generic `ERMor1.natRec` combinator cannot exist in
  Wikipedia-literal ER (iterating an arbitrary ER step n
  times escapes E_3, witness tetration per Phase 4f.2).  The
  correct combinator is bounded primitive recursion:
  `ERMor1.boundedRec (base) (step) (bound)` with truncation
  semantics `min (Nat.rec ...) bound.interp`.  This is the
  Meyer-Ritchie-Kleene characterization of E_3.  When the
  client proves the bound dominates, a convenience lemma
  `boundedRec_eq_natRec_of_bounded` gives exact `Nat.rec`
  semantics.

* **ER-Primrec mini-phase progress**:
  * **Task 12a complete** (commit `e068f938`): renamed
    `Utilities/ERTreeArith.lean` → `Utilities/ERArith.lean`,
    updated docstring header, updated `GebLean.lean` import.
  * **Task 12b complete** (commit `bd8fcf63`): ER-derived
    `ERMor1.div` and `ERMor1.mod` with `@[simp]`
    correctness theorems.
  * **Task 12c complete** (commit `7bf90c6b`): `ERMor1.beta`
    as direct arithmetic plus `Nat.beta_exists` wrapping
    mathlib's `Nat.unbeta`.
  * **Task 12d complete** (commit `d2cb3a1a`):
    `ERMor1.boundedSearch` with correctness via
    `natBSum_pos_iff_exists` and `natBSum_firstWitness`.
  * **Task 12e minN helper** (commit `c6223f68`).
  * **Task 12e.1** (commit `9cf56b33`):
    `Nat.bounded_beta_exists` via public
    `Nat.chineseRemainderOfFinset` with bound
    `b = (max N M + 1)!` and `a < (N * b + 1)^N`.
  * **Task 12e.2** (commit `684ceffe`): `ERMor1.factN` via
    `bprod (succ (proj 0))` and `ERMor1.powN` as `expER` with
    swapped arguments.
  * **Task 12e Phase A** (commit `b14a558b`): initial
    `ERMor1.boundedRec` inline definition plus the
    unconditional `interp_boundedRec_le_bound`.
  * **Task 12e Phase B restructure** (commit `e1453b74`):
    refactored into 10 top-level helpers
    (`boundedRecRange`, `betaOnCand`, `baseOnCand`,
    `boundedRecBaseCheck`, `betaOnCandStep`, `stepOnCandStep`,
    `boundedRecStepBody`, `boundedRecStepCheck`,
    `boundedRecPred`, `boundedRec`), each with spec lemmas,
    culminating in `boundedRecPred_eq_one_iff_trace`.
  * **Task 12e Phase B correctness** (commit `05080b47`):
    `interp_boundedRec_of_bounded` conditional correctness via
    the arithmetic envelope `Nat.pair_lt_boundedRecRange`, the
    trace-match induction helper `boundedRecPred_trace_match`,
    and the main induction.  Takes two hypotheses: pointwise
    bound adequacy (`h : ∀ j ≤ n, trace j ≤ bound (cons j
    ctx)`) and counter monotonicity (`h_mono : ∀ j ≤ n, bound
    (cons j ctx) ≤ bound (cons n ctx)`).
  * **Task 12e convenience + tests** (commit `c68f57b7`):
    `boundedRec_eq_natRec_of_bounded` alias plus sanity
    examples exercising both correctness theorems.
  * **Task 12f showcases** (commit `ebcc3cf2`):
    `ERMor1.natAdd`, `ERMor1.natMul`, `ERMor1.factorial` via
    `boundedRec`, each with a `@[simp]`-marked correctness
    theorem proved by `boundedRec_eq_natRec_of_bounded`.
    `natAdd`/`natMul` use polynomial bounds; `factorial` uses
    `factN` itself (the function is its own bound since
    `j! ≤ n!` for `j ≤ n`).  Per-showcase helpers
    (`*_step_eval`, `*_bound_eval`, `*_trace_direct`) perform
    the `Nat.rec` iota reduction through `rw [Nat.succ_mul,
    ← ih] ; exact step_eval _ _ _` since `change`/`show`
    cannot unify through match-embedded step terms.  Six
    numerical example tests exercise each showcase at both
    non-zero and zero inputs.
  * **Task 13 Phase 1** (commit `b309fbe2`): creates
    `GebLean/Utilities/ERTreeArith.lean` with `ERMor1.twoN`,
    `ERMor1.btlEncodeLeaf`, `ERMor1.btlEncodeNode`.
  * **Task 13 Phase 2** (commit `ad1c0cf2`):
    `ERMor1.foldBTLOnCode` with the same conditional
    correctness pattern as `boundedRec` — a user-supplied
    `bound` parameter plus pointwise-adequacy and counter-
    monotonicity hypotheses.  Construction: single
    `boundedSearch` over Szudzik-paired `(a, b)` candidates
    for a Gödel β-witness satisfying the course-of-values
    recurrence (leaf case at even `j`, node case at odd `j`),
    then β-extraction at `code`.  Support helpers mirror the
    `boundedRec` structure: `foldBTLBody`,
    `foldBTLPred_eq_one_iff_trace`,
    `foldBTLPred_trace_match`.

**Design revision during Phase B** (recorded in
`docs/superpowers/specs/2026-04-17-er-primrec-design.md`
D5/D6): the originally-proposed strict `min (Nat.rec ...)
(bound ...)` correctness statement is not provable with the
β-witness-search construction — counterexamples exist when an
intermediate trace value exceeds the bound.  The spec was
revised to a two-part conditional form:
`interp_boundedRec_le_bound` (unconditional) and
`interp_boundedRec_of_bounded` (under pointwise bound
adequacy plus counter monotonicity).

**Task 14 split into 14a (fold-free fragment, DONE) and 14b
(fold handling, deferred until after Task 14.5 research).**

* **Task 14a complete** (commit `8a469dd0`):
  `GebLean/LawvereNatBTBackTrans.lean` defines
  `NatBTMor1.isFoldFree` (structural Prop predicate ruling out
  `foldBTNat`/`foldBTBT` and requiring `nm'.2 = 0` at
  composition sites), `NatBTSort.encodeValue` (identity on
  `.nat`, `BTL.encode` on `.bt`), and the sort-uniform
  `NatBTMor1.toERUniform` with per-sort wrappers `toER` /
  `toER_bt`.  Correctness via the uniform
  `toERUniform_interp_aux` theorem under `isFoldFree + nm.2 = 0`
  hypotheses, with per-sort corollaries and the `NatBTMorN`
  tuple lift.  Sort-uniform recursion chosen because Lean's
  mutual structural recursion rejects specialized mutual `def`s
  when the sort index is pinned rather than a recursion
  variable.  Fold cases and off-invariant composition sites
  receive placeholder `ERMor1.zeroN` values (never reached
  under the invariants).  Tests:
  `GebLeanTests/LawvereNatBTBackTrans.lean` with `#guard`s on
  zero/succ/natProj/sub/leafBT/nodeBT/encodeBT.

**First design pivot (2026-04-18)**: during Task 14.5 research, a
strength-mismatch obstruction was identified — the current
`foldBTNat`/`foldBTBT` (non-ramified state-threaded recursion
over ER step functions) computes tower-of-variable-height values,
provably escaping E_3.  The proposed `LawvereERCat ≃ LawvereNatBT`
equivalence therefore cannot hold for the theory as currently
defined.

The first design pivot proposed a two-stage chain
`LawvereERCat ≃ LawvereNatBT_bounded ≃ LawvereNatBT_ramified`
with a bounded intermediate exposing user-supplied bound
parameters at constructor sites.  Five Stage β.a tasks were
implemented (commits `a6fb05c7`..`7893c3bb`) before further
analysis surfaced an irreducible impedance mismatch.

**Second design pivot (2026-04-18, evening)**: closer reading of
`ERMor1.boundedSearch`'s off-conditions behavior revealed that
ER's `foldBTLOnCode` returns
`min(β-of-(boundedRecRange + 1), bound)` (a witness-search
fallback value) when the user-supplied bound is not pointwise
adequate or not counter-monotonic.  No clean choice for the
bounded theory's interp at the same off-conditions matches
that semantics on the nose:

* Truncation (`min(trace, bound)`) gives a meaningful value but
  differs from ER's garbage.
* Adequate-or-zero gives 0 but differs from ER (which gives
  garbage, not 0).
* Direct port of ER's witness search would require duplicating
  the construction at the Nat level.

The five Stage β.a commits were reverted.  The cleaner factoring
removes the bounded intermediate entirely and inserts a Nat-only
ramified intermediate instead:

```text
LawvereERCat ≃ LawvereNatRamified ≃ LawvereNatBTRamified
```

Stage A's first three commits (Tier + inductive, natMatch arity
fix, interp, tuples-with-mayRec-fallback) were implemented before
analysis surfaced a foundational obstruction (see third pivot).

**Third design pivot (2026-04-18, late evening)**: while
implementing Stage A's tuple-level composition, the Σ-erased-
inner-family approach hit Lean's nested-Σ kernel restriction
and was worked around with a `.mayRec` over-approximation.  This
prompted re-examination of the ramified design's expressive
class.  Re-reading earlier research (recorded above): first-
order ramified recurrence over free algebras is polynomial-time
or PR-strength (depending on what's allowed in the step), not
E_3.  Operation-level tier discipline isn't strong enough to
land at exactly E_3 — the only mechanisms that do are (a) ER's
specific generators (`bsum`/`bprod`), (b) bounded recursion
with explicit user-supplied bounds (Meyer-Ritchie limited
primitive recursion), or (c) the ER witness-search construction
itself.

Stage A's four commits (`5ac6e47e`..`f2d087d7`) were reverted.
The new design (Option E) uses bounded recursion at the
constructor level, with the off-conditions match-with-ER issue
resolved by porting ER's witness-search semantics to Nat-level
helpers:

```text
LawvereERCat ≃ LawvereNatBTBounded   (single equivalence)
                ↑
                Layer 1 combinators (foldBTNatAuto, primRecAuto)
                ↑
                Layer 0 raw constructors (foldBTNat, foldBTBT,
                                         boundedNatRec)
                ↑
                Nat.foldBTLOnCodeERStyle, Nat.boundedRecERStyle
                (mirror ER's witness-search at Nat level)
```

The bounded NatBT theory has user-supplied `bound` parameters
on the three recursive constructors.  Interp delegates to the
Nat-level helpers, which mirror ER's witness-search semantics
on the nose.  A soundness theorem connects each Nat helper to
the corresponding ER combinator.  The categorical equivalence
`LawvereERCat ≃ LawvereNatBTBounded` is on-the-nose at the
raw constructor level.

Layer 1 provides programmer-friendly auto-bound combinators
(`foldBTNatAuto`, `primRecAuto`, `foldBTBTAuto`) that derive
adequate-monotonic bounds from `step.towerHeight` automatically.
`@[simp]` correctness lemmas reduce these to the structural
`BTL.fold` / `Nat.rec` semantics (no min, no fallback).
Programmers writing `foldBTNatAuto base step tree` see no
witness-search machinery.

Existing `LawvereNatBT*` files (the unbounded "non-ramified"
two-sort theory) are kept under their current names as a
parallel development.  The new bounded theory uses
`LawvereNatBTBounded*` filenames.

Design spec:
`docs/superpowers/specs/2026-04-18-option-e-bounded-natbt-design.md`
(local, gitignored).

Implementation plan:
`docs/superpowers/plans/2026-04-18-option-e-bounded-natbt.md`
(local, gitignored).  ~17 tasks across six stages:

* **Stage 1** (Tasks 1.1-1.2): Layer 0 — Nat-level
  ER-style helpers + soundness theorems.
* **Stage 2** (Tasks 2.1-2.3): bounded NatBT inductive + interp.
* **Stage 3** (Tasks 3.1-3.3): quotient + Category +
  products + interp functor + `m = 0` subcategory.
* **Stage 4** (Tasks 4.1-4.3): Layer 1 auto-bound combinators
  + `@[simp]` correctness lemmas.
* **Stage 5** (Tasks 5.1-5.3): `LawvereERCat ≃
  LawvereNatBTBounded0` equivalence.
* **Stage 6** (Tasks 6.1-6.3): Phase 4f transport + tests +
  tracker.

**Fourth design pivot (2026-04-19, morning)**: Option E was
implemented through Stage 5.2.  The equivalence assembly
required either restricting to a well-formed subcategory or
extending the back-translation to handle `foldBTBT` and BT
contexts.  Re-examination surfaced a more disciplined
architecture: instead of designing the NatBT inductive
top-down and trying to back-translate, build each NatBT
constructor as a *named ER implementation* — implement first,
expose afterwards.  Under this discipline:

* The categorical equivalence with `LawvereERCat` is preserved
  by construction: every NatBT constructor IS a named ER
  expression.
* `interp` is derived from `toER` (`(t.toER).interp combinedCtx`
  with sort-aware decoding), eliminating the Layer 0 Nat-level
  helpers and their soundness theorems.
* The `LawvereERWrap` workaround disappears once the
  `@[reducible]` aliases (`LawvereERCat`, `LawvereBTQuotCat`,
  `LawvereBTCat`, `LawvereTreeERCat`) are made non-reducible,
  eliminating the typeclass conflict.
* `foldBTBT` becomes implementable in the back-translation
  because BT context slots are encoded as ℕ slots in a
  wider-arity ER term.
* No more "settling" or "well-formed subcategory" gymnastics —
  if a constructor isn't ER-implementable, we don't add it.
* The API grows incrementally: each new constructor is added
  only after its ER implementation is in hand.

The eight Option E commits (`bf33e2d0`..`b5f8f7c9`) were
reverted.  Implementation infrastructure built earlier in this
workstream — particularly the `Utilities/ERArith.lean`,
`Utilities/ERTreeArith.lean`, and `LawvereERBoundComputable.lean`
files containing `boundedRec`, `foldBTLOnCode`, `towerHeight`,
`towerER`, `towerBound`, `btlEncodeLeaf`, `btlEncodeNode`, and
many other ER-derived primitives — is exactly what the new
bottom-up design uses as its named-ER-implementation library.

Design spec:
`docs/superpowers/specs/2026-04-19-bottom-up-natbt-design.md`
(local, gitignored).

Implementation plan:
`docs/superpowers/plans/2026-04-19-bottom-up-natbt.md` (local,
gitignored).  ~17 tasks across five phases:

* **Phase A** (3 tasks): drop `@[reducible]` from the four
  ℕ-aliased Lawvere categories; fix breakage.
* **Phase C** (7 tasks): build `LawvereNatBTV2.lean` —
  inductive (foundational + BT structural + bounded recursive
  constructors), `toER` structural translation, derived
  `interp`, per-constructor `@[simp]` lemmas.
* **Phase D** (3 tasks): quotient + category + products +
  faithful interp functor.
* **Phase E** (3 tasks): forward functor (lift of ER
  constructors), back functor (case-split lookup of `toER`),
  equivalence assembly (trivial by construction).
* **Phase F** (3 tasks): Layer 1 auto-bound combinators +
  tests + tracker update.

**Current resume point**: execute the plan via
`superpowers:subagent-driven-development`.  Starts at Phase A
Task A.1 (drop `@[reducible]` from the four aliases).  Proceed
directly on branch `terence/syntax`.

**Bottom-up NatBT chain complete (2026-04-19)**: all five phases
landed.  Commits:

* Phase A (`3c2ecc50`): drop @[reducible] from four ℕ-aliased
  Lawvere category defs (16 fix sites across LawvereERInterp,
  LawvereERDelta, LawvereERTetration, LawvereBTPrimrec,
  LawvereBTInterp, TreePERLawvereBT).
* Phase C wave 1 (`931c0567`): NatBTMor1V2 inductive
  (foundational ER-direct constructors), structural toER,
  derived interp, per-constructor simp lemmas.
* Phase C wave 2 (`1d8336ce`): BT structural and bounded
  recursive constructors added; foldBTBT slot permutation
  handled.
* Phase D Task D.1 (`685047ca`): NatBTMorNV2 + quotient +
  Category + HasChosenFiniteProducts.
* Phase D Task D.2 (`f6a23508`): faithful interp functor
  natBTV2InterpFunctor.
* Phase D Task D.3 (`b3a3084b`): LawvereNatBTV20Cat full
  subcategory (m = 0).
* Phase E Task E.1 (`71bef50f`): erToNatBTV2Functor.
* Phase E Task E.2 (`38134a6e`): natBTV20ToERFunctor via toER.
* Phase E Task E.3 (`3679df57`): lawvereERNatBTV20Equivalence
  assembled.

Layer 1 auto-bound combinators (foldBTNatAuto, primRecAuto,
foldBTBTAuto with auto-derived bounds via NatBT-level tower
infrastructure) are deferred to a follow-up workstream.  The
basic equivalence chain ships without them; programmers who
want to use the bounded recursive constructors must currently
supply explicit `bound` parameters.

Phase 4f non-fullness transport (Ackermann/tetration not
definable in NatBTV2) is also deferred — the equivalence is in
place, so the transport is a 1-2 task follow-up.

**Task 14.5-extended (deferred)**: BT-only adequacy research
— proving that the unlabeled-BT + 0-way-ℕ-product subfragment
of `LawvereNatBTBounded` is already equivalent to
`LawvereERCat`.  Remains deferred until after the full
equivalence chain ships.

Natural checkpoints: end of Stage 1 (Layer 0 ready), end of
Stage 4 (programmer-friendly API in place), end of Stage 5
(equivalence proved), end of Stage 6 (full chain shipped).

The Option E architecture's distinguishing property: a single
on-the-nose categorical equivalence with `LawvereERCat`,
with Layer 1 combinators providing native fold ergonomics
without exposing witness-search machinery to programmers.
The bounded constructors form a stable raw interface; Layer 1
is built on top by pure `def`s with no proof content; the
equivalence is proven once at the raw level.

## Phase 4g: Tree-Native ER Parallel Development (planned)

Before proceeding to Phase 5, build a tree-native presentation of
elementary recursive functions (`LawvereTreeERCat` and
`LawvereTreeERLexCat`), categorically isomorphic to `LawvereERCat`
and `LawvereERLexCat` respectively.  Tree-ER expresses ER-level
computations over binary trees natively (via `leaf`, `branch`,
`proj`, `fold`, `comp`), without arithmetic primitives — arithmetic
is derived once and reused.  Both presentations remain first-class
citizens in the project; the isomorphism provides free transport of
proofs between them.  Phase 5's internal categorical development
then has a choice of target; current expectation is that it is more
natural in `LawvereTreeERLexCat`.

### Motivation

* Programmer ergonomics: data-structure-style algorithms (tree
  calculus, fold/catamorphism, internal term types) read naturally
  on trees, awkwardly through Gödel encoding.
* Mathematical validation: the existing literature on elementary
  recursive functions is almost entirely in `ℕ`-based form.  Proving
  categorical isomorphism between a tree form and the established
  `LawvereERCat` gives high confidence that the tree form captures
  exactly ER — neither strengthened nor weakened by accident.
* Dual-side reasoning: "applications are usually most convenient in
  trees; proofs are usually most convenient in natural numbers".
  The isomorphism transports results across whichever side is
  easier for each step.

### Design decisions

1. **Primary representations: both.**  `LawvereERCat` (existing,
   ℕ-based, literature-matched) and `LawvereTreeERCat` (new,
   tree-native) both receive full Lawvere-theory development
   including finite-limit completion.  The isomorphism is proved
   once and used as transport in both directions.

2. **Tree-ER syntax: depth-2 stratified `BTMor1`.**  The term type
   `TreeERMor1 n` is the fold-nesting-depth-≤-2 fragment of
   `BTMor1 n`.  This matches the Leivant 1999 / Beckmann-Weiermann
   2000 characterization of E_3 as the two-tier ramified recursion
   over free algebras.  Equivalently (our Phase 4f.2 result), it is
   the tower-bounded fragment of `BTMor1`.

3. **Minimal-core generators.**  Tree-ER's generators are exactly
   `BTMor1`'s: `leaf`, `branch`, `proj`, `fold`, `comp`.  No
   arithmetic primitives.  Arithmetic is built as derived
   definitions (`succ`, `sub`, `bsum`, `bprod`) each as a specific
   depth-≤-2 tree-ER term.

4. **Gödel encoding: Szudzik's elegant pairing, as written.**  The
   arithmetic of `encodeBT`/`decodeBT` follows Szudzik's paper
   (`.claude/docs/ElegantPairing.pdf`) verbatim.  Szudzik's cleaner
   max-shell property (`max(x, y) = isqrt(pair(x, y))`) makes
   reduction rules easier to state; the project already has
   `GebLean/NatElegantPair.lean` infrastructure.  Cantor pairing
   would be categorically equivalent but less ergonomic.

5. **Categorical isomorphism, not just equivalence.**  Construct
   functors `J : LawvereERCat → LawvereTreeERCat` and
   `K : LawvereTreeERCat → LawvereERCat` such that `KJ = 1` and
   `JK = 1` hold on the nose.  Falling back to equivalence is
   acceptable only if isomorphism turns out to be provably
   impossible.

6. **Transport via faithful-inclusion.**  `LawvereTreeERCat` embeds
   as a sub-Lawvere-theory of `LawvereBTQuotCat` via a faithful
   inclusion functor.  Prove equations in `LawvereBTQuotCat` (where
   all BT machinery is available) and lift them to
   `LawvereTreeERCat` via faithfulness.  Similarly for native-Lean
   equations: prove in `Lean` on BT directly and lift.

7. **Small arithmetic functions with proven reduction rules.**
   Every derived arithmetic primitive (`pair`, `unpair`, `succ`,
   `sub`, `isqrt`, etc.) gets `@[simp]`-marked computation
   theorems.  Clients should not need to unfold multiple levels to
   establish their own reduction rules.

### Sub-project structure

* **4g.1 — Tree-ER core Lawvere theory** (new modules
  `GebLean/LawvereTreeER.lean`, `GebLean/LawvereTreeERQuot.lean`,
  `GebLean/LawvereTreeERInterp.lean`): term type, quotient,
  category instance, `HasChosenFiniteProducts`, faithful interp
  functor to `Type`.
* **4g.2 — Tree-ER ↔ LawvereER base-level isomorphism** (new
  modules `GebLean/LawvereTreeERArith.lean` for derived
  arithmetic, `GebLean/LawvereTreeERLawvereEquiv.lean` for the
  isomorphism): bidirectional translation, mutual-inverse
  functoriality, Gödel arithmetic on trees.
* **4g.3 — Transport of Phase 4f results to Tree-ER** (new
  modules `GebLean/LawvereTreeERBound.lean`,
  `GebLean/LawvereTreeERPrimrec.lean`,
  `GebLean/LawvereTreeERTetration.lean`): tower bound, Primrec'
  translation, non-fullness via Ackermann, non-elementarity via
  tetration — mostly corollaries of the iso + existing
  LawvereER results.
* **4g.4 — Tree-ERLexCat + Lex-level isomorphism parity** (new
  modules `GebLean/LawvereTreeERLex.lean`,
  `GebLean/LawvereTreeERDelta.lean`): decidable-subobject
  finite-limit closure + Δ embedding, mirroring Phase 4a–4e.
  Extend the iso to `LawvereTreeERLexCat ≅ LawvereERLexCat`.
* **4g.5 — Documentation** (`docs/tree-er-correspondence.md`):
  central reference with full Axt / Grzegorczyk / Meyer-Ritchie /
  Leivant / Beckmann-Weiermann correspondence map, citations, and
  links to key theorems.

### Literature references

* Leivant, D. "Ramified recurrence and computational complexity
  III: Higher-type recurrence and elementary complexity." *Annals
  of Pure and Applied Logic* 96 (1999), 209–229.  Tree-native
  characterization of E_n over free algebras via ramified
  recurrence at depth n−1.
* Beckmann, A. & Weiermann, A. "Characterizing the elementary
  recursive functions by a fragment of Gödel's T."  *Archive for
  Mathematical Logic* 39 (2000), 475–491.  Depth-2 fold over type-0
  iterators gives exactly E_3.
* Meyer, A. & Ritchie, D. "The complexity of loop programs."
  *Proc. ACM 22nd National Conference* (1967).  LOOP program depth
  stratification.
* Fachini, E. & Maggiolo-Schettini, A. "A hierarchy of primitive
  recursive sequence functions."  *ITA* 13 (1979).  Establishes
  `L_i = E_{i+1}` for `i > 1`.
* Szudzik, M. "An elegant pairing function."  `.claude/docs/ElegantPairing.pdf`.
* Péter, R.  *Recursive Functions.*  Academic Press, 1967.
  Standard reference for reducibility of mutual primitive recursion
  to non-mutual.

### Phase 5 impact

Phase 5 (internal categorical development) originally targeted
`LawvereERLexCat`.  With Phase 4g in place, the internal
`BTMor1`-analogue, arity object, source/target/identity/composition
morphisms can be defined inside `LawvereTreeERLexCat` instead, where
the tree structure is native rather than encoded.  The isomorphism
transports the resulting internal category to
`LawvereERLexCat` for free, so downstream lex functors out of either
preserve the internal structure.  The Phase 5 re-plan will occur
after Phase 4g.1 so the target is nailed down.

## Goal

Produce a category analogous to `LawvereBTQuotCat` /
`LawvereBTLexCat` whose morphisms are elementary recursive
functions (rather than primitive-recursive functions) modulo
extensional equality, and whose finite-limit closure is
intended to serve as the ambient syntax category for further
categorical development in the project.

Design documentation: `docs/lawvere-elementary-recursive.md`.

## Context

The `LawvereBT*` family of modules already presents the free
Lawvere theory of parameterized binary tree objects,
interprets it in `Type u`, proves faithfulness and a
primitive-recursive correspondence, and closes it under finite
limits via the free equalizer completion.

The present workstream mirrors that stratification but narrows
the computational strength from primitive recursion to
elementary recursion, on the grounds that elementary recursion
is sufficient for typechecking (and, at the Grzegorczyk-E^3 /
Axt level, expected to be necessary for iterating over paired
natural numbers and hence trees).

## Reference Modules

Existing modules whose pattern is being mirrored:

* `GebLean/LawvereBT.lean`
* `GebLean/LawvereBTInterp.lean`
* `GebLean/LawvereBTEq.lean`
* `GebLean/LawvereBTQuot.lean`
* `GebLean/LawvereBTPrimrec.lean`
* `GebLean/LawvereBTEqCompletion.lean`
* `GebLean/EqualizerCompletion.lean`
* `GebLean/NatArith.lean`, `GebLean/NatElegantPair.lean`,
  `GebLean/NatNNO.lean` (primitive-recursive pairing and
  Goedel-encoding infrastructure that will be reused or
  adapted)

## Phases

### Phase 1 -- Inductive term for ER functions

* Pick a presentation (see open questions below).
* Define the term type, the arity-indexed tuple type, and
  substitution / composition operations.

### Phase 2 -- Extensional-equality quotient

* Define the setoid (or equational theory) under extensional
  equality.
* Prove substitution and composition are congruences.

### Phase 3 -- Lawvere theory and interpretation functor

* Assemble the Lawvere theory with chosen finite products.
* Define the interpretation functor into `Type u`.
* Prove faithfulness.

### Phase 4 -- Finite-limit structure as definable subobjects

* Build the category `LawvereERLexCat` directly as the
  category of decidable ER-subobjects, with finite products
  from conjunction of predicates and equalizers from the
  ER-definable `Nat` equality.
* Establish the full and faithful finite-product-preserving
  embedding `LawvereERCat -> LawvereERLexCat` sending `n`
  to `(n, 1)`.
* No free-equalizer-completion route is developed.

### Phase 5 -- Internalization (Stages 1 and 2)

Phase 5 is developed primarily inside `LawvereTreeERLexCat`, where
the internal `BTMor1`-analogue sits as a decidable subobject of `BT`
itself and constructors/destructors are tree-native.  By the Phase
4g Lex-level isomorphism `LawvereTreeERLexCat ≅ LawvereERLexCat`,
the resulting internal-category construction also presents as an
internal category in `LawvereERLexCat`; no separate development is
required on the `ℕ`-encoded side.

Stage 1 (internal `BTMor1`-analogue as a decidable subobject):

* Define an internal `BTMor1`-analogue `X` as a decidable
  subobject of some `(BT, p)` in `LawvereTreeERLexCat`.
* Define tree-ER morphisms for `proj`, `leaf`, `branch`, `fold`
  landing in or out of `X`.
* Define an internal typechecker `X -> (ℕ, 1)` (or equivalently
  to `(BT, 1)`).

Stage 2 (internal-category structure on the subobject):

* Reuse `X` verbatim as the `C₁` of an internal category.
* Define the arity object `C₀`.
* Define `src, tgt : X -> C₀`, `id : C₀ -> X`, and
  `comp : X ×_{C₀} X -> X` as tree-ER morphisms.
* Check the unit and associativity laws as equations of
  `LawvereTreeERLexCat` morphisms.

Downstream consequence:

* Establish that for every lex functor
  `I : LawvereTreeERLexCat -> D` into a finite-limit category
  `D`, the image of the Stage-2 internal category is an
  internal category in `D`.  (By the Phase 4g isomorphism,
  this is equivalent to stating the same property for
  `I : LawvereERLexCat -> D`; the tree form is more natural
  for the construction itself.)

## Decisions So Far

1. **Presentation of ER functions.**  Literal transcription of
   the Wikipedia definition.  Generators: `0`, `succ`, `proj`,
   `sub`, `comp`, `bsum`, `bprod`.  Rationale: removes any
   doubt about which class of functions is being characterised
   (given that the literature offers inequivalent-looking
   bases), and keeps the operations manifestly polynomial so
   that equivalences with polynomial-functor algebras can be
   expressed smoothly.  Reference:
   <https://en.wikipedia.org/wiki/Elementary_recursive_function#Definition>.

2. **Carrier.**  Standard interpretation `(Fin n -> Nat) ->
   Nat`.  The tree semantics is deferred to a derived
   interpretation obtained by pre- and post-composition with
   the elementary-recursive Goedel encodings from
   `GebLean/LawvereBTPrimrec.lean`.

3. **Quotient presentation.**  Setoid quotient by direct
   extensional equality of the standard interpretation.  No
   Lean-level inductive congruence relation, no Lean-level
   soundness/completeness theorem.  Reflective Lean-level
   reconstructions of the term type (an analogue of
   `BTMor1`) are deliberately not built; instead, the
   `BTMor1` analogue for this development is planned as an
   internal construction of the resulting syntax category,
   with reflective operations on it (typechecking,
   evaluation, normalisation) expressed as morphisms of the
   category rather than as meta-level Lean functions.

4. **Finite-limit structure via definable subobjects.**
   Objects are pairs `(n, p)` with `p : ERMor1 n`
   Boolean-valued; morphisms `(n, p) -> (m, q)` are ER
   tuples respecting membership, quotiented by extensional
   equality *restricted to the source predicate*.  Finite
   products use conjunction of predicates; equalizers use
   the ER-definable Boolean equality on `Nat` conjoined
   with the source predicate.  Predicates use the
   convention "1 = true, 0 = false".  No separate
   equivalence proof between this construction and the
   free equalizer completion is planned.

5. **Phase 5 internalisation: subobject-plus-category in
   two stages, in the tree form.**  With Phase 4g in
   place, Phase 5 is developed inside
   `LawvereTreeERLexCat`, where tree structure is native.
   Stage 1 builds an internal `BTMor1`-analogue as a
   decidable subobject of `(BT, p)` with tree-ER
   constructors, destructors, and typechecker.  Stage 2
   upgrades the same subobject in place into an internal
   category in `LawvereTreeERLexCat` by adding `src`,
   `tgt`, `id`, and `comp` morphisms; the Stage-1
   subobject is reused verbatim as `C₁`.  No construction
   is thrown away between stages.  The Phase 4g
   Lex-level isomorphism carries the resulting internal
   category to `LawvereERLexCat` automatically, so
   downstream lex functors out of either category
   transport the internal-category structure in one
   functor application.

### Derivations verified for the chosen basis

* Multiplication: `bsum(proj_y)(x, y) = x * y`.
* Exponentiation: `bprod(proj_y)(n, y) = y^n`.
* Addition: `bsum(g)(succ(x), y)` where
  `g(i, y) = bprod(proj_y)(sub(succ(zero), i))`.  The
  conditional `if i = 0 then y else 1` uses the indicator
  `sub(succ(zero), i)` together with bounded product.

## Open Questions

All Phase 0 design questions have been resolved.
Implementation is unblocked at Phase 1.

## Naming

Provisional Lean-module prefix and category names are not yet
fixed.  Options under consideration:

* `LawvereER*` (parallel to `LawvereBT*`);
* `LawvereElemRec*`;
* `ElemRec*` without the `Lawvere` prefix.

## Tasks

The task list below is seeded from the phases above.  It is
expanded as each phase becomes ready to implement.

* [x] Resolve open design questions 1-5.
* [x] Decide on module-naming convention (`LawvereER*`).
* [x] Phase 1: inductive term type for ER functions.
* [x] Phase 2: extensional-equality quotient.
* [x] Phase 3: Lawvere theory and interpretation functor.
* [x] Phase 4: definable-subobject finite-limit category.
  * [x] 4a: Objects, morphisms, category structure.
  * [x] 4b: Boolean operations on ER terms.
  * [x] 4c: Finite products.
  * [x] 4d: Equalizers (raw construction and
    universal property).
  * [x] 4d.2: ERBoolPredE quotient + chosen
    equalizers + HasChosenFiniteLimits.
  * [x] 4d.3: Mathlib HasEqualizers and
    HasFiniteLimits derivations.
  * [x] 4e: Full-and-faithful embedding Δ
    (with PreservesFiniteProducts).
* [ ] Phase 4g: Tree-Native ER parallel development.
  * [x] 4g.1: Tree-ER core Lawvere theory.
  * [ ] 4g.2: Tree-ER ↔ LawvereER base-level isomorphism
    (+ Gödel arithmetic on trees).
  * [ ] 4g.3: Transport of Phase 4f results to Tree-ER.
  * [ ] 4g.4: Tree-ERLexCat + Lex-level isomorphism parity.
  * [ ] 4g.5: `docs/tree-er-correspondence.md`.
* [ ] Phase 5: Stage 1 internal term type, then Stage 2
  internal-category structure.  Target category to be
  decided after Phase 4g.1.
* Non-fullness of `erInterpFunctor`:
  * [x] 4f.1: Ackermann non-fullness via Primrec' translation.
  * [x] 4f.2: Tetration non-elementary via tower-bounding argument.
* [ ] Factorisation through `LawvereBTQuotCat`: construct
  a functor `LawvereERCat -> LawvereBTQuotCat` (via the
  Goedel encodings `encodeBT`/`decodeBT` from
  `LawvereBTPrimrec.lean`, both of which are elementary
  recursive) and show that it is faithful but not full,
  with its image strictly contained in the primitive
  recursive subtheory.  Prove that composition with the
  `Type`-valued interpretation of `LawvereBTQuotCat`
  recovers `erInterpFunctor`.  Tetration is primitive
  recursive but not elementary recursive, so it
  witnesses the non-fullness of this functor and hence
  precisely locates `LawvereERCat` within the Grzegorczyk
  and Axt hierarchies as genuinely elementary.

## Notes

The `NatArith`, `NatElegantPair`, and `NatNNO` modules already
contain primitive-recursive pairing, iterated subtraction,
integer square root, and related infrastructure that is
expected to be reusable for an elementary-recursive term
semantics, either directly or as a template for an ER-level
reimplementation.
