# Adversarial review 4 — ramified-recurrence approaches survey (revision 2)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary verdict](#summary-verdict)
- [Verification status](#verification-status)
- [Major](#major)
  - [R4-M1 — Proposition 7 has no direct (2)-implies-(4)](#r4-m1--proposition-7-has-no-direct-2-implies-4)
  - [R4-M2 — "Command-for-command" URM correspondence overclaims the source](#r4-m2--command-for-command-urm-correspondence-overclaims-the-source)
- [Minor](#minor)
  - [R4-m1 — Soundness route map omits ingredients the paper's proof uses](#r4-m1--soundness-route-map-omits-ingredients-the-papers-proof-uses)
  - [R4-m2 — The 2012 paper's base system is `S-minus`, and it is not two-sorted](#r4-m2--the-2012-papers-base-system-is-s-minus-and-it-is-not-two-sorted)
  - [R4-m3 — Quoted linear-space sentence elides a type qualifier](#r4-m3--quoted-linear-space-sentence-elides-a-type-qualifier)
  - [R4-m4 — Dangling cross-reference to revision 1's syntax survey](#r4-m4--dangling-cross-reference-to-revision-1s-syntax-survey)
  - [R4-m5 — Phase list violates its own dependency order](#r4-m5--phase-list-violates-its-own-dependency-order)
- [Nit](#nit)
  - [R4-n1 — "Propositions 11"](#r4-n1--propositions-11)
  - [R4-n2 — Section 2.3 glosses read as source content](#r4-n2--section-23-glosses-read-as-source-content)
  - [R4-n3 — Style-rule words](#r4-n3--style-rule-words)
  - [R4-n4 — Bare "section 2.4" citations ambiguous between paper and document](#r4-n4--bare-section-24-citations-ambiguous-between-paper-and-document)
  - [R4-n5 — `algCoprodDesc` file attribution](#r4-n5--algcoproddesc-file-attribution)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`,
revision 2. Rounds 1-3 (`review-1` through `review-3`) applied to
revision 1; this is a fresh full cycle over revision 2. Content
carried over unchanged from revision 1 and verified in round 1 was
not re-verified (see Verification status); revision 2's new
content — the transcription-only policy, the single-system scoping,
the polynomial-signature-functor algebra axis, the reference-target
and algebra-choice analyses, the proof-route map, and the three
2026-07-02 paper summaries — was verified against the primary PDFs
and the repository from scratch.

## Summary verdict

Revision 2 is accurate in the large and materially more careful
than revision 1 in exactly the places the user review demanded: the
withdrawn machine-free routes are cleanly excised, the fullness
route matches Leivant III's Lemma 6 (statement, `stt`/`[phi]`
simultaneous-recurrence proof, `c * 2_q(sz(a))` clock, and
ingredient list all check against pp. 220-221), the Lemma 12 bound
`O((2_{q+1}(h))^2)` is exact, Theorem 14's five items and its proof
chain are quoted correctly, the three new-paper summaries are
faithful on every theorem-level claim checked, the attribution
correction for arXiv `1201.4567` is right, and every named
repository declaration exists with the claimed content (including
`compileER` at `Compiler.lean:1590`, the tower-bound lemmas, the
K^sim simulator, and the Beckmann-Weiermann `T*` docstrings).

Two major findings. First, the paper proves no direct (2) implies
(4) for Proposition 7: the arrow the soundness route needs is
realized as the composite (2) to (1) to (3) to (4), which passes
through the full applicative calculus `RlMR-omega`, contradicting
the document's "only the fragment `RlMR-omega_o`" scoping. Second,
the zero-test URM does not correspond "command-for-command" to
Leivant's register machines over the unary algebra: Leivant's
assignment and destructor commands move values across registers,
which the URM cannot do in one instruction, and the URM's
constant-assignment has no single-command counterpart; the honest
(and still sufficient) statement is a one-directional
constant-overhead embedding. The remaining findings are precision,
cross-reference, and style items.

## Verification status

Verified directly for this review:

- Leivant III PDF, journal pp. 215-229, read as page images with
  the symbol-garbled text layer cross-checked: the section 3.1
  machine model and Lemma 5 (three command kinds, end-state
  convention, the three reducibilities and footnote 8's
  exponential-size tree remark); Lemma 6's statement and full proof
  (pp. 220-221); section 4.1's calculi definitions and
  Proposition 7's statement and proof including eq. (9) (pp.
  222-223); `1l(A)`, the Berarducci-Boehm attribution and
  reference [6], Lemmas 8-10, Proposition 11 (pp. 223-225);
  Lemma 12 (re-rendered at 300 dpi; bound exactly
  `O((2_{q+1}(h))^2)`) and Proposition 13 (p. 226); Theorem 14's
  statement and proof (p. 227); the section 6.2 multi-sorted
  sketch (pp. 227-228); Lemma 1, Lemma 2 with eqs. (6)-(7), and
  sections 2.4(4), 2.4(6) (pp. 216-218).
- Dal Lago-Martini-Zorzi full text: EPTCS 23 pp. 47-62 and DOI in
  the page footer; the tier-vector scheme with `i < j` on the
  recurrence tier; the tier-drop-free conditional; the term-graph
  proof method (Proposition 1's tier-indexed counting); Theorem 1;
  the p. 48 full-binary-tree counterexample with references [7]
  (POPL '93) and [8] (Leivant I); absence of Leivant III from the
  bibliography and of any higher-order or elementary-class content.
- Danner-Royer 2012 full text: title page (authors, "Extended
  Abstract", arXiv `1201.4567v2`); references [17] (WoLLIC 2010,
  LNCS 6188) and [18] (MFPS XXVII, ENTCS 276, 247-261); the data
  system (`data tau = mu t. sigma`, signature functor, `fold`
  typing and initial-algebra equation, Examples 1-2 giving
  `unit + X` and `unit + X x X`); the cons-cell DAG cost model with
  memoized branching folds; `up_tau` and the `lower` rule with the
  Bellantoni-Cook raising attribution; the p. 7 `E^2` sentence and
  its citations (Bellantoni thesis, Leivant I); the stream/logspace
  characterizations; absence of an equational theory.
- Danner-Royer 2022 full text: title and identifier; Theorem 10
  (p. 15), the height-function obstruction and the incompleteness
  conjecture (pp. 4, 15, 28); `cs_delta` with the
  Downey-Sethi-Tarjan reference; Theorems 22, 23, 25 (pp. 27-28);
  the CEK machine (Figures 7, 9) with the step-bounded
  `fold_nat step b_0` iteration; hereditarily sequential
  representation (p. 5, section 6.1); Scholium 32 (p. 32) and
  Scholium 35 (p. 37); bibliography (Leivant I and DLMZ present,
  Leivant III absent).
- Repository declarations, all present with claimed content:
  `compileER` (`GebLean/LawvereERKSim/Compiler.lean:1590`, type
  `ERMor1 a → URMProgram a`); `compileER_pre_stop_correct` and
  `compileER_runFor` (`Top.lean:55`, `:89`);
  `boundExprKParams_dominates` (`RuntimeBound.lean:225`, joint
  runtime/value tower bound of exactly the stated shape),
  `boundExprK_dominates` (`:1745`), `boundExprK_level ≤ 2`
  (`:1702`); `URMInstr` with exactly the five stated constructors
  (`Utilities/ZeroTestURM.lean:89`); `simulate : URMProgram a →
  KMor1 (a+1)` (`Utilities/KSimURMSimulator.lean:544`),
  `simulate_interp` (`:948`), `simulate_level ≤ 2` (`:961`),
  Tourlakis §0.1.0.37 in the module docstring; the four
  `LawvereGodelT*` module docstrings supporting every claim in
  section 3.3's bullet (combinatory `K`/`S_comb` abstraction,
  Definition 4 reduction with `interp_invariance`, Definition 7
  level measure, Lemma 16 "on pp. 480-484", `dominates_app`,
  `majorizes_redIter_zero`/`_succ`, `S = {.nat}` nucleus and
  `{.nat, .tree}` extension); `docs/areas/lawvere-er-ksim.md`
  recording the layer as adjacent with no functor to
  `LawvereERCat`; `erToNatBTV2Functor`
  (`LawvereERNatBTV2Equiv.lean:163`, forward functor of
  `lawvereERNatBTV20Equivalence`); `erKSimEquiv :
  LawvereERCat ≌ LawvereKSimDCat 2`
  (`LawvereERKSim/Equivalence.lean:183`) with `erToKFunctor` and
  `kToERFunctor`; `Era.lean`'s `Tm`/`Eqn`/`Defs`/`Derivable` and
  clone laws; `ERMor1.exists_lt_tower`, `ERMor1.towerBound`;
  the `PolyFix` stack (`PolyFix`, `polyFixAlg_isInitial`,
  `polyFixStr_iso` (Lambek), `polyFixFoldHom_unique`,
  `polyBetweenCoprod`, `polyEndoEquiv`), `PLang/TreeCalcPoly.lean`,
  `PLang/IndexedEAT.lean`; the vendored slice/presheaf functor
  files with no W-type or coproduct content; `SetoidCat.lean` and
  `Utilities/Category.lean`; ER-side Godel-numbering
  (`ERMor1.natPair`/`natUnpair*`) and bounded recursion
  (`ERMor1.boundedRec`) with the `EraComplete` history-code
  precedent.
- Beckmann-Weiermann citation: Springer confirms "Characterizing
  the elementary recursive functions by a fragment of Godel's T",
  Archive for Mathematical Logic 39 (2000) 475-491, DOI
  `10.1007/s001530050160`; consistent with the
  `LawvereGodelTLemma16.lean` docstring's "pp. 480-484".
- Lint gates: `markdownlint-cli2` 0 errors; `doctoc --dryrun
  --update-only` "Everything is OK"; no absolute local paths; no
  emojis; no all-caps non-acronym words.

Standing from review 1 (carried-over content, not re-verified):
the section 2.1 table rows other than those named above (checked
row-by-row in round 1 against the same PDF), the Bellantoni-Cook
content, the Tourlakis quotations behind section 2.4, the
section 3.1 anchor summaries' resolved DOIs, and the mathlib/CSLib
verdicts of section 3.3.

Not independently verified (unchanged status from round 1):
Leivant I full text (the document flags abstract-only
verification); Clote's Definition 3.100, Theorem 3.101, and the
p. 50 tier dictionary; Ritchie's Theorem 5; Handley-Wainer; the
Bellantoni and Nguyen theses and the Handley manuscript; the Otto
thesis; Heraud-Nowak internals; the Kolichala Lean 3 work; the
upstream geb-mathlib W-type development status.

## Major

### R4-M1 — Proposition 7 has no direct (2)-implies-(4)

Location: section 2.1 (the applicative-calculi row's "the fragment
`RlMR-omega_o` and the direction (2) implies (4) of Proposition 7"
and the Proposition 7 row's "only the (2) implies (4) direction is
in scope"); section 1.1 ("parts return as proof apparatus");
section 6.3 step 1; section 8 phase 6.

Defect: the document scopes the soundness apparatus to the fragment
`RlMR-omega_o` plus "the direction (2) implies (4) of
Proposition 7", presenting that direction as a transcribable unit.
The paper's proof of Proposition 7 (p. 223) reads, in full:
"(1) and (2) are equivalent by Lemma 1, and the equivalence of (3)
and (4) is similar. (3) implies (1) trivially. The only observation
of interest is the implication from (1) to (3), because RMRec^omega
allows recurrence with parameters, whereas the operators R^tau used
in RlMR^omega represent closed induction." Equation (9) and the
translation `F ≡ lambda x-bar. R^tau (G_1(x-bar)) ... (G_k(x-bar))`
belong to the (1)-to-(3) leg, which lands in the full calculus
`RlMR-omega` (with the flat-recurrence constants `F^tau`), not in
the fragment. The arrow (2) implies (4) therefore exists in the
paper only as the composite (2) to (1) (Lemma 1) to (3) (eq. (9))
to (4) (the unspelled "similar" flat-to-`dstr`/`case` translation
at the applicative level). Transcribing the literature route as
written requires formalizing `RlMR-omega` as well as
`RlMR-omega_o`; conversely, a direct (2)-to-(4) construction
(eq. (9)'s device applied inside `RMRec-omega_o`/`RlMR-omega_o`,
with `dstr`/`case` in place of flat recurrence) is not in the paper
and would be an adaptation that section 1.2's policy requires
marking and justifying. As written, the scope accounting understates
either the apparatus (a second calculus) or the novelty (an adapted
proof), and the understatement sits in rows whose scope annotations
are binding inputs to the design spec and the Lean docstrings.

Suggested fix: pick one of the two consistent scopings and record
it. (a) Literature-faithful: scope in `RlMR-omega` as soundness
apparatus too, name the composite (2)-(1)-(3)-(4) with its three
legs (Lemma 1; eq. (9); the (3)-to-(4) translation, noting the
paper leaves it at "similar", so its transcription reconstructs an
unwritten argument), and update sections 1.1, 2.1, 6.3, and 8
phase 6 accordingly. (b) Adaptation: keep only `RlMR-omega_o`,
state the direct (2)-to-(4) as eq. (9)'s translation transported to
the `dstr`/`case` fragment, and mark it as a presentation
adaptation under section 1.2 (on the same footing as the URM
adaptation), with the composite route recorded as the literal
literature route.

### R4-M2 — "Command-for-command" URM correspondence overclaims the source

Location: section 1.2 ("corresponds command-for-command to
Leivant III's register machines over the unary algebra");
section 6.2 ("the instruction sets correspond one-for-one over the
unary algebra"); section 5.2 ("Leivant's register machines over the
unary algebra are the zero-test URM already in the repository").

Defect: Leivant's commands (p. 220) are: assignment
"s -> s' | phi_0 := c_i phi_1 ... phi_{r_i}" (store in `phi_0` the
constructor applied to the values of registers `phi_1 ...
phi_{r_i}`), branch "s(phi_0) -> s_1 ... s_k", and destructor
"s -> s' | phi_0 := j(phi_1)". Over the unary algebra, assignment
and destructor move values across registers (`phi_0 := s(phi_1)`,
`phi_0 := dstr(phi_1)` with `phi_0` distinct from `phi_1`); the
zero-test URM's `inc`/`dec` act in place and the instruction set
has no register-to-register move, so those commands have no
single-instruction (nor constant-length) URM counterpart — copying
requires a value-dependent loop. In the other direction,
`assign i c` for `c >= 1` is a block of `c + 1` Leivant commands,
not one; and Leivant's machines have no stop command at all —
halting is the end-state convention ("we stipulate that every
machine allows for an idempotent repetition of the end state",
p. 220). So neither direction is command-for-command, and
section 5.2's identity claim is false as stated. What is true, and
sufficient for the fullness route: every zero-test URM program
translates to a Leivant register machine over the unary algebra
with constant overhead (each instruction becomes a constant block
of commands; PC values become states; `stop` becomes the end
state), and the Lemma 6 transcription needs only this direction —
the simultaneous-recurrence simulation of the URM step relation is
the same argument shape over a machine that is, if anything,
simpler. The document's policy conclusion (presentation adaptation,
not novel route) survives; the stated justification does not, and
"command-for-command" would propagate into binding docstrings.

Suggested fix: replace the correspondence claims in 1.2, 5.2, and
6.2 with the one-directional statement, e.g.: "each zero-test URM
instruction is a single command or a constant-length command block
of Leivant's machine over the unary algebra (`inc`/`dec` are
in-place constructor assignment and destructor; `assign i c` is a
zero assignment followed by `c` increments; `jumpZ` is the two-way
branch; `stop` is the end-state convention; PC values are states),
so URM computations are Leivant-machine computations with constant
time overhead, which is the direction Lemma 6's transcription
uses. Leivant's cross-register assignment and destructor commands
have no single-instruction URM counterpart, but that direction is
not needed."

## Minor

### R4-m1 — Soundness route map omits ingredients the paper's proof uses

Location: section 6.3 steps 2-3; section 8 phase 6.

Defect: the route map lists Proposition 11, Lemma 12, and
Proposition 13, but the paper's soundness leg uses more than these
three. Proposition 11 rests on Lemmas 8-10 (representation under
equality, normal-form uniqueness for closed object-type terms,
lambda-free contexts; p. 224). Proposition 13's proof begins "By
Lemma 4 we may assume that F : Omega tau -> o for some tau, and so
F-bar : A[tau-bar] -> o (as defined in Section 4.2)" — it needs
Lemma 4 (section 2.7 raising/collapse) and the section 4.2
term translation `E` to `E-bar`. All of these fall inside sections
the 2.1 table already scopes (the Lemmas 3-4 row; the "sections
4.2-4.3" row), so nothing is out of scope; but section 6.3 is the
proof-route map the plan phase will cost, and the unlisted pieces
(three lemmas plus a translation on terms with binders) are not
free. Suggested fix: name Lemmas 8-10, Lemma 4, and the `E-bar`
translation in step 2/3 of section 6.3.

### R4-m2 — The 2012 paper's base system is `S-minus`, and it is not two-sorted

Location: section 2.3, Danner-Royer 2012 bullet: "Two-sorted
(normal/safe) lambda calculi `S1-minus`/`RS1-minus`".

Defect: the 2012 paper introduces the base system as `S-minus`
("We first introduce S-, a formalism for computing over inductively
defined data by classical structural (aka primitive) recursion",
p. 1) — unramified and single-sorted; only `RS1-minus` carries the
normal/safe sorts ("we impose a form of Bellantoni and Cook
normal/safe ramification on S-'s structural recursions and obtain
RS1-", p. 2). The name `S1-minus` first appears in the 2022 paper.
The document's clause attributes both the subscript and the
two-sortedness to both systems. Suggested fix: "an unramified base
calculus `S-minus` and its two-sorted (normal/safe) ramification
`RS1-minus`" (optionally noting the 2022 paper renames the base
`S1-minus`).

### R4-m3 — Quoted linear-space sentence elides a type qualifier

Location: section 2.2, monadic cell: the quotation "the
RS1-minus[nat]-computable functions = E^2, the second Grzegorczyk
class (aka, the linear-space computable functions)".

Defect: the sentence on p. 7 of Danner-Royer 2012 reads "the
RS1-[nat]-computable (nat x ... x nat -> nat)-functions = E_2, the
second Grzegorczyk class (aka, the linear-space computable
functions)", with the citation "[2,14]" (Bellantoni's thesis and
Leivant I, as the document says). The document presents the
sentence in quotation marks but drops the
"(nat x ... x nat -> nat)-functions" qualifier without ellipsis.
The qualifier is meaning-bearing (it restricts to type-1 functions
over `nat`). Suggested fix: restore the qualifier or mark the
elision with an ellipsis.

### R4-m4 — Dangling cross-reference to revision 1's syntax survey

Location: section 6.3, closing paragraph of the numbered route:
"the intrinsically-typed de Bruijn templates of section 3.2's
survey are the starting points".

Defect: revision 2's section 3.2 is "Mechanization prior art"
(Heraud-Nowak, the quasi-interpretation line, Kolichala,
Cook-Levin) and contains no de Bruijn material; no section of
revision 2 surveys intrinsically-typed de Bruijn representations.
The reference points at revision 1 content that the rewrite
dropped. Suggested fix: either restore a one-line pointer to the
intended templates (with their sources) somewhere in section 3, or
reword to name the representation choice directly ("intrinsically-
typed de Bruijn terms, to be surveyed in the design spec").

### R4-m5 — Phase list violates its own dependency order

Location: section 8, phases 5-7 ("In dependency order").

Defect: phase 5 delivers `collapseFunctor_full`, a statement about
the functor `collapseFunctor` that phase 6 delivers; a theorem
cannot precede the declaration it quantifies over. The mathematics
does not force this order — the fullness content (every ER morphism
is definable with the stated interpretation) is stateable before
the functor is assembled — but then phase 5's deliverable is not
`collapseFunctor_full` as named in section 6.1. Suggested fix:
either rename phase 5's deliverable to the pre-functor surjectivity
statement and let phase 7's assembly derive `collapseFunctor_full`,
or move the functor definition (well-definedness) ahead of the
fullness phase.

## Nit

### R4-n1 — "Propositions 11"

Section 2.1's representation row reads "Lambda-representation in
`1l(A)`; Propositions 11". The paper has exactly one Proposition 11
there; its support is Lemmas 8-10 (see R4-m1). Suggested fix:
"Lemmas 8-10 and Proposition 11".

### R4-n2 — Section 2.3 glosses read as source content

Four phrases in the paper summaries are the document's own
characterizations, adjacent to page-cited claims and not marked as
glosses: "the analogue of Leivant's `kappa-hat`" (the 2012 paper
never mentions `kappa-hat`); "clocked CEK-machine self-interpreter
(... Jones self-interpreter tradition)" (the 2022 paper's machine
interprets `S1-minus` programs inside `RS1.1-minus`, and the paper
uses neither "clocked" nor "self-interpreter"; it credits Jones's
influence generally, p. 4); the "poly-heap" label attached to
Scholium 32 (the term is from the 2012 paper; Scholium 32 says
"poly-max" versus additive bounds); and "conjectured
incompleteness, p. 4" (p. 4's conjecture concerns the
DLMZ/Avanzini-Dal Lago formalisms; the `RS1-minus` form is on
pp. 15 and 28). Each gloss is substantively defensible; marking
them (e.g. "in our terms") keeps the summaries quotable.

### R4-n3 — Style-rule words

"the cleanest first-order formulation found" (section 2.3);
"massaged into" (section 6.2); "where the issue does not arise"
(section 2.2; "issue" is a state-judgment word); "the heaviest
single deliverable" (section 6.4). Comparatives inside the
section 7 trade-off table continue to read as acceptable, as in
round 1.

### R4-n4 — Bare "section 2.4" citations ambiguous between paper and document

Section 8 phase 4 says "the section 2.4 example ladder"; the
document's own section 2.4 is the K^sim caution, while the intended
referent is the paper's section 2.4. Section 6.2's "(2.4(1))" etc.
are disambiguated by the surrounding "Leivant III Lemma 6"
context; phase 4 is not. Suggested fix: "the paper's section 2.4
example ladder".

### R4-n5 — `algCoprodDesc` file attribution

Section 3.3 places `algCoprodDesc` under
"`GebLean/Polynomial.lean`/`PolyAlg.lean`/`PolyUMorph.lean`"; it is
declared in `GebLean/PolyAlgUMorph.lean:418` (`polyBetweenCoprod`
is in `PolyUMorph.lean` as implied). Add the fourth file or drop
the declaration-to-file pairing.

## Convergence verdict

Not converged. Revision 2's structural direction is sound and its
sourcing is verified at every theorem-level claim, but the two
major findings both sit in the transcription-scope accounting that
the design spec and Lean docstrings will inherit: R4-M1 requires a
decision (scope in `RlMR-omega`, or mark a direct (2)-to-(4)
adaptation) with edits across sections 1.1, 2.1, 6.3, and 8; R4-M2
requires rewording the machine-correspondence claims in sections
1.2, 5.2, and 6.2 to the one-directional form. Both fixes are
bounded and route-preserving — no proof route changes. The five
minor findings are localized edits. One focused follow-up round to
verify the R4-M1 scoping decision and the reworded correspondence
should suffice.

Finding counts: 0 blocker, 2 major (R4-M1, R4-M2), 5 minor
(R4-m1 through R4-m5), 5 nit (R4-n1 through R4-n5).
