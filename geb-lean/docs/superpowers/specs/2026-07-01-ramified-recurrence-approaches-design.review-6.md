# Adversarial review 6 — ramified-recurrence approaches survey (revision 3)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary verdict](#summary-verdict)
- [Verification status](#verification-status)
- [Blocker](#blocker)
  - [R6-B1 — `ramified_definability` restricts the existential to tower sorts](#r6-b1--ramified_definability-restricts-the-existential-to-tower-sorts)
- [Major](#major)
  - [R6-M1 — The collapse-category packaging overclaims and leaves obligations unnamed](#r6-m1--the-collapse-category-packaging-overclaims-and-leaves-obligations-unnamed)
- [Minor](#minor)
  - [R6-m1 — The no-recursion parenthetical overlooks flat recurrence](#r6-m1--the-no-recursion-parenthetical-overlooks-flat-recurrence)
- [Nit](#nit)
  - [R6-n1 — Altered text inside quotation marks](#r6-n1--altered-text-inside-quotation-marks)
  - [R6-n2 — "essential"](#r6-n2--essential)
  - [R6-n3 — `interpSetoid` sketch omits its model dependence](#r6-n3--interpsetoid-sketch-omits-its-model-dependence)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`,
revision 3. This is a fresh cycle over revision 3's change — the
switch from equational to interpretative equality, with the
equational presentation deferred — concentrated on the edited
regions, with section 6.1's reworked statement shape examined from
scratch against the primary source. Content verified in rounds 1-5
(revisions 1-2 at every theorem-level claim) was not re-verified.

## Summary verdict

The presentation-layer switch itself is coherent and correctly
propagated: the interpretative-setoid characterization matches
`LawvereERQuot.lean`/`LawvereKSimQuot.lean` exactly (verified
against both files); every remaining mention of `Derivable`,
derivable equality, or the equational presentation is correctly
scoped to the deferred workstream or to historical notes; sections
6.3 and 6.4 are unaffected as claimed (their steps concern
definability of denotations, not program equality); 4.2's
`standardModel`/`interpSetoid` sketch coheres with 4.1's
structural-recursion interpretation and with 6.1's faithfulness
claim; the constructive constraint is respected by the standard
model at arrow sorts; and the well-definedness and faithfulness
reasoning for `collapseFunctor` is sound. The withdrawal of
revision 2's fullness claim is correct, and the doubling
counterexample at uniform tier stands (with one repair to its
stated justification, R6-m1).

The correction undershoots, however. The replacement statement
`ramified_definability` narrows Leivant's definability existential
("for some ramified f", ranging over arbitrary object types) to
contexts of tower sorts `Omega^k o`, and the narrowed statement is
false: the paper's own completeness realizer (Lemma 6, eq. (8),
p. 221) has input type `Omega(eta -> eta)`, an object sort no
coercion connects to the tower sorts, and tower-sorted inputs
support object-type recurrence only — the fragment Leivant
identifies as first-order (2.4(3), p. 216), which excludes
exponentiation. Independently of truth, the tower-quantified
statement is not what Lemma 6 proves, so under the
transcription-only policy it has no source. The collapse-category
packaging built on the tower colimit inherits the defect and
additionally asserts an assembly whose coherence obligations are
unnamed. One blocker, one major; both are statement-shape and
packaging repairs that leave the proof routes of sections 6.2-6.4
untouched.

## Verification status

Verified directly for this review:

- The document was read in full; each region named in the
  revision-3 change list was checked (title and status paragraph;
  1.1; 1.2; the 2.1 scope phrases; 2.3 tail; 2.5; 3.3; section 4
  title; 4.1; 4.2; 4.3; 5.1; 6.1; 6.2 title; 7 intro; 8 phases 1,
  5, 7; 9 first bullet; 10 questions 3 and 7).
- Leivant III PDF, read as page images this round: p. 213 (simple
  types and their semantic function spaces); p. 214 (r-type
  grammar; object types are `o` and the `Omega`-types `Omega tau`
  for every r-type `tau`; "extensionally, A^{Omega tau} = A^o";
  the iterate remark contrasting `N^{Omega(o->o)}` with `N^o`);
  p. 215 (eq. (4): recurrence argument `Omega tau`, output `tau`;
  eq. (5): flat recurrence with recurrence argument at `o` and
  step functions receiving subterms only; the note that flat
  recurrence is not stipulated at `Omega`-typed recurrence
  arguments; the `RMRec-omega` definition); p. 216 (2.4(1)
  coercions `kappa_tau : Omega tau -> theta`,
  `kappa-hat_tau : Omega tau -> tau`, `delta_theta : theta -> o`;
  2.4(2) `+ : o, Omega o -> o`, `x : (Omega o)^2 -> o`; 2.4(3):
  `exp` is not ramifiable at first order "because the two
  arguments of ramified addition must be of different types",
  `e : Omega(o -> o) -> (o -> o)`, and "ramified recurrence in
  first-order types ... is the same as recurrence restricted to
  object types of the form `Omega^m o`", the polynomial-time
  characterization; 2.4(4): `2_m` at type `eta -> theta` with
  `eta` built by induction through `Omega(eta' -> eta')`); p. 217
  (2.4(6): `sz : Omega(theta -> theta) -> theta`; Lemma 1);
  p. 218 (ramified simultaneous recurrence takes its recurrence
  argument at `Omega tau`; section 2.7's `tau-minus`, `f-minus`,
  `G-plus-tau`; Lemma 3); p. 219 (the definability definition:
  "We say that a function f over A is defined in RRec-omega
  (respectively, RMRec-omega) if f = f-minus for some ramified f
  generated in RRec-omega (RMRec-omega)"; Lemma 4; the
  `iter`/`exp` non-closure remark); p. 221 (Lemma 6's statement
  and proof: `stt` and `[phi]` as ramified functions of type
  `o, Omega o -> o`; eq. (8):
  `f(a) = [pi_1](delta_{Omega(eta->eta)} a, c x 2_q(sz(a)))` with
  `f : Omega(eta -> eta) -> o`); p. 227 (Theorem 14's five items
  and proof chain, re-confirming item (2) is the `f-minus`
  definability sense).
- Repository: `GebLean/LawvereERQuot.lean` (`erMorNSetoid` relates
  tuples by `interp` agreement at every context; composition via
  `Quotient.lift₂`; constructive throughout) and
  `GebLean/LawvereKSimQuot.lean` (`kMorNSetoid`, same pattern) —
  supporting 1.1's and 4.2's characterization of the adopted
  pattern and the assembly-plan paragraph.
- Section 6.1(a), reasoned through: with interpretative hom-sets,
  `collapseFunctor`'s morphism map factors as an ER-realizer
  assignment on raw terms (the substance deferred to 6.3) followed
  by `Quotient` descent; interp-equal terms have equal denotations,
  hence realizers in one ER class (well-definedness), and equal ER
  classes force equal denotations, hence interp-equal terms
  (faithfulness). Both arguments need every object sort to
  interpret as the algebra's carrier, which the paper supplies
  (p. 214, p. 218) and 4.2's `standardModel` matches. The claim
  "well-defined and faithful by construction" is sound, and remains
  sound if `SynCatFO` is widened per R6-B1.
- Section 6.1(b), the doubling counterexample: the conclusion is
  verified (2.4(3) states that `exp(sn) = +(exp(n), exp(n))`
  "cannot be ramified, because the two arguments of ramified
  addition must be of different types"; the document's 4.2 note
  that no identity-realizing `o -> Omega o` map exists is
  consistent with 2.4(1), whose coercions all run downward). The
  stated justification has a gap (R6-m1). The stronger claim
  implicit in "has no realizer" (no term of any shape, not merely
  no recurrence on the input) is a routine semantic-growth
  argument not spelled out in the paper; it is acceptable at
  survey level because the corrected statement does not depend on
  it, only the motivation does.
- Consistency sweep: grep over `Derivable`/derivable/equational —
  every occurrence sits in a deferred-workstream, historical, or
  source-description context; no passage assumes equational
  equality for in-scope content. Sections 6.3 and 6.4 checked leg
  by leg: the Proposition 7 composite, the `1l(A)` representation,
  Lemma 12/Proposition 13, and both landing options concern which
  functions are definable, not which programs are equated; none
  invokes derivable program equality.
- Constructivity at arrow sorts: function-space carriers,
  recursors at higher types (`Nat.rec`/`PolyFix` folds), and
  `Quotient.mk`/`lift` composition are all computable; the
  interpretative setoid is `Prop`-valued extensional agreement,
  needing no decidability; nothing forces `noncomputable`. No
  finding.
- Lint gates on the reviewed document: `markdownlint-cli2`
  0 errors; `doctoc --dryrun --update-only` "Everything is OK"; no
  absolute local paths; all all-caps tokens are acronyms; no
  emojis.

Standing from rounds 1-5 (not re-verified): everything outside the
revision-3 edit list, including the 2.1 table's row-by-row
verification, the machine-embedding claims (R4-M2 fix), the
Proposition 7 composite scoping (R4-M1 fix, R5-m1 relabeling —
confirmed present in its corrected "(1) to (3) to (4)" form), the
three 2026-07-02 paper summaries, and the repository-declaration
inventory.

## Blocker

### R6-B1 — `ramified_definability` restricts the existential to tower sorts

Location: section 6.1 (the `SynCatFO` docstring "contexts of
object sorts Omega^m o"; the statement
`∃ k (g : tierCtx k n ⟶ tierCtx 0 m), collapseDenotation g = f`;
the paragraph "The tier quantification is essential, and corrects
revision 2"; the sentence "Together the two statements are the
denotational form of Leivant III Theorem 14, items (1)-(2)");
section 2.5 ("a tier-quantified definability theorem"); section 8
phase 5 ("deliverable: for every ER morphism, a tier and a
ramified realizer with matching denotation") and phase 7.

Defect: Leivant's definability — the sentence the document itself
cites in 6.1 — is an existential over ramified realizers of
arbitrary r-type: "f = f-minus for some ramified f generated in
RMRec-omega" (p. 219). For a first-order collapse the realizer's
type is `sigma-vec -> theta` with the `sigma_i` and `theta`
arbitrary object types, and object types are `o` and `Omega tau`
for every r-type `tau` (p. 214) — including `Omega`-of-arrow sorts
such as `Omega(o -> o)`, not only the tower sorts `Omega^m o`. The
document narrows the existential to `tierCtx k n`, contexts of
tower sorts. The narrowed statement is false, and separately it is
not the literature's statement:

- The paper's completeness realizer lands outside the tower
  sorts. Lemma 6's proof concludes (eq. (8), p. 221) with
  `f(a) = [pi_1](delta_{Omega(eta->eta)} a, c x 2_q(sz(a)))` of
  type `Omega(eta -> eta) -> o`: the input must sit at
  `Omega(eta -> eta)` because `sz` has type
  `Omega(theta -> theta) -> theta` (2.4(6), p. 217) and `2_q` has
  type `eta -> theta` with `eta` produced by 2.4(4)'s induction as
  nested `Omega(eta' -> eta')` sorts — none of the form
  `Omega^m o`.
- No coercion repairs the mismatch. The 2.4(1) coercions run from
  `Omega(sigma-vec -> theta)` to `theta` and, composed, down to
  `o`; from a tower sort `Omega^k o` they reach exactly the lower
  tower sorts and never an `Omega`-of-arrow sort. (Precomposition
  with `kappa-hat` composites does raise tower-sorted inputs to a
  common tower tier, so the uniform-tier shape within the towers
  is not the defect; the restriction to towers is.)
- Tower-context hom-sets exclude exponentiation. A genuine
  recurrence (eq. (4)) consuming an input of type `Omega^k o` has
  output type `Omega^{k-1} o`, so recursion driven by tower-sorted
  inputs stays at object-type outputs — the fragment 2.4(3)
  identifies with first-order ramified recurrence and, over word
  algebras, with polynomial time (over the unary algebra, the
  corresponding first-order cell is `E^2`, section 2.2 of the
  document; both strictly below elementary). Recurrence at an
  arrow type — the only source of exponential growth (2.4(3)) —
  needs its recurrence argument at an `Omega`-of-arrow sort, and
  the only schemas producing such a term from tower-sorted inputs
  are explicit definition and flat recurrence, neither of which
  passes recursive values, so the dependence on the inputs is
  bounded-depth case analysis and the higher-type internals
  contribute constants only. Hence `fun x => 2^x`, an ER morphism
  `1 ⟶ 1`, has no realizer `g : tierCtx k 1 ⟶ tierCtx 0 1` for any
  `k`, and `ramified_definability` fails.
- Policy ground, independent of the semantic argument: Lemma 6
  proves definability with an `Omega(eta -> eta)`-sorted realizer,
  not a tower-sorted one, so the tower-quantified statement has no
  transcription source; establishing it (even if it were true)
  would be a novel proof route, which section 1.2 forbids.

Consequences: the in-scope theorem's completeness half is
unprovable as stated; the sentence identifying the two statements
with Theorem 14 (1)-(2) is false; section 6.2 (which faithfully
records what Lemma 6 gives) and phase 5's deliverable disagree;
and `SynCatFO`'s object restriction excludes the very morphism the
Lemma 6 transcription will construct.

Suggested fix: widen `SynCatFO` to the full subcategory on
contexts of all object sorts (`o` and `Omega tau` for every r-type
`tau`); the collapse and the standard model treat all object sorts
uniformly (every object sort's carrier is the algebra, pp. 214,
218), so `collapseFunctor`'s well-definedness and faithfulness
arguments carry over verbatim. State definability with the
existential over an object-sort context: for every
`f : n ⟶ m` in `LawvereERCat` there exist an object-sort context
`Γ` of length `n` and `g : Γ ⟶ objCtx o m` with
`collapseDenotation g = f` (pinning the output at `o` is harmless:
Lemma 6's realizer already has output `o`, and `delta`
postcomposition, 2.4(1), lowers any object-sort output). If a
common input sort is wanted, derive it from the transcribed
Lemma 6 realizer's shape rather than fixing it in the statement.
Rework 2.5, 6.1's narrative paragraph, and phases 5 and 7
accordingly; in the narrative, the doubling example still shows
why uniform-tier fullness fails, and the exponentiation example
shows why tower-tier quantification is still insufficient.

## Major

### R6-M1 — The collapse-category packaging overclaims and leaves obligations unnamed

Location: section 6.1, final paragraph ("a collapse category with
objects `N` and `hom(n, m)` the colimit over `k` of
`Hom(tierCtx k n, tierCtx 0 m)` ... the two statements then
assemble into an explicit equivalence with `LawvereERCat`");
section 2.5 ("optionally packaged as an equivalence out of a
tier-colimit collapse category"); section 10, question 7.

Defect, two parts. (i) Under R6-B1, the colimit over `k` of the
tower-context hom-sets collects exactly the tower-realizable
functions, a class that excludes exponentiation; the described
category is therefore not equivalent to `LawvereERCat`, and the
sentence asserting the assembly is false as stated, independently
of whether the packaging is built. (ii) Even for a reworked index
(object-sort contexts under coercion precomposition), the
paragraph asserts composition "aligning tiers via `omegaShift`" as
if available: well-definedness of composition on colimit classes —
compatibility of the shift with the coercion-precomposition
transition maps and independence of representatives — is a proof
obligation named nowhere, and functoriality of `omegaShift` on the
higher-order system is itself open question 3, a dependence the
paragraph does not acknowledge. Over object-sort contexts a
further obligation appears: the coercion diagram is not obviously
directed (2.4(1) coercions run from `Omega(sigma-vec -> theta)` to
`theta` only, and two arbitrary object sorts need not admit a
common sort above both), so the hom-colimit is over a non-directed
diagram and composition needs a fresh argument.

Suggested fix: after the R6-B1 restatement, either reduce the
packaging to a sentence marking it contingent — on the reworked
colimit shape, on `omegaShift` functoriality (cross-reference
question 3), and on composition well-definedness, all named as
obligations — or move it to sections 9/10 as an open design
question. Do not assert the equivalence as an assembly that
follows from the two statements.

## Minor

### R6-m1 — The no-recursion parenthetical overlooks flat recurrence

Location: section 6.1: "a morphism `[o] -> [o]` admits no
recursion on its input at all (the recurrence argument must sit at
an Omega-sort strictly above the output)".

Defect: the document's `RMRec-omega` includes flat recurrence (the
2.1 table's eq. (5) row: "the system formalized here"), whose
recurrence argument sits at type `o` — not at an `Omega`-sort —
with arbitrary output type (p. 215). As a statement about
recurrence arguments in the formalized system, the parenthetical
is therefore false. The conclusion survives for a different
reason: flat recurrence's step functions receive only the subterms
(`g_ci : sigma-vec, o^{r_i} -> tau`), never the recursive values,
so it is one-step case analysis and contributes no recursion; the
doubling-specific evidence is 2.4(3)'s remark that the two
arguments of ramified addition must have different types.

Suggested fix: reword to, e.g., "admits no value-passing
recurrence on its input: eq. (4) recurrence arguments sit at an
Omega-sort strictly above the output, and flat recurrence
(eq. (5)), which does consume an `o`-sorted argument, passes no
recursive values and so is case analysis".

## Nit

### R6-n1 — Altered text inside quotation marks

Section 6.1 renders the 2.7 definition as "f is defined in
`RMRec-omega` if f = g-minus for some ramified g" inside quotation
marks; the paper reads "f = f-minus for some ramified f generated
in RMRec-omega" (p. 219). The bound-variable renaming is
meaning-preserving, but altered text should not sit unmarked
inside quotation marks; either quote verbatim or drop the marks.

### R6-n2 — "essential"

Section 6.1: "The tier quantification is essential" — a
value-laden adjective under the style rules; the sentence is
rewritten under R6-B1 in any case ("required" or "load-bearing by
the source's formulation" style phrasing conforms).

### R6-n3 — `interpSetoid` sketch omits its model dependence

Section 4.2 sketches
`def interpSetoid (Γ : Ctx S) (s : S) : Setoid (Tm Σ Γ s)`; the
relation is agreement of `eval` at `standardModel P` on every
environment, but the signature surfaces neither the presentation
nor the model. Names are declared provisional; the missing
parameter is structural rather than nominal, so the sketch should
carry it (compare `erMorNSetoid`, which needs no such parameter
only because `ERMorN.interp` is globally fixed).

## Convergence verdict

Not converged. Revision 3's interpretative-equality switch is
correctly and consistently executed everywhere except the one
place that carries new mathematics: section 6.1's statement shape.
R6-B1 (the tower-sort restriction of the definability existential)
makes the in-scope theorem's completeness half false as stated and
without a transcription source; R6-M1 (the tier-colimit packaging)
asserts an equivalence the described construction cannot realize
and leaves its coherence obligations unnamed. Both fixes are
statement-shape and packaging edits confined to sections 2.5, 6.1,
and 8 (phases 5 and 7): no proof route changes, since section
6.2's Lemma 6 transcription already delivers exactly the corrected
statement's content and section 6.3's soundness route is
unaffected (its functor domain widens with `SynCatFO` under the
same well-definedness and faithfulness arguments). One focused
follow-up round to verify the restated 6.1 should suffice.

Finding counts: 1 blocker (R6-B1), 1 major (R6-M1), 1 minor
(R6-m1), 3 nits (R6-n1 through R6-n3).
