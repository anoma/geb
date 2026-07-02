# Adversarial review 1 — ramified-recurrence approaches survey

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary verdict](#summary-verdict)
- [Verification status](#verification-status)
- [Blocker](#blocker)
  - [B1 — bsum/bprod realizers mislabeled as transcription](#b1--bsumbprod-realizers-mislabeled-as-transcription)
- [Major](#major)
  - [M1 — `omegaShift` asserted as an endofunctor of the higher-order system](#m1--omegashift-asserted-as-an-endofunctor-of-the-higher-order-system)
  - [M2 — Transcription list at odds with the no-binder recommendation](#m2--transcription-list-at-odds-with-the-no-binder-recommendation)
- [Minor](#minor)
  - [m1 — `kappa` naming inconsistent with the source](#m1--kappa-naming-inconsistent-with-the-source)
  - [m2 — Unhedged universal negative in section 2.2](#m2--unhedged-universal-negative-in-section-22)
  - [m3 — Missing table of contents](#m3--missing-table-of-contents)
- [Nit](#nit)
  - [n1 — "sub via dstrCase" compresses a two-step construction](#n1--sub-via-dstrcase-compresses-a-two-step-construction)
  - [n2 — Style-rule words](#n2--style-rule-words)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
The document is a brainstorming-phase approaches survey; per its own
status statement it is not penalized here for declining to fix a
single approach.

## Summary verdict

The survey is accurate in the large. Every row of the section 1.1
transcription table was checked against the primary PDF and matches
(section and equation numbers, the eq. (4) typing, the coercion
construction, Lemmas 1–4, Proposition 7's four items, Theorem 14's
five items, the section 2.4(3) p. 216 quotation). The repository
citations (Era.lean rule names and clone laws, `erMorNSetoid`,
`erKSimEquiv`, `SetoidCat`, `CategoryData`, the vendored slice
polynomial functors and their lack of W-types/coproducts, `PolyFix`,
`polyFixAlg_isInitial`, `polyBetweenCoprod`, `PolyFixRel`,
`polyEndoEquiv`, the `ERMor1` generator list) all check out, as do
the section 1.3 K^sim statements against the recorded Tourlakis
quotations. All external identifiers that were spot-checked resolve
to the claimed works.

One blocker: the fullness sketch labels the bsum/bprod realizers as
transcription of Leivant III section 2.4, which contains no such
constructions. Two major findings: the `omegaShift` endofunctor is
asserted for the higher-order system although the application
summand is not `Omega`-stable, and the transcription list includes
Proposition 7 and the applicative calculi while the recommended
design excludes the binder metatheory those calculi are defined
with. The remaining findings are precision and style items.

The document correctly avoids claiming an equivalence of categories
in section 4.6, and its remark that faithfulness of the collapse
functor is neither expected nor needed is right: `LawvereERCat`
hom-sets are interpretations-modulo-extensional-equality
(`erMorNSetoid`), so distinct derivability classes with equal
denotations must collapse.

## Verification status

Verified directly for this review:

- Leivant III PDF, pages 209–229: all rows of section 1.1, the
  monotonic/closed/flat definitions, footnote 4, Table 1, sections
  2.4(1)–(6), 2.5–2.7, 4.1, 6.1, 6.2. The PII on page 1 confirms
  DOI `10.1016/S0168-0072(98)00040-2`.
- Bellantoni–Cook full text: class `B` (initial functions i–v,
  schemas vi–vii, `s_i(;a) = 2a + i`), Theorem 3.3, Theorem 4.2,
  and Lemma 4.1 verbatim
  (`|f(x;y)| <= q_f(|x|) + max_i |y_i|`).
- DOIs resolved via Crossref/publisher: `10.1007/BF01201998`
  (Bellantoni–Cook, Computational Complexity 2(2) 1992, 97–110),
  `10.1007/978-1-4612-2566-9_11` (Leivant I, Feasible Mathematics
  II, 1995, 320–343), `10.1016/S0049-237X(99)80033-0` (Computation
  models and function algebras, Handbook of Computability Theory,
  1999, 589–681), `10.1016/j.tcs.2013.09.034` (Burrell–Cockett–
  Redmond, Safe recursion revisited I, TCS 2014; the safe/normal =
  player/opponent polarity reading matches the abstract). Laurent,
  TAC 22(10) (2009) 269–301, elementary Seely categories, confirmed
  via the journal's site.
- `docs/research/2026-04-30-ksim-polynomial-bound-references.md`:
  Corollary 0.1.0.44 (`K^sim_n = E^{n+1}` for `n >= 2`), the
  `K^sim_1 ⊊ E^2 ⊊ K^sim_2` caveat, and the level-1
  linear-value-bound lemma all match section 1.3's use.
- All repository files and declarations named in section 2.3;
  mathlib spot checks (`Language.Functions : ℕ → Type u`, absence
  of `Term.subst` identity/composition laws, `Nat.Primrec'`,
  `ofChosenFiniteProducts`, no Lawvere-theory or operad
  formalization beyond passing mentions).
- The document contains no absolute local paths and no emojis, and
  passes `markdownlint-cli2` as-is.

Not independently verified (paywalled or not obtained): Clote's
Definition 3.100, Theorem 3.101, Corollary 3.37, and the p. 50
tier/safe correspondence; Ritchie's Theorem 5 and its corollary;
Leivant I content claims (the document itself flags abstract-only
verification); Handley–Wainer; the Otto thesis (its existence and
relevance are corroborated by Bellantoni–Cook's reference [22],
"Categorical Characterization of Ptime I", McGill, 1991);
Burroni, Thibault, Hofmann, Danner, Hainry et al., Dal Lago et al.
content summaries; Heraud–Nowak internals; the Kolichala Lean 3
work; the upstream geb-mathlib W-type development status.

## Blocker

### B1 — bsum/bprod realizers mislabeled as transcription

Location: section 4.6 (docstring of `collapseFunctor_full`); the
same reading colors section 6 deliverable 5.

Defect: the fullness sketch says "bsum, bprod via ramified
recurrence with parameters (transcribing Leivant III section 2.4
constructions)". Leivant III section 2.4 contains coercions (1),
addition and multiplication (2), exponentiation (3), iterated
exponentials (4), simulation in arbitrary `A` (5), and size (6). No
bounded-sum or bounded-product construction appears there or
anywhere else in the paper; Leivant obtains the completeness
direction of Theorem 14 ((1) implies (2)) by register-machine
simulation (Lemma 6, section 3.2), which the survey places out of
scope. Moreover, in monotonic recurrence the step function sees
only the parameters and the previous value, not the recurrence
index (section 2.1: monotonic means the critical arguments are
absent), so `bsum f` needs the loop index threaded through ramified
simultaneous recurrence (section 2.6, Lemma 2) or an equivalent
device, plus tier alignment for the asymmetric ramified addition
`+ : o, Omega o -> o`. The realizers are therefore novel
constructions, and labeling them transcription contradicts the
document's own section 1.4 discipline; left as-is, the incorrect
marking would propagate into the design spec and the Lean
docstrings, where transcription markings are binding.

Suggested fix: reword to mark the bsum/bprod realizers as novel
constructions in the style of sections 2.4(2) and 2.6 (simultaneous
recurrence, Lemma 2), note that the paper's own completeness route
is the excluded machine simulation, and add the construction to the
spike list of section 7 (it is the load-bearing novel step of the
fullness proof, on par with open question 3).

## Major

### M1 — `omegaShift` asserted as an endofunctor of the higher-order system

Location: sections 4.4 (`def omegaShift : SynCat Σ E ⥤ SynCat Σ E`),
4.5 ("`omegaShift` as an endofunctor per system"), 1.4, and 7.1
(which presupposes the endofunctor exists and asks only for its
structure).

Defect: for the higher-order presentation the sort map `Omega` is
not a signature endomorphism, so the evident structural definition
of `omegaShift` on morphisms is partial. The application operation
at `(arrow σ τ, σ) -> τ` would have to map to an operation with
argument sorts `Omega (arrow σ τ), Omega σ` and result `Omega τ`,
but `Omega (arrow σ τ)` is an object sort, not the arrow sort
`arrow (Omega σ) (Omega τ)`, and the signature has no application
there. Leivant flags exactly this asymmetry (p. 214: an iterate of
`f` is defined if `f` inhabits `N^{Omega(o -> o)}`, "but not if
`n ∈ N^o`; and if `f : N^{Omega(o -> o)} -> N^o` then no
non-trivial iterate of `f` is well-defined"). For the first-order
systems (`S = N`, no application summand) the shift is a signature
endomorphism and the endofunctor is unproblematic. Section 4.6's
"comp via omegaShift and kappa" inherits the dependence.

Suggested fix: restrict the endofunctor deliverable to the
first-order systems and record the higher-order case as an open
question (existence, not just structure), or re-route the fullness
sketch's comp case through object-type-indexed families of
realizers — which is how the paper itself phrases its
constructions ("for each object type θ there is a copy of exp",
section 2.4(3)) — so that fullness does not depend on a syntactic
endofunctor.

### M2 — Transcription list at odds with the no-binder recommendation

Location: section 1.1 rows "Applicative calculi `RlMR-omega`,
`RlMR-omega_o`" and "Proposition 7"; sections 3.2 and the scope
paragraph.

Defect: Leivant defines `RλMR^ω` as an applied λ-calculus whose
reduction rules are "the usual β and η reductions, plus Recurrence
Reduction and Flat Reduction" (p. 222), and Proposition 7's items
(3) and (4) quantify over its terms. The survey lists both rows
under "Definitions and results to transcribe" while recommending
options A/B, which exclude binders (option C "Requires binder and
substitution metatheory that `Era.lean` deliberately avoids"), and
while excluding only "sections 4.2-5" from scope. Within A/B only a
combinatory analogue of Proposition 7 can be stated, and the
adequacy of the combinator basis is precisely open question 3. The
1.1 row also lists only "recurrence reduction and flat reduction
rules", omitting β/η, which reinforces the misreading that the
section 4.1 calculi are lambda-free.

Suggested fix: annotate the two rows as transcription targets only
under option C, with the A/B combinatory analogue marked as a novel
adaptation; or scope the transcription claim for Theorem 14 to its
items (1)–(2) and state that items (3)–(5) are represented
denotationally at most. Add β/η to the row's rule list.

## Minor

### m1 — `kappa` naming inconsistent with the source

Location: sections 4.4 and 7.1 versus section 1.1.

Section 1.1 correctly reports the paper's coercion `κ_τ : Ωτ → θ`
(p. 216: "we define a coercion function κ_τ : Ωτ → θ"). Sections
4.4 (`kappa (τ) : omegaShift.obj [τ] ⟶ [τ]`) and 7.1
("`kappa_tau : Omega tau -> tau`") type it `Ωτ → τ`, which is
Leivant's auxiliary `κ̂_τ` ("First, define an auxiliary function
κ̂_τ : Ωτ → τ"). The morphism exists and the dereliction analogy in
7.1 is mathematically correct; only the name is misattributed.
Suggested fix: use a distinct name (e.g. `kappaHat`) for the
`Ωτ → τ` morphism, or note the deviation from the paper's naming.

### m2 — Unhedged universal negative in section 2.2

Section 2.2 states "No formalization of Leivant ramified/tiered
recurrence exists in any proof assistant", while section 1.4 hedges
correctly ("no published precedent found"). A survey can attest
only to a search. Suggested fix: adopt the "none found" phrasing in
section 2.2 as well.

### m3 — Missing table of contents

`.claude/rules/markdown-writing.md` requires a doctoc-maintained
TOC in every committed Markdown document with more than one `##`
heading; the document has eight and carries no doctoc markers. The
pre-push check (`doctoc --dryrun --update-only`) skips files
without markers, so this is not caught mechanically. Suggested fix:
run `doctoc <file>` once and commit the inserted TOC.

## Nit

### n1 — "sub via dstrCase" compresses a two-step construction

Section 4.6: cut-off subtraction needs a monotonic recurrence whose
step is the dstr-defined predecessor; `dstrCase` alone yields only
predecessor and case. Suggested fix: "sub by monotonic recurrence
with a dstr-defined predecessor step".

### n2 — Style-rule words

Value-laden adjectives and metaphors per the CLAUDE.md style
section: "(the mathematical core)" (section 4.6 comment), "the
hinge" (section 5.4), "the natural home" and "cleanest categorical
story" (section 5.3), "first-order shadow" (sections 2.2 and 4.6).
Comparatives inside the trade-off table (e.g. "best proof
ergonomics") are serving a comparison and read as acceptable.
