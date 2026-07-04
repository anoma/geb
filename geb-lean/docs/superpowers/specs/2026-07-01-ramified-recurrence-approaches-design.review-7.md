# Adversarial review 7 — ramified-recurrence approaches survey (round-6 fixes)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Resolution of round-6 findings](#resolution-of-round-6-findings)
  - [R6-B1 — resolved](#r6-b1--resolved)
  - [R6-M1 — resolved](#r6-m1--resolved)
  - [R6-m1 — resolved](#r6-m1--resolved-1)
  - [R6-n1 — resolved](#r6-n1--resolved)
  - [R6-n2 — resolved](#r6-n2--resolved)
  - [R6-n3 — resolved](#r6-n3--resolved)
- [Source verification of the reworked section 6.1](#source-verification-of-the-reworked-section-61)
  - [(a) All object sorts denote carrier copies](#a-all-object-sorts-denote-carrier-copies)
  - [(b) The f-minus definability paraphrase](#b-the-f-minus-definability-paraphrase)
  - [(c) The exponentiation counterexample](#c-the-exponentiation-counterexample)
- [Faithfulness and well-definedness over the widened `SynCatFO`](#faithfulness-and-well-definedness-over-the-widened-syncatfo)
- [Consistency sweep](#consistency-sweep)
- [Lint gates](#lint-gates)
- [New findings](#new-findings)
  - [Minor](#minor)
    - [R7-m1 — Lemma 6's proof is displayed unary; a tupling remark is due](#r7-m1--lemma-6s-proof-is-displayed-unary-a-tupling-remark-is-due)
  - [Nit](#nit)
    - [R7-n1 — `ObjCtx` is not glossed](#r7-n1--objctx-is-not-glossed)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`,
revision 3 with the round-6 fix set applied. This is a focused
convergence check: each round-6 finding is verified against the
current text, the reworked section 6.1 is re-checked from scratch
against the primary source (Leivant III, pp. 214-221 re-read as
page images this round), and the fix-adjacent regions (2.5, 4.2,
6.2, 8 phases 5 and 7, open questions 3 and 7) are swept for
consistency. Content verified in rounds 1-6 outside those regions
was not re-verified.

## Resolution of round-6 findings

| Finding | Severity | Status |
| --- | --- | --- |
| R6-B1 (definability existential restricted to tower sorts) | Blocker | Resolved |
| R6-M1 (collapse-category packaging overclaimed) | Major | Resolved |
| R6-m1 (no-recursion parenthetical overlooked flat recurrence) | Minor | Resolved |
| R6-n1 (altered text inside quotation marks) | Nit | Resolved |
| R6-n2 ("essential") | Nit | Resolved |
| R6-n3 (`interpSetoid` model dependence) | Nit | Resolved |

### R6-B1 — resolved

`SynCatFO` is now "the full subcategory of the higher-order
syntactic category on contexts of object sorts - o and Omega tau
for arbitrary r-types tau", with the section-2.7 justification
quoted in the docstring: "Every object sort's universe is a copy
of the base carrier (Leivant III section 2.7: 'the universe of
sort theta is a copy A^theta of A')". The quotation is verbatim
against the paper (p. 218; see source check (a) below). The
statement now reads

```lean
theorem ramified_definability {n m} (f : (n : LawvereERCat) ⟶ m) :
    ∃ (Γ : ObjCtx n) (g : Γ ⟶ oCtx m),
      collapseDenotation g = f
```

quantifying an object-sort context, with the output pinned at
`oCtx m` — the shape Lemma 4 (p. 219) licenses ("iff G = f-minus
for some ramified f with target type o"). The explanatory prose
matches the round-6 analysis point for point: "It must range
beyond the tower sorts `Omega^k o`: Lemma 6's own realizer
(eq. (8), p. 221) takes its input at the object sort
`Omega(eta -> eta)`, the coercions of section 2.4(1) run downward
only, and tower-sorted inputs drive object-type recurrence alone
(the first-order fragment), so, e.g., exponentiation has no
realizer over any tower-sort context." Each leg is re-verified
against the source in check (c) below. Sections 2.5 ("an
object-sort-quantified definability theorem") and 8 (phase 5:
"deliverable: for every ER morphism, an object-sort context and a
ramified realizer with matching denotation") are updated to match;
no occurrence of `tierCtx` or of tier-quantified phrasing remains
(grep-verified; the residual "tower" occurrences are the ER
runtime tower bounds and the tower sorts named as the rejected
narrower choice).

### R6-M1 — resolved

The packaging paragraph now opens "A categorical packaging ... is
an investigation item (open question 7), not an assertion" and
names the three obligations: "over general object sorts the
coercion diagram is not directed as a tower-indexed colimit would
require, composition on classes carries a well-definedness
obligation, and any `omegaShift`-based alignment depends on open
question 3. The theorem content is the two statements above either
way." Open question 7 restates all three and cross-references
question 3; section 2.5 says "a categorical packaging of the pair
is an open question (section 6.1)"; phase 7 conditions the
packaging on "open question 7 resolves it". The non-directedness
assertion (strengthened from round 6's "not obviously directed")
was checked and holds: from any object sort, the 2.4(1) coercions
out of it (`kappa` to the target sort, `delta` to `o`, `kappa-hat`
landing at a functional type unless the sort is a bare
`Omega theta`) determine a single descending chain of object
sorts, so no object sort coerces to both `Omega o` and
`Omega(o -> o)`, and the diagram has no common upper bounds.

### R6-m1 — resolved

The fullness-failure justification now reads: "at `[o] -> [o]` no
monotonic recurrence applies to the input (its recurrence argument
must sit at an Omega-sort), and flat recurrence, which is
available at sort `o`, passes no recursive values and so yields
case analysis and destructors only; doubling has no realizer
there." This matches eq. (5) (p. 215: recurrence argument at `o`;
step functions `g_ci : sigma-vec, o^{r_i} -> tau` receive subterms
only) and Lemma 1's reduction of flat recurrence to `case` plus
destructors (p. 217).

### R6-n1 — resolved

The definition is now paraphrased without quotation marks:
"(section 2.7 of the paper: a function over A is defined in
RMRec-omega when it is the collapse f-minus of some ramified f)".
Content matches the paper's definition (p. 219, inside
section 2.7; source check (b) below).

### R6-n2 — resolved

"The quantification over object-sort contexts is required by the
source." — the value-laden adjective is gone; grep confirms no
occurrence of "essential" remains in the document.

### R6-n3 — resolved

`interpSetoid` now carries the presentation parameter,
`def interpSetoid (P : Presentation) (Γ : Ctx S) (s : S) :
Setoid (Tm P.sig Γ s)`, with the comment "The model dependence is
structural: erMorNSetoid needs no such parameter only because
ERMorN.interp is globally fixed."

## Source verification of the reworked section 6.1

### (a) All object sorts denote carrier copies

Confirmed. Section 2.7 (p. 218) reads: "Recall that the
functionals defined in RRec-omega(A) are not over A, but over a
sorted algebra whose sorts are the object types, and where the
universe of sort theta is a copy A^theta of A." The sorts of the
semantic algebra are all the object types (`o` and `Omega tau` for
every r-type `tau`, per the definition on p. 214, which also notes
"extensionally, A^{Omega tau} = A^o"). So every object sort
denotes a copy of the carrier, morphisms between object-sort
contexts collapse to functions over `A` — numeric for `natSig` —
and the docstring's quotation is verbatim.

### (b) The f-minus definability paraphrase

Confirmed. The paper (p. 219): "We say that a function f over A is
defined in RRec-omega (respectively, RMRec-omega) if f = f-minus
for some ramified f generated in RRec-omega (RMRec-omega)." The
document's paraphrase — "a function over A is defined in
RMRec-omega when it is the collapse f-minus of some ramified f" —
is faithful, and its statement realizes the existential over
arbitrary ramified realizers: `ObjCtx n` ranges over all
object-sort contexts, and the output pinned at `o` is the normal
form Lemma 4 (p. 219) establishes ("An unramified functional G
over A is defined in RRec-omega(A) iff G = f-minus for some
ramified f with target type o"; `delta_theta : theta -> o`
postcomposition supplies the reduction).

### (c) The exponentiation counterexample

Confirmed on all three legs.

- Eq. (8) (p. 221) concludes Lemma 6's proof with
  `f(a) = [pi_1](delta_{Omega(eta->eta)} a, c x 2_q(sz(a)))` "with
  `f : Omega(eta -> eta) -> o`" — the realizer's input sort is
  `Omega(eta -> eta)`, where `eta` is produced by 2.4(4)'s
  induction (p. 216: for `2_{m+1}` at `Omega(eta -> eta) -> theta`
  from `2_m` at `eta -> theta`) and consumed by `sz` at
  `Omega(theta -> theta) -> theta` (2.4(6), p. 217). None of these
  sorts is a tower sort `Omega^m o`.
- The 2.4(1) coercions (p. 216) are
  `kappa_tau : Omega tau -> theta` (for
  `Omega tau === Omega(sigma-vec -> theta)`),
  `kappa-hat_tau : Omega tau -> tau`, and
  `delta_theta : theta -> o` — all downward; no coercion raises a
  tower sort to an `Omega`-of-arrow sort.
- 2.4(3) (p. 216) identifies "ramified recurrence in first-order
  types, which in the present context is the same as recurrence
  restricted to object types of the form Omega^m o", and gives the
  exponentiation obstruction: the recurrence
  `exp(sn) = +(exp(n), exp(n))` "cannot be ramified, because the
  two arguments of ramified addition must be of different types";
  exponentiation instead needs second-order recurrence
  (`e : Omega(o -> o) -> (o -> o)`). Over the unary algebra the
  first-order cell is `E^2` (document section 2.2; Table 1), whose
  functions are polynomially bounded, so `fun x => 2^x` is
  excluded, and the document's conclusion — exponentiation has no
  realizer over any tower-sort context — follows. The compressed
  phrase "tower-sorted inputs drive object-type recurrence alone"
  is the round-6-verified argument (inputs can serve as recurrence
  arguments only at their own sorts; parameters and flat
  recurrence pass no recursive values into arrow-type iteration
  counts), restated at survey granularity.

## Faithfulness and well-definedness over the widened `SynCatFO`

The `collapseFunctor` docstring's claim — "With interpretative
hom-sets it is well-defined and faithful by construction" — holds
verbatim over the widened domain. Both directions of the round-6
argument (interp-equal terms have equal denotations, hence
realizers in one ER class; equal ER classes force equal
denotations, hence interp-equal terms) use only the fact that
every object sort interprets as the algebra's carrier, which
p. 218 supplies for all object sorts at once (quoted in check (a))
and which 4.2's `standardModel` docstring matches ("object sorts
interpret as the algebra's carrier"). A sweep of the document
found no passage that still assumes the narrower tower-sort
domain: `tierCtx` is gone, 2.5 and phases 5 and 7 quantify
object-sort contexts, and the tower sorts appear only where they
are named as insufficient.

## Consistency sweep

- 6.1 versus 6.2: consistent. The 6.2 chain (Lemma 6 into
  `RMRec-omega_o`, Lemma 1 into `RMRec-omega`) delivers exactly
  the existential's content: an object-sort input context
  (Lemma 6's `Omega(eta -> eta)` slot) and output `o`. One
  arity-shape gap between the paper's displayed proof and the
  document's n-ary statement is recorded as R7-m1 below.
- 6.1 versus 8: phase 5's deliverable is the
  `ramified_definability` family over object-sort contexts; phase
  7 assembles it and conditions the categorical packaging on open
  question 7. Consistent.
- 6.1 versus 2.5: "object-sort-quantified definability theorem
  plus a soundness functor", packaging an open question.
  Consistent.
- Open questions 3 and 7: question 7 names the three packaging
  obligations and depends on question 3 exactly as 6.1's paragraph
  says. Consistent.

## Lint gates

- `npx markdownlint-cli2` on the reviewed document: 0 errors.
- `npx doctoc --dryrun --update-only`: "Everything is OK."

## New findings

### Minor

#### R7-m1 — Lemma 6's proof is displayed unary; a tupling remark is due

Location: section 6.1 (`ramified_definability` quantifies
`f : (n : LawvereERCat) ⟶ m` with a single length-`n` context);
section 6.2 step 2; section 8 phase 5.

Observation: Lemma 6's statement (p. 221, "If a function f over A
is computable in time elementary in the size of the input, then
f in RMRec-omega_o(A)") covers the p-ary partial functions
`[M]^p` of the machine model (p. 220), but its proof is displayed
in unary notation throughout, with no explicit arity remark: the
input-loading clause is `[phi](a, alpha) = if phi is phi_1 then a
else alpha` (one input, one input register), `stt` and `[phi]`
are "ramified functions of type o, Omega o -> o" with a single
`a`, and eq. (8) is unary. The document's statement generalizes in
two directions at once: `n` inputs sharing one context and `m`
outputs sharing one realizer context. The generalization is
routine but not displayed in the paper: per-register input
loading is immediate; the clock term over `n` inputs needs the
per-input sizes combined (per-input `sz` instances at staggered
object sorts chained by ramified `+`, or equivalent bound
arithmetic — the heterogeneous `ObjCtx n` accommodates this, and
is presumably why the context is not sort-uniform); `m`
components can share one context by taking the maximum `q` across
components (`2_q` is monotone in `q`). Phase 5's "bound-format
arithmetic" line covers the tower-to-`c * 2_q` conversion but not
this multi-input clock assembly.

Suggested fix: one sentence in 6.2 step 2 (or phase 5)
acknowledging that Lemma 6's proof is presented for a single input
and output and that the n-ary, m-output form of
`ramified_definability` is assembled componentwise with a common
clock — keeping the transcription boundary explicit under
section 1.2's policy.

### Nit

#### R7-n1 — `ObjCtx` is not glossed

Section 6.1's docstring glosses `oCtx m` ("the context of m copies
of o") but not `ObjCtx n`; the length-`n` object-sort reading is
inferable from the prose ("quantified over object-sort input
contexts") but a parallel gloss ("object-sort contexts of length
n") would remove the inference. Names are declared provisional;
cosmetic.

## Convergence verdict

Converged: no blocker and no major. All six round-6 findings are
resolved as described, the reworked section 6.1 is faithful to the
source at every checked point (the section-2.7 carrier-copy
sentence, the f-minus definability definition, eq. (8)'s realizer
sort, the downward-only coercions, and the first-order
identification of 2.4(3)), the widened `SynCatFO` preserves the
`collapseFunctor` well-definedness and faithfulness reasoning
verbatim, and the fix-adjacent regions are mutually consistent.

Finding counts: 0 blockers, 0 majors, 1 minor (R7-m1), 1 nit
(R7-n1). Both new findings are one-sentence documentation
additions; neither affects the statement shape or the proof-route
map.
