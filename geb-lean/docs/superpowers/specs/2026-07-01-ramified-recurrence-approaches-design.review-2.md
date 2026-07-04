# Adversarial review 2 — ramified-recurrence approaches survey

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round-1 finding resolution](#round-1-finding-resolution)
- [Source verification notes](#source-verification-notes)
  - [M1 fix: base substitution](#m1-fix-base-substitution)
  - [B1 fix: bsum/bprod novelty claims](#b1-fix-bsumbprod-novelty-claims)
- [New findings](#new-findings)
  - [Major](#major)
    - [R2-M1 — `kappaHat`'s type contradicts its docstring under the new `omegaShift`](#r2-m1--kappahats-type-contradicts-its-docstring-under-the-new-omegashift)
  - [Minor](#minor)
    - [R2-m1 — Stale cross-reference "section 7.5" in section 3.2](#r2-m1--stale-cross-reference-section-75-in-section-32)
  - [Nit](#nit)
    - [R2-n1 — All-caps emphasis introduced by the edits](#r2-n1--all-caps-emphasis-introduced-by-the-edits)
    - [R2-n2 — "the last three rows" miscounts the annotated rows](#r2-n2--the-last-three-rows-miscounts-the-annotated-rows)
    - [R2-n3 — Residual unhedged universal negative in section 1.4](#r2-n3--residual-unhedged-universal-negative-in-section-14)
    - [R2-n4 — References entry splits a repository path across code spans](#r2-n4--references-entry-splits-a-repository-path-across-code-spans)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Round-1 review:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.review-1.md`.
This is a verification round: it checks that each round-1 finding is
resolved, re-verifies the mathematical content of the B1 and M1 fixes
against the Leivant III PDF, and sweeps for defects introduced by the
round-1 edits. The document remains a brainstorming-phase approaches
survey and is not penalized for presenting multiple approaches.

## Round-1 finding resolution

| Finding | Status | Evidence |
| --- | --- | --- |
| B1 (bsum/bprod mislabeled transcription) | Resolved | Section 1.4 now lists the realizers as novel: "The bounded-sum and bounded-product realizers in the fullness proof (section 4.6): Leivant III contains no such constructions (its completeness route is the excluded machine simulation, Lemma 6), so these are novel, built in the style of its sections 2.4(2) and 2.6." Section 4.6's docstring marks them "NOVEL constructions in the style of sections 2.4(2) and 2.6 (the step needs the loop index, so ramified simultaneous recurrence, Lemma 2, or an equivalent device, plus tier alignment for the asymmetric ramified addition)". Section 6 item 5 adds "carry the main risk of this deliverable; section 7.3 schedules them for a spike", and open question 3 includes "the bsum/bprod realizers themselves (novel; section 4.6)". Mathematical claims verified below. |
| M1 (`omegaShift` asserted as higher-order endofunctor) | Resolved | Section 4.4 now states "Postcomposition with Omega is NOT a signature morphism on the higher-order presentation ... The candidate that does respect the signature is base substitution, tau -> tau[o := Omega o] ... Functoriality on the higher-order syntactic category (in particular closure of the axiom set under the shift) is unverified; see open question 7.1." Section 4.5 makes the endofunctor "unconditional ... for the first-order systems ...; for the higher-order system contingent on the base-substitution functoriality". Open question 7.1 now asks "Existence first". The base-substitution claims are verified below. The edit leaves `kappaHat`'s type inconsistent with its docstring — a new defect, filed as R2-M1 (round-1 M1 did not cover `kappaHat`, whose typing was consistent under the old definition). |
| M2 (applicative calculi / Proposition 7 listed as transcription; beta/eta omitted) | Resolved | The section 1.1 applicative row now reads "beta and eta reductions plus recurrence reduction and flat reduction. Transcription only under option C (section 3.2); options A/B formalize a combinatory analogue, a novel adaptation"; verified against p. 222 ("The reduction rules are the usual beta and eta reductions, plus Recurrence Reduction and Flat Reduction"). The Proposition 7 row carries "Same caveat: items (3)-(4) quantify over lambda terms"; the Theorem 14 row scopes in-scope transcription to "(1)-(2) relative to `LawvereERCat`". Section 1.4 lists "The combinatory analogue of the applicative calculi under options A/B (section 3.2)" as novel. Residual: the post-table sentence miscounts the annotated rows (R2-n2). |
| m1 (`kappa` vs `kappa`-hat naming) | Resolved | The morphism is named `kappaHat` throughout (sections 4.4, 4.5, 6 item 2, 7.1), with the deviation documented: "Leivant III's auxiliary kappa-hat (section 2.4(1)); the paper reserves kappa_tau for the composite Omega tau -> theta" — matching p. 216 ("we define a coercion function kappa_tau : Omega tau -> theta. First, define an auxiliary function kappa-hat_tau : Omega tau -> tau"). The typing defect at non-first-order sorts is separate (R2-M1). |
| m2 (unhedged universal negative in 2.2) | Resolved | Section 2.2: "No formalization of Leivant ramified/tiered recurrence was found in any proof assistant ... Subject to the limits of the search, the present workstream would be first of its kind on both counts." Residual echo in section 1.4's final bullet (R2-n3). |
| m3 (missing doctoc TOC) | Resolved | doctoc markers and a generated TOC are present after the H1; `doctoc --dryrun --update-only` reports "Everything is OK". |
| n1 (sub via dstrCase compression) | Resolved | Section 4.6: "sub by monotonic recurrence with a dstr-defined predecessor step". Checked: the step `pred(phi)` mentions no constructor components, hence is monotonic (p. 212), and `dstr` is available (flat recurrence, p. 212; primitive in the `_o` variants, section 2.5). |
| n2 (style-rule words) | Resolved | None of the flagged phrases remain ("the mathematical core", "the hinge", "the natural home", "cleanest categorical story", "first-order shadow"); replacements are neutral ("the first-order instance of the hereditary-majorization invariant of section 4.6", "the most direct correspondence with the cited constructions"). New all-caps emphasis was introduced by the edits (R2-n1). |

## Source verification notes

Verified directly for this review against the Leivant III PDF
(pp. 209-222): the section 2.1 monotonic/closed/flat definitions,
sections 2.3-2.7 (r-types, eq. (4)-(5), examples (1)-(6), Lemmas 1-4,
eqs. (6)-(7)), Lemma 6 (p. 221), and section 4.1 (p. 222).
`markdownlint-cli2` and `doctoc --dryrun --update-only` were run on
the reviewed document; both pass. Items round 1 listed as not
independently verified (Clote, Ritchie internals beyond round 1's
checks, Otto, Handley-Wainer, and the content summaries of the
section 2.1 modal/linear literature) remain unverified; spot checks
of venue/volume data in sections 2.1 and the References found no
discrepancies.

### M1 fix: base substitution

The document's claims for `tau[o := Omega o]` check out:

- Well-defined on r-types: r-types are freely generated from `o` by
  `->` and `Omega` (section 2.3, p. 214), so base substitution is a
  total structural recursion.
- Commutes with arrow and `Omega`: by the defining clauses of the
  recursion.
- Sends object types to object types: `o` maps to `Omega o` (an
  `Omega`-type) and `Omega tau` maps to `Omega (tau[o := Omega o])`;
  this is what makes the constructor-copy clause of the
  signature-endomorphism claim work (constants `c_i^theta` exist at
  every object type `theta`, p. 214). Application maps to application
  because substitution commutes with arrow; the `R_tau` instance maps
  to the `R_{tau[o := Omega o]}` instance, whose eq. (4) typing is
  the substituted typing.
- Tier successor on first-order sorts:
  `(Omega^m o)[o := Omega o] = Omega^{m+1} o` by induction on `m`,
  and p. 216(3) confirms the first-order sorts are exactly the
  `Omega^m o`. On `S = N` the shift is the signature endomorphism
  `m -> m + 1` outright, as section 4.4 states.
- The p. 214 iterate quotation supporting "postcomposition is not a
  signature morphism" matches the source.

One consequence the edit did not propagate:
`tau[o := Omega o] = Omega tau` holds exactly when `tau = Omega^m o`
(substitution commutes with `Omega`, and an arrow type is never an
`Omega`-type, so the fixed points are generated from `o` alone). At
every other sort — including object sorts such as `Omega (o -> o)`,
whose shift is `Omega (Omega o -> Omega o)`, not
`Omega Omega (o -> o)` — the shifted sort differs from `Omega tau`.
This produces finding R2-M1.

### B1 fix: bsum/bprod novelty claims

- Leivant III section 2.4 contains exactly: (1) coercion,
  (2) addition and multiplication, (3) exponentiation, (4) iterated
  exponentiation, (5) exponentiation in arbitrary `A`, (6) size of
  terms (pp. 216-217). No bounded-sum or bounded-product construction
  appears there or elsewhere in the paper.
- The completeness route is Lemma 6 (p. 221, section 3.2): "If a
  function `f` over `A` is computable in time elementary in the size
  of the input, then `f` is in `RMRec-omega_o(A)`", proved by
  register-machine simulation — the route the survey excludes.
- Monotonic recurrence denies the step access to the loop index:
  p. 212, "If the arguments `a...` are all absent, then the
  recurrence is monotonic" — over `N` the step sees the parameters
  and the critical (recursive) value but not the predecessor.
- Lemma 2 (section 2.6, p. 218) reduces ramified simultaneous
  monotonic recurrence to plain ramified monotonic recurrence; the
  proof of Lemma 6 itself threads machine state through simultaneous
  recurrence, corroborating it as the plausible index-threading
  device. The "asymmetric ramified addition" is confirmed at
  p. 216(2) (`+ : o, Omega o -> o`).

The section 4.6 docstring, the 1.4 bullet, section 6 item 5, and open
question 3 are mutually consistent on all of this.

## New findings

### Major

#### R2-M1 — `kappaHat`'s type contradicts its docstring under the new `omegaShift`

Location: section 4.4
(`def kappaHat (τ) : (omegaShift.obj [τ] ⟶ ([τ] : SynCat Σ E))`);
section 4.5 ("`kappaHat` naturality likewise"); open question 7.1
(the copointed-endofunctor candidate reading).

Defect: the round-1 M1 fix redefined `omegaShift` on sorts as base
substitution `tau -> tau[o := Omega o]`, but `kappaHat` kept its
round-1 type `omegaShift.obj [τ] ⟶ [τ]` and its docstring "Coercion
Omega tau -> tau". Under postcomposition these coincided; under base
substitution they coincide exactly at the sorts `Omega^m o` (see the
verification note above). At any other sort `omegaShift.obj [τ]` is
not `[Omega τ]`, so the declared morphism is not the paper's
`kappa-hat_tau : Omega tau -> tau` (p. 216). At arrow sorts the
declared type cannot be a coercion at all: a term of sort `o -> o` in
context `Omega o -> Omega o` that is extensionally the identity would
require a raising term `o -> Omega o`, which ramification excludes
(the point of the section 2.7 collapse/raising asymmetry). The same
conflation infects "Naturality with respect to omegaShift is a novel
statement to prove" (4.4), the 4.5 deliverable, and 7.1's "copointed
monoidal endofunctor" candidate: the would-be counit of the
base-substitution shift and Leivant's `kappa-hat` family are
different things outside the first-order sorts.

Suggested fix: type `kappaHat` independently of `omegaShift`, as
`[RType.omega τ] ⟶ [τ]` (a sort-indexed family of morphisms, per the
paper); note that it supplies counit components for `omegaShift`
exactly on the sorts `Omega^m o` (equivalently on `SynCatFO`); and
restate the 4.5 naturality deliverable and the 7.1 copointed reading
as scoped to that subcategory or as requiring a separate bridge.

### Minor

#### R2-m1 — Stale cross-reference "section 7.5" in section 3.2

Section 3.2: "Open sub-question (spike candidate, section 7.5): which
combinator basis suffices for the fullness proof". The combinator-
basis spike is open question 3; section 6 item 5 refers to the same
item as "section 7.3". Open question 5 concerns `Presentation`
structure, not combinator bases. The pointer was presumably orphaned
when the B1 fix merged the realizer spike into item 3. Suggested fix:
"section 7.3".

### Nit

#### R2-n1 — All-caps emphasis introduced by the edits

"NOT" (section 4.4 docstring) and "NOVEL" (section 4.6 docstring)
violate "No all-caps words unless they are acronyms" (CLAUDE.md style
guidelines). Suggested fix: lower-case them; the sentences carry the
emphasis without markup.

#### R2-n2 — "the last three rows" miscounts the annotated rows

Section 1.1, after the table: "except as annotated in the last three
rows (the lambda-calculus rows ...)". The annotated rows are the
applicative-calculi, Proposition 7, and Theorem 14 rows — the three
rows preceding the final (multi-sorted generalization) row, which
carries no annotation. "The last three rows" includes the unannotated
final row and excludes the applicative-calculi row. The parenthetical
disambiguates, but the count sends a checker to the wrong rows.
Suggested fix: "the three rows preceding the last" or name the rows.

#### R2-n3 — Residual unhedged universal negative in section 1.4

The final 1.4 bullet reads "no formalization of ramified recurrence,
the Grzegorczyk hierarchy, or a Kalmar-elementary characterization
exists in any proof assistant (section 2.2)" while section 2.2 was
rehedged to "was found". The list header's "no published precedent
found" arguably scopes the bullet, but aligning the phrasing would
remove the last unhedged instance. Suggested fix: "was found in any
proof assistant".

#### R2-n4 — References entry splits a repository path across code spans

The Tourlakis entry renders the path as two adjacent code spans
("`docs/research/2026-04-30-ksim-polynomial-bound-`" then
"`references.md`"), which displays with an intervening space and
defeats copy-paste. Suggested fix: a repo-relative link with short
link text, per `.claude/rules/markdown-writing.md` link conventions.

## Convergence verdict

Not converged. One MAJOR finding remains open (R2-M1, introduced by
the round-1 M1 edit); all eight round-1 findings are resolved. New
findings this round: 0 BLOCKER, 1 MAJOR, 1 MINOR, 4 NIT. A round 3
limited to R2-M1 (and optionally the MINOR/NIT items) should suffice
for convergence.
