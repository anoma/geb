# Adversarial review 12 — ramified-recurrence survey (rescope of first-order cells)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Verification status](#verification-status)
- [Findings](#findings)
  - [Blocker](#blocker)
    - [R12-B1 — 4.1's tower-context hom-set claim contradicts 6.1](#r12-b1--41s-tower-context-hom-set-claim-contradicts-61)
  - [Major](#major)
    - [R12-M1 — the tower-fragment `omegaShift` claim fails on flat recurrence](#r12-m1--the-tower-fragment-omegashift-claim-fails-on-flat-recurrence)
  - [Minor](#minor)
    - [R12-m1 — "recurrence at object sorts" in the sub-theory description](#r12-m1--recurrence-at-object-sorts-in-the-sub-theory-description)
    - [R12-m2 — the orientation's W-type sentence now over-covers `TieredFn`](#r12-m2--the-orientations-w-type-sentence-now-over-covers-tieredfn)
    - [R12-m3 — phase 2 lists `omegaShift` without the open-question-3 condition](#r12-m3--phase-2-lists-omegashift-without-the-open-question-3-condition)
  - [Nits](#nits)
- [Checks that passed](#checks-that-passed)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Scope of this round, per the review brief: only the rescope commit
`3498ff5a` (first-order cells changed from separate implementations
to restricted sub-theories of the single higher-order presentation;
DLMZ rescoped to notation; the standalone tier-sorted instantiation
and its tier-to-r-type functor deferred). Edited regions verified:
sections 1.1, 2.3, 4.1, 4.2, 4.3, 5.2, 7, 8 (phases 2-4), 9. The
straggler sweep additionally covered sections 2.1 (orientation),
2.2, 3.3, 6.1-6.4, and 10. Material converged in rounds 1-11 was
not re-reviewed.

Sources consulted: Leivant III at
`/home/terence/wingeb/ramified-recurrence-computational-complexity-iii-higher-type-elementary.pdf`,
pp. 213-218 (eq. (4) and eq. (5) with its flat-recurrence note,
p. 215; section 2.4(1) coercions and 2.4(3) first-order sentence,
p. 216; section 2.5 destructors and case, p. 217; section 2.7
collapse and raising, p. 218); the round-6 review (R6-B1, R6-M1)
and the round-7 resolution record; the reviewed document in full.

## Verification status

| Check (from the review brief) | Result |
| --- | --- |
| 1a. "hom-sets are all of the collapse" for tower-sort contexts | Fail (R12-B1) |
| 1b. Sub-theory description faithful to 2.4(3), p. 216 | Pass, wording note (R12-m1) |
| 2. Rescope internal consistency; straggler sweep | Pass except R12-m2, nits |
| 3. `omegaShift` bullet restated for the tower fragment | Fail (R12-M1) |
| 4a. `markdownlint-cli2` on the document | Pass (0 errors) |
| 4b. `doctoc --dryrun --update-only` | Pass ("Everything is OK") |
| 4c. Style rules on the new text | Pass with nit R12-n4 |

## Findings

### Blocker

#### R12-B1 — 4.1's tower-context hom-set claim contradicts 6.1

Location: section 4.1, the implementation paragraph after the
instances table: "The distinction matters: the full subcategory of
the higher-order syntactic category on tower-sort contexts is not
the first-order system - its hom-sets are all of the collapse
(section 6.1) - so the restriction is on the signature, not on the
objects."

Defect: the middle clause is false, and the section it cites says
the opposite. Section 6.1 states that "exponentiation has no
realizer over any tower-sort context" (with the supporting chain:
the 2.4(1) coercions run downward only, and tower-sorted inputs
drive object-type recurrence alone). Exponentiation is in the
collapse (Leivant III section 2.4(3): its realizer takes input at
`Omega(o -> o)`, a non-tower object sort; Theorem 14 identifies
the collapse with the elementary functions). Hence the hom-sets of
the full subcategory on tower-sort contexts are strictly smaller
than the collapse. This is also exactly what round 6 established:
R6-B1's third bullet ("Tower-context hom-sets exclude
exponentiation ... the dependence on the inputs is bounded-depth
case analysis and the higher-type internals contribute constants
only") is the finding that forced 6.1's current object-sort
quantification. The new sentence re-asserts, for the same
subcategory, the claim whose negation resolved R6-B1.

Adjudication of what the tower-context hom-sets are. Between
tower-sort contexts the hom-sets contain the first-order-definable
functions (every sub-theory term is a term of the host theory) and
exclude exponentiation (above). Whether they exceed the
first-order-definable functions extensionally is a conservativity
question the source does not address: fullness admits morphisms
formed by higher-order schemas with tower endpoints — eq. (4)
leaves the parameter types `sigma_vec` unconstrained, so a
recurrence at a tower sort may take arrow-sorted parameters fed by
closed higher-order terms — and no statement of the paper
identifies those with first-order derivations. So neither "all of
the collapse" nor "exactly the first-order system" is assertable
on transcription terms; the correct grounds for the sentence's
conclusion are definitional and policy-level, not extensional.

The conclusion itself — the restriction is on the signature, not
on the objects — is correct and survives on two grounds: (i) the
source states first-order as a restriction on the schema
("recurrence restricted to object types of the form `Omega^m o`",
section 2.4(3), p. 216), which a signature restriction renders and
an object restriction does not; (ii) identifying the full
subcategory on tower-sort contexts with the first-order system
would require a conservativity argument absent from the source — a
novel proof route, which section 1.2 forbids relying on.

Suggested replacement wording:

> The distinction matters: the full subcategory of the higher-order
> syntactic category on tower-sort contexts is not the first-order
> system. Fullness admits every higher-order-formed morphism with
> tower-sorted endpoints (a recurrence at a tower sort takes
> parameters of arbitrary r-types, eq. (4), and closed higher-order
> terms occur internally), and the source defines first-order by
> restricting the schema — "recurrence restricted to object types
> of the form `Omega^m o`" (section 2.4(3), p. 216) — not by
> restricting the endpoints; no conservativity statement in the
> paper identifies the two. (Those hom-sets are in any case
> strictly smaller than the collapse: exponentiation has no
> realizer over any tower-sort context, section 6.1.) The
> restriction is therefore on the signature, not on the objects.

If the drafted clause instead intended containment ("the hom-sets
consist of collapse functions"), the sentence still fails: that
containment holds for every subcategory and does not distinguish
the full subcategory from the first-order system, and the
cross-reference to 6.1 still points at the opposite claim. A
rewrite is needed under either reading. The rescope's design
decision is unaffected.

### Major

#### R12-M1 — the tower-fragment `omegaShift` claim fails on flat recurrence

Location: section 4.3, "`omegaShift` as an endofunctor: on the
tower sorts the shift is a signature endomorphism"; consequentially
the copoint bullets (4.3 "the copoint on the tower-sort fragment";
4.2 "supplying a copoint for the shift on the first-order systems
only"; section 9 "copoint on first-order systems"), which
presuppose the endofunctor.

Defect: the withdrawn claim this restates ("unconditional for the
first-order systems") was about the standalone `S = N` systems in
the DLMZ presentation, where the conditional/destructor layer is
untiered and the tier successor maps every operation to an
operation. The tower fragment of the r-type system differs exactly
there. Flat recurrence — part of `RMRec-omega` (eq. (5); the
document's section 2.1 table row "the system formalized here") and
of the first-order sub-theories (its arities are tower-sorted) —
pins its recurrence argument and subterms at sort `o`:
`f : sigma_vec, o -> tau`, `g_ci : sigma_vec, o^{r_i} -> tau`,
with the paper's explicit note "(Note that we do not stipulate
flat recurrence for recurrence arguments of `Omega`-type.)"
(p. 215); likewise the Lemma 1 replacements, destructors of type
`o -> o` and `case^theta : o, theta^k -> theta` (section 2.5,
p. 217), have their scrutinee pinned at `o`. The sort shift
`Omega^m o -> Omega^{m+1} o` maps these operations to operations
with scrutinee `Omega o` that are not schema instances, so the
shift is not a signature endomorphism of the sub-theory as
defined.

Nor does a derived repair evidently exist for the destructor
summand: a denotation-preserving image of `dstr_j : [o] -> [o]`
would be the destructor at `[Omega o] -> [Omega o]`, and no
realizer is apparent — from an input at `Omega o`, sort `Omega o`
is reached only through constructors, `case` branches (scrutinee
lowered by `delta`), and `x`-independent internals (coercions run
downward, 2.4(1); recurrence driven by the input outputs one sort
down, eq. (4); no raising coercion exists, the document's own
section 4.2) — so every morphism `[Omega o] -> [Omega o]` denotes
a function that piecewise either pads its argument with
constructors or is constant, and the destructor is neither. (The
shifted `case` is derivable, via `delta` on the scrutinee; the
shifted destructor is the obstruction.) At minimum the claim as
written asserts an unestablished property; on the argument above
it is false for any sub-theory containing flat-recurrence or
destructor identifiers.

Suggested fix: restrict the claim to the summand where it holds —
constructors (present at every object sort) and eq. (4) monotonic
recurrences (whose types shift within the tower sorts) — and
condition the sub-theory endofunctor on the treatment of the
flat/destructor summand, either alongside the higher-order case
under open question 3 or as its own recorded question; adjust the
three copoint mentions to carry the same condition.

### Minor

#### R12-m1 — "recurrence at object sorts" in the sub-theory description

Location: section 4.1, "identifier formation restricted to
first-order arities over the tower sorts `Omega^m o` and
recurrence at object sorts".

In this document "object sorts" includes `Omega(eta -> eta)` (the
glossary's `tau` row; section 6.1) — the very sorts the
surrounding sentence is distinguishing the sub-theory from. Within
the restricted arities the recurrence types are forced to tower
sorts, so the phrase is not wrong, but it re-imports the ambiguity
the sentence resolves. Use 2.4(3)'s own form: "recurrence at
object sorts of the form `Omega^m o`" (or "at the tower sorts").
With that note, sub-check 1b passes: the paper's primary
formulation ("ramified recurrence in first-order types")
restricted to the tower object types is licensed by 2.4(3)'s "is
the same as recurrence restricted to object types of the form
`Omega^m o`", and rendering that restriction at identifier
formation is the signature-level reading the rescope requires.

#### R12-m2 — the orientation's W-type sentence now over-covers `TieredFn`

Location: section 2.1, orientation intro: "The Lean code below is
illustrative and verified to compile; in the implementation the
corresponding inductives are realized as W-types of polynomial
functors ..., per sections 4 and 7."

After the rescope, `TieredFn` — part of "the Lean code below" —
has no implementation counterpart: the standalone tier-sorted
instantiation is deferred (sections 4.1, 9), and the first-order
sub-theories are restricted signatures, not tier-indexed
inductives. Scope the sentence to the signature/free-algebra/
recurrence illustrations, or exempt the tier illustration
explicitly (it is notation per section 2.3's adoption bullet). The
illustration framing itself ("First-order illustration ... with
tiers as natural numbers") survives the rescope and needs no
change.

#### R12-m3 — phase 2 lists `omegaShift` without the open-question-3 condition

Location: section 8, phase 2: "Higher-order system over `1 + X`
...: category, `omegaShift`, `kappaHat`; ...".

Before the rescope, `omegaShift` sat in phase 2's monadic
first-order system, where the endofunctor claim was then held
unconditional. The restructuring moved it into the higher-order
phase, where section 4.3 and open question 3 make the endofunctor
contingent on base-substitution functoriality, but the phase line
carries no condition. Qualify the deliverable (e.g., "`omegaShift`
at the sort level; endofunctor status per open question 3"), and
propagate whatever resolution R12-M1 receives.

### Nits

- R12-n1: terminology drift. Section 4.2 ("on the first-order
  systems only") and section 9 ("copoint on first-order systems")
  retain the pre-rescope referent "first-order systems"; sections
  4.3 and 8 say "first-order sub-theories" / "tower-sort
  fragment". No standalone first-order systems remain in scope;
  align the two older lines.
- R12-n2: section 2.2 says the provenance "is recorded for the
  structures' docstrings"; per revised 1.1 the cells receive
  "sub-theory definitions", not structures.
- R12-n3: section 7 spikes "the monadic first-order sub-theory"
  through approaches A and B to choose the representation that
  phase 1 commits to, while phase 4 names that sub-theory a
  deliverable ("doubles as the section-7 spike vehicle"). The
  spike must precede phase 1; a clause noting that the spike is a
  throwaway prototype of the phase-4 artifact would remove the
  apparent cycle. (Mitigated by "phase boundaries fixed by the
  plan, not here".)
- R12-n4: style, new text only: "near-free by genericity" (5.2)
  and "near-trivial inclusion" (phase 4) are informal cost
  shorthands; "The distinction matters" (4.1) is a rhetorical
  lead-in. Borderline against the avoid-colloquialisms rule;
  flagged without a required change.

## Checks that passed

- Section 1.1: both edited bullets consistent with 4.1, 4.3, 8,
  and 9 (single presentation, three instantiations; sub-theory
  definitions and inclusion functors only for the deferred cells).
- Section 2.3 DLMZ adoption bullet consistent with 4.1's
  notation-only scoping (`i < j` in prose and docstrings, the
  orientation illustration) and with section 9's deferral of the
  standalone tier-sorted instantiation and its citation-fit
  decision.
- Instances table: the sorts column is gone and no passage
  references it; the glossary `tau` row's "the first-order tiers
  `m : N` are the tower `Omega^m o`" reads as the notation
  dictionary the rescope intends.
- "One copy per object sort" in the algebra-axis paragraph is
  unambiguous post-rescope (the single system's object sorts) and
  matches the paper's section 2.3 (a constant `c_i^theta` for each
  object type `theta`).
- Straggler sweep: "DLMZ tier presentation" absent; "tiers
  `m : N`" only in the glossary; the tier-to-r-type functor
  appears only as deferred (4.3, 9); sections 3.3, 6.1-6.4, and 10
  contain no residual promise of first-order implementations
  (open question 5's generic "theory-inclusion functors" still
  reads correctly for the sub-theory inclusions).
- Section 5.2's revised recommendation and section 7's revised
  spike sentence carry the rescope correctly (modulo R12-n3,
  R12-n4).
- Gates: `markdownlint-cli2` reports 0 errors on the reviewed
  document; `doctoc --dryrun --update-only` reports "Everything is
  OK".

## Convergence verdict

Not converged for this scoped round: one blocker (R12-B1) and one
major (R12-M1), both confined to sentences introduced by the
rescope commit. The rescope's design decision itself — one
higher-order presentation, generic in the signature functor, with
the first-order cells as restricted sub-theories, DLMZ as
notation, and the standalone tier-sorted instantiation deferred —
is sound, and is in fact better grounded (2.4(3)'s schema-level
restriction plus the section 1.2 policy argument) than the drafted
justification. Both findings are local rewrites; no structural
change to the rescope is required.
