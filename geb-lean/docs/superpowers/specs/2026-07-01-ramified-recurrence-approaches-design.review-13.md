# Adversarial review 13 — ramified-recurrence survey (fix verification)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Verification status](#verification-status)
- [Part 1 — resolution of round-12 findings](#part-1--resolution-of-round-12-findings)
  - [R12-B1 (blocker) — resolved](#r12-b1-blocker--resolved)
  - [R12-M1 (major) — resolved](#r12-m1-major--resolved)
  - [R12 minors — resolved](#r12-minors--resolved)
  - [R12 nits — resolved](#r12-nits--resolved)
- [Part 2 — the two additions](#part-2--the-two-additions)
  - [The `LawvereGodelT*` audit gate (3.3, 6.3, open question 1)](#the-lawveregodelt-audit-gate-33-63-open-question-1)
  - [The tree-algebra corollary route (section 9; 5.2 pointer)](#the-tree-algebra-corollary-route-section-9-52-pointer)
- [New findings](#new-findings)
  - [Minor](#minor)
    - [R13-m1 — "untested" is contradicted by an existing test file](#r13-m1--untested-is-contradicted-by-an-existing-test-file)
  - [Nits](#nits)
- [Checks that passed](#checks-that-passed)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Scope of this round, per the review brief: verification of the
round-12 fixes (commit `36302b37`; 1 blocker, 1 major, 3 minors,
4 nits) against the current text, plus a review on their own terms
of the two user-directed additions in the same commit — the
`LawvereGodelT*` audit gate (sections 3.3, 6.3, open question 1)
and the tree-algebra corollary route (section 9, with the section
5.2 pointer). Material converged in rounds 1-12 was not
re-reviewed.

Sources consulted: Leivant III at
`/home/terence/wingeb/ramified-recurrence-computational-complexity-iii-higher-type-elementary.pdf`,
pp. 215-221 (eq. (4), eq. (5) and its flat-recurrence note,
p. 215; sections 2.4(1)-(6), pp. 216-217; section 2.5 destructors
and case, p. 217; Lemma 2's proof with the `choose` device,
p. 218; section 3.1 register machines and Lemma 5 with footnote 8
and the post-lemma equivalence sentence, p. 220; Lemma 6's
statement and proof, p. 221); the round-12 review file; the
round-6 resolution record as summarized there;
`GebLean/LawvereGodelT*.lean` filenames and
`GebLeanTests/LawvereGodelTTerm.lean` (read in full); the
reviewed document in full.

## Verification status

| Check (from the review brief) | Result |
| --- | --- |
| 1. R12-B1 fix (4.1 justification) | Resolved |
| 2. R12-M1 fix (`omegaShift`, copoints, open question 3) | Resolved |
| 3. R12-m1, m2, m3 | Resolved |
| 4. R12-n1, n2, n3, n4 | Resolved |
| 5. Audit gate internal consistency (3.3, 6.3, question 1) | Pass, with R13-m1 on one factual clause |
| 6. Tree-corollary claims against Leivant III | Pass (details below) |
| 7. Style and cross-section consistency of the additions | Pass, with nits |
| 8a. `markdownlint-cli2` on the document | Pass (0 errors) |
| 8b. `doctoc --dryrun --update-only` | Pass ("Everything is OK") |

## Part 1 — resolution of round-12 findings

### R12-B1 (blocker) — resolved

Section 4.1 now reads: "The full subcategory of the higher-order
syntactic category on tower-sort contexts is not the first-order
system: fullness admits every higher-order-formed morphism with
tower-sorted endpoints (a recurrence at a tower sort takes
parameters of arbitrary r-types, eq. (4), and closed higher-order
terms occur internally), and the source defines first-order by
restricting the schema - 'recurrence restricted to object types
of the form `Omega^m o`' (section 2.4(3), p. 216) - not by
restricting the endpoints; no conservativity statement in the
paper identifies the two. (Those hom-sets are in any case
strictly smaller than the collapse: exponentiation has no
realizer over any tower-sort context, section 6.1.) The
restriction is therefore on the signature, not on the objects."

This is the round-12 suggested wording, adopted nearly verbatim.
Checks: the 2.4(3) quotation matches the source, p. 216 ("which
in the present context is the same as recurrence restricted to
object types of the form `Omega^m o`"); the parenthetical's
clause matches section 6.1's own sentence ("exponentiation has no
realizer over any tower-sort context") word for word, so the
cross-reference now points at a claim 6.1 makes rather than
contradicts; "strictly smaller than the collapse" is the
direction round 6's R6-B1 established (tower-context hom-sets
exclude exponentiation, which is in the collapse). No passage
asserting the hom-sets are "all of the collapse" remains.
Resolved.

### R12-M1 (major) — resolved

Section 4.3's `omegaShift` bullet now reads: "the sort shift maps
the constructor summand (present at every object sort) and
eq. (4) monotonic recurrences to schema instances, but not the
flat-recurrence and destructor summand, whose scrutinee is pinned
at sort `o` (eq. (5) and the p. 215 note; destructors are
`o -> o`, section 2.5) - the shifted destructor at `[Omega o]`
has no evident realizer. Endofunctor status, for the sub-theories
as for the full system, is open question 3."

Source checks: eq. (5) types flat recurrence at
`f : sigma_vec, o -> tau` with the note "(Note that we do not
stipulate flat recurrence for recurrence arguments of
Omega-type.)" (p. 215); section 2.5 gives destructors "of type
`o -> o`" and `case^theta : o, theta^k -> theta` (p. 217). All
four cited elements are present and correct, and "no evident
realizer" is the appropriately hedged form of the round-12
argument.

The three copoint mentions carry the condition:

- 4.2: "supplying copoint components at the Omega-sorts ...;
  their assembly into a copoint depends on open question 3."
- 4.3: "`kappaHat` at every r-type; whether its components
  assemble into a copoint of a shift endofunctor depends on open
  question 3."
- 9: "The Omega-shift structure analysis (the copoint question of
  open question 3; ...)".

Open question 3 is restated to cover both cases: "For the full
higher-order system: base-substitution functoriality
(interpretation compatibility). For the first-order sub-theories:
the flat-recurrence and destructor summand blocks the sort shift
from being a signature endomorphism ...; so no fragment's
endofunctor is currently established; the copoint statements of
sections 4.2 and 4.3 are conditioned on this question." Phase 2
carries the condition (see R12-m3 below). Resolved.

### R12 minors — resolved

- R12-m1: section 4.1 now reads "recurrence at object sorts of
  the form `Omega^m o`" — 2.4(3)'s own form, as suggested.
- R12-m2: the orientation sentence is scoped: "The signature,
  free-algebra, and recurrence code corresponds to implementation
  inductives realized as W-types of polynomial functors ...; the
  tier illustration further below is notation only (sections 2.3
  and 4.1)." `TieredFn` is exempted exactly as suggested.
- R12-m3: phase 2 now reads "category; `omegaShift` at the sort
  level (endofunctor status per open question 3); `kappaHat`;
  ...", carrying the R12-M1 resolution.

### R12 nits — resolved

- R12-n1: 4.2 no longer says "on the first-order systems only"
  (now "copoint components at the Omega-sorts"); section 9 no
  longer says "copoint on first-order systems" (now "the copoint
  question of open question 3"). The remaining occurrences of
  "first-order systems" (sections 1.1 and 4.1) name the systems
  as objects of study, which is correct usage.
- R12-n2: section 2.2 now reads "the provenance is recorded for
  the sub-theory definitions' docstrings".
- R12-n3: section 7 now reads "the spikes are throwaway
  prototypes of the phase-4 artifact, run before phase 1 commits
  to a representation", removing the apparent cycle.
- R12-n4: "near-free by genericity" is now "a small step, since
  the presentation is generic in the functor" (5.2);
  "near-trivial inclusion" is now "with its inclusion into the
  host theory" (phase 4); "The distinction matters" is deleted
  (4.1 now opens the sentence with "The full subcategory ...").

## Part 2 — the two additions

### The `LawvereGodelT*` audit gate (3.3, 6.3, open question 1)

Internal consistency across the three sites: consistent. Section
3.3 closes its `LawvereGodelT*` bullet with "its fidelity to the
source is unestablished; it is treated as unverified until the
audit of section 6.3", deferring to 6.3. Section 6.3 states both
preconditions explicitly: "Two preconditions gate the reuse.
First, under the transcription-only policy the substitution is
admissible only if the bridge itself is literature. Second, the
`LawvereGodelT*` formalization is untested and little is proven
about it, so before any reliance it must be audited clause by
clause against Beckmann-Weiermann 2000 (their Definition 4
reduction relation, the Definitions 7-10 measures, and the
Lemma 16 statement and proof structure); until that audit it is
treated as not established to represent its source. Failing
either precondition, route 1-3 stands." — literature bridge AND
clause-by-clause audit, with the fallback (route 1-3 is the
Leivant III sections 4-5 transcription of the same section).
Open question 1 restates the same conjunction: "Reuse of
`LawvereGodelT*` requires both an affirmative answer and the
section-6.3 audit of that formalization against the source;
failing either, the Leivant III sections 4-5 transcription
stands." The three sites agree on the gate's content, its
location (6.3), and its fallback.

Overclaim check: the gate does not overclaim. It states what the
audit covers (definitional clauses, measures, the Lemma 16
statement and proof structure — matching 3.3's inventory of what
the formalization contains) and states only that, absent the
audit, the formalization "is treated as not established to
represent its source". It does not claim the audit would supply
the bridge (open question 1's literature question remains
separate) or the missing connection to `LawvereERCat` (3.3 still
records "no connection to `LawvereERCat` is proven yet"). The
Beckmann-Weiermann clause numbering (Definition 4, Definitions
7-10, Lemma 16) is taken from the formalization's
self-description in 3.3; verifying that numbering against the
paper is itself part of the audit the text mandates, so no
circularity arises from not verifying it here.

One factual clause is inaccurate: see R13-m1 below ("untested,
and little is proven about it").

### The tree-algebra corollary route (section 9; 5.2 pointer)

(a) Lemma 5 use. The source (p. 220) states: "Register machines
over a tree algebra are exponential-time reducible to Turing
machines computing over natural coding of algebra elements", with
footnote 8 ("Exponential time is essential here, because a
register machine over binary trees can build in linear time a
full binary tree with 2^n nodes from a (skewed) tree with n
nodes") and the post-lemma sentence "computational complexity for
register machines over A and for Turing machines are ...
exponential time equivalent for tree algebras". The bullet's
claims — "Lemma 5 supplies the machine-model robustness of that
definition; the exponential factor it records for tree algebras
is absorbed by elementary" — are fair use: the coded reference
class is machine-model robust exactly because the model change
costs at most an exponential, and the elementary class is closed
under composition with exponentials (one more level in a
fixed-height tower). Verified.

(b) The alpha/beta devices. Section 2.4(5) (p. 216): "Since A is
assumed infinite, it has some 0-ary constructor alpha and some
constructor beta of arity > 0. If arity(beta) > 1 then write
beta(a) for beta(a, alpha ... alpha). The numeric functions exp
and 2_m defined above can be simulated over A using alpha and
beta in place of 0 and s" — exactly the "unary sub-algebra
generated by a 0-ary and a positive-arity constructor" of the
bullet. Lemma 6's proof (p. 221) opens "Let alpha and beta be
constructors of A, as in Example 2.4(5)" and uses beta iterates
as the step-count recurrence argument (`stt(a, beta^[n] alpha)`
and `[phi](a, beta^[n] alpha)` give the state and register values
after `n` steps), with the clock `c * 2_q(sz(a))` built from the
2.4(4)/2.4(6) functions that rest on 2.4(5); machine states are
coded by distinct elements `b_1 ... b_l` chosen in A (via
Lemma 2's `choose`, p. 218). The bullet claims only that 2.4(5)
and Lemma 6's proof "already use" the alpha/beta devices — true
on both counts — and does not claim the paper already holds
register contents in the unary sub-algebra (that deployment is
part of the assembly it marks as new). Verified as phrased.

(c) Honesty about the assembly. The bullet closes: "The paper
does not spell out that assembly (in particular the ramified
definability of the encoding and decoding); the future workstream
designs it and marks it under the section 1.2 policy." This is
accurate and correctly placed: Lemma 6 simulates register
machines over A, not the zero-test URM over the tree algebra's
unary sub-algebra, and the paper contains no
encoding/decoding-between-algebras development. The "in
particular" keeps the marked scope non-exhaustive, which also
covers the other new glue the route needs (the extension of
section 1.2's URM-to-Leivant-machine embedding from the unary
algebra to the unary sub-algebra of an arbitrary algebra, and the
soundness-side coding at the 6.4 landing). Verified.

(d) Consistency with 1.2 and 6.2. Section 1.2's embedding
statement remains scoped to the unary algebra and is not
contradicted; the bullet's route reuses the `ZeroTestURM`-facing
work rather than introducing a new machine family, consistent
with 5.2's observation that register machines over the tree
algebra "do not yet exist in the repository or CSLib" and with
"No new register-machine family is planned for it". "The
soundness route of section 6.3 is algebra-generic" is correct for
the route's steps 1-3 (Leivant III sections 4-5 are developed
over an arbitrary infinite free algebra); the per-algebra glue
sits in the marked assembly per (c). The 5.2 pointer ("as a
future corollary, with the coding-based route sketched in
section 9") matches. One wording defect in the parenthetical
"(from `compileER`, built once in this workstream)" — see
R13-n1.

Both additions sit in the correct scope tiers (the audit gate
inside the already-conditional 6.3 reuse candidate; the corollary
route under section 9 deferred/future work), so neither
contradicts 1.1's single-theorem scope.

## New findings

### Minor

#### R13-m1 — "untested" is contradicted by an existing test file

Location: section 3.3 ("The formalization is untested, and little
is proven about it, so its fidelity to the source is
unestablished") and section 6.3 ("the `LawvereGodelT*`
formalization is untested and little is proven about it").

Defect: `GebLeanTests/LawvereGodelTTerm.lean` exists and runs
under `lake test` (per the repository's test layout): it `#guard`s
numeral interpretation, exhibits a `K`-redex reduction, and
applies `GodelTTerm.Reduces.interp_invariance` to a closed
instance. So "untested" is factually false as committed text.
"Little is proven about it" is likewise in tension with the same
3.3 bullet, which lists the reduction relation "with
interpretation invariance" and "the structural tower bound of
their Lemma 16 ... with the majorization apparatus" as formalized
content — internal theorems are proven; what is missing is
anything establishing fidelity to the source or a connection to
the rest of the repository.

The audit gate itself is unaffected — the existing tests exercise
the term layer and one reduction case only (nothing touches the
Definitions 7-10 measures or the Lemma 16 apparatus), which
establishes nothing about source fidelity — but the factual
ground should be stated accurately. Suggested rewording, both
sites: "the formalization is only lightly tested (a numeral and
one reduction case) and nothing proven about it bears on its
fidelity to the source" or equivalent.

### Nits

- R13-n1: section 9, "the conjugate's `ZeroTestURM` program (from
  `compileER`, built once in this workstream)". The appositive's
  antecedent is ambiguous, and under the nearest reading — that
  `compileER` is built in this workstream — it contradicts 3.3
  and 6.2, which record `compileER` and its correctness and bound
  theorems as already formalized, pre-existing assets. The
  intended referent is presumably the workstream's
  `ZeroTestURM`-facing definability machinery (the phase-5
  Lemma 6 transcription), which the future corollary would reuse.
  Suggested: "(obtained from the pre-existing `compileER`; the
  URM-facing simulation machinery is built once in this
  workstream's phase 5)".
- R13-n2: the two audit-gate sites describe the pre-audit status
  in different words — "treated as unverified" (3.3) versus
  "treated as not established to represent its source" (6.3).
  Same content; aligning the phrasing would remove a place for
  readings to diverge. No change required.

## Checks that passed

- All nine round-12 findings verified resolved against the
  current text (Part 1), with the source citations in the new
  4.3/open-question-3 text (eq. (5), p. 215 note, section 2.5,
  section 2.4(3) p. 216) each re-verified against the PDF.
- The audit gate is internally consistent across 3.3, 6.3, and
  open question 1; both preconditions and the fallback are stated
  in 6.3; no overclaim about what the audit establishes.
- The tree-corollary bullet's mathematical claims verified
  against Leivant III pp. 216-221 (Lemma 5 and footnote 8;
  section 2.4(5); Lemma 6's proof including the beta-iterate
  clock and the `b_1 ... b_l` state codes); the
  novelty-marking sentence is accurate; no contradiction with
  sections 1.1, 1.2, 5.2, 6.2, 6.3.
- Style on the new text: no value-laden adjectives, no
  colloquialisms beyond the round-12-suggested "throwaway
  prototypes" (accepted there); "spell out" is standard technical
  usage; no emphasis markup.
- Gates: `markdownlint-cli2` reports 0 errors on the reviewed
  document; `doctoc --dryrun --update-only` reports "Everything
  is OK".

## Convergence verdict

Converged for this round's scope, modulo one minor: all round-12
findings (1 blocker, 1 major, 3 minors, 4 nits) are resolved, and
the two additions are internally consistent, source-accurate on
every checked claim, and correctly scoped and novelty-marked. No
blocker and no major. Remaining: R13-m1 (the "untested" clause in
3.3 and 6.3 is contradicted by `GebLeanTests/LawvereGodelTTerm.lean`
and should be reworded to the accurate ground — thin coverage
that establishes nothing about source fidelity) and two nits. A
fix for R13-m1 is a two-sentence local rewording; no further
review round is needed for it beyond spot-checking the new
sentences.
