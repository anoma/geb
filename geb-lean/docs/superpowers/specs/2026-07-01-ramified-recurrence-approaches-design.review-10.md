# Adversarial review 10 — ramified-recurrence survey (r-type rows)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verification status](#verification-status)
  - [1. The `tau` row against the paper's section 2.3](#1-the-tau-row-against-the-papers-section-23)
  - [2. The `Omega tau` row against pp. 214-216 and section 2.7](#2-the-omega-tau-row-against-pp-214-216-and-section-27)
  - [3. Consistency with the document's later uses of `Omega`](#3-consistency-with-the-documents-later-uses-of-omega)
- [Findings](#findings)
  - [Major](#major)
    - [R10-M1 — "output type" for "critical arguments of type"](#r10-m1--output-type-for-critical-arguments-of-type)
  - [Minor](#minor)
    - [R10-m1 — the paper's expansion of "r-type" is "ramified functional types"](#r10-m1--the-papers-expansion-of-r-type-is-ramified-functional-types)
  - [Observations (no change requested)](#observations-no-change-requested)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Scope of this round, per the review brief: the two rows appended to
the terminology glossary in section 2.1's orientation (the `tau` and
`Omega tau` rows), the reworded glossary intro sentence announcing
them, and the "(last two rows)" pointer added to the
recurrence-argument row. Content converged in rounds 1-9 was not
re-reviewed except where the new rows cite it.

Sources consulted this round: Leivant III, journal pp. 214-216 and
218 (PDF pages 6-8 and 10, read as page images), against the
document at lines 228-243 and the cross-referenced passages at
lines 282-323, 686-729, 820-828, and 904-945.

## Verification status

| Check | Result |
| --- | --- |
| 1a. r-type generation: base `o`, binary `->`, unary `Omega` | Pass — verbatim against the section 2.3 definition, p. 214 |
| 1b. Object/functional split: `o` and every `Omega tau` object; rest functional | Pass — verbatim |
| 1c. Cross-references: `RType` in the document's section 4.1; first-order tiers as `Omega^m o` (the paper's section 2.4(3), p. 216) | Pass |
| 2a. Paraphrase of the p. 214 sentence introducing `Omega` | Fail — R10-M1 |
| 2b. Copy-of-carrier use ("a number, not a function"); the p. 214 "Note that, extensionally, ..." sentence | Pass — the Note supports, and does not qualify, the reading; exact sentence reported below |
| 2c. Iterate example and section 2.4(3) exponentiation | Pass |
| 3. Consistency with the document's later uses of `Omega` | Pass — no contradiction introduced by the new rows; section 6.1's flat-recurrence sentence is the internal witness for R10-M1 |
| 4. Gates: markdownlint, doctoc, style | Pass — one naming-fidelity finding (R10-m1) |

### 1. The `tau` row against the paper's section 2.3

The paper's definition sentence (p. 214, opening the definition
"(Ramified recurrence, RRec^omega(A))"):

> The *ramified functional types* (*r-types* for short) are
> generated from the base type o by the binary type operation ->
> and the unary Omega. The *object types* are o and the
> Omega-types, i.e. those of the form Omega tau; the remaining
> types are *functional*. Note that every r-type tau is of the
> form sigma-vec -> theta, for some object type theta.

- (1a) The row's "the grammar generated from the single base type
  `o` by the binary arrow `sigma -> tau` and the unary constructor
  `Omega`" matches the first sentence exactly (the paper says
  "binary type operation"; "binary arrow" is a faithful rendering).
- (1b) The row's "The object types are `o` and every `Omega tau`;
  all other r-types are functional" matches the second sentence
  exactly ("the remaining types are functional" / "all other
  r-types are functional").
- (1c) Cross-references. `RType` appears in the document's
  section 4.1 (the canonical-instances table, "Sorts" column:
  "`RType` (`o`, `arrow`, `omega`)", line 717), and section 4.1
  states "For the higher-order system the sorts are Leivant III's
  r-types" (line 723) — the row's "the sorts are exactly the
  r-types (`RType`, section 4.1)" is accurate. The first-order-tier
  claim matches the paper's section 2.4(3), p. 216: "defined by
  ramified recurrence in first-order types, which in the present
  context is the same as recurrence restricted to object types of
  the form Omega^m o"; the document's section 4.1 table reads the
  first-order tiers the same way ("tiers `m : N` (read
  `Omega^m o`)", line 715).

The row's second-column entry is the subject of R10-m1.

### 2. The `Omega tau` row against pp. 214-216 and section 2.7

(2a) The paper's sentence introducing `Omega` (p. 214):

> We introduce a type-constructor, Omega, where Omega tau is
> intended as the type of those base objects that support
> recurrence with critical arguments of type tau.

The row paraphrases this as "the type of base-algebra elements
permitted to serve as the recurrence argument of a recurrence whose
output type is `tau`". The substitution of "output type `tau`" for
the paper's "critical arguments of type tau" is adjudicated in
R10-M1: within the schema of eq. (4) the two coincide, but the
paper's wording was chosen to exclude flat recurrence (eq. (5)),
for which the substitution fails.

(2b) The p. 214 sentence immediately following, read exactly from
the page image:

> Note that, extensionally, A^{Omega tau} = A^{o}, but copies of a
> in A^{Omega tau} have different computational behavior with
> respect to the sorted structure.

(A rendered blackboard-bold.) The sentence relates
A^{Omega tau} to A^{o} — the base type's universe — not to
A^{tau}. It is therefore in agreement with, and is itself direct
p. 214 evidence for, the copy-of-carrier reading the row draws
from section 2.7; no qualification of the row is needed. The
section 2.7 claim itself re-verifies on p. 218:

> Recall that the functionals defined in RRec^omega(A) are not
> over A, but over a sorted algebra whose sorts are the object
> types, and where the universe of sort theta is a copy A^theta
> of A.

Since `Omega (o -> o)` is an object type, its universe is a copy of
the carrier; over the unary naturals its elements are numbers. The
row's conclusion "an element of `Omega (o -> o)` is a number, not a
function" is correct, and the "different computational behavior
with respect to the sorted structure" clause is what the row
renders as "purely the typing license".

(2c) The iterate example, p. 214 (continuing the Note sentence):

> For instance, the nth iterate of f : N^{o} -> N^{o} is defined
> if n in N^{Omega(o -> o)}, but not if n in N^{o}; and if
> f : N^{Omega(o -> o)} -> N^{o} then no non-trivial iterate of f
> is well-defined.

The row's "iteration of an `o -> o` function requires its count at
`Omega (o -> o)`" matches. The section 2.4(3) exponentiation
construction (p. 216) confirms the same pattern in use: `dbl :
(o -> o) -> (o -> o)`, and "define by recurrence in o -> o a
function e : Omega(o -> o) -> (o -> o): e(0) = s^{o}, e(sn) =
dbl(e(n))", with e(n)(x) = 2^n + x — the iteration count of the
`o -> o` function `dbl` enters at `Omega(o -> o)`. Both citations
in the row are accurate.

The schema types the row and the intro sentence rely on
re-verified against eq. (4), p. 215:

> f(x-vec)(c_i(a-vec)) = g_{c_i}(x-vec)(a-vec)(f(x-vec)((a-vec))),
> where f : sigma-vec, Omega tau -> tau,
> g_{c_i} : sigma-vec, (Omega tau)^{r_i}, tau^{r_i} -> tau,
> i = 1, ..., k.

This matches the document's rendering at lines 320-321 exactly.

### 3. Consistency with the document's later uses of `Omega`

- The ramified paragraph at the end of the orientation
  (lines 282-323): fixes the recurrence argument at `Omega tau`
  against output `tau` per eq. (4) — consistent with both new
  rows.
- The "(last two rows)" pointer in the recurrence-argument row
  (line 238) points correctly: the `tau` and `Omega tau` rows are
  the last two rows of the table.
- The reworded intro sentence (lines 228-233): the table has seven
  rows; the first five are eq. (1)'s pieces; the last two define
  `tau` and `Omega tau`; the second row does mention `Omega tau`;
  the ramified paragraph does use both. Eq. (4) is in the paper's
  section 2.3. All accurate.
- Section 4.1 (lines 707-729) and section 4.2's ramified-structure
  sketch (lines 820-828): `RType`, the tower reading of first-order
  tiers, and `kappaHat (τ) : [RType.omega τ] ⟶ [τ]` (the paper's
  kappa-hat_tau : Omega tau -> tau, section 2.4(1), p. 216) — all
  consistent with the new rows.
- Section 6.1's `SynCatFO` docstring (lines 907-912): "o and Omega
  tau for arbitrary r-types tau" as the object sorts, quoting the
  section 2.7 copy-of-carrier sentence — consistent with, and the
  same citation as, the `Omega tau` row.
- Section 6.1's flat-recurrence sentence (lines 941-945) is the one
  later passage in tension with the new text — with the `Omega tau`
  row's paraphrase specifically, not with `Omega` usage; see
  R10-M1.

## Findings

### Major

#### R10-M1 — "output type" for "critical arguments of type"

The `Omega tau` row (line 243) states: "`Omega tau` is the type of
base-algebra elements permitted to serve as the recurrence argument
of a recurrence whose output type is `tau` (paraphrasing the
paper's p. 214)." The paper's sentence is:

> We introduce a type-constructor, Omega, where Omega tau is
> intended as the type of those base objects that support
> recurrence with critical arguments of type tau.

The paper characterizes `Omega tau` by the type of the *critical
arguments* (the recursive results, glossary row four), not by the
output type. Within the schema of eq. (4) the two coincide — the
critical arguments are values of `f` itself, so
`g_{c_i} : sigma-vec, (Omega tau)^{r_i}, tau^{r_i} -> tau` puts
both at `tau` — and under a reading of "a recurrence" as an
instance of eq. (4) (the row's first column cites eq. (4)) the
paraphrase is true. But the paper's wording is not an arbitrary
variant: flat recurrence (eq. (5), p. 215) has

> f : sigma-vec, o -> tau, g_{c_i} : sigma-vec, o^{r_i} -> tau

— recurrence argument at type `o`, output type `tau`, and no
critical arguments — and the paper immediately notes:

> (Note that we do not stipulate flat recurrence for recurrence
> arguments of Omega-type.)

So elements of type `o` are also "permitted to serve as the
recurrence argument of a recurrence whose output type is `tau`"
(a flat one), and the paraphrase's implicit uniqueness fails on
exactly the case the paper's phrasing was chosen to exclude. The
document itself depends on this distinction: section 6.1
(lines 941-945) argues that at `[o] -> [o]` "no monotonic
recurrence applies to the input (its recurrence argument must sit
at an Omega-sort), and flat recurrence, which is available at sort
`o`, passes no recursive results" — i.e., a flat recurrence with
an `o`-typed recurrence argument and arbitrary output type. Read
literally, the glossary row and that sentence disagree about what
recurrence-argument types an output type `tau` admits.

Fix (one phrase; the glossary already defines critical arguments
two rows above): replace "of a recurrence whose output type is
`tau`" with "of a recurrence whose critical arguments (recursive
results) carry `tau`", optionally adding "— by eq. (4) the output
type is then also `tau`". This restores the paper's wording,
keeps the row's substance, and removes the tension with
section 6.1.

### Minor

#### R10-m1 — the paper's expansion of "r-type" is "ramified functional types"

The `tau` row's second column ("The paper's name") reads: r-type
("ramified type"). The paper's expansion is "ramified *functional*
types (r-types for short)" (p. 214). The paper then overloads
"functional" — within the r-types, "the remaining types [those not
object types] are functional" — so the document's shorthand avoids
a genuine collision, but a column purporting to give the paper's
name should give the paper's phrase. Suggested form: r-type (the
paper's "ramified functional types"; "functional" there names the
whole class, and separately the non-object subclass). Adopting or
declining is wording-level either way.

### Observations (no change requested)

- The p. 214 "Note that, extensionally, A^{Omega tau} = A^{o}"
  sentence is direct on-page support for the row's
  copy-of-carrier conclusion; the row currently cites only
  section 2.7 for it. Citing the p. 214 sentence as well would
  place the evidence on the same page as the rest of the row's
  citations, but the section 2.7 citation is correct and
  sufficient.
- The row's "base-algebra elements" for the paper's "base objects"
  and "binary arrow" for "binary type operation" are faithful
  renderings; no action.

## Convergence verdict

Not converged for this scoped round: one major finding (R10-M1),
with a one-phrase fix that requires no structural change. All other
checks pass: the `tau` row's grammar and object/functional split
are verbatim-faithful to the paper's section 2.3 definition
(p. 214); its cross-references (`RType` in section 4.1, the
`Omega^m o` tower per the paper's section 2.4(3), p. 216) are
accurate; the `Omega tau` row's copy-of-carrier use is confirmed
by both the paper's section 2.7 (p. 218) and p. 214's extensional
Note, and its iterate/exponentiation citations match the paper;
the intro sentence and the "(last two rows)" pointer are accurate;
no contradiction with the document's later uses of `Omega` is
introduced beyond the R10-M1 tension; markdownlint and doctoc
pass. The minor finding (R10-m1) can be adopted or declined
without a further round; R10-M1 warrants a re-check of the single
revised phrase.
