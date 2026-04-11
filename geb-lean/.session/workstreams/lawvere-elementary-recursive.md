# Workstream: Lawvere Theory of Elementary Recursive Functions

## Status

Phase 0 design complete.  No Lean modules created yet.
Implementation unblocked at Phase 1 (inductive term type
for elementary recursive functions).

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

### Phase 5 -- Internalization (stages (b) then (c))

Stage (b):

* Define an internal `BTMor1`-analogue `X` as a decidable
  subobject of some `(ℕ, p)` in `LawvereERLexCat`.
* Define ER morphisms for `proj`, `leaf`, `branch`, `fold`
  landing in or out of `X`.
* Define an internal typechecker `X -> (ℕ, 1)`.

Stage (c):

* Reuse `X` verbatim as the `C₁` of an internal category.
* Define the arity object `C₀`.
* Define `src, tgt : X -> C₀`, `id : C₀ -> X`, and
  `comp : X ×_{C₀} X -> X` as ER morphisms.
* Check the unit and associativity laws as equations of
  `LawvereERLexCat` morphisms.

Downstream consequence:

* Establish that for every lex functor
  `I : LawvereERLexCat -> D` into a finite-limit category
  `D`, the image of the stage-(c) internal category is an
  internal category in `D`.  (This is a general property
  of lex functors; the statement lives at the workstream
  level rather than as separate Lean code for each `D`.)

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
   two stages.**  Stage (b) builds an internal
   `BTMor1`-analogue as a decidable subobject of
   `(ℕ, p)` with ER constructors, destructors, and
   typechecker.  Stage (c) upgrades the same subobject in
   place into an internal category in `LawvereERLexCat`
   by adding `src`, `tgt`, `id`, and `comp` morphisms; the
   stage-(b) subobject is reused verbatim as `C₁`.  No
   construction is thrown away between stages.
   Downstream finite-limit categories receive their
   internal `BTMor1`-analogue as the image of the
   `LawvereERLexCat` version under a lex
   (elementary-function-preserving) functor, which
   transports the full internal-category structure in one
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
* [ ] Phase 1: inductive term type for ER functions.
* [ ] Phase 2: extensional-equality quotient.
* [ ] Phase 3: Lawvere theory and interpretation functor.
* [ ] Phase 4: definable-subobject finite-limit category.
* [ ] Phase 5: stage (b) internal term type, then stage (c)
  internal-category structure.

## Notes

The `NatArith`, `NatElegantPair`, and `NatNNO` modules already
contain primitive-recursive pairing, iterated subtraction,
integer square root, and related infrastructure that is
expected to be reusable for an elementary-recursive term
semantics, either directly or as a template for an ER-level
reimplementation.
