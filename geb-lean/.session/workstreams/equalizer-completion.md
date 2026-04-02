# Workstream: Equalizer Completion of LawvereBTQuotCat

## Status

Implementation substantially complete. PBTO preservation
(Task 8) deferred -- requires showing the fold universal
property extends from embedded objects to arbitrary
coreflexive pairs.

## Goal

Add finite limits (equalizers) to the Lawvere theory of
parameterized binary tree objects, using the Pitts/Bunge
construction (free equalizer completion of a category with
finite products).

## Mathematical Background

The construction, from Bunge & Carboni "The Symmetric Topos"
(JPAA 1995), attributed to Pitts:

- Objects: coreflexive pairs (X₀, X₁, ∂₀, ∂₁, ρ) with
  ∂₀ ≫ ρ = id and ∂₁ ≫ ρ = id
- Morphisms: EqvGen-equivalence classes of premorphisms
- Finite products: pointwise from the base category
- Equalizers: E₀ = X₀, E₁ = X₁ × Y₁, with asymmetric
  section maps using f and g

## Files

- `docs/equalizer-completion.md` -- mathematical
  transcription (complete)
- `docs/superpowers/plans/2026-04-01-equalizer-completion.md`
  -- implementation plan (complete)
- `GebLean/EqualizerCompletion.lean` -- generic construction
  (complete: 671 lines)
- `GebLean/EqualizerCompletionLimits.lean` -- limits
  (complete: 894 lines)
- `GebLean/LawvereBTEqCompletion.lean` -- application
  (complete except PBTO)
- `GebLeanTests/TestEqualizerCompletion.lean` -- tests
  (complete)

## Dependencies

- `GebLean/LawvereBTQuot.lean` -- HasChosenFiniteProducts,
  HasPBTO instances
- `GebLean/LawvereBTInterp.lean` -- interpFunctor,
  faithfulness
- `GebLean/Utilities/ComputableLimits.lean` -- cfpMap, etc.
- `Mathlib.Logic.Relation` -- EqvGen
- `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`
  -- hasFiniteLimits_of_hasEqualizers_and_finite_products

## Tasks

- [x] Transcribe Bunge/Carboni construction to docs/
- [x] Research mathlib for existing constructions
- [x] Write implementation plan
- [x] Task 1: CoreflexivePairObj structure
- [x] Task 2: Equivalence relation and premorphisms
- [x] Task 3: Quotient category instance
- [x] Task 4: Embedding functor (full and faithful)
- [x] Task 5: Pointwise finite products
- [x] Task 6: Equalizer construction + HasFiniteLimits
- [x] Task 7: LawvereBTLexCat definition + instances
- [ ] Task 8: PBTO preservation (deferred)
- [x] Task 9: Interpretation functor extension
- [x] Task 10: Tests
- [x] Task 11: Module registration (done incrementally)

## Remaining: PBTO Preservation (Task 8)

The PBTO in `LawvereBTQuotCat` has `T = 1`,
`ℓ = btLeafQ`, `β = btBranchQ`. Under the embedding,
these become morphisms between trivially-embedded objects.
The universal property `elim` must be extended to work
for arbitrary coreflexive pairs A and X (not just
embedded ones). This requires:

1. Defining `elim` on the src-components using the
   existing `elimQ` from `LawvereBTQuot.lean`
2. Showing the result is a premorphism in the completion
3. Proving computation rules hold modulo the coreflexive
   equivalence relation
4. Proving uniqueness modulo the equivalence relation

The main difficulty is that `elimQ` operates on raw
quotient morphisms in `LawvereBTQuotCat`, and the
coreflexive equivalence adds another layer of quotient
that the fold axioms must respect.
