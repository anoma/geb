# Workstream: Equalizer Completion of LawvereBTQuotCat

## Status

Planning complete; implementation not started.

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
  (not started)
- `GebLean/EqualizerCompletionLimits.lean` -- limits
  (not started)
- `GebLean/LawvereBTEqCompletion.lean` -- application
  (not started)

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
- [ ] Task 1: CoreflexivePairObj structure
- [ ] Task 2: Equivalence relation and premorphisms
- [ ] Task 3: Quotient category instance
- [ ] Task 4: Embedding functor
- [ ] Task 5: Pointwise finite products
- [ ] Task 6: Equalizer construction
- [ ] Task 7: Application to LawvereBTQuotCat
- [ ] Task 8: PBTO preservation
- [ ] Task 9: Interpretation functor extension
- [ ] Task 10: Tests
- [ ] Task 11: Module registration
