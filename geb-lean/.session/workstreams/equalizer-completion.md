# Workstream: Equalizer Completion of LawvereBTQuotCat

## Status

Implementation substantially complete. PBTO preservation
(Task 8) partially complete: generic premorphism lemmas
for the fold have been proved in
`EqualizerCompletionPBTO.lean`, including the result
`elim_isPremorphism_of_oneStep_step` which proves the
premorphism condition for `p.elim f g` when the step
function `g` has a one-step premorphism witness.
The general case with `EqvGen` step-function premorphism
condition remains open (see "Remaining" section).

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
- [~] Task 8: PBTO preservation (partial -- see below)
- [x] Task 9: Interpretation functor extension
- [x] Task 10: Tests
- [x] Task 11: Module registration (done incrementally)

## Remaining: PBTO Preservation (Task 8)

### What has been proved

In `GebLean/EqualizerCompletionPBTO.lean`:

- `elim_naturality`: naturality of `p.elim` in the
  base parameter
- `elim_algebra_morphism`: algebra morphism property
  of `p.elim`
- `elim_base_relStep` / `elim_base_eqvGen`: changing
  the base of a fold preserves the coreflexive
  equivalence (Lemma A)
- `elim_isPremorphism_oneStep`: one-step premorphism
  condition given one-step witnesses for both `f` and
  `g`
- `cpReflWitness` and related lemmas: reflexivity
  witnesses `cfpMap X.retract X.retract ≫ g ≫ q`
  for sections `q` of `X`
- `elim_left_via_refl` / `elim_right_via_refl`:
  `p.elim f g ≫ X.left = p.elim (f ≫ X.left) wL`
  and similarly for `X.right`
- `elim_refl_retract`: the fold via a reflexivity
  witness retracts to the original fold
- `elim_cross_retract`: the fold via one reflexivity
  witness, post-composed with `X.retract ≫ q₂`,
  equals the fold via the reflexivity witness for `q₂`
- `elim_isPremorphism_of_oneStep_step`: the
  premorphism condition for `p.elim f g` when `g` has
  a one-step premorphism witness (a single `w_g`
  satisfying both `cfpMap X.left X.left ≫ w_g =
  g ≫ X.left` and `cfpMap X.right X.right ≫ w_g =
  g ≫ X.right`)
- `elim_isPremorphism_of_relStep_step`: wrapper
  extracting the one-step witness from a
  `CoreflexiveRelStep`

### What remains

The general premorphism condition
`elim_isPremorphism` with `IsCPPremorphism` (i.e.,
`EqvGen`-based) on BOTH `f` and `g` is not yet
proved. The `elim_isPremorphism_of_oneStep_step`
theorem handles the case where `g`'s premorphism
condition is one-step. The gap is the "step-function
change": showing that changing the step function
between the two reflexivity witnesses
`cpReflWitness X g X.left` and
`cpReflWitness X g X.right` preserves the
coreflexive equivalence of the fold output.

The step-function change reduces to:
`CoreflexiveEqv (cpProd A (cpEmbed p.T))
  (p.elim (f ≫ X.right) (cpReflWitness X g X.left))
  (p.elim (f ≫ X.right) (cpReflWitness X g X.right))`

The two step functions differ by post-composition of
`cfpMap X.retract X.retract ≫ g` with `X.left` vs
`X.right`. Both retract to the same fold
`p.elim f g`, but the coreflexive equivalence in
`cpProd A (cpEmbed p.T)` relates things through the
`A`-side structure, while the step-function change is
an `X`-side phenomenon. This mismatch makes the
pre-quotient proof non-trivial.

Possible approaches for the remaining gap:

1. Prove at the quotient-category level where the
   universal property directly gives the result
2. Show that in the application to `LawvereBTQuotCat`,
   the `g` premorphism condition is always one-step
   (which may follow from the construction)
3. Prove a structural result about `EqvGen` and folds
   that handles the step-function change
