# Workstream: Twisted Arrow Categories as Grothendieck Constructions

## Status

Complete - Main equivalences proven, remaining variants documented

## Context

This workstream explores the relationship between twisted arrow categories and
Grothendieck constructions. The goal is to express each of the four twisted
arrow variants as a Grothendieck construction over slice/coslice categories,
which would enable cleaner functor constructions by leveraging existing
`FunctorFromData` infrastructure.

## Analysis

### Twisted Arrow Category Structure

The twisted arrow category `TwistedArrow' C` has:

- Objects: `(x, y, f : x ⟶ y)` - morphisms in C
- Morphisms `(x, y, f) → (x', y', f')`:
  - `domArr : x' ⟶ x` (backwards on domain)
  - `codArr : y ⟶ y'` (forwards on codomain)
  - Commutativity: `domArr ≫ f ≫ codArr = f'`

### Key Finding: TwistedArrow' C ≅ Grothendieck(Under : Cᵒᵖ ⥤ Cat)

The twisted arrow category is isomorphic to the Grothendieck construction of
the Under functor:

**Under functor**: `Under : Cᵒᵖ ⥤ Cat`

- `Under.obj (op x) = Under x` (category of arrows out of x)
- `Under.map (op domArr) : Under x ⥤ Under x'` for `domArr : x' ⟶ x`
  via precomposition: `(y, f : x ⟶ y) ↦ (y, domArr ≫ f : x' ⟶ y)`

**Grothendieck(Under)** has:

- Objects: `(op x, (y, f : x ⟶ y))`
- Morphisms `(op x, f) → (op x', f')`:
  - Base: `op domArr : op x ⟶ op x'` in Cᵒᵖ (i.e., `domArr : x' ⟶ x` in C)
  - Fiber: `(y, domArr ≫ f) ⟶ (y', f')` in Under x'
    which is `codArr : y ⟶ y'` with `domArr ≫ f ≫ codArr = f'`

This exactly matches `TwistedArrow' C`.

### The Four Variants

The four twisted arrow variants arise from two binary choices:

1. **Base indexing**: Domain (Under) vs Codomain (Over)
2. **Grothendieck variance**: Covariant vs Contravariant

| Variant | Base | Grothendieck | domArr direction | codArr direction |
|---------|------|--------------|------------------|------------------|
| TwistedArrow' C | Under (domain) | Covariant | backwards | forwards |
| Grothendieck(Over) | Over (codomain) | Covariant | forwards | forwards |
| GrothendieckContra(Under') | Under | Contravariant | forwards | backwards |
| GrothendieckContra(Over') | Over | Contravariant | backwards | backwards |

### Detailed Analysis of Each Variant

#### 1. TwistedArrow' C = Grothendieck(Under : Cᵒᵖ ⥤ Cat)

- Domain x is base (indexed contravariantly via Cᵒᵖ)
- `domArr : x' ⟶ x` backwards, `codArr : y ⟶ y'` forwards
- Commutativity: `domArr ≫ f ≫ codArr = f'`

#### 2. Grothendieck(Over : C ⥤ Cat)

- Codomain y is base (indexed covariantly)
- `domArr : x ⟶ x'` forwards, `codArr : y ⟶ y'` forwards
- Commutativity: `domArr ≫ f' = f ≫ codArr`
- This is related to `(TwistedArrow' C)ᵒᵖ` via the isomorphism that swaps the
  direction of morphisms

#### 3. GrothendieckContra(Under' : C ⥤ Cat)

- Would require Under viewed as a C-indexed functor (not Cᵒᵖ)
- Fiber morphisms go "against" the transport direction
- Results in: `domArr : x ⟶ x'` forwards, `codArr : y' ⟶ y` backwards

#### 4. GrothendieckContra(Over' : Cᵒᵖ ⥤ Cat)

- Over viewed as Cᵒᵖ-indexed
- Fiber morphisms go "against" the transport direction
- Results in: `domArr : x' ⟶ x` backwards, `codArr : y' ⟶ y` backwards

### Duality Between Over and Under

The Over and Under categories are dual in the following sense:

- `Over y` = arrows INTO y = `Under(Cᵒᵖ).obj (op y)`
- `Under x` = arrows FROM x = `Over(Cᵒᵖ).obj (op x)`

This explains why:

- TwistedArrow' C uses Under (domain-indexed, backwards domArr)
- The "opposite" twisted arrow uses Over (codomain-indexed, forwards domArr)

## Implications for Functor Factorization

### The Factorization Strategy

A functor `TwistedArrow' C ⥤ Type v` can be factored as:

```text
TwistedArrow' C ──equiv──▶ Grothendieck(Under) ──functorFrom──▶ Type v
```

Where:

1. **equiv**: The isomorphism `TwistedArrow' C ≅ Grothendieck(Under : Cᵒᵖ ⥤ Cat)`
2. **functorFrom**: A functor FROM the Grothendieck construction using
   `FunctorFromData`

### FunctorFromData for Under

The `FunctorFromData` structure for `Under : Cᵒᵖ ⥤ Cat` consists of:

- `fib : ∀ x, Under x ⥤ Type v` - a functor from each coslice category
- `hom : ∀ (domArr : x' ⟶ x), fib x ⟶ Under.map domArr ⋙ fib x'`
- `hom_id`, `hom_comp` - coherence conditions

The key benefit: `FunctorFromData.functorFromData` already has proven functor
laws (`map_id`, `map_comp`), so the eqToHom management is handled once in that
general construction.

### Contravariant Fibers

Our slice data has contravariant fibers: `fib y : (Over y)ᵒᵖ ⥤ Type v`
(presheaves on slices). For the Under-based formulation, we need:

`fib x : (Under x)ᵒᵖ ⥤ Type v` or equivalently `fib x : Under x ⥤ Type v` with
appropriate variance handling.

This may require:

1. A `FunctorFromContraFibData` variant where fibers are contravariant
2. Or careful use of opposite categories in the base functor

## Implementation Plan

### Phase 1: Establish Equivalences

- [x] Use mathlib's `Under.mapFunctor : Cᵒᵖ ⥤ Cat`
- [x] Prove `TwistedArrow' C ≌ Grothendieck(Under.mapFunctor C)` via
  `twArrEquivGrothendieckUnder` in `TwistedArrow.lean`
- [x] Prove `OpTwistedArrow' C ≌ (Grothendieck(Under.mapFunctor C))ᵒᵖ'` via
  `opTwArrEquivGrothendieckUnderOp'`
- [x] Document equivalences for remaining variants:
  - `TwistedArrowOp' C ≌ Grothendieck(Under.mapFunctor Cᵒᵖ')` (conceptually;
    Lean implementation blocked by typeclass instance differences)
  - `CoTwistedArrow C ≌ (Grothendieck(Under.mapFunctor Cᵒᵖ'))ᵒᵖ'` (conceptually)

### Phase 2: FunctorFromData with Contravariant Fibers

- [ ] Define `FunctorFromContraFibData` for functors with contravariant fibers
- [ ] Prove the functor laws for `functorFromContraFibData`
- [ ] Show this generalizes the existing `FunctorFromData`

### Phase 3: Refactor Twisted Arrow Presheaves

- [ ] Express `TwArrCopresheaf` slice data as `FunctorFromContraFibData`
- [ ] Factor the functor construction through the equivalence
- [ ] Verify the functor laws follow from the general construction

### Phase 4: Other Variants

- [ ] Apply the same factorization to `TwArrPresheaf`
- [ ] Apply to `TwArrOpCopresheaf` and `TwArrOpPresheaf`

## Connection to Existing Work

This builds on the Grothendieck functor factorization workstream:

- `SectionData` captures sections of `forget : Grothendieck F ⥤ C`
- `FunctorToData` decomposes as base functor + section data
- `FunctorFromData` captures functors FROM Grothendieck constructions

The new insight is that twisted arrow categories ARE Grothendieck constructions
over Under/Over, so the existing infrastructure applies directly.

## Open Questions

1. What is the precise relationship between `Grothendieck(Over)` and
   `(TwistedArrow' C)ᵒᵖ`?

2. Can we unify all four variants under a single parameterized construction?

3. ~~Does mathlib already have the `underMapFunctor : Cᵒᵖ ⥤ Cat`?~~
   **Resolved**: Yes, mathlib has `Under.mapFunctor : Cᵒᵖ ⥤ Cat`.

## Findings

### Proven Equivalences

`TwistedArrow' C ≌ Grothendieck (Under.mapFunctor C)` is proven via:
- `twArrToGrothendieckUnder : TwistedArrow' C ⥤ Grothendieck (Under.mapFunctor C)`
- `grothendieckUnderToTwArr : Grothendieck (Under.mapFunctor C) ⥤ TwistedArrow' C`
- `twArrEquivGrothendieckUnder : TwistedArrow' C ≌ Grothendieck (Under.mapFunctor C)`

`OpTwistedArrow' C ≌ (Grothendieck (Under.mapFunctor C))ᵒᵖ'` is proven via:
- `opTwArrEquivGrothendieckUnderOp'` which combines:
  - `opTwistedArrowIsoTwistedArrowOp' : OpTwistedArrow' C ≅Cat (TwistedArrow' C)ᵒᵖ'`
  - `Equivalence.op' twArrEquivGrothendieckUnder`

### Typeclass Instance Limitation

The equivalences for `TwistedArrowOp' C` and `CoTwistedArrow C` are conceptually
straightforward but blocked by Lean typeclass instance differences:

- `TwistedArrowOp' C = TwistedArrow' Cᵒᵖ'` definitionally (by `rfl`)
- However, `instCategoryTwistedArrowOp' C` and `instCategoryTwistedArrow' Cᵒᵖ'`
  are different instance names
- This prevents direct casting of the equivalence

The mathematical relationships are documented in `TwistedArrow.lean`.

### Morphism Direction Analysis

The four twisted arrow variants have different morphism directions:

| Variant | domArr direction | codArr direction |
|---------|------------------|------------------|
| TwistedArrow' C | backwards | forwards |
| TwistedArrowOp' C | backwards | forwards |
| OpTwistedArrow' C | forwards | backwards |
| CoTwistedArrow C | forwards | backwards |

TwistedArrow' and TwistedArrowOp' have the same morphism directions but different
object arrows (f : dom ⟶ cod vs f : cod ⟶ dom). Similarly for OpTwistedArrow'
and CoTwistedArrow.

### Why Direct Grothendieck Equivalences Are Not Straightforward

For the covariant Grothendieck construction `Grothendieck(F)`:
- Base morphisms go forwards
- Fiber morphisms go forwards

For the contravariant Grothendieck construction `GrothendieckContra'(F')`:
- Base morphisms go forwards
- Fiber morphisms go forwards (within the transported fiber)

Neither construction directly matches variants with one morphism direction
backwards and one forwards. The equivalences for other variants require
composing with opposite category functors or using different indexing schemes.

## References

- `GebLean/Utilities/TwistedArrow.lean` - Twisted arrow category definitions
- `GebLean/Utilities/Grothendieck.lean` - Grothendieck constructions and
  FunctorFromData
- `GebLean/Utilities/TwArrPresheaf.lean` - Current slice-based approach
- `Mathlib.CategoryTheory.Comma.Over` - Over categories
- `Mathlib.CategoryTheory.Comma.Basic` - Under categories
