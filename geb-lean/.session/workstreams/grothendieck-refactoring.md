# Grothendieck Refactoring: High-Level Polynomial Functor API

Status: Phase 1 In Progress (2025-12-23)

## Objective

Refactor polynomial functor operations to work at the categorical level via
Grothendieck constructions, eliminating all low-level dependent type
manipulations.

## Background

See `docs/polynomial-functors-as-grothendieck.md` for the theoretical
foundation. Summary:

- Polynomial functors are double Grothendieck constructions
- This gives universal functorFrom/To/Between
- All operations should go through these universal functors
- Naturality and functoriality become automatic

## Theoretical Foundation: Enriched Hom Unification

See `docs/enriched-hom-unification.md` for the complete theory. Summary:

All categorical constructions in this codebase derive from the Cat-enriched
hom-bifunctor `[-, -] : Cat^op x Cat -> Cat`:

```text
[-, -] : Cat^op x Cat -> Cat
    |
    +-- [Discrete(X), D] = FamilyCat D X
    |       |
    |       +-- [Discrete(X), Type] = Over X   (familySliceEquiv)
    |
    +-- Grothendieck([-,-]) = Arr(Cat)
    |       |
    |       +-- Grothendieck(Hom_C) = TwArr(C)   (Set-enriched case)
    |
    +-- Double Grothendieck = Polynomial structure
            |
            +-- CoprodCovarRepCat(Over X) = PolyFunctorCat X
```

This means:

1. **FamilyCat is the Cat-enriched hom** with discrete first argument
2. **TwistedArrow is the Grothendieck** of the Set-enriched hom
3. **Polynomial functors use double Grothendieck** of the Cat-enriched hom
4. **Intro/elim rules are universal properties** of enriched hom

The enrichment hierarchy (Set -> Cat -> [J, Type]) provides progressively
richer structure, with our judgment-category adjunction transferring
Cat-enriched operations to copresheaf-enriched operations

## Current Problems

1. **Low-level proofs**: Operations like `polyFreeMap` require manual dependent
   type transport proofs (currently stuck at `polyFreeMLeafData_map_inr`)

2. **Monolithic evaluation**: `polyBetweenEvalFunctor` defined as single
   functor rather than composition

3. **Repeated patterns**: Each new polynomial operation requires reproving
   naturality from scratch

4. **No reuse**: Universal properties not exploited for composition

## Current Status

### Related Work: PolyTwCoprType Refactoring (2025-01-03)

The `PolyTwCoprType.lean` module has been refactored to use mathlib's category
of elements (`F.Elements`) as the foundation for `ElemCatObj` and `ElemCatMor`.
This aligns with the Grothendieck refactoring goals:

- `ElemCatObj` is now an abbreviation for `ccrElementsObj P.outerPolyProdId`
- `ElemCatMor` is now an abbreviation for `ccrElementsMor X Y`
- Accessor functions extract components from the sigma-type representation
- Compatibility proofs use categorical structure rather than ad-hoc transport

This demonstrates the pattern of using mathlib's categorical infrastructure
to avoid low-level dependent type manipulations.

See `.session/workstreams/paranatural-investigations.md` for details.

### Completed (2025-12-23 Session)

1. **Double Grothendieck Composition Lemmas** (Phase 1.1 continued):
   - Added `ιSecond` and `ιNested` fiber inclusion functors
   - Added `ιSecond_comp_forgetSecond` composition lemma
   - Added `forgetBothIso` factorization isomorphism
   - Added `forgetSecond_base_eq` and `forgetSecond_fiber_eq` extractors
   - Added `functor_factors_forgetSecond` and `functor_from_factors` theorems
   - Documented layered construction pattern for functors into double Grothendieck

2. **Build Status**: Clean build, all tests passing, no warnings

### Files Modified This Session

- `GebLean/Utilities/Grothendieck.lean`: Extended DoubleGrothendieck section
  (now lines 6535-6728)

### What's Still Missing from Phase 1

1. **functorBetween completion** (Phase 1.2):
   - Need clean public API for `functorBetween` constructor
   - Currently `toFunctorViaPre` exists but interface needs refinement

2. **Generic functorFrom for double Grothendieck**:
   - Dual to functorTo pattern already documented
   - Should compose two single-layer FunctorFromData

### Next Steps When Resuming

**Immediate next task**: Proceed to Phase 1.2 (functorBetween completion) or
move to Phase 2 (applying infrastructure to polynomial functors).

**Location to continue**: Either `GebLean/Utilities/Grothendieck.lean` for
functorBetween API, or `GebLean/PolyAdjunctions.lean` to apply the double
Grothendieck infrastructure.

**Pattern to use**: The documented pattern for constructing functors into
double Grothendieck:

1. Define first-layer FunctorToData F
2. Define second-layer FunctorToData G with baseFunc := first-layer functor
3. Apply functorTo G

## Implementation Plan

### Phase 1: Extend Grothendieck Infrastructure

Location: `GebLean/Utilities/Grothendieck.lean`

#### 1.1: functorBetween for Grothendieck Constructions

```lean
/--
Universal functor between Grothendieck constructions.
Given F : C ⥤ Cat and G : D ⥤ Cat, to define (∫F) ⟶ (∫G),
it suffices to define functors on base and fibers with compatibility.
-/
def functorBetween {C D : Type*} [Category C] [Category D]
    (F : C ⥤ Cat) (G : D ⥤ Cat)
    (baseMap : C ⥤ D)
    (fiberMaps : ∀ c, F.obj c ⥤ G.obj (baseMap.obj c))
    (compatibility : ...) : (∫F) ⥤ (∫G)
```

**Rationale**: Completing the universal property interface. functorFrom and
functorTo handle one-sided constructions; functorBetween handles transformations
between Grothendieck constructions.

#### 1.2: Double Grothendieck Utilities

```lean
/--
For composed Grothendieck constructions ∫∫F, provide utilities for:
- Associativity of Grothendieck composition
- Functoriality of the double construction
- Universal properties that compose
-/
section DoubleGrothendieck
  -- Composition of two Grothendieck layers
  -- Universal properties for double constructions
  -- Functoriality lemmas
end DoubleGrothendieck
```

**Rationale**: Polynomial functors use TWO Grothendieck layers (position then
direction). Need infrastructure for working with composed constructions.

### Phase 2: Generic Polynomial Functor API

Location: `GebLean/PolyAdjunctions.lean`

#### 2.1: Polynomial Functors as Double Grothendieck

```lean
/--
Recognize that a polynomial functor I ← E → X is a double Grothendieck:
1. First layer: position p : E → I gives ∫ᵖ
2. Second layer: direction d : E → X gives ∫ᵈ(∫ᵖ)
The evaluation Type/I → Type/X factors through these constructions.
-/
section PolyAsGrothendieck
  /-- Position Grothendieck layer -/
  def polyPositionGrothendieck (P : PolyBetween I X) : ...

  /-- Direction Grothendieck layer -/
  def polyDirectionGrothendieck (P : PolyBetween I X) : ...

  /-- Evaluation as composition -/
  def polyEvalViaGrothendieck (P : PolyBetween I X) :
    polyBetweenEvalFunctor P ≅
    (composition of position and direction Grothendieck functors)
end PolyAsGrothendieck
```

**Rationale**: Makes explicit that polynomial functors ARE Grothendieck
constructions. All subsequent development builds on this recognition.

#### 2.2: Generic functorFrom for Polynomials

```lean
/--
Universal elimination rule for polynomial functors.
To define Poly(I,X) ⟹ G, apply functorFrom twice (direction then position).
The result is automatically natural.
-/
def polyFunctorFrom {G : Type*} [Category G]
    (P : PolyBetween I X)
    (targetData : ...) : -- Specification of what you want to construct
    (∫∫P) ⥤ G
```

**Rationale**: Every operation that EXTRACTS from polynomials (like
representations, evaluations at specific objects) uses this. Naturality
automatic.

**Examples**:

- `polyFreeM_to_polyFreeMPolyEval`: use polyFunctorFrom
- Evaluation at a specific object: use polyFunctorFrom
- Projections and observations: use polyFunctorFrom

#### 2.3: Generic functorTo for Polynomials

```lean
/--
Universal introduction rule for polynomial functors.
To construct Poly(I,X) from F, apply functorTo twice (position then direction).
The result is automatically functorial.
-/
def polyFunctorTo {F : Type*} [Category F]
    (sourceData : ...) : -- Specification of source structure
    F ⥤ (∫∫P)
```

**Rationale**: Every operation that CONSTRUCTS polynomials uses this. Functoriality
automatic.

**Examples**:

- Free monad unit: use polyFunctorTo
- Cofree comonad counit: use polyFunctorTo
- Algebra structure maps: use polyFunctorTo

#### 2.4: Generic functorBetween for Polynomials

```lean
/--
Universal transformation rule for polynomial functors.
To define Poly(I,X) ⟹ Poly(J,Y), factor through intermediate categories
using functorFrom on source and functorTo on target.
-/
def polyFunctorBetween
    (P : PolyBetween I X) (Q : PolyBetween J Y)
    (transformData : ...) : -- How to transform position/direction
    (∫∫P) ⥤ (∫∫Q)
```

**Rationale**: Every polynomial-to-polynomial transformation uses this.
Naturality automatic from composition.

**Examples**:

- Free monad map: use polyFunctorBetween
- Free monad join: use polyFunctorBetween
- Cofree comonad operations: use polyFunctorBetween

### Phase 3: Refactor Evaluation Functor

Location: `GebLean/Polynomial.lean` and `GebLean/PolyAdjunctions.lean`

#### 3.1: Factor polyBetweenEvalFunctor

Currently `polyBetweenEvalFunctor` is monolithic. Refactor as:

```lean
/--
The evaluation functor as composition of Grothendieck functors.
Type/I
  → [functorFrom for position]
  → (intermediate category)
  → [base change]
  → Type
  → [functorTo for direction]
  → Type/X
-/
def polyBetweenEvalFunctor (P : PolyBetween I X) :
    (Over I) ⥤ (Over X) :=
  positionFunctorFrom ≫ baseChange ≫ directionFunctorTo
```

**Benefits**:

- Each component has its own universal property
- Composition of natural transformations is natural
- Properties of evaluation follow from properties of components

#### 3.2: Prove Evaluation Properties via Composition

Instead of proving properties of `polyBetweenEvalFunctor` directly, prove:

- Properties of position functorFrom
- Properties of base change
- Properties of direction functorTo
- Evaluation properties follow by composition

### Phase 4: Refactor Free Monad Operations

Location: `GebLean/PolyAlg.lean`

#### 4.1: Free Monad Representation via polyFunctorFrom

Replace:

```lean
def polyFreeM_to_polyFreeMPolyEval : ...
theorem polyFreeM_to_polyFreeMPolyEval_natural : ...
```

With:

```lean
def polyFreeMRepresentation :
    polyFunctorFrom (polyFreeMPoly P) targetSpec ≅ ...
-- Naturality automatic from polyFunctorFrom
```

**Benefit**: Eliminates `polyFreeMLeafData_map` and all its transport proofs.
The generic functorFrom handles all dependent type manipulations.

#### 4.2: Free Monad Map via polyFunctorBetween

Replace:

```lean
def polyFreeMapAt (f : A ⟶ B) : PolyFreeM A P x → PolyFreeM B P x
theorem polyFreeMapAt_natural : ...
```

With:

```lean
def polyFreeMap :
    polyFunctorBetween (polyFreeMPoly P at A) (polyFreeMPoly P at B)
-- Naturality automatic from polyFunctorBetween
```

**Benefit**: Eliminates all naturality proofs. The transformation between
polynomial categories is handled by the generic machinery.

#### 4.3: Free Monad Join via Universal Property

Replace direct definition with:

```lean
def polyFreeMJoin :
    polyFunctorBetween
      (polyFreeMPoly (polyFreeMPoly P))
      (polyFreeMPoly P)
```

Define via universal property: Free(Free(P)) is initial algebra for certain
endofunctor, join is the unique morphism to Free(P).

**Benefit**: Naturality follows from uniqueness in universal property. No manual
proof needed.

### Phase 5: Apply to Cofree Comonad

Location: `GebLean/PolyAlg.lean`

Dual refactoring for cofree comonad:

- Cofree representation via polyFunctorFrom
- Cofree map via polyFunctorBetween
- Cofree duplicate (comultiplication) via universal property

All following the same pattern as free monad.

### Phase 6: The Module Structure (Future)

Once both free and cofree work smoothly with the new API:

```lean
/--
The distributive law Free ∘ Cofree → Cofree ∘ Free
making Free monad a module over Cofree comonad.
-/
def freeMonadCofreeComonadModule :
    polyFunctorBetween
      (Free ∘ Cofree)
      (Cofree ∘ Free)
```

This is now straightforward composition of polyFunctorBetween.

## Migration Strategy

### Compatibility Layer

During migration, maintain compatibility:

```lean
-- Old interface (deprecated, but working)
def polyFreeMap_old := ... -- current implementation

-- New interface
def polyFreeMap := polyFunctorBetween ...

-- Compatibility
theorem polyFreeMap_eq_old : polyFreeMap = polyFreeMap_old := ...
```

### Incremental Refactoring

1. **Phase 1-2**: Build new infrastructure without touching existing code
2. **Phase 3**: Refactor evaluation functor, prove equivalence to old version
3. **Phase 4**: Refactor free monad using new API
4. **Phase 5**: Refactor cofree comonad
5. **Phase 6**: Add module structure

At each phase, all tests continue to pass because we prove equivalence.

### Testing Strategy

For each refactored operation:

1. Prove it's equivalent to old version
2. Run existing tests through compatibility layer
3. Write new tests using only new API
4. Eventually remove old version once all clients migrated

## Success Criteria

After completion:

- **Zero manual transport proofs** in polynomial functor operations
- **Automatic naturality** for all operations via functorFrom/To/Between
- **Compositional**: New operations build from existing ones
- **All existing tests pass** through compatibility layer
- **Free monad monad multiplication naturality** proven with no low-level work

## Estimated Scope

This is a major refactoring touching:

- `Grothendieck.lean`: +300 lines (functorBetween, double Grothendieck utilities)
- `PolyAdjunctions.lean`: +500 lines (polynomial as Grothendieck, generic functors)
- `Polynomial.lean`: ~200 lines (refactor evaluation functor)
- `PolyAlg.lean`: ~1000 lines (refactor free/cofree operations)

But eliminates: ~2000 lines of transport proofs that we would otherwise write.

Net: More upfront infrastructure, massive savings in all future development.

## Next Actions

1. ✅ Document theory (this file + docs/polynomial-functors-as-grothendieck.md)
2. Implement Phase 1: Extend Grothendieck utilities
3. Implement Phase 2: Generic polynomial API
4. Implement Phase 3: Refactor evaluation functor
5. Implement Phase 4-6: Apply to free/cofree/module

Begin with Phase 1, building incrementally with tests at each stage.
