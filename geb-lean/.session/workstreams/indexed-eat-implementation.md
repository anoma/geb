# Indexed EAT Implementation

## Status: EAT Adjunction Complete (via EATHasQuotient Typeclass)

## Goal

Implement a generic essentially algebraic theory (EAT) embedding framework that:

1. Takes an EAT specification (polynomial endofunctor + equations)
2. Produces an adjunction L ⊣ Φ embedding models into copresheaves
3. Decomposes as two adjunctions: completion and quotient

## Architecture

### Core Structure: IndexedEAT

```text
structure IndexedEAT (X : Type u) where
  poly : PolyEndo X           -- polynomial endofunctor on Over X
  equations : PolyFixRel poly -- equivalence relation on initial algebra
  eqIsEquiv : equations.IsEquivalence
```

### Model Predicate (Fold-Based)

A P-algebra A is a model iff the canonical fold from PolyFix respects
the EAT equations:

```text
def IsEATModel (T : IndexedEAT X) (A : PolyAlg T.poly) : Prop :=
  ∀ x (t₁ t₂ : PolyFix T.poly x),
    T.equations x t₁ t₂ →
    polyFixFoldLeft T.poly A ⟨x, t₁⟩ = polyFixFoldLeft T.poly A ⟨x, t₂⟩
```

This avoids `Quotient.choice` by using the existing catamorphism (fold)
and checking if it collapses equivalent elements.

### Two Adjunctions

1. **Completion Adjunction** (Free ⊣ Forget):
   - Free : Over X → PolyAlg poly (free P-algebra via PolyFreeM)
   - Forget : PolyAlg poly → Over X (forgetful)
   - Already implemented in PolyAlg.lean

2. **Quotient Adjunction** (Quotient ⊣ Inclusion):
   - EATModel : full subcategory of PolyAlg poly (bundled algebras + proof)
   - Inclusion : EATModel → PolyAlg poly (fully faithful)
   - Quotient : PolyAlg poly → EATModel (via EATIsQuotientable)

### Combined Adjunction

- L = Quotient ∘ Free : Over X → EATModel
- Φ = Forget ∘ Inclusion : EATModel → Over X
- L ⊣ Φ by adjunction composition

## Completed Work

### PLang/IndexedEAT.lean

Core Definitions:

- `IndexedEAT X` - core structure with poly + equations + equivalence proof
- `PolyFixRel` - indexed equivalence relation on initial algebra
- `EATCongruence` - congruence condition for equations

Setoid Infrastructure:

- `SetoidOverX` - setoid-valued families over X
- `SetoidOverMor` - setoid-respecting morphisms
- `IndexedEAT.initialSetoid` - initial algebra as setoid

Model Category:

- `IsEATModel` - model predicate via fold
- `EATModel` - bundled model structure
- `EATModelHom` - morphisms between models
- `EATModel.inclusionFunctor` - inclusion into PolyAlg
- `EATModel.inclusionFullyFaithful` - fully faithful embedding
- `EATModel.embeddingFunctor` - composition with forgetful

Trivial EAT:

- `trivialEAT` - trivial EAT where all algebras are models
- `trivialEAT_allModels` - proof all algebras satisfy IsEATModel
- `trivialEAT.reflector` - wraps algebras as models
- `trivialEAT.reflectorFunctor` - functor version
- `trivialEAT.reflectorUnit/Counit` - unit and counit
- `trivialEAT.reflectorAdjunction` - Reflector ⊣ Inclusion adjunction

Generic Quotient Infrastructure:

- `FreeAlgEquiv` - equivalence on free algebra induced by EAT equations
- `FreeAlgQuot` - quotient type at each fiber
- `freeAlgQuotOver` - quotient as Over X object
- `polyFixToFreeAlg` - embedding of initial algebra into free algebra
- `freeAlgQuotStrRepr` - structure map on representatives
- `freeAlgQuotStrRepr_resp` - congruence property for lifting

Setoid Algebra:

- `PolySetoidAlg` - P-algebra with equivalence relation
- `freeAlgFiberElem` - extract fiber element
- `freeAlgSetoidAlg` - free algebra as setoid algebra

Quotient Factorization:

- `AlgHomRespectsEquiv` - predicate for homomorphisms respecting equiv
- `modelCounitRespectsEq` - models respect EAT equations
- `polyFreeCounitFoldAt_closed` - fold on embedded elements equals initial fold
- `freeAlgFoldRespectsFromEq` - fold respects equations on embedded elements
- `freeAlgCounitRespectsEquiv` - counit respects equivalence
- `quotientLift` - lift equivalence-respecting map through quotient

Quotient Data Interface:

- `EATQuotientData` - data needed for quotient adjunction
- `trivialEAT.quotientData` - trivial EAT instance

Composed Functors:

- `trivialEAT.leftAdjoint` - Free ⋙ Reflector for trivial EAT
- `trivialEAT.rightAdjoint` - Embedding functor

EATHasQuotient Typeclass:

- `EATHasQuotient` - typeclass providing quotient algebra infrastructure
  - `quotientAlg` - quotient of free algebra as P-algebra
  - `quotientHomomorphism` - quotient map as algebra homomorphism
  - `quotientNaturality` - naturality of quotient map
  - `quotientRespectsEquiv` - quotient identifies equivalent elements
  - `quotientFactor` - factorization through quotient for model targets

EAT Adjunction:

- `eatAdjunctionUnit` - unit: A → Φ(L(A))
- `eatAdjunctionCounit` - counit: L(Φ(M)) → M
- `eatAdjunction` - full L ⊣ Φ adjunction for any EAT with quotients
  - Left triangle identity proven via quotient factor uniqueness
  - Right triangle identity proven via polyFreeCounitFoldAt_pure

## Remaining Work

### Step 1: Instantiate EATHasQuotient for Non-Trivial EATs

The typeclass-based approach allows incremental instantiation. To use the
adjunction for a specific EAT, provide an instance of `EATHasQuotient`.
The trivial EAT (with no equations) already has an instance.

### Step 2: Cat Example

Instantiate for Cat to verify the construction matches
CatJudgmentAdjunction. This requires defining `EATHasQuotient` for the
category EAT with associativity and unit equations.

## Design Decisions

1. **No Quotient.choice**: Use fold predicate instead of quotient types
2. **Typeclass for quotients**: EATIsQuotientable captures when quotients
   exist computably
3. **Full subcategory**: EATModel is a full subcategory via bundling
4. **Initiality**: Use existing polyFixFold infrastructure
5. **Congruence**: Required for quotient to preserve algebra structure

## Code References

- `GebLean/PolyAlg.lean:91` - PolyAlg definition
- `GebLean/PolyAlg.lean:155` - PolyFix inductive
- `GebLean/PolyAlg.lean:360` - polyFixFoldHom (catamorphism)
- `GebLean/PolyAlg.lean:2242` - PolyFreeM definition
- `GebLean/PLang/IndexedEAT.lean` - current implementation
