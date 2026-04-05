# Workstream: Predicate-Based Syntax Category

## Motivation

The PER-based syntax category in `TreePER.lean` uses equivalence
relations with quotient morphisms.  On a decidable layer (where every
equality is already decidable at the ambient tree level), equivalence
classes are singletons and the quotient structure is paying for something
we don't use.  The predicate-based alternative replaces `rel : T × T → T`
with `pred : T → T` (a Boolean-valued characteristic function), and
morphisms with raw `T → T` maps satisfying a preservation condition.

Architecturally separate from the PER layer; PER code is preserved for
Layer 2 (undecidable quotients).

## File structure

- `GebLean/TreePredicate.lean` (153 lines): objects, morphisms, category
  instance.  Preservation condition:
  `cfpLift X.pred (map ≫ Y.pred) ≫ boolAnd = X.pred`.
  No quotient on morphisms.
- `GebLean/TreePredicateColimits.lean` (pending): finite coproducts.
- `GebLean/TreePredicateLimits.lean` (pending): finite limits.

## Open architectural concern: morphism uniqueness

Morphisms in `TreePredCat` are raw `T ⟶ T` endomorphisms with a
preservation equation.  Equality of morphisms is equality of the
underlying raw maps.

**Concern**: the preservation condition
`cfpLift X.pred (map ≫ Y.pred) ≫ boolAnd = X.pred`
constrains `map` only where `X.pred` holds (i.e., where `X.pred(x) = ℓ`).
Off the support of `X.pred`, `map` is unconstrained because
`boolAnd(treeFalse, _) = treeFalse` holds regardless.

Consequence: for any coproduct candidate `X ⊕ Y` with copairing
`coprodCase f g`, there can be MULTIPLE morphisms `h : X ⊕ Y ⟶ Z`
satisfying `inl ≫ h = f` and `inr ≫ h = g` — they agree on the
tagged (predicate-satisfying) elements but can differ off them as raw
`T ⟶ T` maps.  Strict categorical uniqueness of the copairing fails.

Similar issue for initial objects (if source predicate is always false,
any map from the initial satisfies preservation, not just one), and for
equalizers.

## Possible resolutions

1. **Quotient morphisms by "agree on X.pred support"**: define an
   equivalence `f ~ g` iff f and g agree wherever X.pred holds.  This is
   simpler than the full PER quotient (no symmetry/transitivity on
   objects) but still involves quotienting.  Most proof-level simpler
   than PER but not quotient-free.
2. **Canonical-form morphisms**: require the underlying map to act as
   identity (or some other canonical form) off the predicate's support.
   Adds a new axiom to every morphism.  Canonical-form-ness needs to be
   preserved by identity and composition.
3. **Weak coproducts**: accept non-uniqueness and work with "existence
   plus commutativity" rather than strict categorical universal
   properties.  Cleaner architecturally but non-standard.
4. **View as subobject category**: objects are subobjects (monos into T),
   morphisms are T-maps that factor through the codomain subobject.  This
   is a standard construction with strict uniqueness.  Requires building
   the subobject category infrastructure.

## Status

- `TreePredicate.lean` skeleton: complete (153 lines, clean build).
- Coproducts construction: in progress, with the uniqueness concern as
  a known risk.
- Decision on architectural resolution: pending.
