# Enriched Hom Unification

This document describes how the categorical constructions in this codebase
unify under the Cat-enriched hom-bifunctor.

## The Cat-Enriched Hom-Functor

The internal hom in Cat is the bifunctor:

```text
[-, -] : Cat^op x Cat -> Cat
```

This sends a pair of categories (A, B) to the functor category [A, B]. It is:

- Contravariant in the first argument (precomposition)
- Covariant in the second argument (postcomposition)

This makes Cat a Cartesian closed 2-category.

## Derivation Hierarchy

All major constructions in this codebase derive from [-, -]:

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

## FamilyCat as Enriched Hom

`FamilyCat D X` in `GebLean/Utilities/Families.lean` is defined as:

```lean
def FamilyCat (C : Type) [Category C] (X : Type) : Cat :=
  Cat.of (forall _ : X, C)
```

This is precisely `[Discrete(X), D]`, the functor category from the discrete
category on X to D. It is the specialization of the Cat-enriched hom to
discrete first argument.

The equivalence `familySliceEquiv : FamilyCat Type Y = Over Y` in
`GebLean/Polynomial.lean` is the fundamental theorem connecting:

- Type-indexed families (dependent types)
- Slice categories (fibrations)

## Grothendieck as Category of Elements

The Grothendieck construction for F : C -> Cat produces the "total category":

```text
Objects of Grothendieck(F): pairs (c, x) where c in C and x in F(c)
```

When F = [-, D] : Cat^op -> Cat (fixing the second argument of [-,-]):

```text
Grothendieck([-, D]) = category of functors into D with varying domain
```

When F = Hom_C : C^op x C -> Set (the Set-enriched hom):

```text
Grothendieck(Hom_C) = TwArr(C)   (twisted arrow category)
```

## Twisted Arrow Categories

The twisted arrow category TwArr(C) has:

- Objects: morphisms f : A -> B in C
- Morphisms (f : A -> B) -> (g : A' -> B'): pairs (alpha, beta) with
  alpha : A' -> A, beta : B -> B', and g = beta . f . alpha

This "twists" by going:

- Backwards on domain (contravariant)
- Forwards on codomain (covariant)

The Cat-enriched version Arr(Cat) = Grothendieck([-, -]) has:

- Objects: functors F : A -> B
- Morphisms: pairs of functors plus natural transformation

## Polynomial Functors as Double Grothendieck

A polynomial functor P : Over I -> Over X corresponds to a span I <- E -> X.

This involves TWO layers of the [-,-] construction:

1. Position layer: [Discrete(I), Type] = Over I
2. Direction layer: For each position, fibers determining output

The double Grothendieck captures both layers, giving the polynomial category
structure in `CoprodCovarRepCat(Over X)`.

## The Enrichment Hierarchy

### Level 1: Set-Enriched (1-Categorical)

- Hom-sets are sets
- TwArr(C) = Grothendieck(Hom_C : C^op x C -> Set)
- Presheaves: [C^op, Set]
- Copresheaves: [C, Set]

### Level 2: Cat-Enriched (2-Categorical)

- Hom-objects are categories
- [A, B] = functor category
- Arr(Cat) = Grothendieck([-, -])
- Natural transformations are 2-morphisms

### Level 3: Copresheaf-Enriched (Judgment-Sensitive)

For a judgment category J:

- Hom-objects are copresheaves [J, Type]
- Morphisms carry "witnesses" at each judgment level
- The Cat <-> [J, Type] adjunction transfers enriched structure

## Intro/Elim Rules as Universal Properties

The universal properties of Grothendieck constructions correspond to
type-theoretic intro/elim rules:

| Rule | Type Theory | Category Theory |
| ---- | ----------- | --------------- |
| Intro | Sigma-introduction | functorTo |
| Elim | Pattern match | functorFrom |
| Transform | Function on Sigma | functorBetween |

These are implemented in `GebLean/Utilities/Grothendieck.lean`:

- `FunctorToData` / `functorTo`: introduction rule
- `FunctorFromData` / `functorFrom`: elimination rule
- Both compose for transformation (functorBetween)

## Connection to Adjunctions

### The Sigma-BaseChange-Pi Triple

For f : A -> B, the triple adjunction:

```text
Sigma_f -| f* -| Pi_f
```

Where:

- Sigma_f : Over A -> Over B (dependent sum, pushforward)
- f* : Over B -> Over A (base change, pullback)
- Pi_f : Over A -> Over B (dependent product)

This adjunction powers polynomial functor evaluation.

### The Cat-Copresheaf Adjunction

For judgment category J:

```text
Free -| Underlying : Cat <-> [J, Type]
```

This transfers Cat-enriched structure to copresheaf-enriched structure,
making intro/elim rules "judgment-sensitive."

## Implications for Development

### Grothendieck Refactoring

The refactoring described in `.session/workstreams/grothendieck-refactoring.md`
implements the Cat-enriched universal properties. By expressing polynomial
operations via Grothendieck intro/elim rules:

1. Naturality becomes automatic (from universal property)
2. Dependent type manipulations are encapsulated
3. Operations compose via the enriched hom structure

### Unification of Codebase

The files:

- `GebLean/Utilities/Families.lean` (FamilyCat = [-,-] with discrete domain)
- `GebLean/Utilities/TwistedArrow.lean` (TwArr = Grothendieck(Hom))
- `GebLean/Utilities/TwArrPresheaf.lean` (presheaves on TwArr)
- `GebLean/Utilities/Grothendieck.lean` (general Grothendieck)

All implement aspects of the same underlying structure: operations on the
Cat-enriched hom-bifunctor and its Grothendieck construction.

## References

- nLab: Internal hom
- nLab: Grothendieck construction
- nLab: Twisted arrow category
- nLab: Enriched category theory
