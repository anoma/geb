# Paranatural Category Theory Investigations

## Status: Active

## Questions to Investigate

### 1. Dialgebra Category in Mathlib

Does mathlib have a dialgebra category? If so:

- Show equivalence between that and the category of diagonal elements for
  the dialgebra profunctor (in ParanatAlg.lean)
- This parallels what we did for algebra and coalgebra profunctors
- Show that when input functors are endofunctors and one is identity, the
  dialgebra profunctor is naturally isomorphic to the algebra or coalgebra
  profunctor (depending on which endofunctor is identity)

### 2. Structure/Costructure Integrals as Ends/Coends

The current form of structure and costructure integrals (as equalizers and
coequalizers) looks like they may be Type-valued ends and coends.

- Work out if this is true
- If so, identify exactly which profunctors on which categories (probably
  categories of diagonal elements?) they are the ends and coends of

### 3. Wedges and Cowedges as Diagonal Elements

Can we express wedges and cowedges as categories of diagonal elements of
some profunctor? This would mean:

- Ends become terminal objects in some category of diagonal elements
- Coends become initial objects in some category of diagonal elements

### 4. Parametricity vs Paranaturality Divergence

Reference: docs/updates-on-paranatural-category-theory-*.pdf (abstract and
slideshow)

Page 10 slide "Divergence between strong dinaturality and parametricity"
shows a case where the "free theorem" from parametric polymorphism differs
from what we get from paranaturality (strong dinaturality).

Questions:

- Given our work on paranaturality and categories of diagonal elements,
  can we understand what's wrong and what would be right?
- Paranaturality is not always correct, but works in important cases
  (Church numerals, initial algebras, terminal coalgebras)
- What is the right category-theoretic notion of parametricity?
- Can we identify possibilities and rank them by likelihood of correctness?

## Context Files

- GebLean/Paranatural.lean - Core paranatural definitions
- GebLean/ParanatAlg.lean - Algebra/coalgebra/dialgebra profunctors
- GebLean/HexagonCat.lean - Hexagon category and profunctor-dialgebra
- GebLean/DinaturalNumbers.lean - Church numerals application
- docs/updates-on-paranatural-category-theory-*.pdf - Problem descriptions

## Progress

(To be updated as investigation proceeds)
