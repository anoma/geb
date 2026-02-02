# Weighted (Co)Ends vs Paranatural Transformations in Algebra

This document describes a research investigation into whether weighted (co)ends
can provide equivalent formalizations to the three main algebraic results that
justify the use of paranatural transformations in theoretical computer science.

## Background and Motivation

### Paranatural Transformations in Algebraic Semantics

Paranatural transformations (a.k.a. strong dinatural transformations), as
developed by researchers such as Uustalu and Neumann, provide a categorical
framework for understanding polymorphism and recursive data types. The theory
has three primary applications that justify its use:

1. **Initial algebras of endofunctors**: Elements of an initial F-algebra
   correspond to paranatural transformations from the algebra profunctor to the
   identity profunctor.

2. **Terminal coalgebras of endofunctors**: Elements of a terminal F-coalgebra
   correspond to elements of the structural coend of the coalgebra profunctor.

3. **Church numerals**: The natural numbers are isomorphic to the set of
   endo-paranatural transformations of the hom-functor, providing a
   category-theoretic formalization of Church numerals.

### Weighted (Co)Ends: A Generalization

In `Weighted.lean`, we have developed a theory of "weighted (co)ends" which
simultaneously generalizes:

- **Weighted (co)limits**: Limits and colimits parameterized by a weight
  functor
- **(Co)ends**: Universal constructions for profunctors

This combination has not been explicitly formalized before, though it is a
straightforward consequence of established concepts.

### Research Question

**Can weighted (co)ends provide equivalent formulations for the three main
paranatural transformation results?**

If so, weighted (co)ends would subsume paranatural transformations for these
use cases because:

1. Weighted (co)ends are more directly derived from established categorical
   concepts (weighted limits and ends)
2. They can be expressed in strictly more general contexts
3. Neumann has discovered cases where paranatural transformations diverge from
   the "parametricity" expected in programming semantics (outside these three
   cases)

## Existing Formalizations

### In ParanatAlg.lean

#### Initial Algebra Result

For an endofunctor `F : Type v ⥤ Type v` with initial algebra `μF`:

```lean
def initialAlgebraStructuralEndEquiv (F : Type v ⥤ Type v)
    (μF : Endofunctor.Algebra F) (hμF : IsInitial μF) :
    μF.a ≃ StructuralEnd (AlgProf F)
```

Where `AlgProf F : Typeᵒᵖ ⥤ Type ⥤ Type v` is the algebra profunctor
`(A, B) ↦ (F A → B)`, and `StructuralEnd` is the type of paranatural
transformations to the identity profunctor.

#### Terminal Coalgebra Result

For an endofunctor `F : Type v ⥤ Type v` with terminal coalgebra `νF`:

```lean
def terminalCoalgebraStructuralCoendEquiv (F : Type v ⥤ Type v)
    (νF : Endofunctor.Coalgebra F) (hνF : IsTerminal νF) :
    νF.V ≃ StructuralCoend (CoalgProf F)
```

Where `CoalgProf F : Typeᵒᵖ ⥤ Type ⥤ Type v` is the coalgebra profunctor
`(A, B) ↦ (A → F B)`, and `StructuralCoend` is the coend quotient.

### In DinaturalNumbers.lean

#### Church Numerals Result

```lean
def dinaturalNumbersEquiv : ℕ ≃ Paranat HomProf HomProf
```

Where `HomProf : Typeᵒᵖ ⥤ Type ⥤ Type` is the hom-profunctor
`(A, B) ↦ (A → B)`, and `Paranat HomProf HomProf` is the type of
endo-paranatural transformations.

### In WeightedAlg.lean

#### Mendler-Lambek Correspondence

For a C-valued endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C`:

```lean
def mendlerLambekEquiv [HasAllHomToProfCoends G] :
    MendlerAlgebra G ≌ ConventionalAlgebra (GExtFunctor G)
```

This establishes an equivalence between Mendler-style algebras (defined via
paranatural transformations from `HomToProf pt` to `G ⇓ pt`) and conventional
algebras of the functor `GExtFunctor` (defined via restricted coends).

## Weighted (Co)End Formulations

### Supporting Infrastructure

#### In Weighted.lean

- `WeightedCowedge W P`: Weighted cowedge with data at ALL co-twisted arrows
- `RestrictedCowedge G H`: H-restricted G-cowedge (diagonal data only)
- `restrictionFunctor`: `WeightedCowedge H G ⥤ RestrictedCowedge G H`
  (faithful but not full)

#### In PowersAndCopowers.lean

Mathematical foundations for expressing weighted (co)ends via:

- Powers and copowers in enriched categories
- Explicit formulas when the enriching category has suitable structure
- Relationships between weighted limits and ends

#### In RestrictedCoendAsColimit.lean

- Restricted coends expressed as colimits over co-twisted arrow categories
- Relationships between different cowedge notions

### Known Relationships

From `weighted-vs-strong-restricted.md`:

1. **WeightedCowedge → StrongRestrictedCowedge**: Faithful but NOT full
2. **WeightedCowedge → RestrictedCowedge**: Faithful but NOT full
3. **StrongRestrictedCowedge → WeightedCowedge**: No inclusion exists
4. **RestrictedCowedge → StrongRestrictedCowedge**: No inclusion exists

**Conclusion**: In the general case, `WeightedCowedge` cannot substitute for
`RestrictedCowedge`. However, the question remains whether they coincide for
the specific cases of initial algebras, terminal coalgebras, and Church
numerals.

## Research Questions

### Q1: Weighted Formulation for Initial Algebras

Can we express the result `μF.a ≃ StructuralEnd (AlgProf F)` as a weighted
coend?

**Approach**: The algebra profunctor `AlgProf F` can be weighted by a suitable
profunctor (perhaps `HomToProf μF.a`). The structural end might coincide with
a weighted end over the co-twisted arrow category.

**Observation**: The existing `extendRestrictedCowedge` in `WeightedAlg.lean`
shows how to extend Mendler algebra data to weighted cowedge data when the
weight is `HomToProf pt`.

### Q2: Weighted Formulation for Terminal Coalgebras

Can we express the result `νF.V ≃ StructuralCoend (CoalgProf F)` as a weighted
coend?

**Approach**: The structural coend has a "reversed directionality" compared to
standard coends. This is captured by the quotient structure where elements are
identified based on mapping TO off-diagonal positions (not FROM them).

### Q3: Weighted Formulation for Church Numerals

Can we express the result `ℕ ≃ Paranat HomProf HomProf` as a weighted
(co)end?

**Approach**: Endo-paranatural transformations of `HomProf` have components
`η_A : (A → A) → (A → A)` satisfying naturality. This might correspond to a
weighted end where the weight and diagram are both `HomProf`.

### Q4: Universal Property Comparison

When both formulations exist:

- Does the weighted coend have the same universal property as the structural
  coend?
- Are the resulting types naturally isomorphic?

## Mathematical References

### On Paranatural Transformations

- Mulry, "Strong Monads, Algebras and Fixed Points" (1992) - Original
  definition of strong dinaturality
- Neumann, "Paranatural Category Theory" (2023, arXiv:2307.09289) - Confirms
  paranaturality = strong dinaturality, discusses divergence from parametricity
- Eppendahl, "Parametricity and Mulry's Strong Dinaturality" (1999)
- Vene, "Parametricity and Strong Dinaturality" (2006)

### On Weighted Limits and (Co)Ends

- Kelly, "Basic Concepts of Enriched Category Theory" - Foundational text on
  weighted limits
- nLab, "weighted limit" - <https://ncatlab.org/nlab/show/weighted+limit>
- nLab, "end" - <https://ncatlab.org/nlab/show/end>

### On Mendler-Style Algebras

- Uustalu, "Mendler-style Inductive Types, Categorically" - Categorified
  Mendler algebras
- Vene, "Categorical Programming with Inductive and Coinductive Types" -
  Mendler-Lambek correspondence (sections 5.3-5.7)

### On Parametricity Divergence

Neumann's work identifies cases where paranaturality diverges from the "free
theorem" behavior expected from parametric polymorphism. The counterexample
type `((X → X) → X) → X` exhibits this divergence. See
`.session/workstreams/paranatural-investigations.md` for detailed analysis.

## Codebase File Map

### Core Paranatural Theory

| File | Contents |
| ---- | -------- |
| `Paranatural.lean` | `Paranat`, `StructuralEnd`, `StructuralCoend` |
| `ParanatAlg.lean` | `AlgProf`, `CoalgProf`, initial/terminal |
| `DinaturalNumbers.lean` | Church numerals equivalence |

### Weighted (Co)End Theory

| File | Contents |
| ---- | -------- |
| `Weighted.lean` | `WeightedCowedge`, `RestrictedCowedge` |
| `WeightedAlg.lean` | `MendlerAlgebra`, `HomToProf` |
| `RestrictedCoendAsColimit.lean` | Restricted coend as colimit |
| `Utilities/PowersAndCopowers.lean` | Powers, copowers |

### Utility Files

| File | Contents |
| ---- | -------- |
| `Utilities/TwArrPresheaf.lean` | Profunctor on twisted arrows |
| `Utilities/CoTwistedArrow.lean` | Co-twisted arrow category |

## Progress and Findings

### Completed

- Mendler-Lambek correspondence formalized in `WeightedAlg.lean`
- Restriction functor `WeightedCowedge → RestrictedCowedge` proven faithful
  but not full
- Extension functor `extendRestrictedCowedge` for `HomToProf` weight

### In Progress

- Investigation of weighted formulations for initial algebras
- Investigation of weighted formulations for terminal coalgebras
- Investigation of weighted formulations for Church numerals

### Open Questions

1. For which weights W does `WeightedCowedge W G` coincide with
   `RestrictedCowedge G W`?

2. Is there a general characterization of when weighted and restricted coends
   agree?

3. Can the structural coend's "reversed directionality" be captured by a
   weighted construction with an appropriate weight?
