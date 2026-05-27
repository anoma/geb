# (Co)End Formulas and Universal Properties Research

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Overview](#overview)
- [Well-Known Formula Correspondences](#well-known-formula-correspondences)
  - [WeightedWedge/Cowedge = Weighted (Co)Limits](#weightedwedgecowedge--weighted-colimits)
  - [StrongRestrictedWedge/Cowedge = (Co)Limits over Category of Elements](#strongrestrictedwedgecowedge--colimits-over-category-of-elements)
  - [RestrictedWedge/Cowedge = Vene's Restricted (Co)Ends](#restrictedwedgecowedge--venes-restricted-coends)
  - [Kan Extension Connection](#kan-extension-connection)
- [Open Research Questions](#open-research-questions)
  - [Q1: Kan Extensions, Adjoints, and Initial Algebras (FORMALIZED)](#q1-kan-extensions-adjoints-and-initial-algebras-formalized)
  - [Q2: Transfer of Terminality/Initiality Across Inclusions](#q2-transfer-of-terminalityinitiality-across-inclusions)
    - [Formalized: Fully Faithful Case](#formalized-fully-faithful-case)
    - [Non-Full Case: Condition on Profunctors](#non-full-case-condition-on-profunctors)
      - [Identified Condition: Weight Maps Jointly Surjective](#identified-condition-weight-maps-jointly-surjective)
    - [Counterexample: WalkingParallelPair](#counterexample-walkingparallelpair)
    - [Formalized Counterexample: Initial Cowedges Differ](#formalized-counterexample-initial-cowedges-differ)
    - [Summary](#summary)
    - [Implication: Weighted (Co)Ends Do Not Capture Initial Algebras](#implication-weighted-coends-do-not-capture-initial-algebras)
  - [Q3: 2-Categorical Structure from Composability](#q3-2-categorical-structure-from-composability)
- [Relationships Between Universal Objects](#relationships-between-universal-objects)
  - [Hierarchy of Inclusions and Universal Properties](#hierarchy-of-inclusions-and-universal-properties)
  - [Comparison Maps (Task #46)](#comparison-maps-task-46)
    - [Analysis](#analysis)
    - [Counterexample: WalkingParallelPair with Constant Profunctor](#counterexample-walkingparallelpair-with-constant-profunctor)
    - [When Do They Coincide?](#when-do-they-coincide)
- [Implementation Status](#implementation-status)
  - [Completed](#completed)
  - [To Implement](#to-implement)
- [References](#references)
  - [Primary Sources](#primary-sources)
  - [nLab References](#nlab-references)
  - [Additional Resources](#additional-resources)
- [Related Files](#related-files)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document tracks research on the categorical semantics of restricted
and weighted (co)wedges, their relationship to well-known (co)end formulas,
and open questions about their structure.

## Overview

We have characterized three levels of (co)wedge structures as standard
(co)wedges over particular profunctors:

| Construction | Profunctor | (Co)End Formula |
| --- | --- | --- |
| `WeightedCowedge W G` | `copowerWeightedProfunctor` | `∫^j W(j) × G(j)` |
| `WeightedWedge W G` | `powerWeightedProfunctor` | `∫_j [W(j), G(j)]` |
| `StrongRestrictedCowedge G H` | `diagElemProf G H` | `colim_{DiagElem H}` |
| `StrongRestrictedWedge G H` | `diagElemProf G H` | `lim_{DiagElem H}` |
| `RestrictedCowedge G H` | `copowerProfunctorProfArg` | `∫^I H(I,I) × G(I,I)` |
| `RestrictedWedge G H` | `powerProfunctorProfArg` | `∫_I [H(I,I), G(I,I)]` |

## Well-Known Formula Correspondences

### WeightedWedge/Cowedge = Weighted (Co)Limits

The most direct correspondence. The standard weighted (co)limit formulas:

- Weighted colimit: `W * F ≅ ∫^{j∈J} W(j) ⋅ F(j)`
- Weighted limit: `{W, F} ≅ ∫_{j∈J} [W(j), F(j)]`

Our constructions:

- `copowerWeightedProfunctor W G` at `j` = `W(j) × G(j)`
- `powerWeightedProfunctor W G` at `j` = `W(j) → G(j)`

These match exactly. WeightedWedge/WeightedCowedge are weighted
limits/colimits expressed via their end/coend formulas.

### StrongRestrictedWedge/Cowedge = (Co)Limits over Category of Elements

Standard result: weighted colimits can be expressed as ordinary colimits
over the category of elements:

`W * F = colim_{(j,w) : El(W)} F(j)`

Our construction:

- `diagElemProf G H = profPullback G (DiagElem.forget H)`
- Coend: `∫^{(A,a) : DiagElem H} G(A,A) = colim_{DiagElem H} (G ∘ forget)`

This is the **structural coend** from Neumann's Paranatural Category
Theory. The paranaturality condition on morphisms in `DiagElem H` ensures
the correct quotient.

### RestrictedWedge/Cowedge = Vene's Restricted (Co)Ends

The formulas:

- End: `∫_I [H(I,I), G(I,I)]` (pointwise power on diagonal)
- Coend: `∫^I H(I,I) × G(I,I)` (pointwise copower on diagonal)

This is a "profunctor-weighted" (co)end where both weight and diagram are
profunctors, integrated only over the diagonal. The universal object is
Vene's restricted coend `Σ(H,G)` for Mendler-style recursion.

### Kan Extension Connection

The left Kan extension formula:

`(Lan_K F)(c) = ∫^d C(K(d), c) × F(d)`

For `K = DiagElem.forget H` and the terminal functor `! : DiagElem H → 1`:

`Lan_! (G ∘ forget) = colim_{DiagElem H} (G ∘ forget) = CostructureIntegral H G`

So `CostructureIntegral H G` is the left Kan extension of the diagonal
restriction of `G` along the terminal functor.

## Open Research Questions

### Q1: Kan Extensions, Adjoints, and Initial Algebras (FORMALIZED)

**Background**: If a functor `U` has a left adjoint `F`, then `F` is the
right Kan extension of the identity along `U`, preserved by `U`:

`F ≅ Ran_U Id` and `U` preserves this Kan extension.

**Observation**: Categories of algebras can be expressed as diagonal element
categories. For a functor `G : C → C`:

- `G-Alg ≌ DiagElem (AlgProf G)`
- The forgetful functor `U : G-Alg → C` corresponds to `DiagElem.forget`
- When `U` has a left adjoint (free algebra), that adjoint is `Ran_U Id`

**Question**: Is there a precise correspondence between:

1. `StructuralEnd (AlgProf G)` (which gives the initial algebra carrier)
2. `Ran_{DiagElem.forget} Id` (right Kan extension of identity on algebras)

**Answer**: Y:  the connection is through `Functor.sections` (the
limit construction in `Type v`).

**Formalized equivalences in `GebLean/ParanatAlg.lean`**:

1. `structuralEndEquivSections` — for any endoprofunctor `F`:
   `StructuralEnd F ≃ (DiagElem.forget F).sections`
   Since limits in `Type v` are computed by sections, this identifies
   the structural end with `lim (DiagElem.forget F)`.

2. `diagElemAlg_forget_eq` — the forgetful functors agree:
   `DiagElem.forget (AlgProf G) = diagElemToAlgFunctor G ⋙ Algebra.forget G`

3. `algSectionsEquivStructuralEnd` — combining (1) and (2):
   algebra forgetful functor sections ≃ structural end

4. Dual: `diagElemCoalg_forget_eq` and `coalgSectionsEquivStructuralEnd`
   for `CoalgProf G` and `Coalgebra.forget G`.

**The full chain** (for algebras, composing with existing results):

```text
(diagElemToAlgFunctor G ⋙ Algebra.forget G).sections
  ≃ StructuralEnd (AlgProf G)      -- algSectionsEquivStructuralEnd
  ≃ μG.a                            -- initialAlgebraStructuralEndEquiv
```

This says: the limit of the diagram of G-algebras projected to their
carriers is the carrier of the initial algebra.

**Formal limit universal property**: The structural end also satisfies
mathlib's formal `IsLimit` universal property:

- `structuralEndLimitCone F` — a `Limits.Cone` for
  `DiagElem.forget F ⋙ uliftFunctor.{v+1}` with cone point
  `StructuralEnd F` (universe-lifted to match `DiagElem F : Type (v+1)`)
- `structuralEndLimitCone_isLimit F` — the `Limits.IsLimit` proof:
  for any cone `s` over the lifted forgetful functor, there is a
  unique morphism `s.pt → StructuralEnd F` commuting with all
  projections
- `structuralCoendColimitCocone F` — a `Limits.Cocone` for the same
  lifted functor with cocone point `StructuralCoend F`, where
  coprojections inject via `CostructureIntegral.mk`
- `structuralCoendColimitCocone_isColimit F` — the `Limits.IsColimit`
  proof: for any cocone `s`, there is a unique morphism
  `StructuralCoend F → s.pt` commuting with all coprojections

**Relationship to Kan extensions**: The right Kan extension
`(Ran_U Id)(c)` computes (pointwise) as
`lim (StructuredArrow.proj c U ⋙ Id)`, which is a limit over a slice
category. When `c = μG.a`, this limit gives the full algebra `μG`, not
just its carrier. The structural end gives only the carrier `μG.a`,
which is the carrier projection of the Kan extension value

### Q2: Transfer of Terminality/Initiality Across Inclusions

We have a hierarchy of categories with inclusions:

```text
WeightedWedge ──(faithful, not full)──> StrongRestrictedWedge
                                              │
                                        (fully faithful)
                                              │
                                              v
                                       RestrictedWedge
```

**Known results**:

1. `StrongRestrictedWedge.inclusion : StrongRestrictedWedge → RestrictedWedge`
   is fully faithful.
2. `strongRestrictionFunctor : WeightedWedge → StrongRestrictedWedge` is
   faithful but NOT full.

#### Formalized: Fully Faithful Case

**General theorem for full subcategories**: If `F : C → D` is fully
faithful and `F(c)` is terminal in `D`, then `c` is terminal in `C`.

**Formalized in `GebLean/Weighted.lean`**:

```lean
def isStrongRestrictedEnd_of_isRestrictedEnd
    (G : Cᵒᵖ ⥤ C ⥤ D) (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (c : StrongRestrictedWedge G H)
    (h : IsRestrictedEnd G H c.toRestrictedWedge) :
    IsStrongRestrictedEnd G H c

def isStrongRestrictedCoend_of_isRestrictedCoend
    (G : Cᵒᵖ ⥤ C ⥤ D) (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (c : StrongRestrictedCowedge G H)
    (h : IsRestrictedCoend G H c.toRestrictedCowedge) :
    IsStrongRestrictedCoend G H c
```

These use the explicit preimage from `inclusion_fullyFaithful` to remain
computable (avoiding mathlib's `Functor.preimage`).

#### Non-Full Case: Condition on Profunctors

**Question for non-full inclusions**: Under what conditions can terminality
transfer from `StrongRestrictedWedge` to `WeightedWedge`?

##### Identified Condition: Weight Maps Jointly Surjective

For the restriction functor to be full (and thus for terminality to
transfer automatically), the weight maps from diagonals must be jointly
surjective. Formally:

For every co-twisted arrow `tw` and weight element `w ∈ H(tw)`, there
should exist:

- An identity co-twisted arrow `id(A)` for some object `A`
- A morphism `m : tw → id(A)` in `CoTwistedArrow C`
- A diagonal weight element `w' ∈ diagApp H A`
- Such that `H.map m.op w' = w`

**Theorem (`commutativity_from_identity_image`)**: If a morphism commutes
with legs at identity co-twisted arrows, it also commutes at weight
elements in the image of weight maps from diagonals.

**Consequence**: When weight maps are jointly surjective, every morphism
in `StrongRestrictedCowedge` lifts to `WeightedCowedge`, making the
restriction functor full and enabling automatic transfer.

#### Counterexample: WalkingParallelPair

**Theorem (`wpp_weight_maps_not_surjective`)**: For `WalkingParallelPair`
with the Hom-profunctor, weight maps from diagonals are NOT jointly
surjective.

The category `WalkingParallelPair` has:

- Objects: `zero`, `one`
- Morphisms: `left, right : zero ⟶ one` plus identities

For the Hom-profunctor:

- `Hom(zero, zero) = {id}` (singleton)
- `Hom(one, one) = {id}` (singleton)
- `Hom(zero, one) = {left, right}` (two elements)

Weight maps from diagonals both send to `left`:

- `id_zero ≫ left = left`
- `left ≫ id_one = left`

This leaves `right` unreachable from any diagonal.

**Theorem (`cValued_strongRestrictionFunctor_not_full`)**: The strong
restriction functor is not full for this profunctor.

#### Formalized Counterexample: Initial Cowedges Differ

**Theorem (`wppInitialCowedges_pt_not_equiv`)**: For `WalkingParallelPair`
with the Hom-profunctor and constant profunctor at `Unit`:

- The initial `StrongRestrictedCowedge` has `pt ≃ Unit`
  (via `costructureIntegralCowedge` and `wppCostructureIntegralEquivT`)
- The initial `RestrictedCowedge` has `pt = Unit + Unit`
  (via `wppRestrictedCowedgeSumT` and `wppRestrictedCowedgeSumT_isInitial`)
- These are NOT equivalent (`wppUnitSumUnit_not_equiv_Unit`)

**Mechanism**: Dinaturality conditions involve `H(one, zero) = ∅`, making
them vacuous. Paranaturality uses `DiagElem` morphisms which exist (via
`left` and `right`). So the paranaturality quotient identifies elements
that dinaturality leaves distinct.

#### Summary

| Inclusion | Full? | Transfer of Terminal/Initial |
| --- | --- | --- |
| `Strong → Restricted` | Y | Automatic |
| `Weighted → Strong` | N (in general) | If: weight maps jointly surjective |

**Dual**: The same analysis applies for initial objects and cowedges.

#### Implication: Weighted (Co)Ends Do Not Capture Initial Algebras

**Conclusion**: Initial algebras correspond to `StructureIntegral`/
`CostructureIntegral`, which are terminal/initial in the
`StrongRestrictedWedge`/`Cowedge` categories. Since:

1. `StrongRestricted` ≠ `Weighted` (different initial objects, as shown)
2. `Weighted → StrongRestricted` is faithful but not full
3. Initial algebras live in `StrongRestricted`, not `Weighted`

The conjectured weighted (co)end formulas for initial algebras (Church
numerals, etc.) do NOT hold. The `WeightedWedge`/`Cowedge` categories
are "too small" — they lack morphisms needed to identify the correct
universal object.

### Q3: 2-Categorical Structure from Composability

**Background**:

- Paranatural transformations compose (unlike dinatural transformations).
- Natural transformations also compose (as in WeightedWedge/Cowedge).
- Dinatural transformations generally do NOT compose.

**Observation**: `StrongRestrictedWedge` and `WeightedWedge` both involve
composable transformation types, while `RestrictedWedge` does not.

**Question**: Does composability enable additional 2-categorical structure
on `StrongRestrictedWedge`/`WeightedWedge` that is unavailable for
`RestrictedWedge`?

**Possible structures to investigate**:

1. **2-cells between wedge morphisms**: Can we define natural
   transformations or modifications between wedge morphisms?
2. **Horizontal composition**: Given wedges `w₁, w₂, w₃` and morphisms
   `f : w₁ → w₂`, `g : w₂ → w₃`, the composite `g ∘ f` exists. But is
   there meaningful horizontal composition?
3. **Bicategorical structure**: Could the categories of strong restricted
   or weighted (co)wedges form bicategories with appropriate 2-cells?
4. **Double categorical structure**: The combination of profunctor
   composition and (co)wedge morphisms might form a double category.

**Connection to paranaturality**:

- Paranatural transformations form a category `Para(C)` with composition.
- This category has its own (co)limits and universal properties.
- The structural (co)ends are computed in this category.
- Does the 2-categorical structure of `Para(C)` (if any) induce structure
  on `StrongRestrictedWedge`/`Cowedge`?

**Contrast with RestrictedWedge**:

- Dinatural transformations do not compose in general.
- The category `RestrictedWedge` has objects and morphisms, but the
  morphisms are just apex morphisms satisfying compatibility.
- There may be no natural notion of 2-cell.

**Analysis: Para(C) as a 2-category?**

The category `Para(C)` of profunctors and paranatural transformations:

- 0-cells: Objects of C (or perhaps profunctors C^op × C → Set)
- 1-cells: Paranatural transformations
- 2-cells: ???

For `Para(C)` to be a 2-category, we'd need "modifications" between
paranatural transformations. A modification `m : α ⇒ β` between
`α, β : F → G` would be a family of morphisms satisfying coherence.

**Observation**: In the standard setting, modifications between natural
transformations exist (giving Cat as a 2-category). The question is whether
analogous modifications exist for paranaturals.

**Potential 2-categorical structure on StrongRestrictedWedge**:

Given wedges `w₁, w₂ : StrongRestrictedWedge G H` with the same apex `pt`,
a 2-cell `w₁ ⇒ w₂` could be a family witnessing that the two paranatural
families are "related" in some coherent way.

Since both families are `pt → G(A,A)` for each `A` and `a : H(A,A)`, a
2-cell might be a "homotopy" between them — but in Set, this would just
mean equality.

**Higher structure might appear**:

1. If we work in a category with non-trivial 2-cells (like Cat or a
   2-category), then modifications would give genuine 2-categorical
   structure.

2. The profunctor bicategory `Prof` has profunctors as 1-cells and
   natural transformations as 2-cells. The composition of paranaturals
   might fit into this framework.

3. Double categorical structure: with profunctors horizontally, objects
   vertically, and (co)wedge morphisms as squares.

**To investigate**:

- Whether `Para(C)` admits a natural 2-category structure
- Whether StrongRestrictedWedge inherits this structure
- Connection to the profunctor bicategory `Prof`
- Possible double categorical structures

## Relationships Between Universal Objects

### Hierarchy of Inclusions and Universal Properties

```text
                    ┌─────────────────────────────────────┐
                    │     WeightedWedge / Cowedge         │
                    │   (naturality at all tw. arrows)    │
                    └─────────────┬───────────────────────┘
                                  │ strongRestrictionFunctor
                                  │ (faithful, NOT full)
                                  v
                    ┌─────────────────────────────────────┐
                    │ StrongRestrictedWedge / Cowedge     │
                    │      (paranaturality)               │
                    │  Universal: StructureIntegral /     │
                    │             CostructureIntegral     │
                    └─────────────┬───────────────────────┘
                                  │ inclusion
                                  │ (fully faithful)
                                  v
                    ┌─────────────────────────────────────┐
                    │   RestrictedWedge / Cowedge         │
                    │       (dinaturality)                │
                    │  Universal: Vene's restricted       │
                    │             (co)end Σ(H,G)          │
                    └─────────────────────────────────────┘
```

### Comparison Maps (Task #46)

Since `StrongRestricted → Restricted` is fully faithful, initiality in the
larger category (RestrictedCowedge) implies initiality in the smaller
category (StrongRestrictedCowedge). This gives a canonical comparison map:

`Σ(H,G) → CostructureIntegral H G`

(from the initial RestrictedCowedge to the initial StrongRestrictedCowedge)

**Question**: Is this comparison an isomorphism?

**Answer**: NO, not in general.

#### Analysis

The comparison map exists by initiality of `Σ(H,G)`. For it to be an
isomorphism, `CostructureIntegral H G` would also need to be initial in
`RestrictedCowedge`.

A morphism `h : CostructureIntegral H G → c.pt` (for RestrictedCowedge `c`)
must satisfy:

```lean
h (CostructureIntegral.mk ⟨A, a⟩ g) = c.family A a g
```

This uniquely determines `h` on generators. But `CostructureIntegral` is a
quotient by the **paranaturality** relation, which identifies:

```text
mk x (contravAction f ψ) ~ mk y (covAction f ψ)
```

for morphisms `f : x → y` in `DiagElem H`.

For `h` to be well-defined, the target `c` must respect this identification.
A merely **dinatural** family doesn't necessarily satisfy this stronger
condition.

#### Counterexample: WalkingParallelPair with Constant Profunctor

**Setup**:

- `C = WalkingParallelPair` (objects: `zero`, `one`; morphisms: `left, right`)
- `H = Hom` profunctor
- `G = const T` (constant profunctor at some type T)

**DiagElem H**:

- Objects: `(zero, id_zero)` and `(one, id_one)`
- Morphisms: `(zero, id_zero) → (one, id_one)` via `left` and `right`

**CostructureIntegral H G** (initial StrongRestrictedCowedge):

- Generators: `(zero, t)` and `(one, t)` for `t : T`
- Paranaturality quotient: since there exist morphisms in DiagElem H from
  `(zero, id_zero)` to `(one, id_one)`, and G is constant (so contrav/cov
  actions are identity), we get `(zero, t) ~ (one, t)` for all `t`
- Result: **CostructureIntegral ≅ T**

**Initial RestrictedCowedge** (Vene's `Σ(H,G)`):

- Dinaturality at `left, right : zero → one` involves elements of
  `H(one, zero) = ∅` (no morphisms from one to zero)
- So dinaturality is **vacuously satisfied** - no identifications!
- Result: **Σ(H,G) ≅ T + T** (disjoint union)

**Conclusion**: For non-empty `T`, we have `T ≇ T + T`, so the comparison
map `T + T → T` is NOT an isomorphism. It's a surjection (collapsing two
copies), not an injection.

#### When Do They Coincide?

The comparison map is an isomorphism when every dinaturality identification
is also a paranaturality identification. This happens when:

1. **H(one, zero) generates enough identifications**: The off-diagonal
   elements used in dinaturality must generate the same equivalence as
   the DiagElem morphisms used in paranaturality.

2. **DiagElem H has no non-trivial morphisms**: If DiagElem H is discrete
   (only identity morphisms), then paranaturality adds no identifications
   beyond dinaturality.

3. **G is "faithful enough"**: If the contrav/cov actions of G distinguish
   elements that are related by DiagElem morphisms, then paranaturality
   may collapse to dinaturality.

## Implementation Status

### Completed

- `restrictedWedgePowerEquiv` / `restrictedCowedgeCopowerEquiv`
- `strongRestrictedWedgeEquiv` / `strongRestrictedCowedgeEquiv`
- `weightedWedgeWedgeEquiv` / `weightedCowedgeCowedgeEquiv`
- `structureIntegralWedge_isTerminal` / `costructureIntegralCowedge_isInitial`
- Transfer theorems via equivalences
- `isStrongRestrictedEnd_of_isRestrictedEnd` (fully faithful case)
- `isStrongRestrictedCoend_of_isRestrictedCoend` (fully faithful case)
- `wpp_weight_maps_not_surjective` (counterexample for non-full case)
- `cValued_strongRestrictionFunctor_not_full` (non-fullness proof)

### To Implement

- Formalize WPP counterexample for comparison map (Task #46 - analysis complete)
- Investigation of Kan extension connection (Q1)
- 2-categorical structure exploration (Q3)

## References

### Primary Sources

- Neumann, J. (2023). [Paranatural Category Theory](https://arxiv.org/abs/2307.09289).
  arXiv:2307.09289.
- Vene, V. (2000). Categorical Programming with Inductive and Coinductive
  Types. PhD thesis, University of Tartu.
- Loregian, F. (2021). [Coend Calculus](https://arxiv.org/abs/1501.02503).
  Cambridge University Press.

### nLab References

- [end](https://ncatlab.org/nlab/show/end)
- [weighted colimit](https://ncatlab.org/nlab/show/weighted+colimit)
- [Kan extension](https://ncatlab.org/nlab/show/Kan+extension)
- [dinatural transformation](https://ncatlab.org/nlab/show/dinatural+transformation)
- [category of elements](https://en.wikipedia.org/wiki/Category_of_elements)

### Additional Resources

- [Bartosz Milewski: Weighted Colimits](https://bartoszmilewski.com/2020/07/20/weighted-colimits/)
- Kelly, G.M. (1982). Basic Concepts of Enriched Category Theory.
  Cambridge University Press.

## Related Files

- `GebLean/Weighted.lean` - Main (co)wedge definitions and equivalences
- `GebLean/Paranatural.lean` - DiagElem, StructureIntegral, CostructureIntegral
- `GebLean/Utilities/PowersAndCopowers.lean` - Weighted profunctor equivalences
- `GebLean/WeightedAlg.lean` - AlgProf, CoalgProf, algebra categories
- `docs/restricted-weighted-wedge-hierarchy.md` - Summary of equivalences
- `docs/restricted-coends.md` - Vene's original definitions
