# PRA Universal Morphisms Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax
> for tracking.

**Goal:** Implement universal morphisms, composition,
algebras, and double-category structure for presheaf
PRA functors, generalizing the existing polynomial
functor infrastructure from slice categories to
presheaf categories.

**Architecture:** Each PRA decomposes via
`FunctorToData` into two presheaf-category
components:

- **Positions:** `praPositionsPresheaf P :
  Jᵒᵖ ⥤ Type w'` — a presheaf on `J`
- **Directions:** `praDirectionsAtFunctor :
  (praPositionsPresheaf P).ElementsPre ⥤
  (Iᵒᵖ ⥤ Type w_I)` — a presheaf-valued functor
  on the category of elements of positions

Both components live in (co)complete categories
(presheaf categories and Type). Universal
morphisms in `PresheafPRACat I J` are computed
from universal morphisms in these components,
following the position/direction duality pattern
from `PolyBetweenCat`:

- **Limits:** limits on positions, colimits on
  directions
- **Colimits:** colimits on positions, limits on
  directions

This replaces the previous approach of "define at
`CoprodCovarRepCat` level, then lift." That
approach fails because `CoprodCovarRepCat C` does
not always have colimits (they depend on
properties of `C`). The presheaf decomposition
gives unconditional (co)completeness.

The inverse of the decomposition — reassembling a
PRA from position and direction data — uses
`functorTo` (from `FunctorToData`) applied to
`familyFunctor`.

**Tech Stack:** Lean 4, mathlib (category theory,
presheaf categories, Grothendieck construction,
category of elements, W-types), existing GebLean
infrastructure (polynomial functors, PRA
definitions, `FunctorToData`/`functorToDataIsoCat`,
`praPositionsNat`, `praDirectionsAtFunctor`).

---

## Existing Infrastructure (Reference)

### PRA Decomposition (PresheafPRA.lean)

| Definition | Type | Role |
| ---------- | ---- | ---- |
| `PresheafPRACat I J` | `Cat` | PRA category |
| `praPositionsNat` | `...⥤ (Jᵒᵖ ⥤ Type w')` | Position presheaf |
| `praDirectionsAtFunctor` | `Elem(A)ᵒᵖ ⥤ PSh(I)` | Directions |
| `praEvalAtFunctor` | `...⥤ (PSh(I) ⥤ PSh(J))` | Evaluation |

### Grothendieck Data (Utilities/Grothendieck.lean)

| Definition | Type | Role |
| ---------- | ---- | ---- |
| `FunctorToData F` | structure | Decomposed functor |
| `functorTo F data` | `D ⥤ Groth F` | Reassembly |
| `ofFunctor F G` | `FunctorToData F` | Decomposition |
| `functorToDataIsoCat` | `... ≅Cat ...` | Categorical iso |
| `NatTransToData` | structure | Decomposed nat trans |

### Existing PolyBetween Pattern (PolyUMorph.lean)

| Construction | Positions | Directions |
| ------------ | --------- | ---------- |
| Product `∏_k P_k` | `∏_k I_k(y)` | `∐_k F_k(y, p_k)` |
| Coproduct `∐_k P_k` | `∐_k I_k(y)` | `F_k(y, i_k)` |
| Equalizer `eq(f,g)` | `{i \| f(i)=g(i)}` | coequalizer |
| Coequalizer `coeq(f,g)` | quotient | product over component |
| Terminal | `PUnit` | `∅` |
| Initial | `∅` | (vacuous) |

### Existing CoprodCovarRepCat Limits (PresheafPRAUMorph.lean)

| Definition | Role |
| ---------- | ---- |
| `ccrHasLimit` | Limits exist in CCR when C has colimits |
| `ccrHasLimitsOfShape` | Typeclass instance |
| `ccrLimFunctor` | Computable limit functor |
| `ccrConstLimAdj` | Constant-limit adjunction |

---

## Plan: PRA Presheaf Analogs

### Phase A: Limits and Colimits of PRAs

The strategy for each construction:

1. Define position (co)limit in `Jᵒᵖ ⥤ Type w'`
2. Identify the category of elements of the
   resulting position presheaf
3. Define direction (co)limit on that category
   of elements (dual to the position construction)
4. Reassemble into a PRA via `functorTo`
5. Prove the universal property in
   `PresheafPRACat`

#### A0: Reassembly Infrastructure

**Goal:** Establish the round-trip between PRA
objects and (positions, directions) pairs. Given
`A : Jᵒᵖ ⥤ Type w'` and
`E : A.ElementsPre ⥤ PSh(I)`, construct a PRA
`P : PresheafPRACat I J`.

**Implementation:** Use `functorTo` applied to
`familyFunctor (PSh(I))` with:

- `baseFunc` derived from `A` (mapping `j` to
  `op (A.obj j)`)
- `fib` at `j` given by `E` restricted to the
  fiber at `j`
- `hom` from functoriality of `E`

**Result:** An equivalence (or at least adjunction)
between the decomposed form and `PresheafPRACat`.

**File:** `GebLean/PresheafPRAUMorph.lean`

#### A1: Products

**Formula:** For PRAs `P_k` (`k ∈ K`) with
positions `A_k` and directions `E_k`:

- Positions: `A(j) = ∏_k A_k(j)` — pointwise
  product of position presheaves (limit in
  `Jᵒᵖ ⥤ Type w'`)
- Elements of product: `(j, (a_k)_k)` where
  `a_k ∈ A_k(j)` for each `k`
- Directions at `(j, (a_k)_k)`:
  `∐_k E_k(j, a_k)` — coproduct of direction
  presheaves (colimit in `PSh(I)`)

**Implementation:**

- [ ] Define `praProductPos` as the product of
  position presheaves
- [ ] Identify `Elements(praProductPos)` and
  define projection functors to each
  `Elements(A_k)`
- [ ] Define `praProductDir` as the coproduct of
  pulled-back direction presheaves
- [ ] Assemble via `functorTo` into PRA
- [ ] Define cone morphisms from the product to
  each `P_k`
- [ ] Prove universal property (lift + uniqueness)
- [ ] Package as `HasLimit` instance

**File:** `GebLean/PresheafPRAUMorph.lean`

#### A2: Coproducts

**Formula:** Positions `A(j) = ∐_k A_k(j)` —
coproduct of position presheaves. Directions at
`(j, (k, a_k))`: `E_k(j, a_k)` — the selected
direction presheaf.

**Implementation:** Sigma type on positions,
unchanged directions at the selected component.
Generalizes `polyBetweenCoprod`.

#### A3: Equalizers

**Formula:** For `f, g : P → Q`:

- Positions: `A(j) = {a ∈ A_P(j) | f_pos(a) =
  g_pos(a)}` — equalizer of position morphisms
  (limit/subtype)
- Directions: coequalizer of the two direction
  morphisms at positions where they agree
  (colimit)

**Implementation:** Subtype on positions,
coequalizer on directions. Generalizes
`polyBetweenEq`.

#### A4: Coequalizers

**Formula:**

- Positions: `A(j) = A_Q(j) / ~` where `~`
  identifies images under `f_pos` and `g_pos` —
  coequalizer of position morphisms (colimit)
- Directions: pullback/equalizer of direction
  morphisms at identified positions (limit)

**Implementation:** Quotient on positions,
equalizer on directions. Generalizes
`polyBetweenCoeq`.

#### A5: Completeness and Cocompleteness

**Result:** `PresheafPRACat I J` has all small
limits and colimits. This follows from A1-A4 (or
directly from the presheaf decomposition and the
fact that presheaf categories are (co)complete).

**Implementation:** Derive `HasLimitsOfSize` and
`HasColimitsOfSize` instances. Optionally build
computable (co)limit functors and adjunctions
(as done for `ccrLimFunctor`/`ccrConstLimAdj`).

---

### Phase B: Closed Monoidal Structure

#### B1: Cartesian Product

Pointwise product of evaluation functors.
Binary specialization of A1: positions are
products, directions are coproducts.

#### B2: Internal Hom (Exponential)

`[P, Q]` uses the LCCC structure of presheaf
categories (dependent products along the
positions presheaf). The presheaf decomposition
makes this natural: work directly in the
presheaf topos.

Generalizes `pbCurry`/`pbUncurry`. May need
`Sigma`/`Pi`/`Delta` adjunctions.

#### B3: Dirichlet Product

Positions `A(j) = A_P(j) × A_Q(j)` (product),
directions `E(j, (a,b)) = E_P(j,a) ⊕ E_Q(j,b)`
(coproduct). Generalizes `polyBetweenDirichlet`.

#### B4: Dirichlet Closure

Right adjoint to the Dirichlet product.
Generalizes `polyBetweenDirichletClosure`.

---

### Phase C: Composition and Identity

#### C1: Identity PRA

For `PSh(I) → PSh(I)`:

- Positions: terminal presheaf (constant `{*}`)
- Directions: `E(i, *) = yo(i)` (Yoneda at `i`)
- Evaluation: `Id(Z)(i) = Hom(yo(i), Z) = Z(i)`

Implementation uses terminal presheaf and Yoneda
embedding.

#### C2: Composition of PRAs

For `P : PSh(I) → PSh(J)` with `(A_P, E_P)` and
`Q : PSh(J) → PSh(K)` with `(A_Q, E_Q)`:

Factor each PRA as `π_! ∘ E^*`:

```text
P = (π_P)_! ∘ E_P^*
Q = (π_Q)_! ∘ E_Q^*
```

Then `Q ∘ P = (π_Q)_! ∘ E_Q^* ∘ (π_P)_! ∘ E_P^*`.
The middle part uses Beck-Chevalley.

Uses `praDirectionsAtFunctor` for `E` and
`CategoryOfElements.π` for `π`. Generalizes
`polyBetweenComp`.

#### C3: PRA Factorization

Every PRA `P : PSh(I) → PSh(J)` with `(A, E)`
factors as:

```text
PSh(I) --E^*--> PSh(el(A)) --π_!--> PSh(J)
```

Uses `praDirectionsAtFunctor` and the category
of elements projection.

---

### Phase D: Algebras and Coalgebras

#### D1: Algebra Category

For PRA endofunctor `P : PSh(I) → PSh(I)`, use
mathlib's `Endofunctor.Algebra` applied to
`praEvalAtFunctor.obj P`.

#### D2: Initial Algebra (W-type)

Colimit of the iteration sequence
`∅ → P(∅) → P²(∅) → ⋯`. Exists
unconditionally since `PSh(I)` is cocomplete
(Phase A). Generalizes `PolyFix`.

#### D3: Terminal Coalgebra (M-type)

Limit of `1 ← P(1) ← P²(1) ← ⋯`.
Generalizes `PolyCofix`.

#### D4: Free Monad

Underlying endofunctor sends `A` to the initial
algebra of `X ↦ A + P(X)`. Uses Phase A
coproducts and D2. Generalizes `polyFreeMonad`.

#### D5: Cofree Comonad

Dual of D4. Generalizes
`polyCoalgComonadEquiv`.

---

### Phase E: Double Category Structure

#### E1: Objects and Morphisms

- Objects: small categories `I : Cat`
- Vertical: functors `F : I ⥤ J`
- Horizontal: PRAs `P : PresheafPRACat I J`
- Cells: natural transformations

#### E2: Vertical Composition

Composition of functors.

#### E3: Horizontal Composition

Composition of PRAs (Phase C2).

#### E4: Cell Structure

A cell filling the square:

```text
PSh(I₁) --P--> PSh(J₁)
  |               |
  F^*             G^*
  |               |
  v               v
PSh(I₂) --Q--> PSh(J₂)
```

is a natural transformation
`G^* ∘ P → Q ∘ F^*`.

---

## Implementation Order and Dependencies

```text
Phase A (Limits/Colimits)
├── A0: Reassembly infrastructure (first)
├── A1: Products (depends A0)
├── A2: Coproducts (depends A0)
├── A3: Equalizers (depends A0)
├── A4: Coequalizers (depends A0)
└── A5: Completeness (depends A1-A4)

Phase B (Closed Monoidal)
├── B1: Cartesian product (depends A1)
├── B2: Internal hom (depends B1, Phase C)
├── B3: Dirichlet product (depends A0)
└── B4: Dirichlet closure (depends B3)

Phase C (Composition)
├── C1: Identity (independent)
├── C2: Composition (depends C1)
└── C3: PRA factorization (depends C2)

Phase D (Algebras)
├── D1: Algebra category (depends C1)
├── D2: Initial algebra/W-type (depends D1, A2)
├── D3: Terminal coalgebra/M-type (depends D1, A1)
├── D4: Free monad (depends D2, A2)
└── D5: Cofree comonad (depends D3, A1)

Phase E (Double Category)
├── E1: Objects/morphisms (independent)
├── E2: Vertical composition (independent)
├── E3: Horizontal composition (depends C2)
└── E4: Cell structure (depends E1-E3)
```

## Recommended Starting Order

1. **A0** (reassembly) — establishes the
   decomposition/recomposition round-trip
2. **A1-A2** (products, coproducts) — most
   mechanical, direct PolyBetween generalization
3. **A3-A4** (equalizers, coequalizers)
4. **A5** (completeness instances)
5. **C1** (identity) — needed for composition
6. **C3** (PRA factorization) — demonstrates
   `π_! ∘ E^*` decomposition
7. **C2** (composition) — uses C3
8. **D1** (algebra category)
9. **D2-D3** (W-types, M-types)
10. **B1-B4** (closed monoidal) — uses A1 and C2
11. **E1-E4** (double category) — capstone

## File Structure

| File | Contents |
| ---- | -------- |
| `GebLean/PresheafPRAUMorph.lean` | Phase A (reassembly + limits/colimits) |
| `GebLean/PresheafPRAComp.lean` | Phase C (composition, identity) |
| `GebLean/PresheafPRAAlg.lean` | Phase D (algebras, W/M-types) |
| `GebLean/PresheafPRADouble.lean` | Phase E (double category) |
| `GebLean/PresheafPRAMonoidal.lean` | Phase B (closed monoidal) |

## Key Mathematical References

- nLab: parametric right adjoint (PRA
  factorization, generic morphisms)
- nLab: polynomial functor (LCCC formulas)
- Gambino-Kock: "Polynomial functors and
  polynomial monads" (composition, W-types)
- Weber: "Polynomials in categories with
  pullbacks" (LCCC setting, Beck-Chevalley)
- Gambino-Hyland: "Wellfounded trees and
  dependent polynomial functors" (W-types in
  presheaf categories)
- Berger-Mellies-Weber: "Monads with arities"
  (PRA monads, free monads)
