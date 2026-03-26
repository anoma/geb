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

**Architecture:** Each construction follows the pattern:
define it for `CoprodCovarRepCat` (the polynomial
level), then lift to `PresheafPRACat` (the PRA level)
via the functorial infrastructure already in place
(`praEvalAtFunctor`, `praPositionsFunctor`, etc.).
Where possible, constructions are expressed as
compositions of existing functors.

**Tech Stack:** Lean 4, mathlib (category theory,
presheaf categories, Grothendieck construction,
W-types), existing GebLean infrastructure (polynomial
functors, PRA definitions, op/op' transfer).

---

## Existing Polynomial Infrastructure (Reference)

The following constructions exist for
`PolyFunctorBetweenCat X Y` (polynomial functors
between slice categories `Over X → Over Y`):

### Limits and Colimits (PolyUMorph.lean)

| Construction | Positions | Directions |
| ------------ | --------- | ---------- |
| Product `∏_k P_k` | `∏_k I_k(y)` | `∐_k F_k(y, p_k)` |
| Coproduct `∐_k P_k` | `∐_k I_k(y)` | `F_k(y, i_k)` |
| Equalizer `eq(f,g)` | `{i \| f(i)=g(i)}` | `F(y,i)` |
| Coequalizer `coeq(f,g)` | quotient | pushout fibers |
| Terminal | `PUnit` | `∅` |
| Initial | `∅` | (vacuous) |

### Closed Monoidal Structure (PolyUMorph.lean)

| Construction | Formula |
| ------------ | ------- |
| Cartesian product | pointwise product |
| Internal hom `[P,Q]` | `∏_{i:I_P(y)} Q^{F_P(y,i)}` |
| Dirichlet product | `(I_P × I_Q, F_P ⊕ F_Q)` |
| Dirichlet closure | right adjoint of Dirichlet |

### Composition (Polynomial.lean)

| Construction | Formula |
| ------------ | ------- |
| Identity | `(PUnit, yo)` at each `y` |
| Composition `Q ∘ P` | positions: `Σ_b P(F_Q(b))`, directions: dependent |
| Left Kan extension | adjoint to restriction |

### Algebras (PolyAlg.lean)

| Construction | Description |
| ------------ | ----------- |
| Initial algebra (W-type) | Inductive `PolyFix` |
| Terminal coalgebra (M-type) | Limit `PolyCofix` |
| Free monad | `polyFreeMonad` |
| Cofree comonad | `polyCoalgComonadEquiv` |
| Algebra/monad equivalence | `polyAlgMonadEquiv` |

### Double Category (Polynomial.lean)

| Component | Description |
| --------- | ----------- |
| Objects | Types `X : Type u` |
| Vertical morphisms | Functions `X → Y` |
| Horizontal morphisms | `PolyFunctorBetweenCat X Y` |
| Cells | Natural transformations |

---

## Plan: PRA Presheaf Analogs

### Phase A: Limits and Colimits of PRAs

#### A1: Products

**Formula:** For PRAs `P_k` with positions `A_k`
and directions `E_k`:

```text
(∏_k P_k)(Z)(j) = ∏_k (∐_{a_k ∈ A_k(j)}
  Hom(E_k(j,a_k), Z))
```

Positions: `A(j) = ∏_k A_k(j)` (pointwise product
of presheaves)

Directions at `(j, (a_k)_k)`:
`E(j, (a_k)) = ∐_k E_k(j, a_k)` (coproduct of
direction presheaves)

**Implementation:** Define at `CoprodCovarRepCat`
level (indexed product of CCR objects), then lift.
The positions are a product in `Type w'` and the
directions are a coproduct in the presheaf category.
This generalizes `polyBetweenProd`.

**File:** `GebLean/PresheafPRAUMorph.lean`

#### A2: Coproducts

**Formula:** Positions `A(j) = ∐_k A_k(j)`,
directions `E(j, (k,a_k)) = E_k(j, a_k)`.

**Implementation:** Sigma type on positions, same
directions. Generalizes `polyBetweenCoprod`.

#### A3: Equalizers

**Formula:** Positions `A(j) = {a ∈ A_P(j) |
f(a) = g(a)}`, directions unchanged.

**Implementation:** Subtype on positions.
Generalizes `polyBetweenEq`.

#### A4: Coequalizers

**Formula:** Positions `A(j) = A_Q(j) / ~` where
`~` identifies images of `f` and `g`.  Directions
are the pushout of fibers along the identification.

**Implementation:** Quotient on positions, pushout
on directions.  Generalizes `polyBetweenCoeq`.

#### A5: Completeness and Cocompleteness

**Result:** `PresheafPRACat I J` has all small
limits and colimits (since `CoprodCovarRepCat` does
and the functor-category structure preserves them).

**Implementation:** Derive `HasLimitsOfSize` and
`HasColimitsOfSize` instances.

---

### Phase B: Closed Monoidal Structure

#### B1: Cartesian Product

**Formula:** Pointwise product of evaluation
functors.  Positions are products, directions are
coproducts (same as products of two PRAs).

**Implementation:** Binary specialization of A1.

#### B2: Internal Hom (Exponential)

**Formula:** `[P, Q]` is the PRA whose evaluation
at `Z` and `j` is `NatTrans(P(Z), Q(Z))` restricted
to `j`.  Concretely:

```text
[P,Q](Z)(j) = ∏_{a ∈ A_P(j)} ∐_{b ∈ A_Q(j)}
  Hom(E_Q(j,b), Z)^{Hom(E_P(j,a), Z) → {b}}
```

This is more involved; it uses the LCCC structure
of presheaf categories (dependent products along
the positions presheaf).

**Implementation:** Generalizes `pbCurry`/
`pbUncurry`.  Requires `Pi` (dependent product) in
the presheaf topos.  May need to use
`Sigma`/`Pi`/`Delta` adjunctions.

#### B3: Dirichlet Product

**Formula:** Positions `A(j) = A_P(j) × A_Q(j)`,
directions `E(j, (a,b)) = E_P(j,a) ⊕ E_Q(j,b)`
(coproduct of direction presheaves).

**Implementation:** Product on positions, coproduct
on directions.  Generalizes `polyBetweenDirichlet`.

#### B4: Dirichlet Closure

Right adjoint to the Dirichlet product.
Generalizes `polyBetweenDirichletClosure`.

---

### Phase C: Composition and Identity

#### C1: Identity PRA

**Formula:** For `PSh(I) → PSh(I)`:

- Positions: `A = terminal presheaf` (constant `{*}`)
- Directions: `E(i, *) = yo(i)` (Yoneda at `i`)

Evaluation: `Id(Z)(i) = Hom(yo(i), Z) = Z(i)` by
Yoneda.

**Implementation:** Define using the terminal
presheaf and Yoneda embedding.

#### C2: Composition of PRAs

**Formula:** For `P : PSh(I) → PSh(J)` with
`(A_P, E_P)` and `Q : PSh(J) → PSh(K)` with
`(A_Q, E_Q)`:

The composite `Q ∘ P` has positions at `k`:

- `Σ_{b ∈ A_Q(k)} ∏_{(j,e) ∈ el(E_Q(k,b))} A_P(j)`

Actually, the correct formula uses the
Beck-Chevalley condition.  Factor each PRA as
`π_! ∘ E^*`:

```text
P = (π_P)_! ∘ E_P^*  where π_P : el(A_P) → J
Q = (π_Q)_! ∘ E_Q^*  where π_Q : el(A_Q) → K
```

Then `Q ∘ P = (π_Q)_! ∘ E_Q^* ∘ (π_P)_! ∘ E_P^*`.
The middle part `E_Q^* ∘ (π_P)_!` is computed via
Beck-Chevalley for the pullback square.

**Implementation:** This is the deepest
construction.  Define the pullback category, then
use the Beck-Chevalley formula.  Generalizes
`polyBetweenComp`.

#### C3: PRA Factorization

**Formula:** Every PRA `P : PSh(I) → PSh(J)` with
`(A, E)` factors as:

```text
PSh(I) --E^*--> PSh(el(A)) --π_!--> PSh(J)
```

where:

- `E^* = E ∘ -` is precomposition with
  `E : el(A)^op → PSh(I)` (a right adjoint)
- `π_! = Lan_π` is left Kan extension along
  `π : el(A) → J` (a discrete opfibration part)

**Implementation:** Define `E^*` and `π_!`
separately, prove their composition equals `P`.
Uses `praDirectionsAtFunctor` for `E` and
`CategoryOfElements.π` for `π`.

---

### Phase D: Algebras and Coalgebras

#### D1: Algebra Category

**Definition:** For PRA endofunctor
`P : PSh(I) → PSh(I)`, an algebra is
`(A, α : P(A) → A)` where `A : PSh(I)` and
`α` is a presheaf morphism.

**Implementation:** Use mathlib's
`Endofunctor.Algebra` applied to
`praEvalAtFunctor.obj P`.

#### D2: Initial Algebra (W-type)

**Construction:** Since `PSh(I)` is a topos (hence
LCCC), W-types exist.  The initial algebra of a PRA
endofunctor `P` is computed as the colimit of the
iteration sequence
`∅ → P(∅) → P²(∅) → ⋯`.

For the pointwise formula: at each `i : I`, the
W-type fiber is the set of well-founded trees whose
nodes are labeled by positions and edges by
directions, compatible with the presheaf structure.

**Implementation:** Define `praFix P : PSh(I)` as
the colimit of the iteration chain.  Generalizes
`PolyFix`.

#### D3: Terminal Coalgebra (M-type)

**Construction:** Dual: the limit of
`1 ← P(1) ← P²(1) ← ⋯`.

**Implementation:** Define `praCofix P : PSh(I)` as
the limit.  Generalizes `PolyCofix`.

#### D4: Free Monad

**Construction:** The free monad on `P` is the
monad whose algebras are exactly the `P`-algebras.
Its underlying endofunctor sends `A` to the initial
algebra of `X ↦ A + P(X)`.

**Implementation:** Define using the coproduct PRA
`A + P(-)` and its initial algebra.  Generalizes
`polyFreeMonad`.

#### D5: Cofree Comonad

Dual of D4.  Generalizes `polyCoalgComonadEquiv`.

---

### Phase E: Double Category Structure

#### E1: Objects and Morphisms

- **Objects:** Small categories `I : Cat`
- **Vertical morphisms:** Functors `F : I ⥤ J`
  (or a restricted class: discrete fibrations,
  discrete opfibrations, or all functors —
  investigate which gives the right 2-cell
  structure)
- **Horizontal morphisms:** PRAs `P : PSh(I) →
  PSh(J)`, i.e., objects of `PresheafPRACat I J`
- **Cells:** Natural transformations between
  appropriate compositions

#### E2: Vertical Composition

Composition of functors `F : I ⥤ J` and
`G : J ⥤ K`.

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

is a natural transformation `G^* ∘ P → Q ∘ F^*`
(where `F^*` and `G^*` are precomposition
functors).

**Note on vertical morphisms:** The most natural
choice for the polynomial/PRA double category is:

- Vertical morphisms are **functors** `I ⥤ J`
  (general)
- The restricted version with **discrete
  opfibrations** gives the PRA factorization
  (Phase C3)

The existing slice-polynomial double category uses
**functions** `X → Y` as vertical morphisms, which
are the discrete-category specialization of
functors.

---

## Implementation Order and Dependencies

```text
Phase A (Limits/Colimits)
├── A1: Products (independent)
├── A2: Coproducts (independent)
├── A3: Equalizers (independent)
├── A4: Coequalizers (independent)
└── A5: Completeness (depends A1-A4)

Phase B (Closed Monoidal)
├── B1: Cartesian product (depends A1)
├── B2: Internal hom (depends B1, Phase C)
├── B3: Dirichlet product (independent)
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

1. **A1-A4** (limits/colimits) — most mechanical,
   direct generalization of `PolyUMorph.lean`
2. **C1** (identity) — needed for everything else
3. **C3** (PRA factorization) — demonstrates the
   right-adjoint + discrete-opfibration
   decomposition
4. **C2** (composition) — uses C3
5. **D1** (algebra category) — enables fixed points
6. **D2-D3** (W-types, M-types)
7. **B1-B4** (closed monoidal) — uses A1 and C2
8. **E1-E4** (double category) — capstone

## File Structure

| File | Contents |
| ---- | -------- |
| `GebLean/PresheafPRAUMorph.lean` | Phases A, B |
| `GebLean/PresheafPRAComp.lean` | Phase C |
| `GebLean/PresheafPRAAlg.lean` | Phase D |
| `GebLean/PresheafPRADouble.lean` | Phase E |

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
