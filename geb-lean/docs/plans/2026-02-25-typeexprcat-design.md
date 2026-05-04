# TypeExprCat and Parametric Wedges

## Motivation

`ParametricFamily T` is the type of polymorphic families
`app : ∀ I, T.interp I I` satisfying the full relational
interpretation condition
`∀ R, T.fullRelInterp R (app I₀) (app I₁)`.

This document characterizes `ParametricFamily` in two ways:

1. As the terminal object in a category of **parametric
   wedges** (analogous to how an end is a terminal wedge for a
   profunctor).
2. As the hom from a unit object in **TypeExprCat**, a
   category whose objects are type expressions and whose
   morphisms are relation-preserving polymorphic functions.

These characterizations provide a categorical framework for
the free theorems already proved in `ParanaturalTopos.lean`.

## Part 1: Parametric wedges

### Definition

A parametric wedge for `T : TypeExpr` consists of:

- `pt : Type` (the vertex)
- `proj : (I : Type) → pt → T.interp I I` (the family)
- `parametric : ∀ (w : pt) (I₀ I₁ : Type)
    (R : I₀ → I₁ → Prop),
    T.fullRelInterp R (proj I₀ w) (proj I₁ w)`

A morphism of parametric wedges from `(W, w)` to `(W', w')`
is a function `f : W → W'` with `w'_I ∘ f = w_I` for all `I`.

### Comparison with standard wedges

A standard wedge for `T.toProfunctor` replaces the parametric
condition with the wedge condition:

```text
∀ (f : I₀ → I₁),
  T.profMap id f (proj I₀ w) = T.profMap f id (proj I₁ w)
```

Every parametric wedge is a standard wedge (via
`relInterp_implies_wedge`). The forgetful functor from
parametric wedges to standard wedges sends the terminal
parametric wedge to a sub-wedge of the terminal standard
wedge (the end).

### Terminal object

`ParametricFamily T` is the terminal parametric wedge:

- `pt := ParametricFamily T`
- `proj I p := p.app I`
- `parametric w := w.parametric`

Terminality: given any parametric wedge `(W, w)`, the unique
morphism is `fun w => ⟨fun I => w.proj I w, w.parametric w⟩`.
Uniqueness follows from `ParametricFamily.ext`.

### Tower of terminal objects

```text
ParametricFamily T → ∫_I T.interp I I → ∏_I T.interp I I
```

- Terminal parametric wedge → terminal standard wedge →
  terminal cone (product)
- The first map is `ParametricFamily.wedge`
- The second is the end's cone projection

## Part 2: TypeExprCat

### Objects and morphisms

- **Objects**: `TypeExpr`
- **Morphisms** `T₁ → T₂`:
  `ParametricFamily (arrow T₁ T₂)`

A morphism consists of a family
`η : ∀ I, T₁.interp I I → T₂.interp I I` such that for all
`R : I₀ → I₁ → Prop`, `x₀`, `x₁`:

```text
T₁.fullRelInterp R x₀ x₁ →
  T₂.fullRelInterp R (η I₀ x₀) (η I₁ x₁)
```

### Category laws

- **Identity**: `fun I => id` with the trivial preservation
  proof.
- **Composition**: given `η : Hom(T₁, T₂)` and
  `μ : Hom(T₂, T₃)`, the composite is
  `fun I => μ.app I ∘ η.app I`. The relational preservation
  composes by modus ponens.
- **Associativity and unit laws**: inherited from function
  composition.

### Unit object

Define:

```lean
def TypeExpr.unit : TypeExpr :=
  .app (Functor.const PUnit) .var
```

with `unit.interp I I = PUnit`. Then:

```text
Hom(unit, T) ≅ ParametricFamily T
```

via the isomorphism `(PUnit → X) ≅ X`.

### Existing equivalences as Hom computations

The following results in `ParanaturalTopos.lean` compute
specific `Hom` types in `TypeExprCat`:

- `homParametricEquivUnit`:
  `Hom(var, var) ≅ Unit`
- `dialgebraParametricEquivNatTrans`:
  `Hom(app F var, app G var) ≅ (F ⟶ G)`
- `algebraParametricEquivParanat`:
  `Hom(unit, algebraTypeExpr F) ≅ Paranat ...`
- `initialAlgebraParametricEquiv`:
  `Hom(unit, algebraTypeExpr F) ≅ μF.a`
- `dinaturalNumbersParametricEquiv`:
  `Hom(unit, dinaturalTypeExpr) ≅ ℕ`
- `dialgebraParametricEquivNatTrans` (via unit):
  `Hom(unit, dialgebraTypeExpr F G) ≅ (F ⟶ G)`

## Part 3: Inductive morphism characterization (future)

The morphisms of `TypeExprCat` are defined via
`fullRelInterp` preservation (a semantic condition). A
complementary **inductive** characterization `HomInd(T₁, T₂)`
would define morphisms structurally, by recursion on pairs
of type expressions.

### Known cases

- `HomInd(var, var) = Unit` (identity)
- `HomInd(app F T₁, app G T₂) =
    (F ⟶ G) × HomInd(T₁, T₂)` (natural transformation
    on the outer functor, recursive morphism on the inner
    expression), subject to a naturality condition between the
    two components
- `HomInd(arrow S₁ S₂, arrow T₁ T₂) ⊇
    HomInd(T₁, S₁) × HomInd(S₂, T₂)` (pre/post-composition),
    but this is not exhaustive: `Hom(arrow var var,
    arrow var var) ≅ ℕ` (Church numerals) while
    pre/post-composition gives only `Unit`

### The general free theorem

The equivalence `HomInd(T₁, T₂) ≅ Hom(T₁, T₂)` for all
pairs is the **general free theorem** for `TypeExpr`:
structural commutativity conditions (naturality, commuting
diagrams) are equivalent to semantic relation-preservation
(`fullRelInterp` for all `R`).

The proof content of `HomInd` is structural
(naturality squares, commuting diagrams between
sub-components), while the proof content of `Hom` is
semantic (preservation of all `Prop`-valued relations).

### Relationship to lax double functors

The vertical part of the lax double endoprofunctor
`T.interpret` on `PshRel` maps relations `R` to
`fullRelInterp T R` (via `biRelInterp_diag`). The end of
this vertical endoprofunctor is `ParametricFamily T`. The
lax composition comparison
`fullRelInterp T R ∘ fullRelInterp T S ⊆
  fullRelInterp T (R ∘ S)`
explains why `ParametricFamily` (quantifying over all
relations) is strictly smaller than `End(T.toProfunctor)`
(quantifying only via the wedge condition) for type
expressions with nested arrows.

## Implementation plan

### Phase 1: ParametricWedge and TypeExprCat

1. Define `ParametricWedge T` as a structure
2. Define `ParametricWedgeMorphism` and the category instance
3. Prove `ParametricFamily T` is terminal
4. Define `TypeExprCat` with `Hom = ParametricFamily ∘ arrow`
5. Prove the category laws
6. Define `TypeExpr.unit` and prove
   `Hom(unit, T) ≅ ParametricFamily T`
7. Restate existing equivalences as `Hom` computations

### Phase 2: Inductive characterization

1. Define `HomInd(T₁, T₂)` by recursion on pairs
2. Construct the realization map
   `HomInd(T₁, T₂) → Hom(T₁, T₂)`
3. Prove the backward direction for specific cases
4. Investigate the general backward direction

## Files

- `GebLean/ParanaturalTopos.lean`: `ParametricWedge`,
  `TypeExprCat`, `TypeExpr.unit`, terminality proof,
  restatement of existing equivalences
- `GebLean/PshRelDouble.lean`: lax double functor
  infrastructure (if needed for Part 3)
