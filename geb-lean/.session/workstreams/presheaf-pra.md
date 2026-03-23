# Workstream: Presheaf PRA (Polynomial Functors Between Presheaf Categories)

## Status

Planning complete. Implementation not started.

## Goal

Define polynomial functors between presheaf categories
(parametric right adjoints) in Lean, building on the existing
`CoprodCovarRepCat` and `PolyFunctorBetweenCat` infrastructure.

## Design Principles

### One step at a time

Every definition and proof should take exactly one step
beyond the definitions it depends on. Factor out intermediate
definitions so that each one is expressed in terms of the
layer directly below it, not multiple layers down. This
ensures that goals and contexts remain readable, that
tactics can operate at a single level of abstraction, and
that each definition has a clear, testable meaning.

Use `def`, not `abbrev`, for named intermediate
constructions. `abbrev` causes automatic expansion, which
defeats the purpose of factoring: goals appear in terms
of internals rather than the next layer down.

### Everything is functorial

Every operation must be expressed as a functor (or natural
transformation, or other higher-order categorical
construction) to the greatest degree possible. This makes
operations composable, allows reuse of existing results
about functor categories, and ensures that naturality
conditions are handled structurally rather than by ad-hoc
proofs.

When decomposing a construction, each intermediate step
should itself be a functor. The final construction is then
a composition of functors, and its properties follow from
the properties of the components.

### Worked example: decomposing PresheafPRACat

The original definition was:

```lean
abbrev PresheafPRACat I J : Cat :=
  Cat.of
    (Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I))
```

This is decomposed into:

1. `catContraHomFunctor (Type w_I) : Catᵒᵖ ⥤ Cat`
   — the contravariant hom-functor, sending `C` to
   `C ⥤ Type w_I` via precomposition
2. Composition with `Cat.opFunctor : Cat ⥤ Cat`
   (via the op involution `Cat ≅ Catᵒᵖ`) gives a
   functor `Catᵒᵖ ⥤ Cat` sending `I` to
   `Iᵒᵖ ⥤ Type w_I`
3. `CoprodCovarRepCat` applied functorially gives
   another `Cat`-level operation
4. The outer `Jᵒᵖ ⥤ ...` functor category is another
   contravariant hom application

Each step is a `def` with its own type signature, and
`PresheafPRACat` is defined by composing them.

## Design Decisions

### Representation

A PRA `Presheaf I -> Presheaf J` is a functor
`Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.

At each `j : J`, this gives a polynomial
`(A(j), E_j : A(j) -> Presheaf I)`. The functor action
provides restriction maps, making the evaluation a presheaf on
`J` without any `Subtype` or separate naturality predicate.

### Universe Polymorphism

Universe parameters are maximally independent:

- `I : Type u_I` with `Category.{v_I} I`
- `J : Type u_J` with `Category.{v_J} J`
- `w_I` — domain presheaf value universe
- `w'` — position/index type universe

No correlation between `I` and `J` universes. The output
presheaf values live in `Type (max w' u_I w_I)` (determined,
not a free parameter). Operations such as composition that
require universe alignment impose constraints only at the
point of use.

### Hom Formula vs LCCC Decomposition

The Hom formula
`P(Z)(j) = coprod_{a in A(j)} Hom(E_j(a), Z)` is the
primary representation. Neither it nor the LCCC form
`Sigma_A . Pi_p . B*` involves pushouts or coends — both use
only limits and discrete coproducts. The LCCC equivalence is a
secondary result for later.

## Implementation Plan

### Phase 1: Core Definitions (PresheafPRA.lean)

1. Define `catContraHomFunctor D : Catᵒᵖ ⥤ Cat`
   (contravariant hom-functor)
2. Define presheaf-category functor
   `I ↦ Iᵒᵖ ⥤ Type w_I` as a composite
3. Define `PresheafPRACat I J` using the factored
   operations (as `def`, not `abbrev`)
4. Accessor functions: `praPositions`, `praDirectionsAt`
3. Pointwise evaluation `praEvalAt P Z j` via `ccrEval`
4. Restriction map construction using `ccrReindex` and
   `ccrFiberMor` from the functor action
5. Full evaluation `praEvalObj P Z : Jᵒᵖ ⥤ Type _`
6. Functorial action `praEvalMap` on presheaf morphisms
7. Evaluation functor `praEvalFunctor P : (Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type _)`
8. Morphism evaluation `praMorphEvalAt`, `praMorphEval`
9. Functor lifting `praEvalCatFunctor :
   PresheafPRACat I J ⥤ ((Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type _))`
10. Register in `GebLean.lean`

### Phase 2: Discrete-Category Connection

- Equivalence between `PresheafPRACat I J` over discrete
  categories and `PolyFunctorBetweenCat I J`
- Compatibility of evaluation functors under this equivalence

### Phase 3: Identity and Composition

- Identity PRA `praId I : PresheafPRACat I I`
- Composition `praComp : PresheafPRACat J K ->
  PresheafPRACat I J -> PresheafPRACat I K`
- Evaluation compatibility: `praEvalFunctor (praComp g f) ≅
  praEvalFunctor f ⋙ praEvalFunctor g`

### Phase 4: Universal Morphisms (PresheafPRAUMorph.lean)

- Products, coproducts, equalizers, coequalizers
- Completeness/cocompleteness of `PresheafPRACat I J`

### Phase 5: Algebras (PresheafPRAAlg.lean)

- Algebras and coalgebras of PRA endofunctors
- Fixed points (initial algebras, terminal coalgebras)

## Dependencies

- `GebLean/Polynomial.lean`: `CoprodCovarRepCat`, `ccrEval`,
  `ccrEvalMap`, `ccrToFunctor`, `ccrReindex`, `ccrFiberMor`
- `GebLean/Utilities/Presheaf.lean`: `Presheaf`, `Copresheaf`
- `GebLean/Utilities/Elements.lean`: `ElementsContra'`,
  `sliceEquivPresheaf`
- `GebLean/Utilities/Families.lean`: `FamilyCat`, `ccrIndex`,
  `ccrFamily`
- `GebLean/Utilities/Opposites.lean`: `Cᵒᵖ`

## Relation to Other Workstreams

- `poly-presheaf-ccc.md`: this workstream implements Layers
  1-2 of that plan. Layer 3 (cartesian closure) and Layer 4
  (connection to PshRelEdge) remain for later.

## References

- `docs/presheaf-pra.md` — concept documentation
- nLab: parametric right adjoint
- Existing `PolyFunctorBetweenCat` in `Polynomial.lean`
- Existing `polyBetweenEvalFunctor` pattern in
  `Polynomial.lean`
