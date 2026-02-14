# Parametric Generalization

## Status: Planning

## Goal

Generalize `TypeExpr` and `ParametricFamily` from `Type` to
arbitrary categories via `YonedaRel`, and embed parametric
transformations into the twisted-arrow copresheaf topos
alongside paranatural transformations.

## Context

### Existing infrastructure

- `TypeExpr` (`ParanaturalTopos.lean`): Inductive type
  with `.leaf (F : Type ⥤ Type)` and `.arrow T₁ T₂`,
  representing type expressions in one variable over `Type`.
- `TypeExpr.relInterp`: Relational interpretation replacing
  leaves with `graphRel (F.map f)` and arrows with `arrowRel`.
- `ParametricFamily T` (`ParanaturalTopos.lean`): A
  `Type`-indexed family `app : (I : Type) → T.interp I I`
  with `T.relInterp f (app I₀) (app I₁)` for all `f`.
- `StrongRestrictedWedge G H` (`Weighted.lean`):
  Generalizes paranatural transformations via weighted limits
  to arbitrary codomain `D`. Parametrized by
  `G : Cᵒᵖ ⥤ C ⥤ D` (diagram) and
  `H : Cᵒᵖ ⥤ C ⥤ Type v` (restriction weight).
- `wedgeWeight G H : TwistedArrow C ⥤ Type v`
  (`ComprehensiveWeighted.lean`): Embeds paranatural
  transformations as natural transformations in the
  twisted-arrow copresheaf topos, via
  `comprehensiveCopresheaf (twistedArrowMap (DiagElem.forget H))`.
- `YonedaRel X Y = Skeleton (YonedaProdOver X Y)`
  (`ParamPoly.lean`): Yoneda relations as isomorphism
  classes of presheaf maps into yoneda products, with
  `relId`, `relComp`, and a `Category` instance on
  `YonedaRelCat C`.
- `YonedaRelDouble` (`YonedaRelDouble.lean`): Double
  category with objects of `C`, horizontal morphisms of
  `C`, vertical morphisms `YonedaRel`, and `Prop`-valued
  squares `relRelated`.
- `algebraParametricEquivParanat`,
  `dinaturalParametricEquivParanat`
  (`ParanaturalTopos.lean`): For the algebra and
  dinatural type expressions, `ParametricFamily` is
  equivalent to `Paranat`.
- `initialAlgebraParametricEquiv`,
  `dinaturalNumbersParametricEquiv`
  (`ParanaturalTopos.lean`): Chained equivalences
  giving `μF.a ≃ ParametricFamily (algebraTypeExpr F)`
  and `ℕ ≃ ParametricFamily dinaturalTypeExpr`.

### Observations motivating this workstream

1. `ParametricFamily T` has the form of an end:
   a `Type`-indexed family of diagonal elements of a
   profunctor (`T.interp I I`) together with a condition
   (`T.relInterp f (app I₀) (app I₁)`) that acts as an
   equalizer for each morphism `f`. This is the standard
   presentation of an end as an equalizer of products.

2. `TypeExpr` and `ParametricFamily` are restricted to the
   category `Type`. The double category `YonedaRelDouble`
   was built to generalize to arbitrary `C`. A generalized
   `ParametricExpr` should work over arbitrary categories
   using `YonedaRel` in place of function graphs.

3. `StrongRestrictedWedge` generalizes paranatural
   transformations to weighted limits with codomain `D`.
   A parallel "parametric wedge" construction should
   generalize parametric families the same way.

4. `wedgeWeight` embeds paranatural transformations into
   the twisted-arrow copresheaf topos. A corresponding
   embedding for parametric transformations would place
   both notions in the same topos, enabling direct
   comparison and potentially resolving the
   parametricity/paranaturality divergence at the level of
   copresheaf morphisms.

## Workstream items

### W1. ParametricFamily as an end

Show that `ParametricFamily T` is an end of the profunctor
`T.interp : Typeᵒᵖ × Type → Type` (or more precisely, the
end of the functor that sends `I` to `T.interp I I`, with
the morphism condition being the wedge condition).

This involves:

- Defining `T.interp` as a profunctor (functor
  `Typeᵒᵖ × Type → Type`) and verifying its functoriality
  from `TypeExpr.relInterp`.
- Showing that `ParametricFamily T` is the set of wedge
  elements for this profunctor, i.e., that the
  parametricity condition `T.relInterp f` is the wedge
  condition for the end.
- Relating this to the existing `StructuralEnd`
  construction (which is the end for paranatural
  transformations).

### W2. Generalized ParametricExpr via YonedaRel

Define a generalized version of `TypeExpr` (tentatively
`ParametricExpr`) that works over an arbitrary category
`C` using `YonedaRel` instead of function graphs.

#### W2a. ParametricExpr definition

An analogue of `TypeExpr` where:

- Leaf nodes carry a functor `F : C ⥤ C` (endofunctor on
  `C` rather than `Type ⥤ Type`).
- Arrow nodes combine sub-expressions using the
  function-space lifting of Yoneda relations (the internal
  hom in the presheaf topos).
- The relational interpretation `ParametricExpr.relInterp`
  maps a `YonedaRel X Y` to a new `YonedaRel` (or
  `YonedaProdOver`) by lifting through the type structure.

The leaf case lifts a `YonedaRel R` between `X` and `Y`
to the graph of `F.map` applied to the underlying
relation. The arrow case uses the exponential
(internal hom) in the presheaf category.

#### W2b. TypeExpr as a special case

Show that when `C = Type`, `ParametricExpr` specializes to
`TypeExpr`. This requires showing that the Yoneda relation
lifting agrees with the `graphRel`/`arrowRel` construction.

#### W2c. Internal relations lift to YonedaRel

For any category `C`, show that an internal relation
(a monomorphism or span `R → X × Y` in `C`) lifts to a
`YonedaRel` via the Yoneda embedding, and that this
lifting is compatible with the relation operations
(products, exponentials).

The Yoneda embedding `y : C → PSh(C)` preserves limits
(as a right adjoint / representable functor), so it
preserves the product `X × Y` and thus sends a
relation `R ↪ X × Y` in `C` to a relation
`y(R) → y(X) × y(Y)` in `PSh(C)`. The
`YonedaProdOver` structure is exactly this lifted
relation.

Since `y` is fully faithful, it preserves monomorphisms,
so proof-irrelevant relations (subobjects) in `C` lift
faithfully.

#### W2d. Equivalence via transitivity

Chain the results: `TypeExpr` produces an internal
relation in `Type`; internal relations in `C` lift to
`YonedaRel`; therefore `TypeExpr.relInterp` agrees with
`ParametricExpr.relInterp` when `C = Type`.

### W3. Parametric wedges

Define a "parametric wedge" construction analogous to
`StrongRestrictedWedge`, using the parametric condition
instead of the paranatural condition.

#### W3a. StrongParametricWedge structure

Define `StrongParametricWedge G H T` where:

- `G : Cᵒᵖ ⥤ C ⥤ D` (diagram profunctor, codomain `D`)
- `H : Cᵒᵖ ⥤ C ⥤ Type v` (restriction weight)
- `T : ParametricExpr` (type expression determining the
  parametricity condition)
- The structure contains a point `pt : D` and a family
  satisfying the parametric condition determined by `T`,
  lifting relations via `ParametricExpr.relInterp` rather
  than the `DiagCompat` condition used by
  `StrongRestrictedWedge`.

#### W3b. Specialization to StrongRestrictedWedge

For type expressions where paranaturality and parametricity
agree (algebra profunctor, hom profunctor, etc.),
`StrongParametricWedge` should specialize to
`StrongRestrictedWedge`.

### W4. Twisted-arrow parametric embedding

Embed parametric transformations into the twisted-arrow
copresheaf topos alongside paranatural transformations.

#### W4a. Parametric weight functor

Define a `parametricWeight G H T : TwistedArrow C ⥤ Type v`
analogous to `wedgeWeight G H`, such that natural
transformations from `parametricWeight` into a copresheaf
correspond to parametric families.

The construction should differ from `wedgeWeight` in the
way it handles the arrow case of the type expression:
`wedgeWeight` uses `DiagCompat` (which tests pairs
`(r ∘ f, f ∘ r)`), while `parametricWeight` should test
all pairs `(h, k)` with `f ∘ h = k ∘ f` (or their
`YonedaRel` analogue).

#### W4b. Comparison map

Construct a natural transformation
`wedgeWeight G H → parametricWeight G H T` (or the
reverse direction, depending on which condition is
stronger). For type expressions where paranaturality
implies parametricity, this should be an epimorphism;
for the divergence type, it should not be an isomorphism.

#### W4c. Topos-level analysis

Both `wedgeWeight` and `parametricWeight` live in the
copresheaf topos `[TwistedArrow C, Type v]`. The
divergence between paranaturality and parametricity should
be visible as a difference between the corresponding
copresheaves. Characterize this difference.

## Open questions

1. For W2a, the arrow case requires the exponential
   (internal hom) in the presheaf category. `PSh(C)` is
   always a topos and thus has exponentials, but we may
   need to formalize or import the exponential
   construction. Does mathlib provide `Closed` or
   `CartesianClosed` instances for presheaf categories?

2. For W4a, the parametric weight needs to encode the
   type expression `T` into the weight functor. The
   recursive structure of `T` must be reflected in
   the copresheaf. The right construction may involve
   iterated exponentials in the copresheaf category
   itself.

3. The relationship between W1 (ParametricFamily as end)
   and W3 (parametric wedges) should be clarified: the
   end is the universal parametric wedge, and
   `ParametricFamily T` should be the set of elements of
   this end.

4. For W2c, the statement that internal relations lift
   faithfully to `YonedaRel` depends on the Yoneda
   embedding preserving the relevant limits. For
   products and pullbacks this is standard (Yoneda
   preserves all limits). For exponentials, the
   situation is more subtle: the Yoneda embedding does
   not preserve exponentials in general (it sends them
   to different exponentials in the presheaf category).
   This may affect the arrow case of the lifting.

## Dependencies

- `YonedaRelDouble.lean` (complete)
- `ParanaturalTopos.lean` (ParametricityDivergence section)
- `ComprehensiveWeighted.lean` (wedgeWeight)
- `Weighted.lean` (StrongRestrictedWedge)
- `ParamPoly.lean` (YonedaRel, relComp, etc.)
