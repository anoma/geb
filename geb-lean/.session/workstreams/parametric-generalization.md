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
  with `.var`, `.app (F : Type ⥤ Type) (T : TypeExpr)`,
  and `.arrow T₁ T₂`, representing type expressions in
  one variable over `Type`.
- `TypeExpr.relInterp`: Relational interpretation
  replacing `var` with the given relation, `app` with
  `functorRelLift F`, and `arrow` with `arrowRel`.
- `TypeExpr.profMap`: Profunctor action (covariant and
  contravariant maps) on `T.interp`.
- `ParametricFamily T` (`ParanaturalTopos.lean`): A
  `Type`-indexed family `app : (I : Type) → T.interp I I`
  with `T.relInterp f (app I₀) (app I₁)` for all `f`.
- `TypeExpr.relInterp_of_offDiag`: Off-diagonal elements
  produce related pairs via `relInterp`.
- `TypeExpr.relInterp_implies_wedge`: The relational
  interpretation implies the profunctor wedge condition.
- `ParametricFamily.wedge`: Every parametric family
  satisfies the profunctor wedge condition.
- `strongRestrictedWedge_weightedCone_equivalence`
  (`ComprehensiveWeighted.lean`): Characterizes strong
  restricted wedges as weighted cones in the
  twisted-arrow category.
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

### W1. ParametricFamily and the profunctor end

#### W1a. Relationship between relInterp and wedge (done)

Proved two mutually dependent results by induction on
`TypeExpr` (`relInterp_wedge_aux`):

- `TypeExpr.relInterp_of_offDiag`: For
  `c : T.interp I₁ I₀`, the pair
  `(T.profMap f id c, T.profMap id f c)` satisfies
  `T.relInterp f`. Analogue of `diagCompat_of_offDiag`.
- `TypeExpr.relInterp_implies_wedge`: If
  `T.relInterp f x₀ x₁`, then
  `T.profMap id f x₀ = T.profMap f id x₁`.
- `ParametricFamily.wedge`: Every parametric family
  satisfies the profunctor wedge condition.

The converse of `relInterp_implies_wedge` does NOT hold
in general: for nested arrows like `((X → X) → X) → X`,
`relInterp` tests all commuting pairs `(h, k)` while the
wedge tests only pairs `(T₁.profMap f id c,
T₁.profMap id f c)` arising from off-diagonal elements.
This is the parametricity/paranaturality gap:

- `relInterp` = parametricity (stronger)
- wedge = paranaturality (weaker)

So `ParametricFamily T` is NOT the end of `T.toProfunctor`.
Every parametric family is a wedge element (end element),
but not every wedge element is parametric.

#### W1b. Characterize when the converse holds

The converse holds when all related pairs `(a₀, a₁)` in
the domain arise as projections of off-diagonal elements.
This is the case for leaves and single-level arrows
(algebra profunctor, hom profunctor) but fails for nested
arrows. Formalizing this characterization would give a
structural criterion on `TypeExpr` for when
parametricity = paranaturality.

### W2. ParametricFamily as weighted cones

Since `ParametricFamily T` is not the end of
`T.toProfunctor` (W1a), it cannot be characterized as
the standard wedge weight. However, ends are a special
case of weighted cones in twisted-arrow categories
(`strongRestrictedWedge_weightedCone_equivalence`
characterizes paranatural wedges this way). The question
is whether `ParametricFamily` admits a characterization
as weighted cones for a different weight.

#### W2a. Compute wedgeWeight for standard profunctors

Expand the `wedgeWeight` construction for the three cases
where paranaturality gives the right answer:

- `AlgProf F` (algebra profunctor of an endofunctor `F`)
- `CoalgProf F` (coalgebra profunctor)
- `HomProf` (hom profunctor, for dinatural numbers)

In each case, determine what the twisted-arrow copresheaf
`wedgeWeight G H : TwistedArrow C ⥤ Type v` looks like
concretely. This yields reference examples for what a
"correct" weight functor should produce.

#### W2b. Find a weight for ParametricFamily

Using the concrete descriptions from W2a as guidance,
find a weight functor
`parametricFamilyWeight T : TwistedArrow Type ⥤ Type v`
such that weighted cones with this weight correspond to
parametric families. The weight must differ from
`wedgeWeight` in the arrow case, encoding the full
relational condition `T.relInterp` rather than the
weaker `DiagCompat` condition.

#### W2c. Comparison with wedgeWeight

For type expressions where paranaturality and
parametricity agree, `parametricFamilyWeight T` should
be isomorphic to the corresponding `wedgeWeight`. For
the divergence type, they should differ. Construct the
comparison map and characterize when it is an
isomorphism.

### W3. Parametric cowedges and terminal coalgebras

The dual of the initial algebra result: parametric
families applied to `AlgProf F` give initial algebras.
The question is whether parametric cowedges (the dual
construction) applied to `CoalgProf F` give terminal
coalgebras.

#### W3a. Define parametric cowedges

Define `ParametricCofamily T` (or a similar structure)
dualizing `ParametricFamily`: a `Type`-indexed family
with the coparametricity condition (the dual of
`T.relInterp`). This should be the analogue for
parametricity of what `StrongRestrictedCowedge` (if
defined) would be for paranaturality.

#### W3b. Terminal coalgebra characterization

Show that for an endofunctor `F : Type ⥤ Type` with a
terminal coalgebra `νF`, there is an equivalence
`νF.a ≃ ParametricCofamily (coalgebraTypeExpr F)`.
This would be the dual of
`initialAlgebraParametricEquiv`.

### W4. Generalized ParametricExpr via YonedaRel

Define a generalized version of `TypeExpr` (tentatively
`ParametricExpr`) that works over an arbitrary category
`C` using `YonedaRel` instead of function graphs.

#### W4a. ParametricExpr definition

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

#### W4b. TypeExpr as a special case

Show that when `C = Type`, `ParametricExpr` specializes to
`TypeExpr`. This requires showing that the Yoneda relation
lifting agrees with the `graphRel`/`arrowRel` construction.

#### W4c. Internal relations lift to YonedaRel

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

#### W4d. Equivalence via transitivity

Chain the results: `TypeExpr` produces an internal
relation in `Type`; internal relations in `C` lift to
`YonedaRel`; therefore `TypeExpr.relInterp` agrees with
`ParametricExpr.relInterp` when `C = Type`.

### W5. Parametric wedges

Define a "parametric wedge" construction analogous to
`StrongRestrictedWedge`, using the parametric condition
instead of the paranatural condition.

#### W5a. StrongParametricWedge structure

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

#### W5b. Specialization to StrongRestrictedWedge

For type expressions where paranaturality and parametricity
agree (algebra profunctor, hom profunctor, etc.),
`StrongParametricWedge` should specialize to
`StrongRestrictedWedge`.

### W6. Twisted-arrow parametric embedding

Embed parametric transformations into the twisted-arrow
copresheaf topos alongside paranatural transformations.

#### W6a. Parametric weight functor

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

#### W6b. Comparison map

Construct a natural transformation
`wedgeWeight G H → parametricWeight G H T` (or the
reverse direction, depending on which condition is
stronger). For type expressions where paranaturality
implies parametricity, this should be an epimorphism;
for the divergence type, it should not be an isomorphism.

#### W6c. Topos-level analysis

Both `wedgeWeight` and `parametricWeight` live in the
copresheaf topos `[TwistedArrow C, Type v]`. The
divergence between paranaturality and parametricity should
be visible as a difference between the corresponding
copresheaves. Characterize this difference.

## Open questions

1. For W4a, the arrow case requires the exponential
   (internal hom) in the presheaf category. `PSh(C)` is
   always a topos and thus has exponentials, but we may
   need to formalize or import the exponential
   construction. Does mathlib provide `Closed` or
   `CartesianClosed` instances for presheaf categories?

2. For W6a, the parametric weight needs to encode the
   type expression `T` into the weight functor. The
   recursive structure of `T` must be reflected in
   the copresheaf. The right construction may involve
   iterated exponentials in the copresheaf category
   itself.

3. Since `ParametricFamily T` is NOT the end of
   `T.toProfunctor` (W1a), the relationship between
   `ParametricFamily` and weighted cones (W2) is the
   central question. If `ParametricFamily` can be
   expressed as weighted cones for a suitable weight,
   then `StrongParametricWedge` (W5) should be the
   generalization of that weighted-cone characterization
   to arbitrary codomain `D`.

4. For W4c, the statement that internal relations lift
   faithfully to `YonedaRel` depends on the Yoneda
   embedding preserving the relevant limits. For
   products and pullbacks this is standard (Yoneda
   preserves all limits). For exponentials, the
   situation is more subtle: the Yoneda embedding does
   not preserve exponentials in general (it sends them
   to different exponentials in the presheaf category).
   This may affect the arrow case of the lifting.

5. For W3, the dual of `relInterp` needs to be defined.
   The standard dual of a relation `R(x₀, x₁)` replaces
   universal quantification with existential, so the
   coparametricity condition would state that there
   exist witnesses rather than that all witnesses
   satisfy the condition. The correct formulation needs
   to be determined.

## Dependencies

- `YonedaRelDouble.lean` (complete)
- `ParanaturalTopos.lean` (ParametricityDivergence section)
- `ComprehensiveWeighted.lean` (wedgeWeight)
- `Weighted.lean` (StrongRestrictedWedge)
- `ParamPoly.lean` (YonedaRel, relComp, etc.)
