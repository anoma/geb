# Parametric Generalization

## Status: TypeExprCat complete; HomInd characterization next

### TypeExprCat (completed)

`TypeExprCat` is a category whose objects are `TypeExpr` and
whose morphisms `T₁ → T₂` are
`ParametricFamily (.arrow T₁ T₂)` — relation-preserving
polymorphic functions.  Identity is `id`, composition is
pointwise function composition with proofs composed by modus
ponens.  Category laws are definitional (`rfl`).

`ParametricFamily T ≅ Hom(unit, T)` where
`TypeExpr.unit = .app ((Functor.const Type).obj PUnit) .var`.
This makes `ParametricFamily` representable.

Existing free theorems restated as `Hom` computations:

- `typeExprHom_var_var : Hom(var, var) ≃ Unit`
- `typeExprHom_leaf_leaf F G : Hom(leaf F, leaf G) ≃ (F ⟶ G)`
- `typeExprHomUnit_algebra : Hom(unit, algebraTypeExpr F) ≃ μF.a`

`ParametricWedge T` defined with `ParametricFamily T` as its
terminal object.

### PshRel subobject refactoring (completed)

`PshRel` has been changed from `Skeleton (PshProdOver P Q)` to
`Subfunctor (pshProdPresheaf P Q)`.

### RelSpanObj ≅Cat PshRelSpanObj (Discrete PUnit) (completed)

`PshRelSpanDiagram.lean` now contains a categorical isomorphism
`relSpanPshRelSpanIso` witnessing that `RelSpanObj` is the
terminal-category specialization of `PshRelSpanObj C`.

Definitions added:

- `propRelToTypeRel` / `typeRelToPropRel`: convert between
  `Prop`-valued relations and `TypeRel` (subfunctor-based)
- `pshRelToPropRel`: extract `Prop`-valued relation from `PshRel`
- `pshOnUnit_eq_const`: presheaves on `(Discrete PUnit)ᵒᵖ` are
  constant
- `relSpanToPshRelSpan` / `pshRelSpanToRelSpan`: mutually inverse
  functors
- `relSpanPshRelSpan_unit` / `relSpanPshRelSpan_counit`: both
  round-trip composites equal the identity (as functor equalities
  via `Functor.ext`)
- `relSpanPshRelSpanIso : RelSpanObj ≅Cat PshRelSpanObj (Discrete
  PUnit)`: the `Cat`-isomorphism

The counit object equality for the `relNode` case uses a double
`@Eq.ndrec` to handle the dependent type in
`PshRelSpanObj.relNode`. The counit morphism compatibility uses
`heq_iff_comp_eqToHom_comp` with factored-out HEq lemmas
(`fstProj_heq`, `sndProj_heq`,
`propRelToTypeRel_pshRelToPropRel_heq`).

### Analysis results

`profRelInterp` / `biRelMap` are oplax on `TypeRelCat` (the
composition inclusion goes
`biRelMap T R₁ S₁ ∘ biRelMap T R₂ S₂ ⊆
biRelMap T (R₂ ∘ R₁) (S₁ ∘ S₂)` but not equality).
The arrow case is not strictly functorial because
`arrowRel` requires a uniform intermediate function while
existential composition provides only pointwise witnesses.

`TypeExprCat` avoids this: its morphisms carry
relation-preservation proofs intrinsically, so composition
uses modus ponens rather than existential quantification.

### Next: Inductive morphism characterization (HomInd)

Define `HomInd(T₁, T₂)` by recursion on pairs of `TypeExpr`,
with structural proof content (naturality, commuting diagrams)
rather than semantic (`fullRelInterp` for all `R`).  The
equivalence `HomInd ≅ Hom` is the general free theorem.
See `docs/plans/2026-02-25-typeexprcat-design.md`.

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

#### W2a. Compute wedgeWeight for standard profunctors (in progress)

Expand the `wedgeWeight` construction for the three cases
where paranaturality gives the right answer:

- `AlgProf F` (algebra profunctor of an endofunctor `F`)
- `CoalgProf F` (coalgebra profunctor)
- `HomProf` (hom profunctor, for dinatural numbers)

In each case, determine what the twisted-arrow copresheaf
`wedgeWeight G H : TwistedArrow C ⥤ Type v` looks like
concretely. This yields reference examples for what a
"correct" weight functor should produce.

##### Completed results (WedgeWeightComputation.lean)

- `wedgeWeightIdentityMap H I`: canonical map from
  `diagApp H I` to `(wedgeWeight H).obj (twObjMk (𝟙 I))`
- `wedgeWeightExtract H I`: extraction function from
  costructured arrows over the identity twisted arrow
  back to diagonal elements
- `wedgeWeightExtract_canonical`: extraction sends
  canonical arrows to their diagonal elements
- `wedgeWeightExtract_invariant`: extraction is invariant
  under costructured arrow morphisms (the main technical
  lemma)
- `wedgeWeightExtractLifted H I`: extraction lifted to
  connected components via `Quotient.lift`
- `wedgeWeightIdentityMap_injective`: the canonical map
  is injective (proved via left inverse)
- `diagApp_algProf`: `diagApp (AlgProf F) I = (F.obj I ⟶ I)`
- `diagApp_coalgProf`: `diagApp (CoalgProf F) I = (I ⟶ F.obj I)`

##### Analysis (docs/wedge-weight-factorization-analysis.md)

- General factorization characterization: for any
  profunctor `H`, `(wedgeWeight H).obj tw` at
  `tw = (f : A ⟶ B)` is the set of connected components
  of factorizations of `f` through a `DiagElem(H)` morphism.
- Surjectivity of `wedgeWeightIdentityMap` likely fails in
  general; it may hold for specific profunctors via
  universal properties.
- Natural transformations to `IdProf` are determined by
  values at identity twisted arrows.
- Dual characterization for `cowedgeWeight`: connected
  components of factorizations through `DiagElem(H)`
  morphisms in the co-twisted-arrow direction.

##### relInterp composition (RelInterpComposition.lean)

Structural analysis of when `T.relInterp` composes
transitively (prerequisite for defining `ParamDiagElem T`
as a category):

- `graphRel_comp`, `graphRel_decomp`: graph relations
  compose and decompose.
- `TypeExpr.isArrowFree`: predicate for type expressions
  built from `var` and `app` only (no `arrow`).
- `TypeExpr.arrowFreeMap`: the covariant map for
  arrow-free types; `arrowFreeMap_comp` proves
  functorial composition.
- `TypeExpr.relInterp_eq_graphRel`: for arrow-free T,
  `T.relInterp f = graphRel (arrowFreeMap T haf f)`.
- `relInterp_comp_of_isArrowFree`,
  `relInterp_decomp_of_isArrowFree`: composition and
  decomposition for arrow-free types.
- `arrowRel_comp`: conditional composition for
  `arrowRel` given domain decomposition and codomain
  composition.
- `TypeExpr.hasRelInterpComp`: structural predicate
  classifying which type expressions have composable
  `relInterp`. Satisfied when every `arrow` node has
  an arrow-free domain.
- `relInterp_comp_of_hasComp`: composition for types
  satisfying `hasRelInterpComp`.
- Classification of standard examples:
  - `dialgebraTypeExpr F G` (`F(X) → G(X)`): has comp
  - `homTypeExpr` (`X → X`): has comp
  - `dinaturalTypeExpr` (`(X → X) → (X → X)`): no comp
    (domain `X → X` is not arrow-free)
  - `algebraTypeExpr F` (`(F(X) → X) → X`): no comp
    (domain `F(X) → X` is not arrow-free)
  - `divTypeExpr` (`((X → X) → X) → X`): no comp
- `relInterp_decomp_homTypeExpr_fails`: counterexample
  proving decomposition fails for `arrow var var` using
  `Unit`, `Bool`, `Fin 3`.

The structural result: `hasRelInterpComp` is very
restrictive, holding only for "shallow" arrows where
no arrow appears in a domain position. For the
algebra and dinatural types where parametricity and
paranaturality are known to agree, the composability
of `relInterp` relies on the specific relational
structure rather than the generic type-expression
criterion. Defining `ParamDiagElem` as a category
using `relInterp` morphisms fails for most
type expressions of interest.

##### Remaining for W2a

- Formalize `WedgeWeightFactorization` as an explicit
  structure and show it matches `CostructuredArrow` data.
- Define `typeExprWeight : TypeExpr → (TwistedArrow Type ⥤ Type)`
  recursively using `relInterp` pairs.
- Construct comparison natural transformation
  `typeExprWeight T → wedgeWeight (T.toProfunctor)`.

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

6. Both covariant functors `(Type ⥤ Type)` and
   contravariant functors `(Typeᵒᵖ ⥤ Type)` embed
   fully faithfully into `ParametricCopresheaf`
   (`RelSpanObj ⥤ Type 1`). What is the
   relationship between `ParametricCopresheaf` and
   profunctors `(Typeᵒᵖ × Type ⥤ Type)`? Is there
   a faithful embedding of profunctors into
   `ParametricCopresheaf`, or of
   `ParametricCopresheaf` into profunctors, or
   neither? The covariant embedding uses the Barr
   extension (`covRelImage`/`functorRelLift`) at
   relNodes, while the contravariant uses a
   pullback
   (`contraRelImage`/`contravariantRelLift`). A
   profunctor has both covariant and contravariant
   arguments, so its embedding would need to
   combine both constructions. The relNode type
   for a profunctor `P` at relation `R` might be
   `{ (a, b) : P(I₀, I₀) × P(I₁, I₁) //
   ∃ w : P(I₀, I₁), ... }` or a pullback/image
   hybrid. Understanding this would clarify how
   `ParametricCopresheaf` relates to the
   twisted-arrow copresheaf topos where paranatural
   transformations live.

   Resolved: `profunctorEmbedding` is a functor
   (via `profRelImage`) but neither full nor
   faithful (only sees diagonal). No natural
   embedding from ParametricCopresheaf to
   profunctors or twisted-arrow copresheaves
   (RelSpanObj too discrete). No embedding from
   TwArr copresheaves to ParametricCopresheaf
   either (would need
   left-totality of all relations). The
   relationship is at the level of specific
   limits, not category-wide functors.

   Update: `paranaturalProfEmbedding` (profunctors
   with PARANATURAL morphisms → ParametricCopresheaf)
   is a valid functor. The FullyFaithful proof
   is in progress -- the embedding functor
   compiles, and the structure matches
   (paranaturality = `DiagCompat` preservation =
   `diagRelImage` transport). Faithful should hold
   (paranatural transformations determined by
   diagonal components). Full should hold
   (`diagRelImage` is a product subtype). This
   would make `endoProfCategory` a full
   subcategory of `ParametricCopresheaf`.

7. Generalize `RelSpanDiagram.lean` to presheaves
   on arbitrary `C` (creating
   `PshRelSpanDiagram.lean`). Replace `Type` with
   `PSh(C)`, `R : I₀ → I₁ → Prop` with `PshRel`,
   `relType R` with the corresponding presheaf
   subobject. The current `RelSpanDiagram` would be
   the special case `C = terminal category`.

8. Research question: does `ParametricCopresheaf`
   have a universal property within `Cat`?
   Written up in
   `docs/parametric-functor-universal-property.md`.

## Completed infrastructure for generalization

### PshRelDouble.lean additions

- `pshIhom` (internal hom presheaf): for
  `D : Type w, Category.{w} D` (same universe for
  objects and morphisms)
- `pshCurry`, `pshUncurry`: adjunction morphisms
- `pshIhomProfMap`: profunctor structure on `pshIhom`
- `pshBarrLift`, `pshBarrLiftSkel`: Barr extension
  (canonical relation lifting through functors)
- `pshArrowRel`, `pshArrowRelSkel`: arrow relation
  for internal hom in presheaf categories
- `PshExponentialData A B E`: data witnessing `E` as
  exponential of `A` and `B` via evaluation/currying
- `pshIhomYonedaRepresentableBy`: `pshIhom (y A) (y B)`
  is representable by `E`, given `PshExponentialData`
- `pshIhomYonedaIso`: the isomorphism
  `yoneda.obj E ≅ pshIhom (yoneda.obj A) (yoneda.obj B)`

### PshTypeExpr.lean

- `PshTypeExpr C`: type expressions for presheaf
  categories, generalizing `TypeExpr` from `Type` to
  `PSh(C)`
- `PshTypeExpr.interp`, `profMap`, `relInterp`:
  interpretation as profunctor, profunctor action, and
  relational interpretation

### Universe constraint for bridge

`pshIhom` requires `Category.{w} D` (same universe for
objects and morphisms). `Type v` has objects in
`Type (v+1)` and morphisms in `Type v`, so `pshIhom`
does not apply to `D = Type v`. The bridge from
`TypeExpr` (over `Type`) to `PshTypeExpr` (over
`PSh(C)`) is deferred until `pshIhom` is generalized
to separate universe levels or a different approach is
found.

### Full relational interpretation and type abstractions

#### ParanaturalTopos.lean additions

- `TypeExpr.fullRelInterp T R`: generalization of
  `relInterp` from function graphs (`graphRel f`) to
  arbitrary binary relations `R : I₀ → I₁ → Prop`
- `TypeExpr.fullRelInterp_graphRel`: `fullRelInterp`
  at `graphRel f` coincides with `relInterp f`
- `TypeAbs T`: type abstractions
  `(I : Type) → T.interp I I`, following Wadler's
  `∀X. T(X)` (Theorems for Free, 1989)
- `typeAbsRel T t₀ t₁`: relatedness of type
  abstractions under the full relational
  interpretation — two abstractions are related if
  for all types `I₀, I₁` and all relations
  `R : I₀ → I₁ → Prop`, the specializations are
  related by `T.fullRelInterp R`
- `typeAbsRel_self_implies_parametric`: self-relatedness
  under `typeAbsRel` implies parametricity (the
  condition of `ParametricFamily`)
- `ParametricFamily.ofTypeAbsRel`: constructor for
  `ParametricFamily` from a self-related type
  abstraction

#### PshTypeExpr.lean additions (presheaf-level)

- `PshTypeExpr.fullRelInterp T R`: presheaf-level
  full relational interpretation for arbitrary
  `R : PshRel P Q`
- `PshTypeExpr.fullRelInterp_graph`:
  `fullRelInterp (pshRelGraph α) = relInterp α`
- `PshProdOver.sectionsRelated R s₀ s₁`: predicate
  relating two sections `s₀, s₁` of presheaves `F, G`
  via a `PshProdOver F G` witness
- `pshRelSectionsRelated R s₀ s₁`: relating sections
  via `PshRel` (well-defined on isomorphism classes)
- `PshTypeAbs T`: presheaf type abstractions,
  `(P : PSh(C)) → (T.interp P P).sections`
- `pshTypeAbsRel T t₀ t₁`: presheaf-level relatedness

#### PshTypeExpr.lean additions (Type↔presheaf bridge)

- `yonedaULiftMap f`: lifts `f : A → B` to
  `yonedaULift A ⟶ yonedaULift B` via whiskerRight
- `yonedaULiftRelPsh R`: presheaf of `R`-related
  pairs at ULift-Yoneda representables
- `yonedaULiftRelOver R`, `yonedaULiftRel R`:
  lifts `R : A → B → Prop` to
  `PshRel (yonedaULift A) (yonedaULift B)`
- `yonedaULiftSection a`: converts `a : X` to a
  section of `yonedaULift X` (constant family)
- `sectionMap α s`: transports a section along a
  natural transformation
- `TypeExpr.toInterpSection T a`: converts
  `a : T.interp X X` to a section of
  `T.toPshTypeExpr.interp (yonedaULift X) ...`
  via `toPshTypeExpr_interp_iso`
- `yonedaULiftRelOver_sectionsRelated_iff`:
  `(yonedaULiftRelOver R).sectionsRelated
    (yonedaULiftSection a₀) (yonedaULiftSection a₁)
    ↔ R a₀ a₁` — the lifting of relations is
  faithful at the level of constant sections
- `fullRelInterp_bridge_var`: the `var` case of the
  bridge, showing `fullRelInterp` at the Type level
  corresponds to `fullRelInterp` at the presheaf
  level through the ULift-Yoneda embedding

##### Remaining for bridge

The `app` and `arrow` induction cases of
`fullRelInterp_bridge` require relating
`functorRelLift F` to `pshBarrLiftSkel (yonedaExt F)`
and `arrowRel` to `pshArrowRelSkel` through
`toPshTypeExpr_interp_iso`. These form the substance
of the general bridge between `typeAbsRel` and
`pshTypeAbsRel`.

## Dependencies

- `YonedaRelDouble.lean` (complete)
- `ParanaturalTopos.lean` (ParametricityDivergence section)
- `ComprehensiveWeighted.lean` (wedgeWeight)
- `Weighted.lean` (StrongRestrictedWedge)
- `ParamPoly.lean` (YonedaRel, relComp, etc.)
- `PshRelDouble.lean` (Barr extension, arrow relation,
  Yoneda-exponential preservation)
- `PshTypeExpr.lean` (generalized type expressions)
