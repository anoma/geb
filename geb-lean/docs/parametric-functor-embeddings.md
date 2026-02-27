# Embeddings Into and Out of ParametricCopresheaf

## Definition

`ParametricFunctor E := RelSpanObj ⥤ E`, the
category of functors from the relational span
category `RelSpanObj` to an arbitrary target
category `E`.

`ParametricCopresheaf := ParametricFunctor (Type 1)`,
the copresheaf specialization.

`RelSpanObj` is a bipartite category:

- **typeNodes**: one per `Type`, denoted
  `.typeNode I`
- **relNodes**: one per relation
  `R : I₀ → I₁ → Prop`, denoted
  `.relNode I₀ I₁ R`
- **Morphisms**: identities, plus `fstProj` and
  `sndProj` from each relNode to its endpoint
  typeNodes. No morphisms between distinct
  typeNodes or between distinct relNodes.

A parametric functor `P` assigns a type to each
typeNode and relNode, with projection maps from
relNodes to typeNodes. The absence of morphisms
between same-kind objects means the values at
distinct typeNodes (or relNodes) are independent
except through the projection constraints.

## Embeddings into ParametricCopresheaf

### Covariant endofunctors (fully faithful)

`covariantEmbedding : (Type ⥤ Type) ⥤ ParametricCopresheaf`

- `typeNode I ↦ ULift (F.obj I)`
- `relNode I₀ I₁ R ↦ ULift (covRelImage F R)`

where `covRelImage F R` is the subtype of
`F.obj I₀ × F.obj I₁` consisting of pairs in the
image of `(F.map π₁, F.map π₂)` from
`F.obj (relType R)`. This is the Barr extension
(covariant relation lifting) of `F` at `R`.

Fully faithful because:

- **Faithful**: a natural transformation
  `α : F ⟶ G` is determined by `α.app I` for each
  `I`, which the embedding preserves at typeNodes.
- **Full**: the relNode component of a copresheaf
  map is a subtype of the product, determined by
  its pair projections via naturality at
  `fstProj`/`sndProj`. The preimage's naturality
  uses graph relations: `relType (graphRel f) ≅ I₀`
  gives a witness connecting `F.map f` to the
  projections.

### Contravariant functors (fully faithful)

`contravariantEmbedding : (Typeᵒᵖ ⥤ Type) ⥤ ParametricCopresheaf`

- `typeNode I ↦ ULift (F.obj (op I))`
- `relNode I₀ I₁ R ↦ ULift (contraRelImage F R)`

where `contraRelImage F R` is the pullback: pairs
`(a, b) ∈ F.obj (op I₀) × F.obj (op I₁)` with
`F.map (op π₁) a = F.map (op π₂) b` in
`F.obj (op (relType R))`.

Fully faithful by the same argument (pullback is a
subtype of the product; naturality at
`fstProj`/`sndProj` determines the pair; graph
relations + `graphRelEquiv` provide the witness).

### Type expressions (fully faithful)

`relSpanDiagramFunctor : TypeExprCat ⥤ ParametricCopresheaf`

- `typeNode I ↦ ULift (T.interp I I)`
- `relNode I₀ I₁ R ↦ ULift (T.relFiber R)`

where `T.relFiber R` is the subtype of
`T.interp I₀ I₀ × T.interp I₁ I₁` satisfying the
full relational interpretation
`T.fullRelInterp R`.

Fully faithful by the same pattern.

### Profunctors with natural morphisms (neither)

`profunctorEmbedding : (Typeᵒᵖ × Type ⥤ Type) ⥤ ParametricCopresheaf`

- `typeNode I ↦ ULift (G.obj (op I, I))`
  (diagonal only)
- `relNode I₀ I₁ R ↦ ULift (profRelImage G R)`

**Not faithful**: a natural transformation
`α : G ⟶ H` of profunctors has components at all
`(op A, B)`, but the embedding only sees the
diagonal `(op I, I)`. Two natural transformations
agreeing on the diagonal can differ off-diagonal.

**Not full**: the diagonal components of a
copresheaf map do not determine a natural
transformation (off-diagonal components must be
constructed but are unconstrained by the
copresheaf data).

### Profunctors with paranatural morphisms (faithful)

`paranaturalProfEmbedding : EndoProf(Type) ⥤ ParametricCopresheaf`

Same object map as `profunctorEmbedding`, but on
morphisms maps paranatural transformations
(which have diagonal-only components with a
`DiagCompat`-preservation condition) rather than
natural transformations.

**Faithful**: a paranatural transformation is
determined by its diagonal components, which the
embedding preserves.

**Not full in general**: recovering the
`DiagCompat` condition from the copresheaf data
requires cancelling `(H.map (op π₁)).app I₁`,
which is not injective for all profunctors.

## Embeddings out of ParametricCopresheaf

### Into profunctors: no natural functor

`RelSpanObj` has no morphisms between distinct
typeNodes. A profunctor requires functorial
transport `G.map (op f, g)` between arbitrary
`G.obj (op A, B)` values. Since a parametric
functor provides no transport between typeNode
values, there is no natural way to construct a
profunctor from a parametric functor.

### Into EndoProf: no natural functor

Same reason. `EndoProf` objects are profunctors;
even though morphisms are paranatural
(diagonal-only), the objects still carry
covariant/contravariant structure that cannot be
derived from a parametric functor.

### Into twisted-arrow copresheaves: no natural functor

Mapping `P : ParametricCopresheaf` to
`F : TwistedArrow(Type) ⥤ Type 1` requires
defining `F.map` at twisted-arrow morphisms,
which needs transport between distinct relNodes
of `P`. No such transport exists.

The reverse direction (twisted-arrow copresheaves
into `ParametricCopresheaf`) would require a
functor `RelSpanObj → TwistedArrow(Type)`, which
fails because the `fstProj` map at non-left-total
relations has no corresponding twisted-arrow
morphism.

## Structural explanation

`RelSpanObj` is a "wide span" category: many
objects, but only projection morphisms from
relNodes to typeNodes. This structure makes
`ParametricFunctor E` (and its copresheaf
specialization `ParametricCopresheaf`):

- **Receptive**: functors from `RelSpanObj` have
  few naturality constraints (only at projections),
  so many categories embed faithfully or fully
  faithfully into the copresheaf specialization.
  The pattern is: define the relNode type as a
  subtype of the product of typeNode types, so that
  (a) the pair projections determine the subtype
  element (giving fullness via naturality at
  `fstProj`/`sndProj`), and (b) the subtype
  condition carries enough structure for the
  preimage's coherence conditions (giving the
  preimage's naturality/paranaturality).

- **Isolated**: no natural functors out of
  `ParametricCopresheaf` into richer categories
  (profunctors, twisted-arrow copresheaves),
  because `RelSpanObj` lacks the inter-object
  morphisms needed to build transport maps.

The relationship between `ParametricCopresheaf`
and the twisted-arrow copresheaf topos (where
paranatural transformations live as weighted
cones) is therefore at the level of specific
limits and colimits, not at the level of
category-wide functors.

## Summary table

| Embedding | Direction | Full | Faithful |
| - | - | - | - |
| `covariantEmbedding` | `[Type,Type] → PC` | Y | Y |
| `contravariantEmbedding` | `[Typeᵒᵖ,Type] → PC` | Y | Y |
| `relSpanDiagramFunctor` | `TypeExprCat → PC` | Y | Y |
| `profunctorEmbedding` | `[Typeᵒᵖ×Type,Type]_nat → PC` | N | N |
| `paranaturalProfEmbedding` | `EndoProf_paranat → PC` | N | Y |
| (none) | `PC → Profunctors` | — | — |
| (none) | `PC → EndoProf` | — | — |
| (none) | `PC ↔ TwArr copresheaves` | — | — |

(`PC` = `ParametricCopresheaf`)
