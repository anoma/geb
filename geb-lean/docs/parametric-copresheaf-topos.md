# The Parametric Copresheaf Topos

## Overview

This document describes the general categorical framework for
parametric polymorphism based on copresheaves on the relational
span category `PshRelSpanObj C`. The construction does not
depend on any inductively-defined type language; it uses only
the double category of presheaf relations, the Yoneda
embedding, and the relational span category.

The three layers of the construction are:

1. `PshRelDouble` -- the double category of relations internal
   to presheaf categories (standard)
2. `YonedaRel` -- lifting of an ordinary category `C` to
   relations between representable presheaves (standard)
3. `PshRelSpanObj C` -- the relational span category, whose
   copresheaf category is a Grothendieck topos serving as the
   ambient universe for parametric polymorphism over `PSh(C)`

## 1. Presheaf relations

### 1.1 Definition

A presheaf relation `R : PshRel P Q` between presheaves
`P, Q : C^op => Type` is a subfunctor of the product
presheaf `P x Q`. Concretely, `R` picks out, at each stage
`c : C^op`, a subset of `P(c) x Q(c)`, compatibly with
restriction maps.

Code: `PshRel` (`PshRelDouble.lean:206`), defined as
`Subfunctor (pshProdPresheaf P Q)`.

### 1.2 Double category structure

Presheaf relations form a double category `PshRelDouble`:

- **Horizontal morphisms**: natural transformations between
  presheaves
- **Vertical morphisms**: presheaf relations `PshRel P Q`
- **Squares**: given horizontal morphisms `alpha : P => P'`,
  `beta : Q => Q'` and vertical morphisms `R : PshRel P Q`,
  `S : PshRel P' Q'`, a square witnesses that `alpha` and
  `beta` map R-related pairs to S-related pairs
  (`pshRelRelated`, `PshRelDouble.lean:682`)

Operations and laws:

| Operation | Code | Line |
|-----------|------|------|
| Identity relation | `pshRelId` | 212 |
| Relation composition | `pshRelComp` | 358 |
| Graph of nat. trans. | `pshRelGraph` | 416 |
| Dagger (transpose) | `pshRelDagger` | 535 |
| Graph functor | `pshRelGraphFunctor` | 472 |
| Left identity | `pshRelComp_id_left` | 371 |
| Right identity | `pshRelComp_id_right` | 385 |
| Associativity | `pshRelComp_assoc` | 399 |
| Dagger involution | `pshRelDagger_dagger` | 541 |
| Double cat. data | `pshRelDoubleData` | 917 |

All references in `GebLean/PshRelDouble.lean`.

### 1.3 Relation lifting

Given an endofunctor `G : PSh(C) => PSh(C)` and a relation
`R : PshRel P Q`, the **Barr extension** (relation lifting)
`pshBarrLiftSkel G R : PshRel (G P) (G Q)` produces the
relation whose witnesses are pairs `(G(pi_1)(w), G(pi_2)(w))`
for `w` in the Barr lift of `R` through `G`.

Variants:

| Variant | Functor type | Code | Line |
|---------|-------------|------|------|
| Covariant | `PSh(C) => PSh(C)` | `pshBarrLiftSkel` | 999 |
| Contravariant | `PSh(C)^op => PSh(C)` | `pshContraBarrLiftSkel` | 1494 |
| Profunctor | `PSh(C)^op x PSh(C) => PSh(C)` | `pshProfBarrLiftSkel` | 1714 |
| Arrow | internal hom | `pshArrowRelSkel` | 2158 |

All in `GebLean/PshRelDouble.lean`.

The Barr extension of a graph relation recovers the graph of
the functor's action: `pshBarrLiftSkel_graph`
(`PshRelDouble.lean:1186`).

### 1.4 Arrow relation

Given relations `R_1 : PshRel P_1 Q_1` and
`R_2 : PshRel P_2 Q_2`, the arrow relation
`pshArrowRelSkel R_1 R_2` relates internal-hom elements
`f : P_1 => P_2` and `g : Q_1 => Q_2` when `f` maps
R_1-related inputs to R_2-related outputs via `g`
(`PshRelDouble.lean:2158`).

This is the presheaf-level analogue of Wadler's relational
interpretation of function types.

## 2. Yoneda relations

### 2.1 Definition

A Yoneda relation `YonedaRel X Y` between objects
`X, Y : C` is a presheaf relation between their
representable presheaves:
`YonedaRel X Y = PshRel (yoneda X) (yoneda Y)`
(`YonedaRelDouble.lean:304`).

This embeds the morphisms of `C` into relations via the
graph construction: `yonedaRelGraph f` for `f : X => Y`
(`YonedaRelDouble.lean:401`).

### 2.2 Double category structure

Yoneda relations form their own double category
`yonedaRelDoubleData` (`YonedaRelDouble.lean:768`), which
is a sub-double-category of `PshRelDouble`. The graph
functor `yonedaRelGraphFunctor : C => YonedaRelCat`
(`YonedaRelDouble.lean:447`) embeds `C` into its double
category of Yoneda relations.

### 2.3 Terminal specialization

When `C = Discrete PUnit`, Yoneda relations specialize to
ordinary type-level relations `R : I_0 => I_1 => Prop`.
The specialization is `terminalYonedaRelDoubleData`
(`YonedaRelDouble.lean:803`).

## 3. The relational span category

### 3.1 Definition

`PshRelSpanObj C` is a category whose objects are:

- `.typeNode P` for each presheaf `P : C^op => Type`
- `.relNode P Q R` for each presheaf relation
  `R : PshRel P Q`

and whose only non-identity morphisms are:

- `.fstProj P Q R : .relNode P Q R => .typeNode P`
- `.sndProj P Q R : .relNode P Q R => .typeNode Q`

Code: `PshRelSpanObj` (`PshRelSpanDiagram.lean:33`),
`PshRelSpanHom` (`PshRelSpanDiagram.lean:44`),
category instance (`PshRelSpanDiagram.lean:104`).

There are no morphisms between distinct type nodes or
between distinct relation nodes. Each relation node
participates in exactly one span.

### 3.2 Collage characterization

`PshRelSpanObj C` is isomorphic to the collage of the
profunctor `pshRelSpanProfunctor` that sends a presheaf
`P` and a relation index `(P_0, Q_0, R)` to the set of
endpoint projections from `R` to `P`
(`pshRelSpanCollageIso`, `PshRelSpanDiagram.lean:417`).

### 3.3 Terminal specialization

When `C = Discrete PUnit`, there is a categorical
isomorphism `relSpanPshRelSpanIso : RelSpanObj ≅ PshRelSpanObj (Discrete PUnit)`
(`PshRelSpanDiagram.lean:839`). This identifies the
type-level span category with the presheaf-level one over
the terminal category.

## 4. The parametric copresheaf topos

### 4.1 Definition

The **parametric copresheaf topos** is the functor category

```text
PshParametricCopresheaf C :=
  PshRelSpanObj C => Type
```

(with appropriate universe annotations). More generally,
`PshParametricFunctor C E := PshRelSpanObj C => E` for
an arbitrary target category `E`.

Code: `PshParametricFunctor` (`PshRelSpanDiagram.lean:111`),
`PshParametricCopresheaf` (`PshRelSpanDiagram.lean:125`).

As a functor category into `Type`, this is a
**Grothendieck topos**. It therefore has:

- All small limits and colimits
- Exponential objects (internal hom)
- A subobject classifier
- Epi-mono factorization

### 4.2 Objects: relational diagrams

An object `F : PshParametricCopresheaf C` assigns:

- To each presheaf `P`: a type `F(.typeNode P)`, the
  "interpretation at `P`"
- To each relation `R : PshRel P Q`: a type
  `F(.relNode P Q R)`, the "R-relatedness witnesses"
- Projection maps `F(fstProj) : F(R) => F(P)` and
  `F(sndProj) : F(R) => F(Q)`, extracting which
  elements are related

The projections make `F(R)` a span over `F(P) x F(Q)`,
defining a relation on `F(P) x F(Q)` for each input
relation `R`. A copresheaf is therefore a systematic
assignment of "relational interpretations" to all
presheaf relations.

### 4.3 Morphisms: relation-preserving maps

A morphism `eta : F => G` in the copresheaf topos
(= natural transformation) has:

- Components `eta(.typeNode P) : F(P) => G(P)` for
  each presheaf `P`
- Components `eta(.relNode P Q R) : F(R) => G(R)` for
  each relation `R`
- Naturality: if `w` witnesses that `x_0` and `x_1`
  are F-related via R, then `eta(R)(w)` witnesses that
  `eta(P)(x_0)` and `eta(Q)(x_1)` are G-related via R

This is exactly a **parametric morphism**: a family of maps
indexed by presheaves that preserves relatedness under all
relations.

### 4.4 Sections: parametric families

A **section** (global element) of `F` is a natural
transformation from the terminal copresheaf to `F`. It
picks:

- One element `s(P) in F(P)` for each presheaf `P`
- One witness `s(R) in F(R)` for each relation `R`

with `F(fstProj)(s(R)) = s(P)` and
`F(sndProj)(s(R)) = s(Q)`.

The witness condition says: the chosen elements are
related under every relation. This is precisely the
**parametricity condition**.

### 4.5 Equivalently: limits

Sections of `F` are equivalently the limit of `F`
viewed as a diagram `PshRelSpanObj C => Type`. The
limit cone picks a compatible family of elements
across all type nodes and relation nodes. This
characterization is the content of
`parametricFamilyIsLimit` (`ParanaturalTopos.lean:4662`)
at the type level.

### 4.6 Parametricity is naturality

In Wadler's framework, the Parametricity Theorem states
that every System F term inhabits its relational
interpretation. This theorem requires proof by induction
on the term structure.

In the copresheaf topos, this theorem becomes
**definitional**: a section of a copresheaf satisfies the
parametricity condition because that condition *is* the
naturality condition that defines sections. There is no
separate theorem to prove.

The content that Wadler proves by induction is replaced
by the fact that the copresheaf topos exists and has the
structure of a Grothendieck topos, which is standard.

### 4.7 Type formers as topos operations

Because `PshParametricCopresheaf C` is a topos, all
standard type formers are available and automatically
respect parametricity:

| Type former | Topos operation | Parametricity |
|------------|----------------|---------------|
| `forall X. T(X)` | Limit (end) | Sections of limits are limits of sections |
| `exists X. T(X)` | Colimit (coend) | Standard |
| `T_1 -> T_2` | Exponential `[F, G]` | Internal hom in topos |
| `T_1 x T_2` | Product | Standard |
| `T_1 + T_2` | Coproduct | Standard |
| Subtype | Subobject | Via subobject classifier |

The exponential `[F, G]` assigns to `.typeNode P` the
set of parametric maps from `F` to `G` "at stage P,"
and to `.relNode P Q R` the relatedness witnesses for
such maps. This is the parametric function type.

## 5. Embeddings

Several classes of categorical data embed into the
copresheaf topos:

### 5.1 Covariant embedding

An endofunctor `G : PSh(C) => PSh(C)` determines a
copresheaf via the Barr extension:

- `.typeNode P |-> G(P)`
- `.relNode P Q R |-> pshBarrLiftSkel G R`

This embedding is **fully faithful**: natural
transformations between endofunctors correspond
bijectively to parametric morphisms between their
copresheaves.

Code: `pshCovariantEmbedding`
(`PshRelSpanDiagram.lean:904`),
`pshCovariantEmbedding_fullyFaithful`
(`PshRelSpanDiagram.lean:958`).

### 5.2 Contravariant embedding

A contravariant functor `F : PSh(C)^op => PSh(C)`
determines a copresheaf via the contravariant Barr
extension (pullback along relation projections):

- `.typeNode P |-> F(op P)`
- `.relNode P Q R |-> pshContraBarrLiftSkel F R`

This embedding is also **fully faithful**.

Code: `pshContravariantEmbedding`
(`PshRelSpanDiagram.lean:1072`),
`pshContravariantEmbedding_fullyFaithful`
(`PshRelSpanDiagram.lean:1134`).

### 5.3 Profunctor embedding

A profunctor `G : PSh(C)^op x PSh(C) => PSh(C)`
embeds via the profunctor Barr extension:

- `.typeNode P |-> G(op P, P)` (diagonal)
- `.relNode P Q R |-> pshProfBarrLiftSkel G R`

Code: `pshProfunctorEmbedding`
(`PshRelSpanDiagram.lean:1229`).

### 5.4 Paranatural embedding

Endoprofunctors with paranatural transformations
(morphisms respecting the wedge condition) embed
faithfully:

Code: `pshParanaturalProfEmbedding`
(`PshRelSpanDiagram.lean:1325`),
`pshParanaturalProfEmbedding_faithful`
(`PshRelSpanDiagram.lean:1400`).

This embedding is faithful but not full: parametricity
is a stronger condition than paranaturality for nested
arrow types (see Section 7).

### 5.5 Type-level specialization

At `C = Discrete PUnit`, all embeddings specialize to
their type-level counterparts in `RelSpanDiagram.lean`:

| Presheaf | Type | Code |
|----------|------|------|
| `pshCovariantEmbedding` | `covariantEmbedding` | L611 |
| `pshContravariantEmbedding` | `contravariantEmbedding` | L826 |
| `pshProfunctorEmbedding` | `profunctorEmbedding` | L1113 |
| `pshParanaturalProfEmbedding` | (via equiv) | -- |

Line numbers refer to `RelSpanDiagram.lean`.

The equivalence `parametricFunctorEquiv`
(`PshRelSpanDiagram.lean:864`) mediates between the two
levels.

## 6. Free theorem derivation

### 6.1 From relations to functions

Given a section `s` of a copresheaf `F` and a presheaf
relation `R : PshRel P Q` that is the **graph** of a
natural transformation `alpha : P => Q`, the parametricity
condition specializes to an equational constraint.

The graph relation `pshRelGraph alpha`
(`PshRelDouble.lean:416`) satisfies
`pshBarrLiftSkel_graph` (`PshRelDouble.lean:1186`):
the Barr extension of a graph relation is the graph of
the functor's action. This means the relatedness witness
degenerates to a function equation.

For a section `s` of the copresheaf associated to an
endofunctor `G`, specializing the parametricity condition
at `pshRelGraph alpha` yields:

```text
G(alpha)(s(P)) = s(Q)
```

which is naturality of `s` with respect to `alpha`. This
is Wadler's derivation of the "free theorem" for covariant
types.

### 6.2 General pattern

More generally, for copresheaves not arising from a
single embedding, specializing the parametricity
condition at graph relations produces constraints that
generalize naturality. For arrow types, these become
commutative diagrams involving the functions derived from
the graph relation.

This is the content of `relInterp_implies_wedge`
(`ParanaturalTopos.lean:3739`) at the type level: the
relational interpretation at a function graph implies the
wedge (naturality) condition.

## 7. Parametricity vs. paranaturality

### 7.1 The distinction

Paranaturality tests only pairs of elements arising from
**off-diagonal** profunctor elements (the wedge
condition). Parametricity tests **all** commuting pairs
via arbitrary relations. These coincide for types with at
most one level of arrow nesting ("depth-one" types) but
diverge for nested arrows.

### 7.2 Separation results

The divergence type `forall X. ((X -> X) -> X) -> X`
separates the two notions:

- `divApplyId` is parametric but not paranatural
  (`divApplyId_parametric`,
  `divApplyId_not_paranatural`,
  `ParanaturalTopos.lean:2391-2402`)
- `divIterOnce` is parametric but not paranatural
  (`ParanaturalTopos.lean:2423-2434`)

The theorem `divParametric_not_implies_divParanatural`
(`ParanaturalTopos.lean:2412`) establishes the separation.

### 7.3 Categorical interpretation

In the copresheaf topos, paranaturality corresponds to
naturality with respect to a **subcategory** of
`PshRelSpanObj C` that includes only graph relations
(or more precisely, the image of the graph functor from
presheaf morphisms). Parametricity requires naturality
with respect to *all* morphisms of `PshRelSpanObj C`,
which includes non-graph relations.

The paranatural embedding being faithful but not full
(`pshParanaturalProfEmbedding_faithful`) reflects this:
every parametric morphism determines a paranatural one
(by restriction to graph relations), but not conversely.

## 8. Why PshRelSpanObj

### 8.1 Minimality

`PshRelSpanObj C` is the **free category** generated by
one span `typeNode P <-- relNode P Q R --> typeNode Q`
per presheaf relation `R : PshRel P Q`, with no
additional morphisms. This means:

- No morphisms between distinct type nodes (no
  naturality/equivariance constraints between
  interpretations at different presheaves)
- No morphisms between distinct relation nodes (no
  consistency constraints between relatedness at
  different relations)
- No composition of relations (which `fullRelInterp`
  does not always preserve; see
  `RelInterpComposition.lean`)

### 8.2 What additional structure would give

Adding morphisms between type nodes (for each natural
transformation `alpha : P => Q`) would impose
equivariance conditions on interpretations, yielding the
**wedge condition** (paranaturality) rather than full
parametricity. The resulting copresheaf category would be
smaller.

Adding relation composition morphisms would impose
transitivity-like constraints that are not universally
satisfied by relational interpretations.

`PshRelSpanObj C` therefore captures the maximal
"relational diagram" structure: it asks for relatedness
data at every relation independently, without imposing
consistency between different relations. Parametricity
is the condition that a family of elements is compatible
with all of these independent relatedness constraints.

### 8.3 Copresheaf topos as ambient universe

Because `PshParametricCopresheaf C` is a Grothendieck
topos, it provides a complete universe for parametric
polymorphism:

- **Universally quantified types** are limits
- **Existentially quantified types** are colimits
- **Parametric function types** are exponentials
- **Parametric predicates** are subobjects
- **Parametric morphisms** are natural transformations

All of these automatically satisfy parametricity because
they are constructed within the topos, where
"respecting the relational structure" is built into the
notion of morphism.

## 9. Existing code infrastructure

### 9.1 File map

| File | Content |
|------|---------|
| `PshRelDouble.lean` | Double category of presheaf relations |
| `YonedaRelDouble.lean` | Yoneda-based relations and double category |
| `PshRelSpanDiagram.lean` | `PshRelSpanObj`, embeddings, full faithfulness |
| `RelSpanDiagram.lean` | Type-level specialization of span category |
| `ParanaturalTopos.lean` | `TypeExpr`, `ParametricFamily`, divergence |
| `PshTypeExpr.lean` | `PshTypeExpr`, presheaf-level bridges |
| `Utilities/Presheaf.lean` | `yonedaULift`, Yoneda extension, pullbacks |

### 9.2 Equivalences with the type level

| Presheaf level | Type level |
|---------------|-----------|
| `PshRelSpanObj (Discrete PUnit)` | `RelSpanObj` |
| `PshParametricFunctor .. E` | `ParametricFunctor E` |
| `PshParametricCopresheaf ..` | `ParametricCopresheaf` |

Mediated by `relSpanPshRelSpanIso`,
`parametricFunctorEquiv`, `parametricCopresheafEquiv`.

## 10. Areas of exploration

### 10.1 Exponentials in the copresheaf topos

The exponential `[F, G]` in `PshParametricCopresheaf C`
exists by general topos theory. Its concrete description
would show what "parametric function type" looks like at
each stage and relation. This may connect to the arrow
relation `pshArrowRelSkel` and the internal hom
`pshIhomProfMap`.

### 10.2 Identity extension

For a copresheaf `F` arising from a specific embedding,
the relation `F` induces at the identity relation
`pshRelId P` may or may not be the identity relation on
`F(P)`. Understanding when this holds (and whether it
holds for all copresheaves or only specific ones) is the
copresheaf-topos analogue of Wadler's Identity Extension
Lemma.

### 10.3 Subobject classifier

The subobject classifier `Omega` in the copresheaf topos
assigns to each object of `PshRelSpanObj C` a set of
"sieves." Its concrete description would characterize
parametric predicates.

### 10.4 Graph restriction functor

There should be a restriction functor from
`PshParametricCopresheaf C` to copresheaves on the
subcategory of `PshRelSpanObj C` generated by graph
relations. This functor extracts the "free theorem
content" from a parametric copresheaf. Its left and
right adjoints (Kan extensions) would give ways to
extend equivariant data to full parametric data.

### 10.5 Internal parametricity

The internal language of the copresheaf topos (its
Mitchell-Benabou language) provides a type theory in
which parametricity is a built-in property. Statements
and proofs in this internal language automatically
respect the relational structure. This may connect to
recent work on directed type theory and parametricity
(Neumann-Licata, POPL 2026).

### 10.6 Copresheaf topos vs. exploratory constructions

The exploratory constructions `TypeExpr`, `PshTypeExpr`,
`fullRelInterp`, and `PshParametricFamily` were used to
develop and validate the theory. They provide:

- Specific copresheaves in the topos (via
  `relSpanDiagramFunctor` and
  `pshRelSpanDiagramFunctor`)
- Concrete calculations showing the construction
  produces expected results
- Separation results between parametricity and
  paranaturality

These remain as computational tools and test cases, but
the general theory rests on the copresheaf topos alone.

## References

### Codebase documents

- `docs/parametric-functor-embeddings.md` -- embedding
  analysis
- `docs/parametric-functor-universal-property.md` --
  universal property investigation
- `docs/ParametricityViaYonedaRelations.md` -- Reynolds/
  Wadler to Yoneda relation connection
- `docs/paranatural-topos-research.md` -- topos structure
  investigation
- `docs/DoubleCategory.md` -- double category formalism

### Literature

- Wadler, "Theorems for free!" (1989)
- Reynolds, "Types, abstraction, and parametric
  polymorphism" (1983)
- Mulry, "Strong monads, algebras and fixed points"
  (1992) -- paranatural composition
- Pare-Roman (1998) -- paranatural transformations
- Uustalu (2010) -- paranatural category not Cartesian
  closed
- Neumann, "Paranatural Category Theory" -- directed
  type theory via dinaturality; note that the di-Yoneda
  lemma claimed there has an error
- Pastro-Street, "Doubles for monoidal categories"
  (2008) -- Tambara modules as presheaves
- Neumann-Licata (POPL 2026) -- directed type theory
