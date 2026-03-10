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
| --------- | ---- | ---- |
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
| ------- | ----------- | ---- | ---- |
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
PshParametricPresheaf C :=
  PshRelSpanObj C => Type
```

(with appropriate universe annotations). More generally,
`PshParametricFunctor C E := PshRelSpanObj C => E` for
an arbitrary target category `E`.

Code: `PshParametricFunctor` (`PshRelSpanDiagram.lean:111`),
`PshParametricPresheaf` (`PshRelSpanDiagram.lean:125`).

As a functor category into `Type`, this is a
**Grothendieck topos**. It therefore has:

- All small limits and colimits
- Exponential objects (internal hom)
- A subobject classifier
- Epi-mono factorization

### 4.2 Objects: relational diagrams

An object `F : PshParametricPresheaf C` assigns:

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

#### 4.5.1 Mechanism: how limits produce parametricity

The span diagram `relSpanDiagram T` assigns to each
relation-node object the **fiber type**
`T.relFiber R`, which is a subtype:

```text
T.relFiber R =
  { p : T.interp I₀ I₀ × T.interp I₁ I₁ //
    T.fullRelInterp R p.1 p.2 }
```

The two span projections extract the endpoints:

```text
fstProj : relFiber(R) → interp(I₀, I₀)
                         via p ↦ p.val.1
sndProj : relFiber(R) → interp(I₁, I₁)
                         via p ↦ p.val.2
```

A cone over this diagram with vertex `V` consists
of maps `πᵢ : V → T.interp I I` (at each type-node)
and `πᵣ : V → T.relFiber R` (at each relation-node).
Cone naturality at the span projections requires:

```text
πᵣ(x).val.1 = πᵢ₀(x)    (via s.w fstProj)
πᵣ(x).val.2 = πᵢ₁(x)    (via s.w sndProj)
```

Since `πᵣ(x) : T.relFiber R` carries a proof that
`T.fullRelInterp R πᵣ(x).val.1 πᵣ(x).val.2`,
substituting the cone naturality equalities gives
`T.fullRelInterp R (πᵢ₀(x)) (πᵢ₁(x))`: the
type-node values are R-related.

This is the content of `relSpanCone_parametric`
(`ParanaturalTopos.lean:4633`). The limit of
`relSpanDiagram T` is therefore exactly the type of
families `(I ↦ T.interp I I)` satisfying the
parametricity condition for all relations.

The parametricity condition is encoded in the
**types** of the diagram objects (via the subtype
`T.relFiber R`), not in morphisms between objects.
The span projections serve only to ensure that
the fiber endpoints match the type-node choices.
No lattice morphisms between relation nodes are
needed.

#### 4.5.2 Colimits: existential parametric types

The colimit of `relSpanDiagram T` is the quotient:

```text
colim(relSpanDiagram T) =
  (∐ᵢ T.interp I I  ⊔  ∐ᵣ T.relFiber R) / ~
```

where `~` identifies, for each `R : I₀ → I₁ → Prop`
and each fiber element `⟨(x, y), proof⟩`:

- `x` in the `I₀` summand with
  `⟨(x, y), proof⟩` in the `R` summand
- `y` in the `I₁` summand with
  `⟨(x, y), proof⟩` in the `R` summand

After quotienting, two elements
`x : T.interp I I` and `y : T.interp J J` become
identified when there exists a relation
`R : I → J → Prop` with `T.fullRelInterp R x y`.
This is the existential parametric type:

```text
∃X. T(X) ≅ (Σ I, T.interp I I) /
  (x ~ y iff ∃ R, T.fullRelInterp R x y)
```

The impredicative encoding
`∃X. T(X) ≅ ∀Y. (∀X. T(X) → Y) → Y`
translates to:

```text
colim(relSpanDiagram T) ≅
  ∀ Y, (lim(relSpanDiagram (T → Y))) → Y
```

where the inner limit ranges over parametric
consumers. Whether this coincides with the direct
colimit depends on whether the exponential in the
copresheaf topos matches the type-expression
internal hom (tasks T1, T3).

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

Because `PshParametricPresheaf C` is a topos, all
standard type formers are available and automatically
respect parametricity:

| Type former | Topos operation | Parametricity |
| ---------- | -------------- | ------------- |
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
| -------- | ---- | ---- |
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

Because `PshParametricPresheaf C` is a Grothendieck
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
| ---- | ------- |
| `PshRelDouble.lean` | Double category of presheaf relations |
| `YonedaRelDouble.lean` | Yoneda-based relations and double category |
| `PshRelSpanDiagram.lean` | `PshRelSpanObj`, embeddings, full faithfulness |
| `RelSpanDiagram.lean` | Type-level specialization of span category |
| `ParanaturalTopos.lean` | `TypeExpr`, `ParametricFamily`, divergence |
| `PshTypeExpr.lean` | `PshTypeExpr`, presheaf-level bridges |
| `Utilities/Presheaf.lean` | `yonedaULift`, Yoneda extension, pullbacks |

### 9.2 Equivalences with the type level

| Presheaf level | Type level |
| ------------- | --------- |
| `PshRelSpanObj (Discrete PUnit)` | `RelSpanObj` |
| `PshParametricFunctor .. E` | `ParametricFunctor E` |
| `PshParametricPresheaf ..` | `ParametricCopresheaf` |

Mediated by `relSpanPshRelSpanIso`,
`parametricFunctorEquiv`, `parametricCopresheafEquiv`.

## 10. Areas of exploration

### 10.1 Exponentials in the copresheaf topos

The exponential `[F, G]` in `PshParametricPresheaf C`
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
`PshParametricPresheaf C` to copresheaves on the
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

## 11. The edge category quasitopos

### 11.1 The vertical edge category

The vertical edge category `PshRelEdge C` of the double
category of presheaf relations has:

- **Objects**: triples `(P, Q, R)` where
  `P, Q : C^op => Type` are presheaves and
  `R : PshRel P Q` is a subfunctor of `P x Q`
- **Morphisms** `(P, Q, R) => (P', Q', S)`: pairs
  `(alpha : P => P', beta : Q => Q')` of natural
  transformations such that `alpha` and `beta` map
  R-related pairs to S-related pairs
  (`pshRelRelated alpha beta R S`)

Code: `PshRelEdge` (`PshRelDouble.lean`), category
instance `pshRelEdgeCategory` (`PshRelDouble.lean`).

### 11.2 Separated presheaf characterization

Let `I = {0 <-- 01 --> 1}` be the walking span
category. An object of `PSh(C x I^op)` assigns to each
`c : C^op`:

- A set `F_0(c)` (at vertex 0)
- A set `F_1(c)` (at vertex 1)
- A set `F_01(c)` (at the span vertex)
- Maps `F_01(c) => F_0(c)` and `F_01(c) => F_1(c)`

functorially in `c`. This is a span of presheaves.

The Grothendieck topology `J` on `(C^op x I)` generated
by covering each `(c, 01)` by `{(c, 01 => 0), (c, 01 => 1)}`
defines a separation condition: a presheaf `F` is
`J`-separated when `F(c, 01) => F(c, 0) x F(c, 1)` is
injective at each stage `c`. This is exactly the
condition that `F_01` is a subfunctor of `F_0 x F_1`.

There is an equivalence of categories:

```text
PshRelEdge C  ~=  Sep_J(C x I^op)
```

- **Objects**: a separated presheaf assigns P(c), Q(c),
  R(c) with R(c) ↪ P(c) x Q(c), matching a subfunctor
  of the product.
- **Morphisms**: since the target is separated, a
  natural transformation at the 01-component is
  uniquely determined by its 0- and 1-components.
  The compatibility condition reduces to
  `pshRelRelated`.

The J-sheaves (where `F(c, 01) => F(c, 0) x F(c, 1)` is
bijective, forcing `R = P x Q`) form the sheaf topos:

```text
Sh_J(C x I^op)  ~=  PSh(C) x PSh(C)  ~=  PSh(C ⊔ C)
```

This gives a chain of inclusions:

```text
PSh(C ⊔ C) ~= Sh_J  ↪  Sep_J ~= PshRelEdge C
                                  ↪  PSh(C x I^op)
```

### 11.3 Quasitopos structure

As a category of J-separated presheaves for a
Grothendieck topology on a small category,
`PshRelEdge C` is a **Grothendieck quasitopos**
(Wyler 1991, Borceux "Handbook of Categorical
Algebra" Vol. 3). It has:

- All small limits and colimits
- Exponential objects (cartesian closed)
- Local cartesian closure
- A strong subobject classifier
- Epi-mono factorization (regular)

It is not a topos: it lacks a (full) subobject
classifier. Non-strong monomorphisms exist (e.g.,
a proper inclusion `R ⊊ P x Q` into the total
relation).

### 11.4 Reflective and coreflective inclusions

The inclusion `PshRelEdge C ↪ PSh(C x I^op)` has a
left adjoint: the **separation reflector**
`sep : PSh(C x I^op) => PshRelEdge C`, which replaces
a span `(P, Q, F_01)` with the image
`(P, Q, Im(F_01 => P x Q))`. This makes `PshRelEdge C`
a **reflective subcategory** of `PSh(C x I^op)`.

The inclusion `PSh(C ⊔ C) ↪ PshRelEdge C` sends
`(P, Q)` to the total relation `(P, Q, P x Q)`. The
sheafification left adjoint `PshRelEdge C => PSh(C ⊔ C)`
sends `(P, Q, R)` to `(P, Q)` (forgetting the relation).

```text
PSh(C x I^op)  --sep-->  PshRelEdge C  --forget-->
                                          PSh(C ⊔ C)
     ↑                       ↑                ↑
  inclusion              inclusion         inclusion
     |                       |                |
PSh(C x I^op)  <--incl--  PshRelEdge C  <--total--
                                          PSh(C ⊔ C)
```

### 11.5 Exponentials and the arrow relation

The exponential in `PshRelEdge C` of two objects
`(A_1, B_1, R_1)` and `(A_2, B_2, R_2)` is:

```text
[(A_1, B_1, R_1), (A_2, B_2, R_2)]
  = (A_1.functorHom A_2,
     B_1.functorHom B_2,
     pshArrowRelSkel R_1 R_2)
```

The arrow relation `pshArrowRelSkel R_1 R_2` relates
`f : [A_1, A_2](c)` and `g : [B_1, B_2](c)` when `f`
maps R_1-related inputs to R_2-related outputs via
`g`. This is the presheaf-level analogue of Wadler's
relational interpretation of function types.

Verification via the exponential adjunction:
morphisms `(P, Q, S) x (A_1, B_1, R_1) => (A_2, B_2, R_2)`
in `PshRelEdge C` consist of `phi : P x A_1 => A_2`
and `psi : Q x B_1 => B_2` preserving
`(S x R_1)`-relatedness to `R_2`-relatedness. By the
internal hom adjunction in `PSh(C)`, this transposes to
`alpha : P => [A_1, A_2]` and `beta : Q => [B_1, B_2]`
mapping S-related pairs to
`pshArrowRelSkel R_1 R_2`-related pairs.

Code: `pshArrowRelSkel` and `pshIhomProfMap`
(`PshRelDouble.lean`).

### 11.6 Identity extension as exponential preservation

The identity section functor
`pshRelIdentFunctor : PSh(C) => PshRelEdge C` sends
`P` to the identity relation `(P, P, Delta_P)`.

This functor preserves exponentials:
`pshArrowRelSkel Delta_P Delta_Q = Delta_{[P, Q]}`.

Verification: `(f, g)` is arrow-related at diagonal
relations iff for all equal pairs `a = a'`,
`f(a) = g(a')`, which gives `f = g`. So the arrow
relation on diagonals is the diagonal of the
internal hom.

This is the **Identity Extension Property**
(Reynolds, Hermida-Reddy-Robinson Proposition 6.3),
now characterized as the statement that
`pshRelIdentFunctor` is a cartesian closed functor.

Properties of `pshRelIdentFunctor`:

- Fully faithful (morphisms between identity relations
  are pairs `(alpha, alpha)`, determined by `alpha`)
- Preserves all limits (identity on products is
  product of identities: `Delta_{P x Q} = Delta_P x Delta_Q`)
- Preserves exponentials (identity extension property)

### 11.7 Yoneda embedding into the edge category

The composite
`C --yoneda--> PSh(C) --pshRelIdentFunctor--> PshRelEdge C`
embeds `C` into the quasitopos. It is:

- Fully faithful (composite of fully faithful functors)
- Preserves all limits that exist in `C`
- Preserves cartesian closed structure when it exists
  (via identity extension)

Code: `pshRelIdentFunctor` (`PshRelDouble.lean`),
`yoneda` (mathlib).

### 11.8 Comparison: PshRelEdge C vs PshParametricPresheaf C

| Property | PshRelEdge C | PshParametricPresheaf C |
| -------- | ------------ | ----------------------- |
| Definition | Sep_J(C x I^op) | PSh(PshRelSpanObj C) |
| Topos? | N (quasitopos) | Y (Grothendieck) |
| Subobj. classifier | Strong only | Full |
| Objects | Single relations | Functors on all spans |
| Ambient topos | PSh(C x I^op) | = itself |
| Size of diagram cat. | C x I^op (small) | PshRelSpanObj C (large) |

`PshRelEdge C` makes relations into objects with
morphisms between them. `PshParametricPresheaf C`
assigns interpretations to all relations
simultaneously (a copresheaf on the span category).

The ambient presheaf topos `PSh(C x I^op)` contains
`PshRelEdge C` as a reflective subcategory and may
serve as an alternative ambient topos. See
Section 11.9.

### 11.9 PSh(C x I^op) as an ambient topos

`PSh(C x I^op)` is the category of "spans of
presheaves on C" (without the joint monomorphism
condition). It is a Grothendieck topos with a
small diagram category `C x I^op`.

Comparison with `PshParametricPresheaf C`:

- `PshRelSpanObj C` has one span per presheaf
  relation `R : PshRel P Q`, with no morphisms
  between distinct type nodes or relation nodes.
  It is a large category (its objects are indexed
  by presheaves and their relations).
- `C x I^op` has one copy of the span shape per
  object `c` of `C`. It is a small category.

An object of `PSh(C x I^op)` is a span
`(P, Q, R)` of presheaves with maps `R => P` and
`R => Q`, without requiring joint monicity.
Morphisms are triples `(alpha, beta, gamma)` with
naturality squares. This is richer than
`PshParametricPresheaf C` in that it has
morphisms connecting different "stages" of the
span (via the functoriality in `C`), but it does
not independently assign relation data to each
`PshRel P Q`.

The relationship between these categories and
their relative merits as ambient universes for
parametricity requires further investigation.
The separation reflector
`PSh(C x I^op) => PshRelEdge C` may provide a
bridge connecting the two perspectives.

### 11.10 The subobject classifier and lattice-enriched sites

In any topos `E`, the subobject classifier `Omega`
is an internal Heyting algebra: a bicartesian closed
poset, and therefore an internal category with
objects = truth values and morphisms = implications
(ordering). In `PSh(C)`, `Omega(c)` = the set of
sieves on `c`, ordered by inclusion.

Relations in `PSh(C)` are classified by `Omega`:

```text
Sub(P x Q)  ~=  Hom(P x Q, Omega)
            ~=  Hom(P, [Q, Omega])
            =   Hom(P, P(Q))
```

where `P(Q) = [Q, Omega]` is the power object. So
`PshRel P Q` is the set of global sections of the
presheaf `Hom(P x Q, Omega)`, and
`PshRelEdge C` is the Grothendieck construction
of the functor
`(P, Q) |-> Hom(P x Q, Omega) : (PSh(C) x PSh(C))^op -> Set`.

For representable presheaves, `YonedaRel X Y` =
`Sub(y(X) x y(Y))` is a Heyting algebra. Each
element is a subfunctor that at stage `c` picks
a subset of `Hom(c, X) x Hom(c, Y)` closed under
precomposition. This is equivalent to a sieve-like
structure on the pair `(X, Y)`.

#### Candidate: lattice-enriched span site

The "awkwardness" of `PshRelSpanObj C` stems from
two structural choices:

1. **No morphisms between type nodes.** This is
   structurally necessary: adding `C`-morphisms
   between type nodes would impose the
   equivariance/naturality condition on
   interpretations, producing the paranaturality
   condition rather than full parametricity. Since
   parametricity strictly subsumes paranaturality
   (divergence results in Section 7), the absence
   of type-node morphisms is a feature.

2. **No morphisms between relation nodes.** This
   is where improvement may be possible. Each
   `Sub(P x Q)` is a Heyting algebra, and adding
   inclusions `R <= S` as morphisms between
   relation nodes would impose monotonicity on the
   relational interpretation.

A **lattice-enriched span site** `S_C'` would have:

- Type objects: `typeNode P` for each presheaf `P`
- Relation objects: `relNode P Q R` for each
  `R : PshRel P Q`
- Span projections: `relNode P Q R => typeNode P`
  and `relNode P Q R => typeNode Q`
- **Lattice inclusions**: `relNode P Q R => relNode P Q S`
  when `R <= S` as subfunctors
- **No** morphisms between type nodes

Copresheaves on `S_C'` satisfy:

- Span compatibility (relational witnesses project
  correctly)
- **Monotonicity**: if `R <= S`, then the `R`-witness
  type maps to the `S`-witness type

This is a strictly smaller category than
`PshParametricPresheaf C` (fewer copresheaves,
because of monotonicity). The question is whether
the relational interpretations arising from the
embeddings (covariant, contravariant, profunctor)
satisfy monotonicity.

For the covariant embedding, `pshBarrLiftSkel G R`
is monotone in `R` (image preserves subobject
ordering). For the arrow relation, monotonicity
in the output relation holds, but the input
relation is contravariant (`R_1 <= R_1'` gives
`pshArrowRelSkel R_1' R_2 <= pshArrowRelSkel R_1 R_2`).
This means the lattice enrichment must be
covariant for some relation-node morphisms and
contravariant for others, reflecting the
mixed-variance structure of the arrow relation.

#### Candidate: Yoneda-restricted subobject site

Restricting to representable presheaves gives
a potentially small site:

- Type objects: `X` for each `X : C`
- Relation objects: `(X, Y, R)` for each
  `R : YonedaRel X Y`
- Span projections and lattice inclusions as above
- Base change: for `f : X' => X`, `g : Y' => Y`,
  a morphism
  `(X', Y', pullback R along (f, g)) => (X, Y, R)`

If `C` is small, this site is essentially small
(objects indexed by
`C + Sigma_{X,Y : C} Sub(y(X) x y(Y))`, which is
a set). Copresheaves on it form a Grothendieck
topos.

Extension to general presheaves would use the
Yoneda extension (left Kan extension along the
Yoneda embedding). Whether this preserves the
parametricity structure is an open question
connected to the density theorem and existing
infrastructure (`yonedaULift`, `yonedaExt` in
`Presheaf.lean`).

#### The fibration perspective

The boundary functor
`pshRelBoundaryFunctor : PshRelEdge C => PSh(C) x PSh(C)`
is a pre-fibered category (proven in
`PshRelDouble.lean`). The fiber over `(P, Q)` is
`Sub(P x Q)`, which is a Heyting algebra. The
Grothendieck construction of this fibration IS
`PshRelEdge C`.

The subobject classifier `Omega` of `PSh(C)` is
the representing object for the fibers: the fiber
over `(P, Q)` is `Hom(P x Q, Omega)`. So the
fibration structure of `PshRelEdge C` is
controlled by `Omega`.

This suggests a connection: `PshRelEdge C` is
the **total category of the Omega-valued
subobject fibration** over `PSh(C) x PSh(C)`.
The structure of `Omega` as an internal Heyting
algebra (and hence as an internal category)
determines the lattice structure on the fibers,
the base change functors (pullback of subobjects),
and the logical operations available on relations.

### 11.11 Open questions

#### Q1: PSh(C x I^op) vs PshParametricPresheaf C

`PSh(C x I^op)` handles one span at a time (an
object is a single span of presheaves).
`PshParametricPresheaf C` handles all relations
simultaneously (an object assigns data to every
presheaf and every relation independently). The
parametricity condition requires consistency
across all relations simultaneously, which
`PshParametricPresheaf C` captures through its
copresheaf structure.

Does `PSh(C x I^op)` allow a construction that
recovers the "all relations at once" aspect?
Possible approaches:

- Internal presheaves on `Omega` within
  `PSh(C x I^op)` (internalizing the subobject
  lattice)
- Power object constructions (using `P(Q) = [Q, Omega]`
  to parameterize over all relations)
- Eilenberg-Moore algebras for the power monad
  `P : E -> E` given by `P(X) = Omega^X`

#### Q2: Lattice enrichment and variance

Does the lattice-enriched span site `S_C'` give a
strictly better "ambient topos" than
`PshParametricPresheaf C`? The answer is **no**:
the three standard embeddings have incompatible
variance with respect to the subobject ordering
on relations.

**Variance of the Barr extensions:**

- Covariant: `pshBarrLiftRel G R` is **monotone**
  in `R`. Proof: `pshBarrLiftRel_mono`
  (`PshRelDouble.lean`). Enlarging `R` to `S ≥ R`
  enlarges the image under `G.map`.
- Contravariant: `pshContraBarrLiftRel F R` is
  **antitone** in `R`. The equalizer defining
  `pshContraBarrLiftRel` consists of elements
  where two maps agree; when `R ≤ S`, the
  map `homOfLe` from `S` to `R` carries agreement
  on `S` to agreement on `R`, but not conversely.
  Enlarging `R` shrinks the equalizer.
- Profunctor: `pshProfBarrLiftRel G R` is
  **neither monotone nor antitone** in `R`. The
  diagonal application `G.obj(op(R.toProdPresheaf),
  R.toProdPresheaf)` has the relation appearing in
  both a contravariant and a covariant position,
  making one-variable monotonicity impossible.

**Consequence:** adding covariant lattice
inclusions `R ≤ S` as morphisms between relation
nodes accommodates the covariant embedding but
breaks the contravariant embedding. Adding
contravariant inclusions does the reverse. No
single lattice enrichment accommodates all three
embedding classes simultaneously. The absence of
inter-relation morphisms in `PshRelSpanObj C` is
therefore structurally necessary.

#### Q3: Yoneda extension of parametric structure

For the Yoneda-restricted subobject site: does the
left Kan extension along the Yoneda embedding
preserve the parametricity structure? This connects
to existing task P6b in
`parametricity-free-theorems.md` and the
infrastructure in `yonedaULift`, `yonedaExt`.

#### Q4: Internal Heyting algebra and directed type theory

The subobject classifier `Omega`, viewed as an
internal category (via its Heyting algebra
structure), determines a notion of "internal
presheaves on Omega." The category of such
internal presheaves (externalized via the
Grothendieck construction) may provide a
canonical ambient topos that reflects the full
subobject lattice structure. This connects to
the Neumann-Licata directed type theory (POPL
2026), where directionality is built into the
type theory via an internal notion of ordering.

### 11.12 Formalization candidates

The following are candidates for Lean formalization,
ordered roughly by dependency:

- **(a)** Construct the equivalence
  `PshRelEdge C ~= Sep_J(C x I^op)` explicitly.
  Requires defining the walking span category `I`,
  the product site `C x I^op`, the Grothendieck
  topology `J`, and the separation condition.

- **(b)** Show the exponential in `PshRelEdge C`
  equals `(FunctorHom, FunctorHom, pshArrowRelSkel)`.
  Verify the exponential adjunction directly in
  `PshRelEdge C`. Uses existing `pshArrowRelSkel`
  and `pshIhomProfMap` infrastructure.

- **(c)** Show `pshRelIdentFunctor` preserves
  exponentials (the Identity Extension Property
  as a functor property). Uses (b) and the
  identity extension result.

- **(d)** Show `pshRelIdentFunctor` preserves
  products and limits.

- **(e)** Construct the inclusion
  `PshRelEdge C -> PSh(C x I^op)` as an explicit
  fully faithful functor, and its left adjoint
  (the separation reflector).

- **(f)** Construct the extraction functor
  `PshParametricPresheaf C -> PshRelEdge C` that
  sends a copresheaf to a single relation.
  Investigate its properties (faithful? full?
  preserves limits?).

- **(g)** Investigate whether the lattice-enriched
  span site `S_C'` (adding Heyting algebra
  structure to `PshRelSpanObj C`) gives a
  Grothendieck topos that improves on
  `PshParametricPresheaf C`. This requires:
  defining the enriched site, verifying that
  embedded copresheaves satisfy monotonicity,
  and characterizing the resulting topos.

- **(h)** Investigate the Yoneda-restricted
  subobject site (restricting to representable
  presheaves with `YonedaRel` and the subobject
  lattice structure). Determine whether Kan
  extension along the Yoneda embedding recovers
  the full parametric structure.

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
