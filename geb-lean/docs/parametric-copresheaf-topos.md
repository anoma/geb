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

The **parametric functor category** is

```text
PshParametricFunctor C E := PshRelSpanObj C => E
```

for a domain category `C` (determining the presheaf
relations) and target category `E`.

The **parametric copresheaf topos** is the
presheaf-valued specialization

```text
PshParametricPresheaf C D :=
  PshRelSpanObj C => (D^op => Type)
```

where `D` is an independent category parameter.
When `D = Discrete PUnit`, `D`-presheaves reduce
to types, recovering `Type`-valued copresheaves.
When `D = C`, the copresheaf is doubly
parameterized by `C`.

Code: `PshParametricFunctor`
(`PshRelSpanDiagram.lean:306`),
`PshParametricPresheaf`
(`PshRelSpanDiagram.lean:320`).

As a functor category into `Type` (or into a
presheaf category), this is a **Grothendieck
topos**. It therefore has:

- All small limits and colimits
- Exponential objects (internal hom)
- A subobject classifier
- Epi-mono factorization

### 4.2 Objects: relational diagrams

An object `F : PshParametricPresheaf C D` assigns:

- To each presheaf `P : C^op => Type`: an object
  `F(.typeNode P) : D^op => Type` (a `D`-presheaf
  of "interpretations at `P`")
- To each relation `R : PshRel P Q`: an object
  `F(.relNode P Q R) : D^op => Type` (a `D`-presheaf
  of "R-relatedness witnesses")
- Projection maps
  `F(fstProj) : F(.relNode P Q R) => F(.typeNode P)`
  and
  `F(sndProj) : F(.relNode P Q R) => F(.typeNode Q)`
  (natural transformations of `D`-presheaves)

The projections make `F(.relNode P Q R)` a span
of `D`-presheaves over `F(.typeNode P)` and
`F(.typeNode Q)`. At each stage `d : D^op`, the
composite

```text
(F(fstProj).app d, F(sndProj).app d) :
  F(.relNode P Q R).obj d =>
    F(.typeNode P).obj d x F(.typeNode Q).obj d
```

sends witnesses to pairs. The induced relation
on `F(.typeNode P).obj d x F(.typeNode Q).obj d`
is the **image** of this map.

In general, this span map need not be injective:
a copresheaf may assign multiple distinct
witnesses for the same pair. The relation is
**proof-relevant**. When the projections are
jointly monic (`HasJointlyMonicProjections`,
`SpanFamily.lean:354`), the relation degenerates
to a property (proof-irrelevant).

Note that `C` (the domain) and `D` (the target
presheaf parameter) are independent. When
`D = Discrete PUnit`, `D`-presheaves reduce to
types, and the copresheaf assigns a bare type
to each node. When `D = C`, the copresheaf is
doubly parameterized.

#### Equivalence with span family data

The unpacked form of a copresheaf is
`SpanFamilyData` (`SpanFamily.lean:26`):

```text
SpanFamilyData :=
  { vertexObj : (C^op => Type) => D
    edgeObj : (P Q : C^op => Type) =>
      PshRel P Q => D
    fstProj : edgeObj P Q R => vertexObj P
    sndProj : edgeObj P Q R => vertexObj Q }
```

The equivalence `pshParametricFunctorSpanFamilyEquiv`
(`PshRelSpanDiagram.lean:330`) identifies
`PshParametricFunctor C D` with
`SpanFamily (C^op => Type) PshRel D`, and the
further equivalence `spanFamilyEquiv`
(`SpanFamily.lean:298`) identifies `SpanFamily`
with `SpanFamilyData`. This provides the
"intuitive" unpacked view of copresheaves
as vertex-object families, edge-object families,
and projection morphisms.

### 4.3 Morphisms: relation-preserving maps

A morphism `eta : F => G` in the copresheaf
category (= natural transformation) has:

- Components
  `eta(.typeNode P) : F(.typeNode P) => G(.typeNode P)`
  for each presheaf `P`
- Components
  `eta(.relNode P Q R) :
    F(.relNode P Q R) => G(.relNode P Q R)`
  for each relation `R`
- Naturality at projections:
  `eta(.relNode P Q R) >> G(fstProj) =
    F(fstProj) >> eta(.typeNode P)`
  (F-witnesses map to G-witnesses preserving
  endpoints)

The unpacked form is `SpanFamilyHom`
(`SpanFamily.lean:40`):

```text
SpanFamilyHom F G :=
  { vertexMap : (P) => F.vertexObj P => G.vertexObj P
    edgeMap : (R) => F.edgeObj R => G.edgeObj R
    fstCompat : edgeMap R >> G.fstProj R =
      F.fstProj R >> vertexMap P
    sndCompat : edgeMap R >> G.sndProj R =
      F.sndProj R >> vertexMap Q }
```

This is a **parametric morphism**: a family of maps
indexed by presheaves that preserves relatedness
under all relations.

When the target has jointly monic projections,
`edgeMap` is determined by `vertexMap`
(`spanFamilyHom_ext_vertexMap`,
`SpanFamily.lean:374`).

### 4.4 Sections: parametric families

A **section** (global element) of `F` is a natural
transformation from the terminal copresheaf to `F`.
For a `Type`-valued copresheaf, this picks:

- One element `s(P) in F(.typeNode P)` for each
  presheaf `P`
- One witness `s(R) in F(.relNode P Q R)` for each
  relation `R`

with `F(fstProj)(s(R)) = s(P)` and
`F(sndProj)(s(R)) = s(Q)`.

The witness condition says: the chosen elements are
related under every relation. This is the
**parametricity condition**.

For a `D`-presheaf-valued copresheaf, a section picks
a section of each `D`-presheaf `F(.typeNode P)` and
`F(.relNode P Q R)`, with the same endpoint
compatibility.

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

Because `PshParametricPresheaf C D` is a functor
category, all limits and colimits are computed
**pointwise**: `(F ⊕ G)(X) = F(X) ⊕ G(X)`,
`(F × G)(X) = F(X) × G(X)`, etc. for each object
`X` of `PshRelSpanObj C`. This pointwise computation
produces the correct parametric type formers:

| Type former | Topos operation | Parametricity |
| ---------- | -------------- | ------------- |
| `forall X. T(X)` | Limit (end) | Section 4.5 |
| `exists X. T(X)` | Colimit (coend) | Section 4.5.2 |
| `T_1 -> T_2` | Exponential `[F, G]` | Section 4.7.3 |
| `T_1 x T_2` | Product | Section 4.7.1 |
| `T_1 + T_2` | Coproduct | Section 4.7.2 |
| Subtype | Subobject | Via subobject classifier |

#### 4.7.1 Products

The product `F × G` in `PshParametricFunctor C E`
assigns:

```text
(F × G)(.typeNode P) = F(.typeNode P) × G(.typeNode P)
(F × G)(.relNode P Q R) =
  F(.relNode P Q R) × G(.relNode P Q R)
```

A witness in the product is a pair of witnesses.
The projections decompose componentwise:

```text
(F × G)(fstProj)(w_F, w_G) =
  (F(fstProj)(w_F), G(fstProj)(w_G))
```

This matches Wadler's relational interpretation
of product types: `rel(A × B)(R)` consists of
pairs `((a₁, b₁), (a₂, b₂))` where `a₁` R-relates
to `a₂` via `A` and `b₁` R-relates to `b₂` via `B`.

#### 4.7.2 Coproducts

The coproduct `F ⊕ G` assigns:

```text
(F ⊕ G)(.typeNode P) =
  F(.typeNode P) ⊕ G(.typeNode P)
(F ⊕ G)(.relNode P Q R) =
  F(.relNode P Q R) ⊕ G(.relNode P Q R)
```

A witness in the coproduct is either an F-witness
(via `inl`) or a G-witness (via `inr`). An
F-witness projects to F-elements at both
endpoints; a G-witness projects to G-elements.
There are **no witnesses for mixed pairs**: an
F-element at `.typeNode P` and a G-element at
`.typeNode Q` have no witness in
`F(.relNode P Q R) ⊕ G(.relNode P Q R)` that
projects to them.

This matches Wadler's relational interpretation
of sum types: `rel(A + B)(R) = rel(A)(R) + rel(B)(R)`,
where `inl(a₁)` and `inl(a₂)` are related iff
`a₁` R-relates to `a₂` via `A`, `inr(b₁)` and
`inr(b₂)` are related iff `b₁` R-relates to
`b₂` via `B`, and `inl/inr` mixtures are never
related.

**Compatibility with the covariant embedding.**
For endofunctors `G₁, G₂ : PSh(C) => PSh(C)`,
the coproduct `G₁ ⊕ G₂` (pointwise:
`(G₁ ⊕ G₂)(P) = G₁(P) ⊕ G₂(P)`) has Barr
extension:

```text
pshBarrLiftRel (G₁ ⊕ G₂) R ≅
  pshBarrLiftRel G₁ R ⊕ pshBarrLiftRel G₂ R
```

because `(G₁ ⊕ G₂).map(R.ι)` decomposes as
`G₁.map(R.ι) ⊕ G₂.map(R.ι)` and the image
decomposes into the two summands with no mixed
terms. This gives:

```text
embed(G₁ ⊕ G₂) ≅ embed(G₁) ⊕ embed(G₂)
```

so the covariant embedding preserves coproducts.

**Compatibility with identity extension.** The
identity section functor preserves coproducts:
`I(A ⊕ B) = I(A) ⊕ I(B)` in `PshRelEdge C`.
The diagonal relation on a coproduct presheaf
is the coproduct of the diagonal relations,
with mixed pairs never equal. This is the
identity extension property for sum types.

Code: `pshRelId_coprod` and
`pshRelIdentFunctor_preserves_coprod`
(`PshRelEdgeIdentPreservation.lean:108,197`).

#### 4.7.3 Exponentials

The exponential `[F, G]` in
`PshParametricPresheaf C D` assigns to
`.typeNode P` the `D`-presheaf of parametric maps
from `F` to `G` "at stage P", and to
`.relNode P Q R` the `D`-presheaf of relatedness
witnesses for such maps.

For the edge category `PshRelEdge C`, the
exponential is computed explicitly:

```text
[(A₁, B₁, R₁), (A₂, B₂, R₂)]
  = (A₁.functorHom A₂,
     B₁.functorHom B₂,
     pshArrowRelSkel R₁ R₂)
```

where `pshArrowRelSkel R₁ R₂` relates `f` and `g`
when `f` maps R₁-related inputs to R₂-related
outputs via `g`. This is the presheaf-level
analogue of Wadler's relational interpretation of
function types (Section 11.5).

The identity section functor preserves
exponentials: `pshArrowRelSkel ΔA ΔB = Δ[A,B]`.
Code: `pshRelIdentFunctor_preserves_exp`
(`PshRelEdgeIdentPreservation.lean:141`).

#### 4.7.4 Why pointwise computation is correct

The correctness of the pointwise construction
follows from the span shape of `PshRelSpanObj C`.
Each type former decomposes relatedness correctly
because the witness type at each relation node is
the corresponding type-former applied to the
witness types of the components. The span
projections then force the decomposition to
respect endpoints.

This is definitional rather than a theorem: it
follows from how limits and colimits in functor
categories are computed (pointwise in the target
`E`). The span shape ensures that pointwise
computation at relation nodes produces the correct
relational interpretation.

### 4.8 Adjunction lifting

Type formers arising from universal properties
(products, coproducts, exponentials) are
characterized by adjunctions. The Barr extension
(Section 1.3) lifts endofunctors to relations,
but it does not correctly lift multi-argument
type formers: Barr-extending a partially applied
bifunctor replaces the fixed argument's relational
structure with the diagonal.

For example, Barr-extending `(. + B_0)` at
relation `R : PshRel P Q` yields:

```text
pshBarrLiftRel (. + B_0) R =
  { (inl(p), inl(q)) | (p, q) in R }
  ∪ { (inr(b), inr(b)) | b in B_0 }
```

The right component carries only the diagonal of
`B_0`, not an independent relation `R_2`. This
is NOT the parametric coproduct relation
`pshRelCoprod R_1 R_2`, which allows an arbitrary
`R_2` on the right.

#### 4.8.1 The adjunction lift recipe

Given an adjunction `G ⊣ F` (or `F ⊣ G`) where
`F : D -> PSh(C)` is a type former and
`G : PSh(C) -> D` is the structural adjunct, the
canonical parametric lift proceeds as follows:

1. **Determine the edge category of D.** For each
   category `D` appearing in the adjunction,
   determine the corresponding relational category
   `Edge(D)`.

2. **Lift the structural adjunct.** The functor
   `G : PSh(C) -> D` lifts to
   `G~ : PshRelEdge(C) -> Edge(D)`. This is
   typically straightforward because `G` has
   a canonical action on relations (e.g., the
   diagonal `Delta` maps `(P, Q, R)` to
   `((P, Q, R), (P, Q, R))`).

3. **Define the type former as the adjoint of
   the lifted structural functor.** The
   left (or right) adjoint of `G~` in
   `PshRelEdge(C)` is the canonical parametric
   lift `F~` of the type former.

The following table records the instances of
this recipe for the standard type formers:

| Adjunction | D | Edge(D) | G~ | F~ |
| ---------- | - | ------- | -- | -- |
| `+ ⊣ Delta` | `PSh(C)^2` | `PshRelEdge(C)^2` | `(E, E)` | `pshRelEdgeCoprod` |
| `Delta ⊣ x` | `PSh(C)^2` | `PshRelEdge(C)^2` | `(E, E)` | `pshRelEdgeProd` |
| `x ⊣ [-,-]` | `PSh(C)^2` | `PshRelEdge(C)^2` | `x~` | `pshRelEdgeExp` |
| `! ⊣ Delta_0` | `1` | `1` | `*` | `pshRelEdgeTerminal` |
| `Delta_0 ⊣ !` | `1` | `1` | `*` | `pshRelEdgeInitial` |

Code: `pshRelEdgeCoprod`
(`PshRelEdgeLimits.lean:228`),
`pshRelEdgeProd` (`PshRelEdgeExp.lean`),
`pshRelEdgeExp` (`PshRelEdgeExp.lean`).

#### 4.8.2 Properties of adjunction lifts

**Graph preservation.** When specializing the
lifted type former at graph relations
`pshRelGraph(f)`, the result is the graph of the
type former applied to the underlying morphisms.
For coproducts:

```text
pshRelCoprod (pshRelGraph f_1) (pshRelGraph f_2)
  = pshRelGraph (f_1 + f_2)
```

because `inl(a_1)` relates to `inl(b_1)` iff
`f_1(a_1) = b_1`, and `inr(a_2)` relates to
`inr(b_2)` iff `f_2(a_2) = b_2`, which is the
graph of `Sum.map f_1 f_2`. This is the "free
theorem" content for sum types.

**Identity extension.** The identity section
functor `pshRelIdentFunctor` preserves
adjunction lifts: for each type former `F`,

```text
I(F(A_1, ..., A_n)) = F~(I(A_1), ..., I(A_n))
```

This follows from `pshRelIdentFunctor` preserving
all finite limits and colimits
(`PshRelEdgeIdentPreservation.lean`) and
exponentials (`pshRelIdentFunctor_preserves_exp`).

**Compatibility with the copresheaf topos.**
At the `PshParametricFunctor C E` level, the
adjunction lift is postcomposition: `G ⊣ F`
in `E` gives `(G o -) ⊣ (F o -)` in the functor
category. This produces the pointwise (co)limits
of Section 4.7, which are the correct parametric
constructions.

#### 4.8.3 Limitations

Step 1 of the recipe (determining `Edge(D)`) is
not mechanical. For `D = PSh(C)^n`, the edge
category is `PshRelEdge(C)^n` — this follows from
the product structure. For `D = PSh(B)` with
`B != C`, the edge category would be
`PshRelEdge(B)`, but the relationship between
`PshRelEdge(B)` and `PshRelEdge(C)` is not
immediate.

For `D` not of the form `PSh(B)` or a product
thereof, it is not clear how to determine
`Edge(D)` canonically. The recipe applies when
`D` has a natural "relational" or "double
categorical" structure, but a general construction
of `Edge(D)` from `D` alone remains an open
question (Section 11.11, Q5).

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

`PshRelEdge C` is not balanced (a morphism that is
both mono and epi need not be iso). Consider the
morphism
`(id, id) : (P, P, emptyset) => (P, P, Delta_P)`
where `P` is nonempty. This is:

- **Mono**: the underlying presheaf maps `(id, id)`
  are jointly monic.
- **Epi**: the underlying presheaf maps are epi
  (both are identity), and since any extension of
  `(id, id)` to a third object determines its
  action on the relation by relatedness preservation,
  `(id, id)` is epi.
- **Not iso**: the inverse would require
  `(id, id) : (P, P, Delta_P) => (P, P, emptyset)`
  to preserve relatedness, mapping diagonal pairs to
  the empty relation; but `(a, a) in Delta_P` with
  `P` nonempty gives `(a, a) notin emptyset`.

Non-balancedness follows from the quasitopos
structure: in a quasitopos, non-strong monomorphisms
are not isomorphisms even when they are epi, because
they do not factor through the strong subobject
classifier.

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

- Fully faithful (`pshRelIdentFunctor_fullyFaithful`,
  `PshRelDouble.lean`; morphisms between identity
  relations are pairs `(alpha, alpha)`, determined
  by `alpha`, via `pshRelRelated_id_eq`)
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

By currying, `PSh(C x I^op)` is equivalent to
`[I^op, PSh(C)]`: functors from the walking
span category to presheaf categories. An object
is a span-shaped diagram `P <-- R --> Q` in
`PSh(C)`. The currying equivalence is standard
at the `Cat` level:
`PSh(C x I^op) = [(C x I^op)^op, Type]`
`~= [(C^op x I), Type]`
`~= [I, [C^op, Type]]`
`~= [I^op, PSh(C)]^op^op`
using the universal property of the product of
categories and the fact that `I` is self-dual
(the walking span is isomorphic to its opposite).
In Lean, the equivalence would use
`Functor.curry` and `Functor.uncurry` from
mathlib.

The relationship between these categories and
their relative merits as ambient universes for
parametricity requires further investigation.
The separation reflector
`PSh(C x I^op) => PshRelEdge C` may provide a
bridge connecting the two perspectives.

### 11.10 The topos landscape around PshRelEdge

The following chain of functors connects the
categories in our construction:

```text
PSh(C) --ident--> PshRelEdge C --incl--> PSh(C x I^op)
```

where:

- `ident = pshRelIdentFunctor` sends `P` to
  `(P, P, Delta_P)`. It is fully faithful
  (`pshRelIdentFunctor_fullyFaithful`,
  `PshRelDouble.lean`) and preserves all finite
  limits, finite colimits, and exponentials
  (Sections 11.6, 11.7;
  `PshRelEdgeIdentPreservation.lean`).
- `incl = pshRelEdgeInclusionFunctor` sends
  `(P, Q, R)` to the span
  `P <-- R.toFunctor --> Q` in `PSh(C)`.
  It is fully faithful
  (`pshRelEdgeInclusionFullyFaithful`,
  `PshRelEdgeInclusion.lean`). It has a left
  adjoint (the separation reflector, not yet
  formalized).

Composing these gives a fully faithful embedding
`PSh(C) -> PSh(C x I^op)`.

Structural properties along this chain:

| Category | Topos? | Balanced? | Size |
| -------- | ------ | --------- | ---- |
| PSh(C) | Y | Y | small site |
| PshRelEdge C | N (quasitopos) | N | small site |
| PSh(C x I^op) | Y | Y | small site |

`PshRelEdge C` sits between two toposes. The
outer topos `PSh(C x I^op)` is the presheaf topos
on `C x I^op`, equivalent to `[I^op, PSh(C)]`
(Section 11.9).

#### Ex/reg completion conjecture

The **exact completion** (or ex/reg completion)
`ex/reg(E)` of a regular category `E` freely
adjoins quotients of equivalence relations. For
a quasitopos `E`, the ex/reg completion is a
topos (Carboni, "Some free constructions in
realizability and proof theory", 1995; Menni,
"Exact completions and toposes", 2000).

`PshRelEdge C` is a quasitopos (Section 11.3),
hence regular. Its ex/reg completion is a topos.

**Conjecture**: `ex/reg(PshRelEdge C) ~= PSh(C x I^op)`.

Evidence:

- `PSh(C x I^op)` is a topos containing
  `PshRelEdge C` as a reflective subcategory with
  left-exact reflector (the separation reflector
  sends a span to its image in the product, which
  preserves finite limits).
- The objects of `PSh(C x I^op)` that are NOT in
  `PshRelEdge C` are spans `P <-- R --> Q` where
  `R -> P x Q` is not injective. These are
  quotient-like: the fibers of `R -> P x Q` give
  an equivalence relation on `R` whose quotient is
  a subobject of `P x Q` (i.e., a separated
  presheaf).
- The ex/reg completion of `Sep_J` for a subcanonical
  topology `J` on a presheaf category is known to be
  `Sh_J` in some cases; here the topology is not
  subcanonical, so the situation may differ. The
  ex/reg completion of `Sep_J(D)` for a general
  topology `J` on a presheaf category `PSh(D)` is
  `PSh(D)` itself when `Sep_J(D)` generates `PSh(D)`
  under exact completion.

If the conjecture holds, then
`PSh(C x I^op)` is the canonical topos completion
of the parametric quasitopos, and the chain becomes:

```text
PSh(C) --ident--> PshRelEdge C --incl-->
  ex/reg(PshRelEdge C) ~= PSh(C x I^op)
```

This would give a precise sense in which
`PSh(C x I^op)` is the "nearest topos" to
`PshRelEdge C`: it is obtained by freely
adjoining quotients.

### 11.11 The subobject classifier and lattice-enriched sites

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

### 11.12 Open questions

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

#### Q5: Canonical edge category construction

The adjunction lift recipe (Section 4.8) requires
determining the edge category `Edge(D)` for the
"other" category `D` in the adjunction. For
`D = PSh(C)^n`, the answer is `PshRelEdge(C)^n`.
For `D = PSh(B)`, the answer is `PshRelEdge(B)`.

Is there a canonical construction `Edge(-)` that
takes an arbitrary category `D` (or a category
with suitable structure) and produces its edge
category? Candidates:

- **Double-categorical structure.** If `D` has
  a double category of relations (analogous to
  `PshRelDouble` for presheaf categories), then
  `Edge(D)` is its vertical edge category. The
  question reduces to: which categories admit a
  canonical double category of relations?

- **Internal relations.** In a regular category
  `D`, one can form the category of internal
  relations (jointly monic spans). This gives
  `Edge(D)` as the category of "relation triples"
  `(A, B, R)` with `R ↪ A x B`. For `D = PSh(C)`,
  this recovers `PshRelEdge(C)`.

- **Subobject fibration.** `Edge(D)` could be
  defined as the total category of the subobject
  fibration over `D x D`, sending `(A, B)` to
  `Sub(A x B)`. This is the Grothendieck
  construction of
  `(A, B) |-> Sub(A x B) : (D x D)^op -> Cat`.
  For `D = PSh(C)`, this gives `PshRelEdge(C)`
  (Section 11.10, fibration perspective).

- **Power object.** If `D` is a topos with power
  object `P(B) = [B, Omega]`, then `Edge(D)` is
  the total category of
  `(A, B) |-> Hom(A, P(B)) : (D x D)^op -> Set`,
  which is equivalent to the subobject fibration.

The regularity-based and subobject-based
approaches apply whenever `D` has finite limits
and a suitable notion of subobject (regular
monomorphisms suffice). Whether these produce
the correct `Edge(D)` for the adjunction lift
recipe — and whether the lifted adjunctions
preserve the expected properties (graph
preservation, identity extension) — requires
further investigation.

#### Q6: Ex/reg completion of PshRelEdge

Is `ex/reg(PshRelEdge C) ~= PSh(C x I^op)`?
(See Section 11.10 for the conjecture and
evidence.) If so, the presheaf topos on
`C x I^op` is the canonical topos completion of
the parametric quasitopos. Verification would
require:

- Showing that the inclusion
  `PshRelEdge C -> PSh(C x I^op)` has a left exact
  left adjoint (i.e., that the separation reflector
  preserves finite limits)
- Verifying the universal property of the ex/reg
  completion: that every left exact functor from
  `PshRelEdge C` to a topos factors uniquely through
  `PSh(C x I^op)`

### 11.13 Formalization candidates

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
  identity extension result. **Done:**
  `pshRelIdentFunctor_preserves_exp`
  (`PshRelEdgeIdentPreservation.lean`).

- **(d)** Show `pshRelIdentFunctor` preserves
  products, limits, and colimits. **Done:**
  `pshRelIdentFunctor_preserves_prod`,
  `_preserves_terminal`, `_preserves_initial`,
  `_preserves_coprod`, `_preserves_equalizer`,
  `_preserves_coequalizer`
  (`PshRelEdgeIdentPreservation.lean`).

- **(d')** Show `pshRelIdentFunctor` is fully
  faithful. The functor sends `P` to
  `(P, P, Delta_P)`. A morphism
  `(alpha, beta) : (P, P, Delta_P) => (Q, Q, Delta_Q)`
  preserving diagonal relatedness forces
  `alpha = beta`: for all `a`, `(a, a) in Delta_P`
  implies `(alpha(a), beta(a)) in Delta_Q`, i.e.,
  `alpha(a) = beta(a)`. So `Hom(ident(P), ident(Q))`
  is isomorphic to `Hom(P, Q)`. **Done:**
  `pshRelIdentFunctor_fullyFaithful`
  (`PshRelDouble.lean`).

- **(e)** Construct the inclusion
  `PshRelEdge C -> PSh(C x I^op)` as an explicit
  fully faithful functor, and its left adjoint
  (the separation reflector). **Partially done:**
  `pshRelEdgeInclusionFunctor` and
  `pshRelEdgeInclusionFullyFaithful`
  (`PshRelEdgeInclusion.lean`) give the
  fully faithful functor
  `PshRelEdge C -> [WalkingSpan, PSh(C)]`.
  The left adjoint (separation reflector) is
  not yet formalized.

- **(f)** Construct the family of evaluation
  functors: for each `(P, Q, R)`,
  `eval_{P,Q,R} : PshParametricFunctor C E -> Spans(E)`
  sending `F` to
  `(F(.typeNode P), F(.typeNode Q), F(.relNode P Q R))`
  with projections `F(fstProj)`, `F(sndProj)`.
  Investigate the profunctor assembling these:
  `PshRelEdge(C)^op x PshParametricFunctor(C, E) -> E`.
  Note: there is no single functor
  `PshParametricPresheaf C -> PshRelEdge C` without
  fixing a relation.

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
