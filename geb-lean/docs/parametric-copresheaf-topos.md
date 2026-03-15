# The Parametric Copresheaf Topos

## Overview

This document describes the categorical framework for
parametric polymorphism over presheaf categories.

The construction centers on the **edge category**
`PshRelEdge C`, whose objects are presheaf relations
`(P, Q, R)` and whose morphisms are pairs of natural
transformations preserving relatedness. This category
carries the structure needed for parametric
polymorphism: finite limits and colimits, exponential
objects, a strong subobject classifier, and a fully
faithful embedding of `PSh(C)` via the identity
relation functor.

`PshRelEdge C` is the category of J-separated
presheaves on the product site `C x I^op` (where
`I` is the walking span), and sits between two
toposes:

```text
PSh(C)  --ident-->  PshRelEdge C  --incl-->
                                    PSh(C x I^op)
```

The **copresheaf topos** `PshParametricPresheaf C`
over the relational span category `PshRelSpanObj C`
provides an alternative ambient universe in which
parametricity is definitional: sections of a
copresheaf are parametric families by construction.
The Barr embedding lifts endofunctors on `PSh(C)` to
objects of `PshRelEdge C`, and the parametricity
condition on sections of the resulting edge functor
is equivalent to naturality of the endofunctor
section.

The construction does not depend on any
inductively-defined type language; it uses only the
double category of presheaf relations, the Yoneda
embedding, and the Barr extension.

## 1. Presheaf relations

### 1.1 Definition

A presheaf relation `R : PshRel P Q` between
presheaves `P, Q : C^op => Type` is a subfunctor of
the product presheaf `P x Q`. Concretely, `R` picks
out, at each stage `c : C^op`, a subset of
`P(c) x Q(c)`, compatibly with restriction maps.

Code: `PshRel` (`PshRelDouble.lean`), defined as
`Subfunctor (pshProdPresheaf P Q)`.

### 1.2 Double category structure

Presheaf relations form a double category
`PshRelDouble`:

- **Horizontal morphisms**: natural transformations
  between presheaves
- **Vertical morphisms**: presheaf relations
  `PshRel P Q`
- **Squares**: given horizontal morphisms
  `alpha : P => P'`, `beta : Q => Q'` and vertical
  morphisms `R : PshRel P Q`, `S : PshRel P' Q'`, a
  square witnesses that `alpha` and `beta` map
  R-related pairs to S-related pairs
  (`pshRelRelated`, `PshRelDouble.lean`)

Operations and laws:

| Operation | Code |
| --------- | ---- |
| Identity relation | `pshRelId` |
| Relation composition | `pshRelComp` |
| Graph of nat. trans. | `pshRelGraph` |
| Dagger (transpose) | `pshRelDagger` |
| Graph functor | `pshRelGraphFunctor` |
| Left identity | `pshRelComp_id_left` |
| Right identity | `pshRelComp_id_right` |
| Associativity | `pshRelComp_assoc` |
| Dagger involution | `pshRelDagger_dagger` |
| Double cat. data | `pshRelDoubleData` |

All references in `GebLean/PshRelDouble.lean`.

### 1.3 Relation lifting

Given an endofunctor `G : PSh(C) => PSh(C)` and a
relation `R : PshRel P Q`, the **Barr extension**
(relation lifting) `pshBarrLiftRel G R :
PshRel (G P) (G Q)` produces the relation whose
witnesses are pairs `(G(pi_1)(w), G(pi_2)(w))` for
`w` in the Barr lift of `R` through `G`.

Variants:

| Variant | Functor type | Code |
| ------- | ----------- | ---- |
| Covariant | `PSh(C) => PSh(C)` | `pshBarrLiftRel` |
| Contravariant | `PSh(C)^op => PSh(C)` | `pshContraBarrLiftRel` |
| Profunctor | `PSh(C)^op x PSh(C) => PSh(C)` | `pshProfBarrLiftRel` |
| Arrow | internal hom | `pshArrowRel` |

All in `GebLean/PshRelDouble.lean`.

The Barr extension of a graph relation recovers the
graph of the functor's action: `pshBarrLiftRel_graph`
(`PshRelDouble.lean`).

### 1.4 Arrow relation

Given relations `R_1 : PshRel P_1 Q_1` and
`R_2 : PshRel P_2 Q_2`, the arrow relation
`pshArrowRel R_1 R_2` relates internal-hom elements
`f : P_1 => P_2` and `g : Q_1 => Q_2` when `f` maps
R_1-related inputs to R_2-related outputs via `g`
(`PshRelDouble.lean`).

This is the presheaf-level analogue of Wadler's
relational interpretation of function types.

## 2. The edge category PshRelEdge C

### 2.1 Definition

The vertical edge category `PshRelEdge C` of the
double category of presheaf relations has:

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

### 2.2 Structure

As a category of J-separated presheaves for a
Grothendieck topology on the small category
`C x I^op` (Section 7.1), `PshRelEdge C` is a
**Grothendieck quasitopos** (Wyler 1991, Borceux
"Handbook of Categorical Algebra" Vol. 3). It has:

- All small limits and colimits
- Exponential objects (cartesian closed)
- Local cartesian closure
- A strong subobject classifier
- Epi-mono factorization (regular)

It is not a topos: it lacks a (full) subobject
classifier. Non-strong monomorphisms exist (e.g., a
proper inclusion `R ⊊ P x Q` into the total
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

Formalized structure:

| Construction | Code | File |
| ------------ | ---- | ---- |
| Terminal | `pshRelEdgeTerminal` | `PshRelEdgeLimits.lean` |
| Initial | `pshRelEdgeInitial` | `PshRelEdgeLimits.lean` |
| Binary products | `pshRelEdgeProd` | `PshRelEdgeExp.lean` |
| Binary coproducts | `pshRelEdgeCoprod` | `PshRelEdgeLimits.lean` |
| Equalizers | `pshRelEdgeEqualizer` | `PshRelEdgeLimits.lean` |
| Coequalizers | `pshRelEdgeCoequalizer` | `PshRelEdgeLimits.lean` |
| Exponentials | `pshRelEdgeExp` | `PshRelEdgeExp.lean` |
| Strong SO classif. | `pshRelEdgeSOClassifier` | `..SOClassifier.lean` |

### 2.3 Exponentials and the arrow relation

The exponential in `PshRelEdge C` of two objects
`(A_1, B_1, R_1)` and `(A_2, B_2, R_2)` is:

```text
[(A_1, B_1, R_1), (A_2, B_2, R_2)]
  = (A_1.functorHom A_2,
     B_1.functorHom B_2,
     pshArrowRel R_1 R_2)
```

The arrow relation `pshArrowRel R_1 R_2` relates
`f : [A_1, A_2](c)` and `g : [B_1, B_2](c)` when
`f` maps R_1-related inputs to R_2-related outputs
via `g`. This is the presheaf-level analogue of
Wadler's relational interpretation of function types.

Verification via the exponential adjunction:
morphisms
`(P, Q, S) x (A_1, B_1, R_1) => (A_2, B_2, R_2)`
in `PshRelEdge C` consist of `phi : P x A_1 => A_2`
and `psi : Q x B_1 => B_2` preserving
`(S x R_1)`-relatedness to `R_2`-relatedness. By the
internal hom adjunction in `PSh(C)`, this transposes
to `alpha : P => [A_1, A_2]` and
`beta : Q => [B_1, B_2]` mapping S-related pairs to
`pshArrowRel R_1 R_2`-related pairs.

Code: `pshArrowRel` and `pshIhomProfMap`
(`PshRelDouble.lean`).

### 2.4 Identity extension

The identity section functor
`pshRelIdentFunctor : PSh(C) => PshRelEdge C` sends
`P` to the identity relation `(P, P, Delta_P)`.

Properties:

- Fully faithful
  (`pshRelIdentFunctor_fullyFaithful`,
  `PshRelDouble.lean`; morphisms between identity
  relations are pairs `(alpha, alpha)`, determined by
  `alpha`, via `pshRelRelated_id_eq`)
- Preserves all finite limits and colimits
  (`PshRelEdgeIdentPreservation.lean`)
- Preserves exponentials:
  `pshArrowRel Delta_P Delta_Q = Delta_{[P, Q]}`.
  Code: `pshRelIdentFunctor_preserves_exp`
  (`PshRelEdgeIdentPreservation.lean`).

The exponential preservation is the **Identity
Extension Property** (Reynolds, Hermida-Reddy-Robinson
Proposition 6.3), now characterized as the statement
that `pshRelIdentFunctor` is a cartesian closed
functor.

Verification: `(f, g)` is arrow-related at diagonal
relations iff for all equal pairs `a = a'`,
`f(a) = g(a')`, which gives `f = g`. So the arrow
relation on diagonals is the diagonal of the internal
hom.

### 2.5 Yoneda embedding into the edge category

The composite
`C --yoneda--> PSh(C) --pshRelIdentFunctor-->
PshRelEdge C`
embeds `C` into the quasitopos. It is:

- Fully faithful (composite of fully faithful
  functors)
- Preserves all limits that exist in `C`
- Preserves cartesian closed structure when it exists
  (via identity extension)

Code: `pshRelIdentFunctor` (`PshRelDouble.lean`),
`yoneda` (mathlib).

## 3. Embeddings into PshRelEdge C

Several classes of categorical data embed into the
edge category:

### 3.1 Covariant Barr embedding

An endofunctor `G : PSh(C) => PSh(C)` determines an
edge object via the Barr extension:

- `P |-> (G(P), G(P), pshBarrLiftRel G (pshRelId P))`

and more generally, each presheaf relation
`R : PshRel P Q` yields an edge object
`(G(P), G(Q), pshBarrLiftRel G R)`.

The Barr extension is functorial in the presheaf
argument: `pshBarrLiftEdgeFunctor G :
PshRelEdge C => PshRelEdge C` sends edge objects to
edge objects and preserves the relatedness structure.

The Barr embedding is defined as the diagonal
composition:

```text
pshBarrEmbedding G :=
  pshRelIdentFunctor >> pshBarrLiftEdgeFunctor G
```

sending `P` to
`(G(P), G(P), pshBarrLiftRel G (pshRelId P))`.

This embedding is **fully faithful**: natural
transformations between endofunctors correspond
bijectively to natural transformations between their
Barr embeddings.

Code: `pshBarrEmbedding`,
`pshBarrEmbeddingFunctor`,
`pshBarrEmbeddingFunctor_fullyFaithful`
(`PshRelEdgeGraphRestriction.lean`);
`pshBarrLiftEdgeFunctor` (`PshRelDouble.lean`).

**Barr extension composition.** For composable
endofunctors `F, G : PSh(C) => PSh(C)`, the Barr
extension of the composition relates to the
composition of Barr extensions via a natural
comparison morphism:

```text
pshBarrLiftEdgeCompComparison F G :
  pshBarrLiftEdgeFunctor (F ⋙ G) ⟶
    pshBarrLiftEdgeFunctor F ⋙
    pshBarrLiftEdgeFunctor G
```

This comparison is a natural isomorphism when `G`
preserves pullbacks, and in particular when `G` is
a right adjoint.

Code: `pshBarrLiftEdgeCompComparison`,
`pshBarrLiftEdgeCompIso_of_preservesPullbacks`,
`pshBarrLiftEdgeCompIso_of_rightAdj`
(`PshRelDouble.lean`).

The Barr extension is a lax double functor from the
endofunctor category to the double category of
presheaf relations, and the laxity comparison
morphisms satisfy the expected coherence conditions.

Code: `pshBarrLiftDoubleFunctor`,
`pshBarrLiftDoubleFunctorUnit`,
`pshBarrLiftDoubleFunctorComposition`
(`PshRelDouble.lean`).

### 3.2 Contravariant embedding

A contravariant functor `F : PSh(C)^op => PSh(C)`
determines an edge object via the contravariant
Barr extension (pullback along relation projections):

- `P |-> (F(op P), F(op P),
  pshContraBarrLiftRel F (pshRelId P))`

This embedding is also **fully faithful**.

Code: `pshContraBarrEmbedding`
(`PshRelEdgeGraphRestriction.lean`).

### 3.3 Profunctor embedding

A profunctor `G : PSh(C)^op x PSh(C) => PSh(C)`
embeds via the profunctor Barr extension:

- `P |-> (G(op P, P), G(op P, P),
  pshProfBarrLiftRel G (pshRelId P))`

Code: `pshProfunctorEmbedding`
(`PshRelSpanDiagram.lean`).

### 3.4 Paranatural embedding

Endoprofunctors with paranatural transformations
(morphisms respecting the wedge condition) embed
faithfully.

Code: `pshParanaturalProfEmbedding`,
`pshParanaturalProfEmbedding_faithful`
(`PshRelSpanDiagram.lean`).

This embedding is faithful but not full: parametricity
is a stronger condition than paranaturality for nested
arrow types (see Section 5).

### 3.5 Type-level specialization

At `C = Discrete PUnit`, all embeddings specialize to
their type-level counterparts in
`RelSpanDiagram.lean`:

| Presheaf | Type | File |
| -------- | ---- | ---- |
| `pshBarrEmbedding` | `covariantEmbedding` | `RelSpanDiagram.lean` |
| `pshContraBarrEmbedding` | `contravariantEmbedding` | `RelSpanDiagram.lean` |
| `pshProfunctorEmbedding` | `profunctorEmbedding` | `RelSpanDiagram.lean` |
| `pshParanaturalProfEmbedding` | (via equiv) | -- |

The equivalence `parametricFunctorEquiv`
(`PshRelSpanDiagram.lean`) mediates between the two
levels.

## 4. Graph restriction and free theorems

### 4.1 Graph subcategory

The graph functor
`pshRelEdgeGraphFunctor : PSh(C) => PshRelEdge C`
sends a presheaf morphism `alpha : P => Q` to the
edge object `(P, Q, pshRelGraph alpha)`. This
functor is fully faithful
(`pshRelEdgeGraphFullyFaithful`,
`PshRelDouble.lean`).

The graph subcategory is the image of this functor:
the full subcategory of `PshRelEdge C` on objects of
the form `(P, Q, pshRelGraph alpha)`. The
inclusion from the graph subcategory into
`PshRelEdge C` is fully faithful.

Code: `pshRelEdgeGraphSubcatFunctor`,
`pshRelEdgeGraphSubcatFullyFaithful`
(`PshRelEdgeGraphRestriction.lean`).

### 4.2 Graph restriction

The Barr embedding interacts with the graph
subcategory via two natural isomorphisms:

```text
pshBarrLiftEdge_graphNatIso G :
  pshRelEdgeGraphFunctor ⋙ pshBarrLiftEdgeFunctor G
    ≅ G ⋙ pshRelEdgeGraphFunctor
```

This says: the Barr extension of a graph relation is
the graph of the functor's action. Specializing to
the identity relation gives:

```text
pshBarrLiftEdge_identNatIso G :
  pshRelIdentFunctor ⋙ pshBarrLiftEdgeFunctor G
    ≅ pshBarrEmbedding G
```

Code: `pshBarrLiftEdge_graphNatIso`,
`pshBarrLiftEdge_identNatIso`
(`PshRelEdgeGraphRestriction.lean`).

### 4.3 From relations to functions

Given a section `s` of a Barr-embedded copresheaf and
a presheaf relation `R : PshRel P Q` that is the
**graph** of a natural transformation `alpha : P => Q`,
the parametricity condition specializes to an
equational constraint.

For a section `s` of the copresheaf associated to an
endofunctor `G`, specializing the parametricity
condition at `pshRelGraph alpha` yields:

```text
G(alpha)(s(P)) = s(Q)
```

which is naturality of `s` with respect to `alpha`.
This is Wadler's derivation of the "free theorem" for
covariant types.

More generally, for copresheaves not arising from a
single embedding, specializing the parametricity
condition at graph relations produces constraints
that generalize naturality. For arrow types, these
become commutative diagrams involving the functions
derived from the graph relation.

### 4.4 Conditional free theorems

The free theorem for graph restrictions has both
unconditional and conditional variants.

**Unconditional.** For an endofunctor natural
transformation `sigma : F => G` and any presheaf
morphism `alpha : P => Q`:

```text
F.map(alpha) >> sigma_Q = sigma_P >> G.map(alpha)
```

This is the content of `conditional_freeTheorem_graph`
specialized to the full subcategory.

**Conditional.** For a functor `G` and a graph
subcategory restriction to a subcategory `S` of
`PSh(C)`, the free theorem holds for morphisms
`alpha` in `S`:

```text
conditional_freeTheorem_graph :
  G.map(alpha) >> sigma_Q = sigma_P >> G.map(alpha)
```

whenever `alpha` lies in the designated subcategory.
This captures Wadler's conditional free theorems
(monotonicity for sort, predicate-preservation for
filter, algebra homomorphism for fold) by choosing
`S` to be the subcategory of morphisms satisfying
the additional hypothesis.

Code: `conditional_freeTheorem_graph`,
`conditional_edge_freeTheorem`
(`PshRelEdgeGraphRestriction.lean`).

### 4.5 Specific free theorems

The Wadler correspondence table records specific
instances:

| Function | Free theorem | Code |
| -------- | ------------ | ---- |
| `head, tail, map` | naturality | W1-W2 |
| `r : [X] -> [X]` | `map a . r = r . map a` | W3 |
| `fold` | algebra homomorphism | W4 |
| `sort, nub` | conditional naturality | W5 |
| `filter` | predicate preservation | W6 |
| `(==)` | impossibility | W7 |
| `y(X)` | Yoneda isomorphism | W8 |
| parametricity | naturality = param. | W9 |

All in `PshRelEdgeGraphRestriction.lean`.

## 5. Parametricity vs. paranaturality

### 5.1 The distinction

Paranaturality tests only pairs of elements arising
from **off-diagonal** profunctor elements (the wedge
condition). Parametricity tests **all** commuting
pairs via arbitrary relations. These coincide for
types with at most one level of arrow nesting
("depth-one" types) but diverge for nested arrows.

### 5.2 Separation results

The divergence type
`forall X. ((X -> X) -> X) -> X` separates the
two notions:

- `divApplyId` is parametric but not paranatural
  (`divApplyId_parametric`,
  `divApplyId_not_paranatural`,
  `ParanaturalTopos.lean`)
- `divIterOnce` is parametric but not paranatural
  (`ParanaturalTopos.lean`)

The theorem
`divParametric_not_implies_divParanatural`
(`ParanaturalTopos.lean`) establishes the separation.

### 5.3 Categorical interpretation

In the copresheaf topos, paranaturality corresponds to
naturality with respect to a **subcategory** of
`PshRelSpanObj C` that includes only graph relations
(or more precisely, the image of the graph functor
from presheaf morphisms). Parametricity requires
naturality with respect to *all* morphisms of
`PshRelSpanObj C`, which includes non-graph relations.

The paranatural embedding being faithful but not full
(`pshParanaturalProfEmbedding_faithful`) reflects
this: every parametric morphism determines a
paranatural one (by restriction to graph relations),
but not conversely.

## 6. Sections and Yoneda extension

### 6.1 Presheaf sections and parametric cones

A **parametric cone** of an edge functor
`G : PshRelEdge C => PshRelEdge C` is a cone over the
composite `pshRelIdentFunctor >> G` with the terminal
edge object as vertex. Concretely, it picks an element
of `G(P, P, Delta_P)` at each presheaf `P`, compatibly
with the action of `G` on identity-related morphisms.

A **presheaf section** of an endofunctor
`G : PSh(C) => PSh(C)` is a natural transformation
from the terminal presheaf to `G`, i.e., a morphism
`pshUnitPresheaf C => G` in the functor category
`[PSh(C), PSh(C)]`. Equivalently, it selects an
element `sigma_P : G(P)` for each presheaf `P`,
natural in `P`.

These two concepts are equivalent:

```text
parametricConeEquivPresheafSection G :
  ParametricCone (pshBarrLiftEdgeFunctor G)
    ≃ PresheafSection G
```

Code: `ParametricCone`, `PresheafSection`,
`parametricConeEquivPresheafSection`
(`PshRelEdgeGraphRestriction.lean`).

### 6.2 Initial-presheaf characterization

Every presheaf section is uniquely determined by its
value at the initial presheaf `pshEmptyPresheaf C`:

```text
presheafSectionEquivInitial G :
  PresheafSection G ≃
    (pshUnitPresheaf C ⟶ G.obj (pshEmptyPresheaf C))
```

The forward direction evaluates at `∅`. The inverse
extends a morphism `tau : top => G(∅)` to a full
section via `sigma_P = tau >> G.map(!_P)`, where
`!_P : ∅ => P` is the unique morphism from the
initial presheaf.

Composing both equivalences gives:

```text
parametricConeEquivInitial G :
  ParametricCone (pshBarrLiftEdgeFunctor G) ≃
    (pshUnitPresheaf C ⟶ G.obj (pshEmptyPresheaf C))
```

Code: `presheafSectionEquivInitial`,
`presheafSectionOfInitial`,
`parametricConeEquivInitial`
(`PshRelEdgeGraphRestriction.lean`);
`pshEmptyPresheafIsInitial`, `pshEmptyMap_unique`
(`PshRelEdgeLimits.lean`).

### 6.3 Restriction to representables

A **representable section** of `G` restricted to an
embedding `Y : C => PSh(C)` picks an element
`rho_X : G(Y(X))` for each `X : C`, natural in `X`.

```text
RepresentableSection Y G :=
  constTerminal C (terminal) ⟶ Y ⋙ G
```

The definition is parameterized by `Y` to handle
universe polymorphism: standard `yoneda` gives
`Y : C => (C^op => Type v)` while `G` may act on
`Type w` with `w != v`. The functorial universe-
lifted Yoneda embedding `yonedaLarge` gives
`Y : C => (C^op => Type (max u v))` for use when
`w = max u v`.

Restriction from a presheaf section to a
representable section is given by
`presheafSectionRestrict Y sigma`. This restriction
is injective when the maps
`G.map(!_{Y(X)}) : G(∅) => G(Y(X))` are jointly
monic (`presheafSectionRestrict_injective`).

Code: `RepresentableSection`,
`presheafSectionRestrict`,
`presheafSectionRestrict_injective`,
`yonedaLarge` (`Utilities/Presheaf.lean`).

### 6.4 Full round-trip equivalence

Given a weakly initial object `X_0 : C` (meaning
`forall X, X_0 => X`) and an isomorphism
`Y(X_0) ≅ pshEmptyPresheaf C`, the restriction and
extension maps form an equivalence:

```text
presheafSectionEquivRepresentable Y G X_0 i hInit :
  PresheafSection G ≃ RepresentableSection Y G
```

The extension map sends a representable section `rho`
to a presheaf section via `sigma_P = rho_{X_0} >>
i.hom >> G.map(!_P)`. The proof that
extend-then-restrict recovers `rho` uses that all
morphisms from `Y(X_0) ≅ ∅` are equal (initiality).

Code: `presheafSectionEquivRepresentable`,
`representableSectionExtend`,
`representableSectionExtend_restrict`
(`PshRelEdgeGraphRestriction.lean`).

### 6.5 Joint-mono conditions

The behavior of presheaf sections depends on `G(∅)`:

- **`G(∅)` is initial and `C` is nonempty**: no
  presheaf sections exist, because a section would
  require a morphism `top => G(∅) ≅ ∅`, but `top` is
  inhabited while `∅` is not.
  Code: `presheafSection_empty_of_initial`.

- **`G(∅)` is terminal**: any two presheaf sections
  are equal, because both map to the unique morphism
  `top => G(∅) ≅ top` under `presheafSectionEquivInitial`.
  Code: `presheafSection_unique_of_terminal`.

Code: `no_morphism_terminal_to_initial`,
`presheafSection_empty_of_initial`,
`presheafSection_unique_of_terminal`
(`PshRelEdgeGraphRestriction.lean`).

### 6.6 Existential types (cocones and cosections)

The existential dual of `ParametricCone` is
`ParametricCocone`: a global element of a
colimit cocone point. Where `ParametricCone G`
gives the universal type `∀X. G(X)` (a cone
over `G` with vertex `⊤`), `ParametricCocone`
gives the existential type `∃X. G(X)` (a
morphism `⊤ ⟶ colim G`).

Unlike `ParametricCone`, which is defined
intrinsically as a natural transformation
`constTerminal ⟶ G`, the cocone side must be
parametrized by an explicit colimit cocone `s`
(to be computable).
The type `ParametricCocone G s hs` is
independent of the choice of `s` up to the
canonical isomorphism between colimit cocone
points (`parametricCoconeEquiv`).

An element of the colimit is an equivalence
class of **witnesses**: pairs `(e, x)` where
`e` is an edge and `x : ⊤ ⟶ G(e)`, with
`(e₁, x₁) ~ (e₂, x₂)` when they become
equal after pushing forward along morphisms
to a common edge.

The colimit injection at the terminal
edge/presheaf is an epimorphism: every other
injection factors through it. This is because
for any `e`, the unique morphism `e ⟶ ⊤` gives
`s.ι.app e = G.map(e ⟶ ⊤) ≫ s.ι.app ⊤`.

For Barr-lifted edge functors, the source
extraction `barrCoconeToPresheafCocone` builds
a cocone for `G` in `PSh(C)` from a cocone
for `pshBarrLiftEdgeFunctor G` in
`PshRelEdge C`, by restricting to identity
edges and taking source components. This is
the cocone dual of `parametricConeSrcSection`.

Code: `ParametricCocone`,
`parametricCoconeInject`,
`parametricCoconeEquiv`,
`PresheafCosection`,
`presheafCosectionInject`,
`presheafCosection_terminal_epi`,
`barrCoconeToPresheafCocone`,
`parametricCoconeToPresheafCosection`
(`PshRelEdgeGraphRestriction.lean`).

A potential connection to terminal coalgebras:
for a covariant endofunctor `G`, the terminal
`G`-coalgebra `νG` (when it exists) should
relate to `ParametricCocone` in the same way
that initial `G`-algebras relate to
`ParametricCone` via catamorphisms.

### 6.7 Future directions

Three extensions are not yet formalized:

- **Density-based extension.** Using the colimit
  decomposition of presheaves as colimits of
  representables (the density theorem) to construct
  sections, rather than the initial-presheaf
  characterization.

- **Right Kan extension.** Relating the initial-
  presheaf characterization to right Kan extension
  along the Yoneda embedding.

- **Terminal coalgebra connection.** Relating
  `ParametricCocone` to terminal coalgebra
  carriers, dualizing the initial-algebra /
  catamorphism connection for `ParametricCone`.

## 7. The ambient topos landscape

### 7.1 Separated presheaf characterization

Let `I = {0 <-- 01 --> 1}` be the walking span
category. An object of `PSh(C x I^op)` assigns to
each `c : C^op`:

- A set `F_0(c)` (at vertex 0)
- A set `F_1(c)` (at vertex 1)
- A set `F_01(c)` (at the span vertex)
- Maps `F_01(c) => F_0(c)` and `F_01(c) => F_1(c)`

functorially in `c`. This is a span of presheaves.

The Grothendieck topology `J` on `(C^op x I)`
generated by covering each `(c, 01)` by
`{(c, 01 => 0), (c, 01 => 1)}` defines a
separation condition: a presheaf `F` is
`J`-separated when
`F(c, 01) => F(c, 0) x F(c, 1)` is injective at
each stage `c`. This is exactly the condition that
`F_01` is a subfunctor of `F_0 x F_1`.

There is an equivalence of categories:

```text
PshRelEdge C  ~=  Sep_J(C x I^op)
```

- **Objects**: a separated presheaf assigns
  P(c), Q(c), R(c) with R(c) injecting into
  P(c) x Q(c), matching a subfunctor of the
  product.
- **Morphisms**: since the target is separated,
  a natural transformation at the
  01-component is uniquely determined by its
  0- and 1-components. The compatibility
  condition reduces to `pshRelRelated`.

Formalized: `IsSeparatedSpan` defines the
separation condition (joint monicity of
span projections).
`pshRelEdge_isSeparatedSpan` shows every
edge is separated.
`separatedSpanToEdge_inclusion` shows the
round-trip `sep(incl(E)) = E`.
`pshRelEdgeSepObj_inclusion` shows the
reflector round-trip.
`separatedSpan_unit_injective` shows the
adjunction unit is injective for separated
spans. The reflective adjunction
`pshRelEdgeSepAdjunction`
(`PshRelEdgeInclusion.lean`) captures the
categorical content.
Code: `PshRelEdgeSeparation.lean`.

The J-sheaves (where
`F(c, 01) => F(c, 0) x F(c, 1)` is bijective,
forcing `R = P x Q`) form the sheaf topos:

```text
Sh_J(C x I^op)  ~=  PSh(C) x PSh(C)
                 ~=  PSh(C ⊔ C)
```

This gives a chain of inclusions:

```text
PSh(C ⊔ C) ~= Sh_J  ↪  Sep_J ~= PshRelEdge C
                                  ↪  PSh(C x I^op)
```

### 7.2 Reflective and coreflective inclusions

The inclusion `PshRelEdge C ↪ PSh(C x I^op)` has a
left adjoint: the **separation reflector**
`sep : PSh(C x I^op) => PshRelEdge C`, which replaces
a span `(P, Q, F_01)` with the image
`(P, Q, Im(F_01 => P x Q))`. This makes
`PshRelEdge C` a **reflective subcategory** of
`PSh(C x I^op)`.

Formalized: `pshRelEdgeSepFunctor` (the reflector),
`pshRelEdgeSepAdjunction` (the adjunction
`pshRelEdgeSepFunctor ⊣ pshRelEdgeInclusionFunctor`),
`pshRelEdgeInclusionReflective` (the `Reflective`
instance), and `pshRelEdgeSepCounitIsIso` (the counit
is a natural isomorphism, since the right adjoint is
fully faithful). (`PshRelEdgeInclusion.lean`)

**Product preservation and exponential ideals.**
The separation reflector preserves finite products.
The vertex components are preserved trivially
(products in the functor category are pointwise).
For the relation component, the result follows from
the pointwise computation of images in presheaf
categories: `Im(f x g) = Im(f) x Im(g)` when images
are computed stagewise. This product preservation is
equivalent to `PshRelEdge C` being an **exponential
ideal** in `PSh(C x I^op)` (by
`Mathlib.CategoryTheory.Monoidal.Closed.Ideal`),
meaning the inclusion functor preserves exponentials.

The inclusion `PSh(C ⊔ C) ↪ PshRelEdge C` sends
`(P, Q)` to the total relation `(P, Q, P x Q)`. The
sheafification left adjoint
`PshRelEdge C => PSh(C ⊔ C)` sends `(P, Q, R)` to
`(P, Q)` (forgetting the relation).

```text
PSh(C x I^op)  --sep-->  PshRelEdge C  --forget-->
                                          PSh(C ⊔ C)
     ↑                       ↑                ↑
  inclusion              inclusion         inclusion
     |                       |                |
PSh(C x I^op)  <--incl--  PshRelEdge C  <--total--
                                          PSh(C ⊔ C)
```

### 7.3 The topos chain

The following chain of functors connects the
categories in the construction:

```text
PSh(C)  --ident-->  PshRelEdge C  --incl-->
                                    PSh(C x I^op)
```

where:

- `ident = pshRelIdentFunctor` sends `P` to
  `(P, P, Delta_P)`. It is fully faithful
  (`pshRelIdentFunctor_fullyFaithful`,
  `PshRelDouble.lean`) and preserves all finite
  limits, finite colimits, and exponentials
  (Section 2.4;
  `PshRelEdgeIdentPreservation.lean`).
- `incl = pshRelEdgeInclusionFunctor` sends
  `(P, Q, R)` to the span
  `P <-- R.toFunctor --> Q` in `PSh(C)`. It is
  fully faithful
  (`pshRelEdgeInclusionFullyFaithful`,
  `PshRelEdgeInclusion.lean`). It has a left
  adjoint (the separation reflector,
  `pshRelEdgeSepFunctor`).

Composing these gives a fully faithful embedding
`PSh(C) -> PSh(C x I^op)`.

Structural properties along this chain:

| Category | Topos? | Balanced? | Size |
| -------- | ------ | --------- | ---- |
| PSh(C) | Y | Y | small site |
| PshRelEdge C | N (quasitopos) | N | small site |
| PSh(C x I^op) | Y | Y | small site |

`PshRelEdge C` sits between two toposes. The outer
topos `PSh(C x I^op)` is the presheaf topos on
`C x I^op`, equivalent to `[I^op, PSh(C)]`
(Section 7.7).

#### Ex/reg completion

The **exact completion** (or ex/reg completion)
`ex/reg(E)` of a regular category `E` freely adjoins
quotients of equivalence relations. For a quasitopos
`E`, the ex/reg completion is a topos (Carboni,
"Some free constructions in realizability and proof
theory", 1995; Menni, "Exact completions and toposes",
2000).

The correct picture is the standard
presheaf/separated/sheaf layering:

```text
PSh(C x I^op)      presheaf topos (exact)
     |
     | separation reflector
     v
PshRelEdge C        separated presheaves (regular)
     |
     | sheafification
     v
Sh_J(C x I^op)     sheaf topos (exact)
```

The three layers correspond to:

| Sheaf theory | Completion theory |
| ------------ | ----------------- |
| PSh(D) | C (category with finite limits) |
| Sep_J(D) | C_reg (regular completion) |
| Sh_J(D) | C_ex (exact completion) |

The ex/reg completion goes **downward** from `Sep_J`
to `Sh_J`, not upward to `PSh`.

References: Carboni-Vitale, "Regular and exact
completions" (JPAA 125, 1998); Menni, "Exact
completions and toposes" (Edinburgh thesis, 2000);
Menni, "Closure operators in exact completions"
(TAC 8, 2001); Lack, "A note on the exact completion
of a regular category" (TAC 5, 1999);
Garner-Lack, "Grothendieck quasitoposes" (J. Algebra
355, 2012); Shulman, "Exact completions and small
sheaves" (TAC 27, 2012).

### 7.4 The relational span category PshRelSpanObj C

`PshRelSpanObj C` is a category whose objects are:

- `.typeNode P` for each presheaf `P : C^op => Type`
- `.relNode P Q R` for each presheaf relation
  `R : PshRel P Q`

and whose only non-identity morphisms are:

- `.fstProj P Q R : .relNode P Q R => .typeNode P`
- `.sndProj P Q R : .relNode P Q R => .typeNode Q`

There are no morphisms between distinct type nodes or
between distinct relation nodes. Each relation node
participates in exactly one span.

`PshRelSpanObj C` is the **free category** generated
by one span per presheaf relation, with no additional
morphisms. This means:

- No morphisms between distinct type nodes (no
  naturality/equivariance constraints between
  interpretations at different presheaves)
- No morphisms between distinct relation nodes (no
  consistency constraints between relatedness at
  different relations)
- No composition of relations

The absence of inter-relation morphisms is
structurally necessary: the three standard embeddings
(covariant, contravariant, profunctor) have
incompatible variance with respect to the subobject
ordering on relations (covariant Barr extension is
monotone, contravariant is antitone, profunctor is
neither). No single lattice enrichment accommodates
all three simultaneously.

Code: `PshRelSpanObj`, `PshRelSpanHom`
(`PshRelSpanDiagram.lean`).

`PshRelSpanObj C` is isomorphic to the collage of
the profunctor `pshRelSpanProfunctor`
(`pshRelSpanCollageIso`, `PshRelSpanDiagram.lean`).

### 7.5 The copresheaf topos PshParametricPresheaf C

The **parametric copresheaf topos** is:

```text
PshParametricPresheaf C D :=
  PshRelSpanObj C => (D^op => Type)
```

As a functor category into `Type` (or into a presheaf
category), this is a **Grothendieck topos**. It
therefore has all small limits and colimits,
exponential objects, a subobject classifier, and
epi-mono factorization.

An object `F : PshParametricPresheaf C D` assigns:

- To each presheaf `P`: an object
  `F(.typeNode P) : D^op => Type`
- To each relation `R : PshRel P Q`: an object
  `F(.relNode P Q R) : D^op => Type`
- Projection maps
  `F(fstProj) : F(.relNode P Q R) => F(.typeNode P)`
  and
  `F(sndProj) : F(.relNode P Q R) => F(.typeNode Q)`

A **section** (global element) of `F` picks one
element `s(P) in F(.typeNode P)` for each presheaf
`P` and one witness `s(R) in F(.relNode P Q R)` for
each relation `R`, with
`F(fstProj)(s(R)) = s(P)` and
`F(sndProj)(s(R)) = s(Q)`. The witness condition
says: the chosen elements are related under every
relation. This is the **parametricity condition**.

Equivalently, sections of `F` are the limit of `F`
viewed as a diagram `PshRelSpanObj C => Type`.

In the copresheaf topos, parametricity is
**definitional**: a section satisfies the
parametricity condition because that condition *is*
the naturality condition that defines sections. The
content that Wadler proves by induction on term
structure is replaced by the fact that the copresheaf
topos exists and has standard topos structure.

Code: `PshParametricFunctor`,
`PshParametricPresheaf`
(`PshRelSpanDiagram.lean`).

### 7.6 Comparison

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

### 7.7 PSh(C x I^op) as an ambient topos

`PSh(C x I^op)` is the category of "spans of
presheaves on C" (without the joint monomorphism
condition). It is a Grothendieck topos with a small
diagram category `C x I^op`.

By currying, `PSh(C x I^op)` is equivalent to
`[I^op, PSh(C)]`: functors from the walking span
category to presheaf categories. An object is a
span-shaped diagram `P <-- R --> Q` in `PSh(C)`.

An object of `PSh(C x I^op)` is a span
`(P, Q, R)` of presheaves with maps `R => P` and
`R => Q`, without requiring joint monicity.
Morphisms are triples `(alpha, beta, gamma)` with
naturality squares. This is richer than
`PshParametricPresheaf C` in that it has morphisms
connecting different "stages" of the span (via the
functoriality in `C`), but it does not independently
assign relation data to each `PshRel P Q`.

### 7.8 The subobject classifier and fibration

Relations in `PSh(C)` are classified by the subobject
classifier `Omega`:

```text
Sub(P x Q)  ~=  Hom(P x Q, Omega)
            ~=  Hom(P, [Q, Omega])
            =   Hom(P, P(Q))
```

where `P(Q) = [Q, Omega]` is the power object.

The boundary functor
`pshRelBoundaryFunctor :
PshRelEdge C => PSh(C) x PSh(C)`
is a pre-fibered category (proven in
`PshRelDouble.lean`). The fiber over `(P, Q)` is
`Sub(P x Q)`, which is a Heyting algebra.
`PshRelEdge C` is the **total category of the
Omega-valued subobject fibration** over
`PSh(C) x PSh(C)`.

For representable presheaves, `YonedaRel X Y` =
`Sub(y(X) x y(Y))` is a Heyting algebra. Each
element is a subfunctor that at stage `c` picks a
subset of `Hom(c, X) x Hom(c, Y)` closed under
precomposition.

## 8. Type formers as edge category operations

### 8.1 Products

The product `E_1 x E_2` in `PshRelEdge C` assigns:

```text
(A_1, B_1, R_1) x (A_2, B_2, R_2)
  = (A_1 x A_2, B_1 x B_2, R_1 x R_2)
```

where `R_1 x R_2` is the product of subfunctors.
A witness in the product is a pair of witnesses.

This matches Wadler's relational interpretation
of product types: `rel(A x B)(R)` consists of
pairs `((a_1, b_1), (a_2, b_2))` where `a_1`
R-relates to `a_2` via `A` and `b_1` R-relates to
`b_2` via `B`.

The identity section functor preserves products:
`pshRelIdentFunctor_preserves_prod`
(`PshRelEdgeIdentPreservation.lean`).

### 8.2 Coproducts

The coproduct `E_1 ⊕ E_2` in `PshRelEdge C` assigns:

```text
(A_1, B_1, R_1) ⊕ (A_2, B_2, R_2)
  = (A_1 ⊕ A_2, B_1 ⊕ B_2, R_1 ⊕ R_2)
```

A witness in the coproduct is either an `R_1`-witness
(via `inl`) or an `R_2`-witness (via `inr`). There
are **no witnesses for mixed pairs**: an `A_1`-element
and a `B_2`-element have no witness that projects to
them.

This matches Wadler's relational interpretation
of sum types: `rel(A + B)(R) = rel(A)(R) + rel(B)(R)`,
where `inl(a_1)` and `inl(a_2)` are related iff
`a_1` R-relates to `a_2` via `A`, and `inl/inr`
mixtures are never related.

The identity section functor preserves coproducts:
`pshRelIdentFunctor_preserves_coprod`
(`PshRelEdgeIdentPreservation.lean`).

### 8.3 Exponentials

See Section 2.3. The exponential in `PshRelEdge C`
uses the arrow relation, and the identity section
functor preserves exponentials (Section 2.4).

### 8.4 Adjunction lifting

Type formers arising from universal properties
(products, coproducts, exponentials) are characterized
by adjunctions. The Barr extension (Section 1.3)
lifts endofunctors to relations, but it does not
correctly lift multi-argument type formers:
Barr-extending a partially applied bifunctor replaces
the fixed argument's relational structure with the
diagonal.

#### The adjunction lift recipe

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
   `G~ : PshRelEdge(C) -> Edge(D)`.

3. **Define the type former as the adjoint of the
   lifted structural functor.** The left (or right)
   adjoint of `G~` in `PshRelEdge(C)` is the
   canonical parametric lift `F~`.

| Adjunction | D | Edge(D) | G~ | F~ |
| ---------- | - | ------- | -- | -- |
| `+ ⊣ Delta` | `PSh(C)^2` | `PshRelEdge(C)^2` | `(E, E)` | `pshRelEdgeCoprod` |
| `Delta ⊣ x` | `PSh(C)^2` | `PshRelEdge(C)^2` | `(E, E)` | `pshRelEdgeProd` |
| `x ⊣ [-,-]` | `PSh(C)^2` | `PshRelEdge(C)^2` | `x~` | `pshRelEdgeExp` |
| `! ⊣ Delta_0` | `1` | `1` | `*` | `pshRelEdgeTerminal` |
| `Delta_0 ⊣ !` | `1` | `1` | `*` | `pshRelEdgeInitial` |

#### Properties of adjunction lifts

**Graph preservation.** When specializing the lifted
type former at graph relations
`pshRelGraph(f)`, the result is the graph of the type
former applied to the underlying morphisms.

**Identity extension.** The identity section functor
`pshRelIdentFunctor` preserves adjunction lifts: for
each type former `F`,

```text
I(F(A_1, ..., A_n)) = F~(I(A_1), ..., I(A_n))
```

This follows from `pshRelIdentFunctor` preserving all
finite limits and colimits
(`PshRelEdgeIdentPreservation.lean`) and exponentials
(`pshRelIdentFunctor_preserves_exp`).

#### Limitations

Step 1 of the recipe (determining `Edge(D)`) is not
mechanical. For `D = PSh(C)^n`, the edge category is
`PshRelEdge(C)^n`. For `D = PSh(B)` with `B != C`,
the edge category would be `PshRelEdge(B)`, but the
relationship between `PshRelEdge(B)` and
`PshRelEdge(C)` is not immediate.

For `D` not of the form `PSh(B)` or a product thereof,
it is not clear how to determine `Edge(D)` canonically.
This remains an open question (Section 11, Q5).

### 8.5 Pointwise computation

Because `PshParametricPresheaf C D` is a functor
category, all limits and colimits are computed
**pointwise**:
`(F ⊕ G)(X) = F(X) ⊕ G(X)`,
`(F × G)(X) = F(X) × G(X)`, etc. for each object
`X` of `PshRelSpanObj C`. This pointwise computation
produces the correct parametric type formers
(Section 7.5).

| Type former | Operation | Edge category |
| ---------- | --------- | ------------- |
| `forall X. T(X)` | Limit (end) | Section 6.1 |
| `exists X. T(X)` | Colimit (coend) | -- |
| `T_1 -> T_2` | Exponential | Section 2.3 |
| `T_1 x T_2` | Product | Section 8.1 |
| `T_1 + T_2` | Coproduct | Section 8.2 |
| Subtype | Subobject | Via SO classifier |

## 9. Yoneda relations

### 9.1 Definition

A Yoneda relation `YonedaRel X Y` between objects
`X, Y : C` is a presheaf relation between their
representable presheaves:
`YonedaRel X Y = PshRel (yoneda X) (yoneda Y)`
(`YonedaRelDouble.lean`).

This embeds the morphisms of `C` into relations via
the graph construction: `yonedaRelGraph f` for
`f : X => Y` (`YonedaRelDouble.lean`).

### 9.2 Double category structure

Yoneda relations form their own double category
`yonedaRelDoubleData` (`YonedaRelDouble.lean`), which
is a sub-double-category of `PshRelDouble`. The graph
functor `yonedaRelGraphFunctor : C => YonedaRelCat`
(`YonedaRelDouble.lean`) embeds `C` into its double
category of Yoneda relations.

### 9.3 Terminal specialization

When `C = Discrete PUnit`, Yoneda relations specialize
to ordinary type-level relations
`R : I_0 => I_1 => Prop`. The specialization is
`terminalYonedaRelDoubleData`
(`YonedaRelDouble.lean`).

## 10. Code infrastructure

### 10.1 File map

| File | Content |
| ---- | ------- |
| `PshRelDouble.lean` | Double category, Barr extension, identity functor |
| `YonedaRelDouble.lean` | Yoneda relations, double category |
| `PshRelEdgeExp.lean` | Products, exponentials |
| `PshRelEdgeLimits.lean` | Terminal, initial, (co)products, (co)equalizers |
| `PshRelEdgeSOClassifier.lean` | Strong subobject classifier |
| `..IdentPreservation.lean` | Identity functor preserves (co)limits, exp |
| `PshRelEdgeInclusion.lean` | Inclusion, separation reflector, adjunction |
| `PshRelEdgeSeparation.lean` | Separated span characterization |
| `PshRelEdgeOverOmega.lean` | Characteristic maps, sieve presheaves |
| `..GraphRestriction.lean` | Barr embeddings, graph restriction, free theorems |
| `PshRelSpanDiagram.lean` | PshRelSpanObj, copresheaf embeddings |
| `RelSpanDiagram.lean` | Type-level span category |
| `ParanaturalTopos.lean` | TypeExpr, ParametricFamily, divergence |
| `PshTypeExpr.lean` | PshTypeExpr, presheaf-level bridges |
| `Utilities/Presheaf.lean` | yonedaULift, yonedaLarge, Yoneda extension |

### 10.2 Equivalences with the type level

| Presheaf level | Type level |
| ------------- | --------- |
| `PshRelSpanObj (Discrete PUnit)` | `RelSpanObj` |
| `PshParametricFunctor .. E` | `ParametricFunctor E` |
| `PshParametricPresheaf ..` | `ParametricCopresheaf` |

Mediated by `relSpanPshRelSpanIso`,
`parametricFunctorEquiv`, `parametricCopresheafEquiv`.

### 10.3 Syntax layers (TypeExpr / PshTypeExpr)

`TypeExpr` (`ParanaturalTopos.lean`) and
`PshTypeExpr` (`PshTypeExpr.lean`) provide an
inductive type-expression syntax with `.var`,
`.app F T`, `.arrow T₁ T₂`. These define
`relInterp` / `fullRelInterp` by structural
induction, compute `ParametricFamily T` for
specific type expressions, and establish
equivalences such as
`dialgebraParametricEquivNatTrans` and
`initialAlgebraParametricEquiv`.

These are potential front-end syntaxes for the
categorical foundations, not part of the
foundations themselves. The categorical layer
(`PshRelEdge`, `ParametricCone`,
`PresheafSection`, `pshBarrLiftEdgeFunctor`,
etc.) is independent of `TypeExpr` and handles
covariant endofunctors directly. Extensions to
`TypeExpr` (multi-variable types, product types,
weight functors) are deferred as potential
future work on the syntax layer.

## 11. Open questions and future work

### Q1: PSh(C x I^op) vs PshParametricPresheaf C

`PSh(C x I^op)` handles one span at a time.
`PshParametricPresheaf C` handles all relations
simultaneously. Does `PSh(C x I^op)` allow a
construction that recovers the "all relations at
once" aspect? Approaches include internal presheaves
on `Omega`, power object constructions, and
Eilenberg-Moore algebras for the power monad.

### Q2: Lattice enrichment and variance

The three standard embeddings have incompatible
variance with respect to the subobject ordering on
relations (Section 7.4). No single lattice
enrichment of the span category accommodates all
three embedding classes simultaneously.

### Q3: Yoneda extension of parametric structure

For the Yoneda-restricted subobject site: does the
left Kan extension along the Yoneda embedding
preserve the parametricity structure? See the
`yonedaULift`, `yonedaLarge`, `yonedaExt`
infrastructure in `Utilities/Presheaf.lean`.

### Q4: Internal Heyting algebra and directed type theory

The subobject classifier `Omega`, viewed as an
internal category (via its Heyting algebra structure),
determines a notion of "internal presheaves on
Omega." The category of such internal presheaves may
provide a canonical ambient topos reflecting the full
subobject lattice structure. This connects to
Neumann-Licata directed type theory (POPL 2026).

### Q5: Canonical edge category construction

The adjunction lift recipe (Section 8.4) requires
determining `Edge(D)` for the "other" category `D`.
Candidates:

- **Internal relations.** In a regular category `D`,
  form the category of internal relations (jointly
  monic spans). For `D = PSh(C)`, this recovers
  `PshRelEdge(C)`.
- **Subobject fibration.** `Edge(D)` as the total
  category of `(A, B) |-> Sub(A x B)`. For
  `D = PSh(C)`, this gives `PshRelEdge(C)`
  (Section 7.8).
- **Power object.** If `D` is a topos, use
  `(A, B) |-> Hom(A, [B, Omega])`.

### Q6: Sep_J equivalence (resolved)

The separation characterization is formalized
in `PshRelEdgeSeparation.lean`: `IsSeparatedSpan`
defines the condition, edges are separated
(`pshRelEdge_isSeparatedSpan`), and the
reflective adjunction (`pshRelEdgeSepAdjunction`)
captures the categorical equivalence. The full
isomorphism with the separated full subcategory
requires `Classical.choice` to invert the
pairing map (extracting witnesses from
`Set.range`). (Task S1.)

### Q7: Span bicategory

Spans in `PSh(C)` form a bicategory (using pullbacks
for composition). The objects of `PshRelEdge C` are
spans, and span composition via pullback gives a
bicategorical structure. Constructing this would
require span composition, associators, 2-morphisms,
and coherence identities.

### Q8: Internal parametricity

The internal language of the copresheaf topos
(its Mitchell-Benabou language) provides a type
theory in which parametricity is a built-in property.
This may connect to directed type theory and
parametricity (Neumann-Licata, POPL 2026). (Task I1.)

### Q9: Density-based extension

Use the colimit decomposition of presheaves as
colimits of representables (the density theorem) to
construct presheaf sections, as an alternative to
the initial-presheaf characterization of
Section 6.2.

### Q10: Right Kan extension connection

Relate the initial-presheaf characterization of
presheaf sections (Section 6.2) to right Kan
extension along the Yoneda embedding.

### Q11: Terminal coalgebra and ParametricCocone

Relate `ParametricCocone` (Section 6.6) to
terminal coalgebra carriers, dualizing the
type-level result `initialAlgebraParametricEquiv`
(`ParanaturalTopos.lean`). For a covariant
endofunctor `G`, the terminal `G`-coalgebra
`νG` should biject with parametric cocones of
the Barr-lifted edge functor, with the
anamorphism (unfold) playing the role that the
catamorphism (fold) plays for initial algebras.

## 12. References

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
- Hermida, Reddy, Robinson, "Logical relations and
  parametricity" (2014) -- presheaf-level parametricity
  and Identity Extension Property
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
- Wyler, "Lecture Notes on Topoi and Quasitopoi" (1991)
  -- quasitopos theory
- Borceux, "Handbook of Categorical Algebra" Vol. 3
  (1994) -- topos and quasitopos theory
- Carboni-Vitale, "Regular and exact completions"
  (JPAA 125, 1998)
- Menni, "Exact completions and toposes" (Edinburgh
  thesis, 2000)
- Menni, "Closure operators in exact completions"
  (TAC 8, 2001)
- Lack, "A note on the exact completion of a regular
  category" (TAC 5, 1999)
- Garner-Lack, "Grothendieck quasitoposes" (J. Algebra
  355, 2012)
- Shulman, "Exact completions and small sheaves"
  (TAC 27, 2012)
