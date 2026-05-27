# Categories as Copresheaves on CategoryJudgments

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [The CategoryJudgments Index Category](#the-categoryjudgments-index-category)
- [Embedding Categories into Copresheaves](#embedding-categories-into-copresheaves)
  - [Object assignments](#object-assignments)
  - [Morphism assignments](#morphism-assignments)
  - [Verification of commutativity](#verification-of-commutativity)
- [The Functor Cat → [J, Type]](#the-functor-cat-%E2%86%92-j-type)
- [What Copresheaves Miss: The Gap Between [J, Type] and Cat](#what-copresheaves-miss-the-gap-between-j-type-and-cat)
  - [1. Identity uniqueness (F(Id) ≅ F(Obj))](#1-identity-uniqueness-fid-%E2%89%85-fobj)
  - [2. Composition totality (F(Comp) is the pullback)](#2-composition-totality-fcomp-is-the-pullback)
  - [3. Associativity (equalizer condition)](#3-associativity-equalizer-condition)
  - [4. Unit laws (equalizer conditions)](#4-unit-laws-equalizer-conditions)
- [Characterizing the Image](#characterizing-the-image)
- [Relationship to Quivers and the Walking Arrows](#relationship-to-quivers-and-the-walking-arrows)
- [The Reflection Functor [J, Type] → Cat](#the-reflection-functor-j-type-%E2%86%92-cat)
  - [Construction of L(F)](#construction-of-lf)
    - [Step 1: Extract the quiver](#step-1-extract-the-quiver)
    - [Step 2: Form the free category](#step-2-form-the-free-category)
    - [Step 3: Quotient by identity and composition relations](#step-3-quotient-by-identity-and-composition-relations)
  - [Category laws are automatic](#category-laws-are-automatic)
  - [Functoriality](#functoriality)
  - [The adjunction L ⊣ Φ](#the-adjunction-l-%E2%8A%A3-%CF%86)
  - [Round-trip properties](#round-trip-properties)
  - [Characterization via the adjunction](#characterization-via-the-adjunction)
- [Identity as a Natural Transformation](#identity-as-a-natural-transformation)
- [Why Cat is Not a Topos](#why-cat-is-not-a-topos)
- [Implementation Design Decisions](#implementation-design-decisions)
  - [Copresheaf representation](#copresheaf-representation)
  - [Free category (FreeMor) representation](#free-category-freemor-representation)
  - [Quotient structure](#quotient-structure)
  - [Category representation](#category-representation)
  - [Implementation phases](#implementation-phases)
- [References](#references)
- [Mathematical Context](#mathematical-context)
  - [Related Constructions](#related-constructions)
  - [Potential Applications](#potential-applications)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document describes the relationship between the category `Cat` of small
categories and the copresheaf category `[CategoryJudgments, Type]`.

## The CategoryJudgments Index Category

The file `GebLean/CategoryJudgments.lean` defines a finite acyclic category J
(which we call "CategoryJudgments") whose objects represent the components
needed to specify a category:

**Objects:**

- `Obj` - represents the type of objects
- `Mor` - represents the type of morphisms
- `Id` - represents identity judgments (witnesses that a morphism is an
  identity)
- `Comp` - represents composition judgments (witnesses of composition triples)

**Morphisms (non-identity):**

From `Mor`:

- `dom : Mor → Obj` - domain of a morphism
- `cod : Mor → Obj` - codomain of a morphism

From `Id`:

- `idObj : Id → Obj` - which object an identity is for
- `idMor : Id → Mor` - which morphism is the identity

From `Comp`:

- `left : Comp → Mor` - the second morphism (post-composed)
- `right : Comp → Mor` - the first morphism (pre-composed)
- `composite : Comp → Mor` - the resulting composite
- `intermediate : Comp → Obj` - the shared intermediate object
- `compositeDom : Comp → Obj` - domain of the composite
- `compositeCod : Comp → Obj` - codomain of the composite

**Commutativity relations:**

The composition of morphisms in J encodes type-correctness constraints:

```text
idMor ≫ dom = idObj       (identity has same domain as its object)
idMor ≫ cod = idObj       (identity has same codomain as its object)
right ≫ cod = intermediate    (first morphism's codomain is intermediate)
left ≫ dom = intermediate     (second morphism's domain is intermediate)
right ≫ dom = compositeDom    (composite's domain = first morphism's domain)
left ≫ cod = compositeCod     (composite's codomain = second morphism's codomain)
composite ≫ dom = compositeDom
composite ≫ cod = compositeCod
```

## Embedding Categories into Copresheaves

Given a category C, we construct a copresheaf F : J → Type as follows:

### Object assignments

|J object|F assigns|Description|
|---|---|---|
|Obj|Obj_C|The type of objects in C|
|Mor|Σ (a b : Obj_C), Hom(a,b)|The sigma type of all morphisms|
|Id|Obj_C|One identity witness per object|
|Comp|{ (f,g) \| tgt(f) = src(g) }|Composable pairs|

### Morphism assignments

|J morphism|F assigns|Description|
|---|---|---|
|dom|src|First projection of sigma|
|cod|tgt|Second index of sigma|
|idObj|id_Obj|Identity on objects|
|idMor|a ↦ ⟨a, a, id_a⟩|Identity morphism assignment|
|left|(f,g) ↦ g|Second morphism of pair|
|right|(f,g) ↦ f|First morphism of pair|
|composite|(f,g) ↦ f ≫ g|Actual composition|
|intermediate|(f,g) ↦ tgt(f)|Shared object|
|compositeDom|(f,g) ↦ src(f)|Domain of composite|
|compositeCod|(f,g) ↦ tgt(g)|Codomain of composite|

### Verification of commutativity

The commutativity relations in J are satisfied:

- `F(idMor) ≫ F(dom) = F(idObj)`: src(id_a) = a
- `F(idMor) ≫ F(cod) = F(idObj)`: tgt(id_a) = a
- `F(right) ≫ F(cod) = F(intermediate)`: tgt(f) = intermediate
- `F(left) ≫ F(dom) = F(intermediate)`: src(g) = intermediate
- `F(right) ≫ F(dom) = F(compositeDom)`: src(f) = compositeDom
- `F(left) ≫ F(cod) = F(compositeCod)`: tgt(g) = compositeCod
- `F(composite) ≫ F(dom) = F(compositeDom)`: src(f ≫ g) = src(f)
- `F(composite) ≫ F(cod) = F(compositeCod)`: tgt(f ≫ g) = tgt(g)

## The Functor Cat → [J, Type]

The construction above defines a functor from Cat to the copresheaf category:

```text
Φ : Cat → [J, Type]
```

This functor is:

- **Faithful**: Distinct functors between categories give distinct natural
  transformations between copresheaves
- **Not full**: Not every natural transformation between Φ(C) and Φ(D) comes
  from a functor C → D
- **Not essentially surjective**: Not every copresheaf on J is in the image

## What Copresheaves Miss: The Gap Between [J, Type] and Cat

A general copresheaf F : J → Type has the right "shape" but may fail to be
an actual category in several ways:

### 1. Identity uniqueness (F(Id) ≅ F(Obj))

For an actual category, each object has exactly one identity morphism. In
the copresheaf, this means F(Id) should be isomorphic to F(Obj) via F(idObj).

A general copresheaf might have:

- Multiple "identity witnesses" for the same object
- Missing identity witnesses for some objects

### 2. Composition totality (F(Comp) is the pullback)

For an actual category, every composable pair has exactly one composite. This
means F(Comp) should be the pullback:

```text
F(Comp) ──→ F(Mor)
   │           │
   │           │ F(dom)
   ↓           ↓
F(Mor) ──→ F(Obj)
       F(cod)
```

A general copresheaf might have:

- Multiple composition witnesses for the same pair
- Missing compositions for some composable pairs
- "Spurious" composition witnesses for non-composable pairs

### 3. Associativity (equalizer condition)

For an actual category, (f ≫ g) ≫ h = f ≫ (g ≫ h). This is an equality
between two morphisms of copresheaves, not structure that J encodes.

### 4. Unit laws (equalizer conditions)

For an actual category, id_a ≫ f = f and f ≫ id_b = f. These are also
equalities not encoded by J.

## Characterizing the Image

The image of Φ consists of copresheaves F : J → Type satisfying:

1. **Isomorphism condition**: F(idObj) : F(Id) → F(Obj) is an isomorphism
2. **Pullback condition**: F(Comp) with (F(right), F(left)) is the pullback
   of (F(cod), F(dom))
3. **Functionality**: F(composite) is determined by (F(right), F(left))
4. **Associativity**: For triple-composable morphisms, the two ways of
   composing give equal results
5. **Unit laws**: Composing with identities acts as identity

Conditions 1-3 are limit conditions in the copresheaf category.
Conditions 4-5 are equalizer conditions (equations between morphisms).

This characterization shows that Cat is the category of models of a
**finite limit sketch** (or essentially algebraic theory) presented over J.

## Relationship to Quivers and the Walking Arrows

The simplest case is the quiver level. A quiver is a copresheaf on the
"walking parallel arrows" category:

```text
W = { 0 ⇉ 1 }  (two objects, two parallel non-identity morphisms s, t)
```

A copresheaf F : W → Type gives:

- F(0) = MorType (morphisms)
- F(1) = Obj (objects)
- F(s) = src, F(t) = tgt

CategoryJudgments extends this by adding Id and Comp objects with their
morphisms, encoding the additional structure needed for categories.

## The Reflection Functor [J, Type] → Cat

The embedding Φ : Cat → [J, Type] has a left adjoint L : [J, Type] → Cat.
This makes Cat a **reflective subcategory** of [J, Type].

### Construction of L(F)

Given a copresheaf F : J → Type, we construct a category L(F) as follows:

#### Step 1: Extract the quiver

From F, extract a quiver Q_F:

- Objects: F(Obj)
- Morphisms: F(Mor)
- Source: F(dom) : F(Mor) → F(Obj)
- Target: F(cod) : F(Mor) → F(Obj)

#### Step 2: Form the free category

Construct Free(Q_F), the free category on this quiver:

- Objects: F(Obj)
- Morphisms a → b: binary trees of composable morphisms (`FreeMor Q_F a b`)
- Identity at a: the `id a` constructor
- Composition: the `comp g f` constructor

The free category satisfies identity and associativity laws up to the
equivalence relation defined in Step 3.

#### Step 3: Quotient by identity and composition relations

Define an equivalence relation `FreeMorEquiv` on morphisms of Free(Q_F)
generated by:

1. **Category axioms**:
   - `id_left`: `comp (id b) f ~ f`
   - `id_right`: `comp f (id a) ~ f`
   - `assoc`: `comp h (comp g f) ~ comp (comp h g) f`

2. **Identity relations**: For each i ∈ F(Id), identify:
   - `var (F(idMor)(i)) ~ id (F(idObj)(i))`

3. **Composition relations**: For each c ∈ F(Comp), identify:
   - `comp (var (F(left)(c))) (var (F(right)(c))) ~ var (F(composite)(c))`

4. **Congruence**: The relation respects composition:
   - If `f ~ f'` and `g ~ g'` then `comp g f ~ comp g' f'`

The category L(F) = Free(Q_F) / FreeMorEquiv is the quotient category.

### Category laws are automatic

Category laws are built into the equivalence relation via the generating
relations `id_left`, `id_right`, and `assoc`. The quotient then inherits
these laws as equalities.

**Associativity**: The `assoc` generating relation directly gives:

```text
comp h (comp g f) ~ comp (comp h g) f
```

**Left identity**: For f : a → b, if i witnesses identity at a:

- `var (idMor i) ~ id (idObj i)` (by identity witness relation)
- `comp (id b) f ~ f` (by id_left)

**Right identity**: Similarly via the `id_right` relation.

**Associativity of declared composites**: If we have composition witnesses:

- c₁ witnessing `comp (var g) (var f) ~ var h`
- c₂ witnessing `comp (var k) (var g) ~ var m`

Then in the quotient, using congruence and transitivity:

```text
comp (var k) (comp (var g) (var f))
  ~ comp (var k) (var h)           (by c₁ + congruence)
  ~ comp (comp (var k) (var g)) (var f)  (by assoc)
  ~ comp (var m) (var f)           (by c₂ + congruence)
```

The category axioms, identity witnesses, and composition witnesses together
force all morphisms to be identified appropriately in the quotient.

### Functoriality

Given a natural transformation α : F → G between copresheaves, we get a
functor L(α) : L(F) → L(G):

- On objects: α_Obj : F(Obj) → G(Obj)
- On morphisms: map recursively via `FreeMor.mapQuiver`:
  - `var f ↦ var (α_Mor f)`
  - `id a ↦ id (α_Obj a)`
  - `comp g f ↦ comp (L(α) g) (L(α) f)`

This respects the quotient because naturality ensures:

- Identity witnesses map to identity witnesses
- Composition witnesses map to composition witnesses
- Category axioms are preserved structurally

### The adjunction L ⊣ Φ

**Claim**: L is left adjoint to Φ.

```text
Hom_Cat(L(F), C) ≅ Hom_{[J,Type]}(F, Φ(C))
```

**Forward direction**: Given functor G : L(F) → C, construct α : F → Φ(C):

- α_Obj = G.obj
- α_Mor(m) = ⟨G.obj(dom m), G.obj(cod m), G.map([var m])⟩
- α_Id, α_Comp defined similarly

**Backward direction**: Given α : F → Φ(C), construct functor G : L(F) → C:

- G.obj = α_Obj
- G.map defined via `counitEval`:
  - `var m ↦ α_Mor(m).hom`
  - `id a ↦ id (α_Obj a)`
  - `comp g f ↦ (G.map g) ≫ (G.map f)`

This respects the quotient because α preserves identity/composition structure.

### Round-trip properties

**Counit ε_C : L(Φ(C)) → C is an isomorphism**:

For an actual category C:

- L(Φ(C)) has the same objects as C
- A free morphism in the quotient corresponds to a composite in C
- The `counitEval` function evaluates free morphisms to actual morphisms
- The composition data in Φ(C) identifies every free morphism with its
  evaluated composite
- So L(Φ(C)) ≅ C (via `roundtripEmbed` and `counitEval`)

**Unit η_F : F → Φ(L(F)) is not generally an isomorphism**:

- η_Obj is the identity on F(Obj)
- η_Mor sends m to the equivalence class `[var m]` via `unitComponent`

This fails to be an isomorphism when:

- Multiple identity witnesses collapse to one (forced equal by the quotient)
- Multiple composition witnesses collapse to one
- Different morphisms in F(Mor) become equal in L(F) due to the quotient

### Characterization via the adjunction

The adjunction characterizes Cat as a reflective subcategory:

- Every copresheaf F has a "best approximation" as a category: L(F)
- A copresheaf F is (equivalent to) an actual category iff η_F is an isomorphism
- The conditions in "Characterizing the Image" are precisely those ensuring
  η_F is an isomorphism

This is analogous to:

- Groups as a reflective subcategory of monoids (reflection adds inverses)
- Abelian groups as a reflective subcategory of groups (reflection quotients
  by commutator)
- Complete metric spaces as a reflective subcategory of metric spaces
  (reflection is Cauchy completion)

## Identity as a Natural Transformation

The identity operation can be understood as a natural transformation of
copresheaves on W. Define the "object quiver" O : W → Type by:

- O(0) = Obj (morphisms are just objects)
- O(1) = Obj (objects are objects)
- O(s) = O(t) = id_Obj

This is the pullback of the terminal quiver along the constant map.

Then the identity operation is a natural transformation η : O ⇒ F where:

- η_1 : Obj → Obj is the identity
- η_0 : Obj → MorType is the identity assignment

The naturality squares encode id_src and id_tgt:

- F(s) ∘ η_0 = η_1 ∘ O(s) gives src(id_a) = a
- F(t) ∘ η_0 = η_1 ∘ O(t) gives tgt(id_a) = a

## Why Cat is Not a Topos

Copresheaf categories [J, Type] are always toposes (they have subobject
classifiers, are cartesian closed, have all limits and colimits, etc.).

Cat is not a topos because:

1. The conditions cutting out Cat from [J, Type] involve **equations**
   (equalizers), not just limits
2. These equations "collapse" the free structure of the copresheaf category
3. Specifically, Cat lacks a subobject classifier

However, Cat is **locally finitely presentable** and can be characterized as
the category of models of a finite limit sketch, which is a well-behaved
class of categories.

## Implementation Design Decisions

This section documents design decisions for the Lean implementation in
`GebLean/CatJudgmentAdjunction.lean`.

### Copresheaf representation

We use `CategoryJudgments.FunctorData` and `CategoryJudgments.NatTransData`
for internal representations. These provide a minimal specification of what's
required to specify a copresheaf or natural transformation, trimming redundant
equalities and minimizing the data we need to provide.

When we need to import properties from mathlib (such as universal properties
of presheaves or topos structure), we use the isomorphism of categories
`functorDataIsoCat` to exchange between `CategoryJudgments.FunctorData` and
mathlib's functor category.

### Free category (FreeMor) representation

Rather than using paths (linear lists of composable morphisms), we represent
free morphisms as binary trees using the `FreeMor` inductive type:

```lean
inductive FreeMor (Q : OverQuiver) : Q.Obj → Q.Obj → Type where
  | var (f : Q.MorType) : FreeMor Q (Q.src f) (Q.tgt f)
  | id (a : Q.Obj) : FreeMor Q a a
  | comp {a b c : Q.Obj} (g : FreeMor Q b c) (f : FreeMor Q a b) : FreeMor Q a c
```

This representation has properties:

- `var f` injects a base morphism from the quiver
- `id a` is the identity at object a
- `comp g f` is composition (f first, then g)

The tree representation avoids circular dependencies in congruence proofs that
arise with the path-based approach. When proving that the equivalence relation
respects composition (congruence), binary trees allow straightforward structural
induction without having to reason about list concatenation.

### Quotient structure

The quotient is structured via `CategoryQuotientData`:

```lean
structure CategoryQuotientData where
  quiver : OverQuiver
  IdWitness : Type
  idObj : IdWitness → quiver.Obj
  idMor : IdWitness → quiver.MorType
  id_src : ∀ (i : IdWitness), quiver.src (idMor i) = idObj i
  id_tgt : ∀ (i : IdWitness), quiver.tgt (idMor i) = idObj i
  CompWitness : Type
  compRight : CompWitness → quiver.MorType
  compLeft : CompWitness → quiver.MorType
  compComposite : CompWitness → quiver.MorType
  comp_match : ∀ (c : CompWitness),
    quiver.tgt (compRight c) = quiver.src (compLeft c)
  comp_dom : ∀ (c : CompWitness),
    quiver.src (compComposite c) = quiver.src (compRight c)
  comp_cod : ∀ (c : CompWitness),
    quiver.tgt (compComposite c) = quiver.tgt (compLeft c)
```

The equivalence relation `FreeMorEquiv` is generated by:

- Category axioms: `id_left`, `id_right`, `assoc`
- Identity witnesses: `var(idMor i) ~ id(idObj i)`
- Composition witnesses:
  `var(compComposite c) ~ comp(var(compLeft c), var(compRight c))`
- Congruence: if `f ~ f'` and `g ~ g'`, then `comp g f ~ comp g' f'`

The quotient type `QuotMor a b := Quotient (freeMorSetoid a b)` gives the
morphisms of the resulting category.

### Category representation

We use the Over formulation (`OverCategoryData`) for the result category L(F)
because:

- It uses equalities rather than dependent types
- This closely matches the notion of copresheaves over `CategoryJudgments`
- It provides a cleaner interface for the adjunction

### Implementation phases

Phase 1 (complete): Get the functors in place

- Embedding Φ : `OverCategoryData.toJudgmentFunctorData`
- Free morphisms: `FreeMor` inductive type
- Equivalence relation: `FreeMorEquivGen` and `FreeMorEquiv`
- Quotient category: `CategoryQuotientData.toOverCategoryData`
- Reflection L : `CategoryJudgments.FunctorData.toOverCategoryData`

Phase 2 (in progress): Functoriality

- `OverFunctorData.toJudgmentNatTrans`: Functor action on morphisms
- `FreeMor.mapQuiver`: Mapping free morphisms through quiver morphisms
- `unitComponent` and `counitEval`: Adjunction unit/counit components

Phase 3 (complete): Prove round-trip properties

- Counit isomorphism: `counitFunctorData_inv` provides the inverse
- Round-trip identities: `counit_comp_inv_eq_id` and `inv_comp_counit_eq_id`
- Uses `roundtripEquiv` equivalence between quotient and original morphisms

Phase 4 (complete): Full adjunction

- Triangle identities proven via `triangle1` and `triangle2` lemmas
- `catCopresheafMathlibAdjunction : LFunctor ⊣ PhiFunctor`
- Extended to mathlib functor categories via `catCopresheafExtAdjunction`

Phase 5 (complete): Reflectivity

- Counit is an isomorphism at the `OverFunctorData` level
- This establishes that the adjunction L ⊣ Φ is reflective
- `adjunctionCounit_isIso` provides the mathlib `IsIso` instance for the counit
- `catCopresheafCounitNatIso` gives the natural isomorphism form

## References

- `GebLean/CategoryJudgments.lean` - Definition of the CategoryJudgments
  category
- `GebLean/Utilities/OverCategoryEquiv.lean` - Over-based category structures
  and their equivalence to dependent formulations
- `GebLean/CatJudgmentAdjunction.lean` - Implementation of the adjunction

## Mathematical Context

### Related Constructions

The adjunction L ⊣ Φ relates to several constructions in the literature.

**Category presentations.** The construction of categories by generators and
relations is standard (Mac Lane, Mitchell). Given a graph G and relations R,
one forms F(G)/R where F(G) is the free category on G. The adjunction L ⊣ Φ
is a type-theoretic reformulation: the copresheaf F on CategoryJudgments
bundles the graph and relation data into a single structure, with identity
and composition witnesses as first-class components.

**Essentially algebraic theories.** The category Cat of small categories is
locally finitely presentable (Adámek-Rosický). Categories are models of a
finitary essentially algebraic theory, and Gabriel-Ulmer duality relates
such theories to their model categories. The adjunction L ⊣ Φ provides a
computational presentation of this relationship: CategoryJudgments encodes
the signature, FunctorData encodes presentations with explicit witnesses,
L constructs the semantic category, and Φ extracts the presentation.

**Nerve-realization.** The nerve-realization adjunction N ⊣ τ₁ relates
categories to simplicial sets. The nerve encodes a category as a presheaf
on the simplex category Δ, where face maps encode composition and
degeneracies encode identities. The adjunction L ⊣ Φ uses explicit judgment
types (Obj, Mor, Id, Comp) rather than positional encoding, making the
construction more directly expressible in dependent type theory.

**Computads.** Computads (Street, Batanin) generalize category presentations
to higher dimensions by treating relations as 2-cells. CategoryJudgments can
be viewed as a 1-truncated computad where the identity and composition
witnesses play the role of generating 2-cells that are then quotiented.

**Type-theoretic categories.** FunctorData corresponds to the standard
type-theoretic representation of categories: a type of objects, a dependent
type of morphisms, identity and composition operations, with equations.
The adjunction formalizes the syntax-semantics relationship between such
presentations and actual categories, connecting to categorical semantics
of dependent type theory and Categories with Families.

### Potential Applications

**Categorical programming.** FunctorData can serve as source-level
representations of categories, with L as a compiler to semantic categories
and Φ as extraction of presentations. This parallels the use of polynomial
functors for data types in systems such as Geb.

**Coherence theorems.** The counit ε : L(Φ(C)) → C provides a canonicalization
map, and the unit η : F → Φ(L(F)) provides a quotient map. The triangle
identities establish coherence conditions. This structure may be applicable
to proving coherence theorems for monoidal categories, bicategories, and
related structures.

**Higher category presentations.** CategoryJudgments can be extended with
additional judgment types for 2-cells and higher coherences, providing a
systematic approach to presenting 2-categories and (∞,1)-categories via
dependent type-theoretic signatures.

**Proof assistant infrastructure.** FunctorData is naturally type-checkable,
making it suitable as a user-facing interface for defining categories in
proof assistants. The functor L constructs the verified mathematical object
from the presentation.

**Computational category theory.** Categories can be computed via their
presentations. The quotient construction (QuotMor) provides a representation
suitable for algorithmic manipulation, potentially enabling implementation
of categorical constructions such as limits, colimits, and adjunctions on
presentations.

**Categorical databases.** Related to functorial data migration (Spivak),
schemas can be presented as copresheaves, with L giving the free category
on the schema and Φ extracting the schema from a category of instances.
