# Categories as Copresheaves on CategoryJudgments

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

| J object | F assigns | Description |
|----------|-----------|-------------|
| Obj | Obj_C | The type of objects in C |
| Mor | Σ (a b : Obj_C), Hom(a,b) | The sigma type of all morphisms |
| Id | Obj_C | One identity witness per object |
| Comp | { (f,g) \| tgt(f) = src(g) } | Composable pairs |

### Morphism assignments

| J morphism | F assigns | Description |
|------------|-----------|-------------|
| dom | src | First projection of sigma |
| cod | tgt | Second index of sigma |
| idObj | id_Obj | Identity on objects |
| idMor | a ↦ ⟨a, a, id_a⟩ | Identity morphism assignment |
| left | (f,g) ↦ g | Second morphism of pair |
| right | (f,g) ↦ f | First morphism of pair |
| composite | (f,g) ↦ f ≫ g | Actual composition |
| intermediate | (f,g) ↦ tgt(f) | Shared object |
| compositeDom | (f,g) ↦ src(f) | Domain of composite |
| compositeCod | (f,g) ↦ tgt(g) | Codomain of composite |

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
- Morphisms a → b: paths (finite lists of composable morphisms from a to b)
- Identity at a: the empty path []
- Composition: path concatenation

The free category has identity and associativity laws automatically.

#### Step 3: Quotient by identity and composition relations

Define an equivalence relation on morphisms of Free(Q_F) generated by:

1. **Identity relations**: For each i ∈ F(Id), identify:
   - The length-1 path [F(idMor)(i)]
   - The empty path at F(idObj)(i)

2. **Composition relations**: For each c ∈ F(Comp), identify:
   - The length-2 path [F(right)(c), F(left)(c)]
   - The length-1 path [F(composite)(c)]

The category L(F) = Free(Q_F) / ~ is the quotient by the equivalence relation
generated by these two families.

### Category laws are automatic

Note that category laws do not need to be explicitly imposed;
they follow automatically from the free category's structure:

**Associativity**: In Free(Q_F), composition is path concatenation:

```text
(f ≫ g) ≫ h = ([f] ++ [g]) ++ [h] = [f, g, h] = [f] ++ ([g] ++ [h]) = f ≫ (g ≫ h)
```

Path concatenation is associative, and the quotient preserves this.

**Left identity**: For f : a → b, if i witnesses identity at a:

- [F(idMor)(i)] ~ [] (by identity relation)
- So [F(idMor)(i), f] ~ [f] (concatenation with empty path)

**Right identity**: Similarly for right identity.

**Associativity of declared composites**: If we have composition witnesses:

- c₁ witnessing f ≫ g = h
- c₂ witnessing g ≫ k = m
- c₃ witnessing h ≫ k = n
- c₄ witnessing f ≫ m = p

Then in the quotient:

```text
[f, g, k] ~ [h, k] (by c₁) ~ [n] (by c₃)
[f, g, k] ~ [f, m] (by c₂) ~ [p] (by c₄)
```

So [n] ~ [p], and the associativity equation n = p is forced by the quotient.

### Functoriality

Given a natural transformation α : F → G between copresheaves, we get a
functor L(α) : L(F) → L(G):

- On objects: α_Obj : F(Obj) → G(Obj)
- On morphisms: map path [m₁, ..., mₙ] to [α_Mor(m₁), ..., α_Mor(mₙ)]

This respects the quotient because naturality ensures:

- Identity witnesses map to identity witnesses
- Composition witnesses map to composition witnesses

### The adjunction L ⊣ Φ

**Claim**: L is left adjoint to Φ.

```text
Hom_Cat(L(F), C) ≅ Hom_{[J,Type]}(F, Φ(C))
```

**Forward direction**: Given functor G : L(F) → C, construct α : F → Φ(C):

- α_Obj = G.obj
- α_Mor(m) = ⟨G.obj(dom m), G.obj(cod m), G.map([m])⟩
- α_Id, α_Comp defined similarly

**Backward direction**: Given α : F → Φ(C), construct functor G : L(F) → C:

- G.obj = α_Obj
- G.map([m₁, ..., mₙ]) = α_Mor(m₁).hom ≫ ... ≫ α_Mor(mₙ).hom

This respects the quotient because α preserves identity/composition structure.

### Round-trip properties

**Counit ε_C : L(Φ(C)) → C is an isomorphism**:

For an actual category C:

- L(Φ(C)) has the same objects as C
- A path in the bundled morphism type corresponds to a composite in C
- The composition data in Φ(C) identifies every path with its composite
- So L(Φ(C)) ≅ C

**Unit η_F : F → Φ(L(F)) is not generally an isomorphism**:

- η_Obj is the identity on F(Obj)
- η_Mor sends m to the length-1 path [m]

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

## References

- `GebLean/CategoryJudgments.lean` - Definition of the CategoryJudgments
  category
- `GebLean/Utilities/OverCategoryEquiv.lean` - Over-based category structures
  and their equivalence to dependent formulations
