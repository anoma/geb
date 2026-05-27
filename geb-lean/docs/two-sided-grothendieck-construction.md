# Two-sided Grothendieck constructions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Lucyshyn-Wright’s explicit two-sided Grothendieck construction](#lucyshyn-wrights-explicit-two-sided-grothendieck-construction)
  - [Objects](#objects)
  - [Morphisms](#morphisms)
  - [Composition](#composition)
- [Relation to Stefanich’s “cartesian then cocartesian” composite](#relation-to-stefanichs-cartesian-then-cocartesian-composite)
- [Code References](#code-references)
  - [Grothendieck Construction](#grothendieck-construction)
  - [Product Categories and Opposite Conventions](#product-categories-and-opposite-conventions)
  - [Lax and Oplax Natural Transformations](#lax-and-oplax-natural-transformations)
  - [Implementation Strategy for Two-Sided Construction](#implementation-strategy-for-two-sided-construction)
  - [Relation to Connected Grothendieck](#relation-to-connected-grothendieck)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Lucyshyn-Wright, in *Bifold Algebras and Commutants*, Def. 7.1,
spells out a **two-sided Grothendieck construction** for a functor
`Ψ : Aᵒᵖ × B → Cat`.

---

## Lucyshyn-Wright’s explicit two-sided Grothendieck construction

Fix categories `A`, `B` and a functor

```text
Ψ : Aᵒᵖ × B → Cat.
```

For each morphism `a : A → A'` in `A` and object `B ∈ B`, Lucyshyn-Wright writes

```text
a* = Ψ(a, B) : Ψ(A', B) → Ψ(A, B)
```

(the "pullback" along `a` in the first, contravariant argument), and for
each `b : B → B'` in `B` and object `A ∈ A` he writes

```text
b! = Ψ(A, b) : Ψ(A, B) → Ψ(A, B')
```

(the “pushforward” along `b` in the second, covariant argument).

Then he defines a category

```text
TwoSided(A, B, Ψ)
```

as follows.

### Objects

An object is a triple

```text
(A, B, X)
```

where

- `A ∈ ob A`,
- `B ∈ ob B`,
- `X ∈ ob Ψ(A, B)`.

So you can think of this as "a point of the fibre category `Ψ(A,B)`
sitting over the base point `(A,B)`".

### Morphisms

A morphism

```text
(a, b, x) : (A, B, X) → (A', B', X')
```

consists of:

- a morphism `a : A → A'` in `A`,
- a morphism `b : B → B'` in `B`,
- and a morphism

  ```text
  x : b!(X) → a*(X')
  ```

  in the category `Ψ(A, B')`.

Here:

- `b!(X)` lives in `Ψ(A, B')`, because `b! : Ψ(A, B) → Ψ(A, B')`,
- `a*(X')` also lives in `Ψ(A, B')`, because `a* : Ψ(A', B') → Ψ(A, B')`.

So the 2-cell `x` is the "comparison" between the covariant transport
along `b` and the contravariant transport along `a`.

### Composition

Given

```text
(a, b, x) : (A, B, X) → (A', B', X')
(c, d, y) : (A', B', X') → (A'', B'', X'')
```

with

- `a : A → A'`, `b : B → B'`,
- `c : A' → A''`, `d : B' → B''`,
- `x : b!(X) → a*(X')` in `Ψ(A, B')`,
- `y : d!(X') → c*(X'')` in `Ψ(A', B'')`,

the composite is

```text
(c ⋅ a, d ⋅ b, a*(y) ⋅ d!(x))
  : (A, B, X) → (A'', B'', X'')
```

where:

- `d!(x) : (d ⋅ b)!(X) → d!(a*(X'))` is obtained by functoriality of `d!`,
- `a*(y) : a*(d!(X')) → (c ⋅ a)*(X'')` is obtained by functoriality of `a*`,
- their composite is a morphism

  ```text
  (d ⋅ b)!(X) → (c ⋅ a)*(X'')
  ```

  in the fibre `Ψ(A, B'')`, as required.

There are evident projection functors

```text
P : TwoSided(A, B, Ψ) → A,
Q : TwoSided(A, B, Ψ) → B,
```

sending `(A,B,X)` to `A` and `B` respectively; these make a split
two-sided fibration in Street's sense.

---

## Relation to Stefanich’s “cartesian then cocartesian” composite

Stefanich defines his “bilax colimit”

```text
R_{C×Dᵒᵖ} H
```

as the weighted colimit of `H : C×Dᵒᵖ → Cat` by the weight
`C_{-/} × D_{/-}`, and then notes that this is equivalent to first doing
a cocartesian Grothendieck construction in one variable and then a
cartesian one in the other. ([arXiv][1])

Unwinding that composite:

1. Regard `H` as a functor

   ```text
   H̃ : C → Fun(Dᵒᵖ, Cat)
   ```

   by currying.

2. Apply the **cocartesian Grothendieck construction** in the
   `Dᵒᵖ`-variable to get a cocartesian fibration over `D` whose objects
   look like `(d, x)` with `x ∈ H(c, d)`, for varying `c`. (This is the
   ordinary op-Grothendieck construction in the second variable.)

3. Now apply the **cartesian Grothendieck construction** in the
   `C`-variable to `H̃`, which adds the `c` coordinate and the
   appropriate cartesian lifts in `C`.

If you chase through those two single-variable Grothendieck
constructions, the resulting "total category" over `C×D` has:

- objects given by triples `(c,d,x)` with `x ∈ H(c,d)`,
- morphisms as we just described in §2: a pair `(f,g)` in the base
  together with a fibre morphism comparing the cocartesian transport
  along `f` and the cartesian transport along `g`.

That is exactly the same data as in the Lucyshyn-Wright two-sided
Grothendieck construction (up to the trivial symmetry between `C×Dᵒᵖ`
and `Dᵒᵖ×C`), so you can safely take the explicit formula above as
*the* concrete description of Stefanich's two-sided Grothendieck
construction in terms of objects and morphisms.

If you like a slogan:

```text
Two-sided Grothendieck of H : C × Dᵒᵖ → Cat
  has objects (c, d, x ∈ H(c,d))
  and morphisms (f, g, 2-cell comparing f_! and g^* acting on x, x').
```

where `f_!` is the cocartesian (lax) action in the `C`-coordinate and
`g*` is the cartesian (oplax) action in the `D`-coordinate.

[1]: https://arxiv.org/pdf/2011.03027 "arXiv:2011.03027v1 [math.AT] 5 Nov 2020"

---

## Code References

The following references link the mathematical concepts in this document to
their implementations in Lean code.

### Grothendieck Construction

- **Mathlib definition**: `CategoryTheory.Grothendieck` for covariant
  `F : C ⥤ Cat` in
  [Mathlib.CategoryTheory.Grothendieck](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Grothendieck.html)
- **Project extensions**: `GebLean/Utilities/Grothendieck.lean`
  - `GrothendieckContra'`: Contravariant Grothendieck for `F' : Cᵒᵖ' ⥤ Cat`
    (lines 1500-1628)
  - `grothendieckContraIso`: Isomorphism between mathlib's covariant form
    (with opposite) and our contravariant form (lines 1886-1900)
  - `Grothendieck.pre`: Precomposition with functors (lines 2643-2674)
  - `Grothendieck.map`: Functoriality on natural transformations
    (lines 2308-2333)

### Product Categories and Opposite Conventions

- **Project definitions**: `GebLean/Utilities/Profunctors.lean`
  - `opProd C D := Cᵒᵖ × D`: The standard profunctor domain
  - `opProdEquiv`: Equivalence between mathlib `ᵒᵖ` and project `ᵒᵖ'`
    (lines 35-37)
  - `opProdSymSelfDual`: Self-duality `(Cᵒᵖ × C)ᵒᵖ ≌ (Cᵒᵖ × C)` (lines 63-69)

### Lax and Oplax Natural Transformations

The two-sided construction involves both lax (cocartesian) and oplax
(cartesian) structure. These are formalized in `GebLean/Utilities/Grothendieck.lean`:

- `LaxNatTransData` (lines 5064-5201): Data for lax natural transformations
  between functors `C ⥤ Cat`, including:
  - `laxApp`: Component functors
  - `laxNat`: Naturality with 2-cells going the "lax" direction
- `OplaxNatTransData` (lines 5588-5742): Dual structure for oplax
  transformations
- `LaxNatTransData.toFunctor`: Converts lax nat trans to functor between
  Grothendieck categories (lines 5205-5232)
- `OplaxNatTransData.toFunctor`: Converts oplax nat trans to functor between
  contravariant Grothendieck categories (lines 5810-5846)

### Implementation Strategy for Two-Sided Construction

Two potential ways to implement `TwoSided(A, B, Ψ)` for `Ψ : Aᵒᵖ × B ⥤ Cat`:

1. **1 - Direct definition**:
   - Define objects as sigma type: `Σ (a : A) (b : B), Ψ.obj (a, b)`
   - Define morphisms with fiber morphism in `Ψ.obj (a, b')`
   - Use `eqToHom` for functoriality coherence

2. **2 - Iterated Grothendieck**:
   - First apply contravariant Grothendieck in `A`:
     `GrothendieckContra' (curry Ψ : Aᵒᵖ' ⥤ (B ⥤ Cat))`
   - Then apply covariant Grothendieck in `B` to fibers
   - Use `Grothendieck.pre` to compose

Required infrastructure:

- `Functor.curry` / `Functor.uncurry` for product category functors
- `GrothendieckContra'.FunctorFromData` for universal property
- The commutation `a*(d!(X)) = d!(a*(X))` follows from `Ψ` being a functor
  on the product category

### Relation to Connected Grothendieck

The connected Grothendieck construction (see `twisted-grothendieck-construction.md`)
generalizes the two-sided construction by:

- Using `Tw(C)` as the indexing category instead of `Aᵒᵖ × B`
- Projecting to `Arr(C)` instead of `A × B`
- Allowing dependence on the arrow itself, not just its endpoints

The twisted-arrow to Grothendieck equivalence `twArrEquivGrothendieckUnder`
`: TwistedArrow' C ≌ Grothendieck (Under.mapFunctor C)` in
`TwistedArrow.lean` (lines 1008-1037) shows a concrete case of this
relationship.
