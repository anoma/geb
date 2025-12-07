# The Connected Grothendieck Construction: Functors `Tw(C) → Cat` Landing in `Cat/Arr(C)`

This note summarizes a functorial construction that assigns to every functor
`F : Tw(C) → Cat` a category `E(F)` equipped with a functor `E(F) → Arr(C)`.
This defines a functor

```text
E : Fun(Tw(C), Cat) → Cat/Arr(C).
```

The construction is an "enhanced" variant of the two-sided Grothendieck
construction in which objects and morphisms carry additional arrow-category
structure.

---

## 1. Preliminaries

Let `C` be a category. We define two associated categories.

### 1.1 The arrow category `Arr(C)`

* **Objects:** Morphisms `f : a → b` in `C`.
* **Morphisms:** A morphism `(g, h) : f → f'` between arrows
  `f : a → b` and `f' : a' → b'` is a commutative square

```text
a  ──g──▶  a'
│         │
f         f'
▼         ▼
b  ──h──▶  b'
```

that is, a pair of arrows `g : a → a'` and `h : b → b'` satisfying

```text
h ∘ f = f' ∘ g.
```

### 1.2 The twisted-arrow category `Tw(C)`

* **Objects:** Morphisms `f : a → b` in `C`.
* **Morphisms:** A morphism `(u, v) : f → f'` for arrows
  `f : a → b` and `f' : a' → b'` consists of `u : a' → a` and `v : b → b'` such that

```text
f' = v ∘ f ∘ u.
```

Each such morphism determines a functorial reindexing operation when a
functor `F : Tw(C) → Cat` is given.

---

## 2. Input Data: A Functor `F : Tw(C) → Cat`

Given `F`, denote the category assigned to an arrow `f : a → b` by `F(f)`.

Given a twisted-arrow morphism `(u, v) : f → f'`, write

```text
F(u, v) : F(f) → F(f').
```

This data is required to satisfy the usual functoriality conditions.

---

## 3. Output: A Category `E(F)` Over `Arr(C)`

We now define a category `E(F)` and a functor

```text
π_F : E(F) → Arr(C).
```

---

## 4. Objects of `E(F)`

An object of `E(F)` is a pair

```text
(f : a → b, e)
```

where

* `f : a → b` is an arrow of `C`,
* `e` is an object of the category `F(f)`.

The projection sends

```text
π_F(f, e) = f.
```

---

## 5. Morphisms in `E(F)`

Let `(f : a → b, e)` and `(f' : a' → b', e')` be objects of `E(F)`.

A **morphism** in `E(F)` from `(f, e)` to `(f', e')` consists of:

1. a morphism `(g, h) : f → f'` in `Arr(C)`, that is

   ```text
   h ∘ f = f' ∘ g,
   ```

2. **together with a fibre morphism**

   ```text
   φ : F(idₐ, h)(e) → F(g, id_{b'})(e')
   ```

   in the category `F(w)`, where

   ```text
   w := h ∘ f = f' ∘ g : a → b'.
   ```

To unpack this:

* The pair `(idₐ, h)` is a Tw(C) morphism `f → w`, hence induces a functor
  `F(idₐ, h) : F(f) → F(w)`.
* The pair `(g, id_{b'})` is a Tw(C) morphism `f' → w`, hence induces a functor
  `F(g, id_{b'}) : F(f') → F(w)`.

Thus both `F(idₐ, h)(e)` and `F(g, id_{b'})(e')` lie in the **same** category `F(w)`,
and the component `φ` is a morphism in that category.

The projection sends

```text
π_F(g, h, φ) = (g, h) : f → f'.
```

---

## 6. Identity Morphisms

For an object `(f : a → b, e)`:

* the identity square in `Arr(C)` is `(idₐ, id_b)`,
* the composite arrow is `f`,
* and the Tw(C) morphisms `(idₐ, id_b) : f → f` act as the identity on `F(f)`.

Therefore the identity morphism in `E(F)` is the morphism over `(idₐ, id_b)`
whose fibre component is the identity

```text
id_e : e → e
```

in `F(f)`.

---

## 7. Composition of Morphisms

Suppose we have composable morphisms in `E(F)`:

* `(g, h, φ)` from `(f : a → b, e)` to `(f' : a' → b', e')`,
* `(g', h', ψ)` from `(f' : a' → b', e')` to `(f'' : a'' → b'', e'')`.

The underlying squares in `Arr(C)` compose to give `(g' ∘ g, h' ∘ h)`.

Let the corresponding composite arrows be

```text
w₁ := h ∘ f = f' ∘ g : a → b',
w₂ := h' ∘ f' = f'' ∘ g' : a' → b'',
w₃ := h' ∘ h ∘ f = f'' ∘ g' ∘ g : a → b''.
```

There are canonical twisted-arrow morphisms

```text
(idₐ, h') : w₁ → w₃,
(g, id_{b''}) : w₂ → w₃.
```

Thus we can transport fibre morphisms:

* `φ` transported along `(idₐ, h')` becomes a morphism in `F(w₃)`,
* `ψ` transported along `(g, id_{b''})` becomes a morphism in `F(w₃)`.

The **composite fibre morphism** in `E(F)` is then defined to be

```text
F(g, id_{b''})(ψ) ∘ F(idₐ, h')(φ)
```

which is a morphism in the category `F(w₃)` from `F(idₐ, h' ∘ h)(e)` to
`F(g' ∘ g, id_{b''})(e'')`.

(Note: Using standard right-to-left composition notation where `g ∘ f` means
"first f, then g". In diagrammatic notation, this would be written
`F(idₐ, h')(φ) ; F(g, id_{b''})(ψ)`.)

Associativity follows from:

* functoriality of `F` on Tw(C),
* associativity of composition in `C`,
* associativity of composition in each fibre category `F(f)`.

Thus `E(F)` is a well-defined category and `π_F : E(F) → Arr(C)` is a functor.

---

## 8. Functoriality of the Assignment `F ↦ E(F)`

Given a natural transformation

```text
η : F ⇒ G
```

between two functors `Tw(C) → Cat`, define

```text
E(η) : E(F) → E(G)
```

by

* on objects:

```text
(f, e) ↦ (f, η_f(e)),
```

* on morphisms, given `(g, h, φ)` as above:

  * apply `η` at the twisted-arrow object `w = h ∘ f = f' ∘ g`,
  * transport via naturality to obtain a morphism in `G(w)`:

```text
η_w(F(idₐ, h)(e))
  → η_w(F(g, id_{b'})(e'))
```

which equals

```text
G(idₐ, h)(η_f(e)) → G(g, id_{b'})(η_{f'}(e'))
```

by naturality.

This defines a functor over `Arr(C)` and yields functoriality

```text
E : Fun(Tw(C), Cat) → Cat/Arr(C).
```

---

## 9. Summary

The construction above assigns to each `Cat`-valued functor on the
twisted-arrow category of `C` a category over the arrow category of `C`.

It generalizes the ordinary (one- or two-sided) Grothendieck construction by
allowing the indexing to depend not only on the source and target objects
`a, b` of an arrow `f : a → b`, but also on the arrow itself, with morphisms
defined through canonical mediating twisted-arrow morphisms.

Formally:

```text
E(F) is the category whose
  objects are (f : a → b, e ∈ F(f)),
  morphisms over (g,h) : f → f' are fibre morphisms in F(h ∘ f = f' ∘ g),
and the projection E(F) → Arr(C) is functorial in F.
```

This yields a well-defined functor

```text
E : Fun(Tw(C), Cat) → Cat/Arr(C).
```

---

## 10. Code References

The following references link the mathematical concepts in this document to
their implementations in Lean code.

### 10.1 Arrow Category

* **Mathlib definition**: `CategoryTheory.Arrow` is defined as
  `Comma (𝟭 C) (𝟭 C)` in [Mathlib.CategoryTheory.Comma.Arrow][arr]
* **Project usage**: `GebLean/Utilities/TwistedArrow.lean` imports and uses
  `Arrow` from mathlib; see also `ArrowOp' C := Arrow Cᵒᵖ'` (line 1226)
* **Self-duality**: `arrowIsoArrowOpOp' : Arrow C ≅Cat (ArrowOp' C)ᵒᵖ'`
  (lines 1301-1336 of `TwistedArrow.lean`)

### 10.2 Twisted Arrow Category

* **Mathlib definition**: `CategoryTheory.TwistedArrow` in
  [Mathlib.CategoryTheory.Comma.StructuredArrow.Basic][tw]
* **Project definitions**: `GebLean/Utilities/TwistedArrow.lean`
  * `TwistedArrow'` (lines 48-54): Objects are arrows, morphisms are twisted
    factorizations
  * `TwistedArrowOp'` (lines 185-195): `TwistedArrow' Cᵒᵖ'`
  * `twObjMk'`, `twHomMk'`: Constructors for objects and morphisms
  * `twDomArr'`, `twCodArr'`: Extract components from twisted morphisms
* **Self-duality**:
  `twistedArrowIsoTwistedArrowOp' : TwistedArrow' C ≅Cat TwistedArrowOp' C`
  (lines 751-781)
* **Grothendieck equivalence**:
  `twArrEquivGrothendieckUnder : TwistedArrow' C ≌ Grothendieck ...`
  (lines 1008-1037)

[arr]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Arrow.html
[tw]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.html

### 10.3 Grothendieck Construction

* **Mathlib definition**: `CategoryTheory.Grothendieck` for `F : C ⥤ Cat` in
  [Mathlib.CategoryTheory.Grothendieck](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Grothendieck.html)
* **Project extensions**: `GebLean/Utilities/Grothendieck.lean`
  * `GrothendieckContra'`: Contravariant version for `F' : Cᵒᵖ' ⥤ Cat`
  * `Grothendieck.FunctorToData`, `FunctorFromData`: Characterize functors
    to/from Grothendieck categories
  * `LaxNatTransData`, `OplaxNatTransData`: Lax/oplax natural transformations
    between Grothendieck constructions

### 10.4 Profunctors

* **Project definitions**: `GebLean/Utilities/Profunctors.lean`
  * `opProdSym C := Cᵒᵖ × C`: The standard profunctor domain
  * `hom' : opProdSym' C ⥤ Type v`: Hom functor using `ᵒᵖ'`
  * Various profunctor variants for different opposite conventions

### 10.5 Implementation Strategy

To implement this connected Grothendieck construction in the project:

1. **Define `E(F)` objects**: Pairs `(f, e)` where `f : Arrow C` and
   `e : F.obj (corresponding Tw(C) object)`

2. **Define `E(F)` morphisms**: Use `Arrow.homMk` for the base square and
   construct the fiber morphism in `F(w)` where `w` is the common diagonal

3. **Leverage existing infrastructure**:
   * Use `Grothendieck.FunctorFromData` pattern for the projection to `Arr(C)`
   * The twisted-arrow to Grothendieck equivalence `twArrEquivGrothendieckUnder`
     shows how to handle the fiber structure
   * The arrow self-duality `arrowIsoArrowOpOp'` may help with dual constructions

4. **Key lemmas needed**:
   * Composition of Tw(C) morphisms: `(u, v) ; (u', v') = (u ∘ u', v' ∘ v)`
   * Transport along Tw(C) morphisms preserves composition
