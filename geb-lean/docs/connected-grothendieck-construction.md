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
  `f : a → b` and `f' : a' → b'` consists of `u : a' → a` and
  `v : b → b'` such that

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

### 10.5 Implementation Strategy: Nested Grothendieck Construction

The connected Grothendieck construction can be implemented as a composition of
two standard Grothendieck constructions, leveraging existing mathlib
infrastructure and avoiding manual associativity proofs.

#### 10.5.1 Tw(C) as a Grothendieck Opfibration

The twisted arrow category `Tw(C)` is a Grothendieck opfibration over `C` via
the codomain functor `cod : Tw(C) → C` sending `f : a → b` to `b`.

The fiber over `b ∈ C` consists of arrows with codomain `b`:

* **Objects**: morphisms `f : a → b` in `C`
* **Morphisms** from `f : a → b` to `g : c → b`: pairs `(α, id_b)` where
  `α : c → a` satisfies `f ∘ α = g`

This is precisely `(Over b)^op`:

* In `Over b`, morphisms `f → g` are `α : a → c` with `g ∘ α = f`
* In `(Over b)^op`, morphisms `f → g` are `α : c → a` with `f ∘ α = g` ✓

#### 10.5.2 Decomposition into Two Grothendieck Constructions

Given `F : Tw(C) → Cat`, the connected Grothendieck construction `E(F)`
decomposes as:

```text
E(F) = ∫_C H

where H : C → Cat is defined by H(b) = ∫_{(Over b)^op} G_b
and G_b = ι_b ⋙ F : (Over b)^op → Cat
```

1. *Fiber inclusion functor*: For each `b ∈ C`, define the inclusion
   `ι_b : (Over b)^op → Tw(C)`:
   * On objects: `(f : a → b) ↦ f` (as a twisted arrow)
   * On morphisms: `α : f → g` in `(Over b)^op` (i.e., `α : c → a` with
     `f ∘ α = g`) maps to `(α, id_b) : f → g` in `Tw(C)`

2. *Restricted functor on each fiber*: Define `G_b = ι_b ⋙ F : (Over b)^op → Cat`.
   This restricts `F` to the fiber over `b`.

3. *Inner Grothendieck construction*: Apply the standard Grothendieck
   construction to `G_b`:
   * Objects of `∫ G_b`: pairs `(f : a → b, x)` where `x ∈ F(f)`
   * Morphisms `(f, x) → (g, y)`: `α : c → a` with `f ∘ α = g`, plus
     `φ : F(α, id_b)(x) → y`

   This captures the "horizontal" morphisms (those along the fiber).

4. *Fiber functor H : C → Cat*: Define `H : C → Cat` where:
   * `H.obj b = Cat.of (∫ G_b)`
   * For `β : b → d` in `C`, define `H.map β : ∫ G_b → ∫ G_d`:
     * On objects: `(f : a → b, x) ↦ (β ∘ f : a → d, F(id_a, β)(x))`
     * On morphisms: `(α, φ) ↦ (α, F(id, β)(φ))`

   The well-definedness of `H.map β` on morphisms follows from the identity:

   ```text
   F(α, id_d) ∘ F(id_a, β) = F(α, β) = F(id_c, β) ∘ F(α, id_b)
   ```

   Functoriality of `H` (i.e., `H(β₂ ∘ β₁) = H(β₂) ∘ H(β₁)`) follows from
   functoriality of `F`.

5. *Outer Grothendieck construction*: Apply the standard Grothendieck
   construction to `H`:
   * Objects of `∫_C H`: `(b, (f : a → b, x))` ≅ `(f : a → b, x ∈ F(f))`
   * Morphisms `(f, x) → (g, y)`:
     * `β : b → d` in `C`
     * A morphism `H(β)(f, x) → (g, y)` in `H(d)`, which is:
       * `α : c → a` with `(β ∘ f) ∘ α = g`
       * `φ : F(α, id_d)(F(id, β)(x)) → y`, i.e., `φ : F(α, β)(x) → y`

   This exactly matches the specification of `E(F)`.

#### 10.5.3 Implementation Steps in Lean

1. **Define `overOpToTwistedArrow b : (Over b)^op ⥤ TwistedArrow' C`**

   The fiber inclusion functor.

2. **Define `restrictToFiber F b = overOpToTwistedArrow b ⋙ F`**

   Restriction of `F` to the fiber over `b`.

3. **Use mathlib's `Grothendieck (restrictToFiber F b)`**

   The inner Grothendieck construction on each fiber.

4. **Define `fiberFunctor F : C ⥤ Cat`**

   Assembles the fiber Grothendieck constructions into a functor.
   Requires defining the transition functors `H(β)` for `β : b → d`.

5. **Define `ConnectedGrothendieck F = Grothendieck (fiberFunctor F)`**

   The outer Grothendieck construction.

6. **Define the projection `ConnectedGrothendieck F ⥤ Arrow C`**

   Sends `(f, x)` to `f` viewed as an arrow.

#### 10.5.4 Advantages of This Approach

* **Associativity for free**: Both Grothendieck constructions inherit
  associativity from mathlib's existing proofs.
* **Identity laws for free**: Similarly inherited from mathlib.
* **Cleaner code**: The structure of the construction is explicit in the
  types.
* **Reusable components**: The fiber inclusion and transition functors may
  be useful elsewhere.
* **Maintainability**: Less custom proof machinery to maintain.

---

## 11. The Presheaf Variant: Functors `Tw(C)^op → Cat`

The construction above uses a covariant functor `F : Tw(C) → Cat` (a copresheaf
on twisted arrows). There is a dual construction for presheaves on twisted
arrows.

### 11.1 Input Data

A **presheaf on twisted arrows** is a functor `G : Tw(C)^op → Cat`. This
assigns to each arrow `f : a → b` in `C` a category `G(f)`, with functorial
transport in the opposite direction from copresheaves.

### 11.2 Formulation via `Tw(C^op)`

The twisted arrow category `Tw(C)` is self-dual: there is an equivalence
`Tw(C^op) ≃ Tw(C)` (implemented as `twistedArrowIsoTwistedArrowOp'`). This
equivalence swaps domain and codomain.

A presheaf on `Tw(C)` (functor `Tw(C)^op → Cat`) can equivalently be viewed as:

* A presheaf on `Tw(C^op)` (functor `Tw(C^op)^op → Cat`)
* A copresheaf on `Tw(C^op)` composed with the opposite functor

This formulation is parallel to the two-sided Grothendieck construction, with
the connecting morphism in the opposite direction.

### 11.3 Objects

An object of the presheaf connected Grothendieck construction `E^op(G)` is:

```text
(f : b → a, e)
```

where `f : b → a` is an arrow in `C` (note: opposite direction from the
copresheaf case) and `e` is an object of `G(f)`.

### 11.4 Morphisms

A morphism from `(f : b → a, e)` to `(f' : b' → a', e')` consists of:

1. A commutative square:

   ```text
   b  ──g──▶  b'
   │         │
   f         f'
   ▼         ▼
   a  ──h──▶  a'
   ```

   where `g : b → b'` and `h : a → a'` satisfy `h ∘ f = f' ∘ g`.

2. A fiber morphism in `G(w)` where `w = h ∘ f = f' ∘ g`:

   ```text
   φ : G(id_b, h)(e) → G(g, id_{a'})(e')
   ```

The fiber morphism structure is the same as for copresheaves (pushforward of
source to pullback of target), with the difference being that `G` is
contravariant on `Tw(C)`.

### 11.5 Nested Grothendieck Decomposition

The presheaf construction decomposes as two nested Grothendieck constructions
with opposite variance from the copresheaf case:

```text
E^op(G) = GrothendieckContra' (fiberFunctorPresheaf G)

where fiberFunctorPresheaf G : C^op → Cat is defined by
      fiberFunctorPresheaf G b = Grothendieck (restrictToFiberPresheaf G b)
```

Compared to the copresheaf decomposition:

|Layer|Copresheaf|Presheaf|
|---|---|---|
|Outer|Grothendieck (covariant on C)|GrothendieckContra' (contravariant)|
|Inner|GrothendieckContra' (contravariant)|Grothendieck (covariant)|

### 11.6 Using Over Categories

The inner fiber for the presheaf construction can be formulated using:

* `Under b` in `C`: arrows `f : b → a` with domain `b`
* Equivalently: `Over b` in `C^op`

The equivalence `Under(c) ≃ Over(c^op)^op` allows either formulation. Using
`Over` (in `C^op`) corresponds to the standard presentation of dependent types.

### 11.7 Code Reuse

The presheaf construction can reuse existing infrastructure:

* The existing `fiberFunctor` (which uses regular `Grothendieck` for inner)
  may serve as the inner functor, since presheaf uses "covariant inner"
* The `GrothendieckContra'` construction provides the outer layer
* Transition functors and transport mechanisms parallel the copresheaf case

### 11.8 Relationship to Two-Sided Grothendieck

The two-sided Grothendieck construction for `F : C^op × D → Cat` uses:

* Covariant Grothendieck on `D` (for each `c`, apply to `F_c : D → Cat`)
* Contravariant Grothendieck on the result (to flip `C^op` to `C`)

The connected Grothendieck constructions follow the same pattern:

* Copresheaf: `F : Tw(C) → Cat` - covariant outer, contravariant inner
* Presheaf: `G : Tw(C)^op → Cat` - contravariant outer, covariant inner

The presheaf construction is the dual, with connecting morphisms in the
opposite direction, analogous to how two-sided handles the variance flip.

### 11.9 Projection Asymmetry: Arrow vs TwistedArrow

The copresheaf and presheaf constructions project to different categories:

* **Copresheaf** `F : Tw(C) → Cat` projects to `Arr(C)`
* **Presheaf** `G : Tw(C)^op → Cat` projects to `Tw(C)`

This asymmetry arises from the diagonal construction used for fiber transport.

#### 11.9.1 The Diagonal Construction

Given an Arrow morphism `(g, h) : f → f'` with commuting square
`h ∘ f = f' ∘ g`, the **diagonal** is:

```text
w = h ∘ f = f' ∘ g : a → b'
```

There are canonical TwistedArrow morphisms from the component arrows to this
composite:

```text
(id_a, h) : f → w      (component arrow f to composite w)
(g, id_{b'}) : f' → w  (component arrow f' to composite w)
```

These morphisms go FROM component arrows TO the composite diagonal.

#### 11.9.2 Fiber Transport Direction

For **covariant** `F : Tw(C) → Cat`:

```text
F(id_a, h) : F(f) → F(w)   transports INTO F(w)
F(g, id_{b'}) : F(f') → F(w)   transports INTO F(w)
```

Both fiber elements can be transported INTO the common category `F(w)`, where
they can be compared via a fiber morphism. This enables the diagonal
construction to work, and the resulting category projects to `Arr(C)`.

For **contravariant** `G : Tw(C)^op → Cat`:

```text
G(id_a, h) : G(w) → G(f)   transports OUT OF G(w)
G(g, id_{b'}) : G(w) → G(f')   transports OUT OF G(w)
```

The functors go OUT of `G(w)`, not into it. We cannot use these to transport
fiber elements into a common category for comparison.

#### 11.9.3 Presheaf Uses TwistedArrow Morphisms Directly

Since the diagonal construction fails for presheaves, the presheaf connected
Grothendieck construction uses TwistedArrow morphisms directly as the base
morphisms:

```text
Morphism from (f, e) to (f', e'):
  - twMorph : f → f' in Tw(C)
  - fiberMorph : e → G(twMorph)(e') in G(f)
```

For `twMorph : f → f'` in `Tw(C)`:

```text
G(twMorph) : G(f') → G(f)   transports e' into G(f)
```

The fiber morphism `e → G(twMorph)(e')` lives in `G(f)`, the source fiber.

This construction naturally projects to `Tw(C)`, not `Arr(C)`, because the
morphisms ARE TwistedArrow morphisms rather than Arrow morphisms mediated by
diagonals.

#### 11.9.4 Implementation Status

* `ConnectedGrothendieckContra C F` for copresheaves projects to `Arrow C`
  via `connGrothendieckContraProjection`
* `ConnectedGrothendieckPresheaf C G` for presheaves projects to
  `TwistedArrow' C` via `connGrothendieckPresheafProjection`

See `GebLean/Utilities/ConnectedGrothendieck.lean` lines 3329-3368 for detailed
documentation of this asymmetry.
