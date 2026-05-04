# Currying in `Cat` at the level of natural transformations

Let `A`, `B`, `C` be (small) categories.  Write `A × B` for the cartesian
product in `Cat`, and `[B, C]` for the functor category.

There is the usual “exponential adjunction” (currying) bijection on objects:

```text
Cat(A × B, C) ≅ Cat(A, [B, C]).
```

In fact this extends to an isomorphism of *categories*:

```text
[A × B, C] ≅ [A, [B, C]].
```

Equivalently, `Cat` is cartesian closed as a `Cat`-enriched category (or as a 2-category).

The rest of this note makes the action on natural transformations explicit.

## The curry and uncurry functors

Define two functors between functor categories:

```text
curry   : [A × B, C] → [A, [B, C]]

uncurry : [A, [B, C]] → [A × B, C].
```

### On objects

Given `F : A × B → C`, define its curried form `F^♯ : A → [B, C]` by

```text
F^♯(a)(b) := F(a, b),
F^♯(a)(g : b → b') := F(1_a, g) : F(a, b) → F(a, b').
```

and for `f : a → a'` in `A`, define the component of the induced natural transformation

```text
F^♯(f) : F^♯(a) ⇒ F^♯(a')
```

by

```text
(F^♯(f))_b := F(f, 1_b) : F(a, b) → F(a', b).
```

Naturality of `F^♯(f)` in `b` follows from functoriality of `F` in `A × B`.

Conversely, given `H : A → [B, C]`, define its uncurried form `H^♭ : A × B → C` by

```text
H^♭(a, b) := H(a)(b),
H^♭(f : a → a', g : b → b') := (H(a')(g)) ∘ (H(f))_b.
```

This is the usual “evaluation + functoriality” formula.

## The induced bijection on natural transformations

Let `F, G : A × B → C`, and let `F^♯, G^♯ : A → [B, C]` be their curried forms.

Then there is a canonical bijection of sets:

```text
Nat(F, G) ≅ Nat(F^♯, G^♯).
```

More concretely, we can define mutually inverse functions

```text
Φ : Nat(F, G) → Nat(F^♯, G^♯)
Ψ : Nat(F^♯, G^♯) → Nat(F, G).
```

### From uncurried to curried: `Φ`

Given a natural transformation `η : F ⇒ G`, define `Φ(η) : F^♯ ⇒ G^♯` as follows.

For each object `a` of `A`, the component `(Φ(η))_a` must be a natural
transformation in `[B, C]`:

```text
(Φ(η))_a : F^♯(a) ⇒ G^♯(a).
```

Define its components at each `b ∈ B` by the evident reuse of `η`:

```text
((Φ(η))_a)_b := η_(a, b) : F(a, b) → G(a, b).
```

Naturality of `((Φ(η))_a)` in `b` is exactly naturality of `η` with respect
to morphisms of the form `(1_a, g)` in `A × B`.

Naturality of `Φ(η)` in `a` is naturality of `η` with respect to morphisms
of the form `(f, 1_b)`.

### From curried to uncurried: `Ψ`

Given a natural transformation `θ : F^♯ ⇒ G^♯` (a natural transformation in
the functor category `[A, [B, C]]`), define `Ψ(θ) : F ⇒ G` by components

```text
(Ψ(θ))_(a, b) := ((θ_a)_b) : F(a, b) → G(a, b).
```

Here `θ_a : F^♯(a) ⇒ G^♯(a)` is itself a natural transformation in `[B, C]`,
so it has components `(θ_a)_b`.

Naturality of `Ψ(θ)` with respect to a general morphism
`(f, g) : (a, b) → (a', b')` in `A × B` follows by combining:

- naturality of `θ` in `a` (which compares `θ_a` and `θ_{a'}` via `f`), and
- naturality of each `θ_a` in `b` (which compares components along `g`).

## These correspondences are inverse

With the above definitions, one checks immediately that:

```text
Ψ(Φ(η)) = η
Φ(Ψ(θ)) = θ
```

because both constructions are “componentwise reindexing”:

```text
(Ψ(Φ(η)))_(a, b) = ((Φ(η))_a)_b = η_(a, b)

((Φ(Ψ(θ)))_a)_b = (Ψ(θ))_(a, b) = ((θ_a)_b).
```

So `Nat(F, G)` and `Nat(F^♯, G^♯)` are not merely equivalent but canonically bijective.

## The stronger statement: an isomorphism of functor categories

The previous section gave the induced bijection on hom-sets.  In fact,
`curry` and `uncurry` are mutually inverse functors:

```text
curry ∘ uncurry = 1_[A,[B,C]]
uncurry ∘ curry = 1_[A×B,C].
```

So there is a canonical isomorphism of categories:

```text
[A × B, C] ≅ [A, [B, C]].
```

In particular:

- Objects correspond by `F ↦ F^♯` and `H ↦ H^♭`.
- Morphisms correspond by `η ↦ Φ(η)` and `θ ↦ Ψ(θ)` as above.

## “Vice versa”: from curried forms to uncurried forms

Everything above is symmetric under exchanging `curry` with `uncurry`.

If you start with `F', G' : A → [B, C]` and write `F'^♭, G'^♭ : A × B → C`
for their uncurried forms, then the same componentwise recipe yields a
canonical bijection

```text
Nat(F', G') ≅ Nat(F'^♭, G'^♭),
```

namely:

- Given `θ : F' ⇒ G'`, define `θ^♭ : F'^♭ ⇒ G'^♭` by `(θ^♭)_(a,b) := (θ_a)_b`.
- Given `η : F'^♭ ⇒ G'^♭`, define `η^♯ : F' ⇒ G'` by `((η^♯)_a)_b := η_(a,b)`.

## 2-categorical phrasing

If you regard `Cat` as a 2-category (objects = categories, 1-cells =
functors, 2-cells = natural transformations), then for each fixed `B`
there is a 2-adjunction:

```text
(- × B) ⊣ [B, -]
```

in the 2-category `Cat`.

The "unit/counit" part at the level of 2-cells is exactly the componentwise
correspondence above, and the induced correspondence on 2-cells is
*natural in* `A`, `B`, and `C`.
