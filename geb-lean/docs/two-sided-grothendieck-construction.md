# Two-sided Grothendieck constructions

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

* `A ∈ ob A`,
* `B ∈ ob B`,
* `X ∈ ob Ψ(A, B)`.

So you can think of this as "a point of the fibre category `Ψ(A,B)`
sitting over the base point `(A,B)`".

### Morphisms

A morphism

```text
(a, b, x) : (A, B, X) → (A', B', X')
```

consists of:

* a morphism `a : A → A'` in `A`,
* a morphism `b : B → B'` in `B`,
* and a morphism

  ```text
  x : b!(X) → a*(X')
  ```

  in the category `Ψ(A, B')`.

Here:

* `b!(X)` lives in `Ψ(A, B')`, because `b! : Ψ(A, B) → Ψ(A, B')`,
* `a*(X')` also lives in `Ψ(A, B')`, because `a* : Ψ(A', B') → Ψ(A, B')`.

So the 2-cell `x` is the "comparison" between the covariant transport
along `b` and the contravariant transport along `a`.

### Composition

Given

```text
(a, b, x) : (A, B, X) → (A', B', X')
(c, d, y) : (A', B', X') → (A'', B'', X'')
```

with

* `a : A → A'`, `b : B → B'`,
* `c : A' → A''`, `d : B' → B''`,
* `x : b!(X) → a*(X')` in `Ψ(A, B')`,
* `y : d!(X') → c*(X'')` in `Ψ(A', B'')`,

the composite is

```text
(c ⋅ a, d ⋅ b, a*(y) ⋅ d!(x))
  : (A, B, X) → (A'', B'', X'')
```

where:

* `d!(x) : (d ⋅ b)!(X) → d!(a*(X'))` is obtained by functoriality of `d!`,
* `a*(y) : a*(d!(X')) → (c ⋅ a)*(X'')` is obtained by functoriality of `a*`,
* their composite is a morphism

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

* objects given by triples `(c,d,x)` with `x ∈ H(c,d)`,
* morphisms as we just described in §2: a pair `(f,g)` in the base
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
