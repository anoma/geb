# Universal properties, categories of elements, and comma categories

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Universal properties via categories of elements](#universal-properties-via-categories-of-elements)
  - [Representability as a universal property](#representability-as-a-universal-property)
  - [The category of elements](#the-category-of-elements)
  - [Representability <=> existence of an initial/terminal element-object](#representability--existence-of-an-initialterminal-element-object)
- [Universal morphisms, comma categories, and categories of elements](#universal-morphisms-comma-categories-and-categories-of-elements)
  - [Universal morphisms as initial/terminal objects in comma categories](#universal-morphisms-as-initialterminal-objects-in-comma-categories)
  - [`(X down F)` is a category of elements of a copresheaf](#x-down-f-is-a-category-of-elements-of-a-copresheaf)
  - [`(F down X)` is a category of elements of a presheaf](#f-down-x-is-a-category-of-elements-of-a-presheaf)
  - [Summary in one line](#summary-in-one-line)
- [Mathlib references](#mathlib-references)
  - [Category of elements](#category-of-elements)
  - [Comma categories and structured arrows](#comma-categories-and-structured-arrows)
  - [Representable functors and the Yoneda lemma](#representable-functors-and-the-yoneda-lemma)
  - [Initial and terminal objects](#initial-and-terminal-objects)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This note records two closely related “universality patterns”:

1. **Universal properties as representability**, detected by
   **initial/terminal objects in categories of elements**.
2. **Universal morphisms** (universal arrows) presented as
   **initial/terminal objects in comma categories**, and the fact that
   those comma categories are (canonically) **categories of elements**
   of certain (co)presheaves.

Throughout, assume categories are locally small so that hom-sets are honest sets.

---

## Universal properties via categories of elements

### Representability as a universal property

A common way to package a universal property is:

- pick a functor `F : C → Set` (covariant) or `F : Cᵒᵖ → Set` (contravariant),
- say that an object `c ∈ C` "has the universal property" when `F` is
  **represented** by `c`, i.e. when there is a natural isomorphism

  - covariant: `C(c, -) ≅ F`, or
  - contravariant: `C(-, c) ≅ F`.

Riehl explicitly emphasizes that universal properties are often expressed
as representability statements, and that these are closely related to
initial/terminal objects.

### The category of elements

For a covariant functor `F : C → Set`, its **category of elements**
(Riehl writes `∫F`) is:

- objects: pairs `(c, x)` with `c ∈ C` and `x ∈ F(c)`,
- morphisms `(c, x) → (d, y)`: arrows `f : c → d` in `C` such that `F(f)(x) = y`.

For a presheaf `P : Cᵒᵖ → Set`, the category of elements is defined similarly:

- objects: `(c, x)` with `x ∈ P(c)`,
- morphisms `(c, x) → (d, y)`: arrows `f : c → d` in `C` such that
  `P(f)(y) = x` (note the variance reversal).

Riehl notes how taking opposites relates "category of elements of a
representable" to slice/coslice-like constructions, which is a useful
sanity check for the variance bookkeeping.

### Representability <=> existence of an initial/terminal element-object

A theorem relating representablility to categories of elements
(Riehl, Prop. 2.4.4) is:

- For `F : C → Set`, the functor `F` is representable **iff** its category
  of elements `∫F` has an **initial object**.
- Concretely, an initial object `(c, u)` means:

  - for every `(d, y)` there exists a unique `f : c → d` with `F(f)(u) = y`.

  This condition is exactly what makes the Yoneda-transpose map
  `C(c, d) → F(d)` bijective for each `d`, hence gives a natural
  isomorphism `C(c, -) ≅ F`.

Dually, for a presheaf `P : Cᵒᵖ → Set`:

- `P` is representable **iff** `∫P` has a **terminal object**.

To see the duality: view `P` as a covariant functor from `Cᵒᵖ` to `Set`.
By the covariant theorem, `P` is representable iff its covariant category
of elements (call it `∫ᶜᵒᵛP`) has an initial object. But the standard
(contravariant) category of elements `∫P` for a presheaf is defined as
the opposite of this covariant construction: `∫P = (∫ᶜᵒᵛP)ᵒᵖ`. Taking
opposites swaps initial and terminal objects, so `P` is representable iff
`∫P` has a terminal object.

Finally, Riehl explicitly frames this as a general “universality template”:

> the universal object is either initial or terminal in the appropriate
> category, and this category frequently turns out to be a category of
> elements.

---

## Universal morphisms, comma categories, and categories of elements

### Universal morphisms as initial/terminal objects in comma categories

Let `F : C → D` and fix an object `X ∈ D`.

Two standard comma categories are:

- `(X ↓ F)`:

  - objects: pairs `(c, u : X → F(c))`,
  - morphisms `(c, u) → (c', u')`: arrows `g : c → c'` in `C` such that
    `F(g) ∘ u = u'`.

- `(F ↓ X)`:

  - objects: pairs `(c, v : F(c) → X)`,
  - morphisms `(c, v) → (c', v')`: arrows `g : c → c'` in `C` such that
    `v = v' ∘ F(g)`.

A **universal morphism from `X` to `F`** is exactly an **initial object**
in `(X ↓ F)`, and a **universal morphism from `F` to `X`** is exactly a
**terminal object** in `(F ↓ X)`. ([Wikipedia][1])

### `(X down F)` is a category of elements of a copresheaf

Define a copresheaf (covariant Set-valued functor)

```text
H_X : C → Set
H_X(c) = D(X, F(c))
H_X(g : c → c') sends (u : X → F(c)) to F(g) ∘ u : X → F(c')
```

Now form its category of elements `∫H_X`.

- An object of `∫H_X` is a pair `(c, u)` with `u ∈ H_X(c)`, i.e. exactly
  `(c, u : X → F(c))`.
- A morphism `(c, u) → (c', u')` in `∫H_X` is an arrow `g : c → c'` in `C`
  such that

```text
H_X(g)(u) = u'
```

i.e.

```text
F(g) ∘ u = u'
```

But this is precisely the definition of a morphism in the comma category `(X ↓ F)`.

So there is an isomorphism of categories

```text
(X ↓ F) ≅ ∫(c ↦ D(X, F(c))).
```

Under this identification:

- an initial object in `(X ↓ F)` is exactly an initial object in that
  category of elements,
- i.e. a **universal arrow from `X` to `F`** can be viewed as an
  **initial element-object** of the copresheaf `c ↦ D(X, F(c))`.
  ([Wikipedia][1])

### `(F down X)` is a category of elements of a presheaf

Define a presheaf (contravariant Set-valued functor)

```text
K_X : Cᵒᵖ → Set
K_X(c) = D(F(c), X)
K_X(g : c → c') sends (v : F(c') → X) to v ∘ F(g) : F(c) → X
```

Now form `∫K_X`.

- An object is `(c, v)` with `v ∈ D(F(c), X)`, i.e. exactly `(c, v : F(c) → X)`.
- A morphism `(c, v) → (c', v')` is `g : c → c'` in `C` such that

```text
K_X(g)(v') = v
```

i.e.

```text
v' ∘ F(g) = v
```

which is exactly the defining commutativity condition for morphisms in `(F ↓ X)`.

Hence

```text
(F ↓ X) ≅ ∫(c ↦ D(F(c), X)).
```

Under this identification:

- a terminal object in `(F ↓ X)` is exactly a terminal object in this
  category of elements,
- i.e. a **universal arrow from `F` to `X`** can be viewed as a
  **terminal element-object** of the presheaf `c ↦ D(F(c), X)`.
  ([Wikipedia][1])

---

### Summary in one line

Universal arrows are (co)representability problems for hom-functors:

- `(X ↓ F)` is the category of elements of the **copresheaf** `c ↦ D(X, F(c))`,
- `(F ↓ X)` is the category of elements of the **presheaf** `c ↦ D(F(c), X)`,

so universal morphisms are just initial/terminal objects in those
categories of elements.

[1]: https://en.wikipedia.org/wiki/Universal_property "Universal property - Wikipedia"

---

## Mathlib references

The following mathlib4 modules formalize the concepts discussed above:

### Category of elements

- [Mathlib.CategoryTheory.Elements][2]: Defines the category of elements
  `F.Elements` for a functor `F : C ⥤ Type`. Objects are pairs `(c, x)`
  with `x ∈ F(c)`, and morphisms are arrows in `C` respecting the elements.
  Includes the forgetful functor `π : F.Elements → C`.

- [Mathlib.CategoryTheory.Grothendieck][3]: The general Grothendieck
  construction for `F : C ⥤ Cat`, of which the category of elements is
  a special case (when the target is `Type` viewed as a discrete category).

### Comma categories and structured arrows

- [Mathlib.CategoryTheory.Comma.Basic][4]: Defines the comma category
  `Comma L R` for functors `L : A ⥤ T` and `R : B ⥤ T`. Objects are
  triples `(a, b, f : L(a) → R(b))`.

- [Mathlib.CategoryTheory.Comma.StructuredArrow][5]: Defines
  `StructuredArrow S T` (the category `(S ↓ T)` in the document's notation)
  and `CostructuredArrow S T` (the category `(S ↓ T)` with arrows reversed).
  The `IsUniversal` predicate captures when a structured arrow is an
  initial object.

### Representable functors and the Yoneda lemma

- [Mathlib.CategoryTheory.Yoneda][6]: The Yoneda embedding `yoneda : C ⥤ Cᵒᵖ ⥤ Type`
  and `coyoneda : Cᵒᵖ ⥤ C ⥤ Type`. Defines `RepresentableBy` and
  `CorepresentableBy` structures expressing when a functor is (co)represented
  by an object.

- [Mathlib.CategoryTheory.Limits.Presheaf][7]: The density theorem showing
  every presheaf is a colimit of representables. Uses the category of
  elements to express this via `functorToRepresentables`.

### Initial and terminal objects

- [Mathlib.CategoryTheory.Limits.Shapes.Terminal][8]: Defines initial and
  terminal objects, including `IsInitial` and `IsTerminal` predicates and
  the `initial.to` morphism from an initial object.

[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Elements.html "Mathlib.CategoryTheory.Elements"
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Grothendieck.html "Mathlib.CategoryTheory.Grothendieck"
[4]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Basic.html "Mathlib.CategoryTheory.Comma.Basic"
[5]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.html "Mathlib.CategoryTheory.Comma.StructuredArrow"
[6]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Yoneda.html "Mathlib.CategoryTheory.Yoneda"
[7]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Presheaf.html "Mathlib.CategoryTheory.Limits.Presheaf"
[8]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Terminal.html "Mathlib.CategoryTheory.Limits.Shapes.Terminal"
