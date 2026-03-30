# FunctorData Generalization of the Grothendieck Equivalence

## Background

The equivalence `pshInternalGrothendieckEquiv` establishes:

```text
PshInternalPresheaf X  ≌  (Grothendieck (externalize X) ⥤ Type w)
```

for `X : PshInternalCat C`, where
`externalize X : Cᵒᵖ ⥤ Cat` sends each stage `c` to the
fiber category at `c`.

This document describes a generalization that replaces `Cat`
with `FunctorData(Type w)` — the category of copresheaves
on `CategoryJudgments.Obj` — using the reflective embedding
`Cat ↪ FunctorData(Type)` via `PhiFunctor`.

## CategoryJudgments.Obj as a schema for categorical structure

The category `CategoryJudgments.Obj` has four objects:

```text
obj   — the type of objects
mor   — the type of morphisms
id    — identity witnesses
comp  — composition witnesses
```

and morphisms encoding structural relationships:

```text
dom : mor → obj       (source of a morphism)
cod : mor → obj       (target of a morphism)
idMor : id → mor      (identity morphism assignment)
idObj : id → obj      (underlying object of identity)
left : comp → mor     (first morphism in a composite)
right : comp → mor    (second morphism in a composite)
composite : comp → mor (the composite morphism)
```

with conditions `h_id_endo`, `h_comp_match`,
`h_comp_dom`, `h_comp_cod` ensuring structural
compatibility (identities are endomorphisms, composable
pairs have matching target/source, composite has the
expected source and target).

A `FunctorData(Type w)` — equivalently, a copresheaf
`Obj ⥤ Type w` — assigns a type to each of these four
roles and functions between them respecting the structural
relationships.  This is the data of a "proto-category":
objects, morphisms, identities, and compositions, but
without the category axioms (associativity, identity laws).

## FunctorData-valued functors as copresheaves on a product

A functor `F : Cᵒᵖ ⥤ FunctorData(Type w)` assigns to each
stage `c : Cᵒᵖ` a proto-category `F(c)`, with restriction
maps that preserve the proto-category structure.

Via the equivalence
`FunctorData(Type w) ≅ (Obj ⥤ Type w)`:

```text
[Cᵒᵖ, FunctorData(Type w)]
  ≅ [Cᵒᵖ, [Obj, Type w]]
  ≅ [Cᵒᵖ × Obj, Type w]
```

The second step is the currying/uncurrying equivalence
for functor categories.

A FunctorData-valued functor on `Cᵒᵖ` is therefore the
same as a copresheaf on the product category
`Cᵒᵖ × Obj`.  The four components of `Obj` decompose the
copresheaf into four families varying over `c`:

```text
F(c, obj)  = type of objects at stage c
F(c, mor)  = type of morphisms at stage c
F(c, id)   = identity witnesses at stage c
F(c, comp) = composition witnesses at stage c
```

The morphisms of `Obj` connect these components
(source, target, etc.), and the morphisms of `Cᵒᵖ`
provide restriction maps between stages.

## The reflective embedding and reflection

The adjunction `LFunctor ⊣ PhiFunctor` relates
`FunctorData(Type)` and `BundledOverCategoryData`
(which is equivalent to `Cat`):

```text
LFunctor : FunctorData(Type u) → BundledOverCategoryData
PhiFunctor : BundledOverCategoryData → FunctorData(Type u)
```

`PhiFunctor` is fully faithful, making `Cat` a reflective
subcategory of `FunctorData(Type)`.  The reflection
`LFunctor` sends a proto-category to the free category on
its morphism data, quotiented by the relations from the
identity and composition structure.

This adjunction lifts pointwise to functor categories
(`CatValuedFunctor.lean`):

```text
lWhiskering Cᵒᵖ : [Cᵒᵖ, FunctorData(Type)] ⥤ [Cᵒᵖ, Cat]
phiWhiskering Cᵒᵖ : [Cᵒᵖ, Cat] ⥤ [Cᵒᵖ, FunctorData(Type)]
```

with `phiWhiskering_reflective : Reflective (phiWhiskering Cᵒᵖ)`.

## The generalized construction

Given `F : Cᵒᵖ ⥤ FunctorData(Type u)`:

1. **Reflect to Cat**: compose with `LFunctor` (and
   `overToCatFunctor` to convert
   `BundledOverCategoryData` to `Cat`) to obtain
   `reflectToCat F : Cᵒᵖ ⥤ Cat`.

2. **Apply Grothendieck**: form
   `Grothendieck (reflectToCat F)`, the total category
   whose objects are pairs `(c, x)` where `c : Cᵒᵖ` and
   `x` is an object of the reflected category at `c`.

3. **Internal presheaves**: the equivalence
   `pshInternalGrothendieckEquiv` (applied to the
   internal category corresponding to `reflectToCat F`)
   gives:

```text
PshInternalPresheaf (internalize(reflectToCat F))
  ≌ (Grothendieck (reflectToCat F) ⥤ Type w)
```

## Connection to PshInternalCat

For `X : PshInternalCat C`, the externalization
`externalize X : Cᵒᵖ ⥤ Cat` can be factored through
`FunctorData(Type w)`:

**Extract FunctorData.** At each `c : Cᵒᵖ`, the fiber
data of `X` gives a `FunctorData(Type w)`:

```text
toFunctorDataFunctor X : Cᵒᵖ ⥤ FunctorData(Type w)
```

where `(toFunctorDataFunctor X).obj c` has:

- `objC = fiberObj X c`
- `morC = fiberMor X c`
- `dom = fiberSrc X c`, `cod = fiberTgt X c`
- `idC = fiberObj X c` (one identity per object)
- `idMor = fiberId X c`
- `compC = fiberCompPairs X c`
- `left`, `right`, `composite` from the pullback
  projections and `fiberComp`

**Image of Phi.** Since `X` is an internal category
(not merely a proto-category), each fiber satisfies the
category axioms.  The FunctorData at each stage
therefore lies in the image of `PhiFunctor` —
equivalently, the reflection `L` recovers the original
category:

```text
reflectToCat (toFunctorDataFunctor X) ≅ externalize X
```

**Grothendieck compatibility.** The Grothendieck
constructions agree:

```text
Grothendieck (reflectToCat (toFunctorDataFunctor X))
  ≅ Grothendieck (externalize X) = X.groth
```

## The copresheaf-on-product perspective

Combining the copresheaf equivalence with the
Grothendieck construction:

Given `F : Cᵒᵖ ⥤ FunctorData(Type)`, equivalently a
copresheaf `F̃ : Cᵒᵖ × Obj ⥤ Type`:

- The objects of `Grothendieck(reflectToCat F)` are
  pairs `(c, x)` where `x` is an object of
  `LFunctor(F(c))`.  Since `LFunctor` quotients free
  morphisms, the objects of `LFunctor(F(c))` are the
  same as `F(c).objC = F̃(c, obj)`.

- The morphisms involve equivalence classes of free
  morphisms generated by `F(c).morC = F̃(c, mor)`,
  subject to the relations from
  `F(c).idC = F̃(c, id)` and
  `F(c).compC = F̃(c, comp)`.

The Grothendieck category of the reflected functor is
thus constructible from the four components of the
copresheaf on `Cᵒᵖ × Obj`: objects from the
`obj`-component, morphisms from the quotient of the
`mor`-component, with relations from the `id`- and
`comp`-components.

When `F` is in the image of `PhiFunctor` (i.e., when
each fiber is an actual category), the quotient is
trivial (the free morphisms are already identified by
the category axioms), and the Grothendieck construction
reduces to the standard one.

## References

### Internal to this project

- `GebLean/CategoryJudgments.lean`: `Obj`, `FunctorData`,
  `NatTransData`, `functorDataIsoCat`
- `GebLean/CatJudgmentAdjunction.lean`: `LFunctor`,
  `PhiFunctor`, `phiFunctor_reflective`,
  `catCopresheafMathlibAdjunction`
- `GebLean/CatValuedFunctor.lean`: `phiWhiskering`,
  `lWhiskering`, `phiWhiskering_reflective`
- `GebLean/PshInternalExternalize.lean`: `externalize`,
  `fiberCategory`
- `GebLean/PshInternalGrothendieck.lean`:
  `pshInternalGrothendieckEquiv`

### External

- Johnstone, *Sketches of an Elephant*, B2.3
  (internal presheaves in a topos)
- Mac Lane and Moerdijk, *Sheaves in Geometry and Logic*,
  V.7 (Grothendieck construction)
