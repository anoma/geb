# Internal-presheaf Grothendieck equivalence

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area formalises internal categories in the presheaf topos
`[Cᵒᵖ, Set]`, the process of externalising such a category to a
`Cᵒᵖ ⥤ Cat` functor, and the equivalence between internal
presheaves on an internal category `X` and ordinary presheaves on
the Grothendieck construction of its externalisation. It provides
Geb with a bridge between internal categorical structure and the
external fibre-based language that mathlib's `Grothendieck`
machinery can consume.

## Mathematical context

An internal category in a presheaf topos `[Cᵒᵖ, Set]` is a monoid
object in the endomorphism monoidal category of the span bicategory
of presheaves (Johnstone, *Sketches of an Elephant*, vol. I, §B2).
Given such an internal category `X`, its *externalisation* is the
functor `Cᵒᵖ ⥤ Cat` that sends each stage `c : Cᵒᵖ` to the
fibre category of `X` at `c` (objects and morphisms are the
presheaf stalks, composition comes from the internal composition
map). An *internal presheaf* on `X` is a total-space presheaf
`P : Cᵒᵖ ⥤ Set` equipped with a projection to the object presheaf
of `X` and an action of the morphism presheaf satisfying unit and
associativity axioms; this is the internal-logic counterpart of the
notion of a discrete fibration over an internal category (Johnstone,
op. cit., §B2.3). The Grothendieck construction
(`CategoryTheory.Grothendieck`) of the externalisation assembles
all the fibre categories into a single category whose objects are
pairs `⟨c, x⟩` with `x` an object in the fibre at `c`. The main
theorem of this area is that internal presheaves on `X` are
equivalent, as a category, to ordinary presheaves on this
Grothendieck category — `PSh(X_int) ≃ PSh(Gr(ext(X)))`. This is an
instance of the general equivalence between slices of a presheaf
topos and presheaves on the category of elements (Johnstone, op.
cit., §B2.3; Moerdijk–MacLane, *Sheaves in Geometry and Logic*,
§I.5), specialised to the internal-category setting and carried out
in Lean against mathlib's `Grothendieck`.

## Modules

- [`GebLean/PshInternalCat.lean`](../../GebLean/PshInternalCat.lean)
  — the structure of an internal category in `[Cᵒᵖ, Set]`.
  `PshInternalCat` packs an object presheaf `objs` together with a
  monoid object `cat` in the endomorphism monoidal category of the
  span bicategory; `PshInternalFunctor` defines internal functors;
  `pshInternalCatCategory` gives the resulting category; and
  `catPshInternalEquiv` is the equivalence `Cat ≌ PshInternalCat
  (Discrete Unit)` exhibiting ordinary categories as the special
  case over the terminal site.
  The monoid-in-spans encoding of an internal category is
  well-known (Johnstone *Elephant* §B2; Borceux *Handbook*
  vol. 2, ch. 8), but the direct Lean formalisation over
  mathlib's `Mon_`, `PshSpanBicat`, and `Grothendieck` machinery
  is novel to this project; we have found no prior Lean
  formalisation. (Unverified.)

- [`GebLean/PshInternalExternalize.lean`](../../GebLean/PshInternalExternalize.lean)
  — the externalisation of an internal category to a `Cᵒᵖ ⥤ Cat`
  functor. `fiberCategory` equips the stalk `fiberObj X c` with a
  category structure for each stage `c`; `fiberRestrict` produces
  the restriction functors; `externalize` assembles the resulting
  functor `Cᵒᵖ ⥤ Cat`; and `externalizeNatTrans` extends the
  construction to internal functors, showing externalization is
  functorial.
  Externalisation of an internal category is a classical
  construction (Johnstone *Elephant* §B2; Borceux vol. 2, ch. 8);
  we have found no prior Lean formalisation against mathlib.
  (Unverified.)

- [`GebLean/PshInternalPresheaf.lean`](../../GebLean/PshInternalPresheaf.lean)
  — the notion of an internal presheaf on an internal category.
  `PshInternalPresheaf` is a structure carrying a total-space
  presheaf `fiber`, a projection `proj` to the object presheaf, and
  an `action` by the morphism presheaf with `action_id` and
  `action_assoc` axioms; `PshInternalPresheafHom` and
  `PshInternalPresheaf.category` complete the category of internal
  presheaves.
  Internal presheaves / discrete fibrations over internal categories
  are standard (Johnstone *Elephant* §B2.3); the Lean formalisation
  is project-original, and we have found no prior Lean
  formalisation. (Unverified.)

- [`GebLean/PshInternalGrothendieck.lean`](../../GebLean/PshInternalGrothendieck.lean)
  — the equivalence between internal presheaves and ordinary
  presheaves on the Grothendieck construction.
  `comparisonFunctor` maps `PshInternalPresheaf X` to
  `X.groth ⥤ Type w`; `inverseFunctor` is the quasi-inverse;
  `pshInternalGrothendieckEquiv` packages them as a category
  equivalence `PshInternalPresheaf X ≌ (X.groth ⥤ Type w)`.
  The equivalence is a special case of the slice-presheaf
  adjunction / discrete-fibration characterisation (Johnstone
  *Elephant* §B2.3; SGA4 Exp. I); this Lean proof is
  project-original, and we have found no prior mathlib
  formalization. (Unverified.)

- [`GebLean/Utilities/Elements.lean`](../../GebLean/Utilities/Elements.lean)
  — the contravariant category of elements and the slice-presheaf
  equivalence. `sliceEquivCopresheaf` establishes `Over F ≌
  (F.Elements ⥤ Type w)` for a copresheaf `F`; `Functor.ElementsContra`
  and `Functor.ElementsContra'` provide two variants of the
  contravariant category of elements, with conversion functors
  between them; `sliceEquivPresheaf` packages the equivalence for
  presheaves.
  The equivalence `Over F ≌ PSh(Elts(F))` is standard
  (MacLane–Moerdijk §I.5; nLab: category of elements); the
  covariant half `F.Elements` is already in mathlib
  (`CategoryTheory.Elements`).

- [`GebLean/Utilities/Grothendieck.lean`](../../GebLean/Utilities/Grothendieck.lean)
  — the contravariant Grothendieck construction. `GrothendieckContra`
  is the type of objects (pairs `(b, f)` with `b : C` and
  `f : F.obj (op b)`) with `GrothendieckContraCatInst` the
  category structure; the file provides transfer helpers
  `gcDomFuncToGcContra`, `gcCodFuncToGcContra`, and
  `gcDomCodFuncToGcContra` for moving functors involving mathlib's
  covariant `Grothendieck` into the contravariant setting.
  The contravariant Grothendieck construction is the opposite of
  the covariant one (nLab: Grothendieck construction; mathlib
  `CategoryTheory.Grothendieck`); the transfer helpers are
  bookkeeping over that standard construction.

- [`GebLean/Utilities/ConnectedGrothendieck.lean`](../../GebLean/Utilities/ConnectedGrothendieck.lean)
  — the connected Grothendieck construction over the twisted-arrow
  category. `ConnGrothendieckObj` and `ConnGrothendieckHom` define
  objects and morphisms of a category `E(F)` for a functor
  `F : Tw(C) ⥤ Cat`; each morphism carries both a commuting square
  in `Arr(C)` and a fibre morphism in the common diagonal category;
  the module assembles the full category structure including
  identity and composition.
  The connected Grothendieck construction generalises the
  two-sided Grothendieck construction to twisted-arrow indexing;
  the construction is described in
  [`docs/research/connected-grothendieck-construction.md`](../research/connected-grothendieck-construction.md)
  and appears novel to this project; we have found no prior Lean
  formalisation. (Unverified.)

## Dependencies

This area builds on:

- The span bicategory of presheaves (`PshSpanBicategory`) and
  polynomial-functor infrastructure, which supply the monoidal
  structure used to define `PshInternalCat`.
- The profunctors-ends layer, which supplies pointwise extraction
  helpers reused in the externalisation and comparison proofs.
- The quivers / semicategories area for the underlying site
  category `C`. That area does not yet have its own area doc; see
  the documentation index.

## Pointers

- [`docs/research/connected-grothendieck-construction.md`](../research/connected-grothendieck-construction.md)
  — mathematical specification of the connected Grothendieck
  construction formalised in `ConnectedGrothendieck.lean`.
- [`docs/research/universal-properties-categories-of-elements.md`](../research/universal-properties-categories-of-elements.md)
  — universal-property analysis of the category-of-elements
  construction underlying `Elements.lean`.
- [`docs/research/two-sided-grothendieck-construction.md`](../research/two-sided-grothendieck-construction.md)
  — the two-sided Grothendieck construction, which the connected
  variant in `ConnectedGrothendieck.lean` generalises.
- [`docs/superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md`](../superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md)
  — design spec for the strict two-sided Grothendieck construction
  adjacent to this area.
