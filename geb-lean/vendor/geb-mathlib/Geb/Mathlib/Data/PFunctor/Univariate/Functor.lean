/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# The functor of a univariate polynomial functor

Packages mathlib's `PFunctor` interpretation as a
`CategoryTheory.Functor`. The interpretation `P.Obj` already carries
`Functor` and `LawfulFunctor` instances upstream, so the categorical
functor is their transport along `CategoryTheory.ofTypeFunctor` rather
than a hand-written object map, morphism map, and pair of functor laws.

`P.Obj : Type v → Type (max v uA uB)` maps `Type v` to itself whenever
`uA ≤ v` and `uB ≤ v`, so the functor is stated at an unconstrained `v`
and instantiated at the universe an endofunctor is wanted in.

## Main definitions

* `PFunctor.functor` — the functor `Type v ⥤ Type (max v uA uB)`.

## Main statements

* `PFunctor.functor_obj` / `PFunctor.functor_map` — the categorical
  object and morphism maps are the upstream `PFunctor.Obj` and
  `PFunctor.map`.

## Implementation notes

Morphisms of `Type v` are bundled, so a function is promoted to a
morphism with `↾` and the underlying function of a morphism is read
through `ConcreteCategory.hom`; `functor_map` is therefore stated in
promoted form on both sides. `functor` is `@[expose]` so both statements
are exported `rfl` theorems. Inside `namespace PFunctor` under
`open CategoryTheory` the bare identifier `Functor` is ambiguous between
core `Functor` and `CategoryTheory.Functor`, so the latter is written in
full.

## References

* [AltenkirchGhaniHancockMcBrideMorris2015]

## Tags

polynomial functor, container, PFunctor, functor
-/

public section

universe uA uB v

open CategoryTheory

namespace PFunctor

/-- The functor `Type v ⥤ Type (max v uA uB)` interpreting a polynomial
functor, transported from the upstream `Functor` and `LawfulFunctor`
instances on `PFunctor.Obj`. -/
@[expose] def functor (P : PFunctor.{uA, uB}) :
    CategoryTheory.Functor (Type v) (Type (max v uA uB)) :=
  ofTypeFunctor P.Obj

/-- The categorical object map is the upstream interpretation. -/
theorem functor_obj (P : PFunctor.{uA, uB}) (α : Type v) :
    (P.functor).obj α = P.Obj α :=
  rfl

/-- The categorical morphism map is the upstream action, on both sides
in the promoted form `Type v` morphisms take. -/
theorem functor_map (P : PFunctor.{uA, uB}) {α β : Type v} (f : α → β) :
    (P.functor).map (↾f) = ↾(P.map f) :=
  rfl

end PFunctor
