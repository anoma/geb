/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Univariate.Functor
public import Geb.Mathlib.Data.W.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# The W-type as the initial algebra of a polynomial functor

The W-type `P.W` of a polynomial functor carries an algebra structure
for the endofunctor `P.functor`, and is initial among such algebras.
Initiality is stated as `Unique` on the hom-set rather than through
mathlib's colimit API, which keeps the whole module free of
`Classical.choice`; the `Limits.IsInitial` packaging is the sibling
`Univariate.Initial` module.

The universe is forced here and only here: `P.W : Type (max uA uB)` is
the algebra's carrier, so `P.functor` is instantiated at
`v := max uA uB`.

## Main definitions

* `PFunctor.wAlgebra` — the algebra `⟨P.W, W.mk⟩`.
* `PFunctor.wElim` — the algebra morphism into any algebra.
* `PFunctor.wUniqueHom` — uniqueness of that morphism; initiality.
* `PFunctor.wStrIso` — the structure map as an isomorphism.

## Main statements

* `PFunctor.wStrIso_hom` — the isomorphism's forward map is the
  algebra's structure map.

## Implementation notes

`wUniqueHom` is not an `instance`: as one it would determine `default`
on the algebra hom-sets out of `wAlgebra`, competing with the identity
morphism the upstream `Inhabited` gives on endomorphism sets. Consumers
introduce it as a local hypothesis where a `Unique` instance is wanted.

`wStrIso` is mathlib's fixed-point equivalence `WType.equivSigma`
transported along `Equiv.toIso`. The `Iso` form is preferred to `IsIso`
because an `Iso` carries its inverse as data, so consumers never need
`CategoryTheory.inv`, which depends on `Classical.choice`. There is no
companion statement for `wStrIso.inv`: it is `equivSigma`'s forward
map, which is not definitionally `PFunctor.W.dest`.

## References

* [GambinoHyland2004]

## Tags

polynomial functor, W-type, initial algebra, PFunctor
-/

public section

universe uA uB

open CategoryTheory

namespace PFunctor

/-- The W-type of `P` as an algebra of `P.functor`, with the constructor
`W.mk` as structure map. -/
@[expose] def wAlgebra (P : PFunctor.{uA, uB}) :
    Endofunctor.Algebra (PFunctor.functor.{uA, uB, max uA uB} P) where
  a := P.W
  str := ↾W.mk

/-- The algebra morphism from the W-type algebra into any algebra: the
fold of that algebra's structure map. -/
@[expose] def wElim (P : PFunctor.{uA, uB})
    (B : Endofunctor.Algebra (PFunctor.functor.{uA, uB, max uA uB} P)) :
    P.wAlgebra ⟶ B where
  f := ↾(WType.elim B.a B.str)
  h := funext fun ⟨_, _⟩ ↦ rfl

/-- The W-type algebra is initial: the morphism into any algebra is
unique. -/
@[expose, instance_reducible] def wUniqueHom (P : PFunctor.{uA, uB})
    (B : Endofunctor.Algebra (PFunctor.functor.{uA, uB, max uA uB} P)) :
    Unique (P.wAlgebra ⟶ B) where
  default := P.wElim B
  uniq g :=
    Endofunctor.Algebra.Hom.ext
      (funext fun x ↦
        congrFun (WType.elim_unique B.str g.f
          (fun a f ↦ (congrFun g.h (⟨a, f⟩ : P.Obj P.W)).symm)) x)

/-- The structure map of the W-type algebra is an isomorphism: mathlib's
fixed-point equivalence, read as an isomorphism of types. -/
@[expose] def wStrIso (P : PFunctor.{uA, uB}) :
    (PFunctor.functor.{uA, uB, max uA uB} P).obj P.W ≅ P.W :=
  (WType.equivSigma P.B).symm.toIso

/-- The isomorphism's forward map is the algebra's structure map. -/
theorem wStrIso_hom (P : PFunctor.{uA, uB}) :
    (P.wStrIso).hom = (P.wAlgebra).str :=
  rfl

end PFunctor
