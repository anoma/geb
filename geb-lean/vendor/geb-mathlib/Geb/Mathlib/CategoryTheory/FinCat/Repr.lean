/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom2

/-!
# `Repr` for specifications

`Repr` instances at each of the three levels: finite-category
specifications, functor specifications and 2-cell specifications. Each
renders the counts and the tables as nested naturals, through
`List.ofFn` and `Fin.val`, dropping to core's `Repr` instances for
`Nat`, `List` and tuples at every leaf and index. The `Bool`-validity
fields are not rendered: they carry no information a reader of the
table needs, being determined by the table itself.

`Repr` requires no transport at any level: it maps out of the
dependent structure into `Format`, discarding the types whose
disagreement obstructs equality. That is why this module is separate
from, and simpler than, the decidable-equality module.

## Main definitions

* `CategoryTheory.FinCat.instRepr` — renders a specification as its
  object count, its count matrix and its composition table.
* `CategoryTheory.FinCat.Hom.instRepr` — renders a functor
  specification as its object map and its morphism table.
* `CategoryTheory.FinCat.Hom₂.instRepr` — renders a 2-cell
  specification as its component vector.

## Implementation notes

Beyond its own dependency this module needs no import: `List.ofFn` is
axiom-free and core.

## Tags

category, functor, natural transformation, finite category, repr,
constructive, choice-free
-/

@[expose] public section

namespace CategoryTheory

namespace FinCat

/-- Renders a specification as its object count, its count matrix and
its composition table. -/
instance instRepr : Repr FinCat where
  reprPrec S _ :=
    repr (S.objCount,
      List.ofFn (fun i ↦ List.ofFn (fun j ↦ S.nonIdCount i j)),
      List.ofFn (fun i ↦ List.ofFn (fun j ↦ List.ofFn (fun k ↦
        List.ofFn (fun f ↦ List.ofFn (fun g ↦ (S.comp i j k f g).val))))))

/-- Renders a functor specification as its object map and its morphism
table. -/
instance Hom.instRepr {S T : FinCat} : Repr (Hom S T) where
  reprPrec F _ :=
    repr (List.ofFn (fun i ↦ (F.objMap i).val),
      List.ofFn (fun i ↦ List.ofFn (fun j ↦ List.ofFn (fun f ↦ (F.map i j f).val))))

/-- Renders a 2-cell specification as its component vector. -/
instance Hom₂.instRepr {S T : FinCat} {F G : Hom S T} :
    Repr (Hom₂ F G) where
  reprPrec α _ := repr (List.ofFn (fun i ↦ (α.app i).val))

end FinCat

end CategoryTheory
