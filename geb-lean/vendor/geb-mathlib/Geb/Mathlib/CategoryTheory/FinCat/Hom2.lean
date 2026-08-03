/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom
public import Mathlib.CategoryTheory.NatTrans

/-!
# 2-cell specifications

A natural transformation between two functor specifications with the
same source and target is specified by a component at each object
index and a `Bool` equation asserting naturality. The component ranges
over the target's full hom type from the outset, so the identity
2-cell has every component an identity.

The 2-cells between a fixed pair of functor specifications form a
category under componentwise composition, and each of them generates a
mathlib natural transformation between the generated functors.

## Main definitions

* `CategoryTheory.FinCat.Hom₂.natCheckOf`,
  `CategoryTheory.FinCat.Hom₂.natCheck` — the decidable naturality
  check on client morphisms.
* `CategoryTheory.FinCat.Hom₂` — the 2-cell specification type.
* `CategoryTheory.FinCat.Hom.instCategory` — the hom-category:
  vertical composition and the identity 2-cell.
* `CategoryTheory.FinCat.Hom₂.toNatTrans` — the mathlib natural
  transformation a 2-cell specification generates.

## Main statements

* `FinCat.Hom₂.natCheck_eq_true_iff` — the check reflects naturality on
  client morphisms.
* `FinCat.Hom₂.eq_of_app_eq`, `FinCat.Hom₂.ext` — extensionality, at
  `FinCat.Hom₂ F G` and at `F ⟶ G` respectively.
* `FinCat.Hom₂.app_id`, `FinCat.Hom₂.app_comp` — the components of the
  identity 2-cell and of a vertical composite.
* `FinCat.Hom₂.natCheck_total` — naturality, on all morphisms.

## Implementation notes

`natCheckOf` precedes the structure because the `natValid` field's type
mentions it. The enclosing `namespace FinCat` stays open throughout;
the inner `namespace Hom₂` blocks close around `structure Hom₂`, which
cannot be declared inside a namespace of its own name, and around
`instance Hom.instCategory`, whose full name is a `FinCat.Hom` name and
so cannot be written inside a `namespace Hom₂` either.

`eq_of_app_eq` precedes the category instance because the instance's
three law fields need it and the hom notation `⟶` does not exist until
the instance does. `CategoryTheory.Cat.Hom.instCategory` discharges its
counterparts by `congrArg`, which is available there because
`CategoryTheory.Cat.Hom₂` is a one-field wrapper; `FinCat.Hom` is not
such a bundling, so that route is unavailable here.

`natCheck_total` extends the check off the client range, as
`FinCat.Hom.mapTotal_compTotal` does for the composition check. The
extension, rather than the check itself, is what `toNatTrans` needs: a
morphism of the generated category is an arbitrary element of the full
hom type, not an embedded client morphism.

`toNatTrans` states its result type as `CategoryTheory.NatTrans` rather
than through `⟶`. The two are the same type, but the notation names it
via `CategoryTheory.Functor.category`, whose category laws are
discharged by `aesop_cat` and so depend on `Classical.choice`; the
notation therefore carries that dependence into the type of any
declaration written with it.

The check is stated over the total composition and the total morphism
maps, for the reason `FinCat.Hom.compCheckOf` is: a client composite
may land on the reserved identity index, on which the client's
morphism map is undefined.

`FinCat.Hom₂` is not marked `@[ext]`. A structure-derived
extensionality lemma does not fire on goals stated through the hom
notation `F ⟶ G`, so it would be unusable at the only place it is
needed; the name `FinCat.Hom₂.ext` is left free for a hand-written
lemma phrased at `F ⟶ G`, matching what mathlib does for
`CategoryTheory.Cat.Hom₂`.

## References

* [JohnsonYau2021] § 1.1 — the notion of natural transformation, of
  which this module's specification type is a presentation.

## Tags

category, functor, natural transformation, finite category, decidable,
constructive, choice-free
-/

@[expose] public section

namespace CategoryTheory

namespace FinCat

namespace Hom₂

/-- Naturality, as a `Bool`, on client morphisms. Stated over the total
composition and the total morphism maps, for the reason
`FinCat.Hom.compCheckOf` is. -/
def natCheckOf (S T : FinCat) (F G : Hom S T)
    (app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)) : Bool :=
  decide <| ∀ (i j : Fin S.objCount) (f : Fin (S.nonIdCount i j)),
    T.compTotal (F.mapTotal (S.emb f)) (app j)
      = T.compTotal (app i) (G.mapTotal (S.emb f))

end Hom₂

/-- A 2-cell specification: a natural transformation between two
functor specifications. -/
structure Hom₂ {S T : FinCat} (F G : Hom S T) where
  /-- The component at each object. It ranges over the full hom type
  from the outset, the identity 2-cell having every component an
  identity. -/
  app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)
  /-- Naturality. -/
  natValid : Hom₂.natCheckOf S T F G app = true

namespace Hom₂

/-- The naturality check reflects naturality on client morphisms. -/
theorem natCheck_eq_true_iff (S T : FinCat) (F G : Hom S T)
    (app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)) :
    natCheckOf S T F G app = true ↔
      ∀ (i j : Fin S.objCount) (f : Fin (S.nonIdCount i j)),
        T.compTotal (F.mapTotal (S.emb f)) (app j)
          = T.compTotal (app i) (G.mapTotal (S.emb f)) :=
  decide_eq_true_iff

/-- `α`'s naturality check. -/
def natCheck {S T : FinCat} {F G : Hom S T} (α : Hom₂ F G) : Bool :=
  natCheckOf S T F G α.app

/-- Two 2-cells with equal components are equal. Stated at
`FinCat.Hom₂ F G` rather than at `F ⟶ G`, so that it is available
before the hom-category instance exists. -/
theorem eq_of_app_eq {S T : FinCat} {F G : Hom S T} {α β : Hom₂ F G}
    (h : ∀ i, α.app i = β.app i) : α = β := by
  obtain ⟨a, _⟩ := α
  obtain ⟨b, _⟩ := β
  have hab : a = b := funext h
  subst hab
  rfl

end Hom₂

/-- The category of 2-cells between two functor specifications:
vertical composition and the identity 2-cell. -/
instance Hom.instCategory {S T : FinCat} : Category (Hom S T) where
  Hom F G := Hom₂ F G
  id F :=
    { app := fun i ↦ T.id (F.objMap i)
      natValid := by
        refine (Hom₂.natCheck_eq_true_iff S T F F _).mpr ?_
        intro i j f
        rw [T.comp_id, T.id_comp] }
  comp α β :=
    { app := fun i ↦ T.compTotal (α.app i) (β.app i)
      natValid := by
        refine (Hom₂.natCheck_eq_true_iff S T _ _ _).mpr ?_
        intro i j f
        rw [← T.compTotal_assoc,
          (Hom₂.natCheck_eq_true_iff S T _ _ _).mp α.natValid i j f, T.compTotal_assoc,
          (Hom₂.natCheck_eq_true_iff S T _ _ _).mp β.natValid i j f, ← T.compTotal_assoc] }
  id_comp α := Hom₂.eq_of_app_eq fun i ↦ T.id_comp (α.app i)
  comp_id α := Hom₂.eq_of_app_eq fun i ↦ T.comp_id (α.app i)
  assoc α β γ := Hom₂.eq_of_app_eq fun i ↦ T.compTotal_assoc (α.app i) (β.app i) (γ.app i)

namespace Hom₂

variable {S T : FinCat}

/-- The identity 2-cell's components are the reserved identities. -/
@[simp] theorem app_id {F : Hom S T} (i : Fin S.objCount) :
    (𝟙 F : F ⟶ F).app i = T.id (F.objMap i) := rfl

/-- A vertical composite's components are the composites. -/
@[simp] theorem app_comp {F G H : Hom S T} (α : F ⟶ G) (β : G ⟶ H)
    (i : Fin S.objCount) :
    (α ≫ β).app i = T.compTotal (α.app i) (β.app i) := rfl

/-- Two 2-cells with equal components are equal, phrased at `F ⟶ G` so
that the `ext` tactic fires on goals stated through the hom notation. -/
@[ext] theorem ext {F G : Hom S T} {α β : F ⟶ G} (h : ∀ i, α.app i = β.app i) :
    α = β := eq_of_app_eq h

/-- Naturality at total morphisms, extending `natCheck` off the client
range. -/
theorem natCheck_total {F G : Hom S T} (α : Hom₂ F G)
    {i j : Fin S.objCount} (x : S.Mor i j) :
    T.compTotal (F.mapTotal x) (α.app j) = T.compTotal (α.app i) (G.mapTotal x) := by
  by_cases hx : x.val < S.nonIdCount i j
  · have h := (natCheck_eq_true_iff S T F G α.app).mp α.natValid i j ⟨x.val, hx⟩
    rwa [show S.emb (⟨x.val, hx⟩ : Fin (S.nonIdCount i j)) = x from Fin.ext rfl] at h
  · have hij := S.eq_of_nonIdCount_le x (Nat.not_lt.mp hx)
    subst hij
    rw [show x = S.id _ from Fin.ext (S.val_eq_of_nonIdCount_le x (Nat.not_lt.mp hx)),
      F.mapTotal_id, G.mapTotal_id, T.id_comp, T.comp_id]

/-- The mathlib natural transformation a 2-cell specification
generates. -/
def toNatTrans.{v, u} {F G : Hom S T} (α : Hom₂ F G) :
    NatTrans (Hom.toFunctor.{v, u} F) (Hom.toFunctor.{v, u} G) where
  app X := ULift.up (α.app X.idx.down)
  naturality _ _ f := congrArg ULift.up (α.natCheck_total f.down)

end Hom₂

end FinCat

end CategoryTheory
