import GebLean.RestrictedCoendAsColimit
import GebLean.Utilities.EndsAndCoends

/-!
# Mendler-Lambek Equivalence via Ends and Powers

This module re-expresses the `GExtFunctor` (Vene's `G^e`) using
ends and powers instead of restricted coends.

Starting from
`G^e(pt) = restricted coend of G by HomToProf(pt)`,
the derivation proceeds in three steps:

1. Transfer the restricted coend to a copower-profunctor coend
   (done in `RestrictedCoendAsColimit.lean`).
2. Apply coend-end duality:
   `Hom(coend, Y) ≃ typeEnd (P ⇓ Y)`.
3. Replace copowers with powers inside the end via
   `copowerPowerEquiv`.

The final characterization is:
`Hom(G^e(pt), Y) ≃ ∫_A Hom(G(A,A), Y^(A→pt))`.
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits

universe v w

/-!
## Coend-End Duality for Initial Cowedges

Given a coend cowedge `c` (initial in `Cowedge P`) for a
`D`-valued profunctor, the hom-set `c.pt ⟶ Y` is
isomorphic to the explicit end `typeEnd (P ⇓ Y)`.
-/

section CoendEndDuality

variable
  {C : Type v} [Category.{v} C]
  {D : Type w} [Category.{v} D]

/-- Coend-end duality for initial cowedges:
given a coend cowedge `c` (initial in `Cowedge P`),
`(c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y)`.

Combines `ordinaryHomIsoEndApex` (relating the
coend apex hom to any terminal wedge apex) with
`typeEndWedge_isTerminal` (making `typeEnd` the apex
of a terminal wedge). -/
def cowedgeHomEndEquiv
    (P : Cᵒᵖ ⥤ C ⥤ D)
    {c : Cowedge (J := C) (C := D) P}
    (hc : IsInitial c) (Y : D) :
    (c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y) :=
  let iso := ordinaryHomIsoEndApex P hc Y
    (typeEndWedge_isTerminal (P ⇓ Y))
  ⟨iso.hom, iso.inv,
   fun x => congr_fun iso.hom_inv_id x,
   fun x => congr_fun iso.inv_hom_id x⟩

end CoendEndDuality

/-!
## End Formula for GExtFunctor

Apply coend-end duality to the copower-profunctor coend
to express the hom from `CopowerGExtObj` as an explicit
end:
`(CopowerGExtObj G pt ⟶ Y) ≃
  typeEnd (copowerProf (HomToProf pt) G ⇓ Y)`.
-/

section EndFormula

variable
  {C : Type v} [Category.{v} C] [HasCopowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

open HasAllCopowerProfCoends

/-- The hom from the copower-profunctor coend carrier
to any `Y` is an explicit end of the slice profunctor.

On the diagonal at `A`, the slice profunctor sends
`A` to `(copower (A ⟶ pt) (G(op A, A)) ⟶ Y)`. -/
def copowerGExtHomEndEquiv (pt Y : C) :
    (CopowerGExtObj G pt ⟶ Y) ≃
      typeEnd
        (copowerProf (HomToProf pt) G ⇓ Y) :=
  cowedgeHomEndEquiv
    (copowerProf (HomToProf pt) G)
    (copowerCoendIsInitial G pt) Y

end EndFormula

/-!
## Power-Slice Profunctor

The profunctor `powerSliceProf G pt Y` sends
`(A, B) ↦ (G(op B, A.unop) ⟶ Y^(B ⟶ pt))`.

On the diagonal `(op j, j)` this gives
`G(op j, j) ⟶ Y^(j ⟶ pt)`.

The structure follows `sliceProfunctor` (the
`P ⇓ Y` notation from `Weighted.lean`), with the
constant target `c` replaced by `Y^(B ⟶ pt)` varying
covariantly in `B`.
-/

section PowerEnd

variable
  {C : Type v} [Category.{v} C]
  [HasCopowers C] [HasPowers C]

/-- The power-slice profunctor: sends
`(A, B) ↦ (G(op B, A.unop) ⟶ Y^(B ⟶ pt))`.

Follows the convention of `sliceProfunctor`:
the outer functor is indexed by `A : Cᵒᵖ` and the
inner by `B : C`. The covariant map (in B) precomposes
with `(G.map g.op).app A.unop` and postcomposes with
`HasPowers.mapIdx (g ≫ ·)`. The contravariant map
(in A, given `f : A₁ ⟶ A₂` in `Cᵒᵖ`) precomposes
with `(G.obj (op B)).map f.unop`. -/
def powerSliceProf
    (G : Cᵒᵖ ⥤ C ⥤ C)
    (pt Y : C) : Cᵒᵖ ⥤ C ⥤ Type v where
  obj A := {
    obj := fun B =>
      (G.obj (Opposite.op B)).obj A.unop ⟶
        HasPowers.power Y (B ⟶ pt)
    map := fun {B₁ B₂} g h =>
      (G.map g.op).app A.unop ≫ h ≫
        HasPowers.mapIdx (g ≫ ·)
    map_id := fun B => by
      ext h
      simp only [types_id_apply, op_id,
        CategoryTheory.Functor.map_id,
        NatTrans.id_app, Category.id_comp]
      erw [HasPowers.mapIdx_id, Category.comp_id]
    map_comp := fun {B₁ B₂ B₃} f g => by
      ext h
      simp only [types_comp_apply, op_comp,
        Functor.map_comp, NatTrans.comp_app,
        Category.assoc]
      congr 1; congr 1; congr 1
      exact HasPowers.mapIdx_comp
        (g ≫ ·) (f ≫ ·)
  }
  map {A₁ A₂} f := {
    app := fun B h =>
      (G.obj (Opposite.op B)).map f.unop ≫ h
    naturality := fun {B₁ B₂} g => by
      ext h
      simp only [types_comp_apply, Category.assoc]
      rw [← Category.assoc
        ((G.obj (Opposite.op B₂)).map f.unop)
        ((G.map g.op).app A₁.unop)]
      rw [(G.map g.op).naturality f.unop]
      simp only [Category.assoc]
  }
  map_id := fun A => by
    ext B h
    simp only [NatTrans.id_app, types_id_apply,
      unop_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  map_comp := fun {A₁ A₂ A₃} f g => by
    ext B h
    simp only [NatTrans.comp_app, types_comp_apply,
      unop_comp, Functor.map_comp, Category.assoc]

end PowerEnd

end GebLean
