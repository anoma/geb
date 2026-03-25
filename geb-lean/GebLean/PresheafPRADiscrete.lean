import GebLean.Polynomial
import GebLean.PresheafPRA
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Over X as a Presheaf Category on Discrete X

The slice category `Over X` for a type `X` is equivalent to
the presheaf category `(Discrete X)ᵒᵖ ⥤ Type u`.  The
equivalence composes three steps:

1. `familySliceEquiv.symm : Over X ≌ (X → Type u)`
2. `piEquivalenceFunctorDiscrete X (Type u) :
     (X → Type u) ≌ (Discrete X ⥤ Type u)`
3. `(Discrete.opposite X).symm.congrLeft :
     (Discrete X ⥤ Type u) ≌ ((Discrete X)ᵒᵖ ⥤ Type u)`
-/

namespace GebLean

open CategoryTheory

universe u

/--
The equivalence between `Over X` and the presheaf
category `(Discrete X)ᵒᵖ ⥤ Type u`.

Composes `familySliceEquiv.symm`, which identifies
`Over X` with `X`-indexed families of types, with
`piEquivalenceFunctorDiscrete`, which identifies
families with functors out of `Discrete X`, and finally
precomposition by `(Discrete.opposite X).symm` to pass
from `Discrete X` to `(Discrete X)ᵒᵖ`.
-/
def overDiscretePresheafEquiv (X : Type u) :
    Over X ≌ ((Discrete X)ᵒᵖ ⥤ Type u) :=
  (familySliceEquiv X).symm |>.trans
    (piEquivalenceFunctorDiscrete X (Type u))
    |>.trans
    ((Discrete.opposite X).symm.congrLeft)

section CcrMapEquiv

variable {C : Type (u + 1)} [Category.{u} C]
  {D : Type (u + 1)} [Category.{u} D]
  (e : C ≌ D)

/--
Forward functor from `CoprodCovarRepCat' C` to
`CoprodCovarRepCat' D` induced by an equivalence
`e : C ≌ D`.  Applies `e.functor` to each element
of the family.
-/
def ccrMapEquivFwd :
    CoprodCovarRepCat'.{u + 1, u, u} C ⥤
      CoprodCovarRepCat'.{u + 1, u, u} D where
  obj P := ccrObjMk (e.functor.obj ∘ ccrFamily P)
  map {P Q} f :=
    ccrHomMk (f.base) (fun i =>
      e.functor.map (ccrFiberMor f i))
  map_id P := by
    simp only [ccrId_mk, ccrHomMk, ccrFiberMor,
      ccrObjMk_family, Function.comp]
    congr 1
    funext i
    exact e.functor.map_id _
  map_comp {P Q R} f g := by
    simp only [ccrComp_mk,
      ccrHomMk_reindex, ccrHomMk_fiberMor,
      ccrComp_fiberMor, ccrReindex,
      Functor.map_comp]
    congr 1

/--
Inverse functor from `CoprodCovarRepCat' D` to
`CoprodCovarRepCat' C` induced by an equivalence
`e : C ≌ D`.  Applies `e.inverse` to each element
of the family.
-/
def ccrMapEquivInv :
    CoprodCovarRepCat'.{u + 1, u, u} D ⥤
      CoprodCovarRepCat'.{u + 1, u, u} C :=
  ccrMapEquivFwd e.symm

/--
Component of the unit natural isomorphism for
`ccrMapEquiv` at object `P`.
-/
def ccrMapEquivUnitApp
    (P : CoprodCovarRepCat'.{u + 1, u, u} C) :
    P ≅ (ccrMapEquivFwd e ⋙
      ccrMapEquivInv e).obj P where
  hom := ccrHomMk id
    (fun i => e.unitIso.inv.app (ccrFamily P i))
  inv := ccrHomMk id
    (fun i => e.unitIso.hom.app (ccrFamily P i))
  hom_inv_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.unitIso.hom_inv_id_app _
  inv_hom_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.unitIso.inv_hom_id_app _

/--
Component of the counit natural isomorphism for
`ccrMapEquiv` at object `Q`.
-/
def ccrMapEquivCounitApp
    (Q : CoprodCovarRepCat'.{u + 1, u, u} D) :
    (ccrMapEquivInv e ⋙
      ccrMapEquivFwd e).obj Q ≅ Q where
  hom := ccrHomMk id
    (fun i => e.counitIso.inv.app (ccrFamily Q i))
  inv := ccrHomMk id
    (fun i => e.counitIso.hom.app (ccrFamily Q i))
  hom_inv_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.counitIso.hom_inv_id_app _
  inv_hom_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.counitIso.inv_hom_id_app _

/--
The unit natural isomorphism for `ccrMapEquiv`.
-/
def ccrMapEquivUnit :
    𝟭 (CoprodCovarRepCat'.{u + 1, u, u} C) ≅
      ccrMapEquivFwd e ⋙ ccrMapEquivInv e :=
  NatIso.ofComponents (ccrMapEquivUnitApp e)
    (fun {P Q} f => by
      simp only [ccrComp_mk, Functor.id_map,
        Functor.comp_map, ccrMapEquivFwd,
        ccrMapEquivInv, ccrMapEquivFwd,
        ccrHomMk_reindex, ccrHomMk_fiberMor,
        ccrMapEquivUnitApp, ccrObjMk_family,
        Function.comp]
      congr 1
      funext i
      exact (e.unitIso.inv.naturality
        (ccrFiberMor f i)).symm)

/--
The counit natural isomorphism for `ccrMapEquiv`.
-/
def ccrMapEquivCounit :
    ccrMapEquivInv e ⋙ ccrMapEquivFwd e ≅
      𝟭 (CoprodCovarRepCat'.{u + 1, u, u} D) :=
  NatIso.ofComponents (ccrMapEquivCounitApp e)
    (fun {P Q} f => by
      simp only [ccrComp_mk, Functor.id_map,
        Functor.comp_map, ccrMapEquivFwd,
        ccrMapEquivInv, ccrMapEquivFwd,
        ccrHomMk_reindex, ccrHomMk_fiberMor,
        ccrMapEquivCounitApp, ccrObjMk_family,
        Function.comp]
      congr 1
      funext i
      exact (e.counitIso.inv.naturality
        (ccrFiberMor f i)).symm)

/--
The equivalence `CoprodCovarRepCat' C ≌
CoprodCovarRepCat' D` induced by `e : C ≌ D`.
Applies `e.functor` / `e.inverse` pointwise to each
family element.
-/
def ccrMapEquiv :
    CoprodCovarRepCat'.{u + 1, u, u} C ≌
      CoprodCovarRepCat'.{u + 1, u, u} D where
  functor := ccrMapEquivFwd e
  inverse := ccrMapEquivInv e
  unitIso := ccrMapEquivUnit e
  counitIso := ccrMapEquivCounit e
  functor_unitIso_comp P := by
    simp only [ccrComp_mk, ccrMapEquivFwd,
      ccrHomMk_reindex, ccrHomMk_fiberMor,
      ccrMapEquivUnit, ccrMapEquivUnitApp,
      ccrMapEquivCounit, ccrMapEquivCounitApp,
      NatIso.ofComponents, ccrObjMk_family,
      Function.comp, ccrId_mk]
    congr 1
    funext i
    simp only [ccrHomMk, id]
    let x := ccrFamily P i
    have h := e.functor_unitIso_comp x
    rw [← cancel_mono
      (e.functor.map (e.unitIso.hom.app x) ≫
        e.counitIso.hom.app
          (e.functor.obj x))]
    simp [h]

end CcrMapEquiv

/--
The equivalence between `CoprodCovarRepCat' (Over X)`
and `CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type u)`.

Composes three equivalences:
1. `ccrMapEquiv (overDiscretePresheafEquiv X)`
   transfers from `Over X` families to presheaf families
   at the `CoprodCovarRepCat'` level.
2. `ccrOp'OpEquiv` transfers from the `op'`-based to
   the `op`-based coproduct-of-covariant-representables
   category.
-/
def ccrOverDiscreteEquiv (X : Type u) :
    CoprodCovarRepCat'.{u + 1, u, u} (Over X) ≌
      CoprodCovarRepCat.{u + 1, u, u}
        ((Discrete X)ᵒᵖ ⥤ Type u) :=
  (ccrMapEquiv (overDiscretePresheafEquiv X)).trans
    (ccrOp'OpEquiv ((Discrete X)ᵒᵖ ⥤ Type u))

end GebLean
