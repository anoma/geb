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

universe v w

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

end CcrMapEquiv

end GebLean
