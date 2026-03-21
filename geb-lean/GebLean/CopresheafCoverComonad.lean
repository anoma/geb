import GebLean.PolyCover
import GebLean.BarResolution
import Mathlib.CategoryTheory.Monad.Basic

/-!
# Copresheaf Cover Comonad

The copresheaf cover construction `F ↦ copresheafCover F`
extends to an endofunctor on `C ⥤ Type (max u w v)`.
Equipped with a counit (the cover map) and
comultiplication (tautological embedding), it forms a
comonad.
-/

namespace GebLean

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v, u} C]

section CopresheafCoverFunctor

variable (C)

/--
The copresheaf cover as an endofunctor on
`C ⥤ Type (max u w v)`.  On objects, sends `F` to
its projective cover (a coproduct of covariant
representables indexed by elements of `F`).
On morphisms `α : F ⟶ G`, transports each element
`(j, f) ∈ copresheafCover F (Y)` to
`(α_*(j), f) ∈ copresheafCover G (Y)` via the
functoriality of the category of elements.
-/
def copresheafCoverFunctor :
    (C ⥤ Type (max u w v)) ⥤
      (C ⥤ Type (max u w v)) where
  obj F := copresheafCover.{max u w, v, u} F
  map {F G} α := {
    app := fun Y ⟨j, f⟩ =>
      ⟨Functor.elementsMk G j.1
        (α.app j.1 j.2), f⟩
    naturality := by
      intros Y Z g
      ext ⟨j, f⟩
      rfl
  }
  map_id := by
    intro F
    ext Y ⟨j, f⟩
    simp [Functor.elementsMk]
    rfl
  map_comp := by
    intro F G H α β
    ext Y ⟨j, f⟩
    simp [Functor.elementsMk]

end CopresheafCoverFunctor

section CopresheafCoverCounit

variable (C)

/--
The counit of the copresheaf cover comonad.
At each copresheaf `F`, sends `(j, f) ∈
copresheafCover F (Y)` (where `j = (c, x) ∈
F.Elements` and `f : c ⟶ Y`) to `F.map f x`.
-/
def copresheafCoverCounit :
    copresheafCoverFunctor.{w, v, u} C ⟶ 𝟭 _ where
  app F := {
    app := fun Y ⟨j, f⟩ => F.map f j.2
    naturality := by
      intros Y Z g
      ext ⟨j, f⟩
      exact congr_fun (F.map_comp f g) j.2
  }
  naturality := by
    intros F G α
    ext Y ⟨j, f⟩
    simp only [Functor.id_obj,
      FunctorToTypes.comp, Functor.id_map]
    exact congr_fun (α.naturality f).symm j.2

end CopresheafCoverCounit

section CopresheafCoverComult

variable (C)

/--
The comultiplication of the copresheaf cover comonad.
At each copresheaf `F`, sends `(j, f) ∈
copresheafCover F (Y)` to the tautological element
`(k, 𝟙 Y) ∈ copresheafCover (copresheafCover F) (Y)`
where `k = elementsMk (copresheafCover F) Y (j, f)`.
-/
def copresheafCoverComult :
    copresheafCoverFunctor.{w, v, u} C ⟶
      copresheafCoverFunctor.{w, v, u} C ⋙
        copresheafCoverFunctor.{w, v, u} C where
  app F := {
    app := fun Y ⟨j, f⟩ =>
      ⟨Functor.elementsMk
        (copresheafCover.{max u w, v, u} F) j.1
        ⟨j, 𝟙 j.1⟩, f⟩
    naturality := by
      intros Y Z g
      ext ⟨j, f⟩
      rfl
  }
  naturality := by
    intros F G α
    ext Y ⟨j, f⟩
    rfl

end CopresheafCoverComult

section CopresheafCoverComonadInstance

variable (C)

/--
The copresheaf cover comonad on `C ⥤ Type (max u w v)`.
-/
def copresheafCoverComonad :
    CategoryTheory.Comonad
      (C ⥤ Type (max u w v)) where
  toFunctor := copresheafCoverFunctor.{w, v, u} C
  ε := copresheafCoverCounit.{w, v, u} C
  δ := copresheafCoverComult.{w, v, u} C
  left_counit := by
    intro F
    ext Y ⟨j, f⟩
    simp only [copresheafCoverComult,
      copresheafCoverCounit,
      FunctorToTypes.comp, NatTrans.id_app]
    simp only [copresheafCoverFunctor,
      copresheafCover, ccrToFunctor, ccrEvalMap,
      types_id, id_eq]
    congr 1
    exact Category.id_comp f
  right_counit := by
    intro F
    ext Y ⟨j, f⟩
    simp only [copresheafCoverComult,
      copresheafCoverFunctor,
      copresheafCoverCounit,
      FunctorToTypes.comp,
      NatTrans.id_app, Functor.elementsMk]
    exact Sigma.ext
      (Sigma.ext rfl
        (heq_of_eq
          (congr_fun (F.map_id j.1) j.2)))
      (heq_of_eq rfl)
  coassoc := by
    intro F
    ext Y ⟨j, f⟩
    rfl

end CopresheafCoverComonadInstance

section CopresheafBarResolution

open CategoryTheory

variable (C)

/--
The bar resolution of the copresheaf cover comonad
applied to a copresheaf `F`.  This is a functor
`SimplexCategoryGenRelᵒᵖ ⥤ (C ⥤ Type (max u w v))`
whose level `n` is the `(n+1)`-fold iterated
copresheaf cover of `F`.
-/
def copresheafBarResolution
    (F : C ⥤ Type (max u w v)) :
    SimplexCategoryGenRelᵒᵖ ⥤
      (C ⥤ Type (max u w v)) :=
  Comonad.barResolution
    (copresheafCoverComonad.{w, v, u} C) F

end CopresheafBarResolution

end GebLean
