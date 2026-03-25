import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Adjunction.Reflective

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- The functor sending each object to its identity arrow. -/
@[simps]
def Arrow.idInclusion (C : Type u) [Category.{v} C] :
    C ⥤ Arrow C where
  obj c := Arrow.mk (𝟙 c)
  map f := Arrow.homMk f f

/-- `Arrow.idInclusion` is fully faithful: a morphism between
identity arrows is determined by its left (equivalently, right)
component. -/
def Arrow.idInclusion.fullyFaithful :
    (Arrow.idInclusion C).FullyFaithful where
  preimage sq := sq.left
  map_preimage {X Y} sq := by
    apply Arrow.hom_ext
    · rfl
    · change sq.left = sq.right
      have h : sq.left ≫ 𝟙 Y = 𝟙 X ≫ sq.right :=
        sq.w
      calc sq.left
          = sq.left ≫ 𝟙 Y :=
            (Category.comp_id sq.left).symm
        _ = 𝟙 X ≫ sq.right := h
        _ = sq.right :=
            Category.id_comp sq.right
  preimage_map _ := rfl

instance : (Arrow.idInclusion C).Faithful :=
  Arrow.idInclusion.fullyFaithful.faithful

instance : (Arrow.idInclusion C).Full :=
  Arrow.idInclusion.fullyFaithful.full

/-- The codomain functor `Arrow.rightFunc` is left adjoint
to `Arrow.idInclusion`: a morphism from an arrow `f` to
an identity arrow `id_c` is determined by a morphism from
the codomain of `f` to `c`. -/
def Arrow.rightFuncAdjIdInclusion :
    (Arrow.rightFunc : Arrow C ⥤ C) ⊣
      Arrow.idInclusion C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun f c => {
      toFun := fun h =>
        Arrow.homMk (f.hom ≫ h) h
      invFun := fun sq => sq.right
      left_inv := fun _ => rfl
      right_inv := fun sq => by
        apply Arrow.hom_ext
        · change f.hom ≫ sq.right = sq.left
          have h : sq.left ≫ 𝟙 c = f.hom ≫ sq.right :=
            sq.w
          calc f.hom ≫ sq.right
              = sq.left ≫ 𝟙 c := h.symm
            _ = sq.left :=
                Category.comp_id sq.left
        · rfl
    }
  }

instance : Reflective (Arrow.idInclusion C) where
  L := Arrow.rightFunc
  adj := Arrow.rightFuncAdjIdInclusion

/-- `Arrow.idInclusion` is left adjoint to the domain functor
`Arrow.leftFunc`: a morphism from an identity arrow `id_c`
to an arrow `f` is determined by a morphism from `c` to
the domain of `f`. -/
def Arrow.idInclusionAdjLeftFunc :
    Arrow.idInclusion C ⊣
      (Arrow.leftFunc : Arrow C ⥤ C) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun c f => {
      toFun := fun sq => sq.left
      invFun := fun g =>
        Arrow.homMk g (g ≫ f.hom)
      left_inv := fun sq => by
        apply Arrow.hom_ext
        · rfl
        · change sq.left ≫ f.hom = sq.right
          have h : sq.left ≫ f.hom = 𝟙 c ≫ sq.right :=
            sq.w
          calc sq.left ≫ f.hom
              = 𝟙 c ≫ sq.right := h
            _ = sq.right :=
                Category.id_comp sq.right
      right_inv := fun _ => rfl
    }
  }

instance : Coreflective (Arrow.idInclusion C) where
  R := Arrow.leftFunc
  adj := Arrow.idInclusionAdjLeftFunc

end GebLean
