import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Arrow-Cospan Coreflective Adjunction

Dual to `ArrowSpanAdjunction`: given a category
with constructive pullbacks, the arrow category is
a coreflective subcategory of the category of
cospan diagrams.

The inclusion sends an arrow `f : P ⟶ Q` to the
cospan `P ─[f]→ Q ←[𝟙]─ Q`. The coreflector
sends each cospan to the arrow given by the right
projection from its pullback.

The adjunction is parameterized by an explicit
choice of limit cone for each cospan, avoiding
`Classical.choice`.
-/

open CategoryTheory Limits

namespace GebLean

universe v u

variable {C : Type u} [Category.{v} C]

/-- The inclusion of the arrow category into the
category of cospan diagrams, sending an arrow
`f : P ⟶ Q` to the cospan
`P ─[f]→ Q ←[𝟙]─ Q`. -/
@[simps]
def arrowCospanInclusion
    (C : Type u) [Category.{v} C] :
    Arrow C ⥤ (WalkingCospan ⥤ C) where
  obj f := cospan f.hom (𝟙 f.right)
  map {f g} sq :=
    cospanHomMk sq.right sq.left sq.right
      (by simp)
      (by simp)
  map_id f := by
    apply NatTrans.ext
    funext j
    match j with
    | .one => simp
    | .left => simp
    | .right => simp
  map_comp {f g h} sq₁ sq₂ := by
    apply NatTrans.ext
    funext j
    match j with
    | .one => simp
    | .left => simp
    | .right => simp

/-- `arrowCospanInclusion` is fully faithful. -/
def arrowCospanInclusion.fullyFaithful :
    (arrowCospanInclusion C).FullyFaithful where
  preimage {f g} α :=
    Arrow.homMk (α.app .left) (α.app .right)
      (by
        have hinl :=
          α.naturality WalkingCospan.Hom.inl
        have hinr :=
          α.naturality WalkingCospan.Hom.inr
        simp at hinr
        simp [hinr] at hinl
        exact hinl.symm)
  map_preimage {f g} α := by
    apply NatTrans.ext
    funext j
    match j with
    | .one =>
      change α.app .right = α.app .one
      have h :=
        α.naturality WalkingCospan.Hom.inr
      simp at h
      exact h.symm
    | .left => simp
    | .right => simp
  preimage_map {f g} sq := by
    apply Arrow.hom_ext
    · rfl
    · rfl

instance : (arrowCospanInclusion C).Faithful :=
  arrowCospanInclusion.fullyFaithful.faithful

instance : (arrowCospanInclusion C).Full :=
  arrowCospanInclusion.fullyFaithful.full

/-- The coreflector from cospan diagrams to
arrows, sending each cospan to the arrow given
by the right projection from its pullback.
Parameterized by an explicit choice of limit
cone for each cospan. -/
def cospanArrowCoreflector
    (pullbacks :
      (S : WalkingCospan ⥤ C) → LimitCone S) :
    (WalkingCospan ⥤ C) ⥤ Arrow C where
  obj S :=
    Arrow.mk
      ((pullbacks S).cone.π.app WalkingCospan.right)
  map {S₁ S₂} α :=
    Arrow.homMk
      ((pullbacks S₂).isLimit.lift
        (Cone.mk (pullbacks S₁).cone.pt
          ((pullbacks S₁).cone.π ≫ α)))
      (α.app WalkingCospan.right)
      (by
        have := (pullbacks S₂).isLimit.fac
          (Cone.mk (pullbacks S₁).cone.pt
            ((pullbacks S₁).cone.π ≫ α))
          WalkingCospan.right
        dsimp at this
        exact this)
  map_id S := by
    apply Arrow.hom_ext
    · dsimp
      symm
      apply (pullbacks S).isLimit.uniq
        (Cone.mk (pullbacks S).cone.pt
          ((pullbacks S).cone.π ≫ 𝟙 S))
      intro j
      simp [Category.comp_id]
    · simp
  map_comp {S₁ S₂ S₃} α β := by
    apply Arrow.hom_ext
    · dsimp
      symm
      apply (pullbacks S₃).isLimit.uniq
        (Cone.mk (pullbacks S₁).cone.pt
          ((pullbacks S₁).cone.π ≫ (α ≫ β)))
      intro j
      rw [Category.assoc,
        (pullbacks S₃).isLimit.fac
          (Cone.mk (pullbacks S₂).cone.pt
            ((pullbacks S₂).cone.π ≫ β)) j]
      dsimp
      rw [← Category.assoc,
        (pullbacks S₂).isLimit.fac
          (Cone.mk (pullbacks S₁).cone.pt
            ((pullbacks S₁).cone.π ≫ α)) j]
      dsimp
      simp only [Category.assoc]
    · simp

end GebLean
