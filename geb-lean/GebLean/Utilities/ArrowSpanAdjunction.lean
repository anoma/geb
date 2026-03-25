import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Adjunction.Reflective

open CategoryTheory Limits

namespace GebLean

universe v u

variable {C : Type u} [Category.{v} C]

/-- The inclusion of the arrow category into the category
of span diagrams, sending an arrow `f : P ⟶ Q` to the span
`P ←[id]─ P ─[f]→ Q`. -/
@[simps]
def arrowSpanInclusion
    (C : Type u) [Category.{v} C] :
    Arrow C ⥤ (WalkingSpan ⥤ C) where
  obj f := span (𝟙 f.left) f.hom
  map {f g} sq :=
    spanHomMk sq.left sq.left sq.right
      (by simp)
      (by simp)
  map_id f := by
    apply NatTrans.ext
    funext j
    match j with
    | .zero => simp
    | .left => simp
    | .right => simp
  map_comp {f g h} sq₁ sq₂ := by
    apply NatTrans.ext
    funext j
    match j with
    | .zero => simp
    | .left => simp
    | .right => simp

/-- `arrowSpanInclusion` is fully faithful: a natural
transformation between spans `(id, f)` and `(id, g)` is
determined by its components at `.left` and `.right`,
which form a commutative square. -/
def arrowSpanInclusion.fullyFaithful :
    (arrowSpanInclusion C).FullyFaithful where
  preimage {f g} α :=
    Arrow.homMk (α.app .left) (α.app .right)
      (by
        have hfst :=
          α.naturality WalkingSpan.Hom.fst
        simp only [Functor.id_obj,
          arrowSpanInclusion_obj,
          span_map_fst] at hfst
        have hsnd :=
          α.naturality WalkingSpan.Hom.snd
        simp only [Functor.id_obj,
          arrowSpanInclusion_obj,
          span_map_snd] at hsnd
        rw [show α.app .left =
            α.app .zero from by
          rw [← Category.id_comp
            (α.app .left),
            ← Category.comp_id
            (α.app .zero)]
          exact hfst]
        exact hsnd.symm)
  map_preimage {f g} α := by
    apply NatTrans.ext
    funext j
    match j with
    | .zero =>
      simp only [arrowSpanInclusion_obj,
        Functor.id_obj, span_zero,
        arrowSpanInclusion_map,
        Arrow.homMk_left, Arrow.homMk_right,
        spanHomMk_app]
      have h :=
        α.naturality WalkingSpan.Hom.fst
      simp only [Functor.id_obj,
        arrowSpanInclusion_obj,
        span_map_fst] at h
      rw [← Category.id_comp
        (α.app .left),
        ← Category.comp_id
        (α.app .zero)]
      exact h
    | .left => simp
    | .right => simp
  preimage_map {f g} sq := by
    apply Arrow.hom_ext
    · rfl
    · rfl

instance : (arrowSpanInclusion C).Faithful :=
  arrowSpanInclusion.fullyFaithful.faithful

instance : (arrowSpanInclusion C).Full :=
  arrowSpanInclusion.fullyFaithful.full

end GebLean
