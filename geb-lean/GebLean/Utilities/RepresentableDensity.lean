import GebLean.PshRelEdgeSeparation

/-!
# Representable embedding and density for PshRelEdge

The representable embedding sends each pair
`(i : WalkingSpan, c : Cᵒᵖ)` to the separated
representable edge `pshRelEdgeRepresentable i c`.
This embedding is contravariant (Yoneda-like) and
factors through the span presheaf category via the
separation functor.
-/

namespace GebLean

open CategoryTheory Category Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C]

section SpanRepresentableFunctor

/-- The span representable embedding as a
contravariant functor from the small index
category to the span presheaf category.
A morphism `op(i₀,c₀) ⟶ op(i₁,c₁)` (i.e.,
`(i₁,c₁) ⟶ (i₀,c₀)` = `(φ : i₁ ⟶ i₀,
g : c₁ ⟶ c₀)`) maps `spanRep(i₀,c₀)` to
`spanRep(i₁,c₁)` by precomposition. -/
def spanRepresentableFunctor :
    (WalkingSpan × Cᵒᵖ)ᵒᵖ ⥤
      (WalkingSpan ⥤
        Cᵒᵖ ⥤ Type (max u v)) where
  obj ic :=
    spanRepresentable ic.unop.1 ic.unop.2
  map {ic₁ ic₂} f :=
    let φ := f.unop.1
    let g := f.unop.2
    { app := fun j =>
        { app := fun c' sp =>
            (φ ≫ sp.1, ⟨g ≫ sp.2.down⟩)
          naturality := fun {_ _} h => by
            funext ⟨a, ⟨b⟩⟩
            exact Prod.ext rfl
              (ULift.ext _ _
                (Category.assoc _ _ _).symm) }
      naturality := fun {_ _} ψ => by
        apply NatTrans.ext; funext c'
        funext ⟨a, ⟨b⟩⟩
        exact Prod.ext
          (Category.assoc _ _ _).symm rfl }
  map_id ic := by
    apply NatTrans.ext; funext j
    apply NatTrans.ext; funext c'
    funext ⟨h, ⟨k⟩⟩
    dsimp
    exact Prod.ext (Category.id_comp _)
      (ULift.ext _ _ (Category.id_comp _))
  map_comp {ic₁ ic₂ ic₃} f g := by
    apply NatTrans.ext; funext j
    apply NatTrans.ext; funext c'
    funext ⟨h, ⟨k⟩⟩
    dsimp
    exact Prod.ext
      (Category.assoc _ _ _)
      (ULift.ext _ _
        (Category.assoc _ _ _))

/-- The representable embedding as a functor
from the small index category
`(WalkingSpan × Cᵒᵖ)ᵒᵖ` to `PshRelEdge C`,
defined as the span representable functor
composed with the separation functor. -/
def pshRelEdgeRepresentableFunctor :
    (WalkingSpan × Cᵒᵖ)ᵒᵖ ⥤
      PshRelEdge.{u, v, max u v} C :=
  spanRepresentableFunctor ⋙
    pshRelEdgeSepFunctor C

end SpanRepresentableFunctor

end GebLean
