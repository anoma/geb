import GebLean.ComprehensiveFactorization
import GebLean.Weighted

namespace GebLean

open CategoryTheory

universe v u u₂ w

variable {C : Type u} [Category.{v} C]

section ProfPullbackCompatibility

variable {E : Type u₂} [Category.{v} E]
  {D : Type w} [Category.{v} D]

theorem profOnCoTwArr_profPullback
    (G : Cᵒᵖ ⥤ C ⥤ D) (F : E ⥤ C) :
    profunctorOnCoTwistedArrow E (profPullback G F) =
    coTwistedArrowMap F ⋙
      profunctorOnCoTwistedArrow C G := by
  exact _root_.CategoryTheory.Functor.ext
    (fun tw => rfl)

theorem profOnTwArr_profPullback
    (G : Cᵒᵖ ⥤ C ⥤ D) (F : E ⥤ C) :
    profunctorOnTwistedArrow E (profPullback G F) =
    twistedArrowMap F ⋙
      profunctorOnTwistedArrow C G := by
  exact _root_.CategoryTheory.Functor.ext
    (fun tw => rfl)

end ProfPullbackCompatibility

section WeightedCoconeDiagramEq

variable {J : Type u₂} [Category.{v} J]
  {D : Type w} [Category.{v} D]

theorem weightedCoconeDiagram_eq
    (W : Jᵒᵖ ⥤ Type v) (G : J ⥤ D) :
    weightedCoconeDiagram W G =
    elementsPre_π W ⋙ G := by
  exact _root_.CategoryTheory.Functor.ext
    (fun _ => rfl)

end WeightedCoconeDiagramEq

end GebLean
