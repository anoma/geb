import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.IsConnected

/-!
# Connected Components Utilities

Equivalence between connected components of a category
and its opposite, and `IsInhabitedConnected` (the data-level
analogue of `IsConnected`).
-/

namespace CategoryTheory

open Opposite

universe w₁ w₂

/--
A category is inhabited-connected if it is preconnected and
`Inhabited`.  This is the data-level strengthening of
`IsConnected` (which uses `Nonempty`): the distinguished
object is provided as data rather than a `Prop` witness.
-/
class IsInhabitedConnected (J : Type w₁)
    [Category.{w₂} J]
    extends IsPreconnected J, Inhabited J

instance (priority := 100) IsInhabitedConnected.isConnected
    (J : Type w₁) [Category.{w₂} J]
    [IsInhabitedConnected J] : IsConnected J where
  is_nonempty := ⟨default⟩

variable {J : Type w₁} [Category.{w₂} J]

theorem zag_op_iff {a b : J} :
    Zag (op a) (op b) ↔ Zag a b := by
  constructor
  · rintro (⟨⟨f⟩⟩ | ⟨⟨g⟩⟩)
    · exact Zag.of_inv f.unop
    · exact Zag.of_hom g.unop
  · rintro (⟨⟨f⟩⟩ | ⟨⟨g⟩⟩)
    · exact Zag.of_inv f.op
    · exact Zag.of_hom g.op

theorem zigzag_op {a b : J} (h : Zigzag a b) :
    Zigzag (op a) (op b) :=
  h.lift op (fun _ _ hab => zag_op_iff.mpr hab)

theorem zigzag_unop {a b : Jᵒᵖ}
    (h : Zigzag a b) :
    Zigzag a.unop b.unop :=
  h.lift Opposite.unop
    (fun _ _ hab => zag_op_iff.mp hab)

def connectedComponentsOpEquiv (J : Type w₁)
    [Category.{w₂} J] :
    ConnectedComponents Jᵒᵖ ≃
      ConnectedComponents J where
  toFun := Quotient.lift
    (Quotient.mk (Zigzag.setoid J) ∘
      Opposite.unop)
    (fun _ _ h => Quotient.sound (zigzag_unop h))
  invFun := Quotient.lift
    (Quotient.mk (Zigzag.setoid Jᵒᵖ) ∘ op)
    (fun _ _ h => Quotient.sound (zigzag_op h))
  left_inv x := Quotient.inductionOn x
    (fun _ => rfl)
  right_inv x := Quotient.inductionOn x
    (fun _ => rfl)

def connectedComponentsEquivOfEquiv
    {K : Type w₁} [Category.{w₂} K]
    (e : J ≌ K) :
    ConnectedComponents J ≃
      ConnectedComponents K where
  toFun := e.functor.mapConnectedComponents
  invFun := e.inverse.mapConnectedComponents
  left_inv x := Quotient.inductionOn x
    (fun j => Quotient.sound
      (Zigzag.of_hom (e.unitIso.inv.app j)))
  right_inv x := Quotient.inductionOn x
    (fun k => Quotient.sound
      (Zigzag.of_hom (e.counitIso.hom.app k)))

end CategoryTheory
