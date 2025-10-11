universe u v

namespace GebLean

namespace Utilities

/-- Auxiliary lemma for unpacking sigma equalities after `simp`. -/
lemma sigmaCases {α : Sort u} {β : α → Sort v}
    {a₁ : α} {b₁ : β a₁} {a₂ : α} {b₂ : β a₂}
    (h : Sigma.mk a₁ b₁ = Sigma.mk a₂ b₂) :
    HEq b₁ (cast (by cases h; simp) b₂) := by
  cases h
  simp

end Utilities

end GebLean