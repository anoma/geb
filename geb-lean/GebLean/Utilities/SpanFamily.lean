import GebLean.Utilities.Graph

open CategoryTheory

namespace GebLean

universe u_V u_E u_D v_D

variable (V : Type u_V)
  (E : V → V → Type u_E)
  (D : Type u_D) [Category.{v_D} D]

/-- The category of span families: functors from
the graph span diagram category
`GraphSpanObj V E` to a target category `D`. -/
abbrev SpanFamily :=
  GraphSpanObj V E ⥤ D

end GebLean
