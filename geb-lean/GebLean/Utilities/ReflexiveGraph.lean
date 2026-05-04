import Mathlib.CategoryTheory.Functor.Basic

/-!
# Reflexive Graph Categories

A reflexive graph category consists of a vertex
category `V`, an edge category `E`, source and
target functors `E ⥤ V`, and an identity section
`V ⥤ E` that is a section of both source and
target.
-/

namespace GebLean

open CategoryTheory

universe u_V v_V u_E v_E

/-- Data for a reflexive graph category: vertex
and edge categories with source, target, and
identity functors satisfying the retraction
conditions. -/
structure ReflexiveGraphData
    (V : Type u_V) [Category.{v_V} V]
    (E : Type u_E) [Category.{v_E} E] where
  src : E ⥤ V
  tgt : E ⥤ V
  ident : V ⥤ E
  src_ident : ident ⋙ src = 𝟭 V
  tgt_ident : ident ⋙ tgt = 𝟭 V

end GebLean
