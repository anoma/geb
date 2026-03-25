import GebLean.Utilities.Arrow
import GebLean.PshRelEdgeFunctionalize
import GebLean.PshRelEdgeInclusion

/-!
# Reflective Chain: PSh(C) ↪ Arrow(PSh(C)) ↪
#   PshRelEdge(C) ↪ WalkingSpan ⥤ PSh(C)

The presheaf category `PSh(C)` embeds into the
span presheaf category `WalkingSpan ⥤ PSh(C)`
through a chain of three reflective inclusions:

1. `Arrow.idInclusion`: sends `P` to the identity
   arrow `𝟙 P`. Reflector: codomain functor
   `Arrow.rightFunc`.

2. `pshRelEdgeGraphFunctor`: sends an arrow
   `f : P ⟶ Q` to the graph edge
   `(P, Q, graph(f))`. Reflector:
   `pshRelEdgeFunctionalizeFunctor`.

3. `pshRelEdgeInclusionFunctor`: sends an edge
   `(P, Q, R)` to the span
   `P ←─ R.toFunctor ─→ Q`. Reflector:
   `pshRelEdgeSepFunctor`.

Each step is reflective, and `Reflective.comp`
provides the composed reflective instances.
-/

open CategoryTheory Limits

namespace GebLean

universe u v w

variable (C : Type u) [Category.{v} C]

section PairwiseCompositions

/-- The composed inclusion
`PSh(C) ↪ PshRelEdge(C)`, sending `P` to
`(P, P, graph(𝟙 P))`. -/
abbrev pshRelEdgeFromPshInclusion :
    (Cᵒᵖ ⥤ Type w) ⥤
    PshRelEdge.{u, v, w} C :=
  Arrow.idInclusion (Cᵒᵖ ⥤ Type w) ⋙
    pshRelEdgeGraphFunctor

/-- The composed inclusion
`Arrow(PSh(C)) ↪ WalkingSpan ⥤ PSh(C)`, sending
`f : P ⟶ Q` to the span
`P ←─ graph(f).toFunctor ─→ Q`. -/
abbrev pshSpanFromArrowInclusion :
    Arrow (Cᵒᵖ ⥤ Type w) ⥤
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :=
  pshRelEdgeGraphFunctor ⋙
    pshRelEdgeInclusionFunctor C

/-- The full composed inclusion
`PSh(C) ↪ WalkingSpan ⥤ PSh(C)`. -/
abbrev pshSpanFromPshInclusion :
    (Cᵒᵖ ⥤ Type w) ⥤
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :=
  Arrow.idInclusion (Cᵒᵖ ⥤ Type w) ⋙
    pshSpanFromArrowInclusion C

end PairwiseCompositions

section ComposedReflectors

/-- The composed reflector
`PshRelEdge(C) → PSh(C)`: functionalize the
relation then take the codomain. -/
abbrev pshRelEdgeFromPshReflector :
    PshRelEdge.{u, v, w} C ⥤
    (Cᵒᵖ ⥤ Type w) :=
  pshRelEdgeFunctionalizeFunctor C ⋙
    Arrow.rightFunc

/-- The composed reflector
`WalkingSpan ⥤ PSh(C) → Arrow(PSh(C))`:
separate the span then functionalize. -/
abbrev pshSpanFromArrowReflector :
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) ⥤
    Arrow (Cᵒᵖ ⥤ Type w) :=
  pshRelEdgeSepFunctor C ⋙
    pshRelEdgeFunctionalizeFunctor C

/-- The composed reflector
`WalkingSpan ⥤ PSh(C) → PSh(C)`: separate,
functionalize, and take the codomain. -/
abbrev pshSpanFromPshReflector :
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) ⥤
    (Cᵒᵖ ⥤ Type w) :=
  pshSpanFromArrowReflector C ⋙
    Arrow.rightFunc

end ComposedReflectors

section ComposedAdjunctions

/-- The composed adjunction for
`PSh(C) ↪ PshRelEdge(C)`. -/
def pshRelEdgeFromPshAdj :
    pshRelEdgeFromPshReflector.{u, v, w} C ⊣
    pshRelEdgeFromPshInclusion.{u, v, w} C :=
  (pshRelEdgeFunctionalizeAdj C).comp
    Arrow.rightFuncAdjIdInclusion

instance : Reflective
    (pshRelEdgeFromPshInclusion.{u, v, w}
      C) :=
  Reflective.comp
    (Arrow.idInclusion (Cᵒᵖ ⥤ Type w))
    pshRelEdgeGraphFunctor

/-- The composed adjunction for
`Arrow(PSh(C)) ↪ WalkingSpan ⥤ PSh(C)`. -/
def pshSpanFromArrowAdj :
    pshSpanFromArrowReflector.{u, v, w} C ⊣
    pshSpanFromArrowInclusion.{u, v, w} C :=
  (pshRelEdgeSepAdjunction C).comp
    (pshRelEdgeFunctionalizeAdj C)

instance : Reflective
    (pshSpanFromArrowInclusion.{u, v, w}
      C) :=
  Reflective.comp
    (pshRelEdgeGraphFunctor (C := C))
    (pshRelEdgeInclusionFunctor C)

/-- The full composed adjunction for
`PSh(C) ↪ WalkingSpan ⥤ PSh(C)`. -/
def pshSpanFromPshAdj :
    pshSpanFromPshReflector.{u, v, w} C ⊣
    pshSpanFromPshInclusion.{u, v, w} C :=
  (pshSpanFromArrowAdj C).comp
    Arrow.rightFuncAdjIdInclusion

instance : Reflective
    (pshSpanFromPshInclusion.{u, v, w} C) :=
  Reflective.comp
    (Arrow.idInclusion (Cᵒᵖ ⥤ Type w))
    (pshSpanFromArrowInclusion C)

end ComposedAdjunctions

end GebLean
