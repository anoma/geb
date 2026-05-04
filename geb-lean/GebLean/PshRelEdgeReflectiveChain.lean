import GebLean.Utilities.Arrow
import GebLean.PshRelEdgeFunctionalize
import GebLean.PshRelEdgeInclusion

/-!
# Reflective Chain: PSh(C) ↪ Arrow(PSh(C)) ↪
#   WalkingSpan ⥤ PSh(C)

The presheaf category `PSh(C)` embeds into the
span presheaf category `WalkingSpan ⥤ PSh(C)`
through a chain of two reflective inclusions:

1. `Arrow.idInclusion`: sends `P` to the identity
   arrow `𝟙 P`. Reflector: codomain functor
   `Arrow.rightFunc`.

2. `arrowSpanInclusion`: sends an arrow
   `f : P ⟶ Q` to the span
   `P ←[𝟙]─ P ─[f]→ Q`. Reflector:
   `spanArrowReflector`, using constructive
   presheaf pushouts.

The edge category `PshRelEdge(C)` embeds into
`WalkingSpan ⥤ PSh(C)` via a separate reflective
inclusion through `pshRelEdgeInclusionFunctor`,
and into `Arrow(PSh(C))` via
`pshRelEdgeGraphFunctor`.

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

/-- The inclusion `Arrow(PSh(C)) ↪
WalkingSpan ⥤ PSh(C)`, sending `f : P ⟶ Q`
to the span `P ←[𝟙]─ P ─[f]→ Q`. -/
abbrev pshSpanFromArrowInclusion :
    Arrow (Cᵒᵖ ⥤ Type w) ⥤
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :=
  arrowSpanInclusion (Cᵒᵖ ⥤ Type w)

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

/-- The reflector
`WalkingSpan ⥤ PSh(C) → Arrow(PSh(C))`:
take the pushout of each span. -/
abbrev pshSpanFromArrowReflector :
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) ⥤
    Arrow (Cᵒᵖ ⥤ Type w) :=
  spanArrowReflector (pshSpanPushouts C)

/-- The composed reflector
`WalkingSpan ⥤ PSh(C) → PSh(C)`: take
the pushout then the codomain. -/
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

/-- The adjunction for
`Arrow(PSh(C)) ↪ WalkingSpan ⥤ PSh(C)`. -/
def pshSpanFromArrowAdj :
    pshSpanFromArrowReflector.{u, v, w} C ⊣
    pshSpanFromArrowInclusion.{u, v, w} C :=
  arrowSpanAdj (pshSpanPushouts C)

instance : Reflective
    (pshSpanFromArrowInclusion.{u, v, w}
      C) :=
  arrowSpanReflective (pshSpanPushouts C)

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
