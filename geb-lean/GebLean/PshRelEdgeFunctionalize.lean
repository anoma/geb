import GebLean.PshRelEdgeInclusion
import GebLean.Utilities.ArrowSpanAdjunction

/-!
# Functionalization of Presheaf Relations

This file constructs a reflective adjunction from
the arrow category of presheaves into the edge
category of presheaf relations.

The right adjoint (inclusion) sends an arrow
`f : P ⟶ Q` to the edge `(P, Q, graph(f))`,
using `pshRelEdgeGraphFunctor`.

The left adjoint (reflector) functionalizes a
relation by composing the edge-to-span inclusion
`pshRelEdgeInclusionFunctor` with the general
span-to-arrow reflector `spanArrowReflector`
that forms pushouts.

## Main definitions

* `pshRelEdgeFunctionalizeFunctor`: the
  reflector functor
  `PshRelEdge C ⥤ Arrow(PSh(C))`
* `pshRelEdgeFunctionalizeAdj`: the adjunction
  `functionalize ⊣ graph`
* `pshRelEdgeGraphReflective`: the reflective
  subcategory instance
-/

open CategoryTheory Limits

namespace GebLean

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The functorializer from `PshRelEdge C` to
`Arrow(PSh(C))`, defined as the composition of
the edge-to-span inclusion with the span-to-arrow
reflector using constructive presheaf pushouts. -/
abbrev pshRelEdgeFunctionalizeFunctor
    (C : Type u) [Category.{v} C] :
    PshRelEdge.{u, v, w} C ⥤
    Arrow (Cᵒᵖ ⥤ Type w) :=
  pshRelEdgeInclusionFunctor C ⋙
    spanArrowReflector (pshSpanPushouts C)

/-- The unit component at edge `E`: the morphism
`E ⟶ graph(L(E))` in `PshRelEdge C`. The source
map is the identity; the target map is the right
injection into the pushout. -/
def pshRelEdgeFunctionalizeUnitComp
    (E : PshRelEdge.{u, v, w} C) :
    E ⟶ (pshRelEdgeGraphFunctor (C := C)).obj
      ((pshRelEdgeFunctionalizeFunctor C).obj
        E) where
  srcMap := 𝟙 _
  tgtMap :=
    (pshSpanPushouts C
      (pshRelEdgeSpan E)).cocone.ι.app
        WalkingSpan.right
  sq _ p q hR :=
    Quot.sound ⟨⟨(p, q), hR⟩, rfl, rfl⟩

/-- The cocone over the span of `graph(f)` with
point `f.right`, used to define the counit. The
left leg is `f.hom`, the right leg is `𝟙`. -/
private def functionalizeCounitCocone
    (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    Cocone (pshRelEdgeSpan
      ((pshRelEdgeGraphFunctor
        (C := C)).obj f)) where
  pt := f.right
  ι :=
    { app := fun j => match j with
        | .zero =>
          pshRelSndProj (pshRelGraph f.hom)
        | .left => f.hom
        | .right => 𝟙 _
      naturality := by
        intro X Y h
        induction h with
        | id => simp
        | init j =>
          cases j with
          | left =>
            simp only [Functor.const_obj_map]
            ext c ⟨⟨p, q⟩,
              (h : f.hom.app c p = q)⟩
            exact h
          | right =>
            simp [pshRelEdgeSpan,
              pshRelEdgeGraphFunctor] }

/-- The counit component at arrow `f`: the
morphism `L(graph(f)) ⟶ f` in `Arrow(PSh(C))`.
The left component is `𝟙`; the right is given
by the universal property of the pushout. -/
def pshRelEdgeFunctionalizeCounitComp
    (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    (pshRelEdgeFunctionalizeFunctor C).obj
      ((pshRelEdgeGraphFunctor
        (C := C)).obj f) ⟶ f :=
  Arrow.homMk (𝟙 _)
    ((pshSpanPushouts C _).isColimit.desc
      (functionalizeCounitCocone f))
    (by
      dsimp [spanArrowReflector]
      rw [Category.id_comp]
      exact ((pshSpanPushouts C _).isColimit.fac
        (functionalizeCounitCocone f)
        WalkingSpan.left).symm)

/-- The unit of the functionalize-graph
adjunction as a natural transformation. -/
def pshRelEdgeFunctionalizeAdjUnit
    (C : Type u) [Category.{v} C] :
    𝟭 (PshRelEdge.{u, v, w} C) ⟶
    pshRelEdgeFunctionalizeFunctor C ⋙
      pshRelEdgeGraphFunctor where
  app E := pshRelEdgeFunctionalizeUnitComp E
  naturality _ _ _ := by
    apply VertEdgeHom.ext <;>
    · ext c x; rfl

/-- The counit of the functionalize-graph
adjunction as a natural transformation. -/
def pshRelEdgeFunctionalizeAdjCounit
    (C : Type u) [Category.{v} C] :
    pshRelEdgeGraphFunctor ⋙
      pshRelEdgeFunctionalizeFunctor C ⟶
    𝟭 (Arrow (Cᵒᵖ ⥤ Type w)) where
  app f := pshRelEdgeFunctionalizeCounitComp f
  naturality {f g} sq := by
    apply CommaMorphism.ext
    · ext c x; rfl
    · apply NatTrans.ext; funext c
      exact funext (Quot.ind fun a => by
        cases a with
        | inl p =>
          exact congr_fun
            (congr_app sq.w c) p
        | inr q => rfl)

/-- The functionalize-graph adjunction:
`pshRelEdgeFunctionalizeFunctor ⊣
pshRelEdgeGraphFunctor`. -/
def pshRelEdgeFunctionalizeAdj
    (C : Type u) [Category.{v} C] :
    pshRelEdgeFunctionalizeFunctor.{u, v, w}
      C ⊣ pshRelEdgeGraphFunctor :=
  Adjunction.mkOfUnitCounit {
    unit :=
      pshRelEdgeFunctionalizeAdjUnit C
    counit :=
      pshRelEdgeFunctionalizeAdjCounit C
    left_triangle := by
      apply NatTrans.ext; funext E
      simp only [NatTrans.comp_app,
        Functor.whiskerRight_app,
        Functor.whiskerLeft_app,
        Functor.associator,
        Category.id_comp]
      apply CommaMorphism.ext
      · rfl
      · apply NatTrans.ext; funext c
        exact funext (Quot.ind fun a => by
          cases a with
          | inl p => rfl
          | inr q => rfl)
    right_triangle := by
      apply NatTrans.ext; funext f
      simp only [NatTrans.comp_app,
        Functor.whiskerRight_app,
        Functor.whiskerLeft_app,
        Functor.associator,
        Category.id_comp]
      apply VertEdgeHom.ext
      · rfl
      · ext c q; rfl
  }

/-- `Arrow(PSh(C))` is a reflective subcategory
of `PshRelEdge C` via the graph functor. The
reflector functionalizes relations by composing
the edge-to-span inclusion with the span-to-arrow
reflector. -/
instance pshRelEdgeGraphReflective
    (C : Type u) [Category.{v} C] :
    Reflective
      (pshRelEdgeGraphFunctor :
        Arrow (Cᵒᵖ ⥤ Type w) ⥤
          PshRelEdge.{u, v, w} C) where
  L := pshRelEdgeFunctionalizeFunctor C
  adj := pshRelEdgeFunctionalizeAdj C

end GebLean
