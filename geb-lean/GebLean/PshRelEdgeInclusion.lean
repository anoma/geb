import GebLean.PshRelDouble
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

open CategoryTheory Limits

namespace GebLean

universe u v w

variable {C : Type u} [Category.{v} C]

/-- Given a relatedness square, the induced map on
total presheaves of subfunctors. If `alpha` and
`beta` map R-related pairs to S-related pairs,
then the induced map sends `(p, q, h)` to
`(alpha p, beta q, h')`. -/
def pshRelRelatedTotalMap
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    {α : P ⟶ P'} {β : Q ⟶ Q'}
    {R : PshRel P Q} {S : PshRel P' Q'}
    (sq : pshRelRelated α β R S) :
    R.toFunctor ⟶ S.toFunctor where
  app c x :=
    ⟨(α.app c x.val.1, β.app c x.val.2),
      sq c x.val.1 x.val.2 x.prop⟩
  naturality c d f := by
    ext ⟨⟨p, q⟩, h⟩
    simp only [Subfunctor.toFunctor, types_comp_apply]
    apply Subtype.ext
    exact Prod.ext
      (congr_fun (α.naturality f) p)
      (congr_fun (β.naturality f) q)

/-- The first projection from the total presheaf
of a relation to the source presheaf. -/
abbrev pshRelFstProj
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    R.toFunctor ⟶ P :=
  R.ι ≫ pshProdFst P Q

/-- The second projection from the total presheaf
of a relation to the target presheaf. -/
abbrev pshRelSndProj
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    R.toFunctor ⟶ Q :=
  R.ι ≫ pshProdSnd P Q

/-- The total map commutes with the first
projection. -/
theorem pshRelRelatedTotalMap_fst
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    {α : P ⟶ P'} {β : Q ⟶ Q'}
    {R : PshRel P Q} {S : PshRel P' Q'}
    (sq : pshRelRelated α β R S) :
    pshRelRelatedTotalMap sq ≫
      pshRelFstProj S =
    pshRelFstProj R ≫ α := by
  ext c ⟨⟨_, _⟩, _⟩; rfl

/-- The total map commutes with the second
projection. -/
theorem pshRelRelatedTotalMap_snd
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    {α : P ⟶ P'} {β : Q ⟶ Q'}
    {R : PshRel P Q} {S : PshRel P' Q'}
    (sq : pshRelRelated α β R S) :
    pshRelRelatedTotalMap sq ≫
      pshRelSndProj S =
    pshRelSndProj R ≫ β := by
  ext c ⟨⟨_, _⟩, _⟩; rfl

/-- The span diagram in `PSh(C)` associated to
a presheaf relation edge `(P, Q, R)`:
`P <-- R.toFunctor --> Q`. -/
def pshRelEdgeSpan
    (E : PshRelEdge.{u, v, w} C) :
    WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w) :=
  span (pshRelFstProj (C := C) E.edge)
       (pshRelSndProj (C := C) E.edge)

/-- The morphism between span diagrams induced by
a morphism in the edge category. -/
def pshRelEdgeSpanMap
    {E E' : PshRelEdge.{u, v, w} C}
    (h : E ⟶ E') :
    pshRelEdgeSpan E ⟶ pshRelEdgeSpan E' :=
  spanHomMk
    (pshRelRelatedTotalMap h.sq)
    h.srcMap
    h.tgtMap
    (pshRelRelatedTotalMap_fst h.sq).symm
    (pshRelRelatedTotalMap_snd h.sq).symm

/-- The total map of the identity morphism is the
identity natural transformation. -/
theorem pshRelRelatedTotalMap_id
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelRelatedTotalMap
      (pshRelRelatedSqHorId (C := C) R) =
    𝟙 R.toFunctor := by
  ext c ⟨⟨_, _⟩, _⟩; rfl

/-- The total map of the composite of two
relatedness squares is the composite of the total
maps. -/
theorem pshRelRelatedTotalMap_comp
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : Cᵒᵖ ⥤ Type w}
    {α₁ : P₁ ⟶ P₂} {β₁ : Q₁ ⟶ Q₂}
    {α₂ : P₂ ⟶ P₃} {β₂ : Q₂ ⟶ Q₃}
    {R₁ : PshRel P₁ Q₁} {R₂ : PshRel P₂ Q₂}
    {R₃ : PshRel P₃ Q₃}
    (sq₁ : pshRelRelated α₁ β₁ R₁ R₂)
    (sq₂ : pshRelRelated α₂ β₂ R₂ R₃) :
    pshRelRelatedTotalMap
      (pshRelRelatedHComp sq₁ sq₂) =
    pshRelRelatedTotalMap sq₁ ≫
      pshRelRelatedTotalMap sq₂ := by
  ext c ⟨⟨_, _⟩, _⟩; rfl

/-- The inclusion functor from `PshRelEdge C` into
the functor category `WalkingSpan ⥤ PSh(C)`.
Sends `(P, Q, R)` to the span
`P <-- R.toFunctor --> Q`. -/
def pshRelEdgeInclusionFunctor (C : Type u)
    [Category.{v} C] :
    PshRelEdge.{u, v, w} C ⥤
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) where
  obj E := pshRelEdgeSpan E
  map h := pshRelEdgeSpanMap h
  map_id E := by
    dsimp only [pshRelEdgeSpanMap,
      pshRelEdgeSpan]
    apply NatTrans.ext; funext j
    match j with
    | .none =>
      exact pshRelRelatedTotalMap_id E.edge
    | .some .left => rfl
    | .some .right => rfl
  map_comp f g := by
    dsimp only [pshRelEdgeSpanMap,
      pshRelEdgeSpan]
    apply NatTrans.ext; funext j
    match j with
    | .none =>
      exact pshRelRelatedTotalMap_comp
        f.sq g.sq
    | .some .left => rfl
    | .some .right => rfl

/-- Given a natural transformation between
edge spans, the vertex components preserve
the relation. The proof uses naturality at
the span projections. -/
theorem pshRelEdgeSpan_nat_related
    {E E' : PshRelEdge.{u, v, w} C}
    (h : pshRelEdgeSpan E ⟶
         pshRelEdgeSpan E') :
    pshRelRelated
      (h.app (.some .left))
      (h.app (.some .right))
      E.edge E'.edge := by
  intro c p q hpq
  set elem : E.edge.toFunctor.obj c :=
    ⟨(p, q), hpq⟩
  set img := (h.app .none).app c elem with
    img_def
  have hval : img.val =
      ((h.app (.some .left)).app c p,
       (h.app (.some .right)).app c q) := by
    apply Prod.ext
    · have := congr_fun (congr_app
        (h.naturality
          (WidePushoutShape.Hom.init
            WalkingPair.left)) c) elem
      dsimp [pshRelEdgeSpan, span,
        WidePushoutShape.wideSpan,
        pshRelFstProj,
        types_comp_apply] at this
      exact this.symm
    · have := congr_fun (congr_app
        (h.naturality
          (WidePushoutShape.Hom.init
            WalkingPair.right)) c) elem
      dsimp [pshRelEdgeSpan, span,
        WidePushoutShape.wideSpan,
        pshRelSndProj,
        types_comp_apply] at this
      exact this.symm
  rw [← hval]
  exact img.prop

/-- The inclusion functor is fully faithful.
Injectivity on morphisms follows from the fact
that edge morphisms are determined by their
vertex components (`srcMap`, `tgtMap`), and the
span maps at the vertices are exactly these
components. -/
def pshRelEdgeInclusionFullyFaithful
    (C : Type u) [Category.{v} C] :
    (pshRelEdgeInclusionFunctor.{u, v, w} C
    ).FullyFaithful where
  preimage {E E'} h :=
    { srcMap := h.app (.some .left)
      tgtMap := h.app (.some .right)
      sq := pshRelEdgeSpan_nat_related h }
  map_preimage h := by
    dsimp only [pshRelEdgeInclusionFunctor,
      pshRelEdgeSpanMap, pshRelEdgeSpan]
    apply NatTrans.ext; funext j
    match j with
    | .none =>
      simp only [spanHomMk]
      ext c ⟨⟨p, q⟩, hpq⟩
      apply Subtype.ext
      apply Prod.ext
      · have := congr_fun (congr_app
          (h.naturality
            (WidePushoutShape.Hom.init
              WalkingPair.left)) c)
          ⟨(p, q), hpq⟩
        dsimp [pshRelEdgeInclusionFunctor,
          pshRelEdgeSpan, span,
          WidePushoutShape.wideSpan,
          pshRelFstProj,
          pshRelRelatedTotalMap] at this ⊢
        exact this
      · have := congr_fun (congr_app
          (h.naturality
            (WidePushoutShape.Hom.init
              WalkingPair.right)) c)
          ⟨(p, q), hpq⟩
        dsimp [pshRelEdgeInclusionFunctor,
          pshRelEdgeSpan, span,
          WidePushoutShape.wideSpan,
          pshRelSndProj,
          pshRelRelatedTotalMap] at this ⊢
        exact this
    | .some .left => rfl
    | .some .right => rfl
  preimage_map _ :=
    VertEdgeHom.ext rfl rfl

/-- The separation reflector on objects. Sends a
span `P <-- R --> Q` to the edge
`(P, Q, image(R -> P x Q))`, replacing the apex
with the image of the pairing map. -/
def pshRelEdgeSepObj
    (F : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :
    PshRelEdge.{u, v, w} C :=
  { src := F.obj (.some .left)
    tgt := F.obj (.some .right)
    edge := Subfunctor.range
      (pshProdLift
        (F.map (WidePushoutShape.Hom.init
          WalkingPair.left))
        (F.map (WidePushoutShape.Hom.init
          WalkingPair.right))) }

/-- The separation reflector on morphisms. Given
a natural transformation between spans, the vertex
components preserve the image relation. -/
def pshRelEdgeSepMap
    {F G : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)}
    (h : F ⟶ G) :
    pshRelEdgeSepObj (C := C) F ⟶
    pshRelEdgeSepObj (C := C) G :=
  { srcMap := h.app (.some .left)
    tgtMap := h.app (.some .right)
    sq := by
      intro c p q ⟨r, hr⟩
      dsimp [pshProdLift,
        FunctorToTypes.prod.lift] at hr
      refine ⟨(h.app .none).app c r, ?_⟩
      dsimp [pshProdLift,
        FunctorToTypes.prod.lift]
      have hp := congr_arg Prod.fst hr
      have hq := congr_arg Prod.snd hr
      dsimp at hp hq
      rw [← hp, ← hq]
      exact Prod.ext
        (congr_fun (congr_app
          (h.naturality
            (WidePushoutShape.Hom.init
              WalkingPair.left)) c) r).symm
        (congr_fun (congr_app
          (h.naturality
            (WidePushoutShape.Hom.init
              WalkingPair.right)) c) r).symm }

/-- The separation reflector functor from
`WalkingSpan ⥤ PSh(C)` to `PshRelEdge C`.
Sends each span to its separated version by
taking the image of the pairing map. -/
def pshRelEdgeSepFunctor (C : Type u)
    [Category.{v} C] :
    (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) ⥤
    PshRelEdge.{u, v, w} C where
  obj F := pshRelEdgeSepObj F
  map h := pshRelEdgeSepMap h
  map_id _ := VertEdgeHom.ext rfl rfl
  map_comp _ _ := VertEdgeHom.ext rfl rfl

/-- The unit of the adjunction: the canonical map
from a span to its separated version, viewed back
as a span via the inclusion. At the vertices this
is the identity; at the apex it sends each element
of `R` to its image in the subfunctor
`Im(R -> P x Q)`. -/
def pshRelEdgeSepUnit
    (F : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :
    F ⟶ (pshRelEdgeInclusionFunctor.{u, v, w}
      C).obj
        ((pshRelEdgeSepFunctor C).obj F) :=
  spanHomMk
    { app := fun c r =>
        ⟨((pshProdLift
            (F.map (WidePushoutShape.Hom.init
              WalkingPair.left))
            (F.map (WidePushoutShape.Hom.init
              WalkingPair.right))).app c r),
          ⟨r, rfl⟩⟩
      naturality := by
        intro c d f; ext r
        apply Subtype.ext
        dsimp [pshRelEdgeInclusionFunctor,
          pshRelEdgeSepFunctor,
          pshRelEdgeSepObj,
          pshRelEdgeSpan,
          pshRelFstProj, pshRelSndProj,
          Subfunctor.toFunctor,
          pshProdLift,
          FunctorToTypes.prod.lift,
          FunctorToTypes.prod]
        apply Prod.ext
        · have := congr_fun
            ((F.map
              (WidePushoutShape.Hom.init
                WalkingPair.left)).naturality
              f) r
          dsimp [types_comp_apply,
            pshProdPresheaf] at this ⊢
          exact this
        · have := congr_fun
            ((F.map
              (WidePushoutShape.Hom.init
                WalkingPair.right)).naturality
              f) r
          dsimp [types_comp_apply,
            pshProdPresheaf] at this ⊢
          exact this }
    (𝟙 _)
    (𝟙 _)
    (by ext c r; rfl)
    (by ext c r; rfl)

/-- The counit of the adjunction: the canonical
map from the separated version of an edge back
to the edge. The vertices are the identity; at
the relation level, an element `(p, q)` in the
image of `R.toFunctor -> P x Q` is sent back to
its witness `(p, q) in R`. -/
def pshRelEdgeSepCounit
    (E : PshRelEdge.{u, v, w} C) :
    (pshRelEdgeSepFunctor C).obj
      ((pshRelEdgeInclusionFunctor.{u, v, w}
        C).obj E) ⟶ E :=
  { srcMap := 𝟙 _
    tgtMap := 𝟙 _
    sq := by
      intro c p q ⟨⟨⟨p', q'⟩, hpq'⟩, himg⟩
      dsimp [pshRelEdgeInclusionFunctor,
        pshRelEdgeSpan,
        pshRelFstProj, pshRelSndProj,
        pshProdLift,
        FunctorToTypes.prod.lift] at himg
      have hp := congr_arg Prod.fst himg
      have hq := congr_arg Prod.snd himg
      dsimp at hp hq
      rw [← hp, ← hq]
      exact hpq' }

/-- The unit of the separation-inclusion adjunction
as a natural transformation. -/
def pshRelEdgeSepAdjUnit (C : Type u)
    [Category.{v} C] :
    𝟭 (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) ⟶
    (pshRelEdgeSepFunctor C) ⋙
      (pshRelEdgeInclusionFunctor.{u, v, w}
        C) where
  app F := pshRelEdgeSepUnit F
  naturality F G h := by
    apply NatTrans.ext; funext j
    match j with
    | .none =>
      ext c r; apply Subtype.ext
      dsimp [pshRelEdgeSepFunctor,
        pshRelEdgeInclusionFunctor,
        pshRelEdgeSepUnit, pshRelEdgeSepMap,
        pshRelEdgeSpanMap,
        pshRelRelatedTotalMap,
        pshRelEdgeSepObj, pshRelEdgeSpan,
        pshProdLift,
        FunctorToTypes.prod.lift,
        spanHomMk]
      apply Prod.ext
      · have := congr_fun (congr_app
          (h.naturality
            (WidePushoutShape.Hom.init
              WalkingPair.left)) c) r
        dsimp [types_comp_apply] at this
        exact this.symm
      · have := congr_fun (congr_app
          (h.naturality
            (WidePushoutShape.Hom.init
              WalkingPair.right)) c) r
        dsimp [types_comp_apply] at this
        exact this.symm
    | .some .left =>
      dsimp [pshRelEdgeSepUnit,
        pshRelEdgeInclusionFunctor,
        pshRelEdgeSepFunctor,
        pshRelEdgeSpanMap,
        pshRelEdgeSepMap, spanHomMk]
      simp [Category.id_comp,
        Category.comp_id]
    | .some .right =>
      dsimp [pshRelEdgeSepUnit,
        pshRelEdgeInclusionFunctor,
        pshRelEdgeSepFunctor,
        pshRelEdgeSpanMap,
        pshRelEdgeSepMap, spanHomMk]
      simp [Category.id_comp,
        Category.comp_id]

/-- The counit of the separation-inclusion
adjunction as a natural transformation. -/
def pshRelEdgeSepAdjCounit (C : Type u)
    [Category.{v} C] :
    (pshRelEdgeInclusionFunctor.{u, v, w}
      C) ⋙ (pshRelEdgeSepFunctor C) ⟶
    𝟭 (PshRelEdge.{u, v, w} C) where
  app E := pshRelEdgeSepCounit E
  naturality E E' h := by
    apply VertEdgeHom.ext <;>
    · dsimp only [pshRelEdgeSepCounit,
        pshRelEdgeSepFunctor,
        pshRelEdgeSepMap,
        pshRelEdgeInclusionFunctor,
        pshRelEdgeSpanMap,
        pshRelEdgeCategory, vertEdgeCategory,
        pshRelDoubleData, pshRelDoubleOps,
        CategoryStruct.comp, spanHomMk,
        Functor.comp_map, Functor.id_map,
        NatTrans.vcomp,
        pshRelEdgeSepObj, pshRelEdgeSpan]
      ext; dsimp

/-- The separation-inclusion adjunction:
`pshRelEdgeSepFunctor ⊣ pshRelEdgeInclusionFunctor`.
This exhibits `PshRelEdge C` as a reflective
subcategory of `WalkingSpan ⥤ PSh(C)`. -/
def pshRelEdgeSepAdjunction (C : Type u)
    [Category.{v} C] :
    pshRelEdgeSepFunctor.{u, v, w} C ⊣
    pshRelEdgeInclusionFunctor.{u, v, w} C :=
  Adjunction.mkOfUnitCounit {
    unit := pshRelEdgeSepAdjUnit C
    counit := pshRelEdgeSepAdjCounit C
    left_triangle := by
      ext E; apply VertEdgeHom.ext <;>
      · ext x a; rfl
    right_triangle := by
      ext F j c x
      match j with
      | .none => apply Subtype.ext; rfl
      | .some .left => rfl
      | .some .right => rfl
  }

end GebLean
