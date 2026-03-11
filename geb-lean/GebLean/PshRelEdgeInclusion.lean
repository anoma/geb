import GebLean.PshRelDouble
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

set_option autoImplicit false
set_option relaxedAutoImplicit false
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

end GebLean
