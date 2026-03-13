import GebLean.PshRelEdgeLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Closed.Ideal
import Mathlib.CategoryTheory.Monad.Limits

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

instance pshRelEdgeInclusionFull (C : Type u)
    [Category.{v} C] :
    (pshRelEdgeInclusionFunctor.{u, v, w}
      C).Full :=
  (pshRelEdgeInclusionFullyFaithful C).full

instance pshRelEdgeInclusionFaithful
    (C : Type u) [Category.{v} C] :
    (pshRelEdgeInclusionFunctor.{u, v, w}
      C).Faithful :=
  (pshRelEdgeInclusionFullyFaithful C).faithful

instance pshRelEdgeInclusionReflective
    (C : Type u) [Category.{v} C] :
    Reflective
      (pshRelEdgeInclusionFunctor.{u, v, w}
        C) where
  L := pshRelEdgeSepFunctor C
  adj := pshRelEdgeSepAdjunction C

section SepPreservesProducts

variable (F G : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))

/-- The pointwise product of two span functors
in `[WalkingSpan, PSh(C)]`. -/
def spanProd :
    WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w) where
  obj j := pshProdPresheaf (F.obj j) (G.obj j)
  map f := pshProdMap (F.map f) (G.map f)
  map_id j := by simp [pshProdMap_id]
  map_comp f g := by
    simp [pshProdMap_comp]

/-- First projection from the pointwise product
to the first factor. -/
def spanProdFst :
    spanProd F G ⟶ F where
  app j := pshProdFst (F.obj j) (G.obj j)
  naturality j j' f := by ext c ⟨x, y⟩; rfl

/-- Second projection from the pointwise product
to the second factor. -/
def spanProdSnd :
    spanProd F G ⟶ G where
  app j := pshProdSnd (F.obj j) (G.obj j)
  naturality j j' f := by ext c ⟨x, y⟩; rfl

end SepPreservesProducts

instance pshRelEdgeSepCounitIsIso
    (C : Type u) [Category.{v} C] :
    IsIso
      (pshRelEdgeSepAdjunction.{u, v, w}
        C).counit :=
  (pshRelEdgeSepAdjunction C
    ).counit_isIso_of_R_fully_faithful

section SepPreservesProducts2

variable {C : Type u} [Category.{v} C]

/-- Pointwise pairing: given natural
transformations `H ⟶ F` and `H ⟶ G` in
`[WalkingSpan, PSh(C)]`, produce `H ⟶ spanProd
F G` by pairing at each vertex. -/
def spanProdLift
    {F G H : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)}
    (α : H ⟶ F) (β : H ⟶ G) :
    H ⟶ spanProd F G where
  app j := pshProdLift (α.app j) (β.app j)
  naturality j j' f := by
    apply pshProdPresheaf_hom_ext
    · simp only [Category.assoc, spanProd,
        pshProdMap_fst]
      simp only [← Category.assoc,
        pshProdLift, FunctorToTypes.prod.lift,
        pshProdFst, FunctorToTypes.prod.fst]
      exact α.naturality f
    · simp only [Category.assoc, spanProd,
        pshProdMap_snd]
      simp only [← Category.assoc,
        pshProdLift, FunctorToTypes.prod.lift,
        pshProdSnd, FunctorToTypes.prod.snd]
      exact β.naturality f

/-- The cone for `Discrete.functor f` in
`[WalkingSpan, PSh(C)]` given by the pointwise
product. -/
def spanProdCone
    (f : WalkingPair →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    Cone (Discrete.functor f) where
  pt := spanProd (f .left) (f .right)
  π := Discrete.natTrans (fun ⟨i⟩ =>
    match i with
    | .left => spanProdFst (f .left) (f .right)
    | .right => spanProdSnd (f .left) (f .right))

/-- The pointwise product cone is a limit in
`[WalkingSpan, PSh(C)]`. -/
def spanProdIsLimit
    (f : WalkingPair →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    IsLimit (spanProdCone f) where
  lift s := spanProdLift
    (s.π.app ⟨.left⟩) (s.π.app ⟨.right⟩)
  fac s j := by
    match j with
    | ⟨.left⟩ => ext k c x; rfl
    | ⟨.right⟩ => ext k c x; rfl
  uniq s m hm := by
    have h₁ := hm ⟨.left⟩
    have h₂ := hm ⟨.right⟩
    ext j c x
    apply Prod.ext
    · have := congr_fun (congr_app
        (congr_app h₁ j) c) x
      dsimp [spanProdCone, spanProdFst,
        Discrete.natTrans] at this
      dsimp [spanProdLift, pshProdLift,
        FunctorToTypes.prod.lift,
        pshProdFst, FunctorToTypes.prod.fst]
      exact this
    · have := congr_fun (congr_app
        (congr_app h₂ j) c) x
      dsimp [spanProdCone, spanProdSnd,
        Discrete.natTrans] at this
      dsimp [spanProdLift, pshProdLift,
        FunctorToTypes.prod.lift,
        pshProdSnd, FunctorToTypes.prod.snd]
      exact this

/-- The lift for the mapped cone: given a cone
over `Discrete.functor f ⋙ sep` in `PshRelEdge
C`, construct a morphism to `sep(spanProd)`. -/
def sepMapSpanProdLift
    (f : WalkingPair →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)))
    (s : Cone (Discrete.functor f ⋙
      pshRelEdgeSepFunctor.{u, v, w} C)) :
    s.pt ⟶
    (pshRelEdgeSepFunctor C).obj
      (spanProd (f .left) (f .right)) :=
  { srcMap := pshProdLift
      (s.π.app ⟨.left⟩).srcMap
      (s.π.app ⟨.right⟩).srcMap
    tgtMap := pshProdLift
      (s.π.app ⟨.left⟩).tgtMap
      (s.π.app ⟨.right⟩).tgtMap
    sq := by
      intro c p q hpq
      obtain ⟨r₁, hr₁⟩ :=
        (s.π.app ⟨.left⟩).sq c p q hpq
      obtain ⟨r₂, hr₂⟩ :=
        (s.π.app ⟨.right⟩).sq c p q hpq
      dsimp [pshRelEdgeSepFunctor,
        pshRelEdgeSepObj, Subfunctor.range,
        pshProdLift,
        FunctorToTypes.prod.lift] at hr₁ hr₂
      have h₁₁ := congr_arg Prod.fst hr₁
      have h₁₂ := congr_arg Prod.snd hr₁
      have h₂₁ := congr_arg Prod.fst hr₂
      have h₂₂ := congr_arg Prod.snd hr₂
      dsimp at h₁₁ h₁₂ h₂₁ h₂₂
      dsimp [pshRelEdgeSepFunctor,
        pshRelEdgeSepObj, Subfunctor.range]
      refine ⟨(r₁, r₂), ?_⟩
      dsimp [spanProd, pshProdMap,
        pshProdLift,
        FunctorToTypes.prod.lift,
        pshProdFst, FunctorToTypes.prod.fst,
        pshProdSnd, FunctorToTypes.prod.snd]
      exact Prod.ext
        (Prod.ext h₁₁ h₂₁)
        (Prod.ext h₁₂ h₂₂)
  }

/-- The image of the pointwise product cone
under `sep` is a limit in `PshRelEdge C`. -/
def sepMapSpanProdIsLimit
    (f : WalkingPair →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    IsLimit ((pshRelEdgeSepFunctor.{u, v, w}
      C).mapCone (spanProdCone f)) where
  lift s := sepMapSpanProdLift f s
  fac s j := by
    match j with
    | ⟨.left⟩ =>
      apply VertEdgeHom.ext <;>
      · ext c x; rfl
    | ⟨.right⟩ =>
      apply VertEdgeHom.ext <;>
      · ext c x; rfl
  uniq s m hm := by
    have h₁ := hm ⟨.left⟩
    have h₂ := hm ⟨.right⟩
    apply VertEdgeHom.ext
    · apply pshProdPresheaf_hom_ext
      · have : m.srcMap ≫
            pshProdFst _ _ =
          (s.π.app ⟨.left⟩).srcMap := by
          have := congr_arg VertEdgeHom.srcMap h₁
          dsimp [Functor.mapCone, spanProdCone,
            pshRelEdgeSepFunctor,
            pshRelEdgeSepMap,
            Discrete.natTrans] at this
          exact this
        dsimp [sepMapSpanProdLift]
        rw [← this]
      · have : m.srcMap ≫
            pshProdSnd _ _ =
          (s.π.app ⟨.right⟩).srcMap := by
          have := congr_arg VertEdgeHom.srcMap h₂
          dsimp [Functor.mapCone, spanProdCone,
            pshRelEdgeSepFunctor,
            pshRelEdgeSepMap,
            Discrete.natTrans] at this
          exact this
        dsimp [sepMapSpanProdLift]
        rw [← this]
    · apply pshProdPresheaf_hom_ext
      · have : m.tgtMap ≫
            pshProdFst _ _ =
          (s.π.app ⟨.left⟩).tgtMap := by
          have := congr_arg VertEdgeHom.tgtMap h₁
          dsimp [Functor.mapCone, spanProdCone,
            pshRelEdgeSepFunctor,
            pshRelEdgeSepMap,
            Discrete.natTrans] at this
          exact this
        dsimp [sepMapSpanProdLift]
        rw [← this]
      · have : m.tgtMap ≫
            pshProdSnd _ _ =
          (s.π.app ⟨.right⟩).tgtMap := by
          have := congr_arg VertEdgeHom.tgtMap h₂
          dsimp [Functor.mapCone, spanProdCone,
            pshRelEdgeSepFunctor,
            pshRelEdgeSepMap,
            Discrete.natTrans] at this
          exact this
        dsimp [sepMapSpanProdLift]
        rw [← this]

instance pshRelEdgeSepPreservesProduct
    (f : WalkingPair →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    PreservesLimit (Discrete.functor f)
      (pshRelEdgeSepFunctor.{u, v, w} C) :=
  preservesLimit_of_preserves_limit_cone
    (spanProdIsLimit f)
    (sepMapSpanProdIsLimit f)

instance pshRelEdgeSepPreservesBinaryProducts
    (C : Type u) [Category.{v} C] :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (pshRelEdgeSepFunctor.{u, v, w} C) :=
  preservesLimitsOfShape_of_discrete _

/-- The constant span at the unit presheaf,
serving as a terminal object in
`WalkingSpan ⥤ PSh(C)`. -/
def spanTerminal :
    WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w) :=
  (Functor.const _).obj (pshUnitPresheaf C)

/-- The unique morphism from any span to the
terminal span. -/
def spanTerminalMap
    (F : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :
    F ⟶ spanTerminal (C := C) where
  app _ := pshUnitMap _

/-- The cone for `Discrete.functor f` in
`[WalkingSpan, PSh(C)]` for
`f : PEmpty → ...`, given by the terminal span.
-/
def spanTerminalCone
    (f : PEmpty →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    Cone (Discrete.functor f) where
  pt := spanTerminal (C := C)
  π := Discrete.natTrans (fun ⟨i⟩ => i.elim)

/-- The terminal cone is a limit for the empty
diagram. -/
def spanTerminalIsLimit
    (f : PEmpty →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    IsLimit (spanTerminalCone (C := C) f) where
  lift s := spanTerminalMap s.pt
  fac _ j := j.as.elim
  uniq s m _ := by
    ext j c x
    match j with
    | .none =>
      exact ULift.ext _ _
        (Subsingleton.elim _ _)
    | .some .left =>
      exact ULift.ext _ _
        (Subsingleton.elim _ _)
    | .some .right =>
      exact ULift.ext _ _
        (Subsingleton.elim _ _)

/-- The `sep` image of the terminal cone is a
limit for the empty diagram in `PshRelEdge C`.
-/
def sepMapSpanTerminalIsLimit
    (f : PEmpty →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    IsLimit ((pshRelEdgeSepFunctor.{u, v, w}
      C).mapCone (spanTerminalCone f)) where
  lift s :=
    { srcMap := pshUnitMap s.pt.src
      tgtMap := pshUnitMap s.pt.tgt
      sq := by
        intro c _ _ _
        dsimp [pshRelEdgeSepFunctor,
          pshRelEdgeSepObj, Subfunctor.range,
          spanTerminal, pshProdLift,
          FunctorToTypes.prod.lift,
          pshUnitPresheaf]
        exact ⟨⟨PUnit.unit⟩, rfl⟩ }
  fac _ j := j.as.elim
  uniq _ m _ := by
    apply VertEdgeHom.ext <;>
    · ext c x
      exact ULift.ext _ _
        (Subsingleton.elim _ _)

instance pshRelEdgeSepPreservesTerminalProduct
    (f : PEmpty →
      (WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))) :
    PreservesLimit (Discrete.functor f)
      (pshRelEdgeSepFunctor.{u, v, w} C) :=
  preservesLimit_of_preserves_limit_cone
    (spanTerminalIsLimit f)
    (sepMapSpanTerminalIsLimit f)

instance pshRelEdgeSepPreservesTerminal
    (C : Type u) [Category.{v} C] :
    PreservesLimitsOfShape (Discrete PEmpty)
      (pshRelEdgeSepFunctor.{u, v, w} C) :=
  preservesLimitsOfShape_of_discrete _

instance pshRelEdgeSepPreservesFiniteProducts
    (C : Type u) [Category.{v} C] :
    PreservesFiniteProducts
      (pshRelEdgeSepFunctor.{u, v, w} C) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

instance pshRelEdgeReflectorPreservesBinaryProducts
    (C : Type u) [Category.{v} C] :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (reflector
        (pshRelEdgeInclusionFunctor.{u, v, w}
          C)) :=
  pshRelEdgeSepPreservesBinaryProducts C

def pshRelEdgeTerminalLimitCone
    (C : Type u) [Category.{v} C] :
    LimitCone
      (Functor.empty.{0}
        (PshRelEdge.{u, v, w} C)) where
  cone :=
    { pt := pshRelEdgeTerminal C
      π := (Functor.uniqueFromEmpty _).hom }
  isLimit :=
    { lift := fun s =>
        pshRelEdgeTerminalMap s.pt
      fac := fun _ => by rintro ⟨⟨⟩⟩ }

def pshRelEdgeProdLimitCone
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    LimitCone (pair E₁ E₂) where
  cone := BinaryFan.mk
    (pshRelEdgeProdFst E₁ E₂)
    (pshRelEdgeProdSnd E₁ E₂)
  isLimit := pshRelEdgeProdIsLimit E₁ E₂

instance pshRelEdgeCartesianMonoidal
    (C : Type u) [Category.{v} C] :
    CartesianMonoidalCategory
      (PshRelEdge.{u, v, w} C) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    (pshRelEdgeTerminalLimitCone C)
    (pshRelEdgeProdLimitCone)

instance pshRelEdgeExponentialIdeal
    (C : Type u) [Category.{v} C] :
    ExponentialIdeal
      (pshRelEdgeInclusionFunctor.{u, v, max v u}
        C) :=
  exponentialIdeal_of_preservesBinaryProducts _

end SepPreservesProducts2

section InclusionPreservesCoproducts

variable {C : Type u} [Category.{v} C]

/-- The subfunctor total space of a coproduct
relation is the coproduct of the total spaces.
This is the natural isomorphism witnessing that
`(R₁ ⊕ R₂).toFunctor ≅ R₁.toFunctor ⊕ R₂.toFunctor`
where ⊕ is the coproduct presheaf. -/
private def pshRelCoprodToFunctorFwdAux
    {P₁ Q₁ P₂ Q₂ : Cᵒᵖ ⥤ Type w}
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂)
    (c : Cᵒᵖ)
    (p : P₁.obj c ⊕ P₂.obj c)
    (q : Q₁.obj c ⊕ Q₂.obj c)
    (h : (p, q) ∈ (pshRelCoprod R₁ R₂).obj c) :
    R₁.toFunctor.obj c ⊕
      R₂.toFunctor.obj c :=
  match p, q, h with
  | Sum.inl p₁, Sum.inl q₁, h =>
    Sum.inl ⟨(p₁, q₁), h⟩
  | Sum.inr p₂, Sum.inr q₂, h =>
    Sum.inr ⟨(p₂, q₂), h⟩
  | Sum.inl _, Sum.inr _, h =>
    False.elim h
  | Sum.inr _, Sum.inl _, h =>
    False.elim h

def pshRelCoprodToFunctorFwd
    {P₁ Q₁ P₂ Q₂ : Cᵒᵖ ⥤ Type w}
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    (pshRelCoprod R₁ R₂).toFunctor ⟶
      pshCoprodPresheaf
        R₁.toFunctor R₂.toFunctor where
  app c x :=
    pshRelCoprodToFunctorFwdAux
      R₁ R₂ c x.val.1 x.val.2 x.prop
  naturality {c d} f := by
    ext ⟨⟨p, q⟩, h⟩
    dsimp [pshRelCoprodToFunctorFwdAux]
    match p, q, h with
    | Sum.inl _, Sum.inl _, _ => rfl
    | Sum.inr _, Sum.inr _, _ => rfl
    | Sum.inl _, Sum.inr _, h =>
      exact False.elim h
    | Sum.inr _, Sum.inl _, h =>
      exact False.elim h

def pshRelCoprodToFunctorBwd
    {P₁ Q₁ P₂ Q₂ : Cᵒᵖ ⥤ Type w}
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    pshCoprodPresheaf
      R₁.toFunctor R₂.toFunctor ⟶
      (pshRelCoprod R₁ R₂).toFunctor where
  app c x :=
    match x with
    | Sum.inl ⟨(p₁, q₁), h⟩ =>
      ⟨(Sum.inl p₁, Sum.inl q₁), h⟩
    | Sum.inr ⟨(p₂, q₂), h⟩ =>
      ⟨(Sum.inr p₂, Sum.inr q₂), h⟩
  naturality {c d} f := by
    ext (⟨⟨_, _⟩, _⟩ | ⟨⟨_, _⟩, _⟩) <;> rfl

def pshCoprodIsColimit
    (P Q : Cᵒᵖ ⥤ Type w) :
    IsColimit (BinaryCofan.mk
      (pshCoprodInl P Q)
      (pshCoprodInr P Q)) :=
  BinaryCofan.isColimitMk
    (fun s => pshCoprodDesc s.inl s.inr)
    (fun s => by ext c p; rfl)
    (fun s => by ext c p; rfl)
    (fun s m h₁ h₂ => by
      ext c (p | p)
      · exact congrFun
          (congr_fun (congrArg NatTrans.app h₁)
            c) p
      · exact congrFun
          (congr_fun (congrArg NatTrans.app h₂)
            c) p)

def pshRelCoprodToFunctorIso
    {P₁ Q₁ P₂ Q₂ : Cᵒᵖ ⥤ Type w}
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    (pshRelCoprod R₁ R₂).toFunctor ≅
      pshCoprodPresheaf
        R₁.toFunctor R₂.toFunctor where
  hom := pshRelCoprodToFunctorFwd R₁ R₂
  inv := pshRelCoprodToFunctorBwd R₁ R₂
  hom_inv_id := by
    ext c ⟨⟨p, q⟩, h⟩
    dsimp [pshRelCoprodToFunctorFwd,
      pshRelCoprodToFunctorFwdAux,
      pshRelCoprodToFunctorBwd]
    match p, q, h with
    | Sum.inl _, Sum.inl _, _ => rfl
    | Sum.inr _, Sum.inr _, _ => rfl
    | Sum.inl _, Sum.inr _, h =>
      exact False.elim h
    | Sum.inr _, Sum.inl _, h =>
      exact False.elim h
  inv_hom_id := by
    ext c (⟨⟨_, _⟩, _⟩ | ⟨⟨_, _⟩, _⟩) <;> rfl

private def inclusionCoprodDesc
    (E₁ E₂ : PshRelEdge.{u, v, w} C)
    (s : Cocone (pair E₁ E₂ ⋙
      pshRelEdgeInclusionFunctor C)) :
    (pshRelEdgeInclusionFunctor C).obj
      (pshRelEdgeCoprod E₁ E₂) ⟶ s.pt where
  app j :=
    match j with
    | .some .left => pshCoprodDesc
        ((s.ι.app ⟨.left⟩).app
          (.some .left))
        ((s.ι.app ⟨.right⟩).app
          (.some .left))
    | .some .right => pshCoprodDesc
        ((s.ι.app ⟨.left⟩).app
          (.some .right))
        ((s.ι.app ⟨.right⟩).app
          (.some .right))
    | .none =>
        (pshRelCoprodToFunctorIso
          E₁.edge E₂.edge).hom ≫
        pshCoprodDesc
          ((s.ι.app ⟨.left⟩).app .none)
          ((s.ι.app ⟨.right⟩).app .none)
  naturality {j j'} f := by
    cases f with
    | id j =>
      erw [(pshRelEdgeSpan
        (pshRelEdgeCoprod E₁ E₂)).map_id j,
        Category.id_comp,
        s.pt.map_id j,
        Category.comp_id]
    | init b =>
      ext c ⟨⟨p, q⟩, h⟩
      match b, p, q, h with
      | .left, Sum.inl p₁, Sum.inl q₁, h =>
        change ((s.ι.app ⟨.left⟩).app
            (.some .left)).app c p₁ =
          (s.pt.map
            (WidePushoutShape.Hom.init
              .left)).app c
          (((s.ι.app ⟨.left⟩).app .none).app
            c ⟨(p₁, q₁), h⟩)
        have := congr_fun (congr_app
          ((s.ι.app ⟨.left⟩).naturality
            (WidePushoutShape.Hom.init
              .left)) c)
          ⟨(p₁, q₁), h⟩
        dsimp [types_comp_apply,
          pshRelEdgeSpan, span,
          WidePushoutShape.wideSpan,
          pshRelFstProj,
          Subfunctor.toFunctor] at this
        exact this
      | .left, Sum.inr p₂, Sum.inr q₂, h =>
        change ((s.ι.app ⟨.right⟩).app
            (.some .left)).app c p₂ =
          (s.pt.map
            (WidePushoutShape.Hom.init
              .left)).app c
          (((s.ι.app ⟨.right⟩).app .none).app
            c ⟨(p₂, q₂), h⟩)
        have := congr_fun (congr_app
          ((s.ι.app ⟨.right⟩).naturality
            (WidePushoutShape.Hom.init
              .left)) c)
          ⟨(p₂, q₂), h⟩
        dsimp [types_comp_apply,
          pshRelEdgeSpan, span,
          WidePushoutShape.wideSpan,
          pshRelFstProj,
          Subfunctor.toFunctor] at this
        exact this
      | .left, Sum.inl _, Sum.inr _, h =>
        exact False.elim h
      | .left, Sum.inr _, Sum.inl _, h =>
        exact False.elim h
      | .right, Sum.inl p₁, Sum.inl q₁, h =>
        change ((s.ι.app ⟨.left⟩).app
            (.some .right)).app c q₁ =
          (s.pt.map
            (WidePushoutShape.Hom.init
              .right)).app c
          (((s.ι.app ⟨.left⟩).app .none).app
            c ⟨(p₁, q₁), h⟩)
        have := congr_fun (congr_app
          ((s.ι.app ⟨.left⟩).naturality
            (WidePushoutShape.Hom.init
              .right)) c)
          ⟨(p₁, q₁), h⟩
        dsimp [types_comp_apply,
          pshRelEdgeSpan, span,
          WidePushoutShape.wideSpan,
          pshRelSndProj,
          Subfunctor.toFunctor] at this
        exact this
      | .right, Sum.inr p₂, Sum.inr q₂, h =>
        change ((s.ι.app ⟨.right⟩).app
            (.some .right)).app c q₂ =
          (s.pt.map
            (WidePushoutShape.Hom.init
              .right)).app c
          (((s.ι.app ⟨.right⟩).app .none).app
            c ⟨(p₂, q₂), h⟩)
        have := congr_fun (congr_app
          ((s.ι.app ⟨.right⟩).naturality
            (WidePushoutShape.Hom.init
              .right)) c)
          ⟨(p₂, q₂), h⟩
        dsimp [types_comp_apply,
          pshRelEdgeSpan, span,
          WidePushoutShape.wideSpan,
          pshRelSndProj,
          Subfunctor.toFunctor] at this
        exact this
      | .right, Sum.inl _, Sum.inr _, h =>
        exact False.elim h
      | .right, Sum.inr _, Sum.inl _, h =>
        exact False.elim h

def inclusionMapCoprodCoconeIsColimit
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    IsColimit
      ((pshRelEdgeInclusionFunctor C).mapCocone
        (BinaryCofan.mk
          (pshRelEdgeCoprodInl E₁ E₂)
          (pshRelEdgeCoprodInr E₁ E₂))) where
  desc s := inclusionCoprodDesc E₁ E₂ s
  fac s j := by
    apply NatTrans.ext; funext k
    match j, k with
    | ⟨.left⟩, .some .left => ext c p₁; rfl
    | ⟨.left⟩, .some .right => ext c q₁; rfl
    | ⟨.left⟩, .none => ext c ⟨⟨p₁, q₁⟩, h⟩; rfl
    | ⟨.right⟩, .some .left => ext c p₂; rfl
    | ⟨.right⟩, .some .right => ext c q₂; rfl
    | ⟨.right⟩, .none =>
      ext c ⟨⟨p₂, q₂⟩, h⟩; rfl
  uniq s m hm := by
    apply NatTrans.ext; funext k
    match k with
    | .some .left =>
      have h₁ := congr_fun
        (congr_arg NatTrans.app (hm ⟨.left⟩))
        (.some WalkingPair.left)
      have h₂ := congr_fun
        (congr_arg NatTrans.app (hm ⟨.right⟩))
        (.some WalkingPair.left)
      dsimp [Functor.mapCocone,
        pshRelEdgeInclusionFunctor,
        pshRelEdgeSpanMap, pshRelEdgeSpan,
        span, WidePushoutShape.wideSpan,
        inclusionCoprodDesc,
        pshRelEdgeCoprodInl,
        pshRelEdgeCoprodInr] at h₁ h₂ ⊢
      ext c (p | p)
      · exact congr_fun (congr_app h₁ c) p
      · exact congr_fun (congr_app h₂ c) p
    | .some .right =>
      have h₁ := congr_fun
        (congr_arg NatTrans.app (hm ⟨.left⟩))
        (.some WalkingPair.right)
      have h₂ := congr_fun
        (congr_arg NatTrans.app (hm ⟨.right⟩))
        (.some WalkingPair.right)
      dsimp [Functor.mapCocone,
        pshRelEdgeInclusionFunctor,
        pshRelEdgeSpanMap, pshRelEdgeSpan,
        span, WidePushoutShape.wideSpan,
        inclusionCoprodDesc,
        pshRelEdgeCoprodInl,
        pshRelEdgeCoprodInr] at h₁ h₂ ⊢
      ext c (p | p)
      · exact congr_fun (congr_app h₁ c) p
      · exact congr_fun (congr_app h₂ c) p
    | .none =>
      have h₁ := congr_fun
        (congr_arg NatTrans.app (hm ⟨.left⟩))
          (.none : WalkingSpan)
      have h₂ := congr_fun
        (congr_arg NatTrans.app (hm ⟨.right⟩))
          (.none : WalkingSpan)
      dsimp [Functor.mapCocone,
        pshRelEdgeInclusionFunctor,
        pshRelEdgeSpanMap, pshRelEdgeSpan,
        span, WidePushoutShape.wideSpan,
        pshRelRelatedTotalMap,
        inclusionCoprodDesc,
        pshRelCoprodToFunctorIso,
        pshRelCoprodToFunctorFwd,
        pshRelCoprodToFunctorFwdAux,
        pshRelEdgeCoprodInl,
        pshRelEdgeCoprodInr,
        pshCoprodInl, pshCoprodInr,
        pshCoprodDesc] at h₁ h₂ ⊢
      ext c ⟨⟨p, q⟩, h⟩
      match p, q, h with
      | Sum.inl p₁, Sum.inl q₁, h =>
        exact congr_fun (congr_app h₁ c)
          ⟨(p₁, q₁), h⟩
      | Sum.inr p₂, Sum.inr q₂, h =>
        exact congr_fun (congr_app h₂ c)
          ⟨(p₂, q₂), h⟩
      | Sum.inl _, Sum.inr _, h =>
        exact False.elim h
      | Sum.inr _, Sum.inl _, h =>
        exact False.elim h

instance inclusionPreservesColimitPairEdge
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    PreservesColimit (pair E₁ E₂)
      (pshRelEdgeInclusionFunctor C) :=
  preservesColimit_of_preserves_colimit_cocone
    (pshRelEdgeCoprodIsColimit E₁ E₂)
    (inclusionMapCoprodCoconeIsColimit E₁ E₂)

instance inclusionPreservesBinaryCoproducts
    (C : Type u) [Category.{v} C] :
    PreservesColimitsOfShape
      (Discrete WalkingPair)
      (pshRelEdgeInclusionFunctor.{u, v, w}
        C) where
  preservesColimit {F} := by
    haveI := inclusionPreservesColimitPairEdge
      (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)
    exact preservesColimit_of_iso_diagram _
      (diagramIsoPair F).symm

private def inclusionInitialMap
    (G : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :
    (pshRelEdgeInclusionFunctor C).obj
      (pshRelEdgeInitial C) ⟶ G where
  app j := match j with
    | .some .left =>
      pshEmptyMap (G.obj (.some .left))
    | .some .right =>
      pshEmptyMap (G.obj (.some .right))
    | .none =>
      { app := fun c x => (x.val.1.down).elim
        naturality := fun {_ _} _ => by
          ext ⟨⟨p, _⟩, _⟩; exact p.down.elim }
  naturality {j j'} f := by
    ext c x
    match j with
    | .some .left =>
      exact (x : ULift PEmpty).down.elim
    | .some .right =>
      exact (x : ULift PEmpty).down.elim
    | .none =>
      exact ((x : { pq : ULift PEmpty × _ //
        _ }).val.1.down).elim

instance inclusionPreservesInitialObj
    (C : Type u) [Category.{v} C] :
    PreservesColimit (Functor.empty.{0}
      (PshRelEdge.{u, v, w} C))
      (pshRelEdgeInclusionFunctor C) :=
  preservesColimit_of_preserves_colimit_cocone
    (pshRelEdgeIsInitial C)
    ((isColimitMapCoconeEmptyCoconeEquiv
      (pshRelEdgeInclusionFunctor C)
      (pshRelEdgeInitial C)).symm
      (IsInitial.ofUniqueHom
        (fun G => inclusionInitialMap G)
        (fun G f => by
          apply NatTrans.ext; funext j
          match j with
          | .some .left =>
            ext c (e : ULift PEmpty)
            exact e.down.elim
          | .some .right =>
            ext c (e : ULift PEmpty)
            exact e.down.elim
          | .none =>
            ext c ⟨⟨p, _⟩, _⟩
            exact p.down.elim)))

instance inclusionPreservesInitial
    (C : Type u) [Category.{v} C] :
    PreservesColimitsOfShape
      (Discrete PEmpty.{1})
      (pshRelEdgeInclusionFunctor.{u, v, w}
        C) :=
  preservesColimitsOfShape_pempty_of_preservesInitial
    _

end InclusionPreservesCoproducts

/-- `PshRelEdge C` has all small limits, inherited
from the ambient presheaf topos
`[WalkingSpan, PSh(C)]` via the reflective
embedding (the inclusion, being a right adjoint,
creates limits). -/
instance pshRelEdgeHasLimitsOfSize
    (C : Type u) [Category.{v} C] :
    HasLimitsOfSize.{w, w}
      (PshRelEdge.{u, v, w} C) :=
  hasLimits_of_reflective
    (pshRelEdgeInclusionFunctor C)

/-- `PshRelEdge C` has all small colimits: for a
diagram `D` in `PshRelEdge C`, the colimit is
`L(colim(ι ∘ D))` where `ι` is the inclusion
and `L = pshRelEdgeSepFunctor` is the reflector.
The universal property follows from the adjunction
`L ⊣ ι` and full faithfulness of `ι`. -/
instance pshRelEdgeHasColimitsOfSize
    (C : Type u) [Category.{v} C] :
    HasColimitsOfSize.{w, w}
      (PshRelEdge.{u, v, w} C) :=
  hasColimits_of_reflective
    (pshRelEdgeInclusionFunctor C)

end GebLean
