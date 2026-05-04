import GebLean.ComprehensiveFactorization
import GebLean.Weighted

namespace GebLean

open CategoryTheory

universe v u u₂ w

variable {C : Type u} [Category.{v} C]

section ProfPullbackCompatibility

variable {E : Type u₂} [Category.{v} E]
  {D : Type w} [Category.{v} D]

theorem profOnCoTwArr_profPullback
    (G : Cᵒᵖ ⥤ C ⥤ D) (F : E ⥤ C) :
    profunctorOnCoTwistedArrow E (profPullback G F) =
    coTwistedArrowMap F ⋙
      profunctorOnCoTwistedArrow C G := by
  exact _root_.CategoryTheory.Functor.ext
    (fun tw => rfl)

set_option backward.isDefEq.respectTransparency false in
theorem profOnTwArr_profPullback
    (G : Cᵒᵖ ⥤ C ⥤ D) (F : E ⥤ C) :
    profunctorOnTwistedArrow E (profPullback G F) =
    twistedArrowMap F ⋙
      profunctorOnTwistedArrow C G := by
  exact _root_.CategoryTheory.Functor.ext
    (fun tw => rfl)

end ProfPullbackCompatibility

section WeightedCoconeDiagramEq

variable {J : Type u₂} [Category.{v} J]
  {D : Type w} [Category.{v} D]

set_option backward.isDefEq.respectTransparency false in
theorem weightedCoconeDiagram_eq
    (W : Jᵒᵖ ⥤ Type v) (G : J ⥤ D) :
    weightedCoconeDiagram W G =
    elementsPre_π W ⋙ G := by
  exact _root_.CategoryTheory.Functor.ext
    (fun _ => rfl)

end WeightedCoconeDiagramEq

section ComprehensiveCoconeEquiv

variable {D : Type u₂} [Category.{v} D]
  (F : C ⥤ D)
  {E : Type w} [Category.{v} E]

set_option backward.isDefEq.respectTransparency false in
private theorem comprehensiveLiftLeg_wd
    (G : D ⥤ E)
    (s : Limits.Cocone (F ⋙ G))
    (d : D)
    (σ₁ σ₂ : StructuredArrow d F)
    (h : Zigzag σ₁ σ₂) :
    G.map σ₁.hom ≫ s.ι.app σ₁.right =
    G.map σ₂.hom ≫ s.ι.app σ₂.right := by
  induction h with
  | refl => rfl
  | tail _ h ih =>
    rw [ih]
    rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · rw [← StructuredArrow.w f, G.map_comp,
        Category.assoc, ← Functor.comp_map,
        s.w]
    · conv_lhs =>
        rw [← StructuredArrow.w f, G.map_comp,
          Category.assoc, ← Functor.comp_map,
          s.w]

set_option backward.isDefEq.respectTransparency false in
private theorem comprehensiveCoconeForward_nat
    (G : D ⥤ E)
    (s : Limits.Cocone (F ⋙ G))
    (d₁ d₂ : D) (f : d₁ ⟶ d₂)
    (q : ConnectedComponents
      (StructuredArrow d₂ F)) :
    G.map f ≫
      Quotient.lift
        (fun σ : StructuredArrow d₂ F =>
          G.map σ.hom ≫ s.ι.app σ.right)
        (comprehensiveLiftLeg_wd F G s d₂) q =
    Quotient.lift
      (fun σ : StructuredArrow d₁ F =>
        G.map σ.hom ≫ s.ι.app σ.right)
      (comprehensiveLiftLeg_wd F G s d₁)
      (Functor.mapConnectedComponents
        (StructuredArrow.map f) q) := by
  refine Quotient.inductionOn q (fun σ => ?_)
  simp only [Functor.mapConnectedComponents_mk,
    Quotient.lift_mk]
  simp only [StructuredArrow.map,
    Comma.mapLeft_obj_hom,
    Comma.mapLeft_obj_right,
    Functor.const_map_app,
    ← G.map_comp_assoc]

def comprehensiveCoconeForward
    (G : D ⥤ E)
    (s : Limits.Cocone (F ⋙ G)) :
    Limits.Cocone (comprehensiveM F ⋙ G) where
  pt := s.pt
  ι := {
    app := fun e =>
      Quotient.lift
        (fun σ : StructuredArrow e.unop.fst.unop F =>
          G.map σ.hom ≫ s.ι.app σ.right)
        (comprehensiveLiftLeg_wd F G s
          e.unop.fst.unop)
        e.unop.snd
    naturality := by
      intro e₁ e₂ m
      simp only [Functor.const_obj_map,
        Functor.comp_map, elementsPre_π_map]
      erw [Category.comp_id]
      erw [comprehensiveCoconeForward_nat]
      congr 1
      exact m.unop.property }

def comprehensiveCoconeBackward
    (G : D ⥤ E)
    (t : Limits.Cocone (comprehensiveM F ⋙ G)) :
    Limits.Cocone (F ⋙ G) where
  pt := t.pt
  ι := {
    app := fun c => t.ι.app ((comprehensiveE F).obj c)
    naturality := by
      intro c₁ c₂ f
      simp only [Functor.const_obj_map,
        Functor.comp_map]
      erw [Category.comp_id]
      rw [← t.w ((comprehensiveE F).map f)]
      congr 1 }

theorem comprehensiveCocone_backward_forward
    (G : D ⥤ E)
    (s : Limits.Cocone (F ⋙ G)) :
    comprehensiveCoconeBackward F G
      (comprehensiveCoconeForward F G s) = s := by
  change Limits.Cocone.mk s.pt _ = s
  cases s
  congr 1
  ext c
  simp only [comprehensiveCoconeForward,
    comprehensiveE, Quotient.lift_mk]
  dsimp
  simp only [G.map_id, Category.id_comp]

private theorem comprehensiveCocone_fwdbwd_leg
    (G : D ⥤ E)
    {pt : E}
    (ι : comprehensiveM F ⋙ G ⟶
      (Functor.const
        (comprehensivePresheaf F).ElementsPre).obj pt)
    (d : D)
    (q : ConnectedComponents (StructuredArrow d F))
    (hw : ∀ (σ₁ σ₂ : StructuredArrow d F),
      Zigzag σ₁ σ₂ →
      G.map σ₁.hom ≫
        ι.app ((comprehensiveE F).obj σ₁.right) =
      G.map σ₂.hom ≫
        ι.app ((comprehensiveE F).obj σ₂.right)) :
    Quotient.lift
      (fun σ : StructuredArrow d F =>
        G.map σ.hom ≫
          ι.app ((comprehensiveE F).obj σ.right))
      hw q =
    ι.app (Opposite.op ⟨Opposite.op d, q⟩) := by
  refine Quotient.inductionOn q (fun σ => ?_)
  simp only [Quotient.lift_mk]
  let m :
      (Opposite.op
        ⟨Opposite.op d,
          ⟦σ⟧⟩ :
        (comprehensivePresheaf F).ElementsPre) ⟶
      (comprehensiveE F).obj σ.right :=
    Quiver.Hom.op
      ⟨σ.hom.op, by
        simp only [comprehensivePresheaf_map,
          Functor.mapConnectedComponents_mk,
          StructuredArrow.map_mk, Category.comp_id]
        exact Quotient.sound
          (Zigzag.of_inv
            (StructuredArrow.eta σ).hom)⟩
  have nat := ι.naturality m
  simp only [Functor.const_obj_map] at nat
  erw [Category.comp_id] at nat
  simp only [Functor.comp_map,
    elementsPre_π_map] at nat
  convert nat using 2

theorem comprehensiveCocone_forward_backward
    (G : D ⥤ E)
    (t : Limits.Cocone (comprehensiveM F ⋙ G)) :
    comprehensiveCoconeForward F G
      (comprehensiveCoconeBackward F G t) = t := by
  change Limits.Cocone.mk t.pt _ = t
  cases t with | mk pt ι =>
  congr 1
  ext e
  simp only [comprehensiveCoconeBackward]
  exact comprehensiveCocone_fwdbwd_leg F G ι
    e.unop.fst.unop e.unop.snd _

def comprehensiveCoconeEquiv
    (G : D ⥤ E) :
    Limits.Cocone (F ⋙ G) ≃
    Limits.Cocone (comprehensiveM F ⋙ G) where
  toFun := comprehensiveCoconeForward F G
  invFun := comprehensiveCoconeBackward F G
  left_inv := comprehensiveCocone_backward_forward F G
  right_inv := comprehensiveCocone_forward_backward F G

set_option backward.isDefEq.respectTransparency false in
def comprehensiveCoconeForwardFunctor
    (G : D ⥤ E) :
    Limits.Cocone (F ⋙ G) ⥤
    Limits.Cocone (comprehensiveM F ⋙ G) where
  obj := comprehensiveCoconeForward F G
  map {s₁ s₂} f := {
    hom := f.hom
    w := by
      intro e
      simp only [comprehensiveCoconeForward]
      refine Quotient.inductionOn e.unop.snd
        (fun σ => ?_)
      simp only [Quotient.lift_mk, Category.assoc]
      rw [← f.w σ.right] }

def comprehensiveCoconeBackwardFunctor
    (G : D ⥤ E) :
    Limits.Cocone (comprehensiveM F ⋙ G) ⥤
    Limits.Cocone (F ⋙ G) where
  obj := comprehensiveCoconeBackward F G
  map {t₁ t₂} g := {
    hom := g.hom
    w := fun c => by
      simp only [comprehensiveCoconeBackward]
      exact g.w ((comprehensiveE F).obj c) }

set_option backward.isDefEq.respectTransparency false in
def comprehensiveCoconeEquivalence
    (G : D ⥤ E) :
    Limits.Cocone (F ⋙ G) ≌
    Limits.Cocone (comprehensiveM F ⋙ G) where
  functor := comprehensiveCoconeForwardFunctor F G
  inverse := comprehensiveCoconeBackwardFunctor F G
  unitIso := NatIso.ofComponents
    (fun s => eqToIso
      (comprehensiveCocone_backward_forward
        F G s).symm)
    (fun f => by
      apply Limits.CoconeMorphism.ext
      simp only [Limits.Cocone.category_comp_hom,
        GebLean.Cocone.eqToHom_hom, eqToIso.hom,
        eqToHom_refl, Category.id_comp,
        Category.comp_id,
        comprehensiveCoconeForwardFunctor,
        comprehensiveCoconeBackwardFunctor]
      rfl)
  counitIso := NatIso.ofComponents
    (fun t => eqToIso
      (comprehensiveCocone_forward_backward
        F G t))
    (fun g => by
      apply Limits.CoconeMorphism.ext
      simp only [Limits.Cocone.category_comp_hom,
        GebLean.Cocone.eqToHom_hom, eqToIso.hom,
        eqToHom_refl, Category.id_comp,
        Category.comp_id,
        comprehensiveCoconeForwardFunctor,
        comprehensiveCoconeBackwardFunctor]
      rfl)
  functor_unitIso_comp s := by
    apply Limits.CoconeMorphism.ext
    simp only [Limits.Cocone.category_comp_hom,
      Limits.Cocone.category_id_hom,
      GebLean.Cocone.eqToHom_hom, eqToIso.hom,
      NatIso.ofComponents, Functor.id_obj,
      comprehensiveCoconeForwardFunctor,
      comprehensiveCoconeForward,
      eqToHom_refl, Category.comp_id]

end ComprehensiveCoconeEquiv

section ComprehensiveConeEquiv

variable {D : Type u₂} [Category.{v} D]
  (F : C ⥤ D)
  {E : Type w} [Category.{v} E]

set_option backward.isDefEq.respectTransparency false in
private theorem comprehensiveLiftLeg_wd'
    (G : D ⥤ E)
    (s : Limits.Cone (F ⋙ G))
    (d : D)
    (τ₁ τ₂ : CostructuredArrow F d)
    (h : Zigzag τ₁ τ₂) :
    s.π.app τ₁.left ≫ G.map τ₁.hom =
    s.π.app τ₂.left ≫ G.map τ₂.hom := by
  induction h with
  | refl => rfl
  | tail _ h ih =>
    rw [ih]
    rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · rw [← CostructuredArrow.w f, G.map_comp,
        ← Category.assoc, ← Functor.comp_map,
        s.w]
    · conv_rhs =>
        rw [← CostructuredArrow.w f, G.map_comp,
          ← Category.assoc, ← Functor.comp_map,
          s.w]

set_option backward.isDefEq.respectTransparency false in
private theorem comprehensiveConeForward_nat
    (G : D ⥤ E)
    (s : Limits.Cone (F ⋙ G))
    (d₁ d₂ : D) (f : d₁ ⟶ d₂)
    (q : ConnectedComponents
      (CostructuredArrow F d₁)) :
    Quotient.lift
      (fun τ : CostructuredArrow F d₁ =>
        s.π.app τ.left ≫ G.map τ.hom)
      (comprehensiveLiftLeg_wd' F G s d₁) q ≫
    G.map f =
    Quotient.lift
      (fun τ : CostructuredArrow F d₂ =>
        s.π.app τ.left ≫ G.map τ.hom)
      (comprehensiveLiftLeg_wd' F G s d₂)
      (Functor.mapConnectedComponents
        (CostructuredArrow.map f) q) := by
  refine Quotient.inductionOn q (fun τ => ?_)
  simp only [Functor.mapConnectedComponents_mk,
    Quotient.lift_mk]
  simp only [CostructuredArrow.map,
    Comma.mapRight_obj_left,
    Comma.mapRight_obj_hom,
    Functor.const_map_app,
    Category.assoc, ← G.map_comp]

def comprehensiveConeForward
    (G : D ⥤ E)
    (s : Limits.Cone (F ⋙ G)) :
    Limits.Cone (comprehensiveM' F ⋙ G) where
  pt := s.pt
  π := {
    app := fun e =>
      Quotient.lift
        (fun τ : CostructuredArrow F e.fst =>
          s.π.app τ.left ≫ G.map τ.hom)
        (comprehensiveLiftLeg_wd' F G s e.fst)
        e.snd
    naturality := by
      intro e₁ e₂ m
      simp only [Functor.const_obj_map,
        Functor.comp_map, CategoryOfElements.π_map]
      erw [Category.id_comp]
      erw [comprehensiveConeForward_nat]
      congr 1
      exact m.property.symm }

def comprehensiveConeBackward
    (G : D ⥤ E)
    (t : Limits.Cone (comprehensiveM' F ⋙ G)) :
    Limits.Cone (F ⋙ G) where
  pt := t.pt
  π := {
    app := fun c =>
      t.π.app ((comprehensiveE' F).obj c)
    naturality := by
      intro c₁ c₂ f
      simp only [Functor.const_obj_map,
        Functor.comp_map]
      erw [Category.id_comp]
      rw [← t.w ((comprehensiveE' F).map f)]
      congr 1 }

theorem comprehensiveCone_backward_forward
    (G : D ⥤ E)
    (s : Limits.Cone (F ⋙ G)) :
    comprehensiveConeBackward F G
      (comprehensiveConeForward F G s) = s := by
  change Limits.Cone.mk s.pt _ = s
  cases s
  congr 1
  ext c
  simp only [comprehensiveConeForward,
    comprehensiveE', Quotient.lift_mk]
  dsimp
  simp only [G.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem comprehensiveCone_fwdbwd_leg
    (G : D ⥤ E)
    {pt : E}
    (π : (Functor.const
        (comprehensiveCopresheaf F).Elements).obj pt ⟶
      comprehensiveM' F ⋙ G)
    (d : D)
    (q : ConnectedComponents (CostructuredArrow F d))
    (hw : ∀ (τ₁ τ₂ : CostructuredArrow F d),
      Zigzag τ₁ τ₂ →
      π.app ((comprehensiveE' F).obj τ₁.left) ≫
        G.map τ₁.hom =
      π.app ((comprehensiveE' F).obj τ₂.left) ≫
        G.map τ₂.hom) :
    Quotient.lift
      (fun τ : CostructuredArrow F d =>
        π.app ((comprehensiveE' F).obj τ.left) ≫
          G.map τ.hom)
      hw q =
    π.app ⟨d, q⟩ := by
  refine Quotient.inductionOn q (fun τ => ?_)
  simp only [Quotient.lift_mk]
  let m :
      (comprehensiveE' F).obj τ.left ⟶
      (⟨d, ⟦τ⟧⟩ :
        (comprehensiveCopresheaf F).Elements) :=
    ⟨τ.hom, by
      simp only [comprehensiveCopresheaf_map]
      exact Quotient.sound
        (Zigzag.of_inv
          (CostructuredArrow.homMk (𝟙 _)
            (by simp)))⟩
  have nat := π.naturality m
  simp only [Functor.const_obj_map] at nat
  erw [Category.id_comp] at nat
  simp only [Functor.comp_map,
    CategoryOfElements.π_map] at nat
  exact nat.symm

theorem comprehensiveCone_forward_backward
    (G : D ⥤ E)
    (t : Limits.Cone (comprehensiveM' F ⋙ G)) :
    comprehensiveConeForward F G
      (comprehensiveConeBackward F G t) = t := by
  change Limits.Cone.mk t.pt _ = t
  cases t with | mk pt π =>
  congr 1
  ext e
  simp only [comprehensiveConeBackward]
  exact comprehensiveCone_fwdbwd_leg F G π
    e.fst e.snd _

def comprehensiveConeEquiv
    (G : D ⥤ E) :
    Limits.Cone (F ⋙ G) ≃
    Limits.Cone (comprehensiveM' F ⋙ G) where
  toFun := comprehensiveConeForward F G
  invFun := comprehensiveConeBackward F G
  left_inv := comprehensiveCone_backward_forward F G
  right_inv := comprehensiveCone_forward_backward F G

set_option backward.isDefEq.respectTransparency false in
def comprehensiveConeForwardFunctor
    (G : D ⥤ E) :
    Limits.Cone (F ⋙ G) ⥤
    Limits.Cone (comprehensiveM' F ⋙ G) where
  obj := comprehensiveConeForward F G
  map {s₁ s₂} f := {
    hom := f.hom
    w := by
      intro e
      simp only [comprehensiveConeForward]
      refine Quotient.inductionOn e.snd
        (fun τ => ?_)
      simp only [Quotient.lift_mk,
        ← Category.assoc]
      rw [← f.w τ.left] }

def comprehensiveConeBackwardFunctor
    (G : D ⥤ E) :
    Limits.Cone (comprehensiveM' F ⋙ G) ⥤
    Limits.Cone (F ⋙ G) where
  obj := comprehensiveConeBackward F G
  map {t₁ t₂} g := {
    hom := g.hom
    w := fun c => by
      simp only [comprehensiveConeBackward]
      exact g.w ((comprehensiveE' F).obj c) }

set_option backward.isDefEq.respectTransparency false in
def comprehensiveConeEquivalence
    (G : D ⥤ E) :
    Limits.Cone (F ⋙ G) ≌
    Limits.Cone (comprehensiveM' F ⋙ G) where
  functor := comprehensiveConeForwardFunctor F G
  inverse := comprehensiveConeBackwardFunctor F G
  unitIso := NatIso.ofComponents
    (fun s => eqToIso
      (comprehensiveCone_backward_forward
        F G s).symm)
    (fun f => by
      apply Limits.ConeMorphism.ext
      simp only [Limits.Cone.category_comp_hom,
        GebLean.Cone.eqToHom_hom, eqToIso.hom,
        eqToHom_refl, Category.id_comp,
        Category.comp_id,
        comprehensiveConeForwardFunctor,
        comprehensiveConeBackwardFunctor]
      rfl)
  counitIso := NatIso.ofComponents
    (fun t => eqToIso
      (comprehensiveCone_forward_backward
        F G t))
    (fun g => by
      apply Limits.ConeMorphism.ext
      simp only [Limits.Cone.category_comp_hom,
        GebLean.Cone.eqToHom_hom, eqToIso.hom,
        eqToHom_refl, Category.id_comp,
        Category.comp_id,
        comprehensiveConeForwardFunctor,
        comprehensiveConeBackwardFunctor]
      rfl)
  functor_unitIso_comp s := by
    apply Limits.ConeMorphism.ext
    simp only [Limits.Cone.category_comp_hom,
      Limits.Cone.category_id_hom,
      GebLean.Cone.eqToHom_hom, eqToIso.hom,
      NatIso.ofComponents, Functor.id_obj,
      comprehensiveConeForwardFunctor,
      comprehensiveConeForward,
      eqToHom_refl, Category.comp_id]

end ComprehensiveConeEquiv

section StrongRestrictedCowedgeWeightedCocone

variable {C : Type v} [Category.{v} C]
  {D : Type w} [Category.{v} D]
  (G : Cᵒᵖ ⥤ C ⥤ D)
  (H : Cᵒᵖ ⥤ C ⥤ Type v)

abbrev cowedgeWeight :
    (CoTwistedArrow C)ᵒᵖ ⥤ Type v :=
  comprehensivePresheaf
    (coTwistedArrowMap (DiagElem.forget H))

def strongRestrictedCowedgeToWeightedCocone
    (s : StrongRestrictedCowedge G H) :
    WeightedCocone (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G) :=
  (weightedCoconeElementsEquiv _ _).inverse.obj
    ((weightedCoconeDiagram_eq
      (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)).symm ▸
    ((comprehensiveCoconeEquiv
      (coTwistedArrowMap (DiagElem.forget H))
      (profunctorOnCoTwistedArrow C G)).toFun
    ((profOnCoTwArr_profPullback G
      (DiagElem.forget H)) ▸
    ((cowedgeCoconeEquiv
      (diagElemProf G H)).functor.obj
    ((strongRestrictedCowedgeEquiv G H).functor.obj
      s)))))

def weightedCoconeToStrongRestrictedCowedge
    (t : WeightedCocone (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)) :
    StrongRestrictedCowedge G H :=
  (strongRestrictedCowedgeEquiv G H).inverse.obj
    ((cowedgeCoconeEquiv
      (diagElemProf G H)).inverse.obj
    ((profOnCoTwArr_profPullback G
      (DiagElem.forget H)).symm ▸
    ((comprehensiveCoconeEquiv
      (coTwistedArrowMap (DiagElem.forget H))
      (profunctorOnCoTwistedArrow C G)).invFun
    ((weightedCoconeDiagram_eq
      (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)) ▸
    ((weightedCoconeElementsEquiv _ _).functor.obj
      t)))))

private theorem wCEE_roundtrip
    (x : Limits.Cocone
      (weightedCoconeDiagram (cowedgeWeight H)
        (profunctorOnCoTwistedArrow C G))) :
    (weightedCoconeElementsEquiv
      (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)).functor.obj
    ((weightedCoconeElementsEquiv
      (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)).inverse.obj
      x) = x :=
  elements_weightedCocone_roundtrip _ _ x

theorem strongRestrictedCowedge_weightedCocone_bwd_fwd
    (s : StrongRestrictedCowedge G H) :
    weightedCoconeToStrongRestrictedCowedge G H
      (strongRestrictedCowedgeToWeightedCocone G H
        s) = s := by
  unfold strongRestrictedCowedgeToWeightedCocone
    weightedCoconeToStrongRestrictedCowedge
  simp only [wCEE_roundtrip]
  simp only [comprehensiveCoconeEquiv,
    comprehensiveCocone_backward_forward]
  simp only [cowedgeCoconeEquiv,
    coconeToCowedgeFunctor, cowedgeToCoconeFunctor,
    cowedgeToCocone_coconeToCowedge]
  simp only [strongRestrictedCowedgeEquiv,
    cowedgeToStrongRestrictedFunctor,
    strongRestrictedToCowedgeFunctor,
    cowedge_strongRestricted_roundtrip]

private theorem wCEE_roundtrip'
    (t : WeightedCocone (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)) :
    (weightedCoconeElementsEquiv
      (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)).inverse.obj
    ((weightedCoconeElementsEquiv
      (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)).functor.obj
      t) = t :=
  weightedCocone_elements_roundtrip _ _ t

private theorem srce_roundtrip
    (cw : Limits.Cowedge (diagElemProf G H)) :
    strongRestrictedToCowedge G H
      (cowedgeToStrongRestricted G H cw) = cw := by
  cases cw with | mk pt ι =>
  change Limits.Cocone.mk pt _ = ⟨pt, ι⟩
  congr 1
  ext (a | j)
  · -- left a
    simp only [cowedgeToStrongRestricted,
      StrongRestrictedCowedge.mk',
      StrongRestrictedCowedge.family]
    exact (Limits.Multicofork.fst_app_right
      ⟨pt, ι⟩ a).symm
  · -- right j
    rfl

theorem strongRestrictedCowedge_weightedCocone_fwd_bwd
    (t : WeightedCocone (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G)) :
    strongRestrictedCowedgeToWeightedCocone G H
      (weightedCoconeToStrongRestrictedCowedge G H
        t) = t := by
  unfold strongRestrictedCowedgeToWeightedCocone
    weightedCoconeToStrongRestrictedCowedge
  simp only [strongRestrictedCowedgeEquiv,
    strongRestrictedToCowedgeFunctor,
    cowedgeToStrongRestrictedFunctor,
    srce_roundtrip]
  simp only [cowedgeCoconeEquiv,
    coconeToCowedgeFunctor, cowedgeToCoconeFunctor,
    coconeToCowedge_cowedgeToCocone]
  simp only [comprehensiveCoconeEquiv,
    comprehensiveCocone_forward_backward]
  simp only [wCEE_roundtrip']

def strongRestrictedCowedge_weightedCocone_equiv :
    StrongRestrictedCowedge G H ≃
    WeightedCocone (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G) where
  toFun :=
    strongRestrictedCowedgeToWeightedCocone G H
  invFun :=
    weightedCoconeToStrongRestrictedCowedge G H
  left_inv :=
    strongRestrictedCowedge_weightedCocone_bwd_fwd
      G H
  right_inv :=
    strongRestrictedCowedge_weightedCocone_fwd_bwd
      G H

def strongRestrictedCowedge_weightedCocone_equivalence
    :
    StrongRestrictedCowedge (C := C) (D := D) G H ≌
    WeightedCocone (J := CoTwistedArrow C) (C := D) (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G) :=
  (strongRestrictedCowedgeEquiv G H)
  |>.trans (cowedgeCoconeEquiv (diagElemProf G H))
  |>.trans (Limits.Cocone.precomposeEquivalence
    ((eqToIso (profOnCoTwArr_profPullback G
      (DiagElem.forget H))).symm))
  |>.trans (comprehensiveCoconeEquivalence
    (coTwistedArrowMap (DiagElem.forget H))
    (profunctorOnCoTwistedArrow C G))
  |>.trans (Limits.Cocone.precomposeEquivalence
    (eqToIso (weightedCoconeDiagram_eq
      (cowedgeWeight H)
      (profunctorOnCoTwistedArrow C G))))
  |>.trans (weightedCoconeElementsEquiv _ _).symm

end StrongRestrictedCowedgeWeightedCocone

section StrongRestrictedWedgeWeightedCone

variable {C : Type v} [Category.{v} C]
  {D : Type w} [Category.{v} D]
  (G : Cᵒᵖ ⥤ C ⥤ D)
  (H : Cᵒᵖ ⥤ C ⥤ Type v)

abbrev wedgeWeight :
    TwistedArrow C ⥤ Type v :=
  comprehensiveCopresheaf
    (twistedArrowMap (DiagElem.forget H))

def strongRestrictedWedgeToWeightedCone
    (s : StrongRestrictedWedge G H) :
    WeightedCone (wedgeWeight H)
      (profunctorOnTwistedArrow C G) :=
  (weightedConeElementsEquiv _ _).inverse.obj
    ((comprehensiveConeEquiv
      (twistedArrowMap (DiagElem.forget H))
      (profunctorOnTwistedArrow C G)).toFun
    ((profOnTwArr_profPullback G
      (DiagElem.forget H)) ▸
    ((wedgeConeEquiv
      (diagElemProf G H)).functor.obj
    ((strongRestrictedWedgeEquiv G H).functor.obj
      s))))

def weightedConeToStrongRestrictedWedge
    (t : WeightedCone (wedgeWeight H)
      (profunctorOnTwistedArrow C G)) :
    StrongRestrictedWedge G H :=
  (strongRestrictedWedgeEquiv G H).inverse.obj
    ((wedgeConeEquiv
      (diagElemProf G H)).inverse.obj
    ((profOnTwArr_profPullback G
      (DiagElem.forget H)).symm ▸
    ((comprehensiveConeEquiv
      (twistedArrowMap (DiagElem.forget H))
      (profunctorOnTwistedArrow C G)).invFun
    ((weightedConeElementsEquiv _ _).functor.obj
      t))))

private theorem wCEE_cone_roundtrip
    (x : Limits.Cone
      (weightedConeDiagram (wedgeWeight H)
        (profunctorOnTwistedArrow C G))) :
    (weightedConeElementsEquiv
      (wedgeWeight H)
      (profunctorOnTwistedArrow C G)).functor.obj
    ((weightedConeElementsEquiv
      (wedgeWeight H)
      (profunctorOnTwistedArrow C G)).inverse.obj
      x) = x :=
  elements_weightedCone_roundtrip _ _ x

theorem strongRestrictedWedge_weightedCone_bwd_fwd
    (s : StrongRestrictedWedge G H) :
    weightedConeToStrongRestrictedWedge G H
      (strongRestrictedWedgeToWeightedCone G H
        s) = s := by
  unfold strongRestrictedWedgeToWeightedCone
    weightedConeToStrongRestrictedWedge
  simp only [wCEE_cone_roundtrip]
  simp only [comprehensiveConeEquiv,
    comprehensiveCone_backward_forward]
  simp only [wedgeConeEquiv,
    coneToWedgeFunctor, wedgeToConeFunctor,
    wedgeToCone_coneToWedge]
  simp only [strongRestrictedWedgeEquiv,
    wedgeToStrongRestrictedFunctor,
    strongRestrictedToWedgeFunctor,
    wedge_strongRestricted_roundtrip]

private theorem wCEE_cone_roundtrip'
    (t : WeightedCone (wedgeWeight H)
      (profunctorOnTwistedArrow C G)) :
    (weightedConeElementsEquiv
      (wedgeWeight H)
      (profunctorOnTwistedArrow C G)).inverse.obj
    ((weightedConeElementsEquiv
      (wedgeWeight H)
      (profunctorOnTwistedArrow C G)).functor.obj
      t) = t :=
  weightedCone_elements_roundtrip _ _ t

private theorem srwe_roundtrip
    (w : Limits.Wedge (diagElemProf G H)) :
    strongRestrictedToWedge G H
      (wedgeToStrongRestricted G H w) = w := by
  cases w with | mk pt π =>
  change Limits.Cone.mk pt _ = ⟨pt, π⟩
  congr 1
  ext (j | b)
  · -- left j
    rfl
  · -- right b
    simp only [wedgeToStrongRestricted,
      StrongRestrictedWedge.mk',
      StrongRestrictedWedge.family]
    exact (Limits.Multifork.app_right_eq_ι_comp_fst
      ⟨pt, π⟩ b).symm

theorem strongRestrictedWedge_weightedCone_fwd_bwd
    (t : WeightedCone (wedgeWeight H)
      (profunctorOnTwistedArrow C G)) :
    strongRestrictedWedgeToWeightedCone G H
      (weightedConeToStrongRestrictedWedge G H
        t) = t := by
  unfold strongRestrictedWedgeToWeightedCone
    weightedConeToStrongRestrictedWedge
  simp only [strongRestrictedWedgeEquiv,
    strongRestrictedToWedgeFunctor,
    wedgeToStrongRestrictedFunctor,
    srwe_roundtrip]
  simp only [wedgeConeEquiv,
    coneToWedgeFunctor, wedgeToConeFunctor,
    coneToWedge_wedgeToCone]
  simp only [comprehensiveConeEquiv,
    comprehensiveCone_forward_backward]
  simp only [wCEE_cone_roundtrip']

def strongRestrictedWedge_weightedCone_equiv :
    StrongRestrictedWedge G H ≃
    WeightedCone (wedgeWeight H)
      (profunctorOnTwistedArrow C G) where
  toFun :=
    strongRestrictedWedgeToWeightedCone G H
  invFun :=
    weightedConeToStrongRestrictedWedge G H
  left_inv :=
    strongRestrictedWedge_weightedCone_bwd_fwd
      G H
  right_inv :=
    strongRestrictedWedge_weightedCone_fwd_bwd
      G H

def strongRestrictedWedge_weightedCone_equivalence :
    StrongRestrictedWedge (C := C) (D := D) G H ≌
    WeightedCone (J := TwistedArrow C) (C := D) (wedgeWeight H)
      (profunctorOnTwistedArrow C G) :=
  (strongRestrictedWedgeEquiv G H)
  |>.trans (wedgeConeEquiv (diagElemProf G H))
  |>.trans (Limits.Cone.postcomposeEquivalence
    (eqToIso (profOnTwArr_profPullback G
      (DiagElem.forget H))))
  |>.trans (comprehensiveConeEquivalence
    (twistedArrowMap (DiagElem.forget H))
    (profunctorOnTwistedArrow C G))
  |>.trans (weightedConeElementsEquiv _ _).symm

end StrongRestrictedWedgeWeightedCone

section ParanatWeightedLimit

variable {C : Type v} [Category.{v} C]
  (G H : Cᵒᵖ ⥤ C ⥤ Type v)

/-- The image of the structure integral wedge
under the equivalence to weighted cones is
terminal. -/
def structureIntegralWeightedCone_isTerminal :
    Limits.IsTerminal
      ((strongRestrictedWedge_weightedCone_equivalence
        G H).functor.obj
        (structureIntegralWedge G H)) :=
  isTerminalOfEquivFunctor
    (strongRestrictedWedge_weightedCone_equivalence
      G H)
    (structureIntegralWedge_isTerminal G H)

/-- Isomorphism in the weighted cone category between
the structure integral image and the natural
transformation cone. -/
def structureIntegralWeightedConeIso :
    (strongRestrictedWedge_weightedCone_equivalence
      G H).functor.obj
      (structureIntegralWedge G H) ≅
    natTransWeightedCone
      (wedgeWeight H)
      (profunctorOnTwistedArrow C G) :=
  (structureIntegralWeightedCone_isTerminal
    G H).uniqueUpToIso
    natTransWeightedCone_isTerminal

/-- Iso in `Type v` between `StructureIntegral H G`
and `wedgeWeight H ⟶ profunctorOnTwistedArrow C G`,
extracted from the weighted cone iso between
terminal objects. -/
def structureIntegralNatTransIso :
    StructureIntegral H G ≅
    (wedgeWeight H ⟶
      profunctorOnTwistedArrow C G) where
  hom :=
    (structureIntegralWeightedConeIso G H).hom.hom
  inv :=
    (structureIntegralWeightedConeIso G H).inv.hom
  hom_inv_id := by
    have h :=
      (structureIntegralWeightedConeIso
        G H).hom_inv_id
    have := congr_arg
      WeightedCone.Hom.hom h
    simp only [WeightedCone.category_comp_hom,
      WeightedCone.category_id_hom] at this
    exact this
  inv_hom_id := by
    have h :=
      (structureIntegralWeightedConeIso
        G H).inv_hom_id
    have := congr_arg
      WeightedCone.Hom.hom h
    simp only [WeightedCone.category_comp_hom,
      WeightedCone.category_id_hom] at this
    exact this

/-- Paranatural transformations `Paranat H G` are
equivalent to natural transformations from the wedge
weight to the profunctor on twisted arrows:
`Paranat H G ≃
  (wedgeWeight H ⟶ profunctorOnTwistedArrow C G)`.

This characterizes paranaturality entirely in terms
of ordinary naturality: a paranatural transformation
from `H` to `G` is the same as a natural
transformation between functors on `TwistedArrow C`.
-/
def paranatWeightedLimitEquiv :
    Paranat H G ≃
    (wedgeWeight H ⟶
      profunctorOnTwistedArrow (D := Type v) C G) :=
  (structureIntegralEquivParanat H G).symm |>.trans
    (structureIntegralNatTransIso G H).toEquiv

end ParanatWeightedLimit

section ParanatCoTwistedArrow

variable {C : Type v} [Category.{v} C]
  (G H : Cᵒᵖ ⥤ C ⥤ Type v)

/-- The wedge weight reindexed from `TwistedArrow C`
to `(CoTwistedArrow C)ᵒᵖ` via the canonical
equivalence. -/
abbrev wedgeWeightCoTw :
    (CoTwistedArrow C)ᵒᵖ ⥤ Type v :=
  coTwistedArrowOpEquivTwistedArrow.functor ⋙
    wedgeWeight H

/-- Paranatural transformations `Paranat H G` are
equivalent to natural transformations from the
reindexed wedge weight to the profunctor on
opposite co-twisted arrows:
`Paranat H G ≃
  (wedgeWeightCoTw H ⟶
    profunctorOnOpCoTwistedArrow C G)`.

This re-expresses `paranatWeightedLimitEquiv`
using `(CoTwistedArrow C)ᵒᵖ` as the index
category instead of `TwistedArrow C`. -/
def paranatWeightedLimitEquivCoTw :
    Paranat H G ≃
    (wedgeWeightCoTw H ⟶
      profunctorOnOpCoTwistedArrow C G) :=
  let e := coTwistedArrowOpEquivTwistedArrow
    (C := C)
  let cl := e.symm.congrLeft (E := Type v)
  (paranatWeightedLimitEquiv G H).trans
    (cl.fullyFaithfulFunctor.homEquiv)

end ParanatCoTwistedArrow

section WedgeWeightFunctoriality

variable {C : Type v} [Category.{v} C]
  (H G : Cᵒᵖ ⥤ C ⥤ Type v)

set_option backward.isDefEq.respectTransparency false in
/-- Given `η : H ⟶ G`, the induced functor between
costructured arrow categories. At each `tw`, this
sends a costructured arrow over
`twistedArrowMap (DiagElem.forget H)` to one over
`twistedArrowMap (DiagElem.forget G)` by applying
`twistedArrowMap (DiagElem.map η)` to the source
object. The `hom` is reused without transport because
the forgetful functor agrees definitionally on objects
and morphisms after applying `DiagElem.map η`. -/
def wedgeWeightPreMap (η : H ⟶ G)
    (tw : TwistedArrow C) :
    CostructuredArrow
      (twistedArrowMap (DiagElem.forget H)) tw ⥤
    CostructuredArrow
      (twistedArrowMap (DiagElem.forget G)) tw where
  obj σ := CostructuredArrow.mk
    (Y := (twistedArrowMap
      (DiagElem.map η)).obj σ.left)
    σ.hom
  map f := CostructuredArrow.homMk
    ((twistedArrowMap (DiagElem.map η)).map f.left)
    (by
      have h : (twistedArrowMap (DiagElem.forget G)).map
          ((twistedArrowMap (DiagElem.map η)).map
            f.left) =
          (twistedArrowMap (DiagElem.forget H)).map
            f.left := by
        apply twHom_ext <;> rfl
      rw [h]
      exact CostructuredArrow.w f)

/-- The natural transformation `wedgeWeight H ⟶ wedgeWeight G`
induced by `η : H ⟶ G`. At each twisted arrow `tw`,
applies `wedgeWeightPreMap η tw` to connected
components. -/
def wedgeWeightMap (η : H ⟶ G) :
    wedgeWeight H ⟶ wedgeWeight G where
  app tw :=
    (wedgeWeightPreMap H G η tw).mapConnectedComponents
  naturality {tw₁ tw₂} f := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp only [types_comp_apply, wedgeWeight,
        comprehensiveCopresheaf_map,
        Functor.mapConnectedComponents_mk,
        wedgeWeightPreMap, CostructuredArrow.map_mk]
      exact Quotient.sound (Zigzag.refl _)

/-- The wedge weight construction is functorial in the
source profunctor: a natural transformation `η : H ⟶ G`
induces `wedgeWeight H ⟶ wedgeWeight G`. -/
def wedgeWeightFunctor (C : Type v) [Category.{v} C] :
    (Cᵒᵖ ⥤ C ⥤ Type v) ⥤
      (TwistedArrow C ⥤ Type v) where
  obj H := wedgeWeight H
  map η := wedgeWeightMap _ _ η
  map_id H := by
    ext tw x
    exact Quotient.inductionOn x fun σ => by
      simp only [wedgeWeightMap, NatTrans.id_app,
        types_id_apply,
        Functor.mapConnectedComponents_mk,
        wedgeWeightPreMap]
      congr 1
  map_comp {H G K} η θ := by
    ext tw x
    exact Quotient.inductionOn x fun σ => by
      simp only [wedgeWeightMap, NatTrans.comp_app,
        types_comp_apply,
        Functor.mapConnectedComponents_mk,
        wedgeWeightPreMap]
      congr 1

end WedgeWeightFunctoriality

section CostructureIntegralElimination

variable {C : Type v} [Category.{v} C]
  (G H : Cᵒᵖ ⥤ C ⥤ Type v)

/-- The image of the costructure integral cowedge
under the equivalence to weighted cocones is
initial. -/
def costructureIntegralWeightedCocone_isInitial :
    Limits.IsInitial
      ((strongRestrictedCowedge_weightedCocone_equivalence
        G H).functor.obj
        (costructureIntegralCowedge G H)) :=
  isInitialOfEquivFunctor
    (strongRestrictedCowedge_weightedCocone_equivalence
      G H)
    (costructureIntegralCowedge_isInitial G H)

/-- The weighted cocone corresponding to the
costructure integral has apex
`CostructureIntegral H G`. -/
theorem costructureIntegralWeightedCocone_pt :
    ((strongRestrictedCowedge_weightedCocone_equivalence
      G H).functor.obj
      (costructureIntegralCowedge G H)).pt =
    CostructureIntegral H G := by rfl

/-- The elimination rule for `CostructureIntegral`:
maps from `CostructureIntegral H G` to any type `Y`
correspond to natural transformations from
`cowedgeWeight H` to `homToFunctor (profOnCoTwArr C G) Y`.

Categorically, this expresses the weighted
colimit-limit adjunction: `Hom(colim, Y) ≅ lim Hom(D(-), Y)`,
specialized to `Type v` where the weighted limit
is a natural transformation type. -/
def costructureIntegralElimIso (Y : Type v) :
    (CostructureIntegral H G → Y) ≅
    (cowedgeWeight H ⟶
      homToFunctor
        (profunctorOnCoTwistedArrow C G) Y) :=
  IsWeightedColimit.homIsoWeightedLimitApex
    (costructureIntegralWeightedCocone_isInitial
      G H)
    Y
    natTransWeightedCone_isTerminal

/-- Maps from `CostructureIntegral H G` to any
type `Y` are equivalent to natural transformations
`cowedgeWeight H ⟶ homToFunctor (profOnCoTwArr C G) Y`.
-/
def costructureIntegralElimEquiv (Y : Type v) :
    (CostructureIntegral H G → Y) ≃
    (cowedgeWeight H ⟶
      homToFunctor
        (profunctorOnCoTwistedArrow C G) Y) :=
  (costructureIntegralElimIso G H Y).toEquiv

end CostructureIntegralElimination

section WeightedCoendSliceElim

variable {C : Type v} [Category.{v} C]
  (G : Cᵒᵖ ⥤ C ⥤ Type v) (Y : Type v)

theorem homToFunctor_profOnCoTwArr_eq :
    homToFunctor
      (profunctorOnCoTwistedArrow C G) Y =
    profunctorOnOpCoTwistedArrow C (G ⇓ Y) :=
  rfl

variable {W : Cᵒᵖ ⥤ C ⥤ Type v}
  {c : WeightedCowedge W G}

/-- The general weighted coend elimination with
slice profunctor.

For a weighted coend `c` of `G` by `W`, maps from
`c.pt` to `Y` correspond to natural transformations
from `profOnOpCoTwArr C W` to
`profOnOpCoTwArr C (G ⇓ Y)`.

This follows from `homIsoWeightedLimitApex` and the
definitional equality
`homToFunctor (profOnCoTwArr C G) Y =
  profOnOpCoTwArr C (G ⇓ Y)`. -/
def weightedCoendElimSlice
    (hc : IsWeightedCoend c)
    (Y : Type v) :
    (c.pt → Y) ≅
    (profunctorOnOpCoTwistedArrow C W ⟶
      profunctorOnOpCoTwistedArrow C
        (G ⇓ Y)) :=
  hc.homIsoWeightedLimitApex Y
    natTransWeightedCone_isTerminal

/-- Equiv version of `weightedCoendElimSlice`. -/
def weightedCoendElimSliceEquiv
    (hc : IsWeightedCoend c)
    (Y : Type v) :
    (c.pt → Y) ≃
    (profunctorOnOpCoTwistedArrow C W ⟶
      profunctorOnOpCoTwistedArrow C
        (G ⇓ Y)) :=
  (weightedCoendElimSlice G hc Y).toEquiv

end WeightedCoendSliceElim

section CoendHomAdjunction

variable {C : Type v} [Category.{v} C]
  (G H : Cᵒᵖ ⥤ C ⥤ Type v)

/-- The coend-hom adjunction:
maps from `CostructureIntegral H G` to `Y`
correspond to elements of
`StructureIntegral H (G ⇓ Y)`.

The underlying data of both sides is the same:
families `(x : DiagElem H) → (diagApp G x.base → Y)`.
The slice profunctor `G ⇓ Y` reverses variance, so
the cowedge condition for the costructure integral
becomes the wedge/end condition for the structure
integral. -/
def coendHomAdjunction (Y : Type v) :
    (CostructureIntegral H G → Y) ≃
      StructureIntegral H (G ⇓ Y) where
  toFun f := {
    family := fun x g => f (CostructureIntegral.mk x g)
    equalizer := by
      funext x y fhom
      simp only [structIntMapCov, structIntMapContrav]
      funext ψ
      simp only [covAction, contravAction,
        sliceProfunctor, types_comp_apply]
      exact congrArg f
        (CostructureIntegral.sound fhom ψ)
  }
  invFun φ := CostructureIntegral.lift
    (fun x g => φ.family x g) (by
      intro x y fhom ψ
      have h := φ.paranatural fhom
      simp only [covAction, contravAction,
        sliceProfunctor] at h
      exact congrFun h ψ)
  left_inv f := by
    ext q
    exact Quotient.inductionOn q
      (fun ⟨_, _⟩ => rfl)
  right_inv φ := by
    ext x
    rfl

/-- The coend-hom adjunction expressed using
`Paranat` instead of `StructureIntegral`. -/
def coendHomAdjunctionParanat (Y : Type v) :
    (CostructureIntegral H G → Y) ≃
      Paranat H (G ⇓ Y) :=
  (coendHomAdjunction G H Y).trans
    (structureIntegralEquivParanat H (G ⇓ Y))

end CoendHomAdjunction

end GebLean
