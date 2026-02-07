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
  |>.trans (Limits.Cocones.precomposeEquivalence
    ((eqToIso (profOnCoTwArr_profPullback G
      (DiagElem.forget H))).symm))
  |>.trans (comprehensiveCoconeEquivalence
    (coTwistedArrowMap (DiagElem.forget H))
    (profunctorOnCoTwistedArrow C G))
  |>.trans (Limits.Cocones.precomposeEquivalence
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
  |>.trans (Limits.Cones.postcomposeEquivalence
    (eqToIso (profOnTwArr_profPullback G
      (DiagElem.forget H))))
  |>.trans (comprehensiveConeEquivalence
    (twistedArrowMap (DiagElem.forget H))
    (profunctorOnTwistedArrow C G))
  |>.trans (weightedConeElementsEquiv _ _).symm

end StrongRestrictedWedgeWeightedCone

end GebLean
