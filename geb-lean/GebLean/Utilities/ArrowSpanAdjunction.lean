import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Adjunction.Reflective

set_option backward.isDefEq.respectTransparency true

open CategoryTheory Limits

namespace GebLean

universe v u

variable {C : Type u} [Category.{v} C]

/-- The inclusion of the arrow category into the category
of span diagrams, sending an arrow `f : P ⟶ Q` to the span
`P ←[id]─ P ─[f]→ Q`. -/
@[simps]
def arrowSpanInclusion
    (C : Type u) [Category.{v} C] :
    Arrow C ⥤ (WalkingSpan ⥤ C) where
  obj f := span (𝟙 f.left) f.hom
  map {f g} sq :=
    spanHomMk sq.left sq.left sq.right
      (by simp [span_map_fst])
      (by
        simp only [span_map_snd]
        exact sq.w.symm)
  map_id f := by
    apply NatTrans.ext
    funext j
    match j with
    | .zero => simp
    | .left => simp
    | .right => simp
  map_comp {f g h} sq₁ sq₂ := by
    apply NatTrans.ext
    funext j
    match j with
    | .zero => simp
    | .left => simp
    | .right => simp

/-- `arrowSpanInclusion` is fully faithful: a natural
transformation between spans `(id, f)` and `(id, g)` is
determined by its components at `.left` and `.right`,
which form a commutative square. -/
def arrowSpanInclusion.fullyFaithful :
    (arrowSpanInclusion C).FullyFaithful where
  preimage {f g} α :=
    Arrow.homMk (α.app .left) (α.app .right)
      (by
        have hfst :=
          α.naturality WalkingSpan.Hom.fst
        simp only [Functor.id_obj,
          arrowSpanInclusion_obj,
          span_map_fst] at hfst
        have hsnd :=
          α.naturality WalkingSpan.Hom.snd
        simp only [Functor.id_obj,
          arrowSpanInclusion_obj,
          span_map_snd] at hsnd
        rw [show α.app .left =
            α.app .zero from by
          rw [← Category.id_comp
            (α.app .left),
            ← Category.comp_id
            (α.app .zero)]
          exact hfst]
        exact hsnd.symm)
  map_preimage {f g} α := by
    apply NatTrans.ext
    funext j
    match j with
    | .zero =>
      simp only [arrowSpanInclusion_obj,
        Functor.id_obj, span_zero,
        arrowSpanInclusion_map,
        Arrow.homMk_left, Arrow.homMk_right,
        spanHomMk_app]
      have h :=
        α.naturality WalkingSpan.Hom.fst
      simp only [Functor.id_obj,
        arrowSpanInclusion_obj,
        span_map_fst] at h
      rw [← Category.id_comp
        (α.app .left),
        ← Category.comp_id
        (α.app .zero)]
      exact h
    | .left => simp
    | .right => simp
  preimage_map {f g} sq := by
    apply Arrow.hom_ext
    · rfl
    · rfl

instance : (arrowSpanInclusion C).Faithful :=
  arrowSpanInclusion.fullyFaithful.faithful

instance : (arrowSpanInclusion C).Full :=
  arrowSpanInclusion.fullyFaithful.full

set_option backward.isDefEq.respectTransparency false in
/-- The reflector from span diagrams to arrows, sending
each span to the arrow given by the left injection into
its pushout. Parameterized by an explicit choice of
pushout cocone for each span. -/
def spanArrowReflector
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S) :
    (WalkingSpan ⥤ C) ⥤ Arrow C where
  obj S :=
    Arrow.mk
      ((pushouts S).cocone.ι.app WalkingSpan.left)
  map {S₁ S₂} α :=
    Arrow.homMk (α.app WalkingSpan.left)
      ((pushouts S₁).isColimit.desc
        (Cocone.mk (pushouts S₂).cocone.pt
          (α ≫ (pushouts S₂).cocone.ι)))
      (by
        have := (pushouts S₁).isColimit.fac
          (Cocone.mk (pushouts S₂).cocone.pt
            (α ≫ (pushouts S₂).cocone.ι))
          WalkingSpan.left
        dsimp at this
        exact this.symm)
  map_id S := by
    apply Arrow.hom_ext
    · simp
    · dsimp
      symm
      apply (pushouts S).isColimit.uniq
        (Cocone.mk (pushouts S).cocone.pt
          (𝟙 S ≫ (pushouts S).cocone.ι))
      intro j
      simp [Category.id_comp]
  map_comp {S₁ S₂ S₃} α β := by
    apply Arrow.hom_ext
    · simp
    · dsimp
      symm
      apply (pushouts S₁).isColimit.uniq
        (Cocone.mk (pushouts S₃).cocone.pt
          ((α ≫ β) ≫ (pushouts S₃).cocone.ι))
      intro j
      rw [← Category.assoc,
        (pushouts S₁).isColimit.fac
          (Cocone.mk (pushouts S₂).cocone.pt
            (α ≫ (pushouts S₂).cocone.ι)) j]
      dsimp
      rw [Category.assoc,
        (pushouts S₂).isColimit.fac
          (Cocone.mk (pushouts S₃).cocone.pt
            (β ≫ (pushouts S₃).cocone.ι)) j]
      dsimp
      simp only [← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The unit of the arrow-span adjunction at a span
`S`. Maps `S` to the inclusion of its reflection
(the pushout arrow). -/
def arrowSpanAdjUnitApp
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S)
    (S : WalkingSpan ⥤ C) :
    S ⟶ ((spanArrowReflector pushouts ⋙
      arrowSpanInclusion C).obj S) :=
  spanHomMk
    (S.map WalkingSpan.Hom.fst)
    (𝟙 _)
    ((pushouts S).cocone.ι.app WalkingSpan.right)
    (by simp)
    (by
      dsimp [spanArrowReflector, arrowSpanInclusion]
      rw [(pushouts S).cocone.w
        WalkingSpan.Hom.snd,
        (pushouts S).cocone.w
        WalkingSpan.Hom.fst])

set_option backward.isDefEq.respectTransparency false in
/-- The unit of the arrow-span adjunction as a
natural transformation. -/
def arrowSpanAdjUnit
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S) :
    𝟭 (WalkingSpan ⥤ C) ⟶
    spanArrowReflector pushouts ⋙
      arrowSpanInclusion C where
  app S := arrowSpanAdjUnitApp pushouts S
  naturality S₁ S₂ α := by
    ext j
    match j with
    | .zero | .left | .right =>
      simp [arrowSpanAdjUnitApp,
        spanArrowReflector, arrowSpanInclusion]

/-- The cocone over `span (𝟙 f.left) f.hom` with
point `f.right`, used to define the counit. -/
def arrowSpanAdjCounitCocone
    (f : Arrow C) :
    Cocone ((arrowSpanInclusion C).obj f) where
  pt := f.right
  ι :=
    { app := fun j => match j with
        | .zero => f.hom
        | .left => f.hom
        | .right => 𝟙 _
      naturality := by
        intro X Y h
        induction h with
        | id => simp
        | init j =>
          cases j <;>
            simp [arrowSpanInclusion] }

/-- The counit of the arrow-span adjunction at an
arrow `f`. Maps the pushout of `span (𝟙 f.left)
f.hom` back to `f` via the universal property. -/
def arrowSpanAdjCounitApp
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S)
    (f : Arrow C) :
    ((arrowSpanInclusion C ⋙
      spanArrowReflector pushouts).obj f) ⟶ f :=
  Arrow.homMk (𝟙 _)
    ((pushouts
      ((arrowSpanInclusion C).obj f)).isColimit.desc
        (arrowSpanAdjCounitCocone f))
    (by
      dsimp [spanArrowReflector, arrowSpanInclusion]
      rw [Category.id_comp]
      exact ((pushouts _).isColimit.fac
        (arrowSpanAdjCounitCocone f)
        WalkingSpan.left).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The counit of the arrow-span adjunction as a
natural transformation. -/
def arrowSpanAdjCounit
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S) :
    arrowSpanInclusion C ⋙
      spanArrowReflector pushouts ⟶
    𝟭 (Arrow C) where
  app f := arrowSpanAdjCounitApp pushouts f
  naturality {f g} sq := by
    apply Arrow.hom_ext
    · simp [arrowSpanAdjCounitApp,
        spanArrowReflector, arrowSpanInclusion]
    · dsimp [arrowSpanAdjCounitApp,
        spanArrowReflector, arrowSpanInclusion]
      apply PushoutCocone.IsColimit.hom_ext
        (pushouts _).isColimit
      · change (pushouts _).cocone.ι.app
            WalkingSpan.left ≫ _ ≫ _ =
          (pushouts _).cocone.ι.app
            WalkingSpan.left ≫ _ ≫ _
        rw [← Category.assoc,
          (pushouts _).isColimit.fac
            _ WalkingSpan.left,
          ← Category.assoc,
          (pushouts _).isColimit.fac
            _ WalkingSpan.left]
        dsimp [arrowSpanAdjCounitCocone]
        rw [Category.assoc,
          (pushouts _).isColimit.fac
            _ WalkingSpan.left]
        dsimp [arrowSpanAdjCounitCocone]
        exact sq.w
      · change (pushouts _).cocone.ι.app
            WalkingSpan.right ≫ _ ≫ _ =
          (pushouts _).cocone.ι.app
            WalkingSpan.right ≫ _ ≫ _
        rw [← Category.assoc,
          (pushouts _).isColimit.fac
            _ WalkingSpan.right,
          ← Category.assoc,
          (pushouts _).isColimit.fac
            _ WalkingSpan.right]
        dsimp [arrowSpanAdjCounitCocone]
        rw [Category.assoc,
          (pushouts _).isColimit.fac
            _ WalkingSpan.right]
        dsimp [arrowSpanAdjCounitCocone]
        simp

private theorem colimit_hom_ext
    {J : Type*} [Category J]
    {F : J ⥤ C} {c : Cocone F}
    (hc : IsColimit c)
    {W : C} {f g : c.pt ⟶ W}
    (h : ∀ j, c.ι.app j ≫ f =
      c.ι.app j ≫ g) : f = g := by
  let s := Cocone.mk W
    (c.ι ≫ (Functor.const J).map f)
  have hf : f = hc.desc s :=
    hc.uniq s f (fun j => by dsimp [s])
  have hg : g = hc.desc s :=
    hc.uniq s g (fun j => by
      dsimp [s]; exact (h j).symm)
  rw [hf, hg]

set_option backward.isDefEq.respectTransparency false in
/-- The left triangle identity:
`reflector.map (unit S) ≫ counit (reflector S) = 𝟙`.
-/
theorem arrowSpanAdj_left_triangle
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S)
    (S : WalkingSpan ⥤ C) :
    (spanArrowReflector pushouts).map
      (arrowSpanAdjUnitApp pushouts S) ≫
    arrowSpanAdjCounitApp pushouts
      ((spanArrowReflector pushouts).obj S) =
    𝟙 _ := by
  apply Arrow.hom_ext
  · simp [arrowSpanAdjUnitApp,
      arrowSpanAdjCounitApp,
      spanArrowReflector, arrowSpanInclusion]
  · dsimp [arrowSpanAdjCounitApp,
      spanArrowReflector, arrowSpanInclusion,
      arrowSpanAdjUnitApp]
    apply colimit_hom_ext
      (pushouts S).isColimit
    intro j
    rw [← Category.assoc,
      (pushouts S).isColimit.fac]
    dsimp
    rw [Category.assoc,
      (pushouts _).isColimit.fac]
    dsimp [arrowSpanAdjCounitCocone]
    match j with
    | .zero =>
      simp only [Category.comp_id]
      exact (pushouts S).cocone.w
        WalkingSpan.Hom.fst
    | .left =>
      simp only [Category.comp_id,
        Category.id_comp]
    | .right => simp

set_option backward.isDefEq.respectTransparency false in
/-- The right triangle identity:
`unit (inclusion f) ≫ inclusion.map (counit f) = 𝟙`.
-/
theorem arrowSpanAdj_right_triangle
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S)
    (f : Arrow C) :
    arrowSpanAdjUnitApp pushouts
      ((arrowSpanInclusion C).obj f) ≫
    (arrowSpanInclusion C).map
      (arrowSpanAdjCounitApp pushouts f) =
    𝟙 _ := by
  ext j
  match j with
  | .zero =>
    simp [arrowSpanAdjUnitApp,
      arrowSpanAdjCounitApp,
      arrowSpanInclusion]
  | .left =>
    simp [arrowSpanAdjUnitApp,
      arrowSpanAdjCounitApp,
      arrowSpanInclusion]
  | .right =>
    simp only [NatTrans.comp_app,
      arrowSpanInclusion_map,
      arrowSpanAdjUnitApp,
      arrowSpanAdjCounitApp,
      spanHomMk_app, NatTrans.id_app]
    dsimp [arrowSpanInclusion, spanArrowReflector]
    exact (pushouts _).isColimit.fac
      (arrowSpanAdjCounitCocone f)
      WalkingSpan.right

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction
`spanArrowReflector pushouts ⊣ arrowSpanInclusion C`,
parameterized by an explicit pushout cocone assignment.
-/
def arrowSpanAdj
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S) :
    spanArrowReflector pushouts ⊣
      arrowSpanInclusion C :=
  Adjunction.mkOfUnitCounit {
    unit := arrowSpanAdjUnit pushouts
    counit := arrowSpanAdjCounit pushouts
    left_triangle := by
      apply NatTrans.ext; funext S
      simp only [NatTrans.comp_app,
        Functor.whiskerRight_app,
        Functor.whiskerLeft_app,
        Functor.associator,
        Category.id_comp]
      convert arrowSpanAdj_left_triangle
        pushouts S using 1
    right_triangle := by
      apply NatTrans.ext; funext f
      simp only [NatTrans.comp_app,
        Functor.whiskerRight_app,
        Functor.whiskerLeft_app,
        Functor.associator,
        Category.id_comp]
      convert arrowSpanAdj_right_triangle
        pushouts f using 1
  }

/-- `Arrow C` is a reflective subcategory of
`WalkingSpan ⥤ C` via the arrow-span inclusion,
given an explicit pushout cocone assignment. -/
instance arrowSpanReflective
    (pushouts :
      (S : WalkingSpan ⥤ C) → ColimitCocone S) :
    Reflective (arrowSpanInclusion C) where
  L := spanArrowReflector pushouts
  adj := arrowSpanAdj pushouts

section PshSpanPushouts

universe w

variable {C : Type*} [Category C]

/-- The raw relation on the coproduct of the
left and right feet of a presheaf span, at a
given stage. Identifies `inl (fst x)` with
`inr (snd x)` for each `x` in the apex. -/
def pshSpanPushoutRel
    (S : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))
    (c : Cᵒᵖ) :
    ((S.obj .left).obj c ⊕
      (S.obj .right).obj c) →
    ((S.obj .left).obj c ⊕
      (S.obj .right).obj c) → Prop :=
  fun x y => ∃ t : (S.obj .zero).obj c,
    x = .inl ((S.map WalkingSpan.Hom.fst).app
      c t) ∧
    y = .inr ((S.map WalkingSpan.Hom.snd).app
      c t)

/-- The presheaf action on the pushout quotient:
maps via `Sum.map` on coproduct components and
respects the quotient by naturality of the span
legs. -/
def pshSpanPushoutMap
    (S : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))
    {c d : Cᵒᵖ} (f : c ⟶ d) :
    Quot (pshSpanPushoutRel S c) →
    Quot (pshSpanPushoutRel S d) :=
  Quot.lift
    (fun x => Quot.mk _ (Sum.map
      ((S.obj .left).map f)
      ((S.obj .right).map f) x))
    (by
      rintro _ _ ⟨t, rfl, rfl⟩
      exact Quot.sound
        ⟨(S.obj .zero).map f t,
         congr_arg Sum.inl (congr_fun
          ((S.map WalkingSpan.Hom.fst).naturality
            f) t).symm,
         congr_arg Sum.inr (congr_fun
          ((S.map WalkingSpan.Hom.snd).naturality
            f) t).symm⟩)

@[simp]
theorem pshSpanPushoutMap_mk
    (S : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w))
    {c d : Cᵒᵖ} (f : c ⟶ d)
    (a : (S.obj .left).obj c ⊕
      (S.obj .right).obj c) :
    pshSpanPushoutMap S f (Quot.mk _ a) =
    Quot.mk _ (Sum.map
      ((S.obj .left).map f)
      ((S.obj .right).map f) a) :=
  rfl

/-- The pushout presheaf of a span diagram in
presheaves. At each stage, takes the quotient
of the coproduct of the feet by identifying
`inl (fst x)` with `inr (snd x)`. -/
def pshSpanPushoutObj
    (S : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :
    Cᵒᵖ ⥤ Type w where
  obj c := Quot (pshSpanPushoutRel S c)
  map f := pshSpanPushoutMap S f
  map_id c := funext (Quot.ind fun a => by
    simp only [pshSpanPushoutMap_mk,
      (S.obj .left).map_id,
      (S.obj .right).map_id]
    cases a <;> rfl)
  map_comp f g := funext (Quot.ind fun a => by
    simp only [pshSpanPushoutMap_mk,
      (S.obj .left).map_comp,
      (S.obj .right).map_comp]
    cases a <;> rfl)

/-- The cocone over a presheaf span diagram with
point given by the pointwise pushout presheaf. -/
def pshSpanPushoutCocone
    (S : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :
    Cocone S where
  pt := pshSpanPushoutObj S
  ι :=
    { app := fun j => match j with
        | .zero =>
          { app := fun c t =>
              Quot.mk _ (.inl
                ((S.map WalkingSpan.Hom.fst).app
                  c t))
            naturality := fun c d f =>
              funext fun t => by
                simp only [types_comp_apply]
                exact congr_arg (Quot.mk _ ∘
                  Sum.inl) (congr_fun
                    ((S.map WalkingSpan.Hom.fst
                      ).naturality f) t) }
        | .left =>
          { app := fun c p =>
              Quot.mk _ (.inl p)
            naturality := fun _ _ _ => rfl }
        | .right =>
          { app := fun c q =>
              Quot.mk _ (.inr q)
            naturality := fun _ _ _ => rfl }
      naturality := by
        intro X Y h
        induction h with
        | id => simp
        | init j =>
          cases j
          · ext c t; rfl
          · ext c t; simp only [NatTrans.comp_app,
              types_comp_apply,
              Functor.const_obj_map]
            exact (Quot.sound
              ⟨t, rfl, rfl⟩).symm }

/-- The pointwise pushout cocone is a colimit.
`desc` is given by pointwise `Quot.lift`. -/
def pshSpanPushoutIsColimit
    (S : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) :
    IsColimit (pshSpanPushoutCocone S) where
  desc s :=
    { app := fun c =>
        Quot.lift
          (fun x => match x with
            | .inl p => (s.ι.app .left).app c p
            | .inr q =>
              (s.ι.app .right).app c q)
          (by
            rintro _ _ ⟨t, rfl, rfl⟩
            have hsnd := congr_fun (congr_app
              (s.w WalkingSpan.Hom.snd) c) t
            simp only [NatTrans.comp_app,
              types_comp_apply] at hsnd
            have hfst := congr_fun (congr_app
              (s.w WalkingSpan.Hom.fst) c) t
            simp only [NatTrans.comp_app,
              types_comp_apply] at hfst
            dsimp
            rw [hfst, hsnd])
      naturality := fun c d f =>
        funext (Quot.ind fun a => by
          cases a with
          | inl p =>
            simp only [types_comp_apply]
            exact congr_fun
              ((s.ι.app .left).naturality f) p
          | inr q =>
            simp only [types_comp_apply]
            exact congr_fun
              ((s.ι.app .right).naturality f)
              q) }
  fac s j := by
    match j with
    | .zero =>
      ext c t
      simp only [Functor.const_obj_obj,
        NatTrans.comp_app, types_comp_apply]
      dsimp [pshSpanPushoutCocone]
      have := congr_fun (congr_app
        (s.w WalkingSpan.Hom.fst) c) t
      simp only [NatTrans.comp_app,
        types_comp_apply] at this
      exact this
    | .left => ext c p; rfl
    | .right => ext c q; rfl
  uniq s m h := by
    apply NatTrans.ext; funext c
    apply funext; apply Quot.ind; intro a
    cases a with
    | inl p =>
      have := congr_fun
        (congr_app (h .left) c) p
      simp only [Functor.const_obj_obj,
        NatTrans.comp_app,
        types_comp_apply] at this
      dsimp [pshSpanPushoutCocone] at this
      dsimp
      exact this
    | inr q =>
      have := congr_fun
        (congr_app (h .right) c) q
      simp only [Functor.const_obj_obj,
        NatTrans.comp_app,
        types_comp_apply] at this
      dsimp [pshSpanPushoutCocone] at this
      dsimp
      exact this

/-- Constructive pushouts for presheaf span diagrams
via pointwise `Quot` in `Type w`. -/
def pshSpanPushouts
    (C : Type*) [Category C] :
    (S : WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)) →
    ColimitCocone S :=
  fun S =>
    { cocone := pshSpanPushoutCocone S
      isColimit := pshSpanPushoutIsColimit S }

end PshSpanPushouts

end GebLean
