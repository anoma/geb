import GebLean.Utilities.Graph

open CategoryTheory

namespace GebLean

universe u_V u_E u_D v_D

variable (V : Type u_V)
  (E : V → V → Type u_E)
  (D : Type u_D) [Category.{v_D} D]

/-- The category of span families: functors from
the graph span diagram category
`GraphSpanObj V E` to a target category `D`. -/
abbrev SpanFamily :=
  GraphSpanObj V E ⥤ D

variable {V} {E} {D}

/-- The data of a functor from `GraphSpanObj V E`
to `D`, unpacked: a family of objects at vertices,
a family of objects at edges, and two projection
morphism families. -/
@[ext]
structure SpanFamilyData where
  vertexObj : V → D
  edgeObj : (v₀ v₁ : V) → E v₀ v₁ → D
  fstProj : {v₀ v₁ : V} →
    (e : E v₀ v₁) →
    edgeObj v₀ v₁ e ⟶ vertexObj v₀
  sndProj : {v₀ v₁ : V} →
    (e : E v₀ v₁) →
    edgeObj v₀ v₁ e ⟶ vertexObj v₁

/-- A morphism of span family data: morphism
families at vertices and edges satisfying the
two naturality (commutativity) conditions. -/
@[ext]
structure SpanFamilyHom
    (F G : SpanFamilyData
      (V := V) (E := E) (D := D)) where
  vertexMap :
    (v : V) → F.vertexObj v ⟶ G.vertexObj v
  edgeMap :
    {v₀ v₁ : V} → (e : E v₀ v₁) →
    F.edgeObj v₀ v₁ e ⟶ G.edgeObj v₀ v₁ e
  fstCompat :
    {v₀ v₁ : V} → (e : E v₀ v₁) →
    edgeMap e ≫ G.fstProj e =
    F.fstProj e ≫ vertexMap v₀
  sndCompat :
    {v₀ v₁ : V} → (e : E v₀ v₁) →
    edgeMap e ≫ G.sndProj e =
    F.sndProj e ≫ vertexMap v₁

variable (V) (E) (D)

/-- Identity morphism of span family data. -/
def SpanFamilyHom.id
    (F : SpanFamilyData
      (V := V) (E := E) (D := D)) :
    SpanFamilyHom F F where
  vertexMap _ := 𝟙 _
  edgeMap _ := 𝟙 _
  fstCompat _ := by simp
  sndCompat _ := by simp

/-- Composition of span family data
morphisms. -/
def SpanFamilyHom.comp
    {F G H : SpanFamilyData
      (V := V) (E := E) (D := D)}
    (α : SpanFamilyHom F G)
    (β : SpanFamilyHom G H) :
    SpanFamilyHom F H where
  vertexMap v := α.vertexMap v ≫ β.vertexMap v
  edgeMap e := α.edgeMap e ≫ β.edgeMap e
  fstCompat e := by
    simp only [Category.assoc]
    rw [β.fstCompat, ← Category.assoc,
      α.fstCompat, Category.assoc]
  sndCompat e := by
    simp only [Category.assoc]
    rw [β.sndCompat, ← Category.assoc,
      α.sndCompat, Category.assoc]

instance : Category
    (SpanFamilyData
      (V := V) (E := E) (D := D)) where
  Hom := SpanFamilyHom
  id := SpanFamilyHom.id V E D
  comp := SpanFamilyHom.comp V E D
  id_comp := by
    intro _ _ f; ext <;> simp [
      SpanFamilyHom.comp,
      SpanFamilyHom.id]
  comp_id := by
    intro _ _ f; ext <;> simp [
      SpanFamilyHom.comp,
      SpanFamilyHom.id]
  assoc := by
    intro _ _ _ _ f g h; ext <;> simp [
      SpanFamilyHom.comp, Category.assoc]

variable {V} {E} {D}

/-- Extract `SpanFamilyData` from a functor
`F : GraphSpanObj V E ⥤ D`. -/
def SpanFamilyData.ofFunctor
    (F : SpanFamily V E D) :
    SpanFamilyData (V := V) (E := E) (D := D)
    where
  vertexObj v := F.obj (.vertexNode v)
  edgeObj v₀ v₁ e :=
    F.obj (.edgeNode v₀ v₁ e)
  fstProj e := F.map (.fstProj _ _ e)
  sndProj e := F.map (.sndProj _ _ e)

/-- Extract a `SpanFamilyHom` from a natural
transformation between functors
`F G : GraphSpanObj V E ⥤ D`. -/
def SpanFamilyHom.ofNatTrans
    {F G : SpanFamily V E D}
    (η : F ⟶ G) :
    SpanFamilyHom
      (SpanFamilyData.ofFunctor F)
      (SpanFamilyData.ofFunctor G) where
  vertexMap v := η.app (.vertexNode v)
  edgeMap e := η.app (.edgeNode _ _ e)
  fstCompat e :=
    (η.naturality (.fstProj _ _ e)).symm
  sndCompat e :=
    (η.naturality (.sndProj _ _ e)).symm

/-- Build a functor `GraphSpanObj V E ⥤ D` from
`SpanFamilyData`. -/
def SpanFamilyData.toFunctor
    (F : SpanFamilyData
      (V := V) (E := E) (D := D)) :
    SpanFamily V E D where
  obj
    | .vertexNode v => F.vertexObj v
    | .edgeNode v₀ v₁ e => F.edgeObj v₀ v₁ e
  map {X Y} f :=
    match X, Y, f with
    | _, _, .id _ => 𝟙 _
    | _, _, .fstProj v₀ v₁ e => F.fstProj e
    | _, _, .sndProj v₀ v₁ e => F.sndProj e
  map_id := by intro X; cases X <;> rfl
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | _, _, _, .id _, .id _ =>
      dsimp [CategoryStruct.comp,
        GraphSpanHom.comp]; simp
    | _, _, _, .id _, .fstProj _ _ _ =>
      dsimp [CategoryStruct.comp,
        GraphSpanHom.comp]; simp
    | _, _, _, .id _, .sndProj _ _ _ =>
      dsimp [CategoryStruct.comp,
        GraphSpanHom.comp]; simp
    | _, _, _, .fstProj _ _ _, .id _ =>
      dsimp [CategoryStruct.comp,
        GraphSpanHom.comp]; simp
    | _, _, _, .sndProj _ _ _, .id _ =>
      dsimp [CategoryStruct.comp,
        GraphSpanHom.comp]; simp

/-- Build a natural transformation from a
`SpanFamilyHom`. -/
def SpanFamilyHom.toNatTrans
    {F G : SpanFamilyData
      (V := V) (E := E) (D := D)}
    (η : SpanFamilyHom F G) :
    F.toFunctor ⟶ G.toFunctor where
  app X :=
    match X with
    | .vertexNode v => η.vertexMap v
    | .edgeNode v₀ v₁ e => η.edgeMap e
  naturality {X Y} f := by
    match X, Y, f with
    | _, _, .id _ =>
      simp [SpanFamilyData.toFunctor]
    | _, _, .fstProj v₀ v₁ e =>
      exact η.fstCompat e |>.symm
    | _, _, .sndProj v₀ v₁ e =>
      exact η.sndCompat e |>.symm

variable (V) (E) (D)

set_option backward.isDefEq.respectTransparency false in
/-- The functor extracting `SpanFamilyData` from
`SpanFamily V E D`. -/
def spanFamilyUnpack :
    SpanFamily V E D ⥤
    SpanFamilyData
      (V := V) (E := E) (D := D) where
  obj := SpanFamilyData.ofFunctor
  map := SpanFamilyHom.ofNatTrans
  map_id F := by
    change SpanFamilyHom.ofNatTrans (𝟙 F) =
      SpanFamilyHom.id V E D _
    ext <;> simp [SpanFamilyHom.ofNatTrans,
        SpanFamilyHom.id,
        SpanFamilyData.ofFunctor]
  map_comp {F G H} α β := by
    change SpanFamilyHom.ofNatTrans (α ≫ β) =
      SpanFamilyHom.comp V E D
        (SpanFamilyHom.ofNatTrans α)
        (SpanFamilyHom.ofNatTrans β)
    ext <;> simp [SpanFamilyHom.ofNatTrans,
        SpanFamilyHom.comp]

set_option backward.isDefEq.respectTransparency false in
/-- The functor assembling `SpanFamilyData`
into `SpanFamily V E D`. -/
def spanFamilyPack :
    SpanFamilyData
      (V := V) (E := E) (D := D) ⥤
    SpanFamily V E D where
  obj := SpanFamilyData.toFunctor
  map := SpanFamilyHom.toNatTrans
  map_id F := by
    change (SpanFamilyHom.id V E D F).toNatTrans
      = 𝟙 F.toFunctor
    ext X; cases X <;>
      simp [SpanFamilyHom.toNatTrans,
        SpanFamilyHom.id,
        SpanFamilyData.toFunctor]
  map_comp {F G H} α β := by
    change (SpanFamilyHom.comp V E D α β
      ).toNatTrans = α.toNatTrans ≫ β.toNatTrans
    ext X; cases X <;>
      simp [SpanFamilyHom.toNatTrans,
        SpanFamilyHom.comp]

set_option backward.isDefEq.respectTransparency false in
/-- Object-level round-trip:
`(spanFamilyPack V E D).obj
  ((spanFamilyUnpack V E D).obj F) = F`. -/
theorem spanFamily_unpack_pack_obj
    (F : SpanFamily V E D) :
    ((spanFamilyUnpack V E D).obj F
      |> (spanFamilyPack V E D).obj) = F :=
  _root_.CategoryTheory.Functor.ext
    (fun X => by cases X <;> rfl)
    (fun {X Y} f => by
      match X, Y, f with
      | _, _, .id X =>
        cases X <;> (
          simp only [eqToHom_refl,
            Category.comp_id,
            Category.id_comp]
          exact (F.map_id _).symm)
      | _, _, .fstProj _ _ _ =>
        simp [SpanFamilyData.toFunctor,
          SpanFamilyData.ofFunctor,
          spanFamilyUnpack, spanFamilyPack]
      | _, _, .sndProj _ _ _ =>
        simp [SpanFamilyData.toFunctor,
          SpanFamilyData.ofFunctor,
          spanFamilyUnpack, spanFamilyPack])

set_option backward.isDefEq.respectTransparency false in
/-- `spanFamilyPack ⋙ spanFamilyUnpack` is
naturally isomorphic to the identity on
`SpanFamilyData`. -/
def spanFamily_pack_unpack_iso :
    spanFamilyPack V E D ⋙
    spanFamilyUnpack V E D ≅
    𝟭 _ := by
  refine NatIso.ofComponents
    (fun F => ?_) (fun {F G} η => ?_)
  · exact Iso.refl _
  · dsimp [spanFamilyPack, spanFamilyUnpack]
    simp only [Category.comp_id, Category.id_comp]
    apply SpanFamilyHom.ext <;> (funext; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- `spanFamilyUnpack ⋙ spanFamilyPack` is
naturally isomorphic to the identity on
`SpanFamily V E D`. -/
def spanFamily_unpack_pack_iso :
    spanFamilyUnpack V E D ⋙
    spanFamilyPack V E D ≅
    𝟭 _ := by
  refine NatIso.ofComponents
    (fun F => eqToIso
      (spanFamily_unpack_pack_obj V E D F))
    (fun {F G} η => ?_)
  ext X
  cases X <;>
    simp [spanFamilyUnpack, spanFamilyPack,
      SpanFamilyHom.ofNatTrans,
      SpanFamilyHom.toNatTrans,
      SpanFamilyData.toFunctor]

/-- The category of `SpanFamilyData` is
equivalent to `SpanFamily V E D`. -/
def spanFamilyEquiv :
    SpanFamilyData
      (V := V) (E := E) (D := D) ≌
    SpanFamily V E D where
  functor := spanFamilyPack V E D
  inverse := spanFamilyUnpack V E D
  unitIso :=
    (spanFamily_pack_unpack_iso V E D).symm
  counitIso :=
    spanFamily_unpack_pack_iso V E D
  functor_unitIso_comp X := by
    ext Y
    cases Y <;>
      simp [spanFamilyPack, spanFamilyUnpack,
        spanFamily_pack_unpack_iso,
        spanFamily_unpack_pack_iso,
        SpanFamilyData.toFunctor,
        SpanFamilyData.ofFunctor]

variable {V} {E} {D}

/-- The identity extension property for span
family data: on identity relations, both
projections coincide and are isomorphisms.

Given `idRel : (v : V) → E v v` designating
an "identity relation" for each vertex, a
`SpanFamilyData` satisfies the identity extension
property if `fstProj (idRel v) = sndProj (idRel v)`
and this common morphism is an isomorphism.

This property distinguishes "parametric" from
"non-parametric" functors on span diagram
categories (Hermida/Reddy/Robinson 2014,
Definition 6.1 and equation (14)). -/
structure HasIdentityExtension
    (F : SpanFamilyData
      (V := V) (E := E) (D := D))
    (idRel : (v : V) → E v v) : Prop where
  fstEqSnd :
    ∀ (v : V),
    F.fstProj (idRel v) = F.sndProj (idRel v)
  fstIsIso :
    ∀ (v : V), IsIso (F.fstProj (idRel v))

/-- When the identity extension property holds,
`sndProj (idRel v)` is also an isomorphism. -/
theorem HasIdentityExtension.sndIsIso
    {F : SpanFamilyData
      (V := V) (E := E) (D := D)}
    {idRel : (v : V) → E v v}
    (h : HasIdentityExtension F idRel)
    (v : V) : IsIso (F.sndProj (idRel v)) := by
  rw [← h.fstEqSnd v]; exact h.fstIsIso v

/-- A `SpanFamilyData` has jointly monic
projections if for each edge `e`, the pair
`(fstProj e, sndProj e)` is jointly monic:
any two morphisms into the edge object that
agree on both projections are equal. -/
structure HasJointlyMonicProjections
    (G : SpanFamilyData
      (V := V) (E := E) (D := D)) :
    Prop where
  jointly_monic :
    ∀ {v₀ v₁ : V} (e : E v₀ v₁)
      {X : D}
      (f g : X ⟶ G.edgeObj v₀ v₁ e),
      f ≫ G.fstProj e =
        g ≫ G.fstProj e →
      f ≫ G.sndProj e =
        g ≫ G.sndProj e →
      f = g

/-- When the target span family has jointly monic
projections, a `SpanFamilyHom` is determined by
its `vertexMap` components alone (Hermida/Reddy/
Robinson Fact 6.6: parametricity subsumes
naturality). -/
theorem spanFamilyHom_ext_vertexMap
    {F G : SpanFamilyData
      (V := V) (E := E) (D := D)}
    (hG : HasJointlyMonicProjections G)
    {α β : SpanFamilyHom F G}
    (hv : α.vertexMap = β.vertexMap) :
    α = β := by
  apply SpanFamilyHom.ext
  · exact hv
  · funext v₀ v₁ e
    apply hG.jointly_monic e
    · rw [α.fstCompat e, β.fstCompat e,
        congr_fun hv v₀]
    · rw [α.sndCompat e, β.sndCompat e,
        congr_fun hv v₁]

/-- When the identity extension property holds,
`fstProj (idRel v)` is an isomorphism and hence
a monomorphism, so agreement on the first
projection at identity edges implies equality. -/
theorem HasIdentityExtension.monicProjectionAt
    {F : SpanFamilyData
      (V := V) (E := E) (D := D)}
    {idRel : (v : V) → E v v}
    (h : HasIdentityExtension F idRel)
    (v : V) {X : D}
    (f g : X ⟶ F.edgeObj v v (idRel v))
    (hfst :
      f ≫ F.fstProj (idRel v) =
      g ≫ F.fstProj (idRel v)) :
    f = g := by
  have : IsIso (F.fstProj (idRel v)) :=
    h.fstIsIso v
  exact (cancel_mono (F.fstProj (idRel v))).mp
    hfst

end GebLean
