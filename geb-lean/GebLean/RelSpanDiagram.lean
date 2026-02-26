import GebLean.Utilities.Profunctors

/-!
# Relational Span Category

The diagram category `RelSpanObj` is a bipartite
category whose objects are either type-nodes (one per
`Type`) or relation-nodes (one per relation
`R : I₀ → I₁ → Prop`), with projections from
relation-nodes to their endpoint type-nodes.

The category is isomorphic to the collage of
`relSpanProfunctor`.
-/

open CategoryTheory

namespace GebLean

/-- Objects of the relational span category:
either a type-node for a type `I`, or a
relation-node for a relation `R : I₀ → I₁ → Prop`. -/
inductive RelSpanObj : Type 1 where
  | typeNode : Type → RelSpanObj
  | relNode :
    (I₀ I₁ : Type) →
    (I₀ → I₁ → Prop) → RelSpanObj

/-- Morphisms of the relational span category:
identity morphisms for each object, and a pair
of projections from each relation-node to
its endpoint type-nodes. -/
inductive RelSpanHom :
    RelSpanObj → RelSpanObj → Type 1 where
  | id : (X : RelSpanObj) → RelSpanHom X X
  | fstProj :
    (I₀ I₁ : Type) →
    (R : I₀ → I₁ → Prop) →
    RelSpanHom (.relNode I₀ I₁ R) (.typeNode I₀)
  | sndProj :
    (I₀ I₁ : Type) →
    (R : I₀ → I₁ → Prop) →
    RelSpanHom (.relNode I₀ I₁ R) (.typeNode I₁)

/-- Composition of morphisms in `RelSpanObj`.
No composable pair of non-identity morphisms
exists, since all generators map from
relation-nodes to type-nodes. -/
def RelSpanHom.comp :
    {X Y Z : RelSpanObj} →
    RelSpanHom X Y →
    RelSpanHom Y Z →
    RelSpanHom X Z
  | _, _, _, .id _, g => g
  | _, _, _, f, .id _ => f

instance RelSpanCatStruct : CategoryStruct RelSpanObj where
  Hom := RelSpanHom
  id := RelSpanHom.id
  comp := RelSpanHom.comp

theorem RelSpanHom.id_comp
    {X Y : RelSpanObj} (f : RelSpanHom X Y) :
    RelSpanHom.comp (.id X) f = f := by
  cases f <;> rfl

theorem RelSpanHom.comp_id
    {X Y : RelSpanObj} (f : RelSpanHom X Y) :
    RelSpanHom.comp f (.id Y) = f := by
  cases f <;> rfl

theorem RelSpanHom.assoc
    {W X Y Z : RelSpanObj}
    (f : RelSpanHom W X)
    (g : RelSpanHom X Y)
    (h : RelSpanHom Y Z) :
    RelSpanHom.comp (RelSpanHom.comp f g) h =
    RelSpanHom.comp f (RelSpanHom.comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance RelSpanCat : Category RelSpanObj where
  id_comp := RelSpanHom.id_comp
  comp_id := RelSpanHom.comp_id
  assoc := RelSpanHom.assoc

/-- Index type for relation-nodes: a triple
`(I₀, I₁, R)` where `R : I₀ → I₁ → Prop`. -/
abbrev RelIndex :=
  Σ (I₀ I₁ : Type), I₀ → I₁ → Prop

/-- The type of endpoint projections from a
relation with endpoints `I₀`, `I₁` to a type
`I`.  An element witnesses that `I` is one of
the endpoints. -/
inductive EndpointProj
    (I₀ I₁ I : Type) : Type where
  | fst : I₀ = I → EndpointProj I₀ I₁ I
  | snd : I₁ = I → EndpointProj I₀ I₁ I

/-- The profunctor whose collage is the relational
span category.  Maps `(op ⟨r⟩, ⟨I⟩)` to the type
of endpoint projections from `r` to `I`, lifted
to `Type 1`. -/
def relSpanProfunctor :
    (Discrete RelIndex)ᵒᵖ ×
    (Discrete Type) ⥤ Type 1 where
  obj p :=
    ULift.{1} (EndpointProj
      p.1.unop.as.1 p.1.unop.as.2.1
      p.2.as)
  map {p q} f := eqToHom (by
    obtain ⟨⟨⟨r₁⟩⟩, ⟨I₁⟩⟩ := p
    obtain ⟨⟨⟨r₂⟩⟩, ⟨I₂⟩⟩ := q
    have h₁ : r₂ = r₁ :=
      Discrete.eq_of_hom f.1.unop
    have h₂ : I₁ = I₂ :=
      Discrete.eq_of_hom f.2
    subst h₁; subst h₂; rfl)
  map_id _ := by simp
  map_comp _ _ := by simp

/-- Functor from `RelSpanObj` to the collage of
`relSpanProfunctor`, sending type-nodes to the
right component and relation-nodes to the left
component. -/
def relSpanToCollage :
    RelSpanObj ⥤ Collage relSpanProfunctor where
  obj
    | .typeNode I => Collage.inr ⟨I⟩
    | .relNode I₀ I₁ R =>
      Collage.inl ⟨⟨I₀, I₁, R⟩⟩
  map {X Y} f :=
    match X, Y, f with
    | .typeNode I, _, .id _ => ⟨𝟙 _⟩
    | .relNode I₀ I₁ R, _, .id _ => ⟨𝟙 _⟩
    | _, _, .fstProj I₀ I₁ R =>
      ⟨⟨EndpointProj.fst rfl⟩⟩
    | _, _, .sndProj I₀ I₁ R =>
      ⟨⟨EndpointProj.snd rfl⟩⟩
  map_id := by intro X; cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g
    all_goals
      first
      | (cases ‹RelSpanObj›
         all_goals rfl)
      | (simp only [CategoryStruct.comp,
           RelSpanHom.comp]
         apply ULift.ext
         dsimp [Collage.Hom.comp,
           Collage.inl, Collage.inr]
         simp [relSpanProfunctor])

/-- Object map for `collageToRelSpan`. -/
def collageToRelSpanObj :
    Collage relSpanProfunctor → RelSpanObj
  | ⟨.inl ⟨⟨I₀, I₁, R⟩⟩⟩ =>
    .relNode I₀ I₁ R
  | ⟨.inr ⟨I⟩⟩ => .typeNode I

/-- Morphism map for `collageToRelSpan`. -/
def collageToRelSpanMap
    {X Y : Collage relSpanProfunctor}
    (f : X ⟶ Y) :
    collageToRelSpanObj X ⟶
    collageToRelSpanObj Y := by
  match X, Y, f with
  | ⟨.inl ⟨r⟩⟩, ⟨.inl ⟨r'⟩⟩, f =>
    have h : r = r' := f.down.down.down
    subst h; exact .id _
  | ⟨.inr ⟨I⟩⟩, ⟨.inr ⟨I'⟩⟩, f =>
    have h : I = I' := f.down.down.down
    subst h; exact .id _
  | ⟨.inl ⟨⟨I₀, I₁, R⟩⟩⟩, ⟨.inr ⟨I⟩⟩, f =>
    have p : EndpointProj I₀ I₁ I :=
      f.down.down
    exact p.casesOn
      (fun h => h ▸ .fstProj I₀ I₁ R)
      (fun h => h ▸ .sndProj I₀ I₁ R)
  | ⟨.inr _⟩, ⟨.inl _⟩, f =>
    exact PEmpty.elim f

@[simp]
theorem collageToRelSpanMap_id_inl
    (r : RelIndex) :
    collageToRelSpanMap
      (𝟙 (Collage.inl (P := relSpanProfunctor)
        ⟨r⟩)) =
    .id (.relNode r.1 r.2.1 r.2.2) := rfl

@[simp]
theorem collageToRelSpanMap_id_inr
    (I : Type) :
    collageToRelSpanMap
      (𝟙 (Collage.inr (P := relSpanProfunctor)
        ⟨I⟩)) =
    .id (.typeNode I) := rfl

@[simp]
theorem collageToRelSpanMap_fst
    (I₀ I₁ : Type) (R : I₀ → I₁ → Prop) :
    collageToRelSpanMap
      (show Collage.inl
        (P := relSpanProfunctor)
        ⟨⟨I₀, I₁, R⟩⟩ ⟶
        Collage.inr ⟨I₀⟩
        from ⟨⟨EndpointProj.fst rfl⟩⟩) =
    .fstProj I₀ I₁ R := rfl

@[simp]
theorem collageToRelSpanMap_snd
    (I₀ I₁ : Type) (R : I₀ → I₁ → Prop) :
    collageToRelSpanMap
      (show Collage.inl
        (P := relSpanProfunctor)
        ⟨⟨I₀, I₁, R⟩⟩ ⟶
        Collage.inr ⟨I₁⟩
        from ⟨⟨EndpointProj.snd rfl⟩⟩) =
    .sndProj I₀ I₁ R := rfl

/-- Functor from the collage of
`relSpanProfunctor` back to `RelSpanObj`. -/
def collageToRelSpan :
    Collage relSpanProfunctor ⥤
    RelSpanObj where
  obj := collageToRelSpanObj
  map := collageToRelSpanMap
  map_id := by
    intro ⟨X⟩
    match X with
    | .inl ⟨_⟩ => rfl
    | .inr ⟨_⟩ => rfl
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g
    match X, Y, Z, f, g with
    | .inl ⟨_⟩, .inl ⟨_⟩, .inl ⟨_⟩,
      ⟨f⟩, ⟨g⟩ =>
      have := f.down.down
      have := g.down.down
      subst_vars; rfl
    | .inr ⟨_⟩, .inr ⟨_⟩, .inr ⟨_⟩,
      ⟨f⟩, ⟨g⟩ =>
      have := f.down.down
      have := g.down.down
      subst_vars; rfl
    | .inl ⟨_⟩, .inl ⟨_⟩, .inr ⟨_⟩,
      ⟨f⟩, ⟨h⟩ =>
      have := f.down.down
      subst_vars
      have p : EndpointProj _ _ _ :=
        h.down
      cases p <;> rfl
    | .inl ⟨_⟩, .inr ⟨_⟩, .inr ⟨_⟩,
      ⟨h⟩, ⟨g⟩ =>
      have := g.down.down
      subst_vars
      have p : EndpointProj _ _ _ :=
        h.down
      cases p <;>
        simp [collageToRelSpanMap,
          collageToRelSpanObj,
          Collage.Hom.comp,
          CategoryStruct.comp,
          RelSpanHom.comp,
          relSpanProfunctor]
    | .inr _, .inl _, _, f, _ =>
      exact PEmpty.elim f
    | .inl _, .inr _, .inl _,
      _, g => exact PEmpty.elim g
    | .inr _, .inr _, .inl _,
      _, g => exact PEmpty.elim g

/-- `RelSpanObj` is categorically isomorphic to the
collage of `relSpanProfunctor`. -/
-- The hom_inv_id direction (RelSpan round-trip)
-- needs lemmas showing the composite map
-- acts as the identity on each morphism type.
theorem relSpanCollage_hom_inv_obj
    (X : RelSpanObj) :
    collageToRelSpanObj
      (relSpanToCollage.obj X) = X := by
  cases X <;> rfl

theorem relSpanCollage_hom_inv_map
    {X Y : RelSpanObj}
    (f : X ⟶ Y) :
    collageToRelSpanMap
      (relSpanToCollage.map f) =
    eqToHom (relSpanCollage_hom_inv_obj X) ≫
      f ≫
      eqToHom
        (relSpanCollage_hom_inv_obj Y).symm := by
  cases f with
  | id X =>
    simp only [relSpanToCollage]
    cases X <;> rfl
  | fstProj I₀ I₁ R =>
    simp only [relSpanToCollage]
    exact collageToRelSpanMap_fst I₀ I₁ R
  | sndProj I₀ I₁ R =>
    simp only [relSpanToCollage]
    exact collageToRelSpanMap_snd I₀ I₁ R

theorem relSpanCollage_inv_hom_obj
    (X : Collage relSpanProfunctor) :
    relSpanToCollage.obj
      (collageToRelSpanObj X) = X := by
  match X with
  | ⟨.inl ⟨_⟩⟩ => rfl
  | ⟨.inr ⟨_⟩⟩ => rfl

theorem relSpanCollage_inv_hom_map_fst
    (I₀ I₁ : Type) (R : I₀ → I₁ → Prop) :
    relSpanToCollage.map
      (collageToRelSpanMap
        (show Collage.inl
          (P := relSpanProfunctor)
          ⟨⟨I₀, I₁, R⟩⟩ ⟶ Collage.inr ⟨I₀⟩
          from ⟨⟨EndpointProj.fst rfl⟩⟩)) =
    ⟨⟨EndpointProj.fst rfl⟩⟩ := by
  rfl

theorem relSpanCollage_inv_hom_map_snd
    (I₀ I₁ : Type) (R : I₀ → I₁ → Prop) :
    relSpanToCollage.map
      (collageToRelSpanMap
        (show Collage.inl
          (P := relSpanProfunctor)
          ⟨⟨I₀, I₁, R⟩⟩ ⟶ Collage.inr ⟨I₁⟩
          from ⟨⟨EndpointProj.snd rfl⟩⟩)) =
    ⟨⟨EndpointProj.snd rfl⟩⟩ := by
  rfl

def relSpanCollageIso :
    RelSpanObj ≅Cat
    Collage relSpanProfunctor where
  hom := relSpanToCollage.toCatHom
  inv := collageToRelSpan.toCatHom
  hom_inv_id := by
    change (relSpanToCollage ⋙
      collageToRelSpan).toCatHom =
      (𝟭 _).toCatHom
    congr 1
    exact _root_.CategoryTheory.Functor.ext
      (relSpanCollage_hom_inv_obj)
      (fun {X Y} f =>
        relSpanCollage_hom_inv_map f)
  inv_hom_id := by
    change (collageToRelSpan ⋙
      relSpanToCollage).toCatHom =
      (𝟭 _).toCatHom
    congr 1
    exact _root_.CategoryTheory.Functor.ext
      (relSpanCollage_inv_hom_obj)
      (fun {X Y} f => by
        match X, Y, f with
        | ⟨.inl ⟨_⟩⟩, ⟨.inl ⟨_⟩⟩, ⟨g⟩ =>
          have := g.down.down
          subst_vars
          dsimp [collageToRelSpan,
            collageToRelSpanMap,
            collageToRelSpanObj,
            relSpanToCollage,
            relSpanCollage_inv_hom_obj]
          rfl
        | ⟨.inr ⟨_⟩⟩, ⟨.inr ⟨_⟩⟩, ⟨g⟩ =>
          have := g.down.down
          subst_vars
          dsimp [collageToRelSpan,
            collageToRelSpanMap,
            collageToRelSpanObj,
            relSpanToCollage,
            relSpanCollage_inv_hom_obj]
          rfl
        | ⟨.inl ⟨⟨I₀, I₁, R⟩⟩⟩,
          ⟨.inr ⟨_⟩⟩, ⟨h⟩ =>
          simp only [
            eqToHom_refl, Category.id_comp,
            Category.comp_id, Functor.id_map,
            Functor.comp_map]
          cases h with
          | up p =>
            cases p with
            | fst hp =>
              cases hp
              simp only [collageToRelSpan]
              rfl
            | snd hp =>
              cases hp
              simp only [collageToRelSpan]
              rfl
        | ⟨.inr _⟩, ⟨.inl _⟩, f =>
          exact PEmpty.elim f)

/-- The category of parametric functors:
copresheaves on `RelSpanObj`. -/
abbrev ParametricFunctor := RelSpanObj ⥤ Type 1

/-- The type of related pairs under a relation
`R : I₀ → I₁ → Prop`. -/
def relType {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :=
  { p : I₀ × I₁ // R p.1 p.2 }

/-- The covariant embedding maps an endofunctor
`F : Type ⥤ Type` to a parametric functor.
Type-nodes map to `ULift (F.obj I)`;
relation-nodes map to
`ULift (F.obj (relType R))`; projections are
induced by `F.map` applied to the component
projections of `relType R`. -/
def covariantEmbedding :
    (Type ⥤ Type) ⥤ ParametricFunctor where
  obj F :=
    { obj := fun X =>
        match X with
        | .typeNode I => ULift.{1} (F.obj I)
        | .relNode I₀ I₁ R =>
          ULift.{1} (F.obj (relType R))
      map := fun {X Y} f =>
        match X, Y, f with
        | _, _, .id _ => id
        | _, _, .fstProj I₀ I₁ R =>
          ULift.up ∘ F.map
            (fun (s : relType R) => s.val.1) ∘
            ULift.down
        | _, _, .sndProj I₀ I₁ R =>
          ULift.up ∘ F.map
            (fun (s : relType R) => s.val.2) ∘
            ULift.down
      map_id := by
        intro X; cases X <;> rfl
      map_comp := by
        intro X Y Z f g
        cases f <;> cases g <;> rfl }
  map {F G} (α : F ⟶ G) :=
    { app := fun X =>
        match X with
        | .typeNode I =>
          ULift.up ∘ α.app I ∘ ULift.down
        | .relNode I₀ I₁ R =>
          ULift.up ∘ α.app (relType R) ∘
            ULift.down
      naturality := by
        intro X Y f
        cases f with
        | id => rfl
        | fstProj I₀ I₁ R =>
          funext ⟨x⟩
          change ULift.up (α.app I₀
            (F.map _ x)) =
            ULift.up (G.map _
              (α.app _ x))
          congr 1
          exact congr_fun
            (α.naturality _) x
        | sndProj I₀ I₁ R =>
          funext ⟨x⟩
          change ULift.up (α.app I₁
            (F.map _ x)) =
            ULift.up (G.map _
              (α.app _ x))
          congr 1
          exact congr_fun
            (α.naturality _) x }
  map_id F := by
    ext X x
    cases X <;> simp
  map_comp {F G H} (α : F ⟶ G) (β : G ⟶ H) := by
    ext X x
    cases X <;> simp

/-- The graph relation of `f : I₀ → I₁`:
`graphRel f a b ↔ f a = b`. -/
def graphRel {I₀ I₁ : Type} (f : I₀ → I₁) :
    I₀ → I₁ → Prop :=
  fun a b => f a = b

/-- The canonical isomorphism between `I₀` and
`relType (graphRel f)`: every `a : I₀` maps to
`⟨(a, f a), rfl⟩`. -/
def graphRelEquiv {I₀ I₁ : Type}
    (f : I₀ → I₁) :
    I₀ ≃ relType (graphRel f) where
  toFun a := ⟨(a, f a), rfl⟩
  invFun s := s.val.1
  left_inv _ := rfl
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact s.property

/-- The canonical map from `I₀` to
`relType (graphRel f)`. -/
def graphRelInj {I₀ I₁ : Type}
    (f : I₀ → I₁) :
    I₀ → relType (graphRel f) :=
  fun a => ⟨(a, f a), rfl⟩

/-- Composition of `graphRelInj f` with the
first projection is the identity. -/
theorem graphRelInj_comp_fst
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    (fun (s : relType (graphRel f)) =>
      s.val.1) ∘ graphRelInj f = id :=
  rfl

/-- Composition of `graphRelInj f` with the
second projection is `f`. -/
theorem graphRelInj_comp_snd
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    (fun (s : relType (graphRel f)) =>
      s.val.2) ∘ graphRelInj f = f :=
  rfl

/-- On `relType (graphRel f)`, the second
projection equals `f` composed with the first
projection. -/
theorem relType_graphRel_snd_eq_comp_fst
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (s : relType (graphRel f)) :
    s.val.2 = f s.val.1 :=
  s.property.symm

/-- The preimage of a natural transformation
`β : covariantEmbedding.obj F ⟶
covariantEmbedding.obj G` is a natural
transformation `F ⟶ G`, extracted from the
typeNode components. -/
def covariantEmbedding_preimage
    {F G : Type ⥤ Type}
    (β : covariantEmbedding.obj F ⟶
      covariantEmbedding.obj G) :
    F ⟶ G where
  app I x :=
    (β.app (.typeNode I) ⟨x⟩).down
  naturality {I₀ I₁} f := by
    funext x
    simp only [types_comp_apply]
    -- m is the relational witness
    set y := F.map (graphRelInj f) x
    set m := (β.app
      (.relNode I₀ I₁ (graphRel f))
      ⟨y⟩).down with hm_def
    -- fstProj naturality of β
    have hfst := congr_arg ULift.down
      (congr_fun (β.naturality
        (RelSpanHom.fstProj I₀ I₁
          (graphRel f))) ⟨y⟩)
    simp only [types_comp_apply,
      covariantEmbedding,
      Function.comp] at hfst
    -- F.map π₁ y = x
    have hfst_y :
        F.map (fun s : relType
          (graphRel f) => s.val.1) y =
        x := by
      change (F.map (graphRelInj f) ≫
        F.map _) x = x
      rw [← F.map_comp,
        show (graphRelInj f ≫
          (fun s : relType (graphRel f) =>
            s.val.1)) = 𝟙 I₀ from rfl,
        F.map_id]
      rfl
    -- sndProj naturality of β
    have hsnd := congr_arg ULift.down
      (congr_fun (β.naturality
        (RelSpanHom.sndProj I₀ I₁
          (graphRel f))) ⟨y⟩)
    simp only [types_comp_apply,
      covariantEmbedding,
      Function.comp] at hsnd
    -- F.map π₂ y = F.map f x
    have hsnd_y :
        F.map (fun s : relType
          (graphRel f) => s.val.2) y =
        F.map f x := by
      change (F.map (graphRelInj f) ≫
        F.map _) x = F.map f x
      rw [← F.map_comp,
        show (graphRelInj f ≫
          (fun s : relType (graphRel f) =>
            s.val.2)) = f from rfl]
    -- G.map (f ∘ π₁) = G.map π₂
    have hcomp : G.map
        (fun s : relType (graphRel f) =>
          f s.val.1) =
        G.map
          (fun s : relType (graphRel f) =>
            s.val.2) := by
      congr 1; funext s
      exact (relType_graphRel_snd_eq_comp_fst
        f s).symm
    -- Combine: goal is β(.typeNode I₁)(F.map f x)
    --   = G.map f (β(.typeNode I₀)(x))
    -- From hfst: β(.typeNode I₀)(π₁ y)
    --   = G.map π₁ m
    -- From hsnd: β(.typeNode I₁)(π₂ y)
    --   = G.map π₂ m
    -- With hfst_y: π₁ y = x, hsnd_y: π₂ y = f x
    conv_lhs =>
      rw [← hsnd_y]
      rw [hsnd]
    conv_rhs =>
      rw [← hfst_y]
      rw [hfst]
    -- Goal: G.map π₂ m = G.map f (G.map π₁ m)
    have h :
        (G.map (fun s : relType
          (graphRel f) => s.val.1) ≫
          G.map f) m =
        G.map f (G.map (fun s =>
          s.val.1) m) := rfl
    rw [← h, ← G.map_comp]
    exact congr_fun hcomp.symm m

end GebLean
