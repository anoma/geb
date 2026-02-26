import GebLean.Utilities.Profunctors
import Mathlib.CategoryTheory.Functor.FullyFaithful

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
@[reducible]
def relType {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :=
  { p : I₀ × I₁ // R p.1 p.2 }

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

/-- The opposite graph of a function `f : B → A`,
viewed as a relation `A → B → Prop`.
`graphRelOp f a b` holds iff `f b = a`. -/
def graphRelOp {A B : Type} (f : B → A)
    (a : A) (b : B) : Prop :=
  f b = a

/-- The canonical relation lifting for a functor
`F : Type ⥤ Type`. Given a relation `R` between
types `A` and `B`, `functorRelLift F R` relates
`x : F.obj A` and `y : F.obj B` iff there exists
a witness `w : F.obj {p : A × B // R p.1 p.2}`
whose projections under `F.map` give `x`
and `y`. -/
def functorRelLift
    (F : Type ⥤ Type) {A B : Type}
    (R : A → B → Prop) :
    F.obj A → F.obj B → Prop :=
  fun x y =>
    ∃ (w : F.obj (relType R)),
      F.map (fun s : relType R =>
        s.val.1) w = x ∧
      F.map (fun s : relType R =>
        s.val.2) w = y

/-- When the relation is the graph of a function
`g`, the relation lifting reduces to the graph
of `F.map g`. -/
@[simp]
theorem functorRelLift_graphRel
    (F : Type ⥤ Type) {A B : Type}
    (g : A → B) :
    functorRelLift F (graphRel g) =
    graphRel (F.map g) := by
  ext x y
  simp only [functorRelLift, graphRel]
  constructor
  · rintro ⟨w, hw₁, hw₂⟩
    rw [← hw₁, ← hw₂]
    have h₁ : (fun s : relType
        (graphRel g) => s.val.2) =
        g ∘ (fun s => s.val.1) := by
      ext ⟨⟨a, _⟩, h⟩; exact h.symm
    conv_rhs => rw [h₁]
    exact (FunctorToTypes.map_comp_apply F
      (fun s => s.val.1) g w).symm
  · intro h
    let e : A → relType (graphRel g) :=
      fun a => ⟨⟨a, g a⟩, rfl⟩
    refine ⟨F.map e x, ?_, ?_⟩
    · change F.map (fun s => s.val.1)
        (F.map e x) = x
      rw [← FunctorToTypes.map_comp_apply]
      exact FunctorToTypes.map_id_apply F x
    · change F.map (fun s => s.val.2)
        (F.map e x) = y
      rw [← FunctorToTypes.map_comp_apply]
      exact h

/-- When the relation is the opposite graph of
a function `f : B → A`, the relation lifting
reduces to the opposite graph of
`F.map f`. -/
@[simp]
theorem functorRelLift_graphRelOp
    (F : Type ⥤ Type) {A B : Type}
    (f : B → A) :
    functorRelLift F (graphRelOp f) =
    graphRelOp (F.map f) := by
  ext x y
  simp only [functorRelLift, graphRelOp]
  constructor
  · rintro ⟨w, hw₁, hw₂⟩
    rw [← hw₁, ← hw₂]
    have h₁ : (fun s : relType
        (graphRelOp f) => s.val.1) =
        f ∘ fun s => s.val.2 := by
      ext ⟨⟨_, _⟩, h⟩; exact h.symm
    conv_rhs => rw [h₁]
    exact (FunctorToTypes.map_comp_apply F
      (fun s => s.val.2) f w).symm
  · intro h
    let e : B → relType (graphRelOp f) :=
      fun b => ⟨⟨f b, b⟩, rfl⟩
    refine ⟨F.map e y, ?_, ?_⟩
    · change F.map (fun s => s.val.1)
          (F.map e y) = x
      rw [← FunctorToTypes.map_comp_apply]
      exact h
    · change F.map (fun s => s.val.2)
          (F.map e y) = y
      rw [← FunctorToTypes.map_comp_apply]
      exact FunctorToTypes.map_id_apply F y

/-- The identity functor `𝟭 Type` does not
change the relation:
`functorRelLift (𝟭 Type) R = R`. -/
@[simp]
theorem functorRelLift_id {A B : Type}
    (R : A → B → Prop) :
    functorRelLift (𝟭 Type) R = R := by
  ext a b
  constructor
  · rintro ⟨⟨⟨_, _⟩, hab⟩, rfl, rfl⟩
    exact hab
  · intro h
    exact ⟨⟨(a, b), h⟩, rfl, rfl⟩

/-- The subtype of `F.obj I₀ × F.obj I₁`
consisting of pairs in the relation lifting
of `R` through `F`. -/
def covRelImage
    (F : Type ⥤ Type) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :=
  { p : F.obj I₀ × F.obj I₁ //
    functorRelLift F R p.1 p.2 }

/-- Transport a `covRelImage` element along a
natural transformation `α : F ⟶ G`. -/
def covRelImage.map {F G : Type ⥤ Type}
    (α : F ⟶ G) {I₀ I₁ : Type}
    {R : I₀ → I₁ → Prop}
    (p : covRelImage F R) :
    covRelImage G R :=
  ⟨(α.app I₀ p.val.1, α.app I₁ p.val.2),
    p.property.elim fun w ⟨h₁, h₂⟩ =>
      ⟨α.app (relType R) w,
        (congr_fun (α.naturality
          (fun s : relType R =>
            s.val.1)) w).symm.trans
          (congr_arg (α.app I₀) h₁),
        (congr_fun (α.naturality
          (fun s : relType R =>
            s.val.2)) w).symm.trans
          (congr_arg (α.app I₁) h₂)⟩⟩

/-- The covariant embedding maps an endofunctor
`F : Type ⥤ Type` to a parametric functor.
Type-nodes map to `ULift (F.obj I)`;
relation-nodes map to
`ULift (covRelImage F R)`. Projections
extract the pair components. -/
def covariantEmbedding :
    (Type ⥤ Type) ⥤ ParametricFunctor where
  obj F :=
    { obj := fun X =>
        match X with
        | .typeNode I => ULift.{1} (F.obj I)
        | .relNode I₀ I₁ R =>
          ULift.{1} (covRelImage F R)
      map := fun {X Y} f =>
        match X, Y, f with
        | _, _, .id _ => id
        | _, _, .fstProj I₀ I₁ R =>
          fun ⟨p⟩ => ⟨p.val.1⟩
        | _, _, .sndProj I₀ I₁ R =>
          fun ⟨p⟩ => ⟨p.val.2⟩
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
          fun ⟨p⟩ => ⟨covRelImage.map α p⟩
      naturality := by
        intro X Y f
        match X, Y, f with
        | _, _, .id _ => rfl
        | _, _, .fstProj I₀ I₁ R =>
          funext ⟨p⟩; rfl
        | _, _, .sndProj I₀ I₁ R =>
          funext ⟨p⟩; rfl }
  map_id F := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      simp [covRelImage.map]
  map_comp {F G H}
      (α : F ⟶ G) (β : G ⟶ H) := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      simp [covRelImage.map]

/-- The covariant embedding is fully faithful.
The preimage extracts `typeNode` components;
fullness follows from the `relNode` component
being a subtype of the product, determined by
its projections via naturality. -/
def covariantEmbedding_fullyFaithful :
    covariantEmbedding.FullyFaithful where
  preimage {F G} β :=
    { app := fun I x =>
        (β.app (.typeNode I) ⟨x⟩).down
      naturality := fun {I₀ I₁} f => by
        funext x
        simp only [types_comp_apply]
        let e : I₀ → relType (graphRel f) :=
          fun a => ⟨⟨a, f a⟩, rfl⟩
        let p₀ : covRelImage F
            (graphRel f) :=
          ⟨(x, F.map f x),
            F.map e x,
            FunctorToTypes.map_comp_apply
              F e (fun s : relType
                (graphRel f) =>
                s.val.1) x |>.symm |>.trans
              (FunctorToTypes.map_id_apply
                F x),
            FunctorToTypes.map_comp_apply
              F e (fun s : relType
                (graphRel f) =>
                s.val.2) x |>.symm⟩
        let m := (β.app (.relNode I₀ I₁
          (graphRel f)) ⟨p₀⟩).down
        have hfst :
            m.val.1 =
              (β.app (.typeNode I₀)
                ⟨x⟩).down := by
          have := congr_fun (β.naturality
            (RelSpanHom.fstProj I₀ I₁
              (graphRel f))) ⟨p₀⟩
          exact (congr_arg ULift.down
            this).symm
        have hsnd :
            m.val.2 =
              (β.app (.typeNode I₁)
                ⟨F.map f x⟩).down := by
          have := congr_fun (β.naturality
            (RelSpanHom.sndProj I₀ I₁
              (graphRel f))) ⟨p₀⟩
          exact (congr_arg ULift.down
            this).symm
        obtain ⟨w', hw'₁, hw'₂⟩ :=
          m.property
        rw [← hfst, ← hw'₁,
          ← hsnd, ← hw'₂]
        have : (fun s : relType
            (graphRel f) => s.val.1) ≫
            f = fun s => s.val.2 :=
          funext fun s => s.property
        rw [← FunctorToTypes.map_comp_apply
          G _ f, this] }
  map_preimage {F G} β := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      have hfst :
          (β.app (.relNode I₀ I₁ R)
            ⟨p⟩).down.val.1 =
          (β.app (.typeNode I₀)
            ⟨p.val.1⟩).down := by
        exact (congr_arg ULift.down
          (congr_fun (β.naturality
            (RelSpanHom.fstProj I₀ I₁ R))
            ⟨p⟩)).symm
      have hsnd :
          (β.app (.relNode I₀ I₁ R)
            ⟨p⟩).down.val.2 =
          (β.app (.typeNode I₁)
            ⟨p.val.2⟩).down := by
        exact (congr_arg ULift.down
          (congr_fun (β.naturality
            (RelSpanHom.sndProj I₀ I₁ R))
            ⟨p⟩)).symm
      apply Prod.ext
      · exact hfst.symm
      · exact hsnd.symm

instance covariantEmbedding_faithful :
    covariantEmbedding.Faithful :=
  covariantEmbedding_fullyFaithful.faithful

instance covariantEmbedding_full :
    covariantEmbedding.Full :=
  covariantEmbedding_fullyFaithful.full

end GebLean
