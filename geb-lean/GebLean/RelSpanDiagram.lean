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

end GebLean
