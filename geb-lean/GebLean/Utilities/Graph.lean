import Mathlib.CategoryTheory.Category.Basic
import GebLean.Utilities.Profunctors

/-!
# Graph Span Diagram Category

Given a type `V` of vertices and a family
`E : V → V → Type` of edges, the graph span
diagram category `GraphSpanObj V E` has:
- a vertex-node for each `v : V`,
- an edge-node for each `e : E v₀ v₁`,
- projections from each edge-node to its two
  endpoint vertex-nodes.

No composable pair of non-identity morphisms
exists, since all generators map from
edge-nodes to vertex-nodes.

Both `RelSpanObj` and `PshRelSpanObj C` are
instances of this construction.
-/

open CategoryTheory

namespace GebLean

universe u_V u_E

variable (V : Type u_V) (E : V → V → Type u_E)

/-- Objects of the graph span diagram category:
either a vertex-node for some `v : V`, or an
edge-node for some `e : E v₀ v₁`. -/
inductive GraphSpanObj :
    Type (max u_V u_E) where
  | vertexNode : V → GraphSpanObj
  | edgeNode :
    (v₀ v₁ : V) → E v₀ v₁ → GraphSpanObj

/-- Morphisms of the graph span diagram
category: identity morphisms for each object,
and a pair of projections from each edge-node
to its endpoint vertex-nodes. -/
inductive GraphSpanHom :
    GraphSpanObj V E →
    GraphSpanObj V E →
    Type (max u_V u_E) where
  | id : (X : GraphSpanObj V E) →
    GraphSpanHom X X
  | fstProj :
    (v₀ v₁ : V) →
    (e : E v₀ v₁) →
    GraphSpanHom (.edgeNode v₀ v₁ e)
      (.vertexNode v₀)
  | sndProj :
    (v₀ v₁ : V) →
    (e : E v₀ v₁) →
    GraphSpanHom (.edgeNode v₀ v₁ e)
      (.vertexNode v₁)

/-- Composition of morphisms in
`GraphSpanObj V E`. No composable pair of
non-identity morphisms exists, since all
generators map from edge-nodes to
vertex-nodes. -/
def GraphSpanHom.comp :
    {X Y Z : GraphSpanObj V E} →
    GraphSpanHom V E X Y →
    GraphSpanHom V E Y Z →
    GraphSpanHom V E X Z
  | _, _, _, .id _, g => g
  | _, _, _, f, .id _ => f

instance GraphSpanCatStruct :
    CategoryStruct
      (GraphSpanObj V E) where
  Hom := GraphSpanHom V E
  id X := GraphSpanHom.id X
  comp := GraphSpanHom.comp V E

theorem GraphSpanHom.id_comp
    {X Y : GraphSpanObj V E}
    (f : GraphSpanHom V E X Y) :
    GraphSpanHom.comp V E (.id X) f = f := by
  cases f <;> rfl

theorem GraphSpanHom.comp_id
    {X Y : GraphSpanObj V E}
    (f : GraphSpanHom V E X Y) :
    GraphSpanHom.comp V E f (.id Y) = f := by
  cases f <;> rfl

theorem GraphSpanHom.assoc
    {W X Y Z : GraphSpanObj V E}
    (f : GraphSpanHom V E W X)
    (g : GraphSpanHom V E X Y)
    (h : GraphSpanHom V E Y Z) :
    GraphSpanHom.comp V E
      (GraphSpanHom.comp V E f g) h =
    GraphSpanHom.comp V E f
      (GraphSpanHom.comp V E g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance GraphSpanCat :
    SmallCategory.{max u_V u_E}
      (GraphSpanObj V E) where
  id_comp := GraphSpanHom.id_comp V E
  comp_id := GraphSpanHom.comp_id V E
  assoc := GraphSpanHom.assoc V E

instance [Inhabited V] :
    Inhabited (GraphSpanObj V E) :=
  ⟨.vertexNode default⟩

section GraphSpanCollage

/-- Index type for edge-nodes in the collage
construction: a triple `(v₀, v₁, e)` where
`e : E v₀ v₁`. -/
abbrev GraphEdgeIndex :=
  Σ (v₀ v₁ : V), E v₀ v₁

/-- Endpoint projection from an edge with
endpoints `v₀`, `v₁` to a vertex.  An element
witnesses that the vertex is one of the
endpoints. -/
inductive GraphEndpointProj
    (v₀ v₁ : V) : V → Type where
  | fst : GraphEndpointProj v₀ v₁ v₀
  | snd : GraphEndpointProj v₀ v₁ v₁

/-- The profunctor whose collage is the graph
span diagram category.  Maps
`(op ⟨e⟩, ⟨v⟩)` to the type of endpoint
projections from `e` to `v`, lifted to
`Type (max u_V u_E)`. -/
def graphSpanProfunctor :
    (Discrete (GraphEdgeIndex V E))ᵒᵖ ×
    (Discrete V) ⥤
    Type (max u_V u_E) where
  obj p :=
    ULift.{max u_V u_E}
      (GraphEndpointProj V
        p.1.unop.as.1 p.1.unop.as.2.1
        p.2.as)
  map {p q} f := eqToHom (by
    obtain ⟨⟨⟨e₁⟩⟩, ⟨v₁⟩⟩ := p
    obtain ⟨⟨⟨e₂⟩⟩, ⟨v₂⟩⟩ := q
    have h₁ : e₂ = e₁ :=
      Discrete.eq_of_hom f.1.unop
    have h₂ : v₁ = v₂ :=
      Discrete.eq_of_hom f.2
    subst h₁; subst h₂; rfl)
  map_id _ := by simp
  map_comp _ _ := by simp

/-- Functor from `GraphSpanObj V E` to the
collage of `graphSpanProfunctor V E`, sending
vertex-nodes to the right component and
edge-nodes to the left component. -/
def graphSpanToCollage :
    GraphSpanObj V E ⥤
    Collage (graphSpanProfunctor V E) where
  obj
    | .vertexNode v =>
      Collage.inr ⟨v⟩
    | .edgeNode v₀ v₁ e =>
      Collage.inl ⟨⟨v₀, v₁, e⟩⟩
  map {X Y} f :=
    match X, Y, f with
    | .vertexNode _, _, .id _ => ⟨𝟙 _⟩
    | .edgeNode _ _ _, _, .id _ => ⟨𝟙 _⟩
    | _, _, .fstProj v₀ v₁ e =>
      ⟨⟨GraphEndpointProj.fst⟩⟩
    | _, _, .sndProj v₀ v₁ e =>
      ⟨⟨GraphEndpointProj.snd⟩⟩
  map_id := by intro X; cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g
    all_goals
      first
      | (cases ‹GraphSpanObj V E›
         all_goals rfl)
      | (simp only [CategoryStruct.comp,
           GraphSpanHom.comp]
         apply ULift.ext
         dsimp [Collage.Hom.comp,
           Collage.inl, Collage.inr]
         simp [graphSpanProfunctor])

/-- Object map for `collageToGraphSpan`. -/
def collageToGraphSpanObj :
    Collage (graphSpanProfunctor V E) →
    GraphSpanObj V E
  | ⟨.inl ⟨⟨v₀, v₁, e⟩⟩⟩ =>
    .edgeNode v₀ v₁ e
  | ⟨.inr ⟨v⟩⟩ => .vertexNode v

/-- Morphism map for `collageToGraphSpan`. -/
def collageToGraphSpanMap
    {X Y :
      Collage (graphSpanProfunctor V E)}
    (f : X ⟶ Y) :
    collageToGraphSpanObj V E X ⟶
    collageToGraphSpanObj V E Y := by
  match X, Y, f with
  | ⟨.inl ⟨r⟩⟩, ⟨.inl ⟨r'⟩⟩, f =>
    have h : r = r' := f.down.down.down
    subst h; exact .id _
  | ⟨.inr ⟨v⟩⟩, ⟨.inr ⟨v'⟩⟩, f =>
    have h : v = v' := f.down.down.down
    subst h; exact .id _
  | ⟨.inl ⟨⟨v₀, v₁, e⟩⟩⟩,
    ⟨.inr ⟨w⟩⟩, f =>
    exact match w, f.down.down with
    | _, .fst => .fstProj v₀ v₁ e
    | _, .snd => .sndProj v₀ v₁ e
  | ⟨.inr _⟩, ⟨.inl _⟩, f =>
    exact PEmpty.elim f

@[simp]
theorem collageToGraphSpanMap_id_inl
    (r : GraphEdgeIndex V E) :
    collageToGraphSpanMap V E
      (𝟙 (Collage.inl
        (P := graphSpanProfunctor V E)
        ⟨r⟩)) =
    .id (.edgeNode r.1 r.2.1 r.2.2) := rfl

@[simp]
theorem collageToGraphSpanMap_id_inr
    (v : V) :
    collageToGraphSpanMap V E
      (𝟙 (Collage.inr
        (P := graphSpanProfunctor V E)
        ⟨v⟩)) =
    .id (.vertexNode v) := rfl

@[simp]
theorem collageToGraphSpanMap_fst
    (v₀ v₁ : V) (e : E v₀ v₁) :
    collageToGraphSpanMap V E
      (show Collage.inl
        (P := graphSpanProfunctor V E)
        ⟨⟨v₀, v₁, e⟩⟩ ⟶
        Collage.inr ⟨v₀⟩
        from ⟨⟨GraphEndpointProj.fst⟩⟩) =
    .fstProj v₀ v₁ e := rfl

@[simp]
theorem collageToGraphSpanMap_snd
    (v₀ v₁ : V) (e : E v₀ v₁) :
    collageToGraphSpanMap V E
      (show Collage.inl
        (P := graphSpanProfunctor V E)
        ⟨⟨v₀, v₁, e⟩⟩ ⟶
        Collage.inr ⟨v₁⟩
        from ⟨⟨GraphEndpointProj.snd⟩⟩) =
    .sndProj v₀ v₁ e := rfl

/-- Functor from the collage of
`graphSpanProfunctor V E` back to
`GraphSpanObj V E`. -/
def collageToGraphSpan :
    Collage (graphSpanProfunctor V E) ⥤
    GraphSpanObj V E where
  obj := collageToGraphSpanObj V E
  map := collageToGraphSpanMap V E
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
      match h.down with
      | .fst => rfl
      | .snd => rfl
    | .inl ⟨⟨v₀, v₁, e⟩⟩,
      .inr ⟨w⟩, .inr ⟨w'⟩,
      ⟨h⟩, ⟨g⟩ =>
      have heq : w = w' := g.down.down
      subst heq
      match h.down with
      | .fst =>
        simp [collageToGraphSpanMap,
          collageToGraphSpanObj,
          Collage.Hom.comp,
          CategoryStruct.comp,
          GraphSpanHom.comp,
          graphSpanProfunctor]
      | .snd =>
        simp [collageToGraphSpanMap,
          collageToGraphSpanObj,
          Collage.Hom.comp,
          CategoryStruct.comp,
          GraphSpanHom.comp,
          graphSpanProfunctor]
    | .inr _, .inl _, _, f, _ =>
      exact PEmpty.elim f
    | .inl _, .inr _, .inl _,
      _, g => exact PEmpty.elim g
    | .inr _, .inr _, .inl _,
      _, g => exact PEmpty.elim g

theorem graphSpanCollage_hom_inv_obj
    (X : GraphSpanObj V E) :
    collageToGraphSpanObj V E
      ((graphSpanToCollage V E).obj X) =
    X := by
  cases X <;> rfl

theorem graphSpanCollage_hom_inv_map
    {X Y : GraphSpanObj V E}
    (f : X ⟶ Y) :
    collageToGraphSpanMap V E
      ((graphSpanToCollage V E).map f) =
    eqToHom
      (graphSpanCollage_hom_inv_obj
        V E X) ≫
      f ≫
      eqToHom
        (graphSpanCollage_hom_inv_obj
          V E Y).symm := by
  cases f with
  | id X =>
    simp only [graphSpanToCollage]
    cases X <;> rfl
  | fstProj v₀ v₁ e =>
    simp only [graphSpanToCollage]
    exact collageToGraphSpanMap_fst
      V E v₀ v₁ e
  | sndProj v₀ v₁ e =>
    simp only [graphSpanToCollage]
    exact collageToGraphSpanMap_snd
      V E v₀ v₁ e

theorem graphSpanCollage_inv_hom_obj
    (X :
      Collage (graphSpanProfunctor V E)) :
    (graphSpanToCollage V E).obj
      (collageToGraphSpanObj V E X) =
    X := by
  match X with
  | ⟨.inl ⟨_⟩⟩ => rfl
  | ⟨.inr ⟨_⟩⟩ => rfl

def graphSpanCollageIso :
    GraphSpanObj V E ≅Cat
    Collage (graphSpanProfunctor V E) where
  hom :=
    (graphSpanToCollage V E).toCatHom
  inv :=
    (collageToGraphSpan V E).toCatHom
  hom_inv_id := by
    change (graphSpanToCollage V E ⋙
      collageToGraphSpan V E).toCatHom =
      (𝟭 _).toCatHom
    congr 1
    exact _root_.CategoryTheory.Functor.ext
      (graphSpanCollage_hom_inv_obj V E)
      (fun {X Y} f =>
        graphSpanCollage_hom_inv_map V E f)
  inv_hom_id := by
    change (collageToGraphSpan V E ⋙
      graphSpanToCollage V E).toCatHom =
      (𝟭 _).toCatHom
    congr 1
    exact _root_.CategoryTheory.Functor.ext
      (graphSpanCollage_inv_hom_obj V E)
      (fun {X Y} f => by
        match X, Y, f with
        | ⟨.inl ⟨_⟩⟩, ⟨.inl ⟨_⟩⟩, ⟨g⟩ =>
          have := g.down.down
          subst_vars
          dsimp [collageToGraphSpan,
            collageToGraphSpanMap,
            collageToGraphSpanObj,
            graphSpanToCollage,
            graphSpanCollage_inv_hom_obj]
          rfl
        | ⟨.inr ⟨_⟩⟩, ⟨.inr ⟨_⟩⟩, ⟨g⟩ =>
          have := g.down.down
          subst_vars
          dsimp [collageToGraphSpan,
            collageToGraphSpanMap,
            collageToGraphSpanObj,
            graphSpanToCollage,
            graphSpanCollage_inv_hom_obj]
          rfl
        | ⟨.inl ⟨⟨v₀, v₁, e⟩⟩⟩,
          ⟨.inr ⟨w⟩⟩, ⟨h⟩ =>
          simp only [
            eqToHom_refl, Category.id_comp,
            Category.comp_id, Functor.id_map,
            Functor.comp_map]
          match w, h with
          | _, ⟨.fst⟩ =>
            simp only [collageToGraphSpan]
            rfl
          | _, ⟨.snd⟩ =>
            simp only [collageToGraphSpan]
            rfl
        | ⟨.inr _⟩, ⟨.inl _⟩, f =>
          exact PEmpty.elim f)

end GraphSpanCollage

end GebLean
