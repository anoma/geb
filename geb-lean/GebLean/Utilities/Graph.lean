import Mathlib.CategoryTheory.Category.Basic

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

end GebLean
