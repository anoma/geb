import GebLean.Utilities.Graph
import GebLean.Utilities.Profunctors
import GebLean.Utilities.SpanFamily
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

section RelSpanGraphSpanEquiv

/-- The edge family for `RelSpanObj`: an edge
from `I₀` to `I₁` is a relation
`I₀ → I₁ → Prop`. -/
abbrev relSpanEdge (I₀ I₁ : Type) : Type :=
  I₀ → I₁ → Prop

/-- Object mapping from `RelSpanObj` to
`GraphSpanObj Type relSpanEdge`. -/
def relSpanToGraphSpanObj :
    RelSpanObj →
    GraphSpanObj Type relSpanEdge
  | .typeNode I => .vertexNode I
  | .relNode I₀ I₁ R => .edgeNode I₀ I₁ R

/-- Morphism mapping from `RelSpanObj` to
`GraphSpanObj Type relSpanEdge`. -/
def relSpanToGraphSpanMap
    {X Y : RelSpanObj}
    (f : X ⟶ Y) :
    relSpanToGraphSpanObj X ⟶
    relSpanToGraphSpanObj Y :=
  match X, Y, f with
  | _, _, RelSpanHom.id X =>
    @GraphSpanHom.id Type relSpanEdge
      (relSpanToGraphSpanObj X)
  | _, _, RelSpanHom.fstProj I₀ I₁ R =>
    @GraphSpanHom.fstProj Type relSpanEdge
      I₀ I₁ R
  | _, _, RelSpanHom.sndProj I₀ I₁ R =>
    @GraphSpanHom.sndProj Type relSpanEdge
      I₀ I₁ R

/-- Functor from `RelSpanObj` to the graph
span diagram category instantiated at
`Type` and `relSpanEdge`. -/
def relSpanToGraphSpan :
    RelSpanObj ⥤
    GraphSpanObj Type relSpanEdge where
  obj := relSpanToGraphSpanObj
  map := relSpanToGraphSpanMap
  map_id := by
    intro X; cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> rfl

/-- Object mapping from
`GraphSpanObj Type relSpanEdge` to
`RelSpanObj`. -/
def graphSpanToRelSpanObj :
    GraphSpanObj Type relSpanEdge →
    RelSpanObj
  | .vertexNode I => .typeNode I
  | .edgeNode I₀ I₁ R => .relNode I₀ I₁ R

/-- Morphism mapping from
`GraphSpanObj Type relSpanEdge` to
`RelSpanObj`. -/
def graphSpanToRelSpanMap
    {X Y : GraphSpanObj Type relSpanEdge}
    (f : X ⟶ Y) :
    graphSpanToRelSpanObj X ⟶
    graphSpanToRelSpanObj Y :=
  match X, Y, f with
  | _, _, GraphSpanHom.id X =>
    @RelSpanHom.id
      (graphSpanToRelSpanObj X)
  | _, _, GraphSpanHom.fstProj I₀ I₁ R =>
    @RelSpanHom.fstProj I₀ I₁ R
  | _, _, GraphSpanHom.sndProj I₀ I₁ R =>
    @RelSpanHom.sndProj I₀ I₁ R

/-- Functor from the graph span diagram
category instantiated at `Type` and
`relSpanEdge` to `RelSpanObj`. -/
def graphSpanToRelSpan :
    GraphSpanObj Type relSpanEdge ⥤
    RelSpanObj where
  obj := graphSpanToRelSpanObj
  map := graphSpanToRelSpanMap
  map_id := by
    intro X; cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> rfl

theorem relSpan_graphSpan_comp_eq_id :
    relSpanToGraphSpan ⋙ graphSpanToRelSpan =
    𝟭 RelSpanObj :=
  _root_.CategoryTheory.Functor.ext
    (fun X => by cases X <;> rfl)
    (fun _ _ f => by
      cases f <;>
        first | rfl
              | (rename_i X; cases X <;> rfl))

theorem graphSpan_relSpan_comp_eq_id :
    graphSpanToRelSpan ⋙ relSpanToGraphSpan =
    𝟭 (GraphSpanObj Type relSpanEdge) :=
  _root_.CategoryTheory.Functor.ext
    (fun Y => by cases Y <;> rfl)
    (fun _ _ f => by
      cases f <;>
        first | rfl
              | (rename_i X; cases X <;> rfl))

/-- Equivalence between `RelSpanObj` and the
graph span diagram category instantiated at
`Type` and `relSpanEdge`. -/
def relSpanGraphSpanEquiv :
    RelSpanObj ≌
    GraphSpanObj Type relSpanEdge where
  functor := relSpanToGraphSpan
  inverse := graphSpanToRelSpan
  unitIso :=
    eqToIso relSpan_graphSpan_comp_eq_id.symm
  counitIso :=
    eqToIso graphSpan_relSpan_comp_eq_id

/-- Isomorphism in `Cat` between `RelSpanObj`
and `GraphSpanObj Type relSpanEdge`.  Upgraded
from the equivalence via `Cat.isoOfEquiv`. -/
def relSpanGraphSpanIso :
    Cat.of RelSpanObj ≅
    Cat.of
      (GraphSpanObj Type relSpanEdge) :=
  Cat.isoOfEquiv relSpanGraphSpanEquiv
    (fun X => by cases X <;> rfl)
    (fun Y => by cases Y <;> rfl)
    (fun X => eqToHom_app
      relSpan_graphSpan_comp_eq_id.symm X)
    (fun Y => eqToHom_app
      graphSpan_relSpan_comp_eq_id Y)

end RelSpanGraphSpanEquiv

abbrev relSpanProfunctor :=
  graphSpanProfunctor Type relSpanEdge

def relSpanCollageIso :
    RelSpanObj ≅Cat
    Collage relSpanProfunctor :=
  relSpanGraphSpanIso ≪≫
    graphSpanCollageIso Type relSpanEdge

universe u₁ v₁ in
/-- Functors from `RelSpanObj` to an arbitrary
target category `E`. -/
abbrev ParametricFunctor
    (E : Type u₁) [Category.{v₁} E] :=
  RelSpanObj ⥤ E

/-- Copresheaves on `RelSpanObj`:
`ParametricFunctor` specialized to `Type 1`. -/
abbrev ParametricCopresheaf :=
  ParametricFunctor (Type 1)

universe u₂ v₂ in
/-- Equivalence between `ParametricFunctor D`
and the span family
`SpanFamily Type relSpanEdge D`, induced by
the equivalence `relSpanGraphSpanEquiv` via
precomposition. -/
def parametricFunctorSpanFamilyEquiv
    (D : Type u₂) [Category.{v₂} D] :
    ParametricFunctor D ≌
    SpanFamily Type relSpanEdge D :=
  relSpanGraphSpanEquiv.congrLeft

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
    (Type ⥤ Type) ⥤ ParametricCopresheaf where
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

/-- The contravariant relation lifting for a
functor `F : Typeᵒᵖ ⥤ Type`. Given a relation
`R : I₀ → I₁ → Prop`,
`contravariantRelLift F R a b` holds iff
`F.map (op π₁) a = F.map (op π₂) b` in
`F.obj (op (relType R))`: the pullback
condition. -/
def contravariantRelLift
    (F : Typeᵒᵖ ⥤ Type) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :
    F.obj (Opposite.op I₀) →
    F.obj (Opposite.op I₁) → Prop :=
  fun a b =>
    F.map (Opposite.op
      (fun s : relType R => s.val.1)) a =
    F.map (Opposite.op
      (fun s : relType R => s.val.2)) b

/-- The subtype of
`F.obj (op I₀) × F.obj (op I₁)` consisting
of pairs in the contravariant relation lifting
of `R` through `F`. -/
def contraRelImage
    (F : Typeᵒᵖ ⥤ Type) {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :=
  { p : F.obj (Opposite.op I₀) ×
        F.obj (Opposite.op I₁) //
    contravariantRelLift F R p.1 p.2 }

/-- Transport a `contraRelImage` element along
a natural transformation `α : F ⟶ G`. -/
def contraRelImage.map
    {F G : Typeᵒᵖ ⥤ Type}
    (α : F ⟶ G) {I₀ I₁ : Type}
    {R : I₀ → I₁ → Prop}
    (p : contraRelImage F R) :
    contraRelImage G R :=
  let π₁ : relType R → I₀ :=
    fun s => s.val.1
  let π₂ : relType R → I₁ :=
    fun s => s.val.2
  ⟨(α.app (Opposite.op I₀) p.val.1,
    α.app (Opposite.op I₁) p.val.2), by
    simp only [contravariantRelLift]
    have h₁ := congr_fun
      (α.naturality (Opposite.op π₁))
      p.val.1
    have h₂ := congr_fun
      (α.naturality (Opposite.op π₂))
      p.val.2
    simp only [types_comp_apply] at h₁ h₂
    rw [← h₁, ← h₂]
    exact congr_arg
      (α.app (Opposite.op (relType R)))
      p.property⟩

/-- The contravariant embedding maps a
presheaf `F : Typeᵒᵖ ⥤ Type` to a parametric
functor. Type-nodes map to
`ULift (F.obj (op I))`; relation-nodes map to
`ULift (contraRelImage F R)`, the pullback of
`F.map (op π₁)` and `F.map (op π₂)`.
Projections extract the pair components. -/
def contravariantEmbedding :
    (Typeᵒᵖ ⥤ Type) ⥤ ParametricCopresheaf where
  obj F :=
    { obj := fun X =>
        match X with
        | .typeNode I =>
          ULift.{1} (F.obj (Opposite.op I))
        | .relNode I₀ I₁ R =>
          ULift.{1} (contraRelImage F R)
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
          ULift.up ∘
            α.app (Opposite.op I) ∘
            ULift.down
        | .relNode I₀ I₁ R =>
          fun ⟨p⟩ =>
            ⟨contraRelImage.map α p⟩
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
      simp [contraRelImage.map]
  map_comp {F G H}
      (α : F ⟶ G) (β : G ⟶ H) := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      simp [contraRelImage.map]

/-- The contravariant embedding is fully
faithful. The preimage extracts typeNode
components; fullness follows from the relNode
component being a subtype of the product,
determined by its projections via
naturality. -/
def contravariantEmbedding_fullyFaithful :
    contravariantEmbedding.FullyFaithful where
  preimage {F G} β :=
    { app := fun opI x =>
        (β.app (.typeNode opI.unop)
          ⟨x⟩).down
      naturality := fun {opI₀ opI₁} opf => by
        let f := opf.unop
        let I₀ := opI₁.unop
        let I₁ := opI₀.unop
        funext x
        simp only [types_comp_apply]
        let π₁ : relType (graphRel f) → I₀ :=
          fun s => s.val.1
        let π₂ : relType (graphRel f) → I₁ :=
          fun s => s.val.2
        have hpb :
            F.map (Opposite.op π₁)
              (F.map opf x) =
            F.map (Opposite.op π₂) x := by
          have h := congr_fun
            (F.map_comp opf
              (Opposite.op π₁)) x
          simp only [types_comp_apply] at h
          rw [← h]
          have heq : opf ≫ Opposite.op π₁ =
              Opposite.op π₂ := by
            apply Quiver.Hom.unop_inj
            funext s
            exact s.property
          rw [heq]
        let p₀ : contraRelImage F
            (graphRel f) :=
          ⟨(F.map opf x, x), hpb⟩
        let m := (β.app (.relNode I₀ I₁
          (graphRel f)) ⟨p₀⟩).down
        have hfst :
            m.val.1 =
              (β.app (.typeNode I₀)
                ⟨F.map opf x⟩).down :=
          (congr_arg ULift.down
            (congr_fun (β.naturality
              (RelSpanHom.fstProj I₀ I₁
                (graphRel f))) ⟨p₀⟩)).symm
        have hsnd :
            m.val.2 =
              (β.app (.typeNode I₁)
                ⟨x⟩).down :=
          (congr_arg ULift.down
            (congr_fun (β.naturality
              (RelSpanHom.sndProj I₀ I₁
                (graphRel f))) ⟨p₀⟩)).symm
        -- Apply G.map (op e) to m.property
        -- where e a = ⟨(a, f a), rfl⟩
        let e : I₀ → relType (graphRel f) :=
          fun a => ⟨⟨a, f a⟩, rfl⟩
        have h := congr_arg
          (G.map (Opposite.op e))
          m.property
        -- G.map (op e) ∘ G.map (op π₁)
        --   = G.map (op π₁ ≫ op e)
        --   = G.map (op (e ∘ π₁))
        --   = G.map (op id)
        --   = id
        have hcomp₁ : Opposite.op π₁ ≫
            Opposite.op e =
            𝟙 (Opposite.op I₀) := by
          apply Quiver.Hom.unop_inj
          funext _; rfl
        have hcomp₂ : Opposite.op π₂ ≫
            Opposite.op e = opf := by
          apply Quiver.Hom.unop_inj
          rfl
        have lhs :
            G.map (Opposite.op e)
              (G.map (Opposite.op π₁)
                m.val.1) = m.val.1 := by
          have := congr_fun
            (G.map_comp (Opposite.op π₁)
              (Opposite.op e)) m.val.1
          simp only [types_comp_apply] at this
          rw [hcomp₁,
            congr_fun (G.map_id _)]
              at this
          exact this.symm
        have rhs :
            G.map (Opposite.op e)
              (G.map (Opposite.op π₂)
                m.val.2) =
            G.map opf m.val.2 := by
          have := congr_fun
            (G.map_comp (Opposite.op π₂)
              (Opposite.op e)) m.val.2
          simp only [types_comp_apply] at this
          rw [hcomp₂] at this
          exact this.symm
        rw [lhs, rhs] at h
        rw [← hfst, ← hsnd]
        exact h }
  map_preimage {F G} β := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      have hfst :=
        (congr_arg ULift.down
          (congr_fun (β.naturality
            (RelSpanHom.fstProj I₀ I₁ R))
            ⟨p⟩)).symm
      have hsnd :=
        (congr_arg ULift.down
          (congr_fun (β.naturality
            (RelSpanHom.sndProj I₀ I₁ R))
            ⟨p⟩)).symm
      apply Prod.ext
      · exact hfst.symm
      · exact hsnd.symm

instance contravariantEmbedding_faithful :
    contravariantEmbedding.Faithful :=
  contravariantEmbedding_fullyFaithful.faithful

instance contravariantEmbedding_full :
    contravariantEmbedding.Full :=
  contravariantEmbedding_fullyFaithful.full

/-- The canonical relation lifting for a
profunctor `G : Typeᵒᵖ × Type ⥤ Type`. Given
a relation `R` between types `A₁` and `A₂`,
`profRelLift G R x y` holds iff there exists
a witness `w : G.obj (op (relType R), relType R)`
whose projections match `x` and `y`. -/
def profRelLift
    (G : Typeᵒᵖ × Type ⥤ Type)
    {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop)
    (x : G.obj (Opposite.op I₀, I₀))
    (y : G.obj (Opposite.op I₁, I₁)) :
    Prop :=
  let π₁ : relType R → I₀ := fun s => s.val.1
  let π₂ : relType R → I₁ := fun s => s.val.2
  let SubR := relType R
  ∃ (w : G.obj (Opposite.op SubR, SubR)),
    G.map (show (Opposite.op SubR, SubR) ⟶
        (Opposite.op SubR, I₀) from
      (𝟙 _, π₁)) w =
      G.map (show (Opposite.op I₀, I₀) ⟶
          (Opposite.op SubR, I₀) from
        (Quiver.Hom.op π₁, 𝟙 _)) x ∧
    G.map (show (Opposite.op SubR, SubR) ⟶
        (Opposite.op SubR, I₁) from
      (𝟙 _, π₂)) w =
      G.map (show (Opposite.op I₁, I₁) ⟶
          (Opposite.op SubR, I₁) from
        (Quiver.Hom.op π₂, 𝟙 _)) y

/-- The subtype of
`G.obj (op I₀, I₀) × G.obj (op I₁, I₁)`
consisting of diagonal pairs in the
profunctor relation lifting of `R`
through `G`. -/
def profRelImage
    (G : Typeᵒᵖ × Type ⥤ Type)
    {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :=
  { p : G.obj (Opposite.op I₀, I₀) ×
        G.obj (Opposite.op I₁, I₁) //
    profRelLift G R p.1 p.2 }

/-- Transport a `profRelImage` element along
a natural transformation `α : G ⟶ H`. -/
def profRelImage.map
    {G H : Typeᵒᵖ × Type ⥤ Type}
    (α : G ⟶ H) {I₀ I₁ : Type}
    {R : I₀ → I₁ → Prop}
    (p : profRelImage G R) :
    profRelImage H R :=
  let π₁ : relType R → I₀ := fun s => s.val.1
  let π₂ : relType R → I₁ := fun s => s.val.2
  let SubR := relType R
  ⟨(α.app (Opposite.op I₀, I₀) p.val.1,
    α.app (Opposite.op I₁, I₁) p.val.2),
    p.property.elim fun w ⟨hw₁, hw₂⟩ =>
      ⟨α.app (Opposite.op SubR, SubR) w, by
        let f₁ : (Opposite.op SubR, SubR) ⟶
            (Opposite.op SubR, I₀) :=
          (𝟙 _, π₁)
        let g₁ : (Opposite.op I₀, I₀) ⟶
            (Opposite.op SubR, I₀) :=
          (Quiver.Hom.op π₁, 𝟙 _)
        let f₂ : (Opposite.op SubR, SubR) ⟶
            (Opposite.op SubR, I₁) :=
          (𝟙 _, π₂)
        let g₂ : (Opposite.op I₁, I₁) ⟶
            (Opposite.op SubR, I₁) :=
          (Quiver.Hom.op π₂, 𝟙 _)
        have nat_f₁ := congr_fun
          (α.naturality f₁) w
        have nat_g₁ := congr_fun
          (α.naturality g₁) p.val.1
        have nat_f₂ := congr_fun
          (α.naturality f₂) w
        have nat_g₂ := congr_fun
          (α.naturality g₂) p.val.2
        simp only [types_comp_apply]
          at nat_f₁ nat_g₁ nat_f₂ nat_g₂
        exact ⟨
          nat_f₁.symm.trans
            ((congr_arg _ hw₁).trans
              nat_g₁),
          nat_f₂.symm.trans
            ((congr_arg _ hw₂).trans
              nat_g₂)⟩⟩⟩

/-- The profunctor embedding maps a profunctor
`G : Typeᵒᵖ × Type ⥤ Type` to a parametric
functor. Type-nodes map to the diagonal
`ULift (G.obj (op I, I))`; relation-nodes map
to `ULift (profRelImage G R)`. -/
def profunctorEmbedding :
    (Typeᵒᵖ × Type ⥤ Type) ⥤
    ParametricCopresheaf where
  obj G :=
    { obj := fun X =>
        match X with
        | .typeNode I =>
          ULift.{1}
            (G.obj (Opposite.op I, I))
        | .relNode I₀ I₁ R =>
          ULift.{1} (profRelImage G R)
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
  map {G H} (α : G ⟶ H) :=
    { app := fun X =>
        match X with
        | .typeNode I =>
          ULift.up ∘
            α.app (Opposite.op I, I) ∘
            ULift.down
        | .relNode I₀ I₁ R =>
          fun ⟨p⟩ =>
            ⟨profRelImage.map α p⟩
      naturality := by
        intro X Y f
        match X, Y, f with
        | _, _, .id _ => rfl
        | _, _, .fstProj I₀ I₁ R =>
          funext ⟨p⟩; rfl
        | _, _, .sndProj I₀ I₁ R =>
          funext ⟨p⟩; rfl }
  map_id G := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      simp [profRelImage.map]
  map_comp {G H K}
      (α : G ⟶ H) (β : H ⟶ K) := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode I => funext ⟨_⟩; rfl
    | relNode I₀ I₁ R =>
      funext ⟨p⟩
      apply ULift.ext
      apply Subtype.ext
      simp [profRelImage.map]

-- When profunctors are equipped with NATURAL
-- transformations as morphisms,
-- `profunctorEmbedding` is neither full nor
-- faithful (only sees diagonal components, and
-- natural transformations have independent
-- off-diagonal data).
--
-- When profunctors are equipped with
-- PARANATURAL transformations as morphisms
-- (the category `endoProfCategory` from
-- `Paranatural.lean`), the situation improves:
-- paranatural transformations have only
-- diagonal components, and the paranaturality
-- condition (`DiagCompat` preservation)
-- matches the `profRelLift` transport.
-- The embedding to `ParametricCopresheaf` using
-- paranatural morphisms is analyzed in
-- `ParanaturalTopos.lean`.

end GebLean
