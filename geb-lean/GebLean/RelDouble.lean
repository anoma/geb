import GebLean.Paranatural

/-!
# Type-Level Relational Double Category

Type-level versions of the relational
double-categorical concepts from `PshRelDouble`.
`Type` is a presheaf category over `Discrete Unit`,
so these concepts are specializations of their
presheaf-level counterparts, but having them
directly at the type level avoids routing through
that encoding.

The main definitions are:
- `relType R`: the subtype of related pairs
- `graphRel f`: the graph of a function as a
  relation
- `graphRelInj f`: the canonical section
  `I₀ → relType (graphRel f)`
- `functorRelLift F R`: the Barr lift of a
  relation through a functor
- `profBarrLiftRel G R`: the Barr lift of a
  relation through a profunctor (bifunctor
  `Typeᵒᵖ ⥤ Type ⥤ Type`)
-/

open CategoryTheory

namespace GebLean

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

/-- The Barr lift of a relation `R` through a
profunctor `G : Typeᵒᵖ ⥤ Type ⥤ Type`. Two
diagonal elements `d₀ : diagApp G I₀` and
`d₁ : diagApp G I₁` are related when there
exists a witness `w : diagApp G S` (where
`S = relType R`) whose projections are
`DiagCompat` with `d₀` and `d₁`. -/
def profBarrLiftRel
    (G : Typeᵒᵖ ⥤ Type ⥤ Type)
    {I₀ I₁ : Type} (R : I₀ → I₁ → Prop)
    (d₀ : diagApp G I₀)
    (d₁ : diagApp G I₁) : Prop :=
  let S := { p : I₀ × I₁ // R p.1 p.2 }
  let π₁ : S → I₀ := fun s => s.val.1
  let π₂ : S → I₁ := fun s => s.val.2
  ∃ w : diagApp G S,
    DiagCompat G S I₀ π₁ w d₀ ∧
    DiagCompat G S I₁ π₂ w d₁

/-- For graph relations, the profunctor Barr lift
implies `DiagCompat`. Since `graphRel f` has
`relType (graphRel f) ≅ I₀` via `graphRelEquiv`,
the Barr lift witness can be transported to show
the covariant-contravariant compatibility. -/
theorem profBarrLiftRel_graph_implies_diagCompat
    (G : Typeᵒᵖ ⥤ Type ⥤ Type)
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (d₀ : diagApp G I₀)
    (d₁ : diagApp G I₁)
    (h : profBarrLiftRel G (graphRel f) d₀ d₁) :
    DiagCompat G I₀ I₁ f d₀ d₁ := by
  obtain ⟨w, h₁, h₂⟩ := h
  simp only [DiagCompat] at h₁ h₂ ⊢
  -- π₂ = f ∘ π₁ on relType (graphRel f)
  have hπ₂ :
      (fun s : { p : I₀ × I₁ //
        graphRel f p.1 p.2 } =>
        (↑s : I₀ × I₁).2) =
      f ∘ (fun s : { p : I₀ × I₁ //
        graphRel f p.1 p.2 } =>
        (↑s : I₀ × I₁).1) :=
    funext fun s => s.property.symm
  rw [hπ₂] at h₂
  -- Pointwise naturality of G.map ι.op at
  -- π₁ and f ∘ π₁, applied to w
  have nat₁ := congrFun
    ((G.map (Quiver.Hom.op
      (graphRelInj f))).naturality
    (fun s : { p : I₀ × I₁ //
      graphRel f p.1 p.2 } =>
      (↑s : I₀ × I₁).1)) w
  simp only [types_comp_apply] at nat₁
  rw [h₁] at nat₁
  have nat₂ := congrFun
    ((G.map (Quiver.Hom.op
      (graphRelInj f))).naturality
    (f ∘ fun s : { p : I₀ × I₁ //
      graphRel f p.1 p.2 } =>
      (↑s : I₀ × I₁).1)) w
  simp only [types_comp_apply] at nat₂
  rw [h₂] at nat₂
  -- The NatTrans composition G.map π₁.op ≫
  -- G.map ι.op = 𝟙 (retraction: π₁ ∘ ι = id)
  have h_retract :
      G.map (Quiver.Hom.op
        (fun s : { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).1)) ≫
      G.map (Quiver.Hom.op
        (graphRelInj f)) =
      𝟙 _ := by
    simp only [← Functor.map_comp,
      ← op_comp, types_comp,
      graphRelInj_comp_fst]
    exact G.map_id _
  -- (f∘π₁) ∘ ι = f (definitional in Type)
  have h_section :
      G.map (Quiver.Hom.op
        (f ∘ fun s : { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).1)) ≫
      G.map (Quiver.Hom.op
        (graphRelInj f)) =
      G.map (Quiver.Hom.op f) := by
    simp only [← Functor.map_comp,
      ← op_comp, types_comp]
    rfl
  -- Retraction applied pointwise at I₀ to d₀
  have h_r :
      (G.map (Quiver.Hom.op
        (graphRelInj f))).app I₀
        ((G.map (Quiver.Hom.op
          fun s : { p : I₀ × I₁ //
            graphRel f p.1 p.2 } =>
            (↑s : I₀ × I₁).1)).app I₀ d₀) =
        d₀ := by
    change ((G.map (Quiver.Hom.op
      fun s : { p : I₀ × I₁ //
        graphRel f p.1 p.2 } =>
        (↑s : I₀ × I₁).1) ≫
      G.map (Quiver.Hom.op
        (graphRelInj f))).app I₀) d₀ = d₀
    rw [h_retract]; rfl
  -- Section applied pointwise at I₁ to d₁
  have h_s :
      (G.map (Quiver.Hom.op
        (graphRelInj f))).app I₁
        ((G.map (Quiver.Hom.op
          (f ∘ fun s : { p : I₀ × I₁ //
            graphRel f p.1 p.2 } =>
            (↑s : I₀ × I₁).1))).app I₁ d₁) =
      (G.map (Quiver.Hom.op f)).app
        I₁ d₁ := by
    change ((G.map (Quiver.Hom.op
      (f ∘ fun s : { p : I₀ × I₁ //
        graphRel f p.1 p.2 } =>
        (↑s : I₀ × I₁).1)) ≫
      G.map (Quiver.Hom.op
        (graphRelInj f))).app I₁) d₁ =
      (G.map (Quiver.Hom.op f)).app I₁ d₁
    rw [h_section]
  -- d₀ = map π w', map f d₁ = map (f∘π) w'
  conv_lhs => rw [h_r.symm.trans nat₁]
  rw [← FunctorToTypes.map_comp_apply]
  exact (h_s.symm.trans nat₂).symm

/-- The converse of
`profBarrLiftRel_graph_implies_diagCompat`:
`DiagCompat` implies the profunctor Barr lift at
graph relations. The witness is obtained by
transporting `d₀` contravariantly along `π₁`
and covariantly along `graphRelInj f`. -/
theorem diagCompat_implies_profBarrLiftRel_graph
    (G : Typeᵒᵖ ⥤ Type ⥤ Type)
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (d₀ : diagApp G I₀)
    (d₁ : diagApp G I₁)
    (h : DiagCompat G I₀ I₁ f d₀ d₁) :
    profBarrLiftRel G (graphRel f) d₀ d₁ := by
  refine ⟨(G.obj (Opposite.op _)).map
    (graphRelInj f)
    ((G.map (Quiver.Hom.op
      fun s : { p : I₀ × I₁ //
        graphRel f p.1 p.2 } =>
        (↑s : I₀ × I₁).1)).app I₀ d₀),
    ?_, ?_⟩
  · -- π₁ ∘ ι = id, so map π₁ (map ι x) = x
    simp only [DiagCompat]
    rw [← FunctorToTypes.map_comp_apply]
    exact FunctorToTypes.map_id_apply _ _
  · -- π₂ ∘ ι = f, then naturality + hypothesis
    simp only [DiagCompat]
    rw [← FunctorToTypes.map_comp_apply]
    -- ι ≫ π₂ = f definitionally in Type
    change (G.obj (Opposite.op
      { p : I₀ × I₁ //
        graphRel f p.1 p.2 })).map f
      ((G.map (Quiver.Hom.op
        fun s : { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).1)).app I₀ d₀) =
      (G.map (Quiver.Hom.op
        fun s : { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).2)).app I₁ d₁
    -- Use naturality of G.map π₁.op at f
    have nat := congrFun
      ((G.map (Quiver.Hom.op
        fun s : { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).1)).naturality f)
      d₀
    simp only [types_comp_apply] at nat
    rw [← nat, h]
    -- Goal: (G.map π₁.op).app I₁
    --   ((G.map f.op).app I₁ d₁)
    -- = (G.map π₂.op).app I₁ d₁
    change ((G.map (Quiver.Hom.op f) ≫
      G.map (Quiver.Hom.op
        fun s : { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).1)).app I₁) d₁ =
      (G.map (Quiver.Hom.op
        fun s : { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).2)).app I₁ d₁
    simp only [← Functor.map_comp,
      ← op_comp, types_comp]
    have key : f ∘ (fun s :
        { p : I₀ × I₁ //
          graphRel f p.1 p.2 } =>
        (↑s : I₀ × I₁).1) =
        (fun s :
          { p : I₀ × I₁ //
            graphRel f p.1 p.2 } =>
          (↑s : I₀ × I₁).2) :=
      funext fun s => s.property
    simp only [key]

/-- The profunctor Barr lift at graph relations
is equivalent to `DiagCompat`. -/
theorem profBarrLiftRel_graph_iff_diagCompat
    (G : Typeᵒᵖ ⥤ Type ⥤ Type)
    {I₀ I₁ : Type} (f : I₀ → I₁)
    (d₀ : diagApp G I₀)
    (d₁ : diagApp G I₁) :
    profBarrLiftRel G (graphRel f) d₀ d₁ ↔
    DiagCompat G I₀ I₁ f d₀ d₁ :=
  ⟨profBarrLiftRel_graph_implies_diagCompat
    G f d₀ d₁,
   diagCompat_implies_profBarrLiftRel_graph
    G f d₀ d₁⟩

end GebLean
