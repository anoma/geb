import GebLean.ParanaturalTopos
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Relational Span Diagram

This module characterizes `ParametricFamily T` as a
standard categorical limit.  The diagram category
`RelSpanObj` is a bipartite category whose objects are
either type-nodes (one per `Type`) or relation-nodes
(one per relation `R : I₀ → I₁ → Prop`), with
projections from relation-nodes to their endpoint
type-nodes.

The functor `relSpanDiagram T : RelSpanObj ⥤ Type 1`
sends type-nodes to `ULift (T.interp I I)` and
relation-nodes to `ULift (T.relFiber R)`.
`parametricFamilyIsLimit` proves that
`ParametricFamily T` is the limit of this diagram.
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

instance : CategoryStruct RelSpanObj where
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

instance : Category RelSpanObj where
  id_comp := RelSpanHom.id_comp
  comp_id := RelSpanHom.comp_id
  assoc := RelSpanHom.assoc

/-- The diagram functor for a type expression `T`.
Maps type-nodes to `ULift (T.interp I I)` and
relation-nodes to `ULift (T.relFiber R)`. -/
def relSpanDiagram (T : TypeExpr) :
    RelSpanObj ⥤ Type 1 where
  obj
    | .typeNode I => ULift.{1} (T.interp I I)
    | .relNode I₀ I₁ R =>
      ULift.{1} (T.relFiber R)
  map {X Y} f :=
    match X, Y, f with
    | _, _, .id _ => id
    | _, _, .fstProj _ _ _ =>
      fun ⟨p⟩ => ⟨p.val.1⟩
    | _, _, .sndProj _ _ _ =>
      fun ⟨p⟩ => ⟨p.val.2⟩
  map_id := by
    intro X
    cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    cases f <;> cases g <;> rfl

abbrev RelSpanCone (T : TypeExpr) :=
  Limits.Cone (relSpanDiagram T)

/-- The cone over `relSpanDiagram T` with vertex
`ULift (ParametricFamily T)`.  The type-node
projections extract `p.app I`; the relation-node
projections extract the relational fiber
witness `⟨(p.app I₀, p.app I₁), p.parametric⟩`. -/
def parametricFamilyCone (T : TypeExpr) :
    RelSpanCone T where
  pt := ULift.{1} (ParametricFamily T)
  π :=
    { app := fun X =>
        match X with
        | .typeNode I =>
          fun ⟨p⟩ => ⟨p.app I⟩
        | .relNode I₀ I₁ R =>
          fun ⟨p⟩ =>
            ⟨⟨(p.app I₀, p.app I₁),
              p.parametric I₀ I₁ R⟩⟩
      naturality := by
        intro X Y f
        cases f <;> rfl }

/-- Auxiliary: given a cone `s` over
`relSpanDiagram T` and a point `x : s.pt`,
the parametricity condition holds for the
components extracted from type-node
projections. -/
theorem relSpanCone_parametric
    {T : TypeExpr}
    (s : RelSpanCone T)
    (x : s.pt)
    (I₀ I₁ : Type) (R : I₀ → I₁ → Prop) :
    T.fullRelInterp R
      (s.π.app (.typeNode I₀) x).down
      (s.π.app (.typeNode I₁) x).down := by
  have hw₁ := congr_fun (s.w
    (RelSpanHom.fstProj I₀ I₁ R)) x
  have hw₂ := congr_fun (s.w
    (RelSpanHom.sndProj I₀ I₁ R)) x
  simp only [types_comp_apply] at hw₁ hw₂
  let fiber := (s.π.app (.relNode I₀ I₁ R) x).down
  have hfib := fiber.property
  have h₁ : fiber.val.1 =
      (s.π.app (.typeNode I₀) x).down := by
    exact congr_arg ULift.down hw₁
  have h₂ : fiber.val.2 =
      (s.π.app (.typeNode I₁) x).down := by
    exact congr_arg ULift.down hw₂
  rw [← h₁, ← h₂]
  exact hfib

/-- `ParametricFamily T` is the limit of
`relSpanDiagram T`.  The lift extracts
type-node components; parametricity follows
from the cone's naturality at projection
morphisms. -/
def parametricFamilyIsLimit (T : TypeExpr) :
    Limits.IsLimit
      (parametricFamilyCone T) :=
  Limits.IsLimit.mk
    (fun s => fun x =>
      ⟨{ app := fun I => (s.π.app (.typeNode I) x).down
         parametric := fun I₀ I₁ R =>
           relSpanCone_parametric s x I₀ I₁ R }⟩)
    (by
      intro s j
      cases j with
      | typeNode I => rfl
      | relNode I₀ I₁ R =>
        funext x
        apply ULift.ext
        apply Subtype.ext
        apply Prod.ext
        · exact (congr_arg ULift.down
            (congr_fun (s.w
              (RelSpanHom.fstProj I₀ I₁ R))
              x)).symm
        · exact (congr_arg ULift.down
            (congr_fun (s.w
              (RelSpanHom.sndProj I₀ I₁ R))
              x)).symm)
    (by
      intro s m hm
      funext x
      apply ULift.ext
      ext I
      exact congr_arg ULift.down
        (congr_fun (hm (.typeNode I)) x))

/-- The functor from `ParametricWedge.{1} T` to
`RelSpanCone T`, sending a wedge to the cone
whose type-node projections are `ULift`-wrapped
wedge projections and whose relation-node
projections pair the projections with the
parametricity witness. -/
def wedgeToRelSpanCone (T : TypeExpr) :
    ParametricWedge.{1} T ⥤ RelSpanCone T where
  obj W :=
    { pt := W.pt
      π :=
        { app := fun X =>
            match X with
            | .typeNode I =>
              fun w => ⟨W.proj I w⟩
            | .relNode I₀ I₁ R =>
              fun w =>
                ⟨⟨(W.proj I₀ w, W.proj I₁ w),
                  W.parametric w I₀ I₁ R⟩⟩
          naturality := by
            intro X Y f
            cases f <;> rfl } }
  map f :=
    { hom := f.func
      w := by
        intro j
        cases j with
        | typeNode I =>
          funext w
          simp only [types_comp_apply]
          exact congrArg ULift.up (f.comm I w)
        | relNode I₀ I₁ R =>
          funext w
          simp only [types_comp_apply]
          apply ULift.ext
          apply Subtype.ext
          apply Prod.ext
          · exact f.comm I₀ w
          · exact f.comm I₁ w }
  map_id _ := by
    apply Limits.ConeMorphism.ext; rfl
  map_comp _ _ := by
    apply Limits.ConeMorphism.ext; rfl

/-- The functor from `RelSpanCone T` to
`ParametricWedge.{1} T`, extracting wedge
projections from the type-node components of
the cone via `ULift.down`, with parametricity
from `relSpanCone_parametric`. -/
def relSpanConeToWedge (T : TypeExpr) :
    RelSpanCone T ⥤ ParametricWedge.{1} T where
  obj s :=
    { pt := s.pt
      proj := fun I w =>
        (s.π.app (.typeNode I) w).down
      parametric := fun w I₀ I₁ R =>
        relSpanCone_parametric s w I₀ I₁ R }
  map f :=
    { func := f.hom
      comm := fun I w => by
        exact congr_arg ULift.down
          (congr_fun (f.w (.typeNode I)) w) }
  map_id _ := ParametricWedgeMorphism.ext rfl
  map_comp _ _ := ParametricWedgeMorphism.ext rfl

/-- The composite
`wedgeToRelSpanCone T ⋙ relSpanConeToWedge T`
is naturally isomorphic to the identity on
`ParametricWedge.{1} T`. -/
def wedgeRelSpanConeUnitIso (T : TypeExpr) :
    𝟭 (ParametricWedge.{1} T) ≅
    wedgeToRelSpanCone T ⋙
      relSpanConeToWedge T :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun _ => ParametricWedgeMorphism.ext rfl)

/-- The composite cone
`relSpanConeToWedge T ⋙ wedgeToRelSpanCone T`
applied to `s` equals `s`. -/
theorem relSpanCone_roundtrip_π
    {T : TypeExpr}
    (s : RelSpanCone T) (j : RelSpanObj) :
    ((wedgeToRelSpanCone T).obj
      ((relSpanConeToWedge T).obj s)).π.app j =
    s.π.app j := by
  cases j with
  | typeNode I =>
    funext x
    simp only [wedgeToRelSpanCone,
      relSpanConeToWedge]
    exact ULift.ext _ _
      (ULift.down_up _)
  | relNode I₀ I₁ R =>
    funext x
    simp only [wedgeToRelSpanCone,
      relSpanConeToWedge]
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext
    · simp only []
      exact (congr_arg ULift.down
        (congr_fun (s.w
          (RelSpanHom.fstProj I₀ I₁ R))
          x)).symm
    · simp only []
      exact (congr_arg ULift.down
        (congr_fun (s.w
          (RelSpanHom.sndProj I₀ I₁ R))
          x)).symm

theorem relSpanCone_roundtrip
    {T : TypeExpr} (s : RelSpanCone T) :
    (wedgeToRelSpanCone T).obj
      ((relSpanConeToWedge T).obj s) = s := by
  cases s with
  | mk pt π =>
    simp only [wedgeToRelSpanCone,
      relSpanConeToWedge]
    congr 1
    exact NatTrans.ext (funext fun j =>
      relSpanCone_roundtrip_π ⟨pt, π⟩ j)

/-- The composite
`relSpanConeToWedge T ⋙ wedgeToRelSpanCone T`
is naturally isomorphic to the identity on
`RelSpanCone T`. -/
def wedgeRelSpanConeCounitIso (T : TypeExpr) :
    relSpanConeToWedge T ⋙
      wedgeToRelSpanCone T ≅
    𝟭 (RelSpanCone T) :=
  NatIso.ofComponents
    (fun s =>
      eqToIso (relSpanCone_roundtrip s))
    (fun {s₁ s₂} f => by
      apply Limits.ConeMorphism.ext
      simp [wedgeToRelSpanCone,
        relSpanConeToWedge])

/-- `ParametricWedge.{1} T` is equivalent as a
category to `RelSpanCone T`, the category of
cones over the relational span diagram. -/
def wedgeRelSpanConeEquivalence
    (T : TypeExpr) :
    ParametricWedge.{1} T ≌ RelSpanCone T where
  functor := wedgeToRelSpanCone T
  inverse := relSpanConeToWedge T
  unitIso := wedgeRelSpanConeUnitIso T
  counitIso := wedgeRelSpanConeCounitIso T
  functor_unitIso_comp W := by
    apply Limits.ConeMorphism.ext
    simp [wedgeToRelSpanCone,
      relSpanConeToWedge,
      wedgeRelSpanConeUnitIso,
      wedgeRelSpanConeCounitIso]

theorem wedge_roundtrip
    {T : TypeExpr}
    (W : ParametricWedge.{1} T) :
    (relSpanConeToWedge T).obj
      ((wedgeToRelSpanCone T).obj W) = W :=
  rfl

/-- The equivalence between `ParametricWedge.{1} T`
and `RelSpanCone T` is a categorical isomorphism:
the composites of the two functors are (propositionally)
equal to the respective identity functors. -/
def wedgeRelSpanConeIso (T : TypeExpr) :
    ParametricWedge.{1} T ≅Cat RelSpanCone T :=
  Cat.isoOfEquiv
    (wedgeRelSpanConeEquivalence T)
    (fun W => wedge_roundtrip W)
    (fun s => relSpanCone_roundtrip s)

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
