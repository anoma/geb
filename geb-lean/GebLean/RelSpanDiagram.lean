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

end GebLean
