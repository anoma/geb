import GebLean.Paranatural
import GebLean.Utilities.Skeleton
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Parametric polymorphism for endoprofunctors

Given endoprofunctors `F, G : Cᵒᵖ ⥤ C ⥤ Type w`, a family of
functions `α_I : F(I, I) → G(I, I)` is *paranatural* if it respects
the diagonal compatibility condition for all morphisms in `C`
(Definition 2.7 in Neumann's "Paranatural Category Theory").

Full parametric polymorphism strengthens this: instead of requiring
compatibility for individual morphisms `f : I₀ ⟶ I₁` (which are
"representable relations"), it requires compatibility for arbitrary
*spans* `(R, π₁ : R ⟶ I₀, π₂ : R ⟶ I₁)` in `C`.

The relation lifting of a profunctor `F` at a span `(R, π₁, π₂)` is
defined semantically: `d₀ ∈ F(I₀, I₀)` and `d₁ ∈ F(I₁, I₁)` are
`F`-related via `(R, π₁, π₂)` if there exists `e ∈ F(R, R)` such
that both the `I₀`-projection and `I₁`-projection conditions hold.
When `R = I₀`, `π₁ = 𝟙`, `π₂ = f`, this reduces to the paranaturality
condition `DiagCompat`.

## References

* Wadler, "Theorems for free!" (1989)
* Neumann, "Paranatural Category Theory"
-/

namespace GebLean

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

section ProfunctorRelationLifting

variable (F : Cᵒᵖ ⥤ C ⥤ Type v)

/-- The profunctor relation lifting through `F` at a span
`(R, π₁ : R ⟶ I₀, π₂ : R ⟶ I₁)`.

Given `d₀ ∈ F(I₀, I₀)` and `d₁ ∈ F(I₁, I₁)`, they are
`F`-related via the span if there exists `e ∈ F(R, R)` such that:
- `map₁(π₁)(d₀) = map₂(π₁)(e)` in `F(R, I₀)`
- `map₁(π₂)(d₁) = map₂(π₂)(e)` in `F(R, I₁)`

where `map₁` is the contravariant action and `map₂` is the
covariant action of `F`. -/
def ProfRelLift
    {I₀ I₁ R : C} (π₁ : R ⟶ I₀) (π₂ : R ⟶ I₁)
    (d₀ : diagApp F I₀) (d₁ : diagApp F I₁) : Prop :=
  ∃ (e : diagApp F R),
    (F.map π₁.op).app I₀ d₀ =
      (F.obj (Opposite.op R)).map π₁ e ∧
    (F.map π₂.op).app I₁ d₁ =
      (F.obj (Opposite.op R)).map π₂ e

/-- When the span is a graph `(I₀, 𝟙 I₀, f)` for a morphism
`f : I₀ ⟶ I₁`, the profunctor relation lifting reduces to the
diagonal compatibility condition `DiagCompat`. -/
theorem profRelLift_graph_iff_diagCompat
    {I₀ I₁ : C} (f : I₀ ⟶ I₁)
    (d₀ : diagApp F I₀) (d₁ : diagApp F I₁) :
    ProfRelLift F (𝟙 I₀) f d₀ d₁ ↔
      DiagCompat F I₀ I₁ f d₀ d₁ := by
  simp only [ProfRelLift, DiagCompat]
  constructor
  · rintro ⟨e, h₁, h₂⟩
    have he : e = d₀ := by
      have := h₁
      simp at this
      exact this.symm
    rw [he] at h₂
    exact h₂.symm
  · intro h
    exact ⟨d₀, by simp, h.symm⟩

end ProfunctorRelationLifting

section ParametricPolymorphism

variable (F G : Cᵒᵖ ⥤ C ⥤ Type v)

/-- A family `α : ParanatSig F G` is parametrically
polymorphic if it preserves the profunctor relation
lifting for all spans `(R, π₁, π₂)` in `C`.

This strengthens `IsParanatural`, which requires
preservation only for graph spans `(I₀, 𝟙, f)`. -/
def IsParamPoly (α : ParanatSig F G) : Prop :=
  ∀ {I₀ I₁ R : C}
    (π₁ : R ⟶ I₀) (π₂ : R ⟶ I₁)
    (d₀ : diagApp F I₀) (d₁ : diagApp F I₁),
    ProfRelLift F π₁ π₂ d₀ d₁ →
      ProfRelLift G π₁ π₂ (α I₀ d₀) (α I₁ d₁)

/-- Parametric polymorphism implies paranaturality.
The graph span `(I₀, 𝟙 I₀, f)` is a special case of
an arbitrary span, and the profunctor relation lifting
at a graph span is equivalent to `DiagCompat`. -/
theorem isParamPoly_implies_isParanatural
    {α : ParanatSig F G} (h : IsParamPoly F G α) :
    IsParanatural F G α := by
  intro I₀ I₁ f d₀ d₁ hcompat
  rw [← profRelLift_graph_iff_diagCompat]
  exact h (𝟙 I₀) f d₀ d₁
    ((profRelLift_graph_iff_diagCompat F f d₀ d₁).mpr
      hcompat)

/-- Paranaturality implies parametric polymorphism.
The witness `e` in a `ProfRelLift` satisfies
`DiagCompat F R I₀ π₁ e d₀` and
`DiagCompat F R I₁ π₂ e d₁` (one per leg of the
span). Applying paranaturality to each leg
independently yields the two output conditions with
witness `α R e`. -/
theorem isParanatural_implies_isParamPoly
    {α : ParanatSig F G}
    (hα : IsParanatural F G α) :
    IsParamPoly F G α := by
  intro I₀ I₁ R π₁ π₂ d₀ d₁ ⟨e, h₁, h₂⟩
  exact ⟨α R e,
    (hα R I₀ π₁ e d₀ h₁.symm).symm,
    (hα R I₁ π₂ e d₁ h₂.symm).symm⟩

/-- Parametric polymorphism and paranaturality are
equivalent for all endoprofunctors. The forward
direction holds because graph spans are a special
case of arbitrary spans; the reverse because each
leg of a span-based relation lifting is a
`DiagCompat` condition. -/
theorem isParamPoly_iff_isParanatural
    (α : ParanatSig F G) :
    IsParamPoly F G α ↔ IsParanatural F G α := by
  constructor
  · intro h I₀ I₁ f d₀ d₁ hcompat
    rw [← profRelLift_graph_iff_diagCompat]
    exact h (𝟙 I₀) f d₀ d₁
      ((profRelLift_graph_iff_diagCompat F f
        d₀ d₁).mpr hcompat)
  · intro h I₀ I₁ R π₁ π₂ d₀ d₁ ⟨e, h₁, h₂⟩
    exact ⟨α R e,
      (h R I₀ π₁ e d₀ h₁.symm).symm,
      (h R I₁ π₂ e d₁ h₂.symm).symm⟩

/-- The diagonal restriction of a natural transformation
between endoprofunctors is parametrically polymorphic.

The witness for the relation lifting is the image of the
original witness under `η` at `(R, R)`. Naturality in
both the contravariant and covariant directions ensures
that the projection conditions are preserved. -/
theorem natTrans_restrict_isParamPoly
    (η : F ⟶ G) :
    IsParamPoly F G (NatTrans.restrict F G η) := by
  intro I₀ I₁ R π₁ π₂ d₀ d₁ ⟨e, h₁, h₂⟩
  refine ⟨(η.app (Opposite.op R)).app R e, ?_, ?_⟩
  · simp only [NatTrans.restrict]
    have nat_con :=
      congrFun (congrArg (NatTrans.app · I₀)
        (η.naturality π₁.op)) d₀
    simp only [types_comp_apply, NatTrans.comp_app]
      at nat_con
    rw [← nat_con]
    have nat_cov :=
      congrFun
        ((η.app (Opposite.op R)).naturality π₁) e
    simp only [types_comp_apply] at nat_cov
    rw [← nat_cov]
    exact congrArg _ h₁
  · simp only [NatTrans.restrict]
    have nat_con :=
      congrFun (congrArg (NatTrans.app · I₁)
        (η.naturality π₂.op)) d₁
    simp only [types_comp_apply, NatTrans.comp_app]
      at nat_con
    rw [← nat_con]
    have nat_cov :=
      congrFun
        ((η.app (Opposite.op R)).naturality π₂) e
    simp only [types_comp_apply] at nat_cov
    rw [← nat_cov]
    exact congrArg _ h₂

/-- The identity family is parametrically polymorphic. -/
theorem isParamPoly_id :
    IsParamPoly F F (Paranat.id (F := F)).app := by
  intro I₀ I₁ R π₁ π₂ d₀ d₁ h
  exact h

variable {H : Cᵒᵖ ⥤ C ⥤ Type v}

/-- Composition of parametrically polymorphic families
is parametrically polymorphic. Given `α : F → G` and
`β : G → H`, if both preserve all span-based relation
liftings, then so does `β ∘ α`. -/
theorem isParamPoly_comp
    {α : ParanatSig F G} {β : ParanatSig G H}
    (hα : IsParamPoly F G α) (hβ : IsParamPoly G H β) :
    IsParamPoly F H (fun I d => β I (α I d)) := by
  intro I₀ I₁ R π₁ π₂ d₀ d₁ h
  exact hβ π₁ π₂ (α I₀ d₀) (α I₁ d₁) (hα π₁ π₂ d₀ d₁ h)

/-- The morphism property on `EndoProf` selecting those
paranatural transformations that are parametrically
polymorphic. -/
def paramPolyMorphProp :
    @MorphismProperty
      (EndoProf (C := C))
      endoProfCategory.toCategoryStruct :=
  fun {F G} (α : Paranat F G) =>
    IsParamPoly F G α.app

instance : @MorphismProperty.ContainsIdentities
    (EndoProf (C := C))
    endoProfCategory
    paramPolyMorphProp where
  id_mem F := by
    intro I₀ I₁ R π₁ π₂ d₀ d₁ h
    exact h

instance : @MorphismProperty.IsStableUnderComposition
    (EndoProf (C := C))
    endoProfCategory
    paramPolyMorphProp where
  comp_mem {F G H} f g hf hg := by
    intro I₀ I₁ R π₁ π₂ d₀ d₁ h
    exact hg π₁ π₂ _ _ (hf π₁ π₂ d₀ d₁ h)

instance : @MorphismProperty.IsMultiplicative
    (EndoProf (C := C))
    endoProfCategory
    paramPolyMorphProp where

/-- The wide subcategory of `EndoProf` consisting of
all endoprofunctors with parametrically polymorphic
paranatural transformations as morphisms.

The category instance and faithful inclusion functor
into `EndoProf` are provided by mathlib's
`WideSubcategory` infrastructure. -/
abbrev ParamEndoProf :=
  @WideSubcategory
    (EndoProf (C := C))
    endoProfCategory
    paramPolyMorphProp
    inferInstance

/-- The faithful inclusion of the parametrically
polymorphic subcategory into the full paranatural
category. -/
abbrev paramEndoProfInclusion :
    ParamEndoProf (C := C) ⥤
      EndoProf (C := C) :=
  @wideSubcategoryInclusion
    (EndoProf (C := C))
    endoProfCategory
    paramPolyMorphProp
    inferInstance

end ParametricPolymorphism

section PresheafReduction

/-- A presheaf `Q : Cᵒᵖ ⥤ Type v` viewed as a profunctor
that ignores its covariant argument. The profunctor
`presheafAsProf Q` sends `(a, b) ↦ Q(a)`, constant in
`b`. -/
def presheafAsProf (Q : Cᵒᵖ ⥤ Type v) :
    Cᵒᵖ ⥤ C ⥤ Type v :=
  Q ⋙ Functor.const C

/-- The profunctor relation lifting for a presheaf-as-
profunctor simplifies: the covariant projections become
trivial (identity), so the lifting reduces to the
presheaf actions agreeing on a common element. -/
theorem profRelLift_presheafAsProf_iff
    (Q : Cᵒᵖ ⥤ Type v)
    {I₀ I₁ R : C} (π₁ : R ⟶ I₀) (π₂ : R ⟶ I₁)
    (d₀ : diagApp (presheafAsProf Q) I₀)
    (d₁ : diagApp (presheafAsProf Q) I₁) :
    ProfRelLift (presheafAsProf Q) π₁ π₂ d₀ d₁ ↔
      Q.map π₁.op d₀ = Q.map π₂.op d₁ := by
  simp only [ProfRelLift, presheafAsProf,
    Functor.comp_obj, Functor.const_obj_obj,
    Functor.comp_map, Functor.const_map_app,
    Functor.const_obj_map, types_id]
  constructor
  · rintro ⟨e, h₁, h₂⟩
    rw [h₁, h₂]
  · intro h
    exact ⟨Q.map π₁.op d₀, rfl, h.symm⟩

/-- For presheaf-as-profunctors, `IsParamPoly` is equivalent
to naturality of the family as a presheaf transformation.

For `g : op I₀ ⟶ op I₁` in `Cᵒᵖ` (equivalently
`g.unop : I₁ ⟶ I₀` in `C`), the naturality condition is
`Q'.map g ∘ α_{I₀} = α_{I₁} ∘ Q.map g`. -/
theorem isParamPoly_presheafAsProf_iff
    (Q Q' : Cᵒᵖ ⥤ Type v)
    (α : ParanatSig (presheafAsProf Q)
      (presheafAsProf Q')) :
    IsParamPoly (presheafAsProf Q)
      (presheafAsProf Q') α ↔
      (∀ {I₀ I₁ : C} (f : I₁ ⟶ I₀)
        (d : diagApp (presheafAsProf Q) I₀),
        Q'.map f.op (α I₀ d) =
          α I₁ (Q.map f.op d)) := by
  constructor
  · intro hparam I₀ I₁ f d
    have hlift := hparam f (𝟙 I₁) d
      (Q.map f.op d)
      ((profRelLift_presheafAsProf_iff Q f
        (𝟙 I₁) d (Q.map f.op d)).mpr (by simp))
    rw [profRelLift_presheafAsProf_iff] at hlift
    simp only [op_id, CategoryTheory.Functor.map_id, types_id,
      id_eq] at hlift
    exact hlift
  · intro hnat I₀ I₁ R π₁ π₂ d₀ d₁ hlift
    rw [profRelLift_presheafAsProf_iff] at hlift ⊢
    rw [hnat π₁, hnat π₂, hlift]

end PresheafReduction

section CopresheafReduction

/-- A copresheaf `Q : C ⥤ Type v` viewed as a profunctor
that ignores its contravariant argument. The profunctor
`copresheafAsProf Q` sends `(a, b) ↦ Q(b)`, constant
in `a`. -/
def copresheafAsProf (Q : C ⥤ Type v) :
    Cᵒᵖ ⥤ C ⥤ Type v :=
  (Functor.const Cᵒᵖ).obj Q

/-- The profunctor relation lifting for a copresheaf-as-
profunctor simplifies: the contravariant projections
become trivial, so the lifting reduces to the existence
of a common preimage under the covariant action. -/
theorem profRelLift_copresheafAsProf_iff
    (Q : C ⥤ Type v)
    {I₀ I₁ R : C} (π₁ : R ⟶ I₀) (π₂ : R ⟶ I₁)
    (d₀ : diagApp (copresheafAsProf Q) I₀)
    (d₁ : diagApp (copresheafAsProf Q) I₁) :
    ProfRelLift (copresheafAsProf Q) π₁ π₂ d₀ d₁ ↔
      ∃ (e : Q.obj R),
        Q.map π₁ e = d₀ ∧ Q.map π₂ e = d₁ := by
  simp only [ProfRelLift, copresheafAsProf,
    Functor.const_obj_obj, Functor.const_obj_map]
  constructor
  · rintro ⟨e, h₁, h₂⟩
    exact ⟨e, h₁.symm, h₂.symm⟩
  · rintro ⟨e, h₁, h₂⟩
    exact ⟨e, h₁.symm, h₂.symm⟩

/-- For copresheaf-as-profunctors, `IsParamPoly` is
equivalent to naturality of the family as a copresheaf
transformation: `Q'.map f ∘ α = α ∘ Q.map f` for all
`f : I₀ ⟶ I₁` in `C`. -/
theorem isParamPoly_copresheafAsProf_iff
    (Q Q' : C ⥤ Type v)
    (α : ParanatSig (copresheafAsProf Q)
      (copresheafAsProf Q')) :
    IsParamPoly (copresheafAsProf Q)
      (copresheafAsProf Q') α ↔
      (∀ {I₀ I₁ : C} (f : I₀ ⟶ I₁)
        (d : diagApp (copresheafAsProf Q) I₀),
        Q'.map f (α I₀ d) =
          α I₁ (Q.map f d)) := by
  constructor
  · intro hparam I₀ I₁ f d
    have hlift := hparam (𝟙 I₀) f d (Q.map f d)
      ((profRelLift_copresheafAsProf_iff Q
        (𝟙 I₀) f d (Q.map f d)).mpr
        ⟨d, by simp, rfl⟩)
    rw [profRelLift_copresheafAsProf_iff] at hlift
    obtain ⟨e', h₁, h₂⟩ := hlift
    simp only [CategoryTheory.Functor.map_id, types_id, id_eq]
      at h₁
    rw [← h₁, h₂]
  · intro hnat I₀ I₁ R π₁ π₂ d₀ d₁ hlift
    rw [profRelLift_copresheafAsProf_iff] at hlift ⊢
    obtain ⟨e, he₀, he₁⟩ := hlift
    exact ⟨α R e,
      by rw [hnat π₁, he₀],
      by rw [hnat π₂, he₁]⟩

end CopresheafReduction

section YonedaEmbedding

open Opposite

/-- `presheafAsProf` as a functor from presheaves to
profunctors. Postcomposition with `Functor.const C`
sends `Q : Cᵒᵖ ⥤ Type v` to the profunctor
`Q ⋙ Functor.const C : (a, b) ↦ Q(a)`. -/
def presheafAsProfFunctor :
    (Cᵒᵖ ⥤ Type v) ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) :=
  (Functor.whiskeringRight Cᵒᵖ (Type v)
    (C ⥤ Type v)).obj (Functor.const C)

@[simp]
theorem presheafAsProfFunctor_obj (Q : Cᵒᵖ ⥤ Type v) :
    presheafAsProfFunctor.obj Q =
      presheafAsProf (C := C) Q :=
  rfl

/-- `copresheafAsProf` as a functor from copresheaves
to profunctors. The constant functor
`Functor.const Cᵒᵖ` sends `Q : C ⥤ Type v` to the
profunctor `(a, b) ↦ Q(b)`. -/
def copresheafAsProfFunctor :
    (C ⥤ Type v) ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) :=
  Functor.const Cᵒᵖ

@[simp]
theorem copresheafAsProfFunctor_obj
    (Q : C ⥤ Type v) :
    copresheafAsProfFunctor.obj Q =
      copresheafAsProf (C := C) Q :=
  rfl

/-- The Yoneda embedding composed with
`presheafAsProfFunctor`, sending `c : C` to the
profunctor `(a, b) ↦ Hom(a, c)`. -/
def yonedaProfFunctor :
    C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) :=
  yoneda ⋙ presheafAsProfFunctor

/-- The profunctor `(a, b) ↦ Hom(a, c)`, i.e., the
Yoneda embedding of `c` viewed as an endoprofunctor
that ignores its covariant argument. -/
def yonedaProf (c : C) : Cᵒᵖ ⥤ C ⥤ Type v :=
  yonedaProfFunctor.obj c

/-- The diagonal elements of `yonedaProf c` at `I`
are `Hom(I, c)`. -/
theorem diagApp_yonedaProf (c I : C) :
    diagApp (yonedaProf c) I = (unop (op I) ⟶ c) :=
  rfl

/-- The paranatural family induced by `f : c₁ ⟶ c₂`
between Yoneda profunctors: postcomposition with `f`
at each component. -/
def yonedaProfMap {c₁ c₂ : C} (f : c₁ ⟶ c₂) :
    ParanatSig (yonedaProf c₁)
      (yonedaProf (C := C) c₂) :=
  fun I (g : unop (op I) ⟶ c₁) => g ≫ f

theorem yonedaProfMap_isParamPoly
    {c₁ c₂ : C} (f : c₁ ⟶ c₂) :
    IsParamPoly (yonedaProf c₁)
      (yonedaProf (C := C) c₂)
      (yonedaProfMap f) := by
  change IsParamPoly
    (presheafAsProf (yoneda.obj c₁))
    (presheafAsProf (yoneda.obj c₂))
    (yonedaProfMap f)
  rw [isParamPoly_presheafAsProf_iff]
  intro I₀ I₁ g d
  simp only [yonedaProfMap, yoneda_obj_map]
  simp only [Category.assoc]

/-- The `Paranat` morphism in `EndoProf` induced by
`f : c₁ ⟶ c₂`. -/
def yonedaProfParanat {c₁ c₂ : C} (f : c₁ ⟶ c₂) :
    @Paranat C _ (yonedaProf c₁) (yonedaProf c₂) where
  app := yonedaProfMap f
  paranatural :=
    isParamPoly_implies_isParanatural _ _
      (yonedaProfMap_isParamPoly f)

theorem yonedaProfParanat_id (c : C) :
    yonedaProfParanat (𝟙 c) =
      @Paranat.id C _ (yonedaProf c) := by
  apply Paranat.ext
  funext I g
  simp [yonedaProfParanat, yonedaProfMap,
    Paranat.id]

theorem yonedaProfParanat_comp
    {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) :
    yonedaProfParanat (f ≫ g) =
      (yonedaProfParanat f).comp
        (yonedaProfParanat g) := by
  apply Paranat.ext
  funext I h
  simp [yonedaProfParanat, yonedaProfMap,
    Paranat.comp, Category.assoc]

/-- The Yoneda embedding into `EndoProf`, sending
`c : C` to the profunctor `(a, b) ↦ Hom(a, c)` and
`f : c₁ ⟶ c₂` to the paranatural transformation
given by postcomposition with `f`. -/
def yonedaEndoProf :
    @CategoryTheory.Functor C _
      (EndoProf (C := C))
      endoProfCategory where
  obj c := yonedaProf c
  map f := yonedaProfParanat f
  map_id c := yonedaProfParanat_id c
  map_comp f g := yonedaProfParanat_comp f g

/-- For presheaf-as-profunctors, paranaturality already
implies parametric polymorphism. The DiagCompat
condition for `presheafAsProf Q` at `f : I₀ ⟶ I₁`
gives `d₀ = Q.map f.op d₁`, so paranaturality yields
naturality of the family. -/
theorem isParanatural_presheafAsProf_implies_isParamPoly
    (Q Q' : Cᵒᵖ ⥤ Type v)
    {α : ParanatSig (presheafAsProf Q)
      (presheafAsProf Q')}
    (hα : IsParanatural (presheafAsProf Q)
      (presheafAsProf Q') α) :
    IsParamPoly (presheafAsProf Q)
      (presheafAsProf Q') α := by
  rw [isParamPoly_presheafAsProf_iff]
  intro I₀ I₁ f d
  have hcompat : DiagCompat (presheafAsProf Q)
      I₁ I₀ f (Q.map f.op d) d := by
    simp [DiagCompat, presheafAsProf,
      Functor.comp_obj, Functor.const_obj_obj,
      Functor.comp_map, Functor.const_map_app,
      Functor.const_obj_map]
  have h := hα I₁ I₀ f _ _ hcompat
  simp [DiagCompat, presheafAsProf,
    Functor.comp_obj, Functor.const_obj_obj,
    Functor.comp_map, Functor.const_map_app,
    Functor.const_obj_map] at h
  exact h.symm

/-- Evaluating the Yoneda paranatural transformation at
`c₁` on `𝟙 c₁` recovers the original morphism. -/
theorem yonedaProfParanat_preimage_map
    {c₁ c₂ : C} (f : c₁ ⟶ c₂) :
    (yonedaProfParanat f).app c₁ (𝟙 c₁) = f := by
  simp [yonedaProfParanat, yonedaProfMap]

/-- A paranatural transformation between Yoneda
profunctors is determined by its value at the identity:
`α I g = g ≫ α c₁ (𝟙 c₁)`. This uses the fact that
paranaturality implies naturality for presheaf-as-
profunctors. -/
theorem yonedaProfParanat_map_preimage
    {c₁ c₂ : C}
    (α : @Paranat C _ (yonedaProf c₁)
      (yonedaProf c₂)) :
    yonedaProfParanat (α.app c₁ (𝟙 c₁)) = α := by
  apply Paranat.ext
  funext I g
  simp only [yonedaProfParanat, yonedaProfMap]
  have hpara : IsParanatural
      (presheafAsProf (yoneda.obj c₁))
      (presheafAsProf (yoneda.obj c₂)) α.app :=
    α.paranatural
  have hparam :
      IsParamPoly
        (presheafAsProf (yoneda.obj c₁))
        (presheafAsProf (yoneda.obj c₂)) α.app :=
    isParanatural_presheafAsProf_implies_isParamPoly
      (yoneda.obj c₁) (yoneda.obj c₂) hpara
  rw [isParamPoly_presheafAsProf_iff] at hparam
  have hnat := hparam g (𝟙 c₁)
  simp only [yoneda_obj_map, Quiver.Hom.unop_op,
    Category.comp_id] at hnat
  exact hnat

/-- The Yoneda embedding into `EndoProf` is fully
faithful: the map `Hom(c₁, c₂) → Paranat(yonedaProf c₁,
yonedaProf c₂)` is a bijection with inverse given by
evaluation at `𝟙 c₁`. -/
def yonedaEndoProf_fullyFaithful :
    yonedaEndoProf (C := C).FullyFaithful where
  preimage α := α.app _ (𝟙 _)
  map_preimage α :=
    yonedaProfParanat_map_preimage α
  preimage_map f :=
    yonedaProfParanat_preimage_map f

end YonedaEmbedding

section PresheafRelations

/-!
## Presheaf representation of relations

The presheaf `yoneda(X) × yoneda(Y)` represents "coherent
pairs of generalized elements": its category of elements
has objects `(T, a : T ⟶ X, b : T ⟶ Y)` (spans from `X`
to `Y`) and morphisms given by stage-change maps `s : T' ⟶ T`
compatible with both components.

A proof-relevant relation from `X` to `Y` is a presheaf on
this category of elements, or equivalently (by the standard
equivalence `PSh(∫F) ≃ PSh(C)/F`) a morphism into
`yoneda(X) × yoneda(Y)` in `PSh(C)`.

The construction `(X, Y) ↦ yoneda(X) × yoneda(Y)` is
bifunctorial in `X` and `Y`, arising as a composition of
existing higher-order functors: the Yoneda embedding
applied to each component, the functorial pairing into
a product functor category, and the pointwise application
of the binary product on types.
-/

open Limits.Types in
/-- The presheaf `T ↦ Hom(T, X) × Hom(T, Y)`, bifunctorial
in `X` and `Y`, constructed as a composition of the Yoneda
embedding, the functorial pairing
`prodFunctorToFunctorProd`, and the pointwise binary
product on types. -/
def yonedaProd : C ⥤ C ⥤ (Cᵒᵖ ⥤ Type v) :=
  Functor.curry.obj
    ((yoneda (C := C)).prod (yoneda (C := C)) ⋙
     prodFunctorToFunctorProd Cᵒᵖ (Type v) (Type v) ⋙
     (Functor.whiskeringRight Cᵒᵖ _ _).obj
       (Functor.uncurry.obj binaryProductFunctor))

abbrev yonedaProdPresheaf (X Y : C) :
    Cᵒᵖ ⥤ Type v :=
  (yonedaProd.obj X).obj Y

/-- A proof-relevant relation from `X` to `Y` in
`PSh(C)`: an object of the slice category over the
product presheaf `yoneda(X) × yoneda(Y)`. -/
abbrev YonedaProdOver (X Y : C) :=
  Over (yonedaProdPresheaf (C := C) X Y)

/-- The category of elements of `yonedaProd X Y`,
bifunctorial in `X` and `Y`.  The resulting category
(for fixed `X` and `Y`) has objects `(T, a, b)` with
`a : T ⟶ X` and `b : T ⟶ Y` (spans from `X` to `Y`),
and morphisms `s : T' ⟶ T` compatible with both
components.

Constructed as `yonedaProd` post-composed (via
`whiskeringRight`) with the functorial contravariant
category of elements `ElementsPreF`. -/
def yonedaProdElem : C ⥤ C ⥤ Cat :=
  yonedaProd ⋙
    (Functor.whiskeringRight C _ _).obj
      (ElementsPreF Cᵒᵖ)

theorem yonedaProdElem_obj (X Y : C) :
    (yonedaProdElem.obj X).obj Y =
    Cat.of
      (yonedaProdPresheaf X Y).ElementsPre :=
  rfl

/-- The slice category of `PSh(C)` over
`yonedaProd X Y`, bifunctorial in `X` and `Y`.

For fixed `(X, Y)`, the resulting category is
`Over (yonedaProd X Y)`, whose objects are
morphisms `G ⟶ yonedaProd X Y` in `PSh(C)` and
whose morphisms are commuting triangles.  By the
equivalence `sliceEquivCopresheaf`, this is
equivalent to copresheaves on the (covariant)
category of elements of `yonedaProd X Y`, i.e.
presheaves on the category of spans from `X` to `Y`.

Constructed as `yonedaProd` post-composed (via
`whiskeringRight`) with mathlib's `Over.mapFunctor`,
the functorial slice construction. -/
def yonedaProdSlice : C ⥤ C ⥤ Cat :=
  yonedaProd ⋙
    (Functor.whiskeringRight C _ _).obj
      (Over.mapFunctor (Cᵒᵖ ⥤ Type v))

theorem yonedaProdSlice_obj (X Y : C) :
    (yonedaProdSlice.obj X).obj Y =
    Cat.of (YonedaProdOver X Y) :=
  rfl

/-- The presheaf category on the category of elements
of `yonedaProd X Y`.  For fixed `(X, Y)`, this is
`PSh(∫(yoneda(X) × yoneda(Y)))`, whose objects are
presheaves on spans from `X` to `Y`.

For a bifunctorial version, use `yonedaProdSlice`,
which is equivalent pointwise via `sliceEquivPre`. -/
def yonedaProdElemPresheaf (X Y : C) : Cat :=
  Cat.of
    ((yonedaProdPresheaf X Y).ElementsPreᵒᵖ ⥤
      Type v)

/-- The slice category `Over (yonedaProd X Y)` in
`PSh(C)` is equivalent to the presheaf category on
the category of elements of `yonedaProd X Y`.

This is `sliceEquivPre` applied to `yonedaProd X Y`,
witnessing that `yonedaProdSlice` is pointwise the
presheaf topos `PSh(∫(yoneda(X) × yoneda(Y)))`. -/
def yonedaProdSlice_equiv (X Y : C) :
    ((yonedaProdSlice.obj X).obj Y).α ≌
    (yonedaProdElemPresheaf X Y).α :=
  sliceEquivPre (yonedaProdPresheaf X Y)

/-- `(yonedaProd.obj X).obj Y` is the explicit
`FunctorToTypes` product of `yoneda.obj X` and
`yoneda.obj Y`. -/
theorem yonedaProd_eq_prod (X Y : C) :
    yonedaProdPresheaf X Y =
    FunctorToTypes.prod
      (yoneda.obj X) (yoneda.obj Y) :=
  rfl

/-- First projection from the product presheaf
`yonedaProd X Y` to `yoneda X`, via
`FunctorToTypes.prod.fst`. -/
abbrev yonedaProdFst (X Y : C) :
    yonedaProdPresheaf X Y ⟶ yoneda.obj X :=
  @FunctorToTypes.prod.fst
    _ _ (yoneda.obj X) (yoneda.obj Y)

/-- Second projection from the product presheaf
`yonedaProd X Y` to `yoneda Y`, via
`FunctorToTypes.prod.snd`. -/
abbrev yonedaProdSnd (X Y : C) :
    yonedaProdPresheaf X Y ⟶ yoneda.obj Y :=
  @FunctorToTypes.prod.snd
    _ _ (yoneda.obj X) (yoneda.obj Y)

/-- Pairing of morphisms into representables to a
morphism into the product presheaf `yonedaProd X Y`,
via `FunctorToTypes.prod.lift`. -/
abbrev yonedaProdLift {P : Cᵒᵖ ⥤ Type v} (X Y : C)
    (f : P ⟶ yoneda.obj X)
    (g : P ⟶ yoneda.obj Y) :
    P ⟶ yonedaProdPresheaf X Y :=
  FunctorToTypes.prod.lift f g

/-- Two morphisms into `yonedaProdPresheaf X Y` are
equal iff their compositions with the two projections
agree. -/
theorem yonedaProdPresheaf_hom_ext
    {P : Cᵒᵖ ⥤ Type v} {X Y : C}
    {h₁ h₂ : P ⟶ yonedaProdPresheaf X Y}
    (hfst : h₁ ≫ yonedaProdFst X Y =
      h₂ ≫ yonedaProdFst X Y)
    (hsnd : h₁ ≫ yonedaProdSnd X Y =
      h₂ ≫ yonedaProdSnd X Y) :
    h₁ = h₂ := by
  ext T x
  exact Prod.ext
    (congr_fun (NatTrans.congr_app hfst T) x)
    (congr_fun (NatTrans.congr_app hsnd T) x)

@[simp]
theorem yonedaProdLift_fst_snd
    {P : Cᵒᵖ ⥤ Type v} (X Y : C)
    (h : P ⟶ yonedaProdPresheaf X Y) :
    yonedaProdLift X Y
      (h ≫ yonedaProdFst X Y)
      (h ≫ yonedaProdSnd X Y) = h :=
  yonedaProdPresheaf_hom_ext
    (by simp [yonedaProdLift])
    (by simp [yonedaProdLift])

/-- The identity relation on `X` in the over category,
given by the diagonal
`yoneda(X) → yoneda(X) × yoneda(X)`. -/
def yonedaProdOverId (X : C) :
    YonedaProdOver X X :=
  Over.mk (yonedaProdLift X X
    (𝟙 (yoneda.obj X)) (𝟙 (yoneda.obj X)))

@[simp]
theorem yonedaProdOverId_fst (X : C) :
    (yonedaProdOverId X).hom ≫
      yonedaProdFst X X =
    𝟙 (yoneda.obj X) :=
  rfl

@[simp]
theorem yonedaProdOverId_snd (X : C) :
    (yonedaProdOverId X).hom ≫
      yonedaProdSnd X X =
    𝟙 (yoneda.obj X) :=
  rfl

/-- The graph of a morphism `f : X ⟶ Y` as a
proof-relevant relation. The underlying presheaf is
`yoneda(X)`, with first projection the identity and
second projection `yoneda.map f`. At each test object
`T`, a pair `(a : T ⟶ X, b : T ⟶ Y)` is in the graph
iff `b = f ≫ a`. This generalizes `graphRel` from
`Type` to an arbitrary category `C`. -/
def yonedaProdOverGraph {X Y : C} (f : X ⟶ Y) :
    YonedaProdOver X Y :=
  Over.mk (yonedaProdLift X Y
    (𝟙 (yoneda.obj X)) (yoneda.map f))

@[simp]
theorem yonedaProdOverGraph_fst
    {X Y : C} (f : X ⟶ Y) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdFst X Y =
    𝟙 (yoneda.obj X) :=
  rfl

@[simp]
theorem yonedaProdOverGraph_snd
    {X Y : C} (f : X ⟶ Y) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdSnd X Y =
    yoneda.map f :=
  rfl

theorem yonedaProdOverGraph_snd_assoc
    {X Y : C} (f : X ⟶ Y)
    {P : Cᵒᵖ ⥤ Type v}
    (k : yoneda.obj Y ⟶ P) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdSnd X Y ≫ k =
    yoneda.map f ≫ k := by
  rw [← Category.assoc,
    yonedaProdOverGraph_snd]

theorem yonedaProdOverGraph_fst_assoc
    {X Y : C} (f : X ⟶ Y)
    {P : Cᵒᵖ ⥤ Type v}
    (k : yoneda.obj X ⟶ P) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdFst X Y ≫ k =
    k := by
  rw [← Category.assoc,
    yonedaProdOverGraph_fst]
  exact Category.id_comp k

theorem yonedaProdOverGraph_id (X : C) :
    yonedaProdOverGraph (𝟙 X) =
      yonedaProdOverId X := by
  simp [yonedaProdOverGraph, yonedaProdOverId,
    yoneda]

/-- Composition of proof-relevant relations in the over
category.

Given `R ⟶ yonedaProd X Y` and `S ⟶ yonedaProd Y Z`,
their composite is obtained by pulling back `R` and `S`
over `yoneda Y` (matching the second component of `R`
with the first component of `S`), then projecting the
first component from `R` and the second from `S` into
`yonedaProd X Z`. -/
def yonedaProdOverComp {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    YonedaProdOver X Z :=
  Over.mk
    (yonedaProdLift X Z
      (presheafPullbackFst
          (R.hom ≫ yonedaProdSnd X Y)
          (S.hom ≫ yonedaProdFst Y Z) ≫
        R.hom ≫ yonedaProdFst X Y)
      (presheafPullbackSnd
          (R.hom ≫ yonedaProdSnd X Y)
          (S.hom ≫ yonedaProdFst Y Z) ≫
        S.hom ≫ yonedaProdSnd Y Z))

/-- A relation from `X` to `Y` up to isomorphism:
an isomorphism class in the over category
`Over (yonedaProdPresheaf X Y)`. -/
abbrev YonedaRel (X Y : C) :=
  Skeleton (YonedaProdOver X Y)

/-- The identity relation on `X`, up to isomorphism. -/
def relId (X : C) : YonedaRel X X :=
  toSkeleton _ (yonedaProdOverId X)

/-- `yonedaProdOverComp` respects isomorphisms: given
isomorphisms `R₁ ≅ R₂` and `S₁ ≅ S₂` in the over
categories, their compositions are isomorphic. -/
def yonedaProdOverComp_iso {X Y Z : C}
    {R₁ R₂ : YonedaProdOver X Y}
    {S₁ S₂ : YonedaProdOver Y Z}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂) :
    yonedaProdOverComp R₁ S₁ ≅
      yonedaProdOverComp R₂ S₂ := by
  have hR := Over.w αR.hom
  have hS := Over.w αS.hom
  refine Over.isoMk
    (presheafPullbackIsoOfIso
      ((Over.forget _).mapIso αR)
      ((Over.forget _).mapIso αS)
      (by simp only [Functor.mapIso_hom,
        Over.forget_map, ← Category.assoc, hR])
      (by simp only [Functor.mapIso_hom,
        Over.forget_map, ← Category.assoc, hS]))
    ?_
  simp only [yonedaProdOverComp, Over.mk_hom]
  apply yonedaProdPresheaf_hom_ext
  · -- fst projection
    open Limits in
    simp only [Category.assoc,
      FunctorToTypes.prod.lift_fst]
    rw [presheafPullbackIsoOfIso_hom_fst_assoc]
    simp only [Functor.mapIso_hom, Over.forget_map,
      ← Category.assoc, hR]
  · -- snd projection
    open Limits in
    simp only [Category.assoc,
      FunctorToTypes.prod.lift_snd]
    rw [presheafPullbackIsoOfIso_hom_snd_assoc]
    simp only [Functor.mapIso_hom, Over.forget_map,
      ← Category.assoc, hS]

/-- Left identity for `yonedaProdOverComp`: composing
with the identity relation on `X` yields an isomorphic
relation. -/
def yonedaProdOverComp_id_left
    {X Y : C} (R : YonedaProdOver X Y) :
    yonedaProdOverComp (yonedaProdOverId X) R ≅
      R :=
  Over.isoMk
    (presheafPullbackIdLeftIso
      (R.hom ≫ yonedaProdFst X Y))
    (by
      simp only [yonedaProdOverComp, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext
      · simp only [Category.assoc,
          presheafPullbackIdLeftIso]
        have := presheafPullbackCondition
          (𝟙 (yoneda.obj X))
          (R.hom ≫ yonedaProdFst X Y)
        simp only [Category.comp_id] at this
        exact this.symm
      · rfl)

/-- Right identity for `yonedaProdOverComp`: composing
with the identity relation on `Y` yields an isomorphic
relation. -/
def yonedaProdOverComp_id_right
    {X Y : C} (R : YonedaProdOver X Y) :
    yonedaProdOverComp R (yonedaProdOverId Y) ≅
      R :=
  Over.isoMk
    (presheafPullbackIdRightIso
      (R.hom ≫ yonedaProdSnd X Y))
    (by
      simp only [yonedaProdOverComp, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext
      · rfl
      · simp only [Category.assoc,
          presheafPullbackIdRightIso]
        exact presheafPullbackCondition _ _)

/-- Associativity for `yonedaProdOverComp`:
`(R ; S) ; T ≅ R ; (S ; T)`. -/
def yonedaProdOverComp_assoc
    {X Y Z W : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z)
    (T : YonedaProdOver Z W) :
    yonedaProdOverComp
      (yonedaProdOverComp R S) T ≅
    yonedaProdOverComp
      R (yonedaProdOverComp S T) :=
  Over.isoMk
    (presheafPullbackAssocIso
      (R.hom ≫ yonedaProdSnd X Y)
      (S.hom ≫ yonedaProdFst Y Z)
      (S.hom ≫ yonedaProdSnd Y Z)
      (T.hom ≫ yonedaProdFst Z W))
    (by
      simp only [yonedaProdOverComp, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext <;> rfl)

/-- The composite of two graph relations
`graph(f) ; graph(g)` is isomorphic to `graph(f ≫ g)`.
The pullback that defines relational composition
matches `yoneda.map f` with `𝟙 (yoneda Y)`, giving
back `yoneda X` via `presheafPullbackIdRightIso`. -/
def yonedaProdOverGraph_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    yonedaProdOverComp
      (yonedaProdOverGraph f)
      (yonedaProdOverGraph g) ≅
    yonedaProdOverGraph (f ≫ g) :=
  Over.isoMk
    (presheafPullbackIdRightIso (yoneda.map f))
    (by
      simp only [yonedaProdOverComp,
        yonedaProdOverGraph, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext
      · simp [presheafPullbackIdRightIso,
          presheafPullbackLift]
      · simp only [Category.assoc,
          FunctorToTypes.prod.lift_snd,
          FunctorToTypes.prod.lift_fst]
        have hpb := presheafPullbackCondition
          (yoneda.map f) (𝟙 (yoneda.obj Y))
        simp only [Category.comp_id] at hpb
        change presheafPullbackFst
          (yoneda.map f) (𝟙 _) ≫
          yoneda.map (f ≫ g) = _
        rw [yoneda.map_comp,
          ← Category.assoc, hpb])

/-- Composition of relations up to isomorphism:
applies `yonedaProdOverComp` via `Skeleton.lift₂`,
using `yonedaProdOverComp_iso` for
well-definedness. -/
def relComp {X Y Z : C} :
    YonedaRel X Y → YonedaRel Y Z →
    YonedaRel X Z :=
  Skeleton.lift₂
    (fun R S =>
      toSkeleton _ (yonedaProdOverComp R S))
    (fun _ _ _ _ ⟨αR⟩ ⟨αS⟩ =>
      toSkeleton_eq_iff.mpr
        ⟨yonedaProdOverComp_iso αR αS⟩)

theorem relComp_relId_left
    {X Y : C} (R : YonedaRel X Y) :
    relComp (relId X) R = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨yonedaProdOverComp_id_left R'⟩

theorem relComp_relId_right
    {X Y : C} (R : YonedaRel X Y) :
    relComp R (relId Y) = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨yonedaProdOverComp_id_right R'⟩

theorem relComp_assoc
    {X Y Z W : C}
    (R : YonedaRel X Y)
    (S : YonedaRel Y Z)
    (T : YonedaRel Z W) :
    relComp (relComp R S) T =
      relComp R (relComp S T) := by
  induction R using Quotient.inductionOn with
  | h R' =>
  induction S using Quotient.inductionOn with
  | h S' =>
  induction T using Quotient.inductionOn with
  | h T' =>
    exact toSkeleton_eq_iff.mpr
      ⟨yonedaProdOverComp_assoc R' S' T'⟩

/-- The graph of a morphism as a `YonedaRel`
(isomorphism class of `YonedaProdOver`). -/
def yonedaRelGraph {X Y : C} (f : X ⟶ Y) :
    YonedaRel X Y :=
  toSkeleton _ (yonedaProdOverGraph f)

theorem yonedaRelGraph_eq_relId (X : C) :
    yonedaRelGraph (𝟙 X) = relId (C := C) X := by
  simp [yonedaRelGraph, relId,
    yonedaProdOverGraph_id]

theorem yonedaRelGraph_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    relComp (yonedaRelGraph f) (yonedaRelGraph g) =
      yonedaRelGraph (f ≫ g) :=
  toSkeleton_eq_iff.mpr
    ⟨yonedaProdOverGraph_comp f g⟩

end PresheafRelations

section YonedaRelCategory

/-- Wrapper type for objects of `C` whose morphisms
are Yoneda relations (`YonedaRel`). Using a
`structure` prevents the existing `Category` instance
on `C` from leaking through. -/
@[ext]
structure YonedaRelCat (C : Type u)
    [Category.{v} C] where
  obj : C

instance : Category.{max u (v + 1)}
    (YonedaRelCat C) where
  Hom X Y := YonedaRel X.obj Y.obj
  id X := relId X.obj
  comp R S := relComp R S
  id_comp := relComp_relId_left
  comp_id := relComp_relId_right
  assoc := relComp_assoc

/-- Functor sending each morphism `f : X ⟶ Y` in
`C` to its graph relation `yonedaRelGraph f` in
`YonedaRelCat C`. This is the categorical
generalization of the assignment `f ↦ graphRel f`
from `Type` to an arbitrary category. -/
def yonedaRelGraphFunctor :
    C ⥤ YonedaRelCat C where
  obj X := ⟨X⟩
  map f := yonedaRelGraph f
  map_id X := yonedaRelGraph_eq_relId X
  map_comp f g := (yonedaRelGraph_comp f g).symm

end YonedaRelCategory

section RelatedMorphisms

/-- The bifunctorial action of a pair of morphisms
`(f, f')` on the product presheaf
`yoneda(A) × yoneda(A')`. At stage `T`, this sends
`(a : T ⟶ A, a' : T ⟶ A')` to
`(a ≫ f : T ⟶ B, a' ≫ f' : T ⟶ B')`. -/
abbrev yonedaProdMap {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdPresheaf A A' ⟶
      yonedaProdPresheaf B B' :=
  yonedaProdLift B B'
    (yonedaProdFst A A' ≫ yoneda.map f)
    (yonedaProdSnd A A' ≫ yoneda.map f')

@[simp]
theorem yonedaProdMap_fst {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdMap f f' ≫ yonedaProdFst B B' =
      yonedaProdFst A A' ≫ yoneda.map f := by
  simp [yonedaProdMap, yonedaProdLift]

@[simp]
theorem yonedaProdMap_snd {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdMap f f' ≫ yonedaProdSnd B B' =
      yonedaProdSnd A A' ≫ yoneda.map f' := by
  simp [yonedaProdMap, yonedaProdLift]

@[simp]
theorem yonedaProdMap_id (A A' : C) :
    yonedaProdMap (𝟙 A) (𝟙 A') =
      𝟙 (yonedaProdPresheaf A A') := by
  apply yonedaProdPresheaf_hom_ext <;>
    simp [yoneda]

theorem yonedaProdMap_comp
    {A A' B B' D D' : C}
    (f : A ⟶ B) (f' : A' ⟶ B')
    (g : B ⟶ D) (g' : B' ⟶ D') :
    yonedaProdMap (f ≫ g) (f' ≫ g') =
      yonedaProdMap f f' ≫
        yonedaProdMap g g' := by
  apply yonedaProdPresheaf_hom_ext <;> {
    simp only [Category.assoc,
      yonedaProdMap_fst, yonedaProdMap_snd]
    simp only [← Category.assoc,
      yonedaProdMap_fst, yonedaProdMap_snd]
    simp only [Category.assoc, yoneda.map_comp]
  }

/-- Two morphisms `f : A ⟶ B` and `f' : A' ⟶ B'` are
`(R, S)`-related at the `YonedaProdOver` level when
there exists a lift `φ : R.left ⟶ S.left` making the
square commute:
```
  R.left ---φ---> S.left
    |                |
    R.hom           S.hom
    v                v
  yonedaProd A A' -> yonedaProd B B'
         (yonedaProdMap f f')
```
-/
def YonedaProdOverRelated
    {A A' B B' : C}
    (R : YonedaProdOver A A')
    (S : YonedaProdOver B B')
    (f : A ⟶ B) (f' : A' ⟶ B') : Prop :=
  ∃ (φ : R.left ⟶ S.left),
    φ ≫ S.hom =
      R.hom ≫ yonedaProdMap f f'

/-- `YonedaProdOverRelated` is invariant under
isomorphism in both relation arguments. -/
theorem yonedaProdOverRelated_iso
    {A A' B B' : C}
    {R₁ R₂ : YonedaProdOver A A'}
    {S₁ S₂ : YonedaProdOver B B'}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂)
    {f : A ⟶ B} {f' : A' ⟶ B'} :
    YonedaProdOverRelated R₁ S₁ f f' ↔
      YonedaProdOverRelated R₂ S₂ f f' := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨αR.inv.left ≫ φ ≫ αS.hom.left, by
      simp only [Category.assoc, Over.w αS.hom]
      rw [hφ, ← Category.assoc,
        Over.w αR.inv]⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨αR.hom.left ≫ φ ≫ αS.inv.left, by
      simp only [Category.assoc, Over.w αS.inv]
      rw [hφ, ← Category.assoc,
        Over.w αR.hom]⟩

/-- Two morphisms `f : A ⟶ B` and `f' : A' ⟶ B'` in
`C` are `(R, S)`-related (where `R : YonedaRel A A'` and
`S : YonedaRel B B'`) when they admit a lifting at the
`YonedaProdOver` level. This descends through the
skeleton quotient via `Skeleton.lift₂`, using
`yonedaProdOverRelated_iso` for well-definedness. -/
def relRelated
    {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    YonedaRel A A' → YonedaRel B B' → Prop :=
  Skeleton.lift₂
    (fun R S =>
      YonedaProdOverRelated R S f f')
    (fun _ _ _ _ ⟨αR⟩ ⟨αS⟩ =>
      propext
        (yonedaProdOverRelated_iso αR αS))

/-- For graph relations, `YonedaProdOverRelated`
reduces to commutativity of the naturality square.
The forward direction extracts the square from the
lift; the reverse constructs a lift from the commuting
square using `yoneda.map g₀`. -/
theorem yonedaProdOverRelated_graph_iff
    {A A' B B' : C}
    (f : A ⟶ A') (f' : B ⟶ B')
    (g₀ : A ⟶ B) (g₁ : A' ⟶ B') :
    YonedaProdOverRelated
      (yonedaProdOverGraph f)
      (yonedaProdOverGraph f')
      g₀ g₁ ↔
    g₀ ≫ f' = f ≫ g₁ := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hfst : φ = yoneda.map g₀ := by
      have h :=
        congr_arg (· ≫ yonedaProdFst B B') hφ
      simp only [Category.assoc,
        yonedaProdOverGraph_fst,
        yonedaProdOverGraph_fst_assoc,
        yonedaProdMap_fst] at h
      exact h
    have hsnd : φ ≫ yoneda.map f' =
        yoneda.map f ≫ yoneda.map g₁ := by
      have h :=
        congr_arg (· ≫ yonedaProdSnd B B') hφ
      simp only [Category.assoc,
        yonedaProdOverGraph_snd,
        yonedaProdOverGraph_snd_assoc,
        yonedaProdMap_snd] at h
      exact h
    rw [hfst] at hsnd
    rw [← yoneda.map_comp,
      ← yoneda.map_comp] at hsnd
    exact yoneda.map_injective hsnd
  · intro hsq
    refine ⟨yoneda.map g₀, ?_⟩
    apply yonedaProdPresheaf_hom_ext
    · simp only [Category.assoc,
        yonedaProdOverGraph_fst,
        yonedaProdOverGraph_fst_assoc,
        yonedaProdMap_fst]
      exact Category.comp_id _
    · simp only [Category.assoc,
        yonedaProdOverGraph_snd,
        yonedaProdOverGraph_snd_assoc,
        yonedaProdMap_snd]
      rw [← yoneda.map_comp, hsq,
        yoneda.map_comp]

end RelatedMorphisms

section FunctorRelationLifting

/-- Predicate asserting that an element `p` of
`yonedaProdPresheaf (F.obj A) (F.obj A')` at test
object `T` lies in the relation lifted through `F`
from `R : YonedaProdOver A A'`.

Concretely, `p = (g, h)` satisfies the predicate when
there exist `S : C`, `e : R.left.obj (op S)`, and
`t : T.unop ⟶ F.obj S` such that
`t ≫ F.map r = g` and `t ≫ F.map r' = h`, where
`r` and `r'` are the first and second projections of
the image of `e` under `R.hom`. -/
def functorYPOLiftPred
    {A A' : C} (F : C ⥤ C)
    (R : YonedaProdOver A A')
    (T : Cᵒᵖ)
    (p : (yonedaProdPresheaf
      (F.obj A) (F.obj A')).obj T) :
    Prop :=
  ∃ (S : C)
    (e : R.left.obj (Opposite.op S))
    (t : T.unop ⟶ F.obj S),
    t ≫ F.map ((R.hom ≫ yonedaProdFst A A').app
      (Opposite.op S) e) =
      (yonedaProdFst (F.obj A) (F.obj A')).app
        T p ∧
    t ≫ F.map ((R.hom ≫ yonedaProdSnd A A').app
      (Opposite.op S) e) =
      (yonedaProdSnd (F.obj A) (F.obj A')).app
        T p

theorem functorYPOLiftPred_map
    {A A' : C} (F : C ⥤ C)
    (R : YonedaProdOver A A')
    {T' T : Cᵒᵖ} (s : T' ⟶ T)
    {p : (yonedaProdPresheaf
      (F.obj A) (F.obj A')).obj T'}
    (hp : functorYPOLiftPred F R T' p) :
    functorYPOLiftPred F R T
      ((yonedaProdPresheaf
        (F.obj A) (F.obj A')).map s p) := by
  obtain ⟨S, e, t, hfst, hsnd⟩ := hp
  refine ⟨S, e, s.unop ≫ t, ?_, ?_⟩
  · rw [Category.assoc, hfst]; rfl
  · rw [Category.assoc, hsnd]; rfl

/-- The subtype presheaf whose elements at `T` are
pairs `(g, h)` in
`yonedaProdPresheaf (F.obj A) (F.obj A')` satisfying
`functorYPOLiftPred F R T`. Functoriality follows
from `functorYPOLiftPred_map`. -/
def functorYPOLiftPresheaf
    {A A' : C} (F : C ⥤ C)
    (R : YonedaProdOver A A') :
    Cᵒᵖ ⥤ Type v where
  obj T := { p : (yonedaProdPresheaf
    (F.obj A) (F.obj A')).obj T //
    functorYPOLiftPred F R T p }
  map s x := ⟨(yonedaProdPresheaf
    (F.obj A) (F.obj A')).map s x.val,
    functorYPOLiftPred_map F R s x.property⟩
  map_id T := by
    ext ⟨x, hx⟩
    simp
  map_comp s t := by
    ext ⟨x, hx⟩
    simp [FunctorToTypes.map_comp_apply]

/-- The forgetful natural transformation from the
subtype presheaf `functorYPOLiftPresheaf F R` to
`yonedaProdPresheaf (F.obj A) (F.obj A')`. -/
def functorYPOLiftProj
    {A A' : C} (F : C ⥤ C)
    (R : YonedaProdOver A A') :
    functorYPOLiftPresheaf F R ⟶
      yonedaProdPresheaf (F.obj A) (F.obj A') where
  app _ x := x.val
  naturality _ _ _ := rfl

/-- Lifting a relation `R : YonedaProdOver A A'`
through an endofunctor `F : C ⥤ C`. The underlying
presheaf consists of pairs `(g, h)` in
`yoneda(F A) × yoneda(F A')` that factor through
`F` applied to a witness span from `R`. -/
def functorYPOLift
    {A A' : C} (F : C ⥤ C)
    (R : YonedaProdOver A A') :
    YonedaProdOver (F.obj A) (F.obj A') :=
  Over.mk (functorYPOLiftProj F R)

/-- For graph relations, the lifted predicate forces
the second component to equal the first composed with
`F.map f`. -/
theorem functorYPOLiftPred_graph_snd
    {A A' : C} (F : C ⥤ C) (f : A ⟶ A')
    (T : Cᵒᵖ)
    (p : (yonedaProdPresheaf
      (F.obj A) (F.obj A')).obj T)
    (hp : functorYPOLiftPred F
      (yonedaProdOverGraph f) T p) :
    (yonedaProdSnd (F.obj A) (F.obj A')).app T p =
      (yonedaProdFst (F.obj A) (F.obj A')).app
        T p ≫ F.map f := by
  obtain ⟨S, e, t, hfst, hsnd⟩ := hp
  simp only [yonedaProdOverGraph_fst] at hfst
  simp only [yonedaProdOverGraph_snd] at hsnd
  rw [← hsnd, ← hfst, Category.assoc, ← F.map_comp]
  simp [yoneda]

/-- For any `g : T.unop ⟶ F.obj A`, the pair
`(g, g ≫ F.map f)` satisfies the lifted predicate
for the graph of `f`, witnessed by
`S = A, e = 𝟙 A, t = g`. -/
theorem functorYPOLiftPred_graph_inv
    {A A' : C} (F : C ⥤ C) (f : A ⟶ A')
    (T : Cᵒᵖ)
    (g : (yoneda.obj (F.obj A)).obj T) :
    functorYPOLiftPred F (yonedaProdOverGraph f) T
      ((yonedaProdLift (F.obj A) (F.obj A')
        (𝟙 (yoneda.obj (F.obj A)))
        (yoneda.map (F.map f))).app T g) := by
  refine ⟨A, 𝟙 A, g, ?_, ?_⟩
  · simp [yoneda, F.map_id]
  · simp [yoneda]

/-- The presheaf underlying
`functorYPOLift F (yonedaProdOverGraph f)` is
naturally isomorphic to `yoneda.obj (F.obj A)`:
the lifted graph relation is representable. -/
def functorYPOLiftPresheaf_graphIso
    {A A' : C} (F : C ⥤ C) (f : A ⟶ A') :
    functorYPOLiftPresheaf F
      (yonedaProdOverGraph f) ≅
      yoneda.obj (F.obj A) :=
  NatIso.ofComponents
    (fun T => {
      hom := fun ⟨p, _⟩ =>
        (yonedaProdFst (F.obj A) (F.obj A')).app
          T p
      inv := fun g =>
        ⟨(yonedaProdLift (F.obj A) (F.obj A')
          (𝟙 (yoneda.obj (F.obj A)))
          (yoneda.map (F.map f))).app T g,
        functorYPOLiftPred_graph_inv F f T g⟩
      hom_inv_id := by
        ext ⟨p, hp⟩
        simp only [types_comp_apply, types_id_apply]
        exact Subtype.ext (Prod.ext rfl
          (functorYPOLiftPred_graph_snd
            F f T p hp).symm)
      inv_hom_id := by
        ext g
        simp [types_comp_apply, types_id_apply]
    })
    (by intro T' T s; ext ⟨p, hp⟩; rfl)

/-- The lifted graph relation in the Over category is
isomorphic to the graph of `F.map f`. -/
def functorYPOLift_graphIso
    {A A' : C} (F : C ⥤ C) (f : A ⟶ A') :
    functorYPOLift F (yonedaProdOverGraph f) ≅
      yonedaProdOverGraph (F.map f) :=
  Over.isoMk
    (functorYPOLiftPresheaf_graphIso F f)
    (by
      ext T ⟨p, hp⟩
      exact Prod.ext rfl
        (functorYPOLiftPred_graph_snd
          F f T p hp).symm)

/-- The lifted predicate is preserved by Over
morphisms: if `φ : R₁ ⟶ R₂` and
`functorYPOLiftPred F R₁ T p`, then
`functorYPOLiftPred F R₂ T p`.
The witness `(S, e, t)` transforms to
`(S, φ.left.app (op S) e, t)`. -/
theorem functorYPOLiftPred_of_over_hom
    {A A' : C} (F : C ⥤ C)
    {R₁ R₂ : YonedaProdOver A A'}
    (φ : R₁ ⟶ R₂)
    (T : Cᵒᵖ)
    (p : (yonedaProdPresheaf
      (F.obj A) (F.obj A')).obj T)
    (hp : functorYPOLiftPred F R₁ T p) :
    functorYPOLiftPred F R₂ T p := by
  obtain ⟨S, e, t, hfst, hsnd⟩ := hp
  have hR := Over.w φ
  have hR_fst :
      (R₂.hom ≫ yonedaProdFst A A').app
        (Opposite.op S)
        (φ.left.app (Opposite.op S) e) =
      (R₁.hom ≫ yonedaProdFst A A').app
        (Opposite.op S) e := by
    change ((φ.left ≫ R₂.hom) ≫
      yonedaProdFst A A').app
        (Opposite.op S) e = _
    rw [hR]
  have hR_snd :
      (R₂.hom ≫ yonedaProdSnd A A').app
        (Opposite.op S)
        (φ.left.app (Opposite.op S) e) =
      (R₁.hom ≫ yonedaProdSnd A A').app
        (Opposite.op S) e := by
    change ((φ.left ≫ R₂.hom) ≫
      yonedaProdSnd A A').app
        (Opposite.op S) e = _
    rw [hR]
  exact ⟨S, φ.left.app (Opposite.op S) e, t,
    by rw [hR_fst, hfst],
    by rw [hR_snd, hsnd]⟩

/-- `functorYPOLift F` preserves isomorphisms in the
Over category: if `R₁ ≅ R₂`, then
`functorYPOLift F R₁ ≅ functorYPOLift F R₂`.
The underlying element is unchanged; only the
predicate proof is transported. -/
def functorYPOLift_iso
    {A A' : C} (F : C ⥤ C)
    {R₁ R₂ : YonedaProdOver A A'}
    (α : R₁ ≅ R₂) :
    functorYPOLift F R₁ ≅
      functorYPOLift F R₂ :=
  Over.isoMk
    (NatIso.ofComponents
      (fun T => {
        hom := fun ⟨p, hp⟩ =>
          ⟨p, functorYPOLiftPred_of_over_hom
            F α.hom T p hp⟩
        inv := fun ⟨p, hp⟩ =>
          ⟨p, functorYPOLiftPred_of_over_hom
            F α.inv T p hp⟩
        hom_inv_id := by ext; rfl
        inv_hom_id := by ext; rfl
      })
      (by intros; ext; rfl))
    (by ext; rfl)

/-- Lifting a relation from `YonedaRel A A'`
through an endofunctor `F : C ⥤ C`. Descends through
the skeleton quotient using `Skeleton.lift` and
`functorYPOLift_iso` for well-definedness. -/
def functorYonedaRelLift
    {A A' : C} (F : C ⥤ C)
    (R : YonedaRel A A') :
    YonedaRel (F.obj A) (F.obj A') :=
  Skeleton.lift
    (fun R' => toSkeleton _ (functorYPOLift F R'))
    (fun _ _ ⟨α⟩ =>
      toSkeleton_eq_iff.mpr
        ⟨functorYPOLift_iso F α⟩) R

/-- Lifting the graph of `f` through `F` yields the
graph of `F.map f`. -/
theorem functorYonedaRelLift_graph
    {A A' : C} (F : C ⥤ C) (f : A ⟶ A') :
    functorYonedaRelLift F (yonedaRelGraph f) =
      yonedaRelGraph (F.map f) :=
  toSkeleton_eq_iff.mpr
    ⟨functorYPOLift_graphIso F f⟩

/-- The lifted predicate for `S` is satisfied by
`yonedaProdMap (F.map f) (F.map f')` applied to an
element satisfying the predicate for `R`, given a
lift `φ : R.left ⟶ S.left` witnessing
`YonedaProdOverRelated R S f f'`. -/
theorem functorYPOLiftPred_related_map
    {A A' B B' : C} (F : C ⥤ C)
    {R : YonedaProdOver A A'}
    {S : YonedaProdOver B B'}
    {f : A ⟶ B} {f' : A' ⟶ B'}
    (φ : R.left ⟶ S.left)
    (hφ : φ ≫ S.hom =
      R.hom ≫ yonedaProdMap f f')
    (T : Cᵒᵖ)
    (p : (yonedaProdPresheaf
      (F.obj A) (F.obj A')).obj T)
    (hp : functorYPOLiftPred F R T p) :
    functorYPOLiftPred F S T
      ((yonedaProdMap (F.map f)
        (F.map f')).app T p) := by
  obtain ⟨S₀, e, t, hfst, hsnd⟩ := hp
  refine ⟨S₀, φ.app (Opposite.op S₀) e,
    t, ?_, ?_⟩
  · have hkey :
        (S.hom ≫ yonedaProdFst B B').app
          (Opposite.op S₀)
          (φ.app (Opposite.op S₀) e) =
        (R.hom ≫ yonedaProdFst A A').app
          (Opposite.op S₀) e ≫ f := by
      change ((φ ≫ S.hom) ≫
        yonedaProdFst B B').app
          (Opposite.op S₀) e = _
      rw [hφ]
      simp only [Category.assoc,
        yonedaProdMap_fst]
      rfl
    rw [hkey, F.map_comp,
      ← Category.assoc, hfst]
    rfl
  · have hkey :
        (S.hom ≫ yonedaProdSnd B B').app
          (Opposite.op S₀)
          (φ.app (Opposite.op S₀) e) =
        (R.hom ≫ yonedaProdSnd A A').app
          (Opposite.op S₀) e ≫ f' := by
      change ((φ ≫ S.hom) ≫
        yonedaProdSnd B B').app
          (Opposite.op S₀) e = _
      rw [hφ]
      simp only [Category.assoc,
        yonedaProdMap_snd]
      rfl
    rw [hkey, F.map_comp,
      ← Category.assoc, hsnd]
    rfl

/-- `functorYPOLift` preserves 2-cell relatedness:
if morphisms `(f, f')` are `(R, S)`-related, then
`(F.map f, F.map f')` are
`(functorYPOLift F R, functorYPOLift F S)`-related. -/
theorem functorYPOLift_related
    {A A' B B' : C} (F : C ⥤ C)
    {R : YonedaProdOver A A'}
    {S : YonedaProdOver B B'}
    {f : A ⟶ B} {f' : A' ⟶ B'}
    (h : YonedaProdOverRelated R S f f') :
    YonedaProdOverRelated
      (functorYPOLift F R)
      (functorYPOLift F S)
      (F.map f) (F.map f') := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨{
    app := fun T ⟨p, hp⟩ =>
      ⟨(yonedaProdMap (F.map f)
        (F.map f')).app T p,
      functorYPOLiftPred_related_map
        F φ hφ T p hp⟩
    naturality := by
      intro T' T s
      ext ⟨p, hp⟩
      refine Subtype.ext ?_
      exact congr_fun
        ((yonedaProdMap (F.map f)
          (F.map f')).naturality s) p
  }, ?_⟩
  ext T ⟨p, hp⟩
  rfl

/-- `functorYPOLift_related` descends through the
skeleton quotient: if `f` and `f'` are
`(R, S)`-related at the `YonedaRel` level,
then `F.map f` and `F.map f'` are
`(functorYonedaRelLift F R,
functorYonedaRelLift F S)`-related. -/
theorem functorYonedaRelLift_related
    {A A' B B' : C} (F : C ⥤ C)
    {f : A ⟶ B} {f' : A' ⟶ B'}
    {R : YonedaRel A A'} {S : YonedaRel B B'}
    (h : relRelated f f' R S) :
    relRelated (F.map f) (F.map f')
      (functorYonedaRelLift F R)
      (functorYonedaRelLift F S) := by
  revert h
  refine Quotient.inductionOn₂ R S ?_
  intro R₀ S₀ h
  exact functorYPOLift_related F h

end FunctorRelationLifting

end GebLean
