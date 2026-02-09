import GebLean.Paranatural

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

end ParametricPolymorphism

end GebLean
