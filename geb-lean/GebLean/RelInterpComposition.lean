import GebLean.ParanaturalTopos

/-!
# Composition properties of relational interpretation

This module studies when `TypeExpr.relInterp` composes
transitively: given `T.relInterp f x y` and
`T.relInterp g y z`, when does
`T.relInterp (g ∘ f) x z` hold?

The composition property holds for variables (`graphRel`),
functor applications (`functorRelLift` of `graphRel`),
and arrows whose domain admits decomposition.  The
decomposition property (existence of an intermediate
witness) holds for variables and leaves but fails for
arrow types, preventing composition for type expressions
with nested contravariant arrows.
-/

open CategoryTheory

namespace GebLean

/-- Composition of `graphRel`: if `f a = b` and
`g b = c`, then `(g ∘ f) a = c`. -/
theorem graphRel_comp
    {A B C : Type}
    {f : A → B} {g : B → C}
    {a : A} {b : B} {c : C}
    (hf : graphRel f a b)
    (hg : graphRel g b c) :
    graphRel (g ∘ f) a c := by
  simp only [graphRel] at *
  rw [Function.comp_apply, hf, hg]

/-- Decomposition of `graphRel`: if
`(g ∘ f) a = c`, then there exists `b` with
`f a = b` and `g b = c`. -/
theorem graphRel_decomp
    {A B C : Type}
    {f : A → B} {g : B → C}
    {a : A} {c : C}
    (h : graphRel (g ∘ f) a c) :
    ∃ (b : B),
      graphRel f a b ∧ graphRel g b c := by
  exact ⟨f a, rfl, h⟩

/-- `relInterp` composition for `var`:
`graphRel f` and `graphRel g` compose to
`graphRel (g ∘ f)`. -/
theorem TypeExpr.relInterp_comp_var
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    {x : I₀} {y : I₁} {z : I₂}
    (hf : TypeExpr.var.relInterp f x y)
    (hg : TypeExpr.var.relInterp g y z) :
    TypeExpr.var.relInterp (g ∘ f) x z :=
  graphRel_comp hf hg

/-- `relInterp` decomposition for `var`:
`graphRel (g ∘ f)` decomposes into `graphRel f`
and `graphRel g`. -/
theorem TypeExpr.relInterp_decomp_var
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    {x : I₀} {z : I₂}
    (h : TypeExpr.var.relInterp (g ∘ f) x z) :
    ∃ (y : I₁),
      TypeExpr.var.relInterp f x y ∧
      TypeExpr.var.relInterp g y z :=
  graphRel_decomp h

/-- `relInterp` composition for `leaf F`:
`functorRelLift F (graphRel f)` and
`functorRelLift F (graphRel g)` compose to
`functorRelLift F (graphRel (g ∘ f))`. -/
theorem TypeExpr.relInterp_comp_leaf
    (F : Type ⥤ Type)
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    {x : F.obj I₀} {y : F.obj I₁}
    {z : F.obj I₂}
    (hf : (TypeExpr.leaf F).relInterp f x y)
    (hg : (TypeExpr.leaf F).relInterp g y z) :
    (TypeExpr.leaf F).relInterp (g ∘ f) x z := by
  simp only [TypeExpr.leaf_relInterp,
    graphRel] at *
  rw [show F.map (g ∘ f) =
    F.map g ∘ F.map f from by
      ext a
      exact FunctorToTypes.map_comp_apply
        F f g a]
  simp only [Function.comp_apply, hf, hg]

/-- `relInterp` decomposition for `leaf F`:
`functorRelLift F (graphRel (g ∘ f))` decomposes
into `functorRelLift F (graphRel f)` and
`functorRelLift F (graphRel g)`. -/
theorem TypeExpr.relInterp_decomp_leaf
    (F : Type ⥤ Type)
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    {x : F.obj I₀} {z : F.obj I₂}
    (h : (TypeExpr.leaf F).relInterp
      (g ∘ f) x z) :
    ∃ (y : F.obj I₁),
      (TypeExpr.leaf F).relInterp f x y ∧
      (TypeExpr.leaf F).relInterp g y z := by
  simp only [TypeExpr.leaf_relInterp] at *
  simp only [graphRel] at *
  exact ⟨F.map f x,
    rfl,
    by rw [← FunctorToTypes.map_comp_apply]; exact h⟩

/-- Composition of `arrowRel`: if the domain
relation decomposes and the codomain relation
composes, then `arrowRel` composes.

Given `arrowRel R₁ S₁ h₀ h₁` and
`arrowRel R₂ S₂ h₁ h₂`, to show
`arrowRel R₁₂ S₁₂ h₀ h₂`, we decompose each
`R₁₂`-related pair `(a₀, a₂)` through an
intermediate `a₁` using the domain decomposition,
then compose the two `S`-related steps. -/
theorem arrowRel_comp
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type}
    {R₁ : A₀ → A₁ → Prop}
    {R₂ : A₁ → A₂ → Prop}
    {R₁₂ : A₀ → A₂ → Prop}
    {S₁ : B₀ → B₁ → Prop}
    {S₂ : B₁ → B₂ → Prop}
    {S₁₂ : B₀ → B₂ → Prop}
    (hR_decomp : ∀ (a₀ : A₀) (a₂ : A₂),
      R₁₂ a₀ a₂ →
      ∃ (a₁ : A₁), R₁ a₀ a₁ ∧ R₂ a₁ a₂)
    (hS_comp : ∀ (b₀ : B₀) (b₁ : B₁)
      (b₂ : B₂),
      S₁ b₀ b₁ → S₂ b₁ b₂ → S₁₂ b₀ b₂)
    {h₀ : A₀ → B₀} {h₁ : A₁ → B₁}
    {h₂ : A₂ → B₂}
    (hf : arrowRel R₁ S₁ h₀ h₁)
    (hg : arrowRel R₂ S₂ h₁ h₂) :
    arrowRel R₁₂ S₁₂ h₀ h₂ := by
  intro a₀ a₂ hrel
  obtain ⟨a₁, hr₁, hr₂⟩ := hR_decomp a₀ a₂ hrel
  exact hS_comp (h₀ a₀) (h₁ a₁) (h₂ a₂)
    (hf a₀ a₁ hr₁) (hg a₁ a₂ hr₂)

/-- `relInterp` composition for `arrow T₁ T₂`:
if `T₁.relInterp` decomposes and `T₂.relInterp`
composes, then `(arrow T₁ T₂).relInterp`
composes. -/
theorem TypeExpr.relInterp_comp_arrow
    {T₁ T₂ : TypeExpr}
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    (hT₁_decomp :
      ∀ (x : T₁.interp I₀ I₀)
        (z : T₁.interp I₂ I₂),
        T₁.relInterp (g ∘ f) x z →
        ∃ (y : T₁.interp I₁ I₁),
          T₁.relInterp f x y ∧
          T₁.relInterp g y z)
    (hT₂_comp :
      ∀ (x : T₂.interp I₀ I₀)
        (y : T₂.interp I₁ I₁)
        (z : T₂.interp I₂ I₂),
        T₂.relInterp f x y →
        T₂.relInterp g y z →
        T₂.relInterp (g ∘ f) x z)
    {h₀ : T₁.interp I₀ I₀ → T₂.interp I₀ I₀}
    {h₁ : T₁.interp I₁ I₁ → T₂.interp I₁ I₁}
    {h₂ : T₁.interp I₂ I₂ → T₂.interp I₂ I₂}
    (hf : (TypeExpr.arrow T₁ T₂).relInterp
      f h₀ h₁)
    (hg : (TypeExpr.arrow T₁ T₂).relInterp
      g h₁ h₂) :
    (TypeExpr.arrow T₁ T₂).relInterp
      (g ∘ f) h₀ h₂ :=
  arrowRel_comp hT₁_decomp hT₂_comp hf hg

/-- A type expression is arrow-free when it
contains no `arrow` constructor.  For arrow-free
type expressions, `interp T A B` depends only on
`B` (the covariant parameter), and `relInterp f`
reduces to the graph of a function. -/
def TypeExpr.isArrowFree : TypeExpr → Bool
  | .var => true
  | .app _ T => T.isArrowFree
  | .arrow _ _ => false

/-- The covariant map of an arrow-free type
expression at `f : I₀ → I₁`, producing a
function `T.interp I₀ I₀ → T.interp I₁ I₁`.
For arrow-free T, `interp T A B` depends only
on `B`, so this is the natural covariant
action. -/
def TypeExpr.arrowFreeMap
    (T : TypeExpr)
    (haf : T.isArrowFree = true)
    {I₀ I₁ : Type}
    (f : I₀ → I₁) :
    T.interp I₀ I₀ → T.interp I₁ I₁ :=
  match T, haf with
  | .var, _ => f
  | .app F T, haf =>
    F.map (T.arrowFreeMap haf f)

/-- For arrow-free type expressions, the
relational interpretation at `f` equals
`graphRel (arrowFreeMap T haf f)`. -/
theorem TypeExpr.relInterp_eq_graphRel
    (T : TypeExpr)
    (haf : T.isArrowFree = true)
    {I₀ I₁ : Type} (f : I₀ → I₁) :
    T.relInterp f =
    graphRel (T.arrowFreeMap haf f) := by
  match T, haf with
  | .var, _ => rfl
  | .app F T, haf =>
    simp only [TypeExpr.relInterp,
      TypeExpr.arrowFreeMap]
    rw [TypeExpr.relInterp_eq_graphRel T haf f]
    exact functorRelLift_graphRel F
      (T.arrowFreeMap haf f)

/-- `arrowFreeMap` preserves composition:
`arrowFreeMap T haf (g ∘ f) =
arrowFreeMap T haf g ∘ arrowFreeMap T haf f`. -/
theorem TypeExpr.arrowFreeMap_comp
    (T : TypeExpr)
    (haf : T.isArrowFree = true)
    {I₀ I₁ I₂ : Type}
    (f : I₀ → I₁) (g : I₁ → I₂) :
    T.arrowFreeMap haf (g ∘ f) =
    T.arrowFreeMap haf g ∘
      T.arrowFreeMap haf f := by
  match T, haf with
  | .var, _ => rfl
  | .app F T, haf =>
    simp only [TypeExpr.arrowFreeMap]
    rw [T.arrowFreeMap_comp haf f g]
    ext x
    exact FunctorToTypes.map_comp_apply F
      (T.arrowFreeMap haf f)
      (T.arrowFreeMap haf g) x

/-- Composition of `relInterp` for arrow-free
type expressions. -/
theorem TypeExpr.relInterp_comp_of_isArrowFree
    (T : TypeExpr)
    (haf : T.isArrowFree = true)
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    {x : T.interp I₀ I₀}
    {y : T.interp I₁ I₁}
    {z : T.interp I₂ I₂}
    (hf : T.relInterp f x y)
    (hg : T.relInterp g y z) :
    T.relInterp (g ∘ f) x z := by
  rw [T.relInterp_eq_graphRel haf] at *
  simp only [graphRel] at *
  rw [T.arrowFreeMap_comp haf f g]
  simp only [Function.comp_apply, hf, hg]

/-- Decomposition of `relInterp` for arrow-free
type expressions. -/
theorem TypeExpr.relInterp_decomp_of_isArrowFree
    (T : TypeExpr)
    (haf : T.isArrowFree = true)
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    {x : T.interp I₀ I₀}
    {z : T.interp I₂ I₂}
    (h : T.relInterp (g ∘ f) x z) :
    ∃ (y : T.interp I₁ I₁),
      T.relInterp f x y ∧
      T.relInterp g y z := by
  rw [T.relInterp_eq_graphRel haf (g ∘ f)] at h
  rw [T.relInterp_eq_graphRel haf f,
    T.relInterp_eq_graphRel haf g]
  rw [T.arrowFreeMap_comp haf f g] at h
  exact graphRel_decomp h

/-- The hom type expression `X → X`. -/
abbrev homTypeExpr : TypeExpr :=
  TypeExpr.arrow TypeExpr.var TypeExpr.var

/-- A type expression has composable `relInterp`
when every `arrow` node has an arrow-free domain.
Arrow-free types compose via graph-relation
composition; arrow types compose when the domain
decomposes (requiring arrow-freeness) and the
codomain composes (recursive). -/
def TypeExpr.hasRelInterpComp :
    TypeExpr → Bool
  | .var => true
  | .app _ T => T.isArrowFree
  | .arrow T₁ T₂ =>
    T₁.isArrowFree && T₂.hasRelInterpComp

/-- `relInterp` composes for type expressions
satisfying `hasRelInterpComp`. -/
theorem TypeExpr.relInterp_comp_of_hasComp
    (T : TypeExpr)
    (hc : T.hasRelInterpComp = true)
    {I₀ I₁ I₂ : Type}
    {f : I₀ → I₁} {g : I₁ → I₂}
    {x : T.interp I₀ I₀}
    {y : T.interp I₁ I₁}
    {z : T.interp I₂ I₂}
    (hf : T.relInterp f x y)
    (hg : T.relInterp g y z) :
    T.relInterp (g ∘ f) x z := by
  match T, hc with
  | .var, _ =>
    exact graphRel_comp hf hg
  | .app F T, hc =>
    simp only [TypeExpr.hasRelInterpComp] at hc
    exact TypeExpr.relInterp_comp_of_isArrowFree
      (.app F T) hc hf hg
  | .arrow T₁ T₂, hc =>
    simp only [TypeExpr.hasRelInterpComp,
      Bool.and_eq_true] at hc
    obtain ⟨haf₁, hc₂⟩ := hc
    intro a₀ a₂ hrel₁₂
    obtain ⟨a₁, hr₁, hr₂⟩ :=
      T₁.relInterp_decomp_of_isArrowFree
        haf₁ hrel₁₂
    exact T₂.relInterp_comp_of_hasComp hc₂
      (hf a₀ a₁ hr₁) (hg a₁ a₂ hr₂)

/-- The dialgebra type `F(X) → G(X)` has
composable `relInterp`. -/
theorem dialgebraTypeExpr_hasComp
    (F G : Type ⥤ Type) :
    (dialgebraTypeExpr F G).hasRelInterpComp
      = true := by
  simp [dialgebraTypeExpr,
    TypeExpr.hasRelInterpComp,
    TypeExpr.isArrowFree]

/-- The hom type `X → X` has composable
`relInterp`. -/
theorem homTypeExpr_hasComp :
    homTypeExpr.hasRelInterpComp = true := by
  simp [TypeExpr.hasRelInterpComp,
    TypeExpr.isArrowFree]

/-- The dinatural type `(X → X) → (X → X)` does
NOT have composable `relInterp`: the domain
`X → X` is not arrow-free. -/
theorem dinaturalTypeExpr_not_hasComp :
    dinaturalTypeExpr.hasRelInterpComp
      = false := by
  change (TypeExpr.isArrowFree
    (TypeExpr.arrow
      (TypeExpr.leaf (𝟭 Type))
      (TypeExpr.leaf (𝟭 Type))) &&
    _) = false
  rfl

/-- The algebra type `(F(X) → X) → X` does NOT
have composable `relInterp`: the domain
`F(X) → X` is not arrow-free. -/
theorem algebraTypeExpr_not_hasComp
    (F : Type ⥤ Type) :
    (algebraTypeExpr F).hasRelInterpComp
      = false := by
  change (TypeExpr.isArrowFree
    (TypeExpr.arrow
      (TypeExpr.leaf F)
      (TypeExpr.leaf (𝟭 Type))) &&
    _) = false
  rfl

/-- The divergence type `((X → X) → X) → X`
does NOT have composable `relInterp`: the domain
`(X → X) → X` is not arrow-free. -/
theorem divTypeExpr_not_hasComp :
    divTypeExpr.hasRelInterpComp = false := by
  change (TypeExpr.isArrowFree
    (TypeExpr.arrow _ _) && _) = false
  rfl

section DecompCounterexample

/-- `relInterp_decomp` fails for the hom type
expression `X → X` (`homTypeExpr`).

Counterexample: `I₀ = Unit`, `I₁ = Bool`,
`I₂ = Fin 3`.
- `f : Unit → Bool` maps `() ↦ false`
- `g : Bool → Fin 3` maps `false ↦ 0, true ↦ 1`
- `g ∘ f = fun () ↦ 0`
- `h₀ = id : Unit → Unit`
- `h₂ : Fin 3 → Fin 3` maps `0 ↦ 0` and sends
  `1, 2 ↦ 2`

The composed condition
`arrowRel (graphRel (g ∘ f)) (graphRel (g ∘ f))`
holds for `(h₀, h₂)`, since
`(g ∘ f)(h₀ ()) = 0 = h₂ ((g ∘ f) ()) = h₂ 0`.

But no intermediate `h₁ : Bool → Bool` can satisfy
both `arrowRel (graphRel f) (graphRel f) h₀ h₁`
and `arrowRel (graphRel g) (graphRel g) h₁ h₂`:
the first forces `h₁ false = false`; the second
requires `g (h₁ true) = h₂ (g true) = h₂ 1 = 2`,
but `Im(g) = {0, 1}`, so no such `h₁ true` exists.
-/
theorem relInterp_decomp_homTypeExpr_fails :
    ∃ (I₀ I₁ I₂ : Type)
      (f : I₀ → I₁) (g : I₁ → I₂)
      (x : I₀ → I₀) (z : I₂ → I₂),
      homTypeExpr.relInterp (g ∘ f) x z ∧
      ¬ ∃ (y : I₁ → I₁),
        homTypeExpr.relInterp f x y ∧
        homTypeExpr.relInterp g y z := by
  let f : Unit → Bool := fun _ => false
  let g : Bool → Fin 3 :=
    fun b => if b then 1 else 0
  let h₂ : Fin 3 → Fin 3 :=
    fun n => if n = 0 then 0 else 2
  refine ⟨Unit, Bool, Fin 3, f, g, id, h₂,
    ?_, ?_⟩
  · -- homTypeExpr.relInterp (g ∘ f) id h₂
    -- i.e., arrowRel (graphRel (g ∘ f))
    --   (graphRel (g ∘ f)) id h₂
    change arrowRel (graphRel (g ∘ f))
      (graphRel (g ∘ f)) id h₂
    intro a₀ a₂ ha
    simp only [graphRel, Function.comp_apply,
      id_eq] at *
    simp only [f, g] at *
    subst ha
    rfl
  · intro ⟨h₁, hf, hg⟩
    change arrowRel (graphRel f) (graphRel f)
      id h₁ at hf
    change arrowRel (graphRel g) (graphRel g)
      h₁ h₂ at hg
    have hff : h₁ false = false := by
      have := hf () false (show graphRel f
        (id ()) false from rfl)
      simp only [graphRel, id_eq] at this
      exact this.symm
    have hgt := hg true (g true)
      (show graphRel g true (g true) from rfl)
    simp only [graphRel, g, h₂] at hgt
    revert hgt
    cases h₁ true <;> simp

end DecompCounterexample

end GebLean
