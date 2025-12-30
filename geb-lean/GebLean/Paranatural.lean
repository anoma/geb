import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites

/-!
# Category of diagonal elements and paranatural transformations

Given an endoprofunctor `F : Cᵒᵖ ⥤ C ⥤ Type`, the category of diagonal
elements has as objects pairs `(I, g)` where `I : C` and `g : F.obj (op I) I`,
and as morphisms from `(I₀, g₀)` to `(I₁, g₁)` those morphisms `f : I₀ ⟶ I₁`
satisfying `(F.obj (op I₀)).map f g₀ = (F.map (op f)).app I₁ g₁`.

A paranatural transformation between two endoprofunctors `F` and `G` is
a family of functions `α_I : F.obj (op I) I → G.obj (op I) I` that preserves
the diagonal morphism condition: if `(F.obj (op I₀)).map f d₀ = (F.map (op f)).app I₁ d₁`,
then `(G.obj (op I₀)).map f (α I₀ d₀) = (G.map (op f)).app I₁ (α I₁ d₁)`.

## References

* Definition 2.7 in Neumann, "Paranatural Category Theory"
* https://ncatlab.org/nlab/show/algebra+for+a+profunctor

-/

namespace GebLean

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

section DiagonalElements

universe w

variable (F : Cᵒᵖ ⥤ C ⥤ Type w)

/-- The type of diagonal elements for an endoprofunctor `F : Cᵒᵖ ⥤ C ⥤ Type w`.
An object consists of a base object `I : C` and a diagonal element
`elem : (F.obj (op I)).obj I`. -/
@[ext]
structure DiagElem where
  /-- The base object in `C` -/
  base : C
  /-- The diagonal element in `(F.obj (op base)).obj base` -/
  elem : (F.obj (Opposite.op base)).obj base

/-- The diagonal compatibility condition for an endoprofunctor. Given a morphism
`f : I₀ ⟶ I₁` and diagonal elements `d₀ ∈ F(I₀, I₀)` and `d₁ ∈ F(I₁, I₁)`,
this asserts that the covariant action of `f` on `d₀` equals the contravariant
action of `f` on `d₁`. -/
@[simp]
def DiagCompat (I₀ I₁ : C) (f : I₀ ⟶ I₁)
    (d₀ : (F.obj (Opposite.op I₀)).obj I₀)
    (d₁ : (F.obj (Opposite.op I₁)).obj I₁) : Prop :=
  (F.obj (Opposite.op I₀)).map f d₀ = (F.map f.op).app I₁ d₁

/-- A morphism in the category of diagonal elements from `(I₀, g₀)` to `(I₁, g₁)`
is a morphism `f : I₀ ⟶ I₁` in `C` such that the covariant action of `f` on `g₀`
equals the contravariant action of `f` on `g₁`. -/
@[ext]
structure DiagElem.Hom (x y : DiagElem F) where
  /-- The underlying morphism in `C` -/
  base : x.base ⟶ y.base
  /-- The compatibility condition: covariant action on source element equals
  contravariant action on target element -/
  compat : DiagCompat F x.base y.base base x.elem y.elem

namespace DiagElem

/-- The identity morphism on a diagonal element. -/
@[simp]
def Hom.id (x : DiagElem F) : Hom F x x where
  base := 𝟙 x.base
  compat := by simp

/-- Composition of morphisms of diagonal elements. -/
@[simp]
def Hom.comp {x y z : DiagElem F} (f : Hom F x y) (g : Hom F y z) :
    Hom F x z where
  base := f.base ≫ g.base
  compat := by
    simp only [DiagCompat, Functor.map_comp]
    change (F.obj (Opposite.op x.base)).map g.base
        ((F.obj (Opposite.op x.base)).map f.base x.elem) =
      (F.map (f.base ≫ g.base).op).app z.base z.elem
    rw [f.compat]
    have nat := congrFun ((F.map f.base.op).naturality g.base) y.elem
    simp only [types_comp_apply] at nat
    rw [← nat, g.compat]
    rw [op_comp]
    simp only [Functor.map_comp, NatTrans.comp_app, types_comp_apply]

instance : Category (DiagElem F) where
  Hom := Hom F
  id := Hom.id F
  comp := Hom.comp F
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

variable {F}
variable {G : Cᵒᵖ ⥤ C ⥤ Type w}

/-- A natural transformation `η : F ⟶ G` induces a functor `DiagElem F ⥤ DiagElem G`
by applying `η` to diagonal elements. -/
@[simps]
def map (η : F ⟶ G) : DiagElem F ⥤ DiagElem G where
  obj x := ⟨x.base, (η.app (Opposite.op x.base)).app x.base x.elem⟩
  map {x y} f := ⟨f.base, by
    simp only [DiagCompat]
    have nat_cov := congrFun ((η.app (Opposite.op x.base)).naturality f.base) x.elem
    simp only [types_comp_apply] at nat_cov
    rw [← nat_cov, f.compat]
    have nat_con := congrFun (congrArg (NatTrans.app · y.base) (η.naturality f.base.op)) y.elem
    simp only [types_comp_apply, NatTrans.comp_app] at nat_con
    exact nat_con⟩
  map_id x := Hom.ext rfl
  map_comp f g := Hom.ext rfl

/-- `DiagElem.map` sends the identity natural transformation to the identity functor. -/
@[simp]
theorem map_id_nat : map (𝟙 F) = 𝟭 (DiagElem F) := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · apply DiagElem.ext <;> rfl
  · simp only [Functor.id_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    apply Hom.ext; rfl

variable {H : Cᵒᵖ ⥤ C ⥤ Type w}

/-- `DiagElem.map` preserves composition of natural transformations. -/
@[simp]
theorem map_comp_nat (η : F ⟶ G) (θ : G ⟶ H) :
    map (η ≫ θ) = map η ⋙ map θ := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · apply DiagElem.ext <;> rfl
  · simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    apply Hom.ext; rfl

end DiagElem

end DiagonalElements

section Paranatural

universe w

variable (F G : Cᵒᵖ ⥤ C ⥤ Type w)

/-- The paranaturality condition for a family of functions between diagonal
elements of two endoprofunctors. A family `α` is paranatural if whenever
the covariant and contravariant actions of a morphism agree on elements of `F`,
then the same morphism's actions agree on the images under `α` in `G`. -/
def IsParanatural
    (α : (I : C) → (F.obj (Opposite.op I)).obj I → (G.obj (Opposite.op I)).obj I) :
    Prop :=
  ∀ (I₀ I₁ : C) (f : I₀ ⟶ I₁) (d₀ : (F.obj (Opposite.op I₀)).obj I₀)
    (d₁ : (F.obj (Opposite.op I₁)).obj I₁),
    DiagCompat F I₀ I₁ f d₀ d₁ → DiagCompat G I₀ I₁ f (α I₀ d₀) (α I₁ d₁)

/-- A paranatural transformation between two endoprofunctors `F` and `G` on `C`.
A family of functions on diagonal elements that preserves the compatibility
condition for morphisms between diagonal elements. -/
@[ext]
structure Paranat where
  /-- The component of the paranatural transformation at object `I` -/
  app : (I : C) → (F.obj (Opposite.op I)).obj I → (G.obj (Opposite.op I)).obj I
  /-- The paranaturality condition -/
  paranatural : IsParanatural F G app

namespace Paranat

variable {F G}

/-- The identity paranatural transformation on an endoprofunctor. -/
@[simp]
def id : Paranat F F where
  app _ d := d
  paranatural _ _ _ _ _ h := h

variable {H : Cᵒᵖ ⥤ C ⥤ Type w}

/-- Composition of paranatural transformations. -/
@[simp]
def comp (α : Paranat F G) (β : Paranat G H) : Paranat F H where
  app I d := β.app I (α.app I d)
  paranatural I₀ I₁ f d₀ d₁ hF := β.paranatural I₀ I₁ f _ _ (α.paranatural I₀ I₁ f d₀ d₁ hF)

end Paranat

/-- The type of endoprofunctors on a category `C`, viewed as objects of a
category where morphisms are paranatural transformations. -/
def EndoProf : Type max u v (w + 1) := Cᵒᵖ ⥤ C ⥤ Type w

instance : Category (EndoProf (C := C)) where
  Hom F G := Paranat F G
  id F := Paranat.id
  comp := Paranat.comp
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

end Paranatural

end GebLean
