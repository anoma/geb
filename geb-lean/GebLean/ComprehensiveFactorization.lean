import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Comprehensive factorization of a functor

Given a functor `F : C ⥤ D`, the comprehensive factorization
(Street-Walters 1973) factors `F` as `F = m ≫ e` where:

- `e` is a final functor
- `m` is a discrete fibration

The factorization goes through the category of elements of
the presheaf `K : Dᵒᵖ ⥤ Type` defined by
`K(d) = ConnectedComponents (StructuredArrow d F)`.

A dual factorization exists where `e'` is initial and `m'`
is a discrete opfibration, using the copresheaf
`K'(d) = ConnectedComponents (CostructuredArrow F d)`.
-/

namespace GebLean

open CategoryTheory

universe v₁ u₁ v₂ u₂

variable {E : Type u₁} [Category.{v₁} E]
  {B : Type u₂} [Category.{v₂} B]

section DiscreteFibration

/-- A functor `p : E ⥤ B` is a discrete fibration if for
every object `e : E` and morphism `f : b ⟶ p.obj e` in `B`,
there exists a unique lift: a pair `(e', g : e' ⟶ e)` in `E`
such that `p.obj e' = b` and `p.map g` equals `f` (up to the
transport `eqToHom`). -/
class IsDiscreteFibration (p : E ⥤ B) : Prop where
  unique_lift : ∀ (e : E) {b : B} (f : b ⟶ p.obj e),
    ∃! (g : (e' : E) × (e' ⟶ e)),
      ∃ (h : p.obj g.1 = b),
        p.map g.2 = eqToHom h ≫ f

/-- A functor `p : E ⥤ B` is a discrete opfibration if for
every object `e : E` and morphism `f : p.obj e ⟶ b` in `B`,
there exists a unique lift: a pair `(e', g : e ⟶ e')` in `E`
such that `p.obj e' = b` and `p.map g` equals
`f ≫ eqToHom h.symm`. -/
class IsDiscreteOpfibration (p : E ⥤ B) : Prop where
  unique_lift :
    ∀ (e : E) {b : B} (f : p.obj e ⟶ b),
      ∃! (g : (e' : E) × (e ⟶ e')),
        ∃ (h : p.obj g.1 = b),
          p.map g.2 = f ≫ eqToHom h.symm

end DiscreteFibration

section ElementsProperties

universe w

variable {C : Type u₂} [Category.{v₂} C]

/-- The forgetful functor from the (covariant) category of
elements of `F : C ⥤ Type w` is a discrete opfibration.
Given `⟨c, x⟩ : F.Elements` and `f : c ⟶ d`, the unique
lift is `⟨d, F.map f x⟩` with morphism `⟨f, rfl⟩`. -/
instance elements_π_isDiscreteOpfibration
    (F : C ⥤ Type w) :
    IsDiscreteOpfibration (CategoryOfElements.π F) where
  unique_lift := by
    intro ⟨c, x⟩ d f
    refine ⟨⟨⟨_, F.map f x⟩, ⟨f, rfl⟩⟩,
      ⟨rfl, by simp⟩, ?_⟩
    intro ⟨⟨d', y⟩, g⟩ ⟨h, hg⟩
    simp only [CategoryOfElements.π] at h hg
    subst h
    simp only [eqToHom_refl, Category.comp_id] at hg
    have hval : g.val = f := hg
    have hprop : F.map f x = y := by
      rw [← hval]; exact g.property
    subst hprop
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hval))

end ElementsProperties

section ComprehensiveFactorization

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

/-- The comprehensive copresheaf of a functor `F : C ⥤ D`.
At `d : D`, this is the set of connected components of the
comma category `CostructuredArrow F d` (the category of
objects of `C` equipped with a morphism to `d`).

Functoriality in `d` uses `CostructuredArrow.map`. -/
@[simps]
def comprehensiveCopresheaf (F : C ⥤ D) : D ⥤ Type _ where
  obj d := ConnectedComponents (CostructuredArrow F d)
  map f :=
    Functor.mapConnectedComponents (CostructuredArrow.map f)
  map_id d := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        CostructuredArrow.map_id]
  map_comp f g := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        CostructuredArrow.map_comp]

/-- The comprehensive presheaf of a functor `F : C ⥤ D`.
At `d : Dᵒᵖ`, this is the set of connected components of
the comma category `StructuredArrow d.unop F` (the category
of objects of `C` equipped with a morphism from `d`).

Functoriality in `d` uses `StructuredArrow.map`. -/
@[simps]
def comprehensivePresheaf (F : C ⥤ D) :
    Dᵒᵖ ⥤ Type _ where
  obj d :=
    ConnectedComponents (StructuredArrow d.unop F)
  map f :=
    Functor.mapConnectedComponents
      (StructuredArrow.map f.unop)
  map_id d := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        StructuredArrow.map_id]
  map_comp f g := by
    ext x
    exact Quotient.inductionOn x fun σ => by
      simp [Functor.mapConnectedComponents_mk,
        StructuredArrow.map_comp]

variable (F : C ⥤ D)

/-- The initial functor in the copresheaf comprehensive
factorization. Sends `c : C` to
`(F.obj c, [id_{F(c)}]) : (comprehensiveCopresheaf F).Elements`.

The connected component `[id_{F(c)}]` is the class of the
identity costructured arrow `CostructuredArrow.mk (𝟙 (F.obj c))`
in `CostructuredArrow F (F.obj c)`. -/
def comprehensiveE' :
    C ⥤ (comprehensiveCopresheaf F).Elements where
  obj c :=
    ⟨F.obj c,
      Quotient.mk _
        (CostructuredArrow.mk (𝟙 (F.obj c)))⟩
  map {c₁ c₂} f :=
    ⟨F.map f, by
      simp only [comprehensiveCopresheaf_map,
        Functor.mapConnectedComponents_mk,
        CostructuredArrow.map_mk, Category.id_comp]
      exact Quotient.sound
        (Zigzag.of_hom
          (CostructuredArrow.homMk f (by simp)))⟩
  map_id c := by
    ext
    change F.map (𝟙 c) = 𝟙 (F.obj c)
    exact F.map_id c
  map_comp f g := by
    ext
    change F.map (f ≫ g) = F.map f ≫ F.map g
    exact F.map_comp f g

end ComprehensiveFactorization

end GebLean
