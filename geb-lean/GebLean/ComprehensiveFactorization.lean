import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import GebLean.Utilities.Elements

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

/-- The forgetful functor from the contravariant category
of elements of a presheaf `F : Cᵒᵖ ⥤ Type w` is a
discrete fibration. Given `op ⟨op c, x⟩ : F.ElementsPre`
and `f : b ⟶ c` in `C`, the unique lift is
`op ⟨op b, F.map f.op x⟩` with underlying morphism
`(⟨f.op, rfl⟩).op`. -/
private def elementsPre_lift
    (F : Cᵒᵖ ⥤ Type w)
    (e : F.ElementsPre) {b : C}
    (f : b ⟶ (elementsPre_π F).obj e) :
    (e' : F.ElementsPre) × (e' ⟶ e) :=
  ⟨Opposite.op
      ⟨Opposite.op b, F.map f.op e.unop.snd⟩,
    Quiver.Hom.op
      (⟨f.op, rfl⟩ :
        e.unop ⟶ ⟨Opposite.op b,
          F.map f.op e.unop.snd⟩)⟩

instance elementsPre_π_isDiscreteFibration
    (F : Cᵒᵖ ⥤ Type w) :
    IsDiscreteFibration (elementsPre_π F) where
  unique_lift := by
    intro e b f
    refine ⟨elementsPre_lift F e f,
      ⟨rfl, by simp only [eqToHom_refl,
        Category.id_comp]; rfl⟩, ?_⟩
    rintro ⟨⟨⟨c_op, x⟩⟩, g⟩ ⟨h, hg⟩
    simp only [elementsPre_π_obj] at h
    subst h
    simp only [eqToHom_refl, Category.id_comp,
      elementsPre_π_map] at hg
    have hval : g.unop.val = f.op := by
      rw [← Quiver.Hom.op_unop g.unop.val, hg]
    have hprop : F.map f.op e.unop.snd = x := by
      rw [← hval]; exact g.unop.property
    subst hprop
    exact Sigma.ext rfl
      (heq_of_eq (Quiver.Hom.unop_inj
        (Subtype.ext hval)))

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

/-- The discrete opfibration in the copresheaf comprehensive
factorization. This is the forgetful functor from the
category of elements of `comprehensiveCopresheaf F`,
projecting `(d, [σ])` to `d`. -/
abbrev comprehensiveM' :
    (comprehensiveCopresheaf F).Elements ⥤ D :=
  CategoryOfElements.π (comprehensiveCopresheaf F)

/-- The copresheaf discrete opfibration: the forgetful
functor from elements of `comprehensiveCopresheaf F` is a
discrete opfibration. -/
instance comprehensiveM'_isDiscreteOpfibration :
    IsDiscreteOpfibration (comprehensiveM' F) :=
  elements_π_isDiscreteOpfibration _

/-- The copresheaf comprehensive factorization commutes:
`comprehensiveE' F ⋙ comprehensiveM' F = F`. -/
theorem comprehensiveFactorization'_comm :
    comprehensiveE' F ⋙ comprehensiveM' F = F := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro c; rfl
  case h_map =>
    intro c₁ c₂ f
    simp [comprehensiveE', comprehensiveM',
      eqToHom_refl]

end ComprehensiveFactorization

section ComprehensiveFactorizationPre

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

variable (F : C ⥤ D)

/-- The final functor in the presheaf comprehensive
factorization. Sends `c : C` to `op (op (F.obj c),
[id_{F(c)}])` in `(comprehensivePresheaf F).ElementsPre`.

The connected component `[id_{F(c)}]` is the class of the
identity structured arrow
`StructuredArrow.mk (𝟙 (F.obj c))`
in `StructuredArrow (F.obj c) F`. -/
def comprehensiveE :
    C ⥤ (comprehensivePresheaf F).ElementsPre where
  obj c :=
    Opposite.op
      ⟨Opposite.op (F.obj c),
        Quotient.mk _
          (StructuredArrow.mk (𝟙 (F.obj c)))⟩
  map {c₁ c₂} f :=
    Quiver.Hom.op
      ⟨(F.map f).op, by
        simp only [comprehensivePresheaf_map,
          Functor.mapConnectedComponents_mk,
          StructuredArrow.map_mk, Category.comp_id]
        exact Quotient.sound
          (Zigzag.of_inv
            (StructuredArrow.homMk f (by simp)))⟩
  map_id c := by
    apply congrArg Quiver.Hom.op
    ext
    simp only [F.map_id, op_id]
    rfl
  map_comp f g := by
    apply congrArg Quiver.Hom.op
    ext
    simp only [F.map_comp, op_comp]
    rfl

/-- The discrete fibration in the presheaf comprehensive
factorization. This is the forgetful functor from the
contravariant category of elements of
`comprehensivePresheaf F`, projecting
`op (op d, [σ])` to `d`. -/
abbrev comprehensiveM :
    (comprehensivePresheaf F).ElementsPre ⥤ D :=
  elementsPre_π (comprehensivePresheaf F)

/-- The presheaf discrete fibration: the forgetful functor
from elements of `comprehensivePresheaf F` is a discrete
fibration. -/
instance comprehensiveM_isDiscreteFibration :
    IsDiscreteFibration (comprehensiveM F) :=
  elementsPre_π_isDiscreteFibration _

/-- The presheaf comprehensive factorization commutes:
`comprehensiveE F ⋙ comprehensiveM F = F`. -/
theorem comprehensiveFactorization_comm :
    comprehensiveE F ⋙ comprehensiveM F = F := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro c; rfl
  case h_map =>
    intro c₁ c₂ f
    simp [comprehensiveE, comprehensiveM,
      eqToHom_refl]

end ComprehensiveFactorizationPre

end GebLean
