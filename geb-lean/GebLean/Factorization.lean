import Mathlib.CategoryTheory.Category.Factorisation
import GebLean.Utilities.TwistedArrow

/-!
# Factorization categories

This module re-exports the factorization category from mathlib
(`CategoryTheory.Factorisation`) and provides additional
constructions.

Given a morphism `f : X ⟶ Y` in a category `C`, the factorization
category `Factorisation f` has:
- Objects: triples `(mid, ι : X ⟶ mid, π : mid ⟶ Y)` with
  `ι ≫ π = f`.
- Morphisms `d ⟶ e`: maps `h : d.mid ⟶ e.mid` satisfying
  `d.ι ≫ h = e.ι` and `h ≫ e.π = d.π`.

The category has an initial object `Factorisation.initial`
(with `mid := X`, `ι := 𝟙 X`, `π := f`) and a terminal object
`Factorisation.terminal` (with `mid := Y`, `ι := f`, `π := 𝟙 Y`).

The forgetful functor `Factorisation.forget : Factorisation f ⥤ C`
sends each factorization to its midpoint.

## Main definitions

- `factorisationMapObj`: Given a twisted arrow morphism `φ : x ⟶ y`,
  transforms a factorization of `twArr x` into a factorization of
  `twArr y` by pre-composing `ι` with `twDomArr φ` and
  post-composing `π` with `twCodArr φ`.

- `factorisationFunctor`: The `Cat`-valued functor
  `TwistedArrow C ⥤ Cat` sending each arrow `f` to `Factorisation f`
  and each twisted arrow morphism to the induced functor between
  factorization categories.

## References

- https://ncatlab.org/nlab/show/factorization+category
- `Mathlib.CategoryTheory.Category.Factorisation`
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Functoriality of factorization categories

A twisted arrow morphism `φ : x ⟶ y` in `TwistedArrow C` consists
of `twDomArr φ : twDom y ⟶ twDom x` and
`twCodArr φ : twCod x ⟶ twCod y` satisfying
`twDomArr φ ≫ twArr x ≫ twCodArr φ = twArr y`.

Given such `φ`, each factorization `(mid, ι, π)` of `twArr x`
induces a factorization `(mid, twDomArr φ ≫ ι, π ≫ twCodArr φ)`
of `twArr y`. The midpoint and morphisms between midpoints are
unchanged, yielding a functor
`Factorisation (twArr x) ⥤ Factorisation (twArr y)`.
-/

/-- The image of a factorization object under a twisted arrow
morphism. The midpoint is unchanged; `ι` is pre-composed with the
domain arrow and `π` is post-composed with the codomain arrow. -/
def factorisationMapObj
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    Factorisation (twArr y) where
  mid := d.mid
  ι := twDomArr φ ≫ d.ι
  π := d.π ≫ twCodArr φ
  ι_π := by
    rw [Category.assoc, ← Category.assoc d.ι,
      d.ι_π]
    exact twHomComm φ

/-- The image of a factorization morphism under a twisted arrow
morphism. The underlying map `h` between midpoints is unchanged. -/
def factorisationMapHom
    {x y : TwistedArrow C} (φ : x ⟶ y)
    {d e : Factorisation (twArr x)}
    (g : d ⟶ e) :
    factorisationMapObj φ d ⟶ factorisationMapObj φ e where
  h := g.h
  ι_h := by
    simp only [factorisationMapObj, Category.assoc]
    rw [g.ι_h]
  h_π := by
    simp only [factorisationMapObj, ← Category.assoc]
    rw [g.h_π]

/-- The functor between factorization categories induced by a
twisted arrow morphism. Preserves midpoints and the maps between
them; only the factorization data (`ι` and `π`) changes. -/
def factorisationMap
    {x y : TwistedArrow C} (φ : x ⟶ y) :
    Factorisation (twArr x) ⥤ Factorisation (twArr y) where
  obj := factorisationMapObj φ
  map := factorisationMapHom φ
  map_id _ := Factorisation.Hom.ext rfl
  map_comp _ _ := Factorisation.Hom.ext rfl

@[simp]
private theorem factorisationMapObj_mid
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    (factorisationMapObj φ d).mid = d.mid := rfl

@[simp]
private theorem factorisationMapObj_ι
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    (factorisationMapObj φ d).ι = twDomArr φ ≫ d.ι := rfl

@[simp]
private theorem factorisationMapObj_π
    {x y : TwistedArrow C} (φ : x ⟶ y)
    (d : Factorisation (twArr x)) :
    (factorisationMapObj φ d).π = d.π ≫ twCodArr φ := rfl

@[simp]
private theorem factorisation_comp_h
    {X Y : C} {f : X ⟶ Y}
    {a b c : Factorisation f}
    (g₁ : a ⟶ b) (g₂ : b ⟶ c) :
    (g₁ ≫ g₂).h = g₁.h ≫ g₂.h := rfl

@[simp]
private theorem factorisation_eqToHom_h
    {X Y : C} {f : X ⟶ Y}
    {d e : Factorisation f}
    (p : d = e) :
    (eqToHom p).h =
    eqToHom (congrArg Factorisation.mid p) := by
  subst p; rfl

/-- The `Cat`-valued functor sending each arrow `f : a ⟶ b` in `C`
(viewed as an object of `TwistedArrow C`) to its factorization
category `Factorisation f`, and each twisted arrow morphism to the
induced functor between factorization categories. -/
def factorisationFunctor (C : Type u) [Category.{v} C] :
    TwistedArrow C ⥤ Cat.{max u v, max u v} where
  obj tw := Cat.of (Factorisation (twArr tw))
  map φ := (factorisationMap φ).toCatHom
  map_id tw := by
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor,
      Cat.Hom.id_toFunctor]
    refine CategoryTheory.Functor.ext
      (fun d ↦ ?_) (fun d e f ↦ ?_)
    · cases d
      simp only [factorisationMap, factorisationMapObj,
        Functor.id_obj, Factorisation.mk.injEq,
        heq_eq_eq, true_and]
      exact ⟨twDomArr_id tw ▸ Category.id_comp _,
        twCodArr_id tw ▸ Category.comp_id _⟩
    · apply Factorisation.Hom.ext
      simp only [factorisationMap,
        factorisationMapHom,
        factorisation_comp_h,
        factorisation_eqToHom_h,
        Functor.id_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
  map_comp φ ψ := by
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor,
      Cat.Hom.comp_toFunctor]
    refine CategoryTheory.Functor.ext
      (fun d ↦ ?_) (fun d e f ↦ ?_)
    · cases d
      simp only [factorisationMap, factorisationMapObj,
        Functor.comp_obj, Factorisation.mk.injEq,
        heq_eq_eq, true_and]
      exact ⟨by rw [twDomArr_comp, Category.assoc],
        by rw [twCodArr_comp, ← Category.assoc]⟩
    · apply Factorisation.Hom.ext
      simp only [factorisationMap,
        factorisationMapHom,
        factorisation_comp_h,
        factorisation_eqToHom_h,
        Functor.comp_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]

end GebLean
