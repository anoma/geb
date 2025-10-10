import Mathlib.Logic.Equiv.Defs
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

/-!
# Utilities

General-purpose utility functions and lemmas that may be useful across
different modules.
-/

namespace CategoryTheory

universe u v

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

/-- An isomorphism of categories induces an equivalence of categories.

    Note: This uses `eqToIso` to convert functor equalities into natural
    isomorphisms. The coherence proof is admitted with `sorry` as it requires
    complex reasoning about how `eqToHom` interacts with functor composition.
    In practice, this is always true when functors compose to identity. -/
def Equivalence.ofIso (iso : C ≅Cat D) : C ≌ D where
  functor := iso.hom
  inverse := iso.inv
  unitIso := eqToIso iso.hom_inv_id.symm
  counitIso := eqToIso iso.inv_hom_id
  functor_unitIso_comp := by
    intro X
    -- Unfold eqToIso to eqToHom at natural transformation level
    rw [eqToIso.hom, eqToIso.hom]

    -- Extract object equalities from functor equalities
    -- iso.hom_inv_id : iso.hom ≫ iso.inv = 𝟙 (Cat.of C)
    -- This means as functors: iso.hom ≫ iso.inv = identity functor on C
    have h1 : (iso.hom ≫ iso.inv).obj X = X := by
      rw [iso.hom_inv_id]
      rfl

    have h2 : (iso.inv ≫ iso.hom).obj (iso.hom.obj X) = iso.hom.obj X := by
      rw [iso.inv_hom_id]
      rfl

    -- The eqToHom components are based on these object equalities
    -- Goal: iso.hom.map (eqToHom h1.symm) ≫ eqToHom h2 = 𝟙 (iso.hom.obj X)

    -- Expand composition on objects
    rw [Cat.comp_obj] at h1 h2

    -- Now h1 : iso.inv.obj (iso.hom.obj X) = X
    -- and h2 : iso.hom.obj (iso.inv.obj (iso.hom.obj X)) = iso.hom.obj X

    -- Convert natural transformation components to eqToHom of object equalities
    rw [eqToHom_app, eqToHom_app]

    -- Now the goal is about morphisms eqToHom in the target category
    -- iso.hom.map (eqToHom ...) ≫ eqToHom ... = 𝟙

    -- Use functoriality: F.map (eqToHom p) = eqToHom (congrArg F.obj p)
    rw [eqToHom_map]

    -- Now both are eqToHom, so we can use eqToHom_trans
    rw [eqToHom_trans]

    -- The composite equality should be refl, giving identity
    simp [eqToHom_refl]

end CategoryTheory

/-- A subtype of sigma where both indices are constrained to equal specific
    values is equivalent to the base type at those indices.

    This is useful when extracting dependent types from functors, where the
    functor encoding uses sigma types with equality constraints. -/
def sigmaTrivialSubtype {α : Type*} {β : α → α → Type*} (a b : α) :
    {m : Σ (a' b' : α), β a' b' // m.1 = a ∧ m.2.1 = b} ≃ β a b where
  toFun m := by
    obtain ⟨⟨a', b', x⟩, ha, hb⟩ := m
    subst ha hb
    exact x
  invFun x := ⟨⟨a, b, x⟩, rfl, rfl⟩
  left_inv := by
    intro ⟨⟨a', b', x⟩, ha, hb⟩
    subst ha hb
    rfl
  right_inv := by intro x; rfl
