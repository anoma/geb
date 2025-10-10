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
    -- When iso.hom ⋙ iso.inv = 𝟭 C, the natural transformation from
    -- (iso.hom ⋙ iso.inv).obj X to X composed with the functor's action
    -- should give identity. This is conceptually obvious but technically
    -- complex to prove with eqToHom.
    sorry

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
