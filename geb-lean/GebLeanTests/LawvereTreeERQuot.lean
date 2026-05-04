import GebLean.LawvereTreeERQuot

/-!
# Tests for LawvereTreeERQuot

Category and HasChosenFiniteProducts sanity tests.
-/

open GebLean CategoryTheory

-- Category instance type-checks.
example : Category LawvereTreeERCat :=
  inferInstance

-- HasChosenFiniteProducts type-checks.
example : HasChosenFiniteProducts
    LawvereTreeERCat :=
  inferInstance

-- Category identity composed with itself equals
-- identity.
example : (𝟙 (2 : LawvereTreeERCat)) ≫
    (𝟙 (2 : LawvereTreeERCat)) =
    𝟙 (2 : LawvereTreeERCat) := by
  rw [Category.id_comp]

-- Terminal uniqueness: any morphism to 0 equals
-- the terminal morphism.
example (f : (3 : LawvereTreeERCat) ⟶
    (0 : LawvereTreeERCat)) :
    f = TreeERMorNQuo.terminal 3 :=
  TreeERMorNQuo.terminal_uniq f
