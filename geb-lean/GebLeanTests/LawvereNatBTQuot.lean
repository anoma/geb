import GebLean.LawvereNatBTQuot

/-!
# Tests for LawvereNatBTQuot

Sanity tests verifying the quotient category instance and
chosen finite products structure.
-/

open GebLean
open CategoryTheory

-- Category instance type-checks.
example : Category LawvereNatBTCat := inferInstance

-- HasChosenFiniteProducts type-checks.
example : HasChosenFiniteProducts LawvereNatBTCat :=
  inferInstance

-- Identity quotient morphism type-checks.
example (nm : ℕ × ℕ) : NatBTMorNQuo nm nm :=
  NatBTMorNQuo.id nm

-- Category identity composed with itself equals identity.
example (nm : LawvereNatBTCat) :
    (𝟙 nm) ≫ (𝟙 nm) = 𝟙 nm := by
  rw [Category.id_comp]

-- Terminal uniqueness: any morphism into `(0, 0)` equals the
-- terminal morphism.
example (nm : LawvereNatBTCat)
    (f : nm ⟶ ((0, 0) : LawvereNatBTCat)) :
    f = NatBTMorNQuo.terminal nm :=
  NatBTMorNQuo.terminal_uniq f
