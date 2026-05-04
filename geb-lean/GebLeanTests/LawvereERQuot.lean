import GebLean.LawvereERQuot
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereERQuot

Sanity tests verifying quotient identification and
category-law discharge.
-/

open GebLean
open CategoryTheory

-- Two syntactically distinct `ERMorN 2 1` tuples
-- that both compute `ctx 0 - ctx 1`.

private def subDirect : ERMorN 2 1 :=
  fun _ => ERMor1.sub

private def subViaComp : ERMorN 2 1 :=
  fun _ => ERMor1.comp ERMor1.sub
    (fun i => ERMor1.proj i)

example : (Quotient.mk (erMorNSetoid 2 1)
    subDirect : ERMorNQuo 2 1) =
    Quotient.mk (erMorNSetoid 2 1) subViaComp :=
  Quotient.sound (s := erMorNSetoid 2 1)
    (fun _ => rfl)

-- Category identity composed with itself equals
-- identity.

example : (𝟙 (2 : LawvereERCat)) ≫
    (𝟙 (2 : LawvereERCat)) =
    𝟙 (2 : LawvereERCat) := by
  rw [Category.id_comp]

-- Terminal uniqueness: any morphism to 0 equals
-- the terminal morphism.
example (f : (3 : LawvereERCat) ⟶
    (0 : LawvereERCat)) :
    f = ERMorNQuo.terminal 3 :=
  ERMorNQuo.terminal_uniq f

-- HasChosenFiniteProducts is available.
example : HasChosenFiniteProducts
    LawvereERCat := inferInstance
