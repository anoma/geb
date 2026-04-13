import GebLean.LawvereER
import Mathlib.CategoryTheory.Category.Basic

/-!
# Finite-Limit Category of Decidable ER-Subobjects

Defines `LawvereERLexCat`, a category whose objects are
pairs of an arity and a Boolean-valued elementary
recursive predicate, and whose morphisms are equivalence
classes of `ERMorN` tuples respecting membership,
identified when they agree on every context satisfying
the source predicate.

This file covers the category skeleton only.  Finite
products, equalizers, and the full-and-faithful
embedding `LawvereERCat -> LawvereERLexCat` live in
subsequent modules.
-/

namespace GebLean

open CategoryTheory

/-- A Boolean-valued elementary recursive predicate:
an `ERMor1` term whose standard interpretation always
lies in `{0, 1}`.  Convention: `1 = true`, `0 = false`. -/
structure ERBoolPred (n : ℕ) where
  /-- The underlying predicate term. -/
  pred : ERMor1 n
  /-- Proof that the predicate is Boolean-valued. -/
  bool : ∀ ctx : Fin n → ℕ, pred.interp ctx ≤ 1

/-- Object of `LawvereERLexCat`: an arity together with
a Boolean-valued predicate cutting out a decidable
subobject of `Fin arity -> ℕ`. -/
structure LexObj where
  /-- The arity (number of free variables). -/
  arity : ℕ
  /-- The Boolean predicate. -/
  pred : ERBoolPred arity

/-- Raw morphism in `LawvereERLexCat`: an `ERMorN`
tuple that respects membership, that is, maps inputs
satisfying the source predicate to outputs satisfying
the target predicate. -/
def ERLexMorN (src tgt : LexObj) : Type :=
  { f : ERMorN src.arity tgt.arity //
      ∀ ctx : Fin src.arity → ℕ,
        src.pred.pred.interp ctx = 1 →
        tgt.pred.pred.interp (f.interp ctx) = 1 }

/-- The setoid on `ERLexMorN src tgt`: two raw
morphisms are related when their interpretations agree
on every context satisfying the source predicate. -/
def erLexMorNSetoid (src tgt : LexObj) :
    Setoid (ERLexMorN src tgt) where
  r f g :=
    ∀ ctx : Fin src.arity → ℕ,
      src.pred.pred.interp ctx = 1 →
      f.val.interp ctx = g.val.interp ctx
  iseqv := {
    refl := fun _ _ _ => rfl
    symm := fun h ctx hctx => (h ctx hctx).symm
    trans := fun h1 h2 ctx hctx =>
      (h1 ctx hctx).trans (h2 ctx hctx)
  }

/-- Quotient morphism type for `LawvereERLexCat`:
equivalence classes of `ERLexMorN` tuples under
source-restricted extensional equality. -/
def ERLexMorNQuo (src tgt : LexObj) : Type :=
  Quotient (erLexMorNSetoid src tgt)

end GebLean
