import GebLean.LawvereERQuot
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation Functor for LawvereERCat

Defines a faithful functor from `LawvereERCat` (the
Lawvere theory of elementary recursive functions)
into `Type`, sending arity `n` to `Fin n -> Nat`
and each morphism class to its standard
interpretation.
-/

namespace GebLean

open CategoryTheory

/-- Lift `ERMorN.interp` to the quotient.
Well-defined because the setoid relation is
extensional equality of interpretations. -/
def ERMorNQuo.interp {n m : ℕ}
    (f : ERMorNQuo n m) :
    (Fin n → ℕ) → (Fin m → ℕ) :=
  Quotient.lift
    (s := erMorNSetoid n m)
    ERMorN.interp
    (fun _ _ h => funext h)
    f

/-- `ERMorNQuo.interp` on a concrete
representative reduces to `ERMorN.interp`. -/
@[simp] theorem ERMorNQuo.interp_mk
    {n m : ℕ} (f : ERMorN n m) :
    ERMorNQuo.interp
      (Quotient.mk (erMorNSetoid n m) f) =
      f.interp :=
  rfl

/-- Interpretation of the quotient identity. -/
@[simp] theorem ERMorNQuo.interp_id
    (n : ℕ) (ctx : Fin n → ℕ) :
    (ERMorNQuo.id n).interp ctx = ctx := by
  unfold ERMorNQuo.id
  simp [ERMorNQuo.interp_mk, ERMorN.interp_id]

/-- Interpretation of quotient composition. -/
@[simp] theorem ERMorNQuo.interp_comp
    {n m k : ℕ} (f : ERMorNQuo n m)
    (g : ERMorNQuo m k)
    (ctx : Fin n → ℕ) :
    (ERMorNQuo.comp f g).interp ctx =
      g.interp (f.interp ctx) := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  rfl

/-- The interpretation functor from
`LawvereERCat` into `Type`.  Sends arity `n` to
`Fin n -> Nat` and each morphism class to its
standard interpretation. -/
def erInterpFunctor :
    LawvereERCat ⥤ Type where
  obj n := Fin n → ℕ
  map f := f.interp
  map_id n := by
    funext ctx
    exact ERMorNQuo.interp_id n ctx
  map_comp f g := by
    funext ctx
    exact ERMorNQuo.interp_comp f g ctx

/-- The interpretation functor is faithful:
distinct morphism classes produce distinct
functions.  This is immediate from the
extensional quotient: the setoid relation is
exactly the kernel of the interpretation. -/
instance : erInterpFunctor.Faithful where
  map_injective {n m} {f g} h := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw heq
    exact Quotient.sound
      (s := erMorNSetoid n m)
      (fun ctx => congrFun heq ctx)

end GebLean
