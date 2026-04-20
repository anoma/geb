import GebLean.LawvereGodelTQuot
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation Functor for LawvereGodelTCat

Defines a faithful functor from `LawvereGodelTCat` (the
quotient Lawvere theory of restricted Gödel-T) into `Type`,
sending arity `n` to `Fin n → ℕ` and each morphism class to
its standard interpretation.
-/

namespace GebLean

open CategoryTheory

/-- Lift `GodelTMorN.interp` to the quotient.  Well-defined
because the setoid relation is extensional equality of
interpretations. -/
def GodelTMorNQuo.interp {n m : ℕ} (f : GodelTMorNQuo n m) :
    (Fin n → ℕ) → (Fin m → ℕ) :=
  Quotient.lift
    (s := godelTMorNSetoid n m)
    GodelTMorN.interp
    (fun _ _ h => funext h)
    f

@[simp] theorem GodelTMorNQuo.interp_mk {n m : ℕ} (f : GodelTMorN n m) :
    GodelTMorNQuo.interp (Quotient.mk (godelTMorNSetoid n m) f) =
      f.interp := rfl

@[simp] theorem GodelTMorNQuo.interp_id (n : ℕ) (ctx : Fin n → ℕ) :
    (GodelTMorNQuo.id n).interp ctx = ctx := by
  unfold GodelTMorNQuo.id
  simp [GodelTMorNQuo.interp_mk, GodelTMorN.interp_id]

@[simp] theorem GodelTMorNQuo.interp_comp {n m k : ℕ}
    (f : GodelTMorNQuo n m) (g : GodelTMorNQuo m k)
    (ctx : Fin n → ℕ) :
    (GodelTMorNQuo.comp f g).interp ctx =
      g.interp (f.interp ctx) := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  change (GodelTMorN.comp f_raw g_raw).interp ctx =
    g_raw.interp (f_raw.interp ctx)
  simp [GodelTMorN.interp_comp]

/-- The interpretation functor from `LawvereGodelTCat` into
`Type`.  Sends arity `n` to `Fin n → ℕ` and each morphism class
to its standard interpretation. -/
def godelTInterpFunctor : LawvereGodelTCat ⥤ Type where
  obj n := Fin n → ℕ
  map f := f.interp
  map_id n := by
    funext ctx
    exact GodelTMorNQuo.interp_id n ctx
  map_comp f g := by
    funext ctx
    exact GodelTMorNQuo.interp_comp f g ctx

/-- The interpretation functor is faithful: distinct morphism
classes produce distinct functions.  Immediate from the
extensional quotient. -/
instance : godelTInterpFunctor.Faithful where
  map_injective {n m} {f g} h := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw heq
    exact Quotient.sound
      (s := godelTMorNSetoid n m)
      (fun ctx => congrFun heq ctx)

end GebLean
