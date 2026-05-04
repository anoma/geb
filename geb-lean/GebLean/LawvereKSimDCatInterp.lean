import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimQuot
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation Functor for `LawvereKSimDCat 2`

Defines a faithful functor from `LawvereKSimDCat 2` (the
depth-2 K^sim Lawvere category) into `Type`, sending arity
`n` to `Fin n → ℕ` and each morphism class to its standard
interpretation.  Mirrors `erInterpFunctor` for
`LawvereERCat`; the interp ignores the depth witness, so
the same construction would work for `LawvereKSimDCat d`
at any `d`, but we specialise to `d = 2` for use alongside
step 5's `kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat`.
-/

namespace GebLean

open CategoryTheory

/-- Lift `KMorN.interp` to the quotient.  Well-defined
because the setoid relation `kMorNSetoid` is exactly
extensional equality of interpretations. -/
def KMorNQuo.interp {n m : ℕ}
    (f : KMorNQuo n m) :
    (Fin n → ℕ) → (Fin m → ℕ) :=
  Quotient.lift
    (s := kMorNSetoid n m)
    KMorN.interp
    (fun _ _ h => funext h)
    f

/-- `KMorNQuo.interp` on a concrete representative reduces
to `KMorN.interp`. -/
@[simp] theorem KMorNQuo.interp_mk
    {n m : ℕ} (f : KMorN n m) :
    KMorNQuo.interp
      (Quotient.mk (kMorNSetoid n m) f) =
      f.interp :=
  rfl

/-- Interpretation of the quotient identity. -/
@[simp] theorem KMorNQuo.interp_id
    (n : ℕ) (ctx : Fin n → ℕ) :
    (KMorNQuo.id n).interp ctx = ctx := by
  unfold KMorNQuo.id
  simp [KMorNQuo.interp_mk, KMorN.interp_id]

/-- Interpretation of quotient composition. -/
@[simp] theorem KMorNQuo.interp_comp
    {n m k : ℕ} (f : KMorNQuo n m)
    (g : KMorNQuo m k)
    (ctx : Fin n → ℕ) :
    (KMorNQuo.comp f g).interp ctx =
      g.interp (f.interp ctx) := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  rfl

/-- The interpretation functor from `LawvereKSimDCat 2`
into `Type`.  Sends arity `n` to `Fin n → ℕ` and each
`KSimMor 2 n m` morphism class to its standard
interpretation, projecting through the depth witness via
`f.hom`. -/
def kInterpFunctor :
    LawvereKSimDCat 2 ⥤ Type where
  obj n := Fin n → ℕ
  map f := f.hom.interp
  map_id n := by
    funext ctx
    change (KMorNQuo.id n).interp ctx = ctx
    exact KMorNQuo.interp_id n ctx
  map_comp f g := by
    funext ctx
    change (KMorNQuo.comp f.hom g.hom).interp ctx
      = g.hom.interp (f.hom.interp ctx)
    exact KMorNQuo.interp_comp f.hom g.hom ctx

/-- `kInterpFunctor` is faithful: distinct morphism
classes produce distinct functions.  Reduces to the
extensional quotient on `KMorNQuo` via `KSimMor.ext`. -/
instance : kInterpFunctor.Faithful where
  map_injective {n m} {f g} h := by
    apply KSimMor.ext
    have hh : f.hom.interp = g.hom.interp := h
    refine Quotient.inductionOn₂
      (motive := fun (a b : KMorNQuo n m) =>
        a.interp = b.interp → a = b)
      f.hom g.hom ?_ hh
    intro a b heq
    exact Quotient.sound (fun ctx => congrFun heq ctx)

/-- Object component of `kInterpFunctor`: arity `n` maps
to the function space `Fin n → ℕ`.  Useful as a simp lemma
when reasoning about `kInterpFunctor`-images at concrete
arities. -/
@[simp] theorem kInterpFunctor_obj (n : LawvereKSimDCat 2) :
    kInterpFunctor.obj n = (Fin n → ℕ) := rfl

end GebLean
