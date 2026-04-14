import GebLean.LawvereERQuot
import GebLean.LawvereERPrimrec
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Computability.Ackermann

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

/-- Ackermann at arity `2 → 1` as a function
`(Fin 2 → ℕ) → (Fin 1 → ℕ)`. -/
def ackHom : (Fin 2 → ℕ) → (Fin 1 → ℕ) :=
  fun ctx _ => ack (ctx 0) (ctx 1)

/-- `erInterpFunctor` is not full: `ackHom`, which is
a well-defined function at the interpretation level,
is not the image of any morphism class of ER tuples. -/
theorem erInterpFunctor_not_full :
    ¬ erInterpFunctor.Full := by
  intro hfull
  have hsurj := Functor.map_surjective
    (F := erInterpFunctor)
    (X := (2 : ℕ)) (Y := (1 : ℕ))
  obtain ⟨f, hf⟩ := hsurj ackHom
  obtain ⟨f_raw, hfr⟩ :=
    Quotient.exists_rep (s := erMorNSetoid 2 1) f
  have hinterp : ∀ ctx : Fin 2 → ℕ,
      f_raw.interp ctx = ackHom ctx := by
    intro ctx
    have hmap : erInterpFunctor.map f = ackHom := hf
    have heq1 : erInterpFunctor.map f =
        ERMorNQuo.interp f := rfl
    rw [heq1, ← hfr] at hmap
    have hctx := congrFun hmap ctx
    simp only [ERMorNQuo.interp, Quotient.lift_mk]
      at hctx
    exact hctx
  set t : ERMor1 2 := f_raw 0 with ht
  have hcomp : ∀ ctx : Fin 2 → ℕ,
      t.interp ctx = ack (ctx 0) (ctx 1) := by
    intro ctx
    have h0 := congrFun (hinterp ctx) 0
    simp only [ERMorN.interp, ackHom] at h0
    exact h0
  have hp := t.toPrimrec'
  have heq : (fun v : List.Vector ℕ 2 => t.interp v.get) =
      (fun v : List.Vector ℕ 2 =>
        ack v.head v.tail.head) := by
    funext v
    rw [hcomp]
    congr 1
    · exact List.Vector.get_zero v
    · show v.get 1 = v.tail.head
      rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
        ← List.Vector.get_tail_succ,
        List.Vector.get_zero]
  rw [heq] at hp
  have hprim2 : Primrec₂ ack :=
    Nat.Primrec'.prim_iff₂.mp hp
  exact not_primrec₂_ack hprim2

end GebLean
