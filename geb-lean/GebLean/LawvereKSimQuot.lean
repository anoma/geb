import GebLean.LawvereKSimInterp
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Extensional-equality quotient and Lawvere structure

This module will define the extensional-equality setoid
`kMorNSetoid` on K^sim morphisms, the quotient category
`KMorNQuo`, the Lawvere finite-product structure, and the
depth-restricted full subcategory `KSimMor d` per design
principle P4.
-/

namespace GebLean

/-- Extensional equality on multi-output K^sim
morphisms.  Two `f, g : KMorN n m` are equivalent iff
their interpretations agree at every context (and so
agree component-wise). -/
def kMorNSetoid (n m : ℕ) : Setoid (KMorN n m) where
  r f g := ∀ ctx : Fin n → ℕ, f.interp ctx = g.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }

/-- Quotient morphism type for the K^sim Lawvere theory:
equivalence classes of `KMorN n m` tuples under
extensional equality. -/
def KMorNQuo (n m : ℕ) : Type :=
  Quotient (kMorNSetoid n m)

/-- The identity morphism in the quotient category: the
equivalence class of the tuple of projections. -/
def KMorNQuo.id (n : ℕ) : KMorNQuo n n :=
  Quotient.mk (kMorNSetoid n n) (KMorN.id n)

/-- Composition of quotient morphisms, lifted from
`KMorN.comp` via `Quotient.lift₂`.  Well-definedness
follows from the fact that extensionally equal tuples
compose to extensionally equal results. -/
def KMorNQuo.comp {n m k : ℕ}
    (f : KMorNQuo n m) (g : KMorNQuo m k) :
    KMorNQuo n k :=
  Quotient.lift₂
    (s₁ := kMorNSetoid n m)
    (s₂ := kMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (kMorNSetoid n k)
        (KMorN.comp g' f'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := kMorNSetoid n k)
        (fun ctx => by
          simp only [KMorN.interp_comp]
          rw [hf ctx, hg (ga.interp ctx)]))
    f g

/-- Left identity: `comp (id n) f = f`. -/
theorem KMorNQuo.id_comp {n m : ℕ}
    (f : KMorNQuo n m) :
    KMorNQuo.comp (KMorNQuo.id n) f = f :=
  Quotient.ind
    (motive := fun f =>
      KMorNQuo.comp (KMorNQuo.id n) f = f)
    (fun f_raw =>
      Quotient.sound
        (s := kMorNSetoid n m)
        (fun ctx => by
          funext i
          simp [KMorN.interp_comp,
                KMorN.interp_id]))
    f

/-- Right identity: `comp f (id m) = f`. -/
theorem KMorNQuo.comp_id {n m : ℕ}
    (f : KMorNQuo n m) :
    KMorNQuo.comp f (KMorNQuo.id m) = f :=
  Quotient.ind
    (motive := fun f =>
      KMorNQuo.comp f (KMorNQuo.id m) = f)
    (fun f_raw =>
      Quotient.sound
        (s := kMorNSetoid n m)
        (fun ctx => by
          funext i
          simp [KMorN.interp_comp,
                KMorN.interp_id]))
    f

/-- Associativity of composition. -/
theorem KMorNQuo.comp_assoc {n m k l : ℕ}
    (f : KMorNQuo n m) (g : KMorNQuo m k)
    (h : KMorNQuo k l) :
    KMorNQuo.comp (KMorNQuo.comp f g) h
      = KMorNQuo.comp f (KMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      KMorNQuo.comp (KMorNQuo.comp f g) h
        = KMorNQuo.comp f (KMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          KMorNQuo.comp (KMorNQuo.comp
            (Quotient.mk _ f_raw) g) h
          = KMorNQuo.comp (Quotient.mk _ f_raw)
              (KMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              KMorNQuo.comp (KMorNQuo.comp
                (Quotient.mk _ f_raw)
                (Quotient.mk _ g_raw)) h
              = KMorNQuo.comp (Quotient.mk _ f_raw)
                  (KMorNQuo.comp
                    (Quotient.mk _ g_raw) h))
            (fun h_raw =>
              Quotient.sound
                (s := kMorNSetoid n l)
                (fun ctx => by
                  funext i
                  simp [KMorN.interp_comp]))
            h)
        g)
    f

/-- The Lawvere theory of K^sim functions.  Objects
are natural numbers (arities); morphisms are
equivalence classes of `KMorN` tuples under
extensional equality. -/
def LawvereKSimCat := ℕ

instance (n : ℕ) : OfNat LawvereKSimCat n :=
  ⟨(n : ℕ)⟩

instance : BEq LawvereKSimCat :=
  inferInstanceAs (BEq ℕ)

instance : DecidableEq LawvereKSimCat :=
  inferInstanceAs (DecidableEq ℕ)

instance :
    CategoryTheory.CategoryStruct LawvereKSimCat where
  Hom := KMorNQuo
  id n := KMorNQuo.id n
  comp f g := KMorNQuo.comp f g

instance : CategoryTheory.Category LawvereKSimCat where
  id_comp := KMorNQuo.id_comp
  comp_id := KMorNQuo.comp_id
  assoc := KMorNQuo.comp_assoc

end GebLean
