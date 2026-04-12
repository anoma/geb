import GebLean.LawvereER
import Mathlib.CategoryTheory.Category.Basic

/-!
# Quotient Category of Elementary Recursive Functions

Defines the quotient of `ERMorN` tuples by extensional
equality of their standard interpretations, yielding a
category `LawvereERCat` whose morphisms from `n` to `m`
are equivalence classes of `m`-tuples of `n`-ary
elementary recursive functions.
-/

namespace GebLean

open CategoryTheory

/-- The setoid on `ERMorN n m` induced by extensional
equality of interpretations: two morphism tuples are
related when their interpretations agree on every
context. -/
def erMorNSetoid (n m : ℕ) :
    Setoid (ERMorN n m) where
  r f g := ∀ ctx : Fin n → ℕ,
    f.interp ctx = g.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }

/-- Quotient morphism type: equivalence classes of
`ERMorN n m` tuples under extensional equality. -/
def ERMorNQuo (n m : ℕ) : Type :=
  Quotient (erMorNSetoid n m)

/-- The identity morphism in the quotient category:
the equivalence class of the tuple of projections. -/
def ERMorNQuo.id (n : ℕ) : ERMorNQuo n n :=
  Quotient.mk (erMorNSetoid n n) (ERMorN.id n)

/-- Composition of quotient morphisms, lifted from
`ERMorN.comp` via `Quotient.lift₂`.  Well-definedness
follows from the fact that extensionally equal tuples
compose to extensionally equal results. -/
def ERMorNQuo.comp {n m k : ℕ}
    (f : ERMorNQuo n m) (g : ERMorNQuo m k) :
    ERMorNQuo n k :=
  Quotient.lift₂
    (s₁ := erMorNSetoid n m)
    (s₂ := erMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (erMorNSetoid n k)
        (ERMorN.comp f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erMorNSetoid n k)
        (fun ctx => by
          simp only [ERMorN.interp_comp]
          rw [hf ctx, hg (ga.interp ctx)]))
    f g

/-- Left identity: `comp (id n) f = f`. -/
theorem ERMorNQuo.id_comp {n m : ℕ}
    (f : ERMorNQuo n m) :
    ERMorNQuo.comp (ERMorNQuo.id n) f = f :=
  Quotient.ind
    (motive := fun f =>
      ERMorNQuo.comp (ERMorNQuo.id n) f = f)
    (fun f_raw =>
      Quotient.sound
        (s := erMorNSetoid n m)
        (fun ctx => by
          simp [ERMorN.interp_comp,
                ERMorN.interp_id]))
    f

/-- Right identity: `comp f (id m) = f`. -/
theorem ERMorNQuo.comp_id {n m : ℕ}
    (f : ERMorNQuo n m) :
    ERMorNQuo.comp f (ERMorNQuo.id m) = f :=
  Quotient.ind
    (motive := fun f =>
      ERMorNQuo.comp f (ERMorNQuo.id m) = f)
    (fun f_raw =>
      Quotient.sound
        (s := erMorNSetoid n m)
        (fun ctx => by
          simp [ERMorN.interp_comp,
                ERMorN.interp_id]))
    f

/-- Associativity of composition in the quotient. -/
theorem ERMorNQuo.comp_assoc {n m k l : ℕ}
    (f : ERMorNQuo n m)
    (g : ERMorNQuo m k)
    (h : ERMorNQuo k l) :
    ERMorNQuo.comp (ERMorNQuo.comp f g) h =
      ERMorNQuo.comp f (ERMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      ∀ (g : ERMorNQuo m k)
        (h : ERMorNQuo k l),
        ERMorNQuo.comp
          (ERMorNQuo.comp f g) h =
          ERMorNQuo.comp f
            (ERMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          ∀ (h : ERMorNQuo k l),
            ERMorNQuo.comp
              (ERMorNQuo.comp
                (Quotient.mk _ f_raw) g) h =
              ERMorNQuo.comp
                (Quotient.mk _ f_raw)
                (ERMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              ERMorNQuo.comp
                (ERMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (Quotient.mk _ g_raw)) h =
                ERMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (ERMorNQuo.comp
                    (Quotient.mk _ g_raw) h))
            (fun h_raw =>
              Quotient.sound
                (s := erMorNSetoid n l)
                (fun ctx => by
                  simp [ERMorN.interp_comp]))))
    f g h

/-- The quotient Lawvere theory of elementary recursive
functions.  Objects are natural numbers (arities).
Morphisms are equivalence classes of `ERMorN` tuples
under extensional equality. -/
@[reducible] def LawvereERCat := ℕ

instance : CategoryStruct LawvereERCat where
  Hom := ERMorNQuo
  id n := ERMorNQuo.id n
  comp f g := ERMorNQuo.comp f g

instance : Category LawvereERCat where
  id_comp := ERMorNQuo.id_comp
  comp_id := ERMorNQuo.comp_id
  assoc := ERMorNQuo.comp_assoc

end GebLean
