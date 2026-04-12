import GebLean.LawvereER
import GebLean.Utilities.ComputableLimits
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

/-- Quotient morphism type for the Lawvere theory of
elementary recursive functions: equivalence classes
of `ERMorN n m` tuples under extensional equality. -/
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

/-- The terminal morphism in the quotient
category: the equivalence class of the empty
tuple. -/
def ERMorNQuo.terminal (n : ℕ) :
    ERMorNQuo n 0 :=
  Quotient.mk (erMorNSetoid n 0)
    (ERMorN.terminal n)

/-- Any quotient morphism to arity 0 equals the
terminal morphism. -/
theorem ERMorNQuo.terminal_uniq {n : ℕ}
    (f : ERMorNQuo n 0) :
    f = ERMorNQuo.terminal n :=
  Quotient.ind
    (motive := fun f =>
      f = ERMorNQuo.terminal n)
    (fun _ => Quotient.sound
      (s := erMorNSetoid n 0)
      (fun _ => funext
        (fun i => Fin.elim0 i)))
    f

/-- First projection in the quotient
category. -/
def ERMorNQuo.fst {n m : ℕ} :
    ERMorNQuo (n + m) n :=
  Quotient.mk (erMorNSetoid (n + m) n)
    ERMorN.fst

/-- Second projection in the quotient
category. -/
def ERMorNQuo.snd {n m : ℕ} :
    ERMorNQuo (n + m) m :=
  Quotient.mk (erMorNSetoid (n + m) m)
    ERMorN.snd

/-- Pairing in the quotient category, lifted
from `ERMorN.pair` via `Quotient.lift₂`. -/
def ERMorNQuo.pair {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m) :
    ERMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := erMorNSetoid k n)
    (s₂ := erMorNSetoid k m)
    (fun f' g' =>
      Quotient.mk (erMorNSetoid k (n + m))
        (ERMorN.pair f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erMorNSetoid k (n + m))
        (fun ctx => by
          simp only [ERMorN.interp_pair]
          funext i
          split_ifs with h
          · exact congrFun (hf ctx)
              ⟨i.val, h⟩
          · exact congrFun (hg ctx)
              ⟨i.val - n, by omega⟩))
    f g

/-- Composing pairing with the first projection
recovers the first component. -/
theorem ERMorNQuo.pair_fst {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m) :
    ERMorNQuo.comp (ERMorNQuo.pair f g)
      ERMorNQuo.fst = f :=
  Quotient.ind₂
    (motive := fun f g =>
      ERMorNQuo.comp (ERMorNQuo.pair f g)
        ERMorNQuo.fst = f)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erMorNSetoid k n)
        (fun ctx => by
          simp only [ERMorN.interp_comp,
            ERMorN.interp_pair,
            ERMorN.interp_fst,
            Fin.is_lt, reduceDIte,
            Fin.eta]
          rfl))
    f g

/-- Composing pairing with the second projection
recovers the second component. -/
theorem ERMorNQuo.pair_snd {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m) :
    ERMorNQuo.comp (ERMorNQuo.pair f g)
      ERMorNQuo.snd = g :=
  Quotient.ind₂
    (motive := fun f g =>
      ERMorNQuo.comp (ERMorNQuo.pair f g)
        ERMorNQuo.snd = g)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erMorNSetoid k m)
        (fun ctx => by
          simp only [ERMorN.interp_comp,
            ERMorN.interp_pair,
            ERMorN.interp_snd]
          funext i
          simp only [dif_neg
            (show ¬ (n + i.val) < n
              by omega)]
          change
            (g_raw ⟨n + i.val - n, _⟩).interp
            ctx = (g_raw i).interp ctx
          simp only [Nat.add_sub_cancel_left]))
    f g

/-- Uniqueness of pairing: any morphism whose
compositions with the projections yield `f` and
`g` equals `pair f g`. -/
theorem ERMorNQuo.pair_uniq {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m)
    (h : ERMorNQuo k (n + m))
    (hfst : ERMorNQuo.comp h
      ERMorNQuo.fst = f)
    (hsnd : ERMorNQuo.comp h
      ERMorNQuo.snd = g) :
    h = ERMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : ERMorNQuo k n)
        (g : ERMorNQuo k m),
        ERMorNQuo.comp h ERMorNQuo.fst = f →
        ERMorNQuo.comp h ERMorNQuo.snd = g →
        h = ERMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : ERMorNQuo k m),
            ERMorNQuo.comp
              (Quotient.mk _ h_raw)
              ERMorNQuo.fst = f →
            ERMorNQuo.comp
              (Quotient.mk _ h_raw)
              ERMorNQuo.snd = g →
            Quotient.mk _ h_raw =
              ERMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              ERMorNQuo.comp
                (Quotient.mk _ h_raw)
                ERMorNQuo.fst =
                Quotient.mk _ f_raw →
              ERMorNQuo.comp
                (Quotient.mk _ h_raw)
                ERMorNQuo.snd = g →
              Quotient.mk _ h_raw =
                ERMorNQuo.pair
                  (Quotient.mk _ f_raw) g)
            (fun g_raw hf_eq hs_eq => by
              have hf_rel :=
                Quotient.exact
                  (s := erMorNSetoid k n)
                  hf_eq
              have hs_rel :=
                Quotient.exact
                  (s := erMorNSetoid k m)
                  hs_eq
              apply Quotient.sound
                (s := erMorNSetoid k (n + m))
              intro ctx
              simp only [ERMorN.interp_pair]
              funext i
              split_ifs with hlt
              · have := congrFun
                  (hf_rel ctx) ⟨i.val, hlt⟩
                simp only [ERMorN.interp_comp,
                  ERMorN.interp_fst] at this
                exact this
              · have step := congrFun
                  (hs_rel ctx)
                  ⟨i.val - n, by omega⟩
                simp only [ERMorN.interp_comp,
                  ERMorN.interp_snd] at step
                have : h_raw.interp ctx i =
                  h_raw.interp ctx
                    ⟨n + (i.val - n),
                      (by omega)⟩ := by
                  simp only [
                    Nat.add_sub_cancel'
                      (Nat.le_of_not_lt hlt)]
                rw [this]
                exact step)))
    h f g hfst hsnd

/-- Chosen binary product for `LawvereERCat`:
the product of `n` and `m` is `n + m`. -/
def lawvereERProduct
    (n m : LawvereERCat) :
    ChosenBinaryProduct n m where
  obj := (n + m : ℕ)
  fst := ERMorNQuo.fst
  snd := ERMorNQuo.snd
  lift f g := ERMorNQuo.pair f g
  lift_fst := ERMorNQuo.pair_fst
  lift_snd := ERMorNQuo.pair_snd
  lift_uniq f g h hf hs :=
    ERMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for
`LawvereERCat`. -/
def lawvereERTerminal :
    ChosenTerminal LawvereERCat where
  obj := (0 : ℕ)
  from_ n := ERMorNQuo.terminal n
  uniq f := ERMorNQuo.terminal_uniq f

/-- `LawvereERCat` has chosen finite
products. -/
instance : HasChosenFiniteProducts
    LawvereERCat where
  terminal := lawvereERTerminal
  product := lawvereERProduct

end GebLean
