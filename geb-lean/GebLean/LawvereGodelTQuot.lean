import GebLean.LawvereER
import GebLean.LawvereGodelT
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

/-!
# Categorical structure on `LawvereGodelT`

A fresh inductive `GodelTMor1` parallel to `ERMor1` gives the
B-W T⁻′ fragment its Lawvere-theory presentation directly,
with one constructor per elementary operation
(`zero` / `succ` / `pred` / `proj` / `disc` / `iter`) plus
`comp` for composition.  Tuples, the extensional-equality
quotient, the `Category LawvereGodelTCat` instance, and
`HasChosenFiniteProducts` are built on top.
-/

namespace GebLean

open CategoryTheory

/-- A single GodelT morphism `n → 1`: an elementary-recursive
expression at arity `n`, built from a Gödel-T-flavoured
primitive set that contains `ERMor1`'s primitives plus the
B-W T⁻′ extras `pred` and `disc`.  The iteration primitives
`bsum` / `bprod` match `ERMor1`'s — the iter forms that keep
the fragment within the elementary-recursive functions. -/
inductive GodelTMor1 : ℕ → Type
  | zero : GodelTMor1 0
  | succ : GodelTMor1 1
  | pred : GodelTMor1 1
  | proj {k : ℕ} (i : Fin k) : GodelTMor1 k
  | sub : GodelTMor1 2
  | disc : GodelTMor1 3
  | bsum {k : ℕ} (f : GodelTMor1 (k + 1)) :
      GodelTMor1 (k + 1)
  | bprod {k : ℕ} (f : GodelTMor1 (k + 1)) :
      GodelTMor1 (k + 1)
  | comp {k n : ℕ} (f : GodelTMor1 k)
      (g : Fin k → GodelTMor1 n) : GodelTMor1 n

/-- Standard interpretation of a `GodelTMor1 n` as a function
`(Fin n → ℕ) → ℕ`.  The `bsum` / `bprod` cases delegate to
the shared helpers `natBSum` / `natBProd`. -/
def GodelTMor1.interp : {n : ℕ} → GodelTMor1 n →
    (Fin n → ℕ) → ℕ
  | _, .zero, _ => 0
  | _, .succ, ctx => Nat.succ (ctx 0)
  | _, .pred, ctx => Nat.pred (ctx 0)
  | _, .proj i, ctx => ctx i
  | _, .sub, ctx => ctx 0 - ctx 1
  | _, .disc, ctx =>
      match ctx 0 with
      | 0 => ctx 1
      | _ + 1 => ctx 2
  | _, .bsum f, ctx =>
      natBSum (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx)))
  | _, .bprod f, ctx =>
      natBProd (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx)))
  | _, .comp f g, ctx =>
      f.interp (fun i => (g i).interp ctx)

@[simp] theorem GodelTMor1.interp_zero (ctx : Fin 0 → ℕ) :
    GodelTMor1.zero.interp ctx = 0 := rfl

@[simp] theorem GodelTMor1.interp_succ (ctx : Fin 1 → ℕ) :
    GodelTMor1.succ.interp ctx = (ctx 0).succ := rfl

@[simp] theorem GodelTMor1.interp_pred (ctx : Fin 1 → ℕ) :
    GodelTMor1.pred.interp ctx = (ctx 0).pred := rfl

@[simp] theorem GodelTMor1.interp_proj {k : ℕ} (i : Fin k)
    (ctx : Fin k → ℕ) :
    (GodelTMor1.proj i).interp ctx = ctx i := rfl

@[simp] theorem GodelTMor1.interp_sub (ctx : Fin 2 → ℕ) :
    GodelTMor1.sub.interp ctx = ctx 0 - ctx 1 := rfl

@[simp] theorem GodelTMor1.interp_disc (ctx : Fin 3 → ℕ) :
    GodelTMor1.disc.interp ctx =
      (match ctx 0 with
        | 0 => ctx 1
        | _ + 1 => ctx 2) := rfl

@[simp] theorem GodelTMor1.interp_bsum {k : ℕ}
    (f : GodelTMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (GodelTMor1.bsum f).interp ctx =
      natBSum (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx))) := rfl

@[simp] theorem GodelTMor1.interp_bprod {k : ℕ}
    (f : GodelTMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (GodelTMor1.bprod f).interp ctx =
      natBProd (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx))) := rfl

@[simp] theorem GodelTMor1.interp_comp {k n : ℕ}
    (f : GodelTMor1 k) (g : Fin k → GodelTMor1 n)
    (ctx : Fin n → ℕ) :
    (GodelTMor1.comp f g).interp ctx =
      f.interp (fun i => (g i).interp ctx) := rfl

/-- An `m`-tuple of `n`-ary GodelT morphisms: the hom-object of
the Lawvere theory. -/
def GodelTMorN (n m : ℕ) : Type := Fin m → GodelTMor1 n

/-- Standard interpretation of a `GodelTMorN n m` tuple. -/
def GodelTMorN.interp {n m : ℕ} (f : GodelTMorN n m)
    (ctx : Fin n → ℕ) : Fin m → ℕ :=
  fun i => (f i).interp ctx

/-- Identity morphism at arity `n`: the tuple of `n`
projections. -/
def GodelTMorN.id (n : ℕ) : GodelTMorN n n :=
  fun i => GodelTMor1.proj i

/-- Composition of `GodelTMorN` tuples. -/
def GodelTMorN.comp {n m k : ℕ}
    (f : GodelTMorN n m) (g : GodelTMorN m k) :
    GodelTMorN n k :=
  fun i => GodelTMor1.comp (g i) f

@[simp] theorem GodelTMorN.interp_id {n : ℕ}
    (ctx : Fin n → ℕ) :
    (GodelTMorN.id n).interp ctx = ctx := by
  funext i
  exact GodelTMor1.interp_proj i ctx

@[simp] theorem GodelTMorN.interp_comp {n m k : ℕ}
    (f : GodelTMorN n m) (g : GodelTMorN m k)
    (ctx : Fin n → ℕ) :
    (f.comp g).interp ctx = g.interp (f.interp ctx) := by
  funext i
  exact GodelTMor1.interp_comp (g i) f ctx

/-- The setoid on `GodelTMorN n m` induced by extensional
equality of interpretations. -/
def godelTMorNSetoid (n m : ℕ) : Setoid (GodelTMorN n m) where
  r f g := ∀ ctx : Fin n → ℕ, f.interp ctx = g.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx => (h1 ctx).trans (h2 ctx)
  }

/-- Quotient morphism type for the Lawvere theory of the
GodelT T⁻′ fragment. -/
def GodelTMorNQuo (n m : ℕ) : Type :=
  Quotient (godelTMorNSetoid n m)

/-- Identity morphism in the quotient category. -/
def GodelTMorNQuo.id (n : ℕ) : GodelTMorNQuo n n :=
  Quotient.mk (godelTMorNSetoid n n) (GodelTMorN.id n)

/-- Composition of quotient morphisms, lifted from
`GodelTMorN.comp` via `Quotient.lift₂`. -/
def GodelTMorNQuo.comp {n m k : ℕ}
    (f : GodelTMorNQuo n m) (g : GodelTMorNQuo m k) :
    GodelTMorNQuo n k :=
  Quotient.lift₂
    (s₁ := godelTMorNSetoid n m)
    (s₂ := godelTMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (godelTMorNSetoid n k)
        (GodelTMorN.comp f' g'))
    (fun _ _ _ _ hf hg =>
      Quotient.sound
        (s := godelTMorNSetoid n k)
        (fun ctx => by
          simp only [GodelTMorN.interp_comp]
          rw [hf ctx, hg (_ : Fin m → ℕ)]))
    f g

theorem GodelTMorNQuo.id_comp {n m : ℕ}
    (f : GodelTMorNQuo n m) :
    GodelTMorNQuo.comp (GodelTMorNQuo.id n) f = f :=
  Quotient.ind
    (motive := fun f =>
      GodelTMorNQuo.comp (GodelTMorNQuo.id n) f = f)
    (fun _ =>
      Quotient.sound
        (s := godelTMorNSetoid n m)
        (fun _ => by
          simp [GodelTMorN.interp_comp, GodelTMorN.interp_id]))
    f

theorem GodelTMorNQuo.comp_id {n m : ℕ}
    (f : GodelTMorNQuo n m) :
    GodelTMorNQuo.comp f (GodelTMorNQuo.id m) = f :=
  Quotient.ind
    (motive := fun f =>
      GodelTMorNQuo.comp f (GodelTMorNQuo.id m) = f)
    (fun _ =>
      Quotient.sound
        (s := godelTMorNSetoid n m)
        (fun _ => by
          simp [GodelTMorN.interp_comp, GodelTMorN.interp_id]))
    f

theorem GodelTMorNQuo.comp_assoc {n m k l : ℕ}
    (f : GodelTMorNQuo n m)
    (g : GodelTMorNQuo m k)
    (h : GodelTMorNQuo k l) :
    GodelTMorNQuo.comp (GodelTMorNQuo.comp f g) h =
      GodelTMorNQuo.comp f (GodelTMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      ∀ (g : GodelTMorNQuo m k) (h : GodelTMorNQuo k l),
        GodelTMorNQuo.comp (GodelTMorNQuo.comp f g) h =
          GodelTMorNQuo.comp f (GodelTMorNQuo.comp g h))
    (fun _ =>
      Quotient.ind
        (motive := fun g =>
          ∀ (h : GodelTMorNQuo k l),
            GodelTMorNQuo.comp (GodelTMorNQuo.comp _ g) h =
              GodelTMorNQuo.comp _ (GodelTMorNQuo.comp g h))
        (fun _ =>
          Quotient.ind
            (motive := fun h =>
              GodelTMorNQuo.comp (GodelTMorNQuo.comp _ _) h =
                GodelTMorNQuo.comp _
                  (GodelTMorNQuo.comp _ h))
            (fun _ =>
              Quotient.sound
                (s := godelTMorNSetoid n l)
                (fun _ => by
                  simp [GodelTMorN.interp_comp]))))
    f g h

/-- The quotient Lawvere theory of the GodelT T⁻′ fragment. -/
def LawvereGodelTCat := ℕ

instance (n : ℕ) : OfNat LawvereGodelTCat n := ⟨(n : ℕ)⟩
instance : BEq LawvereGodelTCat := inferInstanceAs (BEq ℕ)
instance : DecidableEq LawvereGodelTCat :=
  inferInstanceAs (DecidableEq ℕ)

instance : CategoryStruct LawvereGodelTCat where
  Hom := GodelTMorNQuo
  id n := GodelTMorNQuo.id n
  comp f g := GodelTMorNQuo.comp f g

instance : Category LawvereGodelTCat where
  id_comp := GodelTMorNQuo.id_comp
  comp_id := GodelTMorNQuo.comp_id
  assoc := GodelTMorNQuo.comp_assoc

/-- Terminal morphism: the empty tuple. -/
def GodelTMorN.terminal (n : ℕ) : GodelTMorN n 0 :=
  fun i => i.elim0

/-- First projection from the product arity `n + m`. -/
def GodelTMorN.fst {n m : ℕ} : GodelTMorN (n + m) n :=
  fun i => GodelTMor1.proj ⟨i.val, by omega⟩

/-- Second projection from the product arity `n + m`. -/
def GodelTMorN.snd {n m : ℕ} : GodelTMorN (n + m) m :=
  fun i => GodelTMor1.proj ⟨n + i.val, by omega⟩

/-- Pairing: produce a morphism to arity `n + m` from morphisms
to arity `n` and arity `m`. -/
def GodelTMorN.pair {k n m : ℕ}
    (f : GodelTMorN k n) (g : GodelTMorN k m) :
    GodelTMorN k (n + m) :=
  fun i =>
    if h : i.val < n then f ⟨i.val, h⟩
    else g ⟨i.val - n, by omega⟩

@[simp] theorem GodelTMorN.interp_terminal {n : ℕ}
    (ctx : Fin n → ℕ) :
    (GodelTMorN.terminal n).interp ctx = Fin.elim0 :=
  funext (fun i => i.elim0)

@[simp] theorem GodelTMorN.interp_fst {n m : ℕ}
    (ctx : Fin (n + m) → ℕ) :
    (GodelTMorN.fst (n := n) (m := m)).interp ctx =
      fun i => ctx ⟨i.val, by omega⟩ := by
  funext i
  exact GodelTMor1.interp_proj ⟨i.val, by omega⟩ ctx

@[simp] theorem GodelTMorN.interp_snd {n m : ℕ}
    (ctx : Fin (n + m) → ℕ) :
    (GodelTMorN.snd (n := n) (m := m)).interp ctx =
      fun i => ctx ⟨n + i.val, by omega⟩ := by
  funext i
  exact GodelTMor1.interp_proj ⟨n + i.val, by omega⟩ ctx

@[simp] theorem GodelTMorN.interp_pair {k n m : ℕ}
    (f : GodelTMorN k n) (g : GodelTMorN k m)
    (ctx : Fin k → ℕ) :
    (GodelTMorN.pair f g).interp ctx =
      fun i =>
        if h : i.val < n then f.interp ctx ⟨i.val, h⟩
        else g.interp ctx ⟨i.val - n, by omega⟩ := by
  funext i
  change (GodelTMorN.pair f g i).interp ctx = _
  unfold GodelTMorN.pair
  split_ifs <;> rfl

/-- Terminal morphism in the quotient category. -/
def GodelTMorNQuo.terminal (n : ℕ) : GodelTMorNQuo n 0 :=
  Quotient.mk (godelTMorNSetoid n 0) (GodelTMorN.terminal n)

/-- Any quotient morphism to arity 0 equals the terminal. -/
theorem GodelTMorNQuo.terminal_uniq {n : ℕ}
    (f : GodelTMorNQuo n 0) :
    f = GodelTMorNQuo.terminal n :=
  Quotient.ind
    (motive := fun f => f = GodelTMorNQuo.terminal n)
    (fun _ =>
      Quotient.sound
        (s := godelTMorNSetoid n 0)
        (fun _ => funext (fun i => Fin.elim0 i)))
    f

/-- First projection in the quotient category. -/
def GodelTMorNQuo.fst {n m : ℕ} : GodelTMorNQuo (n + m) n :=
  Quotient.mk (godelTMorNSetoid (n + m) n) GodelTMorN.fst

/-- Second projection in the quotient category. -/
def GodelTMorNQuo.snd {n m : ℕ} : GodelTMorNQuo (n + m) m :=
  Quotient.mk (godelTMorNSetoid (n + m) m) GodelTMorN.snd

/-- Pairing in the quotient category. -/
def GodelTMorNQuo.pair {k n m : ℕ}
    (f : GodelTMorNQuo k n) (g : GodelTMorNQuo k m) :
    GodelTMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := godelTMorNSetoid k n)
    (s₂ := godelTMorNSetoid k m)
    (fun f' g' =>
      Quotient.mk (godelTMorNSetoid k (n + m))
        (GodelTMorN.pair f' g'))
    (fun _ _ _ _ hf hg =>
      Quotient.sound
        (s := godelTMorNSetoid k (n + m))
        (fun ctx => by
          simp only [GodelTMorN.interp_pair]
          funext i
          split_ifs with h
          · exact congrFun (hf ctx) ⟨i.val, h⟩
          · exact congrFun (hg ctx) ⟨i.val - n, by omega⟩))
    f g

theorem GodelTMorNQuo.pair_fst {k n m : ℕ}
    (f : GodelTMorNQuo k n) (g : GodelTMorNQuo k m) :
    GodelTMorNQuo.comp (GodelTMorNQuo.pair f g)
      GodelTMorNQuo.fst = f :=
  Quotient.ind₂
    (motive := fun f g =>
      GodelTMorNQuo.comp (GodelTMorNQuo.pair f g)
        GodelTMorNQuo.fst = f)
    (fun _ _ =>
      Quotient.sound
        (s := godelTMorNSetoid k n)
        (fun ctx => by
          simp only [GodelTMorN.interp_comp,
            GodelTMorN.interp_pair, GodelTMorN.interp_fst]
          funext i
          simp only [Fin.is_lt, reduceDIte, Fin.eta]))
    f g

theorem GodelTMorNQuo.pair_snd {k n m : ℕ}
    (f : GodelTMorNQuo k n) (g : GodelTMorNQuo k m) :
    GodelTMorNQuo.comp (GodelTMorNQuo.pair f g)
      GodelTMorNQuo.snd = g :=
  Quotient.ind₂
    (motive := fun f g =>
      GodelTMorNQuo.comp (GodelTMorNQuo.pair f g)
        GodelTMorNQuo.snd = g)
    (fun _ g_raw =>
      Quotient.sound
        (s := godelTMorNSetoid k m)
        (fun ctx => by
          simp only [GodelTMorN.interp_comp,
            GodelTMorN.interp_pair, GodelTMorN.interp_snd]
          funext i
          simp only [dif_neg
            (show ¬ (n + i.val) < n by omega)]
          change (g_raw ⟨n + i.val - n, _⟩).interp ctx =
            (g_raw i).interp ctx
          simp only [Nat.add_sub_cancel_left]))
    f g

theorem GodelTMorNQuo.pair_uniq {k n m : ℕ}
    (f : GodelTMorNQuo k n) (g : GodelTMorNQuo k m)
    (h : GodelTMorNQuo k (n + m))
    (hfst : GodelTMorNQuo.comp h GodelTMorNQuo.fst = f)
    (hsnd : GodelTMorNQuo.comp h GodelTMorNQuo.snd = g) :
    h = GodelTMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : GodelTMorNQuo k n) (g : GodelTMorNQuo k m),
        GodelTMorNQuo.comp h GodelTMorNQuo.fst = f →
        GodelTMorNQuo.comp h GodelTMorNQuo.snd = g →
        h = GodelTMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : GodelTMorNQuo k m),
            GodelTMorNQuo.comp (Quotient.mk _ h_raw)
              GodelTMorNQuo.fst = f →
            GodelTMorNQuo.comp (Quotient.mk _ h_raw)
              GodelTMorNQuo.snd = g →
            Quotient.mk _ h_raw = GodelTMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              GodelTMorNQuo.comp (Quotient.mk _ h_raw)
                GodelTMorNQuo.fst = Quotient.mk _ f_raw →
              GodelTMorNQuo.comp (Quotient.mk _ h_raw)
                GodelTMorNQuo.snd = g →
              Quotient.mk _ h_raw =
                GodelTMorNQuo.pair (Quotient.mk _ f_raw) g)
            (fun _ hf_eq hs_eq => by
              have hf_rel := Quotient.exact
                (s := godelTMorNSetoid k n) hf_eq
              have hs_rel := Quotient.exact
                (s := godelTMorNSetoid k m) hs_eq
              apply Quotient.sound
                (s := godelTMorNSetoid k (n + m))
              intro ctx
              simp only [GodelTMorN.interp_pair]
              funext i
              split_ifs with hlt
              · have := congrFun (hf_rel ctx) ⟨i.val, hlt⟩
                simp only [GodelTMorN.interp_comp,
                  GodelTMorN.interp_fst] at this
                exact this
              · have step := congrFun (hs_rel ctx)
                  ⟨i.val - n, by omega⟩
                simp only [GodelTMorN.interp_comp,
                  GodelTMorN.interp_snd] at step
                have hrw : h_raw.interp ctx i =
                  h_raw.interp ctx
                    ⟨n + (i.val - n), by omega⟩ := by
                  simp only [Nat.add_sub_cancel'
                    (Nat.le_of_not_lt hlt)]
                rw [hrw]
                exact step)))
    h f g hfst hsnd

/-- Chosen binary product for `LawvereGodelTCat`. -/
def lawvereGodelTProduct (n m : LawvereGodelTCat) :
    ChosenBinaryProduct n m where
  obj := (Nat.add n m : ℕ)
  fst := GodelTMorNQuo.fst
  snd := GodelTMorNQuo.snd
  lift f g := GodelTMorNQuo.pair f g
  lift_fst := GodelTMorNQuo.pair_fst
  lift_snd := GodelTMorNQuo.pair_snd
  lift_uniq f g h hf hs :=
    GodelTMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for `LawvereGodelTCat`. -/
def lawvereGodelTTerminal : ChosenTerminal LawvereGodelTCat where
  obj := (0 : ℕ)
  from_ n := GodelTMorNQuo.terminal n
  uniq f := GodelTMorNQuo.terminal_uniq f

instance : HasChosenFiniteProducts LawvereGodelTCat where
  terminal := lawvereGodelTTerminal
  product := lawvereGodelTProduct

end GebLean
