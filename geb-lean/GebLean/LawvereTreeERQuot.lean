import GebLean.LawvereTreeER
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

/-!
# Quotient Category for Tree-Native ER Morphisms

Defines the quotient of `TreeERMorN` tuples by extensional
equality of their interpretations on `Fin n → BT.{0}`,
yielding a category `LawvereTreeERCat` whose morphisms
from `n` to `m` are equivalence classes of `m`-tuples of
`n`-ary tree-native elementary recursive functions.
-/

namespace GebLean

open CategoryTheory

/-- The setoid on `TreeERMorN n m` induced by
extensional equality of interpretations: two morphism
tuples are related when their interpretations agree on
every context. -/
def treeErMorNSetoid (n m : ℕ) :
    Setoid (TreeERMorN n m) where
  r f g := ∀ ctx : Fin n → BT.{0},
    f.interp ctx = g.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }

/-- Quotient morphism type for the Lawvere theory of
tree-native elementary recursive functions: equivalence
classes of `TreeERMorN n m` tuples under extensional
equality. -/
def TreeERMorNQuo (n m : ℕ) : Type :=
  Quotient (treeErMorNSetoid n m)

/-- The identity morphism in the quotient category:
the equivalence class of the tuple of projections. -/
def TreeERMorNQuo.id (n : ℕ) :
    TreeERMorNQuo n n :=
  Quotient.mk (treeErMorNSetoid n n)
    (TreeERMorN.id n)

/-- Composition of quotient morphisms, lifted from
`TreeERMorN.comp` via `Quotient.lift₂`. -/
def TreeERMorNQuo.comp {n m k : ℕ}
    (f : TreeERMorNQuo n m)
    (g : TreeERMorNQuo m k) :
    TreeERMorNQuo n k :=
  Quotient.lift₂
    (s₁ := treeErMorNSetoid n m)
    (s₂ := treeErMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (treeErMorNSetoid n k)
        (TreeERMorN.comp f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := treeErMorNSetoid n k)
        (fun ctx => by
          simp only [TreeERMorN.interp_comp]
          rw [hf ctx,
            hg (ga.interp ctx)]))
    f g

/-- Left identity: `comp (id n) f = f`. -/
theorem TreeERMorNQuo.id_comp {n m : ℕ}
    (f : TreeERMorNQuo n m) :
    TreeERMorNQuo.comp
      (TreeERMorNQuo.id n) f = f :=
  Quotient.ind
    (motive := fun f =>
      TreeERMorNQuo.comp
        (TreeERMorNQuo.id n) f = f)
    (fun f_raw =>
      Quotient.sound
        (s := treeErMorNSetoid n m)
        (fun ctx => by
          simp [TreeERMorN.interp_comp,
                TreeERMorN.interp_id]))
    f

/-- Right identity: `comp f (id m) = f`. -/
theorem TreeERMorNQuo.comp_id {n m : ℕ}
    (f : TreeERMorNQuo n m) :
    TreeERMorNQuo.comp
      f (TreeERMorNQuo.id m) = f :=
  Quotient.ind
    (motive := fun f =>
      TreeERMorNQuo.comp
        f (TreeERMorNQuo.id m) = f)
    (fun f_raw =>
      Quotient.sound
        (s := treeErMorNSetoid n m)
        (fun ctx => by
          simp [TreeERMorN.interp_comp,
                TreeERMorN.interp_id]))
    f

/-- Associativity of composition in the
quotient. -/
theorem TreeERMorNQuo.comp_assoc
    {n m k l : ℕ}
    (f : TreeERMorNQuo n m)
    (g : TreeERMorNQuo m k)
    (h : TreeERMorNQuo k l) :
    TreeERMorNQuo.comp
      (TreeERMorNQuo.comp f g) h =
      TreeERMorNQuo.comp f
        (TreeERMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      ∀ (g : TreeERMorNQuo m k)
        (h : TreeERMorNQuo k l),
        TreeERMorNQuo.comp
          (TreeERMorNQuo.comp f g) h =
          TreeERMorNQuo.comp f
            (TreeERMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          ∀ (h : TreeERMorNQuo k l),
            TreeERMorNQuo.comp
              (TreeERMorNQuo.comp
                (Quotient.mk _ f_raw) g) h =
              TreeERMorNQuo.comp
                (Quotient.mk _ f_raw)
                (TreeERMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              TreeERMorNQuo.comp
                (TreeERMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (Quotient.mk _ g_raw))
                h =
                TreeERMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (TreeERMorNQuo.comp
                    (Quotient.mk _ g_raw)
                    h))
            (fun h_raw =>
              Quotient.sound
                (s := treeErMorNSetoid n l)
                (fun ctx => by
                  simp [
                    TreeERMorN.interp_comp
                  ]))))
    f g h

/-- The quotient Lawvere theory of tree-native
elementary recursive functions.  Objects are natural
numbers (arities).  Morphisms are equivalence classes
of `TreeERMorN` tuples under extensional
equality. -/
@[reducible] def LawvereTreeERCat := ℕ

instance : CategoryStruct LawvereTreeERCat where
  Hom := TreeERMorNQuo
  id n := TreeERMorNQuo.id n
  comp f g := TreeERMorNQuo.comp f g

instance : Category LawvereTreeERCat where
  id_comp := TreeERMorNQuo.id_comp
  comp_id := TreeERMorNQuo.comp_id
  assoc := TreeERMorNQuo.comp_assoc

/-- The terminal morphism: the empty tuple. -/
def TreeERMorN.terminal (n : ℕ) :
    TreeERMorN n 0 :=
  fun i => i.elim0

/-- The terminal morphism in the quotient
category. -/
def TreeERMorNQuo.terminal (n : ℕ) :
    TreeERMorNQuo n 0 :=
  Quotient.mk (treeErMorNSetoid n 0)
    (TreeERMorN.terminal n)

/-- Any quotient morphism to arity 0 equals the
terminal morphism. -/
theorem TreeERMorNQuo.terminal_uniq {n : ℕ}
    (f : TreeERMorNQuo n 0) :
    f = TreeERMorNQuo.terminal n :=
  Quotient.ind
    (motive := fun f =>
      f = TreeERMorNQuo.terminal n)
    (fun _ => Quotient.sound
      (s := treeErMorNSetoid n 0)
      (fun _ => funext
        (fun i => Fin.elim0 i)))
    f

/-- First projection from the product arity
`n + m`. -/
def TreeERMorN.fst {n m : ℕ} :
    TreeERMorN (n + m) n :=
  fun i => TreeERMor1.proj ⟨i.val, by omega⟩

/-- Interpretation of `fst`: selects the first
`n` components. -/
@[simp] theorem TreeERMorN.interp_fst
    {n m : ℕ}
    (ctx : Fin (n + m) → BT.{0}) :
    (TreeERMorN.fst
      (n := n) (m := m)).interp ctx =
      fun i => ctx ⟨i.val, by omega⟩ := rfl

/-- Second projection from the product arity
`n + m`. -/
def TreeERMorN.snd {n m : ℕ} :
    TreeERMorN (n + m) m :=
  fun i =>
    TreeERMor1.proj ⟨n + i.val, by omega⟩

/-- Interpretation of `snd`: selects the last
`m` components. -/
@[simp] theorem TreeERMorN.interp_snd
    {n m : ℕ}
    (ctx : Fin (n + m) → BT.{0}) :
    (TreeERMorN.snd
      (n := n) (m := m)).interp ctx =
      fun i =>
        ctx ⟨n + i.val, by omega⟩ := rfl

/-- Pairing: given morphisms to arity `n` and arity
`m`, produce a morphism to arity `n + m`. -/
def TreeERMorN.pair {k n m : ℕ}
    (f : TreeERMorN k n)
    (g : TreeERMorN k m) :
    TreeERMorN k (n + m) :=
  fun i =>
    if h : i.val < n then f ⟨i.val, h⟩
    else g ⟨i.val - n, by omega⟩

/-- Interpretation of `pair`: concatenates the
results of interpreting `f` and `g`. -/
@[simp] theorem TreeERMorN.interp_pair
    {k n m : ℕ} (f : TreeERMorN k n)
    (g : TreeERMorN k m)
    (ctx : Fin k → BT.{0}) :
    (TreeERMorN.pair f g).interp ctx =
      fun i =>
        if h : i.val < n
        then (f ⟨i.val, h⟩).interp ctx
        else (g ⟨i.val - n,
          by omega⟩).interp ctx := by
  funext i
  simp only [TreeERMorN.interp,
    TreeERMorN.pair]
  split <;> rfl

/-- First projection in the quotient
category. -/
def TreeERMorNQuo.fst {n m : ℕ} :
    TreeERMorNQuo (n + m) n :=
  Quotient.mk (treeErMorNSetoid (n + m) n)
    TreeERMorN.fst

/-- Second projection in the quotient
category. -/
def TreeERMorNQuo.snd {n m : ℕ} :
    TreeERMorNQuo (n + m) m :=
  Quotient.mk (treeErMorNSetoid (n + m) m)
    TreeERMorN.snd

/-- Pairing in the quotient category, lifted
from `TreeERMorN.pair` via
`Quotient.lift₂`. -/
def TreeERMorNQuo.pair {k n m : ℕ}
    (f : TreeERMorNQuo k n)
    (g : TreeERMorNQuo k m) :
    TreeERMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := treeErMorNSetoid k n)
    (s₂ := treeErMorNSetoid k m)
    (fun f' g' =>
      Quotient.mk
        (treeErMorNSetoid k (n + m))
        (TreeERMorN.pair f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := treeErMorNSetoid k (n + m))
        (fun ctx => by
          simp only [
            TreeERMorN.interp_pair]
          funext i
          split_ifs with h
          · exact congrFun (hf ctx)
              ⟨i.val, h⟩
          · exact congrFun (hg ctx)
              ⟨i.val - n, by omega⟩))
    f g

/-- Composing pairing with the first projection
recovers the first component. -/
theorem TreeERMorNQuo.pair_fst {k n m : ℕ}
    (f : TreeERMorNQuo k n)
    (g : TreeERMorNQuo k m) :
    TreeERMorNQuo.comp
      (TreeERMorNQuo.pair f g)
      TreeERMorNQuo.fst = f :=
  Quotient.ind₂
    (motive := fun f g =>
      TreeERMorNQuo.comp
        (TreeERMorNQuo.pair f g)
        TreeERMorNQuo.fst = f)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := treeErMorNSetoid k n)
        (fun ctx => by
          simp only [
            TreeERMorN.interp_comp,
            TreeERMorN.interp_pair,
            TreeERMorN.interp_fst,
            Fin.is_lt, reduceDIte,
            Fin.eta]
          rfl))
    f g

/-- Composing pairing with the second projection
recovers the second component. -/
theorem TreeERMorNQuo.pair_snd {k n m : ℕ}
    (f : TreeERMorNQuo k n)
    (g : TreeERMorNQuo k m) :
    TreeERMorNQuo.comp
      (TreeERMorNQuo.pair f g)
      TreeERMorNQuo.snd = g :=
  Quotient.ind₂
    (motive := fun f g =>
      TreeERMorNQuo.comp
        (TreeERMorNQuo.pair f g)
        TreeERMorNQuo.snd = g)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := treeErMorNSetoid k m)
        (fun ctx => by
          simp only [
            TreeERMorN.interp_comp,
            TreeERMorN.interp_pair,
            TreeERMorN.interp_snd]
          funext i
          simp only [dif_neg
            (show ¬ (n + i.val) < n
              by omega)]
          change
            (g_raw ⟨n + i.val - n,
              _⟩).interp ctx =
              (g_raw i).interp ctx
          simp only [
            Nat.add_sub_cancel_left]))
    f g

/-- Uniqueness of pairing: any morphism whose
compositions with the projections yield `f` and
`g` equals `pair f g`. -/
theorem TreeERMorNQuo.pair_uniq {k n m : ℕ}
    (f : TreeERMorNQuo k n)
    (g : TreeERMorNQuo k m)
    (h : TreeERMorNQuo k (n + m))
    (hfst : TreeERMorNQuo.comp h
      TreeERMorNQuo.fst = f)
    (hsnd : TreeERMorNQuo.comp h
      TreeERMorNQuo.snd = g) :
    h = TreeERMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : TreeERMorNQuo k n)
        (g : TreeERMorNQuo k m),
        TreeERMorNQuo.comp h
          TreeERMorNQuo.fst = f →
        TreeERMorNQuo.comp h
          TreeERMorNQuo.snd = g →
        h = TreeERMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : TreeERMorNQuo k m),
            TreeERMorNQuo.comp
              (Quotient.mk _ h_raw)
              TreeERMorNQuo.fst = f →
            TreeERMorNQuo.comp
              (Quotient.mk _ h_raw)
              TreeERMorNQuo.snd = g →
            Quotient.mk _ h_raw =
              TreeERMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              TreeERMorNQuo.comp
                (Quotient.mk _ h_raw)
                TreeERMorNQuo.fst =
                Quotient.mk _ f_raw →
              TreeERMorNQuo.comp
                (Quotient.mk _ h_raw)
                TreeERMorNQuo.snd = g →
              Quotient.mk _ h_raw =
                TreeERMorNQuo.pair
                  (Quotient.mk _ f_raw)
                  g)
            (fun g_raw hf_eq hs_eq =>
              by
              have hf_rel :=
                Quotient.exact
                  (s :=
                    treeErMorNSetoid k n)
                  hf_eq
              have hs_rel :=
                Quotient.exact
                  (s :=
                    treeErMorNSetoid k m)
                  hs_eq
              apply Quotient.sound
                (s :=
                  treeErMorNSetoid
                    k (n + m))
              intro ctx
              simp only [
                TreeERMorN.interp_pair]
              funext i
              split_ifs with hlt
              · have := congrFun
                  (hf_rel ctx)
                  ⟨i.val, hlt⟩
                simp only [
                  TreeERMorN.interp_comp,
                  TreeERMorN.interp_fst
                ] at this
                exact this
              · have step := congrFun
                  (hs_rel ctx)
                  ⟨i.val - n, by omega⟩
                simp only [
                  TreeERMorN.interp_comp,
                  TreeERMorN.interp_snd
                ] at step
                have :
                  h_raw.interp ctx i =
                  h_raw.interp ctx
                    ⟨n + (i.val - n),
                      (by omega)⟩ := by
                  simp only [
                    Nat.add_sub_cancel'
                      (Nat.le_of_not_lt
                        hlt)]
                rw [this]
                exact step)))
    h f g hfst hsnd

/-- Chosen binary product for
`LawvereTreeERCat`: the product of `n` and `m`
is `n + m`. -/
def lawvereTreeERProduct
    (n m : LawvereTreeERCat) :
    ChosenBinaryProduct n m where
  obj := (n + m : ℕ)
  fst := TreeERMorNQuo.fst
  snd := TreeERMorNQuo.snd
  lift f g := TreeERMorNQuo.pair f g
  lift_fst := TreeERMorNQuo.pair_fst
  lift_snd := TreeERMorNQuo.pair_snd
  lift_uniq f g h hf hs :=
    TreeERMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for
`LawvereTreeERCat`. -/
def lawvereTreeERTerminal :
    ChosenTerminal LawvereTreeERCat where
  obj := (0 : ℕ)
  from_ n := TreeERMorNQuo.terminal n
  uniq f := TreeERMorNQuo.terminal_uniq f

/-- `LawvereTreeERCat` has chosen finite
products. -/
instance : HasChosenFiniteProducts
    LawvereTreeERCat where
  terminal := lawvereTreeERTerminal
  product := lawvereTreeERProduct

end GebLean
