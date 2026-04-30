import GebLean.LawvereKSimInterp
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

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

/-- Terminal morphism in the quotient category:
the equivalence class of the empty tuple. -/
def KMorNQuo.terminal (n : ℕ) : KMorNQuo n 0 :=
  Quotient.mk (kMorNSetoid n 0) (KMorN.terminal n)

/-- Any quotient morphism to arity 0 equals the
terminal morphism. -/
theorem KMorNQuo.terminal_uniq {n : ℕ}
    (f : KMorNQuo n 0) :
    f = KMorNQuo.terminal n :=
  Quotient.ind
    (motive := fun f =>
      f = KMorNQuo.terminal n)
    (fun _ => Quotient.sound
      (s := kMorNSetoid n 0)
      (fun _ => funext
        (fun i => Fin.elim0 i)))
    f

/-- First projection in the quotient category. -/
def KMorNQuo.fst {n m : ℕ} :
    KMorNQuo (n + m) n :=
  Quotient.mk (kMorNSetoid (n + m) n) KMorN.fst

/-- Second projection in the quotient category. -/
def KMorNQuo.snd {n m : ℕ} :
    KMorNQuo (n + m) m :=
  Quotient.mk (kMorNSetoid (n + m) m) KMorN.snd

/-- Pairing in the quotient category, lifted from
`KMorN.pair` via `Quotient.lift₂`. -/
def KMorNQuo.pair {k n m : ℕ}
    (f : KMorNQuo k n) (g : KMorNQuo k m) :
    KMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := kMorNSetoid k n)
    (s₂ := kMorNSetoid k m)
    (fun f' g' =>
      Quotient.mk (kMorNSetoid k (n + m))
        (KMorN.pair f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := kMorNSetoid k (n + m))
        (fun ctx => by
          simp only [KMorN.interp_pair]
          funext i
          split_ifs with h
          · exact congrFun (hf ctx) ⟨i.val, h⟩
          · exact congrFun (hg ctx)
              ⟨i.val - n, by omega⟩))
    f g

/-- Composing pairing with the first projection
recovers the first component. -/
theorem KMorNQuo.pair_fst {k n m : ℕ}
    (f : KMorNQuo k n) (g : KMorNQuo k m) :
    KMorNQuo.comp (KMorNQuo.pair f g)
        (KMorNQuo.fst (n := n) (m := m)) = f :=
  Quotient.ind₂
    (motive := fun f g =>
      KMorNQuo.comp (KMorNQuo.pair f g)
          (KMorNQuo.fst (n := n) (m := m)) = f)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := kMorNSetoid k n)
        (fun ctx => by
          funext j
          simp only [KMorN.interp_comp,
            KMorN.interp_pair, KMorN.interp_fst]
          have hlt : (Fin.castAdd m j).val < n :=
            j.is_lt
          rw [dif_pos hlt]
          rfl))
    f g

/-- Composing pairing with the second projection
recovers the second component. -/
theorem KMorNQuo.pair_snd {k n m : ℕ}
    (f : KMorNQuo k n) (g : KMorNQuo k m) :
    KMorNQuo.comp (KMorNQuo.pair f g)
        (KMorNQuo.snd (n := n) (m := m)) = g :=
  Quotient.ind₂
    (motive := fun f g =>
      KMorNQuo.comp (KMorNQuo.pair f g)
          (KMorNQuo.snd (n := n) (m := m)) = g)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := kMorNSetoid k m)
        (fun ctx => by
          funext j
          simp only [KMorN.interp_comp,
            KMorN.interp_pair, KMorN.interp_snd]
          have hge : ¬ (Fin.natAdd n j).val < n :=
            by simp [Fin.natAdd]
          rw [dif_neg hge]
          congr 1
          ext
          simp [Fin.natAdd, Nat.add_sub_cancel_left]))
    f g

/-- Uniqueness of pairing: any morphism whose
compositions with the projections yield `f` and
`g` equals `pair f g`. -/
theorem KMorNQuo.pair_uniq {k n m : ℕ}
    (f : KMorNQuo k n)
    (g : KMorNQuo k m)
    (h : KMorNQuo k (n + m))
    (hfst : KMorNQuo.comp h
        (KMorNQuo.fst (n := n) (m := m)) = f)
    (hsnd : KMorNQuo.comp h
        (KMorNQuo.snd (n := n) (m := m)) = g) :
    h = KMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : KMorNQuo k n)
        (g : KMorNQuo k m),
        KMorNQuo.comp h
            (KMorNQuo.fst (n := n) (m := m)) = f →
        KMorNQuo.comp h
            (KMorNQuo.snd (n := n) (m := m)) = g →
        h = KMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : KMorNQuo k m),
            KMorNQuo.comp
              (Quotient.mk _ h_raw)
              (KMorNQuo.fst (n := n) (m := m)) = f →
            KMorNQuo.comp
              (Quotient.mk _ h_raw)
              (KMorNQuo.snd (n := n) (m := m)) = g →
            Quotient.mk _ h_raw =
              KMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              KMorNQuo.comp
                (Quotient.mk _ h_raw)
                (KMorNQuo.fst (n := n) (m := m)) =
                Quotient.mk _ f_raw →
              KMorNQuo.comp
                (Quotient.mk _ h_raw)
                (KMorNQuo.snd (n := n) (m := m)) = g →
              Quotient.mk _ h_raw =
                KMorNQuo.pair
                  (Quotient.mk _ f_raw) g)
            (fun g_raw hf_eq hs_eq => by
              have hf_rel :=
                Quotient.exact
                  (s := kMorNSetoid k n)
                  hf_eq
              have hs_rel :=
                Quotient.exact
                  (s := kMorNSetoid k m)
                  hs_eq
              apply Quotient.sound
                (s := kMorNSetoid k (n + m))
              intro ctx
              simp only [KMorN.interp_pair]
              funext i
              split_ifs with hlt
              · have := congrFun
                  (hf_rel ctx) ⟨i.val, hlt⟩
                simp only [KMorN.interp_comp,
                  KMorN.interp_fst] at this
                exact this
              · have step := congrFun
                  (hs_rel ctx)
                  ⟨i.val - n, by omega⟩
                simp only [KMorN.interp_comp,
                  KMorN.interp_snd] at step
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

/-- Chosen binary product for `LawvereKSimCat`:
the product of `n` and `m` is `n + m`. -/
def lawvereKSimProduct
    (n m : LawvereKSimCat) :
    ChosenBinaryProduct n m where
  obj := (Nat.add n m : ℕ)
  fst := KMorNQuo.fst
  snd := KMorNQuo.snd
  lift f g := KMorNQuo.pair f g
  lift_fst := KMorNQuo.pair_fst
  lift_snd := KMorNQuo.pair_snd
  lift_uniq f g h hf hs :=
    KMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for
`LawvereKSimCat`. -/
def lawvereKSimTerminal :
    ChosenTerminal LawvereKSimCat where
  obj := (0 : ℕ)
  from_ n := KMorNQuo.terminal n
  uniq f := KMorNQuo.terminal_uniq f

/-- `LawvereKSimCat` has chosen finite
products. -/
instance : HasChosenFiniteProducts
    LawvereKSimCat where
  terminal := lawvereKSimTerminal
  product := lawvereKSimProduct

/-- The `KMorNQuo n m` class admits a syntactic
representative at depth ≤ d iff some `KMorN n m`
representative has each of its components at
`KMor1.level ≤ d`. -/
def KMorNQuo.atDepth {n m : ℕ} (d : ℕ)
    (q : KMorNQuo n m) : Prop :=
  ∃ f : KMorN n m,
    (∀ i : Fin m, (f i).level ≤ d) ∧
    Quotient.mk (kMorNSetoid n m) f = q

theorem KMorNQuo.id_atDepth {n d : ℕ} :
    KMorNQuo.atDepth d (KMorNQuo.id n) := by
  refine ⟨KMorN.id n, ?_, rfl⟩
  intro i
  simp [KMorN.id, KMor1.level]

theorem KMorNQuo.comp_atDepth
    {n m k d : ℕ}
    (f : KMorNQuo n m) (g : KMorNQuo m k)
    (hf : KMorNQuo.atDepth d f)
    (hg : KMorNQuo.atDepth d g) :
    KMorNQuo.atDepth d (KMorNQuo.comp f g) := by
  obtain ⟨f', hf_lvl, hf_eq⟩ := hf
  obtain ⟨g', hg_lvl, hg_eq⟩ := hg
  refine ⟨KMorN.comp g' f', ?_, ?_⟩
  · intro i
    simp only [KMorN.comp, KMor1.level]
    apply Nat.max_le.mpr
    constructor
    · exact hg_lvl i
    · apply Finset.sup_le
      intro j _
      exact hf_lvl j
  · rw [← hf_eq, ← hg_eq]
    rfl

/-- The K^sim_d category at depth d: morphisms are
`KMorNQuo` quotient classes admitting a level-≤-d
representative.  Per design principle P4. -/
structure KSimMor (d : ℕ) (n m : ℕ) where
  hom : KMorNQuo n m
  depth_witness : KMorNQuo.atDepth d hom

/-- The depth-d K^sim category has the same objects as
`LawvereKSimCat` but restricts to KSimMor d morphisms.
The depth `d` is a phantom-type parameter so that
`Category` instances are distinguishable per depth via
typeclass resolution. -/
def LawvereKSimDCat (_d : ℕ) := ℕ

instance (d n : ℕ) : OfNat (LawvereKSimDCat d) n :=
  ⟨(n : ℕ)⟩

instance (d : ℕ) : DecidableEq (LawvereKSimDCat d) :=
  inferInstanceAs (DecidableEq ℕ)

instance (d : ℕ) :
    CategoryTheory.CategoryStruct
      (LawvereKSimDCat d) where
  Hom n m := KSimMor d n m
  id n := ⟨KMorNQuo.id n, KMorNQuo.id_atDepth⟩
  comp f g :=
    ⟨KMorNQuo.comp f.hom g.hom,
     KMorNQuo.comp_atDepth f.hom g.hom
       f.depth_witness g.depth_witness⟩

/-- An extensionality lemma reducing `KSimMor`
equality to `hom`-field equality (since
`depth_witness` is `Prop`-valued and
proof-irrelevant). -/
@[ext] theorem KSimMor.ext {d n m : ℕ}
    {x y : KSimMor d n m} (h : x.hom = y.hom) :
    x = y := by
  cases x; cases y
  congr

instance (d : ℕ) :
    CategoryTheory.Category (LawvereKSimDCat d) where
  id_comp f := by
    apply KSimMor.ext
    exact KMorNQuo.id_comp f.hom
  comp_id f := by
    apply KSimMor.ext
    exact KMorNQuo.comp_id f.hom
  assoc f g h := by
    apply KSimMor.ext
    exact KMorNQuo.comp_assoc f.hom g.hom h.hom

/-- The inclusion functor weakening the depth from
`d` to `d+1`.  On objects it is the identity (both
categories have the same `ℕ`-shaped object
collection); on morphisms it forwards the underlying
`KMorNQuo` and weakens the depth witness via
monotonicity. -/
def KSimMor.includeSucc (d : ℕ) :
    CategoryTheory.Functor
      (LawvereKSimDCat d)
      (LawvereKSimDCat (d + 1)) where
  obj n := n
  map {n m} h :=
    ⟨h.hom, by
      obtain ⟨f, hf_lvl, hf_eq⟩ := h.depth_witness
      exact ⟨f,
        fun i => Nat.le_succ_of_le (hf_lvl i),
        hf_eq⟩⟩
  map_id _ := KSimMor.ext rfl
  map_comp _ _ := KSimMor.ext rfl

end GebLean
