import GebLean.LawvereER
import GebLean.LawvereERBool
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

/-!
# Finite-Limit Category of Decidable ER-Subobjects

Defines `LawvereERLexCat`, a category whose objects are
pairs of an arity and a Boolean-valued elementary
recursive predicate, and whose morphisms are equivalence
classes of `ERMorN` tuples respecting membership,
identified when they agree on every context satisfying
the source predicate.

This file covers the category skeleton only.  Finite
products, equalizers, and the full-and-faithful
embedding `LawvereERCat -> LawvereERLexCat` live in
subsequent modules.
-/

namespace GebLean

open CategoryTheory

/-- A Boolean-valued elementary recursive predicate:
an `ERMor1` term whose standard interpretation always
lies in `{0, 1}`.  Convention: `1 = true`, `0 = false`. -/
structure ERBoolPred (n : ℕ) where
  /-- The underlying predicate term. -/
  pred : ERMor1 n
  /-- Proof that the predicate is Boolean-valued. -/
  bool : ∀ ctx : Fin n → ℕ, pred.interp ctx ≤ 1

/-- Conjunction of two Boolean predicates at arities
`n` and `m`: yields a Boolean predicate at arity
`n + m` that holds when `p` holds on the first `n`
coordinates and `q` holds on the last `m`. -/
def ERBoolPred.and {n m : ℕ}
    (p : ERBoolPred n) (q : ERBoolPred m) :
    ERBoolPred (n + m) where
  pred :=
    ERMor1.comp ERMor1.boolAnd fun i =>
      match i with
      | ⟨0, _⟩ =>
          ERMor1.comp p.pred ERMorN.fst
      | ⟨1, _⟩ =>
          ERMor1.comp q.pred ERMorN.snd
  bool := fun ctx => by
    change ERMor1.boolAnd.interp _ ≤ 1
    rw [ERMor1.interp_boolAnd]
    exact
      (Nat.mul_le_mul
        (p.bool _) (q.bool _)).trans
        (Nat.le_refl 1)

/-- Interpretation of `ERBoolPred.and`: product of
the two predicates evaluated on the respective
coordinate slices. -/
@[simp] theorem ERBoolPred.and_interp
    {n m : ℕ} (p : ERBoolPred n)
    (q : ERBoolPred m)
    (ctx : Fin (n + m) → ℕ) :
    (ERBoolPred.and p q).pred.interp ctx =
      p.pred.interp (ERMorN.fst.interp ctx) *
      q.pred.interp (ERMorN.snd.interp ctx) := by
  change ERMor1.boolAnd.interp _ = _
  rw [ERMor1.interp_boolAnd]
  rfl

/-- Object of `LawvereERLexCat`: an arity together with
a Boolean-valued predicate cutting out a decidable
subobject of `Fin arity -> ℕ`. -/
structure LexObj where
  /-- The arity (number of free variables). -/
  arity : ℕ
  /-- The Boolean predicate. -/
  pred : ERBoolPred arity

/-- Raw morphism in `LawvereERLexCat`: an `ERMorN`
tuple that respects membership, that is, maps inputs
satisfying the source predicate to outputs satisfying
the target predicate. -/
def ERLexMorN (src tgt : LexObj) : Type :=
  { f : ERMorN src.arity tgt.arity //
      ∀ ctx : Fin src.arity → ℕ,
        src.pred.pred.interp ctx = 1 →
        tgt.pred.pred.interp (f.interp ctx) = 1 }

/-- The setoid on `ERLexMorN src tgt`: two raw
morphisms are related when their interpretations agree
on every context satisfying the source predicate. -/
def erLexMorNSetoid (src tgt : LexObj) :
    Setoid (ERLexMorN src tgt) where
  r f g :=
    ∀ ctx : Fin src.arity → ℕ,
      src.pred.pred.interp ctx = 1 →
      f.val.interp ctx = g.val.interp ctx
  iseqv := {
    refl := fun _ _ _ => rfl
    symm := fun h ctx hctx => (h ctx hctx).symm
    trans := fun h1 h2 ctx hctx =>
      (h1 ctx hctx).trans (h2 ctx hctx)
  }

/-- Quotient morphism type for `LawvereERLexCat`:
equivalence classes of `ERLexMorN` tuples under
source-restricted extensional equality. -/
def ERLexMorNQuo (src tgt : LexObj) : Type :=
  Quotient (erLexMorNSetoid src tgt)

/-- The raw identity morphism at `obj`: the
underlying tuple is `ERMorN.id obj.arity`, with
membership preserved because the identity function
on contexts fixes everything. -/
def ERLexMorN.id (obj : LexObj) : ERLexMorN obj obj :=
  ⟨ERMorN.id obj.arity, fun ctx hctx => by
    rw [ERMorN.interp_id]
    exact hctx⟩

/-- The identity morphism in the quotient category. -/
def ERLexMorNQuo.id (obj : LexObj) :
    ERLexMorNQuo obj obj :=
  Quotient.mk (erLexMorNSetoid obj obj)
    (ERLexMorN.id obj)

/-- Raw composition of `ERLexMorN` morphisms: the
underlying tuple is the `ERMorN.comp` of the two
underlying tuples; membership follows by chaining the
respective respect proofs through the interpretation
of the composite. -/
def ERLexMorN.comp
    {src mid tgt : LexObj}
    (f : ERLexMorN src mid)
    (g : ERLexMorN mid tgt) :
    ERLexMorN src tgt :=
  ⟨ERMorN.comp f.val g.val, fun ctx hctx => by
    rw [ERMorN.interp_comp]
    exact g.property _ (f.property ctx hctx)⟩

/-- Composition of quotient morphisms, lifted from
`ERLexMorN.comp` via `Quotient.lift₂`.
Well-definedness: given `f ~ f'` and `g ~ g'` under
the source-restricted setoid, the composites agree on
every context satisfying the source predicate. -/
def ERLexMorNQuo.comp
    {src mid tgt : LexObj}
    (f : ERLexMorNQuo src mid)
    (g : ERLexMorNQuo mid tgt) :
    ERLexMorNQuo src tgt :=
  Quotient.lift₂
    (s₁ := erLexMorNSetoid src mid)
    (s₂ := erLexMorNSetoid mid tgt)
    (fun f' g' =>
      Quotient.mk (erLexMorNSetoid src tgt)
        (ERLexMorN.comp f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erLexMorNSetoid src tgt)
        (fun ctx hctx => by
          simp only [ERLexMorN.comp,
            ERMorN.interp_comp]
          rw [hf ctx hctx]
          exact hg _ (ga.property ctx hctx)))
    f g

/-- Left identity: `comp (id src) f = f`. -/
theorem ERLexMorNQuo.id_comp
    {src tgt : LexObj}
    (f : ERLexMorNQuo src tgt) :
    ERLexMorNQuo.comp (ERLexMorNQuo.id src) f = f :=
  Quotient.ind
    (motive := fun f =>
      ERLexMorNQuo.comp
        (ERLexMorNQuo.id src) f = f)
    (fun f_raw =>
      Quotient.sound
        (s := erLexMorNSetoid src tgt)
        (fun ctx _ => by
          simp only [ERLexMorN.comp,
            ERLexMorN.id,
            ERMorN.interp_comp,
            ERMorN.interp_id]))
    f

/-- Right identity: `comp f (id tgt) = f`. -/
theorem ERLexMorNQuo.comp_id
    {src tgt : LexObj}
    (f : ERLexMorNQuo src tgt) :
    ERLexMorNQuo.comp f (ERLexMorNQuo.id tgt) = f :=
  Quotient.ind
    (motive := fun f =>
      ERLexMorNQuo.comp
        f (ERLexMorNQuo.id tgt) = f)
    (fun f_raw =>
      Quotient.sound
        (s := erLexMorNSetoid src tgt)
        (fun ctx _ => by
          simp only [ERLexMorN.comp,
            ERLexMorN.id,
            ERMorN.interp_comp,
            ERMorN.interp_id]))
    f

/-- Associativity of composition. -/
theorem ERLexMorNQuo.comp_assoc
    {a b c d : LexObj}
    (f : ERLexMorNQuo a b)
    (g : ERLexMorNQuo b c)
    (h : ERLexMorNQuo c d) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.comp f g) h =
    ERLexMorNQuo.comp f
      (ERLexMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      ∀ (g : ERLexMorNQuo b c)
        (h : ERLexMorNQuo c d),
        ERLexMorNQuo.comp
          (ERLexMorNQuo.comp f g) h =
        ERLexMorNQuo.comp f
          (ERLexMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          ∀ (h : ERLexMorNQuo c d),
            ERLexMorNQuo.comp
              (ERLexMorNQuo.comp
                (Quotient.mk _ f_raw) g) h =
            ERLexMorNQuo.comp
              (Quotient.mk _ f_raw)
              (ERLexMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              ERLexMorNQuo.comp
                (ERLexMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (Quotient.mk _ g_raw)) h =
              ERLexMorNQuo.comp
                (Quotient.mk _ f_raw)
                (ERLexMorNQuo.comp
                  (Quotient.mk _ g_raw) h))
            (fun h_raw =>
              Quotient.sound
                (s := erLexMorNSetoid a d)
                (fun ctx _ => by
                  simp only [ERLexMorN.comp,
                    ERMorN.interp_comp]))))
    f g h

/-- The finite-limit category of decidable
ER-subobjects.  Objects are `LexObj`s; morphisms are
equivalence classes of `ERLexMorN` tuples.  Finite
products, equalizers, and the embedding from
`LawvereERCat` are developed in subsequent
modules. -/
@[reducible] def LawvereERLexCat := LexObj

instance : CategoryStruct LawvereERLexCat where
  Hom := ERLexMorNQuo
  id obj := ERLexMorNQuo.id obj
  comp f g := ERLexMorNQuo.comp f g

instance : Category LawvereERLexCat where
  id_comp := ERLexMorNQuo.id_comp
  comp_id := ERLexMorNQuo.comp_id
  assoc := ERLexMorNQuo.comp_assoc

end GebLean
