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

/-- The always-true predicate at arity `n`: the
constant `1` function, trivially Boolean-valued. -/
def ERBoolPred.alwaysTrueN (n : ℕ) :
    ERBoolPred n where
  pred := ERMor1.oneN n
  bool := fun _ => Nat.le_refl 1

/-- Interpretation of `alwaysTrueN`: always `1`. -/
@[simp] theorem ERBoolPred.alwaysTrueN_interp
    (n : ℕ) (ctx : Fin n → ℕ) :
    (ERBoolPred.alwaysTrueN n).pred.interp ctx =
      1 :=
  rfl

/-- Conjunction of two Boolean predicates at the
same arity: composes `boolAnd` with the two
predicates as its inputs. -/
def ERBoolPred.andSameArity {n : ℕ}
    (p q : ERBoolPred n) : ERBoolPred n where
  pred :=
    ERMor1.comp ERMor1.boolAnd fun i =>
      match i with
      | ⟨0, _⟩ => p.pred
      | ⟨1, _⟩ => q.pred
  bool := fun ctx => by
    change ERMor1.boolAnd.interp _ ≤ 1
    rw [ERMor1.interp_boolAnd]
    exact
      (Nat.mul_le_mul
        (p.bool _) (q.bool _)).trans
        (Nat.le_refl 1)

/-- Interpretation of `andSameArity`: product of
the two predicate interpretations. -/
@[simp] theorem ERBoolPred.andSameArity_interp
    {n : ℕ} (p q : ERBoolPred n)
    (ctx : Fin n → ℕ) :
    (ERBoolPred.andSameArity p q).pred.interp
        ctx =
      p.pred.interp ctx * q.pred.interp ctx := by
  change ERMor1.boolAnd.interp _ = _
  rw [ERMor1.interp_boolAnd]

/-- Componentwise Boolean equality of two `ERMorN`
tuples at arity `n`: returns a Boolean predicate
at arity `n` that holds iff the two tuples have
equal interpretations. -/
def ERBoolPred.allEq {n : ℕ} :
    ∀ {m : ℕ}, ERMorN n m → ERMorN n m →
      ERBoolPred n
  | 0, _, _ => ERBoolPred.alwaysTrueN n
  | k + 1, f, g =>
      ERBoolPred.andSameArity
        { pred := ERMor1.boolEqAt (f 0) (g 0)
          bool := ERMor1.boolEqAt_le_one _ _ }
        (ERBoolPred.allEq
          (fun i : Fin k => f i.succ)
          (fun i : Fin k => g i.succ))

/-- Forward direction: if `allEq f g` evaluates to
`1` on a context, then `f` and `g` interpret to the
same function at that context. -/
theorem ERBoolPred.allEq_eq_one_imp
    {n : ℕ} : ∀ {m : ℕ} (f g : ERMorN n m)
      (ctx : Fin n → ℕ),
      (ERBoolPred.allEq f g).pred.interp ctx = 1 →
        f.interp ctx = g.interp ctx
  | 0, _, _, _, _ => funext (fun i => i.elim0)
  | k + 1, f, g, ctx, h => by
      simp only [ERBoolPred.allEq,
        ERBoolPred.andSameArity_interp] at h
      have h_split := mul_eq_one.mp h
      have h_head := h_split.1
      have h_tail := h_split.2
      have eq_head :
          (f 0).interp ctx = (g 0).interp ctx :=
        (ERMor1.boolEqAt_eq_one_iff _ _ _).mp
          h_head
      have eq_tail :
          ERMorN.interp
            (fun i : Fin k => f i.succ) ctx =
          ERMorN.interp
            (fun i : Fin k => g i.succ) ctx :=
        ERBoolPred.allEq_eq_one_imp _ _ _ h_tail
      funext i
      induction i using Fin.cases with
      | zero => exact eq_head
      | succ j =>
        exact congrFun eq_tail j

/-- Backward direction: if `f` and `g` interpret to
the same function at a context, then `allEq f g`
evaluates to `1` there. -/
theorem ERBoolPred.allEq_of_eq
    {n : ℕ} : ∀ {m : ℕ} (f g : ERMorN n m)
      (ctx : Fin n → ℕ),
      f.interp ctx = g.interp ctx →
        (ERBoolPred.allEq f g).pred.interp ctx = 1
  | 0, _, _, _, _ => by
      simp [ERBoolPred.allEq]
  | k + 1, f, g, ctx, h => by
      simp only [ERBoolPred.allEq,
        ERBoolPred.andSameArity_interp]
      have eq0 : (f 0).interp ctx =
          (g 0).interp ctx := congrFun h 0
      have eq_tail :
          ERMorN.interp
            (fun i : Fin k => f i.succ) ctx =
          ERMorN.interp
            (fun i : Fin k => g i.succ) ctx := by
        funext j
        exact congrFun h j.succ
      rw [(ERMor1.boolEqAt_eq_one_iff _ _ _).mpr
          eq0]
      rw [ERBoolPred.allEq_of_eq _ _ _ eq_tail]

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

/-- Terminal object of `LawvereERLexCat`: arity `0`
with the constant-`1` predicate. -/
def LexObj.terminal : LexObj where
  arity := 0
  pred := ERBoolPred.alwaysTrueN 0

/-- The raw terminal morphism from any object to
`LexObj.terminal`: underlying tuple is the empty
tuple; membership is trivially preserved because
the target predicate is always `1`. -/
def ERLexMorN.toTerminal (obj : LexObj) :
    ERLexMorN obj LexObj.terminal :=
  ⟨ERMorN.terminal obj.arity, fun _ _ => rfl⟩

/-- The terminal morphism in the quotient category. -/
def ERLexMorNQuo.toTerminal (obj : LexObj) :
    ERLexMorNQuo obj LexObj.terminal :=
  Quotient.mk (erLexMorNSetoid obj LexObj.terminal)
    (ERLexMorN.toTerminal obj)

/-- Uniqueness of the terminal morphism: any quotient
morphism to `LexObj.terminal` equals
`ERLexMorNQuo.toTerminal`. -/
theorem ERLexMorNQuo.toTerminal_uniq
    {obj : LexObj}
    (f : ERLexMorNQuo obj LexObj.terminal) :
    f = ERLexMorNQuo.toTerminal obj :=
  Quotient.ind
    (motive := fun f =>
      f = ERLexMorNQuo.toTerminal obj)
    (fun _ => Quotient.sound
      (s := erLexMorNSetoid obj LexObj.terminal)
      (fun _ _ => funext (fun i => i.elim0)))
    f

/-- Binary product object in `LawvereERLexCat`: the
product of `(n, p)` and `(m, q)` is `(n + m, p ⊓ q)`
where `⊓` is the conjunction of predicates extended
along the projections. -/
def LexObj.prod (a b : LexObj) : LexObj where
  arity := a.arity + b.arity
  pred := ERBoolPred.and a.pred b.pred

/-- First projection from the product `a × b` to `a`.
Underlying tuple: `ERMorN.fst`.  Membership
preservation: from `(a.pred ⊓ b.pred)(ctx) = 1`,
deduce `a.pred(first n of ctx) = 1` via
`Nat.mul_eq_one`. -/
def ERLexMorN.pi1 (a b : LexObj) :
    ERLexMorN (LexObj.prod a b) a :=
  ⟨ERMorN.fst, fun ctx hctx => by
    change (ERBoolPred.and a.pred b.pred).pred.interp
      ctx = 1 at hctx
    rw [ERBoolPred.and_interp] at hctx
    exact (mul_eq_one.mp hctx).1⟩

/-- Second projection from the product `a × b` to
`b`. -/
def ERLexMorN.pi2 (a b : LexObj) :
    ERLexMorN (LexObj.prod a b) b :=
  ⟨ERMorN.snd, fun ctx hctx => by
    change (ERBoolPred.and a.pred b.pred).pred.interp
      ctx = 1 at hctx
    rw [ERBoolPred.and_interp] at hctx
    exact (mul_eq_one.mp hctx).2⟩

/-- First projection in the quotient category. -/
def ERLexMorNQuo.pi1 (a b : LexObj) :
    ERLexMorNQuo (LexObj.prod a b) a :=
  Quotient.mk (erLexMorNSetoid (LexObj.prod a b) a)
    (ERLexMorN.pi1 a b)

/-- Second projection in the quotient category. -/
def ERLexMorNQuo.pi2 (a b : LexObj) :
    ERLexMorNQuo (LexObj.prod a b) b :=
  Quotient.mk (erLexMorNSetoid (LexObj.prod a b) b)
    (ERLexMorN.pi2 a b)

/-- Pairing in `LawvereERLexCat`: given `f : z → a`
and `g : z → b`, produces the universal arrow
`z → a × b`.  Underlying tuple: `ERMorN.pair f.val
g.val`.  Membership preservation: when `z.pred(ctx)
= 1`, both `a.pred(f.val.interp ctx) = 1` and
`b.pred(g.val.interp ctx) = 1`, so their product is
`1`. -/
def ERLexMorN.pair {z a b : LexObj}
    (f : ERLexMorN z a) (g : ERLexMorN z b) :
    ERLexMorN z (LexObj.prod a b) :=
  ⟨ERMorN.pair f.val g.val, fun ctx hctx => by
    change (ERBoolPred.and a.pred b.pred).pred.interp
      _ = 1
    rw [ERBoolPred.and_interp]
    have hf : a.pred.pred.interp
        (ERMorN.fst.interp
          ((ERMorN.pair f.val g.val).interp ctx)) =
        1 := by
      have step : ERMorN.fst.interp
          ((ERMorN.pair f.val g.val).interp ctx) =
          f.val.interp ctx := by
        funext i
        simp only [ERMorN.interp_fst,
          ERMorN.interp_pair]
        rw [dif_pos i.isLt]
        rfl
      rw [step]
      exact f.property ctx hctx
    have hg : b.pred.pred.interp
        (ERMorN.snd.interp
          ((ERMorN.pair f.val g.val).interp ctx)) =
        1 := by
      have step : ERMorN.snd.interp
          ((ERMorN.pair f.val g.val).interp ctx) =
          g.val.interp ctx := by
        funext i
        simp only [ERMorN.interp_snd,
          ERMorN.interp_pair]
        have h : ¬ (a.arity + i.val) < a.arity := by
          omega
        rw [dif_neg h]
        have idx_eq :
            (⟨a.arity + i.val - a.arity, by omega⟩
              : Fin b.arity) = i := by
          apply Fin.ext
          change a.arity + i.val - a.arity = i.val
          omega
        rw [idx_eq]
        rfl
      rw [step]
      exact g.property ctx hctx
    rw [hf, hg]⟩

/-- Pairing of quotient morphisms, lifted from
`ERLexMorN.pair` via `Quotient.lift₂`.
Well-definedness follows from source-restricted
extensional equality of components. -/
def ERLexMorNQuo.pair {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b) :
    ERLexMorNQuo z (LexObj.prod a b) :=
  Quotient.lift₂
    (s₁ := erLexMorNSetoid z a)
    (s₂ := erLexMorNSetoid z b)
    (fun f' g' =>
      Quotient.mk
        (erLexMorNSetoid z (LexObj.prod a b))
        (ERLexMorN.pair f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erLexMorNSetoid z (LexObj.prod a b))
        (fun ctx hctx => by
          change (ERMorN.pair fa.val fb.val).interp
            ctx = (ERMorN.pair ga.val gb.val).interp
            ctx
          funext i
          simp only [ERMorN.interp_pair]
          split_ifs with h
          · exact congrFun (hf ctx hctx)
              ⟨i.val, h⟩
          · exact congrFun (hg ctx hctx)
              ⟨i.val - a.arity, by omega⟩))
    f g

/-- Composing pairing with the first projection
recovers the first component. -/
theorem ERLexMorNQuo.pair_pi1 {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b) :
    ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
      (ERLexMorNQuo.pi1 a b) = f :=
  Quotient.ind₂
    (motive := fun f g =>
      ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
        (ERLexMorNQuo.pi1 a b) = f)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erLexMorNSetoid z a)
        (fun ctx _ => by
          change (ERMorN.comp
              (ERMorN.pair f_raw.val g_raw.val)
              ERMorN.fst).interp ctx =
              f_raw.val.interp ctx
          funext i
          simp only [ERMorN.interp_comp,
            ERMorN.interp_fst,
            ERMorN.interp_pair]
          rw [dif_pos i.isLt]
          rfl))
    f g

/-- Composing pairing with the second projection
recovers the second component. -/
theorem ERLexMorNQuo.pair_pi2 {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b) :
    ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
      (ERLexMorNQuo.pi2 a b) = g :=
  Quotient.ind₂
    (motive := fun f g =>
      ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
        (ERLexMorNQuo.pi2 a b) = g)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erLexMorNSetoid z b)
        (fun ctx _ => by
          change (ERMorN.comp
              (ERMorN.pair f_raw.val g_raw.val)
              ERMorN.snd).interp ctx =
              g_raw.val.interp ctx
          funext i
          simp only [ERMorN.interp_comp,
            ERMorN.interp_snd,
            ERMorN.interp_pair]
          have h : ¬ (a.arity + i.val) < a.arity :=
            by omega
          rw [dif_neg h]
          have idx_eq :
              (⟨a.arity + i.val - a.arity,
                by omega⟩ : Fin b.arity) = i := by
            apply Fin.ext
            change a.arity + i.val - a.arity =
              i.val
            omega
          rw [idx_eq]
          rfl))
    f g

/-- Uniqueness of pairing: any morphism `h : z →
a × b` whose compositions with the projections yield
`f` and `g` equals `pair f g`. -/
theorem ERLexMorNQuo.pair_uniq {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b)
    (h : ERLexMorNQuo z (LexObj.prod a b))
    (hf : ERLexMorNQuo.comp h
      (ERLexMorNQuo.pi1 a b) = f)
    (hg : ERLexMorNQuo.comp h
      (ERLexMorNQuo.pi2 a b) = g) :
    h = ERLexMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : ERLexMorNQuo z a)
        (g : ERLexMorNQuo z b),
        ERLexMorNQuo.comp h
          (ERLexMorNQuo.pi1 a b) = f →
        ERLexMorNQuo.comp h
          (ERLexMorNQuo.pi2 a b) = g →
        h = ERLexMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : ERLexMorNQuo z b),
            ERLexMorNQuo.comp
              (Quotient.mk _ h_raw)
              (ERLexMorNQuo.pi1 a b) = f →
            ERLexMorNQuo.comp
              (Quotient.mk _ h_raw)
              (ERLexMorNQuo.pi2 a b) = g →
            Quotient.mk _ h_raw =
              ERLexMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              ERLexMorNQuo.comp
                (Quotient.mk _ h_raw)
                (ERLexMorNQuo.pi1 a b) =
                Quotient.mk _ f_raw →
              ERLexMorNQuo.comp
                (Quotient.mk _ h_raw)
                (ERLexMorNQuo.pi2 a b) = g →
              Quotient.mk _ h_raw =
                ERLexMorNQuo.pair
                  (Quotient.mk _ f_raw) g)
            (fun g_raw hf_eq hg_eq => by
              have hf_rel :=
                Quotient.exact
                  (s := erLexMorNSetoid z a)
                  hf_eq
              have hg_rel :=
                Quotient.exact
                  (s := erLexMorNSetoid z b)
                  hg_eq
              apply Quotient.sound
                (s := erLexMorNSetoid z
                  (LexObj.prod a b))
              intro ctx hctx
              change h_raw.val.interp ctx =
                (ERMorN.pair f_raw.val
                  g_raw.val).interp ctx
              funext i
              simp only [ERMorN.interp_pair]
              split_ifs with hlt
              · have hstep := congrFun
                  (hf_rel ctx hctx)
                  ⟨i.val, hlt⟩
                simp only [ERLexMorN.comp,
                  ERLexMorN.pi1,
                  ERMorN.interp_comp,
                  ERMorN.interp_fst] at hstep
                exact hstep
              · have hstep := congrFun
                  (hg_rel ctx hctx)
                  ⟨i.val - a.arity, by omega⟩
                simp only [ERLexMorN.comp,
                  ERLexMorN.pi2,
                  ERMorN.interp_comp,
                  ERMorN.interp_snd] at hstep
                have idx_eq :
                    (⟨a.arity +
                        (i.val - a.arity),
                      by omega⟩ :
                    Fin (a.arity + b.arity)) =
                    i := by
                  apply Fin.ext
                  change
                    a.arity +
                      (i.val - a.arity) = i.val
                  omega
                rw [idx_eq] at hstep
                exact hstep)))
    h f g hf hg

/-- Equalizer object for parallel morphisms
`f, g : a → b` (at the raw `ERLexMorN` level):
the same arity as `a`, with predicate augmented
by componentwise equality of `f` and `g`. -/
def LexObj.equalizer {a b : LexObj}
    (f g : ERLexMorN a b) : LexObj where
  arity := a.arity
  pred :=
    ERBoolPred.andSameArity a.pred
      (ERBoolPred.allEq f.val g.val)

/-- The equalizer inclusion morphism: underlying
tuple is the identity, with respect proof
extracting `a.pred = 1` from the equalizer
predicate. -/
def ERLexMorN.equalizerMap {a b : LexObj}
    (f g : ERLexMorN a b) :
    ERLexMorN (LexObj.equalizer f g) a :=
  ⟨ERMorN.id a.arity, fun ctx hctx => by
    change (ERBoolPred.andSameArity a.pred
        (ERBoolPred.allEq f.val g.val)).pred.interp
        ctx = 1 at hctx
    rw [ERBoolPred.andSameArity_interp] at hctx
    change a.pred.pred.interp ctx = 1
    exact (mul_eq_one.mp hctx).1⟩

/-- The equalizer inclusion morphism in the
quotient category. -/
def ERLexMorNQuo.equalizerMap {a b : LexObj}
    (f g : ERLexMorN a b) :
    ERLexMorNQuo (LexObj.equalizer f g) a :=
  Quotient.mk
    (erLexMorNSetoid (LexObj.equalizer f g) a)
    (ERLexMorN.equalizerMap f g)

/-- Chosen binary product structure for
`LawvereERLexCat`: the product of `a` and `b` is
`LexObj.prod a b`. -/
def lawvereERLexProduct
    (a b : LawvereERLexCat) :
    ChosenBinaryProduct a b where
  obj := LexObj.prod a b
  fst := ERLexMorNQuo.pi1 a b
  snd := ERLexMorNQuo.pi2 a b
  lift f g := ERLexMorNQuo.pair f g
  lift_fst := ERLexMorNQuo.pair_pi1
  lift_snd := ERLexMorNQuo.pair_pi2
  lift_uniq f g h hf hs :=
    ERLexMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for `LawvereERLexCat`. -/
def lawvereERLexTerminal :
    ChosenTerminal LawvereERLexCat where
  obj := LexObj.terminal
  from_ obj := ERLexMorNQuo.toTerminal obj
  uniq f := ERLexMorNQuo.toTerminal_uniq f

/-- `LawvereERLexCat` has chosen finite products. -/
instance : HasChosenFiniteProducts
    LawvereERLexCat where
  terminal := lawvereERLexTerminal
  product := lawvereERLexProduct

end GebLean
