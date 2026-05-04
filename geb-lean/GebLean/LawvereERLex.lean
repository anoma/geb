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

/-- Extensional equality on `ERBoolPred n`: two
predicates are related when their underlying
interpretations agree on every context.  This is
the relation we quotient by to obtain a predicate
type whose equality matches the categorical notion
of "same subobject". -/
def ERBoolPred.ExtEq (n : ℕ) :
    Setoid (ERBoolPred n) where
  r p q := ∀ ctx : Fin n → ℕ,
    p.pred.interp ctx = q.pred.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }

/-- Quotient of `ERBoolPred n` by extensional
equality.  Used as the predicate type of `LexObj`
so that semantically equal predicates yield equal
objects. -/
@[reducible] def ERBoolPredE (n : ℕ) : Type :=
  Quotient (ERBoolPred.ExtEq n)

/-- Lift the interpretation through the quotient:
evaluate a `ERBoolPredE` predicate on a context.
Well-defined because the setoid identifies
predicates with equal interpretations. -/
def ERBoolPredE.eval {n : ℕ}
    (p : ERBoolPredE n) (ctx : Fin n → ℕ) : ℕ :=
  Quotient.liftOn p
    (fun p' => p'.pred.interp ctx)
    (fun _ _ h => h ctx)

/-- The eval of a `ERBoolPredE` is bounded by `1`:
this is the lifted Boolean property. -/
theorem ERBoolPredE.eval_le_one {n : ℕ}
    (p : ERBoolPredE n) (ctx : Fin n → ℕ) :
    p.eval ctx ≤ 1 := by
  induction p using Quotient.ind with
  | _ p_raw => exact p_raw.bool ctx

/-- Computation lemma: `eval` on a concrete
representative reduces to the underlying
`ERBoolPred.pred.interp`. -/
@[simp] theorem ERBoolPredE.eval_mk
    {n : ℕ} (p : ERBoolPred n)
    (ctx : Fin n → ℕ) :
    ERBoolPredE.eval
        (Quotient.mk (ERBoolPred.ExtEq n) p) ctx =
      p.pred.interp ctx :=
  rfl

/-- Two quotient predicates are equal iff their
evaluations agree on every context.  This is the
extensionality principle for `ERBoolPredE`. -/
theorem ERBoolPredE.eval_injective
    {n : ℕ} (p q : ERBoolPredE n)
    (h : ∀ ctx : Fin n → ℕ,
      p.eval ctx = q.eval ctx) :
    p = q := by
  induction p using Quotient.ind with
  | _ p_raw =>
    induction q using Quotient.ind with
    | _ q_raw =>
      apply Quotient.sound
      exact h

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

/-- The always-true predicate at arity `n` in the
quotient form. -/
def ERBoolPredE.alwaysTrue (n : ℕ) :
    ERBoolPredE n :=
  Quotient.mk (ERBoolPred.ExtEq n)
    (ERBoolPred.alwaysTrueN n)

/-- Eval of `alwaysTrue` is always `1`. -/
@[simp] theorem ERBoolPredE.alwaysTrue_eval
    (n : ℕ) (ctx : Fin n → ℕ) :
    (ERBoolPredE.alwaysTrue n).eval ctx = 1 :=
  rfl

/-- Conjunction of two same-arity quotient
predicates, lifted from the raw `andSameArity` via
`Quotient.lift₂`. -/
def ERBoolPredE.andSameArity {n : ℕ}
    (p q : ERBoolPredE n) : ERBoolPredE n :=
  Quotient.lift₂
    (s₁ := ERBoolPred.ExtEq n)
    (s₂ := ERBoolPred.ExtEq n)
    (fun p' q' =>
      Quotient.mk (ERBoolPred.ExtEq n)
        (ERBoolPred.andSameArity p' q'))
    (fun pa pb qa qb hp hq =>
      Quotient.sound
        (s := ERBoolPred.ExtEq n)
        (fun ctx => by
          simp only
            [ERBoolPred.andSameArity_interp]
          rw [hp ctx, hq ctx]))
    p q

/-- Eval of `andSameArity` is the product of the
two evals. -/
@[simp] theorem ERBoolPredE.andSameArity_eval
    {n : ℕ} (p q : ERBoolPredE n)
    (ctx : Fin n → ℕ) :
    (ERBoolPredE.andSameArity p q).eval ctx =
      p.eval ctx * q.eval ctx := by
  induction p using Quotient.ind with
  | _ p_raw =>
    induction q using Quotient.ind with
    | _ q_raw =>
      change (ERBoolPred.andSameArity p_raw
          q_raw).pred.interp ctx = _
      rw [ERBoolPred.andSameArity_interp]
      rfl

/-- Conjunction of two different-arity quotient
predicates, yielding a quotient predicate at arity
`n + m`. -/
def ERBoolPredE.and {n m : ℕ}
    (p : ERBoolPredE n) (q : ERBoolPredE m) :
    ERBoolPredE (n + m) :=
  Quotient.lift₂
    (s₁ := ERBoolPred.ExtEq n)
    (s₂ := ERBoolPred.ExtEq m)
    (fun p' q' =>
      Quotient.mk (ERBoolPred.ExtEq (n + m))
        (ERBoolPred.and p' q'))
    (fun pa pb qa qb hp hq =>
      Quotient.sound
        (s := ERBoolPred.ExtEq (n + m))
        (fun ctx => by
          simp only [ERBoolPred.and_interp]
          rw [hp _, hq _]))
    p q

/-- Eval of `and`: product of the two evals at the
respective coordinate slices. -/
@[simp] theorem ERBoolPredE.and_eval
    {n m : ℕ} (p : ERBoolPredE n)
    (q : ERBoolPredE m)
    (ctx : Fin (n + m) → ℕ) :
    (ERBoolPredE.and p q).eval ctx =
      p.eval (ERMorN.fst.interp ctx) *
      q.eval (ERMorN.snd.interp ctx) := by
  induction p using Quotient.ind with
  | _ p_raw =>
    induction q using Quotient.ind with
    | _ q_raw =>
      change (ERBoolPred.and p_raw
          q_raw).pred.interp ctx = _
      rw [ERBoolPred.and_interp]
      rfl

/-- Componentwise equality of two raw `ERMorN`
tuples, packaged as a quotient predicate. -/
def ERBoolPredE.allEq {n m : ℕ}
    (f g : ERMorN n m) : ERBoolPredE n :=
  Quotient.mk (ERBoolPred.ExtEq n)
    (ERBoolPred.allEq f g)

/-- Eval of `allEq` matches the underlying
`ERBoolPred.allEq` interpretation. -/
@[simp] theorem ERBoolPredE.allEq_eval
    {n m : ℕ} (f g : ERMorN n m)
    (ctx : Fin n → ℕ) :
    (ERBoolPredE.allEq f g).eval ctx =
      (ERBoolPred.allEq f g).pred.interp ctx :=
  rfl

/-- Object of `LawvereERLexCat`: an arity together with
a Boolean-valued *quotient* predicate cutting out a
decidable subobject of `Fin arity -> ℕ`.  Using the
quotient `ERBoolPredE` (rather than raw `ERBoolPred`)
means semantically equal predicates yield literally
equal objects. -/
structure LexObj where
  /-- The arity (number of free variables). -/
  arity : ℕ
  /-- The Boolean predicate (quotient class). -/
  pred : ERBoolPredE arity

/-- Raw morphism in `LawvereERLexCat`: an `ERMorN`
tuple that respects membership, that is, maps inputs
satisfying the source predicate to outputs satisfying
the target predicate.  Membership is checked via the
quotient-lifted `eval`. -/
def ERLexMorN (src tgt : LexObj) : Type :=
  { f : ERMorN src.arity tgt.arity //
      ∀ ctx : Fin src.arity → ℕ,
        src.pred.eval ctx = 1 →
        tgt.pred.eval (f.interp ctx) = 1 }

/-- The setoid on `ERLexMorN src tgt`: source-
restricted extensional equality, with membership
checked via `eval`. -/
def erLexMorNSetoid (src tgt : LexObj) :
    Setoid (ERLexMorN src tgt) where
  r f g :=
    ∀ ctx : Fin src.arity → ℕ,
      src.pred.eval ctx = 1 →
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
  pred := ERBoolPredE.alwaysTrue 0

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
  pred := ERBoolPredE.and a.pred b.pred

/-- First projection from the product `a × b` to `a`.
Underlying tuple: `ERMorN.fst`.  Membership
preservation: from `(a.pred ⊓ b.pred)(ctx) = 1`,
deduce `a.pred(first n of ctx) = 1` via
`Nat.mul_eq_one`. -/
def ERLexMorN.pi1 (a b : LexObj) :
    ERLexMorN (LexObj.prod a b) a :=
  ⟨ERMorN.fst, fun ctx hctx => by
    change (ERBoolPredE.and a.pred b.pred).eval
      ctx = 1 at hctx
    rw [ERBoolPredE.and_eval] at hctx
    exact (mul_eq_one.mp hctx).1⟩

/-- Second projection from the product `a × b` to
`b`. -/
def ERLexMorN.pi2 (a b : LexObj) :
    ERLexMorN (LexObj.prod a b) b :=
  ⟨ERMorN.snd, fun ctx hctx => by
    change (ERBoolPredE.and a.pred b.pred).eval
      ctx = 1 at hctx
    rw [ERBoolPredE.and_eval] at hctx
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

set_option backward.isDefEq.respectTransparency false in
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
    change (ERBoolPredE.and a.pred b.pred).eval
      _ = 1
    rw [ERBoolPredE.and_eval]
    have hf : a.pred.eval
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
    have hg : b.pred.eval
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

set_option backward.isDefEq.respectTransparency false in
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
    ERBoolPredE.andSameArity a.pred
      (ERBoolPredE.allEq f.val g.val)

/-- The equalizer inclusion morphism: underlying
tuple is the identity, with respect proof
extracting `a.pred = 1` from the equalizer
predicate. -/
def ERLexMorN.equalizerMap {a b : LexObj}
    (f g : ERLexMorN a b) :
    ERLexMorN (LexObj.equalizer f g) a :=
  ⟨ERMorN.id a.arity, fun ctx hctx => by
    change (ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f.val g.val)).eval
        ctx = 1 at hctx
    rw [ERBoolPredE.andSameArity_eval] at hctx
    change a.pred.eval ctx = 1
    exact (mul_eq_one.mp hctx).1⟩

/-- The equalizer inclusion morphism in the
quotient category. -/
def ERLexMorNQuo.equalizerMap {a b : LexObj}
    (f g : ERLexMorN a b) :
    ERLexMorNQuo (LexObj.equalizer f g) a :=
  Quotient.mk
    (erLexMorNSetoid (LexObj.equalizer f g) a)
    (ERLexMorN.equalizerMap f g)

set_option backward.isDefEq.respectTransparency false in
/-- Lift of an equalizing morphism through the
equalizer (raw level).  Given `h : z → a` whose
compositions with `f` and `g` agree on
source-satisfying contexts, produces the morphism
into the equalizer with the same underlying
tuple. -/
def ERLexMorN.equalizerLift {z a b : LexObj}
    {f g : ERLexMorN a b} (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.eval ctx = 1 →
      f.val.interp (h.val.interp ctx) =
        g.val.interp (h.val.interp ctx)) :
    ERLexMorN z (LexObj.equalizer f g) :=
  ⟨h.val, fun ctx hctx => by
    change (ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f.val g.val)).eval
        _ = 1
    rw [ERBoolPredE.andSameArity_eval]
    have h1 : a.pred.eval (h.val.interp ctx) = 1 :=
      h.property ctx hctx
    have h2 : (ERBoolPredE.allEq f.val
        g.val).eval (h.val.interp ctx) = 1 :=
      ERBoolPred.allEq_of_eq _ _ _ (heq ctx hctx)
    rw [h1, h2]⟩

/-- Quotient-level lift from a raw equalizing
morphism: takes a raw `h` with the raw equalization
hypothesis and produces the quotient class of the
raw lift. -/
def ERLexMorNQuo.equalizerLift {z a b : LexObj}
    {f g : ERLexMorN a b} (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.eval ctx = 1 →
      f.val.interp (h.val.interp ctx) =
        g.val.interp (h.val.interp ctx)) :
    ERLexMorNQuo z (LexObj.equalizer f g) :=
  Quotient.mk
    (erLexMorNSetoid z (LexObj.equalizer f g))
    (ERLexMorN.equalizerLift h heq)

/-- The equalizer lift, composed with the
equalizer inclusion, recovers the original
morphism (at the quotient level). -/
theorem ERLexMorNQuo.equalizerLift_map
    {z a b : LexObj} {f g : ERLexMorN a b}
    (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.eval ctx = 1 →
      f.val.interp (h.val.interp ctx) =
        g.val.interp (h.val.interp ctx)) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerLift h heq)
      (ERLexMorNQuo.equalizerMap f g) =
    Quotient.mk (erLexMorNSetoid z a) h :=
  Quotient.sound
    (s := erLexMorNSetoid z a)
    (fun ctx _ => by
      simp only [ERLexMorN.comp,
        ERLexMorN.equalizerMap,
        ERLexMorN.equalizerLift]
      change h.val.interp ctx = h.val.interp ctx
      rfl)

/-- Uniqueness: any quotient morphism `h'` whose
composition with the equalizer inclusion equals
`[h]` must equal the equalizer lift. -/
theorem ERLexMorNQuo.equalizerLift_uniq
    {z a b : LexObj} {f g : ERLexMorN a b}
    (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.eval ctx = 1 →
      f.val.interp (h.val.interp ctx) =
        g.val.interp (h.val.interp ctx))
    (h' : ERLexMorNQuo z (LexObj.equalizer f g))
    (hmap :
      ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerMap f g) =
      Quotient.mk (erLexMorNSetoid z a) h) :
    h' = ERLexMorNQuo.equalizerLift h heq :=
  Quotient.ind
    (motive := fun h' =>
      ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerMap f g) =
      Quotient.mk (erLexMorNSetoid z a) h →
      h' = ERLexMorNQuo.equalizerLift h heq)
    (fun h'_raw hmap_eq => by
      have hrel := Quotient.exact
        (s := erLexMorNSetoid z a) hmap_eq
      apply Quotient.sound
        (s := erLexMorNSetoid z
          (LexObj.equalizer f g))
      intro ctx hctx
      have step := hrel ctx hctx
      change (ERMorN.comp h'_raw.val
          (ERMorN.id a.arity)).interp ctx =
        h.val.interp ctx at step
      simp only [ERMorN.interp_comp] at step
      change h'_raw.val.interp ctx = h.val.interp ctx
      exact step)
    h' hmap

/-- The equalizer morphism equalizes `f` and `g`
at the quotient level: composing
`equalizerMap f g` with `[f]` equals composing with
`[g]`. -/
theorem ERLexMorNQuo.equalizerMap_eq
    {a b : LexObj} (f g : ERLexMorN a b) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerMap f g)
      (Quotient.mk (erLexMorNSetoid a b) f) =
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerMap f g)
      (Quotient.mk (erLexMorNSetoid a b) g) :=
  Quotient.sound
    (s := erLexMorNSetoid
      (LexObj.equalizer f g) b)
    (fun ctx hctx => by
      simp only [ERLexMorN.comp,
        ERLexMorN.equalizerMap]
      change f.val.interp ctx = g.val.interp ctx
      change (ERBoolPredE.andSameArity a.pred
          (ERBoolPredE.allEq f.val g.val)).eval
          ctx = 1 at hctx
      rw [ERBoolPredE.andSameArity_eval] at hctx
      have h_allEq :=
        (mul_eq_one.mp hctx).2
      exact ERBoolPred.allEq_eq_one_imp
        f.val g.val ctx h_allEq)

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

/-! ## Chosen equalizers via ERBoolPredE quotient

The combined equalizer predicate `a.pred ⊓ allEq f g`
is well-defined modulo morphism representatives,
because off-`a.pred=1` contexts the conjunction is
zero regardless of the `allEq` term, and
on-`a.pred=1` contexts the source-restricted
extensional equality of `f` and `g` representatives
forces `allEq` agreement. -/

/-- The combined equalizer predicate is well-
defined modulo morphism representatives. -/
theorem ERBoolPredE.equalizerPred_wd
    {a b : LexObj} {f₁ f₂ g₁ g₂ : ERLexMorN a b}
    (hf : (erLexMorNSetoid a b).r f₁ f₂)
    (hg : (erLexMorNSetoid a b).r g₁ g₂) :
    ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f₁.val g₁.val) =
      ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f₂.val g₂.val) := by
  apply ERBoolPredE.eval_injective
  intro ctx
  simp only [ERBoolPredE.andSameArity_eval,
    ERBoolPredE.allEq_eval]
  by_cases h0 : a.pred.eval ctx = 0
  · rw [h0]; simp
  · have h1 : a.pred.eval ctx = 1 := by
      have := ERBoolPredE.eval_le_one a.pred ctx
      omega
    rw [h1]
    have hf_at : f₁.val.interp ctx =
        f₂.val.interp ctx := hf ctx h1
    have hg_at : g₁.val.interp ctx =
        g₂.val.interp ctx := hg ctx h1
    have eq1 : (ERBoolPred.allEq f₁.val
        g₁.val).pred.interp ctx =
      (ERBoolPred.allEq f₂.val
        g₂.val).pred.interp ctx := by
      by_cases heq : f₁.val.interp ctx =
          g₁.val.interp ctx
      · have heq2 : f₂.val.interp ctx =
            g₂.val.interp ctx := by
          rw [← hf_at, ← hg_at]; exact heq
        rw [ERBoolPred.allEq_of_eq _ _ _ heq,
            ERBoolPred.allEq_of_eq _ _ _ heq2]
      · have heq2 : f₂.val.interp ctx ≠
            g₂.val.interp ctx := by
          rw [← hf_at, ← hg_at]; exact heq
        have hne1 : (ERBoolPred.allEq f₁.val
            g₁.val).pred.interp ctx ≠ 1 :=
          fun h => heq
            (ERBoolPred.allEq_eq_one_imp _ _ _ h)
        have hne2 : (ERBoolPred.allEq f₂.val
            g₂.val).pred.interp ctx ≠ 1 :=
          fun h => heq2
            (ERBoolPred.allEq_eq_one_imp _ _ _ h)
        have hle1 : (ERBoolPred.allEq f₁.val
            g₁.val).pred.interp ctx ≤ 1 :=
          (ERBoolPred.allEq f₁.val g₁.val).bool _
        have hle2 : (ERBoolPred.allEq f₂.val
            g₂.val).pred.interp ctx ≤ 1 :=
          (ERBoolPred.allEq f₂.val g₂.val).bool _
        omega
    rw [eq1]

/-- Chosen equalizer object for parallel quotient
morphisms `f, g : a ⟶ b`.  Well-defined modulo
representatives by `equalizerPred_wd`. -/
def LexObj.equalizerQ {a b : LexObj}
    (f g : ERLexMorNQuo a b) : LexObj where
  arity := a.arity
  pred := Quotient.liftOn₂
    (s₁ := erLexMorNSetoid a b)
    (s₂ := erLexMorNSetoid a b)
    f g
    (fun f' g' =>
      ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f'.val g'.val))
    (fun _ _ _ _ hf hg =>
      ERBoolPredE.equalizerPred_wd hf hg)

/-- The chosen equalizer inclusion morphism, taking
quotient morphisms as parameters.  The underlying
tuple is always `ERMorN.id a.arity`; the respect
proof unwraps `f, g` via `Quotient.ind₂` to reduce
to the raw equalizer's respect proof. -/
def ERLexMorNQuo.equalizerQMap {a b : LexObj}
    (f g : ERLexMorNQuo a b) :
    ERLexMorNQuo (LexObj.equalizerQ f g) a :=
  Quotient.mk
    (erLexMorNSetoid (LexObj.equalizerQ f g) a)
    ⟨ERMorN.id a.arity, fun ctx hctx => by
      revert hctx
      refine Quotient.ind₂ ?_ f g
      intro f' g' hctx
      change (ERBoolPredE.andSameArity a.pred
          (ERBoolPredE.allEq f'.val
            g'.val)).eval ctx = 1 at hctx
      rw [ERBoolPredE.andSameArity_eval] at hctx
      change a.pred.eval ((ERMorN.id a.arity).interp
        ctx) = 1
      rw [ERMorN.interp_id]
      exact (mul_eq_one.mp hctx).1⟩

/-- The chosen equalizer morphism equalizes `f`
and `g`. -/
theorem ERLexMorNQuo.equalizerQMap_eq
    {a b : LexObj} (f g : ERLexMorNQuo a b) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerQMap f g) f =
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerQMap f g) g := by
  refine Quotient.ind₂ ?_ f g
  intro f' g'
  -- After unwrapping, this is the raw equalizer's
  -- equalization theorem, which is exactly Phase
  -- 4d's equalizerMap_eq.
  exact ERLexMorNQuo.equalizerMap_eq f' g'

set_option backward.isDefEq.respectTransparency false in
/-- Chosen equalizer lift: given `h : z → a` whose
compositions with the quotient morphisms `f`, `g`
agree, produces a lift to `equalizerQ f g`.  The
lift takes a raw `h` and a raw equalization
hypothesis. -/
def ERLexMorNQuo.equalizerQLift {z a b : LexObj}
    (f g : ERLexMorNQuo a b)
    (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.eval ctx = 1 →
      ERLexMorNQuo.comp
          (Quotient.mk _ h) f =
        ERLexMorNQuo.comp
          (Quotient.mk _ h) g) :
    ERLexMorNQuo z (LexObj.equalizerQ f g) :=
  Quotient.mk
    (erLexMorNSetoid z (LexObj.equalizerQ f g))
    ⟨h.val, fun ctx hctx => by
      revert heq
      refine Quotient.ind₂ ?_ f g
      intro f' g' heq
      change (ERBoolPredE.andSameArity a.pred
          (ERBoolPredE.allEq f'.val
            g'.val)).eval _ = 1
      rw [ERBoolPredE.andSameArity_eval]
      have h1 : a.pred.eval (h.val.interp ctx) =
          1 := h.property ctx hctx
      have hcomp := Quotient.exact
        (s := erLexMorNSetoid z b) (heq ctx hctx)
      have step := hcomp ctx hctx
      simp only [ERLexMorN.comp,
        ERMorN.interp_comp] at step
      have h2 : (ERBoolPredE.allEq f'.val
          g'.val).eval (h.val.interp ctx) = 1 := by
        change (ERBoolPred.allEq f'.val
          g'.val).pred.interp _ = 1
        exact ERBoolPred.allEq_of_eq _ _ _ step
      rw [h1, h2]⟩

/-- The chosen equalizer lift, composed with the
chosen equalizer inclusion, recovers `h`. -/
theorem ERLexMorNQuo.equalizerQLift_map
    {z a b : LexObj} (f g : ERLexMorNQuo a b)
    (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.eval ctx = 1 →
      ERLexMorNQuo.comp
          (Quotient.mk _ h) f =
        ERLexMorNQuo.comp
          (Quotient.mk _ h) g) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerQLift f g h heq)
      (ERLexMorNQuo.equalizerQMap f g) =
    Quotient.mk (erLexMorNSetoid z a) h :=
  Quotient.sound
    (s := erLexMorNSetoid z a)
    (fun ctx _ => by
      change (ERMorN.comp h.val
          (ERMorN.id a.arity)).interp ctx =
        h.val.interp ctx
      rw [ERMorN.interp_comp]
      rfl)

/-- Auxiliary: bridge from a quotient-level
equalization hypothesis to a raw-level one.
Given `heq : comp ⟦h_raw⟧ f = comp ⟦h_raw⟧ g`,
extract the raw fact that `f` and `g` evaluated at
`h_raw.val.interp ctx` agree on `z.pred = 1`
contexts.  Stated for any quotient
representatives `f', g'`. -/
private theorem
    ERLexMorNQuo.equalizerQLift_raw_heq
    {z a b : LexObj} {h_raw : ERLexMorN z a}
    {f g : ERLexMorNQuo a b}
    (heq : ERLexMorNQuo.comp
        (Quotient.mk _ h_raw) f =
      ERLexMorNQuo.comp
        (Quotient.mk _ h_raw) g)
    (ctx : Fin z.arity → ℕ)
    (hctx : z.pred.eval ctx = 1) :
    ∀ (f' g' : ERLexMorN a b),
      Quotient.mk _ f' = f →
      Quotient.mk _ g' = g →
      f'.val.interp (h_raw.val.interp ctx) =
        g'.val.interp (h_raw.val.interp ctx) := by
  intros f' g' hf hg
  subst hf
  subst hg
  have hcomp := Quotient.exact
    (s := erLexMorNSetoid z b) heq
  have step := hcomp ctx hctx
  simp only [ERLexMorN.comp,
    ERMorN.interp_comp] at step
  exact step

/-- The chosen equalizer lift, taking a quotient
morphism `h` and a quotient-level equalization
hypothesis. -/
def ERLexMorNQuo.equalizerQLiftQuo {z a b : LexObj}
    (f g : ERLexMorNQuo a b)
    (h : ERLexMorNQuo z a)
    (heq : ERLexMorNQuo.comp h f =
           ERLexMorNQuo.comp h g) :
    ERLexMorNQuo z (LexObj.equalizerQ f g) :=
  h.hrecOn
    (motive := fun h' =>
      ERLexMorNQuo.comp h' f =
          ERLexMorNQuo.comp h' g →
        ERLexMorNQuo z (LexObj.equalizerQ f g))
    (fun h_raw heq_specialized =>
      ERLexMorNQuo.equalizerQLift f g h_raw
        (fun _ _ => heq_specialized))
    (fun {h₁ h₂} hrel => by
      apply Function.hfunext
      · -- type-equality: the two heq types are equal
        have heq_quo : (Quotient.mk
            (erLexMorNSetoid z a) h₁ :
            ERLexMorNQuo z a) =
            Quotient.mk _ h₂ :=
          Quotient.sound hrel
        rw [heq_quo]
      · -- value-equality: the two function bodies
        -- agree (as HEq, then Eq via heq_of_eq)
        intro heq₁ heq₂ _
        apply heq_of_eq
        apply Quotient.sound
          (s := erLexMorNSetoid z
            (LexObj.equalizerQ f g))
        intro ctx hctx
        exact hrel ctx hctx)
    heq

/-- Uniqueness: the chosen equalizer lift is unique
among morphisms whose composition with the
equalizer inclusion equals `h`. -/
theorem ERLexMorNQuo.equalizerQLift_uniq
    {z a b : LexObj} (f g : ERLexMorNQuo a b)
    (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.eval ctx = 1 →
      ERLexMorNQuo.comp
          (Quotient.mk _ h) f =
        ERLexMorNQuo.comp
          (Quotient.mk _ h) g)
    (h' : ERLexMorNQuo z (LexObj.equalizerQ f g))
    (hmap :
      ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerQMap f g) =
      Quotient.mk (erLexMorNSetoid z a) h) :
    h' = ERLexMorNQuo.equalizerQLift f g h heq :=
  Quotient.ind
    (motive := fun h' =>
      ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerQMap f g) =
      Quotient.mk (erLexMorNSetoid z a) h →
      h' = ERLexMorNQuo.equalizerQLift f g h heq)
    (fun h'_raw hmap_eq => by
      have hrel := Quotient.exact
        (s := erLexMorNSetoid z a) hmap_eq
      apply Quotient.sound
        (s := erLexMorNSetoid z
          (LexObj.equalizerQ f g))
      intro ctx hctx
      have step := hrel ctx hctx
      change (ERMorN.comp h'_raw.val
          (ERMorN.id a.arity)).interp ctx =
        h.val.interp ctx at step
      simp only [ERMorN.interp_comp] at step
      change h'_raw.val.interp ctx = h.val.interp ctx
      exact step)
    h' hmap

/-- The chosen equalizer lift composed with the
inclusion recovers `h`, stated for
`equalizerQLiftQuo`. -/
theorem ERLexMorNQuo.equalizerQLiftQuo_map
    {z a b : LexObj} (f g : ERLexMorNQuo a b)
    (h : ERLexMorNQuo z a)
    (heq : ERLexMorNQuo.comp h f =
           ERLexMorNQuo.comp h g) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerQLiftQuo f g h heq)
      (ERLexMorNQuo.equalizerQMap f g) = h := by
  refine Quotient.ind
    (motive := fun h' =>
      ∀ heq' : ERLexMorNQuo.comp h' f =
          ERLexMorNQuo.comp h' g,
      ERLexMorNQuo.comp
        (ERLexMorNQuo.equalizerQLiftQuo f g h'
          heq')
        (ERLexMorNQuo.equalizerQMap f g) = h')
    ?_ h heq
  intro h_raw heq'
  change ERLexMorNQuo.comp
    (ERLexMorNQuo.equalizerQLift f g h_raw
      (fun _ _ => heq'))
    (ERLexMorNQuo.equalizerQMap f g) =
    Quotient.mk _ h_raw
  exact ERLexMorNQuo.equalizerQLift_map f g h_raw _

/-- Uniqueness for `equalizerQLiftQuo`: any
morphism whose composition with the chosen
equalizer inclusion equals `h` must equal the
lift. -/
theorem ERLexMorNQuo.equalizerQLiftQuo_uniq
    {z a b : LexObj} (f g : ERLexMorNQuo a b)
    (h : ERLexMorNQuo z a)
    (heq : ERLexMorNQuo.comp h f =
           ERLexMorNQuo.comp h g)
    (h' : ERLexMorNQuo z (LexObj.equalizerQ f g))
    (hmap :
      ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerQMap f g) = h) :
    h' = ERLexMorNQuo.equalizerQLiftQuo f g h heq := by
  refine Quotient.ind
    (motive := fun h' =>
      ∀ (heq' : ERLexMorNQuo.comp h' f =
          ERLexMorNQuo.comp h' g)
        (h'' : ERLexMorNQuo z
          (LexObj.equalizerQ f g)),
      ERLexMorNQuo.comp h''
          (ERLexMorNQuo.equalizerQMap f g) = h' →
      h'' = ERLexMorNQuo.equalizerQLiftQuo f g
        h' heq')
    ?_ h heq h' hmap
  intro h_raw heq' h'' hmap'
  change h'' = ERLexMorNQuo.equalizerQLift f g h_raw
    (fun _ _ => heq')
  exact ERLexMorNQuo.equalizerQLift_uniq f g h_raw _
    h'' hmap'

/-- Chosen equalizer for parallel morphisms in
`LawvereERLexCat`. -/
def lawvereERLexEqualizer
    {a b : LawvereERLexCat}
    (f g : a ⟶ b) :
    ChosenEqualizer f g where
  obj := LexObj.equalizerQ f g
  ι := ERLexMorNQuo.equalizerQMap f g
  ι_eq := ERLexMorNQuo.equalizerQMap_eq f g
  lift h heq :=
    ERLexMorNQuo.equalizerQLiftQuo f g h heq
  lift_ι h heq :=
    ERLexMorNQuo.equalizerQLiftQuo_map f g h heq
  lift_uniq h heq h' hmap :=
    ERLexMorNQuo.equalizerQLiftQuo_uniq f g h heq
      h' hmap

/-- `LawvereERLexCat` has chosen equalizers. -/
instance : HasChosenEqualizers LawvereERLexCat where
  equalizer f g := lawvereERLexEqualizer f g

/-- `LawvereERLexCat` has chosen finite limits. -/
instance : HasChosenFiniteLimits
    LawvereERLexCat where

end GebLean
