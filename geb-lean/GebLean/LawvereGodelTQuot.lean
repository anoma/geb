import GebLean.LawvereGodelT
import GebLean.Utilities.ComputableLimits
import GebLean.Utilities.GodelTBracket
import Mathlib.CategoryTheory.Category.Basic

/-!
# Categorical structure on `LawvereGodelT`

Combinator-derived projections and composition, tuples of
GodelT morphisms, extensional-equality quotient,
`Category LawvereGodelTCat`, and `HasChosenFiniteProducts`.
-/

namespace GebLean

open CategoryTheory

/-- A single GodelT morphism `n → 1` is a curried n-ary
ground function: a closed term of type `arrow0 n`. -/
def GodelTMor1 (n : ℕ) : Type :=
  GodelTTerm (GodelTType.arrow0 n)

/-- Walk an `arrow0 n`-typed interpretation down against an
n-tuple of ℕ inputs, peeling off one curried argument at a
time. -/
def applyArrowN : (n : ℕ) → (GodelTType.arrow0 n).interp →
    (Fin n → ℕ) → ℕ
  | 0, v, _ => v
  | n + 1, f, ctx => applyArrowN n (f (ctx 0)) (Fin.tail ctx)

/-- Standard interpretation of a `GodelTMor1 n`: walk the
curried output of the term's interp down the input context
via `applyArrowN`. -/
def GodelTMor1.interp {n : ℕ} (t : GodelTMor1 n)
    (ctx : Fin n → ℕ) : ℕ :=
  applyArrowN n (GodelTTerm.interp t) ctx

/-- Prepend an ignored first argument at position 0 to a
curried n-ary morphism, via one application of
`K (arrow0 n) base`. -/
def GodelTMor1.dropFirst {n : ℕ} (v : GodelTMor1 n) :
    GodelTMor1 (n + 1) :=
  (GodelTTerm.K (GodelTType.arrow0 n) .base).app v

@[simp] theorem GodelTMor1.interp_dropFirst {n : ℕ}
    (v : GodelTMor1 n) (ctx : Fin (n + 1) → ℕ) :
    (v.dropFirst).interp ctx = v.interp (Fin.tail ctx) := rfl

/-- The "first of `n+1`" projection: a curried `(n+1)`-ary
function that returns its first argument and ignores the
remaining `n`.  Defined inductively: at `n = 0`, the identity;
at `n + 1`, compose with `K (arrow0 n) base` to prepend an
ignored tail. -/
def GodelTMor1.projFirst : (n : ℕ) → GodelTMor1 (n + 1)
  | 0 => GodelTTerm.I .base
  | n + 1 =>
      GodelTTerm.B
        (GodelTTerm.K (GodelTType.arrow0 n) .base)
        (GodelTMor1.projFirst n)

/-- Semantic property of `projFirst n` at the term-interp
level: applied to an input `x : ℕ` and then to any n-ary
tail, the result is `x`.  Proved by induction on `n` with the
arguments `x` and `rest` universally quantified so the
induction hypothesis can re-instantiate them. -/
theorem GodelTMor1.applyArrowN_projFirst_term :
    ∀ (n : ℕ) (x : ℕ) (rest : Fin n → ℕ),
      applyArrowN n
        (GodelTTerm.interp (GodelTMor1.projFirst n) x)
        rest = x := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro x rest
      change applyArrowN (n + 1)
        (GodelTTerm.interp
          (GodelTTerm.B
            (GodelTTerm.K (GodelTType.arrow0 n) .base)
            (GodelTMor1.projFirst n)) x) rest = x
      simp only [GodelTTerm.interp_B, GodelTTerm.interp_K]
      change applyArrowN n
        (GodelTTerm.interp (GodelTMor1.projFirst n) x)
        (Fin.tail rest) = x
      exact ih x (Fin.tail rest)

@[simp] theorem GodelTMor1.interp_projFirst (n : ℕ)
    (ctx : Fin (n + 1) → ℕ) :
    (GodelTMor1.projFirst n).interp ctx = ctx 0 := by
  unfold GodelTMor1.interp
  unfold applyArrowN
  exact GodelTMor1.applyArrowN_projFirst_term n (ctx 0)
    (Fin.tail ctx)

/-- The i-th projection in arity `n`.  At the base case
`i = 0` in arity `n+1`, uses `projFirst n`.  At the
recursive case `i = j+1`, uses `dropFirst` on the `j`-th
projection at arity `n`. -/
def GodelTMor1.proj : (n : ℕ) → Fin n → GodelTMor1 n
  | 0, i => Fin.elim0 i
  | n + 1, ⟨0, _⟩ => GodelTMor1.projFirst n
  | n + 1, ⟨j + 1, h⟩ =>
      (GodelTMor1.proj n ⟨j, Nat.lt_of_succ_lt_succ h⟩).dropFirst

@[simp] theorem GodelTMor1.interp_proj :
    ∀ (n : ℕ) (i : Fin n) (ctx : Fin n → ℕ),
      (GodelTMor1.proj n i).interp ctx = ctx i := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i ctx
      match i with
      | ⟨0, _⟩ =>
          change (GodelTMor1.projFirst n).interp ctx = ctx 0
          exact GodelTMor1.interp_projFirst n ctx
      | ⟨j + 1, h⟩ =>
          change ((GodelTMor1.proj n
            ⟨j, Nat.lt_of_succ_lt_succ h⟩).dropFirst).interp
            ctx = ctx ⟨j + 1, h⟩
          rw [GodelTMor1.interp_dropFirst]
          rw [ih ⟨j, Nat.lt_of_succ_lt_succ h⟩ (Fin.tail ctx)]
          rfl

/-- Composition of an n-ary GodelT morphism with an n-tuple of
m-ary GodelT morphisms, producing an m-ary GodelT morphism.
Constructed via bracket abstraction: build a base-typed
expression with `m` free variables representing `f` applied to
the tuple entries each applied to those variables, then
abstract all `m` variables and compile. -/
def GodelTMor1.compMor1 {n m : ℕ} (f : GodelTMor1 n)
    (tuple : Fin n → GodelTMor1 m) : GodelTMor1 m :=
  GodelTExpr.iterateAbstract m
    (GodelTExpr.compExpr f tuple)

/-- Sanity example: composing a unary morphism with a unary
morphism produces a unary morphism whose interp is composition. -/
example (f g : GodelTMor1 1) :
    GodelTMor1.compMor1 f (fun _ => g) =
      GodelTExpr.iterateAbstract 1
        (GodelTExpr.compExpr f (fun _ => g)) := rfl

/-- Interpreting a term cast along an arity equality, applied curried
against a context of the new arity, equals interpreting the underlying
term against the context reindexed across the equality. -/
theorem applyArrowN_castArrow0 {a b : ℕ} (h : a = b)
    (t : GodelTTerm (GodelTType.arrow0 a)) (ctx : Fin b → ℕ) :
    applyArrowN b (GodelTTerm.castArrow0 h t).interp ctx =
      applyArrowN a (GodelTTerm.interp t)
        (fun i : Fin a => ctx ⟨i.val, h ▸ i.isLt⟩) := by
  subst h
  rfl

/-- The reverse-indexed environment for `baseCtx rem`: given a Lean
context `ctx : Fin rem → ℕ`, produce an environment whose value at
`baseCtx rem` position `i` is `ctx (rem - 1 - i)`.  Defined by
structural recursion on `rem` so that the recursive case unfolds as
`envCons` of the last context entry onto the reverse-indexed
environment for the first `rem` entries. -/
def baseEnvRev : (rem : ℕ) → (Fin rem → ℕ) →
    (i : Fin (GodelTExpr.baseCtx rem).length) →
      ((GodelTExpr.baseCtx rem).get i).interp
  | 0, _ =>
      fun i => absurd i.isLt (by simp)
  | rem + 1, ctx =>
      GodelTExpr.envCons (ctx ⟨rem, Nat.lt_succ_self rem⟩)
        (baseEnvRev rem
          (fun j => ctx ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))

@[simp] theorem baseEnvRev_succ (rem : ℕ) (ctx : Fin (rem + 1) → ℕ) :
    baseEnvRev (rem + 1) ctx =
      GodelTExpr.envCons (ctx ⟨rem, Nat.lt_succ_self rem⟩)
        (baseEnvRev rem
          (fun j => ctx ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)) := rfl

/-- Interpretation of `iterateAbstractAux k rem e`.  Expressed as
iterated bracket abstraction, the curried `(k + rem)`-ary function
it denotes, when applied to a context `ctx`, substitutes the last
`rem` entries of `ctx` (in reverse) for `e`'s free variables and
then applies the remaining `k` entries to the resulting `k`-ary
curried structure. -/
theorem applyArrowN_iterateAbstractAux :
    ∀ (rem k : ℕ)
      (e : GodelTExpr (GodelTExpr.baseCtx rem) (GodelTType.arrow0 k))
      (ctx : Fin (k + rem) → ℕ),
    applyArrowN (k + rem)
      (GodelTExpr.iterateAbstract.iterateAbstractAux k rem e).interp
      ctx =
    applyArrowN k
      (e.interp
        (baseEnvRev rem
          (fun j : Fin rem => ctx ⟨j.val, by omega⟩)))
      (fun j : Fin k => ctx ⟨rem + j.val, by omega⟩) := by
  intro rem
  induction rem with
  | zero =>
      intro k e ctx
      have henv :
          baseEnvRev 0 (fun j : Fin 0 => ctx ⟨j.val, by omega⟩)
            = GodelTExpr.emptyEnv := by
        funext i
        exact absurd i.isLt (by simp)
      have hctx :
          (fun j : Fin k => ctx ⟨0 + j.val, by omega⟩) = ctx := by
        funext j
        apply congrArg
        apply Fin.ext
        change 0 + j.val = j.val
        omega
      rw [henv, hctx]
      change applyArrowN k
          (GodelTExpr.iterateAbstract.iterateAbstractAux k 0 e).interp
          ctx =
        applyArrowN k (e.interp GodelTExpr.emptyEnv) ctx
      rw [show
          (GodelTExpr.iterateAbstract.iterateAbstractAux k 0 e)
            = e.compile from rfl]
      rw [GodelTExpr.compile_interp]
  | succ rem ih =>
      intro k e ctx
      show applyArrowN (k + (rem + 1))
          (GodelTExpr.iterateAbstract.iterateAbstractAux k (rem + 1)
            e).interp ctx = _
      rw [show
          GodelTExpr.iterateAbstract.iterateAbstractAux k (rem + 1) e =
            GodelTTerm.castArrow0 (by omega)
              (GodelTExpr.iterateAbstract.iterateAbstractAux (k + 1)
                rem e.abstract) from rfl]
      rw [applyArrowN_castArrow0]
      rw [ih (k + 1) e.abstract]
      show applyArrowN (k + 1) _ _ = _
      rw [show
          ∀ (f : (GodelTType.arrow0 (k + 1)).interp)
            (xs : Fin (k + 1) → ℕ),
            applyArrowN (k + 1) f xs
              = applyArrowN k (f (xs 0)) (Fin.tail xs)
          from fun _ _ => rfl]
      rw [GodelTExpr.abstract_interp]
      rw [baseEnvRev_succ]
      congr 1
      funext j
      change ctx ⟨rem + (j.val + 1), _⟩
        = ctx ⟨(rem + 1) + j.val, _⟩
      apply congrArg
      apply Fin.ext
      change rem + (j.val + 1) = (rem + 1) + j.val
      omega

/-- Applying `iterateAbstract m e` curried against `ctx : Fin m → ℕ`
substitutes `ctx` (in reverse) for `e`'s free variables. -/
theorem applyArrowN_iterateAbstract (m : ℕ)
    (e : GodelTExpr (GodelTExpr.baseCtx m) GodelTType.base)
    (ctx : Fin m → ℕ) :
    applyArrowN m (GodelTExpr.iterateAbstract m e).interp ctx =
      e.interp (baseEnvRev m ctx) := by
  unfold GodelTExpr.iterateAbstract
  rw [applyArrowN_castArrow0]
  have := applyArrowN_iterateAbstractAux m 0 e
    (fun i : Fin (0 + m) => ctx ⟨i.val, by omega⟩)
  change applyArrowN (0 + m) _ _ = _ at this
  rw [this]
  have hfg : (fun j : Fin m => (fun i : Fin (0 + m) =>
      ctx ⟨i.val, by omega⟩) ⟨j.val, by omega⟩) = ctx := by
    funext j
    rfl
  rw [hfg]
  rfl

/-- Interpreting the term cast across a type equality commutes with
transporting the interpretation. -/
theorem GodelTExpr.interp_cast {ctx : List GodelTType}
    {a b : GodelTType} (h : a = b) (t : GodelTExpr ctx a)
    (env : (i : Fin ctx.length) → (ctx.get i).interp) :
    (h ▸ t).interp env = h ▸ t.interp env := by
  subst h
  rfl

/-- Read a ℕ value from a base-context environment at position `j`,
via the cast through `baseCtx_get`.  Uses `▸` with motive
`fun σ => σ.interp` so that it coincides with the interpretation
of `baseVar m j` at this environment. -/
def readBaseEnv (m : ℕ)
    (env : (i : Fin (GodelTExpr.baseCtx m).length) →
      ((GodelTExpr.baseCtx m).get i).interp)
    (j : Fin m) : ℕ :=
  show GodelTType.base.interp from
    GodelTExpr.baseCtx_get m ⟨j.val, by
        rw [GodelTExpr.baseCtx_length]; exact j.isLt⟩ ▸
      env ⟨j.val, by rw [GodelTExpr.baseCtx_length]; exact j.isLt⟩

/-- Interpretation of a base-typed variable at an environment reduces
via the cast to `readBaseEnv`. -/
theorem baseVar_interp (m : ℕ) (j : Fin m)
    (env : (i : Fin (GodelTExpr.baseCtx m).length) →
      ((GodelTExpr.baseCtx m).get i).interp) :
    (GodelTExpr.baseVar m j).interp env = readBaseEnv m env j := by
  unfold GodelTExpr.baseVar readBaseEnv
  rw [GodelTExpr.interp_cast, GodelTExpr.interp_var]

/-- Reading the reverse-indexed environment of a context cancels the
two casts, recovering the original ctx value at the mirrored index. -/
theorem readBaseEnv_baseEnvRev (m : ℕ) (ctx : Fin m → ℕ) (j : Fin m) :
    readBaseEnv m (baseEnvRev m ctx) j =
      ctx ⟨m - 1 - j.val, by omega⟩ := by
  induction m with
  | zero => exact absurd j.isLt (by simp)
  | succ m ih =>
      match j with
      | ⟨0, _⟩ =>
          change readBaseEnv (m + 1) (baseEnvRev (m + 1) ctx)
              ⟨0, by omega⟩ = ctx ⟨m, by omega⟩
          rw [baseEnvRev_succ]
          rfl
      | ⟨i + 1, hi⟩ =>
          change readBaseEnv (m + 1) (baseEnvRev (m + 1) ctx)
              ⟨i + 1, hi⟩ = ctx ⟨m + 1 - 1 - (i + 1), by omega⟩
          rw [baseEnvRev_succ]
          have key := ih (fun j' : Fin m =>
            ctx ⟨j'.val, Nat.lt_succ_of_lt j'.isLt⟩) ⟨i, by omega⟩
          have hred : readBaseEnv (m + 1)
              (GodelTExpr.envCons
                (ctx ⟨m, Nat.lt_succ_self m⟩)
                (baseEnvRev m (fun j' : Fin m =>
                  ctx ⟨j'.val, Nat.lt_succ_of_lt j'.isLt⟩)))
              ⟨i + 1, hi⟩ =
            readBaseEnv m
              (baseEnvRev m (fun j' : Fin m =>
                ctx ⟨j'.val, Nat.lt_succ_of_lt j'.isLt⟩))
              ⟨i, by omega⟩ := rfl
          rw [hred, key]
          apply congrArg
          apply Fin.ext
          change m - 1 - i = m + 1 - 1 - (i + 1)
          omega

/-- Interpretation of `applyAllBaseVarsAux m k hk e` at the
reverse-indexed environment of a ctx: reduces to applyArrowN of e's
interp against a descending subsequence of ctx. -/
theorem applyAllBaseVarsAux_interp (m : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ m)
      (e : GodelTExpr (GodelTExpr.baseCtx m) (GodelTType.arrow0 k))
      (ctx : Fin m → ℕ),
    (GodelTExpr.applyAllBaseVars.applyAllBaseVarsAux m k hk e).interp
        (baseEnvRev m ctx) =
      applyArrowN k (e.interp (baseEnvRev m ctx))
        (fun j : Fin k =>
          ctx ⟨m - 1 - (k - 1 - j.val), by omega⟩) := by
  intro k
  induction k with
  | zero =>
      intro _ e ctx
      rfl
  | succ k ih =>
      intro hk e ctx
      change (GodelTExpr.applyAllBaseVars.applyAllBaseVarsAux m k
          (Nat.le_of_succ_le hk)
          (GodelTExpr.appVar m e
            ⟨k, Nat.lt_of_succ_le hk⟩)).interp (baseEnvRev m ctx)
        = _
      rw [ih (Nat.le_of_succ_le hk)]
      unfold GodelTExpr.appVar
      rw [GodelTExpr.interp_app]
      rw [baseVar_interp]
      rw [readBaseEnv_baseEnvRev]
      change applyArrowN k
          (e.interp (baseEnvRev m ctx) (ctx ⟨m - 1 - k, _⟩))
          (fun j : Fin k =>
            ctx ⟨m - 1 - (k - 1 - j.val), _⟩) =
        applyArrowN (k + 1) (e.interp (baseEnvRev m ctx))
          (fun j : Fin (k + 1) =>
            ctx ⟨m - 1 - (k - j.val), _⟩)
      change applyArrowN k _ _ =
        applyArrowN k
          ((e.interp (baseEnvRev m ctx)) (ctx ⟨m - 1 - (k - 0), _⟩))
          (Fin.tail (fun j : Fin (k + 1) =>
            ctx ⟨m - 1 - (k - j.val), _⟩))
      congr 1
      funext j
      change ctx ⟨m - 1 - (k - 1 - j.val), _⟩
        = ctx ⟨m - 1 - (k - (j.val + 1)), _⟩
      apply congrArg
      apply Fin.ext
      change m - 1 - (k - 1 - j.val) = m - 1 - (k - (j.val + 1))
      omega

/-- Interpretation of `applyAllBaseVars m t` at the reverse-indexed
environment of a context recovers the curried application of `t` to
the context. -/
theorem applyAllBaseVars_interp (m : ℕ) (t : GodelTTerm (GodelTType.arrow0 m))
    (ctx : Fin m → ℕ) :
    (GodelTExpr.applyAllBaseVars m t).interp (baseEnvRev m ctx) =
      applyArrowN m t.interp ctx := by
  unfold GodelTExpr.applyAllBaseVars
  rw [applyAllBaseVarsAux_interp m m (Nat.le_refl m) (.const t) ctx]
  rw [GodelTExpr.interp_const]
  congr 1
  funext j
  apply congrArg
  apply Fin.ext
  change m - 1 - (m - 1 - j.val) = j.val
  omega

/-- Interpretation of `compExprAux k e args` at an environment: the
curried application of `e.interp env` to the tuple of
`(applyAllBaseVars m (args i)).interp env` values. -/
theorem compExprAux_interp {m : ℕ} :
    ∀ (k : ℕ)
      (e : GodelTExpr (GodelTExpr.baseCtx m) (GodelTType.arrow0 k))
      (args : Fin k → GodelTTerm (GodelTType.arrow0 m))
      (env : (i : Fin (GodelTExpr.baseCtx m).length) →
        ((GodelTExpr.baseCtx m).get i).interp),
    (GodelTExpr.compExpr.compExprAux k e args).interp env =
      applyArrowN k (e.interp env)
        (fun i : Fin k =>
          (GodelTExpr.applyAllBaseVars m (args i)).interp env) := by
  intro k
  induction k with
  | zero =>
      intro _ _ _
      rfl
  | succ k ih =>
      intro e args env
      change (GodelTExpr.compExpr.compExprAux k
          (e.app (GodelTExpr.applyAllBaseVars m (args 0)))
          (fun i => args i.succ)).interp env = _
      rw [ih]
      rw [GodelTExpr.interp_app]
      rfl

/-- Interpretation of `compExpr f tuple` at the reverse-indexed
environment of a context: curried application of `f` against the
tuple's interpretations at the context. -/
theorem compExpr_interp {n m : ℕ}
    (f : GodelTTerm (GodelTType.arrow0 n))
    (tuple : Fin n → GodelTTerm (GodelTType.arrow0 m))
    (ctx : Fin m → ℕ) :
    (GodelTExpr.compExpr f tuple).interp (baseEnvRev m ctx) =
      applyArrowN n f.interp
        (fun i : Fin n => applyArrowN m (tuple i).interp ctx) := by
  unfold GodelTExpr.compExpr
  rw [compExprAux_interp n (.const f) tuple (baseEnvRev m ctx)]
  rw [GodelTExpr.interp_const]
  congr 1
  funext i
  rw [applyAllBaseVars_interp]

/-- Interpretation correctness of `GodelTMor1.compMor1`: the composite
morphism's interpretation at a context equals the outer morphism's
interpretation against the tuple of inner morphisms' interpretations
at the context. -/
theorem GodelTMor1.interp_compMor1 {n m : ℕ}
    (f : GodelTMor1 n) (tuple : Fin n → GodelTMor1 m)
    (ctx : Fin m → ℕ) :
    (GodelTMor1.compMor1 f tuple).interp ctx =
      f.interp (fun i => (tuple i).interp ctx) := by
  unfold GodelTMor1.compMor1
  unfold GodelTMor1.interp
  rw [applyArrowN_iterateAbstract]
  rw [compExpr_interp]

end GebLean
