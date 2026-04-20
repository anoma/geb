import GebLean.LawvereGodelT

/-!
# Bracket Abstraction for `GodelTTerm`

A typed de-Bruijn-indexed intermediate representation
`GodelTExpr` together with a bracket-abstraction function that
eliminates free variables by compiling to the `K`, `S`, `I`
combinators of `GodelTTerm`.

The user workflow is:

1. Build a `GodelTExpr ctx σ` with free variables drawn from
   the context `ctx`.
2. Call `.abstract` repeatedly to eliminate head variables.
3. Once the context is empty, extract the closed
   `GodelTTerm σ` via `.compile`.

The correctness theorem `abstract_interp` shows that
`abstract t`, viewed as a function of the abstracted input,
matches `t.interp` with the input substituted for the head
variable.
-/

namespace GebLean

/-- Typed de-Bruijn expressions over `GodelTTerm` parameterised
by a free-variable context.  `var i` refers to the `i`-th
context position; `const t` embeds a closed `GodelTTerm`;
`app` is ordinary function application.  Bracket abstraction
below eliminates the head context variable. -/
inductive GodelTExpr : List GodelTType → GodelTType → Type
  | var {ctx : List GodelTType} (i : Fin ctx.length) :
      GodelTExpr ctx (ctx.get i)
  | const {ctx : List GodelTType} {σ : GodelTType}
      (t : GodelTTerm σ) : GodelTExpr ctx σ
  | app {ctx : List GodelTType} {σ τ : GodelTType}
      (f : GodelTExpr ctx (.arrow σ τ))
      (a : GodelTExpr ctx σ) : GodelTExpr ctx τ

/-- Prepend a value to an environment for a context, producing
an environment for the extended context `head :: ctx`. -/
def GodelTExpr.envCons {ctx : List GodelTType} {head : GodelTType}
    (x : head.interp)
    (env : (i : Fin ctx.length) → (ctx.get i).interp) :
    (i : Fin (head :: ctx).length) →
      ((head :: ctx).get i).interp :=
  fun i => match i with
    | ⟨0, _⟩ => x
    | ⟨j + 1, h⟩ => env ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Standard interpretation of an open expression against an
environment supplying values for the free variables. -/
def GodelTExpr.interp {ctx : List GodelTType} {σ : GodelTType} :
    GodelTExpr ctx σ →
    ((i : Fin ctx.length) → (ctx.get i).interp) →
    σ.interp
  | .var i, env => env i
  | .const c, _ => GodelTTerm.interp c
  | .app f a, env => (f.interp env) (a.interp env)

@[simp] theorem GodelTExpr.interp_var {ctx : List GodelTType}
    (i : Fin ctx.length)
    (env : (j : Fin ctx.length) → (ctx.get j).interp) :
    (GodelTExpr.var i).interp env = env i := rfl

@[simp] theorem GodelTExpr.interp_const {ctx : List GodelTType}
    {σ : GodelTType} (c : GodelTTerm σ)
    (env : (j : Fin ctx.length) → (ctx.get j).interp) :
    ((GodelTExpr.const c : GodelTExpr ctx σ)).interp env =
      GodelTTerm.interp c := rfl

@[simp] theorem GodelTExpr.interp_app {ctx : List GodelTType}
    {σ τ : GodelTType}
    (f : GodelTExpr ctx (.arrow σ τ))
    (a : GodelTExpr ctx σ)
    (env : (j : Fin ctx.length) → (ctx.get j).interp) :
    (f.app a).interp env = (f.interp env) (a.interp env) := rfl

/-- Bracket abstraction: given an expression with one extra
head variable, produce an expression that takes that variable
as an explicit arrow-typed input.  Follows the standard
`I`/`K`/`S` compilation rules. -/
def GodelTExpr.abstract {ctx : List GodelTType}
    {head τ : GodelTType} :
    GodelTExpr (head :: ctx) τ →
    GodelTExpr ctx (.arrow head τ)
  | .var ⟨0, _⟩ => .const (GodelTTerm.I head)
  | .var ⟨i + 1, h⟩ =>
      .app
        (.const (GodelTTerm.K _ head))
        (.var ⟨i, Nat.lt_of_succ_lt_succ h⟩)
  | .const c =>
      .app (.const (GodelTTerm.K τ head)) (.const c)
  | .app (σ := σ') f a =>
      .app
        (.app (.const (GodelTTerm.S head σ' τ)) f.abstract)
        a.abstract

@[simp] theorem GodelTExpr.abstract_var_zero
    {ctx : List GodelTType} {head : GodelTType}
    (h : 0 < (head :: ctx).length) :
    GodelTExpr.abstract
        (GodelTExpr.var (ctx := head :: ctx) ⟨0, h⟩) =
      .const (GodelTTerm.I head) := rfl

@[simp] theorem GodelTExpr.abstract_var_succ
    {ctx : List GodelTType} {head : GodelTType}
    (i : ℕ) (h : i + 1 < (head :: ctx).length) :
    GodelTExpr.abstract
        (GodelTExpr.var (ctx := head :: ctx) ⟨i + 1, h⟩) =
      .app
        (.const (GodelTTerm.K _ head))
        (.var ⟨i, Nat.lt_of_succ_lt_succ h⟩) := rfl

@[simp] theorem GodelTExpr.abstract_const
    {ctx : List GodelTType} {head τ : GodelTType}
    (c : GodelTTerm τ) :
    GodelTExpr.abstract
        (GodelTExpr.const c : GodelTExpr (head :: ctx) τ) =
      .app (.const (GodelTTerm.K τ head)) (.const c) := rfl

@[simp] theorem GodelTExpr.abstract_app
    {ctx : List GodelTType} {head σ τ : GodelTType}
    (f : GodelTExpr (head :: ctx) (.arrow σ τ))
    (a : GodelTExpr (head :: ctx) σ) :
    GodelTExpr.abstract (f.app a) =
      .app
        (.app (.const (GodelTTerm.S head σ τ)) f.abstract)
        a.abstract := rfl

@[simp] theorem GodelTExpr.envCons_zero {ctx : List GodelTType}
    {head : GodelTType} (x : head.interp)
    (env : (i : Fin ctx.length) → (ctx.get i).interp)
    (h : 0 < (head :: ctx).length) :
    envCons x env ⟨0, h⟩ = x := rfl

@[simp] theorem GodelTExpr.envCons_succ {ctx : List GodelTType}
    {head : GodelTType} (x : head.interp)
    (env : (i : Fin ctx.length) → (ctx.get i).interp)
    (j : ℕ) (h : j + 1 < (head :: ctx).length) :
    envCons x env ⟨j + 1, h⟩ =
      env ⟨j, Nat.lt_of_succ_lt_succ h⟩ := rfl

/-- Correctness of `abstract`: applying the abstracted
expression to a value matches evaluating the original with
that value bound to the head context variable. -/
theorem GodelTExpr.abstract_interp {ctx : List GodelTType}
    {head τ : GodelTType} (t : GodelTExpr (head :: ctx) τ)
    (env : (i : Fin ctx.length) → (ctx.get i).interp)
    (x : head.interp) :
    (t.abstract).interp env x = t.interp (envCons x env) := by
  induction t with
  | var i =>
      match i with
      | ⟨0, _⟩ =>
          simp only [abstract_var_zero, interp_const,
            GodelTTerm.interp_I, interp_var, envCons_zero]
      | ⟨_ + 1, _⟩ =>
          simp only [abstract_var_succ, interp_app,
            interp_const, GodelTTerm.interp_K, interp_var,
            envCons_succ]
  | const c =>
      simp only [abstract_const, interp_app, interp_const,
        GodelTTerm.interp_K]
  | app f a ihf iha =>
      simp only [abstract_app, interp_app, interp_const,
        GodelTTerm.interp_S]
      rw [ihf, iha]

/-- Compile a closed expression (with an empty context) down to
a plain `GodelTTerm`. -/
def GodelTExpr.compile {σ : GodelTType} :
    GodelTExpr [] σ → GodelTTerm σ
  | .var ⟨_, h⟩ => absurd h (by simp)
  | .const c => c
  | .app f a => f.compile.app a.compile

@[simp] theorem GodelTExpr.compile_const {σ : GodelTType}
    (c : GodelTTerm σ) :
    ((GodelTExpr.const c : GodelTExpr [] σ)).compile = c := rfl

@[simp] theorem GodelTExpr.compile_app {σ τ : GodelTType}
    (f : GodelTExpr [] (.arrow σ τ))
    (a : GodelTExpr [] σ) :
    (f.app a).compile = f.compile.app a.compile := rfl

/-- The canonical empty environment for the empty context. -/
def GodelTExpr.emptyEnv : (i : Fin ([] : List GodelTType).length) →
    (([] : List GodelTType).get i).interp :=
  fun i => absurd i.isLt (by simp)

/-- Compiling preserves interpretation. -/
theorem GodelTExpr.compile_interp {σ : GodelTType}
    (t : GodelTExpr [] σ) :
    (t.compile).interp = t.interp emptyEnv := by
  induction t with
  | var i => exact absurd i.isLt (by simp)
  | const c => rfl
  | app f a ihf iha =>
      simp only [compile_app, interp_app]
      change f.compile.interp (a.compile.interp) = _
      rw [ihf, iha]

/-- The standard base-typed context of `m` variables. -/
def GodelTExpr.baseCtx (m : ℕ) : List GodelTType :=
  List.replicate m GodelTType.base

@[simp] theorem GodelTExpr.baseCtx_zero :
    GodelTExpr.baseCtx 0 = [] := rfl

@[simp] theorem GodelTExpr.baseCtx_succ (m : ℕ) :
    GodelTExpr.baseCtx (m + 1) =
      GodelTType.base :: GodelTExpr.baseCtx m := rfl

theorem GodelTExpr.baseCtx_length (m : ℕ) :
    (GodelTExpr.baseCtx m).length = m :=
  List.length_replicate

theorem GodelTExpr.baseCtx_get (m : ℕ)
    (i : Fin (GodelTExpr.baseCtx m).length) :
    (GodelTExpr.baseCtx m).get i = GodelTType.base := by
  unfold GodelTExpr.baseCtx
  simp [List.getElem_replicate, List.get_eq_getElem]

/-- The `i`-th variable in `baseCtx m`, typed at `base`. -/
def GodelTExpr.baseVar (m : ℕ) (i : Fin m) :
    GodelTExpr (GodelTExpr.baseCtx m) GodelTType.base :=
  GodelTExpr.baseCtx_get m
      ⟨i.val, by rw [GodelTExpr.baseCtx_length]; exact i.isLt⟩ ▸
    GodelTExpr.var
      ⟨i.val, by rw [GodelTExpr.baseCtx_length]; exact i.isLt⟩

/-- Apply a partial `arrow0 k`-typed expression to a base variable
at some position.  Used in the iterative construction of
`applyAllBaseVars` below. -/
private def GodelTExpr.appVar (m : ℕ) {k : ℕ}
    (e : GodelTExpr (GodelTExpr.baseCtx m) (GodelTType.arrow0 (k + 1)))
    (i : Fin m) :
    GodelTExpr (GodelTExpr.baseCtx m) (GodelTType.arrow0 k) :=
  e.app (GodelTExpr.baseVar m i)

/-- Apply a closed `arrow0 m`-typed term to all `m` variables of the
base context, producing a base-typed expression.  The variables are
applied in order 0, 1, ..., m − 1. -/
def GodelTExpr.applyAllBaseVars :
    (m : ℕ) → GodelTTerm (GodelTType.arrow0 m) →
    GodelTExpr (GodelTExpr.baseCtx m) GodelTType.base :=
  fun m t => applyAllBaseVarsAux m m (Nat.le_refl m) (.const t)
where
  applyAllBaseVarsAux : (m : ℕ) → (k : ℕ) → (hk : k ≤ m) →
      GodelTExpr (GodelTExpr.baseCtx m) (GodelTType.arrow0 k) →
      GodelTExpr (GodelTExpr.baseCtx m) GodelTType.base
    | _, 0, _, e => e
    | m, k + 1, hk, e =>
        applyAllBaseVarsAux m k (Nat.le_of_succ_le hk)
          (GodelTExpr.appVar m e
            ⟨m - k - 1, by omega⟩)

/-- Build a closed base-typed expression in the `m`-variable context
that represents applying `f` to the tuple of base-typed applications
`tuple_i` at the context variables. -/
def GodelTExpr.compExpr {n m : ℕ}
    (f : GodelTTerm (GodelTType.arrow0 n)) (tuple : Fin n → GodelTTerm (GodelTType.arrow0 m)) :
    GodelTExpr (GodelTExpr.baseCtx m) GodelTType.base :=
  compExprAux n (.const f) tuple
where
  /-- Accumulator recursion on the remaining arity `k` of `f`. -/
  compExprAux : (k : ℕ) →
      GodelTExpr (GodelTExpr.baseCtx m) (GodelTType.arrow0 k) →
      (Fin k → GodelTTerm (GodelTType.arrow0 m)) →
      GodelTExpr (GodelTExpr.baseCtx m) GodelTType.base
    | 0, e, _ => e
    | k + 1, e, args =>
        compExprAux k
          (e.app (GodelTExpr.applyAllBaseVars m (args 0)))
          (fun i => args i.succ)

/-- Iterated bracket abstraction: close the `m` head context
variables of a base-typed expression, producing a closed term of type
`arrow0 m`. -/
def GodelTExpr.iterateAbstract :
    (m : ℕ) →
    GodelTExpr (GodelTExpr.baseCtx m) GodelTType.base →
    GodelTTerm (GodelTType.arrow0 m) :=
  fun m e =>
    GodelTTerm.castArrow0 (Nat.zero_add m)
      (iterateAbstractAux 0 m e)
where
  /-- `k` tracks the already-abstracted suffix length; `rem` the
  remaining context variables. -/
  iterateAbstractAux : (k : ℕ) → (rem : ℕ) →
      GodelTExpr (GodelTExpr.baseCtx rem) (GodelTType.arrow0 k) →
      GodelTTerm (GodelTType.arrow0 (k + rem))
    | k, 0, e => e.compile
    | k, rem + 1, e =>
        GodelTTerm.castArrow0
          (by omega : (k + 1) + rem = k + (rem + 1))
          (iterateAbstractAux (k + 1) rem e.abstract)

end GebLean
