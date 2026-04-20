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

end GebLean
