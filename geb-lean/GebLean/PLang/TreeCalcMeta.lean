import GebLean.PLang.TreeCalcPrograms

/-!
# Tree Calculus Metatheory

Partial combinatory algebra (PCA) structure
and confluence for tree calculus.
-/

namespace GebLean

universe u

/-! ## Application

`Value.apply v w` forms the application of `v`
to `w` as a `CompTree`, which may then be
evaluated via `reduce1`.

For leaf and stem heads, application always
produces a value in one step (partial
application).  For fork heads, the triage
rules apply and may require further evaluation.
-/

/-- Form the application of two values as a
`CompTree`. -/
def Value.apply
    (v w : Value.{u}) : CompTree.{u} :=
  CompTree.app
    [CompTree.embedValue v,
     CompTree.embedValue w]

/-- Evaluate a `CompTree` to a `Value` using
`reduce1` iterated `n` times.  Returns `none`
if the result after `n` steps is not a
value. -/
def evalToValue
    (fuel steps : Nat)
    (t : CompTree.{0}) : Option Value.{0} :=
  let result := (reduce1 fuel)^[steps] t
  CompTree.cases
    (fun v => some (compValueToValue v))
    (fun _ => none)
    result

/-! ## PCA Structure

A partial combinatory algebra (PCA) on `Value`
consists of a partial application operation and
designated combinators `k` and `s` satisfying
the PCA axioms.

The partial application `v · w` is defined by:
- `leaf · w = stem(w)` (always defined)
- `stem(a) · w = fork(a, w)` (always defined)
- `fork(a, b) · w` = evaluate the triage rule
  (may diverge)

For tree calculus, leaf and stem applications
are total; only fork applications may diverge.
-/

/-- One-step application of a value to a value,
returning a value when the result is immediate
(leaf/stem heads or triage rules that produce
values in one step), or `none` when further
evaluation is needed.  For the PCA axioms, we
use `evalToValue` instead. -/
def Value.apply1
    (v w : Value.{0}) : Option Value.{0} :=
  evalToValue 10 1 (Value.apply v w)

/-- The PCA's k combinator: `K = stem(leaf)`. -/
abbrev pcaK : Value.{u} := Value.K

/-- The PCA's s combinator:
`s = fork(stem(fork(leaf, leaf)), leaf)`.

Satisfies:
- `s f` evaluates to `stem(stem(f))`
- `s f g` evaluates to `fork(stem(f), g)`
- `s f g x` evaluates to `f x (g x)` -/
def pcaS : Value.{u} :=
  Value.fork
    (Value.stem (Value.fork Value.leaf Value.leaf))
    Value.leaf

/-! ## K Axiom

`K x y = x` for all values x, y.

The proof proceeds via `applyRule` at the
`CompValue` level:

1. `applyRule (stem leaf) (embed cv)` =
   `some (embed (fork leaf cv))` — partial app.
2. `applyRule (fork leaf cv) x` =
   `some (embed cv)` — K rule (independent of x).
-/

/-- Partial application: `stem(leaf)` applied to
an embedded value gives `fork(leaf, cv)`. -/
lemma applyRule_stem_leaf
    (cv : CompValue.{0}) :
    applyRule (CompValue.stem CompValue.leaf)
      (CompTree.embed cv) =
    some (CompTree.embed
      (CompValue.fork CompValue.leaf cv)) := by
  rfl

/-- K rule: `fork(leaf, cv)` applied to any
`CompTree` gives `cv` (the K rule discards its
argument). -/
lemma applyRule_K
    (cv : CompValue.{0})
    (x : CompTree.{0}) :
    applyRule
      (CompValue.fork CompValue.leaf cv) x =
    some (CompTree.embed cv) := by
  rfl

/-! ## S Axiom (partial)

`s f g x ≃ f x (g x)` for all f, g, x
(when defined).

The s combinator requires multiple evaluation
steps:
1. `s f` = `fork(stem(fork(leaf,leaf)), leaf) f`
   → `fork(leaf,leaf) f (leaf f)` (S rule)
   → `leaf (leaf f)` (K + partial app)
   → `stem(stem(f))` (partial apps)
2. `s f g` = `stem(stem(f)) g`
   = `fork(stem(f), g)` (partial app, 1 step)
3. `s f g x` = `fork(stem(f), g) x`
   → `f x (g x)` (S rule)

Steps 2 and 3 are straightforward; step 1
requires several reduction steps.
-/



/-! ## Parallel Reduction

Parallel reduction allows simultaneous reduction
of multiple redexes in one step.  It is the
standard tool for proving confluence via the
diamond property (Tait-Martin-Loef method).

Since tree calculus values are normal forms
(no further reduction possible), parallel
reduction is defined on `CompTree`.

A `CompTree` parallel-reduces to another when:
- An `embed(v)` parallel-reduces to itself.
- An `app(ts)` parallel-reduces to `app(ts')`
  where each child parallel-reduces.
- A redex `app([embed(v), x, ...rest])`
  parallel-reduces to the contractum (with
  children also parallel-reduced).
-/

/-- Parallel reduction on CompTree.  Every
sub-expression may be reduced simultaneously. -/
inductive ParReduces :
    CompTree.{0} → CompTree.{0} → Prop where
  | embed (v : CompValue.{0}) :
    ParReduces
      (CompTree.embed v) (CompTree.embed v)
  | appNil :
    ParReduces (CompTree.app []) (CompTree.app [])
  | appCons
    {t t' : CompTree.{0}}
    {ts ts' : List CompTree.{0}} :
    ParReduces t t' →
    ParReduces (CompTree.app ts)
      (CompTree.app ts') →
    ParReduces (CompTree.app (t :: ts))
      (CompTree.app (t' :: ts'))
  | rule
    {v : CompValue.{0}}
    {x x' : CompTree.{0}}
    {result : CompTree.{0}}
    {rest rest' : List CompTree.{0}} :
    ParReduces x x' →
    applyRule v x' = some result →
    ParReduces (CompTree.app rest)
      (CompTree.app rest') →
    ParReduces
      (CompTree.app
        (CompTree.embed v :: x :: rest))
      (mkApp (result :: rest'))

/-- Parallel reduction is reflexive on embedded
values. -/
lemma ParReduces.refl_embed
    (v : CompValue.{0}) :
    ParReduces
      (CompTree.embed v) (CompTree.embed v) :=
  ParReduces.embed v

/-- Parallel reduction is reflexive on empty
applications. -/
lemma ParReduces.refl_appNil :
    ParReduces
      (CompTree.app []) (CompTree.app []) :=
  ParReduces.appNil

/-- Parallel reduction is reflexive on
cons-applications given reflexivity of
components. -/
lemma ParReduces.refl_appCons
    {t : CompTree.{0}}
    {ts : List CompTree.{0}}
    (ht : ParReduces t t)
    (hts : ParReduces
      (CompTree.app ts) (CompTree.app ts)) :
    ParReduces
      (CompTree.app (t :: ts))
      (CompTree.app (t :: ts)) :=
  ParReduces.appCons ht hts

/-! ## Confluence

Confluence states that if `t` reduces to both
`t1` and `t2`, then there exists `t3` such that
both `t1` and `t2` reduce to `t3`.

The standard proof uses the diamond property
of parallel reduction: if `t` parallel-reduces
to both `t1` and `t2`, there exists `t3` such
that both `t1` and `t2` parallel-reduce to `t3`.

The complete development function maps each term
to its maximally reduced form (all redexes
contracted simultaneously).  The diamond property
follows because both `t1` and `t2` parallel-
reduce to the complete development of `t`.

Full proofs of the diamond property and
confluence require detailed case analysis of the
triage rules. The definitions and structural
lemmas are provided here; the detailed case
analysis is deferred to a subsequent pass.
-/

/-- Multi-step parallel reduction:
reflexive-transitive closure. -/
def ParReducesStar
    (t1 t2 : CompTree.{0}) : Prop :=
  ∃ n : Nat,
    ∃ chain : Fin (n + 1) → CompTree.{0},
      chain ⟨0, by omega⟩ = t1
      ∧ chain ⟨n, by omega⟩ = t2
      ∧ ∀ (i : Fin n),
          ParReduces
            (chain ⟨i.val, by omega⟩)
            (chain ⟨i.val + 1, by omega⟩)

/-- Confluence statement: if `t` multi-step
parallel-reduces to both `t1` and `t2`, then
there exists `t3` reachable from both. -/
def Confluent : Prop :=
  ∀ (t t1 t2 : CompTree.{0}),
    ParReducesStar t t1 →
    ParReducesStar t t2 →
    ∃ t3 : CompTree.{0},
      ParReducesStar t1 t3
      ∧ ParReducesStar t2 t3

end GebLean
