import GebLean.PLO

/-!
# Exploration: Deriving PBTO from PSTO

This module investigates whether the PBTO
(parameterized binary tree object) universal property
can be derived from the PSTO (parameterized
snoclist-of-trees object).

The PSTO has `nil : 1 → T` and `snoc : T × T → T`
with elimination: for `f : A → X` and
`g : X × T → X`, there exists a unique
`φ : A × T → X` satisfying
`φ(a, nil) = f(a)` and
`φ(a, snoc(t₁, t₂)) = g(φ(a, t₁), t₂)`.

The PBTO has the same constructors but with
elimination: for `f : A → X` and `g : X × X → X`,
there exists a unique `ψ : A × T → X` satisfying
`ψ(a, nil) = f(a)` and
`ψ(a, snoc(t₁, t₂)) = g(ψ(a, t₁), ψ(a, t₂))`.

The difference: the PSO fold passes `t₂` as raw
data, while the PBTO recurses into `t₂` as well.

Each section below attempts a different construction
strategy, documenting the outcome.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPSTO C]

/-!
## Approach 1: Direct enriched carrier `T × X`

Mirror the PBTO→PSTO construction in reverse.
Carrier: `cfpProd T X`, tracking the tree alongside
the result.

- Base: `a ↦ (nil, f(a))`
- Step: `((t₁, x₁), t₂) ↦ (snoc(t₁, t₂), g(x₁, ???))`

The `???` must be `ψ(a, t₂)`, the recursive result
on the element.  The PSO fold provides `x₁ = φ(a, t₁)`
(the recursive result on the accumulated snoclist) but
gives `t₂` as raw data, not `ψ(a, t₂)`.

The step morphism type for the PSO is
`cfpProd X T ⟶ X` (i.e., `(X × B) → X` with `B = T`).
To use the enriched carrier `T × X`, the step is
`cfpProd (cfpProd T X) T ⟶ cfpProd T X`.
We can define the first component `snoc(t₁, t₂)`,
but for the second component we need `g(x₁, ψ(a, t₂))`
and we only have `x₁` and raw `t₂`.

The attempt below uses a placeholder `_` at the
point where the construction gets stuck.
-/

section Approach1

variable {A X : C}
  (f : A ⟶ X) (g : cfpProd X X ⟶ X)

/-- Attempt 1: enriched carrier base morphism.
`a ↦ (nil, f(a))`. -/
private def a1Base :
    A ⟶ cfpProd p.T X :=
  cfpLift (cfpTerminalFrom A ≫ p.nil) f
  where p := HasPSTO.isPSTO (C := C)

-- Attempt 1: enriched carrier step morphism.
-- Given `((t₁, x₁), t₂)`, the first component is
-- `snoc(t₁, t₂)`.  The second component requires
-- `g(x₁, ψ(a, t₂))`, but `ψ(a, t₂)` is not
-- available from the PSO step — only `t₂` (raw)
-- is given.
--
-- RESULT: STUCK.  Cannot fill the second argument
-- of `g` with `ψ(a, t₂)` because `ψ` is what we
-- are trying to define, and the PSO step only
-- provides the raw element `t₂`, not the recursive
-- result on it.

-- We cannot write a correct a1Step.  The type would
-- be:
-- cfpProd (cfpProd p.T X) p.T ⟶ cfpProd p.T X
-- The first component (tree tracking) is definable:
--   snoc(t₁, t₂) = cfpLift t1 t2 ≫ snoc
-- The second component (result) needs g(x₁, ψ(a,t₂))
-- but ψ is unavailable.

end Approach1

/-!
## Approach 2: PSO paramorphism

The PSO paramorphism step sees
`(a, l, b, φ(a, l))` where `l` is the raw init,
`b` is the raw element, and `φ(a, l)` is the
recursive result on the init.

For the PBTO, the step needs
`g(ψ(a, t₁), ψ(a, t₂))`.  The paramorphism
provides `ψ(a, t₁)` (as the recursive result on
the init), but `t₂ = b` is only raw data —
`ψ(a, t₂)` is not available.

RESULT: The paramorphism provides strictly more than
the basic fold (it gives `l` and `φ(a, l)` rather
than just `φ(a, l)`), but it still does not recurse
into the element `b`.  We are in the same position
as Approach 1: the recursive result on `b` is not
available.
-/

section Approach2

-- The paramorphism step type for PSTO (B = L = T):
-- cfpProd A (cfpProd T (cfpProd T X)) ⟶ X
-- Components available: (a, (init, (elem, φ(a, init))))
-- We need: g(φ(a, init), φ(a, elem))
-- We have: φ(a, init) but NOT φ(a, elem).

-- No code to write: the paramorphism does not
-- provide the recursive result on the element,
-- for the same structural reason as Approach 1.

-- A trivial definition to make the section
-- non-empty for Lean's parser.
private def a2Placeholder : True := trivial

end Approach2

/-!
## Approach 3: Fixed-point equation

Define `ψ` by the self-referential equation:

`ψ = IsPSO.elim f (cfpLift (cfpFst X T) (cfpSnd X T ≫ ψ) ≫ g)`

In other words, the step morphism `h : X × T → X`
is defined as `h(x, t₂) = g(x, ψ(a, t₂))`, where
`ψ` is the very morphism being defined.

This is circular: the step function depends on `ψ`,
which is defined using `IsPSO.elim` with that step
function.  We attempt it to see the exact Lean error.
-/

section Approach3

-- The definition would be:
-- def a3Elim (f : A ⟶ X) (g : cfpProd X X ⟶ X) :
--     cfpProd A p.T ⟶ X :=
--   IsPSO.elim f
--     (cfpLift
--       (cfpFst X p.T)
--       (cfpSnd X p.T ≫ a3Elim f g) ≫ g)
--
-- RESULT: Lean rejects this with:
-- "unknown identifier 'a3Elim'"
-- (or a "failed to prove termination" error if
-- written as a recursive `def`).  The definition
-- is not structurally recursive and there is no
-- termination measure available in the abstract
-- categorical setting.

-- We can verify that the step morphism TYPE is
-- well-formed if we had a hypothetical `ψ`:
-- from `A × T`, given `(x₁, t₂)` in `X × T`,
-- produce `g(x₁, ψ(a, t₂))`.
-- Here `ψ : A × T → X` and `g : X × X → X`.
-- But the PSO step only sees `X × T`, not `A`.
-- With access to `a`, we can form `(a, t₂)` and
-- apply `ψ`, but `a` is not in the step's scope.

-- The self-reference prevents direct definition.

end Approach3

/-!
## Approach 4: Double PSO fold (nested folds)

Since `T ≅ List(T)`, each element `t₂ : T` is
itself a snoclist. The idea: use an outer PSO fold
for the snoclist structure, and within the step
function, use an INNER PSO fold to recurse into the
element `t₂`.

Outer fold step: given `(x₁, t₂)` where `x₁` is
the accumulated result on the init, apply an inner
fold to `t₂` to get `ψ(a, t₂)`, then combine via
`g(x₁, ψ(a, t₂))`.

The inner fold on `t₂` needs its own base and step.
For `ψ(a, nil) = f(a)` (same base as outer), and
for `ψ(a, snoc(s₁, s₂))` we again need both
recursive results... which requires another inner
fold, ad infinitum.

RESULT: The inner fold faces the same structural
problem as the outer one.  To process `t₂` using an
inner PSO fold, the inner step would need
`g(innerResult, innerRecOnSubelement)`, recreating
the original problem at a deeper level.

However, we CAN define a morphism if we use the
inner fold with a DIFFERENT step function — one
that does not require recursion into sub-elements.
This would compute something different from the
PBTO catamorphism.

We demonstrate the circular dependency below.
-/

section Approach4

-- To make the inner fold work, we need a step
-- morphism for processing elements of t₂.
-- The type of the inner step would be:
--   cfpProd X T ⟶ X
-- which is exactly what we're trying to build
-- for the outer fold.  Hence circular.

-- Concretely: define the step as
-- outer_step(x₁, t₂) =
--   g(x₁, IsPSO.elim f inner_step (a, t₂))
-- where inner_step(x, t) = g(x, ???)
-- and ??? requires yet another recursive call.

-- The non-circular variant would use a fixed
-- inner step that doesn't need recursion, but
-- that computes the wrong function.

-- For example, using `cfpSnd X T ≫ f ≫ ...`
-- would apply f at leaves but not recurse into
-- branches of the element, computing at most
-- one level of the tree rather than the full
-- catamorphism.

end Approach4

/-!
## Approach 5: Product carrier `X × X`

Track two copies of the result type: one for the
accumulated fold, one for... what?

For the PBTO step, we need `g(ψ(a, t₁), ψ(a, t₂))`.
Having carrier `X × X` could track both, but the
step morphism receives `((x₁, x₂), t₂)` and must
produce a new `(x₁', x₂')`.

There is no clear meaning for `x₂` that would help:
- If `x₂` tracks the recursive result on the
  previous element, it does not help compute the
  result on the current element `t₂`.
- The pair `(x₁, x₂)` gives us information about
  `t₁` (the init) but not about `t₂` (the new
  element).

RESULT: STUCK for the same structural reason.
No matter what carrier we use, the PSO fold
processes elements left-to-right, and the step
function receives each element as raw data.  It
cannot recurse into an element because that would
require calling the very fold being defined.
-/

section Approach5

-- No code to write: the carrier choice does not
-- resolve the structural mismatch between PSO
-- (recurse left, data right) and PBTO (recurse
-- both).

end Approach5

/-!
## Summary

All five approaches fail for the same structural
reason: the PSO/PSTO fold processes a snoclist by
recursing on the accumulated prefix (left component)
and passing each element (right component) as raw
data.  The PBTO catamorphism requires recursion into
BOTH components.

In the PSO step `(x₁, t₂) ↦ ...`:
- `x₁` is the recursive result on the init (available)
- `t₂` is the raw element (NOT recursed into)

To get the recursive result on `t₂`, one would need
to call the fold itself on `t₂`, which creates a
circular dependency.

This suggests that PSTO does not imply PBTO in a
general category with finite products.  The PSTO
captures "list-like" recursion (one recursive
argument), while the PBTO captures "tree-like"
recursion (two recursive arguments).  Although the
underlying objects `T` coincide (since `T ≅ List(T)`
in both cases), the elimination principles have
different strength.

The reverse direction (PBTO → PSTO) works because
the PBTO catamorphism can handle both recursive
arguments, and we can define the PSTO step by
recursing on the init while treating the element as
data (using the second copy of the recursive result
trivially).

A direct PSTO → PBTO construction may require
additional structure, such as:
- An internal fixed-point operator (to solve the
  self-referential equation in Approach 3)
- A parameterized NNO (to iterate the Φ operator
  from the fixed-point equation finitely many
  times, bounded by tree depth)
- An exponential object `X^T` (to internalize the
  function space needed for the inner recursion in
  Approach 4)
-/

end GebLean
