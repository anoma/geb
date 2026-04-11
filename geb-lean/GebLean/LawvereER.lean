import Mathlib.Data.Fin.Basic

/-!
# Lawvere Theory of Elementary Recursive Functions

Inductive term type for the elementary recursive
functions, transcribing the generators of the
Wikipedia definition:

* `zero` — the zero constant (arity 0)
* `succ` — the successor function (arity 1)
* `proj i` — the `i`-th projection (arity `k`)
* `sub` — cut-off subtraction (arity 2)
* `comp` — composition
* `bsum` — bounded summation (first argument is
  the bound; on each iteration the first argument
  of the inner term is replaced by the loop index)
* `bprod` — bounded product (same convention)

The standard interpretation lives in
`(Fin n → ℕ) → ℕ`.  The tree-level interpretation
is deferred to later phases as a derived semantics
obtained via the existing Goedel encodings in
`GebLean/LawvereBTPrimrec.lean`.

See also `docs/lawvere-elementary-recursive.md`
for the Phase 0 design decisions.
-/

namespace GebLean

/-- Inductive term type for `n`-ary elementary
recursive functions.  Each generator has the
arity specified by the Wikipedia definition;
arities are adapted to other values via `comp`. -/
inductive ERMor1 : ℕ → Type where
  /-- The zero constant.  Arity 0. -/
  | zero : ERMor1 0
  /-- The successor function.  Arity 1. -/
  | succ : ERMor1 1
  /-- The `i`-th projection out of `k` arguments. -/
  | proj {k : ℕ} (i : Fin k) : ERMor1 k
  /-- Cut-off subtraction.  Arity 2. -/
  | sub : ERMor1 2
  /-- Composition: apply a `k`-ary term to the
  results of `k` `n`-ary terms. -/
  | comp {k n : ℕ} (f : ERMor1 k)
      (g : Fin k → ERMor1 n) : ERMor1 n
  /-- Bounded summation.  The first argument of
  `bsum f` is the bound; on each iteration, the
  first argument of `f` is replaced by the loop
  index. -/
  | bsum {k : ℕ} (f : ERMor1 (k + 1)) :
      ERMor1 (k + 1)
  /-- Bounded product.  Same convention as `bsum`. -/
  | bprod {k : ℕ} (f : ERMor1 (k + 1)) :
      ERMor1 (k + 1)

end GebLean
