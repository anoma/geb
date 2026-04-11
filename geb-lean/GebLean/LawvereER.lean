import Mathlib.Data.Fin.Tuple.Basic

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

/-- Bounded summation helper: iterates `f` from
`0` to `bound - 1` and sums the results. -/
def natBSum (bound : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 0 (fun i acc => acc + f i) bound

/-- Bounded product helper: iterates `f` from `0`
to `bound - 1` and multiplies the results, with
an empty product of `1`. -/
def natBProd (bound : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 1 (fun i acc => acc * f i) bound

/-- Standard interpretation of an `n`-ary term as
a function `(Fin n → ℕ) → ℕ`. -/
def ERMor1.interp : {n : ℕ} → ERMor1 n →
    (Fin n → ℕ) → ℕ
  | _, ERMor1.zero, _ => 0
  | _, ERMor1.succ, ctx => (ctx 0).succ
  | _, ERMor1.proj i, ctx => ctx i
  | _, ERMor1.sub, ctx => (ctx 0) - (ctx 1)
  | _, ERMor1.comp f g, ctx =>
      f.interp (fun i => (g i).interp ctx)
  | _, ERMor1.bsum f, ctx =>
      natBSum (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx)))
  | _, ERMor1.bprod f, ctx =>
      natBProd (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx)))

/-- Interpretation of `zero`. -/
@[simp] theorem ERMor1.interp_zero
    (ctx : Fin 0 → ℕ) :
    ERMor1.zero.interp ctx = 0 :=
  rfl

/-- Interpretation of `succ`. -/
@[simp] theorem ERMor1.interp_succ
    (ctx : Fin 1 → ℕ) :
    ERMor1.succ.interp ctx = (ctx 0).succ :=
  rfl

/-- Interpretation of `proj`. -/
@[simp] theorem ERMor1.interp_proj
    {k : ℕ} (i : Fin k) (ctx : Fin k → ℕ) :
    (ERMor1.proj i).interp ctx = ctx i :=
  rfl

/-- Interpretation of `sub`. -/
@[simp] theorem ERMor1.interp_sub
    (ctx : Fin 2 → ℕ) :
    ERMor1.sub.interp ctx = (ctx 0) - (ctx 1) :=
  rfl

/-- Interpretation of `comp`. -/
@[simp] theorem ERMor1.interp_comp
    {k n : ℕ} (f : ERMor1 k)
    (g : Fin k → ERMor1 n) (ctx : Fin n → ℕ) :
    (ERMor1.comp f g).interp ctx =
      f.interp (fun i => (g i).interp ctx) :=
  rfl

/-- Interpretation of `bsum`. -/
@[simp] theorem ERMor1.interp_bsum
    {k : ℕ} (f : ERMor1 (k + 1))
    (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.bsum f).interp ctx =
      natBSum (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx))) :=
  rfl

/-- Interpretation of `bprod`. -/
@[simp] theorem ERMor1.interp_bprod
    {k : ℕ} (f : ERMor1 (k + 1))
    (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.bprod f).interp ctx =
      natBProd (ctx 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctx))) :=
  rfl

/-- Tuple of `m` `n`-ary elementary recursive
terms, viewed as a single morphism from an
`n`-fold context to an `m`-fold context in the
Lawvere theory. -/
def ERMorN (n m : ℕ) : Type := Fin m → ERMor1 n

/-- Standard interpretation of an `ERMorN n m`
tuple as a function `(Fin n → ℕ) → (Fin m → ℕ)`. -/
def ERMorN.interp {n m : ℕ} (f : ERMorN n m)
    (ctx : Fin n → ℕ) : Fin m → ℕ :=
  fun i => (f i).interp ctx

/-- The identity morphism at arity `n`: the tuple
of `n` projections. -/
def ERMorN.id (n : ℕ) : ERMorN n n :=
  fun i => ERMor1.proj i

/-- Composition of `ERMorN` tuples: each output
component of `g : ERMorN m k` is substituted with
`f : ERMorN n m` via `ERMor1.comp`. -/
def ERMorN.comp {n m k : ℕ}
    (f : ERMorN n m) (g : ERMorN m k) :
    ERMorN n k :=
  fun i => ERMor1.comp (g i) f

/-- The identity tuple interprets as the identity
function on contexts. -/
@[simp] theorem ERMorN.interp_id
    {n : ℕ} (ctx : Fin n → ℕ) :
    (ERMorN.id n).interp ctx = ctx :=
  rfl

/-- Composition of tuples interprets as function
composition of their interpretations. -/
@[simp] theorem ERMorN.interp_comp
    {n m k : ℕ} (f : ERMorN n m) (g : ERMorN m k)
    (ctx : Fin n → ℕ) :
    (f.comp g).interp ctx =
      g.interp (f.interp ctx) :=
  rfl

end GebLean
