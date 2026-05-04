# Lawvere Tree-ER Sub-project 4g.2: ℕ-ER ↔ Tree-ER Isomorphism — Design

## Overview

Sub-project 4g.2 of the Phase 4g tree-native parallel development.
Establishes a bidirectional categorical isomorphism
`LawvereERCat ≅ LawvereTreeERCat` (on the nose at the quotient
level), along with the Gödel arithmetic machinery that makes the
construction go through.  The approach is **Lean-first**:
Szudzik-based arithmetic is written as plain Lean functions with
proved reduction rules, then lifted into `TreeERMor1` terms with
agreement theorems linking the two layers.

### Relation to the larger workstream

See `.session/workstreams/lawvere-elementary-recursive.md` for the
full five-sub-project structure.  Summary of the relevant pieces:

* **4g.1 (complete):** Tree-ER core Lawvere theory with `TreeMor1`
  inductive, `TreeERMor1` depth-≤-2 subtype, category with
  `HasChosenFiniteProducts`, faithful interp functor, faithful
  inclusion into `LawvereBTQuotCat`.
* **4g.2 (this spec):** ℕ-ER ↔ Tree-ER isomorphism + Gödel
  arithmetic.
* **4g.3:** Transport of Phase 4f results (Primrec', tower bound,
  Ackermann non-fullness, tetration non-elementarity) to the tree
  side.
* **4g.4:** Lex-level parity (`LawvereTreeERLexCat`) and
  Lex-level isomorphism.
* **4g.5:** Central correspondence documentation.

## Scope

### In scope

* **Layer 1 (generic Lean arithmetic)** in `GebLean/Utilities/SzudzikSeq.lean`:
  * `seqPack : List ℕ → ℕ` — encode a list via iterated right-
    associated `Nat.pair`.
  * `seqAt : ℕ → ℕ → ℕ` — extract index `i` from packed sequence.
  * Round-trip lemma: `seqAt (seqPack xs) i = xs.getD i 0` (or
    matching default).
  * `treeFoldOnCode : ℕ → α → (α → α → α) → α` — tree fold
    simulated on a Gödel code `code(t) := 1 + Nat.pair (code l)
    (code r)`, base `0 = code(leaf)`.
  * Correctness: `treeFoldOnCode (encodeBT t) h₀ h₁ = BT.fold h₀
    (fun l r => h₁ l r) t` (shape may differ depending on mathlib
    BT.fold's signature; adapt accordingly).
  * `tupleRecN : ∀ k, ...` — finite-arity mutumorphism via
    iterated Szudzik pairing.
  * Growth-bound lemmas showing each primitive's output is
    elementary in the input size, so all of the above are
    expressible as ER functions on ℕ (confirming "these Lean
    functions are all in E₃").

* **Layer 2 (tree-ER syntactic arithmetic)** in
  `GebLean/LawvereTreeERArith.lean`:
  * `TreeERMor1.succOnCode : TreeERMor1 1` — increment a
    Gödel-encoded BT code.
  * `TreeERMor1.subOnCode : TreeERMor1 2` — cut-off subtraction
    on codes.
  * `TreeERMor1.bsumOnCode : TreeERMor1 (k+1) → TreeERMor1 (k+1)`
    — bounded sum.
  * `TreeERMor1.bprodOnCode : TreeERMor1 (k+1) → TreeERMor1 (k+1)`
    — bounded product.
  * `TreeERMor1.szudzikPair : TreeERMor1 2` — Szudzik's pairing
    on codes.
  * `TreeERMor1.szudzikUnpairL`, `szudzikUnpairR : TreeERMor1 1`
    — projections of the unpairing.
  * `TreeERMor1.treeFoldOnCode` — course-of-values recursion tree
    fold.
  * `TreeERMor1.mutuFoldViaPair` — tree-ER mutumorphism via
    pairing (for the ℕ-ER side, since tree-ER already has native
    mutumorphism via `BTMor1.fold`'s m-parameter).
  * For each: an `@[simp]` agreement theorem of the form
    `T.interp ctx = <Layer 1 formula applied to encodeBT ctx,
    result decoded>`.

* **Layer 3 (translation functors + isomorphism)** in
  `GebLean/LawvereTreeERLawvereEquiv.lean`:
  * `J : LawvereERCat ⥤ LawvereTreeERCat` — structural translation
    of `ERMor1` generators via Layer 2 primitives.
  * `K : LawvereTreeERCat ⥤ LawvereERCat` — structural translation
    of `TreeMor1` (depth-≤-2) via Layer 1/2 primitives on the ℕ
    side.
  * `K ∘ J = 1_{LawvereERCat}` on the nose at the quotient level.
  * `J ∘ K = 1_{LawvereTreeERCat}` on the nose at the quotient
    level.
  * Natural isomorphism `btInterp ∘ K ≅ erInterpFunctor` induced
    by `encodeVec` applied componentwise.

* **Tests** in `GebLeanTests/` mirroring the three library files.

### Out of scope

* Lex-level isomorphism parity — deferred to **4g.4**.
* Transport of Phase 4f non-fullness / tower-bound results to
  the tree side — deferred to **4g.3**.
* Central correspondence documentation — deferred to **4g.5**.
* Any restructuring of `LawvereBTPrimrec.lean`'s `encodeBT` /
  `decodeBT` — we consume them as-is.

## Design decisions

### D1: Reuse Mathlib's Szudzik

`Mathlib.Data.Nat.Pairing` provides `Nat.pair`, `Nat.unpair`, and
their reduction rules (`pair_unpair`, `unpair_pair`, bound
lemmas).  The formulas match Szudzik's 2006 paper verbatim.  We
import and consume; no re-derivation.

### D2: Three-layer spec / implementation / agreement pattern

Every piece of tree-ER arithmetic is structured:

* A Lean function in Layer 1 — plain ℕ arithmetic with proved
  reduction rules.
* A `TreeERMor1` term in Layer 2 — syntactic encoding.
* An `@[simp]` agreement theorem linking the two:
  `T.interp ctx = decodeBT (LeanFunction (encodeBT (ctx 0)) ...)`.

This separates mathematical content (Layer 1) from syntactic
encoding (Layer 2).  Proofs about the arithmetic can be done in
whichever layer is easier and transported via the agreement
theorem.

### D3: Tree fold via course-of-values recursion on Gödel codes

Following Rose 1984 Ch. 2 Thm. 2.2.3 and Leivant 1999:

Given `code(leaf) = 0`, `code(branch l r) = 1 + Nat.pair (code l)
(code r)`:

```text
fold'(n) = h₀                           if n = 0
fold'(n) = h₁(fold'(unpair(n-1).1),
              fold'(unpair(n-1).2))    otherwise
```

Both recursive arguments are strictly `< n` by
`Nat.unpair_left_le` and `Nat.unpair_right_le`, so this is strictly
course-of-values recursion on the code.

Implementation: build a fold table `[fold'(0), fold'(1), ...,
fold'(N)]` packed as a single ℕ via iterated Szudzik; populate
via `bsum`-style bounded iteration; at the end, look up
`fold'[code(t)]`.

Growth bound: output is at most `H^{2^d}` where `H` bounds the
step function and `d` is tree depth.  Because Szudzik's `pair` is
quadratic in `max` (from
`Nat.pair_lt_max_add_one_sq`), iterated `d` times gives single-
exponential — within E₃ for elementary `H`.

### D4: Mutumorphism at the generic Lean layer

Finite-arity mutumorphism (`k` mutually-recursive functions) is
fundamentally about tupling `k` values into a single ℕ via
iterated right-associated pairing, then running one bounded
iteration returning the packed state, then unpacking at each
index.  This is a generic construction — we place it in Layer 1
as `Nat.tupleRecN`, and Layer 2 wraps it as
`TreeERMor1.mutuFoldViaPair`.

Note: tree-ER already has native mutumorphism via
`BTMor1.fold`'s m-parameter (exposed as `TreeERMor1.mutuFold` in
4g.1).  `mutuFoldViaPair` is specifically for interpreting ℕ-ER
mutumorphism on the tree side — i.e., the tree-ER term that
corresponds to `k` simultaneously-recursing `ERMor1` functions.

### D5: "Isomorphism on the nose" at the quotient level

`K ∘ J = 1_{LawvereERCat}` means: for every `f : ERMorNQuo n m`,
`(K ∘ J).map f = f`.  Because `ERMorNQuo` is a quotient,
equality holds iff interpretations agree as functions `(Fin n →
ℕ) → (Fin m → ℕ)`.

Proof pattern: let `f` be represented by `f_raw : ERMorN n m`.
Then `J.map f_raw` is a tree-ER term whose interpretation agrees
with `decodeVec ∘ f_raw.interp ∘ encodeVec`.  `K.map (J.map
f_raw)` is an ER term whose interpretation agrees with `encodeVec
∘ decodeVec ∘ f_raw.interp ∘ encodeVec ∘ decodeVec`.  Via
`Nat.Primcodable`'s round-trip lemmas `encodeBT ∘ decodeBT = id`
and `decodeBT ∘ encodeBT = id`, this reduces to `f_raw.interp`,
giving quotient equality with `f`.

Same pattern for `J ∘ K = 1_{LawvereTreeERCat}`.

### D6: Novel formalization — the K translator

Leivant 1999 establishes the function-class equality "depth-2
fold = E₃" by general ramification arguments but does not exhibit
a concrete translator.  Rose 1984 gives the course-of-values
construction abstractly.  As far as our Phase 4g.2 research
identified, **no prior Lean, Coq, Agda, or Isabelle formalization
exhibits the constructive translator** from tree-fold operations
to ℕ-level elementary recursion on Gödel codes.  The spec flags
this as a contribution worth prominence in the 4g.5
documentation.

## Module layout

### Library modules

1. **`GebLean/Utilities/SzudzikSeq.lean`** (~300–400 lines)

   Layer 1 contents:

   * `Nat.seqPack`, `Nat.seqAt`, round-trip lemma.
   * `Nat.treeFoldOnCode`, correctness vs. `BT.fold`.
   * `Nat.tupleRecN`, correctness.
   * Growth-bound lemmas: each primitive's output is bounded by a
     fixed-height tower of its inputs, confirming E₃ membership.

   Imports: `Mathlib.Data.Nat.Pairing`, `GebLean.LawvereBT`
   (for `BT`, `BT.fold`), `GebLean.LawvereBTPrimrec` (for
   `encodeBT`, `decodeBT`).

2. **`GebLean/LawvereTreeERArith.lean`** (~500–700 lines)

   Layer 2 contents:

   * Tree-ER syntactic arithmetic (8 primitives).
   * `@[simp]` agreement theorems linking each to its Layer-1
     counterpart.

   Imports: `GebLean.LawvereTreeERInterp`,
   `GebLean.Utilities.SzudzikSeq`.

3. **`GebLean/LawvereTreeERLawvereEquiv.lean`** (~400–600 lines)

   Layer 3 contents:

   * `J : LawvereERCat ⥤ LawvereTreeERCat`.
   * `K : LawvereTreeERCat ⥤ LawvereERCat`.
   * Mutual-inverse proofs.
   * Natural isomorphism `btInterp ∘ K ≅ erInterpFunctor`.

   Imports: `GebLean.LawvereTreeERArith`,
   `GebLean.LawvereERInterp`.

### Test modules

* `GebLeanTests/Utilities/SzudzikSeq.lean` — Layer 1 `#guard`
  sanity tests for `seqPack`/`seqAt` on specific small lists,
  `treeFoldOnCode` correctness for small trees, `tupleRecN`
  example.
* `GebLeanTests/LawvereTreeERArith.lean` — Layer 2
  type-checks and small `#guard`s via interpretation.
* `GebLeanTests/LawvereTreeERLawvereEquiv.lean` — Layer 3
  `example` type-checks for the functors, their `Faithful`
  instances, and the natural isomorphism.

### Registration

* `GebLean/Utilities.lean` — add `import
  GebLean.Utilities.SzudzikSeq`.
* `GebLean.lean` — add three new imports for Layer 2, Layer 3
  modules.
* `GebLeanTests.lean` — three test-module imports.

## Detailed content per layer

### Layer 1 detail

```lean
-- Sequence encoding (iterated right-associated Szudzik)
def Nat.seqPack : List ℕ → ℕ
  | []      => 0
  | x :: xs => Nat.pair x xs.seqPack + 1

def Nat.seqAt : ℕ → ℕ → ℕ
  | 0,     _     => 0
  | _ + 1, 0     => (Nat.unpair (n - 1)).1  -- illustrative
  | n + 1, i + 1 => seqAt (Nat.unpair n).2 i

theorem Nat.seqAt_seqPack_lt {xs : List ℕ} {i : ℕ}
    (h : i < xs.length) :
    Nat.seqAt (Nat.seqPack xs) i = xs.get ⟨i, h⟩ := ...

-- Tree fold via course-of-values on Gödel codes
def Nat.treeFoldOnCode {α : Type*}
    (n : ℕ) (h₀ : α) (h₁ : α → α → α) : α := ...

theorem Nat.treeFoldOnCode_encodeBT {α : Type*}
    (t : BT) (h₀ : α) (h₁ : α → α → α) :
    Nat.treeFoldOnCode (encodeBT t) h₀ h₁ =
      BT.fold h₀ h₁ t := ...
```

The exact implementation of `treeFoldOnCode` uses a fold-table
approach: populate `[fold'(0), fold'(1), ..., fold'(n)]` via
`List.range` + bounded iteration, then index.  The `seqPack` /
`seqAt` utilities give us the packing/lookup.

### Layer 2 detail

Each Layer-2 primitive follows the pattern:

```lean
def TreeERMor1.succOnCode : TreeERMor1 1 := ... -- specific term

@[simp] theorem TreeERMor1.succOnCode_interp
    (ctx : Fin 1 → BT) :
    TreeERMor1.succOnCode.interp ctx =
      decodeBT (encodeBT (ctx 0) + 1) := by
  -- proof: unfold succOnCode, simp via tree-ER interp reduction
  --        lemmas, reduce to Nat.succ via encodeBT_decodeBT.
  ...
```

The construction of `TreeERMor1.succOnCode` itself is the
smallest `TreeERMor1` term that realizes the Gödel successor.
Natural choice: build a tree-ER analog of the shell-traversal
succ via `branch`/`fold` on a tally-encoded auxiliary.

The most complex Layer-2 term is `TreeERMor1.treeFoldOnCode`.
Because `TreeERMor1`'s `fold` constructor is natively available
at depth ≤ 1 and can be composed with other depth-≤-1 terms to
give depth-2, the implementation mirrors Layer 1's fold-table
approach using `TreeERMor1.fold1` for the inner recursion and
`TreeERMor1.fold` for the outer lookup.

### Layer 3 detail

```lean
def ERMor1.toTreeER : {n : ℕ} → ERMor1 n → TreeERMor1 n
  | _, .zero         => TreeERMor1.leaf
  | _, .succ         => TreeERMor1.succOnCode
  | _, .proj i       => TreeERMor1.proj i
  | _, .sub          => TreeERMor1.subOnCode
  | _, .comp f g     =>
      TreeERMor1.comp f.toTreeER (fun i => (g i).toTreeER)
  | _, .bsum f       => TreeERMor1.bsumOnCode f.toTreeER
  | _, .bprod f      => TreeERMor1.bprodOnCode f.toTreeER

def TreeMor1.toERMor1_depth2 :
    {n : ℕ} → (t : TreeMor1 n) → t.foldDepth ≤ 2 → ERMor1 n
  | _, .leaf, _       => ERMor1.zero'
  | _, .branch l r, h =>
      ERMor1.branchOnCode l.toERMor1_depth2 r.toERMor1_depth2
  | _, .proj i, _     => ERMor1.proj i
  | _, .comp f g, h   => ERMor1.comp ... ...
  | _, .fold m f g t j, h => ERMor1.treeFoldOnCode ...
```

`J : LawvereERCat ⥤ LawvereTreeERCat` lifts `ERMor1.toTreeER`
componentwise through `ERMorN` tuples and the setoid quotient.
`K` lifts `TreeMor1.toERMor1_depth2`.

Inverse proofs `K(J(f)) = f` and `J(K(g)) = g` reduce (at the
quotient level) to agreement of interpretations, which follow
from the Layer-2 agreement theorems + `encodeBT_decodeBT` /
`decodeBT_encodeBT`.

## Build stages

Three natural stages, each producing working and testable code:

### Stage α: Layer 1 (generic Lean arithmetic)

Deliverable: `GebLean/Utilities/SzudzikSeq.lean` with all
functions + reduction rules proved.  Standalone and testable
without any tree-ER machinery.

### Stage β: Layer 2 (tree-ER arithmetic + agreement)

Deliverable: `GebLean/LawvereTreeERArith.lean` with 8 `TreeERMor1`
primitives + 8 agreement theorems.  Depends on Stage α.

### Stage γ: Layer 3 (translation functors + isomorphism)

Deliverable: `GebLean/LawvereTreeERLawvereEquiv.lean` with `J`,
`K`, and proofs of `K ∘ J = 1`, `J ∘ K = 1`, natural iso with
`erInterpFunctor`.  Depends on Stage β.

Each stage has its own test module, mergeable independently.

## Testing plan

### Stage α tests (`GebLeanTests/Utilities/SzudzikSeq.lean`)

* `#guard Nat.seqPack [1, 2, 3] = <specific value>`.
* `#guard Nat.seqAt (Nat.seqPack [1, 2, 3]) 1 = 2`.
* `#guard Nat.treeFoldOnCode 0 ... = <base case value>` — tree
  fold reduces correctly at the `leaf` code.
* `#guard Nat.treeFoldOnCode (1 + Nat.pair 0 0) ... = <branch
  case value>` — tree fold reduces correctly at one branch.
* `example : Nat.treeFoldOnCode (encodeBT t) h₀ h₁ = BT.fold h₀
  h₁ t` for a specific small `t` — correctness type-checks.

### Stage β tests (`GebLeanTests/LawvereTreeERArith.lean`)

* Each agreement theorem yields a `#guard` — for a specific
  `ctx`, the tree-ER term's interpretation matches the
  decodeBT-wrapped Layer-1 formula.
* `example` type-checks that each `TreeERMor1` primitive has the
  expected arity.

### Stage γ tests (`GebLeanTests/LawvereTreeERLawvereEquiv.lean`)

* `example : LawvereERCat ⥤ LawvereTreeERCat := J`.
* `example : LawvereTreeERCat ⥤ LawvereERCat := K`.
* `example : K ∘ J = (𝟭 _)` — the categorical identity.
* `example : J ∘ K = (𝟭 _)`.
* `example : btInterp ∘ K ≅ erInterpFunctor` — natural
  isomorphism.

## Completion criteria

Sub-project 4g.2 is complete when:

1. All three library modules build cleanly — zero warnings, zero
   `sorry`, zero `admit`.
2. Layer 1 contains all generic Lean arithmetic primitives with
   proved reduction rules.
3. Layer 2 contains all 8 tree-ER primitives with proved
   `@[simp]` agreement theorems.
4. Layer 3 contains `J`, `K`, and proofs of `K ∘ J = 1`, `J ∘ K
   = 1`.
5. The natural iso `btInterp ∘ K ≅ erInterpFunctor` is
   established.
6. All tests pass.
7. Workstream tracker updated to mark 4g.2 complete.
8. (Optional) Mutumorphism worked example in test file showing
   tree-ER mutumorphism and ℕ-ER mutumorphism give the same
   result via the isomorphism.

## Literature references

* Szudzik, M. *An Elegant Pairing Function* (2006). Formulas
  implemented in `Mathlib.Data.Nat.Pairing`.
* Rose, H. E. *Subrecursion: Functions and Hierarchies*.  Oxford
  Logic Guides 9 (1984), Ch. 2 Thm. 2.2.3: course-of-values
  recursion bounded by E₃ stays in E₃.
* Leivant, D. *Ramified recurrence and computational complexity
  III.*  APAL 96 (1999): depth-2 fold over free algebras = E₃
  (the function-class equality we are constructively
  witnessing).
* Fokkinga, M. *Tupling and Mutumorphisms.*  The Squiggolist
  1(4), 81–82 (1989): finite-arity mutumorphism via tupling.

## Open questions

* **Exact signature of `Nat.treeFoldOnCode`:** depends on
  whether `BT.fold` is defined natively in `LawvereBT.lean` (if
  so, match its signature) or derived ad-hoc for this spec.
  Resolve during Stage α implementation.
* **Growth-bound lemma precision:** we need each Layer-1
  primitive's output to be bounded by a tower of its input
  (confirming E₃), but the *exact* tower height (e.g., `tower 3
  x` vs `tower 5 x`) is implementation-dependent.  Resolve
  during Stage α; the bounds themselves are not load-bearing for
  Layer 2 or 3 correctness.
* **Mutumorphism arity parameterization:** `Nat.tupleRecN` can be
  parameterized by `k : ℕ` with a fixed encoding, or by a family
  of types with a variadic encoding.  Pick the simpler form
  (fixed `k`, homogeneous type) unless a variadic need arises.
  Resolve during Stage α.
