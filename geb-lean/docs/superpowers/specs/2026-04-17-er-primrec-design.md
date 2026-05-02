# ER-Primrec: Derived Primitive Recursion for Wikipedia-Literal `ERMor1`

## Status

Design for a Stage β prerequisite mini-phase of the `LawvereNatBT`
sub-project (see
`docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`).
Enables Stage β Task 13 Part 2 (`ERMor1.foldBTLOnCode`) and
Task 14 (`NatBTMor1.toER`), which together enable the
three-stage categorical equivalence
`LawvereERCat ≃ LawvereNatBTCat`.

## Motivation

Stage β Task 14's back-translation `NatBTMor1.toER` requires an
`ERMor1`-side simulation of `BTL.fold` on a Gödel-encoded tree.
That simulation requires iterating the step function a dynamic
number of times over runtime-extracted sub-code values, with a
programmable accumulator.  `ERMor1`'s existing primitives
(`zero`/`succ`/`proj`/`sub`/`comp`/`bsum`/`bprod`) do not
directly express this: `bsum`/`bprod` iterate a fixed number of
times into sum or product, without threading a programmable
state.

The classical Kleene-Gödel construction provides the resolution:
primitive recursion is derivable in the Wikipedia-literal ER
fragment via a Gödel β-function (`β(a, b, i) = a mod (1 +
(i+1)*b)`) and bounded search for β-parameters.  The β-function
itself is a constant-depth arithmetic expression in ER; its
universal property (for any finite sequence there exist
witnesses) is a meta-level CRT theorem; bounded search over the
witness space is implementable via `bsum`.

This design records the concrete build-out: a chain of derived
ER terms (`div`, `mod`, `beta`, `boundedSearch`, `natRec`,
`foldBTLOnCode`) each with an `@[simp]`-marked correctness
theorem.  The `ERMor1` inductive is unchanged.  After the
mini-phase lands, downstream work (Task 14 onward) proceeds as
originally specified.

## Scope

### In scope

* Derived ER terms for division, modulo, Gödel β-function,
  bounded search, and primitive recursion with counter access.
* Correctness theorems linking each derived term to its
  mathematical counterpart (`Nat.div`, `Nat.mod`, the Gödel
  β-function, `Nat.find`, `Nat.rec`).
* The CRT existence lemma `Nat.beta_exists` establishing that
  for every finite sequence, β-witnesses exist with an
  elementary bound.
* ER-derived `BTL.fold`-on-Gödel-code as a direct application
  of the primitive-recursion toolkit.
* Showcase applications (`ERMor1.natAdd`, `ERMor1.natMul`,
  `ERMor1.factorial`) validating the combinator's expressive
  power.

### Out of scope

* Modification of the `ERMor1` inductive.  The 7 Wikipedia
  generators remain the exclusive primitives.
* General (unbounded) primitive recursion as a term — the
  derived `natRec` term lives inside E₃ by construction
  (Phase 4f.2's tower dominance extends), so unbounded
  primitive recursion (Ackermann-style) is not reachable and
  not claimed.
* Optimization of the resulting term size.  `natRec` via β +
  bounded search produces a large closed-form term; term size
  is bounded by an elementary function of the arities but is
  not small in practical terms.  Compile-time cost for
  `#guard` tests is accepted as the price of preserving the
  Wikipedia-literal generator set.

## Design decisions

### D1. Wikipedia-literal `ERMor1` preserved

The `ERMor1` inductive is exactly the 7 generators from the
Wikipedia definition: `zero`, `succ`, `proj`, `sub`, `comp`,
`bsum`, `bprod`.  All new primitives in this mini-phase are
*derived* — closed-form `ERMor1` terms built by composition of
the Wikipedia generators, with correctness theorems.  No
inductive constructor is added.

Rationale: the user-facing Stage β theorem is "Wikipedia-literal
ER ≃ LawvereNatBTCat", and this is the only route to that
theorem as a Lean statement.  Adding a constructor to `ERMor1`
would require a separate β-based reduction to return to
Wikipedia-literal terms, which reduces to building the same
infrastructure.

### D2. Gödel β-function as the witness oracle

Primitive recursion is derived via Gödel's β-function
`β(a, b, i) = a mod (1 + (i+1)*b)`.  The construction of
`natRec`:

1. Given `base`, `step`, counter `n`, and context `ctx`,
   SEARCH for parameters `(a, b)` such that
   `β(a, b, 0) = base.interp ctx` and
   `β(a, b, j+1) = step.interp (j :: β(a, b, j) :: ctx)` for
   all `j < n`.
2. Output `β(a, b, n)`.

The search uses bounded enumeration (via `bsum` + indicator
arithmetic) over `(a, b)` Szudzik-paired into a single ℕ.  The
bound comes from the CRT existence lemma `Nat.beta_exists`: for
any sequence `s : Fin N → ℕ`, there exist `a, b ≤ elementary
bound in max(s) and N` with `β(a, b, i) = s i`.

Rationale: Gödel β is the classical way to break the
circularity between "need primrec to encode sequences" and
"need sequence encoding to extract recursive values".  β itself
is constant-depth arithmetic; the existence of witnesses is a
meta-theorem, not a runtime computation.

### D3. `Nat.beta_exists` proved via CRT

The meta-level existence lemma uses the standard
Chinese-Remainder-Theorem construction:

* Let `M = max(s ∪ {N})`; let `m = M + 1`; let `b = m!`.
* The moduli `d_i = 1 + (i+1) * b` for `i < N` are pairwise
  coprime (standard elementary argument).
* Apply CRT to obtain `a` with `a mod d_i = s i` for all `i`.
* The resulting `a` is bounded by the product of the `d_i`,
  which is elementary in `M` and `N`.

If mathlib already provides `Nat.beta_exists` (or a close
equivalent via `Mathlib.Computability.Primrec` or
`Mathlib.Data.Nat.ModEq`), the mini-phase uses it directly.
Otherwise, the proof is approximately 50-100 lines of Lean
building on mathlib's CRT infrastructure
(`Nat.ModEq.chineseRemainder`, `Nat.factorial_dvd_factorial`,
etc.).

Rationale: CRT is the standard route; alternative encodings
(iterated pairing, base-B digit expansion) fail because
extraction requires iteration, which requires the recursion
we are trying to construct.

### D4. Module layout: arithmetic vs tree-specific

Two files for the mini-phase's permanent home:

* `GebLean/Utilities/ERArith.lean` — ER-derived arithmetic:
  `natPair`, `natUnpair`, `natSqrt` (existing, moved from
  current `Utilities/ERTreeArith.lean`), plus new `div`, `mod`,
  `beta`, `boundedSearch`, `natRec`, plus showcase
  applications.
* `GebLean/Utilities/ERTreeArith.lean` — ER-derived tree
  operations: `ERMor1.foldBTLOnCode` and related BTL ops built
  on `natRec`.

Rationale: the arithmetic toolbox is logically distinct from
tree interop.  `natPair`/`natUnpair`/`natSqrt` already in the
Task 12 commit (`29553fd0`) are ER-arithmetic, not tree, so
they belong in `ERArith.lean`.  The rename is a small diff
(git mv + import updates).

### D5. `boundedRec`: Meyer-Ritchie-Kleene bounded primitive recursion

Unrestricted primitive recursion is NOT derivable in
Wikipedia-literal ER: iterating an ER `step` a runtime-variable
number of times escapes E_3 in general (tetration is the
canonical witness, per Phase 4f.2).  Phase 4f.2's
`exists_lt_tower` theorem establishes that every ER term's
interpretation is dominated by a fixed elementary tower,
ruling out unrestricted `natRec` as a derived ER term.

What IS derivable in Wikipedia-literal ER is **bounded
primitive recursion** — primitive recursion where the client
provides an elementary upper bound on the result.  This is the
Meyer-Ritchie-Kleene characterization of E_3.  The combinator:

```lean
ERMor1.boundedRec {k : ℕ}
    (base : ERMor1 k)
    (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    ERMor1 (k + 1)
```

Correctness statements (two-part, conditional form):

```lean
-- (i) Unconditional pointwise upper bound
theorem ERMor1.interp_boundedRec_le_bound :
    (boundedRec base step bound).interp (Fin.cons n ctx) ≤
      bound.interp (Fin.cons n ctx)

-- (ii) Equality with Nat.rec when bound dominates the trace
theorem ERMor1.interp_boundedRec_of_bounded
    (h : ∀ j ≤ n,
      Nat.rec (base.interp ctx)
        (fun i prev =>
          step.interp (Fin.cons i (Fin.cons prev ctx)))
        j ≤
        bound.interp (Fin.cons j ctx)) :
    (boundedRec base step bound).interp (Fin.cons n ctx) =
      Nat.rec (base.interp ctx)
        (fun j prev =>
          step.interp (Fin.cons j (Fin.cons prev ctx)))
        n
```

The combinator always returns a well-defined value bounded by
`bound.interp (Fin.cons n ctx)`.  When the client's bound
pointwise dominates the `Nat.rec` trace, the result equals
`Nat.rec`.  When the bound is inadequate, the result is some
value `≤ bound`; nothing more is asserted.

A naïve `min`-based correctness statement of the form
`output = min (Nat.rec ...) (bound...)` is NOT provable with
the β-witness-search construction.  Counterexample: a step
function whose trace oscillates above and below the bound.
Whenever an intermediate trace value exceeds the bound, the
β-witness search range (sized for trace values ≤ bound per
`Nat.bounded_beta_exists`) cannot accommodate the actual
trace, the search fails, and the output is some value ≤ bound
unrelated to the final `Nat.rec` value.  The conditional
formulation above is what the construction realizes; downstream
clients supply pointwise bound-adequacy proofs to recover
exact `Nat.rec` semantics.

The `step` function receives both the counter `j` (slot 0 of
its input) and the previous result `prev` (slot 1).  This is
the maximally expressive primitive-recursion shape compatible
with the bound constraint.

Rationale: every E_3 function is representable as a bounded
primitive recursion (Meyer-Ritchie-Kleene), so `boundedRec`
captures the full E_3 expressive power without escaping it.
Task 13's `foldBTLOnCode` provides its own bound (derivable
from the input code via `bprod`-style composition of the step
output).  The showcase applications (`natAdd`, `natMul`,
`factorial`) each derive their own polynomial bound
straightforwardly.

### D6. Correctness by induction + CRT appeal

`interp_boundedRec_le_bound` follows directly from the
construction: the outermost `minN` clamps the output to
`bound.interp (Fin.cons n ctx)` regardless of the search
result.

`interp_boundedRec_of_bounded` is proved by induction on `n`,
using the pointwise bound hypothesis at each step:

* **Base case (`n = 0`)**: the trace is the singleton
  `[base.interp ctx]`, bounded by `bound.interp (cons 0 ctx)`
  by hypothesis.  `Nat.bounded_beta_exists` produces witnesses
  `(a, b)` whose Szudzik pair lies within the search range.
  The search predicate evaluates to `1` at this pair (only
  one consistency check is needed).  β-extraction at position
  `0` yields `base.interp ctx`.  The outer `min` with bound
  is vacuous (since `base.interp ctx ≤ bound.interp ...`).
* **Inductive case (`n = succ n'`)**: by hypothesis the entire
  `(n'+2)`-element trace is bounded by `bound.interp` at each
  step.  Apply `Nat.bounded_beta_exists` with `M = max-of-
  trace` (at most `bound.interp (cons n ctx)` after taking the
  max over `j ≤ n` via the bound term's behavior — concretely,
  the search range is sized for `M = bound.interp (cons n
  ctx)`, so as long as the bound is monotone-enough or the
  search range is enlarged via composition with `bsum` of
  bound over the prefix, witnesses exist).  The search finds
  a witness; β-extraction at position `n` yields the final
  trace value; the outer `min` is vacuous.

Sub-lemma factoring is encouraged: a `boundedRec_witness_exists`
helper packaging the search-range sufficiency, a
`boundedRec_search_finds_value` helper packaging the
search-extraction round-trip, and the main inductive theorem
combining them.

The unconditional weak form (`interp_boundedRec_le_bound`)
serves as a fallback for clients who cannot supply a bound-
adequacy proof.

Rationale: this is the classical bounded-primitive-recursion
correctness argument; formalization is direct once the CRT
bound is pinned down.

### D7. Showcase applications as validation

After `natRec` lands, the mini-phase adds derived:

* `ERMor1.natAdd : ERMor1 2` — `natAdd = natRec (proj 1) (succ
  (proj prev))` (addition as iterated succ).
* `ERMor1.natMul : ERMor1 2` — via `natRec` with step adding
  the multiplicand.  Coincides with the existing `bsum`-based
  definition (sanity-check: both produce the same
  interpretation).
* `ERMor1.factorial : ERMor1 1` — `factorial = natRec (succ
  zero) (mul (succ (proj counter)) (proj prev))`.
* `#guard` assertions: `natAdd ![2, 3] = 5`, `natMul ![4, 5] =
  20`, `factorial ![5] = 120`.

Rationale: these validate the combinator end-to-end on
concrete inputs.  Factorial in particular is a standard
primitive-recursion test.  The `bsum` comparison for `natMul`
ensures the derived combinator agrees with the existing
toolchain.

## Module layout

```text
GebLean/
├── Utilities/
│   ├── SzudzikSeq.lean        (existing)
│   │     `Nat.seqPack`, `Nat.seqAt`, `Nat.treeFoldOnCode`,
│   │     `Nat.foldBTLOnCode` (Task 13 Part 1, DONE).
│   ├── ERArith.lean           (renamed from ERTreeArith.lean,
│   │                           extended)
│   │     natPair, natUnpair, natSqrt (moved content),
│   │     div, mod (new),
│   │     beta (new),
│   │     boundedSearch (new),
│   │     natRec (new),
│   │     natAdd, natMul, factorial (showcase, new).
│   │     All with @[simp] correctness theorems.
│   └── ERTreeArith.lean       (recreated with new content)
│         foldBTLOnCode (Task 13 Part 2, built on natRec),
│         btlEncode/btlDecode (Task 14 supporting primitives).
├── LawvereER.lean             (existing, unchanged)
├── LawvereERQuot.lean         (existing, unchanged)
├── LawvereERArith.lean        (existing, unchanged)
├── LawvereERBool.lean         (existing, unchanged)
├── LawvereERPrimrec.lean      (existing, unchanged)
├── LawvereERBound.lean        (existing, unchanged)
├── LawvereERTetration.lean    (existing, unchanged)
├── LawvereNatBT.lean          (existing, unchanged)
├── LawvereNatBTQuot.lean      (existing, unchanged)
├── LawvereNatBTInterp.lean    (existing, unchanged)
├── LawvereNatBT0.lean         (existing, unchanged)
└── LawvereNatBTBackTrans.lean (to be created as part of
                                Task 14; uses ERArith and
                                ERTreeArith outputs).
```

`GebLean.lean` imports the renamed and new modules in
alphabetical position.

## Detailed content sketches

### `Utilities/ERArith.lean` additions

```lean
-- ... (existing natPair/natUnpair/natSqrt, moved) ...

/-- ER-derived integer division `a / b`.  Defined via
bounded search: count `k < a` with `(k+1) * b ≤ a`. -/
def ERMor1.div : ERMor1 2 := ...

@[simp] theorem ERMor1.interp_div (a b : ℕ) :
    (ERMor1.div).interp ![a, b] = a / b := ...

/-- ER-derived modulo `a % b = a - (a / b) * b`. -/
def ERMor1.mod : ERMor1 2 := ...

@[simp] theorem ERMor1.interp_mod (a b : ℕ) :
    (ERMor1.mod).interp ![a, b] = a % b := ...

/-- Gödel's β-function: `β(a, b, i) = a mod (1 + (i+1)*b)`.
Direct arithmetic; no iteration. -/
def ERMor1.beta : ERMor1 3 := ...

@[simp] theorem ERMor1.interp_beta (a b i : ℕ) :
    (ERMor1.beta).interp ![a, b, i] =
      a % (1 + (i + 1) * b) := ...

/-- CRT existence lemma: for every finite ℕ-sequence, Gödel
β-parameters exist.  Proved at the Lean level (no ER
computation; meta-level appeal used by `natRec` correctness). -/
theorem Nat.beta_exists {N : ℕ} (s : Fin N → ℕ) :
    ∃ a b : ℕ, ∀ i : Fin N,
      a % (1 + (i.val + 1) * b) = s i := ...

/-- Bounded search combinator: returns the least `j ≤
bound.interp ctx` with `pred`-at-that-`j` equaling 1, or
`bound.interp ctx + 1` if no witness exists. -/
def ERMor1.boundedSearch {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1)) :
    ERMor1 k := ...

theorem ERMor1.interp_boundedSearch ... := ...

/-- Derived primitive-recursion combinator.  `step`'s first
two slots receive the counter and the previous result. -/
def ERMor1.natRec {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2)) :
    ERMor1 (k + 1) := ...

@[simp] theorem ERMor1.interp_natRec {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (n : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.natRec base step).interp (Fin.cons n ctx) =
      Nat.rec (base.interp ctx)
        (fun j prev =>
          step.interp (Fin.cons j (Fin.cons prev ctx)))
        n := ...

-- Showcase
def ERMor1.natAdd : ERMor1 2 := ...
@[simp] theorem ERMor1.interp_natAdd (x y : ℕ) :
    (ERMor1.natAdd).interp ![x, y] = x + y := ...

def ERMor1.natMul : ERMor1 2 := ...
@[simp] theorem ERMor1.interp_natMul (x y : ℕ) :
    (ERMor1.natMul).interp ![x, y] = x * y := ...

def ERMor1.factorial : ERMor1 1 := ...
@[simp] theorem ERMor1.interp_factorial (n : ℕ) :
    (ERMor1.factorial).interp ![n] = Nat.factorial n := ...
```

### `Utilities/ERTreeArith.lean` (recreated)

```lean
import GebLean.Utilities.ERArith
import GebLean.Utilities.SzudzikSeq
import GebLean.LawvereNatBT

namespace GebLean

/-- ER-derived `BTL`-fold on a Gödel code.  Uses `natRec`
over the code-value countdown, with parity-based case
analysis at each step. -/
def ERMor1.foldBTLOnCode {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2)) :
    ERMor1 (k + 1) := ...

@[simp] theorem ERMor1.interp_foldBTLOnCode {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode).interp ctx =
      Nat.foldBTLOnCode
        (fun lbl =>
          baseLeaf.interp (Fin.cons lbl (Fin.tail ctx)))
        (fun a b => stepNode.interp
          (Fin.cons a (Fin.cons b (Fin.tail ctx))))
        (ctx 0) := ...

-- BTL encoding primitives, ER-side.
def ERMor1.btlEncodeLeaf : ERMor1 1 := ...
def ERMor1.btlEncodeNode : ERMor1 2 := ...

@[simp] theorem ERMor1.interp_btlEncodeLeaf (lbl : ℕ) :
    (ERMor1.btlEncodeLeaf).interp ![lbl] =
      BTL.encode (BTL.leaf lbl) := ...

@[simp] theorem ERMor1.interp_btlEncodeNode (l r : ℕ) :
    (ERMor1.btlEncodeNode).interp ![l, r] =
      BTL.encode (BTL.node (BTL.decode l) (BTL.decode r)) := ...

end GebLean
```

## Build stages

### Task 12a: Rename and extend (tiny)

* `git mv GebLean/Utilities/ERTreeArith.lean
   GebLean/Utilities/ERArith.lean`
* Update `GebLean.lean` import.
* Update namespace references if any differ.
* Build + test.
* Commit: "Rename ERTreeArith.lean to ERArith.lean".

### Task 12b: div and mod

Add to `ERArith.lean`.  ~1 session.  Build + test + commit.

### Task 12c: beta and Nat.beta_exists

Add to `ERArith.lean`.  Investigate mathlib coverage first;
prove `Nat.beta_exists` if not present.  ~1-2 sessions.

### Task 12d: boundedSearch

Add to `ERArith.lean`.  ~1 session.

### Task 12e: natRec

Add to `ERArith.lean`.  Definition plus correctness theorem.
~2 sessions.

### Task 12f: Showcase (natAdd, natMul, factorial)

Add to `ERArith.lean`.  `#guard`-validated.  ~0.5 session.

### Task 13: foldBTLOnCode (completes original Task 13)

Create new `ERTreeArith.lean` with BTL-specific content.  Add
`foldBTLOnCode` via `natRec` plus parity-case splits.  Add
`btlEncodeLeaf`, `btlEncodeNode` supporting primitives.
~1 session.

### Task 14 onward

Unchanged from original Stage β plan.  `NatBTMor1.toER`
uses `foldBTLOnCode` and the btl encoding primitives; the rest
of Stage β (Tasks 15-20) follows as originally specified.

## Testing plan

Each sub-task (12b through 13) contributes:

* `#guard` or `example` on a small concrete input, verifying
  the `@[simp]` correctness theorem reduces as expected.
* Integration test: sub-task 12f adds `#guard` on `natAdd`,
  `natMul`, `factorial`.

Post-13 integration: `#guard` on `foldBTLOnCode` evaluated on
a small tree via `BTL.encode`.

Post-14 integration (Task 14 onward): `#guard` showing
`(encodeBT (decodeBT k)).toER.interp ![k] = k`, validating the
back-translation round-trip.

## Completion criteria

The mini-phase completes when:

1. `Utilities/ERArith.lean` contains all 7 listed primitives
   (existing 3 + 4 new arithmetic + `natRec` + 3 showcase) with
   `@[simp]`-marked correctness theorems.
2. `Utilities/ERTreeArith.lean` exists with `foldBTLOnCode` and
   supporting BTL-encoding primitives, each with `@[simp]`
   correctness.
3. Every new definition builds cleanly: zero warnings, zero
   `sorry`, zero `admit`.
4. `Nat.beta_exists` is provable as a Lean theorem (either via
   mathlib reuse or new proof).
5. Showcase `#guard` assertions (`natAdd`, `natMul`,
   `factorial`) pass.
6. `foldBTLOnCode` reduces correctly on small BTL codes under
   `@[simp]`.
7. `ERMor1` inductive is definitionally unchanged (Wikipedia-
   literal 7 generators).

## Risk flags

### `Nat.beta_exists` bound size

The classical CRT bound on `a` is
`a ≤ (max(s, N) + 1)!^(N+1)` or similar factorial-exponential.
That is elementary but produces a large `bsum` range in
`natRec`'s body.  Compile-time cost for `#guard` tests on
non-trivial inputs may be significant.  Mitigation:

* Verify at each sub-task that `#guard` assertions complete
  within the existing lake-test timeout budget.
* If timeouts appear, either narrow the showcase tests to
  smaller inputs or add a `set_option maxHeartbeats` locally.
* For the correctness theorem (`interp_natRec`) we do not
  execute the search, so proof-checking cost is independent of
  bound size.

### Proof complexity of `interp_natRec`

The correctness theorem requires induction on the counter,
invoking `Nat.beta_exists` at each step and chaining the
β-extraction with `Nat.rec` unfolding.  Budget 2 sessions.  If
the proof proves longer than expected, consider factoring out
a helper lemma `natRec_step` proving the one-step inductive
relation before attacking the full theorem.

### Mathlib β-coverage investigation

Before writing the CRT proof, check mathlib for pre-existing
machinery.  Relevant candidates:

* `Mathlib.Computability.Primrec` — has `Nat.Primrec.prec`
  which gives primitive recursion as a Prop-level judgment.
  May have β-existence internally.
* `Mathlib.Data.Nat.ModEq` — CRT via
  `Nat.ModEq.chineseRemainder`.
* `Mathlib.Data.Nat.Pairing` — Szudzik pairing (already used
  for `natPair`).

If mathlib provides β-existence directly, Task 12c drops to
~0.5 session (wrap and cite).

### Rename churn

The `git mv ERTreeArith.lean → ERArith.lean` changes the
already-landed Task 12 (commit `29553fd0`) file name.
Downstream references in `.session/` trackers and already-
committed doc files need updating.  Mitigation: update in a
dedicated Task 12a commit, keeping all renames and downstream
reference updates together.

## Open questions

All design questions have been resolved via brainstorming
(`docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`
and this document).  Implementation is ready to proceed.

## Literature references

* Kleene, S. C. *Introduction to Metamathematics.* 1952.
  Classic reference for Gödel β-function and bounded-search
  primitive-recursion.
* Gödel, K. "Über formal unentscheidbare Sätze der Principia
  Mathematica und verwandter Systeme I." 1931.  Original
  β-function construction.
* Rogers, H. *Theory of Recursive Functions and Effective
  Computability.* 1967.  Standard reference for the
  CRT-based primitive-recursion formalization.
* Wikipedia, "Elementary recursive function":
  <https://en.wikipedia.org/wiki/Elementary_recursive_function>
