# LawvereER Phase 1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`* [ ]`) syntax.

**Goal:** Create `GebLean/LawvereER.lean` with an inductive
term type `ERMor1 n` transcribing the Wikipedia basis of
elementary recursive functions, its standard interpretation
into `(Fin n → ℕ) → ℕ`, a tuple wrapper `ERMorN n m`, and
identity/composition on tuples.

**Architecture:** Seven generators as constructors of a single
`ℕ`-indexed inductive type (`zero`, `succ`, `proj`, `sub`,
`comp`, `bsum`, `bprod`), with arities baked into the type
index so each constructor has its Wikipedia-specified arity.
Interpretation is a structural recursion into
`(Fin n → ℕ) → ℕ`; `bsum`/`bprod` use the bound-variable-at-
index-0 convention (the first argument of the outer term is
the bound, and on each iteration the first argument of the
inner term is replaced by the loop index via
`Fin.cons i (Fin.tail ctx)`).

**Tech Stack:** Lean 4, mathlib's `Mathlib.Data.Fin.Basic`
(for `Fin.cons`/`Fin.tail`), `Nat.rec`-based iteration
helpers (avoiding `Finset.range` for rfl-friendliness).

## Design references

* `docs/lawvere-elementary-recursive.md` — Phase 0 design
  decisions.
* `.session/workstreams/lawvere-elementary-recursive.md` —
  workstream tracker.
* `GebLean/LawvereBT.lean`, `GebLean/LawvereBTInterp.lean` —
  pattern this plan parallels.

## Coding discipline reminders

* `autoImplicit = false`, `relaxedAutoImplicit = false`: bind
  every type variable explicitly.
* No `sorry`, no `admit`, no warnings; use `_` to see goal
  types when stuck.
* No classical logic, no `noncomputable`, no `axiom`.
* Line length ≤ 80.
* After every step, run `lake build` and `lake test`; fix
  warnings/errors before proceeding.
* Never use `lake clean`.
* One definition at a time; commit each task separately.

## File structure

The plan creates two files and modifies two indices.

**Create `GebLean/LawvereER.lean`.**  Inductive term type,
interpretation, computation lemmas, `ERMorN` tuple type,
identity, composition.

**Modify `GebLean.lean`.**  Add `import GebLean.LawvereER`
alphabetically.

**Create `GebLeanTests/LawvereER.lean`.**  `#guard` tests for
each constructor's interpretation and for tuple composition.

**Modify `GebLeanTests.lean`.**  Add
`import GebLeanTests.LawvereER`.

---

## Task 1: Skeleton file with the inductive `ERMor1` type

**Files:**

* Create: `GebLean/LawvereER.lean`
* Modify: `GebLean.lean`

* [ ] **Step 1: Create `GebLean/LawvereER.lean` with header,
  imports, namespace, and the inductive type.**

```lean
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
```

* [ ] **Step 2: Add the new import to `GebLean.lean`
  alphabetically.**

Insert `import GebLean.LawvereER` between
`GebLean.LawvereBTQuot` and `GebLean.LayeredEquivalence`.

* [ ] **Step 3: Run `lake build` and `lake test` and verify
  zero errors, zero warnings.**

```bash
lake build
lake test
```

Expected: both complete with no errors or warnings.

* [ ] **Step 4: Commit.**

```bash
git add GebLean/LawvereER.lean GebLean.lean
git commit -m "$(cat <<'EOF'
Add LawvereER skeleton with inductive ER term type

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Add `natBSum` and `natBProd` iteration helpers

**Files:**

* Modify: `GebLean/LawvereER.lean`

* [ ] **Step 1: Add the helpers after the inductive type
  definition, still inside `namespace GebLean`.**

```lean
/-- Bounded summation helper: iterates `f` from
`0` to `bound - 1` and sums the results. -/
def natBSum (bound : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 0 (fun i acc => acc + f i) bound

/-- Bounded product helper: iterates `f` from `0`
to `bound - 1` and multiplies the results, with
an empty product of `1`. -/
def natBProd (bound : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 1 (fun i acc => acc * f i) bound
```

* [ ] **Step 2: Run `lake build` and `lake test` and verify
  zero errors, zero warnings.**

* [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereER.lean
git commit -m "$(cat <<'EOF'
Add natBSum and natBProd helpers in LawvereER

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Define `ERMor1.interp`

**Files:**

* Modify: `GebLean/LawvereER.lean`

* [ ] **Step 1: Add the interpretation function after the
  helpers.**

```lean
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
```

* [ ] **Step 2: Run `lake build`.**

**Expected:** clean build.

**If the equation compiler rejects the `comp` case** (error
along the lines of "failed to prove termination" or
"cannot generate recursor"), try these fallbacks in order:

1. Add a `termination_by` clause — Lean may need the hint
   that the first `ERMor1 n` argument is the termination
   argument.
2. Replace the `match` with an explicit call to
   `ERMor1.rec`, handling the `comp` case with the
   generated dependent motive.
3. If still stuck, invoke the `lean4:lean4` skill with a
   summary of the error and ask for help with the
   structural-recursion issue through
   `g : Fin k → ERMor1 n`.

* [ ] **Step 3: Run `lake test` and verify zero errors,
  zero warnings.**

* [ ] **Step 4: Commit.**

```bash
git add GebLean/LawvereER.lean
git commit -m "$(cat <<'EOF'
Define ERMor1.interp with the bound-variable-at-0 convention

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Add rfl-level computation lemmas

These lemmas become the abstraction barrier for all
downstream phases: no code outside this file should unfold
`ERMor1.interp` directly; everything uses these named
lemmas.

**Files:**

* Modify: `GebLean/LawvereER.lean`

* [ ] **Step 1: Add the seven unfolding lemmas after the
  `interp` definition.**

```lean
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
```

* [ ] **Step 2: Run `lake build` and `lake test` and verify
  zero errors, zero warnings.**

* [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereER.lean
git commit -m "$(cat <<'EOF'
Add rfl-level computation lemmas for ERMor1.interp

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Define `ERMorN` tuple type and its interpretation

**Files:**

* Modify: `GebLean/LawvereER.lean`

* [ ] **Step 1: Add the tuple type and its interpretation.**

```lean
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
```

* [ ] **Step 2: Run `lake build` and `lake test` and verify
  zero errors, zero warnings.**

* [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereER.lean
git commit -m "$(cat <<'EOF'
Add ERMorN tuple type and its pointwise interpretation

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Define `ERMorN.id` and `ERMorN.comp`

**Files:**

* Modify: `GebLean/LawvereER.lean`

* [ ] **Step 1: Add the identity and composition
  operations.**

```lean
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
```

* [ ] **Step 2: Add the interpretation-compatibility
  lemmas.**

```lean
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
```

* [ ] **Step 3: Run `lake build` and `lake test` and verify
  zero errors, zero warnings.**

If `interp_id` fails as `rfl` (because `ctx : Fin n → ℕ` is
a function, not a tuple that `rfl` can inspect), replace the
proof with `funext i; rfl`.  Similarly for `interp_comp`.

* [ ] **Step 4: Commit.**

```bash
git add GebLean/LawvereER.lean
git commit -m "$(cat <<'EOF'
Add ERMorN.id and ERMorN.comp with interp lemmas

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Test file with `#guard` tests for generators

**Files:**

* Create: `GebLeanTests/LawvereER.lean`
* Modify: `GebLeanTests.lean`

* [ ] **Step 1: Create the test file.**

```lean
import GebLean.LawvereER

/-!
# Tests for LawvereER

`#guard` sanity tests covering the interpretation
of each generator and of `ERMorN` tuple
composition.
-/

open GebLean

-- The empty context for `ERMor1 0` terms.
private def ctx0 : Fin 0 → ℕ := Fin.elim0

-- A convenient unary context `(x)`.
private def ctx1 (x : ℕ) : Fin 1 → ℕ :=
  fun _ => x

-- A convenient binary context `(x, y)`.
private def ctx2 (x y : ℕ) : Fin 2 → ℕ :=
  ![x, y]

-- zero at the empty context.
#guard ERMor1.zero.interp ctx0 == 0

-- succ of 5.
#guard ERMor1.succ.interp (ctx1 5) == 6

-- proj 0 out of (7, 3).
#guard (ERMor1.proj (0 : Fin 2)).interp
  (ctx2 7 3) == 7

-- proj 1 out of (7, 3).
#guard (ERMor1.proj (1 : Fin 2)).interp
  (ctx2 7 3) == 3

-- sub at (7, 3) is 4.
#guard ERMor1.sub.interp (ctx2 7 3) == 4

-- sub is cut-off: sub at (3, 7) is 0.
#guard ERMor1.sub.interp (ctx2 3 7) == 0

-- bsum of `proj 1` at `(x, y)` is `x * y`.
-- At `(3, 4)` it sums `4` three times: 12.
#guard (ERMor1.bsum
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 3 4) == 12

-- bprod of `proj 1` at `(x, y)` is `y ^ x`.
-- At `(3, 2)` it multiplies `2` three times: 8.
#guard (ERMor1.bprod
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 3 2) == 8

-- Empty bprod returns 1 (bound = 0).
#guard (ERMor1.bprod
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 0 5) == 1

-- Empty bsum returns 0.
#guard (ERMor1.bsum
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 0 5) == 0
```

* [ ] **Step 2: Add the import to `GebLeanTests.lean`.**

Insert `import GebLeanTests.LawvereER` between
`GebLeanTests.LayeredEquivalence` and
`GebLeanTests.TestEqualizerCompletion`.

* [ ] **Step 3: Run `lake build` and `lake test`.**

Expected: zero errors, zero warnings, all `#guard`s pass.

If `![x, y]` vector notation is unavailable, replace with
an explicit function
`fun i => if i.val = 0 then x else y`.

* [ ] **Step 4: Commit.**

```bash
git add GebLeanTests/LawvereER.lean GebLeanTests.lean
git commit -m "$(cat <<'EOF'
Add LawvereER sanity tests for each generator

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: `#guard` tests for `ERMorN` composition

**Files:**

* Modify: `GebLeanTests/LawvereER.lean`

* [ ] **Step 1: Add tuple tests at the end of the test
  file.**

```lean
-- An ERMorN 2 1 tuple of one binary term: sub.
private def subTuple : ERMorN 2 1 :=
  fun _ => ERMor1.sub

-- An ERMorN 2 2 tuple swapping two inputs.
private def swapTuple : ERMorN 2 2 :=
  fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj (1 : Fin 2)
    | ⟨1, _⟩ => ERMor1.proj (0 : Fin 2)

-- subTuple at (7, 3) computes sub once.
#guard (subTuple.interp (ctx2 7 3)) 0 == 4

-- swapTuple at (7, 3) swaps to (3, 7).
#guard (swapTuple.interp (ctx2 7 3)) 0 == 3
#guard (swapTuple.interp (ctx2 7 3)) 1 == 7

-- Composition of ERMorN.id with subTuple is
-- subTuple (verified pointwise on one context).
#guard
  (((ERMorN.id 2).comp subTuple).interp
    (ctx2 7 3)) 0 == 4

-- Composition of swap followed by sub computes
-- (3, 7) → 3 - 7 = 0 (cut-off).
#guard
  ((swapTuple.comp subTuple).interp
    (ctx2 7 3)) 0 == 0
```

* [ ] **Step 2: Run `lake build` and `lake test`.**

Expected: zero errors, zero warnings, all `#guard`s pass.

* [ ] **Step 3: Commit.**

```bash
git add GebLeanTests/LawvereER.lean
git commit -m "$(cat <<'EOF'
Add LawvereER tests for ERMorN identity and composition

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: Final verification and bookkeeping

* [ ] **Step 1: Run the full build and test suite.**

```bash
lake build
lake test
```

Expected: zero errors, zero warnings.

* [ ] **Step 2: Run markdownlint on the changed markdown
  files.**

```bash
markdownlint-cli2 \
  docs/superpowers/plans/2026-04-11-lawvere-er-phase-1.md \
  .session/workstreams/lawvere-elementary-recursive.md \
  docs/lawvere-elementary-recursive.md
```

Expected: zero errors.  Fix any issues inline.

* [ ] **Step 3: Update the workstream tracker to mark Phase
  1 complete and list the new file.**

In `.session/workstreams/lawvere-elementary-recursive.md`,
change the Phase 1 task checkbox from `[ ]` to `[x]` and
note the created files under the Status section.

* [ ] **Step 4: Mark TaskCreate task #102 (ER Phase 1) as
  completed via `TaskUpdate`.**

* [ ] **Step 5: Commit bookkeeping changes.**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "$(cat <<'EOF'
Mark ER Phase 1 complete in the workstream tracker

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Deliverables at end of Phase 1

* `GebLean/LawvereER.lean` containing:
  * `ERMor1 : ℕ → Type` with seven constructors.
  * `natBSum`, `natBProd` iteration helpers.
  * `ERMor1.interp` and seven `@[simp]` unfolding lemmas.
  * `ERMorN n m := Fin m → ERMor1 n` with `ERMorN.interp`.
  * `ERMorN.id`, `ERMorN.comp`, and their two `@[simp]`
    interpretation lemmas.
* `GebLeanTests/LawvereER.lean` containing `#guard` tests for
  every generator and for tuple composition.
* `GebLean.lean` and `GebLeanTests.lean` updated with the
  new imports.
* TaskCreate task #102 marked completed.
* `.session/workstreams/lawvere-elementary-recursive.md`
  Phase 1 checkbox marked.

## Phase 2 dependencies

Phase 2 (extensional-equality setoid quotient) will build on
Phase 1 by:

* Defining `erMorNSetoid (n m : ℕ) : Setoid (ERMorN n m)`
  using the predicate
  `r f g := ∀ ctx, f.interp ctx = g.interp ctx`.
* Quotienting `ERMorN n m` by this setoid.
* Lifting `ERMorN.id` and `ERMorN.comp` through
  `Quotient.lift₂`, with congruence proofs discharged via
  `ERMorN.interp_comp` and `ERMorN.interp_id`.
* Establishing the category laws (`id_comp`, `comp_id`,
  `assoc`) on the quotient, each provable by `funext` and
  the interpretation lemmas.

No Phase 2 work is in scope for this plan.
