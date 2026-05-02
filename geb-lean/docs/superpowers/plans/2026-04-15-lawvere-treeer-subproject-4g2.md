# Lawvere Tree-ER Sub-project 4g.2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish the bidirectional categorical isomorphism
`LawvereERCat ≅ LawvereTreeERCat` via Gödel arithmetic on trees,
structured as a three-layer spec/implementation/agreement pattern.

**Architecture:** Layer 1 is generic Lean-native arithmetic
(Szudzik sequence encoding, tree-fold simulator, mutumorphism).
Layer 2 is tree-ER syntactic arithmetic with agreement theorems
linking it to Layer 1.  Layer 3 is the translation functors `J`,
`K` and mutual-inverse proofs.  Each layer has its own tests.

**Tech Stack:** Lean 4 + Mathlib (`Mathlib.Data.Nat.Pairing` for
Szudzik pair/unpair, `BT.fold` from `LawvereBT.lean` for native
tree fold, `Mathlib.CategoryTheory.Functor.Basic` for functor
machinery).

**Design spec:**
`docs/superpowers/specs/2026-04-15-lawvere-treeer-subproject-4g2-design.md`.

**Workstream tracker entry:**
`.session/workstreams/lawvere-elementary-recursive.md` —
"Phase 4g.2" bullet.

---

## File structure

Files to create:

* `GebLean/Utilities/SzudzikSeq.lean` — Layer 1.
* `GebLean/LawvereTreeERArith.lean` — Layer 2.
* `GebLean/LawvereTreeERLawvereEquiv.lean` — Layer 3.
* `GebLeanTests/Utilities/SzudzikSeq.lean`.
* `GebLeanTests/LawvereTreeERArith.lean`.
* `GebLeanTests/LawvereTreeERLawvereEquiv.lean`.

Files to modify:

* `GebLean/Utilities.lean` — add `SzudzikSeq` import.
* `GebLean.lean` — add two new library-module imports (Layer 2
  + Layer 3).
* `GebLeanTests.lean` — add three test-module imports.
* `.session/workstreams/lawvere-elementary-recursive.md` — mark
  4g.2 complete.

---

## Key Mathlib and project APIs

* `Nat.pair (a b : ℕ) : ℕ` — Szudzik pair (in
  `Mathlib.Data.Nat.Pairing`).
* `Nat.unpair (n : ℕ) : ℕ × ℕ` — Szudzik unpair.
* `Nat.pair_unpair : pair (unpair n).1 (unpair n).2 = n`.
* `Nat.unpair_pair : unpair (pair a b) = (a, b)`.
* `Nat.unpair_left_le : (unpair n).1 ≤ n`.
* `Nat.unpair_right_le : (unpair n).2 ≤ n`.
* `Nat.pair_lt_max_add_one_sq : pair m n < (max m n + 1) ^ 2`.
* `BT.leaf`, `BT.node` — constructors (`LawvereBT.lean:187,196`).
* `BT.fold (b : α) (s : α → α → α) (t : BT) : α` —
  `LawvereBT.lean:239`.
* `encodeBT : BT → ℕ` — `LawvereBTPrimrec.lean:21`.
* `decodeBT : ℕ → BT` — `LawvereBTPrimrec.lean:27`.
* `decodeBT_encodeBT`, `encodeBT_decodeBT` — round-trip lemmas.
* `TreeERMor1`, `TreeERMor1_0`, `TreeERMor1_1` and their smart
  constructors — `LawvereTreeER.lean`.
* `LawvereTreeERCat`, `TreeERMorNQuo` —
  `LawvereTreeERQuot.lean`.
* `LawvereERCat`, `ERMorNQuo`, `ERMor1` generators —
  `LawvereER.lean`, `LawvereERQuot.lean`.

---

## Stage α: Layer 1 — generic Lean arithmetic

### Task 1: Create `SzudzikSeq.lean` with `seqPack`

**Files:**

* Create: `GebLean/Utilities/SzudzikSeq.lean`

- [ ] **Step 1: Create file with header and imports**

```lean
import Mathlib.Data.Nat.Pairing
import GebLean.LawvereBT
import GebLean.LawvereBTPrimrec

/-!
# Szudzik Sequence Encoding and Tree-Fold Simulation

Generic Lean-native arithmetic building blocks for the
`LawvereTreeERCat ≅ LawvereERCat` isomorphism:

* `Nat.seqPack` / `Nat.seqAt` — encode a list of naturals as
  one natural via iterated right-associated Szudzik pairing.
* `Nat.treeFoldOnCode` — simulate `BT.fold` via
  course-of-values recursion on a Gödel-encoded tree.
* `Nat.tupleRecN` — finite-arity mutumorphism via iterated
  pair.

All functions are elementary recursive (E₃).  Reduction rules
are proved with `@[simp]` and are suitable for use in
downstream `TreeERMor1`-level agreement theorems.
-/

namespace Nat

end Nat
```

- [ ] **Step 2: Add `seqPack`**

Inside `namespace Nat`:

```lean
/-- Encode a list of naturals as a single natural via
iterated right-associated Szudzik pairing.  Empty list is 0;
`x :: xs` packs as `pair x (seqPack xs) + 1`. -/
def seqPack : List ℕ → ℕ
  | []      => 0
  | x :: xs => pair x (seqPack xs) + 1

@[simp] theorem seqPack_nil : seqPack [] = 0 := rfl
@[simp] theorem seqPack_cons (x : ℕ) (xs : List ℕ) :
    seqPack (x :: xs) = pair x (seqPack xs) + 1 := rfl
```

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.Utilities.SzudzikSeq
```

Expected: PASS.

```bash
git add GebLean/Utilities/SzudzikSeq.lean
git commit -m "Add Nat.seqPack with Szudzik-based list encoding"
```

---

### Task 2: `Nat.seqAt` and round-trip theorem

**Files:**

* Modify: `GebLean/Utilities/SzudzikSeq.lean`

- [ ] **Step 1: Add `seqAt`**

```lean
/-- Extract the `i`-th element from a packed sequence.
Returns 0 if out of range.  On in-range indices, satisfies
`seqAt (seqPack xs) i = xs.get? i |>.getD 0`. -/
def seqAt : ℕ → ℕ → ℕ
  | 0,     _     => 0
  | _+1,   0     => (unpair ·).1  -- placeholder; fix in step 2
  | n+1,   i+1   => seqAt (unpair n).2 i

-- Fix: properly match on `n+1` first to access its predecessor.
```

Exact form needs refinement: after unpair on `n`, the first
component is the head and the second is the rest's pack.
Concretely:

```lean
def seqAt : ℕ → ℕ → ℕ
  | 0,     _     => 0
  | n + 1, 0     => (unpair n).1
  | n + 1, i + 1 => seqAt (unpair n).2 i
```

- [ ] **Step 2: Prove round-trip**

```lean
theorem seqAt_seqPack : ∀ (xs : List ℕ) (i : ℕ),
    i < xs.length → seqAt (seqPack xs) i = xs.get ⟨i, by omega⟩
  | [],      i,     h => absurd h (by omega)
  | x :: xs, 0,     _ => by
      simp [seqAt, seqPack, unpair_pair]
  | x :: xs, i + 1, h => by
      simp [seqAt, seqPack, unpair_pair]
      exact seqAt_seqPack xs i (by omega)
```

Note: exact incantation may need adjustment — `List.get ⟨i,
h⟩` may have become `List.get xs ⟨i, h⟩` in current mathlib.
Adapt to the current API.

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.Utilities.SzudzikSeq
git add GebLean/Utilities/SzudzikSeq.lean
git commit -m "Add Nat.seqAt with round-trip theorem"
```

---

### Task 3: `Nat.treeFoldOnCode` and correctness

**Files:**

* Modify: `GebLean/Utilities/SzudzikSeq.lean`

- [ ] **Step 1: Define `treeFoldOnCode`**

```lean
/-- Simulate `BT.fold` via course-of-values recursion on a
Gödel code.  The encoding is `code(leaf) = 0`,
`code(branch l r) = 1 + pair (code l) (code r)`, matching
`encodeBT` from `LawvereBTPrimrec.lean`. -/
def treeFoldOnCode {α : Type*}
    (h₀ : α) (h₁ : α → α → α) : ℕ → α
  | 0     => h₀
  | n + 1 =>
      h₁ (treeFoldOnCode h₀ h₁ (unpair n).1)
         (treeFoldOnCode h₀ h₁ (unpair n).2)
  termination_by n => n
  decreasing_by
    · exact Nat.lt_succ_of_le (unpair_left_le n)
    · exact Nat.lt_succ_of_le (unpair_right_le n)
```

- [ ] **Step 2: Prove correctness vs `BT.fold`**

```lean
theorem treeFoldOnCode_encodeBT {α : Type*}
    (t : BT.{0}) (h₀ : α) (h₁ : α → α → α) :
    treeFoldOnCode h₀ h₁ (encodeBT t) = BT.fold h₀ h₁ t := by
  induction t with
  | leaf =>
      simp [treeFoldOnCode, encodeBT, BT.fold]
  | node l r ih_l ih_r =>
      simp [treeFoldOnCode, encodeBT, BT.fold,
            unpair_pair, ih_l, ih_r]
```

Note: the exact `simp` targets depend on how `encodeBT` on
`BT.leaf` reduces (should be `= 0` by definition) and on
`BT.fold`'s definitional behavior (should unfold to `h₀` on
`leaf` and `h₁ (fold ... l) (fold ... r)` on `node l r`).  If
these simp lemmas aren't available out of the box, use
`unfold encodeBT BT.fold treeFoldOnCode` + explicit rewrites.

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.Utilities.SzudzikSeq
git add GebLean/Utilities/SzudzikSeq.lean
git commit -m "Add Nat.treeFoldOnCode with correctness vs BT.fold"
```

---

### Task 4: `Nat.tupleRecN` — finite mutumorphism via pair

**Files:**

* Modify: `GebLean/Utilities/SzudzikSeq.lean`

- [ ] **Step 1: Define `tupleRecN`**

```lean
/-- Finite-arity mutumorphism: given `k` step functions
`fs : Fin k → ℕ → ℕ` over a shared bound, pack their outputs
as a single natural and run one bounded iteration.  The
result at index `i` is `fs i` applied `n` times starting from
`init i`. -/
def tupleRecN (k : ℕ) (init : Fin k → ℕ)
    (step : Fin k → ℕ → ℕ) (n : ℕ) : Fin k → ℕ :=
  fun i => Nat.rec (init i)
    (fun _ acc => step i acc) n
```

Note: this is deliberately simple — k independent
recursions.  Full mutumorphism (where each step sees all k
previous values) is:

```lean
def tupleRecNMutual (k : ℕ) (init : Fin k → ℕ)
    (step : Fin k → (Fin k → ℕ) → ℕ) (n : ℕ) : Fin k → ℕ :=
  Nat.rec init (fun _ prev => fun i => step i prev) n
```

Use whichever matches the downstream need.  The `Mutual`
version is the one tree mutumorphism (Layer 2) will use —
each step function takes all `k` previous slot values.

- [ ] **Step 2: Prove basic reduction rules**

```lean
@[simp] theorem tupleRecN_zero (k init step) (i : Fin k) :
    tupleRecN k init step 0 i = init i := rfl

@[simp] theorem tupleRecN_succ (k init step n) (i : Fin k) :
    tupleRecN k init step (n + 1) i =
      step i (tupleRecN k init step n i) := rfl
```

Similar for `tupleRecNMutual`.

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.Utilities.SzudzikSeq
git add GebLean/Utilities/SzudzikSeq.lean
git commit -m "Add Nat.tupleRecN for finite-arity mutumorphism"
```

---

### Task 5: Register and test Stage α

**Files:**

* Modify: `GebLean/Utilities.lean`
* Create: `GebLeanTests/Utilities/SzudzikSeq.lean`
* Modify: `GebLeanTests.lean`

- [ ] **Step 1: Register in Utilities.lean**

Add `import GebLean.Utilities.SzudzikSeq` in alphabetical
order (likely near `Slice`/`Sigma`/`SpanFamily`).

- [ ] **Step 2: Write test file**

```lean
import GebLean.Utilities.SzudzikSeq

open Nat

-- seqPack / seqAt round-trip on a small list.
#guard seqAt (seqPack [3, 7, 11]) 0 = 3
#guard seqAt (seqPack [3, 7, 11]) 1 = 7
#guard seqAt (seqPack [3, 7, 11]) 2 = 11

-- treeFoldOnCode correctness on a small tree code.
-- code(leaf) = 0, code(node leaf leaf) = 1 + pair 0 0 = 1.
#guard treeFoldOnCode 0 (fun l r => l + r + 1)
  (encodeBT BT.leaf) = 0
#guard treeFoldOnCode 0 (fun l r => l + r + 1)
  (encodeBT (BT.node BT.leaf BT.leaf)) = 1

-- tupleRecN: 3-ary recursion, each step doubles independently.
#guard tupleRecN 3 (fun _ => 1) (fun _ acc => 2 * acc) 3 0 = 8
```

- [ ] **Step 3: Register test**

Add `import GebLeanTests.Utilities.SzudzikSeq` in alphabetical
order to `GebLeanTests.lean`.

- [ ] **Step 4: Build + test + commit**

```bash
lake build && lake test
git add GebLean/Utilities.lean \
        GebLeanTests/Utilities/SzudzikSeq.lean \
        GebLeanTests.lean
git commit -m "Register and test Stage α of Tree-ER 4g.2"
```

---

## Stage β: Layer 2 — tree-ER syntactic arithmetic

Stage β builds tree-ER syntactic counterparts to the Layer-1
arithmetic.  The task order reflects a prerequisite chain:
`treeFoldOnCode` (Task 6) is the foundational substrate that
packages a single `TreeERMor1.fold` over the input as course-
of-values recursion on its Gödel code.  Tasks 7–11 are then
applications that wire specific step functions into this
substrate, keeping fold-nesting depth within the ≤ 2 budget
via `TreeERMor1.comp` (= max-of-depths).

### Task 6: Create `LawvereTreeERArith.lean` stub + `treeFoldOnCode`

**Files:**

* Create: `GebLean/LawvereTreeERArith.lean`

- [ ] **Step 1: Create file with header**

```lean
import GebLean.LawvereTreeERInterp
import GebLean.Utilities.SzudzikSeq

/-!
# Tree-ER Syntactic Arithmetic

Tree-ER term encodings of the Layer-1 arithmetic from
`GebLean/Utilities/SzudzikSeq.lean`.  Each primitive is a
concrete `TreeERMor1` term; for each, an `@[simp]` agreement
theorem links its interpretation to the Layer-1 function via
`encodeBT` / `decodeBT`.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Add `TreeERMor1.treeFoldOnCode` definition**

This is the tree-ER simulation of course-of-values recursion
on Gödel codes, implementing Layer 1's `Nat.treeFoldOnCode` at
the syntactic level.  It is the foundational substrate for the
rest of Stage β: every subsequent Layer-2 primitive is built
as an application of `treeFoldOnCode` with a specific step
function, keeping depth within the ≤ 2 budget.

Given the user's "Lean first, prove correctness, then write in
ER" guidance, use Layer 1's `Nat.treeFoldOnCode` as the spec
and build the tree-ER term to match its interpretation.

The Layer-1 correctness theorem
`treeFoldOnCode_encodeBT : Nat.treeFoldOnCode h₀ h₁
  (encodeBT t) = BT.fold h₀ h₁ t` shows that course-of-values
recursion on `encodeBT t` equals the catamorphic fold over
`t`.  The natural tree-ER realization is therefore
`TreeERMor1.fold1` over the input tree, with the base and step
wrapped via `decodeBT`/`encodeBT` glue so the user-supplied
`base`/`step` handlers operate on BT values.

The primitive must land at depth ≤ 1 so that subsequent tasks
can use it inside another `TreeERMor1.fold` without exceeding
the depth-2 budget.  This constrains the `base` and `step`
parameters to depth 0 (i.e., the `TreeERMor1_0` tier with no
fold constructors).

```lean
def TreeERMor1.treeFoldOnCode
    (base : TreeERMor1_0 0) (step : TreeERMor1_0 2) :
    TreeERMor1_1 1 := ...
```

- [ ] **Step 3: Agreement theorem**

```lean
@[simp] theorem TreeERMor1.treeFoldOnCode_interp
    (base : TreeERMor1_0 0) (step : TreeERMor1_0 2)
    (ctx : Fin 1 → BT.{0}) :
    (TreeERMor1.treeFoldOnCode base step).interp ctx =
      decodeBT (Nat.treeFoldOnCode
        (encodeBT (base.interp Fin.elim0))
        (fun l r => encodeBT
          (step.interp ![decodeBT l, decodeBT r]))
        (encodeBT (ctx 0))) := ...
```

Correctness reduces to `treeFoldOnCode_encodeBT` from Task 3
plus tree-ER interp simp rules.

- [ ] **Step 4: Build and commit**

```bash
lake build GebLean.LawvereTreeERArith
git add GebLean/LawvereTreeERArith.lean
git commit -m "Create LawvereTreeERArith with TreeERMor1.treeFoldOnCode"
```

This task is the hardest individual Layer-2 task and may
require significant iteration.  If blocked, report
NEEDS_CONTEXT with the specific proof state or BLOCKED with
the specific obstacle; we will adjust the approach (e.g.,
weaken the signature, split into further sub-primitives, or
revisit the base/step interface).

---

### Task 7: `mutuFoldOnCode` — multi-slot mutual recursion substrate

**Files:**

* Modify: `GebLean/Utilities/SzudzikSeq.lean` (Layer-1
  primitive + correctness).
* Modify: `GebLean/LawvereTreeERArith.lean` (Layer-2 substrate
  + agreement theorem).

**Rationale:** Task 6's `treeFoldOnCode` is single-slot
(`m = 1`).  Per Leivant 1999 Section 2.6, simultaneous (mutual)
recurrence is a distinct schema that generalizes single-slot
recurrence to an `m`-tuple of functions defined together.  Lemma
2 reduces mutual to non-mutual recurrence in *higher types*
(via a `choose` function + type rewriting), but the reduction
does not preserve first-order depth, and below the relevant
hierarchy levels mutual recurrence is strictly stronger than
non-mutual.  Independently, the Szudzik encoding's quadratic
structure means even simple arithmetic primitives like
`succOnCode` need enough state during the fold to carry outer-
context values alongside the main computation — multi-slot
state provides this.

This task generalizes Task 6's substrate to `m` slots.  The
output depth is still 1, so compositions in later tasks stay
within the depth-2 budget.

- [ ] **Step 1: Layer-1 primitive `Nat.mutuTreeFoldOnCode`**

In `GebLean/Utilities/SzudzikSeq.lean`, inside
`namespace Nat`, add:

```lean
/-- Multi-slot course-of-values recursion on a Gödel code.
With `m` slots, given `m` initial values (for `n = 0`) and an
`m`-ary step combining the `m` slot values from each unpair
component, compute all slots' values at Gödel code `n`.
Generalizes `treeFoldOnCode` from single slot to mutual
`m`-slot.  At `n = encodeBT t` agrees with the `m`-slot
`BT.fold` over `t`. -/
def mutuTreeFoldOnCode {α : Type*} {m : ℕ}
    (base : Fin m → α)
    (step : (Fin m → α) → (Fin m → α) → Fin m → α) :
    ℕ → Fin m → α
  | 0,     => base
  | n + 1, => step
      (mutuTreeFoldOnCode base step (unpair n).1)
      (mutuTreeFoldOnCode base step (unpair n).2)
  termination_by n => n
  decreasing_by
    · exact Nat.lt_succ_of_le (unpair_left_le n)
    · exact Nat.lt_succ_of_le (unpair_right_le n)
```

plus `@[simp]` reduction lemmas `mutuTreeFoldOnCode_zero` and
`mutuTreeFoldOnCode_succ`.

Note: signature details (e.g. whether to return `Fin m → α`
vs. curried at each position) are implementation choices —
adapt for cleanest proofs.  The key property is course-of-
values recursion with unpair-based descent on a ℕ argument.

- [ ] **Step 2: Layer-1 correctness theorem**

```lean
theorem mutuTreeFoldOnCode_encodeBT {α : Type} {m : ℕ}
    (t : BT.{0}) (base : Fin m → α)
    (step : (Fin m → α) → (Fin m → α) → Fin m → α) :
    Nat.mutuTreeFoldOnCode base step (encodeBT t) =
      BT.fold (α := Fin m → α)
        base (fun l r => step l r) t := ...
```

Proof via `BT.ind` (added in the Task 6 refactor).  Reuses the
same structural pattern as `treeFoldOnCode_encodeBT`.

- [ ] **Step 3: Layer-2 substrate `TreeERMor1.mutuFoldOnCode`**

In `GebLean/LawvereTreeERArith.lean`, add:

```lean
/-- Multi-slot course-of-values recursion as a tree-ER term.
At the Nat level, runs `Nat.mutuTreeFoldOnCode` on the Gödel
code of the input; at the tree level, this IS an `m`-slot
`BT.fold` over the input.  `base` and `step` are depth-0
ingredients — `base` has arity 1 (outer-ctx access at leaves),
`step` has arity `m + m` (the `m` slot values from each
recursive branch).  The resulting term has depth 1, leaving
headroom for depth-2 compositions. -/
def TreeERMor1.mutuFoldOnCode {m : ℕ}
    (base : Fin m → TreeERMor1_0 1)
    (step : Fin m → TreeERMor1_0 (m + m))
    (j : Fin m) :
    TreeERMor1_1 1 :=
  TreeERMor1_1.fold base step (TreeERMor1_0.proj 0) j
```

- [ ] **Step 4: Layer-2 agreement theorem**

```lean
@[simp] theorem TreeERMor1.mutuFoldOnCode_interp {m : ℕ}
    (base : Fin m → TreeERMor1_0 1)
    (step : Fin m → TreeERMor1_0 (m + m))
    (j : Fin m) (ctx : Fin 1 → BT.{0}) :
    (TreeERMor1.mutuFoldOnCode base step j).interp ctx =
      decodeBT (Nat.mutuTreeFoldOnCode
        (fun i => encodeBT ((base i).interp ctx))
        (fun leftAll rightAll i =>
          encodeBT ((step i).interp
            (finAppend
              (fun k => decodeBT (leftAll k))
              (fun k => decodeBT (rightAll k)))))
        (encodeBT (ctx 0)) j) := ...
```

Proof via unfolding `mutuFoldOnCode`, applying the tree-ER
interp simp rules (in particular `TreeMor1.interp_fold`), then
rewriting by Step 2's `mutuTreeFoldOnCode_encodeBT` plus a BT-
induction bridge lemma analogous to those from Task 6 (which
are now factored through `BT.ind`).  If a similar
`finAppend`-on-`Fin m` simp lemma is useful (generalizing the
`finAppend_fin1_*` pair added in the Task 6 refactor), extract
it as part of this task.

- [ ] **Step 5: Build and commit**

```bash
lake build GebLean.Utilities.SzudzikSeq \
           GebLean.LawvereTreeERArith
```

Expected: PASS.  Then:

```bash
git add GebLean/Utilities/SzudzikSeq.lean \
        GebLean/LawvereTreeERArith.lean
git commit -m "Add mutuFoldOnCode: multi-slot mutual course-of-values substrate"
```

---

### Task 8: `succOnCode` direct attempt (time-boxed)

**Files:**

* Modify: `GebLean/LawvereTreeERArith.lean`

Prerequisite: Tasks 6–7.

**Purpose:** validate the foundation.  The function-class
argument shows Szudzik-encoded arithmetic must be in depth-2
tree-ER, but the concrete construction is nontrivial.  Before
committing to the general register-machine blueprint (Task 9)
we attempt a direct depth-2 construction of `succOnCode`.  If
the direct construction works, other primitives may follow the
same pattern.  If it does not work after one implementation
cycle, Task 9's blueprint provides a mechanical path and Task
10 applies it.

- [ ] **Step 1: Attempt direct `TreeERMor1.succOnCode`**

Target statement:

```lean
def TreeERMor1.succOnCode : TreeERMor1 1 := ...

@[simp] theorem TreeERMor1.succOnCode_interp
    (ctx : Fin 1 → BT.{0}) :
    TreeERMor1.succOnCode.interp ctx =
      decodeBT (encodeBT (ctx 0) + 1) := ...
```

Candidate approaches (try one; if stuck, report BLOCKED —
the outcome informs Task 9):

* **Multi-slot tupling via Task 7's `mutuFoldOnCode`** — carry
  slots tracking Szudzik-shell decomposition of the current
  subtree's code (e.g., `isqrt`, shell number, position within
  shell) so the step can update them coherently.
* **Inner-fold-in-step** — outer `TreeERMor1.fold` whose step
  is a depth-1 term (another fold or `mutuFoldOnCode`) that
  computes within-shell successor arithmetic.

If one candidate compiles with agreement proven, we have
succ and a pattern; document the pattern in the file's
docstring.

- [ ] **Step 2: Build and commit (success case)**

```bash
lake build GebLean.LawvereTreeERArith
git add GebLean/LawvereTreeERArith.lean
git commit -m "Define TreeERMor1.succOnCode (direct depth-2 construction)"
```

- [ ] **Step 3: Report BLOCKED (fallback case)**

If the direct construction does not compile within one
implementation cycle, report BLOCKED with the specific
obstacle encountered.  Task 9 will then provide a general
blueprint and Task 10 will realize `succOnCode` via the
blueprint.

---

### Task 9: Register-machine simulation blueprint

**Files:**

* Create: `GebLean/Utilities/RegisterMachine.lean` (Layer 1
  — general-purpose Nat-level register machine model and its
  course-of-values simulation).
* Modify: `GebLean/Utilities.lean` (add `RegisterMachine`
  import).
* Modify: `GebLean/LawvereTreeERArith.lean` (Layer 2 tree-ER
  packaging + agreement theorem).

**Rationale:** Following Leivant 1999 Lemma 6, every Nat-E₃
function admits a register-machine presentation with an
elementary step count.  Simulating the register machine over
`c · 2_q(|t|)` steps is a depth-2 construction: an outer fold
over a constructed time-counter chain, with step advancing
the machine configuration one tick.  Packaging this as a
reusable combinator means every arithmetic primitive
specializes to a specific machine description rather than
requiring bespoke depth-2 tree-ER construction.

- [ ] **Step 1: Layer-1 register machine abstraction**

In `GebLean/Utilities/RegisterMachine.lean`:

```lean
import Mathlib.Data.Nat.Pairing
import GebLean.LawvereBT
import GebLean.LawvereBTPrimrec

/-!
# Nat-Level Register Machines

An abstract register machine model over `ℕ` suitable for
specifying elementary-recursive functions.  The simulation
semantics agree with `Nat.treeFoldOnCode`-style course-of-
values recursion on a time-counter `ℕ` argument.
-/

namespace GebLean.RegisterMachine

structure RegisterMachine where
  numStates : ℕ
  numRegs : ℕ
  startState : Fin numStates
  endState : Fin numStates
  transition :
    Fin numStates → (Fin numRegs → ℕ) →
      Fin numStates × (Fin numRegs → ℕ)

def step (M : RegisterMachine)
    (cfg : Fin M.numStates × (Fin M.numRegs → ℕ)) :
    Fin M.numStates × (Fin M.numRegs → ℕ) :=
  M.transition cfg.1 cfg.2

def run (M : RegisterMachine) (input : Fin M.numRegs → ℕ)
    (steps : ℕ) :
    Fin M.numStates × (Fin M.numRegs → ℕ) :=
  Nat.rec (M.startState, input)
    (fun _ cfg => step M cfg) steps

end GebLean.RegisterMachine
```

Details (state encoding, transition relation, single-step
progress) are implementation choices — adapt to what proves
cleanest.  The key property: `run` is a Nat-level function
with a well-defined correctness notion against any specific
target Nat function.

- [ ] **Step 2: Layer-1 elementary time bound**

Provide a type of time bounds:

```lean
def RegisterMachine.ElementaryBound : Type := ℕ → ℕ
```

with a predicate `IsElementary : ElementaryBound → Prop`
expressing "this bound is dominated by some finite
tower-of-exponentials function" (use existing `Tower`
infrastructure from `GebLean/Utilities/Tower.lean`).

- [ ] **Step 3: Layer-2 tree-ER packaging**

In `GebLean/LawvereTreeERArith.lean`, add:

```lean
def TreeERMor1.simulateRegisterMachine {n : ℕ}
    (M : GebLean.RegisterMachine.RegisterMachine)
    (inputMapping : Fin n → Fin M.numRegs)
    (outputReg : Fin M.numRegs)
    (timeBound : TreeERMor1_1 n) :
    TreeERMor1 n := ...
```

with interpretation agreement:

```lean
@[simp] theorem TreeERMor1.simulateRegisterMachine_interp
    {n} (M inputMapping outputReg timeBound)
    (ctx : Fin n → BT.{0}) :
    (simulateRegisterMachine M inputMapping outputReg timeBound)
      .interp ctx =
      decodeBT
        (((GebLean.RegisterMachine.run M
            (fun i => encodeBT (ctx (inputMapping i)))
            (encodeBT (timeBound.interp ctx))).2) outputReg) := ...
```

Implementation strategy: build a time-counter chain of
`encodeBT (timeBound.interp ctx)` nodes via a depth-1 fold
producing exponential-size trees, then outer fold simulates
each transition step.

- [ ] **Step 4: Build and commit**

```bash
lake build GebLean.Utilities.RegisterMachine \
           GebLean.LawvereTreeERArith
git add GebLean/Utilities/RegisterMachine.lean \
        GebLean/Utilities.lean \
        GebLean/LawvereTreeERArith.lean
git commit -m "Add register-machine simulation blueprint (Layers 1 and 2)"
```

This task is the hardest of Stage β, flagged as a distinct
piece of infrastructure.  If blocked on the depth-2 fit or
the time-counter construction, escalate; the design may need
to split the blueprint into smaller pieces.

---

### Task 10: `succOnCode` (if unresolved) and `subOnCode` via blueprint

**Files:**

* Modify: `GebLean/LawvereTreeERArith.lean`

Prerequisite: Task 6's `treeFoldOnCode`, Task 7's
`mutuFoldOnCode`, and Task 9's
`simulateRegisterMachine`.  If Task 8 succeeded in defining
`succOnCode` directly, this task covers `subOnCode` only; if
Task 8 reported BLOCKED, this task covers both.

- [ ] **Step 1: Add definitions**

```lean
def TreeERMor1.succOnCode : TreeERMor1 1 := ...
def TreeERMor1.subOnCode : TreeERMor1 2 := ...
```

`succOnCode` increments the Gödel code: `fun bt => decodeBT
(encodeBT bt + 1)`.  Build via `treeFoldOnCode` with a base
and step that together compute successor on the decoded code.

`subOnCode` implements Gödel-level cut-off subtraction:
`fun (x, y) => decodeBT (encodeBT x -̇ encodeBT y)`.  Build via
`treeFoldOnCode` with appropriate handlers; the second
argument may be threaded through the fold via the context.

Each primitive is a single application of `treeFoldOnCode`
with depth-0 base and step, so sits at depth ≤ 1.

- [ ] **Step 2: Agreement theorems**

```lean
@[simp] theorem TreeERMor1.succOnCode_interp
    (ctx : Fin 1 → BT.{0}) :
    TreeERMor1.succOnCode.interp ctx =
      decodeBT (encodeBT (ctx 0) + 1) := ...

@[simp] theorem TreeERMor1.subOnCode_interp
    (ctx : Fin 2 → BT.{0}) :
    TreeERMor1.subOnCode.interp ctx =
      decodeBT (encodeBT (ctx 0) - encodeBT (ctx 1)) := ...
```

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERArith
git add GebLean/LawvereTreeERArith.lean
git commit -m "Define TreeERMor1 succ/sub on Gödel codes"
```

---

### Task 11: `szudzikPair` + agreement

**Files:**

* Modify: `GebLean/LawvereTreeERArith.lean`

Prerequisites: Tasks 6–10.  This task may also introduce
inline helpers (addition, multiplication, squaring, comparison,
conditional) built as register-machine-blueprint
specializations (Task 9) or direct depth-2 constructions.

- [ ] **Step 1: Add `TreeERMor1.szudzikPair` definition**

Szudzik's formula: `Nat.pair a b = if a < b then b² + a else
a² + a + b`.  Each sub-operation (comparison, squaring,
addition, conditional branch) is expressible as an application
of `treeFoldOnCode` and can be defined as an inline helper in
this task if it does not already exist.  Composition via
`TreeERMor1.comp` (which takes the max of depths) keeps the
overall depth ≤ 2.

```lean
def TreeERMor1.szudzikPair : TreeERMor1 2 := ...
```

- [ ] **Step 2: Agreement theorem**

```lean
@[simp] theorem TreeERMor1.szudzikPair_interp
    (ctx : Fin 2 → BT.{0}) :
    TreeERMor1.szudzikPair.interp ctx =
      decodeBT (Nat.pair (encodeBT (ctx 0))
                         (encodeBT (ctx 1))) := ...
```

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERArith
git add GebLean/LawvereTreeERArith.lean
git commit -m "Define TreeERMor1.szudzikPair with interp agreement"
```

---

### Task 12: `szudzikUnpairL` / `szudzikUnpairR` + agreement

**Files:**

* Modify: `GebLean/LawvereTreeERArith.lean`

Prerequisites: Tasks 6–9.

- [ ] **Step 1: Add unpair definitions**

```lean
def TreeERMor1.szudzikUnpairL : TreeERMor1 1 := ...
def TreeERMor1.szudzikUnpairR : TreeERMor1 1 := ...
```

The Szudzik unpair is `let s := isqrt z in
if z - s² < s then (z - s², s) else (s, z - s² - s)`.
Implementation builds the integer square root and the pair
projections via `treeFoldOnCode` / `mutuFoldOnCode`-based
helpers, plus the subtraction primitive from Task 10 and the
comparison helper from Task 11.

- [ ] **Step 2: Add agreement theorems**

```lean
@[simp] theorem TreeERMor1.szudzikUnpairL_interp
    (ctx : Fin 1 → BT.{0}) :
    TreeERMor1.szudzikUnpairL.interp ctx =
      decodeBT (Nat.unpair (encodeBT (ctx 0))).1 := ...

@[simp] theorem TreeERMor1.szudzikUnpairR_interp
    (ctx : Fin 1 → BT.{0}) :
    TreeERMor1.szudzikUnpairR.interp ctx =
      decodeBT (Nat.unpair (encodeBT (ctx 0))).2 := ...
```

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERArith
git add GebLean/LawvereTreeERArith.lean
git commit -m "Define TreeERMor1.szudzikUnpairL/R with agreement"
```

---

### Task 13: `bsumOnCode` and `bprodOnCode` + agreement

**Files:**

* Modify: `GebLean/LawvereTreeERArith.lean`

Prerequisites: Tasks 6–10.

- [ ] **Step 1: Add definitions**

```lean
def TreeERMor1.bsumOnCode {k : ℕ}
    (f : TreeERMor1_1 (k + 1)) : TreeERMor1 (k + 1) := ...

def TreeERMor1.bprodOnCode {k : ℕ}
    (f : TreeERMor1_1 (k + 1)) : TreeERMor1 (k + 1) := ...
```

These realize bounded sum / bounded product on Gödel codes
via `simulateRegisterMachine` (Task 9) with register-machine
descriptions for bounded sum and bounded product.  Both are
elementary-time in the bound, so Task 9's blueprint applies
directly.

- [ ] **Step 2: Agreement theorems**

Match the ER generator semantics:

```lean
@[simp] theorem TreeERMor1.bsumOnCode_interp {k : ℕ}
    (f : TreeERMor1_1 (k + 1))
    (ctx : Fin (k + 1) → BT.{0}) :
    (TreeERMor1.bsumOnCode f).interp ctx =
      decodeBT (natBSum (encodeBT (ctx 0)) (fun i =>
        encodeBT (f.interp (Fin.cons (decodeBT i)
          (Fin.tail ctx))))) := ...
```

(Analogous for `bprodOnCode`.)

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERArith
git add GebLean/LawvereTreeERArith.lean
git commit -m "Define TreeERMor1 bsum/bprod on Gödel codes"
```

---

### Task 14: `mutuFoldViaPair` + agreement

**Files:**

* Modify: `GebLean/LawvereTreeERArith.lean`

- [ ] **Step 1: Add definition**

```lean
def TreeERMor1.mutuFoldViaPair {k : ℕ}
    (init : Fin k → TreeERMor1 0)
    (step : Fin k → TreeERMor1 (k + 1))
    (bound : TreeERMor1 1) (j : Fin k) : TreeERMor1 1 := ...
```

Implementation: pack initial values via `szudzikPair`, run
bounded iteration with a packed step, unpack at the end via
`szudzikUnpair` at index `j`.  Uses Layer 1's `Nat.tupleRecN`
as the spec.

- [ ] **Step 2: Agreement theorem**

Link to `Nat.tupleRecN` via `encodeBT` / `decodeBT`.

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERArith
git add GebLean/LawvereTreeERArith.lean
git commit -m "Define TreeERMor1.mutuFoldViaPair with agreement"
```

---

### Task 15: Register and test Stage β

**Files:**

* Modify: `GebLean.lean` (add Layer 2 import)
* Create: `GebLeanTests/LawvereTreeERArith.lean`
* Modify: `GebLeanTests.lean`

- [ ] **Step 1: Register**

Add `import GebLean.LawvereTreeERArith` after
`LawvereTreeERInterp`.

- [ ] **Step 2: Test file**

```lean
import GebLean.LawvereTreeERArith

open GebLean

-- Type-checks for each Layer-2 primitive.
example : TreeERMor1 2 := TreeERMor1.szudzikPair
example : TreeERMor1 1 := TreeERMor1.szudzikUnpairL
example : TreeERMor1 1 := TreeERMor1.szudzikUnpairR
example : TreeERMor1 1 := TreeERMor1.succOnCode
example : TreeERMor1 2 := TreeERMor1.subOnCode

-- Agreement-theorem sanity via `#guard` on a small example.
-- (e.g., TreeERMor1.succOnCode applied to `encodeBT leaf = 0`
-- should give decodeBT 1 = node leaf leaf.)
```

- [ ] **Step 3: Register test + build + test + commit**

```bash
lake build && lake test
git add GebLean.lean \
        GebLeanTests/LawvereTreeERArith.lean \
        GebLeanTests.lean
git commit -m "Register and test Stage β of Tree-ER 4g.2"
```

---

## Stage γ: Layer 3 — translation functors + isomorphism

### Task 16: Create `LawvereTreeERLawvereEquiv.lean` + `ERMor1.toTreeER`

**Files:**

* Create: `GebLean/LawvereTreeERLawvereEquiv.lean`

- [ ] **Step 1: File header**

```lean
import GebLean.LawvereTreeERArith
import GebLean.LawvereERInterp

/-!
# Categorical Isomorphism `LawvereERCat ≅ LawvereTreeERCat`

The `J` and `K` functors realizing the isomorphism, with
mutual-inverse proofs and the natural iso `btInterp ∘ K ≅
erInterpFunctor`.
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Add `ERMor1.toTreeER` translation**

Inside namespace:

```lean
def ERMor1.toTreeER : {n : ℕ} → ERMor1 n → TreeERMor1 n
  | _, .zero        => TreeERMor1.leaf
  | _, .succ        => TreeERMor1.succOnCode
  | _, .proj i      => TreeERMor1.proj i
  | _, .sub         => TreeERMor1.subOnCode
  | _, .comp f g    =>
      TreeERMor1.comp f.toTreeER (fun i => (g i).toTreeER)
  | _, .bsum f      => TreeERMor1.bsumOnCode f.toTreeER.toD1
  | _, .bprod f     => TreeERMor1.bprodOnCode f.toTreeER.toD1
```

where `toD1` is a helper converting `TreeERMor1` to
`TreeERMor1_1` when the depth is ≤ 1 (required for
`bsumOnCode` which takes depth-1 args).  Depth analysis is
needed — ER's bsum/bprod's `f` is already at most depth k+1
of ER's structure, which after translation should stay
depth-≤-1 of tree-ER (because ER's recursion constructors are
bsum/bprod, and they translate to depth-≤-1 trees... this
needs verification).

If depth analysis doesn't work out, adjust the translation
to widen where needed.

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERLawvereEquiv
git add GebLean/LawvereTreeERLawvereEquiv.lean
git commit -m "Define ERMor1.toTreeER translation"
```

---

### Task 17: `J : LawvereERCat ⥤ LawvereTreeERCat`

**Files:**

* Modify: `GebLean/LawvereTreeERLawvereEquiv.lean`

- [ ] **Step 1: Lift to tuples and quotient**

```lean
def ERMorN.toTreeERMorN {n m : ℕ}
    (f : ERMorN n m) : TreeERMorN n m :=
  fun i => (f i).toTreeER

def ERMorN.toTreeER_sound {n m : ℕ}
    (f g : ERMorN n m)
    (h : ∀ ctx, f.interp ctx = g.interp ctx) :
    ∀ ctx, (f.toTreeERMorN).interp ctx =
           (g.toTreeERMorN).interp ctx := ...
-- proof via agreement theorems + encodeBT_decodeBT
```

- [ ] **Step 2: Define functor J**

```lean
def J : LawvereERCat ⥤ LawvereTreeERCat where
  obj n := n
  map {n m} f :=
    Quotient.lift
      (fun f' => Quotient.mk _ f'.toTreeERMorN)
      (fun _ _ h => Quotient.sound (toTreeER_sound _ _ h))
      f
  map_id := ...
  map_comp := ...
```

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERLawvereEquiv
git add GebLean/LawvereTreeERLawvereEquiv.lean
git commit -m "Define functor J : LawvereERCat ⥤ LawvereTreeERCat"
```

---

### Task 18: `TreeMor1.toERMor1_depth2` translation

**Files:**

* Modify: `GebLean/LawvereTreeERLawvereEquiv.lean`

The reverse translation: tree-ER terms at depth ≤ 2 to
ER terms.  Structural recursion on `TreeMor1`, using the depth
bound to restrict the `fold` case's arguments.

- [ ] **Step 1: Define translation**

```lean
def TreeMor1.toERMor1 :
    {n : ℕ} → (t : TreeMor1 n) → t.foldDepth ≤ 2 → ERMor1 n
  | _, .leaf, _       => ERMor1.zero'.erased
    -- leaf's interp is BT.leaf; encoded is 0; use ERMor1.zero-equivalent
  | _, .branch l r, h =>
      -- branch encodes (1 + pair l r); use pair + succ as ER terms
      ERMor1.branchCode
        (l.toERMor1 (by simp [TreeMor1.foldDepth] at h; omega))
        (r.toERMor1 (by simp [TreeMor1.foldDepth] at h; omega))
  | _, .proj i, _     => ERMor1.proj i
  | _, .comp f g, h   =>
      ERMor1.comp
        (f.toERMor1 (by ...))
        (fun i => (g i).toERMor1 (by ...))
  | _, .fold m f g t j, h =>
      -- fold at depth ≤ 2 means args are depth ≤ 1
      -- Use ER's treeFoldOnCode helper (to be defined)
      ERMor1.treeFoldOnCode ...
```

where `ERMor1.branchCode`, `ERMor1.treeFoldOnCode`, etc. are
ER-level helpers computing tree operations on Gödel codes.
These must be defined first (add them above).

- [ ] **Step 2: Add supporting ER helpers**

Define `ERMor1.branchCode : ERMor1 2` (computes `1 + pair x
y` as an ER term), `ERMor1.leafCode : ERMor1 0` (= `zero`),
`ERMor1.treeFoldOnCode : ERMor1 0 → ERMor1 2 → ERMor1 1`
(analogous to Layer 2's tree-ER version).

Some of these may live better in a dedicated
`GebLean/LawvereERArith.lean` extension or a new file.  Pick
a consistent location.

- [ ] **Step 3: Build and commit**

```bash
lake build GebLean.LawvereTreeERLawvereEquiv
git add GebLean/LawvereTreeERLawvereEquiv.lean
git commit -m "Define TreeMor1.toERMor1 (depth-2 to ER translation)"
```

---

### Task 19: `K : LawvereTreeERCat ⥤ LawvereERCat`

**Files:**

* Modify: `GebLean/LawvereTreeERLawvereEquiv.lean`

Similar to Task 17: lift `TreeMor1.toERMor1` to tuples +
quotient, define the functor K.

- [ ] **Step 1: Tuple lifting**

```lean
def TreeERMorN.toERMorN {n m : ℕ}
    (f : TreeERMorN n m) : ERMorN n m :=
  fun i => (f i).val.toERMor1 (f i).property

def TreeERMorN.toERMorN_sound {n m : ℕ} ... := ...
```

- [ ] **Step 2: Functor K**

```lean
def K : LawvereTreeERCat ⥤ LawvereERCat where
  obj n := n
  map := ...  -- via Quotient.lift
  map_id := ...
  map_comp := ...
```

- [ ] **Step 3: Build and commit**

---

### Task 20: `K ∘ J = 1` and `J ∘ K = 1`

**Files:**

* Modify: `GebLean/LawvereTreeERLawvereEquiv.lean`

- [ ] **Step 1: `K ∘ J = 1_LawvereERCat`**

```lean
theorem K_comp_J :
    J ⋙ K = 𝟭 LawvereERCat := by
  apply Functor.ext
  · intro n; rfl
  · intro n m f
    -- unwrap f via Quotient.ind
    -- use agreement theorems + encodeBT_decodeBT to show
    -- K(J(f)).interp = f.interp, hence equal in quotient
    ...
```

- [ ] **Step 2: `J ∘ K = 1_LawvereTreeERCat`**

Analogous.

- [ ] **Step 3: Build and commit**

---

### Task 21: Natural iso `btInterp ∘ K ≅ erInterpFunctor`

**Files:**

* Modify: `GebLean/LawvereTreeERLawvereEquiv.lean`

- [ ] **Step 1: Define `encodeVec` natural transformation**

```lean
def encodeVec {n : ℕ} : (Fin n → BT.{0}) ≃ (Fin n → ℕ) :=
  { toFun := fun ctx i => encodeBT (ctx i),
    invFun := fun nctx i => decodeBT (nctx i),
    left_inv := ..., right_inv := ... }

def encodeNT : btInterpFunctor ⋙ K ≅ erInterpFunctor := ...
```

Note: `btInterp` here is actually `treeErInterpFunctor ⋙ ???`
— clarify which BT-level interp functor is meant.  The spec
says `btInterp ∘ K ≅ erInterp` where `btInterp` is the
interp functor for `LawvereBTQuotCat` composed through
`treeErInclusion`.  Adjust to match the actual types.

- [ ] **Step 2: Build and commit**

---

### Task 22: Register and test Stage γ

**Files:**

* Modify: `GebLean.lean`
* Create: `GebLeanTests/LawvereTreeERLawvereEquiv.lean`
* Modify: `GebLeanTests.lean`

- [ ] **Step 1: Register Layer 3**

Add `import GebLean.LawvereTreeERLawvereEquiv` after
`LawvereTreeERArith`.

- [ ] **Step 2: Tests**

```lean
import GebLean.LawvereTreeERLawvereEquiv

open GebLean CategoryTheory

example : LawvereERCat ⥤ LawvereTreeERCat := J
example : LawvereTreeERCat ⥤ LawvereERCat := K
example : J ⋙ K = 𝟭 LawvereERCat := K_comp_J
example : K ⋙ J = 𝟭 LawvereTreeERCat := J_comp_K
```

- [ ] **Step 3: Register + build + test + commit**

---

### Task 23: Workstream tracker update

**Files:**

* Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Append 4g.2 completion paragraph**

Add after the Phase 4g.1 paragraph:

```markdown
Phase 4g.2 complete: see `GebLean/Utilities/SzudzikSeq.lean` for
Layer 1 (Lean-native Szudzik sequence encoding, tree-fold
simulator, finite mutumorphism);
`GebLean/LawvereTreeERArith.lean` for Layer 2 (tree-ER
syntactic arithmetic with `@[simp]` agreement theorems); and
`GebLean/LawvereTreeERLawvereEquiv.lean` for Layer 3 — the
categorical isomorphism `LawvereERCat ≅ LawvereTreeERCat` via
functors `J` and `K`, with `K ∘ J = 𝟭` and `J ∘ K = 𝟭`, plus
the natural iso `btInterp ∘ K ≅ erInterpFunctor` via
`encodeVec`.
```

- [ ] **Step 2: Flip 4g.2 checkbox**

Replace `* [ ] 4g.2: ...` with `* [x] 4g.2: ...`.

- [ ] **Step 3: Commit**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 4g.2 complete in workstream tracker"
```

---

## Self-Review

**Spec coverage:**

* Layer 1 (generic Lean arithmetic, including
  `mutuTreeFoldOnCode` added in Task 7 and `RegisterMachine`
  added in Task 9) — Tasks 1–5 plus Layer-1 parts of Tasks 7
  and 9.
* Layer 2 (tree-ER syntactic arithmetic: two fold substrates
  `treeFoldOnCode` and `mutuFoldOnCode`, the
  `simulateRegisterMachine` blueprint, and 8 derived
  primitives + agreements) — Tasks 6–15.
* Layer 3 (J, K, mutual-inverse, natural iso) — Tasks 16–22.
* Workstream tracker — Task 23.

**Placeholder scan:**

The plan uses `...` placeholders in several Stage β/γ tasks
where the exact Lean term or proof is implementation-dependent
and best worked out interactively with Lean LSP.  These are
identified with "placeholder; concrete term to be constructed"
or similar flags.  For each such placeholder, the surrounding
text provides:

* The target theorem statement (agreement form).
* The conceptual construction (fold-table, iterated pair, etc.).
* A citation to either the Layer-1 function it corresponds to
  or a Mathlib lemma to match.

This is acceptable because 4g.2's hardest pieces (tree-fold
simulation, Szudzik pair/unpair at the syntactic level) are
genuinely novel Lean constructions where an advance-specified
term is likely to be wrong in details; concrete terms will be
derived during implementation with an implementer's LSP-guided
iteration.

**Type consistency:**

* `TreeERMor1 n`, `TreeERMor1_0 n`, `TreeERMor1_1 n` used
  consistently from 4g.1.
* `ERMor1 n`, `ERMorNQuo n m` used consistently per
  `LawvereER.lean` / `LawvereERQuot.lean`.
* `Nat.pair`, `Nat.unpair`, `Nat.seqPack`, `Nat.seqAt`,
  `Nat.treeFoldOnCode`, `Nat.mutuTreeFoldOnCode`,
  `Nat.tupleRecN` — consistent.
* Functor names `J`, `K` used consistently across Tasks 17–22.
* `ERMor1.toTreeER`, `TreeMor1.toERMor1` — the translation
  names are consistent.

**Risk flags:**

* **Tasks 6, 7, and 9 are the Stage-β foundations.**  Task 6
  (complete) and Task 7 (complete) provide single- and multi-
  slot fold substrates on Gödel codes.  Task 9 provides the
  register-machine simulation blueprint, which is the general
  path to realizing any Nat-E₃ function as a depth-2 tree-ER
  term under Szudzik encoding (Leivant 1999 Lemma 6).  Tasks
  10–13 each specialize the blueprint with a specific machine
  description.
* **Task 8 is exploratory.**  A direct succOnCode construction
  at depth 2 would be cleaner than the general register-machine
  path.  Task 8 attempts this in one implementation cycle.  If
  successful, Task 10 inherits the pattern; if blocked, Task 9
  supplies the fallback.
* **Task 9 is the hardest individual piece.**  Constructing a
  time-counter chain of `c · 2_q(|t|)` nodes from an input
  of tree-size `|t|` is a depth-1 exponential-size construction.
  Simulating a register machine transition per outer fold step
  requires careful state-encoding.  If blocked, escalate; we
  may split the blueprint into sub-primitives (time-counter
  construction, machine-step combinator, final decoding) as
  separate helpers.
* **Task 18 (`TreeMor1.toERMor1`) fold case** needs
  `ERMor1.treeFoldOnCode` — an ER-level helper not defined
  before this task.  Add its definition as a prelude (either a
  `GebLean/LawvereERArith.lean` extension or inline in
  `LawvereTreeERLawvereEquiv.lean`) before or during Task 18.
* **Stage γ's "isomorphism on the nose" proofs** rely on
  `Functor.ext` + agreement theorems.  If `Functor.ext` requires
  more than trivial object/morphism agreement, fall back to
  equivalence via `Equivalence.mk` (the spec permits this).
