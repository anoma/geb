# Lawvere ER Phase 4b: Boolean Operations on ER Terms

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Define `boolNot`, `boolAnd`, and `boolEqNat` as
elementary recursive terms with their semantics
(`@[simp]` interpretation lemmas) and Boolean-closure
properties.  These are the building blocks for the
finite-product (Phase 4c) and equalizer (Phase 4d)
constructions on `LawvereERLexCat`.

**Architecture:** Boolean negation is `1 ⊖ x` (cut-off
subtraction from 1).  Boolean conjunction is
multiplication of `{0, 1}`-valued functions, which is
elementary recursive via `bsum (proj 1)` evaluating to
`x * y` at arity 2.  Boolean equality on `Nat` is
`(1 ⊖ (x ⊖ y)) · (1 ⊖ (y ⊖ x))`.  Closure lemmas state
that `boolNot` and `boolEqNat` always produce `{0, 1}`
values; `boolAnd` does so conditionally on its inputs.

**Tech Stack:** Lean 4, Mathlib
(`Data.Fin.Tuple.Basic`, already imported by
`LawvereER.lean`).  Depends on `GebLean.LawvereER`
(ERMor1, interp, bsum).

---

## File Map

| File | Role |
| ---- | ---- |
| Modify: `GebLean/LawvereER.lean` | Add `ERMor1.zeroN`, `ERMor1.oneN`, `natBSum_const` helper |
| Create: `GebLean/LawvereERBool.lean` | `boolNot`, `boolAnd`, `subSwap`, `boolEqNat` plus interp and Boolean closure lemmas |
| Modify: `GebLean.lean` | Add `import GebLean.LawvereERBool` |
| Create: `GebLeanTests/LawvereERBool.lean` | `#guard` tests for each operation |
| Modify: `GebLeanTests.lean` | Add test import |
| Modify: `.session/workstreams/lawvere-elementary-recursive.md` | Mark Phase 4b complete |

---

## Notes on the Boolean Convention

Convention: `1 = true`, `0 = false`.  Then:

* `boolNot x = 1 ⊖ x` returns `1` iff `x = 0`.  It is
  always `≤ 1` because `Nat`'s cut-off subtraction is
  bounded by its first argument.
* `boolAnd x y = x * y` returns `1` iff both are `1`
  (when each is in `{0, 1}`).  General multiplication
  is not bounded; the Boolean closure is conditional on
  the inputs.
* `boolEqNat x y = (1 ⊖ (x ⊖ y)) * (1 ⊖ (y ⊖ x))`
  returns `1` iff `x = y`.  It is always `≤ 1` because
  it is a product of two `boolNot` results, each `≤ 1`.

---

### Task 1: Constants `zeroN` and `oneN`

**Files:**

- Modify: `GebLean/LawvereER.lean`

- [ ] **Step 1: Add `ERMor1.zeroN` and its interp lemma**

Append before `end GebLean` in `LawvereER.lean`:

```lean
/-- Constant `0` at arity `n`: composes `ERMor1.zero`
with the empty input function. -/
def ERMor1.zeroN (n : ℕ) : ERMor1 n :=
  ERMor1.comp ERMor1.zero (Fin.elim0 (α := ERMor1 n))

/-- Interpretation of `zeroN`: always returns `0`. -/
@[simp] theorem ERMor1.interp_zeroN
    {n : ℕ} (ctx : Fin n → ℕ) :
    (ERMor1.zeroN n).interp ctx = 0 :=
  rfl
```

If the `α := ERMor1 n` annotation is unnecessary, the
implementer may omit it.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 3: Add `ERMor1.oneN` and its interp lemma**

```lean
/-- Constant `1` at arity `n`: applies `ERMor1.succ`
to `zeroN`. -/
def ERMor1.oneN (n : ℕ) : ERMor1 n :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) => ERMor1.zeroN n)

/-- Interpretation of `oneN`: always returns `1`. -/
@[simp] theorem ERMor1.interp_oneN
    {n : ℕ} (ctx : Fin n → ℕ) :
    (ERMor1.oneN n).interp ctx = 1 :=
  rfl
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereER.lean
git commit -m "Add ERMor1.zeroN and ERMor1.oneN constants"
```

---

### Task 2: `natBSum_const` helper

**Files:**

- Modify: `GebLean/LawvereER.lean`

This is the arithmetic lemma needed to evaluate
`boolAnd = bsum (proj 1)` to `ctx 0 * ctx 1`.

- [ ] **Step 1: Add the lemma**

Append before `end GebLean`, after `natBSum`:

```lean
/-- Sum of a constant function: summing `k` over
`bound` iterations equals `bound * k`. -/
theorem natBSum_const (bound k : ℕ) :
    natBSum bound (fun _ => k) = bound * k := by
  induction bound with
  | zero => rfl
  | succ b ih =>
    show natBSum b (fun _ => k) + k = (b + 1) * k
    rw [ih]; ring
```

If the `show` does not match the goal, try unfolding
`natBSum` explicitly:

```lean
  | succ b ih =>
    unfold natBSum
    show Nat.rec 0 (fun _ acc => acc + k) b + k =
         (b + 1) * k
    rw [ih]; ring
```

If `ring` is not available for `Nat`, replace with
`Nat.succ_mul` or manual rewriting:

```lean
    rw [ih, Nat.succ_mul]
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereER.lean
git commit -m "Add natBSum_const arithmetic helper"
```

---

### Task 3: Create `LawvereERBool.lean` with `boolNot`

**Files:**

- Create: `GebLean/LawvereERBool.lean`
- Modify: `GebLean.lean`

- [ ] **Step 1: Create the file**

```lean
import GebLean.LawvereER

/-!
# Boolean Operations on Elementary Recursive Terms

Defines `boolNot`, `boolAnd`, and `boolEqNat` as
specific `ERMor1` terms, together with `@[simp]`
interpretation lemmas and Boolean-closure properties.
Convention: `1 = true`, `0 = false`.

These operations are the building blocks for the
finite-product and equalizer constructions in
`LawvereERLex.lean`.
-/

namespace GebLean

/-- Boolean negation as the indicator of `x = 0`:
returns `1` if input is `0`, else `0`.
Definable as `1 ⊖ x`. -/
def ERMor1.boolNot : ERMor1 1 :=
  ERMor1.comp ERMor1.sub fun i => match i with
    | ⟨0, _⟩ => ERMor1.oneN 1
    | ⟨1, _⟩ => ERMor1.proj 0

/-- Interpretation of `boolNot`: returns `1 ⊖ ctx 0`. -/
@[simp] theorem ERMor1.interp_boolNot
    (ctx : Fin 1 → ℕ) :
    ERMor1.boolNot.interp ctx = 1 - ctx 0 :=
  rfl

/-- `boolNot` always returns a Boolean value. -/
theorem ERMor1.boolNot_le_one (ctx : Fin 1 → ℕ) :
    ERMor1.boolNot.interp ctx ≤ 1 := by
  rw [ERMor1.interp_boolNot]
  exact Nat.sub_le 1 (ctx 0)

end GebLean
```

- [ ] **Step 2: Add import to `GebLean.lean`**

Insert `import GebLean.LawvereERBool` alphabetically
after `import GebLean.LawvereER`.

- [ ] **Step 3: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERBool.lean GebLean.lean
git commit -m "Add boolNot ER term with interp and closure"
```

---

### Task 4: `boolAnd` (multiplication)

**Files:**

- Modify: `GebLean/LawvereERBool.lean`

- [ ] **Step 1: Add `boolAnd` definition and interp lemma**

Append before `end GebLean`:

```lean
/-- Boolean conjunction.  At arity 2, computes
`ctx 0 * ctx 1` via bounded summation; for `{0, 1}`
inputs this is the Boolean `and`. -/
def ERMor1.boolAnd : ERMor1 2 :=
  ERMor1.bsum (ERMor1.proj 1)

/-- Interpretation of `boolAnd`: returns the product
of its two inputs. -/
@[simp] theorem ERMor1.interp_boolAnd
    (ctx : Fin 2 → ℕ) :
    ERMor1.boolAnd.interp ctx = ctx 0 * ctx 1 := by
  show natBSum (ctx 0) _ = ctx 0 * ctx 1
  have h : (fun i : ℕ =>
      (ERMor1.proj (1 : Fin 2)).interp
        (Fin.cons i (Fin.tail ctx))) =
      (fun _ : ℕ => ctx 1) := by
    funext i
    rfl
  rw [h]
  exact natBSum_const _ _
```

If the `funext i; rfl` step does not close, expand:

```lean
    funext i
    show Fin.cons i (Fin.tail ctx) 1 = ctx 1
    rfl
```

If even that does not work, replace with explicit
unfolding:

```lean
    funext i
    simp [ERMor1.interp, Fin.cons, Fin.tail]
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add conditional Boolean closure**

```lean
/-- `boolAnd` returns a Boolean value when both its
inputs are Boolean. -/
theorem ERMor1.boolAnd_le_one_of_le_one
    (ctx : Fin 2 → ℕ)
    (h0 : ctx 0 ≤ 1) (h1 : ctx 1 ≤ 1) :
    ERMor1.boolAnd.interp ctx ≤ 1 := by
  rw [ERMor1.interp_boolAnd]
  calc ctx 0 * ctx 1
      _ ≤ 1 * ctx 1 := Nat.mul_le_mul_right _ h0
      _ ≤ 1 * 1 := Nat.mul_le_mul_left _ h1
      _ = 1 := Nat.one_mul 1
```

If the lemma names differ in the current Mathlib
(`Nat.mul_le_mul_left` vs `mul_le_mul_left'`), the
implementer should adapt to whatever the project's
Mathlib version provides.

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERBool.lean
git commit -m "Add boolAnd ER term with interp and closure"
```

---

### Task 5: `subSwap` and `boolEqNat` definitions

**Files:**

- Modify: `GebLean/LawvereERBool.lean`

- [ ] **Step 1: Add `subSwap` and its interp lemma**

```lean
/-- Cut-off subtraction with arguments swapped:
returns `ctx 1 - ctx 0`.  Used as a building block
for `boolEqNat`. -/
def ERMor1.subSwap : ERMor1 2 :=
  ERMor1.comp ERMor1.sub fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj 1
    | ⟨1, _⟩ => ERMor1.proj 0

/-- Interpretation of `subSwap`. -/
@[simp] theorem ERMor1.interp_subSwap
    (ctx : Fin 2 → ℕ) :
    ERMor1.subSwap.interp ctx = ctx 1 - ctx 0 :=
  rfl
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add `boolEqNat` definition**

```lean
/-- Boolean equality on `Nat`.  Returns `1` if
`ctx 0 = ctx 1`, else `0`.  Definable as
`(1 ⊖ (x ⊖ y)) · (1 ⊖ (y ⊖ x))`. -/
def ERMor1.boolEqNat : ERMor1 2 :=
  ERMor1.comp ERMor1.boolAnd fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.boolNot
          (fun (_ : Fin 1) => ERMor1.sub)
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.boolNot
          (fun (_ : Fin 1) => ERMor1.subSwap)
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERBool.lean
git commit -m "Add subSwap and boolEqNat ER terms"
```

---

### Task 6: `boolEqNat` interp and closure

**Files:**

- Modify: `GebLean/LawvereERBool.lean`

- [ ] **Step 1: Add interp lemma in arithmetic form**

```lean
/-- Interpretation of `boolEqNat`: explicit arithmetic
form. -/
@[simp] theorem ERMor1.interp_boolEqNat
    (ctx : Fin 2 → ℕ) :
    ERMor1.boolEqNat.interp ctx =
      (1 - (ctx 0 - ctx 1)) *
      (1 - (ctx 1 - ctx 0)) := by
  show ERMor1.boolAnd.interp _ = _
  rw [ERMor1.interp_boolAnd]
  rfl
```

If the `show` does not match the goal exactly, try:

```lean
  unfold ERMor1.boolEqNat
  rw [ERMor1.interp_comp, ERMor1.interp_boolAnd]
  rfl
```

Or write out the equality more explicitly:

```lean
  unfold ERMor1.boolEqNat
  simp only [ERMor1.interp_comp,
    ERMor1.interp_boolAnd,
    ERMor1.interp_boolNot,
    ERMor1.interp_sub,
    ERMor1.interp_subSwap]
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add Boolean closure (always Boolean)**

```lean
/-- `boolEqNat` always returns a Boolean value. -/
theorem ERMor1.boolEqNat_le_one (ctx : Fin 2 → ℕ) :
    ERMor1.boolEqNat.interp ctx ≤ 1 := by
  rw [ERMor1.interp_boolEqNat]
  have h1 : 1 - (ctx 0 - ctx 1) ≤ 1 :=
    Nat.sub_le 1 _
  have h2 : 1 - (ctx 1 - ctx 0) ≤ 1 :=
    Nat.sub_le 1 _
  calc (1 - (ctx 0 - ctx 1)) *
       (1 - (ctx 1 - ctx 0))
      _ ≤ 1 * (1 - (ctx 1 - ctx 0)) :=
        Nat.mul_le_mul_right _ h1
      _ ≤ 1 * 1 := Nat.mul_le_mul_left _ h2
      _ = 1 := Nat.one_mul 1
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERBool.lean
git commit -m "Add boolEqNat interp and Boolean closure"
```

---

### Task 7: Sanity tests

**Files:**

- Create: `GebLeanTests/LawvereERBool.lean`
- Modify: `GebLeanTests.lean`

- [ ] **Step 1: Create the test file**

```lean
import GebLean.LawvereERBool
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereERBool

`#guard` sanity tests for `boolNot`, `boolAnd`, and
`boolEqNat`.
-/

open GebLean

private def ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x

private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]

-- boolNot: 1 if input is 0, else 0
#guard ERMor1.boolNot.interp (ctx1 0) == 1
#guard ERMor1.boolNot.interp (ctx1 1) == 0
#guard ERMor1.boolNot.interp (ctx1 5) == 0

-- boolAnd: multiplication
#guard ERMor1.boolAnd.interp (ctx2 0 0) == 0
#guard ERMor1.boolAnd.interp (ctx2 1 1) == 1
#guard ERMor1.boolAnd.interp (ctx2 1 0) == 0
#guard ERMor1.boolAnd.interp (ctx2 0 1) == 0
#guard ERMor1.boolAnd.interp (ctx2 3 4) == 12

-- subSwap: y - x
#guard ERMor1.subSwap.interp (ctx2 3 7) == 4
#guard ERMor1.subSwap.interp (ctx2 7 3) == 0

-- boolEqNat: 1 iff equal
#guard ERMor1.boolEqNat.interp (ctx2 3 3) == 1
#guard ERMor1.boolEqNat.interp (ctx2 0 0) == 1
#guard ERMor1.boolEqNat.interp (ctx2 3 5) == 0
#guard ERMor1.boolEqNat.interp (ctx2 5 3) == 0
```

- [ ] **Step 2: Add import to `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereERBool` alphabetically
after `import GebLeanTests.LawvereER`.

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: clean build, all `#guard` assertions pass.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereERBool.lean \
  GebLeanTests.lean
git commit -m "Add LawvereERBool sanity tests"
```

---

### Task 8: Update workstream tracker

**Files:**

- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Update status section**

Extend the status paragraph to note Phase 4b complete:

"Phase 4b complete: see `GebLean/LawvereERBool.lean` for
`boolNot`, `boolAnd`, `subSwap`, and `boolEqNat` ER
terms with `@[simp]` interpretation lemmas and Boolean
closure properties; `GebLean/LawvereER.lean` extended
with `zeroN`, `oneN` constants and the `natBSum_const`
arithmetic helper."

- [ ] **Step 2: Update task checkbox**

Change:
```
  * [ ] 4b: Boolean operations on ER terms.
```

To:
```
  * [x] 4b: Boolean operations on ER terms.
```

- [ ] **Step 3: Commit**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m \
  "Mark ER Phase 4b complete in workstream tracker"
```
