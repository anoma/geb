# Lawvere ER Phase 4f.1: Non-Fullness via Ackermann + Exponentiation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that `erInterpFunctor : LawvereERCat ⥤ Type` is not full,
with the Ackermann function as the witness, and positively define
exponentiation as an ER term (`expER = bprod (proj 1)`).

**Architecture:** Build `GebLean/LawvereERPrimrec.lean` containing a
structural-recursion translation `ERMor1.toPrimrec' : ∀ {n} (t : ERMor1 n),
Nat.Primrec' (fun v : List.Vector ℕ n => t.interp v.get)`, one case per
generator.  Then in `LawvereERInterp.lean`, combine this with Mathlib's
`not_primrec₂_ack` to derive `¬ erInterpFunctor.Full`.  Add a separate file
`GebLean/LawvereERArith.lean` defining `ERMor1.expER := bprod (proj 1)` with
its interpretation theorem and the `natBProd_const` helper.

**Tech Stack:** Lean 4 + Mathlib (`Mathlib.Computability.Primrec`,
`Mathlib.Computability.Primrec.List`, `Mathlib.Computability.Ackermann`),
categorical functor fullness API.

**Translation mapping (for reference in every Primrec task):**

| ER generator          | Mathlib witness                                          |
|-----------------------|----------------------------------------------------------|
| `ERMor1.zero`         | `Nat.Primrec'.zero`                                      |
| `ERMor1.succ`         | `Nat.Primrec'.succ`                                      |
| `ERMor1.proj i`       | `Nat.Primrec'.get i`                                     |
| `ERMor1.sub`          | `Nat.Primrec'.sub`                                       |
| `ERMor1.comp f g`     | `Nat.Primrec'.comp _ hf hg` + `List.Vector.get_ofFn`     |
| `ERMor1.bsum f`       | `Nat.Primrec'.prec (const 0) step_bsum`                  |
| `ERMor1.bprod f`      | `Nat.Primrec'.prec (const 1) step_bprod`                 |

**Key Mathlib lemmas (from research):**

- `Nat.Primrec'.prim_iff₂ : @Nat.Primrec' 2 (fun v => f v.head v.tail.head)
  ↔ Nat.Primrec₂ f`
- `Nat.not_primrec₂_ack : ¬ Nat.Primrec₂ ack`
- `List.Vector.get_ofFn : (List.Vector.ofFn f).get i = f i`
- `List.Vector.get_zero : v.get 0 = v.head` (at positive arity)
- `List.Vector.get_cons_succ : (a ::ᵥ v).get i.succ = v.get i`
- `Functor.map_surjective` (field of `Functor.Full`)

---

## File Structure

Files to create:

- `GebLean/LawvereERArith.lean` — defines `ERMor1.expER`, the
  `natBProd_const` helper, and the exponentiation interpretation theorem.
- `GebLean/LawvereERPrimrec.lean` — defines `ERMor1.toPrimrec'` by structural
  recursion on ER terms.
- `GebLeanTests/LawvereERArith.lean` — sanity tests for `expER` interpretation.
- `GebLeanTests/LawvereERPrimrec.lean` — sanity tests for the translation and
  the non-fullness corollary.

Files to modify:

- `GebLean/LawvereERInterp.lean` — add `¬ erInterpFunctor.Full` theorem at
  the end, importing the Primrec' bridge.
- `GebLean.lean` — re-export the new public modules.
- `GebLeanTests.lean` — add test imports.
- `.session/workstreams/lawvere-elementary-recursive.md` — mark 4f.1 done.

---

## Task 1: Stub `LawvereERArith.lean` with `natBProd_const`

**Files:**

- Create: `GebLean/LawvereERArith.lean`

The `natBSum_const` helper already exists in `GebLean/LawvereER.lean:72`.
We add its product analog here, since `expER` uses it.

- [ ] **Step 1: Create the file with namespace header and imports**

```lean
import GebLean.LawvereER

/-!
# Arithmetic on Elementary Recursive Terms

Derived arithmetic operations beyond the generators:
exponentiation via bounded product.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Add `natBProd_const` helper inside the namespace**

Insert before `end GebLean`:

```lean
/-- Product of a constant function: multiplying `y` over
`bound` iterations equals `y ^ bound`. -/
theorem natBProd_const (bound y : ℕ) :
    natBProd bound (fun _ => y) = y ^ bound := by
  induction bound with
  | zero => rfl
  | succ b ih =>
    change natBProd b (fun _ => y) * y = y ^ (b + 1)
    rw [ih, Nat.pow_succ]
```

- [ ] **Step 3: Build**

Run: `lake build GebLean.LawvereERArith`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereERArith.lean
git commit -m "Add LawvereERArith with natBProd_const helper"
```

---

## Task 2: Define `ERMor1.expER` and its interpretation

**Files:**

- Modify: `GebLean/LawvereERArith.lean`

- [ ] **Step 1: Add `ERMor1.expER` before `end GebLean`**

```lean
/-- Exponentiation as an elementary recursive term:
`expER` interprets at context `[n, y]` as `y ^ n`,
built via bounded product of the projection onto `y`. -/
def ERMor1.expER : ERMor1 2 :=
  ERMor1.bprod (ERMor1.proj 1)
```

- [ ] **Step 2: Add the interpretation theorem**

```lean
/-- Interpretation of `expER`: `expER.interp [n, y] = y ^ n`. -/
@[simp] theorem ERMor1.interp_expER (ctx : Fin 2 → ℕ) :
    ERMor1.expER.interp ctx = (ctx 1) ^ (ctx 0) := by
  change natBProd (ctx 0)
    (fun i => (ERMor1.proj (k := 2) 1).interp
      (Fin.cons i (Fin.tail ctx))) = (ctx 1) ^ (ctx 0)
  have hpt : (fun i : ℕ =>
      (ERMor1.proj (k := 2) 1).interp
        (Fin.cons i (Fin.tail ctx))) =
      (fun _ => ctx 1) := by
    funext i
    simp [ERMor1.interp_proj, Fin.cons, Fin.tail]
  rw [hpt, natBProd_const]
```

- [ ] **Step 3: Build**

Run: `lake build GebLean.LawvereERArith`
Expected: PASS, no warnings.

- [ ] **Step 4: Register in `GebLean.lean`**

Find the line importing `GebLean.LawvereER` and add below it:

```lean
import GebLean.LawvereERArith
```

- [ ] **Step 5: Build full project**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/LawvereERArith.lean GebLean.lean
git commit -m "Define expER = bprod (proj 1) with interpretation y ^ n"
```

---

## Task 3: Sanity-test `expER`

**Files:**

- Create: `GebLeanTests/LawvereERArith.lean`

- [ ] **Step 1: Write the test file**

```lean
import GebLean.LawvereERArith

/-!
# Tests for LawvereERArith

Sanity tests for derived arithmetic operations on ER terms.
-/

open GebLean

/-- `expER` at `[3, 2]` computes `2 ^ 3 = 8`. -/
#guard ERMor1.expER.interp ![3, 2] = 8

/-- `expER` at `[0, 5]` computes `5 ^ 0 = 1`. -/
#guard ERMor1.expER.interp ![0, 5] = 1

/-- `expER` at `[5, 0]` computes `0 ^ 5 = 0`. -/
#guard ERMor1.expER.interp ![5, 0] = 0

/-- `expER` at `[4, 3]` computes `3 ^ 4 = 81`. -/
#guard ERMor1.expER.interp ![4, 3] = 81
```

- [ ] **Step 2: Register in `GebLeanTests.lean`**

Insert in alphabetical order so the file reads:

```lean
import GebLeanTests.LawvereER
import GebLeanTests.LawvereERArith
import GebLeanTests.LawvereERBool
```

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: PASS, no warnings, all `#guard` assertions pass.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereERArith.lean GebLeanTests.lean
git commit -m "Add LawvereERArith sanity tests for expER"
```

---

## Task 4: Stub `LawvereERPrimrec.lean` with base cases

**Files:**

- Create: `GebLean/LawvereERPrimrec.lean`

The strategy: build `ERMor1.toPrimrec' : ∀ {n} (t : ERMor1 n),
Nat.Primrec' (fun v : List.Vector ℕ n => t.interp v.get)` by structural
recursion on `t`.  We start with the base cases `zero`, `succ`, `proj`, `sub`
and handle `comp`, `bsum`, `bprod` in subsequent tasks.

- [ ] **Step 1: Write the file with imports, namespace, and a stub
  theorem with an explicit underscore for the recursive cases**

```lean
import GebLean.LawvereER
import Mathlib.Computability.Primrec
import Mathlib.Computability.Primrec.List

/-!
# Translation of ER Terms to Mathlib's Primitive Recursive Predicate

For every `ERMor1 n` term `t`, the interpretation
`fun v : List.Vector ℕ n => t.interp v.get` is primitive recursive in the
sense of `Nat.Primrec'`.  This places the elementary recursive functions
strictly within the primitive recursive functions and gives a route to
proving that `erInterpFunctor` is not full via `not_primrec₂_ack`.
-/

namespace GebLean

open Nat

/-- Every elementary recursive term's interpretation is primitive
recursive. -/
theorem ERMor1.toPrimrec' :
    ∀ {n : ℕ} (t : ERMor1 n),
      Nat.Primrec' (fun v : List.Vector ℕ n => t.interp v.get)
  | _, ERMor1.zero => by
    change Nat.Primrec' (fun _ : List.Vector ℕ 0 => 0)
    exact Nat.Primrec'.zero
  | _, ERMor1.succ => by
    change Nat.Primrec' (fun v : List.Vector ℕ 1 =>
      (v.get 0).succ)
    have hget : (fun v : List.Vector ℕ 1 => v.get 0) =
        (fun v : List.Vector ℕ 1 => v.head) := by
      funext v; exact List.Vector.get_zero v
    have : Nat.Primrec' (fun v : List.Vector ℕ 1 =>
        v.head.succ) := Nat.Primrec'.succ
    convert this using 1
    funext v
    rw [List.Vector.get_zero]
  | _, ERMor1.proj i => by
    change Nat.Primrec' (fun v => v.get i)
    exact Nat.Primrec'.get i
  | _, ERMor1.sub => by
    change Nat.Primrec' (fun v : List.Vector ℕ 2 =>
      v.get 0 - v.get 1)
    have : Nat.Primrec' (fun v : List.Vector ℕ 2 =>
        v.head - v.tail.head) := Nat.Primrec'.sub
    convert this using 1
    funext v
    rw [List.Vector.get_zero, show (v.get 1 : ℕ) =
      v.tail.head from rfl]
  | _, ERMor1.comp f g => by
    sorry  -- Task 5
  | _, ERMor1.bsum f => by
    sorry  -- Task 6
  | _, ERMor1.bprod f => by
    sorry  -- Task 7

end GebLean
```

Note: The `sorry` placeholders here are **temporary**, only to let us
commit the base cases before filling in the recursive cases.  The project
policy is no `sorry`, so the tasks below replace each `sorry` before
the next commit.

- [ ] **Step 2: Check the expected failure — base cases compile, but
  `sorry` triggers warnings**

Run: `lake build GebLean.LawvereERPrimrec`
Expected: FAIL with "declaration uses 'sorry'" warnings for the three
unfinished cases.

- [ ] **Step 3: Temporarily allow the build locally by proceeding to
  Task 5 without committing**

Do NOT commit this step's file by itself.  Go directly to Task 5 to
replace the `comp` case's `sorry`, then Task 6 for `bsum`, then Task 7
for `bprod`, then commit the complete file at the end of Task 7.

---

## Task 5: Fill `comp` case in `ERMor1.toPrimrec'`

**Files:**

- Modify: `GebLean/LawvereERPrimrec.lean`

The `comp` case has:
- `f : ERMor1 k`, `g : Fin k → ERMor1 n`.
- IH for `f`: `Nat.Primrec' (fun v : List.Vector ℕ k => f.interp v.get)`.
- IH for each `g i`: `Nat.Primrec' (fun v : List.Vector ℕ n => (g i).interp v.get)`.
- Goal: `Nat.Primrec' (fun v : List.Vector ℕ n => (ERMor1.comp f g).interp v.get)`
  `= Nat.Primrec' (fun v => f.interp (fun i => (g i).interp v.get))`.

`Primrec'.comp` gives:
`Primrec' (fun a => f_inner (List.Vector.ofFn fun i => g_i a))`.

Instantiating `f_inner := fun v => f.interp v.get` and
`g_i := fun v => (g i).interp v.get` yields:
`Primrec' (fun a => f.interp (List.Vector.ofFn fun i => (g i).interp a.get).get)`.

The vector `(List.Vector.ofFn fun i => (g i).interp a.get).get` equals the
function `fun i => (g i).interp a.get` by `List.Vector.get_ofFn`, closing
the case.

- [ ] **Step 1: Replace the `comp` case `sorry` with the full proof**

Locate the line `| _, ERMor1.comp f g => by` and replace its body:

```lean
  | _, ERMor1.comp f g => by
    change Nat.Primrec' (fun v =>
      f.interp (fun i => (g i).interp v.get))
    have hbase : Nat.Primrec' (fun a =>
        f.interp (List.Vector.ofFn
          (fun i => (g i).interp a.get)).get) :=
      Nat.Primrec'.comp
        (fun i v => (g i).interp v.get)
        (ERMor1.toPrimrec' f)
        (fun i => ERMor1.toPrimrec' (g i))
    convert hbase using 1
    funext a
    congr 1
    funext i
    rw [List.Vector.get_ofFn]
```

- [ ] **Step 2: Verify `bsum` and `bprod` remain as `sorry` (do not commit yet)**

Run: `lake build GebLean.LawvereERPrimrec`
Expected: FAIL with `sorry` warnings in `bsum` and `bprod` only.

---

## Task 6: Fill `bsum` case in `ERMor1.toPrimrec'`

**Files:**

- Modify: `GebLean/LawvereERPrimrec.lean`

The `bsum` case has:
- `f : ERMor1 (k + 1)`.
- IH: `Nat.Primrec' (fun v : List.Vector ℕ (k+1) => f.interp v.get)`.
- Goal at arity `k+1`: `Nat.Primrec' (fun v => natBSum v.head
  (fun i => f.interp (Fin.cons i v.tail.get)))` (after using
  `List.Vector.get_zero` for `v.get 0 = v.head` and the fact that
  `Fin.tail v.get = v.tail.get`).

Strategy: apply `Nat.Primrec'.prec` with:
- Base function `f_base : List.Vector ℕ k → ℕ := fun _ => 0`
  (instance `Nat.Primrec'.const 0`).
- Step function `g_step : List.Vector ℕ (k+2) → ℕ` computing
  `IH + f.interp (y ::ᵥ tail).get`, built as the sum of:
  - `fun a : List.Vector ℕ (k+2) => a.tail.head` (= IH),
  - `fun a : List.Vector ℕ (k+2) =>
     f.interp (a.head ::ᵥ a.tail.tail).get` (via IH + comp).

The product of `prec` then rewrites to `natBSum` via
`natBSum_eq_rec` (a local lemma we introduce).

- [ ] **Step 1: Add the `natBSum`-as-`Nat.rec` reformulation lemma**

Insert above `ERMor1.toPrimrec'` inside the namespace:

```lean
/-- `natBSum b f` unfolds to `b.rec 0 (fun y IH => IH + f y)`. -/
theorem natBSum_rec (b : ℕ) (f : ℕ → ℕ) :
    natBSum b f = b.rec 0 (fun y IH => IH + f y) := rfl
```

- [ ] **Step 2: Add a helper bridging `Fin.tail` and `List.Vector.tail`**

Insert directly after `natBSum_rec`:

```lean
/-- `Fin.tail` of `v.get` coincides pointwise with `v.tail.get`. -/
theorem fin_tail_get {n : ℕ} (v : List.Vector ℕ (n + 1)) :
    Fin.tail (v.get) = v.tail.get := by
  funext j
  simp [Fin.tail, List.Vector.get_tail]
```

If `List.Vector.get_tail` is not the exact Mathlib name, the implementer
should search with `lean_local_search` for `Vector.get_tail` or equivalent.
Candidate names include `List.Vector.tail_get`, `List.Vector.get_tail_succ`.

- [ ] **Step 3: Replace the `bsum` case `sorry` with the full proof**

Replace the body of `| _, ERMor1.bsum f => by`:

```lean
  | _, ERMor1.bsum (k := k) f => by
    change Nat.Primrec' (fun v : List.Vector ℕ (k+1) =>
      natBSum (v.get 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail v.get))))
    -- Step function: fun a => a.tail.head + f.interp
    --   ((a.head ::ᵥ a.tail.tail).get)
    have h_ih_applied :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have := Nat.Primrec'.comp
        (fun (i : Fin (k+1)) (a : List.Vector ℕ (k+2)) =>
          (a.head ::ᵥ a.tail.tail).get i)
        (ERMor1.toPrimrec' f)
        (fun i => by
          -- Build Primrec' for projecting out index i
          -- of (a.head ::ᵥ a.tail.tail)
          refine Fin.cases ?_ ?_ i
          · -- i = 0 case: a.head
            exact Nat.Primrec'.head
          · -- i = j.succ case: a.tail.tail.get j
            intro j
            exact (Nat.Primrec'.get j).tail.tail)
      convert this using 1
      funext a
      congr 1
      funext i
      rw [List.Vector.get_ofFn]
    have h_step :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          a.tail.head +
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have hadd : Nat.Primrec' (fun w : List.Vector ℕ 2 =>
          w.head + w.tail.head) := Nat.Primrec'.add
      have := Nat.Primrec'.comp
        (fun (i : Fin 2) (a : List.Vector ℕ (k+2)) =>
          if i = 0 then a.tail.head
          else f.interp (a.head ::ᵥ a.tail.tail).get)
        hadd
        (fun i => by
          refine Fin.cases ?_ ?_ i
          · exact Nat.Primrec'.head.tail
          · intro j
            -- j : Fin 1, so j = 0
            have : j = 0 := Subsingleton.elim _ _
            subst this
            exact h_ih_applied)
      convert this using 1
      funext a
      simp only [List.Vector.get_ofFn]
      congr
    -- Now assemble via prec
    have h_prec := Nat.Primrec'.prec
      (Nat.Primrec'.const (n := k) 0) h_step
    -- Unfold prec's result to match the goal
    convert h_prec using 1
    funext v
    rw [List.Vector.get_zero]
    rw [natBSum_rec]
    -- Goal: natBSum form = v.head.rec 0 (fun y IH => ...)
    -- with step matching via fin_tail_get and cons/tail.
    apply Nat.rec
    · rfl
    · intro y ih
      sorry  -- see Step 4
```

- [ ] **Step 4: Fix the final rewrite from `prec`'s output to
  `natBSum`'s form**

The previous step leaves one goal: proving the step functions agree.
Concretely, after unfolding, we need to show
`f.interp (Fin.cons y (Fin.tail v.get))
  = f.interp (y ::ᵥ v.tail).get` etc.

Replace the bsum body's final `apply Nat.rec ... sorry` construct with
the following terminator (which uses `fin_tail_get` and cons/tail
identities for `List.Vector`):

```lean
    congr 1
    · funext y ih
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [List.Vector.get_zero]
      · intro j'
        simp [Fin.cons_succ, List.Vector.get_cons_succ,
          fin_tail_get]
```

Replacing from `-- Now assemble via prec` to `sorry  -- see Step 4`
with:

```lean
    have h_prec := Nat.Primrec'.prec
      (Nat.Primrec'.const (n := k) 0) h_step
    convert h_prec using 1
    funext v
    rw [List.Vector.get_zero, natBSum_rec]
    congr 1
    funext y ih
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [List.Vector.get_zero]
    · intro j'
      simp [Fin.cons_succ, List.Vector.get_cons_succ,
        fin_tail_get]
```

- [ ] **Step 5: Build `bsum` case only (bprod still sorry)**

Run: `lake build GebLean.LawvereERPrimrec`
Expected: FAIL with `sorry` warning only in `bprod`.  No other errors.

If intermediate goals fail due to unexpected `List.Vector` API names,
pause and search: `mcp__lean-lsp__lean_local_search` on the current
buffer with queries like `Vector.get_tail`, `Vector.cons`, `Vector.head`.

---

## Task 7: Fill `bprod` case in `ERMor1.toPrimrec'`

**Files:**

- Modify: `GebLean/LawvereERPrimrec.lean`

`bprod` is structurally identical to `bsum` but with base `1` and step
`IH * f.interp ...` instead of `IH + f.interp ...`.

- [ ] **Step 1: Add `natBProd_rec` alongside `natBSum_rec`**

Insert directly after `natBSum_rec`:

```lean
/-- `natBProd b f` unfolds to `b.rec 1 (fun y IH => IH * f y)`. -/
theorem natBProd_rec (b : ℕ) (f : ℕ → ℕ) :
    natBProd b f = b.rec 1 (fun y IH => IH * f y) := rfl
```

- [ ] **Step 2: Replace the `bprod` case `sorry`**

Replace the body of `| _, ERMor1.bprod f => by` with a proof that mirrors
the `bsum` body but uses `Nat.Primrec'.mul` instead of `.add` and
`Nat.Primrec'.const 1` instead of `.const 0`:

```lean
  | _, ERMor1.bprod (k := k) f => by
    change Nat.Primrec' (fun v : List.Vector ℕ (k+1) =>
      natBProd (v.get 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail v.get))))
    have h_ih_applied :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have := Nat.Primrec'.comp
        (fun (i : Fin (k+1)) (a : List.Vector ℕ (k+2)) =>
          (a.head ::ᵥ a.tail.tail).get i)
        (ERMor1.toPrimrec' f)
        (fun i => by
          refine Fin.cases ?_ ?_ i
          · exact Nat.Primrec'.head
          · intro j
            exact (Nat.Primrec'.get j).tail.tail)
      convert this using 1
      funext a
      congr 1
      funext i
      rw [List.Vector.get_ofFn]
    have h_step :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          a.tail.head *
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have hmul : Nat.Primrec' (fun w : List.Vector ℕ 2 =>
          w.head * w.tail.head) := Nat.Primrec'.mul
      have := Nat.Primrec'.comp
        (fun (i : Fin 2) (a : List.Vector ℕ (k+2)) =>
          if i = 0 then a.tail.head
          else f.interp (a.head ::ᵥ a.tail.tail).get)
        hmul
        (fun i => by
          refine Fin.cases ?_ ?_ i
          · exact Nat.Primrec'.head.tail
          · intro j
            have : j = 0 := Subsingleton.elim _ _
            subst this
            exact h_ih_applied)
      convert this using 1
      funext a
      simp only [List.Vector.get_ofFn]
      congr
    have h_prec := Nat.Primrec'.prec
      (Nat.Primrec'.const (n := k) 1) h_step
    convert h_prec using 1
    funext v
    rw [List.Vector.get_zero, natBProd_rec]
    congr 1
    funext y ih
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [List.Vector.get_zero]
    · intro j'
      simp [Fin.cons_succ, List.Vector.get_cons_succ,
        fin_tail_get]
```

- [ ] **Step 3: Build full file**

Run: `lake build GebLean.LawvereERPrimrec`
Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 4: Register in `GebLean.lean`**

Append to `GebLean.lean`:

```lean
import GebLean.LawvereERPrimrec
```

- [ ] **Step 5: Build full project**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/LawvereERPrimrec.lean GebLean.lean
git commit -m "Prove every ER term's interpretation is Nat.Primrec'"
```

---

## Task 8: Non-fullness of `erInterpFunctor`

**Files:**

- Modify: `GebLean/LawvereERInterp.lean`

Strategy (mirrors `LawvereBTPrimrec.lean:947` almost exactly): we pick
the hom `h : (Fin 2 → ℕ) → (Fin 1 → ℕ)` with `h ctx _ = ack (ctx 0) (ctx 1)`.
If `erInterpFunctor.Full` held, `h` would have a preimage
`f : ERMorNQuo 2 1`.  Choosing a raw representative `f_raw : ERMorN 2 1`,
the single component `f_raw 0 : ERMor1 2` would have interpretation equal
to `fun ctx => ack (ctx 0) (ctx 1)`.  By `ERMor1.toPrimrec'`, that would
give `Nat.Primrec' (fun v => ack v.head v.tail.head)`, and
`Nat.Primrec'.prim_iff₂` converts this to `Nat.Primrec₂ ack`,
contradicting `not_primrec₂_ack`.

- [ ] **Step 1: Add imports at the top of `LawvereERInterp.lean`**

After the existing imports, add:

```lean
import GebLean.LawvereERPrimrec
import Mathlib.Computability.Ackermann
```

- [ ] **Step 2: Insert the non-fullness theorem before `end GebLean`**

Append inside the namespace:

```lean
/-- Ackermann at arity `2 → 1` is a function
`(Fin 2 → ℕ) → (Fin 1 → ℕ)` that is not in the image of any
`ERMorNQuo 2 1` under `erInterpFunctor`. -/
def ackHom : (Fin 2 → ℕ) → (Fin 1 → ℕ) :=
  fun ctx _ => Nat.ack (ctx 0) (ctx 1)

/-- `erInterpFunctor` is not full: `ackHom`, which is
a well-defined function at the interpretation level,
is not the image of any morphism class of ER tuples. -/
theorem erInterpFunctor_not_full :
    ¬ erInterpFunctor.Full := by
  intro hfull
  have hsurj := Functor.map_surjective
    (F := erInterpFunctor)
    (X := (2 : ℕ)) (Y := (1 : ℕ))
  obtain ⟨f, hf⟩ := hsurj ackHom
  obtain ⟨f_raw, hfr⟩ :=
    Quotient.exists_rep (s := erMorNSetoid 2 1) f
  have hinterp : ∀ ctx : Fin 2 → ℕ,
      f_raw.interp ctx = ackHom ctx := by
    intro ctx
    have : erInterpFunctor.map f = ackHom := hf
    have heq1 : erInterpFunctor.map f =
        ERMorNQuo.interp f := rfl
    rw [heq1, ← hfr] at this
    have := congrFun this ctx
    simp only [ERMorNQuo.interp,
      Quotient.lift_mk] at this
    exact this
  -- Extract the single component
  set t : ERMor1 2 := f_raw 0 with ht
  have hcomp : ∀ ctx : Fin 2 → ℕ,
      t.interp ctx = Nat.ack (ctx 0) (ctx 1) := by
    intro ctx
    have h0 := congrFun (hinterp ctx) 0
    simp only [ERMorN.interp, ackHom] at h0
    exact h0
  -- Now pump to Primrec'
  have hp := t.toPrimrec'
  have heq : (fun v : List.Vector ℕ 2 => t.interp v.get) =
      (fun v : List.Vector ℕ 2 =>
        Nat.ack v.head v.tail.head) := by
    funext v
    rw [hcomp]
    congr 1
    · exact List.Vector.get_zero v
    · rfl
  rw [heq] at hp
  -- Convert to Primrec₂
  have hprim2 : Nat.Primrec₂ Nat.ack :=
    (Nat.Primrec'.prim_iff₂).mp hp
  exact Nat.not_primrec₂_ack hprim2
```

- [ ] **Step 3: Build**

Run: `lake build GebLean.LawvereERInterp`
Expected: PASS, no warnings.

If the final `exact Nat.not_primrec₂_ack hprim2` fails due to namespacing
of `ack` or argument-order mismatches, inspect with `lean_hover_info`
to check whether `Nat.Primrec₂` takes `Nat.ack` or `fun m n => Nat.ack m n`,
and adjust `heq` accordingly.

- [ ] **Step 4: Build full project**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereERInterp.lean
git commit -m "Prove erInterpFunctor is not full via Ackermann"
```

---

## Task 9: Sanity-test the Primrec' translation

**Files:**

- Create: `GebLeanTests/LawvereERPrimrec.lean`

- [ ] **Step 1: Write the test file**

```lean
import GebLean.LawvereERPrimrec
import GebLean.LawvereERInterp

/-!
# Tests for LawvereERPrimrec

Sanity tests: confirm `ERMor1.toPrimrec'` instances type-check for each
generator, and confirm `erInterpFunctor_not_full` type-checks.
-/

open GebLean

-- Primrec' translation works on the atomic generators.
example : Nat.Primrec'
    (fun v : List.Vector ℕ 0 =>
      ERMor1.zero.interp v.get) :=
  ERMor1.zero.toPrimrec'

example : Nat.Primrec'
    (fun v : List.Vector ℕ 1 =>
      ERMor1.succ.interp v.get) :=
  ERMor1.succ.toPrimrec'

example : Nat.Primrec'
    (fun v : List.Vector ℕ 3 =>
      (ERMor1.proj (k := 3) 1).interp v.get) :=
  (ERMor1.proj 1).toPrimrec'

example : Nat.Primrec'
    (fun v : List.Vector ℕ 2 =>
      ERMor1.sub.interp v.get) :=
  ERMor1.sub.toPrimrec'

-- Primrec' translation works on composite terms.
example : Nat.Primrec'
    (fun v : List.Vector ℕ 2 =>
      ERMor1.expER.interp v.get) :=
  ERMor1.expER.toPrimrec'

-- erInterpFunctor is not full.
example : ¬ erInterpFunctor.Full :=
  erInterpFunctor_not_full
```

- [ ] **Step 2: Register in `GebLeanTests.lean`**

Add in alphabetical order after `LawvereERInterp`:

```lean
import GebLeanTests.LawvereERPrimrec
```

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereERPrimrec.lean GebLeanTests.lean
git commit -m "Add LawvereERPrimrec sanity tests and non-fullness check"
```

---

## Task 10: Update workstream tracker

**Files:**

- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Mark 4f.1 complete in the Status section**

Find the `## Status` section of the tracker and append after the current
final paragraph (directly before `## Goal`):

```markdown
Phase 4f.1 complete: see `GebLean/LawvereERPrimrec.lean`
for the structural-recursion translation
`ERMor1.toPrimrec'` showing every elementary recursive
term's interpretation is `Nat.Primrec'`, and
`GebLean/LawvereERInterp.lean` for
`erInterpFunctor_not_full` deriving non-fullness
from Mathlib's `Nat.not_primrec₂_ack`.  The positive
side of the story is recorded in
`GebLean/LawvereERArith.lean`, which defines
`ERMor1.expER = bprod (proj 1)` with interpretation
`y ^ n` and the supporting `natBProd_const` helper.
```

- [ ] **Step 2: Update the Tasks checklist**

Find the non-fullness checkbox line (starting `* [ ] Non-fullness:
prove \`erInterpFunctor\` is not full`) and:

- Split it into two sub-items, the first marked complete.
- Replace the single line with:

```markdown
* Non-fullness of `erInterpFunctor`:
  * [x] 4f.1: Ackermann non-fullness via Primrec' translation.
  * [ ] 4f.2: Tetration non-fullness (deferred pending research).
```

- [ ] **Step 3: Build (no-op for the tracker, but verifies everything
  still passes)**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 4f.1 complete in workstream tracker"
```

---

## Self-Review

**Spec coverage:**

- [x] Positive definition of `expER` as `bprod (proj 1)` — Tasks 1-3.
- [x] `ERMor1.toPrimrec'` covering all seven ER generators — Tasks 4-7.
- [x] `erInterpFunctor_not_full` using Ackermann — Task 8.
- [x] Sanity tests for the new translation — Task 9.
- [x] Tests for the exponentiation definition — Task 3.
- [x] Workstream tracker updated — Task 10.
- [x] Phase 4f.2 (tetration) left open by design.

**Placeholder scan:**

- Only use of `sorry` is in Task 4 Step 1 as a **temporary** placeholder
  that is explicitly removed by the end of Task 7.  The plan says "do not
  commit" between these tasks, so the `sorry` never enters version
  control.  All subsequent tasks show actual code.
- Task 6 Step 2 notes that `List.Vector.get_tail` may not be the exact
  Mathlib name and provides search guidance, which is acceptable.

**Type consistency:**

- `ERMor1.toPrimrec'` signature is fixed in Task 4 Step 1 and used
  consistently in Tasks 5-9.
- `ERMor1.expER : ERMor1 2` defined in Task 2 and tested in Tasks 3, 9.
- `ackHom : (Fin 2 → ℕ) → (Fin 1 → ℕ)` defined in Task 8 and used only
  within that task.
- `natBSum_rec`, `natBProd_rec`, `fin_tail_get` are local helpers defined
  and used within the same file (Tasks 6, 7).

All cross-references consistent.
