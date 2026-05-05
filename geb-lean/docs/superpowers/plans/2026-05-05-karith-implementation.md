# KArith Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `KMor1.rec1` to `LawvereKSim`/`LawvereKSimInterp`, then
build twelve K^sim arithmetic functions with `@[simp]` interp
correctness lemmas in a new `Utilities/KArith.lean` module: `pred`,
`isZero`, `add`, `double`, `cond`, `notEq1` (level 1), `mult`,
`monus`, `pow2`, `mod`, `div`, `divNat` (level ≤ 2).

**Architecture:** Each function is a closed-form `KMor1` term built from
existing constructors (`zero`, `succ`, `proj`, `comp`, `simrec`,
`raise`) — no extension to the `KMor1` inductive. `rec1` is a thin
`simrec` wrapper for the non-simultaneous case. `mod` and `div` use a
shared system-size-3 simrec via separate `modAux` / `divAux` helpers.
Each function is paired with a `@[simp]`-marked correctness theorem
linking its interpretation to its `Nat` counterpart, plus a
`example : foo.level ≤ N := by decide` placement proof.

**Tech Stack:** Lean 4, mathlib, `lake build`, `lake test`. No new
deps.

**Spec:** `docs/superpowers/specs/2026-05-05-karith-design.md`. Each
task references the relevant spec section.

---

## Files

- **Modify** `GebLean/LawvereKSim.lean`: add `KMor1.rec1` after the
  existing `KMor1.level` definition (before `level_le_succ`).
- **Modify** `GebLean/LawvereKSimInterp.lean`: add
  `KMor1.interp_rec1_zero` and `KMor1.interp_rec1_succ` `@[simp]`
  lemmas after the existing `KMor1.interp_simrec` block.
- **Create** `GebLean/Utilities/KArith.lean`: all twelve arithmetic
  functions, their `@[simp]` interp theorems, level proofs, and
  inline `#guard` tests. Mirrors `GebLean/Utilities/ERArith.lean`
  structure.
- **Modify** `GebLean.lean`: add `import GebLean.Utilities.KArith`.

## Convention reminders (from CLAUDE.md and the spec)

- After every task, `lake build` and `lake test` must pass with
  no warnings, no `sorry`, no `admit`, no `Classical`, no
  `noncomputable`.
- Every `def` and `theorem` carries a Tourlakis or Marchenkov
  citation in its docstring per the literature-citation discipline.
- Line length ≤ 80 characters.
- Forbidden style words (CLAUDE.md): no "fundamental", "actually",
  "key", "insight", "core", "advanced", "complex", "complicated",
  "simple", "advantage", "benefit", "important", "challenge",
  "yes", "wait", "hmm", "sorry", "careful", "difficult", "blocked",
  "incomplete", "future", "issue", "problem", "block".
- Tests live inline in `Utilities/KArith.lean` (mirroring
  `ERArith.lean`'s pattern, not a separate test file).
- Use `lake build` + `lake test`; never `lake env lean` and never
  `lake clean`.

---

## Phase 0: `rec1` and its interp lemmas

### Task 0.1: Add `KMor1.rec1` to `LawvereKSim.lean`

**Spec:** §3.1.

**Files:**

- Modify: `GebLean/LawvereKSim.lean` (insert before
  `theorem KMor1.level_le_succ`, around line 122).

- [ ] **Step 1: Add `KMor1.rec1` definition**

Insert this block before `theorem KMor1.level_le_succ`:

```lean
/-- Single-output (non-simultaneous) primitive recursion at arity
`a + 1`.  The base `h : KMor1 a` returns the value at recursion
variable `0`; the step `g : KMor1 (a + 2)` receives the recursion
variable, the parameters, and the previous value, in this slot order:

* slot `0`        : recursion variable `x`
* slots `1, …, a` : parameters `y_1, …, y_a`
* slot `a + 1`    : previous value `f(x, y⃗)`

It returns the value at `x + 1`.  Definitional reduction to
`KMor1.simrec` with `k = 0`, `i = 0`.

Tourlakis Notes 10.2.7 (definition of K^sim, with simultaneous
recursion as the primitive); the non-simultaneous case is the
`k = 0` specialization. -/
def KMor1.rec1 {a : ℕ} (h : KMor1 a) (g : KMor1 (a + 2)) :
    KMor1 (a + 1) :=
  KMor1.simrec (a := a) (k := 0) (i := ⟨0, by decide⟩)
    (fun _ => h) (fun _ => g)
```

- [ ] **Step 2: Smoke-check level reduction with one example**

Add immediately after the `rec1` definition:

```lean
example : (KMor1.rec1
    (h := (KMor1.zero : KMor1 0))
    (g := (KMor1.zero : KMor1 2))).level = 1 := by decide
```

- [ ] **Step 3: Build and verify clean**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereKSim.lean
git commit -m "Add KMor1.rec1 (non-simultaneous primrec wrapper)"
```

---

### Task 0.2: Add `KMor1.interp_rec1_zero`

**Spec:** §3.2.

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean` (insert after
  `KMor1.simrecVec_succ`, around line 209).

- [ ] **Step 1: Add the lemma**

Insert after the `KMor1.simrecVec_succ` `@[simp]` theorem:

```lean
/-- Base-case interp for `rec1`: at recursion variable `0`,
`rec1 h g` returns `h.interp params`. -/
@[simp] theorem KMor1.interp_rec1_zero {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons 0 params)
      = h.interp params := by
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  rfl
```

- [ ] **Step 2: Build and verify clean**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 3: Smoke-check via #guard**

Add at the end of the file, before `end GebLean`:

```lean
#guard (KMor1.rec1 (h := (KMor1.zero : KMor1 0))
    (g := (KMor1.proj ⟨0, by decide⟩ : KMor1 2))).interp
    ![0] = 0
```

- [ ] **Step 4: Build**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.interp_rec1_zero base-case simp lemma"
```

---

### Task 0.3: Add `KMor1.interp_rec1_succ`

**Spec:** §3.2.

This is the dite ↔ `Fin.append (Fin.cons …)` bridge proof (the spec
calls this out as the only non-trivial proof in Phase 0). Modeled on
`KMor1.simrecVec_eq_Nat_simRecVec` (already in the same file).

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean` (insert after
  `KMor1.interp_rec1_zero`).

- [ ] **Step 1: Add the lemma with proof**

Insert after `KMor1.interp_rec1_zero`:

```lean
/-- Step-case interp for `rec1`: at recursion variable `n + 1`,
`rec1 h g` returns `g.interp` applied to the context
`(n, params, prev)` where `prev = (rec1 h g).interp (Fin.cons n
params)`. -/
@[simp] theorem KMor1.interp_rec1_succ {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (n : ℕ) (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons (n + 1) params)
      = g.interp (Fin.append (Fin.cons n params)
          (fun _ : Fin 1 =>
            (KMor1.rec1 h g).interp (Fin.cons n params))) := by
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  show KMor1.simrecVec (fun _ => h) (fun _ => g)
        (fun j => Fin.cons (n + 1) params (Fin.succ j))
        (Fin.cons (n + 1) params 0) ⟨0, by decide⟩
      = g.interp _
  -- Both ctx 0 = n+1 and the params lookup reduce; pull n+1 out
  have h_ctx0 : Fin.cons (n + 1) params 0 = n + 1 := by
    simp [Fin.cons_zero]
  have h_params :
      (fun j => Fin.cons (n + 1) params (Fin.succ j)) = params := by
    funext j; simp [Fin.cons_succ]
  rw [h_ctx0, h_params]
  -- Now we have simrecVec ... (n+1) ⟨0, _⟩.  Unfold one step.
  simp only [KMor1.simrecVec_succ]
  -- Goal: g.interp (dite-form) = g.interp (Fin.append (Fin.cons n
  -- params) (fun _ => (rec1 h g).interp (Fin.cons n params)))
  congr 1
  funext idx
  rcases idx with ⟨v, h_v⟩
  by_cases h₁ : v < a + 1
  · -- v in 0..a: select from Fin.cons n params via Fin.append left
    have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + 1))
        = Fin.castAdd 1 (⟨v, h₁⟩ : Fin (a + 1)) := by
      apply Fin.ext; rfl
    rw [show Fin.append (Fin.cons n params) _ ⟨v, h_v⟩
          = Fin.append (Fin.cons n params) _
              (Fin.castAdd 1 (⟨v, h₁⟩ : Fin (a + 1)))
          from congrArg _ h_cast,
        Fin.append_left]
    simp only [h₁, dite_true]
    by_cases h₂ : v = 0
    · simp only [h₂, dite_true]; rfl
    · simp only [h₂, dite_false]
      have h_succ : (⟨v, h₁⟩ : Fin (a + 1))
          = Fin.succ (⟨v - 1, by omega⟩ : Fin a) := by
        apply Fin.ext; change v = (v - 1) + 1; omega
      rw [h_succ, Fin.cons_succ]
  · -- v in a+1: select from prev singleton via Fin.append right
    have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + 1))
        = Fin.natAdd (a + 1) ⟨v - (a + 1), by omega⟩ := by
      apply Fin.ext
      change v = (a + 1) + (v - (a + 1))
      omega
    rw [show Fin.append (Fin.cons n params) _ ⟨v, h_v⟩
          = Fin.append (Fin.cons n params) _
              (Fin.natAdd (a + 1) ⟨v - (a + 1), by omega⟩)
          from congrArg _ h_cast,
        Fin.append_right]
    simp only [h₁, dite_false]
    -- Both sides reduce to simrecVec ... n ⟨0, _⟩
    -- LHS: simrecVec ... n ⟨v - (a+1), _⟩, but v - (a+1) = 0 since
    -- v < a+1+1 and ¬ v < a+1 ⇒ v = a+1.
    have h_idx : (⟨v - (a + 1), by omega⟩ : Fin 1)
        = ⟨0, by decide⟩ := by
      apply Fin.ext; omega
    rw [h_idx]
    -- RHS: (rec1 h g).interp (Fin.cons n params).
    -- Unfold rec1 + interp_simrec to align.
    show _ = (KMor1.rec1 h g).interp (Fin.cons n params)
    unfold KMor1.rec1
    rw [KMor1.interp_simrec]
    show _ = KMor1.simrecVec (fun _ => h) (fun _ => g)
        (fun j => Fin.cons n params (Fin.succ j))
        (Fin.cons n params 0) ⟨0, by decide⟩
    have h_ctx0' : Fin.cons n params 0 = n := by
      simp [Fin.cons_zero]
    have h_params' :
        (fun j => Fin.cons n params (Fin.succ j)) = params := by
      funext j; simp [Fin.cons_succ]
    rw [h_ctx0', h_params']
```

- [ ] **Step 2: Build and verify clean**

Run: `lake build`
Expected: PASS, no warnings.

If the proof fails: replace problematic steps with `_` to inspect
the goal type, then iterate. Reference: the existing
`KMor1.simrecVec_eq_Nat_simRecVec` in the same file uses exactly
this dite-handling pattern. If `Fin.append_left`/`Fin.append_right`
mathlib lemma names have moved, search via `lean_loogle` for
`Fin.append (Fin.cons _ _) _ (Fin.castAdd _ _)`.

- [ ] **Step 3: Smoke-check via #guard**

Add at the end of the file, before `end GebLean`:

```lean
#guard (KMor1.rec1
    (h := (KMor1.zero : KMor1 0))
    (g := (KMor1.proj ⟨0, by decide⟩ : KMor1 2))).interp
    ![5] = 4
```

(This is essentially `pred 5 = 4`.)

- [ ] **Step 4: Build**

Run: `lake build`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.interp_rec1_succ step-case simp lemma"
```

---

## Phase 1: Level-1 functions

### Task 1.1: Create `Utilities/KArith.lean` skeleton

**Spec:** §2.

**Files:**

- Create: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Write the file**

```lean
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp

/-!
# K^sim-Derived Arithmetic

`KMor1`-level versions of basic arithmetic functions: `pred`,
`isZero`, `add`, `double`, `cond`, `notEq1`, `mult`, `monus`,
`pow2`, `mod`, `div`, `divNat`.  Each function carries an
`@[simp]`-marked correctness theorem linking its interpretation to
its `Nat` counterpart, plus a `level ≤ N` placement proof.

Every function is a closed-form `KMor1` term built from the
generators `zero`, `succ`, `proj`, `comp`, `simrec` (and the
non-simultaneous wrapper `rec1`); the `KMor1` inductive is not
extended.

Levels follow Tourlakis's classification (Notes Prop 10.2.12;
PR §0.1.0.17); `mod`, `div`, `divNat` are placed using
constructions in this module.

Sibling of `Utilities/ERArith.lean`; spec at
`docs/superpowers/specs/2026-05-05-karith-design.md`.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Build to verify imports resolve**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Create Utilities/KArith.lean skeleton"
```

---

### Task 1.2: Add `KMor1.one`

**Spec:** §4.2 (helper for `isZero`, `pow2`).

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add the def**

Inside `namespace GebLean`, before `end GebLean`:

```lean
/-- The constant `1` morphism at arity 0.

PR §0.1.0.17 implicit (constants and `succ` generate K^sim_0). -/
def KMor1.one : KMor1 0 :=
  KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.zero)

/-- Interpretation of `one`: always returns `1`. -/
@[simp] theorem KMor1.interp_one (ctx : Fin 0 → ℕ) :
    KMor1.one.interp ctx = 1 := rfl
```

- [ ] **Step 2: Add level smoke-check**

```lean
example : KMor1.one.level = 0 := by decide
```

- [ ] **Step 3: Build**

Run: `lake build`
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.one (constant 1 at arity 0)"
```

---

### Task 1.3: Add `KMor1.pred`

**Spec:** §4.1.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add the def**

After `KMor1.interp_one`:

```lean
/-- Predecessor function as a `KMor1 1` term:
`pred(0) = 0`, `pred(x+1) = x`.

Tourlakis PR §0.1.0.17(4) (`λx.x ∸ 1 ∈ K_1`); Notes 10.2.12 row 2. -/
def KMor1.pred : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.proj ⟨0, by decide⟩)
```

- [ ] **Step 2: Add interp simp lemma**

```lean
/-- Interpretation of `pred`: `Nat.pred`. -/
@[simp] theorem KMor1.interp_pred (ctx : Fin 1 → ℕ) :
    KMor1.pred.interp ctx = (ctx 0).pred := by
  unfold KMor1.pred
  -- Case on ctx 0 = 0 or n + 1 by reducing through Fin.cons-shape
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i; fin_cases i; rfl
  rw [hctx]
  cases h : ctx 0 with
  | zero => simp [KMor1.interp_rec1_zero]
  | succ n =>
    simp [KMor1.interp_rec1_succ]
    rfl
```

If the `simp` calls fail: drop to step-by-step
`rw [KMor1.interp_rec1_zero]` / `rw [KMor1.interp_rec1_succ]` and
finish with `rfl`. The interp of `proj ⟨0, _⟩` against the Fin.append
context is `Fin.append (Fin.cons n Fin.elim0) (fun _ => 0) ⟨0, _⟩
= n` by `Fin.append_left` + `Fin.cons_zero`.

- [ ] **Step 3: Add level proof and #guards**

```lean
example : KMor1.pred.level = 1 := by decide

#guard KMor1.pred.interp ![0] = 0
#guard KMor1.pred.interp ![1] = 0
#guard KMor1.pred.interp ![5] = 4
```

- [ ] **Step 4: Build**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.pred (predecessor at K^sim_1)"
```

---

### Task 1.4: Add `KMor1.isZero`

**Spec:** §4.2.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def**

```lean
/-- Zero indicator: `isZero(0) = 1`, `isZero(x+1) = 0`.
Equivalently `1 ∸ x`.

Tourlakis PR §0.1.0.17(3) (`λx.1 ∸ x ∈ K_1`). -/
def KMor1.isZero : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.one)
    (g := KMor1.zero)
```

- [ ] **Step 2: Add interp simp lemma**

```lean
/-- Interpretation of `isZero`: 1 if input is 0, else 0. -/
@[simp] theorem KMor1.interp_isZero (ctx : Fin 1 → ℕ) :
    KMor1.isZero.interp ctx = if ctx 0 = 0 then 1 else 0 := by
  unfold KMor1.isZero
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i; fin_cases i; rfl
  rw [hctx]
  cases h : ctx 0 with
  | zero => simp [KMor1.interp_rec1_zero]
  | succ n => simp [KMor1.interp_rec1_succ]
```

- [ ] **Step 3: Add level proof and #guards**

```lean
example : KMor1.isZero.level = 1 := by decide

#guard KMor1.isZero.interp ![0] = 1
#guard KMor1.isZero.interp ![1] = 0
#guard KMor1.isZero.interp ![10] = 0
```

- [ ] **Step 4: Build and commit**

Run: `lake build`. Expected: PASS.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.isZero (zero indicator at K^sim_1)"
```

---

### Task 1.5: Add `KMor1.add`

**Spec:** §4.3.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def**

```lean
/-- Addition: `add(0, y) = y`, `add(x+1, y) = succ(add(x, y))`.

Tourlakis PR §0.1.0.17(1); Notes 10.2.12 row 1. -/
def KMor1.add : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    (g := KMor1.comp KMor1.succ
            (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
```

- [ ] **Step 2: Add interp simp lemma**

```lean
/-- Interpretation of `add`: `ctx 0 + ctx 1`. -/
@[simp] theorem KMor1.interp_add (ctx : Fin 2 → ℕ) :
    KMor1.add.interp ctx = ctx 0 + ctx 1 := by
  unfold KMor1.add
  -- Decompose ctx as Fin.cons (ctx 0) (fun j => ctx (Fin.succ j))
  have hctx : ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j; simp [Fin.cons_succ]
  rw [hctx]
  -- Induction on ctx 0
  generalize hp : (fun j => ctx (Fin.succ j)) = params
  induction (ctx 0) with
  | zero =>
    simp [KMor1.interp_rec1_zero]
    -- proj 0 of single-param Fin 1 → ℕ context is params 0 = ctx 1
    rfl
  | succ n ih =>
    simp [KMor1.interp_rec1_succ]
    rw [show Fin.append (Fin.cons n params)
          (fun _ : Fin 1 => (KMor1.rec1 _ _).interp _)
          ⟨2, by decide⟩
        = (KMor1.rec1
            (h := (KMor1.proj ⟨0, by decide⟩ : KMor1 1))
            (g := KMor1.comp KMor1.succ
              (fun _ : Fin 1 =>
                KMor1.proj ⟨2, by decide⟩))).interp
            (Fin.cons n params) by
      simp [Fin.append_right]; rfl]
    -- now LHS = succ (rec1 ... interp (Fin.cons n params))
    -- and we want = n + 1 + ctx 1 = (n + ctx 1) + 1
    -- IH: rec1 interp (Fin.cons n params) = n + ctx 1, so we're done
    omega_or_rfl_via_ih
```

The exact final step depends on what `simp` leaves. If `simp` gets
stuck, drop to manual step-by-step `rw`s:

```lean
    rw [KMor1.interp_succ]
    -- Goal: (rec1 _ _).interp (Fin.cons n params) + 1 = ...
    -- Need: ctx becomes Fin.cons n params on RHS too
    have : Fin.cons (n + 1) params = ctx := hctx.symm  -- from earlier
    -- IH applied: rewrite back to ctx then back to (n, params)
    sorry  -- placeholder; remove and finish
```

If the proof gets long, factor out a helper lemma stating
`(KMor1.add).interp (Fin.cons n params) = n + params 0` and prove
it by induction on `n`; then derive the main lemma by setting
`n := ctx 0` and `params := fun j => ctx (Fin.succ j)`.

- [ ] **Step 3: Add level proof and #guards**

```lean
example : KMor1.add.level = 1 := by decide

#guard KMor1.add.interp ![0, 7] = 7
#guard KMor1.add.interp ![3, 4] = 7
#guard KMor1.add.interp ![5, 0] = 5
```

- [ ] **Step 4: Build and commit**

Run: `lake build`. Expected: PASS.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.add (addition at K^sim_1)"
```

---

### Task 1.6: Add `KMor1.double`

**Spec:** §4.4.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, and #guards**

```lean
/-- Doubling: `double(0) = 0`, `double(x+1) = succ(succ(double(x)))`.

Derived at K^sim_1; used as the level-1 step in `pow2`. -/
def KMor1.double : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.comp KMor1.succ
            (fun _ : Fin 1 =>
              KMor1.comp KMor1.succ
                (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)))

/-- Interpretation of `double`: `2 * ctx 0`. -/
@[simp] theorem KMor1.interp_double (ctx : Fin 1 → ℕ) :
    KMor1.double.interp ctx = 2 * ctx 0 := by
  unfold KMor1.double
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i; fin_cases i; rfl
  rw [hctx]
  generalize hp : (Fin.elim0 : Fin 0 → ℕ) = params
  induction (ctx 0) with
  | zero => simp [KMor1.interp_rec1_zero]
  | succ n ih =>
    simp [KMor1.interp_rec1_succ, Fin.append_right]
    omega

example : KMor1.double.level = 1 := by decide

#guard KMor1.double.interp ![0] = 0
#guard KMor1.double.interp ![5] = 10
```

If `simp` doesn't close the `succ` case, do it manually:

```lean
  | succ n ih =>
    rw [KMor1.interp_rec1_succ]
    rw [KMor1.interp_comp, KMor1.interp_succ]
    rw [KMor1.interp_comp, KMor1.interp_succ]
    rw [KMor1.interp_proj]
    -- Goal: succ (succ (Fin.append … ⟨1, _⟩)) = 2 * (n + 1)
    -- The `proj 1` inside is fetching from the single-element prev
    -- vector via Fin.append_right; reduce that via `Fin.append_right`.
    rw [show (Fin.append (Fin.cons n params)
              (fun _ : Fin 1 => (KMor1.rec1 _ _).interp _) : _ → ℕ)
            ⟨1, by decide⟩
        = (KMor1.rec1
            (h := (KMor1.zero : KMor1 0))
            (g := KMor1.comp KMor1.succ (fun _ =>
              KMor1.comp KMor1.succ (fun _ =>
                KMor1.proj ⟨1, by decide⟩)))).interp
            (Fin.cons n params)
        from by simp [Fin.append_right]]
    -- Now the term is `succ (succ (rec1 … interp (cons n params)))`
    -- Apply IH (rewriting in reverse to match shape)
    omega  -- or finish via rfl + ih
```

- [ ] **Step 2: Build and commit**

Run: `lake build`. Expected: PASS.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.double at K^sim_1"
```

---

### Task 1.7: Add `KMor1.cond`

**Spec:** §4.5.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, #guards**

```lean
/-- Conditional / switch: `cond(0, y, z) = y`, `cond(x+1, y, z) = z`.

Tourlakis PR §0.1.0.17(6) (`switch`). -/
def KMor1.cond : KMor1 3 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    (g := KMor1.proj ⟨2, by decide⟩)

/-- Interpretation of `cond`: `if ctx 0 = 0 then ctx 1 else ctx 2`. -/
@[simp] theorem KMor1.interp_cond (ctx : Fin 3 → ℕ) :
    KMor1.cond.interp ctx
      = if ctx 0 = 0 then ctx 1 else ctx 2 := by
  unfold KMor1.cond
  have hctx :
      ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i; refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j; simp [Fin.cons_succ]
  rw [hctx]
  cases h : ctx 0 with
  | zero =>
    simp [KMor1.interp_rec1_zero]
    rfl
  | succ n =>
    simp [KMor1.interp_rec1_succ, Fin.append_left]
    rfl

example : KMor1.cond.level = 1 := by decide

#guard KMor1.cond.interp ![0, 11, 22] = 11
#guard KMor1.cond.interp ![1, 11, 22] = 22
#guard KMor1.cond.interp ![2, 11, 22] = 22
```

If `Fin.append_left` simp doesn't trigger, replace with explicit
`show … = … from by simp [Fin.append_left]`.

- [ ] **Step 2: Build and commit**

Run: `lake build`. Expected: PASS.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.cond (switch at K^sim_1)"
```

---

### Task 1.8: Add `KMor1.notEq1`

**Spec:** §4.6.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, #guards**

```lean
/-- Characteristic of the predicate `x ≠ 1` (Tourlakis
predicate-as-zero convention): `notEq1(x) = 0` when `x ≠ 1` holds,
`notEq1(x) = 1` when `x = 1`.

Construction: `isZero(pred(x) + isZero(x))`. The inner sum vanishes
exactly at `x = 1` (since `pred(1) = 0` and `isZero(1) = 0`).

Tourlakis PR §0.1.0.20 (`λx.x = a ∈ K_{1,*}`) plus Notes 10.2.14
(Boolean closure of K_{n,*}). The name refers to the predicate
being characterized; per Tourlakis convention, the value is 0 when
the predicate holds. -/
def KMor1.notEq1 : KMor1 1 :=
  KMor1.comp KMor1.isZero (fun _ : Fin 1 =>
    KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.pred
      | ⟨1, _⟩ => KMor1.isZero))

/-- Interpretation of `notEq1`: `1` if `ctx 0 = 1`, else `0`. -/
@[simp] theorem KMor1.interp_notEq1 (ctx : Fin 1 → ℕ) :
    KMor1.notEq1.interp ctx = if ctx 0 = 1 then 1 else 0 := by
  unfold KMor1.notEq1
  rw [KMor1.interp_comp, KMor1.interp_isZero,
      KMor1.interp_comp, KMor1.interp_add,
      KMor1.interp_pred, KMor1.interp_isZero]
  -- Goal: (if pred(ctx 0) + isZero(ctx 0) = 0 then 1 else 0) = ...
  -- Reduce by cases on ctx 0
  rcases h : ctx 0 with _ | _ | n
  · simp
  · simp
  · simp [Nat.pred]
    omega

example : KMor1.notEq1.level = 1 := by decide

#guard KMor1.notEq1.interp ![0] = 0
#guard KMor1.notEq1.interp ![1] = 1
#guard KMor1.notEq1.interp ![2] = 0
#guard KMor1.notEq1.interp ![5] = 0
```

If the `interp_isZero` rewrite under the outer `comp` produces a
term that doesn't match because the inner is a function `Fin 1 →
ℕ`: insert `simp only [KMor1.interp_comp]` first, then the
component rewrites as `simp only [...]`.

- [ ] **Step 2: Build and commit**

Run: `lake build`. Expected: PASS.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.notEq1 (Tourlakis χ(x ≠ 1) at K^sim_1)"
```

---

## Phase 2: Level-2 functions (mult, monus, pow2)

### Task 2.1: Add `KMor1.mult`

**Spec:** §4.7.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, #guards**

```lean
/-- Multiplication: `mult(0, y) = 0`, `mult(x+1, y) = y + mult(x, y)`.

Tourlakis PR §0.1.0.17(b); Notes 10.2.12 row 4. -/
def KMor1.mult : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
      | ⟨1, _⟩ => KMor1.proj ⟨2, by decide⟩))

/-- Interpretation of `mult`: `ctx 0 * ctx 1`. -/
@[simp] theorem KMor1.interp_mult (ctx : Fin 2 → ℕ) :
    KMor1.mult.interp ctx = ctx 0 * ctx 1 := by
  unfold KMor1.mult
  have hctx : ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j; simp [Fin.cons_succ]
  rw [hctx]
  generalize hp : (fun j => ctx (Fin.succ j)) = params
  induction (ctx 0) with
  | zero => simp [KMor1.interp_rec1_zero]
  | succ n ih =>
    simp [KMor1.interp_rec1_succ, KMor1.interp_comp,
          KMor1.interp_add, KMor1.interp_proj, Fin.append_left,
          Fin.append_right]
    rw [ih]
    ring

example : KMor1.mult.level = 2 := by decide

#guard KMor1.mult.interp ![0, 7] = 0
#guard KMor1.mult.interp ![3, 4] = 12
#guard KMor1.mult.interp ![1, 5] = 5
```

- [ ] **Step 2: Build and commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.mult (multiplication at K^sim_2)"
```

---

### Task 2.2: Add `KMor1.monusSwapped` (private helper)

**Spec:** §4.8 (helper for `monus`).

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, private interp lemma, level proof**

```lean
/-- Helper: monus with arguments swapped, recursing on slot 0.
`monusSwapped(y, x) = x ∸ y`.  K^sim's recursion always recurses on
slot 0; this helper makes that explicit, with `KMor1.monus` below
swapping the arg order to recover the conventional `λxy. x ∸ y`. -/
private def KMor1.monusSwapped : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    (g := KMor1.comp KMor1.pred
            (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))

@[simp] private theorem KMor1.interp_monusSwapped
    (ctx : Fin 2 → ℕ) :
    KMor1.monusSwapped.interp ctx = ctx 1 - ctx 0 := by
  unfold KMor1.monusSwapped
  have hctx : ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero]
    · intro j; simp [Fin.cons_succ]
  rw [hctx]
  generalize hp : (fun j => ctx (Fin.succ j)) = params
  induction (ctx 0) with
  | zero =>
    simp [KMor1.interp_rec1_zero]
    rfl
  | succ n ih =>
    simp [KMor1.interp_rec1_succ, KMor1.interp_comp,
          KMor1.interp_pred, Fin.append_right]
    rw [ih]
    omega

example : KMor1.monusSwapped.level = 2 := by decide
```

- [ ] **Step 2: Build and commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.monusSwapped (private helper for monus)"
```

---

### Task 2.3: Add `KMor1.monus`

**Spec:** §4.8.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, #guards**

```lean
/-- Truncated subtraction: `monus(x, y) = x ∸ y`.

Tourlakis PR §0.1.0.17(a); Notes 10.2.12 row 6. -/
def KMor1.monus : KMor1 2 :=
  KMor1.comp KMor1.monusSwapped (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)

/-- Interpretation of `monus`: `ctx 0 - ctx 1` (truncated). -/
@[simp] theorem KMor1.interp_monus (ctx : Fin 2 → ℕ) :
    KMor1.monus.interp ctx = ctx 0 - ctx 1 := by
  unfold KMor1.monus
  rw [KMor1.interp_comp, KMor1.interp_monusSwapped]
  rfl

example : KMor1.monus.level = 2 := by decide

#guard KMor1.monus.interp ![5, 3] = 2
#guard KMor1.monus.interp ![3, 5] = 0
#guard KMor1.monus.interp ![5, 5] = 0
```

- [ ] **Step 2: Build and commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.monus (truncated subtraction at K^sim_2)"
```

---

### Task 2.4: Add `KMor1.pow2`

**Spec:** §4.9.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, #guards**

```lean
/-- Powers of two: `pow2(0) = 1`, `pow2(x+1) = double(pow2(x))`.

Tourlakis PR §0.1.0.17(c); Notes 10.2.12 row 5. -/
def KMor1.pow2 : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.one)
    (g := KMor1.comp KMor1.double
            (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩))

/-- Interpretation of `pow2`: `2 ^ ctx 0`. -/
@[simp] theorem KMor1.interp_pow2 (ctx : Fin 1 → ℕ) :
    KMor1.pow2.interp ctx = 2 ^ ctx 0 := by
  unfold KMor1.pow2
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i; fin_cases i; rfl
  rw [hctx]
  generalize hp : (Fin.elim0 : Fin 0 → ℕ) = params
  induction (ctx 0) with
  | zero => simp [KMor1.interp_rec1_zero]
  | succ n ih =>
    simp [KMor1.interp_rec1_succ, KMor1.interp_comp,
          KMor1.interp_double, Fin.append_right]
    rw [ih]
    ring

example : KMor1.pow2.level = 2 := by decide

#guard KMor1.pow2.interp ![0] = 1
#guard KMor1.pow2.interp ![1] = 2
#guard KMor1.pow2.interp ![4] = 16
```

- [ ] **Step 2: Build and commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.pow2 (2^x at K^sim_2)"
```

---

## Phase 3: `mod`

### Task 3.1: Add `KMor1.modAux` definition

**Spec:** §4.10.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add the system-size-2 simrec**

```lean
/-- Helper: joint recursion of `mod` and a "distance to wrap"
companion. Output index 0 of the `simrec` (the `mod` component);
the second component `(y ∸ 1) ∸ mod(x, y)` is internal and used to
make the wrap test expressible at level 1 via `cond`.

Tourlakis Notes 4.2.3 generalized: Tourlakis treats only `rem(x, 2)`
via a 2-row companion-shift; here we extend the companion to track
"distance to wrap" for arbitrary divisor `y`. The placement
`mod ∈ K^sim_2` follows from Marchenkov 2007 (basis closure).

At `y = 0`: `f₁` stays at `0` forever (since `pred(0) = 0`), so
`f₀(x, 0) = 0` for all `x`. The outer `KMor1.mod` (next task) wraps
this case to match `Nat.mod_zero : x % 0 = x`. -/
private def KMor1.modAux : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 1) (i := ⟨0, by decide⟩)
    (h := fun i => match i with
      | ⟨0, _⟩ => KMor1.zero       -- f₀(0, y) = 0
      | ⟨1, _⟩ => KMor1.pred)      -- f₁(0, y) = pred(y)
    (g := fun i =>
      -- step ctx is Fin (1 + 1 + 2) = Fin 4:
      -- slots 0 = x, 1 = y, 2 = prev_f₀, 3 = prev_f₁
      match i with
      | ⟨0, _⟩ =>
          -- f₀ step: cond(prev_f₁, 0, succ(prev_f₀))
          KMor1.comp KMor1.cond (fun j => match j with
            | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
            | ⟨1, _⟩ => KMor1.zero
            | ⟨2, _⟩ => KMor1.comp KMor1.succ
                          (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
      | ⟨1, _⟩ =>
          -- f₁ step: cond(prev_f₁, pred(y), pred(prev_f₁))
          KMor1.comp KMor1.cond (fun j => match j with
            | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
            | ⟨1, _⟩ => KMor1.comp KMor1.pred
                          (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)
            | ⟨2, _⟩ => KMor1.comp KMor1.pred
                          (fun _ : Fin 1 => KMor1.proj ⟨3, by decide⟩)))

example : KMor1.modAux.level = 2 := by decide
```

- [ ] **Step 2: Build and commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.modAux (system-size-2 mod helper)"
```

---

### Task 3.2: Prove `modAux_components`

**Spec:** §4.10.1 — the helper lemma stating the joint vector value
at any `(x, y)`.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: State and prove the helper**

```lean
/-- The joint two-component vector returned by `modAux`'s simrec at
recursion variable `x` with parameter `y`, for `y ≥ 1`:

  `simrecVec h g params x = ![x % y, (y - 1) - x % y]`.

For `y = 0`, both components are `0` (because `pred(0) = 0`
collapses the wrap-detection logic). -/
private theorem KMor1.modAux_components
    (x : ℕ) (y : ℕ) :
    KMor1.simrecVec
      (fun i => match i with
        | ⟨0, _⟩ => KMor1.zero
        | ⟨1, _⟩ => KMor1.pred : Fin 2 → KMor1 1)
      (fun i => match i with
        | ⟨0, _⟩ =>
            KMor1.comp KMor1.cond (fun j => match j with
              | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
              | ⟨1, _⟩ => KMor1.zero
              | ⟨2, _⟩ => KMor1.comp KMor1.succ
                            (fun _ : Fin 1 =>
                              KMor1.proj ⟨2, by decide⟩))
        | ⟨1, _⟩ =>
            KMor1.comp KMor1.cond (fun j => match j with
              | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
              | ⟨1, _⟩ => KMor1.comp KMor1.pred
                            (fun _ : Fin 1 =>
                              KMor1.proj ⟨1, by decide⟩)
              | ⟨2, _⟩ => KMor1.comp KMor1.pred
                            (fun _ : Fin 1 =>
                              KMor1.proj ⟨3, by decide⟩))
        : Fin 2 → KMor1 (1 + 1 + 2))
      (fun _ : Fin 1 => y)
      x
    = if y = 0 then ![0, 0]
      else ![x % y, (y - 1) - x % y] := by
  induction x with
  | zero =>
    funext j
    fin_cases j
    · simp [KMor1.simrecVec, KMor1.interp]
      split_ifs <;> simp
    · simp [KMor1.simrecVec, KMor1.interp_pred]
      split_ifs with hy
      · simp [hy]
      · rfl
  | succ x ih =>
    funext j
    fin_cases j
    · -- f₀ component
      sorry  -- will fill in step 2
    · -- f₁ component
      sorry  -- will fill in step 2
```

If the type-elaboration of `simrecVec`'s arguments above causes issues
(big match-expressions in implicit positions), refactor to extract
the base and step families as `private def` values:

```lean
private def KMor1.modAux_h : Fin 2 → KMor1 1 :=
  fun i => match i with
    | ⟨0, _⟩ => KMor1.zero
    | ⟨1, _⟩ => KMor1.pred

private def KMor1.modAux_g : Fin 2 → KMor1 (1 + 1 + 2) :=
  fun i => ... -- same as in modAux

private def KMor1.modAux' : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 1) (i := ⟨0, by decide⟩)
    KMor1.modAux_h KMor1.modAux_g

-- Then re-derive modAux as a defeq alias:
example : KMor1.modAux = KMor1.modAux' := rfl
```

This refactor makes `modAux_components` cleaner to state.

- [ ] **Step 2: Fill in succ case proof**

The succ-case proof requires:

- Unfold `KMor1.simrecVec` at `succ x`.
- Apply IH (which has the form `simrecVec ... x = if y = 0 then …
  else …`).
- Compute the cond-based step. Case-split on `y = 0` vs `y ≥ 1`.
- For `y = 0`: f₁ stays at 0, cond picks branch1 everywhere.
- For `y ≥ 1`: case-split on `(y - 1) - x % y = 0` (i.e. `x % y =
  y - 1`, the wrap) vs `> 0`:
  - Wrap case: cond picks branch1; need `(x + 1) % y = 0`. Mathlib:
    `Nat.add_mod_right` or derive via `Nat.succ_mod_self` /
    `Nat.mod_eq_zero_of_dvd`.
  - No-wrap case: cond picks branch2; need `(x + 1) % y = (x % y) +
    1`. Mathlib: `Nat.add_mod` plus `Nat.mod_eq_of_lt` for the
    condition `(x % y) + 1 < y`.

Concrete proof skeleton (replacing the two `sorry`s):

```lean
    · -- f₀ component succ x
      simp only [KMor1.simrecVec_succ]
      -- Reduce the dite-form context for the step's KMor1.cond
      simp only [KMor1.interp_comp, KMor1.interp_cond,
                 KMor1.interp_proj, KMor1.interp_zero,
                 KMor1.interp_succ]
      -- Use IH at component 1 (the f₁ part) for the cond switch
      have ih_f1 := congrFun ih ⟨1, by decide⟩
      -- Case-split on y
      by_cases hy : y = 0
      · subst hy
        simp at ih_f1 ⊢
        -- f₁ at y=0 is 0, so cond picks branch1 = 0
        sorry
      · push_neg at hy
        have hy_pos : 0 < y := Nat.pos_of_ne_zero hy
        simp [hy] at ih_f1 ⊢
        -- f₁ = (y - 1) - x % y; case-split on wrap
        by_cases hw : x % y = y - 1
        · -- Wrap: f₁_prev = 0, branch1 selected, result = 0
          simp [hw]
          -- (x + 1) % y = 0
          rw [show x + 1 = x - x % y + y by omega]
          -- ... simp Nat.add_mod_right etc.
          sorry
        · push_neg at hw
          -- No wrap: f₁_prev > 0, branch2 selected, result = (x % y) + 1
          have hw' : x % y < y - 1 := by
            have := Nat.mod_lt x hy_pos
            omega
          have hf1 : (y - 1) - x % y > 0 := by omega
          simp [Nat.sub_eq_zero_iff_le.not.mpr (by omega : ¬ y - 1 ≤ x % y)]
          -- f₀ = succ (x % y) = x % y + 1
          -- (x + 1) % y = (x % y) + 1 since (x % y) + 1 < y
          rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (x % y) + 1 < y)]
    · -- f₁ component succ x: similar structure
      sorry  -- analogous proof
```

The proof is mechanical but involves several `omega` discharges and
mathlib `Nat.mod_*` lemma applications. If the implementer gets
stuck on a sub-step, factor it out into a helper:

```lean
private lemma KMor1.modAux_wrap_aux (x y : ℕ) (hy : 0 < y)
    (hw : x % y = y - 1) :
    (x + 1) % y = 0 := by
  rw [Nat.add_mod, hw]
  have : (y - 1) + 1 = y := by omega
  rw [this, Nat.mod_self]
  rfl
```

and similarly for the no-wrap case.

- [ ] **Step 3: Build and verify clean**

Run: `lake build`. Expected: PASS, no warnings, no `sorry` (replace
all sorries before building).

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Prove KMor1.modAux_components (joint-vector value)"
```

---

### Task 3.3: Add `KMor1.mod` definition

**Spec:** §4.10.1.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def**

```lean
/-- Remainder: `mod(x, y) = x % y` matching Lean's `Nat.mod`,
including `x % 0 = x` (`Nat.mod_zero`).

Construction: `cond(y, x, modAux(x, y))`.  At `y = 0` returns `x`;
at `y > 0` defers to `modAux`, which computes `x % y` via the
companion-tracked simrec.

Marchenkov 2007 (basis member, derived from `x ∸ y · (x/y)` over
the basis `{x+y, x∸y, x/y, 2^x}`); inspired by Tourlakis Notes
4.2.3's `rem(x, 2)` companion-shift technique. The convention
`rm(x, 0) = x` matches Marchenkov §1 and Lean's `Nat.mod_zero`. -/
def KMor1.mod : KMor1 2 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩       -- switch on y
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩       -- if y = 0, return x
    | ⟨2, _⟩ => KMor1.modAux)                  -- else, modAux(x, y)

example : KMor1.mod.level = 2 := by decide
```

- [ ] **Step 2: Build and commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.mod definition"
```

---

### Task 3.4: Prove `KMor1.interp_mod`

**Spec:** §4.10.1.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add the simp theorem**

```lean
/-- Interpretation of `mod`: `ctx 0 % ctx 1` (matches `Nat.mod`). -/
@[simp] theorem KMor1.interp_mod (ctx : Fin 2 → ℕ) :
    KMor1.mod.interp ctx = ctx 0 % ctx 1 := by
  unfold KMor1.mod
  rw [KMor1.interp_comp, KMor1.interp_cond, KMor1.interp_proj,
      KMor1.interp_proj]
  by_cases hy : ctx 1 = 0
  · simp [hy, Nat.mod_zero]
  · -- ctx 1 > 0: cond picks branch2 = modAux.interp ctx
    have hy_pos : 0 < ctx 1 := Nat.pos_of_ne_zero hy
    simp [hy]
    -- Reduce KMor1.modAux to component 0 of modAux_components at ctx 1
    unfold KMor1.modAux
    rw [KMor1.interp_simrec]
    -- Goal: simrecVec h g params (ctx 0) ⟨0, _⟩ = ctx 0 % ctx 1
    have hp : (fun j : Fin 1 => ctx (Fin.succ j)) = fun _ => ctx 1 := by
      funext j; fin_cases j; rfl
    rw [hp]
    have hc0 : ctx 0 = ctx 0 := rfl  -- placeholder
    have hcomp := KMor1.modAux_components (ctx 0) (ctx 1)
    -- modAux_components is stated for a literal h/g; with the same
    -- inline match shapes here, this should unify by rfl. If not,
    -- factor h and g into private defs in Task 3.1 refactor.
    have := congrFun hcomp ⟨0, by decide⟩
    simp [hy] at this
    convert this using 2
    -- ctx 0 from KMor1.simrec interp matches recvar position
    rfl
```

If the proof gets stuck on unification between `modAux`'s inline
match and `modAux_components`'s inline match: refactor as suggested
in Task 3.2 (extract `modAux_h`, `modAux_g` as `private def`), and
update both `modAux` and `modAux_components` to use them.

- [ ] **Step 2: Add #guards**

```lean
#guard KMor1.mod.interp ![0, 5] = 0
#guard KMor1.mod.interp ![5, 1] = 0
#guard KMor1.mod.interp ![5, 5] = 0
#guard KMor1.mod.interp ![6, 3] = 0
#guard KMor1.mod.interp ![7, 3] = 1
#guard KMor1.mod.interp ![3, 0] = 3
```

- [ ] **Step 3: Build and commit**

Run: `lake build`. Expected: PASS, no warnings.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Prove KMor1.interp_mod and add tests"
```

---

## Phase 4: `div` and `divNat`

### Task 4.1: Add `KMor1.divAux` definition

**Spec:** §4.11.

Same recursion structure as `modAux` but extended to system size 3,
output index 2.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add the system-size-3 simrec**

```lean
/-- Helper: joint recursion of `mod`, "distance to wrap", and `div`.
Output index 2 of the `simrec` (the `div` component).

The first two components mirror `modAux`; the third tracks the
running quotient, incrementing exactly at wrap points (when
`prev_f₁ = 0`, i.e. `x % y = y - 1`).

At `y = 0`: `f₁` stays at `0` forever, so the cond switch always
selects `branch1 = succ(prev_f₂)`; hence `f₂(x, 0) = x`, matching
Marchenkov §1's convention `x/0 = x`.

Marchenkov 2007 (the function `x/y` is one of the four basis
elements `S = {x+y, x∸y, x/y, 2^x}`); the construction technique
extends Notes 4.2.3's two-row companion-shift to a three-row
shift-plus-counter. -/
private def KMor1.divAux : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 2) (i := ⟨2, by decide⟩)
    (h := fun i => match i with
      | ⟨0, _⟩ => KMor1.zero
      | ⟨1, _⟩ => KMor1.pred
      | ⟨2, _⟩ => KMor1.zero)
    (g := fun i => match i with
      | ⟨0, _⟩ =>
          -- f₀ step: cond(prev_f₁, 0, succ(prev_f₀))
          KMor1.comp KMor1.cond (fun j => match j with
            | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
            | ⟨1, _⟩ => KMor1.zero
            | ⟨2, _⟩ => KMor1.comp KMor1.succ
                          (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
      | ⟨1, _⟩ =>
          -- f₁ step: cond(prev_f₁, pred(y), pred(prev_f₁))
          KMor1.comp KMor1.cond (fun j => match j with
            | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
            | ⟨1, _⟩ => KMor1.comp KMor1.pred
                          (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)
            | ⟨2, _⟩ => KMor1.comp KMor1.pred
                          (fun _ : Fin 1 => KMor1.proj ⟨3, by decide⟩))
      | ⟨2, _⟩ =>
          -- f₂ step: cond(prev_f₁, succ(prev_f₂), prev_f₂)
          KMor1.comp KMor1.cond (fun j => match j with
            | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
            | ⟨1, _⟩ => KMor1.comp KMor1.succ
                          (fun _ : Fin 1 => KMor1.proj ⟨4, by decide⟩)
            | ⟨2, _⟩ => KMor1.proj ⟨4, by decide⟩))

example : KMor1.divAux.level = 2 := by decide
```

- [ ] **Step 2: Build and commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.divAux (system-size-3 mod+div helper)"
```

---

### Task 4.2: Prove `divAux_components`

**Spec:** §4.11.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: State and prove the helper**

State: for all `x, y : ℕ`, the joint vector returned by `divAux`'s
simrec at recursion variable `x` with parameter `y` equals:

- `![x % y, (y - 1) - x % y, x / y]` if `y ≥ 1`,
- `![0, 0, x]` if `y = 0`.

The proof structure mirrors `modAux_components` but adds the third
component. Concretely:

```lean
private theorem KMor1.divAux_components
    (x : ℕ) (y : ℕ) :
    -- (use the same h/g shape as in divAux above, or factor into
    -- private defs in Task 4.1 if state-elaboration is awkward)
    KMor1.simrecVec ... (fun _ : Fin 1 => y) x
      = if y = 0 then ![0, 0, x]
        else ![x % y, (y - 1) - x % y, x / y] := by
  induction x with
  | zero =>
    funext j
    fin_cases j <;> simp [KMor1.simrecVec, ...]
  | succ x ih =>
    funext j
    fin_cases j
    · -- f₀ component (mirrors modAux_components proof)
      sorry
    · -- f₁ component (mirrors modAux_components proof)
      sorry
    · -- f₂ component: new
      simp only [KMor1.simrecVec_succ]
      simp only [KMor1.interp_comp, KMor1.interp_cond,
                 KMor1.interp_proj, KMor1.interp_succ]
      have ih_f1 := congrFun ih ⟨1, by decide⟩
      by_cases hy : y = 0
      · subst hy
        simp at ih_f1 ⊢
        -- f₁ = 0, so cond picks branch1 = succ(prev_f₂)
        -- prev_f₂ at y=0 is x (by IH); result = x + 1
        have ih_f2 := congrFun ih ⟨2, by decide⟩
        simp at ih_f2
        omega
      · push_neg at hy
        have hy_pos : 0 < y := Nat.pos_of_ne_zero hy
        simp [hy] at ih_f1 ⊢
        by_cases hw : x % y = y - 1
        · -- Wrap: f₁_prev = 0, branch1 = succ(prev_f₂) = x/y + 1
          have ih_f2 := congrFun ih ⟨2, by decide⟩
          simp [hy] at ih_f2
          simp [hw]
          -- (x + 1) / y = x / y + 1 when x % y = y - 1
          have : (x + 1) / y = x / y + 1 := by
            -- mathlib: x % y = y - 1 ⇒ y ∣ (x + 1)
            have hdvd : y ∣ (x + 1) := by
              have := Nat.mod_add_div x y
              rw [hw] at this
              -- this : (y - 1) + y * (x / y) = x
              -- so (x + 1) = y + y * (x / y) = y * (x / y + 1)
              have : x + 1 = y * (x / y + 1) := by ring_nf; omega
              exact ⟨x / y + 1, this⟩
            -- x + 1 = y * (x/y + 1), and y > 0 ⇒ (x+1)/y = x/y + 1
            obtain ⟨k, hk⟩ := hdvd
            rw [hk, Nat.mul_div_cancel_left _ hy_pos]
            -- need k = x/y + 1
            have : y * k = x + 1 := hk.symm
            have : x + 1 = y * (x / y + 1) := by
              have := Nat.mod_add_div x y
              omega
            -- combining: k = x/y + 1
            have : y * k = y * (x / y + 1) := by linarith
            exact (Nat.mul_left_cancel hy_pos this).symm
          omega
        · push_neg at hw
          -- No wrap: f₁_prev > 0, branch2 = prev_f₂ = x/y
          have ih_f2 := congrFun ih ⟨2, by decide⟩
          simp [hy] at ih_f2
          have hf1 : (y - 1) - x % y > 0 := by
            have := Nat.mod_lt x hy_pos
            omega
          simp [Nat.sub_eq_zero_iff_le.not.mpr (by omega : ¬ y - 1 ≤ x % y)]
          -- (x + 1) / y = x / y when x % y < y - 1
          have : (x + 1) / y = x / y := by
            rw [Nat.add_div hy_pos]
            simp [Nat.mod_eq_of_lt (by omega : (x % y) + 1 < y)]
            -- the conditional adjustment is 0 when (x%y)+1 < y
            split_ifs with hge
            · omega
            · rfl
          omega
```

If the wrap-case arithmetic gets unwieldy, factor:

```lean
private lemma KMor1.div_step_wrap (x y : ℕ) (hy : 0 < y)
    (hw : x % y = y - 1) :
    (x + 1) / y = x / y + 1 := by
  ...

private lemma KMor1.div_step_no_wrap (x y : ℕ) (hy : 0 < y)
    (hw : x % y < y - 1) :
    (x + 1) / y = x / y := by
  ...
```

- [ ] **Step 2: Build and commit**

Run: `lake build`. Expected: PASS, no warnings, no `sorry`.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Prove KMor1.divAux_components (joint-vector value)"
```

---

### Task 4.3: Add `KMor1.div`

**Spec:** §4.11.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, #guards**

```lean
/-- Integer division (Marchenkov convention): `div(x, y) = ⌊x/y⌋`
for `y ≥ 1`; `div(x, 0) = x` per Marchenkov 2007 §1. -/
def KMor1.div : KMor1 2 := KMor1.divAux

/-- Interpretation of `div`: matches Marchenkov's `x/y` (with
`x/0 = x`). -/
@[simp] theorem KMor1.interp_div (ctx : Fin 2 → ℕ) :
    KMor1.div.interp ctx =
      if ctx 1 = 0 then ctx 0 else ctx 0 / ctx 1 := by
  unfold KMor1.div KMor1.divAux
  rw [KMor1.interp_simrec]
  have hp : (fun j : Fin 1 => ctx (Fin.succ j)) = fun _ => ctx 1 := by
    funext j; fin_cases j; rfl
  rw [hp]
  have hcomp := KMor1.divAux_components (ctx 0) (ctx 1)
  have := congrFun hcomp ⟨2, by decide⟩
  by_cases hy : ctx 1 = 0
  · simp [hy] at this ⊢
    convert this using 2
    rfl
  · simp [hy] at this ⊢
    convert this using 2
    rfl

example : KMor1.div.level = 2 := by decide

#guard KMor1.div.interp ![7, 3] = 2
#guard KMor1.div.interp ![6, 3] = 2
#guard KMor1.div.interp ![5, 1] = 5
#guard KMor1.div.interp ![3, 5] = 0
#guard KMor1.div.interp ![5, 0] = 5      -- Marchenkov: x/0 = x
#guard KMor1.div.interp ![0, 5] = 0
#guard KMor1.div.interp ![5, 5] = 1
```

- [ ] **Step 2: Build and commit**

Run: `lake build`. Expected: PASS, no warnings.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.div (Marchenkov integer division)"
```

---

### Task 4.4: Add `KMor1.divNat`

**Spec:** §4.12.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`

- [ ] **Step 1: Add def, interp lemma, level proof, #guards**

```lean
/-- Lean-`Nat.div`-convention integer division: `divNat(x, 0) = 0`
(matching `Nat.div_zero`).  Wraps `KMor1.div` (Marchenkov) with an
outer `cond` to short-circuit the `y = 0` case to `0`. -/
def KMor1.divNat : KMor1 2 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩       -- switch on y
    | ⟨1, _⟩ => KMor1.zero                      -- if y = 0, return 0
    | ⟨2, _⟩ => KMor1.div)                      -- else, Marchenkov div

/-- Interpretation of `divNat`: `ctx 0 / ctx 1` matching Lean
`Nat.div`. -/
@[simp] theorem KMor1.interp_divNat (ctx : Fin 2 → ℕ) :
    KMor1.divNat.interp ctx = ctx 0 / ctx 1 := by
  unfold KMor1.divNat
  rw [KMor1.interp_comp, KMor1.interp_cond, KMor1.interp_proj,
      KMor1.interp_zero]
  rw [KMor1.interp_div]
  by_cases hy : ctx 1 = 0
  · simp [hy, Nat.div_zero]
  · simp [hy]

example : KMor1.divNat.level = 2 := by decide

#guard KMor1.divNat.interp ![7, 3] = 2
#guard KMor1.divNat.interp ![5, 0] = 0   -- Lean Nat.div: x/0 = 0
#guard KMor1.divNat.interp ![0, 5] = 0
#guard KMor1.divNat.interp ![5, 5] = 1
```

- [ ] **Step 2: Build and commit**

Run: `lake build`. Expected: PASS, no warnings.

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.divNat (Lean Nat.div convention)"
```

---

## Phase 5: Re-export and final verification

### Task 5.1: Re-export `Utilities.KArith` from the library entry point

**Files:**

- Modify: `GebLean.lean`

- [ ] **Step 1: Add the import**

Find the existing block of `import GebLean.Utilities.*` in
`GebLean.lean` and add (in alphabetical order):

```lean
import GebLean.Utilities.KArith
```

- [ ] **Step 2: Build and commit**

Run: `lake build`. Expected: PASS, no warnings.

```bash
git add GebLean.lean
git commit -m "Re-export Utilities.KArith from GebLean entry point"
```

---

### Task 5.2: Final verification

- [ ] **Step 1: Full clean build**

Run: `lake build`
Expected: PASS, no warnings, no `sorry` (`grep -r 'sorry' GebLean/`
returns nothing under `GebLean/Utilities/KArith.lean`).

- [ ] **Step 2: Tests pass**

Run: `lake test`
Expected: PASS.

- [ ] **Step 3: Markdownlint clean (for spec and plan)**

Run:

```bash
markdownlint-cli2 \
  docs/superpowers/specs/2026-05-05-karith-design.md \
  docs/superpowers/plans/2026-05-05-karith-implementation.md
```

Expected: no errors.

- [ ] **Step 4: Forbidden-style-word scan**

Build the grep pattern from the CLAUDE.md forbidden list and run
against `GebLean/Utilities/KArith.lean`. Expected: empty output
(false positives like `by decide` filtered out via `grep -v`).

- [ ] **Step 5: All twelve functions present**

Run:

```bash
grep -E "^def KMor1\\.(pred|isZero|add|double|cond|\
notEq1|mult|monus|pow2|mod|div|divNat) " \
  GebLean/Utilities/KArith.lean | wc -l
```

Expected: `12`.

- [ ] **Step 6: Update session notes and commit**

```bash
git add .session/
git commit -m "Final KArith verification: all functions, tests, builds clean"
```

(Skip the commit if `.session/` did not need updates.)

---

## Done

The twelve functions `pred`, `isZero`, `add`, `double`, `cond`,
`notEq1`, `mult`, `monus`, `pow2`, `mod`, `div`, `divNat` are now
available under `KMor1.*` in `GebLean.Utilities.KArith`. Each
function has a `@[simp]`-marked correctness theorem and a
`level ≤ N := by decide` placement proof. Tests are inline.
