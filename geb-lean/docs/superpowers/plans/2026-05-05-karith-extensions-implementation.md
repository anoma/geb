# KArith Extensions Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Refactor `interp_rec1_succ` to delegate to a generalized
simrec lemma; add `permArgs`/`swap` utilities and reuse them in
`monus`; add `eq`/`condEq` for K^sim equality testing; add `pow`
(two-variable exponentiation) at K^sim_2 via the
Marchenkov/Wikipedia formula.

**Architecture:** All four enhancements modify the existing
`Utilities/KArith.lean` and its dependency `LawvereKSim*.lean`.
The `pow` function uses a closed-form composition of existing
level-≤2 K^sim morphisms (no new simrec); correctness is proved via
two `Nat`-level helpers.

**Tech Stack:** Lean 4, mathlib, `lake build`, `lake test`. No new
dependencies.

**Spec:** `docs/superpowers/specs/2026-05-05-karith-extensions-design.md`
(commit `532fbd31`).

**Predecessor:** the original 25-task KArith plan at
`docs/superpowers/plans/2026-05-05-karith-implementation.md` and
its 24 commits on branch `worktree-karith-impl` (latest:
`d6b29e69` re-export of `Utilities.KArith`).

---

## Files

- **Modify** `GebLean/LawvereKSim.lean`: add `KMor1.permArgs`
  and `KMor1.swap` defs (after the existing `KMor1.rec1` block).
- **Modify** `GebLean/LawvereKSimInterp.lean`: add
  `KMor1.simrecVec_succ_append`; refactor `KMor1.interp_rec1_succ`
  to delegate to it; add `KMor1.interp_permArgs` and
  `KMor1.interp_swap`.
- **Modify** `GebLean/Utilities/KArith.lean`:
  - Refactor `KMor1.monus` to use `KMor1.swap KMor1.monusSwapped`.
  - Add `KMor1.signum` (private), `KMor1.eq`, `KMor1.condEq`,
    `KMor1.pow_bound`, `KMor1.pow_formula`, `KMor1.pow`.
- **Modify** `GebLeanTests/Utilities/KArith.lean`: add `#guard`s
  for `swap`, `eq`, `condEq`, `pow`.

## Convention reminders (CLAUDE.md)

- `lake build` and `lake test` clean per commit. Never `lake env
  lean`. Never `lake clean`.
- No `sorry`, `admit`, `Classical`, `noncomputable`, `axiom`. No
  warnings.
- Lines ≤ 80 chars.
- Every `def`/`theorem` cites Tourlakis or another literature
  source per the literature-citation discipline (helper lemmas
  about pure `Nat` arithmetic don't need a citation, but do
  benefit from a brief docstring describing the bound or formula).
- Forbidden style words (in prose; Lean keywords like `sorry` in
  code blocks are exempt only when explicitly used as the keyword
  being prohibited): fundamental, actually, key, insight, core,
  advanced, complex, complicated, simple, advantage, benefit,
  important, challenge, yes, wait, hmm, sorry, careful, difficult,
  blocked, incomplete, future, issue, problem, block.
- Tests live in `GebLeanTests/`, not `GebLean/`. Use `==` (Bool
  decidable equality) inside `#guard`, matching surrounding style.
- Avoid bash process substitution (`<(...)`, `>(...)`); use
  `/tmp` files or shell variables.

## Verification mode notes

- The worktree is at
  `/home/terence/git-workspaces/geb/.claude/worktrees/karith-impl`
  on branch `worktree-karith-impl`. Latest commit before this
  plan starts: `d6b29e69` (re-export of Utilities.KArith).
- Mathlib cache is already warm in the worktree. New `lake build`
  invocations should complete in seconds (incremental).

---

## Phase 0: Generalize `simrecVec_succ_append`, refactor `interp_rec1_succ`

### Task 0.1: Add `KMor1.simrecVec_succ_append` general lemma

**Spec:** §3.1.

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`. Insert immediately
  after the existing `@[simp] theorem KMor1.simrecVec_succ` block
  (around line 209, before the existing `KMor1.interp_rec1_zero`).

- [ ] **Step 1: Insert the general lemma**

Place this new theorem right after `KMor1.simrecVec_succ`'s `rfl`
closing line and before `interp_rec1_zero`:

```lean
/-- Step-case interp for `simrecVec` in the `Fin.append (Fin.cons …)`
form. Equivalent to `simrecVec_succ` (which produces a dite-form
context) but expressed via the standard `Fin.append` of
`Fin.cons (recvar, params)` and the `simrecVec`-at-`n` family.
This is the form used by `KMor1.interp_rec1_succ` and any other
caller that wants to treat the step context positionally. -/
@[simp] theorem KMor1.simrecVec_succ_append {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (n : ℕ) (j : Fin (k + 1)) :
    KMor1.simrecVec h g params (n + 1) j
      = (g j).interp (Fin.append (Fin.cons n params)
                                  (KMor1.simrecVec h g params n)) := by
  -- Proof body: same dite ↔ Fin.append (Fin.cons …) bridge
  -- as the previous `interp_rec1_succ` body, generalized for
  -- arbitrary system size `k + 1`.
  simp only [KMor1.simrecVec_succ]
  congr 1
  funext idx
  rcases idx with ⟨v, h_v⟩
  by_cases h₁ : v < a + 1
  · have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + (k + 1)))
        = Fin.castAdd (k + 1) (⟨v, h₁⟩ : Fin (a + 1)) := by
      apply Fin.ext; rfl
    rw [show Fin.append (Fin.cons n params)
            (KMor1.simrecVec h g params n) ⟨v, h_v⟩
            = Fin.append (Fin.cons n params)
                (KMor1.simrecVec h g params n)
                (Fin.castAdd (k + 1) (⟨v, h₁⟩ : Fin (a + 1)))
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
  · have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + (k + 1)))
        = Fin.natAdd (a + 1)
            (⟨v - (a + 1), by omega⟩ : Fin (k + 1)) := by
      apply Fin.ext
      change v = (a + 1) + (v - (a + 1))
      omega
    rw [show Fin.append (Fin.cons n params)
            (KMor1.simrecVec h g params n) ⟨v, h_v⟩
            = Fin.append (Fin.cons n params)
                (KMor1.simrecVec h g params n)
                (Fin.natAdd (a + 1)
                  (⟨v - (a + 1), by omega⟩ : Fin (k + 1)))
        from congrArg _ h_cast,
        Fin.append_right]
    simp only [h₁, dite_false]
```

- [ ] **Step 2: Build to verify**

Run from the worktree's `geb-lean/`:

```bash
lake build
```

Expected: clean. If the proof fails (e.g., a `simp only`
discharger doesn't fire, or a `Fin.ext`/`congrArg` mismatch
appears): use `lean_multi_attempt` or replace `rfl` with `_` to see
the residual goal. The proof structure mirrors the existing
`KMor1.simrecVec_eq_Nat_simRecVec` proof in the same file
(starting around line 367) — copy its handling pattern as
needed.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.simrecVec_succ_append general step-case lemma"
```

---

### Task 0.2: Refactor `interp_rec1_succ` to use the new lemma

**Spec:** §3.2.

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`. Replace the body of
  the existing `KMor1.interp_rec1_succ` theorem (which currently
  contains the ~50-line dite-bridge proof inline).

- [ ] **Step 1: Replace the proof body**

Find the existing `@[simp] theorem KMor1.interp_rec1_succ` block.
Keep the `@[simp]`, signature, and docstring; replace the proof
body with this short version:

```lean
@[simp] theorem KMor1.interp_rec1_succ {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (n : ℕ) (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons (n + 1) params)
      = g.interp (Fin.append (Fin.cons n params)
          (fun _ : Fin 1 =>
            (KMor1.rec1 h g).interp (Fin.cons n params))) := by
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  -- ctx 0 = n+1; params lookup gives back `params`
  have h_ctx0 :
      (Fin.cons (n + 1) params : Fin (a + 1) → ℕ) 0 = n + 1 := by
    simp [Fin.cons_zero]
  have h_params :
      (fun j : Fin a =>
          (Fin.cons (n + 1) params : Fin (a + 1) → ℕ) (Fin.succ j))
        = params := by
    funext j; simp [Fin.cons_succ]
  rw [h_ctx0, h_params]
  -- Apply the new general lemma with k := 0, j := ⟨0, _⟩
  rw [KMor1.simrecVec_succ_append]
  -- Reduce the prev-vector lookup `simrecVec ... n` (a Fin 1 → ℕ
  -- family) back into the `(rec1 h g).interp` form.
  congr 1
  funext j
  fin_cases j
  show KMor1.simrecVec (fun _ => h) (fun _ => g) params n
        ⟨0, by decide⟩
      = (KMor1.rec1 h g).interp (Fin.cons n params)
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  have h_ctx0' :
      (Fin.cons n params : Fin (a + 1) → ℕ) 0 = n := by
    simp [Fin.cons_zero]
  have h_params' :
      (fun j : Fin a =>
          (Fin.cons n params : Fin (a + 1) → ℕ) (Fin.succ j))
        = params := by
    funext j; simp [Fin.cons_succ]
  rw [h_ctx0', h_params']
```

If the existing `interp_rec1_succ` had a `rfl` line at its end (it
does in Phase 0's original implementation), keep removing it
unless a "no goals" error tells you otherwise — most rewrites here
close definitionally.

- [ ] **Step 2: Build clean**

```bash
lake build
```

Expected: clean. The original `interp_rec1_succ`'s ~50-line proof
collapses into ~25 lines, of which the substantive work is now in
`simrecVec_succ_append`.

If the `fin_cases j` line breaks elaboration (because
`fin_cases` isn't always available without the `Mathlib.Tactic.FinCases`
import), substitute with:

```lean
  match j with
  | ⟨0, _⟩ => ?_
```

and proceed with the existing tactics inside the single subgoal.

- [ ] **Step 3: Run tests to ensure downstream consumers still pass**

```bash
lake test
```

Expected: clean. The existing `pred_aux`, `add_aux`, etc.
in `Utilities/KArith.lean` use `interp_rec1_succ` and must
continue to typecheck.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Refactor KMor1.interp_rec1_succ to use simrecVec_succ_append"
```

---

## Phase 1: `permArgs` and `swap`

### Task 1.1: Add `KMor1.permArgs` definition

**Spec:** §4.1.

**Files:**

- Modify: `GebLean/LawvereKSim.lean`. Insert after the existing
  `KMor1.rec1` block (around line 144, before the existing
  `level_le_succ` theorem).

- [ ] **Step 1: Add the def**

```lean
/-- Precompose a `KMor1 m` term with a context permutation
`σ : Fin n → Fin m`. Given `f : KMor1 m`, produces a `KMor1 n`
that interprets at context `c : Fin n → ℕ` as `f.interp (c ∘ σ)`.

Built from `comp` and `proj` only; no new constructors. The level
is unchanged from `f.level`: `comp` takes `max` over children's
levels and the inner `proj`s are level 0. -/
def KMor1.permArgs {n m : ℕ} (σ : Fin n → Fin m) (f : KMor1 m) :
    KMor1 n :=
  KMor1.comp f (fun i => KMor1.proj (σ i))
```

- [ ] **Step 2: Build clean**

```bash
lake build
```

Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereKSim.lean
git commit -m "Add KMor1.permArgs (precompose with context permutation)"
```

---

### Task 1.2: Add `KMor1.interp_permArgs` simp lemma

**Spec:** §4.2.

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`. Insert after
  `KMor1.interp_rec1_succ`.

- [ ] **Step 1: Add the simp lemma**

```lean
/-- Interpretation of `permArgs`: `f.interp` applied to the
permuted context `c ∘ σ`. -/
@[simp] theorem KMor1.interp_permArgs {n m : ℕ}
    (σ : Fin n → Fin m) (f : KMor1 m) (ctx : Fin n → ℕ) :
    (f.permArgs σ).interp ctx = f.interp (fun i => ctx (σ i)) := by
  unfold KMor1.permArgs
  rw [KMor1.interp_comp]
  rfl
```

- [ ] **Step 2: Build clean**

```bash
lake build
```

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.interp_permArgs simp lemma"
```

---

### Task 1.3: Add `KMor1.swap` definition

**Spec:** §4.1.

**Files:**

- Modify: `GebLean/LawvereKSim.lean`. Insert after `KMor1.permArgs`.

- [ ] **Step 1: Add the def**

```lean
/-- Argument-swap for 2-argument K^sim morphisms:
`(KMor1.swap f).interp ctx = f.interp ![ctx 1, ctx 0]`.
Specialization of `permArgs` to the swap permutation on `Fin 2`. -/
def KMor1.swap (f : KMor1 2) : KMor1 2 :=
  KMor1.permArgs
    (fun i => match i with
      | ⟨0, _⟩ => ⟨1, by decide⟩
      | ⟨1, _⟩ => ⟨0, by decide⟩) f
```

- [ ] **Step 2: Build clean**

```bash
lake build
```

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereKSim.lean
git commit -m "Add KMor1.swap (2-arg specialization of permArgs)"
```

---

### Task 1.4: Add `KMor1.interp_swap` simp lemma

**Spec:** §4.2.

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`. Insert after
  `KMor1.interp_permArgs`.

- [ ] **Step 1: Add the simp lemma**

Try the simpler form first; if downstream proofs (especially the
upcoming `monus` refactor) need a different shape, switch then.

```lean
/-- Interpretation of `swap`: `f` applied with the two arguments
swapped. -/
@[simp] theorem KMor1.interp_swap (f : KMor1 2) (ctx : Fin 2 → ℕ) :
    (KMor1.swap f).interp ctx
      = f.interp (fun i => match i with
                            | ⟨0, _⟩ => ctx 1
                            | ⟨1, _⟩ => ctx 0) := by
  unfold KMor1.swap
  rw [KMor1.interp_permArgs]
  rfl
```

- [ ] **Step 2: Build clean**

```bash
lake build
```

If the `rfl` does not close the goal: replace it with
`simp [Fin.cons_zero, Fin.cons_succ]` or add explicit
`funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl`.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.interp_swap simp lemma"
```

---

### Task 1.5: Refactor `KMor1.monus` to use `swap`

**Spec:** §4.3.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`. Find the existing
  `KMor1.monus` def + `interp_monus` theorem block.

- [ ] **Step 1: Replace the def**

Old (current code):

```lean
def KMor1.monus : KMor1 2 :=
  KMor1.comp KMor1.monusSwapped (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)
```

New:

```lean
def KMor1.monus : KMor1 2 := KMor1.swap KMor1.monusSwapped
```

- [ ] **Step 2: Replace the proof body of `interp_monus`**

Old:

```lean
@[simp] theorem KMor1.interp_monus (ctx : Fin 2 → ℕ) :
    KMor1.monus.interp ctx = ctx 0 - ctx 1 := by
  unfold KMor1.monus
  rw [KMor1.interp_comp, KMor1.interp_monusSwapped]
  rfl
```

New:

```lean
@[simp] theorem KMor1.interp_monus (ctx : Fin 2 → ℕ) :
    KMor1.monus.interp ctx = ctx 0 - ctx 1 := by
  unfold KMor1.monus
  rw [KMor1.interp_swap, KMor1.interp_monusSwapped]
```

The `interp_swap` rewrite substitutes the swap context inside
`monusSwapped`'s interp, which by `interp_monusSwapped` reduces to
`(swap-ctx 1) - (swap-ctx 0) = ctx 0 - ctx 1`.

If the proof leaves a residual `rfl` goal (which it might since
the swap-context match is inside the rewrite): finish with `rfl`
explicitly.

- [ ] **Step 3: Build + test clean**

```bash
lake build && lake test
```

Both must be clean. If the proof breaks, the most likely cause is
that `interp_swap`'s match form doesn't reduce automatically; add
`unfold KMor1.swap; simp [KMor1.interp_permArgs,
KMor1.interp_monusSwapped]` instead.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Refactor KMor1.monus to use KMor1.swap"
```

---

## Phase 2: `eq` and `condEq`

### Task 2.1: Add private `KMor1.signum` helper

**Spec:** §5.1.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`. Insert after the
  refactored `KMor1.monus` block.

- [ ] **Step 1: Verify no existing `KMor1.signum`**

```bash
grep -n 'KMor1.signum' GebLean/ GebLeanTests/ -r
```

Expected: no matches (the original `notEq1` plan had `signum` as
an option but the committed implementation used a different
construction).

- [ ] **Step 2: Add the def + simp lemma**

```lean
/-- Sign function: `signum(0) = 0`, `signum(n+1) = 1`. Equivalent
to the level-1 composite `isZero ∘ isZero`: `isZero(n) = 1 - sgn n`,
so `isZero (isZero n) = sgn n`. Used to normalize `eq`'s {0, ≥1}-
valued output to {0, 1}.

Tourlakis PR §0.1.0.17(3) (`λx. 1 ∸ x ∈ K_1`); composition with
itself stays at K^sim_1. -/
private def KMor1.signum : KMor1 1 :=
  KMor1.comp KMor1.isZero (fun _ : Fin 1 => KMor1.isZero)

@[simp] private theorem KMor1.interp_signum (ctx : Fin 1 → ℕ) :
    KMor1.signum.interp ctx = if ctx 0 = 0 then 0 else 1 := by
  unfold KMor1.signum
  rw [KMor1.interp_comp, KMor1.interp_isZero, KMor1.interp_isZero]
  rcases h : ctx 0 with _ | n
  · simp
  · simp

example : KMor1.signum.level = 1 := by decide
```

- [ ] **Step 3: Build clean**

```bash
lake build
```

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.signum (private helper, K^sim_1)"
```

---

### Task 2.2: Add `KMor1.eq` definition + interp lemma

**Spec:** §5.2.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`. Insert after `signum`.

- [ ] **Step 1: Add the def**

```lean
/-- Characteristic of the predicate `x = y` (Tourlakis convention):
`eq(x, y) = 0` iff `x = y`, `eq(x, y) = 1` iff `x ≠ y`.

Composes with `cond` for "if x = y then z else z'":
`cond(eq(x, y), z, z') = if x = y then z else z'`.

Construction: `signum((x ∸ y) + (y ∸ x))`. The inner sum vanishes
exactly at `x = y`; `signum` normalizes the result to {0, 1}.

Tourlakis Notes 10.2.20 (`λx.x = a ∈ K_{1,*}` for fixed `a`);
generalized here to two-variable equality via Boolean closure of
K_{n,*} (Notes 10.2.14) plus `monus` at K^sim_2. -/
def KMor1.eq : KMor1 2 :=
  KMor1.comp KMor1.signum (fun _ : Fin 1 =>
    KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.monus
      | ⟨1, _⟩ => KMor1.swap KMor1.monus))
```

- [ ] **Step 2: Add the interp lemma**

```lean
/-- Interpretation of `eq`: 0 if `ctx 0 = ctx 1`, else 1. -/
@[simp] theorem KMor1.interp_eq (ctx : Fin 2 → ℕ) :
    KMor1.eq.interp ctx = if ctx 0 = ctx 1 then 0 else 1 := by
  unfold KMor1.eq
  rw [KMor1.interp_comp, KMor1.interp_signum,
      KMor1.interp_comp, KMor1.interp_add,
      KMor1.interp_monus, KMor1.interp_swap, KMor1.interp_monus]
  by_cases h : ctx 0 = ctx 1
  · simp [h]
  · -- ctx 0 ≠ ctx 1: WLOG one of (ctx 0 - ctx 1), (ctx 1 - ctx 0)
    -- is positive, so the inner sum is positive, so signum = 1.
    rcases Nat.lt_or_lt_of_ne h with hlt | hgt
    · have h1 : ctx 0 - ctx 1 = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
      have h2 : ctx 1 - ctx 0 > 0 := Nat.sub_pos_of_lt hlt
      simp [h, h1, Nat.add_pos_right _ h2]
    · have h1 : ctx 1 - ctx 0 = 0 := Nat.sub_eq_zero_of_le (le_of_lt hgt)
      have h2 : ctx 0 - ctx 1 > 0 := Nat.sub_pos_of_lt hgt
      simp [h, h1, Nat.add_pos_left _ h2]

example : KMor1.eq.level = 2 := by decide
```

If `Nat.lt_or_lt_of_ne` is not the canonical name, alternatives
include `Nat.lt_or_gt_of_ne`, `lt_or_gt_of_ne`, or
`rcases lt_trichotomy (ctx 0) (ctx 1) with hlt | heq | hgt`
then dispatch each case (with `(h heq).elim` for the equality
branch).

- [ ] **Step 3: Build clean**

```bash
lake build
```

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Add KMor1.eq (Tourlakis χ(x = y) at K^sim_2)"
```

---

### Task 2.3: Add `KMor1.condEq` definition + interp lemma + tests

**Spec:** §5.3.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`. Insert after `eq`.
- Modify: `GebLeanTests/Utilities/KArith.lean`. Add tests.

- [ ] **Step 1: Add the def**

```lean
/-- "If x = y then z else z'": composition of `cond` with
`eq(x, y)`.

`condEq(x, y, z, z') = z` when `x = y`, `z'` otherwise. -/
def KMor1.condEq : KMor1 4 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ =>
        -- eq applied to slots 0, 1 of the outer 4-arg ctx
        KMor1.comp KMor1.eq (fun j => match j with
          | ⟨0, _⟩ => KMor1.proj ⟨0, by decide⟩
          | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩)
    | ⟨1, _⟩ => KMor1.proj ⟨2, by decide⟩
    | ⟨2, _⟩ => KMor1.proj ⟨3, by decide⟩)
```

(Direct `comp eq ![proj 0, proj 1]` instead of `permArgs`-based
form; both produce the same level-2 morphism but the direct
composition reduces more cleanly through `simp`.)

- [ ] **Step 2: Add the interp lemma**

```lean
/-- Interpretation of `condEq`: `if ctx 0 = ctx 1 then ctx 2 else ctx 3`. -/
@[simp] theorem KMor1.interp_condEq (ctx : Fin 4 → ℕ) :
    KMor1.condEq.interp ctx
      = if ctx 0 = ctx 1 then ctx 2 else ctx 3 := by
  unfold KMor1.condEq
  rw [KMor1.interp_comp, KMor1.interp_cond, KMor1.interp_comp,
      KMor1.interp_eq, KMor1.interp_proj, KMor1.interp_proj,
      KMor1.interp_proj, KMor1.interp_proj]
  by_cases h : ctx 0 = ctx 1
  · simp [h]
  · simp [h]

example : KMor1.condEq.level = 2 := by decide
```

- [ ] **Step 3: Add tests in `GebLeanTests/Utilities/KArith.lean`**

```lean
#guard KMor1.eq.interp ![3, 3] == 0
#guard KMor1.eq.interp ![3, 5] == 1
#guard KMor1.eq.interp ![5, 3] == 1
#guard KMor1.eq.interp ![0, 0] == 0
#guard KMor1.condEq.interp ![3, 3, 11, 22] == 11
#guard KMor1.condEq.interp ![3, 5, 11, 22] == 22
#guard KMor1.condEq.interp ![0, 0, 11, 22] == 11
```

- [ ] **Step 4: Build + test clean**

```bash
lake build && lake test
```

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/KArith.lean GebLeanTests/Utilities/KArith.lean
git commit -m "Add KMor1.condEq + tests (if x = y then z else z')"
```

---

## Phase 3: `pow`

### Task 3.1: Prove `KMor1.pow_bound` (Nat helper)

**Spec:** §6.1.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`. Insert after `condEq`.

- [ ] **Step 1: Add the lemma**

```lean
/-- Bound used in the Wikipedia/Marchenkov formula for `x^y`:
`x^y + x < 2^(x*y + x + 1)`.

Proof by induction on `y` with case-split on `x = 0`:
- `y = 0`: `1 + x < 2^(x + 1)` from `Nat.lt_two_pow_self`.
- `y → y + 1`, `x = 0`: trivially `0 + 0 < 2`.
- `y → y + 1`, `x ≥ 1`: combine IH with `Nat.pow_succ` and
  monotonicity of `2^_`. -/
private theorem KMor1.pow_bound (x y : ℕ) :
    x ^ y + x < 2 ^ (x * y + x + 1) := by
  induction y with
  | zero =>
    -- Goal: x^0 + x < 2^(x*0 + x + 1) = 2^(x + 1)
    -- x^0 = 1, so 1 + x < 2^(x + 1) = 2 * 2^x
    -- and Nat.lt_two_pow_self gives x < 2^x, hence 1 + x ≤ 2^x + 1 ≤ 2 * 2^x
    have hx : x < 2 ^ x := Nat.lt_two_pow_self
    have : 1 + x ≤ 2 ^ x + 1 := by omega
    have : 1 + x < 2 ^ (x + 1) := by
      rw [Nat.pow_succ]
      have : 2 ^ x ≥ 1 := Nat.one_le_two_pow
      omega
    simpa [Nat.pow_zero, Nat.mul_zero] using this
  | succ y ih =>
    -- Goal: x^(y+1) + x < 2^(x*(y+1) + x + 1) = 2^(x*y + x + x + 1)
    by_cases hx : x = 0
    · -- 0^(y+1) = 0; 0 + 0 < 2^(...)
      simp [hx, Nat.pow_succ, Nat.zero_pow (Nat.succ_ne_zero y)]
    · -- x ≥ 1
      have hx1 : x ≥ 1 := Nat.one_le_iff_ne_zero.mpr hx
      -- x^(y+1) = x * x^y. By IH, x^y < 2^(x*y + x + 1) - x ≤ 2^(x*y + x + 1).
      -- So x * x^y ≤ x * 2^(x*y + x + 1) ≤ ... use power-of-2 monotonicity.
      have h_pow_y : x ^ y ≤ 2 ^ (x * y + x + 1) := by
        have := ih
        omega
      have h_pow_succ : x ^ (y + 1) = x * x ^ y := by
        rw [Nat.pow_succ]; ring
      -- 2^(x*(y+1) + x + 1) = 2^(x*y + x + x + 1) = 2^x * 2^(x*y + x + 1)
      have h_target : 2 ^ (x * (y + 1) + x + 1)
          = 2 ^ x * 2 ^ (x * y + x + 1) := by
        rw [← Nat.pow_add]
        congr 1
        ring
      rw [h_pow_succ, h_target]
      -- Need: x * x^y + x < 2^x * 2^(x*y + x + 1)
      -- Use: x ≤ 2^x (Nat.lt_two_pow_self) and x^y < 2^(x*y + x + 1) - x
      have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
      -- Multiply: x * x^y ≤ (2^x - 1) * x^y ≤ 2^x * x^y; but we need
      -- enough slack for the +x. Use the IH more directly:
      have ih_bound : x ^ y < 2 ^ (x * y + x + 1) - x := by omega
      have h_2pow_pos : 2 ^ (x * y + x + 1) > 0 := Nat.two_pow_pos _
      -- Routing: x * x^y + x ≤ x * 2^(x*y + x + 1)
      --                       ≤ 2^x * 2^(x*y + x + 1) - 1
      have h1 : x * x ^ y + x ≤ x * (2 ^ (x * y + x + 1)) := by
        have hxy : x ^ y < 2 ^ (x * y + x + 1) := by omega
        nlinarith [Nat.zero_le x, Nat.zero_le (x ^ y)]
      have h2 : x * 2 ^ (x * y + x + 1) < 2 ^ x * 2 ^ (x * y + x + 1) := by
        exact Nat.mul_lt_mul_right h_2pow_pos hx_lt
      omega
```

The succ case is the substantive piece. If the `nlinarith` /
`omega` chains don't close, factor into smaller steps:

```lean
      -- Replace the nlinarith block with manual steps:
      have hxy_bound : x * x ^ y ≤ x * (2 ^ (x * y + x + 1) - x) := by
        exact Nat.mul_le_mul_left x (Nat.le_of_lt ih_bound)
      have hxy_plus : x * x ^ y + x ≤ x * (2 ^ (x * y + x + 1) - x) + x :=
        Nat.add_le_add_right hxy_bound x
      have h1 : x * (2 ^ (x * y + x + 1) - x) + x
                ≤ x * 2 ^ (x * y + x + 1) := by
        have hsub : x * (2 ^ (x * y + x + 1) - x)
                    = x * 2 ^ (x * y + x + 1) - x * x := by
          rw [Nat.mul_sub_left]
        rw [hsub]
        have hbound : x * x ≤ x * 2 ^ (x * y + x + 1) := by
          exact Nat.mul_le_mul_left x (Nat.le_of_lt
            (Nat.lt_of_lt_of_le hx_lt
              (Nat.pow_le_pow_right (by omega : 2 ≤ 2)
                (by omega : x ≤ x * y + x + 1))))
        omega
```

The exact mathlib lemma names may need tweaks. If
`Nat.pow_le_pow_right` is renamed to `Nat.pow_le_pow_left` or
similar, search via `lean_loogle` for the appropriate form
(`?n ≤ ?m → n ≤ m → n^k ≤ m^k` vs `?n^?a ≤ ?n^?b`).

- [ ] **Step 2: Build clean**

```bash
lake build
```

If the proof gets stuck, replace the failing tactics with `_` to
inspect the residual goal, then iterate. The mathematical content
of `pow_bound` is straightforward — only the Lean tactics may need
adjustment.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Prove KMor1.pow_bound (Nat helper for pow correctness)"
```

---

### Task 3.2: Prove `KMor1.pow_formula` (Nat helper)

**Spec:** §6.2.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`. Insert after
  `pow_bound`.

- [ ] **Step 1: Add the lemma**

```lean
/-- Wikipedia/Marchenkov formula for `x^y`:

  `x^y = 2^((x*y + x + 1) * y) % (2^(x*y + x + 1) - x)`.

Used by `KMor1.pow` to express exponentiation as a level-2
composition. The formula is from Prunescu, Sauras-Altuzarra,
Shunia (2025); see Wikipedia "Further Examples" under Elementary
recursive function § Superposition bases. -/
private theorem KMor1.pow_formula (x y : ℕ) :
    x ^ y =
      2 ^ ((x * y + x + 1) * y) %
        (2 ^ (x * y + x + 1) - x) := by
  set m := x * y + x + 1 with hm_def
  set M := 2 ^ m - x with hM_def
  -- Step 1: M > 0 (because 2^m > x by pow_bound at this index).
  have h_bound := KMor1.pow_bound x y
  have h_pow_gt_x : 2 ^ m > x := by
    have : x ^ y + x < 2 ^ m := h_bound
    have : x < 2 ^ m := by omega
    exact this
  have hM_pos : M > 0 := by
    rw [hM_def]
    omega
  -- Step 2: 2^(m*y) = (2^m)^y
  have h_pow_mul : 2 ^ (m * y) = (2 ^ m) ^ y := by
    rw [← Nat.pow_mul]
  -- Step 3: 2^m ≡ x (mod M); equivalently (2^m) % M = x % M = x
  --   because 2^m = M + x and x < M (from pow_bound rearranged).
  have h_x_lt_M : x ^ y < M := by
    rw [hM_def]; omega
  have h_x_lt_M_base : x < M := by
    have hy0 := KMor1.pow_bound x 0
    have : x ^ 0 + x < 2 ^ (x * 0 + x + 1) := hy0
    -- 1 + x < 2^(x+1); but we want x < M = 2^m - x, i.e., 2x < 2^m.
    -- From pow_bound (general y): x^y + x < 2^m, so 2x ≤ x^y + x < 2^m
    -- when x^y ≥ x. For x = 0 this gives 0 < 2^m trivially; for x ≥ 1
    -- and y ≥ 1, x^y ≥ x. For y = 0, x^0 = 1, need 1 + x < 2^m =
    -- 2^(x*0 + x + 1) = 2^(x+1), which is hy0.
    -- A cleaner route: from h_bound, x ^ y ≥ 0 so 2^m > x^y + x ≥ x.
    have : x ^ y ≥ 0 := Nat.zero_le _
    omega
  have h_2pow_eq : 2 ^ m = M + x := by
    rw [hM_def]; omega
  have h_2pow_mod : 2 ^ m % M = x := by
    rw [h_2pow_eq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_mod, Nat.mod_eq_of_lt h_x_lt_M_base]
  -- Step 4: (2^m)^y % M = x^y % M (modular exponentiation)
  have h_pow_mod : (2 ^ m) ^ y % M = x ^ y % M := by
    rw [Nat.pow_mod, h_2pow_mod, ← Nat.pow_mod]
  -- Step 5: x^y < M, so x^y % M = x^y.
  have h_xy_mod : x ^ y % M = x ^ y :=
    Nat.mod_eq_of_lt h_x_lt_M
  -- Combine: 2^(m*y) % M = (2^m)^y % M = x^y % M = x^y.
  rw [h_pow_mul, h_pow_mod, h_xy_mod]
```

The exact mathlib lemma names may need adjustment:

- `Nat.pow_mul : a ^ (m * n) = (a ^ m) ^ n` — confirm orientation.
  In mathlib it's `pow_mul`. If the orientation is reversed,
  use `← Nat.pow_mul` in the appropriate place.
- `Nat.pow_mod : a^n % m = ((a % m)^n) % m` — confirm.
- `Nat.mod_eq_of_lt : a < n → a % n = a` — confirm.
- `Nat.mod_self : n % n = 0` — confirm.

If any name fails, search via:

```bash
# In lean_loogle or via grep against mathlib4 source:
# Pattern: ?a ^ (?m * ?n) = (?a ^ ?m) ^ ?n
```

- [ ] **Step 2: Build clean**

```bash
lake build
```

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/KArith.lean
git commit -m "Prove KMor1.pow_formula (Wikipedia/Marchenkov x^y formula)"
```

---

### Task 3.3: Add `KMor1.pow` definition + interp lemma + tests

**Spec:** §6.3.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean`. Insert after
  `pow_formula`.
- Modify: `GebLeanTests/Utilities/KArith.lean`. Add tests.

- [ ] **Step 1: Add the def**

```lean
/-- Exponentiation `pow(x, y) = x ^ y` at K^sim_2.

Construction follows the Marchenkov / Wikipedia formula
`x^y = 2^((xy + x + 1) · y) mod (2^(xy + x + 1) ∸ x)` (Prunescu,
Sauras-Altuzarra, Shunia 2025). All sub-expressions use existing
KArith functions at K^sim_2 or below; the composition stays at
K^sim_2. A direct simrec construction `pow(x, y+1) = mult(x,
pow(x, y))` would land at K^sim_3 because the step uses `mult`.

Marchenkov 2007 §1: `x^y` is in the elementary class generated by
`{x+y, x∸y, x/y, 2^x}`. -/
def KMor1.pow : KMor1 2 :=
  -- m := x*y + x + 1
  let mTerm : KMor1 2 :=
    KMor1.comp KMor1.succ (fun _ : Fin 1 =>
      KMor1.comp KMor1.add (fun i => match i with
        | ⟨0, _⟩ => KMor1.mult
        | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩))
  -- numerator = 2^(m * y)
  let numerator : KMor1 2 :=
    KMor1.comp KMor1.pow2 (fun _ : Fin 1 =>
      KMor1.comp KMor1.mult (fun i => match i with
        | ⟨0, _⟩ => mTerm
        | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩))
  -- divisor = 2^m ∸ x
  let divisor : KMor1 2 :=
    KMor1.comp KMor1.monus (fun i => match i with
      | ⟨0, _⟩ => KMor1.comp KMor1.pow2
                    (fun _ : Fin 1 => mTerm)
      | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)
  -- result = numerator mod divisor
  KMor1.comp KMor1.mod (fun i => match i with
    | ⟨0, _⟩ => numerator
    | ⟨1, _⟩ => divisor)
```

- [ ] **Step 2: Add the interp lemma**

```lean
/-- Interpretation of `pow`: standard `Nat` exponentiation. -/
@[simp] theorem KMor1.interp_pow (ctx : Fin 2 → ℕ) :
    KMor1.pow.interp ctx = ctx 0 ^ ctx 1 := by
  unfold KMor1.pow
  -- Reduce all the inner compositions via the @[simp] interp
  -- lemmas of the components (mult, add, succ, pow2, monus, mod, proj).
  simp only [KMor1.interp_comp, KMor1.interp_mod,
             KMor1.interp_pow2, KMor1.interp_mult,
             KMor1.interp_add, KMor1.interp_succ,
             KMor1.interp_monus, KMor1.interp_proj]
  -- Now the goal is the Nat-level formula; apply pow_formula
  -- (with appropriate orientation of `(ctx 0)`, `(ctx 1)`).
  exact (KMor1.pow_formula (ctx 0) (ctx 1)).symm

example : KMor1.pow.level ≤ 2 := by decide
```

If the `simp only` chain leaves residual `Fin (1+0)`-style index
mismatches, add `Nat.add_zero`, `Nat.zero_add` to the simp set. If
`pow_formula`'s LHS/RHS orientation doesn't unify with what `simp
only` leaves, try `rw [← KMor1.pow_formula]` instead of `exact`.

The precise level proof depends on whether `decide` can navigate
`Finset.univ.sup` over the nested `Fin` computations. Empirically
this worked for `mod` (also level ≤ 2 by composition); if it
times out, replace with a structured `unfold KMor1.pow; …`-style
proof.

- [ ] **Step 3: Add tests**

In `GebLeanTests/Utilities/KArith.lean`:

```lean
#guard KMor1.pow.interp ![2, 3] == 8
#guard KMor1.pow.interp ![3, 2] == 9
#guard KMor1.pow.interp ![1, 5] == 1
#guard KMor1.pow.interp ![5, 1] == 5
#guard KMor1.pow.interp ![0, 0] == 1
#guard KMor1.pow.interp ![0, 1] == 0
#guard KMor1.pow.interp ![5, 0] == 1
#guard KMor1.pow.interp ![2, 5] == 32
```

- [ ] **Step 4: Build + test clean**

```bash
lake build && lake test
```

If a `#guard` stalls (kernel reduction of `2^65` etc.), replace
the guard with an `example`-form using simp:

```lean
example : KMor1.pow.interp ![2, 3] = 8 := by simp
```

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/KArith.lean GebLeanTests/Utilities/KArith.lean
git commit -m "Add KMor1.pow + tests (two-variable exponentiation at K^sim_2)"
```

---

## Phase 4: Tests for `swap` and final verification

### Task 4.1: Add `swap` tests

Tests for the `swap` utility were not added in Task 1.5 (which
only refactored `monus`). Add them now to confirm the utility's
behavior independent of `monus`.

**Files:**

- Modify: `GebLeanTests/Utilities/KArith.lean`.

- [ ] **Step 1: Add tests**

Place near the other `KMor1` tests (e.g., near `monus`'s tests):

```lean
#guard (KMor1.swap KMor1.add).interp ![3, 7] == 10
#guard (KMor1.swap KMor1.monusSwapped).interp ![5, 3] == 2
#guard (KMor1.swap KMor1.monus).interp ![3, 5] == 0
```

(Note: `monusSwapped` is private — the test must be in the same
module as `monusSwapped` or use the public-via-monus form. Since
tests live in `GebLeanTests/`, the private cross-module visibility
is the constraint. Use the public form
`(KMor1.swap KMor1.monus).interp ![3, 5] == 0` only.)

**Revised tests** (only public symbols):

```lean
#guard (KMor1.swap KMor1.add).interp ![3, 7] == 10
#guard (KMor1.swap KMor1.monus).interp ![3, 5] == 0
#guard (KMor1.swap KMor1.monus).interp ![5, 3] == 2  -- WAIT: this fails
```

Wait — `KMor1.swap KMor1.monus` swaps the args. `monus` computes
`ctx 0 - ctx 1`, so `swap monus` computes `ctx 1 - ctx 0`. For
`![3, 5]`: `5 - 3 = 2`. For `![5, 3]`: `3 - 5 = 0`. The test list
should be:

```lean
#guard (KMor1.swap KMor1.add).interp ![3, 7] == 10
#guard (KMor1.swap KMor1.monus).interp ![3, 5] == 2
#guard (KMor1.swap KMor1.monus).interp ![5, 3] == 0
```

- [ ] **Step 2: Build + test clean**

```bash
lake build && lake test
```

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/KArith.lean
git commit -m "Add KMor1.swap utility tests"
```

---

### Task 4.2: Final verification

Confirm the entire branch builds clean, all tests pass, no
warnings, and the new symbols are present.

- [ ] **Step 1: Full build clean**

```bash
lake build
```

Expected: "Build completed successfully (1531+ jobs)" — no warnings.

- [ ] **Step 2: Tests pass**

```bash
lake test
```

Expected: clean.

- [ ] **Step 3: No `sorry`/`admit`/`Classical`/`noncomputable`/`axiom`**

```bash
grep -nE 'sorry|admit|Classical|noncomputable|axiom' \
  GebLean/Utilities/KArith.lean \
  GebLeanTests/Utilities/KArith.lean \
  GebLean/LawvereKSim.lean \
  GebLean/LawvereKSimInterp.lean
```

Expected: empty (or only matches in pre-existing prose docstrings
that mention the keyword as a thing being prohibited, not as a
Lean construct).

- [ ] **Step 4: Markdownlint clean for spec + plan**

```bash
markdownlint-cli2 \
  docs/superpowers/specs/2026-05-05-karith-extensions-design.md \
  docs/superpowers/plans/2026-05-05-karith-extensions-implementation.md
```

Expected: 0 errors.

- [ ] **Step 5: New symbols all present**

Use a shell variable to keep the command under 80 chars:

```bash
PAT='^def KMor1\.(permArgs|swap|eq|condEq|pow)( |:)|'
PAT="$PAT^@\\[simp\\] theorem KMor1\\.(simrecVec_succ_append"
PAT="$PAT|interp_permArgs|interp_swap|interp_eq|interp_condEq"
PAT="$PAT|interp_pow)"
grep -cE "$PAT" \
  GebLean/Utilities/KArith.lean \
  GebLean/LawvereKSim.lean \
  GebLean/LawvereKSimInterp.lean
```

Expected: at least 11 matches (5 def + 6 simp theorem; precise
count depends on file boundaries).

- [ ] **Step 6: Forbidden-style-word scan on the new module**

```bash
PAT='\b(fundamental|actually|key|insight|core|advanced|complex'
PAT="$PAT|complicated|simple|advantage|benefit|important|challenge"
PAT="$PAT|wait|hmm|sorry|careful|difficult|blocked|incomplete"
PAT="$PAT|future|issue|problem|block)\b"
grep -niE "$PAT" GebLean/Utilities/KArith.lean
```

Expected: empty (or only `sorry` inside backtick-quoted Lean
keywords being prohibited).

- [ ] **Step 7: Commit verification record (if any fixes were made)**

```bash
git status  # must be clean if no fixes needed
# If fixes were needed:
git add <files>
git commit -m "Final KArith extensions verification"
```

If no fixes were needed, skip this commit.

- [ ] **Step 8: Final summary**

```bash
git log --oneline worktree-karith-impl ^main | head -20
```

Count the new commits (should be ~14: 2 Phase 0 + 5 Phase 1 + 3
Phase 2 + 3 Phase 3 + 1–2 Phase 4).

---

## Done

Three new public functions (`KMor1.eq`, `KMor1.condEq`, `KMor1.pow`)
plus two utilities (`KMor1.permArgs`, `KMor1.swap`) and one
generalized lemma (`KMor1.simrecVec_succ_append`). The
`interp_rec1_succ` proof is now ~25 lines (down from ~70).
`KMor1.monus` uses `swap` for the arg-order shift. `KMor1.pow`
provides level-2 exponentiation via the Marchenkov/Wikipedia
formula, with correctness proved through two `Nat`-level helpers.
