# Lawvere ER Phase 4f.2: Tetration Non-Elementary Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that tetration is not elementary recursive: there is no
`t : ERMor1 1` whose standard interpretation matches tetration.  Derive
the corresponding non-fullness consequence, giving a witness strictly
between primitive recursion and elementary recursion.

**Architecture:** Mirror the Ackermann proof pattern from
`Mathlib/Computability/Ackermann.lean:267-330`, substituting
`Nat.Primrec` for `ERMor1` and `ack` for a tower-of-twos function.
Build a generic `tower` function with arithmetic lemmas in a utilities
module, prove by structural recursion that every `ERMor1` term is
bounded by some fixed-height tower, and derive the tetration corollary.

**Tech Stack:** Lean 4 + Mathlib
(`Mathlib.Data.Nat.Hyperoperation`,
`Mathlib.Data.Nat.Pow`,
`Mathlib.Algebra.Order.Monoid.Unbundled.Pow`,
`Mathlib.Data.Finset.Lattice.Fold`).

---

## File Structure

Files to create:

- `GebLean/Utilities/Tower.lean` — defines `tower : ℕ → ℕ → ℕ` with
  `tower 0 x = x` and `tower (k+1) x = 2 ^ tower k x`.  Proves
  monotonicity, composition identity, and the multiplicative / power
  bounds needed for the `bsum` / `bprod` cases of the structural
  recursion.
- `GebLean/LawvereERBound.lean` — proves `ERMor1.exists_lt_tower`: every
  ER term's interpretation is strictly less than some fixed tower of
  the context's `sup + 2`.  Structural recursion on `t : ERMor1 n`,
  one case per generator.
- `GebLean/LawvereERTetration.lean` — defines `tetration : ℕ → ℕ :=
  fun n => tower n 1`, relates it to `Nat.hyperoperation 4 2`, and
  derives the non-elementary corollary `¬ ∃ t : ERMor1 1, ∀ x,
  t.interp (fun _ => x) = tetration x`.  Also derives the corresponding
  `erInterpFunctor_not_full` witness at `1 → 1`.
- `GebLeanTests/Utilities/Tower.lean` — sanity `#guard` tests for
  concrete `tower k x` values.
- `GebLeanTests/LawvereERTetration.lean` — sanity tests confirming
  `tetration_not_ER` and its non-fullness derivation type-check.

Files to modify:

- `GebLean/Utilities.lean` — re-export `GebLean.Utilities.Tower`.
- `GebLean.lean` — re-export the two new `GebLean/Lawvere*.lean`
  modules.
- `GebLeanTests.lean` — register the new test modules.
- `.session/workstreams/lawvere-elementary-recursive.md` — mark 4f.2
  complete.

---

## Key Mathlib lemmas the plan assumes

The following Mathlib lemmas will be used below.  If any name has
drifted, search via `mcp__lean-lsp__lean_local_search` or
`mcp__lean-lsp__lean_leansearch` for an equivalent before
substituting a manual proof.

- `Nat.pow_le_pow_right : 1 ≤ a → n ≤ m → a ^ n ≤ a ^ m`
  (power is monotone in exponent when base ≥ 1).
- `Nat.pow_le_pow_left : a ≤ b → a ^ n ≤ b ^ n`
  (power is monotone in base).
- `Nat.one_le_two_pow : 1 ≤ 2 ^ n`.
- `Nat.lt_two_pow_self : n < 2 ^ n` (if not present, prove as a
  local helper in `Tower.lean` by `induction n`).
- `Finset.le_sup : b ∈ s → f b ≤ s.sup f`.
- `Mathlib.Data.Nat.Hyperoperation.hyperoperation`:
  `hyperoperation 4 2 0 = 1`, `hyperoperation 4 2 (k+1) =
  hyperoperation 3 2 (hyperoperation 4 2 k) = 2 ^ hyperoperation 4 2 k`.

---

## Task 1: Stub `Tower.lean` with definition and simp lemmas

**Files:**

- Create: `GebLean/Utilities/Tower.lean`
- Modify: `GebLean/Utilities.lean` (add import)

- [ ] **Step 1: Create the file**

Create `/home/terence/git-workspaces/geb-syntax/geb-lean/GebLean/Utilities/Tower.lean`:

```lean
import Mathlib.Data.Nat.Pow
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Tower of Twos

Iterated exponential `tower k x` applies `fun n => 2 ^ n` to `x` a
total of `k` times.  Used as a bounding function for the elementary
recursive functions: every ER term's interpretation is dominated by a
fixed-height tower applied to the context's maximum (plus a padding
constant).
-/

namespace GebLean

/-- `tower k x` is a tower of `k` twos applied to `x`:
`tower 0 x = x` and `tower (k+1) x = 2 ^ tower k x`. -/
def tower : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => 2 ^ tower k x

@[simp] theorem tower_zero (x : ℕ) : tower 0 x = x := rfl

@[simp] theorem tower_succ (k x : ℕ) :
    tower (k + 1) x = 2 ^ tower k x := rfl

end GebLean
```

- [ ] **Step 2: Register in `GebLean/Utilities.lean`**

Open `GebLean/Utilities.lean` and add `import GebLean.Utilities.Tower`
in alphabetical order with the existing imports.

- [ ] **Step 3: Build**

Run: `lake build GebLean.Utilities.Tower`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Tower.lean GebLean/Utilities.lean
git commit -m "Add tower function for ER bounding argument"
```

---

## Task 2: Monotonicity and `self_le_tower`

**Files:**

- Modify: `GebLean/Utilities/Tower.lean`

- [ ] **Step 1: Add three monotonicity lemmas**

Insert before `end GebLean` in `GebLean/Utilities/Tower.lean`:

```lean
/-- `x ≤ tower k x` for all `k`, `x`. -/
theorem self_le_tower (k x : ℕ) : x ≤ tower k x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    calc x ≤ tower k x := ih
      _ ≤ 2 ^ tower k x := by
        have h : tower k x < 2 ^ tower k x :=
          Nat.lt_two_pow_self
        exact le_of_lt h

/-- `1 ≤ tower k x` whenever `1 ≤ x` (or `k ≥ 1`). -/
theorem one_le_tower_of_one_le (k x : ℕ) (hx : 1 ≤ x) :
    1 ≤ tower k x := le_trans hx (self_le_tower k x)

/-- `tower k` is monotone in its second argument. -/
theorem tower_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) :
    tower k x ≤ tower k y := by
  induction k with
  | zero => exact h
  | succ k ih =>
    exact Nat.pow_le_pow_right (by omega) ih
```

Notes on `Nat.lt_two_pow_self`: if this exact name is not in Mathlib,
search for `Nat.lt_two_pow`, `lt_two_pow_self`, or prove as a local
`private theorem`:

```lean
private theorem nat_lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc n + 1 ≤ 2 * n + 1 := by omega
      _ < 2 * 2 ^ n + 1 := by omega -- needs ih
      _ ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
```

(Fill in the exact `omega` / `linarith` steps as needed.)

- [ ] **Step 2: Build**

Run: `lake build GebLean.Utilities.Tower`
Expected: PASS, no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Tower.lean
git commit -m "Add monotonicity and self-bound lemmas for tower"
```

---

## Task 3: Composition identity for `tower`

**Files:**

- Modify: `GebLean/Utilities/Tower.lean`

- [ ] **Step 1: Add the composition lemma**

Insert before `end GebLean`:

```lean
/-- Composition of towers: applying a height-`j` tower to a
height-`k` tower of `x` equals applying a height-`j+k` tower to `x`. -/
theorem tower_comp (j k x : ℕ) :
    tower j (tower k x) = tower (j + k) x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show 2 ^ tower j (tower k x) = 2 ^ tower (j + k) x
    rw [ih]
    rfl
```

- [ ] **Step 2: Build**

Run: `lake build GebLean.Utilities.Tower`
Expected: PASS, no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Tower.lean
git commit -m "Add tower composition identity"
```

---

## Task 4: Arithmetic bounds for `bsum` and `bprod` cases

**Files:**

- Modify: `GebLean/Utilities/Tower.lean`

These are the non-trivial arithmetic lemmas the structural-recursion
proof will need.  Both use the shift `m ≥ 2`, which is why the main
theorem uses `Finset.sup + 2` as its bounding argument: the `+ 2`
guarantees `m ≥ 2` at the point of use.

- [ ] **Step 1: Prove the power-of-two bound `n ≤ 2 ^ n`**

If `Nat.lt_two_pow_self` is available, this is a one-liner via
`le_of_lt`.  Otherwise, add as a helper:

Insert before the composition lemma:

```lean
/-- `n ≤ 2 ^ n` for all `n`. -/
theorem le_two_pow_self (n : ℕ) : n ≤ 2 ^ n :=
  Nat.le_of_lt (Nat.lt_two_pow_self)
```

- [ ] **Step 2: Add the `bsum` bound**

Insert before `end GebLean`:

```lean
/-- Multiplicative bound: for `m ≥ 2`,
`m * tower k m ≤ tower (k + 1) m`. -/
theorem mul_tower_le_tower_succ {k m : ℕ} (hm : 2 ≤ m) :
    m * tower k m ≤ tower (k + 1) m := by
  -- tower (k+1) m = 2 ^ tower k m
  -- We want m * tower k m ≤ 2 ^ tower k m.
  -- Step 1: m ≤ 2 ^ m since le_two_pow_self, and m ≤ tower k m
  --   (by self_le_tower), so
  --   m * tower k m ≤ (tower k m) * (tower k m) = (tower k m)^2.
  -- Step 2: tower k m ≥ 2 (since m ≥ 2 and self_le_tower),
  --   so 2 * tower k m ≤ (tower k m)^2 ≤ 2 ^ (tower k m)
  --   by using nat_lt_two_pow_self on the exponent.
  -- In practice, stitch via these intermediate lemmas:
  show m * tower k m ≤ 2 ^ tower k m
  have h_m_le : m ≤ tower k m := self_le_tower k m
  have h_tower_ge_two : 2 ≤ tower k m := le_trans hm h_m_le
  -- m * tower k m ≤ tower k m * tower k m = (tower k m)^2
  have h_sq : m * tower k m ≤ tower k m * tower k m :=
    Nat.mul_le_mul_right _ h_m_le
  -- (tower k m)^2 = tower k m * tower k m = 2 * tower k m
  --   when tower k m ≥ 2 ... actually (tower k m)^2 grows faster.
  -- We actually want (tower k m)^2 ≤ 2 ^ tower k m.
  -- Using Nat.sq_lt_two_pow or n^2 ≤ 2^n for n ≥ 4 (proved below).
  sorry
```

The final `sorry` must be eliminated before commit.  The crux
inequality is `n^2 ≤ 2^n` for `n ≥ 4`, which Mathlib may prove as
`Nat.sq_lt_pow_two` or similar; if not, prove it by induction as a
private helper.  Alternatively, weaken to `mul_tower_le_tower_add_two`
(`m * tower k m ≤ tower (k + 2) m`), which is easier via the chain
`m * tower k m ≤ 2^m · 2^(tower k m) = 2^(m + tower k m) ≤
 2^(2 · tower k m) ≤ 2^(2^(tower k m)) = tower (k+2) m`, at the cost of
a larger constant in the main theorem.

**If `mul_tower_le_tower_succ` proves too hard**, replace its body
with:

```lean
theorem mul_tower_le_tower_add_two {k m : ℕ} (hm : 2 ≤ m) :
    m * tower k m ≤ tower (k + 2) m := by
  have h_self : m ≤ tower k m := self_le_tower k m
  have h_two_le : 2 ≤ tower k m := le_trans hm h_self
  show m * tower k m ≤ 2 ^ (2 ^ tower k m)
  have h1 : m * tower k m ≤ 2 ^ m * 2 ^ tower k m := by
    exact Nat.mul_le_mul (le_two_pow_self m)
      (le_two_pow_self (tower k m))
  have h2 : 2 ^ m * 2 ^ tower k m = 2 ^ (m + tower k m) := by
    rw [← pow_add]
  have h3 : m + tower k m ≤ 2 * tower k m := by
    omega
  have h4 : 2 * tower k m ≤ 2 ^ tower k m := by
    calc 2 * tower k m
        ≤ tower k m * tower k m := by
          exact Nat.mul_le_mul_right _ h_two_le
      _ ≤ 2 ^ tower k m := by
        -- n * n ≤ 2 ^ n for n ≥ 2, via le_two_pow_self-style arg
        sorry -- replace with actual proof
  calc m * tower k m
      ≤ 2 ^ (m + tower k m) := by rw [← h2]; exact h1
    _ ≤ 2 ^ (2 * tower k m) :=
        Nat.pow_le_pow_right (by omega) h3
    _ ≤ 2 ^ (2 ^ tower k m) :=
        Nat.pow_le_pow_right (by omega) h4
```

(Adjust this if `Nat.pow_le_pow_right` does not match the expected
signature — the Mathlib lemma is `pow_le_pow_right' : 1 ≤ a → n ≤ m
→ a ^ n ≤ a ^ m`.)

The `sorry` inside `h4` is a small helper: `n * n ≤ 2^n` for `n ≥ 2`.
This is `Nat.sq_le_two_pow` if Mathlib has it, otherwise a 3-line
induction.

**In either case, choose ONE of `mul_tower_le_tower_succ` or
`mul_tower_le_tower_add_two` and drop the other.**  Use the chosen
constant (`+1` or `+2`) consistently in Task 8's `bsum` case.

- [ ] **Step 3: Add the `bprod` bound**

Insert after the sum bound:

```lean
/-- Power bound: for `m ≥ 2`,
`tower k m ^ m ≤ tower (k + 2) m`. -/
theorem tower_pow_le_tower_add_two {k m : ℕ} (hm : 2 ≤ m) :
    tower k m ^ m ≤ tower (k + 2) m := by
  -- tower (k+2) m = 2 ^ (2 ^ tower k m)
  -- (tower k m)^m = 2 ^ (m * log2 (tower k m))?  No.
  -- Cleaner: (tower k m)^m ≤ (2 ^ tower k m)^m
  --   = 2 ^ (m * tower k m) ≤ 2 ^ (tower (k+1) m) = tower (k+2) m
  -- where the last step uses mul_tower_le_tower_succ or the
  -- equivalent +2 variant.  Adjust the chain if using
  -- mul_tower_le_tower_add_two instead (then increase to +3).
  show tower k m ^ m ≤ 2 ^ (2 ^ tower k m)
  have h_self : m ≤ tower k m := self_le_tower k m
  have h_tower_le_pow : tower k m ≤ 2 ^ tower k m :=
    le_two_pow_self _
  calc tower k m ^ m
      ≤ (2 ^ tower k m) ^ m :=
        Nat.pow_le_pow_left h_tower_le_pow _
    _ = 2 ^ (tower k m * m) := by rw [← pow_mul]
    _ ≤ 2 ^ (tower k m * tower k m) :=
        Nat.pow_le_pow_right (by omega)
          (Nat.mul_le_mul_left _ h_self)
    _ ≤ 2 ^ (2 ^ tower k m) := by
        apply Nat.pow_le_pow_right (by omega)
        -- Need: tower k m * tower k m ≤ 2 ^ tower k m,
        -- i.e., n * n ≤ 2^n for n ≥ 2.  Uses same helper as
        -- mul_tower case.
        sorry -- replace with actual proof
```

The `sorry` is the same `n * n ≤ 2^n for n ≥ 2` lemma used in the
`bsum` bound.  Extract it once, reuse twice:

Add (before the bounds, after `le_two_pow_self`):

```lean
/-- `n * n ≤ 2 ^ n` for `n ≥ 2`. -/
theorem sq_le_two_pow {n : ℕ} (hn : 2 ≤ n) : n * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    -- 2 ^ (n+1) = 2 * 2^n ≥ 2 * n * n = n * n + n * n
    -- and (n+1)*(n+1) = n * n + 2 * n + 1
    -- So need n * n ≥ 2 * n + 1, i.e., n * (n - 2) ≥ 1,
    -- which holds for n ≥ 3.  Base case n=2 hand-checked.
    sorry -- fill in; small induction step
```

(The implementer may need to adjust the induction base / step
precisely; the key is that for `n ≥ 2`, `n * n ≤ 2^n`.)

- [ ] **Step 4: Build and verify no `sorry`**

Run: `lake build GebLean.Utilities.Tower`
Expected: PASS, no warnings, no `sorry`.

If any case resists, try a larger constant shift (`+3`, `+4`) in
the main theorem.  What matters is that SOME fixed constant exists;
the exact value doesn't affect the Phase 4f.2 conclusion.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/Tower.lean
git commit -m "Add multiplicative and power bounds for tower"
```

---

## Task 5: Stub `LawvereERBound.lean` with base cases

**Files:**

- Create: `GebLean/LawvereERBound.lean`

This file proves `ERMor1.exists_lt_tower`: every ER term is bounded by
a fixed tower applied to the context's `sup + 2`.  Structure parallels
`GebLean/LawvereERPrimrec.lean`.

- [ ] **Step 1: Write the file with imports, namespace, helpers, and
  base cases (comp/bsum/bprod use `sorry` placeholders, DO NOT
  commit)**

```lean
import GebLean.LawvereER
import GebLean.Utilities.Tower
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Tower Bound for Elementary Recursive Terms

Every `ERMor1 n` term's interpretation is dominated by a fixed-height
tower of twos applied to the context's maximum (plus padding).  This
witnesses that the elementary recursive functions are a strict subset
of the primitive recursive functions — tetration escapes this bound.
-/

namespace GebLean

/-- Maximum entry of a context, returning 0 when the context is
empty. -/
def maxCtx {n : ℕ} (ctx : Fin n → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup ctx

/-- Each context entry is bounded by `maxCtx`. -/
theorem le_maxCtx {n : ℕ} (ctx : Fin n → ℕ) (i : Fin n) :
    ctx i ≤ maxCtx ctx :=
  Finset.le_sup (f := ctx) (Finset.mem_univ i)

/-- `2 ≤ maxCtx ctx + 2` holds unconditionally. -/
theorem two_le_maxCtx_plus_two {n : ℕ} (ctx : Fin n → ℕ) :
    2 ≤ maxCtx ctx + 2 := by omega

/-- The bounding theorem: every ER term's interpretation is strictly
below some fixed tower of the context's `sup + 2`.  The structural
recursion proceeds by induction on `t : ERMor1 n`; each case produces
a concrete height constant. -/
theorem ERMor1.exists_lt_tower :
    ∀ {n : ℕ} (t : ERMor1 n),
      ∃ k : ℕ, ∀ ctx : Fin n → ℕ,
        t.interp ctx < tower k (maxCtx ctx + 2)
  | _, ERMor1.zero => by
    refine ⟨0, fun ctx => ?_⟩
    show (0 : ℕ) < maxCtx ctx + 2
    omega
  | _, ERMor1.succ => by
    refine ⟨0, fun ctx => ?_⟩
    show (ctx 0).succ < maxCtx ctx + 2
    have h := le_maxCtx ctx 0
    omega
  | _, ERMor1.proj i => by
    refine ⟨0, fun ctx => ?_⟩
    show ctx i < maxCtx ctx + 2
    have h := le_maxCtx ctx i
    omega
  | _, ERMor1.sub => by
    refine ⟨0, fun ctx => ?_⟩
    show ctx 0 - ctx 1 < maxCtx ctx + 2
    have h := le_maxCtx ctx 0
    omega
  | _, ERMor1.comp f g => by
    sorry  -- Task 6
  | _, ERMor1.bsum f => by
    sorry  -- Task 7
  | _, ERMor1.bprod f => by
    sorry  -- Task 8

end GebLean
```

The `sorry` placeholders must be eliminated by Tasks 6-8 before
committing this file.

- [ ] **Step 2: Verify base cases compile (sorry warnings expected
  only in comp/bsum/bprod)**

Run: `lake build GebLean.LawvereERBound`
Expected: FAIL with three `sorry` warnings, nothing else.

Do **not** commit at this step.  Proceed directly to Task 6.

---

## Task 6: Fill `comp` case

**Files:**

- Modify: `GebLean/LawvereERBound.lean`

The `comp` case receives `f : ERMor1 k` and `g : Fin k → ERMor1 n`, and
inductive hypotheses `toPrimrec'` analog: for each, an existentially-
quantified tower height.

Strategy: let `k_f` witness `f`'s bound and `K` dominate `max_i k_{g i}`
(use `Finset.univ.sup` over `Fin k`).  For every context `ctx : Fin n
→ ℕ`, the vector `inner_ctx := fun i => (g i).interp ctx` satisfies
`maxCtx inner_ctx ≤ tower K (maxCtx ctx + 2) - 1`, so `maxCtx inner_ctx
+ 2 ≤ tower K (maxCtx ctx + 2) + 1 ≤ tower (K+1) (maxCtx ctx + 2)`
(use the `+1` step by `tower_mono_left` or `self_le_tower`-style
comparison).  Then `f.interp inner_ctx < tower k_f (maxCtx inner_ctx +
2) ≤ tower k_f (tower (K+1) (maxCtx ctx + 2)) = tower (k_f + K + 1)
(maxCtx ctx + 2)` by `tower_comp`.  Witness: `k_f + K + 1`.

- [ ] **Step 1: Replace the `comp` case `sorry`**

```lean
  | _, ERMor1.comp (k := kf) f g => by
    -- Obtain f's bound
    obtain ⟨k_f, h_f⟩ := f.exists_lt_tower
    -- Obtain a uniform bound K over all g i's
    have ⟨K, h_K⟩ :
        ∃ K, ∀ i : Fin kf, ∃ k_i, k_i ≤ K ∧
          ∀ ctx, (g i).interp ctx < tower k_i
            (maxCtx ctx + 2) := by
      -- Extract each g i's existential, take the sup.
      -- Use Finset.univ.sup over Fin kf, and
      -- Classical-free collection via vector construction.
      sorry
    refine ⟨k_f + K + 1, fun ctx => ?_⟩
    show f.interp (fun i => (g i).interp ctx) <
      tower (k_f + K + 1) (maxCtx ctx + 2)
    -- ... detailed bound chain using h_f, h_K,
    -- tower_comp, tower_mono_right, le_two_pow_self
    sorry
```

Note: the "collection of existentials" step (gathering each `g i`'s
bound into a uniform `K`) is the main sub-obligation.  In
constructive Lean this is done via structural induction on `kf`,
accumulating the max.

Implement this collector as a separate helper (placed above
`exists_lt_tower` in the same file):

```lean
/-- Given a family `g : Fin k → ERMor1 n` with per-component bounds,
produce a single uniform height dominating all of them. -/
theorem ERMor1.finFamily_uniform_tower {k n : ℕ}
    (g : Fin k → ERMor1 n) :
    ∃ K : ℕ, ∀ i : Fin k, ∀ ctx : Fin n → ℕ,
      (g i).interp ctx < tower K (maxCtx ctx + 2) := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    intro i
    exact i.elim0
  | succ k ih =>
    obtain ⟨K', hK'⟩ := ih (fun i => g i.succ)
    obtain ⟨k_0, hk_0⟩ := (g 0).exists_lt_tower
    refine ⟨max K' k_0, ?_⟩
    intro i ctx
    refine Fin.cases ?_ ?_ i
    · -- i = 0
      exact lt_of_lt_of_le (hk_0 ctx)
        (tower_mono_left (le_max_right _ _) _)
    · -- i = j.succ
      intro j
      exact lt_of_lt_of_le (hK' j ctx)
        (tower_mono_left (le_max_left _ _) _)
```

This requires a `tower_mono_left` lemma.  If it is not already in
`Tower.lean`, add it there with the following statement (and minimal
proof):

```lean
/-- `tower` is monotone in its first argument when the second is
at least 1. -/
theorem tower_mono_left {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (x : ℕ)
    (hx : 1 ≤ x) : tower k₁ x ≤ tower k₂ x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    exact le_trans ih (le_two_pow_self _)
```

(Check that `tower k x ≤ 2 ^ tower k x = tower (k+1) x`.)

If `1 ≤ x` isn't enforceable in the uniform collector (it isn't —
`maxCtx ctx + 2 ≥ 2 > 1` always), simply pass `by omega` at the call
site.

- [ ] **Step 2: Fill in the main `comp` case bound chain**

Using the uniform collector and `tower_comp`:

```lean
  | _, ERMor1.comp (k := kf) f g => by
    obtain ⟨k_f, h_f⟩ := f.exists_lt_tower
    obtain ⟨K, h_K⟩ := ERMor1.finFamily_uniform_tower g
    refine ⟨k_f + K + 1, fun ctx => ?_⟩
    show f.interp (fun i => (g i).interp ctx) <
      tower (k_f + K + 1) (maxCtx ctx + 2)
    -- Step A: inner_ctx := fun i => (g i).interp ctx.
    -- maxCtx inner_ctx ≤ sup of bounds, which is
    -- tower K (maxCtx ctx + 2).
    have h_inner_max : maxCtx (fun i => (g i).interp ctx)
        ≤ tower K (maxCtx ctx + 2) := by
      -- For each i, (g i).interp ctx < tower K (maxCtx ctx + 2),
      -- so ≤ tower K (maxCtx ctx + 2) - 1 when positive,
      -- or ≤ tower K (maxCtx ctx + 2).  Use Finset.sup_le with
      -- Nat.le_of_lt.
      apply Finset.sup_le
      intro i _
      exact Nat.le_of_lt (h_K i ctx)
    -- Step B: f.interp inner_ctx < tower k_f
    --   (maxCtx inner_ctx + 2)
    --   ≤ tower k_f (tower K (maxCtx ctx + 2) + 2)
    --   ≤ tower k_f (tower (K+1) (maxCtx ctx + 2))
    --   = tower (k_f + K + 1) (maxCtx ctx + 2).
    have h_f_applied := h_f (fun i => (g i).interp ctx)
    calc f.interp (fun i => (g i).interp ctx)
        < tower k_f (maxCtx (fun i => (g i).interp ctx) + 2) :=
          h_f_applied
      _ ≤ tower k_f (tower K (maxCtx ctx + 2) + 2) :=
          tower_mono_right _ (by omega)
      _ ≤ tower k_f (tower (K + 1) (maxCtx ctx + 2)) := by
          apply tower_mono_right
          -- Need: tower K m + 2 ≤ tower (K+1) m for m ≥ 2.
          -- tower (K+1) m = 2 ^ tower K m ≥ tower K m + 2
          -- when tower K m ≥ 2.
          sorry
      _ = tower (k_f + K + 1) (maxCtx ctx + 2) := by
          rw [tower_comp]
          ring
```

The remaining `sorry` is `tower K m + 2 ≤ tower (K+1) m` for
`m ≥ 2`.  Sub-proof: `tower (K+1) m = 2 ^ tower K m`, and we need
`tower K m + 2 ≤ 2 ^ tower K m`.  Since `tower K m ≥ 2` (by
`self_le_tower` and `m ≥ 2`), `2 ^ tower K m ≥ 2 ^ 2 = 4 ≥
tower K m + 2` when `tower K m ≤ 2`.  For `tower K m ≥ 3`, use
`Nat.lt_two_pow_self` giving `tower K m < 2 ^ tower K m`, i.e.,
`tower K m + 1 ≤ 2 ^ tower K m`, and then check `+2` case by
case or bootstrap from `n + 2 ≤ 2^n` for `n ≥ 2`.

Add a helper in `Tower.lean`:

```lean
theorem add_two_le_two_pow {n : ℕ} (hn : 2 ≤ n) :
    n + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    -- 2^(n+1) = 2 * 2^n ≥ 2 * (n+2) = 2n + 4 ≥ (n+1) + 2
    --   for n ≥ 2.
    calc (n + 1) + 2 = n + 2 + 1 := by ring
      _ ≤ 2 ^ n + 1 := by omega
      _ ≤ 2 ^ n + 2 ^ n := by
          have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
```

Then the inner sorry becomes:

```lean
          have h_tower_ge_two : 2 ≤ tower K (maxCtx ctx + 2) :=
            le_trans (two_le_maxCtx_plus_two ctx)
              (self_le_tower K (maxCtx ctx + 2))
          exact add_two_le_two_pow h_tower_ge_two
```

- [ ] **Step 3: Verify (bsum/bprod still sorry)**

Run: `lake build GebLean.LawvereERBound`
Expected: FAIL with `sorry` warnings only in `bsum` and `bprod`.

Do not commit yet.

---

## Task 7: Fill `bsum` case

**Files:**

- Modify: `GebLean/LawvereERBound.lean`

Strategy: let `k_f` witness `f`'s bound.  For arity `k+1`,
`(bsum f).interp ctx = natBSum (ctx 0) (fun i => f.interp
(Fin.cons i (Fin.tail ctx)))`.

The outer sum over `i : Fin (ctx 0)` yields `≤ (ctx 0) * (max over
i of inner)`.  Each inner `f.interp (Fin.cons i (Fin.tail ctx))` is
bounded by `tower k_f (maxCtx (Fin.cons i (Fin.tail ctx)) + 2)`.
Since `Fin.cons i (Fin.tail ctx)` at index 0 is `i < ctx 0 ≤
maxCtx ctx`, and at positive indices is `ctx (j+1) ≤ maxCtx ctx`,
we have `maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx`.  So
inner ≤ `tower k_f (maxCtx ctx + 2)`.

Overall:
`natBSum (ctx 0) _ ≤ (ctx 0) * tower k_f (maxCtx ctx + 2)
 ≤ (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2)
 ≤ tower (k_f + 1) (maxCtx ctx + 2)`
using `mul_tower_le_tower_succ` (or `_add_two` — match Task 4's choice).

Witness: `k_f + 1` (or `k_f + 2`, matching Task 4).

- [ ] **Step 1: Add a `natBSum` bound helper**

Insert in `GebLean/LawvereERBound.lean`, above the main theorem:

```lean
/-- Bounded sum is dominated by bound times max entry. -/
theorem natBSum_le_mul_max (b : ℕ) (f : ℕ → ℕ) (M : ℕ)
    (h : ∀ i < b, f i ≤ M) : natBSum b f ≤ b * M := by
  induction b with
  | zero => simp [natBSum]
  | succ b ih =>
    show natBSum b f + f b ≤ (b + 1) * M
    have h_b_lt : b < b + 1 := Nat.lt_succ_self _
    have h_fb : f b ≤ M := h b h_b_lt
    have h_ih_applied : natBSum b f ≤ b * M :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    calc natBSum b f + f b
        ≤ b * M + M := by omega
      _ = (b + 1) * M := by ring
```

Check that `natBSum` unfolds matches expectations; if not, adjust the
`show` in the inductive step.

- [ ] **Step 2: Add a helper bounding `maxCtx (Fin.cons i (Fin.tail
  ctx))`**

Insert above the main theorem:

```lean
/-- Consing a bounded element onto a context tail preserves the
ambient max bound. -/
theorem maxCtx_cons_le {n : ℕ} (i : ℕ) (ctx : Fin (n + 1) → ℕ)
    (hi : i ≤ maxCtx ctx) :
    maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx := by
  apply Finset.sup_le
  intro j _
  refine Fin.cases ?_ ?_ j
  · exact hi
  · intro j'
    show ctx j'.succ ≤ maxCtx ctx
    exact le_maxCtx ctx _
```

Adjust the show/Fin.cases pattern to match `Fin.cons_zero` /
`Fin.cons_succ` as needed.

- [ ] **Step 3: Replace the `bsum` case `sorry`**

```lean
  | _, ERMor1.bsum (k := k) f => by
    obtain ⟨k_f, h_f⟩ := f.exists_lt_tower
    refine ⟨k_f + 1, fun ctx => ?_⟩
    show natBSum (ctx 0) (fun i =>
      f.interp (Fin.cons i (Fin.tail ctx))) <
      tower (k_f + 1) (maxCtx ctx + 2)
    -- Bound each inner term uniformly
    have h_inner : ∀ i < ctx 0,
        f.interp (Fin.cons i (Fin.tail ctx))
          ≤ tower k_f (maxCtx ctx + 2) := by
      intro i hi
      have hi_le : i ≤ maxCtx ctx :=
        le_trans (Nat.le_of_lt hi) (le_maxCtx ctx 0)
      have h_max_le :
          maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx :=
        maxCtx_cons_le i ctx hi_le
      have h_applied := h_f (Fin.cons i (Fin.tail ctx))
      calc f.interp (Fin.cons i (Fin.tail ctx))
          < tower k_f (maxCtx
              (Fin.cons i (Fin.tail ctx)) + 2) := h_applied
        _ ≤ tower k_f (maxCtx ctx + 2) :=
            tower_mono_right _ (by omega)
    -- Sum bound
    have h_sum : natBSum (ctx 0) (fun i =>
          f.interp (Fin.cons i (Fin.tail ctx)))
        ≤ ctx 0 * tower k_f (maxCtx ctx + 2) :=
      natBSum_le_mul_max (ctx 0) _ _ h_inner
    -- Finalize via mul bound
    have h_ctx_le : ctx 0 ≤ maxCtx ctx + 2 := by
      have := le_maxCtx ctx 0; omega
    have h_mul_le :
        ctx 0 * tower k_f (maxCtx ctx + 2)
          ≤ (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2) :=
      Nat.mul_le_mul_right _ h_ctx_le
    have h_bound :
        (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2)
          ≤ tower (k_f + 1) (maxCtx ctx + 2) :=
      mul_tower_le_tower_succ (two_le_maxCtx_plus_two ctx)
    -- Strict inequality via ctx 0 < maxCtx ctx + 2 or similar
    calc natBSum (ctx 0) _
        ≤ ctx 0 * tower k_f (maxCtx ctx + 2) := h_sum
      _ ≤ (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2) :=
          h_mul_le
      _ ≤ tower (k_f + 1) (maxCtx ctx + 2) := h_bound
      _ < tower (k_f + 1) (maxCtx ctx + 2) + 1 := by omega
      -- The above gives ≤, but we need <.  Strengthen by
      -- observing natBSum (ctx 0) _ < tower (k_f+1) _ via
      -- the strict h_applied at some i, or just add a cushion
      -- by increasing k_f + 1 to k_f + 2 — adjust witness.
      _ ≤ tower (k_f + 1) (maxCtx ctx + 2) := sorry
```

The final strict-vs-nonstrict gap is the trickiest bookkeeping
here.  If converting `≤` to `<` proves awkward, **change the witness
to `k_f + 2`** and use the stronger `tower_mono_left` gap to pad the
strict inequality.  Concretely:

```lean
    -- Witness is k_f + 2 for strict inequality
    refine ⟨k_f + 2, fun ctx => ?_⟩
    ...
    calc natBSum (ctx 0) _
        ≤ (maxCtx ctx + 2) * tower k_f (maxCtx ctx + 2) := ...
      _ ≤ tower (k_f + 1) (maxCtx ctx + 2) :=
          mul_tower_le_tower_succ ...
      _ < tower (k_f + 2) (maxCtx ctx + 2) := by
          -- tower (k+2) x = 2^(tower (k+1) x) > tower (k+1) x
          exact Nat.lt_two_pow_self
```

Prefer the `k_f + 2` witness — it's cleaner.

If `mul_tower_le_tower_succ` was weakened to
`mul_tower_le_tower_add_two` in Task 4, use witness `k_f + 3`
correspondingly.

- [ ] **Step 4: Verify (bprod still sorry)**

Run: `lake build GebLean.LawvereERBound`
Expected: FAIL with `sorry` warning only in `bprod`.

Do not commit.

---

## Task 8: Fill `bprod` case and commit

**Files:**

- Modify: `GebLean/LawvereERBound.lean`

Structurally identical to `bsum` but with multiplication instead of
addition, bounded above by `max^bound` instead of `bound * max`.  Uses
`tower_pow_le_tower_add_two` from Task 4.

- [ ] **Step 1: Add a `natBProd` bound helper**

Insert above the main theorem, near the `natBSum_le_mul_max`:

```lean
/-- Bounded product is dominated by max entry raised to bound. -/
theorem natBProd_le_pow_max (b : ℕ) (f : ℕ → ℕ) (M : ℕ)
    (h : ∀ i < b, f i ≤ M) : natBProd b f ≤ M ^ b := by
  induction b with
  | zero => simp [natBProd]
  | succ b ih =>
    show natBProd b f * f b ≤ M ^ (b + 1)
    have h_fb : f b ≤ M := h b (Nat.lt_succ_self _)
    have h_ih : natBProd b f ≤ M ^ b :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    calc natBProd b f * f b
        ≤ M ^ b * M := Nat.mul_le_mul h_ih h_fb
      _ = M ^ (b + 1) := by rw [pow_succ]
```

- [ ] **Step 2: Replace the `bprod` case `sorry`**

```lean
  | _, ERMor1.bprod (k := k) f => by
    obtain ⟨k_f, h_f⟩ := f.exists_lt_tower
    refine ⟨k_f + 3, fun ctx => ?_⟩
    show natBProd (ctx 0) (fun i =>
      f.interp (Fin.cons i (Fin.tail ctx))) <
      tower (k_f + 3) (maxCtx ctx + 2)
    have h_inner : ∀ i < ctx 0,
        f.interp (Fin.cons i (Fin.tail ctx))
          ≤ tower k_f (maxCtx ctx + 2) := by
      intro i hi
      have hi_le : i ≤ maxCtx ctx :=
        le_trans (Nat.le_of_lt hi) (le_maxCtx ctx 0)
      have h_max_le :
          maxCtx (Fin.cons i (Fin.tail ctx)) ≤ maxCtx ctx :=
        maxCtx_cons_le i ctx hi_le
      have h_applied := h_f (Fin.cons i (Fin.tail ctx))
      calc f.interp (Fin.cons i (Fin.tail ctx))
          < tower k_f (maxCtx
              (Fin.cons i (Fin.tail ctx)) + 2) := h_applied
        _ ≤ tower k_f (maxCtx ctx + 2) :=
            tower_mono_right _ (by omega)
    have h_prod : natBProd (ctx 0) (fun i =>
          f.interp (Fin.cons i (Fin.tail ctx)))
        ≤ tower k_f (maxCtx ctx + 2) ^ (ctx 0) :=
      natBProd_le_pow_max (ctx 0) _ _ h_inner
    have h_ctx_le : ctx 0 ≤ maxCtx ctx + 2 := by
      have := le_maxCtx ctx 0; omega
    have h_pow_le :
        tower k_f (maxCtx ctx + 2) ^ (ctx 0)
          ≤ tower k_f (maxCtx ctx + 2) ^ (maxCtx ctx + 2) :=
      Nat.pow_le_pow_right
        (one_le_tower_of_one_le _ _ (by omega)) h_ctx_le
    have h_bound :
        tower k_f (maxCtx ctx + 2) ^ (maxCtx ctx + 2)
          ≤ tower (k_f + 2) (maxCtx ctx + 2) :=
      tower_pow_le_tower_add_two
        (two_le_maxCtx_plus_two ctx)
    calc natBProd (ctx 0) _
        ≤ tower k_f (maxCtx ctx + 2) ^ (ctx 0) := h_prod
      _ ≤ tower k_f (maxCtx ctx + 2) ^ (maxCtx ctx + 2) :=
          h_pow_le
      _ ≤ tower (k_f + 2) (maxCtx ctx + 2) := h_bound
      _ < tower (k_f + 3) (maxCtx ctx + 2) := by
          show _ < 2 ^ tower (k_f + 2) (maxCtx ctx + 2)
          exact Nat.lt_two_pow_self
```

- [ ] **Step 3: Build full project**

Run: `lake build`
Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 4: Register in `GebLean.lean`**

Open `GebLean.lean` and add `import GebLean.LawvereERBound` after the
`GebLean.LawvereERArith` / `GebLean.LawvereERPrimrec` imports (pick
correct alphabetical position).

- [ ] **Step 5: Build full project (verifies registration)**

Run: `lake build`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add GebLean/LawvereERBound.lean GebLean.lean
git commit -m "Prove every ER term's interpretation is tower-bounded"
```

---

## Task 9: Tetration non-elementary corollary

**Files:**

- Create: `GebLean/LawvereERTetration.lean`

- [ ] **Step 1: Write the file**

```lean
import GebLean.LawvereERBound
import GebLean.LawvereERInterp
import GebLean.LawvereERQuot
import Mathlib.Data.Nat.Hyperoperation

/-!
# Tetration is Not Elementary Recursive

The tower-bounding theorem from `LawvereERBound.lean` immediately
gives a negative result for tetration.  Since tetration `n ↦
hyperoperation 4 2 n` coincides with `n ↦ tower n 1`, and no fixed-
height tower can dominate it, no `ERMor1 1` term can compute
tetration.  This strengthens the Ackermann-based non-fullness from
Phase 4f.1 by exhibiting a primitive-recursive-but-not-elementary
witness.
-/

namespace GebLean

/-- Tetration of base 2 at height `n`: a tower of `n` twos applied
to 1.  Equivalent to `Nat.hyperoperation 4 2 n`. -/
def tetration (n : ℕ) : ℕ := tower n 1

/-- Tetration agrees with `hyperoperation 4 2`. -/
theorem tetration_eq_hyperoperation (n : ℕ) :
    tetration n = Nat.hyperoperation 4 2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 2 ^ tower n 1 = Nat.hyperoperation 4 2 (n + 1)
    -- Unfold one step of hyperoperation 4:
    -- hyperoperation 4 2 (n+1)
    --   = hyperoperation 3 2 (hyperoperation 4 2 n)
    --   = 2 ^ hyperoperation 4 2 n
    -- Use Mathlib's hyperoperation_succ and hyperop 3 = pow.
    rw [← ih]
    -- hyperoperation 4 2 (n+1) = 2 ^ (hyperoperation 4 2 n)
    --   = 2 ^ tetration n = 2 ^ tower n 1
    sorry -- fill via Mathlib's hyperoperation_four_succ or
          -- equivalent, plus hyperoperation_three_eq_pow
```

Implementation note: the exact Mathlib names for the `hyperoperation
4` step (`hyperoperation 4 m (k+1) = m ^^ (k+1)` type lemmas) may be
`Nat.hyperoperation_four_succ` and `Nat.hyperoperation_three_eq_pow`.
Search if different.  If Mathlib only provides `hyperoperation_succ`
(the generic unfold), chain:

```lean
    rw [← ih, Nat.hyperoperation]
    -- reduce to 2 ^ tower n 1 = 2 ^ (hyperoperation 4 2 n)
    congr 1
    exact ih.symm  -- or use ih directly if orientation matches
```

The point is to unwrap one `hyperoperation` recursion.  Adjust as
needed from the actual Mathlib API.

- [ ] **Step 2: Add the key growth lemma**

Insert before `end GebLean`:

```lean
/-- Tetration outgrows any fixed-height tower: for any `K`, there
is some argument (`2K + 2`) where tetration strictly exceeds
`tower K (· + 2)`. -/
theorem tetration_gt_fixed_tower (K : ℕ) :
    tower K ((2 * K + 2) + 2) ≤ tetration (2 * K + 2) := by
  -- tetration (2K+2) = tower (2K+2) 1 = tower K (tower (K+2) 1)
  --   by tower_comp
  -- We need tower K (2K+4) ≤ tower K (tower (K+2) 1),
  -- i.e., 2K+4 ≤ tower (K+2) 1.
  -- tower (K+2) 1 ≥ 2 ^ (K+2) ≥ 2 * (K+2) = 2K + 4.
  show tower K (2 * K + 4) ≤ tower (2 * K + 2) 1
  have h_comp : tower (2 * K + 2) 1 = tower K (tower (K + 2) 1) := by
    rw [← tower_comp]
    congr 1
    ring
  rw [h_comp]
  apply tower_mono_right
  -- Goal: 2K + 4 ≤ tower (K+2) 1
  -- tower (K+2) 1 ≥ 2 ^ (K+2)  (by self_le_tower cascading)
  -- 2 ^ (K+2) ≥ 2*(K+2) = 2K + 4
  have h_tower_ge_pow : 2 ^ (K + 2) ≤ tower (K + 2) 1 := by
    -- Prove by induction or use le_two_pow_self chain.
    sorry
  have h_pow_ge : 2 * K + 4 ≤ 2 ^ (K + 2) := by
    -- 2 * n ≤ 2 ^ n for n ≥ 0; here n = K + 2.
    sorry
  exact le_trans h_pow_ge h_tower_ge_pow
```

Both `sorry`s are short self-contained arithmetic facts:

1. `2 ^ (K+2) ≤ tower (K+2) 1`.  Prove by induction on `K+2`:
   base `K+2 = 0` (trivial), step `2^(k+1) = 2 * 2^k ≤
   2^(tower k 1) = tower (k+1) 1` using `2 * 2^k ≤ 2^(2^k)` for
   `2^k ≥ 2`, i.e., `k ≥ 1`.  Package as a helper in `Tower.lean`:
   ```lean
   theorem two_pow_le_tower_one (k : ℕ) : 2 ^ k ≤ tower k 1 := by
     induction k with
     | zero => decide
     | succ k ih =>
       show 2 ^ (k + 1) ≤ 2 ^ tower k 1
       exact Nat.pow_le_pow_right (by omega)
         (le_trans ih (self_le_tower 0 _))
   ```
2. `2n ≤ 2^n` for `n ≥ 0`.  Standard; use `Nat.mul_le_pow` or prove:
   ```lean
   theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
     induction n with
     | zero => decide
     | succ n ih =>
       calc 2 * (n + 1) = 2 * n + 2 := by ring
         _ ≤ 2 ^ n + 2 := by omega
         _ ≤ 2 ^ n + 2 ^ n := by
             have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
             -- need 2 ≤ 2^n when n ≥ 1, adjust base case
             sorry
         _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
   ```
   (The base case `n = 0` gives `0 ≤ 1`, fine.  The step's
   arithmetic may need adjustment — use `Nat.mul_le_pow` from
   Mathlib if available.)

Add both helpers to `GebLean/Utilities/Tower.lean` (not in
`LawvereERTetration.lean`).

- [ ] **Step 3: Prove the main non-elementary theorem**

Append to `GebLean/LawvereERTetration.lean`:

```lean
/-- Tetration is not elementary recursive: no `ERMor1 1` term
computes it. -/
theorem tetration_not_ER :
    ¬ ∃ t : ERMor1 1, ∀ x : ℕ,
      t.interp (fun _ => x) = tetration x := by
  rintro ⟨t, ht⟩
  obtain ⟨K, hK⟩ := t.exists_lt_tower
  -- Specialize to x = 2K + 2
  have h1 := hK (fun _ => 2 * K + 2)
  -- t.interp (fun _ => 2K+2) = tetration (2K+2)
  rw [ht (2 * K + 2)] at h1
  -- maxCtx of constant function (fun _ : Fin 1 => 2K+2) = 2K+2
  have h_maxCtx : maxCtx (fun _ : Fin 1 => 2 * K + 2)
      = 2 * K + 2 := by
    unfold maxCtx
    -- Finset.univ.sup (constant) = that constant, for nonempty
    -- Finset.  For Fin 1, the sup of a const is the const.
    simp [Finset.sup_const] -- or equivalent
  rw [h_maxCtx] at h1
  -- h1 : tetration (2K+2) < tower K (2K+4)
  have h2 := tetration_gt_fixed_tower K
  -- h2 : tower K (2K+4) ≤ tetration (2K+2)
  omega
```

- [ ] **Step 4: Derive non-fullness via tetration**

Append:

```lean
/-- `ackHom`'s tetration analog: the function `(Fin 1 → ℕ) → (Fin 1
→ ℕ)` that maps the single entry to its tetration. -/
def tetrationHom : (Fin 1 → ℕ) → (Fin 1 → ℕ) :=
  fun ctx _ => tetration (ctx 0)

/-- `erInterpFunctor` is not full, witnessed by tetration at
`1 → 1`.  (Phase 4f.1 already proved this via Ackermann at
`2 → 1`; tetration gives a stronger witness since it is primitive
recursive but not elementary.) -/
theorem erInterpFunctor_not_full_via_tetration :
    ¬ erInterpFunctor.Full := by
  intro hfull
  have hsurj := Functor.map_surjective
    (F := erInterpFunctor)
    (X := (1 : ℕ)) (Y := (1 : ℕ))
  obtain ⟨f, hf⟩ := hsurj tetrationHom
  obtain ⟨f_raw, hfr⟩ :=
    Quotient.exists_rep (s := erMorNSetoid 1 1) f
  have hinterp : ∀ ctx : Fin 1 → ℕ,
      f_raw.interp ctx = tetrationHom ctx := by
    intro ctx
    have hmap : erInterpFunctor.map f = ERMorNQuo.interp f := rfl
    rw [hmap, ← hfr] at hf
    have := congrFun hf ctx
    simp only [ERMorNQuo.interp, Quotient.lift_mk] at this
    exact this
  apply tetration_not_ER
  refine ⟨f_raw 0, ?_⟩
  intro x
  have h := congrFun (hinterp (fun _ => x)) 0
  simp only [ERMorN.interp, tetrationHom] at h
  exact h

end GebLean
```

- [ ] **Step 5: Register in `GebLean.lean`**

Add `import GebLean.LawvereERTetration` after `LawvereERBound`.

- [ ] **Step 6: Build**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereERTetration.lean GebLean.lean
git commit -m "Prove tetration is not elementary recursive"
```

---

## Task 10: Sanity tests

**Files:**

- Create: `GebLeanTests/Utilities/Tower.lean`
- Create: `GebLeanTests/LawvereERTetration.lean`
- Modify: `GebLeanTests.lean` (add two imports)

- [ ] **Step 1: Write `Tower.lean` tests**

Create `/home/terence/git-workspaces/geb-syntax/geb-lean/GebLeanTests/Utilities/Tower.lean`:

```lean
import GebLean.Utilities.Tower

/-!
# Tests for tower function

Sanity tests for the iterated-exponential `tower` function.
-/

open GebLean

-- tower 0 x = x
#guard tower 0 5 = 5

-- tower 1 x = 2 ^ x
#guard tower 1 3 = 8

-- tower 2 3 = 2 ^ (2 ^ 3) = 2 ^ 8 = 256
#guard tower 2 3 = 256

-- tower 3 1 = 2 ^ (2 ^ (2 ^ 1)) = 2 ^ (2 ^ 2) = 2 ^ 4 = 16
#guard tower 3 1 = 16
```

- [ ] **Step 2: Write tetration tests**

Create `/home/terence/git-workspaces/geb-syntax/geb-lean/GebLeanTests/LawvereERTetration.lean`:

```lean
import GebLean.LawvereERTetration

/-!
# Tests for tetration non-elementary result

Sanity tests: tetration computation and type-checks of the non-ER /
non-fullness theorems.
-/

open GebLean

-- tetration 0 = tower 0 1 = 1
#guard tetration 0 = 1

-- tetration 1 = tower 1 1 = 2
#guard tetration 1 = 2

-- tetration 2 = tower 2 1 = 4
#guard tetration 2 = 4

-- tetration 3 = tower 3 1 = 16
#guard tetration 3 = 16

-- tetration 4 = tower 4 1 = 2^16 = 65536
#guard tetration 4 = 65536

-- Non-ER theorem type-checks
example : ¬ ∃ t : ERMor1 1, ∀ x : ℕ,
    t.interp (fun _ => x) = tetration x :=
  tetration_not_ER

-- Non-fullness via tetration type-checks
example : ¬ erInterpFunctor.Full :=
  erInterpFunctor_not_full_via_tetration
```

- [ ] **Step 3: Register in `GebLeanTests.lean`**

Add `import GebLeanTests.Utilities.Tower` and `import
GebLeanTests.LawvereERTetration` in alphabetical order.

- [ ] **Step 4: Build and test**

Run: `lake build && lake test`
Expected: PASS, no warnings, all `#guard`s pass.

- [ ] **Step 5: Commit**

```bash
git add GebLeanTests/Utilities/Tower.lean \
        GebLeanTests/LawvereERTetration.lean \
        GebLeanTests.lean
git commit -m "Add sanity tests for tower and tetration non-ER"
```

---

## Task 11: Update workstream tracker

**Files:**

- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Append Phase 4f.2 completion paragraph**

Find the `## Status` section and append, directly before `## Goal`:

```markdown
Phase 4f.2 complete: see `GebLean/Utilities/Tower.lean` for
the `tower k x = 2^^k(x)` function with monotonicity,
composition, and multiplicative / power bounds;
`GebLean/LawvereERBound.lean` for the structural theorem
`ERMor1.exists_lt_tower` (every ER term is dominated by
some fixed-height tower applied to `maxCtx + 2`); and
`GebLean/LawvereERTetration.lean` for the corollary
`tetration_not_ER` (no `ERMor1 1` term computes tetration)
and the derived non-fullness theorem
`erInterpFunctor_not_full_via_tetration`.  This witnesses
the primrec / elementary gap, strengthening Phase 4f.1's
Ackermann-based non-fullness.
```

- [ ] **Step 2: Update the Tasks checklist**

Replace the line:

```markdown
  * [ ] 4f.2: Tetration non-fullness (deferred pending research).
```

With:

```markdown
  * [x] 4f.2: Tetration non-elementary via tower-bounding argument.
```

- [ ] **Step 3: Build (sanity)**

Run: `lake build && lake test`
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 4f.2 complete in workstream tracker"
```

---

## Self-Review

**Spec coverage:**

- [x] Generic `tower` function with arithmetic lemmas — Tasks 1-4.
- [x] `ERMor1.exists_lt_tower` structural bound — Tasks 5-8.
- [x] `tetration_not_ER` corollary — Task 9.
- [x] Derived non-fullness via tetration — Task 9.
- [x] Sanity tests for both tower and tetration — Task 10.
- [x] Workstream tracker updated — Task 11.

**Placeholder scan:**

- `sorry` appears in Tasks 4, 5, 6, 7, 8 as **temporary** placeholders
  during incremental construction of `LawvereERBound.lean` and in the
  sub-helpers of `Tower.lean`.  Each `sorry` site has an associated
  note: either specific Mathlib names to search for, or an alternate
  constant choice that avoids the lemma entirely.  All `sorry`s are
  eliminated before the corresponding commit.  The plan explicitly
  says "do not commit" between Tasks 5-8.
- If tower arithmetic proves more stubborn than anticipated,
  fallbacks are provided at each site (`mul_tower_le_tower_add_two`
  as a substitute for `_succ`, adjusted constants in the main
  theorem witnesses).

**Type consistency:**

- `tower : ℕ → ℕ → ℕ` is fixed in Task 1 and used uniformly.
- `maxCtx : {n : ℕ} → (Fin n → ℕ) → ℕ` is defined in Task 5 and
  referenced in Tasks 6-9.
- `ERMor1.exists_lt_tower : ∀ {n} (t : ERMor1 n), ∃ k, ∀ ctx,
  t.interp ctx < tower k (maxCtx ctx + 2)` signature is fixed in
  Task 5 and used throughout.
- `tetration : ℕ → ℕ := fun n => tower n 1` defined in Task 9.
- All constant choices (`k_f + 1` vs `k_f + 2` vs `k_f + 3`) are
  explicitly coupled through the "choose one, use consistently"
  instruction in each task.

**Risk notes:**

- The trickiest obligations are the tower arithmetic lemmas in Task 4
  (especially `sq_le_two_pow` and `add_two_le_two_pow`) and the comp
  case in Task 6.  Both have fallback strategies documented.
- If `Nat.lt_two_pow_self` doesn't exist under that exact name, the
  plan provides a self-contained proof as `nat_lt_two_pow_self`.
- The `hyperoperation 4` unfolding in `tetration_eq_hyperoperation`
  depends on whichever lemma-naming convention Mathlib uses for
  stepping `hyperoperation`.  The plan notes alternatives.

All type signatures and names cross-reference consistently; any
remaining uncertainty is flagged to the implementer with instructions
for how to substitute.
