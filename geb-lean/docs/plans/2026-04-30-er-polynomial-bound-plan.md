# ER polynomial-bound infrastructure: implementation plan

> **For agentic workers**: REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended)
> or `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal**: Build the polynomial-bound infrastructure (three
new Lean modules) that supplies the dominance hypothesis
needed by Task 14 of the kToER plan
(`docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`).

**Architecture**: Three Lean modules ordered bottom-up
by dependency.  Module A is generic Nat-arithmetic
(no `ERMor1` / `KMor1`).  Module B is ER-side
`PolyBound` data structure + structural `towerHeight`
lemma.  Module C is K^sim-side proofs (Lemmas 1.A and
1.B from the research doc) + final dominance assembly.

**Tech Stack**: Lean 4 with mathlib; existing project
infrastructure (`ERMor1`, `KMor1`, `kToER`,
`kSimTowerBound`, `kSimPackedBase`, `kSimPackedStep`,
`Utilities/Tower.lean`, `Utilities/SzudzikSeq.lean`,
`Utilities/ERArith.lean`).

**Spec**:
`docs/plans/2026-04-30-er-polynomial-bound-design.md`.

**Research**:
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`.

---

## Session-resumption checkpoint (2026-04-30)

This section is a "pick up here" anchor for fresh sessions
resuming this workstream.

### Completed (this workstream's commits, in order)

- Research and design phase commits (db32cca7, 6401b46f, 14302f86,
  1649c898, 986895bf — research doc, design doc, plan, plan
  amendment for option C, plan amendment for kToER deferral).
- Module A `Utilities/ComputationalComplexity.lean` (Tasks 1-6,
  six commits).  Final commit for Task 5 / Task 6 lands the
  `polynomial_iter_tower_bound`.
- Module B `LawvereERPolynomialBound.lean` (Tasks 7-11, ~5
  commits including a structural refactor at `c41064b8`).
- Module C `LawvereKSimPolynomialBound.lean` Tasks 12-16
  (~5 commits including a deferral note at `351a440a` for
  `kToER_polyBound_of_level_one`).
- Task 17a (level-0 base case): commit `159ff0bd`, with bug
  fix at `7f2eb159` (fixed `congr 1` failure in the comp case
  via explicit funext-based rewriting).
- Task 17b.1 (helper `packed_iteration_matches_simrecVec`):
  commit `27c66777`.
- Task 17b.2 partial (structural lemmas
  `kSimSzudzikPackList_towerHeight_ge_two`,
  `kSimPackedStep_towerHeight_ge_two`): commit `c1773838`.
- Plan refinement (this section): commit `e389c58f`.

### Where to resume

**Next task**: complete Task 17b.2.

**Blocker identified at `c1773838`**: the dominance arithmetic
requires `(kSimPackedStep g_ER).towerHeight ≥ k + 1` — stronger
than the existing ≥ 2 lemma.  This is structurally true
(`kSimSzudzikPackList` for system size k+1 has k+1 nested
`comp natPair (...)` layers, each contributing to towerHeight),
but proving it needs induction on `k` and tracking
per-Szudzik-level depth.

**After Task 17b.2 completes**, Tasks 17b.3, 17b.4, 17c, 18,
19, 20, 21 follow.  Total estimated remaining: ~1500-2000
lines of Lean.

### Verification before resumption

A fresh session should verify the current state:

```bash
cd /home/terence/git-workspaces/geb/geb-lean
git log --oneline -25  # see recent commits
lake build              # verify clean build
lake test               # verify clean tests
```

Expected: build clean, 1515 jobs successful; tests pass.

---

## File structure

The plan creates and modifies these files:

- **Create**: `GebLean/Utilities/ComputationalComplexity.lean`
  (Module A) — `Nat.pair_le_sq`, `Nat.seqPackBound`,
  tower-arithmetic helpers, polynomial-iter analytic
  lemma.
- **Create**: `GebLean/LawvereERPolynomialBound.lean`
  (Module B) — `ERMor1.PolyBound` structure,
  per-constructor degree helpers, structural
  `towerHeight` lemma, adapter for Module A.
- **Create**: `GebLean/LawvereKSimPolynomialBound.lean`
  (Module C) — `ConstantOrShiftedProj`, `level0Shape`,
  `linearBound`, `kToER_polyBound_of_level_one`,
  `kSimPackedStep_polyBound`,
  `kSimTowerBound_dominates_inline`.
- **Create**: `GebLeanTests/Utilities/ComputationalComplexity.lean`
  — Module A `#guard` tests.
- **Create**: `GebLeanTests/LawvereERPolynomialBound.lean`
  — Module B `#guard` tests.
- **Create**: `GebLeanTests/LawvereKSimPolynomialBound.lean`
  — Module C `#guard` tests.
- **Modify**: `GebLean.lean` — re-export new modules.
- **Modify**: `GebLeanTests.lean` — register new test
  modules.
- **Modify**:
  `docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md` —
  annotate Task 14's prompt outline to reference the new
  infrastructure.

---

## Tooling notes

- The project uses `lake build` and `lake test`; never
  `lake env lean` or `lake clean`.
- `warningAsError = true` is enabled — any `sorry` /
  unused-var / linter warning fails the build.
- Lean MCP tools (`mcp__lean-lsp__lean_goal`,
  `mcp__lean-lsp__lean_diagnostic_messages`,
  `mcp__lean-lsp__lean_multi_attempt`) should be used
  liberally to inspect intermediate goals.
- The `lean4:sorry-filler-deep` skill is available for
  the trickier proofs (Task 5, Task 9, Task 14, Task 17).

---

## Module A: `Utilities/ComputationalComplexity.lean`

Generic Nat-arithmetic primitives.  No `ERMor1` /
`KMor1` references.

### Task 1: Module A skeleton

**Files**:

- Create: `GebLean/Utilities/ComputationalComplexity.lean`

- [ ] **Step 1.1: Create the module file**

```lean
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Log
import GebLean.Utilities.Tower
import GebLean.Utilities.SzudzikSeq

/-!
# Computational complexity primitives

Generic natural-number arithmetic supporting polynomial
and tower bounds used in the ER polynomial-bound
infrastructure.  This module references neither
`ERMor1` nor `KMor1`; it depends only on `Nat`,
`Nat.pair`, `Nat.seqPack`, and `tower` from
`Utilities/Tower.lean`.

The principal results are:

- `Nat.pair_le_sq` — quadratic upper bound on Cantor
  pairing.
- `Nat.seqPackBound` and its dominance lemma — closed-
  form polynomial upper bound on `Nat.seqPack`.
- `Nat.polynomial_iter_tower_two_bound` — iterating a
  polynomially-bounded step `j` times keeps the value
  within a height-2 tower of a linear function.

See `docs/plans/2026-04-30-er-polynomial-bound-design.md`
(Module A).

A related but distinct concept is course-of-values
recursion (PlanetMath:
`https://planetmath.org/courseofvaluesrecursion`); our
infrastructure does simultaneous primitive recursion
via Hilbert–Bernays reduction with Szudzik pairing,
which is different from course-of-values.
-/

namespace Nat

end Nat
```

- [ ] **Step 1.2: Run `lake build`**

```bash
lake build GebLean.Utilities.ComputationalComplexity
```

Expected: PASS, no warnings.

- [ ] **Step 1.3: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "Add Utilities/ComputationalComplexity skeleton

New utility module hosts generic Nat-arithmetic
primitives for polynomial and tower bounds.  No
ERMor1 or KMor1 references; depends on Nat,
Nat.pair, Nat.seqPack, and tower."
```

---

### Task 2: `Nat.pair_le_sq` — quadratic bound on Cantor pairing

**Files**:

- Modify: `GebLean/Utilities/ComputationalComplexity.lean`

`Nat.pair x y` (mathlib's Cantor pairing) has closed form
`if x < y then y * y + x else x * x + x + y`.  The bound
`Nat.pair x y ≤ (x + y + 1)^2` follows from case analysis.

- [ ] **Step 2.1: Append the lemma to the file**

```lean
/-- Quadratic upper bound on mathlib's `Nat.pair`. -/
theorem pair_le_sq (x y : ℕ) :
    Nat.pair x y ≤ (x + y + 1)^2 := by
  unfold Nat.pair
  by_cases h : x < y
  · simp only [h, if_true]
    have : y * y + x ≤ (x + y + 1) * (x + y + 1) := by
      have h1 : y * y ≤ (x + y) * (x + y) := by
        have : y ≤ x + y := Nat.le_add_left _ _
        exact Nat.mul_le_mul this this
      have h2 : x ≤ (x + y) * (x + y) + 2 * (x + y) + 1 - y * y := by
        omega
      omega
    have hsq : (x + y + 1)^2 = (x + y + 1) * (x + y + 1) := by
      ring
    rw [hsq]
    exact this
  · simp only [h, if_false]
    have hsq : (x + y + 1)^2 = (x + y + 1) * (x + y + 1) := by
      ring
    rw [hsq]
    have : x * x + x + y ≤ (x + y + 1) * (x + y + 1) := by
      have h1 : x * x ≤ (x + y) * (x + y) := by
        have : x ≤ x + y := Nat.le_add_right _ _
        exact Nat.mul_le_mul this this
      omega
    exact this
```

The exact tactic body may need adjustment — use
`mcp__lean-lsp__lean_goal` to inspect; `omega` should
close most arithmetic obligations.

- [ ] **Step 2.2: Run `lake build`**

Expected: PASS, no warnings.

- [ ] **Step 2.3: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "Add Nat.pair_le_sq quadratic bound

Cantor pairing satisfies Nat.pair x y ≤ (x + y + 1)^2.
Proof by case analysis on x < y, with omega closing the
arithmetic obligations in each branch."
```

---

### Task 3: `Nat.seqPackBound` and dominance lemma

**Files**:

- Modify: `GebLean/Utilities/ComputationalComplexity.lean`

`Nat.seqPack [v_0, …, v_k]` packs the (k+1)-list via
iterated pairing.  Closed-form bound:
`(max + 1)^D` where `D = 2^(k+1) · max(d_i)` per the
research doc Claim 3 / Fix B.

- [ ] **Step 3.1: Append `seqPackBound` definition**

```lean
/-- Closed-form polynomial upper bound on `seqPack` for
a list of length at most `k + 1` with components bounded
by `(m + 1)^d` for some shared maximum component degree
`d`.  The exponent `D = 2^(k+1) * d` reflects the
quadratic blow-up per pairing. -/
def seqPackBound (k d m : ℕ) : ℕ :=
  (m + 1)^(2^(k + 1) * d)
```

- [ ] **Step 3.2: Append dominance lemma**

```lean
/-- `Nat.seqPack` is bounded by `seqPackBound` when the
components are themselves polynomially bounded. -/
theorem seqPack_le_seqPackBound :
    ∀ (vs : List ℕ) (k d m : ℕ),
      vs.length ≤ k + 1 →
      (∀ v ∈ vs, v ≤ (m + 1)^d) →
      Nat.seqPack vs ≤ seqPackBound k d m
  | [],         _, _, _, _, _ => by
      simp [Nat.seqPack, seqPackBound]
      exact Nat.zero_le _
  | v :: vs',   k, d, m, hlen, h_bounds => by
      simp only [Nat.seqPack_cons]
      have h_v : v ≤ (m + 1)^d := h_bounds v
        (List.mem_cons_self _ _)
      have h_rest := seqPack_le_seqPackBound vs'
        (k - 1) d m (by ...) (fun v hv =>
          h_bounds v (List.mem_cons_of_mem _ hv))
      have h_pair := Nat.pair_le_sq v (Nat.seqPack vs')
      -- Combine h_pair, h_v, h_rest into the goal:
      -- Nat.pair v (Nat.seqPack vs') + 1 ≤ (m+1)^(2^(k+1) * d)
      sorry
```

The trailing `sorry` is a planning marker; the implementer
discharges it by combining the three hypotheses arithmetically.
Approach:

```text
By h_pair: pair v (seqPack vs') ≤ (v + seqPack vs' + 1)^2.
By h_v and h_rest: v + seqPack vs' ≤ 2 · (m+1)^(max d (2^k * d))
  ≤ 2 · (m+1)^(2^k * d) (for d ≥ 0, 2^k ≥ 1).
So pair ≤ (2 · (m+1)^(2^k * d) + 1)^2 ≤ ... ≤ (m+1)^(2^(k+1) * d).
Adding 1: pair + 1 ≤ (m+1)^(2^(k+1) * d) = seqPackBound k d m.
```

If the arithmetic massaging proves intractable, the
implementer may add intermediate helper lemmas.  Do
**not** commit a `sorry`.

- [ ] **Step 3.3: Run `lake build`**

Expected: PASS with no `sorry` warnings.

- [ ] **Step 3.4: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "Add Nat.seqPackBound and dominance lemma

Closed-form (m+1)^(2^(k+1) * d) upper bound for seqPack
of a (k+1)-list with d-degree-bounded components.
Dominance lemma proves Nat.seqPack vs ≤ seqPackBound
under the hypotheses on length and component bounds."
```

---

### Task 4: Tower-arithmetic helper

**Files**:

- Modify: `GebLean/Utilities/ComputationalComplexity.lean`

The polynomial-iter analytic lemma needs the inequality
`(tower h x + 1)^D ≤ tower (h+1) (x + Nat.log 2 D + 1)`.
This is a standalone tower-arithmetic fact.

- [ ] **Step 4.1: Append the helper lemma**

```lean
/-- Polynomial-of-tower bound: a polynomial of degree
`D` applied to `tower h x` is dominated by a tower of
height `h + 1` applied to `x + log D + 1`.  Used in
the inductive step of `polynomial_iter_tower_two_bound`. -/
theorem tower_succ_pow_bound (h D x : ℕ) :
    (GebLean.tower h x + 1)^D ≤
      GebLean.tower (h + 1) (x + Nat.log 2 D + 1) := by
  -- (tower h x + 1)^D ≤ (2 * tower h x)^D for tower h x ≥ 1
  -- = 2^D · (tower h x)^D
  -- For h = 0: (x + 1)^D ≤ 2^D · x^D ≤ 2^(D + D · log_2 x)
  --            ≤ tower 1 (D + log D · x) ≈ tower 1 (linear)
  -- The `+ Nat.log 2 D + 1` shift in the second argument
  -- of tower (h+1) absorbs the D and log D factors.
  -- Proof outline:
  --   tower (h+1) (x + log D + 1) = 2^(tower h (x + log D + 1))
  --   ≥ 2^(tower h x · (D + 1))   (by tower input-monotonicity
  --                                 plus exp-bound)
  --   ≥ 2^(D · tower h x)          (since D + 1 ≥ D)
  --   = 2^(D · tower h x)
  --   ≥ (2 · tower h x)^D ≥ (tower h x + 1)^D
  sorry
```

The trailing `sorry` is a planning marker; this proof
is genuinely tricky and may need several auxiliary
`have` steps.  Use `mcp__lean-lsp__lean_multi_attempt`
or the `lean4:sorry-filler-deep` skill if needed.

If the proof becomes too involved (>50 lines), factor
into private helpers:

- `tower_h_le_pow_of_le` (relating `tower h x` to powers).
- `pow_le_two_pow_log` (the `(m + 1)^D ≤ 2^(D · log m + D)`
  step).

**Do not commit `sorry`.**

- [ ] **Step 4.2: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 4.3: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "Add tower_succ_pow_bound helper

Inequality (tower h x + 1)^D ≤ tower (h+1) (x + log D + 1)
used in the inductive step of the polynomial-iter
analytic lemma."
```

---

### Task 5: `Nat.polynomial_iter_tower_two_bound`

**Files**:

- Modify: `GebLean/Utilities/ComputationalComplexity.lean`

The principal Module A result: iterating a polynomially-
bounded step `j` times stays within a height-2 tower of
a linear function.

- [ ] **Step 5.1: Append the main lemma**

```lean
/-- Iterating a polynomially-bounded step `j` times
keeps the value bounded by a height-2 tower of a linear
function in `j`, the parameter `x`, and the structural
constants `D, m`. -/
theorem polynomial_iter_tower_two_bound
    (step : ℕ → ℕ → ℕ) (D m : ℕ)
    (h_step : ∀ v x, step v x ≤ (max v x + 1) ^ D)
    (v_0 : ℕ → ℕ) (h_base : ∀ x, v_0 x ≤ m * x + m)
    (j x : ℕ) :
    Nat.iterate (fun v => step v x) j (v_0 x) ≤
      GebLean.tower 2
        ((Nat.log 2 D + 1) * j + m * x + Nat.log 2 D + m + 2) := by
  induction j with
  | zero =>
      simp only [Nat.iterate]
      have : v_0 x ≤ m * x + m := h_base x
      -- m * x + m ≤ tower 2 (linear) since tower 2 is huge
      sorry
  | succ j ih =>
      simp only [Nat.iterate_succ_apply', Nat.iterate]
      -- step (Nat.iterate (step ·) j (v_0 x)) x
      -- ≤ (max (Nat.iterate ...) x + 1)^D       (by h_step)
      -- ≤ (tower 2 (linear in j) + 1)^D         (by IH)
      -- ≤ tower 2 (linear in j + log D + 1)     (by Task 4)
      -- = tower 2 (linear in (j+1))             (by linear-arith)
      sorry
```

The two `sorry`s are planning markers; the implementer
discharges them by combining the IH, `h_step`, `h_base`,
and `tower_succ_pow_bound`.  The base case is just a
`tower 2`-monotonicity argument.  The successor case is
the heart of the proof.

If the proof becomes longer than 80 lines, factor out
helper lemmas:

- `linear_le_tower_two` for the base case.
- `iter_step_one_step_bound` for one iteration's bound.

**Do not commit `sorry`.**

- [ ] **Step 5.2: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 5.3: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "Add polynomial_iter_tower_two_bound

Iterating a polynomially-bounded step j times keeps the
value bounded by tower 2 of a linear function in
(j, x, log D, m).  Heart of the polynomial-bound
infrastructure for level-2 K^sim simrec."
```

---

### Task 6: Module A tests

**Files**:

- Create: `GebLeanTests/Utilities/ComputationalComplexity.lean`

- [ ] **Step 6.1: Create the test file**

```lean
import GebLean.Utilities.ComputationalComplexity

/-!
# Tests for `Utilities/ComputationalComplexity`

`#guard` checks for `Nat.pair_le_sq`, `seqPackBound`,
and `polynomial_iter_tower_two_bound` on small concrete
inputs.
-/

open Nat

-- Nat.pair quadratic bound spot-checks
#guard Nat.pair 0 0 ≤ (0 + 0 + 1)^2
#guard Nat.pair 3 5 ≤ (3 + 5 + 1)^2
#guard Nat.pair 7 7 ≤ (7 + 7 + 1)^2

-- seqPackBound spot-checks (k = 0, single element)
#guard Nat.seqPack [3] ≤ seqPackBound 0 1 3

-- seqPackBound spot-checks (k = 1, two elements)
#guard Nat.seqPack [3, 5] ≤ seqPackBound 1 1 5

-- polynomial_iter_tower_two_bound spot-check on a
-- specific concrete step (e.g., step v x = (v+x+1)^2)
private def testStep (v x : ℕ) : ℕ := (v + x + 1)^2
private def testBase (x : ℕ) : ℕ := x

-- Just verify the lemma's statement type-checks; the
-- actual bound numerics are large, so we don't compute
-- them at #guard time.
example : ∀ j x,
    Nat.iterate (fun v => testStep v x) j (testBase x) ≤
      GebLean.tower 2
        ((Nat.log 2 2 + 1) * j + 1 * x + Nat.log 2 2 + 1 + 2) := by
  intro j x
  apply Nat.polynomial_iter_tower_two_bound
  · intro v x
    unfold testStep
    exact Nat.le_refl _
  · intro x
    unfold testBase
    omega
```

- [ ] **Step 6.2: Run `lake test`**

Expected: PASS.

- [ ] **Step 6.3: Commit**

```bash
git add GebLeanTests/Utilities/ComputationalComplexity.lean
git commit -m "Add tests for Utilities/ComputationalComplexity

#guard checks for Nat.pair_le_sq, seqPackBound, and
a type-level invocation test for
polynomial_iter_tower_two_bound."
```

---

## Module B: `LawvereERPolynomialBound.lean`

ER-side polynomial-bound predicate and structural
`towerHeight` lemma.  References `ERMor1` but not
`KMor1`.

### Task 7: Module B skeleton + `ERMor1.PolyBound`

**Files**:

- Create: `GebLean/LawvereERPolynomialBound.lean`

- [ ] **Step 7.1: Create the module file**

```lean
import GebLean.LawvereER
import GebLean.LawvereERBoundComputable
import GebLean.Utilities.ComputationalComplexity

/-!
# ER polynomial bounds and structural towerHeight lemma

ER-side polynomial-value-bound infrastructure used in
the K^sim → ER forward translation's interp-preservation
theorem.

The principal results are:

- `ERMor1.PolyBound` — data-bearing structure carrying
  a polynomial degree `degree : ℕ` and a value-bound
  proof.
- `ERMor1.PolyBound.log_le_towerHeight` — structural
  lemma relating polynomial degree to the project's
  `ERMor1.towerHeight`.

References `ERMor1` but not `KMor1`.

See `docs/plans/2026-04-30-er-polynomial-bound-design.md`
(Module B) and
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
(Claim 7 / FOLKLORE 4).
-/

namespace GebLean

/-- Data-bearing polynomial-value-bound for an ER term.
The `degree` field is the polynomial degree; the
`bounds` field is the pointwise inequality. -/
structure ERMor1.PolyBound {n : ℕ} (f : ERMor1 n) where
  degree : ℕ
  bounds : ∀ ctx : Fin n → ℕ,
    f.interp ctx ≤
      ((Finset.univ : Finset (Fin n)).sup ctx + 1) ^ degree

end GebLean
```

- [ ] **Step 7.2: Run `lake build`**

Expected: PASS, no warnings.

- [ ] **Step 7.3: Commit**

```bash
git add GebLean/LawvereERPolynomialBound.lean
git commit -m "Add LawvereERPolynomialBound skeleton + PolyBound struct

Plain data-bearing polynomial-value-bound structure for
ERMor1 terms, paired with a value-bound proof.  No
Setoid wrapper since downstream consumers use the
specific degree value."
```

---

### Task 8: Per-constructor degree-of-interp helpers

**Files**:

- Modify: `GebLean/LawvereERPolynomialBound.lean`

The structural `towerHeight` lemma needs per-constructor
analysis of the polynomial degree.  This task provides
the per-constructor helpers used in Task 9's main
induction.

- [ ] **Step 8.1: Read `ERMor1.towerHeight`'s definition**

Run:

```bash
grep -n "ERMor1.towerHeight" GebLean/LawvereERBoundComputable.lean
```

Confirm the definition (around line 34).  Document the
expected behaviour of each constructor on `towerHeight`
in code comments before proving the lemma.

- [ ] **Step 8.2: Append per-constructor `PolyBound` constructors**

```lean
namespace GebLean.ERMor1.PolyBound

/-- Polynomial bound for `zero` (constant 0). -/
def ofZero : PolyBound (ERMor1.zero (n := 0)) where
  degree := 0
  bounds := fun _ => by simp [ERMor1.interp_zero]

/-- Polynomial bound for `succ` (linear, degree 1). -/
def ofSucc : PolyBound ERMor1.succ where
  degree := 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_succ]
    -- ctx 0 + 1 ≤ (sup ctx + 1)^1 = sup ctx + 1
    -- since ctx 0 ≤ sup ctx, ctx 0 + 1 ≤ sup ctx + 1
    have : ctx 0 ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

/-- Polynomial bound for `proj i` (linear, degree 1). -/
def ofProj {k : ℕ} (i : Fin k) :
    PolyBound (ERMor1.proj i) where
  degree := 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_proj, pow_one]
    have : ctx i ≤ (Finset.univ : Finset (Fin k)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

/-- Polynomial bound for `sub` (linear, degree 1). -/
def ofSub : PolyBound ERMor1.sub where
  degree := 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_sub, pow_one]
    have h0 : ctx 0 ≤ (Finset.univ : Finset (Fin 2)).sup ctx :=
      Finset.le_sup (Finset.mem_univ _)
    omega

end GebLean.ERMor1.PolyBound
```

- [ ] **Step 8.3: Append composition `PolyBound`**

```lean
namespace GebLean.ERMor1.PolyBound

/-- Polynomial bound for composition: degree of `comp f g`
is at most `f.degree * (max over i of (g i).degree)`.  -/
def ofComp {k n : ℕ} {f : ERMor1 k} {g : Fin k → ERMor1 n}
    (pb_f : PolyBound f)
    (pb_g : Fin k → (i : Fin k) → PolyBound (g i)) :
    PolyBound (ERMor1.comp f g) :=
  let max_g_degree :=
    (Finset.univ : Finset (Fin k)).sup
      (fun i => (pb_g i i).degree)
  { degree := pb_f.degree * max (max_g_degree) 1
    bounds := fun ctx => by
      simp only [ERMor1.interp_comp]
      -- f.interp (fun i => (g i).interp ctx)
      --   ≤ (sup-over-i (g i).interp ctx + 1)^f.degree   (by pb_f)
      --   ≤ ((sup ctx + 1)^max_g_degree + 1)^f.degree    (by pb_g)
      --   ≤ (sup ctx + 1)^(f.degree * max_g_degree)      (arith)
      sorry }

end GebLean.ERMor1.PolyBound
```

The `ofComp` constructor's body has a `sorry` planning
marker; discharge by chaining `pb_f.bounds`,
`pb_g.bounds`, and `pow_mul` style lemmas.

- [ ] **Step 8.4: Append `bsum` and `bprod` `PolyBound`**

```lean
namespace GebLean.ERMor1.PolyBound

/-- Polynomial bound for `bsum f`: bounded summation
multiplies the inner degree by 1 (each iteration adds at
most a polynomial of degree `f.degree`; iterated `bound`
times). -/
def ofBsum {k : ℕ} {f : ERMor1 (k + 1)} (pb_f : PolyBound f) :
    PolyBound (ERMor1.bsum f) where
  degree := pb_f.degree + 1
  bounds := fun ctx => by
    simp only [ERMor1.interp_bsum, natBSum]
    -- bsum bound = ctx 0; sums (ctx 0)-many copies of f bounded by
    -- (sup + 1)^f.degree ≤ (sup + 1) * (sup + 1)^f.degree
    -- = (sup + 1)^(f.degree + 1)
    sorry

/-- Polynomial bound for `bprod f`: similar to bsum, but
multiplicative; the bound is `(sup+1)^(2 * f.degree)`. -/
def ofBprod {k : ℕ} {f : ERMor1 (k + 1)} (pb_f : PolyBound f) :
    PolyBound (ERMor1.bprod f) where
  degree := 2 * pb_f.degree
  bounds := fun ctx => by
    simp only [ERMor1.interp_bprod, natBProd]
    sorry

end GebLean.ERMor1.PolyBound
```

The `ofBsum` and `ofBprod` constructors have `sorry`s;
discharge using induction on the bound (`ctx 0`) and the
inner `f`'s polynomial bound.

- [ ] **Step 8.5: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 8.6: Commit**

```bash
git add GebLean/LawvereERPolynomialBound.lean
git commit -m "Add per-constructor PolyBound builders for ERMor1

ofZero, ofSucc, ofProj, ofSub, ofComp, ofBsum, ofBprod
construct PolyBound values for each ER constructor.
Used as building blocks for the structural recursion in
Task 9 (log_le_towerHeight)."
```

---

### Task 9: `ERMor1.PolyBound.log_le_towerHeight`

**Files**:

- Modify: `GebLean/LawvereERPolynomialBound.lean`

The structural `towerHeight` lemma (FOLKLORE 4 from the
research doc).  Heart of Module B.

- [ ] **Step 9.1: Read `ERMor1.towerHeight` carefully**

```bash
grep -A 30 "def ERMor1.towerHeight" GebLean/LawvereERBoundComputable.lean
```

Confirm each constructor's `towerHeight` value.

- [ ] **Step 9.2: Append the main lemma**

```lean
namespace GebLean.ERMor1.PolyBound

/-- Structural towerHeight lemma: the polynomial degree
of an ER term's interp is bounded by `2^towerHeight`. -/
theorem log_le_towerHeight :
    ∀ {n : ℕ} (f : ERMor1 n) (pb : PolyBound f),
      Nat.log 2 pb.degree ≤ f.towerHeight
  | _, .zero, pb => by
      -- degree of zero is 0; log_2 0 = 0; towerHeight zero = 0
      sorry
  | _, .succ, pb => by
      -- degree of succ is 1; log_2 1 = 0; towerHeight succ = 0
      sorry
  | _, .proj _, pb => by
      sorry
  | _, .sub, pb => by
      sorry
  | _, .comp f g, pb => by
      -- towerHeight (comp f g) = max towerHeight f, max-i (towerHeight (g i))
      -- pb.degree ≤ pb_f.degree * max-i pb_g.degree
      -- log_2 (a * b) ≤ log_2 a + log_2 b
      -- By IH on f and each g i, log_2 of each child's degree is bounded.
      sorry
  | _, .bsum f, pb => by
      -- towerHeight (bsum f) = towerHeight f + 1
      -- pb.degree = pb_f.degree + 1
      sorry
  | _, .bprod f, pb => by
      sorry

end GebLean.ERMor1.PolyBound
```

The seven `sorry`s are planning markers; each discharges
to a per-constructor analysis.  See the design doc's
"Module B" section for proof outlines.

If any case proves intractable beyond 30 lines, factor
into a private helper.  **Do not commit `sorry`**.

- [ ] **Step 9.3: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 9.4: Commit**

```bash
git add GebLean/LawvereERPolynomialBound.lean
git commit -m "Prove ERMor1.PolyBound.log_le_towerHeight

Structural induction on ERMor1 with per-constructor
analysis of polynomial degree vs structural
towerHeight.  Heart of Module B."
```

---

### Task 10: `PolyBound.to_iter_step_form` adapter

**Files**:

- Modify: `GebLean/LawvereERPolynomialBound.lean`

Adapter from `PolyBound` on a `(k + 2)`-arity ER term
(the shape `boundedRec` expects for its step) to Module
A's polynomial-iter step form.

- [ ] **Step 10.1: Append the adapter**

```lean
namespace GebLean.ERMor1.PolyBound

/-- Adapter: a `PolyBound` on a `(k + 2)`-arity ER term
gives the step-bound shape Module A's
`polynomial_iter_tower_two_bound` consumes. -/
theorem to_iter_step_form {k : ℕ}
    (f : ERMor1 (k + 2)) (pb : PolyBound f)
    (params : Fin k → ℕ) (v x : ℕ) :
    f.interp (Fin.cons x (Fin.cons v params)) ≤
      (max v (max x ((Finset.univ : Finset (Fin k)).sup params)) + 1)
        ^ pb.degree := by
  have h := pb.bounds (Fin.cons x (Fin.cons v params))
  -- sup over Fin (k+2) of Fin.cons x (Fin.cons v params)
  -- = max x (max v (sup over Fin k of params))
  -- = max v (max x (sup over Fin k of params))   (commutativity)
  sorry

end GebLean.ERMor1.PolyBound
```

The `sorry` is a planning marker; discharge by computing
the `sup` of `Fin.cons` and applying commutativity.

- [ ] **Step 10.2: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 10.3: Commit**

```bash
git add GebLean/LawvereERPolynomialBound.lean
git commit -m "Add PolyBound.to_iter_step_form adapter

Translates a PolyBound on a (k+2)-arity ER term into the
step-bound shape Module A's polynomial-iter analytic
lemma consumes."
```

---

### Task 11: Module B tests

**Files**:

- Create: `GebLeanTests/LawvereERPolynomialBound.lean`

- [ ] **Step 11.1: Create the test file**

```lean
import GebLean.LawvereERPolynomialBound

/-!
# Tests for LawvereERPolynomialBound

`#guard` checks for `PolyBound` constructors on small ER
terms, plus type-level checks for
`log_le_towerHeight`.
-/

open GebLean

-- PolyBound on zero
example : (ERMor1.PolyBound.ofZero).degree = 0 := rfl

-- PolyBound on succ
example : (ERMor1.PolyBound.ofSucc).degree = 1 := rfl

-- log_le_towerHeight type-check on succ
example :
    Nat.log 2 ERMor1.PolyBound.ofSucc.degree ≤
      ERMor1.succ.towerHeight :=
  ERMor1.PolyBound.log_le_towerHeight ERMor1.succ
    ERMor1.PolyBound.ofSucc

-- log_le_towerHeight on a comp term
private def succProj0 : ERMor1 1 :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) => ERMor1.proj (k := 1) 0)

private def pb_succProj0 : ERMor1.PolyBound succProj0 :=
  ERMor1.PolyBound.ofComp ERMor1.PolyBound.ofSucc
    (fun _ _ => ERMor1.PolyBound.ofProj 0)

example :
    Nat.log 2 pb_succProj0.degree ≤ succProj0.towerHeight :=
  ERMor1.PolyBound.log_le_towerHeight succProj0 pb_succProj0
```

- [ ] **Step 11.2: Run `lake test`**

Expected: PASS.

- [ ] **Step 11.3: Commit**

```bash
git add GebLeanTests/LawvereERPolynomialBound.lean
git commit -m "Add tests for LawvereERPolynomialBound

PolyBound construction tests on zero/succ/proj/comp,
plus log_le_towerHeight type-checks."
```

---

## Module C: `LawvereKSimPolynomialBound.lean`

K^sim-side proofs.  References both `KMor1` and `ERMor1`.

### Task 12: Module C skeleton + `ConstantOrShiftedProj`

**Files**:

- Create: `GebLean/LawvereKSimPolynomialBound.lean`

- [ ] **Step 12.1: Create the module file**

```lean
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimER
import GebLean.LawvereERPolynomialBound
import GebLean.Utilities.ComputationalComplexity
import GebLean.Utilities.KSimSzudzikSimrec

/-!
# K^sim polynomial bounds and dominance assembly

K^sim-side proofs supporting the simrec dominance
hypothesis required by `kToER_interp`'s level-2
simrec case.

The principal results are:

- `ConstantOrShiftedProj` — inductive shape for level-0
  K^sim functions.
- `KMor1.level0Shape` — Lemma 1.B from the research doc.
- `KMor1.linearBound` — Lemma 1.A from the research doc.
- `kToER_polyBound_of_level_one` — bridge to ER
  polynomial bounds.
- `kSimPackedStep_polyBound` /
  `kSimPackedBase_polyBound` — specialized for the
  packed simrec step / base.
- `kSimTowerBound_dominates_inline` — final dominance
  assembly.

See `docs/plans/2026-04-30-er-polynomial-bound-design.md`
(Module C) and
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
(Claims 1, 3, 4).
-/

namespace GebLean

/-- Shape of a level-0 K^sim function: either a constant
`k` or a projection-plus-constant `ctx i + k`.  Lemma 1.B's
output type. -/
inductive ConstantOrShiftedProj : ℕ → Type
  | const   {a : ℕ} (k : ℕ) : ConstantOrShiftedProj a
  | shifted {a : ℕ} (i : Fin a) (k : ℕ) :
      ConstantOrShiftedProj a

/-- Interpretation of `ConstantOrShiftedProj`. -/
def ConstantOrShiftedProj.interp :
    {a : ℕ} → ConstantOrShiftedProj a → (Fin a → ℕ) → ℕ
  | _, .const k,        _   => k
  | _, .shifted i k,    ctx => ctx i + k

/-- Linear-bound constants (c, k) for a
`ConstantOrShiftedProj`. -/
def ConstantOrShiftedProj.linearBound :
    {a : ℕ} → ConstantOrShiftedProj a → ℕ × ℕ
  | _, .const k       => (0, k)
  | _, .shifted _ k   => (1, k)

end GebLean
```

- [ ] **Step 12.2: Run `lake build`**

Expected: PASS, no warnings.

- [ ] **Step 12.3: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add LawvereKSimPolynomialBound skeleton + ConstantOrShiftedProj

New module hosts K^sim-side polynomial-bound proofs
(Lemma 1.A, 1.B, dominance assembly).
ConstantOrShiftedProj inductive captures level-0
K^sim's shape (constant or shifted projection)."
```

---

### Task 13: `KMor1.level0Shape` (Lemma 1.B)

**Files**:

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

Lemma 1.B: every level-0 K^sim term has interp of
constant-or-shifted-projection form.

- [ ] **Step 13.1: Append `KMor1.level0Shape` definition**

```lean
namespace GebLean

/-- Lemma 1.B: every level-0 K^sim term has interp of
constant or shifted-projection form. -/
def KMor1.level0Shape :
    {a : ℕ} → (f : KMor1 a) → f.level ≤ 0 →
      ConstantOrShiftedProj a
  | _, .zero,         _ => .const 0
  | _, .succ,         _ => .shifted 0 1
  | _, .proj i,       _ => .shifted i 0
  | _, .comp f gs,    h => by
      -- level (comp f gs) = max f.level (sup-i (gs i).level)
      -- ≤ 0 implies f.level ≤ 0 and each gs i has level ≤ 0.
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 0 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 0 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      let f_shape := KMor1.level0Shape f hf
      match f_shape with
      | .const k_f       => .const k_f
      | .shifted i k_f   =>
          let gs_shape := KMor1.level0Shape (gs i) (hgs i)
          match gs_shape with
          | .const c        => .const (c + k_f)
          | .shifted j k_gs => .shifted j (k_gs + k_f)
  | _, .raise _,      h => by
      unfold KMor1.level at h
      omega
  | _, .simrec _ _ _, h => by
      unfold KMor1.level at h
      omega

end GebLean
```

- [ ] **Step 13.2: Append `level0Shape_interp` theorem**

```lean
namespace GebLean

/-- Interp-equality between `f` and its `level0Shape`
representative. -/
theorem KMor1.level0Shape_interp :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 0) →
      (ctx : Fin a → ℕ) →
      f.interp ctx = (KMor1.level0Shape f h).interp ctx
  | _, .zero,         _, _   => by
      simp [KMor1.level0Shape, ConstantOrShiftedProj.interp,
        KMor1.interp]
  | _, .succ,         _, _   => by
      simp [KMor1.level0Shape, ConstantOrShiftedProj.interp,
        KMor1.interp]
  | _, .proj _,       _, _   => by
      simp [KMor1.level0Shape, ConstantOrShiftedProj.interp,
        KMor1.interp]
  | _, .comp f gs,    h, ctx => by
      simp only [KMor1.level0Shape, KMor1.interp_comp]
      have hf : f.level ≤ 0 := …
      have hgs : ∀ i, (gs i).level ≤ 0 := …
      have h_f := KMor1.level0Shape_interp f hf
        (fun i => (gs i).interp ctx)
      -- continue case analysis on f_shape and gs_shape;
      -- match each to verify interp-equality.
      sorry
  | _, .raise _,      h, _   => by
      unfold KMor1.level at h; omega
  | _, .simrec _ _ _, h, _   => by
      unfold KMor1.level at h; omega

end GebLean
```

The `comp` case has a `sorry` planning marker; discharge
by case-analyzing both `f_shape` and `gs_shape` (matching
the definition's structure) and applying the recursive
interp hypotheses.

If the proof becomes longer than 50 lines, factor the
`comp` case's four sub-cases into a private helper.
**Do not commit `sorry`**.

- [ ] **Step 13.3: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 13.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add KMor1.level0Shape + interp-equality (Lemma 1.B)

Structural recursion on level-0 KMor1 terms producing a
ConstantOrShiftedProj witness, plus the interp-equality
theorem.  raise and simrec cases are vacuous at level 0."
```

---

### Task 14: `KMor1.linearBound` (Lemma 1.A)

**Files**:

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

Lemma 1.A: every level-1 K^sim term has linear-value-
bound on its interp.  Constants are conservative
(option α from brainstorm Question 8).

- [ ] **Step 14.1: Append `KMor1.linearBound` definition**

```lean
namespace GebLean

/-- Lemma 1.A: every level-1 K^sim term is
linear-value-bounded.  Returns `(c, k)` such that
`f.interp ctx ≤ c · sup ctx + k`. -/
def KMor1.linearBound :
    {a : ℕ} → (f : KMor1 a) → f.level ≤ 1 → ℕ × ℕ
  | _, .zero,         _ => (0, 0)
  | _, .succ,         _ => (1, 1)
  | _, .proj _,       _ => (1, 0)
  | _, .comp f gs,    h =>
      -- f.level ≤ 1 and each gs i level ≤ 1
      let hf : f.level ≤ 1 := …
      let hgs : ∀ i, (gs i).level ≤ 1 := fun i => …
      let (c_f, k_f) := KMor1.linearBound f hf
      let cs := List.ofFn (fun i => (KMor1.linearBound (gs i) (hgs i)).1)
      let ks := List.ofFn (fun i => (KMor1.linearBound (gs i) (hgs i)).2)
      let c := c_f * (cs.maximum?.getD 0)
      let k := c_f * (ks.foldr (· + ·) 0) + k_f
      (c, k)
  | _, .raise f,      h =>
      -- f.level ≤ 0, use level0Shape's linear bound
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      (KMor1.level0Shape f hf).linearBound
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp =>
      -- All h_l, g_l are level 0 by hypothesis
      let hh : ∀ l, (h_fam l).level ≤ 0 := fun l => …
      let hg : ∀ l, (g_fam l).level ≤ 0 := fun l => …
      let h_shapes : Fin (k + 1) → ConstantOrShiftedProj a :=
        fun l => KMor1.level0Shape (h_fam l) (hh l)
      let g_shapes : Fin (k + 1) →
          ConstantOrShiftedProj (a + 1 + (k + 1)) :=
        fun l => KMor1.level0Shape (g_fam l) (hg l)
      let baseConsts := Fin.foldr (k + 1)
        (fun l acc => max acc (h_shapes l).linearBound.2) 0
      let stepConsts := Fin.foldr (k + 1)
        (fun l acc => max acc (g_shapes l).linearBound.2) 0
      let c := 1 + (k + 1) * stepConsts
      let k_const := baseConsts + (k + 1) * stepConsts
      (c, k_const)

end GebLean
```

The level-bound `…` markers indicate where the
implementer fills in the `KMor1.level` unfolding similar
to other tasks.

- [ ] **Step 14.2: Append `KMor1.linearBound_dominates`**

```lean
namespace GebLean

/-- The linear bound dominates the K^sim interp: for all
contexts, `f.interp ctx ≤ c · sup ctx + k`. -/
theorem KMor1.linearBound_dominates :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
      (ctx : Fin a → ℕ),
      f.interp ctx ≤
        (KMor1.linearBound f h).1 *
          (Finset.univ : Finset (Fin a)).sup ctx +
        (KMor1.linearBound f h).2
  | _, .zero,         _, _   => by
      simp [KMor1.linearBound, KMor1.interp]
  | _, .succ,         _, ctx => by
      simp [KMor1.linearBound, KMor1.interp]
      have : ctx 0 ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
        Finset.le_sup (Finset.mem_univ _)
      omega
  | _, .proj _,       _, ctx => by
      simp [KMor1.linearBound, KMor1.interp]
      have : ctx _ ≤ (Finset.univ : Finset (Fin _)).sup ctx :=
        Finset.le_sup (Finset.mem_univ _)
      omega
  | _, .comp _ _,     h, ctx => by
      sorry  -- compositional bound chase
  | _, .raise f,      h, ctx => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      simp only [KMor1.linearBound, KMor1.interp_raise]
      rw [KMor1.level0Shape_interp f hf ctx]
      -- ConstantOrShiftedProj's interp ≤ its linear bound
      sorry
  | _, .simrec _ _ _, h, ctx => by
      sorry  -- the simrec dominance proof; iterates linear

end GebLean
```

The three `sorry`s are planning markers.  The simrec
case is the largest (~80 lines); the `comp` case is
~30 lines.  The `raise` case is short once the
`ConstantOrShiftedProj.linearBound`-dominance lemma is
exhibited (consider adding as a helper).

If the simrec case proves intractable, add a private
helper `linearBound_dominates_simrec` that takes the
shapes of `h_fam` and `g_fam` explicitly.

**Do not commit `sorry`**.

- [ ] **Step 14.3: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 14.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add KMor1.linearBound + dominance (Lemma 1.A)

Structural recursion producing (c, k) constants for
linear-value-bound on level-1 K^sim terms, plus the
dominance theorem.  Conservative constants per design
choice (option α, factor-of-constant slack)."
```

---

### Task 15: `kToER_polyBound_of_level_one`

**Files**:

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

Bridge: every level-1 K^sim term, when translated via
`kToER`, has an `ERMor1.PolyBound` with degree at most 1
(linear).

**Note**: This task does *not* use `kToER_interp` (which
is what the polynomial-bound infrastructure is being built
to enable).  It proves the bound directly by structural
induction on the K^sim term.

- [ ] **Step 15.1: Append the definition**

```lean
namespace GebLean

/-- Bridge: a level-1 K^sim term, when translated via
`kToER`, has an `ERMor1.PolyBound` with degree at most 1.
Proven directly by structural induction (avoiding
circular dependency on `kToER_interp`). -/
def kToER_polyBound_of_level_one :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 1) →
      ERMor1.PolyBound (kToER f (Nat.le_succ_of_le h))
  | _, .zero,         _ => by
      -- kToER zero = ERMor1.zeroN _; degree 0
      sorry
  | _, .succ,         _ => by
      -- kToER succ = ERMor1.succ; degree 1
      sorry
  | _, .proj _,       _ => by
      -- kToER (proj i) = ERMor1.proj i; degree 1
      sorry
  | _, .comp _ _,     _ => by
      -- recurse on f and gs; combine via ERMor1.PolyBound.ofComp
      sorry
  | _, .raise _,      _ => by
      -- raise's kToER reduces to inner kToER; recurse
      sorry
  | _, .simrec _ _ _, _ => by
      -- simrec at level 1: children at level 0 ⇒ linear bound
      -- Combine kSimPackedBase + kSimPackedStep with
      -- linearBound_dominates to construct PolyBound.
      -- Degree 1 (linear).
      sorry

end GebLean
```

The six `sorry`s are planning markers.  Each constructor
case translates `kToER`'s definition (already in
`LawvereKSimER.lean`) into a `PolyBound` construction.
The simrec case is the largest (~80 lines).

**Do not commit `sorry`**.

- [ ] **Step 15.2: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 15.3: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Bridge: kToER_polyBound_of_level_one

Structural induction on level-1 KMor1 producing an
ERMor1.PolyBound on the kToER image.  Avoids circular
dependency on kToER_interp by proving the bound
directly from the K^sim structure."
```

---

### Task 16: `kSimPackedStep_polyBound` and base counterpart

**Files**:

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

Specialize Module B's `PolyBound` to `kSimPackedStep` and
`kSimPackedBase`, using Module A's `seqPackBound`.

- [ ] **Step 16.1: Append `kSimPackedStep_polyBound`**

```lean
namespace GebLean

/-- The packed simrec step has polynomial bound with
degree `2^(k+1) * D_g`, where `D_g` is the maximum
polynomial degree of the level-1 K^sim children's
`kToER` images. -/
def kSimPackedStep_polyBound {a k : ℕ}
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hg : ∀ l, (g_fam l).level ≤ 1) :
    ERMor1.PolyBound
      (kSimPackedStep
        (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le (hg l)))) := by
  -- Each kToER (g_fam l) has PolyBound (degree 1 since
  -- g_fam l is level 1; bridge via kToER_polyBound_of_level_one).
  -- kSimPackedStep is seqPack composed with kSimStepContext
  -- substitution.
  -- seqPack of (k+1) values each bounded by (sup+1)^1 has
  -- bound (sup+1)^(2^(k+1) * 1) per Module A's seqPackBound.
  -- The outer comp with kSimStepContext doesn't change the degree.
  -- Resulting degree: 2^(k+1).
  sorry

end GebLean
```

- [ ] **Step 16.2: Append `kSimPackedBase_polyBound`**

```lean
namespace GebLean

/-- The packed simrec base has polynomial bound with
degree `2^(k+1)` (linear inputs packed via seqPack). -/
def kSimPackedBase_polyBound {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (hh : ∀ l, (h_fam l).level ≤ 1) :
    ERMor1.PolyBound
      (kSimPackedBase
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le (hh l)))) := by
  sorry

end GebLean
```

Both `sorry`s are planning markers.  Each combines:

- `kToER_polyBound_of_level_one` for each child (Task 15).
- `seqPack_le_seqPackBound` from Module A (Task 3).
- `ERMor1.PolyBound.ofComp` from Module B (Task 8).

**Do not commit `sorry`**.

- [ ] **Step 16.3: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 16.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add kSimPackedStep_polyBound + kSimPackedBase_polyBound

Specialize ERMor1.PolyBound to the packed simrec step
and base, deriving degree 2^(k+1) for level-1 K^sim
children via Module A's seqPackBound and Module B's
ofComp."
```

---

### Plan amendment (2026-04-30, second): Task 17 → recursive bootstrap

After two attempts at the original Task 17 (one via Module A's
`polynomial_iter_tower_bound`, one via "direct per-component analysis"),
both BLOCKED for the same root cause: **the dominance proof for
level-2 K^sim simrec requires the dominance proof for level-1 simrec,
which requires the level-0 case**.  This is the recursive structure of
Tourlakis CN §4.2.2's Hilbert–Bernays reduction proof, where
K^sim_n ⊆ E^{n+1} is proven by induction on `n`.

**Decision**: Replace original Task 17 with **three sequential tasks
(17a, 17b, 17c) implementing the recursive bootstrap by K^sim level**.
Each level has three components:

1. `kSimTowerBound_dominates_level_<n>` — dominance proof for
   simrec at level `n`.
2. `kToER_interp_level_<n>` — interp preservation for K^sim at
   level `n`, using the dominance to convert `boundedRec` to
   `Nat.rec` via `boundedRec_eq_natRec_of_bounded`.
3. `kToER_linearBound_dominates_level_<n>` — explicit linear
   bound on `(kToER f).interp` for `f.level ≤ n`, used by the
   next level's dominance.

The original signature `kSimTowerBound_dominates_inline` (used by
Task 14 of the kToER plan) is the level-2 case (Task 17c).

Total estimated effort: 600-1000 lines of Lean across multiple
sessions.  Tasks 17a, 17b, 17c are designed to be implementable
independently (each level builds on the previous level's interp
preservation and linear bound, but its own level's dominance is
self-contained given those).

#### Why three tasks, not one

The mathematical structure of the proof requires building K^sim
level-by-level:

- **Level 0**: K^sim_0 = closure of {zero, succ, proj} under composition.
  Linear-value-bounded by `λ ctx. max ctx + constant` (via
  `level0Shape` from Task 13).  No simrec, so no dominance needed.

- **Level 1**: K^sim_1 = K^sim_0 + one simrec layer with level-0
  children.  The simrec's trace at iter j is **linear in (j, params)**
  because level-0 step is shifted-projection (additive only, no
  multiplicative coefficients on prev).  Dominance: linear ≤ tower
  (any height ≥ 1) trivially.

- **Level 2**: K^sim_2 = K^sim_1 + one simrec layer with level-1
  children.  Level-1 step is linear in inputs (per
  `KMor1.linearBound`).  Iterating linear j times gives at most
  polynomial-of-fixed-degree in (j, params) (because level-1's
  multiplicative coefficient on prev is bounded — see `linearBound`'s
  computed constants).  This polynomial fits in `tower 2 (linear)`
  by standard polynomial-vs-tower comparison.

Each level's dominance proof reuses the previous level's
`kToER_interp_level_<n-1>` to translate level-(n-1) K^sim children's
interps to their ER images.

### Task 17a: Level-0 K^sim (K^sim_0 ⊆ E^0)

**Status**: pending.  Estimated 50-150 lines.

**Files**:

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal**: prove interp preservation and explicit linear bound for
level-0 K^sim's `kToER` image.  No simrec case (vacuous at level 0),
so no dominance lemma needed at this level.

- [ ] **Step 17a.1: Add `kToER_interp_level_zero`**

```lean
/-- Interp preservation for level-0 K^sim: at level 0,
`kToER` produces an ER term whose interp equals the K^sim
interp.  Proved by structural recursion on level-0 KMor1
(no simrec or raise cases at level 0). -/
theorem kToER_interp_level_zero :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0)
      (ctx : Fin a → ℕ),
      (kToER f
        (Nat.le_succ_of_le (Nat.le_succ_of_le h))).interp
          ctx = f.interp ctx
  | _, .zero,         _, _   => by simp [kToER]
  | _, .succ,         _, _   => by simp [kToER]
  | _, .proj _,       _, _   => by simp [kToER]
  | _, .comp f gs,    h, ctx => by
      have hf : f.level ≤ 0 := …
      have hgs : ∀ i, (gs i).level ≤ 0 := …
      simp only [kToER, ERMor1.interp_comp,
        KMor1.interp_comp]
      congr 1
      funext i
      exact kToER_interp_level_zero (gs i) (hgs i) ctx
  | _, .raise _,      h, _   => by
      unfold KMor1.level at h; omega
  | _, .simrec _ _ _, h, _   => by
      unfold KMor1.level at h; omega
```

- [ ] **Step 17a.2: Add `kToER_linearBound_dominates_level_zero`**

Uses `KMor1.level0Shape` (Task 13) directly:

```lean
/-- Linear bound on level-0 K^sim's kToER image.  Given by
`level0Shape`: either `(0, k)` (constant) or `(1, k)`
(shifted projection). -/
theorem kToER_linearBound_dominates_level_zero
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0)
    (ctx : Fin a → ℕ) :
    (kToER f
      (Nat.le_succ_of_le (Nat.le_succ_of_le h))).interp
        ctx ≤
      ((KMor1.level0Shape f h).linearBound).1 *
        (Finset.univ : Finset (Fin a)).sup ctx +
      ((KMor1.level0Shape f h).linearBound).2 := by
  rw [kToER_interp_level_zero f h ctx,
    KMor1.level0Shape_interp f h ctx]
  -- Then use ConstantOrShiftedProj.linearBound_dominates
  -- (a private helper from Task 14).
  sorry
```

- [ ] **Step 17a.3: Run `lake build` and `lake test`.  Commit.**

```text
Add level-0 kToER_interp + linear bound (recursive bootstrap step 1)

Establishes the base case for the K^sim_n ⊆ E^{n+1}
recursive bootstrap.  Level 0 has no simrec, so this is
purely structural.
```

---

### Task 17b: Level-1 K^sim (K^sim_1 ⊆ E^1)

**Status**: in progress.  Estimated 600-800 lines (revised
upward after partial implementation revealed deeper structural
arithmetic).

**Progress as of 2026-04-30 (commit `c1773838`)**:

- Step 17b.1 (helper `packed_iteration_matches_simrecVec`):
  **DONE** at commit `27c66777`.
- Step 17b.2 partial: structural lemmas
  `kSimSzudzikPackList_towerHeight_ge_two` and
  `kSimPackedStep_towerHeight_ge_two` proven (both ≥ 2)
  at commit `c1773838`.  **Full dominance proof remains.**
- Steps 17b.3, 17b.4: pending.

**Files**:

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal**: prove dominance for level-1 simrec, then interp preservation
and explicit linear bound for level-1 K^sim's kToER image.

- [x] **Step 17b.1: Add level-1 simrec packed value characterisation**

Helper lemma: the iterated `Nat.rec` over `kSimPackedBase` /
`kSimPackedStep` matches `KMor1.simrecVec` of the K^sim simrec at
each iteration, when children are level 0.  Uses the round-trip
via `kSimSzudzikUnpackAt_packList`.  **DONE** at commit `27c66777`.

- [ ] **Step 17b.2: Add `kSimTowerBound_dominates_level_one`**

**Refined approach (post-c1773838 analysis)**:

The naive arithmetic approach fails because `seqPack` of (k+1)
linear values has degree `E = 6 · 4^(k+1)` — exponential in k.
For `tower (stepTH + 1) Y` to dominate `tower 1 (E · linear)`, we
need `stepTH + 1 ≥ log E + 1 = O(k)`, not just `stepTH ≥ 2`.

**Structural towerHeight strengthening required**: refine the
existing `kSimPackedStep_towerHeight_ge_two` to
`kSimPackedStep_towerHeight_ge_succ_k` proving
`(kSimPackedStep g_ER).towerHeight ≥ k + 1` (or similar function
of `k`).  This is structurally true because
`kSimSzudzikPackList` for system size k+1 has k+1 nested
`comp natPair (...)` layers, each contributing to towerHeight.

Estimated refined-structural-lemma effort: ~50-100 lines.

**Arithmetic chain after structural refinement**: once stepTH
≥ k+1 is in hand, the chain

```text
seqPack ≤ (M+2)^E ≤ 2^(E·(M+2)) ≤ tower 1 (E·(M+2))
       ≤ tower (k+2) (small + linear in M)   (using stepTH ≥ k+1)
       ≤ tower (stepTH + 1) (Y)              (Y absorbing constants)
```

closes with E = 6 · 4^(k+1) absorbed by the `tower (k+2)` height.

Estimated arithmetic chain effort: ~200-400 lines.

Approach (in order):

1. Strengthen structural lemma to `stepTH ≥ k + 1` (refine
   `kSimSzudzikPackList_towerHeight_ge_two` by induction on `k`,
   tracking per-Szudzik-level depth contribution).
2. Use Step 17b.1 to convert iterated value to seqPack of simrecVec.
3. Apply `KMor1.linearBound_dominates` to bound each simrecVec
   component linearly.
4. Apply `Nat.seqPack_le_seqPackBound` (with d=1) to bound the
   seqPack by `(M+2)^E`.
5. Convert `(M+2)^E` to `tower 1 (E · (M+2))` via `pow_le_two_pow`
   style estimate.
6. Use the structural `stepTH ≥ k+1` to dominate by
   `tower (stepTH+1) Y` for appropriate Y.
7. Show Y matches `kSimTowerBound`'s closed form (linear in
   sumCtx, with constants absorbed by 2*BH and TH+1).

- [ ] **Step 17b.3: Add `kToER_interp_level_one`**

Uses `boundedRec_eq_natRec_of_bounded` with the dominance from
Step 17b.2 to convert the boundedRec back to `Nat.rec`, then
matches with `KMor1.simrecVec` for the simrec case.

```lean
theorem kToER_interp_level_one :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
      (ctx : Fin a → ℕ),
      (kToER f (Nat.le_succ_of_le h)).interp ctx =
        f.interp ctx
```

Six structural cases (zero/succ/proj/comp/raise/simrec); the simrec
case uses `kSimTowerBound_dominates_level_one`.

- [ ] **Step 17b.4: Add `kToER_linearBound_dominates_level_one`**

Uses `kToER_interp_level_one` to translate K^sim's
`KMor1.linearBound_dominates` to the ER side.

- [ ] **Step 17b.5: Run `lake build` and `lake test`.  Commit.**

```text
Add level-1 dominance + kToER_interp + linear bound (recursive bootstrap step 2)

K^sim_1 ⊆ E^1: level-1 K^sim's kToER image preserves interp,
dominates linearly via `KMor1.linearBound`.  Simrec case
discharges dominance directly (level-0 children give linear
trace).
```

---

### Task 17c: Level-2 K^sim (K^sim_2 ⊆ E^2 = ER), final assembly

**Status**: pending.  Estimated 300-500 lines.

**Files**:

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal**: prove dominance for level-2 simrec.  This is the original
Task 17's `kSimTowerBound_dominates_inline` lemma — the deliverable
of the polynomial-bound sub-project.

- [ ] **Step 17c.1: Add `kSimTowerBound_dominates_inline`**

Uses Task 17b's `kToER_interp_level_one` and
`kToER_linearBound_dominates_level_one` to:

1. Translate each level-1 child's kToER interp via Task 17b's
   interp preservation.
2. Bound each child's interp linearly via Task 17b's linear bound.
3. Apply per-component analysis: each output's value at iter j
   corresponds to `KMor1.simrecVec` (from `LawvereKSimInterp.lean`).
4. Bound the seqPack via `Nat.seqPack_le_seqPackBound` (Task 3).
5. Bound the resulting polynomial by `kSimTowerBound`'s tower form,
   exploiting that the polynomial degree is fixed (constant in K^sim
   term structure, not growing with j).

```lean
theorem kSimTowerBound_dominates_inline {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (j : ℕ) (params : Fin a → ℕ) :
    Nat.rec ... ≤ ...
```

- [ ] **Step 17c.2: Run `lake build` and `lake test`.  Commit.**

```text
Add kSimTowerBound_dominates_inline (final dominance assembly)

K^sim_2 ⊆ E^2 = ER: level-2 simrec's packed iteration
trace is bounded by tower 2 of linear-in-(j, params),
dominated by kSimTowerBound's tower (TH+1) (linear)
form for TH ≥ 1.  Uses Task 17b's level-1 interp
preservation and linear bound to translate level-1
children's K^sim interps to ER bounds, then applies
seqPack polynomial bound (Task 3) for the packed
recursion.
```

---

### Cross-session continuity notes

After Tasks 17a, 17b, 17c land (across multiple sessions if needed):

- Task 14 of the kToER plan
  (`docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`) becomes
  unblocked.  Its simrec case dispatches to
  `kSimTowerBound_dominates_inline` (Task 17c's deliverable).

- The full forward direction K^sim_2 ⊆ ER is then formalized,
  enabling the eventual categorical equivalence
  K^sim_2 ≌ LawvereERCat (Phase 2 sub-project 4).

- Task 17a, 17b, 17c may be subdivided further at dispatch time
  if individual steps prove intractable (e.g., the dominance
  proof at level 2 may need its own private helper for the
  per-component analysis).

### Why this matches the literature

Tourlakis CN §4.2.2 (Hilbert–Bernays reduction) and Tourlakis
2018 §0.1.0.34 (E^2 closure under simultaneous bounded recursion)
both prove K^sim_n closure via induction on `n`, reducing
simultaneous recursion to single recursion via an encoding
function (Gödel multiplicative or Cantor pairing).  Each level's
proof uses the previous level's closure result.

Our recursive-bootstrap structure (Task 17a → 17b → 17c) directly
mirrors this published proof, with Szudzik pairing as the encoding
function (in place of Gödel or Cantor — both polynomial-bounded,
per Task 3).  No novel mathematical content; the work is the
Lean formalization of established results.

---

### Task 18: Module C tests

**Files**:

- Create: `GebLeanTests/LawvereKSimPolynomialBound.lean`

- [ ] **Step 18.1: Create the test file**

```lean
import GebLean.LawvereKSimPolynomialBound
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereKSimPolynomialBound

`#guard` checks for `level0Shape` on atomic K^sim terms,
plus end-to-end test for `linearBound_dominates` and
`kSimTowerBound_dominates_inline` on `addK`.
-/

open GebLean

private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]

-- level0Shape on zero: const 0
example : KMor1.level0Shape (KMor1.zero (n := 0))
    (by simp [KMor1.level]) = .const 0 := rfl

-- level0Shape on succ: shifted 0 1
example : KMor1.level0Shape KMor1.succ
    (by simp [KMor1.level]) = .shifted 0 1 := rfl

-- level0Shape on proj 0
example : KMor1.level0Shape (KMor1.proj (0 : Fin 2))
    (by simp [KMor1.level]) = .shifted 0 0 := rfl

-- linearBound on addK (level-1 simrec example)
private def addK : KMor1 2 :=
  KMor1.simrec (k := 0) (a := 1)
    (0 : Fin 1)
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 1))
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.succ
        (fun _ : Fin 1 => KMor1.proj (2 : Fin 3)))

private theorem addK_level : addK.level ≤ 1 := by decide

-- linearBound dominance test on addK at small inputs
example : addK.interp (ctx2 3 5) ≤
    (KMor1.linearBound addK addK_level).1 *
      (Finset.univ : Finset (Fin 2)).sup (ctx2 3 5) +
    (KMor1.linearBound addK addK_level).2 :=
  KMor1.linearBound_dominates addK addK_level (ctx2 3 5)

-- End-to-end: kSimTowerBound_dominates_inline on addK
private def addK_h_fam : Fin 1 → KMor1 1 :=
  fun _ : Fin 1 => KMor1.proj (0 : Fin 1)
private def addK_g_fam : Fin 1 → KMor1 (1 + 1 + 1) :=
  fun _ : Fin 1 =>
    KMor1.comp KMor1.succ
      (fun _ : Fin 1 => KMor1.proj (2 : Fin 3))

private theorem addK_h_fam_level : ∀ l,
    (addK_h_fam l).level ≤ 1 :=
  fun _ => by simp [addK_h_fam, KMor1.level]

private theorem addK_g_fam_level : ∀ l,
    (addK_g_fam l).level ≤ 1 :=
  fun _ => by simp [addK_g_fam, KMor1.level]

example (j : ℕ) (params : Fin 1 → ℕ) :
    Nat.rec
      ((kSimPackedBase
          (fun l => kToER (addK_h_fam l)
            (Nat.le_succ_of_le (addK_h_fam_level l))
          )).interp params)
      (fun i prev =>
        (kSimPackedStep
          (fun l => kToER (addK_g_fam l)
            (Nat.le_succ_of_le (addK_g_fam_level l))
          )).interp
          (Fin.cons i (Fin.cons prev params)))
      j ≤
      (kSimTowerBound
        (fun l => kToER (addK_h_fam l)
          (Nat.le_succ_of_le (addK_h_fam_level l)))
        (fun l => kToER (addK_g_fam l)
          (Nat.le_succ_of_le (addK_g_fam_level l)))).interp
        (Fin.cons j params) :=
  kSimTowerBound_dominates_inline addK_h_fam addK_g_fam
    addK_h_fam_level addK_g_fam_level j params
```

- [ ] **Step 18.2: Run `lake test`**

Expected: PASS.

- [ ] **Step 18.3: Commit**

```bash
git add GebLeanTests/LawvereKSimPolynomialBound.lean
git commit -m "Add tests for LawvereKSimPolynomialBound

level0Shape #guards on atomic terms, linearBound
dominance test on addK, and end-to-end
kSimTowerBound_dominates_inline test on addK."
```

---

## Phase D: Integration

### Task 19: Re-export new modules

**Files**:

- Modify: `GebLean.lean`
- Modify: `GebLeanTests.lean`

- [ ] **Step 19.1: Add imports to `GebLean.lean`**

Add these lines to `GebLean.lean` in alphabetical order:

```lean
import GebLean.LawvereERPolynomialBound
import GebLean.LawvereKSimPolynomialBound
import GebLean.Utilities.ComputationalComplexity
```

`LawvereERPolynomialBound` and `LawvereKSimPolynomialBound`
go near the other `LawvereER*` and `LawvereKSim*` imports;
`Utilities.ComputationalComplexity` goes near the other
`Utilities.*` imports.

- [ ] **Step 19.2: Add test imports to `GebLeanTests.lean`**

Add these lines to `GebLeanTests.lean`:

```lean
import GebLeanTests.LawvereERPolynomialBound
import GebLeanTests.LawvereKSimPolynomialBound
import GebLeanTests.Utilities.ComputationalComplexity
```

- [ ] **Step 19.3: Run `lake build` and `lake test`**

Expected: PASS for both, no warnings.

- [ ] **Step 19.4: Commit**

```bash
git add GebLean.lean GebLeanTests.lean
git commit -m "Re-export polynomial-bound modules

Register Module A (Utilities/ComputationalComplexity),
Module B (LawvereERPolynomialBound), and Module C
(LawvereKSimPolynomialBound) in the library entry point
and test driver."
```

---

### Task 20: Update kToER plan

**Files**:

- Modify: `docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`

Annotate Task 14 of the kToER plan to reflect the new
infrastructure availability.

- [ ] **Step 20.1: Update the plan amendment section**

Locate the "Plan amendment (2026-04-30): bound-dominance
deferral" section.  Append a new paragraph:

```markdown
### Update: polynomial-bound infrastructure landed

The polynomial-bound sub-project
(`docs/plans/2026-04-30-er-polynomial-bound-design.md`
and `docs/plans/2026-04-30-er-polynomial-bound-plan.md`)
has landed.  Task 14 below should now use Module C's
`kSimTowerBound_dominates_inline` to discharge the
dominance hypothesis (along with
`kSimTowerBound_mono_counter` for monotonicity).
The "revision required" annotation on Task 14 is
superseded by this update.
```

- [ ] **Step 20.2: Update Task 14's annotation**

Locate Task 14's "Revision required (2026-04-30)" note.
Replace its body with:

```markdown
> **Revision required (2026-04-30, updated)**: per the
> plan amendment, the simrec case of this theorem
> discharges the dominance hypothesis of
> `boundedRec_eq_natRec_of_bounded` using
> `GebLean.kSimTowerBound_dominates_inline` (from
> `LawvereKSimPolynomialBound.lean`) and
> `GebLean.kSimTowerBound_mono_counter` (from
> `Utilities/KSimSzudzikSimrec.lean`).  When dispatching
> this task, the implementer prompt should walk through
> the simrec case using these named lemmas.
```

- [ ] **Step 20.3: Verify markdown lint passes**

```bash
markdownlint-cli2 docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md
```

Expected: 0 errors.

- [ ] **Step 20.4: Commit**

```bash
git add docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md
git commit -m "Update kToER plan: polynomial-bound infrastructure landed

Annotate Task 14 to use the new
kSimTowerBound_dominates_inline assembly from Module C
(LawvereKSimPolynomialBound).  Supersedes the previous
'revision required' note."
```

---

### Task 21: Final verification

**Files**:

- (no source modifications)

- [ ] **Step 21.1: Full build**

```bash
lake build
```

Expected: PASS, no warnings, no errors.

- [ ] **Step 21.2: Full test suite**

```bash
lake test
```

Expected: PASS.

- [ ] **Step 21.3: `sorry` audit**

```bash
grep -rn "sorry\|admit" \
  GebLean/Utilities/ComputationalComplexity.lean \
  GebLean/LawvereERPolynomialBound.lean \
  GebLean/LawvereKSimPolynomialBound.lean \
  GebLeanTests/Utilities/ComputationalComplexity.lean \
  GebLeanTests/LawvereERPolynomialBound.lean \
  GebLeanTests/LawvereKSimPolynomialBound.lean
```

Expected: no matches.

- [ ] **Step 21.4: Banned-word audit**

```bash
PATTERN='fundamental|insight|advanced|simple|simpler'
PATTERN+='|advantage|benefit|important|challenge'
PATTERN+='|incomplete|future|issue|problem|block'
PATTERN+='|wait|hmm|sorry|careful|difficult|blocked'
grep -rniE "$PATTERN" \
  GebLean/Utilities/ComputationalComplexity.lean \
  GebLean/LawvereERPolynomialBound.lean \
  GebLean/LawvereKSimPolynomialBound.lean \
  GebLeanTests/Utilities/ComputationalComplexity.lean \
  GebLeanTests/LawvereERPolynomialBound.lean \
  GebLeanTests/LawvereKSimPolynomialBound.lean
```

Expected: no matches in source comments or docstrings.

- [ ] **Step 21.5: Markdown lint of plan and design docs**

```bash
markdownlint-cli2 \
  docs/plans/2026-04-30-er-polynomial-bound-design.md \
  docs/plans/2026-04-30-er-polynomial-bound-plan.md
```

Expected: no errors.

- [ ] **Step 21.6: Confirm interp-preservation discipline**

For each named ER-side construct in the new modules,
confirm there is at least one `@[simp]`-tagged interp or
characterisation lemma:

- `Nat.pair_le_sq` — bound lemma (no `@[simp]` needed
  since not a closed-form).
- `Nat.seqPackBound` + `seqPack_le_seqPackBound` — bound
  lemma.
- `Nat.polynomial_iter_tower_two_bound` — analytic
  lemma.
- `tower_succ_pow_bound` — helper.
- `ERMor1.PolyBound` and per-constructor builders — data;
  no `@[simp]` needed.
- `ERMor1.PolyBound.log_le_towerHeight` — bound lemma.
- `KMor1.level0Shape`, `level0Shape_interp` — interp
  characterisation; consider `@[simp]` on
  `level0Shape_interp`.
- `KMor1.linearBound`, `linearBound_dominates` — bound.
- `kSimPackedStep_polyBound`,
  `kSimPackedBase_polyBound` — data.
- `kSimTowerBound_dominates_inline` — bound.

Add `@[simp]` where appropriate per project convention
(see existing `Utilities/Tower.lean` and
`Utilities/SzudzikSeq.lean`).  Commit any additions.

- [ ] **Step 21.7: Commit any final-verification fixes**

If steps 21.3–21.6 surfaced fixes:

```bash
git commit -m "Final verification fixes: <short description>"
```

If no fixes were needed, no commit is required.

---

## Summary of deliverables

By the end of Task 21, the repository contains:

- `GebLean/Utilities/ComputationalComplexity.lean`
  (Module A) with `Nat.pair_le_sq`, `Nat.seqPackBound`,
  `tower_succ_pow_bound`,
  `Nat.polynomial_iter_tower_two_bound`.
- `GebLean/LawvereERPolynomialBound.lean` (Module B)
  with `ERMor1.PolyBound` data structure, per-constructor
  builders, `log_le_towerHeight`, and `to_iter_step_form`.
- `GebLean/LawvereKSimPolynomialBound.lean` (Module C)
  with `ConstantOrShiftedProj`, `level0Shape`,
  `linearBound`, `kToER_polyBound_of_level_one`,
  `kSimPackedStep_polyBound`,
  `kSimPackedBase_polyBound`, and
  `kSimTowerBound_dominates_inline`.
- Three corresponding test modules under `GebLeanTests/`.
- Updated re-export files (`GebLean.lean`,
  `GebLeanTests.lean`).
- Updated kToER plan annotated to use the new
  infrastructure.

The kToER plan's Task 14 (`kToER_interp`) is now
unblocked: its dispatch can use
`kSimTowerBound_dominates_inline` as the dominance
witness.
