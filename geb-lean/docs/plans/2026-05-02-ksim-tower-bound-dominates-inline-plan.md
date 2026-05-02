# `kSimTowerBound_dominates_inline` (level-2 dominance) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** discharge the Phase IV-B headline theorem
`kSimTowerBound_dominates_inline` (level-2 K^sim simrec
dominance) as a structural mirror of the existing level-1
`kSimTowerBound_dominates_level_one`
(`LawvereKSimPolynomialBound.lean:2578`), routing through
`KMor1.linearBound` (Lemma 1.A) on level-1 K^sim children +
the existing polynomial-iter-tower chain.

**Architecture:** mirrors level-1 in proof structure exactly.
The substitutions at level 2:

Substitutions at level 2 (vs level 1 at line 2578+):

- Per-l children's bound source:
  level-0 `KMor1.level0Shape` (Lemma 1.B) becomes
  level-1 `KMor1.linearBound` (Lemma 1.A).
- Closed-form polynomial bound on iter:
  level-1 routes via `simrecVec_seqPack_le_pow` (closed
  form on the pack); level-2 routes via
  `kSimPackedBase/Step_polyBound` + polynomial-iter-tower
  with a polynomial base.
- Log-vs-tH absorption:
  level-1 uses `stepTH_baseTH_dominates_arg`
  (level-0 children); level-2 uses
  `linearBoundLog_packedStep_le_towerHeight_level_two`
  (level-1 children, via existing
  `KMor1.linearBoundLog_le_towerHeight` at line 1828).

**Tech stack:** Lean 4, mathlib, `lake build` / `lake test`.

**Convention:** every committed task ends in a clean `lake
build` plus `lake test`, with commit subject ending in
`(plan v4 TN)`.  No `sorry` or `admit` in committed state, no
warnings, no banned vocabulary.

**Literature source:** at every task, the Lean lemma cites
the exact published proposition or in-codebase lemma it
discharges.  See
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
(henceforth "research doc") for the citation network.

---

## Plan-level literature trace

The published proof of `K^sim_2 ⊆ ER` routes through these
propositions, in order of consumption by the level-2 chain:

1. **Lemma 1.A** (research doc lines 51-153): every level-1
   K^sim function has a linear bound `c · max(ctx) + k`.
   Already implemented as `KMor1.linearBound` (Poly Task 14)
   and `KMor1.linearBound_dominates`
   (`LawvereKSimPolynomialBound.lean:507`).
2. **Tourlakis 2018 §0.1.0.34** (Theorem on E^2 closure under
   simultaneous bounded recursion): the K^sim simrec's packed
   step has a polynomial bound when the children do.  Already
   implemented as `kSimPackedBase_polyBound` /
   `kSimPackedStep_polyBound` (Poly Task 16, lines 738 / 817).
3. **Recursion Class Ch. 4 Prop. 4.7** (research doc lines
   485-518): the iteration of a polynomial-bounded step is
   in `E^3 = ER`, bounded by `e_3(max + m·j) ≈ tower 2 (linear
   in (j, x))`.  Implemented as `Nat.polynomial_iter_tower_bound`
   for the LINEAR-base case (Poly Task 5, line 471 of
   `Utilities/ComputationalComplexity.lean`).  This plan
   adds Task T2 to handle the POLYNOMIAL-base case (since
   level-2's packed base has degree `2^k`, not linear).
4. **Wong's Prop. 4.6 exponent-tracking** (research doc lines
   263-323): `Nat.log 2 (linearBound₁ + linearBound₂ + 1) ≤ 3
   · towerHeight + 1` for level-1 K^sim.  Already implemented
   as `KMor1.linearBoundLog_le_towerHeight`
   (`LawvereKSimPolynomialBound.lean:1828`).
5. **Tourlakis 2018 §0.1.0.27 (3)** + the `pow ≤ tower`
   conversion: polynomial-of-tower-height becomes
   tower-with-linear-inside via standard `pow_le_tower`
   monotonicity.  Already implemented as
   `Nat.pow_le_tower_two_with_shift` (Utilities) and
   `Nat.tower_two_le_tower_three_linear` (Utilities).

---

## File structure

The plan modifies one existing utility module and one
existing K^sim module; no new files.

- **Modify** `GebLean/Utilities/ComputationalComplexity.lean`:
  add `Nat.polynomial_iter_tower_bound_with_pow_base`
  (~150 lines).
- **Modify** `GebLean/LawvereKSimPolynomialBound.lean`: add
  `kToER_polyBound_at_level_one_via_linearBound` (~60 lines),
  `linearBoundLog_packedStep_le_towerHeight_level_two`
  (~120 lines), and the public theorem
  `kSimTowerBound_dominates_inline` (~250 lines).

Total estimated effort: ~580 lines added across two files.

---

## Task T1: `kToER_polyBound_at_level_one_via_linearBound`

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (insert
  after `KMor1.linearBound_dominates` at line 507, before the
  level-1 dominance helpers at line 1518+).

**Goal:** non-recursive construction of an `ERMor1.PolyBound`
at degree 1 for any level-≤-1 K^sim term's ER translation.

**Literature reference:** research doc Lemma 1.A (lines 51-153).
The construction uses `kToER_interp_level_one` (line 2711)
to convert ER interp to K^sim interp, then
`KMor1.linearBound_dominates` (line 507) to get the linear
bound on the K^sim interp.  No recursion on `KMor1` structure
required.

This is the literature-aligned replacement for plan v2's D.2
(`kToER_polyBound_of_level_one`, deferred per the
`LawvereKSimPolynomialBound.lean:27-47` docstring).

- [ ] **Step T1.1: State the function**

```lean
/-- PolyBound (at degree 1) for the ER translation of a
level-≤-1 K^sim term.  Non-recursive: uses
`kToER_interp_level_one` to reduce the ER interp to the K^sim
interp, then `KMor1.linearBound_dominates` for the linear
bound (Lemma 1.A from the research doc).

Replaces the impossible-by-recursion plan-v2 D.2; see the
docstring at the top of this file for the original deferral
reasoning, which becomes moot once `kToER_interp_level_one`
is available. -/
def kToER_polyBound_at_level_one_via_linearBound
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1) :
    ERMor1.PolyBound (kToER f (Nat.le_succ_of_le h)) := _
```

The transient `_` triggers an "unsolved goals" build error
that exposes the expected return type — use it to inspect.

- [ ] **Step T1.2: Implement the function**

```lean
def kToER_polyBound_at_level_one_via_linearBound
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1) :
    ERMor1.PolyBound (kToER f (Nat.le_succ_of_le h)) where
  degree := 1
  coefficient := (KMor1.linearBound f h).1
  constant := (KMor1.linearBound f h).2
  bounds := fun ctx => by
    rw [kToER_interp_level_one f h ctx]
    have h_dom :=
      KMor1.linearBound_dominates f h ctx
    -- Goal: f.interp ctx ≤
    --   (linearBound).1 * (maxCtx ctx + 1)^1 + (linearBound).2
    -- We have: f.interp ctx ≤ (linearBound).1 * sup ctx
    --                       + (linearBound).2
    -- Note: (maxCtx ctx + 1)^1 = maxCtx ctx + 1 ≥ sup ctx
    -- (since maxCtx = sup for non-empty ctx; for a = 0 the
    --  conclusion holds trivially).
    simp only [pow_one]
    have h_sup_le : (Finset.univ : Finset (Fin a)).sup ctx ≤
        maxCtx ctx + 1 := by
      cases a with
      | zero => simp [maxCtx]
      | succ n => simp [maxCtx]; omega
    have h_mul :
        (KMor1.linearBound f h).1 *
          (Finset.univ : Finset (Fin a)).sup ctx ≤
        (KMor1.linearBound f h).1 * (maxCtx ctx + 1) :=
      Nat.mul_le_mul_left _ h_sup_le
    omega
```

The `pow_one` simp closes `(_)^1 = _`.  The `cases a` deals
with the empty-context corner case (where `Finset.sup ctx` is
defined as 0 and `maxCtx ctx` is also 0, so the inequality
holds vacuously).

If the exact relationship between `Finset.univ.sup ctx` and
`maxCtx ctx` requires a different lemma in the codebase
(e.g. `maxCtx_eq_sup` or similar), the implementer adjusts.
Cap the proof at ~50 lines.

- [ ] **Step T1.3: Run `lake build`**

```bash
lake build
```

Expected: PASS, no warnings.

- [ ] **Step T1.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kToER_polyBound_at_level_one_via_linearBound (plan v4 T1)

Adds a non-recursive PolyBound (at degree 1) for level-≤-1
K^sim translations, via kToER_interp_level_one (line 2711)
+ KMor1.linearBound_dominates (line 507).

Literature reference: research doc Lemma 1.A (lines 51-153)
documents the linear bound on level-1 K^sim.  This task lifts
that bound through the ER translation.

Replaces plan v2's deferred recursive bridge
kToER_polyBound_of_level_one (impossible at the simrec case
because the ER translation involves super-polynomial
boundedRec, but trivially constructible non-recursively
using interp-preservation).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T2: `Nat.polynomial_iter_tower_bound_with_pow_base`

**Files:**

- Modify: `GebLean/Utilities/ComputationalComplexity.lean`
  (insert after `polynomial_iter_tower_bound` at line 471,
  before `tower_two_le_tower_three_linear` at line 558).

**Goal:** add a polynomial-base variant of
`Nat.polynomial_iter_tower_bound`.  The existing version
requires a linear base `v_0 x ≤ m * x + m`; the level-2
chain needs to handle a polynomial base because
`kSimPackedBase_polyBound`'s output has degree `2^k`, not 1.

**Literature reference:** Recursion Class Ch. 4 Prop. 4.7
(n=2 case, research doc lines 485-518): "Specifically for
`n = 2` (the case we need for level-2 K^sim simrec): if
`step` is in `E^2` (polynomial-bounded), then `step^j` is
bounded in `E^3 = ER` by `e_3(max(x, y) + m · j)` for some
constant `m` extracted from the polynomial bound on the step."

The polynomial-base variant generalizes the BASE input to
also be polynomial.  The conclusion shape is preserved (tower
2 of linear in inputs and `j`).

This is plan v2's D.0.C, now correctly motivated by the
literature (rather than as a workaround).

- [ ] **Step T2.1: State the theorem**

```lean
/-- Polynomial-base variant of
`Nat.polynomial_iter_tower_bound`: iterating a polynomially-
bounded step `j` times, starting from a polynomially-
bounded base, keeps the value bounded by `tower 2 (linear in
(j, x, log D, log D_base, m_base))`.

Required at the level-2 K^sim simrec dominance chain
(`kSimTowerBound_dominates_inline`, plan v4 T4) where
`kSimPackedBase`'s polynomial degree is `2^k` (the seqPack
of `(k + 1)` linear-bound children doubles the degree per
pairing application).

Mirrors the `n = 2` case of Recursion Class Ch. 4 Prop. 4.7
(research doc Claim 4, lines 485-518): the ER bound on the
iterated polynomial step is `e_3(max + m · j)` ≈ `tower 2
(linear)` in our `tower` convention. -/
theorem Nat.polynomial_iter_tower_bound_with_pow_base
    (step : ℕ → ℕ → ℕ) (D D_base m_base : ℕ)
    (h_step : ∀ v x, step v x ≤ (max v x + 1) ^ D)
    (v_0 : ℕ → ℕ)
    (h_base : ∀ x, v_0 x ≤
      (m_base * x + m_base + 1) ^ D_base)
    (j x : ℕ) :
    Nat.iterate (fun v => step v x) j (v_0 x) ≤
      GebLean.tower 2
        ((Nat.log 2 D + 2) * (j + 1) +
         (Nat.log 2 D_base + 2) +
         m_base * x + m_base + x +
         Nat.log 2 D + 2) := _
```

The exact constants in the linear-inside are settled by the
proof; the implementer may adjust if the algebra closes
cleaner with slightly different constants — provided the
chain in T4 still closes.

- [ ] **Step T2.2: Prove the theorem**

Strategy: induction on `j`, mirroring
`Nat.polynomial_iter_tower_bound`'s proof
(`Utilities/ComputationalComplexity.lean:471-557`) but
replacing the base case with a `pow_le_tower_two_with_shift`-
style lift of `(m_base * x + m_base + 1)^D_base` to `tower 2
(linear)`.

```lean
theorem Nat.polynomial_iter_tower_bound_with_pow_base
    -- (signature as above) := by
  induction j with
  | zero =>
      simp only [Nat.iterate]
      have h0 : v_0 x ≤
          (m_base * x + m_base + 1) ^ D_base := h_base x
      have h_pow_le_tower :
          (m_base * x + m_base + 1) ^ D_base ≤
          GebLean.tower 2
            (m_base * x + m_base + Nat.log 2 D_base + 2) := by
        -- Apply pow_le_tower_two_with_shift with
        -- CC = 1, S = m_base * x + m_base, KK = 0,
        -- E = D_base.
        _  -- transient, fills via pow_le_tower_two_with_shift
      -- Bound the inner argument.
      have h_arg_le :
          m_base * x + m_base + Nat.log 2 D_base + 2 ≤
          (Nat.log 2 D + 2) * (0 + 1) +
          (Nat.log 2 D_base + 2) +
          m_base * x + m_base + x +
          Nat.log 2 D + 2 := by omega
      exact le_trans h0
        (le_trans h_pow_le_tower
          (GebLean.tower_mono_right 2 h_arg_le))
  | succ j ih =>
      -- Mirror polynomial_iter_tower_bound's succ case
      -- with the larger linear-inside argument.
      _  -- transient, fills via existing pattern
```

The succ-case algebra is identical to
`polynomial_iter_tower_bound`'s succ case, with the linear-
inside argument adjusted to include the `Nat.log 2 D_base + 2`
term.  Cap the proof at ~150 lines.

- [ ] **Step T2.3: Run `lake build` + `lake test`**

```bash
lake build && lake test
```

Expected: PASS, no warnings.

- [ ] **Step T2.4: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "$(cat <<'EOF'
Nat.polynomial_iter_tower_bound_with_pow_base (plan v4 T2)

Polynomial-base variant of polynomial_iter_tower_bound.
Required for the level-2 K^sim simrec dominance chain because
kSimPackedBase's polynomial degree is 2^k (the seqPack of
(k+1) linear-bound children doubles the degree per pairing),
not linear.

Literature reference: Recursion Class Ch. 4 Prop. 4.7
(n = 2 case; research doc Claim 4, lines 485-518).  The
ER bound on the iterated polynomial step is e_3(max + m · j)
≈ tower 2 (linear in (j, x)) in our tower convention.

Proof mirrors polynomial_iter_tower_bound's induction with
the base case lifted via pow_le_tower_two_with_shift.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T3: `linearBoundLog_packedStep_le_towerHeight_level_two`

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (insert
  after `stepTH_baseTH_dominates_arg` at line 2226, before
  `simrecVec_uniform_linear_bound` at line 2427).

**Goal:** prove the level-2 chain-closing log-vs-tH
inequality.  Level-2 analog of the existing
`stepTH_baseTH_dominates_arg` (line 2226), routing through
`KMor1.linearBoundLog_le_towerHeight` (line 1828) per-l on
level-1 K^sim children instead of `level0Shape`-derived
constants on level-0 K^sim children.

**Literature reference:** Wong's Prop. 4.6 exponent-tracking
recipe (research doc lines 263-323): for level-1 K^sim,
`Nat.log 2 (linearBound₁ + linearBound₂ + 1) ≤ 3 · (kToER f).towerHeight + 1`.
Aggregated over `(k + 1)` children and through the
packed-step's structural towerHeight.

- [ ] **Step T3.1: State the theorem**

```lean
/-- Chain-closing log-vs-tH inequality for the level-2
simrec dominance.  Level-2 analog of
`stepTH_baseTH_dominates_arg` (line 2226), with `level0Shape`
replaced by `KMor1.linearBound` and the inner log absorption
routed through `KMor1.linearBoundLog_le_towerHeight`
(line 1828, the public Step-2 deliverable). -/
private theorem linearBoundLog_packedStep_le_towerHeight_level_two
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1) :
    let h_ER : Fin (k + 1) → ERMor1 a :=
      fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
    let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
      fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).1) 0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).2) 0)
      + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (h_fam l) (h_h l)).2) 0
    Nat.log 2 (CC + 1) +
      Nat.log 2 (KK + Nat.log 2 (6 * 4 ^ (k + 1)) + 4) ≤
        (kSimPackedStep g_ER).towerHeight +
          2 * (kSimPackedBase h_ER).towerHeight + 1 := _
```

The shape mirrors `stepTH_baseTH_dominates_arg`'s exactly,
with `level0Shape (...) (...).linearBound.X` replaced by
`KMor1.linearBound (...) (h_X l).X`.

The exponent `6 * 4^(k+1)` matches `simrecVec_seqPack_le_pow`
(line 2509+).  At level 2 the exponent is the same (it
depends only on the pairing structure, not on the children's
level).

- [ ] **Step T3.2: Prove the theorem**

Strategy: mirror the proof of `stepTH_baseTH_dominates_arg`
(line 2226+), substituting `level0Shape ... .linearBound` with
`KMor1.linearBound ...` throughout.  Use
`KMor1.linearBoundLog_le_towerHeight` (line 1828) to bound
each child's `Nat.log 2 (linearBound₁ + linearBound₂ + 1)`
by `3 · (kToER child).towerHeight + 1`.

Aggregate over the `(k + 1)` children and combine with
`kSimPackedStep_towerHeight_ge_succ_k` (line 1376, gives
`stepTH ≥ k + 2`) and `kSimPackedBase_towerHeight_ge_*`
(if a similar lower-bound lemma exists; otherwise add a
small private helper).

Cap the proof at ~120 lines.  If a sub-step requires a
helper lemma that doesn't exist, the implementer may add a
small `private theorem` adjacent.

- [ ] **Step T3.3: Run `lake build`**

Expected: PASS, no warnings.

- [ ] **Step T3.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
linearBoundLog_packedStep_le_towerHeight_level_two (plan v4 T3)

Level-2 chain-closing log-vs-tH inequality.  Level-2 analog
of stepTH_baseTH_dominates_arg (line 2226) with level0Shape
replaced by KMor1.linearBound and the inner log absorption
routed through KMor1.linearBoundLog_le_towerHeight (line 1828).

Literature reference: Wong's Prop. 4.6 exponent-tracking
(research doc lines 263-323).  Aggregates the per-l log bound
over (k + 1) level-1 K^sim children, through the packed step's
structural towerHeight.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T4: `kSimTowerBound_dominates_inline` (headline)

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (insert
  after `kSimTowerBound_dominates_level_one` at line 2703,
  before `kToER_interp_level_one` at line 2711).

**Goal:** prove the Phase IV-B headline theorem.  Public.
Mirrors `kSimTowerBound_dominates_level_one` (line 2578)
calc-by-calc, with substitutions per the plan-level
literature trace.

**Literature reference:** Tourlakis 2018 §0.1.0.34 (E^2
closure under simultaneous bounded recursion) + Recursion
Class Ch. 4 Prop. 4.7 (n = 2 case).  Combined: the level-2
K^sim simrec's iter is bounded by `tower 2 (linear in (j, x))`
which dominates `kSimTowerBound`'s closed-form
`tower (stepTH + 1) (linear)`.

- [ ] **Step T4.1: State the headline**

```lean
/-- Phase IV-B headline: level-2 simrec dominance via the
polynomial-iter chain through level-1 K^sim children's linear
bounds.  Mirrors `kSimTowerBound_dominates_level_one`
(line 2578) at level 2 with `KMor1.linearBound` (Lemma 1.A)
replacing `level0Shape` (Lemma 1.B) on the children.

Literature reference: Tourlakis 2018 §0.1.0.34 + Recursion
Class Ch. 4 Prop. 4.7 (n = 2 case).

Used by `kToER_interp` at level ≤ 2 (kToER plan Task 14). -/
theorem kSimTowerBound_dominates_inline {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (j : ℕ) (params : Fin a → ℕ) :
    Nat.rec
      ((kSimPackedBase
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le (h_h l)))).interp params)
      (fun i prev =>
        (kSimPackedStep
          (fun l => kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l)))).interp
        (Fin.cons i (Fin.cons prev params)))
      j ≤
      (kSimTowerBound
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le (h_h l)))
        (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le (h_g l)))).interp
        (Fin.cons j params) := _
```

- [ ] **Step T4.2: Set up abbreviations**

Mirror lines 2605-2636 of `kSimTowerBound_dominates_level_one`,
with two changes:

1. `KMor1.level0Shape (g_fam l) (h_g l)).linearBound.X`
   becomes `(KMor1.linearBound (g_fam l) (h_g l)).X`.
2. The hypothesis on children is `level ≤ 1`, not `level ≤ 0`.

```lean
  set h_ER : Fin (k + 1) → ERMor1 a :=
    fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
    with h_ER_def
  set g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
    fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
    with g_ER_def
  -- Build per-l PolyBounds at degree 1 via T1.
  have pb_h : (l : Fin (k + 1)) →
      ERMor1.PolyBound (h_ER l) :=
    fun l => kToER_polyBound_at_level_one_via_linearBound
      (h_fam l) (h_h l)
  have pb_g : (l : Fin (k + 1)) →
      ERMor1.PolyBound (g_ER l) :=
    fun l => kToER_polyBound_at_level_one_via_linearBound
      (g_fam l) (h_g l)
  -- Build the packed PolyBounds via existing infrastructure.
  let pb_packed_base := kSimPackedBase_polyBound h_ER pb_h
  let pb_packed_step := kSimPackedStep_polyBound g_ER pb_g
  -- Set sumCtx and CC, KK, E abbreviations matching level 1.
  set sumCtx :=
    (Finset.univ : Finset (Fin (a + 1))).sum
      (Fin.cons j params)
    with hsumCtx_def
  set S := sumCtx with hS_def
  set CC :=
    (Fin.foldr (k + 1) (fun l acc =>
      max acc (KMor1.linearBound (g_fam l) (h_g l)).1) 0) +
    2 * (Fin.foldr (k + 1) (fun l acc =>
      max acc (KMor1.linearBound (g_fam l) (h_g l)).2) 0)
    + 1
    with hCC_def
  set KK :=
    Fin.foldr (k + 1) (fun l acc =>
      max acc (KMor1.linearBound (h_fam l) (h_h l)).2) 0
    with hKK_def
  set E : ℕ := 6 * 4 ^ (k + 1) with hE_def
```

- [ ] **Step T4.3: Apply the polynomial-iter chain**

This is where the level-2 chain DIVERGES structurally from
level-1.  Level-1 used `simrecVec_seqPack_le_pow` directly;
level-2 uses `kSimPackedStep_polyBound` + T2.

Specifically:

```lean
  -- Adapt pb_packed_base / pb_packed_step to the
  -- single-power form via to_iter_step_form (existing).
  have h_step_form :=
    ERMor1.PolyBound.to_iter_step_form
      (kSimPackedStep g_ER) pb_packed_step params
  -- Adapt the packed base to the single-power form via
  -- le_pow_shift_of_polyBound (existing, line 402).
  have h_base_form :
      ∀ ctx, (kSimPackedBase h_ER).interp ctx ≤
        (maxCtx ctx + 2) ^
          (pb_packed_base.degree +
           pb_packed_base.coefficient +
           pb_packed_base.constant + 2) :=
    fun ctx => ERMor1.PolyBound.le_pow_shift_of_polyBound
      (kSimPackedBase h_ER) pb_packed_base ctx
  -- Apply T2's polynomial-base variant.
  have h_iter_bound :=
    Nat.polynomial_iter_tower_bound_with_pow_base
      (fun v x => (kSimPackedStep g_ER).interp
        (Fin.cons x (Fin.cons v params)))
      (pb_packed_step.degree + pb_packed_step.coefficient
        + pb_packed_step.constant + 2)
      (pb_packed_base.degree + pb_packed_base.coefficient
        + pb_packed_base.constant + 2)
      1  -- m_base = 1 (the linear-shape in pow-base variant)
      (fun v x => h_step_form v x)
      (fun x => (kSimPackedBase h_ER).interp _)
      _  -- transient; threading the right base ctx
      j sumCtx
```

The exact threading of arguments to `polynomial_iter_tower_bound_with_pow_base`
is delicate; the implementer adjusts based on T2's signature.

- [ ] **Step T4.4: Apply tower-monotonicity bumps**

Mirror lines 2655-2703 of level-1's chain:

```lean
  -- Bump tower 2 → tower 3 via tower_two_le_tower_three_linear.
  have h_tower3 :
      GebLean.tower 2 (...) ≤
      GebLean.tower 3 (...) :=
    Nat.tower_two_le_tower_three_linear _ _ _
  -- Bump tower 3 → tower (stepTH + 1) via tower_mono_left.
  have h_step_ge_2 : (kSimPackedStep g_ER).towerHeight ≥ k + 2 :=
    kSimPackedStep_towerHeight_ge_succ_k g_ER
  -- Combined log absorption via T3.
  have h_combined :=
    linearBoundLog_packedStep_le_towerHeight_level_two
      h_fam g_fam h_h h_g
  rw [kSimTowerBound_interp]
  rw [ERMor1.interp_sumCtxER]
  -- Final calc chain.
  calc Nat.rec _ _ j
      ≤ GebLean.tower 2 (CC * S + KK + Nat.log 2 E + 3) := _
    _ ≤ GebLean.tower 3 (...) := h_tower3
    _ ≤ GebLean.tower ((kSimPackedStep g_ER).towerHeight + 1)
          (...) := GebLean.tower_mono_left (by omega) _
    _ ≤ GebLean.tower ((kSimPackedStep g_ER).towerHeight + 1)
          (final_target_argument) := by
        apply GebLean.tower_mono_right
        omega  -- using h_combined
```

- [ ] **Step T4.5: Run `lake build` + `lake test`**

Expected: PASS, no warnings, no `sorry`/`admit`.

- [ ] **Step T4.6: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kSimTowerBound_dominates_inline headline (plan v4 T4)

Phase IV-B headline theorem: level-2 simrec dominance.
Public theorem; consumed by kToER plan Task 14.

Literature reference: Tourlakis 2018 §0.1.0.34 (E^2 closure
under simultaneous bounded recursion) + Recursion Class Ch. 4
Prop. 4.7 (n = 2 case): the level-2 K^sim simrec's iter is
bounded by tower 2 (linear in (j, x)) which dominates
kSimTowerBound's closed form tower (stepTH + 1) (linear).

Chain assembly (mirrors kSimTowerBound_dominates_level_one
line 2578 at level 2):
- per-l PolyBounds at degree 1 via T1.
- packed PolyBounds via existing kSimPackedBase/Step_polyBound.
- to_iter_step_form converts to single-power form.
- polynomial_iter_tower_bound_with_pow_base (T2) bounds the
  j-iter at tower 2 (linear).
- tower_two_le_tower_three_linear bumps to tower 3.
- tower_mono_left lifts to tower (stepTH + 1).
- tower_mono_right + linearBoundLog_packedStep_le_towerHeight_level_two
  (T3) absorbs the linear argument into kSimTowerBound's
  closed form.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T5: Final verification

- [ ] **Step T5.1: Confirm headline is public**

```bash
grep -n "theorem kSimTowerBound_dominates_inline" \
  GebLean/LawvereKSimPolynomialBound.lean
```

Expected: one match, NOT prefixed with `private`.

- [ ] **Step T5.2: Confirm no sorries / admits**

```bash
grep -rn "sorry\|admit" \
  GebLean/LawvereKSimPolynomialBound.lean \
  GebLean/Utilities/ComputationalComplexity.lean
```

Expected: zero matches.

- [ ] **Step T5.3: Confirm clean build + test**

```bash
lake build && lake test
```

Expected: PASS, no warnings, all tests pass.

- [ ] **Step T5.4: NO COMMIT — verification only**

---

## Estimated effort

- T1 — `kToER_polyBound_at_level_one_via_linearBound`:
  ~60 lines (non-recursive, one definition).
- T2 — `polynomial_iter_tower_bound_with_pow_base`:
  ~150 lines (mirror of existing + base lift).
- T3 — `linearBoundLog_packedStep_le_towerHeight_level_two`:
  ~120 lines (mirror of existing line 2226).
- T4 — `kSimTowerBound_dominates_inline`: ~250 lines
  (headline calc, mirror of line 2578).
- T5 — verification: 0 lines (read-only).

Total: ~580 lines.

This is substantially smaller than plan v3's ~2130-line
estimate because nothing novel is introduced — every task is
either a non-recursive use of existing infrastructure (T1)
or a structural mirror of an existing proof at one level up
(T2, T3, T4).

---

## Self-review checklist

**Spec coverage:** the headline theorem is the spec; every
task either implements a piece of the chain or supplies an
infrastructure prerequisite.

**Per-task literature citation:** each of T1-T4 cites the
specific published proposition (Lemma 1.A, Prop. 4.7, Wong's
Prop. 4.6, Tourlakis §0.1.0.34) it discharges.  The plan-
level trace at the top of this file is the global citation
network.

**Per-task build/test checkpoints:** each task ends with a
`lake build && lake test` checkpoint and a commit.

**Per-task commit subjects ending in `(plan v4 TN)`:** each
task has a commit subject template.

**Critical-path dependencies on landed lemmas:**

- `KMor1.linearBound` (line 207, public, Poly Task 14) — T1, T3, T4.
- `KMor1.linearBound_dominates` (line 507, public) — T1.
- `kToER_interp_level_one` (line 2711, private; T1 may need
  to widen to public, OR T1 lives inside the same file as
  `kToER_interp_level_one` so private access works).
- `kSimPackedBase_polyBound` (line 738, public, Poly Task 16)
  — T4.
- `kSimPackedStep_polyBound` (line 817, public, Poly Task 16)
  — T4.
- `ERMor1.PolyBound.to_iter_step_form`
  (`LawvereERPolynomialBound.lean:503`, public, Poly Task 10)
  — T4.
- `ERMor1.PolyBound.le_pow_shift_of_polyBound`
  (`LawvereERPolynomialBound.lean:402`, public) — T4.
- `Nat.polynomial_iter_tower_bound`
  (`Utilities/ComputationalComplexity.lean:471`, public,
  Poly Task 5) — T2 (as a structural model).
- `Nat.pow_le_tower_two_with_shift`
  (`Utilities/ComputationalComplexity.lean:612`, public)
  — T2 (in the base case lift).
- `Nat.tower_two_le_tower_three_linear`
  (`Utilities/ComputationalComplexity.lean:558`, public)
  — T4.
- `kSimPackedStep_towerHeight_ge_succ_k`
  (`LawvereKSimPolynomialBound.lean:1376`, private) — T4.
- `KMor1.linearBoundLog_le_towerHeight` (line 1828, public,
  Step 2 / L.3-5 deliverable) — T3.
- `kSimTowerBound_interp` (`KSimSzudzikSimrec.lean`, public)
  — T4.
- `ERMor1.interp_sumCtxER`
  (`LawvereERBoundComputable.lean`, public) — T4.

**Type consistency:** all signatures use `f.level ≤ 1`
hypothesis on level-1 K^sim children, lifted to `f.level ≤ 2`
via `Nat.le_succ_of_le` where required.

**Placeholder scan:** transient `_` underscores appear in
T1.1, T2.1, T2.2, T3.1, T4.1, T4.3 to mark working-tree
states resolved by their own subsequent sub-steps before the
respective task's commit.  No `_` or `sorry` in any committed
state.

---

## Out-of-scope deferred work

After this plan completes, Phase IV-B is fully closed.  The
next phase is the kToER theorem layer:

- **kToER Task 14 — `kToER_interp`**: consumes
  `kSimTowerBound_dominates_inline`.
- **kToER Task 15 — `kToERN_interp`**: pointwise lift.
- **kToER Task 16 — `kToERFunctor` obj/map fields**.
- **kToER Task 17 — functor laws (`map_id`, `map_comp`)**.
- **kToER Tasks 18-22**: tests, re-export, final
  verification.

Permanently out of scope for this codebase:

- `K^sim_d` for `d ≥ 3` (in PR, outside ER — separate
  project).

---

## Adversarial review queue

After this plan is committed, run an adversarial review pass
to verify:

- Every literature citation matches a real proposition (no
  citation drift).
- Every existing-codebase-lemma reference is at the cited
  line / has the cited signature (no codebase drift).
- T1's non-recursive construction is mathematically valid
  (does `kToER_interp_level_one` ∘ `linearBound_dominates`
  actually give a degree-1 PolyBound for level-1 K^sim?).
- T2's polynomial-base variant's bound shape is consistent
  with the existing `polynomial_iter_tower_bound`'s linear-
  base output (specializes correctly when `D_base = 1`,
  `m_base = m`).
- T3's mirror of `stepTH_baseTH_dominates_arg` actually
  closes — at level 2 the children's exponents from
  `KMor1.linearBound` may be larger than `level0Shape`'s,
  potentially breaking the `≤ 3 · towerHeight + 1` bound.
- T4's chain calc closes — the height arithmetic at every
  step is consistent.
- No constructor coverage gaps (level-1 K^sim has all six
  KMor1 constructors at the children; T1 must work for all).
- No repeats of plan v2 / v3 mistakes.
