# Polynomial-bound Task 17b/17c completion: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** complete the K^sim_2 ⊆ ER recursive bootstrap by
proving Task 17b's level-1 dominance (`kSimTowerBound_-`
`dominates_level_one`), level-1 interp preservation
(`kToER_interp_level_one`), and level-1 linear bound
(`kToER_linearBound_dominates_level_one`); then proving Task
17c's level-2 final dominance assembly
(`kSimTowerBound_dominates_inline`); then re-exporting
modules, updating the kToER plan, and performing final
verification.

**Architecture:** the dominance chain at each level routes
through `KMor1.simrecVec` on the K^sim side (Strategy A per
parent plan refinement R3), bounding each component linearly
via `KMor1.linearBound_dominates`, then converting through
`Nat.seqPack_le_seqPackBound`, `tower_succ_pow_bound_strong`,
and tower height-absorption to land inside
`kSimTowerBound`'s closed form.  The level-2 case reuses the
level-1 chain mutatis mutandis with level-1 children's linear
bounds.

**Tech Stack:** Lean 4 with mathlib; existing project
infrastructure
(`GebLean/LawvereKSimPolynomialBound.lean`,
`GebLean/Utilities/KSimSzudzikSimrec.lean`,
`GebLean/Utilities/ComputationalComplexity.lean`,
`GebLean/Utilities/Tower.lean`,
`GebLean/LawvereERBoundComputable.lean`,
`GebLean/LawvereKSim.lean`).

**Parent plan:**
`docs/plans/2026-04-30-er-polynomial-bound-plan.md`
(see "Brainstorm refinements" section for R1–R6 strategic
context that this plan implements).

**Parent kToER plan:**
`docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`
(Task 14 of that plan consumes
`kSimTowerBound_dominates_inline`, this plan's final
deliverable).

---

## Risk assessment

This plan was reviewed adversarially after first draft,
and **mid-execution** an additional correction was made
to A.5.0 / A.5.2 — see the "Plan correction
(2026-04-30, mid-execution)" callouts on those tasks.

The single highest-risk subtask is **Phase I Task A.5**
(tower-level absorption + structural propagation).
Detail:

The arithmetic chain bounds
`iter j ≤ tower 2 (CC * S + KK + 1 + log_2 E + 2)`,
where `CC = max_step_c + 2 * max_step_k + 1` depends on
the K^sim term-determined constants from `level0Shape`
of `g_fam` children.  But `kSimTowerBound`'s argument
shape `Y = stepTH + 1 + 2 * baseTH + 2 * sumCtx + 2`
has only a fixed-coefficient `2 * sumCtx` term — it
cannot directly absorb `CC * S` because `CC` can grow
arbitrarily with K^sim term constants.

Resolution path (Task A.5):

1. **Structural propagation** (A.5.0): prove
   `(kSimSzudzikPackList t).towerHeight ≥
   natPair.towerHeight + 2 + sup_j (t j).towerHeight`.
   Constant-coefficient version: each `comp natPair`
   layer adds the fixed `natPair.towerHeight` per layer.
   (The originally-drafted `k + 2 + sup` version is
   mathematically false; see Plan correction callout.)
2. **Tower-level absorption** (A.5.1): prove
   `tower 2 (C * X + D) ≤ tower 3 (X + log_2 (C+1) +
   log_2 (D+1) + 2)`.  Generic Module-A-friendly
   helper.
3. **Connect-up** (A.5.2): combine A.5.0 with
   level0Shape inspection plus the existing
   `_ge_succ_k` lemmas (separate slack channels).
   - `+sup_l (g_ER l).tH` absorbed by A.5.0
     (constant-coefficient propagation) on stepTH.
   - `+k` absorbed by `≥ k + 2` (existing lemma).
   - `+log_2 E ≈ 2k` absorbed by additional copies of
     baseTH ≥ k+2 in `2 * baseTH`.
   The combined absorption succeeds because the LHS
   slack `stepTH + 2*baseTH + 1` exposes three
   independent slack channels that match the three
   summands on the RHS.

Fallback if A.5 stalls: switch to Strategy B, which
hits the same fundamental absorption issue but routes
through `polynomial_iter_tower_bound` and
`kSimPackedStep_polyBound` instead of `simrecVec` and
`linearBound`.  Same A.5.1 still applies; A.5.0/A.5.2
are replaced by polyBound-degree analysis.  Estimated
pivot cost: ~1 day to retarget.

---

## Context: where this plan starts

State at session start of this plan's first task:

- Build: clean, 1521 jobs.
- Tests: all pass.
- Commits since checkpoint: `9fb91aac` (omega fix on
  structural lemma), `21defbab` (plan refinements R1–R6),
  `9766ca12` (strengthened structural towerHeight bound to
  `≥ k + 2`).
- Available pieces in
  `GebLean/LawvereKSimPolynomialBound.lean`:
  - `KMor1.level0Shape`, `KMor1.level0Shape_interp`
  - `KMor1.linearBound`, `KMor1.linearBound_dominates`
  - `KMor1.simrecVec_linear_bound_aux`
  - `kSimPackedStep_polyBound`, `kSimPackedBase_polyBound`
  - `packed_iteration_matches_simrecVec`
  - `kToER_interp_level_zero`,
    `kToER_linearBound_dominates_level_zero`
  - `kSimSzudzikPackList_towerHeight_ge_two` and
    `kSimSzudzikPackList_towerHeight_ge_succ_k`
  - `kSimPackedStep_towerHeight_ge_two` and
    `kSimPackedStep_towerHeight_ge_succ_k`
- Available pieces in
  `GebLean/Utilities/ComputationalComplexity.lean`:
  - `Nat.seqPack_le_seqPackBound`
  - `tower_succ_pow_bound_strong`
  - `Nat.polynomial_iter_tower_bound` (unused by Strategy A
    but available for Strategy B fallback)
- Available pieces in
  `GebLean/Utilities/KSimSzudzikSimrec.lean`:
  - `kSimSzudzikPackList`,
    `kSimSzudzikPackList_zero_interp`,
    `kSimSzudzikPackList_succ_interp`,
    `kSimSzudzikPackList_interp`
  - `kSimSzudzikUnpackAt`,
    `kSimSzudzikUnpackAt_packList`,
    `kSimSzudzikUnpackAt_interp_eq_seqAt`
  - `kSimPackedBase`, `kSimPackedBase_interp`
  - `kSimStepContext`
  - `kSimPackedStep`, `kSimPackedStep_interp`
  - `kSimTowerBound`, `kSimTowerBound_interp`,
    `kSimTowerBound_mono_counter`

## Verification before resumption

```bash
cd /home/terence/git-workspaces/geb/geb-lean
git log --oneline -10
lake build
lake test
```

Expected: build clean (1521 jobs), tests pass.

---

## File structure

This plan modifies and extends the existing module
`GebLean/LawvereKSimPolynomialBound.lean`.  No new files
are created in Phase I-IV.

In Phase V (housekeeping):

- Create:
  `GebLeanTests/LawvereKSimPolynomialBound.lean` (Task E).
- Modify: `GebLean.lean` (Task F).
- Modify: `GebLeanTests.lean` (Task F).
- Modify:
  `docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`
  (Task G).

---

## Tooling notes

- The project uses `lake build` and `lake test`; never
  `lake env lean` or `lake clean`.
- `warningAsError = true` is enabled.
- Lean MCP tools (`mcp__lean-lsp__lean_goal`,
  `mcp__lean-lsp__lean_diagnostic_messages`,
  `mcp__lean-lsp__lean_multi_attempt`,
  `mcp__lean-lsp__lean_local_search`,
  `mcp__lean-lsp__lean_loogle`) are encouraged liberally.
- The `lean4:sorry-filler-deep` skill may be useful for
  the trickier helpers in Phase I (Tasks A.4, A.5).

---

## Phase I — Task A: kSimTowerBound_dominates_level_one

The level-1 simrec dominance lemma.  Six sub-tasks A.1–A.6
plus a final commit at A.7.

### Task A.1: Stub the main theorem

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (append after `packed_iteration_matches_simrecVec`)

**Goal:** establish the type signature for the dominance
lemma so subsequent tasks can target it precisely.

- [ ] **Step A.1.1: Append the stub**

```lean
/-- Level-1 simrec dominance: the iterated packed value
of `kSimPackedStep` over `kSimPackedBase` is dominated by
`kSimTowerBound`'s closed-form tower at every iteration
counter and parameter context, when both base and step
families consist of level-0 K^sim terms. -/
private theorem kSimTowerBound_dominates_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (j : ℕ) (params : Fin a → ℕ) :
    Nat.rec
      ((kSimPackedBase
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le (h_h l))))).interp params)
      (fun i prev =>
        (kSimPackedStep
          (fun l => kToER (g_fam l)
            (Nat.le_succ_of_le
              (Nat.le_succ_of_le (h_g l))))).interp
        (Fin.cons i (Fin.cons prev params)))
      j ≤
      (kSimTowerBound
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le (h_h l))))
        (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le (h_g l))))).interp
        (Fin.cons j params) := by
  sorry
```

- [ ] **Step A.1.2: Run `lake build`**

Expected: ONE warning ("declaration uses 'sorry'") on the
stub.  No errors.

This stub is intentionally left with `sorry` only for the
duration of Phase I; A.6 fills it in.  Per the project's
no-`sorry` policy, **no commit happens until A.7** when the
sorry has been discharged.

- [ ] **Step A.1.3: Do not commit yet.**

---

### Task A.2: bound each simrecVec component linearly

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (append above `kSimTowerBound_dominates_level_one`'s
  stub)

**Goal:** wrap `KMor1.simrecVec_linear_bound_aux` into a
shape that takes the K^sim term-determined constants as
explicit named parameters tying together base and step
shapes.  The aux already exists; this task constructs the
specific witness instance for our use.

The wrapped lemma takes:

- the level-0 hypotheses on `h_fam` and `g_fam`,
- a uniform bound `S` for the parameter context,
- the iteration counter `n ≤ S`,

and produces, for every `l : Fin (k + 1)`:

```text
simrecVec h_fam g_fam params n l ≤ CC * S + KK
```

where `CC = step_c + 2 * step_k + 1` and `KK = base_max`,
and these in turn are foldr-reduced from the level0Shape
linearBounds of the `g_fam`/`h_fam` children.

- [ ] **Step A.2.1: Append the helper**

```lean
/-- Uniform linear bound on `KMor1.simrecVec` for level-0
families: each component at iteration `n ≤ S` is bounded
by `CC * S + KK`, with `CC` and `KK` extracted from the
children's `level0Shape.linearBound`. -/
private theorem KMor1.simrecVec_uniform_linear_bound
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (params : Fin a → ℕ)
    (S : ℕ)
    (h_params : ∀ j, params j ≤ S)
    (n : ℕ) (h_n : n ≤ S) :
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
        0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
        0) + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
        0
    ∀ l, KMor1.simrecVec h_fam g_fam params n l ≤
          CC * S + KK := by
  intro CC KK l
  set max_base_const := Fin.foldr (k + 1) (fun l acc =>
    max acc
      (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2) 0
  set max_step_c := Fin.foldr (k + 1) (fun l acc =>
    max acc
      (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1) 0
  set max_step_k := Fin.foldr (k + 1) (fun l acc =>
    max acc
      (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2) 0
  have hbm : ∀ j,
      (KMor1.level0Shape (h_fam j) (h_h j)).linearBound.2
        ≤ max_base_const := fun j =>
    Fin.foldr_max_ge
      (fun l =>
        (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
      j
  have hsc : ∀ j,
      (KMor1.level0Shape (g_fam j) (h_g j)).linearBound.1
        ≤ max_step_c := fun j =>
    Fin.foldr_max_ge
      (fun l =>
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
      j
  have hsk : ∀ j,
      (KMor1.level0Shape (g_fam j) (h_g j)).linearBound.2
        ≤ max_step_k := fun j =>
    Fin.foldr_max_ge
      (fun l =>
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
      j
  have haux := KMor1.simrecVec_linear_bound_aux
    h_fam g_fam h_h h_g params S h_params
    max_base_const hbm
    max_step_c max_step_k hsc hsk
    n h_n l
  have hck : max_step_k * n ≤ max_step_k * S :=
    Nat.mul_le_mul_left _ h_n
  have hcoeff_eq :
      (max_step_c + max_step_k + 1) * S + max_step_k * S
        = (max_step_c + 2 * max_step_k + 1) * S := by ring
  calc KMor1.simrecVec h_fam g_fam params n l
      ≤ (max_step_c + max_step_k + 1) * S
          + max_base_const + max_step_k * n := haux
    _ ≤ (max_step_c + max_step_k + 1) * S
          + max_base_const + max_step_k * S := by omega
    _ = (max_step_c + 2 * max_step_k + 1) * S
          + max_base_const := by omega
```

- [ ] **Step A.2.2: Run `lake build`**

Expected: PASS (with the existing `sorry` warning on
`kSimTowerBound_dominates_level_one`).

If the proof fails, the most likely issue is `Fin.foldr`
unfolding mismatch with the let-introduced `CC`/`KK`.
Adjust the `let` shape to match `simrecVec_linear_bound_aux`'s
expected variable names exactly.

- [ ] **Step A.2.3: Do not commit yet.**

---

### Task A.3: bound seqPack of simrecVec by polynomial

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** apply `Nat.seqPack_le_seqPackBound` to the list
of (k+1) `simrecVec` components, using A.2's component bound.

- [ ] **Step A.3.1: Append the helper**

```lean
/-- The `seqPack` of the `(k+1)`-tuple `simrecVec ... l`
is bounded by the polynomial `(CC * S + KK + 2)^E` where
`E = 6 * 4^(k+1)`. -/
private theorem KMor1.simrecVec_seqPack_le_pow
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (params : Fin a → ℕ)
    (S : ℕ)
    (h_params : ∀ j, params j ≤ S)
    (n : ℕ) (h_n : n ≤ S) :
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
        0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
        0) + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
        0
    Nat.seqPack
      ((List.finRange (k + 1)).map
        (fun l =>
          KMor1.simrecVec h_fam g_fam params n l)) ≤
      (CC * S + KK + 2) ^ (6 * 4 ^ (k + 1)) := by
  intro CC KK
  have h_each := KMor1.simrecVec_uniform_linear_bound
    h_fam g_fam h_h h_g params S h_params n h_n
  have h_each_in :
      ∀ v ∈ ((List.finRange (k + 1)).map
              (fun l =>
                KMor1.simrecVec h_fam g_fam params n l)),
        v ≤ ((CC * S + KK) + 1) ^ 1 := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨l, _, hvl⟩
    rw [hvl.symm]
    have := h_each l
    calc KMor1.simrecVec h_fam g_fam params n l
        ≤ CC * S + KK := this
      _ ≤ CC * S + KK + 1 := by omega
      _ = ((CC * S + KK) + 1) ^ 1 := by ring
  have hlen :
      ((List.finRange (k + 1)).map
        (fun l =>
          KMor1.simrecVec h_fam g_fam params n l)).length
        ≤ k + 1 := by simp
  have h_pack :=
    Nat.seqPack_le_seqPackBound
      ((List.finRange (k + 1)).map
        (fun l =>
          KMor1.simrecVec h_fam g_fam params n l))
      k 1 (CC * S + KK) hlen h_each_in
  unfold Nat.seqPackBound at h_pack
  have hexp_eq : (1 + 5) * 4 ^ (k + 1) = 6 * 4 ^ (k + 1) := by
    ring
  rw [hexp_eq] at h_pack
  exact h_pack
```

- [ ] **Step A.3.2: Run `lake build`**

Expected: PASS.

- [ ] **Step A.3.3: Do not commit yet.**

---

### Task A.4: lift polynomial bound to tower 2

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** apply `tower_succ_pow_bound_strong` (height 2,
exponent E) to lift the polynomial bound into a height-2
tower.  Requires choosing `x` such that
`tower 2 x + 1 ≥ CC * S + KK + 2`, i.e.
`tower 2 x ≥ CC * S + KK + 1`.

By `self_le_tower 2 X`, picking `x = CC * S + KK + 1`
satisfies `tower 2 x ≥ x = CC * S + KK + 1` directly.

- [ ] **Step A.4.1: Append the helper**

```lean
/-- Lift the polynomial bound `(CC * S + KK + 2)^E` to a
height-2 tower whose argument is linear in `S` plus a
logarithmic correction in `E`.  The shift
`Nat.log 2 E + 2` follows directly from
`tower_succ_pow_bound_strong`. -/
private theorem pow_le_tower_two_with_shift
    (CC S KK E : ℕ) :
    (CC * S + KK + 2) ^ E ≤
      GebLean.tower 2
        (CC * S + KK + 1 + Nat.log 2 E + 2) := by
  set x := CC * S + KK + 1
  have h_self : x ≤ GebLean.tower 2 x :=
    GebLean.self_le_tower 2 x
  have h_base_eq : CC * S + KK + 2 = x + 1 := by
    change CC * S + KK + 2 = (CC * S + KK + 1) + 1; rfl
  have h_base_le :
      x + 1 ≤ GebLean.tower 2 x + 1 := by omega
  have h_pow_lift :
      (x + 1) ^ E ≤ (GebLean.tower 2 x + 1) ^ E :=
    Nat.pow_le_pow_left h_base_le E
  have h_strong :
      (GebLean.tower 2 x + 1) ^ E ≤
        GebLean.tower 2 (x + Nat.log 2 E + 2) :=
    tower_succ_pow_bound_strong 2 E x (by decide)
  rw [h_base_eq]
  exact le_trans h_pow_lift h_strong
```

- [ ] **Step A.4.2: Run `lake build`**

Expected: PASS.

- [ ] **Step A.4.3: Do not commit yet.**

---

### Task A.5: tower absorption with structural propagation

**Goal:** bridge `tower 2 (CC * S + KK + 1 + log_2 E + 2)`
to `tower (stepTH + 1) (kSimTowerBound's argument)` via
three sub-helpers.  This is the workstream's highest-risk
subtask (see Risk Assessment section).

The chain:

```text
tower 2 (CC * S + ...)
  ≤ tower 3 (S + log_2 (CC+1) + log_2 (...+1) + 2)
                                     [A.5.1: generic absorb]
  ≤ tower (stepTH + 1) (Y' for some Y' ≤ Y)
                                     [A.5.2: connect-up]
```

where the connect-up uses the structural propagation
proved in A.5.0 to show `log_2 CC ≤ stepTH − k − 2 +
small`, giving sufficient slack in the right-hand side.

#### Task A.5.0: structural propagation lemma

> **Plan correction (2026-04-30, mid-execution)**: the
> originally-drafted statement `k + 2 + sup_l (t l).tH ≤
> packList.tH` is *mathematically false*.  Each `comp
> natPair` layer of `kSimSzudzikPackList` adds only the
> *fixed constant* `natPair.towerHeight ≈ 4` (plus 2 for
> the outer `comp succ`), not `k+1` per-layer slack.
>
> Concrete counterexample at `k = 5`: with `t 0` a chain of
> 100 `succ`s (towerHeight 100) and `t 1..5 = zero`
> (towerHeight 0): packList grows `6, 12, 18, 24, 30, then
> 4 + max(100, 30) + 2 = 106`.  Plan's claim
> `5+2+100 = 107 ≤ 106` is false by 1.
>
> Replacement: prove `natPair.towerHeight + 2 + sup ≤
> packList.tH`.  Constant-coefficient (independent of k);
> mathematically correct.  Downstream A.5.2 uses this
> together with the existing structural lemma
> `kSimSzudzikPackList_towerHeight_ge_succ_k` (which gives
> `k + 2 ≤ packList.tH`) as two separate slack channels —
> `+k` from the existing lemma, `+sup_l T_l` from the new
> propagation.  See revised A.5.2 below.

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (append after
  `kSimSzudzikPackList_towerHeight_ge_succ_k`)

**Goal:** prove `(kSimSzudzikPackList t).towerHeight ≥
natPair.tH + 2 + sup_l (t l).towerHeight`.  This pushes
per-child heights up through the natPair stack via a
constant offset.

- [ ] **Step A.5.0.1: Append the propagation lemma**

```lean
/-- `kSimSzudzikPackList`'s towerHeight propagates the
maximum child tower height through a constant offset.
The structural recursion adds `natPair.tH + 2` per layer
(natPair.tH from the inner `comp natPair`, +1 from natPair's
own comp, +1 from the outer `comp succ`), so the sup over
l of `(t l).towerHeight` enters at the deepest layer and
the offset is independent of k. -/
private theorem kSimSzudzikPackList_towerHeight_ge_propagate
    : ∀ {a k : ℕ} (t : Fin (k + 1) → ERMor1 a),
      ERMor1.natPair.towerHeight + 2 +
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun l => (t l).towerHeight) ≤
      (kSimSzudzikPackList t).towerHeight
  | _, 0,     _ => by sorry
  | _, _ + 1, _ => by sorry
```

- [ ] **Step A.5.0.2: Discharge the base case**

For k=0:

- `packList(0, t).tH = natPair.tH + (t 0).tH + 2`
  (inner comp natPair has `natPair.tH + sup{T_0, 0} + 1
  = natPair.tH + T_0 + 1`; outer comp succ adds 1).
- `sup{(t l).tH | l : Fin 1} = (t 0).tH`.
- Need: `natPair.tH + 2 + (t 0).tH ≤ natPair.tH +
  (t 0).tH + 2`.  Equality.

```lean
  | _, 0, t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      have hsup_eq :
          (Finset.univ : Finset (Fin 1)).sup
            (fun l => (t l).towerHeight) =
          (t 0).towerHeight := by
        rw [show (Finset.univ : Finset (Fin 1)) =
              {(0 : Fin 1)} from rfl]
        simp [Finset.sup_singleton]
      rw [hsup_eq]
      let G : Fin 2 → ℕ := fun i =>
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ => ERMor1.zeroN a).towerHeight
      have hG0 : G ⟨0, by omega⟩ = (t 0).towerHeight := rfl
      have hG_le_sup :
          (t 0).towerHeight ≤ Finset.univ.sup G := by
        rw [← hG0]
        exact Finset.le_sup (Finset.mem_univ _)
      let F : Fin 1 → ℕ := fun _ =>
        ERMor1.natPair.towerHeight + Finset.univ.sup G + 1
      have hF0_le_sup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      change ERMor1.natPair.towerHeight + 2 +
          (t 0).towerHeight ≤ 0 + Finset.univ.sup F + 1
      omega
```

- [ ] **Step A.5.0.3: Discharge the inductive case**

For k+1 → induct on k:

- IH: for any t' : Fin (k+1) → ERMor1 a,
  `natPair.tH + 2 + sup_l (t' l).tH ≤ packList(k, t').tH`.
- Apply to `t' = fun j => t j.succ`:
  `natPair.tH + 2 + sup_succ ≤ packList(k, t∘succ).tH`,
  where `sup_succ = sup over Fin (k+1) of (t l.succ).tH`.
- Inner of packList(k+1, t) is `comp natPair [t 0,
  packList(k, t∘succ)]`, with tH `natPair.tH + max(T_0,
  packList(k, t∘succ).tH) + 1`.
- Outer adds 1 from `comp succ`.
- So `packList(k+1, t).tH = natPair.tH + max(T_0,
  packList(k, t∘succ).tH) + 2`.
- Need: `natPair.tH + 2 + max(T_0, sup_succ) ≤
  natPair.tH + max(T_0, packList(k, t∘succ).tH) + 2`,
  i.e. `max(T_0, sup_succ) ≤ max(T_0, packList(k,
  t∘succ).tH)`.
- Since IH gives `packList(k, t∘succ).tH ≥ natPair.tH +
  2 + sup_succ ≥ sup_succ`, this is immediate by case
  analysis on `T_0` vs `sup_succ`.

```lean
  | _, k + 1, t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      have hIH :=
        kSimSzudzikPackList_towerHeight_ge_propagate
          (a := a) (k := k) (fun j => t j.succ)
      let G : Fin 2 → ℕ := fun i =>
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ =>
              kSimSzudzikPackList (a := a) (k := k)
                (fun j => t j.succ)).towerHeight
      have hG0 : G ⟨0, by omega⟩ = (t 0).towerHeight := rfl
      have hG1 :
          G ⟨1, by omega⟩ =
            (kSimSzudzikPackList (a := a) (k := k)
              (fun j => t j.succ)).towerHeight := rfl
      have hG_le_sup0 :
          (t 0).towerHeight ≤ Finset.univ.sup G := by
        rw [← hG0]; exact Finset.le_sup (Finset.mem_univ _)
      have hG_le_sup1 :
          (kSimSzudzikPackList (a := a) (k := k)
            (fun j => t j.succ)).towerHeight ≤
            Finset.univ.sup G := by
        rw [← hG1]; exact Finset.le_sup (Finset.mem_univ _)
      have hsup_succ_le :
          (Finset.univ : Finset (Fin (k + 1))).sup
              (fun l => (t l.succ).towerHeight) ≤
            Finset.univ.sup G := by
        have :
            (Finset.univ : Finset (Fin (k + 1))).sup
                (fun l => (t l.succ).towerHeight) ≤
              (kSimSzudzikPackList (a := a) (k := k)
                (fun j => t j.succ)).towerHeight := by
          have := hIH
          omega
        omega
      have hT0_le :
          (t 0).towerHeight ≤
            (Finset.univ : Finset (Fin (k + 2))).sup
              (fun l => (t l).towerHeight) := by
        have h0 : (0 : Fin (k + 2)) ∈ Finset.univ :=
          Finset.mem_univ _
        exact Finset.le_sup (f :=
          fun l : Fin (k + 2) => (t l).towerHeight) h0
      have hsup_le :
          (Finset.univ : Finset (Fin (k + 2))).sup
              (fun l => (t l).towerHeight) ≤
            max (t 0).towerHeight
              ((Finset.univ : Finset (Fin (k + 1))).sup
                (fun l => (t l.succ).towerHeight)) := by
        apply Finset.sup_le
        intro i _
        match i with
        | ⟨0, _⟩ =>
            have : (t (⟨0, _⟩ : Fin (k + 2))).towerHeight =
                (t 0).towerHeight := rfl
            rw [this]; exact le_max_left _ _
        | ⟨n + 1, h⟩ =>
            have hn : n < k + 1 := by omega
            have : (t (⟨n + 1, h⟩ : Fin (k + 2)))
                .towerHeight =
                (t (⟨n, hn⟩ : Fin (k + 1)).succ)
                .towerHeight := rfl
            rw [this]
            apply le_trans
              (Finset.le_sup (f :=
                fun l : Fin (k + 1) =>
                  (t l.succ).towerHeight)
                (Finset.mem_univ _))
            exact le_max_right _ _
      let F : Fin 1 → ℕ := fun _ =>
        ERMor1.natPair.towerHeight + Finset.univ.sup G + 1
      have hF0_le_sup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      change ERMor1.natPair.towerHeight + 2 +
          Finset.univ.sup
            (fun l : Fin (k + 2) => (t l).towerHeight) ≤
        0 + Finset.univ.sup F + 1
      have hsup_F :
          Finset.univ.sup F ≥
            ERMor1.natPair.towerHeight +
              Finset.univ.sup G + 1 := by
        have : F 0 = ERMor1.natPair.towerHeight +
            Finset.univ.sup G + 1 := rfl
        rw [← this]; exact hF0_le_sup
      omega
```

The detailed proof above is approximate; expect 1-2
iterations of `lean_goal` inspection to settle the
`change` and `match` shaping.

- [ ] **Step A.5.0.4: Add the kSimPackedBase / kSimPackedStep corollaries**

```lean
private theorem kSimPackedBase_towerHeight_ge_propagate
    {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a) :
    ERMor1.natPair.towerHeight + 2 +
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l => (h l).towerHeight) ≤
      (kSimPackedBase h).towerHeight := by
  unfold kSimPackedBase
  exact kSimSzudzikPackList_towerHeight_ge_propagate _

private theorem kSimPackedStep_towerHeight_ge_propagate
    {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1.natPair.towerHeight + 2 +
      (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l =>
          (ERMor1.comp (g l) kSimStepContext).towerHeight) ≤
      (kSimPackedStep g).towerHeight := by
  unfold kSimPackedStep
  exact kSimSzudzikPackList_towerHeight_ge_propagate _
```

The `kSimPackedBase` corollary is new (needed for
absorbing `KK + log_2 E + 4` in A.6.4); the
`kSimPackedStep` corollary's statement now matches the
constant-coefficient form.

- [ ] **Step A.5.0.5: Run `lake build`**

Expected: PASS (with the existing A.1 sorry).

- [ ] **Step A.5.0.6: Do not commit yet.**

#### Task A.5.1: generic tower absorption lemma

**Files:**

- Modify: `GebLean/Utilities/ComputationalComplexity.lean`
  (this lemma is generic; place in Module A for reuse)

**Goal:** prove the height-3 absorbs-linear-coefficient
lemma.

- [ ] **Step A.5.1.1: Append the lemma**

```lean
/-- Going from height 2 to height 3 absorbs a linear
coefficient: `tower 2 (C * X + D)` is dominated by
`tower 3 (X + log_2 (C+1) + log_2 (D+1) + 2)`.

Mechanism: `tower 3 Y = 2^(tower 2 Y) ≥ 2^(2^Y) ≥ tower 2
X` iff `2^Y ≥ X` iff `Y ≥ log_2 X`.  We pick `Y = X +
log_2 (C+1) + log_2 (D+1) + 2`, then bound
`log_2 (C*X + D + 1) ≤ log_2 (C+1) + log_2 (X+1) +
log_2 (D+1) + 2 ≤ log_2 (C+1) + X + log_2 (D+1) + 2 = Y`. -/
theorem GebLean.tower_two_le_tower_three_linear
    (C D X : ℕ) :
    GebLean.tower 2 (C * X + D) ≤
      GebLean.tower 3 (X + Nat.log 2 (C + 1) +
        Nat.log 2 (D + 1) + 2) := by
  sorry
```

- [ ] **Step A.5.1.2: Discharge the sorry**

Proof structure (estimated 60-100 lines):

```lean
  -- Step 1: bound C * X + D ≤ (C+1) * (X+1) * (D+1) - 1
  --   to enable log-of-product.
  have h_prod :
      C * X + D + 1 ≤ (C + 1) * (X + 1) * (D + 1) := by
    cases X
    · simp; omega
    · ring_nf
      omega  -- distributing
  -- Step 2: log of product.
  have h_log_prod :
      Nat.log 2 ((C + 1) * (X + 1) * (D + 1)) ≤
        Nat.log 2 (C + 1) + Nat.log 2 (X + 1)
          + Nat.log 2 (D + 1) := by
    -- Use Nat.log_mul_le (mathlib) twice.
    sorry
  -- Step 3: log_2 (X+1) ≤ X.
  have h_log_X : Nat.log 2 (X + 1) ≤ X := by
    -- Standard: log_2 (n+1) ≤ n for n ≥ 0.
    sorry
  -- Step 4: chain to get log_2 (C*X+D+1) ≤ Y - 2
  --   where Y is target argument.
  set Y := X + Nat.log 2 (C + 1) + Nat.log 2 (D + 1) + 2
  have h_log_le_Y :
      Nat.log 2 (C * X + D + 1) ≤ Y - 2 := by
    have h1 := Nat.log_le_log h_prod
    sorry  -- chain h1 with h_log_prod and h_log_X
  -- Step 5: tower 2 X ≤ tower 3 Y from
  --   log_2 X ≤ Y - 2 implies 2^X ≤ 2^(Y-2) * 4 ≤
  --   tower 2 Y, hence tower 2 X = 2^(2^X) ≤
  --   2^(tower 2 Y) = tower 3 Y.
  sorry
```

The implementer fills in via mathlib's `Nat.log_mul_le`,
`Nat.log_le_log`, and tower's `tower_mono_right`.  If
mathlib's `Nat.log_mul_le` proves elusive, prove it
inline using `Nat.lt_pow_succ_log_self`.

- [ ] **Step A.5.1.3: Run `lake build`**

Expected: PASS.

- [ ] **Step A.5.1.4: Run `lake test`**

Expected: PASS.

- [ ] **Step A.5.1.5: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "Add tower_two_le_tower_three_linear

Going from height 2 to height 3 absorbs a linear
coefficient: tower 2 (C*X + D) is dominated by tower 3
(X + log_2 (C+1) + log_2 (D+1) + 2).  Generic Module-A
helper used by Task 17b.2's dominance chain."
```

#### Task A.5.2: connect-up lemmas absorbing log_2 CC and log_2 (KK + log_2 E + 4)

> **Plan correction (2026-04-30, mid-execution)**: the
> originally-drafted A.5.2 used the (false) propagation
> `stepTH ≥ k + 2 + sup_l (g_ER l).tH`.  The corrected
> chain instead splits the absorption across two slack
> channels:
>
> - `+k` absorption uses the **existing** lemma
>   `kSimPackedStep_towerHeight_ge_succ_k` (and similar for
>   base): `stepTH ≥ k + 2`, `baseTH ≥ k + 2`.
> - `+sup_l T_l` absorption uses the **new** corrected
>   propagation: `stepTH ≥ natPair.tH + 2 + sup_l (g_ER
>   l).tH + (sup over kSimStepContext slots) + 1` (the
>   inner `comp (g l) kSimStepContext` adds 1 to the inner
>   sup), simplified to `stepTH ≥ natPair.tH + 3 + sup_l
>   (g_ER l).tH` for a lower bound; symmetrically `baseTH
>   ≥ natPair.tH + 2 + sup_l (h_ER l).tH`.
>
> Final argument inequality (post A.5.1) becomes:
>
> ```text
> log_2(CC + 1) + log_2(KK + log_2 E + 4) ≤
>   stepTH + 2*baseTH + 1
> ```
>
> The chain is:
>
> 1. `log_2(CC + 1) ≤ sup_l (g_ER l).tH + κ_g` (where κ_g
>    depends on `log_2(linearBound.2 of g) ≤ tH + 1`,
>    plus product-of-three-naturals log bound for CC's
>    structure).
> 2. `log_2(KK + log_2 E + 4) ≤ sup_l (h_ER l).tH + 2k +
>    κ_h` (combining KK ≤ tH+1 and log_2 E ≤ 2k+5).
> 3. `stepTH + 2*baseTH ≥ (natPair.tH + 3 + sup_l (g_ER
>    l).tH) + (k + 2) + (natPair.tH + 2 + sup_l (h_ER
>    l).tH) ≥ sup_l (g_ER l).tH + sup_l (h_ER l).tH + k +
>    big_constant`.  (The first +k+2 uses baseTH ≥ k+2
>    once; the +2k slack from log_2 E is absorbed by
>    repeated use of stepTH ≥ k+2 / baseTH ≥ k+2 across
>    the +1 already in `stepTH + 2*baseTH + 1` plus the
>    full `sumCtx` slack on the RHS.)

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** prove the specific connect-up inequalities
needed by A.6's calc chain.

- [ ] **Step A.5.2.1: Append the level-0 structural
  bound on linearBound.2**

```lean
private theorem kToER_level0_towerHeight_ge_const
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0) :
    (KMor1.level0Shape f h).linearBound.2 ≤
      (kToER f
        (Nat.le_succ_of_le
          (Nat.le_succ_of_le h))).towerHeight + 1 := by
  sorry  -- ~40-60 lines, structural induction
```

The proof is by structural induction on the level-≤-0
KMor1 term:

- `zero`: linearBound.2 = 0, tH = 0; `0 ≤ 1` ✓.
- `succ` (level 0 only at projection-arity 1; appears
  via `comp succ [proj 0]` in level-0 contexts): linear
  Bound.2 = 1 from `shifted 0 1`, kToER produces
  `comp succ [proj 0]` with tH = `succ.tH + sup{proj.tH} +
  1 = 0 + 0 + 1 = 1`; `1 ≤ 1 + 1 = 2` ✓.
- `proj i`: linearBound.2 = 0, tH = 0; `0 ≤ 1` ✓.
- `comp f gs`: by structural-shape recursion.  If
  level0Shape's comp clause produces `const k` with k =
  the substituted constant, kToER produces `comp ...`
  whose tH grows by ≥ 1; combined with IH on f and on
  the gs.  Detailed analysis depends on
  `level0Shape`'s comp clause definition.
- `raise f`: linearBound.2 unchanged from f; tH unchanged
  modulo a fixed offset (raise is a `comp` in kToER);
  IH plus offset bookkeeping.

- [ ] **Step A.5.2.2: Append the global stepTH/baseTH
  bounds in the form A.6 will consume**

These bounds combine A.5.0's propagation with the
existing `≥ k + 2` lemmas plus the constant-offset
analysis.  They state the assertion in the exact form
needed by A.6.4's argument inequality, with all slack
constants tracked explicitly.

```lean
/-- Combined bound: `stepTH + 2*baseTH + 1` absorbs the
sum of K^sim-term-determined log shifts and the
polynomial-degree shift `log_2 E`.  Uses both slack
channels — the existing `≥ k+2` lemmas (for `+k`
absorption) and the corrected propagation (for
`+sup_l T_l` absorption). -/
private theorem stepTH_baseTH_dominates_arg
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0) :
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
        0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
        0) + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc
          (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
        0
    let E : ℕ := 6 * 4 ^ (k + 1)
    let h_ER : Fin (k + 1) → ERMor1 a :=
      fun l => kToER (h_fam l)
        (Nat.le_succ_of_le (Nat.le_succ_of_le (h_h l)))
    let g_ER : Fin (k + 1) →
        ERMor1 (a + 1 + (k + 1)) :=
      fun l => kToER (g_fam l)
        (Nat.le_succ_of_le (Nat.le_succ_of_le (h_g l)))
    Nat.log 2 (CC + 1) +
        Nat.log 2 (KK + Nat.log 2 E + 4) ≤
      (kSimPackedStep g_ER).towerHeight +
        2 * (kSimPackedBase h_ER).towerHeight + 1 := by
  sorry  -- ~80-150 lines
```

Proof outline:

1. Bound `log_2(CC + 1)` using
   `kToER_level0_towerHeight_ge_const`:
   each level0Shape constant ≤ `(kToER ...).tH + 1`.
   Foldr-max + log of sum ≤ `sup_l (g_ER l).tH + κ_g` for
   small κ_g.
2. Bound `log_2(KK + log_2 E + 4)` using the same level-0
   structural bound (for KK) plus log of sum (for the
   `log_2 E` term).  log_2 E ≤ 2k + 5 (from
   `log_2(6*4^(k+1)) ≤ 2k+5`).
3. Combine: total log ≤ `sup_g + sup_h + 2k + κ`.
4. Bound the RHS using the existing `_ge_succ_k` lemmas
   plus the new propagation:
   - `stepTH ≥ natPair.tH + 3 + sup_l (g_ER l).tH`
     (propagation + comp +1 inside)
   - `stepTH ≥ k + 2`
   - `baseTH ≥ natPair.tH + 2 + sup_l (h_ER l).tH`
     (propagation, no comp wrapping)
   - `baseTH ≥ k + 2`
5. Combine RHS bounds: `stepTH + 2*baseTH + 1 ≥ sup_g +
   2*(k+2) + sup_h + κ` (using one copy of each
   propagation and one copy of each `≥ k+2`).
6. Compare with LHS bound from step 3.

- [ ] **Step A.5.2.3: Discharge the sorries**

The level-0 structural bound (A.5.2.1) is the
combinatorial heart of the absorption; the global bound
(A.5.2.2) is mostly arithmetic.  Estimated total:
~100-200 lines.

- [ ] **Step A.5.2.4: Run `lake build`**

Expected: PASS.

- [ ] **Step A.5.2.5: Do not commit yet (commit after
  A.6 closes the main theorem).**

---

### Task A.6: Compose the helpers into the main theorem

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (replace the `sorry` body in
  `kSimTowerBound_dominates_level_one`)

**Goal:** chain together the helpers from A.2–A.5 to
produce the dominance inequality.

The chain in detail:

```text
Nat.rec ... j  =  Nat.seqPack of simrecVec at j   (A.2.1
                                                  via
                                                  packed_iteration_matches_simrecVec)
              ≤  (CC * S + KK + 2)^E              (A.3:
                                                  simrecVec_seqPack_le_pow)
              ≤  tower 2 (CC * S + KK + 1 +
                          log_2 E + 2)            (A.4:
                                                  pow_le_tower_two_with_shift)
              ≤  tower 3 (S + log_2 (CC+1) +
                          log_2 (KK+log_2 E+3) +
                          2)                      (A.5.1:
                                                  tower_two_le_tower_three_linear)
              ≤  tower ((stepTH g_ER) + 1) Y      (A.5.2:
                                                  stepTH_dominates_log_CC
                                                  + tower
                                                  monotonicity)
```

where the final step uses `tower_mono_left` (height
3 ≤ stepTH+1, since stepTH ≥ k+2 ≥ 2) and
`tower_mono_right` (argument fits within Y after
absorbing `log_2(CC+1)` via A.5.2's bound).

- [ ] **Step A.6.1: Replace the `sorry` body**

```lean
private theorem kSimTowerBound_dominates_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 0)
    (h_g : ∀ l, (g_fam l).level ≤ 0)
    (j : ℕ) (params : Fin a → ℕ) :
    -- (full statement as in A.1)
    := by
  set h_ER := fun l => kToER (h_fam l)
    (Nat.le_succ_of_le (Nat.le_succ_of_le (h_h l)))
  set g_ER := fun l => kToER (g_fam l)
    (Nat.le_succ_of_le (Nat.le_succ_of_le (h_g l)))
  -- Step 1: rewrite via packed_iteration_matches_simrecVec.
  rw [packed_iteration_matches_simrecVec
        h_fam g_fam h_h h_g params j]
  -- Step 2: define S = sumCtx as the uniform bound.
  let sumCtx : ℕ :=
    (Finset.univ : Finset (Fin (a + 1))).sum
      (Fin.cons j params)
  let S := sumCtx
  have h_params_le_S : ∀ i, params i ≤ S := by
    intro i
    show params i ≤ sumCtx
    -- Decompose Finset.sum (Fin.cons j params) and extract
    -- params i via Finset.single_le_sum.
    rw [Fin.sum_univ_succ]
    have : params i ≤
        (Finset.univ : Finset (Fin a)).sum params :=
      Finset.single_le_sum
        (f := params) (s := Finset.univ)
        (h := fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  have h_j_le_S : j ≤ S := by
    show j ≤ sumCtx
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_zero]
  -- Define CC and KK as the level-0 foldr-max coefficients
  -- (matching A.2's `let` definitions).
  let CC :=
    (Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.1)
      0) +
    2 * (Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (g_fam l) (h_g l)).linearBound.2)
      0) + 1
  let KK :=
    Fin.foldr (k + 1) (fun l acc =>
      max acc
        (KMor1.level0Shape (h_fam l) (h_h l)).linearBound.2)
      0
  let E : ℕ := 6 * 4 ^ (k + 1)
  -- Step 3: bound seqPack by (CC*S + KK + 2)^E.
  have h_pack_le := KMor1.simrecVec_seqPack_le_pow
    h_fam g_fam h_h h_g params S h_params_le_S j h_j_le_S
  -- Step 4: lift to tower 2 via A.4.
  have h_tower2 := pow_le_tower_two_with_shift
    CC S KK E
  -- Step 5: lift tower 2 to tower 3 via A.5.1.
  -- After A.5.1 application, the argument is
  -- X + log_2 (C+1) + log_2 (D+1) + 2 where X = S +
  -- log_2 E + 2 (?? need to track).  Actually we have
  -- tower 2 (CC * S + KK + 1 + log_2 E + 2); apply A.5.1
  -- with C = CC, D = KK + 1 + log_2 E + 2, X = S.
  have h_log_E : Nat.log 2 E ≤ 2 * k + 5 := by
    -- E = 6 * 4^(k+1) ≤ 8 * 4^(k+1) = 2^(2k+5).
    sorry
  have h_tower3 :
      GebLean.tower 2
        (CC * S + (KK + Nat.log 2 E + 1) + 2 - 1)
        ≤ GebLean.tower 3
          (S + Nat.log 2 (CC + 1)
            + Nat.log 2 (KK + Nat.log 2 E + 1 + 1) + 2) := by
    sorry  -- direct application of A.5.1 with type
           -- adjustments
  -- Step 6: combine slack channels via A.5.2's combined
  -- bound `stepTH + 2*baseTH + 1 ≥ log_2(CC+1) +
  -- log_2(KK + log_2 E + 4)`.
  have h_combined_dom :=
    stepTH_baseTH_dominates_arg h_fam g_fam h_h h_g
  have h_step_ge : (kSimPackedStep g_ER).towerHeight ≥ 3 := by
    have := kSimPackedStep_towerHeight_ge_succ_k g_ER
    omega
  -- Step 7: rewrite the RHS via kSimTowerBound_interp.
  rw [kSimTowerBound_interp]
  -- The ER sumCtxER interp at (Fin.cons j params) equals
  -- our sumCtx.
  rw [ERMor1.interp_sumCtxER]
  -- Final chain: combine h_pack_le, h_tower2, h_tower3,
  -- and tower_mono lemmas.  Estimated ~30 lines of calc.
  sorry
```

The final `sorry` represents ~30-60 lines of detailed
calc chaining.  The implementer:

1. Inspects each goal via `lean_goal`.
2. Composes the bounds with arithmetic adjustments.
3. Discharges the `h_log_E` and `h_tower3` sorries using
   the helpers from A.5.1 plus mathlib's `Nat.log_le_log`
   and `Nat.log_pow`.

- [ ] **Step A.6.2: Discharge `h_log_E`**

```lean
  have h_log_E : Nat.log 2 E ≤ 2 * k + 5 := by
    show Nat.log 2 (6 * 4 ^ (k + 1)) ≤ 2 * k + 5
    have h_le : 6 * 4 ^ (k + 1) ≤ 2 ^ (2 * k + 5) := by
      have h6 : 6 ≤ 8 := by omega
      have h8_eq : (8 : ℕ) = 2 ^ 3 := by norm_num
      have h4_eq : (4 : ℕ) = 2 ^ 2 := by norm_num
      calc 6 * 4 ^ (k + 1)
          ≤ 8 * 4 ^ (k + 1) := by exact
              Nat.mul_le_mul_right _ h6
        _ = 2 ^ 3 * (2 ^ 2) ^ (k + 1) := by rw [h8_eq, h4_eq]
        _ = 2 ^ (2 * k + 5) := by
            rw [← Nat.pow_mul, ← Nat.pow_add]
            congr 1; ring
    exact Nat.log_le_of_le_pow (by omega) h_le
```

- [ ] **Step A.6.3: Discharge `h_tower3`**

```lean
  have h_tower3 :
      GebLean.tower 2 (CC * S + KK + Nat.log 2 E + 3) ≤
      GebLean.tower 3 (S + Nat.log 2 (CC + 1)
        + Nat.log 2 (KK + Nat.log 2 E + 4) + 2) := by
    set D := KK + Nat.log 2 E + 3
    have h_eq : CC * S + KK + Nat.log 2 E + 3 =
                CC * S + D := by ring
    rw [h_eq]
    exact GebLean.tower_two_le_tower_three_linear CC D S
```

- [ ] **Step A.6.4: Discharge the final calc**

Build the calc chain explicitly:

```lean
  calc Nat.seqPack _
      ≤ (CC * S + KK + 2) ^ E := h_pack_le
    _ ≤ GebLean.tower 2 (CC * S + KK + 1 + Nat.log 2 E + 2)
        := h_tower2
    _ = GebLean.tower 2 (CC * S + KK + Nat.log 2 E + 3) := by
        congr 1; ring
    _ ≤ GebLean.tower 3 (S + Nat.log 2 (CC + 1)
          + Nat.log 2 (KK + Nat.log 2 E + 4) + 2) :=
        h_tower3
    _ ≤ GebLean.tower ((kSimPackedStep g_ER).towerHeight
          + 1)
          (S + Nat.log 2 (CC + 1)
            + Nat.log 2 (KK + Nat.log 2 E + 4) + 2) :=
        GebLean.tower_mono_left (by omega) _
    _ ≤ GebLean.tower ((kSimPackedStep g_ER).towerHeight
          + 1)
          ((kSimPackedStep g_ER).towerHeight + 1
            + 2 * (kSimPackedBase h_ER).towerHeight
            + 2 * sumCtx + 2) := by
        apply GebLean.tower_mono_right
        -- Show: S + log(CC+1) + log(KK+...) + 2 ≤
        --   stepTH + 1 + 2*baseTH + 2*sumCtx + 2.
        -- Use: S = sumCtx, h_step_dom (log(CC+1) ≤ stepTH),
        --   2*baseTH ≥ 2*(k+2) absorbs the rest.
        sorry
```

The final `sorry` is the inner-argument inequality.
~10-30 lines of arithmetic; uses `h_step_dom` from
A.5.2.2, `kSimPackedStep_towerHeight_ge_succ_k`,
`kSimSzudzikPackList_towerHeight_ge_succ_k` applied to the
base.

- [ ] **Step A.6.5: Run `lake build`**

If errors, use `lean_goal` to inspect intermediate states.

Expected at completion: PASS, ZERO `sorry`/warning.

- [ ] **Step A.6.6: Do not commit yet — proceed to A.7.**

---

### Task A.7: Build clean and commit Phase I

**Files:**

- Modified: `GebLean/LawvereKSimPolynomialBound.lean`

- [ ] **Step A.7.1: Run `lake build`**

Expected: PASS, no warnings, no `sorry`.

- [ ] **Step A.7.2: Run `lake test`**

Expected: PASS.

- [ ] **Step A.7.3: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add kSimTowerBound_dominates_level_one (Task 17b.2)

Proves the level-1 simrec dominance of the iterated packed
value by kSimTowerBound's closed-form tower at every iteration
counter and parameter context, given level-0 K^sim children.

Routes through five helper lemmas:
- KMor1.simrecVec_uniform_linear_bound
- KMor1.simrecVec_seqPack_le_pow
- pow_le_tower_two_with_shift
- tower_two_le_tower_three_linear
- kSimTowerBound_arg_dominates_log

Closing inequality chain:
  iter j = seqPack of simrecVec
        <= (CC*S + KK + 2)^E   (E = 6 * 4^(k+1))
        <= tower 2 (linear)
        <= tower 3 (linear with log shifts)
        <= tower (stepTH+1) (kSimTowerBound's argument)
where the last step uses kSimPackedStep_towerHeight_ge_succ_k
to dominate the stepTH height."
```

---

## Phase II — Task B: kToER_interp_level_one

The level-1 K^sim interp preservation theorem.  Reuses
Task A's dominance for the simrec case.

### Task B.1: Stub the theorem and atomic cases

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (append after Phase I)

- [ ] **Step B.1.1: Append the theorem with atomic cases
  filled in and complex cases as `sorry`**

```lean
/-- Interp preservation for level-1 K^sim: at level ≤ 1,
`kToER` produces an ER term whose interp equals the K^sim
interp at every context.  Proved by structural recursion;
the simrec case discharges the dominance hypothesis of
`boundedRec_eq_natRec_of_bounded` via
`kSimTowerBound_dominates_level_one`. -/
private theorem kToER_interp_level_one :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
      (ctx : Fin a → ℕ),
      (kToER f
        (Nat.le_succ_of_le h)).interp ctx = f.interp ctx
  | _, .zero,         _, _   => by simp [kToER]
  | _, .succ,         _, _   => by simp [kToER]
  | _, .proj _,       _, _   => by simp [kToER]
  | _, .comp f gs,    h, ctx => by
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 1 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 1 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      simp only [kToER, ERMor1.interp_comp,
        KMor1.interp_comp]
      congr 1
      funext i
      exact kToER_interp_level_one (gs i) (hgs i) ctx
  | _, .raise f,      h, ctx => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      simp only [kToER, KMor1.interp_raise]
      exact kToER_interp_level_zero f hf ctx
  | _, .simrec _ _ _, _, _   => by sorry
```

- [ ] **Step B.1.2: Run `lake build`**

Expected: PASS with `sorry` warning on the simrec case.

- [ ] **Step B.1.3: Do not commit yet.**

---

### Task B.2: Discharge the simrec case

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

- [ ] **Step B.2.1: Replace the simrec sorry with a proof**

The proof structure for the simrec case (using `kToER`'s
definition for simrec, which calls `boundedRec`):

```lean
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp, ctx =>
      by
        have h_h : ∀ l, (h_fam l).level ≤ 0 := fun l => by
          unfold KMor1.level at hyp
          have hsup : Finset.univ.sup
              (fun j => (h_fam j).level) ≤ 0 := by
            have := le_trans (le_max_left _ _)
              (Nat.le_of_succ_le_succ hyp)
            exact this
          exact le_trans
            (Finset.le_sup
              (f := fun j => (h_fam j).level)
              (Finset.mem_univ l))
            hsup
        have h_g : ∀ l, (g_fam l).level ≤ 0 := fun l => by
          unfold KMor1.level at hyp
          have hsup : Finset.univ.sup
              (fun j => (g_fam j).level) ≤ 0 := by
            have := le_trans (le_max_right _ _)
              (Nat.le_of_succ_le_succ hyp)
            exact this
          exact le_trans
            (Finset.le_sup
              (f := fun j => (g_fam j).level)
              (Finset.mem_univ l))
            hsup
        -- Reference: kToER's simrec body in
        -- LawvereKSimER.lean line 58-93 has shape:
        --   ERMor1.comp (kSimSzudzikUnpackAt a i.val)
        --     (fun j => if j.val = 0 then recur
        --               else proj j)
        -- where recur = ERMor1.boundedRec
        --   (kSimPackedBase h_ER) (kSimPackedStep g_ER)
        --   (kSimTowerBound h_ER g_ER).
        let h_ER : Fin (k + 1) → ERMor1 a :=
          fun l => kToER (h_fam l)
            (Nat.le_succ_of_le
              (Nat.le_succ_of_le (h_h l)))
        let g_ER : Fin (k + 1) →
            ERMor1 (a + 1 + (k + 1)) :=
          fun l => kToER (g_fam l)
            (Nat.le_succ_of_le
              (Nat.le_succ_of_le (h_g l)))
        let recVar : ℕ := ctx 0
        let params : Fin a → ℕ := fun j => ctx (Fin.succ j)
        -- Step 1: unfold kToER and ERMor1.interp on the
        -- comp + match structure.
        simp only [kToER, ERMor1.interp_comp]
        -- The LHS becomes
        --   (kSimSzudzikUnpackAt a i.val).interp
        --     (fun j => if j.val = 0 then recur.interp ctx
        --               else ctx j)
        -- Step 2: rewrite recur.interp using
        -- ERMor1.boundedRec_eq_natRec_of_bounded.
        have h_dom := kSimTowerBound_dominates_level_one
          h_fam g_fam h_h h_g
        -- The dominance lemma gives, for every j:
        --   iter j (...) ≤ kSimTowerBound.interp
        --     (Fin.cons j params)
        -- Need to specialize at j = recVar = ctx 0:
        have h_dom_at_rec :
            Nat.rec
              ((kSimPackedBase h_ER).interp params)
              (fun i prev =>
                (kSimPackedStep g_ER).interp
                  (Fin.cons i (Fin.cons prev params)))
              recVar ≤
              (kSimTowerBound h_ER g_ER).interp
                (Fin.cons recVar params) :=
          h_dom recVar params
        -- Step 3: apply boundedRec_eq_natRec_of_bounded.
        -- This converts ERMor1.boundedRec to plain
        -- Nat.rec.  Look up the exact signature of
        -- boundedRec_eq_natRec_of_bounded — it likely
        -- requires:
        --   • The dominance hypothesis at every j.
        --   • A monotonicity hypothesis on the bound (use
        --     kSimTowerBound_mono_counter).
        -- The conclusion: ERMor1.boundedRec ... = Nat.rec
        --   ... (when the bound dominates everywhere).
        sorry  -- substantial: ~30-50 lines
        -- Step 4: rewrite the resulting Nat.rec via
        -- packed_iteration_matches_simrecVec to get
        -- Nat.seqPack of simrecVec.
        -- Step 5: rewrite via
        -- kSimSzudzikUnpackAt_interp_eq_seqAt and
        -- Nat.seqAt_seqPack to extract the i-th
        -- component of simrecVec.
        -- Step 6: KMor1.simrec_interp gives that the K^sim
        -- side is exactly KMor1.simrecVec at the same
        -- (h_fam, g_fam, params, recVar, i).
        -- Combining 4-6 closes the equality.
```

The `sorry` marks where the implementer applies
`ERMor1.boundedRec_eq_natRec_of_bounded`.  Look up its
exact signature first via `mcp__lean-lsp__lean_local_-`
`search` or grep:

```bash
grep -n "boundedRec_eq_natRec_of_bounded" \
  GebLean/Utilities/ERArith.lean
```

Then apply with the dominance + monotonicity, and
proceed through Steps 4-6.

**Decomposition into sub-steps**:

- [ ] **Step B.2.1.a: Look up
  `boundedRec_eq_natRec_of_bounded`'s signature**

```bash
grep -A 20 "theorem.*boundedRec_eq_natRec_of_bounded" \
  GebLean/Utilities/ERArith.lean
```

Document its required hypotheses and conclusion in a
plan comment for reference.

- [ ] **Step B.2.1.b: Discharge Step 3 (boundedRec to
  Nat.rec conversion)**

~20-40 lines, depending on the signature.  May need
auxiliary `set` bindings to make the LHS recognizable.

- [ ] **Step B.2.1.c: Discharge Steps 4-6 (Nat.rec to
  simrec equality)**

Use `packed_iteration_matches_simrecVec` and the unpack
round-trip.  ~20-30 lines.

Total estimated for B.2.1: ~50-100 lines.

- [ ] **Step B.2.2: Run `lake build`**

If errors, use `lean_goal` to inspect intermediate goals.

Expected at completion: PASS, no warnings.

- [ ] **Step B.2.3: Run `lake test`**

Expected: PASS.

- [ ] **Step B.2.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add kToER_interp_level_one (Task 17b.3)

Proves K^sim level-1 interp preservation under kToER:
(kToER f).interp ctx = f.interp ctx for all f with
f.level <= 1.  Six structural cases (zero/succ/proj/comp/
raise/simrec); the simrec case discharges the dominance
hypothesis of boundedRec_eq_natRec_of_bounded via
kSimTowerBound_dominates_level_one (Task 17b.2)."
```

---

## Phase III — Task C: kToER_linearBound_dominates_level_one

The level-1 linear bound on the ER side, derived from
Task B's interp preservation.

### Task C.1: Add the lemma

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

- [ ] **Step C.1.1: Append the lemma**

```lean
/-- Linear bound on level-1 K^sim's kToER image.
Translates `KMor1.linearBound_dominates` to the ER side via
`kToER_interp_level_one`. -/
private theorem kToER_linearBound_dominates_level_one
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
    (ctx : Fin a → ℕ) :
    (kToER f
      (Nat.le_succ_of_le h)).interp ctx ≤
      (KMor1.linearBound f h).1 *
        (Finset.univ : Finset (Fin a)).sup ctx +
      (KMor1.linearBound f h).2 := by
  rw [kToER_interp_level_one f h ctx]
  exact KMor1.linearBound_dominates f h ctx
```

- [ ] **Step C.1.2: Run `lake build`**

Expected: PASS, no warnings.

- [ ] **Step C.1.3: Run `lake test`**

Expected: PASS.

- [ ] **Step C.1.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add kToER_linearBound_dominates_level_one (Task 17b.4)

Translates KMor1.linearBound_dominates to the ER side via
kToER_interp_level_one.  Trivial composition; the heavy
lifting is in level-1 interp preservation (Task 17b.3) and
linearBound_dominates itself (already proved at 2843884a)."
```

---

## Phase IV — Task D: kSimTowerBound_dominates_inline (level-2)

> **Plan correction (2026-05-01, mid-execution)**: The
> original Phase IV (preserved as "Phase IV-A: superseded"
> below) followed Strategy A — a level-1 analog of Task A's
> `simrecVec` / `linearBound` chain.  After investigating the
> stub, this Strategy A approach was found to be
> mathematically inconsistent with Tourlakis 2018 §0.1.0.27 (3),
> which states that K^sim_2 functions are polynomially bounded
> (not linearly bounded as at level 1).  The corrected plan is
> Phase IV-B (Strategy B, polynomial-iteration chain) below.
>
> Specifically, the level-1 chain (Phase III, Task A) absorbed
> `Nat.log 2 (KK + …)` into `stepTH + 2*baseTH` via
> `kToER_level0_towerHeight_ge_const` — a structural shape lemma
> for level-0 `linearBound`.  No analogous level-1 shape lemma
> can hold, because `KMor1.linearBound`'s `comp` clause produces
> `(p_f.1 * max_c, p_f.1 * sum_k + p_f.2)` (multiplicative in
> the children with a sum-over-fan-out), while `(kToER f).tH`
> only adds `+1` per `comp` regardless of fan-out.  The mismatch
> blocks any bound
> `(KMor1.linearBound f h).2 ≤ 2^((kToER f).tH + c)` for
> level-1 `f` with fan-out ≥ 2 and any fixed `c`.
>
> The level-2 chain therefore must use polynomial bounds
> (Recursion Class Ch. 4 Prop. 4.7's "iteration of a linear
> function is polynomial"), which is exactly what
> `Nat.polynomial_iter_tower_bound` (Module A, Poly Task 5)
> formalizes, combined with `kSimPackedStep_polyBound` /
> `kSimPackedBase_polyBound` (Module C, Poly Task 16).  The
> infrastructure already exists; the level-2 case re-uses it
> rather than re-implementing the level-1 chain.
>
> See research doc
> `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
> "Implication for the level-2 dominance chain" callout, and
> R5' in the parent plan
> `docs/plans/2026-04-30-er-polynomial-bound-plan.md`.

---

## Phase IV-B — Task D: kSimTowerBound_dominates_inline (corrected)

The level-2 simrec dominance.  Routes the iteration trace
through a polynomial bound on the packed step (Strategy B),
then through `Nat.polynomial_iter_tower_bound` to land in
`tower 2 (linear)`, and finally into `kSimTowerBound`'s
closed-form `tower (stepTH+1) (linear)` via the same
`tower_two_le_tower_three_linear` + `tower_mono_left/right`
absorption used at level 1.

### Task D.0: Investigation phase (no code yet)

**Goal:** before drafting the chain, settle the chain-closing
log-vs-towerHeight relationship.  Two candidate sub-strategies
(B1 and B2 in the parent plan's R5') are sketched; this task
picks one by validating the key inequality on a concrete
example before committing to ~300+ lines of proof.

- [ ] **Step D.0.1: Validate B1 (constructive ER PolyBound)**
  on a small test case.

  Concretely, for a level-1 K^sim term `f := simrec 0 h_fam g_fam`
  where `h_fam`, `g_fam` are families of level-0 K^sim atoms,
  compute by hand:

  - `kToER f` (an ER term with embedded `boundedRec`).
  - `(kToER f).towerHeight`.
  - A constructively-built `pb : ERMor1.PolyBound (kToER f)` via
    per-constructor builders.  This requires a new builder
    `ofBoundedRec` for `ERMor1.boundedRec`'s case.
  - The single-power adapter
    `D := pb.degree + pb.coefficient + pb.constant + 2`.
  - Verify `Nat.log 2 D ≤ (kToER f).towerHeight + small_const`
    holds for the specific term, and identify the small_const.

  Specifically, the new `ofBoundedRec` would say: if `base`,
  `step`, `bound : ERMor1 _` each have `PolyBound`s, and the
  dominance hypothesis holds, then `boundedRec base step bound`
  has a `PolyBound` whose fields are derived from `bound`'s
  fields (since `boundedRec`'s value never exceeds the bound's
  value at the same arguments).  The structural log-vs-tH
  inequality for `boundedRec` reduces to that of the bound
  argument, plus a small additive constant (per the structural
  recursion of `ERMor1.towerHeight` on `boundedRec`).

  **Outcome:** if B1's `Nat.log 2 D ≤ towerHeight + c` holds
  with a small `c`, proceed to D.1.  If not, try B2 below
  before reverting to a more involved approach.

- [ ] **Step D.0.2: If B1 fails, validate B2 (custom K^sim
  measure)** on the same test case.

  Define `KMor1.linearBoundLog : (f : KMor1 a) → f.level ≤ 1 → ℕ`
  recursively (atomic = small; `comp` = `lBL f + max lBL gs +
  log_2 fan-out + small`; `raise` reduces to level-0; `simrec`
  combines max-over-children).  Verify
  `(KMor1.linearBound f h).1 + (KMor1.linearBound f h).2 + 2
    ≤ 2^(KMor1.linearBoundLog f h)` and
  `KMor1.linearBoundLog f h ≤ (kToER f).towerHeight + c'` for
  some small `c'`.

  The fan-out absorption is the unknown; if `log_2 fan-out`
  cannot be bounded by tower-height growth (which is `+1` per
  `comp`, agnostic to fan-out), B2 doesn't close.  In that
  case, B1 is the only viable path; if B1 also failed at D.0.1,
  pause and surface to the user.

- [x] **Step D.0.3: Document the chosen sub-strategy**

  Write a brief callout at the top of Phase IV-B in this plan
  recording: which sub-strategy (B1 or B2), what the constant
  `c` (or `c'`) is, and what new infrastructure (e.g.,
  `ofBoundedRec`) needs to be built before the chain is drafted.

  **Outcome (recorded 2026-05-01)**: chose **B1**.  Numerical
  validation in `GebLeanTests/Phase4Investigation.lean`
  (`#eval` outputs from `lake build`):

  - For `addK : KMor1 2` (level 1, simrec with level-0 children):
    - `KMor1.linearBound addK = (4, 0)`.
    - `(kToER addK).towerHeight = 1117`.
    - Diagnostic `Nat.log 2 ((linearBound).1 + (linearBound).2 + 1)
      = 2`, so `2 ≤ 1117 + c` holds for any `c ≥ -1115`.

  The huge slack arises structurally: every level-1 K^sim simrec's
  `kToER` includes the `boundedRec` + `kSimTowerBound`
  (`iterAutoBoundExpr`) encoding, which contributes ≥ 1100 of
  tower height *independent of the children's structure*.  The
  linear-bound's multiplicative-comp blow-up grows much slower
  (logarithmic in the structural quantities), so the
  log-vs-towerHeight inequality holds with a small constant `c`
  (analysis suggests `c ≤ 5`; addK alone establishes
  `c ≤ 5` for the simrec case at level 1).

  Generalization argument: split the structural induction by
  whether `f` contains a simrec.  If no, `f.level ≤ 0` and
  Lemma 1.B gives the bound directly.  If yes, the simrec's
  encoding cost dominates the linear-bound growth.  See the
  "Findings" section in `GebLeanTests/Phase4Investigation.lean`
  for the full structural argument.

  **Refinement (recorded 2026-05-01, after literature
  re-check)**: the linear-bound formula's level-1 `comp` clause
  was using `sum_k = Σ_i (lb gs_i).2` over fan-out, which is
  strictly looser than Tourlakis Lemma 1.A's proof (research
  doc lines 86-92), which uses `max(args) ≤ (max_i c_i) ·
  max(ctx) + (max_i k_i)` — i.e., `max_i k_i` (max over
  fan-out, not sum).  Switched to `max_k` per literature.
  This eliminates the residual fan-out blow-up at level-1
  comp, and the structural induction
  `Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1)
  ≤ 3 · (kToER f h).towerHeight + 1` closes uniformly with
  the comp case satisfying equality (no slack wasted).

  Commit `0e3bfa66` on `terence/develop` lands this fix.
  Numerical witnesses in `Phase4Investigation.lean` confirm
  `addK`'s `linearBound = (4, 0)` is unchanged (its simrec
  clause already used `level0Shape` directly).

  **Status of `linearBoundLog_le_towerHeight`'s simrec case**:
  the structural induction for the simrec case requires an
  auxiliary lemma `tH(kToER (simrec h_fam g_fam)) ≥ max_l
  tH(kToER h_l) + small_const` (or analog for g_l).  This is
  an instance of "Fix B (part 3): structural towerHeight
  versus analytical tower height" in the research doc (lines
  581-624), which the doc characterizes as **folklore** in
  the literature: implicit in the proof of Recursion Class
  Ch. 4 Prop. 4.6's exponent-tracking through composition
  and bounded recursion, but no single literature
  proposition states it explicitly.  The research doc
  marks it "REQUIRES PROJECT-INTERNAL PROOF; routine
  structural induction once `towerHeight` recursion is
  fixed".

  This lemma is in the same family as the existing
  `kSimPackedBase_towerHeight_ge_propagate` /
  `kSimPackedStep_towerHeight_ge_propagate` /
  `kSimSzudzikPackList_towerHeight_ge_propagate` lemmas
  (Phase III, landed) which lift Prop. 4.6's recipe through
  specific ER terms (`kSimSzudzikPackList`, `kSimPackedBase`,
  `kSimPackedStep`).  Lifting through `kToER (simrec)`'s
  outer wrapping (`comp · (boundedRec · kSimTowerBound)`)
  is the same exercise on a longer expression.

  **New infrastructure required for B1**:

  - `ofBoundedRec : (base : ERMor1 k) → (step : ERMor1 (k + 2))
    → (bound : ERMor1 (k + 1)) → (pb_bound : PolyBound bound) →
    PolyBound (ERMor1.boundedRec base step bound)`.  Trivial
    `bounds` proof via `interp_boundedRec_le_bound` (already
    landed at `Utilities/ERArith.lean` line 1804).  Lives in
    `GebLean/LawvereERPolynomialBound.lean`, ~30 lines.
  - `KMor1.linearBoundLog_le_towerHeight :  
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1),
       Nat.log 2 ((KMor1.linearBound f h).1 +
                  (KMor1.linearBound f h).2 + 1)
         ≤ (kToER f (Nat.le_succ_of_le h)).towerHeight + c`
    for some explicit small constant `c` (target `c = 5`).
    Proved by structural recursion on `f`, with the simrec
    case using a separately-proved structural lower bound
    `simrecCost_le_towerHeight : (kToER (simrec ...))
    .towerHeight ≥ structural_min_cost` to dominate the
    linear-bound's growth.  Lives in
    `GebLean/LawvereKSimPolynomialBound.lean`, ~100-200 lines.
  - `kToER_polyBound_of_level_one :
    (f : KMor1 a) → (h : f.level ≤ 1) →
    ERMor1.PolyBound (kToER f (Nat.le_succ_of_le h))`
    constructed structurally.  Lives in
    `GebLean/LawvereKSimPolynomialBound.lean`, ~50 lines
    (simple wrapper around the inductive structure).

  **Do not proceed to D.1–D.5 until D.0.3 is complete.**

---

### Task D.1: Stub the main theorem

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

- [ ] **Step D.1.1: Append the stub**

```lean
/-- Level-2 simrec dominance: the iterated packed value of
`kSimPackedStep` over `kSimPackedBase` is dominated by
`kSimTowerBound`'s closed-form tower at every iteration counter
and parameter context, when both base and step families consist
of level-≤-1 K^sim terms.  Used by kToER's simrec case at
level ≤ 2 (see Task 14 of the kToER plan).

Compared to `kSimTowerBound_dominates_level_one` (Task 17b.2,
private), the level-2 case routes through polynomial-iteration
bounds (Strategy B per parent plan R5') rather than linear
bounds, in line with Tourlakis 2018 §0.1.0.27 (3): K^sim_2
functions are polynomially bounded, not linearly. -/
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
        (Fin.cons j params) := by
  sorry
```

Note this lemma is **public** (no `private`), since Task 14
of the kToER plan needs to access it.

- [ ] **Step D.1.2: Run `lake build`**

Expected: PASS with `sorry` warning.

- [ ] **Step D.1.3: Do not commit yet.**

---

### Task D.2: Build per-component PolyBounds for level-1 children

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** for each level-1 K^sim child (`h_fam l` or `g_fam l`),
construct an `ERMor1.PolyBound (kToER (child))`.  Two candidate
constructions, depending on D.0's outcome:

- **B1 path**: build constructively by structural induction on
  the ER term `kToER (child)`, via per-constructor builders
  (`ofZero`, `ofSucc`, `ofProj`, `ofComp`, `ofBoundedRec` —
  the last being new).  This avoids `KMor1.linearBound`'s
  multiplicative blow-up by working directly on the ER side
  where `towerHeight` is the natural measure.  The `bounds`
  proof for each builder follows the ER constructor's value
  bound; the structural log-vs-tH inequality is established
  for each builder during the structural induction.
- **B2 path**: build with `degree = 1`,
  `coefficient = (KMor1.linearBound child h).1`,
  `constant = (KMor1.linearBound child h).1 +
  (KMor1.linearBound child h).2`, with `bounds` proof via
  `kToER_linearBound_dominates_level_one (child) h ctx` plus
  algebra to absorb the `+1` shift between `c * sup ctx + k`
  and `c * (maxCtx + 1) + (c + k)`.  The chain-closing log-vs-tH
  bound then routes through the custom `KMor1.linearBoundLog`
  measure.

(After D.0.3, only the chosen path is implemented here.)

- [ ] **Step D.2.1: Append the chosen per-component PolyBound
  builders**

For B1, this includes `ofBoundedRec` in
`GebLean/LawvereERPolynomialBound.lean` (~80-150 lines) plus a
recursive `ofKToER : (f : KMor1 a) → f.level ≤ 1 → PolyBound
(kToER f h)` in `GebLean/LawvereKSimPolynomialBound.lean`
(~100-200 lines).

For B2, this is a single `polyBoundOfLinearBound` wrapping
`kToER_linearBound_dominates_level_one` (~30-50 lines), plus
the `KMor1.linearBoundLog` definition and its two structural
inequalities (~150-300 lines depending on fan-out absorption).

- [ ] **Step D.2.2: Run `lake build`**

Expected: PASS.

- [ ] **Step D.2.3: Do not commit yet.**

---

### Task D.3: Apply the packed-step / packed-base PolyBound builders

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** use the per-component PolyBounds from D.2 to construct
`pb_packed_base : ERMor1.PolyBound (kSimPackedBase h_ER)` and
`pb_packed_step : ERMor1.PolyBound (kSimPackedStep g_ER)`.
This is a direct call to `kSimPackedBase_polyBound` and
`kSimPackedStep_polyBound` (both already landed at Poly Task 16).

- [ ] **Step D.3.1: Build the packed PolyBounds**

```lean
let pb_packed_base : ERMor1.PolyBound (kSimPackedBase h_ER) :=
  kSimPackedBase_polyBound h_ER pb_h
let pb_packed_step : ERMor1.PolyBound (kSimPackedStep g_ER) :=
  kSimPackedStep_polyBound g_ER pb_g
```

(no new infrastructure; this is plumbing.)

- [ ] **Step D.3.2: Build the chain-closing log-vs-tH lemma**

A new lemma whose statement depends on D.0: roughly
`Nat.log 2 (pb_packed_step.degree + pb_packed_step.coefficient +
pb_packed_step.constant + 2) ≤ stepTH + small_const` (or
analogous for B2).  Proof: combine D.2's per-component log-vs-tH
inequality with the formula for `kSimPackedStep_polyBound`'s
fields (degree = E = (D_max + 5) * 4^(k+1), coefficient = 3^E,
constant = 0), and the structural propagate lemma
`kSimPackedStep_towerHeight_ge_propagate`.

(~80-150 lines.)

- [ ] **Step D.3.3: Run `lake build`**

Expected: PASS.

- [ ] **Step D.3.4: Do not commit yet.**

---

### Task D.4: Apply the iter-step-form adapter and the iteration bound

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** convert the packed step `PolyBound` to the form
consumed by `Nat.polynomial_iter_tower_bound`, then bound the
j-iteration of the packed step starting from packed base.

- [ ] **Step D.4.1: Apply `to_iter_step_form` to
  `pb_packed_step`**

Yields a single-power bound on the packed step's interp
in terms of `(maxCtx + 2)^D` for the integer
`D = pb_packed_step.degree + pb_packed_step.coefficient +
pb_packed_step.constant + 2`.

- [ ] **Step D.4.2: Bound the base linearly**

`Nat.polynomial_iter_tower_bound`'s `h_base` hypothesis
requires `v_0 x ≤ m * x + m` (linear in `x`).  Convert
`pb_packed_base`'s polynomial bound to a linear bound by
choosing `m` large enough; for our use, the polynomial degree
of `pb_packed_base` may exceed 1, so we instead use a slightly
loosened version: `pb_packed_base.interp params ≤
(maxCtx params + 2)^D_base`, then absorb `(maxCtx + 2)^D_base
≤ tower 2 (linear)` via `pow_le_tower_two_with_shift` and
treat the iteration's base as the resulting tower-2 bound.

(May require a generalization of
`Nat.polynomial_iter_tower_bound` to allow polynomial base, or
a small adapter lemma.)

- [ ] **Step D.4.3: Apply `Nat.polynomial_iter_tower_bound`**

Yields `iter j ≤ tower 2 ((Nat.log 2 D + 2) * j + linear in
sumCtx)`.

- [ ] **Step D.4.4: Run `lake build`**

Expected: PASS.

- [ ] **Step D.4.5: Do not commit yet.**

---

### Task D.5: Close the chain into `kSimTowerBound`

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** chain `tower 2 (linear)` into `kSimTowerBound`'s
`tower (stepTH+1) (linear)` form.  Same chain as Phase III's
A.6 from line 1955+ onward, but starting from `tower 2 (linear
in (j, sumCtx, log_2 D, m))` rather than `tower 2 (CC * S +
KK + 1 + log_2 E + 2)`.

- [ ] **Step D.5.1: Apply `tower_two_le_tower_three_linear`**

Yields `tower 3 (j + sumCtx + log_2(log_2 D + 3) + log_2(other
linear factor) + 2)`.

- [ ] **Step D.5.2: Apply `tower_mono_left` (stepTH ≥ 2)
  and `tower_mono_right`**

`stepTH ≥ k+2 ≥ 2` from `kSimPackedStep_towerHeight_ge_succ_k`,
giving stepTH+1 ≥ 3.  For `tower_mono_right`, use the chain-
closing log-vs-tH inequality from D.3.2 to absorb the log_2
factors into stepTH + 2*baseTH, plus j ≤ sumCtx and similar.

- [ ] **Step D.5.3: Replace D.1's sorry**

The full proof composes D.2–D.5's helpers.  Estimated 50-150
lines for the assembly.

- [ ] **Step D.5.4: Run `lake build` and `lake test`**

Expected: PASS, no warnings.

- [ ] **Step D.5.5: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean \
        GebLean/LawvereERPolynomialBound.lean
git commit -m "Add kSimTowerBound_dominates_inline (Task 17c)

Level-2 simrec dominance via polynomial-iteration chain
(Strategy B per parent plan R5'), in line with Tourlakis 2018
\$0.1.0.27 (3) — K^sim_2 functions are polynomially bounded,
not linearly.  Routes through kSimPackedStep_polyBound
(Task 16) plus Nat.polynomial_iter_tower_bound (Task 5,
formalizing Recursion Class Ch. 4 Prop. 4.7) instead of the
linear-bound chain used at level 1.  Public theorem,
consumed by Task 14 of the kToER plan."
```

---

## Phase IV-A — superseded original plan

*Preserved for the record.  Do not implement.*

The original Phase IV plan (Tasks D.1, D.2, D.3 below)
followed Strategy A: a level-1 analog of Task A's
`simrecVec` / `linearBound` chain.  The plan was discarded
on 2026-05-01 after investigation showed that Tourlakis 2018
§0.1.0.27 (3) explicitly stratifies the bound at level — at
level 2 the bound is polynomial, not linear — and that the
level-1 chain's `kToER_level0_towerHeight_ge_const`
absorption step does not extend to a level-1 analog because
`KMor1.linearBound`'s `comp` clause is multiplicative in
the children with a sum-over-fan-out, while `(kToER f).tH`
is additive with a sup-over-fan-out.

The corrected plan is Phase IV-B above.

### (superseded) Task D.1: Stub the theorem

```text
[Same theorem statement as the corrected D.1 above; the
statement itself is correct, only the proof strategy changed.]
```

### (superseded) Task D.2: add parallel level-1 simrecVec aux

A `KMor1.simrecVec_linear_bound_aux_level_one` mirroring the
existing level-0 aux's structure, with `KMor1.linearBound`
substituted for `level0Shape.linearBound`.  The chain-closing
step would need a level-1 analog of
`kToER_level0_towerHeight_ge_const`, which does not exist (per
the obstruction analysis above).

### (superseded) Task D.3: Compose the level-2 chain

Mirrors A.6's calc chain with substitutions
`level0Shape → KMor1.linearBound`, etc.  The chain does not
close at the final `tower_mono_right` step because the
log-vs-tH bound on level-1 `linearBound` constants does not
hold in additive form.

---

## Phase V: tests, re-export, kToER plan, final verification

### Task E: Module C tests

**Files:**

- Create: `GebLeanTests/LawvereKSimPolynomialBound.lean`

- [ ] **Step E.1: Create the test file**

```lean
import GebLean.LawvereKSimPolynomialBound
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereKSimPolynomialBound

`#guard` checks for `level0Shape` on atomic K^sim terms,
plus end-to-end tests for `linearBound_dominates`,
`kToER_linearBound_dominates_level_one`, and
`kSimTowerBound_dominates_inline` on `addK`.
-/

open GebLean

private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]

example : KMor1.level0Shape (KMor1.zero (n := 0))
    (by simp [KMor1.level]) =
      ConstantOrShiftedProj.const 0 := rfl

example : KMor1.level0Shape KMor1.succ
    (by simp [KMor1.level]) =
      ConstantOrShiftedProj.shifted 0 1 := rfl

example : KMor1.level0Shape (KMor1.proj (0 : Fin 2))
    (by simp [KMor1.level]) =
      ConstantOrShiftedProj.shifted 0 0 := rfl

private def addK : KMor1 2 :=
  KMor1.simrec (k := 0) (a := 1)
    (0 : Fin 1)
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 1))
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.succ
        (fun _ : Fin 1 => KMor1.proj (2 : Fin 3)))

private theorem addK_level : addK.level ≤ 1 := by decide

example : addK.interp (ctx2 3 5) ≤
    (KMor1.linearBound addK addK_level).1 *
      (Finset.univ : Finset (Fin 2)).sup (ctx2 3 5) +
    (KMor1.linearBound addK addK_level).2 :=
  KMor1.linearBound_dominates addK addK_level (ctx2 3 5)

example : (kToER addK
    (Nat.le_succ_of_le addK_level)).interp (ctx2 3 5) ≤
    (KMor1.linearBound addK addK_level).1 *
      (Finset.univ : Finset (Fin 2)).sup (ctx2 3 5) +
    (KMor1.linearBound addK addK_level).2 :=
  kToER_linearBound_dominates_level_one
    addK addK_level (ctx2 3 5)
```

(The end-to-end `kSimTowerBound_dominates_inline` test from
the original plan needs witnesses for `addK_h_fam` /
`addK_g_fam` at level 1; if the witnesses are too brittle,
restrict to the level-1 case from Task 17b.4.)

- [ ] **Step E.2: Run `lake build` and `lake test`**

Expected: PASS.

- [ ] **Step E.3: Commit**

```bash
git add GebLeanTests/LawvereKSimPolynomialBound.lean
git commit -m "Add tests for LawvereKSimPolynomialBound

#guard checks for level0Shape on atomic K^sim terms; end-
to-end tests for linearBound_dominates and
kToER_linearBound_dominates_level_one on addK."
```

---

### Task F: Re-export new modules

**Files:**

- Modify: `GebLean.lean`
- Modify: `GebLeanTests.lean`

- [ ] **Step F.1: Add export to GebLean.lean**

Append (in alphabetical position, near
`LawvereERPolynomialBound`):

```lean
import GebLean.LawvereKSimPolynomialBound
```

- [ ] **Step F.2: Add export to GebLeanTests.lean**

```lean
import GebLeanTests.LawvereKSimPolynomialBound
```

- [ ] **Step F.3: Run `lake build` and `lake test`**

Expected: PASS.

- [ ] **Step F.4: Commit**

```bash
git add GebLean.lean GebLeanTests.lean
git commit -m "Re-export LawvereKSimPolynomialBound module

Adds the new module to GebLean.lean's public surface and
to GebLeanTests.lean's test runner."
```

---

### Task G: Update kToER plan to reference new infrastructure

**Files:**

- Modify:
  `docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`

- [ ] **Step G.1: Update Task 14's annotations**

Find the "Revision required" callout in Task 14 (around
line 1428) and update it to reference
`kSimTowerBound_dominates_inline` (now landed) as the
deliverable that closes the simrec case.

Concrete text to replace the existing callout:

```text
> **Inline dominance available (2026-04-30)**: the simrec
> case discharges the `boundedRec_eq_natRec_of_bounded`
> dominance hypothesis via
> `kSimTowerBound_dominates_inline`
> (`GebLean/LawvereKSimPolynomialBound.lean`, public
> theorem).  See the polynomial-bound plan
> `docs/plans/2026-04-30-er-polynomial-bound-plan.md`
> Phase IV / Task D for the chain structure.
```

- [ ] **Step G.2: Run `markdownlint-cli2`**

```bash
markdownlint-cli2 \
  docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md
```

Expected: 0 errors.

- [ ] **Step G.3: Commit**

```bash
git add docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md
git commit -m "Update kToER plan: Task 14 dominance now available

References the newly-landed kSimTowerBound_dominates_inline
(polynomial-bound plan Phase IV / Task D) as the deliverable
that closes Task 14's simrec case."
```

---

### Task H: Final verification

**Files:** none.

- [ ] **Step H.1: Full build**

```bash
lake build
```

Expected: PASS, 1521+ jobs (the new module adds a few),
no warnings.

- [ ] **Step H.2: Full test**

```bash
lake test
```

Expected: PASS.

- [ ] **Step H.3: Verify no `sorry`/`admit`**

```bash
grep -rn "sorry\|admit" GebLean/ GebLeanTests/ \
  --include="*.lean" | \
  grep -v ".session/" | \
  grep -v "^[^:]*:.*--"
```

Expected: zero matches.

- [ ] **Step H.4: Verify task graph in
  `docs/plans/2026-04-30-er-polynomial-bound-plan.md`
  is consistent with completed work**

Open the parent plan, check that Tasks 17a, 17b (now sub-
tasks 17b.1–17b.4), 17c (sub-tasks 17c.1–17c.2), 18, 19,
20, 21 are all done.  Add a final
"Workstream complete" note at the top.

- [ ] **Step H.5: Optional — task list cleanup**

The internal task-tracker list has tasks 307 and 308 (Poly
Task 17b, Poly Task 17c) marked in progress / pending.
Update them to completed.  Also Poly Task 18, 19, 20, 21
(currently pending) become completed.

This is a cosmetic step; skip if not appropriate.

---

## Cross-task notes

### When to invoke `lean4:sorry-filler-deep`

Tasks A.5.1 (`tower_two_le_tower_three_linear`) and A.5.4
(`kSimTowerBound_arg_dominates_log`) involve `Nat.log`
arithmetic that mathlib's automation may not close
trivially.  If after 2-3 attempts these proofs are still
stuck, dispatch `lean4:sorry-filler-deep` on the specific
sorry, with context about the lemma's purpose and the
algebraic identity needed.

### When to fall back to Strategy B

If Task A.5's tower-absorption proof becomes a multi-day
quagmire, switch to Strategy B per parent plan refinement
R3:

1. Reuse Task 16's `kSimPackedStep_polyBound` and
   `kSimPackedBase_polyBound`.
2. Specialize `Nat.polynomial_iter_tower_bound` to a
   single-arg `x = sumCtx` summary, proving the multi-arg
   step bound holds via the `subCtx ≤ s = maxCtx ctx`
   bound already in `kSimPackedStep_polyBound`.
3. The structural lemma `kSimPackedStep_towerHeight_-`
   `ge_two` (already proved) suffices.

Strategy B trades one big absorption proof for one big
specialization proof; pick whichever is making progress.

### Helper lemma module placement

If any of Tasks A.4, A.5.1, or A.5.4's helpers are
generic enough (i.e. don't reference `KMor1` /
`kSimPackedStep`), move them to
`GebLean/Utilities/ComputationalComplexity.lean` for reuse.
Specifically:

- `tower_two_le_tower_three_linear` is generic — move it.
- `pow_le_tower_two_with_shift` is generic — move it.
- `kSimTowerBound_arg_dominates_log` is K^sim-specific —
  keep it in `LawvereKSimPolynomialBound.lean`.

If moving, do so as part of the corresponding sub-task's
commit.

---

## Self-review checklist

Before declaring this plan ready for execution, verify:

- [ ] Every step has either runnable code or a precise
  textual instruction (no "TBD", "TODO", "implement
  later").
- [ ] Every theorem statement is fully written out (not
  "as in Task A.1").
- [ ] Every `sorry` left in the plan as a marker is
  explicitly called out as a placeholder for a sub-task
  to fill in later.
- [ ] Type signatures match between consumer tasks and
  producer tasks (e.g. `KMor1.simrecVec_uniform_linear_-`
  `bound`'s output shape matches what `simrecVec_seqPack_-`
  `le_pow` expects).
- [ ] Every commit message is concrete and references
  the task it implements.
- [ ] No banned-words violations (per
  `CLAUDE.md`'s code-style list).
- [ ] Line length ≤ 80 characters in code blocks.

If any check fails, fix inline before dispatching to an
implementer.
