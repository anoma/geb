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

This plan was reviewed adversarially after first draft.
Findings (P1–P6) are inlined into the relevant tasks
below.  The single highest-risk subtask is **Phase I
Task A.5** (tower-level absorption + structural
propagation).  Detail:

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
   `(kSimSzudzikPackList t).towerHeight ≥ k + 2 +
   sup_j (t j).towerHeight`.  This passes children's
   tower heights up through the packing structure.
2. **Tower-level absorption** (A.5.1): prove
   `tower 2 (C * X + D) ≤ tower 3 (X + log_2 (C+1) +
   log_2 (D+1) + 2)`.  Generic Module-A-friendly
   helper.
3. **Connect-up** (A.5.2): combine A.5.0 with
   level0Shape inspection to bound `log_2 CC ≤
   max_l (g_ER l).towerHeight + small`, hence
   `≤ stepTH - k - 2 + small`, hence absorbed by
   stepTH+1's contribution to `Y`.

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

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (append after
  `kSimSzudzikPackList_towerHeight_ge_succ_k`)

**Goal:** prove `(kSimSzudzikPackList t).towerHeight ≥ k +
2 + sup_l (t l).towerHeight`.  This pushes per-child
heights up through the natPair stack.

- [ ] **Step A.5.0.1: Append the propagation lemma**

```lean
/-- `kSimSzudzikPackList`'s towerHeight propagates the
maximum child tower height: each `comp natPair` layer
contains the recursive packList plus the next child, so
the sup over l of `(t l).towerHeight` enters via
`Finset.le_sup` extraction at depth-l. -/
private theorem kSimSzudzikPackList_towerHeight_ge_propagate
    : ∀ {a k : ℕ} (t : Fin (k + 1) → ERMor1 a),
      k + 2 + (Finset.univ : Finset (Fin (k + 1))).sup
        (fun l => (t l).towerHeight) ≤
      (kSimSzudzikPackList t).towerHeight
  | a, 0,     t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      -- Goal: 0 + 2 + sup{(t 0).tH over Fin 1} ≤ ...
      -- Inner: comp natPair [t 0, zeroN a] has tH ≥
      --   natPair.tH + sup{(t 0).tH, 0} + 1 ≥
      --   1 + (t 0).tH + 1 = (t 0).tH + 2
      -- Outer: comp succ ... = sup{inner} + 1 = (t 0).tH
      --   + 3 ≥ (t 0).tH + 2 ≥ sup{(t 0).tH over Fin 1}
      --   + 2.
      sorry
  | a, k + 1, t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      -- Goal: k + 1 + 2 + sup{(t l).tH over Fin (k+2)}
      --   ≤ inner + 1 (outer comp succ adds 1)
      -- where inner ≥ natPair.tH + sup{(t 0).tH,
      --   packList recur.tH} + 1
      -- packList recur has tH ≥ k + 2 + sup{(t l.succ).tH}
      --   by IH.
      -- sup{(t 0).tH, packList recur.tH} captures both
      -- (t 0).tH and the IH's sup.  Combined:
      -- inner ≥ 1 + max((t 0).tH, k+2+sup{others}) + 1
      --   ≥ 1 + max(k+2+(t 0).tH, k+2+sup{others}) + 1
      --     [if (t 0).tH ≤ sup{others}]
      --   = k + 4 + sup{(t l).tH over Fin (k+2)}
      -- LHS = k + 3 + sup{...over Fin (k+2)} ≤ inner + 1
      --   ✓
      sorry
```

- [ ] **Step A.5.0.2: Discharge the base case sorry**

The k=0 case extracts `(t 0).tH` via `Finset.le_sup` for
both the inner Fin 2 (where `t 0` sits at index 0) and
the outer Fin 1 (the comp natPair wrapper).  Goal
manipulation uses `change` to shape into omega-amenable
arithmetic.

```lean
  | a, 0, t => by
      unfold kSimSzudzikPackList
      simp only [ERMor1.towerHeight]
      -- Sup over Fin 1 of (t l).tH is just (t 0).tH:
      have hsup_eq :
          Finset.univ.sup
            (fun l : Fin 1 => (t l).towerHeight) =
          (t 0).towerHeight := by
        rw [show (Finset.univ : Finset (Fin 1)) =
              {(0 : Fin 1)} from rfl]
        simp [Finset.sup_singleton]
      rw [hsup_eq]
      -- Inner (Fin 2) sup with (t 0).tH at idx 0:
      let G : Fin 2 → ℕ := fun i =>
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ => ERMor1.zeroN a).towerHeight
      have hG0 : G ⟨0, by omega⟩ = (t 0).towerHeight := rfl
      have hG_le_sup :
          (t 0).towerHeight ≤ Finset.univ.sup G := by
        rw [← hG0]
        exact Finset.le_sup (Finset.mem_univ _)
      -- Outer (Fin 1) sup of (natPair.tH + sup G + 1):
      let F : Fin 1 → ℕ := fun _ =>
        ERMor1.natPair.towerHeight + Finset.univ.sup G + 1
      have hF0_eq : F 0 ≥ (t 0).towerHeight + 2 := by
        change ERMor1.natPair.towerHeight +
          Finset.univ.sup G + 1 ≥ (t 0).towerHeight + 2
        omega
      have hF0_le_sup : F 0 ≤ Finset.univ.sup F :=
        Finset.le_sup (Finset.mem_univ (0 : Fin 1))
      change 0 + 2 + (t 0).towerHeight ≤
        0 + Finset.univ.sup F + 1
      omega
```

- [ ] **Step A.5.0.3: Discharge the inductive case sorry**

Similar pattern but the inner Fin 2 sup at index 1 holds
the recursive `packList(k)`.  Use IH on the recursive
call, take `Finset.le_sup` at index 1, combine with sup
over the outer Fin (k+2).

The trickiest part: connecting `sup{(t 0).tH, recur.tH}`
to `sup{(t l).tH over Fin (k+2)}`.  Use:

- `(t 0).tH ≤ sup over Fin (k+2)` (Finset.le_sup at l=0)
- `(t l.succ).tH ≤ sup over Fin (k+2)` for l in Fin (k+1)
- Therefore `sup over Fin (k+1) of (t l.succ).tH ≤ sup
  over Fin (k+2) of (t l).tH`
- IH gives recur.tH ≥ k+2 + sup over Fin (k+1) of
  (t l.succ).tH
- Combining: max((t 0).tH, recur.tH) ≥ max((t 0).tH,
  k+2 + sup_succ) ≥ max(0, k+2) + sup over Fin (k+2)
  = k+2 + sup over Fin (k+2).

Then the outer adds 1 + 1 + natPair.tH ≥ 3 to reach the
required `k + 3 + sup`.  Detailed proof ~50 lines.

- [ ] **Step A.5.0.4: Add the kSimPackedStep corollary**

```lean
private theorem kSimPackedStep_towerHeight_ge_propagate
    {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    k + 2 + (Finset.univ : Finset (Fin (k + 1))).sup
      (fun l =>
        (ERMor1.comp (g l) kSimStepContext).towerHeight) ≤
      (kSimPackedStep g).towerHeight := by
  unfold kSimPackedStep
  exact kSimSzudzikPackList_towerHeight_ge_propagate _
```

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

#### Task A.5.2: connect-up lemma absorbing log_2 CC

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** prove the specific connect-up inequality
needed by A.6's calc chain.  This uses A.5.0's structural
propagation to bound `log_2 CC ≤ stepTH - k - 2 + small`
in a manner compatible with kSimTowerBound's argument
shape.

- [ ] **Step A.5.2.1: Append a structural log-CC bound**

```lean
/-- The structural towerHeight of `kSimPackedStep g`
absorbs `log_2 (CC + 1)` where `CC` is the K^sim-side
linear coefficient extracted from level0Shape.  Mechanism:
each level-0 child's `linearBound.2` (constant) is
bounded by `(kToER child).towerHeight + 1`, and the
packed step's towerHeight propagates `sup_l (kToER
child).towerHeight + (k+2)`. -/
private theorem stepTH_dominates_log_CC
    {a k : ℕ}
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
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
    let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
      fun l => kToER (g_fam l)
        (Nat.le_succ_of_le (Nat.le_succ_of_le (h_g l)))
    Nat.log 2 (CC + 1) ≤
      (kSimPackedStep g_ER).towerHeight := by
  sorry
```

- [ ] **Step A.5.2.2: Discharge the sorry**

Proof outline (estimated 60-100 lines):

1. Use A.5.0's propagation:
   `(kSimPackedStep g_ER).towerHeight ≥ k + 2 + sup_l
   (g_ER l).towerHeight`.
2. Bound `sup_l (g_ER l).towerHeight ≥ max_step_k`:
   - For each level-0 child `g_fam l`, `kToER (g_fam l)`
     has the same structural shape (induction on level-0
     KMor1).
   - `(level0Shape (g_fam l)).linearBound.2` (the
     constant component) equals the structural depth of
     successive succs.
   - This depth equals or exceeds `(kToER (g_fam l)).
     towerHeight - 1` (succ atomically gives towerHeight
     0 even though linearBound.2 = 1; for c≥1 the comp
     stack matches).
3. Combine: `stepTH ≥ k + 2 + max_step_k`.
4. Bound `log_2(CC+1) ≤ log_2(2*max_step_k + 3) ≤
   max_step_k + 2 ≤ stepTH - k`.  For `k ≥ 0`, this
   gives `log_2(CC+1) ≤ stepTH`, satisfying the goal.

The (g_ER l).towerHeight ≥ linearBound.2 - 1 step
requires its own induction lemma over level-0 KMor1.
Place that as a private helper:

```lean
private theorem kToER_level0_towerHeight_ge_const
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0) :
    (KMor1.level0Shape f h).linearBound.2 ≤
      (kToER f
        (Nat.le_succ_of_le
          (Nat.le_succ_of_le h))).towerHeight + 1 := by
  -- Induction on level-0 KMor1: zero/succ/proj/comp/raise.
  -- Atomic cases: zero (linearBound.2 = 0, tH = 0); succ
  -- (linearBound.2 = 1, tH = 0, so tH+1 = 1 ≥ 1); proj
  -- (linearBound.2 = 0, tH = 0).  Comp case: substitution
  -- via level0Shape's comp clause; tower grows by ≥ 1
  -- per layer.  Raise case: same as base.
  sorry
```

This sub-lemma is also estimated 30-60 lines.

- [ ] **Step A.5.2.3: Run `lake build`**

Expected: PASS.

- [ ] **Step A.5.2.4: Do not commit yet (commit after
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
  -- Step 6: combine via stepTH ≥ k+2, then absorb
  -- log_2 (CC+1) via A.5.2.
  have h_step_dom :=
    stepTH_dominates_log_CC g_fam h_g
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

The level-2 simrec dominance, mirroring Task A's structure
with level-1 children.  This is the deliverable that Task 14
of the kToER plan consumes.

### Task D.1: Stub the theorem

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

- [ ] **Step D.1.1: Append the stub**

```lean
/-- Level-2 simrec dominance: same as
`kSimTowerBound_dominates_level_one` but with level-1
children instead of level-0.  Used by kToER's simrec case
at level ≤ 2 (see Task 14 of the kToER plan). -/
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

### Task D.2: add parallel level-1 simrecVec aux

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

**Goal:** create a level-1 analog of
`KMor1.simrecVec_linear_bound_aux` that uses
`KMor1.linearBound` directly instead of `level0Shape`.
Mirrors the existing aux's proof structure.

**Decision (per brainstorm P3)**: do NOT refactor the
existing level-0 aux — it would risk breaking
`KMor1.linearBound_dominates`'s simrec case (currently
landed at line 502+).  Instead, create a parallel aux
with a `_level_one` suffix and reuse helper code where
possible.

- [ ] **Step D.2.1: Append the level-1 aux**

```lean
/-- Level-1 analog of
`KMor1.simrecVec_linear_bound_aux`: at iteration `n ≤ S`,
each component of `simrecVec` is bounded linearly when
the families have level ≤ 1, using
`KMor1.linearBound`'s pair (cf. `KMor1.linearBound_-`
`dominates`). -/
private theorem KMor1.simrecVec_linear_bound_aux_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hh : ∀ j, (h_fam j).level ≤ 1)
    (hg : ∀ j, (g_fam j).level ≤ 1)
    (params : Fin a → ℕ)
    (S : ℕ)
    (hparams : ∀ j, params j ≤ S)
    (base_max : ℕ)
    (hbase_max : ∀ j,
      (KMor1.linearBound (h_fam j) (hh j)).2 ≤ base_max)
    (step_c step_k : ℕ)
    (hstep_c : ∀ j,
      (KMor1.linearBound (g_fam j) (hg j)).1 ≤ step_c)
    (hstep_k : ∀ j,
      (KMor1.linearBound (g_fam j) (hg j)).2 ≤ step_k)
    (n : ℕ) (hn : n ≤ S) :
    ∀ j,
      KMor1.simrecVec h_fam g_fam params n j
        ≤ (step_c + step_k + 1) * S
            + base_max + step_k * n := by
  induction n with
  | zero =>
      intro j
      simp only [KMor1.simrecVec]
      -- KMor1.simrecVec at zero = (h_fam j).interp params
      have hdom :=
        KMor1.linearBound_dominates (h_fam j) (hh j) params
      have hsup_params :
          (Finset.univ : Finset (Fin a)).sup params ≤ S := by
        apply Finset.sup_le
        intro i _
        exact hparams i
      have hbase_j := hbase_max j
      -- (h_fam j).interp params ≤ p.1 * sup ctx + p.2
      -- with p = linearBound h_fam j.  Bound each piece.
      sorry
  | succ n ih =>
      intro j
      have hn' : n ≤ S := Nat.le_of_succ_le hn
      have ih' := ih hn'
      simp only [KMor1.simrecVec]
      -- Mirror the existing level-0 aux's succ case but
      -- substitute KMor1.linearBound for level0Shape.
      sorry
```

The two `sorry`s mirror the existing aux's structure
exactly; the implementer can copy the level-0 proof at
line 342–485 of `LawvereKSimPolynomialBound.lean`,
substituting:

- `KMor1.level0Shape (...)` → no longer used
- `(level0Shape ...).linearBound.1` →
  `(KMor1.linearBound ... hg/hh).1`
- `ConstantOrShiftedProj.linearBound_dominates` →
  `KMor1.linearBound_dominates`
- `KMor1.level0Shape_interp` → omit (linearBound applies
  to f directly)

Estimated 100-180 lines (similar to the existing aux).

- [ ] **Step D.2.2: Run `lake build`**

Expected: PASS.

- [ ] **Step D.2.3: Do not commit yet.**

---

### Task D.3: Compose the level-2 chain

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`

Same structure as Task A.6 but using level-1 inputs.

- [ ] **Step D.3.1: Replace D.1's sorry**

The proof mirrors A.6 with the substitutions:

- `level0Shape` → `KMor1.linearBound`
- `simrecVec_uniform_linear_bound` →
  `simrecVec_linear_bound_aux_general` (or `_level_one`)
- The seqPack-to-tower chain (A.3, A.4, A.5) is identical
  in structure; the constants `CC`/`KK` come from level-1
  `linearBound` instead of level-0 `level0Shape`.

Estimated 100-200 lines.

- [ ] **Step D.3.2: Run `lake build`**

Expected: PASS, no warnings.

- [ ] **Step D.3.3: Run `lake test`**

Expected: PASS.

- [ ] **Step D.3.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Add kSimTowerBound_dominates_inline (Task 17c)

Level-2 simrec dominance: same chain as
kSimTowerBound_dominates_level_one (Task 17b.2) but with
level-1 children using KMor1.linearBound directly instead
of level0Shape.  Public theorem, consumed by Task 14 of
the kToER plan."
```

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
