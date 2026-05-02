# TowerBound architecture v3 Implementation Plan

> **SUPERSEDED 2026-05-02** — see notice in the corresponding
> design doc
> (`docs/plans/2026-05-02-towerbound-architecture-design.md`).
> Plan v4 (literature-aligned, level-1 mirror) replaces this:
> `docs/plans/2026-05-02-ksim-tower-bound-dominates-inline-plan.md`.
> Preserved as a record of the planning exploration.

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** discharge the Phase IV-B headline theorem
`kSimTowerBound_dominates_inline` (level-2 K^sim simrec
dominance) by introducing a `TowerBound` type that generalizes
`PolyBound` to admit tower-shaped majorants, replacing plan v2's
structurally impossible `kToER_polyBound_of_level_one` bridge.

**Architecture:** mirrors the level-1 chain template
`kSimTowerBound_dominates_level_one` (`LawvereKSimPolynomialBound.lean:2578`)
but generalizes the bound type so the recursive bridge becomes
mathematically possible.  All landed `PolyBound` infrastructure
(17 builders, packed bound apparatus, D.0.A's 10 atomic-derived
builders) lifts to `TowerBound` at height 0 via a definitional
injection (since `tower 0 x = x` by `Utilities/Tower.lean:21`).

**Tech stack:** Lean 4, mathlib, `lake build` / `lake test`.

**Convention:** every committed task ends in a clean `lake build`
plus `lake test`, with commit subject ending in `(TowerBound v3 TN)`
where N is the task number.  Per project policy: no `sorry` or
`admit` in committed state, no warnings, no banned vocabulary
(see `CLAUDE.md`).

---

## File structure

The plan creates two new modules and modifies one existing
utilities module:

- **Create** `GebLean/LawvereERTowerBound.lean` — host the
  `TowerBound` type, its injection from `PolyBound`, the
  back-injection at height 0, the `liftHeight` adapter, and the
  TowerBound-specific builders (`ofComp`, `ofBoundedRec`,
  `ofExpER`, `ofTowerER`).  Imports `LawvereERPolynomialBound`.
  Estimated 700-900 lines.
- **Create** `GebLean/LawvereKSimTowerBound.lean` — host the
  K^sim-side TowerBound replumbing
  (`kSimPackedBase_towerBound`, `kSimPackedStep_towerBound`),
  the recursive bridge `KMor1.kToER_towerBound_of_level_one`,
  the chain-closing log-vs-tH lemma
  `linearBoundLog_packedStep_le_towerHeight`, and the headline
  theorem `kSimTowerBound_dominates_inline`.
  Imports `LawvereKSimPolynomialBound` and `LawvereERTowerBound`.
  Estimated 600-800 lines.
- **Modify** `GebLean/Utilities/ComputationalComplexity.lean` —
  add `Nat.tower_iter_tower_bound`, the tower-bumped iteration
  lemma generalizing `polynomial_iter_tower_bound`.  Estimated
  150-250 lines added.
- **Modify** `GebLean.lean` — re-export the two new modules.

The split keeps each module focused.  The existing modules
(`LawvereERPolynomialBound`, `LawvereKSimPolynomialBound`)
remain unchanged at the API level; nothing is renamed or
removed.

---

## Task T1: TowerBound type + PolyBound injection (foundation)

**Files:**

- Create: `GebLean/LawvereERTowerBound.lean`
- Modify: `GebLean.lean` (add import).

**Goal:** create the new module with the `TowerBound` structure
definition, the injection `ofPolyBound : PolyBound f → TowerBound f`,
the back-injection `toPolyBound`, and basic infrastructure.

- [ ] **Step T1.1: Create the module skeleton**

Create `GebLean/LawvereERTowerBound.lean` with content:

```lean
import GebLean.LawvereERPolynomialBound
import GebLean.Utilities.Tower

/-!
# Tower bounds on `ERMor1` interpretations

`ERMor1.TowerBound f` carries a tower-of-polynomial bound on
`f.interp`, generalizing `ERMor1.PolyBound`.  The bound shape is
`f.interp ctx ≤ tower towerHeight (coefficient *
(maxCtx ctx + 1)^degree + constant)`.

`PolyBound f` is exactly `TowerBound f` at `towerHeight = 0`
(definitional via `tower_zero`); the `ofPolyBound` and
`toPolyBound` operations are mutual inverses at height 0.

Used by the K^sim_2 ⊆ ER chain-assembly headline theorem
`kSimTowerBound_dominates_inline` (see
`GebLean/LawvereKSimTowerBound.lean`), where the simrec case of
`kToER` produces a term containing `ERMor1.boundedRec` whose
bound argument has tower height 2 (not polynomial).
-/

namespace GebLean

namespace ERMor1

structure TowerBound {n : ℕ} (f : ERMor1 n) where
  towerHeight : ℕ
  degree      : ℕ
  coefficient : ℕ
  constant    : ℕ
  bounds : ∀ ctx,
    f.interp ctx ≤
      GebLean.tower towerHeight
        (coefficient * (maxCtx ctx + 1) ^ degree + constant)

namespace TowerBound

end TowerBound

end ERMor1

end GebLean
```

- [ ] **Step T1.2: Add `ofPolyBound`**

Inside `namespace TowerBound`, add:

```lean
/-- Lift any `PolyBound` to `TowerBound` at height 0.  All fields
preserved; bounds proof goes through because `tower 0 x = x`. -/
def ofPolyBound {n : ℕ} {f : ERMor1 n}
    (pb : PolyBound f) : TowerBound f where
  towerHeight := 0
  degree      := pb.degree
  coefficient := pb.coefficient
  constant    := pb.constant
  bounds := fun ctx => by
    rw [GebLean.tower_zero]
    exact pb.bounds ctx
```

- [ ] **Step T1.3: Add `toPolyBound`**

```lean
/-- Convert a `TowerBound` of height 0 back to a `PolyBound`.
Together with `ofPolyBound` this makes the two types equivalent
at height 0 with no information loss. -/
def toPolyBound {n : ℕ} {f : ERMor1 n}
    (tb : TowerBound f) (h_zero : tb.towerHeight = 0) :
    PolyBound f where
  degree      := tb.degree
  coefficient := tb.coefficient
  constant    := tb.constant
  bounds := fun ctx => by
    have hb := tb.bounds ctx
    rw [h_zero, GebLean.tower_zero] at hb
    exact hb
```

- [ ] **Step T1.4: Add module re-export**

In `GebLean.lean`, locate the existing line that imports
`LawvereERPolynomialBound` and add directly after it:

```lean
import GebLean.LawvereERTowerBound
```

- [ ] **Step T1.5: Run `lake build` + `lake test`**

```bash
lake build && lake test
```

Expected: PASS, no warnings.

- [ ] **Step T1.6: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean GebLean.lean
git commit -m "$(cat <<'EOF'
TowerBound type + PolyBound injection (TowerBound v3 T1)

Adds GebLean/LawvereERTowerBound.lean with the TowerBound
structure (towerHeight, degree, coefficient, constant) and the
mutual conversion ofPolyBound / toPolyBound.  The conversion is
definitional at height 0 via tower_zero (Utilities/Tower.lean:21).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T2: TowerBound.liftHeight adapter

**Files:**

- Modify: `GebLean/LawvereERTowerBound.lean` (insert in
  `namespace TowerBound`).

**Goal:** add an adapter that lifts a TowerBound to a higher
tower height.  Used by `ofComp` to harmonize sibling heights.

- [ ] **Step T2.1: Add `liftHeight`**

```lean
/-- Lift a `TowerBound` to a strictly higher tower height.
Used to harmonize sibling heights in `ofComp` and similar
combinators.  Justified by `tower_mono_left`
(`Utilities/Tower.lean:65`): `tower h_1 X ≤ tower h_2 X` when
`h_1 ≤ h_2`. -/
def liftHeight {n : ℕ} {f : ERMor1 n}
    (tb : TowerBound f) (extra : ℕ) : TowerBound f where
  towerHeight := tb.towerHeight + extra
  degree      := tb.degree
  coefficient := tb.coefficient
  constant    := tb.constant
  bounds := fun ctx => by
    have hb := tb.bounds ctx
    have h_le :
        GebLean.tower tb.towerHeight
          (tb.coefficient * (maxCtx ctx + 1) ^ tb.degree
            + tb.constant)
          ≤
        GebLean.tower (tb.towerHeight + extra)
          (tb.coefficient * (maxCtx ctx + 1) ^ tb.degree
            + tb.constant) :=
      GebLean.tower_mono_left (Nat.le_add_right _ _) _
    exact le_trans hb h_le
```

- [ ] **Step T2.2: Run `lake build`**

```bash
lake build
```

Expected: PASS, no warnings.

- [ ] **Step T2.3: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean
git commit -m "$(cat <<'EOF'
TowerBound.liftHeight adapter (TowerBound v3 T2)

Adds liftHeight, lifting a TowerBound to a strictly higher tower
height via tower_mono_left.  Used downstream by ofComp to
harmonize sibling heights before combining.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T3: TowerBound.ofComp

**Files:**

- Modify: `GebLean/LawvereERTowerBound.lean` (insert in
  `namespace TowerBound`).

**Goal:** add the composition builder.  Heights add (justified
by `tower_comp`), polynomial degree multiplies, coefficients
combine analogously to the existing `PolyBound.ofComp`
(`LawvereERPolynomialBound.lean:180-267`).

The implementation can route through `PolyBound.ofComp` when
all input heights are 0 (via `toPolyBound` round-trip), but the
proof for general heights requires direct algebra.

- [ ] **Step T3.1: State `ofComp`**

```lean
/-- TowerBound for `comp f gs`.  Output tower height is
`tb_f.towerHeight + max h_g`, where `max h_g` is the supremum
of input children's heights.  Polynomial fields combine as in
`PolyBound.ofComp`.  Justified by `tower_comp`
(`Utilities/Tower.lean:51`):
`tower (a + b) x = tower a (tower b x)`. -/
def ofComp {k n : ℕ} {f : ERMor1 k}
    {g : Fin k → ERMor1 n}
    (tb_f : TowerBound f)
    (tb_g : (i : Fin k) → TowerBound (g i)) :
    TowerBound (ERMor1.comp f g) := _
```

The transient `_` is the to-be-filled body.  Build will fail
with "unsolved goals" — use that to inspect the expected type
of the body.

- [ ] **Step T3.2: Implement `ofComp`**

The body mirrors `PolyBound.ofComp`'s structure but accounts for
the tower height.  Define abbreviations for max sibling height,
combined degree, coefficient, constant; provide the bounds
proof using `tb_f.bounds`, `tb_g.bounds`, `tower_mono_right`,
`tower_mono_left` (height monotonicity), and `tower_comp` (for
the height-summing collapse).

Reference structure (mirrors lines 180-267 of
`LawvereERPolynomialBound.lean`):

```lean
def ofComp {k n : ℕ} {f : ERMor1 k}
    {g : Fin k → ERMor1 n}
    (tb_f : TowerBound f)
    (tb_g : (i : Fin k) → TowerBound (g i)) :
    TowerBound (ERMor1.comp f g) :=
  let h_g : ℕ := (Finset.univ : Finset (Fin k)).sup
    (fun i => (tb_g i).towerHeight)
  let c_g : ℕ := (Finset.univ : Finset (Fin k)).sup
    (fun i => (tb_g i).coefficient)
  let d_g : ℕ := (Finset.univ : Finset (Fin k)).sup
    (fun i => (tb_g i).degree)
  let k_g : ℕ := (Finset.univ : Finset (Fin k)).sup
    (fun i => (tb_g i).constant)
  { towerHeight := tb_f.towerHeight + h_g
    degree := tb_f.degree * d_g
    coefficient :=
      tb_f.coefficient * (c_g + k_g + 1) ^ tb_f.degree
    constant := tb_f.constant
    bounds := fun ctx => by
      _ }
```

The bounds proof's algebra:

1. Each `(g i).interp ctx ≤ tower h_g (poly_g)` by
   `(tb_g i).bounds ctx` and `liftHeight`-style raising to the
   max sibling height.
2. So `maxCtx (fun i => (g i).interp ctx) ≤ tower h_g (poly_g)`.
3. `f.interp (fun i => (g i).interp ctx) ≤ tower
   tb_f.towerHeight (poly_f at tower h_g (poly_g))` by
   `tb_f.bounds`.
4. Bound the inner `(tower h_g (poly_g) + 1)^tb_f.degree ≤
   tower h_g ((poly_g)^tb_f.degree + small_const)` (uses
   `tower_succ` algebra and standard `Nat.pow_le_pow` lemmas).
5. So `f.interp(...) ≤ tower tb_f.towerHeight (tower h_g
   (combined_poly) + tb_f.constant)`.
6. Apply `tower_succ` on the outer tower to absorb the
   `+ tb_f.constant` and rewrite to `tower (tb_f.towerHeight +
   h_g) (combined_poly + tb_f.constant)` via `tower_comp`.

If a step requires a Tower lemma not yet in `Utilities/Tower.lean`,
the implementer is empowered to add a small helper theorem
adjacent to `tower_comp`; cap any such helper at ~30 lines.

If the algebra grows beyond ~150 lines for `ofComp`, factor the
proof into intermediate `private theorem`s (similar to
`comp_inner_bound_pointwise` and `comp_maxCtx_inner_le` at
`LawvereERPolynomialBound.lean:56` and `:111`).

- [ ] **Step T3.3: Run `lake build` + `lake test`**

```bash
lake build && lake test
```

Expected: PASS, no warnings.

- [ ] **Step T3.4: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean GebLean/Utilities/Tower.lean
git commit -m "$(cat <<'EOF'
TowerBound.ofComp (TowerBound v3 T3)

Adds the composition builder for TowerBound: heights add per
tower_comp, polynomial fields combine as in PolyBound.ofComp.
Justified by tower_comp (Utilities/Tower.lean:51) and the
existing PolyBound.ofComp algebra.

If new Tower helpers were added, mention them in the body.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T4: TowerBound.ofBoundedRec

**Files:**

- Modify: `GebLean/LawvereERTowerBound.lean` (insert in
  `namespace TowerBound`).

**Goal:** add the bounded-recursion builder.  This is the
load-bearing fix vs. plan v2: `ofBoundedRec` takes a
`TowerBound bound` (not a `PolyBound bound`), so the bound
argument can have arbitrary tower height.

The mathematical content is identical to
`PolyBound.ofBoundedRec` (`LawvereERPolynomialBound.lean:385`):
the `boundedRec` output is bounded by its `bound` argument's
interpretation, so any `TowerBound` on `bound` becomes a
`TowerBound` on `boundedRec base step bound`.

- [ ] **Step T4.1: Add `ofBoundedRec`**

```lean
/-- TowerBound for `boundedRec base step bound`.  Output is
bounded by `bound`'s interp (the existing
`interp_boundedRec_le_bound` lemma), so the resulting
TowerBound has the same fields as the input `tb_bound`.

This is the level-2 chain's load-bearing fix.  Plan v2 attempted
this with `PolyBound bound`, which was uninhabited for
`bound = kSimTowerBound`; with `TowerBound`, the bound can have
arbitrary tower height. -/
def ofBoundedRec {k : ℕ} {base : ERMor1 k}
    {step : ERMor1 (k + 2)} {bound : ERMor1 (k + 1)}
    (tb_bound : TowerBound bound) :
    TowerBound (ERMor1.boundedRec base step bound) where
  towerHeight := tb_bound.towerHeight
  degree      := tb_bound.degree
  coefficient := tb_bound.coefficient
  constant    := tb_bound.constant
  bounds := fun ctx =>
    le_trans
      (ERMor1.interp_boundedRec_le_bound base step bound ctx)
      (tb_bound.bounds ctx)
```

- [ ] **Step T4.2: Run `lake build`**

```bash
lake build
```

Expected: PASS, no warnings.

- [ ] **Step T4.3: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean
git commit -m "$(cat <<'EOF'
TowerBound.ofBoundedRec (TowerBound v3 T4)

Adds the bounded-recursion builder: a TowerBound on bound
becomes a TowerBound on boundedRec base step bound, with the
same fields.  Routes through interp_boundedRec_le_bound.

This is the load-bearing fix vs plan v2 (which attempted
PolyBound on bound, uninhabited when bound = kSimTowerBound).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T5: TowerBound.ofExpER

**Files:**

- Modify: `GebLean/LawvereERTowerBound.lean` (insert in
  `namespace TowerBound`).

**Goal:** add the atomic builder for `ERMor1.expER`, replacing
the deferred `PolyBound.ofExpER` from D.0.A.  `expER.interp ctx
= (ctx 1)^(ctx 0)`, which is `tower 1 (linear in maxCtx)` in
shape.

- [ ] **Step T5.1: State `ofExpER`**

```lean
/-- TowerBound for `ERMor1.expER`.  `expER.interp ctx =
(ctx 1)^(ctx 0)`.  Bounded by `tower 1 (linear in maxCtx)`
because `2^(maxCtx · log_2(maxCtx + 1) + 1) ≥ (ctx 1)^(ctx 0)`
when `ctx 0, ctx 1 ≤ maxCtx`. -/
def ofExpER : TowerBound ERMor1.expER where
  towerHeight := 1
  degree := 1
  coefficient := 1
  constant := 1
  bounds := fun ctx => _
```

The exact constants in `(coefficient, degree, constant)` are
chosen so the proof closes; the implementer may adjust based on
the actual algebra (e.g., `coefficient = 2`, `constant = 0`,
`degree = 2`).

- [ ] **Step T5.2: Prove `ofExpER`**

Strategy:

1. `expER.interp ctx = (ctx 1)^(ctx 0)` (via
   `ERMor1.interp_expER` at `LawvereERArith.lean:29`).
2. `(ctx 1)^(ctx 0) ≤ (maxCtx ctx + 1)^(maxCtx ctx + 1)`
   (since both `ctx 0, ctx 1 ≤ maxCtx ctx`).
3. `(maxCtx ctx + 1)^(maxCtx ctx + 1) ≤ 2^((maxCtx ctx + 1)^2)`
   (since `(maxCtx + 1)^(maxCtx + 1) ≤ 2^((maxCtx + 1) · log_2
   (maxCtx + 2))` and `log_2 (X + 2) ≤ X + 1`).
4. `2^((maxCtx ctx + 1)^2) = tower 1 ((maxCtx ctx + 1)^2)` by
   `tower_succ` (with `tower 0 = id` and `tower 1 X = 2^X`).
5. Match the TowerBound shape: `tower 1 (1 *
   (maxCtx ctx + 1)^2 + 0)` for `coefficient = 1`, `degree = 2`,
   `constant = 0`.

Cap proof at ~50 lines.  If a step requires a `Nat.pow_le_pow_X`
lemma not in mathlib, the implementer may add a small helper
adjacent.

- [ ] **Step T5.3: Run `lake build`**

Expected: PASS.

- [ ] **Step T5.4: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean
git commit -m "$(cat <<'EOF'
TowerBound.ofExpER (TowerBound v3 T5)

Adds atomic TowerBound for ERMor1.expER at tower height 1,
replacing the deferred PolyBound.ofExpER (impossible — expER
is super-polynomial: (ctx 1)^(ctx 0) bounded by 2^((maxCtx +
1)^2) in TowerBound shape).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T6: TowerBound.ofTowerER

**Files:**

- Modify: `GebLean/LawvereERTowerBound.lean` (insert in
  `namespace TowerBound`).

**Goal:** add the atomic builder for `ERMor1.towerER k`,
replacing the deferred `PolyBound.ofTowerER` from D.0.A.
`towerER k.interp ctx = tower k (linear in ctx)` essentially,
so its TowerBound has tower height `k + 1` (or `k`, depending
on the convention).

- [ ] **Step T6.1: State `ofTowerER`**

```lean
/-- TowerBound for `ERMor1.towerER k`.  Built by induction on
`k`: base case is `towerER 0 = proj 0` (linear, height 0); step
case is `towerER (k+1) = comp expER [towerER k, twoN 1]`,
combining the IH (height k) with `expER` (height 1) via
`ofComp` (heights add).  Resulting tower height: `k + 1` or
similar. -/
def ofTowerER : (k : ℕ) → TowerBound (ERMor1.towerER k)
  | 0 => _
  | k + 1 => _
```

- [ ] **Step T6.2: Implement zero case**

`towerER 0 = ERMor1.proj 0` (per `LawvereERBoundComputable.lean:230`).
Build via `ofPolyBound (.ofProj _)`:

```lean
  | 0 => by
      -- towerER 0 = proj 0; height 0, polynomial.
      change TowerBound (ERMor1.proj (k := 1) 0)
      exact ofPolyBound (PolyBound.ofProj 0)
```

If the `change` doesn't elaborate cleanly because of definitional
unfolding, use `unfold ERMor1.towerER`.

- [ ] **Step T6.3: Implement succ case**

`towerER (k+1) = comp expER [towerER k, twoN 1]` (from the
defining `def` at `LawvereERBoundComputable.lean:230`).  Build
via `ofComp` applied to `ofExpER` and the IH plus `ofTwoN`:

```lean
  | k + 1 => by
      change TowerBound (ERMor1.comp ERMor1.expER _)
      apply ofComp
      · exact ofExpER  -- height 1
      · intro i
        match i with
        | ⟨0, _⟩ => exact ofTowerER k  -- IH, height k
        | ⟨1, _⟩ => exact ofPolyBound (.ofTwoN 1)
```

The exact unfolding may differ from the sketch; verify against
`LawvereERBoundComputable.lean`.

- [ ] **Step T6.4: Run `lake build`**

Expected: PASS.  If the height arithmetic in `ofComp` gives
`k + 1` (not `k + 2`) at the step case, the result tower height
matches the shape we expect.

- [ ] **Step T6.5: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean
git commit -m "$(cat <<'EOF'
TowerBound.ofTowerER (TowerBound v3 T6)

Adds atomic TowerBound for ERMor1.towerER k by structural
induction on k.  Base case (k=0) is proj 0 at height 0.  Step
case applies ofComp to ofExpER (height 1) and IH at height k.
Replaces the deferred PolyBound.ofTowerER (impossible —
super-exponential).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T7: Nat.tower_iter_tower_bound

**Files:**

- Modify: `GebLean/Utilities/ComputationalComplexity.lean`
  (insert after the existing `polynomial_iter_tower_bound` at
  line 471).

**Goal:** add the tower-bumped iteration lemma generalizing
`polynomial_iter_tower_bound`.  When the step is bounded by
`tower h_step (poly)`, the j-iterated trace is bounded by
`tower (max h_step h_base + 2) (linear)`.

- [ ] **Step T7.1: State the lemma**

```lean
/-- Generalization of `polynomial_iter_tower_bound` to
tower-bounded step and base.  When `step v x ≤
tower h_step ((max v x + 1) ^ D)` and `v_0 x ≤
tower h_base ((x + 1) ^ D_base)`, the j-iterated trace
satisfies a tower bound of height `max h_step h_base + 2`,
with the polynomial degrees absorbed into the linear inside
via their logs.

When `h_step = h_base = 0`, this reduces to
`polynomial_iter_tower_bound` (output height 2). -/
theorem Nat.tower_iter_tower_bound
    (step : ℕ → ℕ → ℕ) (h_step D : ℕ)
    (h_step_form : ∀ v x, step v x ≤
      GebLean.tower h_step ((max v x + 1) ^ D))
    (v_0 : ℕ → ℕ) (h_base D_base : ℕ)
    (h_base_form : ∀ x, v_0 x ≤
      GebLean.tower h_base ((x + 1) ^ D_base))
    (j x : ℕ) :
    Nat.iterate (fun v => step v x) j (v_0 x) ≤
      GebLean.tower (max h_step h_base + 2)
        ((Nat.log 2 D + Nat.log 2 D_base + 2) * (j + 1) +
         x + 2) := _
```

- [ ] **Step T7.2: Prove the lemma**

Proof outline (mirrors `polynomial_iter_tower_bound` at
`Utilities/ComputationalComplexity.lean:471-557`):

Strategy: induction on `j`, bounding each iteration by lifting
the previous bound through one more application of the step.
The tower-h step input gives a tower-(h+1) intermediate after
one application; iterating preserves height (via `tower_comp`
collapse) but accumulates linear constants.

```lean
theorem Nat.tower_iter_tower_bound
    -- (signature as above) := by
  induction j with
  | zero =>
      simp only [Nat.iterate]
      have h0 : v_0 x ≤
          GebLean.tower h_base ((x + 1) ^ D_base) := h_base_form x
      -- Bound tower h_base ((x+1)^D_base) by
      -- tower (max h_step h_base + 2) (linear in x).
      have h1 : (x + 1) ^ D_base ≤ 2^((x + 1) * Nat.log 2 D_base + 1)
        := _  -- standard log bound
      have h2 : 2^((x + 1) * Nat.log 2 D_base + 1) ≤
          GebLean.tower 1 ((x + 1) * Nat.log 2 D_base + 1)
        := le_refl _  -- tower 1 = 2^_
      -- Lift through tower height to max h_step h_base + 2.
      sorry  -- transient; algebra to be filled in
  | succ j ih =>
      -- Apply step once more on top of ih.
      sorry  -- transient; analogous to polynomial_iter_tower_bound's succ case
```

The algebra is delicate.  Use `mcp__lean-lsp__lean_goal` and
`lean_multi_attempt` to inspect intermediate states.  Cap proof
at ~250 lines; if it grows, factor into smaller lemmas.

If the proof's exact constants don't match the stated bound,
the implementer is empowered to adjust the bound's linear part
(e.g., `(Nat.log 2 D + Nat.log 2 D_base + 4) * (j + 1) +
2 * x + 5`) — provided the headline assembly chain in T15
still closes.

- [ ] **Step T7.3: Run `lake build` + `lake test`**

Expected: PASS, no warnings.

- [ ] **Step T7.4: Commit**

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "$(cat <<'EOF'
Nat.tower_iter_tower_bound (TowerBound v3 T7)

Generalization of polynomial_iter_tower_bound to tower-bounded
step and base.  Output height = max(h_step, h_base) + 2,
matching the existing polynomial_iter_tower_bound behavior at
height 0.  Used by the headline kSimTowerBound_dominates_inline
chain assembly at level 2.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T8: TowerBound.to_iter_step_form

**Files:**

- Modify: `GebLean/LawvereERTowerBound.lean` (insert in
  `namespace TowerBound`).

**Goal:** add the chain adapter generalizing
`PolyBound.to_iter_step_form`
(`LawvereERPolynomialBound.lean:503`) to TowerBound input.

- [ ] **Step T8.1: State the theorem**

```lean
/-- TowerBound analog of `PolyBound.to_iter_step_form`.  Folds
`coefficient * y^degree + constant` (inside the tower) into a
single-power form `y^(degree + log coefficient + log constant
+ 3)` (still inside the tower).  Used to feed
`Nat.tower_iter_tower_bound` from a TowerBound's bounds proof. -/
theorem to_iter_step_form {k : ℕ}
    (f : ERMor1 (k + 2)) (tb : TowerBound f)
    (params : Fin k → ℕ) :
    ∀ v x, f.interp (Fin.cons x (Fin.cons v params)) ≤
      GebLean.tower tb.towerHeight
        ((max v (max x ((Finset.univ : Finset (Fin k)).sup
          params)) + 2) ^
          (tb.degree +
           Nat.log 2 (tb.coefficient + 1) +
           Nat.log 2 (tb.constant + 1) + 3)) := _
```

- [ ] **Step T8.2: Prove the theorem**

Strategy: apply the existing `PolyBound.to_iter_step_form`-style
algebra inside the `tower towerHeight (...)` wrapping.  The
tower function is monotone, so bounding the inside bounds the
whole.

```lean
theorem to_iter_step_form
    -- (signature as above) := by
  intro v x
  have hb := tb.bounds (Fin.cons x (Fin.cons v params))
  -- Apply standard log-shift algebra inside the tower.
  set sp : ℕ := (Finset.univ : Finset (Fin k)).sup params with hsp
  set y : ℕ := max v (max x sp) + 2 with hy
  -- Bound the inside: tb.coefficient * (maxCtx + 1)^tb.degree
  -- + tb.constant ≤ y^(degree + log coef + log const + 3).
  have h_inside : ... := _
  -- Apply tower_mono_right to the outside.
  exact le_trans hb (GebLean.tower_mono_right
    tb.towerHeight h_inside)
```

The algebra mirrors `PolyBound.to_iter_step_form_log` (which
plan v2 D.0.B intended to add) — the sharper variant that uses
`Nat.log 2` of coefficient and constant rather than the raw
fields.  This gives the exponent's logarithmic-in-coefficient
behavior the chain needs.

Cap proof at ~150 lines.

- [ ] **Step T8.3: Run `lake build`**

Expected: PASS.

- [ ] **Step T8.4: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean
git commit -m "$(cat <<'EOF'
TowerBound.to_iter_step_form (TowerBound v3 T8)

TowerBound analog of PolyBound.to_iter_step_form, with the
sharper Nat.log 2-based exponent (subsumes plan v2 D.0.B's
to_iter_step_form_log).  Folds c·y^d + k inside the tower into
y^(d + log c + log k + 3) inside the tower.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T9: TowerBound.log_le_towerHeight

**Files:**

- Modify: `GebLean/LawvereERTowerBound.lean` (insert in
  `namespace TowerBound`).

**Goal:** add the chain adapter generalizing
`PolyBound.log_le_towerHeight` (Poly Task 9) to TowerBound input.

The level-1 chain (`kSimTowerBound_dominates_level_one`)
consumed `PolyBound.log_le_towerHeight` to bound
`Nat.log 2 (coefficient + constant + 1) ≤ 3 ·
f.towerHeight + 1`.  At level 2, the analog must account for
the `tb.towerHeight` field.

- [ ] **Step T9.1: State the theorem**

```lean
/-- TowerBound analog of `PolyBound.log_le_towerHeight`.  Bounds
`Nat.log 2 (tb.coefficient + tb.constant + 1)` by an expression
linear in `tb.towerHeight` plus `f.towerHeight` (the ER term's
intrinsic tower height).  Used downstream by the chain-closing
log-vs-tH lemma in `LawvereKSimTowerBound`. -/
theorem log_le_towerHeight {n : ℕ} (f : ERMor1 n)
    (tb : TowerBound f) :
    Nat.log 2 (tb.coefficient + tb.constant + 1) ≤
      3 * (f.towerHeight + tb.towerHeight) + 1 := _
```

The exact coefficient (`3` vs another constant) and offset
(`+1`) are settled by the proof.

- [ ] **Step T9.2: Prove the theorem**

Strategy: structural induction on `f`'s tower (similar to the
existing `PolyBound.log_le_towerHeight` proof).  The
`tb.towerHeight` field's contribution is added linearly.

If the proof requires `f.towerHeight` to grow at least linearly
in `tb.towerHeight` (which would be expected — a TowerBound at
height `h` requires the underlying `ERMor1`'s towerHeight to be
at least `h`), the implementer may add an auxiliary lemma
`towerHeight_ge_of_towerBound` first.

Cap proof at ~150 lines.

- [ ] **Step T9.3: Run `lake build`**

Expected: PASS.

- [ ] **Step T9.4: Commit**

```bash
git add GebLean/LawvereERTowerBound.lean
git commit -m "$(cat <<'EOF'
TowerBound.log_le_towerHeight (TowerBound v3 T9)

TowerBound analog of PolyBound.log_le_towerHeight, accounting
for the towerHeight field.  Bounds the log of coefficient +
constant by 3 * (f.towerHeight + tb.towerHeight) + 1.  Used by
the chain-closing log-vs-tH lemma in LawvereKSimTowerBound.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T10: kSimPackedBase_towerBound

**Files:**

- Create: `GebLean/LawvereKSimTowerBound.lean`
- Modify: `GebLean.lean` (add re-export).

**Goal:** create the K^sim-side TowerBound module skeleton and
add the first replumbing function: TowerBound version of
`kSimPackedBase_polyBound`
(`LawvereKSimPolynomialBound.lean:738`).

- [ ] **Step T10.1: Create the module skeleton**

```lean
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimER
import GebLean.LawvereKSimPolynomialBound
import GebLean.LawvereERTowerBound
import GebLean.Utilities.ComputationalComplexity
import GebLean.Utilities.KSimSzudzikSimrec

/-!
# K^sim TowerBound replumbing and headline dominance

K^sim-side proofs supporting the TowerBound v3 chain assembly.
Generalizes the existing PolyBound infrastructure in
`LawvereKSimPolynomialBound.lean` to TowerBound input/output,
making the level-2 simrec dominance theorem
`kSimTowerBound_dominates_inline` discharable.

The principal results are:

- `kSimPackedBase_towerBound` /
  `kSimPackedStep_towerBound` — TowerBound versions of the
  packed simrec wrappers.
- `KMor1.kToER_towerBound_of_level_one` — recursive bridge
  producing TowerBound for every level-≤-1 K^sim term's ER
  translation.
- `linearBoundLog_packedStep_le_towerHeight` —
  chain-closing log-vs-tH lemma at the packed step's
  TowerBound.
- `kSimTowerBound_dominates_inline` — Phase IV-B headline
  theorem.

See `docs/plans/2026-05-02-towerbound-architecture-design.md`.
-/

namespace GebLean

end GebLean
```

- [ ] **Step T10.2: Add `kSimPackedBase_towerBound`**

Inside `namespace GebLean`, add (mirrors
`kSimPackedBase_polyBound` at
`LawvereKSimPolynomialBound.lean:738`):

```lean
/-- TowerBound for the packed simrec base.  Takes per-l
TowerBounds on the K^sim children's ER translations and
produces a TowerBound on the packed base ER term.  Output
tower height is the maximum of input heights (the packed-base
is itself a polynomial expression in the children, no
height bump). -/
def kSimPackedBase_towerBound {a k : ℕ}
    (h_ER : Fin (k + 1) → ERMor1 a)
    (tb_h : (l : Fin (k + 1)) → ERMor1.TowerBound (h_ER l)) :
    ERMor1.TowerBound (kSimPackedBase h_ER) := _
```

The body mirrors `kSimPackedBase_polyBound`'s structure,
substituting `ERMor1.PolyBound` with `ERMor1.TowerBound` and
adding height bookkeeping (max sibling height).  The existing
proof uses `ofComp` over the K^sim children's PolyBounds; the
TowerBound version uses `TowerBound.ofComp` (T3) the same way.

If the algebra grows beyond ~150 lines, the implementer may
inline `kSimPackedBase_polyBound`'s body directly with
`TowerBound.ofPolyBound` lifts at each leaf — i.e., when all
input heights are 0 (the legacy case), the TowerBound version
reduces to `TowerBound.ofPolyBound (kSimPackedBase_polyBound
h_ER (fun l => (tb_h l).toPolyBound h_l_zero))` for some
zero-height proof `h_l_zero`.  The general case (non-zero
heights) requires direct algebra.

- [ ] **Step T10.3: Add module re-export**

In `GebLean.lean`, after `import GebLean.LawvereERTowerBound`,
add:

```lean
import GebLean.LawvereKSimTowerBound
```

- [ ] **Step T10.4: Run `lake build` + `lake test`**

Expected: PASS, no warnings.

- [ ] **Step T10.5: Commit**

```bash
git add GebLean/LawvereKSimTowerBound.lean GebLean.lean
git commit -m "$(cat <<'EOF'
kSimPackedBase_towerBound (TowerBound v3 T10)

Creates GebLean/LawvereKSimTowerBound.lean and adds the first
function: kSimPackedBase_towerBound, the TowerBound version of
kSimPackedBase_polyBound (LawvereKSimPolynomialBound.lean:738).
Output tower height is the max of input children's heights
(no height bump from the packed-base ER term itself).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T11: kSimPackedStep_towerBound

**Files:**

- Modify: `GebLean/LawvereKSimTowerBound.lean` (insert after
  T10's content).

**Goal:** add the TowerBound version of
`kSimPackedStep_polyBound`
(`LawvereKSimPolynomialBound.lean:817`).

- [ ] **Step T11.1: Add `kSimPackedStep_towerBound`**

```lean
/-- TowerBound for the packed simrec step.  Takes per-l
TowerBounds on the K^sim children's ER translations and
produces a TowerBound on the packed step ER term.  Analogous
to `kSimPackedBase_towerBound` but for the step. -/
def kSimPackedStep_towerBound {a k : ℕ}
    (g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (tb_g : (l : Fin (k + 1)) → ERMor1.TowerBound (g_ER l)) :
    ERMor1.TowerBound (kSimPackedStep g_ER) := _
```

Same implementation pattern as T10's `kSimPackedBase_towerBound`.

- [ ] **Step T11.2: Run `lake build`**

Expected: PASS.

- [ ] **Step T11.3: Commit**

```bash
git add GebLean/LawvereKSimTowerBound.lean
git commit -m "$(cat <<'EOF'
kSimPackedStep_towerBound (TowerBound v3 T11)

TowerBound version of kSimPackedStep_polyBound.  Output tower
height is the max of input children's heights.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T12: kToER_towerBound_of_level_one (atomic + comp + raise cases)

**Files:**

- Modify: `GebLean/LawvereKSimTowerBound.lean` (insert after T11).

**Goal:** add the recursive bridge for level-≤-1 K^sim terms.
This task covers the atomic, comp, and raise cases; the simrec
case (the meatiest) is split into its own task T13.

- [ ] **Step T12.1: State the function**

```lean
/-- Recursive TowerBound builder for level-≤-1 K^sim
translations.  At level 0 (atomic / comp / raise / no top-level
simrec) produces a height-0 TowerBound.  At top-level simrec of
level-0 children, produces a height-2 TowerBound via the
polynomial-iter-tower chain on the level-0 children's
PolyBounds.

Used by `kSimTowerBound_dominates_inline` (T15) to feed
`kSimPackedBase_towerBound` and `kSimPackedStep_towerBound` for
the headline assembly. -/
def KMor1.kToER_towerBound_of_level_one :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 1) →
    ERMor1.TowerBound (kToER f (Nat.le_succ_of_le h))
  | _, .zero,         _ =>
      ERMor1.TowerBound.ofPolyBound
        (ERMor1.PolyBound.ofZeroN _)
  | _, .succ,         _ =>
      ERMor1.TowerBound.ofPolyBound ERMor1.PolyBound.ofSucc
  | _, .proj _,       _ =>
      ERMor1.TowerBound.ofPolyBound
        (ERMor1.PolyBound.ofProj _)
  | _, .comp f gs,    h => _
  | _, .raise f,      h => _
  | _, .simrec _ _ _, h => _
```

The build will fail with "unsolved goals" on the `_` cases.
This is intentional and serves as a per-case to-do list.

- [ ] **Step T12.2: Fill the comp case**

```lean
  | _, .comp f gs,    h => by
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
      change ERMor1.TowerBound
        (ERMor1.comp (kToER f (Nat.le_succ_of_le hf))
          (fun i => kToER (gs i)
            (Nat.le_succ_of_le (hgs i))))
      apply ERMor1.TowerBound.ofComp
      · exact KMor1.kToER_towerBound_of_level_one f hf
      · intro i
        exact KMor1.kToER_towerBound_of_level_one (gs i) (hgs i)
```

If the `change` doesn't elaborate cleanly, replace with
`unfold kToER` or use a direct `show ... from ...` ascription.

- [ ] **Step T12.3: Fill the raise case**

```lean
  | _, .raise f,      h => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      have hf_one : f.level ≤ 1 := Nat.le_succ_of_le hf
      change ERMor1.TowerBound
        (kToER f (Nat.le_succ_of_le hf_one))
      exact KMor1.kToER_towerBound_of_level_one f hf_one
```

- [ ] **Step T12.4: Stub the simrec case with `_`**

For now, leave the simrec case as `_`:

```lean
  | _, .simrec _ _ _, h => _
```

Note: this leaves a build error that is intentional — T13 fills
it.  Per project policy, no commit is made with `_` in
committed state.  T12 does NOT commit; T13 closes the loop.

- [ ] **Step T12.5: Confirm only one outstanding error**

```bash
lake build 2>&1 | grep -c "unsolved goals"
```

Expected: exactly one (the simrec case).

If more than one, fix the spurious case-fillers before
proceeding to T13.

- [ ] **Step T12.6: NO COMMIT — proceed to T13**

T13 finishes the simrec case and commits T12+T13 together as a
single task ("kToER_towerBound_of_level_one (TowerBound v3
T12+T13)").  This avoids committing a `_`-stubbed declaration.

---

## Task T13: kToER_towerBound_of_level_one (simrec case)

**Files:**

- Modify: `GebLean/LawvereKSimTowerBound.lean` (replace T12's
  `_` in the simrec case).

**Goal:** fill the simrec case of
`KMor1.kToER_towerBound_of_level_one`.  This is the meatiest
case — produces a TowerBound at height 2 via the polynomial-
iter-tower chain on level-0 K^sim children's PolyBounds.

- [ ] **Step T13.1: Replace the simrec case**

The simrec at level 1 has level-0 children (per
`KMor1.level (.simrec h g _) = max (sup h.level) (sup g.level) + 1`).
The `kToER` translation is (from `LawvereKSimER.lean:58-93`):

```text
comp (kSimSzudzikUnpackAt a i.val) (fun j =>
  if j.val = 0 then
    boundedRec (kSimPackedBase h_ER) (kSimPackedStep g_ER)
               (kSimTowerBound h_ER g_ER)
  else proj _)
where h_ER l = kToER (h l) _; g_ER l = kToER (g l) _.
```

So we need a TowerBound on this comp.  Use `TowerBound.ofComp`
on the unpack atom + the per-branch TowerBounds.

```lean
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp => by
      have hh : ∀ j, (h_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at hyp
        have hsup : Finset.univ.sup
            (fun l => (h_fam l).level) ≤ 0 := by
          have := le_trans (le_max_left _ _)
            (Nat.le_of_succ_le_succ hyp)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j))
          hsup
      have hg : ∀ j, (g_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at hyp
        have hsup : Finset.univ.sup
            (fun l => (g_fam l).level) ≤ 0 := by
          have := le_trans (le_max_right _ _)
            (Nat.le_of_succ_le_succ hyp)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j))
          hsup
      have hh_one : ∀ j, (h_fam j).level ≤ 1 := fun j =>
        Nat.le_succ_of_le (hh j)
      have hg_one : ∀ j, (g_fam j).level ≤ 1 := fun j =>
        Nat.le_succ_of_le (hg j)
      -- Build per-l PolyBounds for the level-0 children.
      have pb_h : (l : Fin (k + 1)) →
          ERMor1.PolyBound
            (kToER (h_fam l) (Nat.le_succ_of_le (hh_one l))) :=
        fun l => _  -- T13.2: structural construction
      have pb_g : (l : Fin (k + 1)) →
          ERMor1.PolyBound
            (kToER (g_fam l) (Nat.le_succ_of_le (hg_one l))) :=
        fun l => _  -- T13.2: structural construction
      -- Build the packed PolyBounds via existing infrastructure.
      let pb_packed_base :=
        kSimPackedBase_polyBound _ pb_h
      let pb_packed_step :=
        kSimPackedStep_polyBound _ pb_g
      -- Apply polynomial_iter_tower_bound to bound the iter.
      -- Wrap as TowerBound on the boundedRec (via ofBoundedRec).
      -- Final comp: TowerBound (kSimSzudzikUnpackAt) + per-branch.
      sorry  -- T13.3: chain assembly, fills the simrec case
```

- [ ] **Step T13.2: Fill `pb_h` and `pb_g` (level-0 PolyBounds)**

Each level-0 K^sim child translates to an atomic-or-comp ER
term (no simrec wrapping since level 0 forbids simrec).  Build
the PolyBound by structural recursion on the K^sim term:

```lean
      have pb_h : (l : Fin (k + 1)) →
          ERMor1.PolyBound
            (kToER (h_fam l) (Nat.le_succ_of_le (hh_one l))) :=
        fun l => by
          -- Convert hh_one l ≤ 1 to a level-0 fact, then build
          -- a PolyBound by structural recursion.
          have hh0 := hh l
          -- Level 0 means no simrec at the top.
          induction h_fam l with
          | zero => exact ERMor1.PolyBound.ofZeroN _
          | succ => exact ERMor1.PolyBound.ofSucc
          | proj i => exact ERMor1.PolyBound.ofProj i
          | comp f gs ih_f ih_gs =>
              apply ERMor1.PolyBound.ofComp
              · exact ih_f _
              · intro i
                exact ih_gs i _
          | raise f ih => exact ih _
          | simrec _ _ _ =>
              -- Impossible at level 0.
              exfalso
              unfold KMor1.level at hh0
              omega
```

The `induction` tactic on `h_fam l` may need to match the
specific KMor1 inductive structure; the implementer adjusts as
needed.  An alternative is a separate `private theorem
kToER_polyBound_of_level_zero` helper.

If the inline `induction` doesn't elaborate cleanly, factor
into a separate helper:

```lean
private theorem kToER_polyBound_of_level_zero {a : ℕ}
    (f : KMor1 a) (h : f.level = 0) :
    ERMor1.PolyBound (kToER f (Nat.le_succ_of_le
      (Nat.le_succ_of_le (Nat.le_of_eq h)))) := by
  -- structural recursion as above
  sorry
```

Then use it inline:

```lean
      have pb_h : ... :=
        fun l => kToER_polyBound_of_level_zero
          (h_fam l) (Nat.le_zero.mp (hh l))
```

Cap helper at ~80 lines.

- [ ] **Step T13.3: Fill the chain assembly**

Build the TowerBound on the simrec's translation:

```lean
      -- Adapt pb_packed_step to single-power form via
      -- to_iter_step_form (existing PolyBound version).
      -- Apply polynomial_iter_tower_bound to bound the iter.
      -- The result is tower 2 (linear), which is exactly a
      -- TowerBound at height 2.

      -- Wrap as TowerBound on the boundedRec via ofBoundedRec
      -- with a TowerBound on kSimTowerBound (built via direct
      -- algebra on iterAutoBoundExpr's structure).

      -- Compose with TowerBound (kSimSzudzikUnpackAt) via
      -- ofComp.

      -- Resulting tower height: 2.
      sorry  -- algebra to be filled
```

The exact assembly:

1. Build `tb_kSimTowerBound : TowerBound (kSimTowerBound h_ER
   g_ER)` — this requires either direct construction from
   `iterAutoBoundExpr`'s structure (via `ofComp` and `ofTowerER`,
   `ofSumCtxER`, `ofAddN`, etc.) OR routing through
   `polynomial_iter_tower_bound` applied to the packed
   PolyBounds.  The cleanest is the latter:

   ```lean
   have h_iter_bound :
       ∀ ctx, (kSimTowerBound h_ER g_ER).interp ctx ≤
         GebLean.tower 2 (linear_in_ctx) :=
     polynomial_iter_tower_bound _ _ _ _ _
   -- Wrap as TowerBound at height 2.
   let tb_kSimTowerBound : ERMor1.TowerBound
       (kSimTowerBound h_ER g_ER) := {
     towerHeight := 2
     degree := 1
     coefficient := some_const
     constant := some_const
     bounds := h_iter_bound
   }
   ```

2. Apply `TowerBound.ofBoundedRec` to get TowerBound on the
   boundedRec at height 2.

3. Build TowerBound on `kSimSzudzikUnpackAt a i.val` via
   structural recursion (height 0 — it's atomic-ER).  Use the
   existing D.0.A builders (`ofNatUnpairFst`, `ofNatUnpairSnd`,
   `ofPred`, `ofProj`) lifted via `ofPolyBound`.

4. Apply `TowerBound.ofComp` to combine.  Output height: 0 + 2
   = 2.

If a sub-step in T13.3 cannot close cleanly, the implementer
may factor into private helpers.  Cap total simrec case at
~300 lines.

- [ ] **Step T13.4: Run `lake build` + `lake test`**

Expected: PASS, no warnings, no `sorry`/`admit`.

- [ ] **Step T13.5: Commit T12+T13 together**

```bash
git add GebLean/LawvereKSimTowerBound.lean
git commit -m "$(cat <<'EOF'
kToER_towerBound_of_level_one (TowerBound v3 T12+T13)

Adds the recursive TowerBound builder for level-≤-1 K^sim
translations:
- atomic / comp / raise cases produce height-0 TowerBound (via
  ofPolyBound).
- top-level simrec at level 1 produces height-2 TowerBound via
  the polynomial-iter-tower chain on level-0 children's
  PolyBounds, wrapped via ofBoundedRec and ofComp.

Replaces plan v2's structurally impossible
kToER_polyBound_of_level_one bridge.  Used by
kSimTowerBound_dominates_inline (T15) for headline assembly.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T14: linearBoundLog_packedStep_le_towerHeight

**Files:**

- Modify: `GebLean/LawvereKSimTowerBound.lean` (insert after
  T13's `kToER_towerBound_of_level_one`).

**Goal:** prove the level-2 chain-closing log-vs-tH inequality
at the packed step's TowerBound.  Level-2 analog of
`stepTH_baseTH_dominates_arg`
(`LawvereKSimPolynomialBound.lean:1544+`).

- [ ] **Step T14.1: State the lemma**

```lean
/-- Chain-closing log-vs-tH inequality at the packed step's
TowerBound.  Level-2 analog of A.5.2.2's
`stepTH_baseTH_dominates_arg`. -/
private theorem linearBoundLog_packedStep_le_towerHeight
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1) :
    let h_ER : Fin (k + 1) → ERMor1 a :=
      fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
    let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
      fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
    let tb_g := fun l =>
      KMor1.kToER_towerBound_of_level_one (g_fam l) (h_g l)
    let tb_packed_step :=
      kSimPackedStep_towerBound g_ER tb_g
    Nat.log 2 (tb_packed_step.coefficient +
      tb_packed_step.constant + 1) ≤
    3 * (kSimPackedStep g_ER).towerHeight +
      3 * tb_packed_step.towerHeight + small_const := _
```

The `small_const` is a numeric constant (target ≤ 50)
determined by the proof.  The implementer may use an existential
form (`∃ c, ...`) if a closed value is elusive.

- [ ] **Step T14.2: Prove the lemma**

The proof routes through:

1. The structural formula for `tb_packed_step`'s fields, derived
   from `kSimPackedStep_towerBound`'s implementation (T11).
2. By `KMor1.linearBoundLog_le_towerHeight`
   (`LawvereKSimPolynomialBound.lean:1828`), the per-l children's
   log bound is bounded by `3 · tH(kToER g_l) + 1`.
3. Aggregate over `l` and through `kSimPackedStep_towerBound`'s
   field formulas.
4. Use the audit-fixed inequality `Nat.log 2 (3^E) ≤
   Nat.log 2 (4^E) = 2E` (plan v2's audit finding A1).

Cap proof at ~150 lines.  Use `mcp__lean-lsp__lean_goal` to
inspect intermediate states.  If the algebra requires small
helper lemmas (e.g., `Nat.log 2 (a + b) ≤ ...`), add them
adjacent to the existing `Nat.log 2`-arithmetic helpers in
`LawvereKSimPolynomialBound.lean`.

- [ ] **Step T14.3: Run `lake build`**

Expected: PASS.

- [ ] **Step T14.4: Commit**

```bash
git add GebLean/LawvereKSimTowerBound.lean
git commit -m "$(cat <<'EOF'
linearBoundLog_packedStep_le_towerHeight (TowerBound v3 T14)

Level-2 chain-closing log-vs-tH inequality at the packed step's
TowerBound.  Level-2 analog of A.5.2.2's
stepTH_baseTH_dominates_arg.  Consumes
KMor1.linearBoundLog_le_towerHeight per-l on K^sim children,
aggregated through kSimPackedStep_towerBound's field formulas.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T15: kSimTowerBound_dominates_inline (headline)

**Files:**

- Modify: `GebLean/LawvereKSimTowerBound.lean` (insert after T14).

**Goal:** prove the Phase IV-B headline theorem.  Mirrors
`kSimTowerBound_dominates_level_one`
(`LawvereKSimPolynomialBound.lean:2578-2703`) but routes through
TowerBound-aware infrastructure.

- [ ] **Step T15.1: State the theorem**

```lean
/-- Phase IV-B headline: level-2 simrec dominance via the
polynomial-iteration chain through TowerBound.  The iterated
packed value of `kSimPackedStep` over `kSimPackedBase` is
dominated by `kSimTowerBound`'s closed-form tower at every
iteration counter and parameter context, when both base and
step families consist of level-≤-1 K^sim terms.

Used by `kToER_interp` at level ≤ 2 (kToER plan Task 14).

Mirrors `kSimTowerBound_dominates_level_one` (Task 17b) but
routes through `Nat.tower_iter_tower_bound` and TowerBound
machinery, allowing the level-1 children to themselves be
top-level simrec terms (which have super-polynomial growth and
were the blocker for plan v2). -/
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

- [ ] **Step T15.2: Set up abbreviations and per-l TowerBounds**

```lean
  -- Set abbreviations matching level-1's structure
  -- (LawvereKSimPolynomialBound.lean:2605+).
  set h_ER : Fin (k + 1) → ERMor1 a :=
    fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
    with h_ER_def
  set g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
    fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
    with g_ER_def
  -- Build per-l TowerBounds via the recursive bridge (T13).
  have tb_h : (l : Fin (k + 1)) →
      ERMor1.TowerBound (h_ER l) :=
    fun l => KMor1.kToER_towerBound_of_level_one
      (h_fam l) (h_h l)
  have tb_g : (l : Fin (k + 1)) →
      ERMor1.TowerBound (g_ER l) :=
    fun l => KMor1.kToER_towerBound_of_level_one
      (g_fam l) (h_g l)
  -- Build the packed TowerBounds via T10 / T11.
  let tb_packed_base := kSimPackedBase_towerBound h_ER tb_h
  let tb_packed_step := kSimPackedStep_towerBound g_ER tb_g
```

- [ ] **Step T15.3: Apply `to_iter_step_form` and
  `tower_iter_tower_bound`**

```lean
  -- Convert packed step's TowerBound to single-power form.
  have h_step_form :=
    ERMor1.TowerBound.to_iter_step_form
      (kSimPackedStep g_ER) tb_packed_step params
  -- Convert packed base's TowerBound to single-power form.
  -- (Adapt to_iter_step_form to the one-input shape, or use
  -- a separate helper.)
  have h_base_form := _  -- T15.4
  -- Apply Nat.tower_iter_tower_bound (T7).
  have h_iter_bound :=
    Nat.tower_iter_tower_bound _ _ _ _ _ _ _ _ _
```

Detailed `tower_iter_tower_bound` invocation requires threading
the correct values for `D`, `D_base`, `h_step`, `h_base`,
extracted from `tb_packed_step` and `tb_packed_base`.  The
implementer adjusts based on T7's actual signature.

- [ ] **Step T15.4: Bridge from packed base to one-input
  single-power form**

`tb_packed_base : TowerBound (kSimPackedBase h_ER)` where
`kSimPackedBase h_ER : ERMor1 (a + 1)` has one slot (no
`x`/`v`).  Adapt to a single-power form analogously to
`PolyBound.le_pow_shift_of_polyBound`
(`LawvereERPolynomialBound.lean:402`):

```lean
have h_base_form :
    ∀ ctx, (kSimPackedBase h_ER).interp ctx ≤
      GebLean.tower tb_packed_base.towerHeight
        ((maxCtx ctx + 2) ^
          (tb_packed_base.degree +
           Nat.log 2 (tb_packed_base.coefficient + 1) +
           Nat.log 2 (tb_packed_base.constant + 1) + 3)) := _
```

If a separate helper proves easier, the implementer may add
`ERMor1.TowerBound.to_iter_step_form_one_input` adjacent to T8.
Cap helper at ~80 lines.

- [ ] **Step T15.5: Apply tower-monotonicity bumps**

Mirror the level-1 chain (lines 2655-2703):

```lean
  have h_tower_bump_2_3 :
      GebLean.tower (max h_step h_base + 2)
        (linear_argument)
        ≤ GebLean.tower (max h_step h_base + 3)
            (smaller_linear_argument) :=
    Nat.tower_two_le_tower_three_linear _ _ _
  have h_tower_bump_to_stepTH :
      GebLean.tower (max h_step h_base + 3)
        (smaller_linear_argument)
        ≤ GebLean.tower
            ((kSimPackedStep g_ER).towerHeight + 1)
            (smaller_linear_argument) :=
    GebLean.tower_mono_left _ _
```

- [ ] **Step T15.6: Apply `tower_mono_right` with T14's lemma**

```lean
  have h_arg_le := linearBoundLog_packedStep_le_towerHeight
    h_fam g_fam h_h h_g
  have h_final :
      GebLean.tower
        ((kSimPackedStep g_ER).towerHeight + 1)
        smaller_linear_argument
        ≤ (kSimTowerBound h_ER g_ER).interp
            (Fin.cons j params) := by
    rw [kSimTowerBound_interp]
    rw [ERMor1.interp_sumCtxER]
    apply GebLean.tower_mono_right
    omega  -- or apply h_arg_le explicitly
```

- [ ] **Step T15.7: Combine via `calc`**

```lean
  calc Nat.rec _ _ j
      ≤ tower (max h_step h_base + 2) _ := h_iter_bound
    _ ≤ tower (max h_step h_base + 3) _ := h_tower_bump_2_3
    _ ≤ tower ((kSimPackedStep g_ER).towerHeight + 1) _
        := h_tower_bump_to_stepTH
    _ ≤ (kSimTowerBound h_ER g_ER).interp _
        := h_final
```

- [ ] **Step T15.8: Run `lake build` + `lake test`**

Expected: PASS, no warnings, no `sorry`/`admit`.

- [ ] **Step T15.9: Commit**

```bash
git add GebLean/LawvereKSimTowerBound.lean
git commit -m "$(cat <<'EOF'
kSimTowerBound_dominates_inline headline (TowerBound v3 T15)

Phase IV-B headline theorem: level-2 simrec dominance via the
polynomial-iteration chain through TowerBound.  Public theorem;
consumed by kToER plan Task 14.

Chain assembly:
- per-l TowerBounds via kToER_towerBound_of_level_one (T12+T13).
- packed TowerBounds via kSimPackedBase_towerBound /
  kSimPackedStep_towerBound (T10 / T11).
- to_iter_step_form converts to single-power form (T8).
- Nat.tower_iter_tower_bound bounds the j-iter at tower
  (max + 2) (linear) (T7).
- tower_two_le_tower_three_linear bumps to tower (max + 3).
- tower_mono_left lifts to tower (stepTH + 1).
- tower_mono_right + linearBoundLog_packedStep_le_towerHeight
  (T14) absorbs the linear argument into kSimTowerBound's
  closed form.

Replaces the impossible PolyBound formulation of plan v2.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T16: Tests

**Files:**

- Modify: an existing test file under `test/` or create
  `test/TowerBoundTests.lean`.

**Goal:** add `#guard` and structural tests verifying the
TowerBound API.

- [ ] **Step T16.1: Test PolyBound ↔ TowerBound round-trip**

Add to `test/TowerBoundTests.lean`:

```lean
import GebLean

open GebLean

-- Round-trip: a PolyBound lifted to TowerBound and back equals
-- the original (at field level).
example :
    let pb : ERMor1.PolyBound ERMor1.succ := .ofSucc
    let tb := ERMor1.TowerBound.ofPolyBound pb
    tb.toPolyBound rfl = pb := rfl
```

If `rfl` doesn't close (due to definitional issues with `rfl` on
structures with proofs), use `by ext <;> rfl` or similar.

- [ ] **Step T16.2: Test `ofExpER` at small contexts**

```lean
-- expER at ctx [0, 5] = 5^0 = 1; at ctx [2, 3] = 3^2 = 9.
#guard ERMor1.expER.interp ![0, 5] = 1
#guard ERMor1.expER.interp ![2, 3] = 9
-- Verify the TowerBound bound holds at a small context.
#guard
  let tb := ERMor1.TowerBound.ofExpER
  ERMor1.expER.interp ![2, 3] ≤
    GebLean.tower tb.towerHeight
      (tb.coefficient * (maxCtx ![2, 3] + 1) ^ tb.degree
        + tb.constant)
```

- [ ] **Step T16.3: Test `kToER_towerBound_of_level_one` on
  `addK`**

```lean
-- addK is a level-1 K^sim simrec witness used elsewhere.
-- Build its TowerBound and verify the bound holds at a small
-- context.
example :
    let tb := KMor1.kToER_towerBound_of_level_one
      KMor1.addK (by decide)
    ∀ ctx, (kToER KMor1.addK ...).interp ctx ≤
      GebLean.tower tb.towerHeight ...
    := by
  intro ctx
  exact tb.bounds ctx
```

The exact test depends on `addK`'s definition — adjust as
needed.

- [ ] **Step T16.4: Run `lake test`**

Expected: PASS.

- [ ] **Step T16.5: Commit**

```bash
git add test/TowerBoundTests.lean
git commit -m "$(cat <<'EOF'
TowerBound tests (TowerBound v3 T16)

Adds #guard and structural tests for: PolyBound ↔ TowerBound
round-trip; ofExpER at small contexts; kToER_towerBound_of_level_one
on addK.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T17: Final verification

- [ ] **Step T17.1: Confirm headline is public**

```bash
grep -n "theorem kSimTowerBound_dominates_inline" \
  GebLean/LawvereKSimTowerBound.lean
```

Expected: one match, NOT prefixed with `private`.

- [ ] **Step T17.2: Confirm no sorries / admits**

```bash
grep -rn "sorry\|admit" \
  GebLean/LawvereERTowerBound.lean \
  GebLean/LawvereKSimTowerBound.lean \
  GebLean/Utilities/ComputationalComplexity.lean
```

Expected: zero matches.

- [ ] **Step T17.3: Confirm clean build + test**

```bash
lake build && lake test
```

Expected: PASS, no warnings, all tests pass.

- [ ] **Step T17.4: Confirm GebLean.lean re-exports**

```bash
grep "LawvereERTowerBound\|LawvereKSimTowerBound" GebLean.lean
```

Expected: two matches (one each for the new modules).

- [ ] **Step T17.5: NO COMMIT — verification only**

---

## Estimated effort

| Task | Lines | Notes |
|---|---|---|
| T1: TowerBound + injections | 100 | foundation |
| T2: liftHeight | 30 | adapter |
| T3: ofComp | 250 | algebra-heavy |
| T4: ofBoundedRec | 30 | one-liner via interp_boundedRec_le_bound |
| T5: ofExpER | 80 | log algebra |
| T6: ofTowerER | 60 | recursion |
| T7: tower_iter_tower_bound | 250 | proof-heavy |
| T8: to_iter_step_form | 150 | analog of existing |
| T9: log_le_towerHeight | 150 | analog of existing |
| T10: kSimPackedBase_towerBound | 100 | replumbing |
| T11: kSimPackedStep_towerBound | 100 | replumbing |
| T12+T13: kToER_towerBound_of_level_one | 350 | recursive |
| T14: linearBoundLog_packedStep_le_towerHeight | 150 | log algebra |
| T15: kSimTowerBound_dominates_inline | 250 | chain assembly |
| T16: tests | 80 | |
| T17: verification | 0 | read-only |
| **Total** | **~2130** | |

This exceeds the spec's ~1400-line estimate by ~50%, primarily
because each task includes its own proof body in detail rather
than referring to a sketch.  Per CLAUDE.md's escalation rule:
if any individual task grows beyond 50% of its line estimate,
pause and surface to user.

---

## Self-review checklist

**Spec coverage:**

- ✓ §1 TowerBound type — T1.
- ✓ §2 PolyBound ↔ TowerBound conversion — T1 (injections),
  T2 (liftHeight).
- ✓ §3a ofComp — T3.
- ✓ §3b ofBoundedRec — T4.
- ✓ §3c atomic builders ofExpER / ofTowerER — T5 / T6.
- ✓ §4a Nat.tower_iter_tower_bound — T7.
- ✓ §4b TowerBound chain adapters — T8 / T9.
- ✓ §5 K^sim-side replumbing — T10 / T11.
- ✓ §6 recursive bridge — T12 + T13.
- ✓ §7 headline theorem — T15 (with T14 as supporting lemma).
- ✓ §8 salvage of D.0.A's 10 builders — implicit (PolyBound
  versions stay as-is, lifted via `ofPolyBound` at use sites).

**Per-task build/test checkpoints:** each task except T12 ends
with a `lake build && lake test` checkpoint and a commit.  T12
intentionally does not commit (its `_`-stub for the simrec case
would block the build); T13 closes T12+T13 together.

**Per-task commit subjects ending in `(TowerBound v3 TN)`:**
each task has a commit subject template.

**Critical-path dependencies on landed lemmas:**

- `tower_zero` (`Utilities/Tower.lean:21`) — used in T1
  (definitional injection).
- `tower_mono_left` / `tower_mono_right` / `tower_comp` /
  `self_le_tower` (Utilities/Tower) — used in T2, T3, T15.
- `interp_boundedRec_le_bound`
  (`LawvereER.lean` or wherever) — used in T4.
- `interp_expER` (`LawvereERArith.lean:29`) — used in T5.
- `polynomial_iter_tower_bound`
  (`Utilities/ComputationalComplexity.lean:471`) — used in T13.
- `pow_le_tower_two_with_shift` / `tower_two_le_tower_three_linear`
  (Utilities) — used in T7 / T15.
- `kSimPackedBase_polyBound` / `kSimPackedStep_polyBound` —
  used in T13 (level-0 inner case).
- `KMor1.linearBoundLog_le_towerHeight`
  (`LawvereKSimPolynomialBound.lean:1828`) — used in T14.
- `kSimTowerBound_interp` — used in T15.
- D.0.A's 10 atomic PolyBound builders (`ofZeroN`, `ofPred`,
  etc.) — used in T13 (kSimSzudzikUnpackAt's PolyBound
  construction).

**Type consistency:** `f.level ≤ 1` hypothesis is threaded
consistently via `Nat.le_succ_of_le` and lifted to `f.level ≤ 2`
where required (matching `kToER`'s level cap).  The TowerBound
type's field names (`towerHeight`, `degree`, `coefficient`,
`constant`) match across all builders.

**Placeholder scan:** Steps T3.1, T5.1, T6.1, T7.1, T8.1, T9.1,
T10.2, T11.1, T12.1, T13.1, T14.1, T15.1 contain `_`
underscores marking transient working-tree states.  These are
all explicitly marked transient and are resolved by their own
subsequent sub-steps before the respective task's commit.  No
`_` or `sorry` appears in any committed state.

---

## Out-of-scope deferred work

After this plan completes, Phase IV-B is fully closed.  The
next phase is the kToER theorem layer:

- **kToER Task 14 — `kToER_interp`**: the headline
  interpretation-preservation theorem, consumes
  `kSimTowerBound_dominates_inline`.
- **kToER Task 15 — `kToERN_interp`**: pointwise lift.
- **kToER Task 16 — `kToERFunctor` obj/map fields**.
- **kToER Task 17 — functor laws (`map_id`, `map_comp`)**.
- **kToER Tasks 18-22**: tests, re-export, final
  verification.

Permanently out of scope for this codebase:

- K^sim_d for d ≥ 3.  These leave ER and belong to a separate
  PR-targeted project.

---

## Adversarial review queue

After this plan is committed, run an adversarial review pass
via `superpowers:brainstorming` + `mcp__sequential-thinking__sequentialthinking`
to identify:

- Mathematical errors (wrong tower-height arithmetic,
  unjustified inequalities).
- Placeholder gaps (any `_` or vague step that wasn't expanded).
- Constructor coverage (level-≤-1 K^sim cases I missed).
- Interface drift (TowerBound field names / signatures
  inconsistent across tasks).
- Repeats of plan v1 / v2's mistake (assuming a buildable
  bound without verifying mathematical possibility).
- Underestimated line counts (any task likely to exceed its
  estimate by > 50%).
- Missing prerequisites (Tower lemmas not yet in
  `Utilities/Tower.lean`, etc.).
