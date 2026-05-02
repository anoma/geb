# `kSimTowerBound_dominates_inline` Implementation Plan (v5)

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** discharge the Phase IV-B headline theorem
`kSimTowerBound_dominates_inline` (level-2 K^sim simrec
dominance) by adding four new helpers, each a structural
mirror of an existing level-1 helper with two specific
substitutions.

**Architecture:** the level-1 chain
(`kSimTowerBound_dominates_level_one`,
`LawvereKSimPolynomialBound.lean:2578-2703`) is **already
proven** and exposes the calc-chain pattern.  Plan v5 mirrors
this chain at level 2 by substituting `KMor1.linearBound`
(line 207, Lemma 1.A) for `KMor1.level0Shape.linearBound`
(Lemma 1.B), and `KMor1.linearBoundLog_le_towerHeight` (line
1828, Wong's Prop. 4.6 transcription) for
`kToER_level0_towerHeight_ge_const`.  All other helpers in
the chain are level-agnostic and reused unchanged.

**Foundational reference:** see
`docs/research/2026-05-02-level-2-chain-infrastructure-investigation.md`
(commits `3c34c33a` + `f2428500`) for the complete dependency
catalog, literature mapping, and the rationale for this
plan's structure.  Section "Part 4: Recommended level-2 chain
structure" lists the four new helpers L2-1, L2-3, L2-4, L2-5
that this plan implements.

**Literature trace** (from the investigation; see also
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`):

- **Tourlakis 2018 §0.1.0.34** (E^2 closure under simultaneous
  bounded recursion) — discharged by L2-3 (seqPack bound on
  level-1 trace).
- **Tourlakis 2018 §0.1.0.44** (K^sim_n = E^{n+1} for n ≥ 2;
  K^sim_2 = E^3 = ER) — the equivalence this whole chain
  formalizes.
- **Recursion Class Ch. 4 Prop. 4.7** (n=2 case: iter of
  polynomial step is in E^3 = ER) — discharged by the
  existing `Nat.polynomial_iter_tower_bound` (Module A,
  Poly Task 5; reused unchanged).
- **Wong's Prop. 4.6 exponent-tracking** — discharged at
  level 1 by the existing
  `KMor1.linearBoundLog_le_towerHeight` (line 1828);
  consumed by L2-4.
- **Lemma 1.A** (research doc lines 51-153) — the linear
  bound on K^sim_1; consumed implicitly by L2-3 and L2-4 via
  `KMor1.linearBound`.
- **Claim 3** (research doc, iterated pairing polynomial
  closure) — discharged by `Nat.seqPack_le_seqPackBound`
  (Poly Task 3, reused unchanged in L2-3).

**Tech stack:** Lean 4, mathlib, `lake build` / `lake test`.

**Convention:** every committed task ends in a clean `lake
build` plus `lake test`, with commit subject ending in
`(plan v5 TN)`.  No `sorry` or `admit` in committed state, no
warnings, no banned vocabulary.

**Citation discipline:** per CLAUDE.md, the ER ↔ K^sim_2
transcription requires every new function, definition, or
theorem to carry a literature reference (or in-codebase
lemma reference) in its docstring.  This plan specifies the
required citation for each new helper.

---

## File structure

The plan modifies a single file:

- **Modify** `GebLean/LawvereKSimPolynomialBound.lean`: add
  four private helpers (L2-1, L2-3, L2-4, L2-5) plus the
  public headline theorem `kSimTowerBound_dominates_inline`.
  Insertion point after the existing
  `kSimTowerBound_dominates_level_one` (line 2703).
  Estimated 400-600 lines added.

No new modules are created; no existing infrastructure is
modified.

---

## Task T1 (L2-1): `packed_iteration_matches_simrecVec_level_one`

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (insert
  after `kSimTowerBound_dominates_level_one` at line 2703).

**Goal:** level-1 analog of `packed_iteration_matches_simrecVec`
(`LawvereKSimPolynomialBound.lean:1126`).  Converts the
`Nat.rec` over the level-2 packed step into `Nat.seqPack` of
the simrecVec trace, when children are level ≤ 1.

**Citation:** project-internal trace agreement.  Substitutes
`kToER_interp_level_one` (line 2711) for the level-0 version's
`kToER_interp_level_zero`.  No literature dependency beyond
this.

- [ ] **Step T1.1: Add the lemma**

```lean
/-- Level-1 analog of `packed_iteration_matches_simrecVec`
(line 1126).  Converts the iterated packed value of
`kSimPackedStep` over `kSimPackedBase` to `Nat.seqPack` of
the simrecVec trace, when children are level ≤ 1.

Mirrors the level-0 version exactly with `kToER_interp_level_one`
substituted for `kToER_interp_level_zero`.

Citation: project-internal trace agreement (no literature
beyond `kToER_interp_level_one`'s correctness, which itself
discharges the level-1 case of K^sim ⊆ ER per Tourlakis 2018
§0.1.0.44 and `kSimTowerBound_dominates_level_one`). -/
private theorem packed_iteration_matches_simrecVec_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (params : Fin a → ℕ) (j : ℕ) :
    Nat.rec
      ((kSimPackedBase (fun l => kToER (h_fam l)
        (Nat.le_succ_of_le (h_h l)))).interp params)
      (fun i prev =>
        (kSimPackedStep (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le (h_g l)))).interp
        (Fin.cons i (Fin.cons prev params)))
      j =
      Nat.seqPack
        ((List.finRange (k + 1)).map
          (fun l =>
            KMor1.simrecVec h_fam g_fam params j l)) := by
  induction j with
  | zero =>
      change (kSimPackedBase _).interp params = _
      rw [kSimPackedBase_interp]
      congr 1
      apply List.map_congr_left
      intro l _
      simp only [KMor1.simrecVec_zero]
      exact kToER_interp_level_one (h_fam l) (h_h l) params
  | succ n ih => _
```

The `succ` case mirrors the level-0 version
(line 1156-1209) verbatim — the only structural change is
the level hypothesis on children.

- [ ] **Step T1.2: Fill the `succ` case**

Copy the body of `packed_iteration_matches_simrecVec`'s `succ`
case (line 1156-1209 of `LawvereKSimPolynomialBound.lean`)
and substitute the level hypothesis where it propagates.
The `succ` case does not invoke `kToER_interp_level_zero`; it
uses `ih` and `kSimPackedStep_interp`.  So no level-specific
substitution is needed in the body.

- [ ] **Step T1.3: Run `lake build`**

```bash
lake build
```

Expected: PASS, no warnings.

- [ ] **Step T1.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
packed_iteration_matches_simrecVec_level_one (plan v5 T1)

Level-1 analog of packed_iteration_matches_simrecVec
(line 1126), used by L2-5's chain assembly to convert the
iterated packed value to Nat.seqPack of the simrecVec trace.

Citation: project-internal trace agreement, substituting
kToER_interp_level_one for kToER_interp_level_zero.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T2 (L2-3): `KMor1.simrecVec_seqPack_le_pow_level_one`

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (insert
  after T1's lemma).

**Goal:** level-1 analog of `KMor1.simrecVec_seqPack_le_pow`
(`LawvereKSimPolynomialBound.lean:2509`).  Bounds the
`Nat.seqPack` of a (k+1)-tuple of simrecVec components at
iteration `n ≤ S` by `(CC*S + KK + 2)^E`, with `CC, KK`
extracted from `KMor1.linearBound` rather than
`level0Shape.linearBound`.

**Citation:** Tourlakis 2018 §0.1.0.34 (E^2 closure under
simultaneous bounded recursion) at the level-1 polynomial
degree.  Realized via `Nat.seqPack_le_seqPackBound` (Poly
Task 3, Module A) applied to per-l linear bounds from
`KMor1.linearBound_dominates` (line 507).

The structural change vs. the level-0 version:

- Per-l bound: at level 0, each `simrecVec_l(n) ≤ CC*S + KK`
  via `simrecVec_uniform_linear_bound` (line 2427).  At
  level 1, this becomes the existing
  `KMor1.linearBound_dominates` applied to each child plus a
  per-iteration linear-iteration argument; alternatively,
  build a uniform polynomial bound directly via
  `Nat.polynomial_iter_tower_bound`.  Per the investigation
  (Part 3 item 2), the level-1 chain takes the simpler route:
  derive the per-l linear bound from `KMor1.linearBound`
  (which already captures the linear-bound structure of
  level-1 K^sim per Lemma 1.A) and feed into
  `Nat.seqPack_le_seqPackBound`.
- Outer seqPack: `Nat.seqPack_le_seqPackBound` is reused
  unchanged.

- [ ] **Step T2.1: Add the lemma signature**

```lean
/-- Level-1 analog of `KMor1.simrecVec_seqPack_le_pow`
(line 2509).  Bounds the seqPack of a (k+1)-tuple of
simrecVec components at iteration `n ≤ S` by
`(CC*S + KK + 2)^E` where `CC, KK` are extracted from
`KMor1.linearBound` (level 1) rather than
`level0Shape.linearBound` (level 0).

Citation: Tourlakis 2018 §0.1.0.34 (E^2 closure under
simultaneous bounded recursion); Lemma 1.A (research doc
lines 51-153) for the per-l linear bound.  Realized via
`Nat.seqPack_le_seqPackBound` (Poly Task 3, Module A) and
`KMor1.linearBound_dominates` (line 507). -/
private theorem KMor1.simrecVec_seqPack_le_pow_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (params : Fin a → ℕ)
    (S : ℕ)
    (h_params : ∀ j, params j ≤ S)
    (n : ℕ) (h_n : n ≤ S) :
    let CC :=
      (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).1) 0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).2) 0)
      + 1
    let KK :=
      Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (h_fam l) (h_h l)).2) 0
    Nat.seqPack
      ((List.finRange (k + 1)).map
        (fun l =>
          KMor1.simrecVec h_fam g_fam params n l)) ≤
      (CC * S + KK + 2) ^ (6 * 4 ^ (k + 1)) := _
```

The `_` triggers an "unsolved goals" build error exposing the
expected return type.

- [ ] **Step T2.2: Add a uniform per-l linear bound (auxiliary)**

This is the level-1 analog of `simrecVec_uniform_linear_bound`
(line 2427).  At level 1 the simrec's iter is no longer
linear in `n`, but it IS linear in (S, n) at iteration `n ≤ S`.
The proof routes through `KMor1.linearBound_dominates` plus
the linear-iteration argument inherited from Lemma 1.A's
simrec case.

```lean
/-- Uniform per-l linear bound: at iteration n ≤ S, every
component of `simrecVec h_fam g_fam params n` is bounded by
`CC * S + KK`, where CC, KK aggregate `KMor1.linearBound`
constants over the level-1 children. -/
private theorem KMor1.simrecVec_uniform_linear_bound_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (params : Fin a → ℕ) (S : ℕ)
    (h_params : ∀ j, params j ≤ S) (n : ℕ) (h_n : n ≤ S) :
    let CC := (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).1) 0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).2) 0)
      + 1
    let KK := Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (h_fam l) (h_h l)).2) 0
    ∀ l, KMor1.simrecVec h_fam g_fam params n l ≤
      CC * S + KK := _
```

The proof mirrors `simrecVec_uniform_linear_bound`'s
structure (line 2427+) with `KMor1.linearBound` substituted
for `level0Shape.linearBound` and
`KMor1.linearBound_dominates` substituted for
`level0Shape_interp` + `ConstantOrShiftedProj.linearBound_dominates`.
Cap proof at ~120 lines.

If the substitution doesn't carry exactly because of the
`max_step_c ≤ 1` absorption that level 0 enjoys (line 2278),
the implementer may need to widen the constant accounting in
the conclusion.  In that case, adjust `CC`'s definition to
absorb the level-1 multiplicative coefficient — this still
keeps the bound polynomial in S and n, which is what L2-3
requires.  Surface to user if the adjustment exceeds 30
lines beyond the line-1 mirror.

- [ ] **Step T2.3: Implement the seqPack bound (main lemma body)**

With T2.2 in place, the proof of `simrecVec_seqPack_le_pow_level_one`
mirrors `simrecVec_seqPack_le_pow`'s body (line 2538-2566)
verbatim, substituting `simrecVec_uniform_linear_bound_level_one`
for `simrecVec_uniform_linear_bound`.  Cap at ~30 lines.

- [ ] **Step T2.4: Run `lake build`**

```bash
lake build
```

Expected: PASS.

- [ ] **Step T2.5: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
simrecVec_seqPack_le_pow_level_one (plan v5 T2)

Level-1 analog of simrecVec_seqPack_le_pow (line 2509),
with KMor1.linearBound substituted for level0Shape.linearBound.
Includes a level-1 uniform-linear-bound auxiliary lemma.

Citation: Tourlakis 2018 §0.1.0.34 (E^2 closure under
simultaneous bounded recursion); Lemma 1.A from research doc
(lines 51-153) for the per-l linear bound.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T3 (L2-4): `stepTH_baseTH_dominates_arg_level_one`

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (insert
  after T2's lemmas).

**Goal:** level-1 analog of `stepTH_baseTH_dominates_arg`
(`LawvereKSimPolynomialBound.lean:2226`).  Proves the
chain-closing log-vs-tH inequality at the level-2 simrec's
packed step's bound, with `KMor1.linearBound` substituted
for `level0Shape.linearBound` and
`KMor1.linearBoundLog_le_towerHeight` (line 1828) substituted
for `kToER_level0_towerHeight_ge_const`.

**Citation:** Wong's Prop. 4.6 exponent-tracking (research
doc lines 263-323).  Realized via the existing
`KMor1.linearBoundLog_le_towerHeight` (line 1828, the public
Step-2 deliverable from L.3-5).

- [ ] **Step T3.1: Add the lemma signature**

```lean
/-- Level-1 analog of `stepTH_baseTH_dominates_arg`
(line 2226).  Chain-closing log-vs-tH inequality at the
level-2 simrec's packed step.  Substitutes `KMor1.linearBound`
for `level0Shape.linearBound`, and
`KMor1.linearBoundLog_le_towerHeight` for
`kToER_level0_towerHeight_ge_const`.

Citation: Wong's Prop. 4.6 inductive recipe (research doc
lines 263-323), realized at level 1 via the existing
`KMor1.linearBoundLog_le_towerHeight` (line 1828, Step 2 / L.3-5
deliverable). -/
private theorem stepTH_baseTH_dominates_arg_level_one
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1) :
    let CC := (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).1) 0) +
      2 * (Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (g_fam l) (h_g l)).2) 0)
      + 1
    let KK := Fin.foldr (k + 1) (fun l acc =>
        max acc (KMor1.linearBound (h_fam l) (h_h l)).2) 0
    let E : ℕ := 6 * 4 ^ (k + 1)
    let h_ER : Fin (k + 1) → ERMor1 a :=
      fun l => kToER (h_fam l) (Nat.le_succ_of_le (h_h l))
    let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
      fun l => kToER (g_fam l) (Nat.le_succ_of_le (h_g l))
    Nat.log 2 (CC + 1) +
        Nat.log 2 (KK + Nat.log 2 E + 4) ≤
      (kSimPackedStep g_ER).towerHeight +
        2 * (kSimPackedBase h_ER).towerHeight + 1 := _
```

- [ ] **Step T3.2: Implement the body**

Mirror `stepTH_baseTH_dominates_arg`'s body (line 2258-2421)
with the following substitutions:

1. `(KMor1.level0Shape (g_fam l) (h_g l)).linearBound.X`
   becomes `(KMor1.linearBound (g_fam l) (h_g l)).X`.
2. `(KMor1.level0Shape (h_fam l) (h_h l)).linearBound.X`
   becomes `(KMor1.linearBound (h_fam l) (h_h l)).X`.
3. The two invocations of `kToER_level0_towerHeight_ge_const`
   (lines 2291, 2304) become invocations of
   `KMor1.linearBoundLog_le_towerHeight` (line 1828),
   adjusted for its signature.  Specifically:
   `kToER_level0_towerHeight_ge_const f h` gives
   `(level0Shape f h).linearBound.2 ≤ (kToER f).towerHeight + 1`;
   `KMor1.linearBoundLog_le_towerHeight` gives
   `Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1) ≤
   3 * (kToER f).towerHeight + 1`.  These are different shapes;
   the level-1 proof must pass through the log explicitly.
4. The `h_msc_le : max_step_c ≤ 1` (line 2278) does NOT
   carry to level 1 (level-1 K^sim has multiplicative
   coefficient).  This must be handled by absorbing the
   level-1 coefficient into the log via T3.2.a below.

- [ ] **Step T3.2.a: Adjust the log absorption for level 1**

At level 0, `Nat.log 2 (CC + 1)` was bounded by `SG + 2`
(line 2335) via `h_msc_le`'s constraint.  At level 1, this
absorption requires a different argument.

Specifically: `CC = max_step_c + 2 * max_step_k + 1`.  At
level 1, `max_step_c` is bounded by some value derived from
per-l `linearBound.1`'s.  Per
`KMor1.linearBoundLog_le_towerHeight` per-l, we have for
each l: `Nat.log 2 ((linearBound g_l).1 + (linearBound g_l).2 + 1)
≤ 3 * (kToER g_l).towerHeight + 1`.  Aggregate over l: the
foldr-max of `linearBound.1` and `linearBound.2` are each
bounded by `2^(3 * SG + 1)` (where SG is the sup of children's
towerHeights), so `CC + 1 ≤ 2^(3*SG + 3) + 2 * 2^(3*SG + 3)`,
i.e. `CC + 1 ≤ 4 * 2^(3*SG + 3) = 2^(3*SG + 5)`.  Therefore
`Nat.log 2 (CC + 1) ≤ 3*SG + 5`.

This replaces line 2335's `≤ SG + 2` with `≤ 3*SG + 5` at
level 1.  The propagate inequalities at line 2407
(`stepTH ≥ natPair.tH + 3 + SG`) and line 2415
(`2 * baseTH ≥ SH + natPair.tH + k + 4`) must absorb the
larger constants.  The `omega` close at line 2421 may need
additional slack — verify by hand.

If the `omega` close fails to admit the larger `3*SG + 5`
slack, the level-2 RHS may need to be `(stepTH).tH + 3 *
baseTH.tH + small_const` rather than the level-0
`stepTH + 2*baseTH + 1`.  In that case, the headline (T4)'s
final calc step's `tower_mono_right` argument adjusts
accordingly.

Cap proof at ~200 lines.  If the level-1 absorption requires
more than 30 additional lines beyond a structural mirror,
surface to user.

- [ ] **Step T3.3: Run `lake build`**

Expected: PASS.

- [ ] **Step T3.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
stepTH_baseTH_dominates_arg_level_one (plan v5 T3)

Level-1 analog of stepTH_baseTH_dominates_arg (line 2226),
substituting KMor1.linearBound for level0Shape.linearBound
and KMor1.linearBoundLog_le_towerHeight for
kToER_level0_towerHeight_ge_const.

Citation: Wong's Prop. 4.6 exponent-tracking (research doc
lines 263-323) at level 1.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task T4 (L2-5): `kSimTowerBound_dominates_inline` (headline)

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (insert
  after T3's lemma).

**Goal:** the Phase IV-B headline theorem.  Public.  Mirrors
`kSimTowerBound_dominates_level_one` (line 2578-2703)
calc-by-calc with the level-1 substitutions.

**Citation:** Tourlakis 2018 §0.1.0.34 (E^2 closure) +
Recursion Class Ch. 4 Prop. 4.7 (n=2 case: iter of polynomial
step is in ER, bounded by `tower 2 (linear)` in our
convention).  The chain assembly mirrors the level-1 version
exactly with `KMor1.linearBound` and
`KMor1.linearBoundLog_le_towerHeight` substituted.

- [ ] **Step T4.1: Add the headline statement**

```lean
/-- Phase IV-B headline: level-2 simrec dominance.  Mirrors
`kSimTowerBound_dominates_level_one` (line 2578) at level 2
with `KMor1.linearBound` (Lemma 1.A) substituted for
`KMor1.level0Shape.linearBound` (Lemma 1.B), and
`KMor1.linearBoundLog_le_towerHeight` (line 1828) substituted
for `kToER_level0_towerHeight_ge_const`.

Citation: Tourlakis 2018 §0.1.0.34 + Recursion Class Ch. 4
Prop. 4.7 (n=2 case).  The K^sim_2 ⊆ ER inclusion follows
from this dominance plus `kToER_interp` at level 2 (kToER
plan Task 14, downstream).

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

- [ ] **Step T4.2: Implement the body**

Mirror `kSimTowerBound_dominates_level_one`'s body
(line 2604-2703) with these substitutions:

1. `KMor1.level0Shape (X) (h_X l).linearBound.Y` becomes
   `KMor1.linearBound (X) (h_X l).Y`.
2. `packed_iteration_matches_simrecVec` becomes
   `packed_iteration_matches_simrecVec_level_one` (T1).
3. `KMor1.simrecVec_seqPack_le_pow` becomes
   `KMor1.simrecVec_seqPack_le_pow_level_one` (T2).
4. `stepTH_baseTH_dominates_arg` becomes
   `stepTH_baseTH_dominates_arg_level_one` (T3).
5. The level cast on children's hypotheses changes from
   `(Nat.le_succ_of_le (Nat.le_succ_of_le (h_h l)))` to
   `(Nat.le_succ_of_le (h_h l))` (one fewer succ since
   level ≤ 1, not ≤ 0).

If the final `omega` at line 2703 needs additional slack to
absorb the larger level-1 RHS shape from T3 (per T3.2.a), the
calc chain's last step adjusts accordingly.

The full body is approximately 100 lines (matching the
level-0 body).

- [ ] **Step T4.3: Run `lake build` + `lake test`**

```bash
lake build && lake test
```

Expected: PASS, no warnings, no `sorry`/`admit`.

- [ ] **Step T4.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
kSimTowerBound_dominates_inline (plan v5 T4 / Phase IV-B headline)

The Phase IV-B headline theorem (public).  Level-2 simrec
dominance via the polynomial-iter chain through level-1
K^sim children.  Calc-chain mirrors
kSimTowerBound_dominates_level_one (line 2578-2703) with
KMor1.linearBound substituted for level0Shape.linearBound,
and KMor1.linearBoundLog_le_towerHeight substituted for
kToER_level0_towerHeight_ge_const.

Citation: Tourlakis 2018 §0.1.0.34 (E^2 closure under
simultaneous bounded recursion) + Recursion Class Ch. 4
Prop. 4.7 (n=2 case).  Discharges K^sim_2 ⊆ ER per Tourlakis
2018 §0.1.0.44.

Used by kToER_interp at level ≤ 2 (kToER plan Task 14,
downstream).

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
grep -n "sorry\|admit" GebLean/LawvereKSimPolynomialBound.lean
```

Expected: zero matches.

- [ ] **Step T5.3: Confirm all four new helpers carry literature
  citations in their docstrings**

```bash
grep -nE "level_one|dominates_inline" \
  GebLean/LawvereKSimPolynomialBound.lean | head -20
```

Verify that each new theorem's docstring (the comment block
preceding it) contains either "Citation:" or a specific
literature reference (e.g. "Tourlakis 2018", "Wong",
"Recursion Class").

- [ ] **Step T5.4: Confirm clean build + test**

```bash
lake build && lake test
```

Expected: PASS, no warnings.

- [ ] **Step T5.5: NO COMMIT — verification only**

---

## Estimated effort

- T1 (`packed_iteration_matches_simrecVec_level_one`): ~80
  lines (mirror of line 1126's level-0 version).
- T2 (`simrecVec_seqPack_le_pow_level_one` +
  `simrecVec_uniform_linear_bound_level_one` aux): ~180 lines
  (T2.2 ~120, T2.3 ~30, plus signature).
- T3 (`stepTH_baseTH_dominates_arg_level_one`): ~200 lines
  (mirror of line 2226's body, with the level-1 absorption
  adjustment in T3.2.a).
- T4 (`kSimTowerBound_dominates_inline` headline): ~100
  lines (mirror of line 2578's body).
- T5 (verification): 0 lines.

Total: ~560 lines.  Comparable to the existing level-1 chain
in `LawvereKSimPolynomialBound.lean` (lines 322 + 1126 +
2226-2703 ≈ 600 lines combined).

---

## Self-review checklist

**Spec coverage:** the headline theorem `kSimTowerBound_dominates_inline`
is the spec; T1-T4 implement the four chain pieces, T5 verifies.

**Per-task literature citation:** each task's docstring
specifies a literature reference per the CLAUDE.md citation
discipline:

- T1: project-internal trace agreement (no literature beyond
  `kToER_interp_level_one`).
- T2: Tourlakis 2018 §0.1.0.34 + Lemma 1.A (research doc
  lines 51-153).
- T3: Wong's Prop. 4.6 (research doc lines 263-323).
- T4: Tourlakis 2018 §0.1.0.34 + Recursion Class Ch. 4
  Prop. 4.7 (n=2 case).

**Per-task build/test checkpoints:** each task ends with a
`lake build` checkpoint (T2/T3) or `lake build && lake test`
(T4) and a commit.

**Per-task commit subjects ending in `(plan v5 TN)`:** each
task has a commit subject template.

**Critical-path dependencies on landed lemmas:**

- `KMor1.linearBound` (line 207, public, Poly Task 14) — T2,
  T3, T4.
- `KMor1.linearBound_dominates` (line 507, public) — T2's aux.
- `KMor1.linearBoundLog_le_towerHeight` (line 1828, public,
  Step-2 / L.3-5 deliverable) — T3.
- `kToER_interp_level_one` (line 2711, private) — T1.  Note:
  T1 is inserted after line 2703, so T1 has access to
  `kToER_interp_level_one` defined just below (mutual
  recursion not required; T1 only invokes it in the `zero`
  case).  Actually T1 needs forward reference; verify whether
  Lean accepts this or requires moving `kToER_interp_level_one`
  to before T1.  If forward reference fails, move T1 to
  insert after line 2880 (where
  `kToER_linearBound_dominates_level_one` lives, which itself
  uses `kToER_interp_level_one`).
- `Nat.seqPack_le_seqPackBound` (`Utilities/ComputationalComplexity.lean`,
  Poly Task 3) — T2.
- `Nat.pow_le_tower_two_with_shift` (Utilities) — T4.
- `Nat.tower_two_le_tower_three_linear` (Utilities) — T4.
- `kSimTowerBound_interp`, `interp_sumCtxER`,
  `tower_mono_left`, `tower_mono_right` — T4.
- `kSimPackedStep_towerHeight_ge_succ_k` (line 1376, private)
  — T4 (also T3).

**Dependencies on T1-T4 themselves:** T2 → uses
`simrecVec_uniform_linear_bound_level_one` from T2.2.  T4 →
uses T1, T2, T3.

**Type consistency:** all four new helpers use
`(h_h : ∀ l, (h_fam l).level ≤ 1)` and
`(h_g : ∀ l, (g_fam l).level ≤ 1)` consistently.  The level
cast in `kToER (X) (Nat.le_succ_of_le (h_X l))` lifts to
level ≤ 2 (single `succ`, since the children are level-1, not
level-0).

**Placeholder scan:** transient `_` underscores appear in
T1.1, T2.1, T2.2, T3.1, T4.1 to mark working-tree states
resolved by their own subsequent sub-steps before the
respective task's commit.  No `_` or `sorry` in any committed
state.

**Investigation reference:** every claim in this plan that
existing infrastructure suffices for level-2 reuse traces to
the investigation document
(`docs/research/2026-05-02-level-2-chain-infrastructure-investigation.md`),
specifically Part 4 ("Recommended level-2 chain structure",
lines 643-746).

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

- The four new lemmas' signatures match what the level-1
  chain expects, with the level-1 hypothesis substitutions
  applied consistently.
- T3's level-1 absorption argument (T3.2.a) actually closes
  — the per-l `linearBoundLog_le_towerHeight` aggregation
  through foldr-max into `Nat.log 2 (CC + 1)` is the load-
  bearing step.
- T4's calc chain at the headline closes after the level-1
  absorption widening, with no hidden tower-height arithmetic
  gaps.
- No constructor coverage gaps — the four new lemmas should
  cover all level-1 K^sim shapes (atomic / comp / raise /
  simrec at level 1) implicitly via `KMor1.linearBound` and
  `KMor1.linearBoundLog_le_towerHeight`'s already-proven
  cases.
- No repeats of plan v2 / v3 / v4 mistakes.  Specifically:
  - v2: assumed a recursive PolyBound bridge with a simrec
    case routed through `ofBoundedRec` on `kSimTowerBound`.
    v5 does NOT do this: there is no recursive PolyBound
    bridge; the chain works directly via the closed-form
    seqPack route mirroring level 1.
  - v3: introduced a TowerBound type with a tower-iter-tower
    bound that was mathematically false.  v5 does NOT
    introduce a new bound type; it uses only existing
    `PolyBound` and the closed-form seqPack route.
  - v4: glossed `Nat.rec → Nat.iterate` bridging and tried
    `polynomial_iter_tower_bound` directly.  v5 does NOT
    use `polynomial_iter_tower_bound` directly on the
    iterated packed step; instead it converts to `Nat.seqPack`
    via T1 and bounds the seqPack via T2.

The investigation has eliminated each prior failure mode by
identifying that the level-1 chain's structure carries to
level 2 without these workarounds.
