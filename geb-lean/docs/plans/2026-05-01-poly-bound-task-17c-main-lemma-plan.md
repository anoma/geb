# Phase IV-B Task 17c — main inequality `KMor1.linearBoundLog_le_towerHeight` plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** prove the chain-closing inequality

```text
∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1),
  Nat.log 2 ((KMor1.linearBound f h).1 +
             (KMor1.linearBound f h).2 + 1)
    ≤ 3 * (kToER f (Nat.le_succ_of_le h)).towerHeight + 1
```

(Step 2 of the resumption-prompt-v2 process; the
auxiliary structural lemma at Step 1 has landed.)

**Architecture:** structural recursion on `f : KMor1 a`
at level ≤ 1.  Six cases:
`zero` / `succ` / `proj` (atomic), `comp` (split by
whether the entire comp is level ≤ 0 or level 1),
`raise` (reduces to a level-0 helper), `simrec` (uses
the auxiliary lemma `kToER_simrec_towerHeight_ge_max_child_tH`
from Step 1).  The level-0-or-`raise`-of-level-0 cases
share a private helper lemma factored out as Task L.2.
The `comp`-at-level-1 case carries the load: the
multiplicative max formula
`(p_f.1 · max_c, p_f.1 · max_k + p_f.2)` requires
`Nat.log 2`-arithmetic plus the IH on `f` and on each
child.  The `simrec` case is mostly mechanical: the
linear-bound's `Nat.log 2` is dwarfed by the simrec's
~1100 of structural towerHeight from the
`boundedRec`+`iterAutoBoundExpr` encoding.

**Tech stack:** Lean 4, mathlib (`Nat.log`, `Finset.sup`),
`lake build` / `lake test`.

**Convention:** every committed task ends in a clean
`lake build` plus `lake test`, with commit subject
`(Task 17c L.X)` (L = "[L]inearBoundLog").  Plans for
Phase IV-B Tasks D.3 onward (chain-closing log-vs-tH
applied at the packed step's PolyBound, polynomial-iter
bound, tower-arithmetic closeout, and final stub
discharge) are separate from this plan.

---

## File structure

The plan touches one or two modules:

- **Modify** `GebLean/LawvereKSimPolynomialBound.lean`:
  add a private level-0 helper lemma plus the headline
  `theorem KMor1.linearBoundLog_le_towerHeight` (public,
  not `private`, since downstream Task D.3.2 consumes
  it).  Place after the existing
  `kToER_simrec_towerHeight_ge_max_child_tH` (E.5,
  currently around line 1711).
- **(Optional) Modify** `GebLean/Utilities/ComputationalComplexity.lean`:
  add small `Nat.log 2`-arithmetic helpers if mathlib
  does not already provide them.  Defer to Task L.1 to
  decide based on `lean_local_search` results.

No new module files are created.

`KMor1.linearBound` (`LawvereKSimPolynomialBound.lean`
line 207) reproduces here for reference (post-`0e3bfa66`,
`c2dfc3d6` tightenings):

```text
zero       : (0, 0)
succ       : (1, 1)
proj _     : (1, 0)
comp f gs  : if (comp f gs).level ≤ 0 then
               (level0Shape (comp f gs) hcomp_0).linearBound
             else
               (p_f.1 * max_c, p_f.1 * max_k + p_f.2)
             where p_f = linearBound f, max_c, max_k from
             max-over-fan-out
raise f    : (level0Shape f hf).linearBound  (where
             hf : f.level ≤ 0)
simrec h g : (max_step_c + 2 * max_step_k + 1,
              max_base_const)
```

Existing critical-path dependencies:

- `kToER_level0_towerHeight_ge_const`
  (`LawvereKSimPolynomialBound.lean` line 1031) —
  private; same-file usage works.  Statement:
  `(level0Shape f h).linearBound.2 ≤
   (kToER f (Nat.le_succ_of_le (Nat.le_succ_of_le h))).
   towerHeight + 1` for `h : f.level ≤ 0`.
- `kToER_simrec_towerHeight_ge_max_child_tH`
  (`LawvereKSimPolynomialBound.lean` line 1711, Step 1
  E.5) — private; same-file usage works.
- `Lemma 1.B` shape constraint:
  `level0Shape.linearBound.1 ∈ {0, 1}` (per
  `ConstantOrShiftedProj.linearBound`'s definition).

`ERMor1.towerHeight` recursion: atomic = 0, comp adds
`f.tH + sup g.tH + 1`, bsum + 3, bprod + 4.

---

## Task L.1: `Nat.log 2`-arithmetic helpers

**Files:**

- (Conditional) Modify
  `GebLean/Utilities/ComputationalComplexity.lean`.

The comp-at-level-1 case requires the following
`Nat.log 2` facts.  Some may exist in mathlib; absent
ones go into `Utilities/ComputationalComplexity.lean`
as small private lemmas.

**Mathlib API verified (audit 2026-05-01)** — all five
lemmas below exist with the listed signatures:

```lean
@Nat.log_lt_of_lt_pow :
    ∀ {b x y : ℕ}, y ≠ 0 → y < b ^ x → Nat.log b y < x
@Nat.log_mono_right :
    ∀ {b n m : ℕ}, n ≤ m → Nat.log b n ≤ Nat.log b m
Nat.pow_log_le_self :
    ∀ (b : ℕ) {x : ℕ}, x ≠ 0 → b ^ Nat.log b x ≤ x
@Nat.lt_pow_succ_log_self :
    ∀ {b : ℕ}, 1 < b → ∀ (x : ℕ),
      x < b ^ (Nat.log b x).succ
@Nat.lt_two_pow_self :
    ∀ {n : ℕ}, n < 2 ^ n
```

Plus `Nat.log_monotone : Monotone (Nat.log b)` and
`Nat.log_le_self : Nat.log b x ≤ x`.

The plan therefore needs two project-internal helpers:

**Helper C** — log-of-product upper bound:

```lean
private theorem Nat.log_two_mul_le (a b : ℕ) :
    Nat.log 2 (a * b) ≤
      Nat.log 2 a + Nat.log 2 b + 1
```

Proof: zero cases trivial; otherwise use
`Nat.pow_log_le_self` and `Nat.lt_pow_succ_log_self`
to bound `a · b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2)`,
then close via `Nat.log_lt_of_lt_pow`.

**Helper D** — log-of-sum upper bound by max:

```lean
private theorem Nat.log_two_add_le_max_succ (a b : ℕ) :
    Nat.log 2 (a + b) ≤
      max (Nat.log 2 a) (Nat.log 2 b) + 1
```

Proof: `a + b ≤ 2 · max a b`, so via
`Nat.log_mono_right` get
`Nat.log 2 (a + b) ≤ Nat.log 2 (2 · max a b)`, which
equals `1 + max (Nat.log 2 a) (Nat.log 2 b)` (by
case-split on `a ≤ b` vs `b ≤ a` and monotonicity).

**Helper E** — log commutes with `Finset.sup`:

```lean
private theorem Nat.log_two_finset_sup
    {n : ℕ} (f : Fin (n + 1) → ℕ) :
    Nat.log 2
        ((Finset.univ : Finset (Fin (n + 1))).sup f) =
      (Finset.univ : Finset (Fin (n + 1))).sup
        (fun i => Nat.log 2 (f i))
```

Proof: extract the witness `i₀` achieving sup via
`Finset.exists_mem_eq_sup` (with explicit
`(s := ...) (f := ...)` named arguments — direct
`apply Finset.sup_le` has typeclass resolution issues
verified in audit), then antisymmetry: ≤ via
`Finset.le_sup`, ≥ via `Finset.sup_le` + monotonicity.

If the implementer prefers an inequality form
(`Nat.log 2 (sup f) ≤ sup (Nat.log 2 ∘ f)`), that
suffices for the comp-1 case.  Equality is recommended
for `simp`-friendliness.

- [ ] **Step L.1.1: Confirm none of C, D, E are already
  in mathlib**

Use `mcp__lean-lsp__lean_local_search` to search for
`Nat.log_two_mul`, `Nat.log_two_add`, `Nat.log_finset_sup`,
or related names.  If found, use the existing names; if
not, add the helpers below.

- [ ] **Step L.1.2: Add `Nat.log_two_mul_le` (if needed)**

In `GebLean/Utilities/ComputationalComplexity.lean`,
near other `Nat.log`-arithmetic if any (use
`grep -n "Nat.log" GebLean/Utilities/ComputationalComplexity.lean`
to find a coherent placement).

```lean
/-- Upper bound on `Nat.log 2 (a · b)` in terms of
`Nat.log 2 a + Nat.log 2 b`.  Off by at most 1 due to
the floor-of-log convention. -/
private theorem Nat.log_two_mul_le (a b : ℕ) :
    Nat.log 2 (a * b) ≤
      Nat.log 2 a + Nat.log 2 b + 1 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [Nat.log]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [Nat.log]
  have ha' : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 ha.ne'
  have hb' : 2 ^ Nat.log 2 b ≤ b := Nat.pow_log_le_self 2 hb.ne'
  have ha'' : a < 2 ^ (Nat.log 2 a + 1) :=
    Nat.lt_pow_succ_log_self (by omega) a
  have hb'' : b < 2 ^ (Nat.log 2 b + 1) :=
    Nat.lt_pow_succ_log_self (by omega) b
  -- a · b < 2^(Nat.log 2 a + 1) · 2^(Nat.log 2 b + 1)
  --      = 2^(Nat.log 2 a + Nat.log 2 b + 2)
  have hmul_lt :
      a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    have hlt :
        a * b < 2 ^ (Nat.log 2 a + 1) *
          2 ^ (Nat.log 2 b + 1) :=
      Nat.mul_lt_mul' ha''.le hb'' (by positivity)
    rw [← pow_add] at hlt
    convert hlt using 2; ring
  -- Convert the strict inequality to log_le.
  have hpos : 0 < a * b := Nat.mul_pos ha hb
  have :
      Nat.log 2 (a * b) <
        Nat.log 2 a + Nat.log 2 b + 2 :=
    Nat.log_lt_of_lt_pow hpos.ne' hmul_lt
  omega
```

All three referenced mathlib names
(`Nat.pow_log_le_self`, `Nat.lt_pow_succ_log_self`,
`Nat.log_lt_of_lt_pow`) verified by audit on
2026-05-01.

- [ ] **Step L.1.3: Add `Nat.log_two_add_le_max_succ`
  (if needed)**

```lean
/-- Upper bound on `Nat.log 2 (a + b)` by
`max (Nat.log 2 a) (Nat.log 2 b) + 1`.  Off by at most 1
because `a + b ≤ 2 · max a b`. -/
private theorem Nat.log_two_add_le_max_succ (a b : ℕ) :
    Nat.log 2 (a + b) ≤
      max (Nat.log 2 a) (Nat.log 2 b) + 1 := by
  -- Strategy: bound a + b above by 2 · 2 ^ max (log a) (log b),
  -- then close via Nat.log_lt_of_lt_pow.
  rcases Nat.eq_zero_or_pos (a + b) with hsum0 | hsum0
  · -- a + b = 0 → both a and b are 0
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb; simp [Nat.log]
  -- Bound a + b strictly by 2 ^ (max log + 2).
  have hLT :
      a + b <
        2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 2) := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have hb : b ≠ 0 := by omega
      calc 0 + b = b := by ring
        _ < 2 ^ (Nat.log 2 b + 1) :=
            Nat.lt_pow_succ_log_self (by omega) b
        _ ≤ 2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 2) := by
            have :
                Nat.log 2 b + 1 ≤
                max (Nat.log 2 a) (Nat.log 2 b) + 2 := by
              have := le_max_right (Nat.log 2 a) (Nat.log 2 b)
              omega
            exact Nat.pow_le_pow_right (by omega) this
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      have ha' : a ≠ 0 := by omega
      calc a + 0 = a := by ring
        _ < 2 ^ (Nat.log 2 a + 1) :=
            Nat.lt_pow_succ_log_self (by omega) a
        _ ≤ 2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 2) := by
            have :
                Nat.log 2 a + 1 ≤
                max (Nat.log 2 a) (Nat.log 2 b) + 2 := by
              have := le_max_left (Nat.log 2 a) (Nat.log 2 b)
              omega
            exact Nat.pow_le_pow_right (by omega) this
    -- both a, b > 0
    have ha_lt : a < 2 ^ (Nat.log 2 a + 1) :=
      Nat.lt_pow_succ_log_self (by omega) a
    have hb_lt : b < 2 ^ (Nat.log 2 b + 1) :=
      Nat.lt_pow_succ_log_self (by omega) b
    have ha_le_max :
        2 ^ (Nat.log 2 a + 1) ≤
        2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 1) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.add_le_add_right (le_max_left _ _) 1)
    have hb_le_max :
        2 ^ (Nat.log 2 b + 1) ≤
        2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 1) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.add_le_add_right (le_max_right _ _) 1)
    have :
        a + b <
        2 * 2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 1) := by
      calc a + b
          < 2 ^ (Nat.log 2 a + 1) +
            2 ^ (Nat.log 2 b + 1) := by omega
        _ ≤ 2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 1) +
            2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 1) := by
            omega
        _ = 2 * 2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 1) := by
            ring
    have hpow_eq :
        2 * 2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 1) =
        2 ^ (max (Nat.log 2 a) (Nat.log 2 b) + 2) := by
      rw [show max (Nat.log 2 a) (Nat.log 2 b) + 2 =
            (max (Nat.log 2 a) (Nat.log 2 b) + 1) + 1 from rfl]
      ring
    omega
  -- Apply Nat.log_lt_of_lt_pow.
  exact Nat.log_lt_of_lt_pow (by omega) hLT |>.le.trans
    (by omega)
```

If individual sub-lemmas (`Nat.pow_le_pow_right`) don't
resolve, use Lean MCP `lean_local_search` to find the
exact mathlib name and substitute.  The proof structure
(case-split on a, b zero/positive; bound by powers of 2;
close via `Nat.log_lt_of_lt_pow`) is robust.

- [ ] **Step L.1.3.bis: Add `Nat.log_two_finset_sup`
  helper E**

```lean
/-- `Nat.log 2` commutes with `Finset.sup` over a non-empty
`Finset` of natural numbers (here over `Fin (n + 1)`,
which is non-empty).  Equality form, useful as a `simp`
target. -/
private theorem Nat.log_two_finset_sup
    {n : ℕ} (f : Fin (n + 1) → ℕ) :
    Nat.log 2
        ((Finset.univ : Finset (Fin (n + 1))).sup f) =
      (Finset.univ : Finset (Fin (n + 1))).sup
        (fun i => Nat.log 2 (f i)) := by
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_mem_eq_sup
      (s := (Finset.univ : Finset (Fin (n + 1))))
      (f := f)
      (Finset.univ_nonempty (α := Fin (n + 1)))
  rw [hi₀]
  apply le_antisymm
  · exact Finset.le_sup
      (f := fun i => Nat.log 2 (f i))
      (Finset.mem_univ i₀)
  · apply Finset.sup_le
    intro i _
    apply Nat.log_mono_right
    have :
        f i ≤ (Finset.univ : Finset (Fin (n + 1))).sup f :=
      Finset.le_sup (Finset.mem_univ i)
    rw [hi₀] at this
    exact this
```

The explicit `(s := ...) (f := ...)` named arguments
are required — direct `apply Finset.sup_le` has
typeclass resolution problems due to `OrderBot`'s
unresolved metavariables.  This was verified empirically
during the audit.

If a polymorphic `Finset α` form is needed downstream
(beyond `Fin (n + 1)`), generalize accordingly; for the
comp-1 case the `Fin (n + 1)` form is sufficient.

- [ ] **Step L.1.4: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step L.1.5: Commit (only if helpers were added)**

If new helpers were added in L.1.2/L.1.3:

```bash
git add GebLean/Utilities/ComputationalComplexity.lean
git commit -m "$(cat <<'EOF'
Nat.log 2 arithmetic helpers (Task 17c L.1)

Adds private theorems Nat.log_two_mul_le,
Nat.log_two_add_le_max_succ, and Nat.log_two_finset_sup
to support the comp-at-level-1
case of KMor1.linearBoundLog_le_towerHeight (Task 17c
L.4).  Both are off-by-1 from the tight bound due to the
floor-of-log convention; sufficient for the structural
induction's slack budget.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

If no helpers were needed (mathlib provides everything),
record this in the commit message of L.2 instead.

---

## Task L.2: Level-0 helper `linearBoundLog_le_towerHeight_level_zero`

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after
  `kToER_simrec_towerHeight_ge_max_child_tH`).

The `raise` and `comp at level ≤ 0` cases of the main
lemma both reduce to: for `f : KMor1 a` with
`h : f.level ≤ 0`, prove

```text
Nat.log 2 ((level0Shape f h).linearBound.1 +
           (level0Shape f h).linearBound.2 + 1)
  ≤ 3 * (kToER f (Nat.le_succ_of_le
                   (Nat.le_succ_of_le h))).towerHeight + 1
```

The proof:

1. By `Lemma 1.B`,
   `(level0Shape f h).linearBound.1 ∈ {0, 1}` (case
   analysis on `level0Shape`'s output:
   `const k → (0, k)`, `shifted i k → (1, k)`).
2. By `kToER_level0_towerHeight_ge_const` (A.5.2.1),
   `(level0Shape f h).linearBound.2 ≤
    (kToER f _).towerHeight + 1`.
3. Hence `.1 + .2 + 1 ≤ 1 + ((kToER f).tH + 1) + 1 =
    (kToER f).tH + 3`.
4. `Nat.log 2 ((kToER f).tH + 3) ≤ (kToER f).tH + 1`
   by induction on `(kToER f).tH` (since
   `n + 3 < 2^(n + 2)`).
5. `(kToER f).tH + 1 ≤ 3 · (kToER f).tH + 1` always.

- [ ] **Step L.2.1: State the helper lemma**

```lean
/-- Level-0 specialization of the main inequality,
factored out for use in the `raise` and `comp ≤ 0` cases
of `linearBoundLog_le_towerHeight`.  The level-0
linearBound (via `level0Shape`) is tame
(`.1 ∈ {0, 1}`, `.2 ≤ tH + 1` by A.5.2.1), so its
`Nat.log 2` is bounded by `tH + 1 ≤ 3 · tH + 1`. -/
private theorem linearBoundLog_le_towerHeight_level_zero
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0) :
    Nat.log 2 ((KMor1.level0Shape f h).linearBound.1 +
               (KMor1.level0Shape f h).linearBound.2 + 1)
      ≤ 3 *
        (kToER f
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le h))).towerHeight + 1 := by
  _
```

- [ ] **Step L.2.2: Prove the helper lemma**

```lean
private theorem linearBoundLog_le_towerHeight_level_zero
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 0) :
    Nat.log 2 ((KMor1.level0Shape f h).linearBound.1 +
               (KMor1.level0Shape f h).linearBound.2 + 1)
      ≤ 3 *
        (kToER f
          (Nat.le_succ_of_le
            (Nat.le_succ_of_le h))).towerHeight + 1 := by
  have hbound :=
    kToER_level0_towerHeight_ge_const f h
  -- hbound : (level0Shape f h).linearBound.2 ≤
  --          (kToER f _).towerHeight + 1
  set tH :=
    (kToER f
      (Nat.le_succ_of_le (Nat.le_succ_of_le h))).towerHeight
  -- Case-split on level0Shape's output to bound .1.
  cases hshape : KMor1.level0Shape f h with
  | const k =>
      simp only [ConstantOrShiftedProj.linearBound]
      rw [hshape] at hbound
      simp only [ConstantOrShiftedProj.linearBound] at hbound
      -- .1 = 0, so .1 + .2 + 1 = k + 1.
      -- We have k ≤ tH + 1, so k + 1 ≤ tH + 2.
      have hlog : Nat.log 2 (k + 1) ≤ tH + 1 := by
        apply Nat.log_lt_of_lt_pow
        · omega
        · -- k + 1 < 2^(tH + 2): since k ≤ tH + 1,
          -- k + 1 ≤ tH + 2 < 2^(tH + 2) (induction).
          have : tH + 2 < 2 ^ (tH + 2) := by
            have := Nat.lt_two_pow_self (n := tH + 2)
            omega
          omega
      omega
  | shifted i k =>
      simp only [ConstantOrShiftedProj.linearBound]
      rw [hshape] at hbound
      simp only [ConstantOrShiftedProj.linearBound] at hbound
      -- .1 = 1, so .1 + .2 + 1 = k + 2.
      -- We have k ≤ tH + 1, so k + 2 ≤ tH + 3.
      have hlog : Nat.log 2 (k + 2) ≤ tH + 1 := by
        apply Nat.log_lt_of_lt_pow
        · omega
        · -- k + 2 < 2^(tH + 2)
          have : tH + 3 < 2 ^ (tH + 2) := by
            have := Nat.lt_two_pow_self (n := tH + 2)
            -- tH + 3 ≤ 2^(tH + 2) needs tH ≥ 0 base case
            -- (3 ≤ 4) plus induction.  Try omega + the
            -- mathlib bound; if needed, prove a separate
            -- helper Nat.add_three_lt_two_pow_succ_succ.
            omega
          omega
      omega
```

The Lean MCP tools (`mcp__lean-lsp__lean_goal`,
`mcp__lean-lsp__lean_diagnostic_messages`,
`mcp__lean-lsp__lean_local_search`) are recommended for
finding the exact mathlib names of
`Nat.log_lt_of_lt_pow` / `Nat.lt_two_pow_self`.  If
those don't resolve, alternatives include
`Nat.log_le_self` plus a numeric `decide` for small
`tH`, or splitting into `tH ≤ 1` and `tH ≥ 2` cases.

The numeric arithmetic `tH + 3 < 2^(tH + 2)` may need
its own one-liner helper `n + 3 < 2 ^ (n + 2)` proved
by induction on `n`; introduce that as
`private theorem` adjacent to L.2 if `omega` cannot
close it directly.

- [ ] **Step L.2.3: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step L.2.4: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
Level-0 helper for linearBoundLog_le_towerHeight (Task 17c L.2)

Adds private theorem linearBoundLog_le_towerHeight_level_zero:
the level-0 specialization of the main inequality, used by
the raise and comp-≤-0 cases of the main lemma at L.3.

Proof: case-split on level0Shape (const/shifted) to bound
the linearBound's .1 to 0 or 1; combine with
kToER_level0_towerHeight_ge_const (A.5.2.1) to bound .2;
close via Nat.log 2 (n + 3) ≤ n + 1 arithmetic.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task L.3: Main lemma — atomic + raise + comp-≤-0 cases

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (insert after `linearBoundLog_le_towerHeight_level_zero`).

The main lemma is proved by structural recursion (pattern
matching) on `f : KMor1 a`.  Lean's elaborator requires
all cases to be present before the lemma compiles.  This
task adds the lemma's skeleton with all six cases, fills
the easy ones (atomic + raise + comp-≤-0) using L.2's
helper, and leaves placeholder bodies for the comp-1
and simrec cases (filled in L.4 and L.5 respectively).

**Implementation strategy:** the placeholder cases use
deliberate `_` (underscore) holes, NOT `sorry`, so the
build remains broken and clearly signals which cases
remain.  The full task L.3 commits AFTER L.4 and L.5
fill their cases — i.e., L.3, L.4, L.5 produce a single
combined commit at the end of L.5, NOT three separate
commits.  This is because Lean's pattern-matching
definition cannot be partially compiled.

(Alternative considered: factor each case into a private
helper lemma.  Rejected because case-helpers would need
to take the IH as an explicit parameter, leading to
awkward higher-order signatures.  Inline pattern-matching
is the project's house style for similar lemmas
— see `KMor1.linearBound_dominates`,
`LawvereKSimPolynomialBound.lean:524`.)

**Working procedure for L.3 / L.4 / L.5:** maintain a
single working-tree state with `_` holes; fill cases in
order L.3 → L.4 → L.5; commit ONLY when all six cases
are sorry-/hole-free and `lake build` is clean.

- [ ] **Step L.3.1: Write the main lemma's signature
  and recursive skeleton**

```lean
/-- The chain-closing structural inequality at the heart
of Phase IV-B Task 17c.  For every level-≤-1 K^sim term,
the `Nat.log 2` of `linearBound`'s sum is bounded by
`3 · towerHeight + 1` of its ER translation.  The
constant `3` is project-internal accounting (pinned by
the comp-case algebra under our `towerHeight`
recursion); the shape (additive in `tH`) follows
Wong's Recursion Class Ch. 4 Prop. 4.6 inductive
recipe.  See research doc's "Implication for the level-2
dominance chain" callout for the explicit derivation.

Public; consumed by Phase IV-B Task D.3.2 in the chain
assembly. -/
theorem KMor1.linearBoundLog_le_towerHeight :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1),
      Nat.log 2 ((KMor1.linearBound f h).1 +
                 (KMor1.linearBound f h).2 + 1)
        ≤ 3 *
          (kToER f
            (Nat.le_succ_of_le h)).towerHeight + 1
  | _, .zero,         _ => _
  | _, .succ,         _ => _
  | _, .proj _,       _ => _
  | _, .comp f gs,    h => _
  | _, .raise f,      h => _
  | _, .simrec _ _ _, h => _
```

The build will fail with "unsolved goals" for each
underscore.  This is intentional and serves as a
case-by-case to-do list.

- [ ] **Step L.3.2: Fill the `zero` case**

```lean
  | _, .zero,         _ => by
      simp [KMor1.linearBound, kToER, ERMor1.towerHeight]
      -- linearBound zero = (0, 0), kToER zero = ERMor1.zero,
      -- towerHeight = 0.  LHS = Nat.log 2 1 = 0; RHS = 1.
      -- 0 ≤ 1.
      decide
```

If `decide` doesn't close the residual `0 ≤ 1`, use
`omega` instead.

- [ ] **Step L.3.3: Fill the `succ` case**

```lean
  | _, .succ,         _ => by
      simp [KMor1.linearBound, kToER, ERMor1.towerHeight]
      -- linearBound succ = (1, 1), kToER succ = ERMor1.succ,
      -- towerHeight = 0.  LHS = Nat.log 2 3 = 1; RHS = 1.
      -- 1 ≤ 1.
      decide
```

- [ ] **Step L.3.4: Fill the `proj` case**

```lean
  | _, .proj _,       _ => by
      simp [KMor1.linearBound, kToER, ERMor1.towerHeight]
      -- linearBound (proj _) = (1, 0), kToER (proj _) =
      -- ERMor1.proj _, towerHeight = 0.  LHS = Nat.log 2 2
      -- = 1; RHS = 1.  1 ≤ 1.
      decide
```

If the projection arity threading produces residual
goals, use `omega` and/or `simp`-set helpers.

- [ ] **Step L.3.5: Fill the `raise` case**

```lean
  | _, .raise f,      h => by
      have hf : f.level ≤ 0 := by
        unfold KMor1.level at h; omega
      -- linearBound (raise f) h = (level0Shape f hf).linearBound
      -- kToER (raise f) _ = kToER f _ (definitional)
      simp only [KMor1.linearBound]
      -- The kToER for raise unfolds to kToER f directly.
      change
        Nat.log 2
            ((KMor1.level0Shape f hf).linearBound.1 +
             (KMor1.level0Shape f hf).linearBound.2 + 1) ≤
          _
      have h_kToER_eq :
          (kToER (KMor1.raise f)
            (Nat.le_succ_of_le h)).towerHeight =
          (kToER f
            (Nat.le_succ_of_le
              (Nat.le_succ_of_le hf))).towerHeight := by
        rfl
      rw [h_kToER_eq]
      exact linearBoundLog_le_towerHeight_level_zero f hf
```

If `change` doesn't elaborate cleanly because of the
implicit `Nat.le_succ_of_le` arguments not matching, use
`show` with the exact expected form, or thread through
`set`.

- [ ] **Step L.3.6: Fill the `comp` case (level ≤ 0
  branch only — level-1 deferred to L.4)**

The comp case has a `dite` on whether
`(KMor1.comp f gs).level ≤ 0`.  Set up a `by_cases`
mirror in the proof:

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
      by_cases hcomp_0 : (KMor1.comp f gs).level ≤ 0
      · -- level-0 branch: linearBound delegates to level0Shape
        have h_lb_eq :
            KMor1.linearBound (KMor1.comp f gs) h =
              (KMor1.level0Shape (KMor1.comp f gs) hcomp_0)
                .linearBound := by
          simp only [KMor1.linearBound]
          rw [dif_pos hcomp_0]
        rw [h_lb_eq]
        -- kToER (comp f gs) is structurally a comp; need
        -- kToER_level0_towerHeight_ge_const wrapped to apply
        -- to the comp viewed as a level-0 term.  This is
        -- exactly what linearBoundLog_le_towerHeight_level_zero
        -- handles.
        exact
          linearBoundLog_le_towerHeight_level_zero
            (KMor1.comp f gs) hcomp_0
      · -- level-1 branch: deferred to L.4
        sorry  -- L.4 fills this
```

The `sorry` placeholder will be replaced in L.4.  At
this point of L.3 the build still fails because of
this `sorry` AND the `simrec` underscore.  Continue to
L.5 to complete the lemma.

If `linearBoundLog_le_towerHeight_level_zero` cannot
take a comp term as its argument (its hypothesis is
`f.level ≤ 0`; the comp's level being ≤ 0 satisfies
this), this should work definitionally.  If Lean
complains about implicit arities, thread an explicit
type ascription.

The deferred `sorry` is a transient state that ends at
L.4; do NOT commit while it is present.

---

## Task L.4: Comp-at-level-1 case

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (in the `comp` case's `else` branch — the `sorry`
  inserted in L.3.6).

The comp-at-level-1 case requires sub-case-splitting on
the fan-out arity `b`:

- **`b = 0`** (empty fan-out, e.g. `comp (raise zero)
  Fin.elim0 : KMor1 0` is a reachable level-1 term):
  the foldr-max collapses to `0`, so
  `linearBound (comp f gs) = (p_f.1 · 0, p_f.1 · 0 +
  p_f.2) = (0, p_f.2)`.  The IH on `f` closes
  immediately (no need for the comp-1 algebra).
- **`b ≥ 1`**: the multiplicative-max algebra below.

The b=0 branch must come first because the comp-1
algebra's intermediate bound
`max_c + max_k + 1 ≤ 2 · max_l (lb_sum gs_l + 1)`
is FALSE at b=0 (LHS = 1, RHS = 0 over empty sup).

The inequality LHS at b ≥ 1 is

```text
Nat.log 2 (p_f.1 * max_c + p_f.1 * max_k + p_f.2 + 1)
```

where `p_f = linearBound f hf`, `max_c = sup_l
(linearBound (gs l) (hgs l)).1`, `max_k = sup_l
(linearBound (gs l) (hgs l)).2`.

The RHS is
`3 · ((kToER f).tH + sup_l (kToER (gs l)).tH + 1) + 1 =
3 · (kToER f).tH + 3 · sup_l (kToER (gs l)).tH + 4`.

Proof outline (matches the comp-case algebra from the
research doc's "Implication for the level-2 dominance
chain" callout):

1. `LHS = Nat.log 2 (p_f.1 · (max_c + max_k) + p_f.2 + 1)
   ≤ Nat.log 2 ((p_f.1 + p_f.2 + 1) · (max_c + max_k + 1))`
   (algebra: the latter expands to
   `p_f.1 · max_c + p_f.1 · max_k + p_f.2 · max_c +
    p_f.2 · max_k + p_f.1 + max_c + max_k + p_f.2 + 1`,
   which strictly dominates the former).
2. `Nat.log 2 ((p_f.1 + p_f.2 + 1) · (max_c + max_k + 1))
   ≤ Nat.log 2 (p_f.1 + p_f.2 + 1) +
      Nat.log 2 (max_c + max_k + 1) + 1`
   (by `Nat.log_two_mul_le` from L.1).
3. `Nat.log 2 (p_f.1 + p_f.2 + 1) ≤ 3 · (kToER f).tH + 1`
   (by IH on `f`).
4. `Nat.log 2 (max_c + max_k + 1) ≤ 1 +
    max_l L(gs_l)` where `L(gs_l) = Nat.log 2
    ((linearBound gs_l).1 + (linearBound gs_l).2 + 1)`.
    Specifically:
    - `max_c + max_k + 1 ≤ 2 · max_l ((lb gs_l).1 +
      (lb gs_l).2 + 1)` (since each summand ≤ max-of-sums
      via algebra; and `max_l A_l ≤ max_l (A_l + B_l)`).
    - Hence `Nat.log 2 (max_c + max_k + 1) ≤
      Nat.log 2 (2 · max_l ...) = 1 + max_l L(gs_l)`.
5. By IH on each `gs_l`:
   `L(gs_l) ≤ 3 · (kToER (gs l)).tH + 1`.
6. Combining:
   `LHS ≤ (3 · (kToER f).tH + 1) +
   (1 + max_l (3 · (kToER (gs l)).tH + 1)) + 1 =
   3 · (kToER f).tH + 3 · sup_l (kToER (gs l)).tH + 4`.
7. RHS =
   `3 · (kToER f).tH + 3 · sup_l (kToER (gs l)).tH + 4`.
   Equal — closes with one bit of slack absorbed by the
   per-`comp` increment in `tH`.

- [ ] **Step L.4.0: Add the b=0 sub-case-split**

In the `· -- level-1 branch` block from L.3.6, before
the multiplicative-max algebra, sub-case-split on
`b = 0` vs `b ≥ 1`:

```lean
        -- level-1 branch: split on fan-out arity.
        -- (b is the arity of `gs : Fin b → KMor1 a`,
        -- inferred from the `comp` constructor's type.)
        rcases Nat.eq_zero_or_pos b with hb0 | hb_pos
        · -- b = 0: empty fan-out, linearBound is (0, p_f.2).
          subst hb0
          have h_lb_eq :
              KMor1.linearBound (KMor1.comp f gs) h =
                (0, (KMor1.linearBound f hf).2) := by
            simp only [KMor1.linearBound]
            rw [dif_neg hcomp_0]
            simp
            -- max_c, max_k both fold over Fin 0; both = 0
            rfl
          rw [h_lb_eq]
          -- LHS = Nat.log 2 (0 + p_f.2 + 1) =
          --       Nat.log 2 (p_f.2 + 1)
          -- ≤ Nat.log 2 (p_f.1 + p_f.2 + 1) (monotone)
          -- ≤ 3 · (kToER f).tH + 1 (IH on f)
          -- ≤ 3 · ((kToER f).tH + 1) + 1 (RHS at b=0).
          have IH_f :=
            KMor1.linearBoundLog_le_towerHeight f hf
          have h_kToER_tH :
              (kToER (KMor1.comp f (gs : Fin 0 → _))
                (Nat.le_succ_of_le h)).towerHeight =
                (kToER f
                  (Nat.le_succ_of_le hf)).towerHeight + 1 := by
            simp only [kToER, ERMor1.towerHeight]
            -- Finset.univ.sup over Fin 0 = 0
            simp
          rw [h_kToER_tH]
          have hmono : Nat.log 2
              (0 + (KMor1.linearBound f hf).2 + 1) ≤
            Nat.log 2
              ((KMor1.linearBound f hf).1 +
               (KMor1.linearBound f hf).2 + 1) := by
            apply Nat.log_mono_right; omega
          omega
        · -- b ≥ 1: multiplicative-max algebra below.
          (continued in L.4.1)
```

If the `subst hb0` produces an unworkable goal because
of `gs : Fin b` with `b` not yet unified to `0`, use
`obtain rfl := Nat.eq_zero_of_le_zero (le_of_eq hb0)`
or rewrite `b` to `0` via `cases b` instead of `rcases`.
The implementer is empowered to adjust this skeleton.

If `(comp f gs).level ≤ 0` is needed at b=0 to dispatch
the dite (because `level (comp f Fin.elim0) = level f`,
and if `f.level = 0` then the comp is level 0 — which
went to the dite_pos branch already at L.3.6), then b=0
combined with `level f ≥ 1` is the ONLY way to enter
this branch.  Hence inside the b=0 branch we have
`level f = 1` (from `hf : f.level ≤ 1` plus
`(comp f gs).level = max (level f) 0 = level f`, and
`hcomp_0 : ¬ level (comp f gs) ≤ 0` rules out
`level f = 0`).  This means `Nat.log 2 (lb f).1 ≥ 1`
implicitly, but we don't need this fact — the IH
suffices.

- [ ] **Step L.4.1: Replace the `sorry` in the
  comp-1 branch (b ≥ 1 sub-case)**

After the b=0 branch above, continue with the
multiplicative-max algebra:

```lean
        -- level-1 branch: multiplicative max formula
        have h_lb_eq :
            KMor1.linearBound (KMor1.comp f gs) h =
              (let p_f := KMor1.linearBound f hf
               let max_c := Fin.foldr _ (fun i acc =>
                 max acc
                   (KMor1.linearBound (gs i) (hgs i)).1) 0
               let max_k := Fin.foldr _ (fun i acc =>
                 max acc
                   (KMor1.linearBound (gs i) (hgs i)).2) 0
               (p_f.1 * max_c, p_f.1 * max_k + p_f.2)) := by
          simp only [KMor1.linearBound]
          rw [dif_neg hcomp_0]
        rw [h_lb_eq]
        simp only []
        -- IH on f and on each gs_l.
        have IH_f := KMor1.linearBoundLog_le_towerHeight f hf
        have IH_gs := fun l =>
          KMor1.linearBoundLog_le_towerHeight (gs l) (hgs l)
        -- (kToER (comp f gs)).towerHeight =
        --   (kToER f).tH + sup_l (kToER (gs l)).tH + 1
        have h_kToER_tH :
            (kToER (KMor1.comp f gs)
              (Nat.le_succ_of_le h)).towerHeight =
              (kToER f
                (Nat.le_succ_of_le hf)).towerHeight +
              (Finset.univ : Finset (Fin _)).sup
                (fun l =>
                  (kToER (gs l)
                    (Nat.le_succ_of_le (hgs l))).towerHeight) +
              1 := by
          simp only [kToER, ERMor1.towerHeight]
        rw [h_kToER_tH]
        -- Set abbreviations for the proof.
        set p_f := KMor1.linearBound f hf with hp_f
        set max_c := Fin.foldr _ (fun i acc =>
          max acc (KMor1.linearBound (gs i) (hgs i)).1) 0
          with hmax_c
        set max_k := Fin.foldr _ (fun i acc =>
          max acc (KMor1.linearBound (gs i) (hgs i)).2) 0
          with hmax_k
        set tH_f :=
          (kToER f (Nat.le_succ_of_le hf)).towerHeight
          with htH_f
        set sup_tH_gs :=
          (Finset.univ : Finset (Fin _)).sup
            (fun l =>
              (kToER (gs l)
                (Nat.le_succ_of_le (hgs l))).towerHeight)
          with hsup_tH_gs
        -- Step (1)+(2): LHS ≤ Nat.log 2 (p_f.1 + p_f.2 + 1)
        --                    + Nat.log 2 (max_c + max_k + 1) + 1.
        have hstep12 :
            Nat.log 2 (p_f.1 * max_c + (p_f.1 * max_k +
              p_f.2) + 1) ≤
            Nat.log 2 (p_f.1 + p_f.2 + 1) +
              Nat.log 2 (max_c + max_k + 1) + 1 := by
          have hexpand :
              p_f.1 * max_c + (p_f.1 * max_k + p_f.2) + 1 ≤
              (p_f.1 + p_f.2 + 1) * (max_c + max_k + 1) := by
            ring_nf
            -- Expand RHS: p_f.1·max_c + p_f.1·max_k + p_f.2·max_c
            --   + p_f.2·max_k + p_f.1 + max_c + max_k + p_f.2 + 1.
            -- This ≥ LHS (which is p_f.1·max_c + p_f.1·max_k
            --   + p_f.2 + 1).
            nlinarith [Nat.zero_le p_f.2, Nat.zero_le max_c,
                       Nat.zero_le max_k, Nat.zero_le p_f.1]
          have hlog_mono :
              Nat.log 2 (p_f.1 * max_c + (p_f.1 * max_k +
                p_f.2) + 1) ≤
              Nat.log 2 ((p_f.1 + p_f.2 + 1) *
                (max_c + max_k + 1)) :=
            Nat.log_mono_right hexpand
          have hlog_mul := Nat.log_two_mul_le
            (p_f.1 + p_f.2 + 1) (max_c + max_k + 1)
          omega
        -- Step (4): bound max_c + max_k + 1.
        have hsum_le_max :
            max_c + max_k + 1 ≤ 2 *
              ((Finset.univ : Finset (Fin _)).sup
                (fun l =>
                  (KMor1.linearBound (gs l) (hgs l)).1 +
                  (KMor1.linearBound (gs l) (hgs l)).2 +
                  1)) := by
          -- max_c ≤ max_l ((lb gs_l).1 + (lb gs_l).2 + 1)
          -- max_k ≤ max_l ((lb gs_l).1 + (lb gs_l).2 + 1)
          -- Sum ≤ 2 · max.  The +1 absorbs the foldr's
          -- 0 base.
          sorry
        -- Step (5)+(6): assemble via IH on f and each gs_l.
        sorry
```

The two remaining `sorry`s in this step are the
core arithmetic.  Fill in L.4.2 and L.4.3.

- [ ] **Step L.4.2: Fill the `hsum_le_max` `sorry`**

The bound
`max_c + max_k + 1 ≤
 2 · max_l ((lb gs_l).1 + (lb gs_l).2 + 1)`
requires two sub-bounds:

- `max_c ≤ max_l (lb_sum gs_l + 1)`
  where `lb_sum gs_l = (lb gs_l).1 + (lb gs_l).2`
- `max_k ≤ max_l (lb_sum gs_l + 1)`

Use `Fin.foldr_max_ge` (already in
`LawvereKSimPolynomialBound.lean`) to extract per-l
bounds and then sum.

Replace `sorry` with:

```lean
          -- Per-l bounds via Fin.foldr_max_ge.
          have hmax_c_le :
              max_c ≤
                (Finset.univ : Finset (Fin _)).sup
                  (fun l =>
                    (KMor1.linearBound (gs l) (hgs l)).1 +
                    (KMor1.linearBound (gs l) (hgs l)).2 +
                    1) := by
            -- (linearBound (gs l) (hgs l)).1 ≤ max_c by
            -- Fin.foldr_max_ge.
            -- And (linearBound _).1 ≤ (.1 + .2 + 1) trivially.
            -- Combined: max_c ≤ max_l (.1 + .2 + 1).
            sorry
          have hmax_k_le :
              max_k ≤
                (Finset.univ : Finset (Fin _)).sup
                  (fun l =>
                    (KMor1.linearBound (gs l) (hgs l)).1 +
                    (KMor1.linearBound (gs l) (hgs l)).2 +
                    1) := by
            sorry
          omega
```

Each inner `sorry` is one `Finset.sup_le` plus
arithmetic.  Helper structure:

```lean
          apply Fin.foldr_max_le
          intro j
          calc (KMor1.linearBound (gs j) (hgs j)).1
              ≤ (KMor1.linearBound (gs j) (hgs j)).1 +
                (KMor1.linearBound (gs j) (hgs j)).2 +
                1 := by omega
            _ ≤ Finset.univ.sup _ :=
                Finset.le_sup (Finset.mem_univ j)
```

(`Fin.foldr_max_le` was added during E.5's
implementation per the file's existing helpers.  Verify
its existence at line ~1530 of the file via
`grep`.)

- [ ] **Step L.4.3: Fill the final assembly `sorry`**

After `hsum_le_max`, complete the arithmetic chain:

```lean
        -- IH_gs maximized over l.
        have hIH_gs_max :
            (Finset.univ : Finset (Fin _)).sup
              (fun l =>
                Nat.log 2
                  ((KMor1.linearBound (gs l) (hgs l)).1 +
                   (KMor1.linearBound (gs l) (hgs l)).2 +
                   1)) ≤
              3 * sup_tH_gs + 1 := by
          apply Finset.sup_le
          intro l _
          have := IH_gs l
          calc _
              ≤ 3 *
                  (kToER (gs l)
                    (Nat.le_succ_of_le (hgs l))).towerHeight
                + 1 := this
            _ ≤ 3 * sup_tH_gs + 1 := by
                have :
                    (kToER (gs l)
                      (Nat.le_succ_of_le (hgs l))).towerHeight ≤
                    sup_tH_gs :=
                  Finset.le_sup (Finset.mem_univ _)
                omega
        -- Combine: Nat.log 2 (max_c + max_k + 1) ≤
        --   1 + max_l L(gs_l) ≤ 1 + (3 sup + 1) =
        --   3 sup + 2.
        have hlog_max_le :
            Nat.log 2 (max_c + max_k + 1) ≤
              3 * sup_tH_gs + 2 := by
          have hlog_mono :=
            Nat.log_mono_right hsum_le_max
          have hlog_two_mul :
              Nat.log 2 (2 *
                ((Finset.univ : Finset (Fin _)).sup _)) ≤
              1 + Nat.log 2
                ((Finset.univ : Finset (Fin _)).sup _) := by
            -- Nat.log 2 (2 · n) ≤ 1 + Nat.log 2 n
            sorry  -- mathlib: Nat.log_mul or compute directly
          have hlog_sup_le_max :
              Nat.log 2
                ((Finset.univ : Finset (Fin _)).sup
                  (fun l =>
                    (KMor1.linearBound (gs l) (hgs l)).1 +
                    (KMor1.linearBound (gs l) (hgs l)).2 +
                    1)) ≤
                (Finset.univ : Finset (Fin _)).sup
                  (fun l =>
                    Nat.log 2
                      ((KMor1.linearBound (gs l) (hgs l)).1 +
                       (KMor1.linearBound (gs l) (hgs l)).2 +
                       1)) := by
            -- Nat.log 2 commutes with sup (monotone).
            sorry  -- factor a small helper if not in mathlib
          omega
        -- Close: LHS ≤ Nat.log 2 (p_f.1+p_f.2+1) +
        --              Nat.log 2 (max_c+max_k+1) + 1
        --        ≤ (3 tH_f + 1) + (3 sup + 2) + 1
        --        = 3 tH_f + 3 sup + 4.
        omega
```

The two further `sorry`s above are small `Nat.log` /
`Finset.sup` arithmetic; resolve via mathlib search +
project-internal helpers in L.1 (or inline if simple
enough).

If by this point the proof has accumulated more than
~3 small sub-lemmas, it may be worth extracting them
to L.1 and re-running the search to ensure mathlib
coverage.

**KEY ESCALATION TRIGGER:** if the comp-1 algebra
proves harder than the sketch suggests (e.g. the
`Nat.log 2`-arithmetic helpers don't compose cleanly
or `omega` can't bridge the gap), the implementer is
empowered to introduce additional small helpers.  Cap
the comp-1 implementation at ~150 lines; if it grows
beyond that, escalate as DONE_WITH_CONCERNS or BLOCKED.

---

## Task L.5: Simrec case

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean`
  (replace the underscore `_` for the `simrec` case
  in the lemma's pattern match).

The simrec case is mostly mechanical: the linear-bound
fields are
`(max_step_c + 2 · max_step_k + 1, max_base_const)`
where the maxes are over the `g_fam` / `h_fam` children's
`level0Shape.linearBound` constants.  The
`simrec`'s towerHeight is huge (~ 1117 for `addK`)
because of the boundedRec + iterAutoBoundExpr encoding,
which is what the auxiliary lemma E.5
(`kToER_simrec_towerHeight_ge_max_child_tH`) makes
explicit.

Proof outline:

1. The simrec linearBound fields satisfy `.1 ≤ 2 ·
   max_step_k + max_step_c + 1` (definitionally) and
   `.2 = max_base_const`.  Each `_step_*` is a
   level0Shape constant for some `g_fam l`; each
   `_base_const` is a level0Shape constant for some
   `h_fam l`.
2. By A.5.2.1 applied per-l: `(level0Shape (g_fam l)).
   linearBound.{1,2} ≤ (kToER (g_fam l)).tH + 1` (and
   the `.1` is in `{0, 1}`).  Same for h_fam.
3. So `linearBound.1 + linearBound.2 + 1 ≤ (some small
   linear function of max-child-tH)`.
4. Apply the auxiliary lemma E.5: the simrec's
   towerHeight ≥ max-child-tH (via combined-max).
5. The Nat.log 2 of (small linear function of max-child-tH)
   is dwarfed by 3 · (much larger tH) + 1.

- [ ] **Step L.5.1: Replace the `simrec` underscore
  with the proof body**

```lean
  | _, .simrec (a := a) (k := k) i h_fam g_fam, h => by
      have hh : ∀ j, (h_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun l => (h_fam l).level) ≤ 0 := by
          have := le_trans (le_max_left _ _)
            (Nat.le_of_succ_le_succ h)
          exact this
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j))
          hsup
      have hg : ∀ j, (g_fam j).level ≤ 0 := fun j => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun l => (g_fam l).level) ≤ 0 := by
          have := le_trans (le_max_right _ _)
            (Nat.le_of_succ_le_succ h)
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
      -- Per-l bounds on level0Shape constants via A.5.2.1.
      have h_base_const_bound : ∀ l,
          (KMor1.level0Shape (h_fam l) (hh l)).linearBound.2 ≤
          (kToER (h_fam l)
            (Nat.le_succ_of_le (hh_one l))).towerHeight + 1 :=
        fun l => kToER_level0_towerHeight_ge_const _ _
      have h_step_c_bound : ∀ l,
          (KMor1.level0Shape (g_fam l) (hg l)).linearBound.1 ≤ 1 := by
        intro l
        cases hshape : KMor1.level0Shape (g_fam l) (hg l) with
        | const _ =>
            simp [hshape, ConstantOrShiftedProj.linearBound]
        | shifted _ _ =>
            simp [hshape, ConstantOrShiftedProj.linearBound]
      have h_step_k_bound : ∀ l,
          (KMor1.level0Shape (g_fam l) (hg l)).linearBound.2 ≤
          (kToER (g_fam l)
            (Nat.le_succ_of_le (hg_one l))).towerHeight + 1 :=
        fun l => kToER_level0_towerHeight_ge_const _ _
      -- Auxiliary lemma: simrec towerHeight ≥ max child tH.
      have h_aux :=
        kToER_simrec_towerHeight_ge_max_child_tH
          h_fam g_fam hh_one hg_one i (Nat.le_succ_of_le h)
      -- Compute linearBound.
      simp only [KMor1.linearBound]
      -- Bound the linearBound's fields.
      -- linearBound.1 = max_step_c + 2 · max_step_k + 1
      --              ≤ 1 + 2 · (max_l (kToER g_l).tH + 1)
      --              = 2 · max_l (kToER g_l).tH + 3
      -- linearBound.2 = max_base_const
      --              ≤ max_l (kToER h_l).tH + 1
      -- So .1 + .2 + 1 ≤ 2 · max_g_tH + max_h_tH + 5.
      -- The simrec's tH dominates by h_aux:
      -- (kToER simrec).tH ≥ max(max_g_tH, max_h_tH).
      -- So .1 + .2 + 1 ≤ 3 · (kToER simrec).tH + 5
      -- (loose).
      -- Nat.log 2 (3 · tH + 5) ≤ tH + 3 ≤ 3 · tH + 1
      -- for tH ≥ 1; the simrec's tH is ≥ ~1100, so trivially.
      sorry
```

The final `sorry` is to be filled with the
arithmetic-chain assembly.  The structure:

- Bound `.1 + .2 + 1` linearly in `max_g_tH` and
  `max_h_tH` (using the per-l bounds).
- Use `h_aux` to bound the resulting linear expression
  by `3 · (kToER simrec).tH + small_const`.
- Apply `Nat.log 2 (linear) ≤ tH + small` via mathlib
  helpers from L.1.

- [ ] **Step L.5.2: Fill the simrec case `sorry`**

```lean
      -- Assemble per-l bounds into max bounds.
      set max_h_tH :=
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun l =>
            (kToER (h_fam l)
              (Nat.le_succ_of_le (hh_one l))).towerHeight)
      set max_g_tH :=
        (Finset.univ : Finset (Fin (k + 1))).sup
          (fun l =>
            (kToER (g_fam l)
              (Nat.le_succ_of_le (hg_one l))).towerHeight)
      -- max_base_const ≤ max_h_tH + 1
      have h_max_base :
          (Fin.foldr (k + 1) (fun l acc =>
            max acc
              (KMor1.level0Shape (h_fam l) (hh l)).linearBound.2)
            0) ≤ max_h_tH + 1 := by
        apply Fin.foldr_max_le
        intro j
        calc _
            ≤ (kToER (h_fam j)
                (Nat.le_succ_of_le (hh_one j))).towerHeight + 1 :=
              h_base_const_bound j
          _ ≤ max_h_tH + 1 := by
              have :
                  (kToER (h_fam j)
                    (Nat.le_succ_of_le (hh_one j))).towerHeight ≤
                  max_h_tH :=
                Finset.le_sup (Finset.mem_univ _)
              omega
      -- max_step_c ≤ 1
      have h_max_step_c :
          (Fin.foldr (k + 1) (fun l acc =>
            max acc
              (KMor1.level0Shape (g_fam l) (hg l)).linearBound.1)
            0) ≤ 1 := by
        apply Fin.foldr_max_le
        intro j; exact h_step_c_bound j
      -- max_step_k ≤ max_g_tH + 1
      have h_max_step_k :
          (Fin.foldr (k + 1) (fun l acc =>
            max acc
              (KMor1.level0Shape (g_fam l) (hg l)).linearBound.2)
            0) ≤ max_g_tH + 1 := by
        apply Fin.foldr_max_le
        intro j
        calc _
            ≤ (kToER (g_fam j)
                (Nat.le_succ_of_le (hg_one j))).towerHeight + 1 :=
              h_step_k_bound j
          _ ≤ max_g_tH + 1 := by
              have :
                  (kToER (g_fam j)
                    (Nat.le_succ_of_le (hg_one j))).towerHeight ≤
                  max_g_tH :=
                Finset.le_sup (Finset.mem_univ _)
              omega
      -- Auxiliary lemma: max(max_h_tH, max_g_tH) ≤ (kToER simrec).tH
      -- h_aux : max max_h_tH max_g_tH ≤ (kToER simrec).tH
      -- Bound .1 + .2 + 1.
      -- linearBound.1 + linearBound.2 + 1
      --   = (max_step_c + 2 · max_step_k + 1) + max_base_const + 1
      --   ≤ 1 + 2 · (max_g_tH + 1) + 1 + (max_h_tH + 1) + 1
      --   = 2 · max_g_tH + max_h_tH + 6
      --   ≤ 3 · max(max_g_tH, max_h_tH) + 6
      --   ≤ 3 · (kToER simrec).tH + 6
      -- Nat.log 2 (3 · tH + 6) ≤ tH + 3 ≤ 3 · tH + 1
      -- for tH ≥ 1.  The simrec's tH ≥ 1 trivially via
      -- the outer comp wrapping in kToER's simrec case
      -- (`comp f g`'s towerHeight = f.tH + sup g.tH + 1
      -- ≥ 1).
      have h_simrec_tH_pos :
          1 ≤ (kToER (KMor1.simrec i h_fam g_fam)
            (Nat.le_succ_of_le h)).towerHeight := by
        -- kToER (simrec ...) unfolds to
        --   ERMor1.comp (kSimSzudzikUnpackAt _) (...)
        -- whose towerHeight is f.tH + sup g.tH + 1 ≥ 1.
        unfold kToER
        simp only [ERMor1.towerHeight]
        omega
      omega
```

The positivity helper above is one line — the outer
`comp` in `kToER`'s simrec case adds `+1` to towerHeight
unconditionally.  No deeper threading through
`kSimPackedBase_towerHeight_ge_succ_k` / E.3 is needed
(though those are available as fall-back if `unfold`
elaborates poorly on the simrec case's `let`-bindings).

If `unfold kToER; simp only [ERMor1.towerHeight]; omega`
does not close, the fall-back is to use `change` to
rewrite the goal into the explicit `ERMor1.comp _ _`
form (mirroring the technique used in E.5's helpers),
then `omega`.

- [ ] **Step L.5.3: Build, test, commit (combined
  L.3 / L.4 / L.5)**

```bash
lake build && lake test
```

Expected: PASS, no warnings, no `sorry`/`admit`.

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "$(cat <<'EOF'
Main lemma: linearBoundLog_le_towerHeight (Task 17c L.3, L.4, L.5)

Proves the chain-closing structural inequality
  Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1)
    ≤ 3 · (kToER f).towerHeight + 1
for level-≤-1 K^sim terms, by structural recursion on f.

- atomic (zero/succ/proj): direct numerical computation.
- raise: reduces via linearBoundLog_le_towerHeight_level_zero (L.2).
- comp at level ≤ 0: same level-0 helper.
- comp at level 1: multiplicative-max formula plus IH on f
  and on each child; comp-case algebra closes with one bit
  of slack absorbed by the +1 per comp in towerHeight.
  Uses Nat.log_two_mul_le and Nat.log_two_add_le_max_succ
  (L.1 helpers).
- simrec: small linear bound on linearBound fields via
  A.5.2.1 per-l, dwarfed by the simrec's huge towerHeight
  (witnessed via kToER_simrec_towerHeight_ge_max_child_tH
  from Step 1 E.5).

Public theorem; consumed by Phase IV-B Task D.3.2 (chain-
closing log-vs-tH lemma).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task L.6: Concrete-witness sanity #guard tests

**Files:**

- Modify: `GebLeanTests/Phase4Investigation.lean`.

The existing #guards record `addK_lb`, `addK_ER_tH`,
`addKFanOut5_lb`, `addKFanOut5_ER_tH`.  L.6 adds a
direct-computation #guard that the inequality
`L ≤ 3 · tH + 1` holds for both witnesses.

- [ ] **Step L.6.1: Append witness-level inequality
  #guards**

```lean
-- L.6 sanity: the main inequality
-- linearBoundLog_le_towerHeight closes on the addK and
-- addKFanOut5 witnesses.  The values are pre-computed
-- above via #guards on addK_lb / addKFanOut5_lb /
-- *_ER_tH; the inequalities below assert the chain-
-- closing form `L ≤ 3 · tH + 1`.
#guard Nat.log 2 (addK_lb.1 + addK_lb.2 + 1) ≤
       3 * addK_ER_tH + 1
#guard Nat.log 2
       (addKFanOut5_lb.1 + addKFanOut5_lb.2 + 1) ≤
       3 * addKFanOut5_ER_tH + 1
```

- [ ] **Step L.6.2: Run `lake build` + `lake test`**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step L.6.3: Commit**

```bash
git add GebLeanTests/Phase4Investigation.lean
git commit -m "$(cat <<'EOF'
Phase4Investigation: witness-level #guards for main lemma (Task 17c L.6)

Adds two #guard assertions checking that
Nat.log 2 (lb stuff) ≤ 3 · towerHeight + 1 holds for
addK (2 ≤ 3352) and addKFanOut5 (2 ≤ 3355) — the
numerical witnesses recorded earlier in this file.
Documents the slack pattern for the chain-closing form.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task L.7: Final verification

- [ ] **Step L.7.1: Run full build + test**

```bash
lake build && lake test
```

Expected: PASS (1521+ build jobs, 1561+ test jobs —
1559 baseline plus 2 added in L.6), no warnings, no
`sorry`/`admit`.

- [ ] **Step L.7.2: Verify theorem is `theorem`,
  not `private`**

```bash
grep -A 1 "linearBoundLog_le_towerHeight" \
  GebLean/LawvereKSimPolynomialBound.lean | head -10
```

Confirm the headline lemma is exported (not `private`).

- [ ] **Step L.7.3: Confirm no extraneous sorries**

```bash
grep -n "sorry\|admit" \
  GebLean/LawvereKSimPolynomialBound.lean
```

Expected: zero matches.

- [ ] **Step L.7.4: No commit on this verification
  step (read-only)**

---

## Wong Prop. 4.6 mapping recap

The main inequality realizes Wong's exponent-tracking
recipe (Recursion Class Ch. 4 Prop. 4.6) in our project's
`towerHeight` recursion.  Each case mirrors Wong:

- **Atomic**: Wong's `e_{n+2}^k(max(x⃗))` at `k = 0`
  matches our `Nat.log 2 (small) = small`-bound on
  atomic linearBound.
- **Composition `C(f, g_1, …, g_k)`**: Wong's exponent
  `m + max j(i)`.  Our comp-1 case:
  `Nat.log 2 (lb_comp)` bounded by
  `Nat.log 2 (lb f) + max_l Nat.log 2 (lb g_l) +
  small_const`.  Closes with one bit of slack against
  `3 · (tH(f) + sup tH(g) + 1) + 1`.
- **Bounded recursion `R(g, f, e)`**: Wong's exponent
  inherits from `e`.  Our simrec case: linearBound is
  small linear in max-child-tH (via A.5.2.1); the
  simrec's `tH` (via `iterAutoBoundExpr` + `boundedRec`)
  dominates by E.5's auxiliary lemma.

The factor `3` and the `+1` constant are project-
internal accounting pinned by the comp-case algebra
(see research doc's "Implication for the level-2
dominance chain" callout).

---

## Self-review checklist

**Spec coverage**: every numbered case from
resumption-prompt-v2 lines 215-228 is covered:

- ✓ zero: L.3.2.
- ✓ succ: L.3.3.
- ✓ proj: L.3.4.
- ✓ comp at level ≤ 0: L.3.6 (positive branch).
- ✓ comp at level 1: L.4.
- ✓ raise: L.3.5.
- ✓ simrec: L.5.

**Per-case build/test checkpoints**: L.1 commits
(if needed), L.2 commits, L.3+L.4+L.5 are a single
combined commit (Lean's pattern-match definition cannot
be partially compiled), L.6 commits, L.7 verifies.

**Per-task commit subjects ending in `(Task 17c L.X)`**:
L.1, L.2, L.3+L.4+L.5, L.6 each have a commit subject.

**Critical-path dependencies on landed lemmas**:

- A.5.2.1 (`kToER_level0_towerHeight_ge_const`,
  `LawvereKSimPolynomialBound.lean:1031`, private) —
  used by L.2 and (transitively) L.3.5, L.3.6.  Same-
  file usage works.
- E.5 (`kToER_simrec_towerHeight_ge_max_child_tH`,
  `LawvereKSimPolynomialBound.lean:1711`, private) —
  used by L.5.  Same-file usage works.
- `Fin.foldr_max_ge` (existing) and `Fin.foldr_max_le`
  (existing) — used by L.4 and L.5 for `max_*` bounds.

**Placeholder scan**: the plan contains `sorry`
placeholders inside Steps L.3.6, L.4.1, L.4.2, L.4.3,
L.5.1, L.5.2 — all explicitly listed as transient
working-tree states resolved by their own subsequent
sub-steps before the L.3+L.4+L.5 combined commit.  No
`sorry` appears in any committed state.

**Type consistency**: all theorem signatures use
consistent `(h : f.level ≤ 1)` plus
`(Nat.le_succ_of_le h)` to lift to `level ≤ 2` for
`kToER`'s argument.  The level-0 helper L.2 uses the
double-`Nat.le_succ_of_le` to lift `level ≤ 0` to
`level ≤ 2`.

---

## Out-of-scope deferred work

After this plan completes:

- **Phase IV-B Task D.3.2** (chain-closing log-vs-tH
  lemma at packed step's PolyBound) — separate plan.
  Consumes `KMor1.linearBoundLog_le_towerHeight`.
- **Phase IV-B Tasks D.4 + D.5** (polynomial-iter +
  tower-arithmetic closeout) — chain assembly only,
  uses landed Module A / B infrastructure; may not
  need a dedicated plan.
- **Phase IV-B Task D.1** (the headline
  `kSimTowerBound_dominates_inline` discharge) —
  one-line term-mode proof once D.3.2 + D.4 + D.5 are
  in place.
- **kToER Tasks 14–22** (kToER_interp, kToERN_interp,
  functor obj/map, functor laws, tests, re-export, final
  verification) — separate plan after Phase IV-B closes.
