# BracketGap Monotonicity (sub-stage delta.4.5) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task.  Steps use checkbox (`* [ ]`) syntax for
> tracking.

**Goal:** Add the bracket-monotonicity infrastructure that
unblocks `majorizes_redS` (B-W Lemma 11) and the general-`σ`
case of `majorizes_redTreeIter_node`, then close both
theorems using that infrastructure.

**Architecture:** All new lemmas land in
`GebLean/LawvereGodelTLemma16.lean`.  A reusable `dominates`
predicate (Section A) provides app-monotonicity for non-strict
and strict-preserving comparisons across structurally-different
terms.  A redS-specific level-1 arithmetic toolkit (Section B)
packages the three coefficient inequalities the redS strict-at-0
expansion requires.  Section C closes the two outstanding
majorization theorems.

**Tech Stack:** Lean 4 + mathlib, project conventions per
`CLAUDE.md`.  Existing infrastructure consumed:
`bracketLevel_app_eq` / `bracketLevel_app_high` /
`bracketLevel_app_ge_arg` / `bracketLevel_app_strict_arg` /
`bracketLevel_app_high_ge` / `G_ge_level` /
`bracketLevel_high_zero` / the `majorizes` predicate.

**Spec:**
`docs/superpowers/specs/2026-04-27-bracketgap-monotonicity-design.md`.

**Branch:** `terence/syntax`.

---

## Pre-existing infrastructure (post-merge note)

A merge of work from a parallel workstream landed before this
plan started executing.  The merge added pointwise-monotonicity
lemmas in `LawvereGodelTLemma16.lean` that overlap with this
plan's Section A:

* **`GodelTTerm.bracketLevelAppGen_mono`** (public, line 1479):
  pointwise monotonicity of the underlying `bracketLevelAppGen`
  helper in both function-level and argument-level inputs.
* **`GodelTTerm.bracketLevel_treeIter_arg_mono`** (private,
  line 1498): argument-wise monotonicity of
  `app (treeIter ...) t` in `t.bracketLevel 0`.
* **`GodelTTerm.bracketLevel_app_mono_left`** (private, line
  1518): pointwise monotonicity of `[app f a]_i` in `f`, for
  `i ≤ σ.level`.
* **`GodelTTerm.bracketLevel_app_mono`** (private, line 1537):
  pointwise monotonicity of `[app f a]_i` in both `f` and `a`,
  for `i ≤ σ.level`.

`majorizes_redTreeIter_node` (line 1559) still carries
`hσ : σ.level = 0`, so Task 11's generalization remains
pending.  `end GebLean` is at line 2034.

**Implication for this plan:** Task 3 (`dominates_app`) becomes
a thin wrapper that lifts `bracketLevel_app_mono` from
`i ≤ σ.level` to all `i`, adding the pass-through case via
`bracketLevel_app_high`.  No fresh downward induction is needed.
Section A retains its other tasks unchanged.

Line-number references elsewhere in this plan reflect the
state before this merge; rely on the lemma names rather than
specific line numbers when navigating.

---

## File Structure

* **Modify:** `GebLean/LawvereGodelTLemma16.lean`.

  * **Insert Section A (`dominates` infrastructure)** between
    `majorizes_redTreeIter_leaf` (line ~892) and the existing
    `lh_pos` (line ~894).  This places A above the rest of
    delta.5's contents, so subsequent majorization lemmas may
    consume it.
  * **Insert Section B (redS coefficient bounds)** and
    **Section C.1 (`majorizes_redS`)** appended after the
    existing `majorizes_redTreeIter_node` (line ~2032), before
    `end GebLean`.
  * **Section C.2 (generalize `majorizes_redTreeIter_node`)**
    revises the existing definition in place; the strict-at-0
    branch is preserved verbatim, the monotone-at-`i` branch is
    rewritten.

* **No new files.**  No edits to `Utilities/`.  No edits to any
  module other than `LawvereGodelTLemma16.lean`.

---

## Conventions

* Each task corresponds to one named lemma (or one small
  cluster of routine lemmas in Task 2).  Steps within a task
  follow the project's standard cadence: introduce signature
  with `_` placeholder, run `lake build` to view the goal,
  fill in the proof following the sketch, run `lake build &&
  lake test` clean, commit.
* All commits use the trailer
  `Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>`.
* Forbidden words per `CLAUDE.md` apply to all commit
  messages and any comment text added to the file.
* Line length ≤ 80.  No emojis.  No `sorry` / `admit` /
  `Classical` / `noncomputable` / `axiom`.  Build must be
  warning-free.
* Where a proof step gets stuck, factor out a smaller lemma
  per `CLAUDE.md`'s "factoring-out-lemmas" guidance and
  recurse.

---

## Section A: `dominates` infrastructure

### Task 1: `GodelTTerm.dominates` definition

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — insert at
  line ~892, after `majorizes_redTreeIter_leaf` and before
  `lh_pos`.

**Note**: `dominates` quantifies over `i ≤ σ.level`, mirroring
the `majorizes` predicate (line 434).  The earlier draft of
this plan used unrestricted `∀ i, ...`, which is unsound: for
compound `.app` terms `t : σ`, the rule-15 pass-through in
`bracketLevelAppGen` can yield `t.bracketLevel i ≠ 0` at
`i > σ.level` (e.g. `app (app (.K σ τ) a) b : σ` carries the
`K`-head's nonzero bracket up to level `(σ→τ→σ).level >
σ.level`).  The restriction to `i ≤ σ.level` matches the only
range where dominance facts are derivable structurally.

* [ ] **Step 1: Add the definition with docstring**

```lean
/-- Non-strict bracket dominance: `t.dominates s` if at every
level `i ≤ σ.level`,
`s.bracketLevel i ≤ t.bracketLevel i`.

Mirrors the monotone-at-`i` clause of `majorizes`.  The range
restriction matches `majorizes`'s and reflects that bracket
values are not in general comparable above `σ.level` for
compound `.app` terms. -/
def GodelTTerm.dominates {S : Set GodelTBase} {n : Nat}
    {σ : GodelTType S} (t s : GodelTTerm S n σ) : Prop :=
  ∀ i, i ≤ σ.level → s.bracketLevel i ≤ t.bracketLevel i
```

* [ ] **Step 2: Build clean**

Run: `lake build`.  Expected: 1510 jobs, no warnings.

* [ ] **Step 3: Run tests**

Run: `lake test`.  Expected: exit 0.

* [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section A.1): GodelTTerm.dominates predicate

Add the non-strict bracket dominance predicate
`t.dominates s := ∀ i, [s]_i ≤ [t]_i` for use in app-
monotonicity lemmas.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

### Task 2: Routine structural lemmas

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append
  immediately after Task 1's definition.

* [ ] **Step 1: Add `dominates_refl`**

```lean
theorem GodelTTerm.dominates_refl {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S} (t : GodelTTerm S n σ) :
    t.dominates t :=
  fun _ _ => Nat.le_refl _
```

* [ ] **Step 2: Build clean**

Run: `lake build`.  Expected: no warnings.

* [ ] **Step 3: Add `dominates_trans`**

```lean
theorem GodelTTerm.dominates_trans {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    {t s u : GodelTTerm S n σ}
    (h₁ : t.dominates s) (h₂ : s.dominates u) :
    t.dominates u :=
  fun i hi => Nat.le_trans (h₂ i hi) (h₁ i hi)
```

* [ ] **Step 4: Build clean**

Run: `lake build`.

* [ ] **Step 5: Add `majorizes_imp_dominates`**

With the restricted `dominates`, this is the trivial
projection of `majorizes`'s monotone clause:

```lean
theorem GodelTTerm.majorizes_imp_dominates {S : Set GodelTBase}
    {n : Nat} {σ : GodelTType S}
    {t s : GodelTTerm S n σ} (h : t.majorizes s) :
    t.dominates s := h.2
```

* [ ] **Step 6: Build clean and run tests**

Run: `lake build && lake test`.

* [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section A.2): dominates structural lemmas

Add `dominates_refl`, `dominates_trans`, and
`majorizes_imp_dominates`.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

### Task 3: `dominates_app` (binary monotonicity)

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  Task 2.

**Approach.** With the restricted `dominates`, the conclusion
quantifies over `i ≤ τ.level`, the premises over
`i ≤ (.arrow σ τ).level` and `i ≤ σ.level` respectively.  We
cannot use the merged `bracketLevel_app_mono` (it requires
unrestricted pointwise hypotheses).  Instead, do downward
induction on `i` ranging over `i ≤ (.arrow σ τ).level` (which
covers `τ.level` since `(.arrow σ τ).level = max (σ.level + 1)
τ.level ≥ τ.level`), case-splitting on `i ≤ σ.level`
(multiplicative) versus `σ.level < i ≤ (.arrow σ τ).level`
(pass-through).

The pass-through case at `i = (.arrow σ τ).level` provides
the induction's base; descending steps handle multiplicative
levels.

* [ ] **Step 1: Add the signature with `_` placeholder**

```lean
/-- Bracket dominance propagates through binary application:
if both heads are non-iter and both arguments are pointwise-
dominated within their type levels, the application is
pointwise-dominated within its type level. -/
theorem GodelTTerm.dominates_app {S : Set GodelTBase}
    {n : Nat} {σ τ : GodelTType S}
    (f f' : GodelTTerm S n (.arrow σ τ))
    (a a' : GodelTTerm S n σ)
    (hf : f.isIterHead = false) (hf' : f'.isIterHead = false)
    (hF : f'.dominates f) (hA : a'.dominates a) :
    (GodelTTerm.app f' a').dominates (GodelTTerm.app f a) := _
```

* [ ] **Step 2: Build to view the goal**

Run: `lake build`.  Expected: unsolved goals.

* [ ] **Step 3: Set up the descent frame**

Replace the `_` with the high-level structure:

```lean
  := by
  -- Prove the stronger statement
  --   ∀ i ≤ (.arrow σ τ).level,
  --     [.app f a]_i ≤ [.app f' a']_i
  -- by descending induction on `i`, then specialize to
  -- `i ≤ τ.level` (since τ.level ≤ (.arrow σ τ).level).
  set M := (GodelTType.arrow σ τ).level with hM_def
  have hM_ge_τ : τ.level ≤ M := by
    rw [hM_def]; change τ.level ≤ max (σ.level + 1) τ.level
    omega
  suffices h : ∀ k, ∀ i, k + i = M → i ≤ M →
      (GodelTTerm.app f a).bracketLevel i ≤
        (GodelTTerm.app f' a').bracketLevel i by
    intro i hi
    have hiM : i ≤ M := Nat.le_trans hi hM_ge_τ
    exact h (M - i) i (by omega) hiM
  intro k
  induction k with
  | zero =>
    intro i hi_sum hi_le
    -- i = M: pass-through (M ≥ σ.level + 1).
    obtain rfl : i = M := by omega
    have hiσ : σ.level < M := by
      rw [hM_def]; change σ.level < max (σ.level + 1) τ.level
      omega
    rw [GodelTTerm.bracketLevel_app_high f a M hiσ hf,
        GodelTTerm.bracketLevel_app_high f' a' M hiσ hf']
    exact hF M (Nat.le_refl _)
  | succ k ih =>
    intro i hi_sum hi_le
    rcases Nat.lt_or_ge σ.level i with hiσ | hiσ
    · -- pass-through: σ.level < i ≤ M.
      rw [GodelTTerm.bracketLevel_app_high f a i hiσ hf,
          GodelTTerm.bracketLevel_app_high f' a' i hiσ hf']
      exact hF i hi_le
    · -- multiplicative: i ≤ σ.level.
      rw [GodelTTerm.bracketLevel_app_eq f a i hiσ hf,
          GodelTTerm.bracketLevel_app_eq f' a' i hiσ hf']
      have hSucc_le : i + 1 ≤ M := by omega
      have hStepInner :
          (GodelTTerm.app f a).bracketLevel (i + 1) ≤
            (GodelTTerm.app f' a').bracketLevel (i + 1) :=
        ih (i + 1) (by omega) hSucc_le
      have hPow :
          2 ^ (GodelTTerm.app f a).bracketLevel (i + 1) ≤
            2 ^ (GodelTTerm.app f' a').bracketLevel (i + 1) :=
        Nat.pow_le_pow_right (by decide) hStepInner
      have hF_at : f.bracketLevel i ≤ f'.bracketLevel i := by
        apply hF i
        -- i ≤ σ.level ≤ (.arrow σ τ).level = M.
        rw [hM_def]
        change i ≤ max (σ.level + 1) τ.level
        omega
      have hA_at : a.bracketLevel i ≤ a'.bracketLevel i :=
        hA i hiσ
      have hSum :
          f.bracketLevel i + a.bracketLevel i ≤
            f'.bracketLevel i + a'.bracketLevel i := by omega
      exact Nat.mul_le_mul hPow hSum
```

* [ ] **Step 4: Build clean and run tests**

Run: `lake build && lake test`.  Expected: no warnings, exit 0.

**If the build fails:**

* The most likely cause is the descent frame's `k + i = M`
  constraint not staying syntactically aligned through the
  `omega` calls.  Adjust by computing `M - i` directly and
  passing that as the descent variable.
* If `Nat.lt_or_ge` is not the right name, search the file for
  prior uses of similar splits (e.g. line 1100 uses
  `Nat.lt_or_ge`).
* If `(GodelTType.arrow σ τ).level` does not unfold cleanly,
  add a `show` tactic with the explicit `max (σ.level + 1)
  τ.level` form.

* [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section A.3): dominates_app monotonicity

Bracket dominance propagates through binary application by
descending induction on the bracket level over the range
`i ≤ (.arrow σ τ).level`, splitting into multiplicative and
pass-through cases at each step.  Specializes to the
restricted-`dominates` conclusion `i ≤ τ.level`.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

### Task 4: `majorizes_app_left`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  Task 3.

**Approach:** Strict-at-0 from `bracketLevel_app_eq` at `i = 0`
plus the strict factor `[f]_0 < [f']_0`.  The level-1 exponent
comparison is done inline rather than via `dominates_app`,
because `dominates_app`'s conclusion is over `i ≤ τ.level`
which can fail at `i = 1` when `τ.level = 0`.  At level 1 we
case-split on `σ.level` (pass-through if 0, multiplicative
otherwise — the latter recurses but at most one level deep
because of the type-level bound).  Monotone-at-`i` for
`i ≤ τ.level` via `dominates_app` with `a' = a`.

* [ ] **Step 1: Add the signature with `_` placeholder**

```lean
/-- `majorizes` propagates through the left side of `app`:
if `f' ≫ f` and both heads are non-iter, then
`app f' a ≫ app f a` for any common right-argument `a`. -/
theorem GodelTTerm.majorizes_app_left {S : Set GodelTBase}
    {n : Nat} {σ τ : GodelTType S}
    (f f' : GodelTTerm S n (.arrow σ τ))
    (a : GodelTTerm S n σ)
    (hf : f.isIterHead = false) (hf' : f'.isIterHead = false)
    (h : f'.majorizes f) :
    (GodelTTerm.app f' a).majorizes (GodelTTerm.app f a) := _
```

* [ ] **Step 2: Build to view goal**

Run: `lake build`.  Expected: unsolved goals showing the
`majorizes` conjunction.

* [ ] **Step 3: Fill in the proof**

```lean
  := by
  refine ⟨?_, ?_⟩
  · -- Strict-at-0.
    rw [GodelTTerm.bracketLevel_app_eq f a 0 (Nat.zero_le _) hf,
        GodelTTerm.bracketLevel_app_eq f' a 0
          (Nat.zero_le _) hf']
    have hStrict : f.bracketLevel 0 < f'.bracketLevel 0 := h.1
    have hPow1 : 1 ≤ 2 ^ (GodelTTerm.app f a).bracketLevel 1 :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hPow2 : 1 ≤ 2 ^ (GodelTTerm.app f' a).bracketLevel 1 :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    -- `[f]_0 + [a]_0 < [f']_0 + [a]_0`, then multiply by ≥ 1
    -- on the left.  Need also that the LHS exponent dominates
    -- via `dominates_app`.
    have hDominates :
        (GodelTTerm.app f a).dominates_  -- placeholder identifier
        := sorry
    sorry
```

Step 3 above is intentionally a sketch; it leaves the
algebraic inequality `2^A * (x + a) < 2^B * (y + a)` when
`x < y` and `A ≤ B` and `1 ≤ 2^A` as a separate piece.
Refactor: factor out a small numeric lemma.

* [ ] **Step 4: Add a numeric helper above `majorizes_app_left`**

```lean
private theorem GodelTTerm.aux_pow_mul_strict
    {A B x y a : Nat} (hA : A ≤ B) (hxy : x < y) :
    2 ^ A * (x + a) < 2 ^ B * (y + a) := by
  have hP : 1 ≤ 2 ^ A :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hPmono : 2 ^ A ≤ 2 ^ B :=
    Nat.pow_le_pow_right (by decide) hA
  have hSum : x + a < y + a := by omega
  calc 2 ^ A * (x + a)
      < 2 ^ A * (y + a) := by
        exact Nat.mul_lt_mul_left
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hP) hSum
    _ ≤ 2 ^ B * (y + a) := Nat.mul_le_mul_right _ hPmono
```

* [ ] **Step 5: Build clean**

Run: `lake build`.  Expected: no warnings (the helper closes).

* [ ] **Step 6: Replace the strict-at-0 sketch with the helper**

```lean
  refine ⟨?_, ?_⟩
  · rw [GodelTTerm.bracketLevel_app_eq f a 0 (Nat.zero_le _) hf,
        GodelTTerm.bracketLevel_app_eq f' a 0
          (Nat.zero_le _) hf']
    have hF_dom : f'.dominates f :=
      GodelTTerm.majorizes_imp_dominates h
    have hA_dom : a.dominates a := GodelTTerm.dominates_refl a
    have hAppDom : (GodelTTerm.app f' a).dominates
        (GodelTTerm.app f a) :=
      GodelTTerm.dominates_app f f' a a hf hf' hF_dom hA_dom
    have hStep1 :
        (GodelTTerm.app f a).bracketLevel 1 ≤
          (GodelTTerm.app f' a).bracketLevel 1 := hAppDom 1
    have hStrict : f.bracketLevel 0 < f'.bracketLevel 0 := h.1
    -- Use `aux_pow_mul_strict` with `x = [f]_0`, `y = [f']_0`,
    -- `a = [a]_0`, `A = [.app f a]_1`, `B = [.app f' a]_1`.
    exact GodelTTerm.aux_pow_mul_strict hStep1 hStrict
```

* [ ] **Step 7: Fill in the monotone-at-`i` branch**

```lean
  · intro i hi
    have hF_dom : f'.dominates f :=
      GodelTTerm.majorizes_imp_dominates h
    have hA_dom : a.dominates a := GodelTTerm.dominates_refl a
    have hAppDom : (GodelTTerm.app f' a).dominates
        (GodelTTerm.app f a) :=
      GodelTTerm.dominates_app f f' a a hf hf' hF_dom hA_dom
    exact hAppDom i
```

* [ ] **Step 8: Build clean and run tests**

Run: `lake build && lake test`.

* [ ] **Step 9: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section A.4): majorizes_app_left

Strict-at-0 via aux_pow_mul_strict and the inner exponent
comparison from dominates_app; monotone-at-i directly from
dominates_app.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

### Task 5: `majorizes_app_right`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  Task 4.

**Approach:** Symmetric to Task 4.  Note: only `f.isIterHead =
false` is required (no `f'`), since `f` appears on both sides.

* [ ] **Step 1: Add the signature**

```lean
/-- `majorizes` propagates through the right side of `app`:
if `a' ≫ a` and `f`'s head is non-iter, then
`app f a' ≫ app f a`. -/
theorem GodelTTerm.majorizes_app_right {S : Set GodelTBase}
    {n : Nat} {σ τ : GodelTType S}
    (f : GodelTTerm S n (.arrow σ τ))
    (a a' : GodelTTerm S n σ)
    (hf : f.isIterHead = false)
    (h : a'.majorizes a) :
    (GodelTTerm.app f a').majorizes (GodelTTerm.app f a) := _
```

* [ ] **Step 2: Fill in the proof, mirroring Task 4**

```lean
  := by
  refine ⟨?_, ?_⟩
  · rw [GodelTTerm.bracketLevel_app_eq f a 0 (Nat.zero_le _) hf,
        GodelTTerm.bracketLevel_app_eq f a' 0
          (Nat.zero_le _) hf]
    have hA_dom : a'.dominates a :=
      GodelTTerm.majorizes_imp_dominates h
    have hF_dom : f.dominates f := GodelTTerm.dominates_refl f
    have hAppDom : (GodelTTerm.app f a').dominates
        (GodelTTerm.app f a) :=
      GodelTTerm.dominates_app f f a a' hf hf hF_dom hA_dom
    have hStep1 :
        (GodelTTerm.app f a).bracketLevel 1 ≤
          (GodelTTerm.app f a').bracketLevel 1 := hAppDom 1
    have hStrict : a.bracketLevel 0 < a'.bracketLevel 0 := h.1
    -- Use the helper but with the `f`-side fixed and the
    -- `a`-side strict.  Reorder the sum.
    have hPerm : ∀ x y z : Nat, x + y = y + x := by
      intros; omega
    rw [hPerm (f.bracketLevel 0) (a.bracketLevel 0),
        hPerm (f.bracketLevel 0) (a'.bracketLevel 0)]
    exact GodelTTerm.aux_pow_mul_strict hStep1 hStrict
  · intro i hi
    have hA_dom : a'.dominates a :=
      GodelTTerm.majorizes_imp_dominates h
    have hF_dom : f.dominates f := GodelTTerm.dominates_refl f
    have hAppDom : (GodelTTerm.app f a').dominates
        (GodelTTerm.app f a) :=
      GodelTTerm.dominates_app f f a a' hf hf hF_dom hA_dom
    exact hAppDom i
```

* [ ] **Step 3: Build clean and run tests**

Run: `lake build && lake test`.

* [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section A.5): majorizes_app_right

Mirror of majorizes_app_left with the strict gap on the
right argument; reuses dominates_app and aux_pow_mul_strict.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Section B: redS coefficient bounds

Each B-task follows the same scaffolding: `set` abbreviations
for the seven sub-terms, derive `isIterHead = false` for each
non-trivial sub-term, then case-split on
`(rho.level ≥ 1, sigma.level ≥ 1)` to discharge the conclusion
via `bracketLevel_app_eq` / `bracketLevel_app_high` plus
`omega` (and `Nat.pow_le_pow_right` where needed).

The four cases are:

* **Case (0, 0)** (`rho.level = 0 ∧ sigma.level = 0`): all
  inner brackets pass-through at level 1; closes via direct
  arithmetic.
* **Case (1, 0)** (`rho.level ≥ 1 ∧ sigma.level = 0`): LHS
  brackets stay multiplicative; RHS pass-through.
* **Case (0, 1)** (`rho.level = 0 ∧ sigma.level ≥ 1`): RHS
  brackets stay multiplicative; LHS pass-through (in the
  problematic component).
* **Case (1, 1)** (`rho.level ≥ 1 ∧ sigma.level ≥ 1`): both
  multiplicative.

### Task 6: Shared scaffolding lemma `redS_setup`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  the existing `majorizes_redTreeIter_node`.

**Approach:** Define a private helper that establishes the
`isIterHead = false` facts and basic bracket-level identities
that B1, B2, B3 all need.  This avoids duplication.

Decision: Inline the scaffolding via `have` bindings inside each
B-task, rather than factoring to a private definition, because:

* Lean's `set` and `have` machinery does not export naturally
  across lemmas.
* The scaffolding is only ~20 lines per consumer.

**Therefore, no separate scaffolding lemma is created.**  The
three B-tasks each begin with the same `set` / `have` block
shown in their respective Step 1 below.

(This task records the decision and adds no code; it has no
commit.  Skip to Task 7.)

---

### Task 7: `redS_f_coef_bound`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  the existing `majorizes_redTreeIter_node`.

* [ ] **Step 1: Add the signature with the standard scaffolding**

```lean
/-- redS coefficient inequality for `[f]_0`:

  [LHS]_1 + [appSfg]_1 + [appSf]_1 ≥ [RHS]_1 + [appfx]_1.

This is one of three level-1 inequalities the `majorizes_redS`
strict-at-0 expansion requires (B-W Lemma 11). -/
theorem GodelTTerm.redS_f_coef_bound {S : Set GodelTBase}
    {n : Nat} (ρ σ τ : GodelTType S)
    (f : GodelTTerm S n (.arrow ρ (.arrow σ τ)))
    (g : GodelTTerm S n (.arrow ρ σ))
    (x : GodelTTerm S n ρ) :
    (GodelTTerm.app (GodelTTerm.app (GodelTTerm.app
      (GodelTTerm.S_comb (n := n) ρ σ τ) f) g) x).bracketLevel 1
    + (GodelTTerm.app (GodelTTerm.app (GodelTTerm.S_comb
      (n := n) ρ σ τ) f) g).bracketLevel 1
    + (GodelTTerm.app (GodelTTerm.S_comb (n := n) ρ σ τ)
      f).bracketLevel 1
    ≥ (GodelTTerm.app (GodelTTerm.app f x)
      (GodelTTerm.app g x)).bracketLevel 1
    + (GodelTTerm.app f x).bracketLevel 1 := _
```

* [ ] **Step 2: Build to view goal**

Run: `lake build`.

* [ ] **Step 3: Add the standard `set` block**

```lean
  := by
  set Sat := GodelTTerm.S_comb (S := S) (n := n) ρ σ τ
    with hSat_def
  set appSf := GodelTTerm.app Sat f with happSf_def
  set appSfg := GodelTTerm.app appSf g with happSfg_def
  set LHS := GodelTTerm.app appSfg x with hLHS_def
  set appfx := GodelTTerm.app f x with happfx_def
  set appgx := GodelTTerm.app g x with happgx_def
  set RHS := GodelTTerm.app appfx appgx with hRHS_def
  -- isIterHead facts.
  have hSatNI : Sat.isIterHead = false := rfl
  have happSfNI : appSf.isIterHead = false := rfl
  have happSfgNI : appSfg.isIterHead = false := rfl
  have happfxNI : appfx.isIterHead = false := rfl
  have happgxNI : appgx.isIterHead = false := rfl
  -- Sat bracket value at low levels.
  have hSat1 : Sat.bracketLevel 1 = 1 := by
    rw [hSat_def, GodelTTerm.bracketLevel_S_comb]
    rw [if_pos]
    -- Sat.type.level ≥ 2.
    change 1 ≤ max ((GodelTType.arrow ρ (.arrow σ τ)).level + 1)
      (max ((GodelTType.arrow ρ σ).level + 1)
        (max (ρ.level + 1) τ.level))
    omega
  sorry
```

* [ ] **Step 4: Build to view goal**

Run: `lake build`.  Expected: error at `sorry` showing the
remaining goal.

* [ ] **Step 5: Case-split on `rho.level` and `sigma.level`**

Replace the `sorry` with:

```lean
  rcases Nat.lt_or_ge ρ.level 1 with hρ | hρ
  · -- ρ.level = 0.
    have hρ0 : ρ.level = 0 := by omega
    rcases Nat.lt_or_ge σ.level 1 with hσ | hσ
    · -- Case (0, 0).
      have hσ0 : σ.level = 0 := by omega
      sorry
    · -- Case (0, 1+).
      sorry
  · -- ρ.level ≥ 1.
    rcases Nat.lt_or_ge σ.level 1 with hσ | hσ
    · -- Case (1+, 0).
      have hσ0 : σ.level = 0 := by omega
      sorry
    · -- Case (1+, 1+).
      sorry
```

* [ ] **Step 6: Discharge case (0, 0)**

In the first `sorry` (case `ρ.level = 0`, `σ.level = 0`):

```lean
      -- LHS.bracketLevel 1 = appSfg.bracketLevel 1
      --   (pass-through, since 1 > ρ.level = 0).
      have hLHS1 : LHS.bracketLevel 1 = appSfg.bracketLevel 1 := by
        rw [hLHS_def]
        exact GodelTTerm.bracketLevel_app_high appSfg x 1
          (by omega) happSfgNI
      -- appSfg.bracketLevel 1 multiplicative
      --   (1 ≤ (ρ→σ).level = 1).
      have h_ρσ_level :
          (GodelTType.arrow ρ σ).level = 1 := by
        change max (ρ.level + 1) σ.level = 1; omega
      have happSfg1 :
          appSfg.bracketLevel 1 =
            2 ^ appSfg.bracketLevel 2 *
              (appSf.bracketLevel 1 + g.bracketLevel 1) := by
        rw [happSfg_def]
        exact GodelTTerm.bracketLevel_app_eq appSf g 1
          (by rw [h_ρσ_level]) happSfNI
      -- appSf.bracketLevel 1 multiplicative
      --   (1 ≤ (ρ→σ→τ).level ≥ 1).
      have h_ρστ_level :
          (GodelTType.arrow ρ (.arrow σ τ)).level ≥ 1 := by
        change max (ρ.level + 1) (max (σ.level + 1) τ.level) ≥ 1
        omega
      have happSf1 :
          appSf.bracketLevel 1 =
            2 ^ appSf.bracketLevel 2 *
              (1 + f.bracketLevel 1) := by
        rw [happSf_def,
            GodelTTerm.bracketLevel_app_eq Sat f 1
              h_ρστ_level hSatNI, hSat1]
      -- RHS.bracketLevel 1 = appfx.bracketLevel 1 (pass-through,
      -- since σ.level = 0 < 1).
      have hRHS1 : RHS.bracketLevel 1 = appfx.bracketLevel 1 := by
        rw [hRHS_def]
        exact GodelTTerm.bracketLevel_app_high appfx appgx 1
          (by omega) happfxNI
      -- appfx.bracketLevel 1 = f.bracketLevel 1 (pass-through,
      -- since ρ.level = 0 < 1).
      have happfx1 : appfx.bracketLevel 1 = f.bracketLevel 1 := by
        rw [happfx_def]
        exact GodelTTerm.bracketLevel_app_high f x 1
          (by omega) (by cases f <;> rfl)
      -- Now the inequality
      --   [LHS]_1 + [appSfg]_1 + [appSf]_1
      --     ≥ [RHS]_1 + [appfx]_1
      -- becomes
      --   appSfg.bracketLevel 1 + appSfg.bracketLevel 1
      --     + appSf.bracketLevel 1 ≥ 2 * f.bracketLevel 1
      -- which holds because each appSf.bracketLevel 1 ≥
      -- 1 + f.bracketLevel 1 by happSf1.
      have hAppSf_lb :
          1 + f.bracketLevel 1 ≤ appSf.bracketLevel 1 := by
        rw [happSf1]
        have hP : 1 ≤ 2 ^ appSf.bracketLevel 2 :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        calc 1 + f.bracketLevel 1
            ≤ 2 ^ appSf.bracketLevel 2 *
                (1 + f.bracketLevel 1) :=
              Nat.le_mul_of_pos_left _ hP
      rw [hLHS1, hRHS1, happfx1]
      omega
```

* [ ] **Step 7: Build to verify case (0, 0) closes**

Run: `lake build`.  Expected: only the three remaining `sorry`s.

* [ ] **Step 8: Discharge case (0, 1+) similarly**

In the second `sorry` (case `ρ.level = 0`, `σ.level ≥ 1`):

```lean
      -- LHS pass-through to appSfg as in case (0, 0).
      have hLHS1 : LHS.bracketLevel 1 = appSfg.bracketLevel 1 := by
        rw [hLHS_def]
        exact GodelTTerm.bracketLevel_app_high appSfg x 1
          (by omega) happSfgNI
      have h_ρσ_level :
          (GodelTType.arrow ρ σ).level ≥ 1 := by
        change max (ρ.level + 1) σ.level ≥ 1; omega
      have h_ρστ_level :
          (GodelTType.arrow ρ (.arrow σ τ)).level ≥ 1 := by
        change max (ρ.level + 1) (max (σ.level + 1) τ.level) ≥ 1
        omega
      have happSfg1 :
          appSfg.bracketLevel 1 =
            2 ^ appSfg.bracketLevel 2 *
              (appSf.bracketLevel 1 + g.bracketLevel 1) := by
        rw [happSfg_def]
        exact GodelTTerm.bracketLevel_app_eq appSf g 1
          h_ρσ_level happSfNI
      have happSf1 :
          appSf.bracketLevel 1 =
            2 ^ appSf.bracketLevel 2 *
              (1 + f.bracketLevel 1) := by
        rw [happSf_def,
            GodelTTerm.bracketLevel_app_eq Sat f 1
              h_ρστ_level hSatNI, hSat1]
      -- RHS multiplicative now (σ.level ≥ 1, so 1 ≤ σ.level).
      have hRHS1 :
          RHS.bracketLevel 1 =
            2 ^ RHS.bracketLevel 2 *
              (appfx.bracketLevel 1 + appgx.bracketLevel 1) := by
        rw [hRHS_def]
        exact GodelTTerm.bracketLevel_app_eq appfx appgx 1
          hσ happfxNI
      -- appfx pass-through (ρ.level = 0 < 1).
      have happfx1 : appfx.bracketLevel 1 = f.bracketLevel 1 := by
        rw [happfx_def]
        exact GodelTTerm.bracketLevel_app_high f x 1
          (by omega) (by cases f <;> rfl)
      have hAppSf_lb :
          1 + f.bracketLevel 1 ≤ appSf.bracketLevel 1 := by
        rw [happSf1]
        have hP : 1 ≤ 2 ^ appSf.bracketLevel 2 :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        calc 1 + f.bracketLevel 1
            ≤ 2 ^ appSf.bracketLevel 2 *
                (1 + f.bracketLevel 1) :=
              Nat.le_mul_of_pos_left _ hP
      have hAppSfg_lb :
          appSf.bracketLevel 1 ≤ appSfg.bracketLevel 1 := by
        rw [happSfg1]
        have hP : 1 ≤ 2 ^ appSfg.bracketLevel 2 :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        calc appSf.bracketLevel 1
            ≤ appSf.bracketLevel 1 + g.bracketLevel 1 := by omega
          _ ≤ 2 ^ appSfg.bracketLevel 2 *
                (appSf.bracketLevel 1 + g.bracketLevel 1) :=
              Nat.le_mul_of_pos_left _ hP
      have hRHS_lb :
          appfx.bracketLevel 1 + appgx.bracketLevel 1
            ≤ RHS.bracketLevel 1 := by
        rw [hRHS1]
        have hP : 1 ≤ 2 ^ RHS.bracketLevel 2 :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        exact Nat.le_mul_of_pos_left _ hP
      rw [hLHS1, happfx1]
      -- Need: appSfg.bracketLevel 1 + appSfg.bracketLevel 1 +
      --   appSf.bracketLevel 1 ≥ RHS.bracketLevel 1 +
      --   f.bracketLevel 1.
      -- From hRHS_lb: RHS.bracketLevel 1 ≥ f.bracketLevel 1 +
      --   appgx.bracketLevel 1 (using happfx1).
      -- This case is harder: RHS_1 contains appgx_1 which is
      -- not directly bounded by appSfg_1.  Rely on the
      -- stronger fact: appSfg_1 + appSf_1 ≥ 2 + 2*f_1 ≥ RHS_1
      -- as shown by combining bounds.
      sorry
```

**Note for Step 8:** Case (0, 1+) is genuinely harder because
RHS_1 contains `appgx_1` (which can be larger than the LHS
contribution if `[g]_1` or `[x]_1` is large).  If the `omega`
discharge fails, factor out a sub-lemma showing that
`appSfg.bracketLevel 1 ≥ appgx.bracketLevel 1` directly via
`bracketLevel_app_eq` expansion of both — this is feasible
because the multiplicative scaffolding on both sides shares
similar shape, and `[appSf]_1 ≥ 1 + [f]_1` plus the iter
factor compensates.

If still stuck, check whether the conclusion is even true in
this case; if not, the case-split granularity needs to be
refined (e.g., split further on `τ.level`).

* [ ] **Step 9: Build incrementally to verify each case**

After each case-discharge, run `lake build` and check that the
specific `sorry` is closed.  Do not move to the next case until
the current one is clean.

* [ ] **Step 10: Discharge case (1+, 0)**

Mirror of case (0, 1+) with the multiplicative-vs-pass-through
roles of LHS and RHS swapped.

* [ ] **Step 11: Discharge case (1+, 1+)**

Both sides multiplicative; the cleanest case.  Both LHS_1 and
RHS_1 expand fully and the inequality reduces to comparison of
3-fold versus 2-fold tower products, which `omega` plus
`Nat.pow_le_pow_right` should close after appropriate
`have`-binding of intermediate values.

* [ ] **Step 12: Build clean and run tests**

Run: `lake build && lake test`.  Expected: no warnings, exit 0.

* [ ] **Step 13: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section B.1): redS_f_coef_bound

Level-1 inequality for the [f]_0 coefficient in the redS
strict-at-0 expansion.  Four-case split on rho.level vs
sigma.level discharged via bracketLevel_app_eq /
bracketLevel_app_high and arithmetic.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

**If a case unexpectedly does not close:** factor out a smaller
sub-lemma per `CLAUDE.md`'s guidance.  Surface the obstruction
in the workstream tracker before attempting further unrolling.

---

### Task 8: `redS_g_coef_bound`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  Task 7.

**Approach:** Same scaffolding as Task 7, conclusion replaces
`appfx` with `appgx` and drops the leftmost `appSf.bracketLevel 1`
term.

* [ ] **Step 1: Add the signature**

```lean
/-- redS coefficient inequality for `[g]_0`:

  [LHS]_1 + [appSfg]_1 ≥ [RHS]_1 + [appgx]_1. -/
theorem GodelTTerm.redS_g_coef_bound {S : Set GodelTBase}
    {n : Nat} (ρ σ τ : GodelTType S)
    (f : GodelTTerm S n (.arrow ρ (.arrow σ τ)))
    (g : GodelTTerm S n (.arrow ρ σ))
    (x : GodelTTerm S n ρ) :
    (GodelTTerm.app (GodelTTerm.app (GodelTTerm.app
      (GodelTTerm.S_comb (n := n) ρ σ τ) f) g) x).bracketLevel 1
    + (GodelTTerm.app (GodelTTerm.app (GodelTTerm.S_comb
      (n := n) ρ σ τ) f) g).bracketLevel 1
    ≥ (GodelTTerm.app (GodelTTerm.app f x)
      (GodelTTerm.app g x)).bracketLevel 1
    + (GodelTTerm.app g x).bracketLevel 1 := _
```

* [ ] **Step 2: Replicate the scaffolding from Task 7 Step 3.**

* [ ] **Step 3: Run the same four-case split.**  Each case
proceeds identically to Task 7 with `g` substituted for `f`
and the leftmost `appSf` term absent.

* [ ] **Step 4: Build clean and run tests**

* [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section B.2): redS_g_coef_bound

Level-1 inequality for the [g]_0 coefficient.  Same case-split
structure as redS_f_coef_bound.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

### Task 9: `redS_x_coef_bound` (KI3)

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  Task 8.

**Approach:** Same scaffolding as Task 7.  The `+1` strict
slack comes from the `[Sat]_2 = 1` contribution, not `[Sat]_1`.
At level 2, `[Sat]_2 = 1` (since `2 ≤ Sat.type.level ≥ 2`).
The doubled `2^...` factor in LHS_1 gains an extra `+1`
relative to `RHS_1 + max(...)`.

* [ ] **Step 1: Add the signature**

```lean
/-- redS coefficient inequality for `[x]_0` (KI3):

  [LHS]_1 ≥ [RHS]_1 + max([appfx]_1, [appgx]_1) + 1. -/
theorem GodelTTerm.redS_x_coef_bound {S : Set GodelTBase}
    {n : Nat} (ρ σ τ : GodelTType S)
    (f : GodelTTerm S n (.arrow ρ (.arrow σ τ)))
    (g : GodelTTerm S n (.arrow ρ σ))
    (x : GodelTTerm S n ρ) :
    (GodelTTerm.app (GodelTTerm.app (GodelTTerm.app
      (GodelTTerm.S_comb (n := n) ρ σ τ) f) g) x).bracketLevel 1
    ≥ (GodelTTerm.app (GodelTTerm.app f x)
      (GodelTTerm.app g x)).bracketLevel 1
    + max ((GodelTTerm.app f x).bracketLevel 1)
        ((GodelTTerm.app g x).bracketLevel 1) + 1 := _
```

* [ ] **Step 2: Add the scaffolding plus a Sat-level-2 fact**

```lean
  := by
  set Sat := GodelTTerm.S_comb (S := S) (n := n) ρ σ τ
    with hSat_def
  set appSf := GodelTTerm.app Sat f with happSf_def
  set appSfg := GodelTTerm.app appSf g with happSfg_def
  set LHS := GodelTTerm.app appSfg x with hLHS_def
  set appfx := GodelTTerm.app f x with happfx_def
  set appgx := GodelTTerm.app g x with happgx_def
  set RHS := GodelTTerm.app appfx appgx with hRHS_def
  have hSatNI : Sat.isIterHead = false := rfl
  have happSfNI : appSf.isIterHead = false := rfl
  have happSfgNI : appSfg.isIterHead = false := rfl
  have happfxNI : appfx.isIterHead = false := rfl
  have happgxNI : appgx.isIterHead = false := rfl
  have hSat1 : Sat.bracketLevel 1 = 1 := by
    rw [hSat_def, GodelTTerm.bracketLevel_S_comb]
    rw [if_pos]
    change 1 ≤ max ((GodelTType.arrow ρ (.arrow σ τ)).level + 1)
      (max ((GodelTType.arrow ρ σ).level + 1)
        (max (ρ.level + 1) τ.level))
    omega
  have hSat2 : Sat.bracketLevel 2 = 1 := by
    rw [hSat_def, GodelTTerm.bracketLevel_S_comb]
    rw [if_pos]
    change 2 ≤ max ((GodelTType.arrow ρ (.arrow σ τ)).level + 1)
      (max ((GodelTType.arrow ρ σ).level + 1)
        (max (ρ.level + 1) τ.level))
    omega
  sorry
```

* [ ] **Step 3: Four-case split as in Task 7**

Each case follows the same scaffolding.  KI3 specifically
requires showing that the `2^...` exponent on LHS_1 dominates
RHS_1's exponent by enough margin to cover the `+1` plus the
`max`.  At level 2:

* `[appSf]_2 ≥ 1 + [f]_2` from `bracketLevel_app_eq` plus
  `hSat2 = 1`.  When `[appSf]_2 ≥ 2`, the doubling gives the
  extra `+1`.

The `+1` slack source: at level 2, `[appSf]_2 ≥ 2`.  Then
`2 ^ [appSfg]_1 ≥ 2 ^ ([appSf]_1 + [g]_1) ≥ 2 ^ [appSf]_1 ≥ 2 ^ 2`,
which provides factor 4 — more than enough to cover `+1` and
the `max` term.

The exact algebra is similar to Tasks 7 and 8.

* [ ] **Step 4: Build clean and run tests**

* [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.4.5 (Section B.3): redS_x_coef_bound (KI3)

Level-1 strict-by-1 inequality for the [x]_0 coefficient.
Slack derived from [Sat]_2 = 1 producing factor ≥ 2 in
[appSf]_2, hence factor ≥ 4 in [appSfg]_1, exceeding the +1
and the max term.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Section C: outstanding majorization theorems

### Task 10: `majorizes_redS`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — append after
  Task 9.

**Approach:** Apply the three coefficient bounds B1, B2, B3.
At level 0, expand both sides via `bracketLevel_app_eq` once.
Match coefficients term-by-term per the strategy doc:

```text
[LHS]_0 = 2^([LHS]_1 + [appSfg]_1 + [appSf]_1) * (1 + [f]_0)
       + 2^([LHS]_1 + [appSfg]_1) * [g]_0
       + 2^[LHS]_1 * [x]_0
[RHS]_0 = 2^([RHS]_1 + [appfx]_1) * [f]_0
       + 2^([RHS]_1 + [appfx]_1) * [x]_0
       + 2^([RHS]_1 + [appgx]_1) * [g]_0
       + 2^([RHS]_1 + [appgx]_1) * [x]_0
```

Apply B1 to `[f]_0` coefficient, B2 to `[g]_0`, B3 to `[x]_0`,
and the `2^(..) * 1` slack from `[Sat]_0 = 1` carries the
strict gap.

Monotone-at-`i` for `1 ≤ i ≤ τ.level` from `dominates_app`
plus the same coefficient bounds applied at higher levels.

* [ ] **Step 1: Add the signature**

```lean
/-- Beckmann-Weiermann Lemma 11: `S_ρστ f g x ≫ (f x)(g x)`.

The strict-at-0 gap arises from the `[S_comb]_0 = 1`
contribution, which on the LHS gets multiplied by
`2^([LHS]_1 + [appSfg]_1 + [appSf]_1)` and has no RHS
counterpart.  Term-by-term coefficient comparison
(`redS_f_coef_bound`, `redS_g_coef_bound`, `redS_x_coef_bound`)
closes the algebraic identity. -/
theorem GodelTTerm.majorizes_redS {S : Set GodelTBase}
    {n : Nat} (ρ σ τ : GodelTType S)
    (f : GodelTTerm S n (.arrow ρ (.arrow σ τ)))
    (g : GodelTTerm S n (.arrow ρ σ))
    (x : GodelTTerm S n ρ) :
    GodelTTerm.majorizes
      (.app (.app (.app (.S_comb (n := n) ρ σ τ) f) g) x)
      (.app (.app f x) (.app g x)) := _
```

* [ ] **Step 2: Add the standard scaffolding**

(Same `set` + `have hSatNI` block as Task 7 Step 3.)

* [ ] **Step 3: Discharge the strict-at-0 part**

```lean
  refine ⟨?_, ?_⟩
  · -- Strict-at-0.
    -- Expand [LHS]_0 via bracketLevel_app_eq.
    rw [hLHS_def, GodelTTerm.bracketLevel_app_eq appSfg x 0
      (Nat.zero_le _) happSfgNI]
    -- Expand [RHS]_0 similarly.
    rw [hRHS_def, GodelTTerm.bracketLevel_app_eq appfx appgx 0
      (Nat.zero_le _) happfxNI]
    -- Use B1, B2, B3 to compare exponents term by term.
    -- Construct the algebraic argument using the slack.
    sorry
  · sorry
```

* [ ] **Step 4: Iterate on the algebraic discharge.**  This is
the most delicate part of the plan; expect 1-2 hours of
back-and-forth with `lake build` to find the right `omega`-
plus-`Nat.pow_le_pow_*` orchestration.  If stuck, factor out a
private numeric lemma capturing the term-by-term comparison.

* [ ] **Step 5: Discharge the monotone-at-`i` part**

For `1 ≤ i ≤ τ.level` (the `i = 0` case is the strict-at-0
above, which entails `≤`).  Strategy: at each level, the LHS
and RHS each decompose via `bracketLevel_app_eq` (or
pass-through), and the same B1/B2/B3 inequalities apply at the
next level up.  Often `dominates_app` captures the entire
content via straightforward induction on the LHS structure.

If the `dominates_app` route does not close cleanly, fall
back to direct case-split on `i ≤ ρ.level`, `i ≤ σ.level`, etc.

* [ ] **Step 6: Build clean and run tests**

* [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.5 (Theorem 5): majorizes_redS

B-W Lemma 11 strict-decrease for the S combinator.  Term-by-
term coefficient comparison via redS_{f,g,x}_coef_bound; the
strict gap comes from the [S_comb]_0 = 1 slack with no RHS
counterpart.  Monotone-at-i via dominates_app applied at each
level.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

### Task 11: Generalize `majorizes_redTreeIter_node`

**Files:**

* Modify: `GebLean/LawvereGodelTLemma16.lean` — revise the
  existing `majorizes_redTreeIter_node` (line ~2032) to drop
  the `hσ : σ.level = 0` hypothesis.  Strict-at-0 branch
  preserved verbatim.  Monotone-at-`i` branch rewritten.

**Approach:** The current proof uses
`Nat.le_zero.mp (by rwa [hσ] at hi)` to conclude that the
`monotone-at-i` obligation is vacuous when `σ.level = 0`.
Without that hypothesis, the obligation must be discharged for
each `1 ≤ i ≤ σ.level`.  Use `dominates_app` (Section A.3) plus
existing `bracketLevel_app_ge_arg` / `bracketLevel_app_high_ge`
to lift sub-term dominance through the redex's `app` chain.

* [ ] **Step 1: Read the existing
  `majorizes_redTreeIter_node` proof in full**

This sets the context for the rewrite.

* [ ] **Step 2: Drop the `hσ : σ.level = 0` parameter**

Update the signature to:

```lean
theorem GodelTTerm.majorizes_redTreeIter_node
    {S : Set GodelTBase} {n : Nat}
    (hT : GodelTBase.tree ∈ S) (σ : GodelTType S)
    (l r : GodelTTerm S n (.tree hT))
    (a : GodelTTerm S n σ)
    (b : GodelTTerm S n (.arrow σ (.arrow σ σ))) :
    GodelTTerm.majorizes
      (.app (.app (.app (.treeIter (n := n) hT σ)
        (.node hT l r)) a) b)
      (.app (.app b
        (.app (.app (.app (.treeIter (n := n) hT σ) l) a) b))
        (.app (.app (.app (.treeIter (n := n) hT σ) r) a) b)) := _
```

* [ ] **Step 3: Build to view the goal and verify the
  redex shape**

Run: `lake build`.  Confirm the redex matches the expected B-W
treeIter-node rule.

* [ ] **Step 4: Restore the strict-at-0 branch verbatim**

The previous strict-at-0 proof did not rely on the `hσ`
hypothesis (only the monotone branch did), so it transfers
unchanged.  Copy it from the existing proof.

* [ ] **Step 5: Rewrite the monotone-at-`i` branch using
  `dominates_app`**

Outline:

```lean
  · intro i hi
    -- Sub-term dominance: each of the recursive subcalls
    -- (treeIter l), (treeIter r) dominates a smaller bracket
    -- structure than (treeIter (.node l r)).
    -- Use dominates_app to lift this through the outer app
    -- chain.
    sorry
```

The exact form depends on the specific dominances available
from the existing helpers.  Anticipate factoring out one or two
sub-lemmas.

* [ ] **Step 6: Build clean and run tests**

Run: `lake build && lake test`.

* [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereGodelTLemma16.lean
git commit -m "$(cat <<'EOF'
Stage delta.5 (Theorem 4 generalized): majorizes_redTreeIter_node

Drop the sigma.level = 0 hypothesis; close the monotone-at-i
branch using dominates_app from Section A.3.  Strict-at-0
preserved verbatim.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Self-review

* **Spec coverage check.**  All deliverables in the spec map
  to tasks: A1=Task 1; A2=Task 2; A3=Task 3; A4=Task 4;
  A5=Task 5; B1=Task 7; B2=Task 8; B3=Task 9;
  `majorizes_redS`=Task 10; `majorizes_redTreeIter_node`
  generalization=Task 11.  Task 6 is a decision-record only
  (no code).

* **Placeholder scan.**  Every task contains the actual
  signature and proof outline.  The `sorry`s in Tasks 3, 7, 8,
  9, 10, 11 are explicit, in-progress placeholders that the
  later steps within each task replace; they will not be
  present at commit time.  Step 4 of Task 10 explicitly notes
  the algebraic discharge is the most delicate step; that is
  documented uncertainty, not a placeholder.

* **Type / name consistency.**  `dominates`, `dominates_app`,
  `dominates_refl`, `dominates_trans`, `majorizes_imp_dominates`
  used consistently across tasks.  `aux_pow_mul_strict` (Task
  4 helper) reused in Task 5.  `redS_f_coef_bound`,
  `redS_g_coef_bound`, `redS_x_coef_bound` referenced by name
  in Task 10's strategy.

* **Risk acknowledgement.**  Tasks 7, 8, 9 case (0, 1+) and
  similar may need additional sub-lemmas if the four-case
  split is insufficient.  Task 10 Step 4's algebraic
  discharge is acknowledged as the most delicate step.

---

## Execution

After each task's commit, the build is clean and tests pass.
The workstream is at a defensible checkpoint between every
task, so a session interruption mid-plan is safe.

After Task 11 commits, sub-stage delta.4.5 is complete.  Stage
delta.5's remaining work (`Reduces.bracketLevel_le_at` and
`Reduces.bracketLevel_strict`) becomes tractable on top of
the new infrastructure and is tracked separately as task #203.
