# Step 4 — K^sim majorization theorems — Implementation Plan

> **For agentic workers:** Required sub-skill: use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land the K^sim → ER A_n^r majorization theorems
transcribing Tourlakis 2018 §0.1.0.10 — `KMor1.majorize_one`
plus `majorize_by_A_one_iter` for level ≤ 1, `KMor1.majorize`
plus `majorize_by_A_two_iter` for level ≤ 2, and a step-5
bridge lemma `KMor1.majorize_by_componentBound`.  Plus
ER-side `sumCtxER`/`sumCtxERPlusOffset` named composites and
the cross-family translation lemmas (`linearBound_le_A_one_iter`,
γ-chain to A_2^2, `A_one_iter_linear_le_A_two_iter_two`,
`A_one_iter_compose`).  One new module:
`LawvereKSimMajorization.lean`.

**Architecture:** Top-level module sitting between
`LawvereKSimPolynomialBound` (consumed for `KMor1.linearBound`)
and `Utilities/ERAMajorants` (consumed for `A_one_iter`,
`A_two_iter`).  Two K^sim-side `def`s
(`KMor1.majorize_one : KMor1 a → ℕ × ℕ` and
`KMor1.majorize : KMor1 a → ℕ × ℕ`), three K^sim-side
dominance theorems, two ER-side named composites with
interp + dominance helpers, six cross-family Nat lemmas, a
small auxiliary library (`vMax_*`, `tower_*`, `A_one_iter_*`),
and a step-5 bridge lemma.  All math content fixed; spec
§3–§7 have full statements and proof outlines.

**Tech Stack:** Lean 4 + mathlib4.  Build via `lake build`,
test via `lake test`.  Existing infrastructure consumed:

- `KMor1`, `KMor1.level`, `KMor1.interp`, `KMor1.simrecVec`
  (`LawvereKSim.lean`, `LawvereKSimInterp.lean`).
- `KMor1.linearBound`, `KMor1.linearBound_dominates`,
  `Fin.foldr_max_ge` (`LawvereKSimPolynomialBound.lean` —
  `Fin.foldr_max_ge` is currently `private` and needs
  exposure per Task 5).
- `ERMor1.A_one_iter`, `ERMor1.A_two_iter`,
  `interp_A_one_iter`, `interp_A_two_iter`
  (`Utilities/ERAMajorants.lean`).
- `ERMor1.addN`, `ERMor1.natN`, their interp simp lemmas
  (`Utilities/ERArith.lean`).
- `tower`, `tower_mono_right`, `tower_mono_left`,
  `self_le_tower`, `tower_comp`, `le_two_pow_self`
  (`Utilities/Tower.lean`).
- Mathlib: `Nat.log`, `Nat.lt_pow_succ_log_self`,
  `Nat.pow_le_pow_right`, `Nat.pow_add`,
  `Nat.lt_two_pow_self`, `Finset.sup_le`,
  `Finset.le_sup`, `Finset.sup_le_sum`,
  `Fin.sum_univ_castSucc`, `Fin.cons_self_tail`.

**Spec:**
`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`
(approved after 2 rounds of adversarial review;
round 2 reports 0 blockers / 0 majors).

**Master design:**
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
§3.4 (majorization theorem; lines 850–1090) and §3.5 (kToER
componentBound construction; lines 1099–1116).

---

## File structure

**Created (implementation):**

- `GebLean/LawvereKSimMajorization.lean` — top-level module
  with all of step 4's deliverables.

**Created (tests):**

- `GebLeanTests/LawvereKSimMajorization.lean` — Nat-level
  `#guard` witness tests + two `example` proofs invoking
  `majorize_by_A_two_iter`.

**Modified:**

- `GebLean.lean` — register the new module's import.
- `GebLeanTests.lean` — register the new test module.
- `GebLean/LawvereKSimPolynomialBound.lean` — remove the
  `private` modifier on `Fin.foldr_max_ge` (Task 5).

---

## Style and discipline reminders (from steps 1–3)

Each task's code must follow CLAUDE.md:

- Lines ≤ 80 characters.
- Spaces around binary operators in source: write
  `Fin (k + 1)` not `Fin (k+1)`, `(2 ^ k)` not `(2^k)`.
- Every public `def`/`theorem` carries a literature
  reference in its docstring (Tourlakis 2018 §0.1.0.10 for
  the majorization theorem; master design §3.4 / §3.5).
- Use `simp only [...]` not bare `simp [...]`.
- Use `change` not `show` when the goal text differs from
  what Lean has after reduction.
- No `sorry`, `admit`, `Classical`, `noncomputable`,
  `axiom`, or warnings (lakefile sets
  `warningAsError = true`).
- No banned words from CLAUDE.md's list.
- `markdownlint-cli2` clean on any docs touched.

### Import-at-skeleton-creation rule

Add the import to `GebLean.lean` (and the test counterpart
to `GebLeanTests.lean`) the moment you create the skeleton
file, before adding any code.  Verified during the
skeleton task itself (Task 1).

### Forced re-elaboration before commit

After each task that touches a `.lean` file, force
re-elaboration to catch latent linter errors masked by
incremental cache:

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Inspect output for `error:` AND `warning:` lines (the
trailing "Build completed successfully" summary is
unreliable when the module was already cached).

### `#guard` and `example` test discipline

ER-side `#guard` on `(ERMor1.A_two_iter r).interp` for
`r ≥ 1` is intractable per CLAUDE.md memory.  Step 4's
test file uses two patterns:

- **`#guard` for Nat-level witness checks**: assertions
  about `KMor1.majorize_one` / `KMor1.majorize`
  computed-pair values.  Pure Nat arithmetic; no kernel
  reduction of ER terms.
- **`example` for concrete-input dominance**: the
  dominance theorem proves the inequality universally, so
  `example` proofs invoking `majorize_by_A_two_iter f h v`
  at concrete `f`, `v` typecheck without forcing kernel
  evaluation of the tower bound.

### `Fin 1` index convention

Match step 3's convention: use `0` (relying on
`OfNat (Fin 1) 0`) in proof goals and lemma RHSs; use
`(0 : Fin 1)` with explicit type ascription in
constructions where Lean cannot infer the `Fin` from
context.

---

## Task 1 — Module skeleton + `GebLean.lean` & `GebLeanTests.lean` imports

**Files:**

- Create: `GebLean/LawvereKSimMajorization.lean`
- Create: `GebLeanTests/LawvereKSimMajorization.lean`
  (empty test skeleton)
- Modify: `GebLean.lean` (register import)
- Modify: `GebLeanTests.lean` (register test import)

- [ ] **Step 1.1: Create the implementation skeleton**

```lean
import GebLean.LawvereKSim
import GebLean.LawvereKSimPolynomialBound
import GebLean.Utilities.ERAMajorants
import GebLean.Utilities.ERArith
import GebLean.Utilities.Tower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

/-!
# K^sim majorization theorems (Tourlakis 2018 §0.1.0.10)

For every `f : KMor1 a` with `f.level ≤ n` (where `n ≤ 2`),
this module produces a Lean-computable `(r, offset) : ℕ × ℕ`
such that
`∀ v : Fin a → ℕ,
  f.interp v ≤ (ERMor1.A_n_iter r).interp ![vMax v + offset]`.

Three deliverables:

- `KMor1.majorize_one : KMor1 a → f.level ≤ 1 → ℕ × ℕ`
  plus `majorize_by_A_one_iter` (level-≤1 case in A_1).
- `KMor1.majorize : KMor1 a → f.level ≤ 2 → ℕ × ℕ` plus
  `majorize_by_A_two_iter` (level-≤2 case in A_2).
- `KMor1.majorize_by_componentBound` step-5 bridge lemma
  feeding `simultaneousBoundedRec_interp_correct`.

ER-side helpers `sumCtxER`, `sumCtxERPlusOffset` named
composites support the bridge.

See
`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`
and master design §3.4 / §3.5 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
Cross-reference network:
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
-/

namespace GebLean

/-- Maximum of a `Fin a → ℕ` family.  Matches the
`Finset.sup` form returned by
`KMor1.linearBound_dominates`.  Private to this file. -/
private abbrev vMax {a : ℕ} (v : Fin a → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin a)).sup v

end GebLean
```

- [ ] **Step 1.2: Create the test skeleton**

```lean
import GebLean.LawvereKSimMajorization

namespace GebLean

end GebLean
```

- [ ] **Step 1.3: Register the import in `GebLean.lean`**

Open `GebLean.lean`.  Insert the new line in case-insensitive
alphabetical order.  `LawvereKSimMajorization` falls between
`LawvereKSimInterp` and `LawvereKSimPolynomialBound`.  Add:

```lean
import GebLean.LawvereKSimMajorization
```

- [ ] **Step 1.4: Register the test import in `GebLeanTests.lean`**

Open `GebLeanTests.lean`.  Insert in case-insensitive
alphabetical order alongside the other `LawvereKSim*`
test imports.  Add:

```lean
import GebLeanTests.LawvereKSimMajorization
```

- [ ] **Step 1.5: Verify the empty skeletons build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
rm -f .lake/build/lib/lean/GebLeanTests/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -3
lake build 2>&1 | tail -3
```

Expected: clean build of the empty skeletons (only the
imports, namespace, `vMax` abbrev, and module docstring).

- [ ] **Step 1.6: Commit**

```bash
git add GebLean/LawvereKSimMajorization.lean \
        GebLeanTests/LawvereKSimMajorization.lean \
        GebLean.lean GebLeanTests.lean
git commit -m "Step 4 task 1: LawvereKSimMajorization skeleton + imports

Module skeleton for K^sim majorization theorems
(Tourlakis 2018 §0.1.0.10; master design §3.4 / §3.5).
Per the import-at-skeleton-creation rule, GebLean.lean and
GebLeanTests.lean register the new modules in this same
commit.  Pins the private vMax abbrev matching
KMor1.linearBound_dominates's Finset.sup form."
```

---

## Task 2 — Auxiliary `vMax` lemmas

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`, after the `vMax` abbrev)

- [ ] **Step 2.1: Add `vMax_apply_le`**

```lean
/-- For any `i : Fin a`, the entry `v i` is bounded by
`vMax v`.  One-line `Finset.le_sup`. -/
private theorem vMax_apply_le {a : ℕ} (v : Fin a → ℕ)
    (i : Fin a) : v i ≤ vMax v :=
  Finset.le_sup (s := (Finset.univ : Finset (Fin a)))
    (f := v) (Finset.mem_univ i)
```

- [ ] **Step 2.2: Add `vMax_le_of_pointwise`**

```lean
/-- If every entry is bounded by `M`, so is `vMax v`.
Wraps `Finset.sup_le`. -/
private theorem vMax_le_of_pointwise {a : ℕ}
    (v : Fin a → ℕ) (M : ℕ) (h : ∀ i, v i ≤ M) :
    vMax v ≤ M :=
  Finset.sup_le (fun i _ => h i)
```

- [ ] **Step 2.3: Add `vMax_cons`**

`vMax (Fin.cons n v) = max n (vMax v)` for
`v : Fin a → ℕ`, `n : ℕ`.  Mathlib does not have a direct
lemma matching this signature; prove it manually using
`Finset.sup_le_iff` and `Fin.cases`.

```lean
/-- Maximum-over-cons identity:
`vMax (Fin.cons n v) = max n (vMax v)`. -/
private theorem vMax_cons {a : ℕ} (n : ℕ) (v : Fin a → ℕ) :
    vMax (Fin.cons n v) = max n (vMax v) := by
  apply le_antisymm
  · apply vMax_le_of_pointwise
    intro i
    refine Fin.cases ?_ ?_ i
    · exact le_max_left _ _
    · intro j
      change v j ≤ max n (vMax v)
      exact le_trans (vMax_apply_le v j) (le_max_right _ _)
  · apply max_le
    · change Fin.cons n v 0 ≤ vMax (Fin.cons n v)
      exact vMax_apply_le _ 0
    · apply vMax_le_of_pointwise
      intro j
      change v j ≤ vMax (Fin.cons n v)
      exact le_trans
        (le_of_eq (Fin.cons_succ n v j).symm)
        (vMax_apply_le _ j.succ)
```

(The proof's tactic shape may need minor adjustment based
on mathlib's exact `Fin.cons_succ` / `Fin.cons_zero` naming.
The implementer tries direct mathlib lemmas first; if
naming has shifted, fall back to `Fin.cases` pattern-match
with `decide` / `rfl` on the `0` and `succ j` branches.)

- [ ] **Step 2.4: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 2: vMax auxiliary lemmas

vMax_apply_le, vMax_le_of_pointwise, and vMax_cons.
Used by the dominance theorems (vMax_apply_le for
v 0 ≤ vMax v in the simrec case) and by
simrecVec_le_A_one_iter's induction (vMax_cons for
relating max over Fin.cons-indexed contexts to the
recursion variable + params split)."
```

---

## Task 3 — De-private `Fin.foldr_max_ge` upstream

**Files:**

- Modify: `GebLean/LawvereKSimPolynomialBound.lean` (one
  line: drop the `private` modifier on
  `Fin.foldr_max_ge` at line 302)

- [ ] **Step 3.1: Drop the `private` modifier**

Open `GebLean/LawvereKSimPolynomialBound.lean`.  Find the
declaration at line 302:

```lean
private theorem Fin.foldr_max_ge {n : ℕ}
```

Change to:

```lean
theorem Fin.foldr_max_ge {n : ℕ}
```

Note: `Fin.foldr_max_le` at line 1808 is also `private` —
leave it alone for now (step 4's `KMor1.majorize` proofs
don't currently need the reverse direction).

- [ ] **Step 3.2: Verify the broader build still passes**

```bash
lake build 2>&1 | tail -10
```

Expected: clean rebuild of the polynomial-bound module
and downstream modules; `Fin.foldr_max_ge` becomes
publicly visible.

- [ ] **Step 3.3: Commit**

```bash
git add GebLean/LawvereKSimPolynomialBound.lean
git commit -m "Step 4 task 3: expose Fin.foldr_max_ge

Strip the private modifier from Fin.foldr_max_ge in
LawvereKSimPolynomialBound.lean.  Step 4's
KMor1.majorize comp / simrec cases consume the lemma
to project per-child majorize values into the
foldr-max bound; the lemma's body is unchanged."
```

---

## Task 4 — `ERMor1.sumCtxER` named composite

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside an `ERMor1` namespace block — open a fresh
  `namespace GebLean.ERMor1` block)

- [ ] **Step 4.1: Define `ERMor1.sumCtxER`**

```lean
namespace ERMor1

/-- n-ary sum of the context: `(sumCtxER n).interp v
= ∑ i, v i`.  Master design §3.5 (kToER simrec
componentBound construction).  Built bottom-up by
recursion on `n` from the binary `addN`. -/
def sumCtxER : (n : ℕ) → ERMor1 n
  | 0     => ERMor1.zeroN 0
  | n + 1 =>
      ERMor1.comp ERMor1.addN fun i => match i with
        | ⟨0, _⟩ => ERMor1.proj (Fin.last n)
        | ⟨1, _⟩ => ERMor1.comp (sumCtxER n)
                      (fun j : Fin n =>
                        ERMor1.proj (Fin.castSucc j))

end ERMor1
```

- [ ] **Step 4.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 4: ERMor1.sumCtxER definition

n-ary sum of the input context, built bottom-up from
addN.  Master design §3.5 lines 1108-1113.  At n = 0
the empty sum is zeroN 0; at n + 1 it splits into
proj (Fin.last n) plus the recursive sum over
Fin.castSucc-shifted entries."
```

---

## Task 5 — `interp_sumCtxER` `@[simp]` theorem

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace ERMor1`)

- [ ] **Step 5.1: State and prove `interp_sumCtxER`**

```lean
namespace ERMor1

/-- Closed-form interpretation of `sumCtxER`:
`(sumCtxER n).interp v = ∑ i, v i`.  Master design §3.5. -/
@[simp] theorem interp_sumCtxER (n : ℕ) (v : Fin n → ℕ) :
    (sumCtxER n).interp v = ∑ i, v i := by
  induction n with
  | zero =>
      simp only [sumCtxER, ERMor1.interp_zeroN,
        Fin.sum_univ_zero]
  | succ n ih =>
      simp only [sumCtxER, ERMor1.interp_comp,
        ERMor1.interp_addN, ERMor1.interp_proj,
        Fin.isValue]
      rw [ih]
      rw [Fin.sum_univ_castSucc]
      ring

end ERMor1
```

(The proof's exact rewrite chain may need adjusting based
on mathlib's `Fin.sum_univ_castSucc` shape; the
implementer should test in incremental builds and try
alternative rewrites — `Finset.sum_insert`, `Fin.sum_succ`,
or manual `Fin.cases` — if the listed simp set leaves
residual goals.  `ring` at the end closes the `+`-shuffle.)

- [ ] **Step 5.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 5: interp_sumCtxER closed-form simp lemma

Master design §3.5.  Induction on n:
- Base: zeroN 0.interp _ = 0 = empty Fin.sum.
- Step: addN(proj last, sumCtxER n ∘ castSucc).interp v
  = v (Fin.last n) + ∑ Fin.castSucc, matching
  Fin.sum_univ_castSucc."
```

---

## Task 6 — `vMax_le_sumCtxER` dominance helper

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace ERMor1`)

- [ ] **Step 6.1: State and prove `vMax_le_sumCtxER`**

```lean
namespace ERMor1

/-- Sum dominates max: `vMax v ≤ (sumCtxER n).interp v`.
Used by the step-5 bridge lemma to discharge the dominance
hypothesis for `simultaneousBoundedRec`. -/
theorem vMax_le_sumCtxER {n : ℕ} (v : Fin n → ℕ) :
    (Finset.univ : Finset (Fin n)).sup v ≤
      (sumCtxER n).interp v := by
  rw [interp_sumCtxER]
  exact Finset.sup_le_sum (fun i _ => Nat.zero_le _)

end ERMor1
```

(If `Finset.sup_le_sum` has a different exact name in the
current mathlib, the implementer searches via `loogle` for
`Finset.sup _ ≤ Finset.sum` patterns; the lemma is
standard for `OrderedAddCommMonoid` Nat values.)

- [ ] **Step 6.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 6: vMax_le_sumCtxER dominance helper

For non-negative ℕ-valued families on Fin n,
the maximum is bounded by the sum.  Routes through
interp_sumCtxER plus mathlib's Finset.sup_le_sum.
Master design §3.5."
```

---

## Task 7 — `ERMor1.sumCtxERPlusOffset` + interp + dominance

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace ERMor1`)

- [ ] **Step 7.1: Define `sumCtxERPlusOffset`**

```lean
namespace ERMor1

/-- n-ary sum plus a constant offset:
`(sumCtxERPlusOffset n offset).interp v
  = (∑ i, v i) + offset`.
Master design §3.5 lines 1108-1113.  Step-5 plug-in for
`simultaneousBoundedRec`'s componentBound slot. -/
def sumCtxERPlusOffset (n offset : ℕ) : ERMor1 n :=
  ERMor1.comp ERMor1.addN fun i => match i with
    | ⟨0, _⟩ => sumCtxER n
    | ⟨1, _⟩ => ERMor1.natN n offset

end ERMor1
```

- [ ] **Step 7.2: Add `interp_sumCtxERPlusOffset`**

```lean
namespace ERMor1

/-- Closed-form interpretation:
`(sumCtxERPlusOffset n offset).interp v
  = (∑ i, v i) + offset`.  Master design §3.5. -/
@[simp] theorem interp_sumCtxERPlusOffset
    (n offset : ℕ) (v : Fin n → ℕ) :
    (sumCtxERPlusOffset n offset).interp v
      = (∑ i, v i) + offset := by
  unfold sumCtxERPlusOffset
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_natN, interp_sumCtxER, Fin.isValue]

end ERMor1
```

- [ ] **Step 7.3: Add `vMax_add_offset_le_sumCtxERPlusOffset`**

```lean
namespace ERMor1

/-- Sum-plus-offset dominates `vMax v + offset`. -/
theorem vMax_add_offset_le_sumCtxERPlusOffset
    {n : ℕ} (offset : ℕ) (v : Fin n → ℕ) :
    (Finset.univ : Finset (Fin n)).sup v + offset
      ≤ (sumCtxERPlusOffset n offset).interp v := by
  rw [interp_sumCtxERPlusOffset]
  exact Nat.add_le_add_right (vMax_le_sumCtxER v) offset

end ERMor1
```

- [ ] **Step 7.4: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 7: sumCtxERPlusOffset + interp + dominance

Adds offset to sumCtxER via addN(sumCtxER, natN offset).
interp_sumCtxERPlusOffset gives the closed form
(∑ v i) + offset; vMax_add_offset_le_sumCtxERPlusOffset
chains vMax_le_sumCtxER through Nat.add_le_add_right.
Master design §3.5 lines 1108-1113."
```

---

## Task 8 — `tower_add_offset_le` and `tower_compose_offsets`

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`, OUTSIDE `namespace ERMor1`)

- [ ] **Step 8.1: Add `tower_add_offset_le`**

```lean
/-- Adding an offset commutes past a tower (loosely):
`tower b x + d ≤ tower b (x + d)` for all `b, x, d ≥ 0`.
Used by `tower_compose_offsets` to absorb the outer
offset of a `tower a (tower b ... + offset)` shape. -/
private theorem tower_add_offset_le (b x d : ℕ) :
    tower b x + d ≤ tower b (x + d) := by
  induction b with
  | zero => simp [tower_zero]
  | succ b ih =>
      change 2 ^ tower b x + d ≤ 2 ^ tower b (x + d)
      have h_mul : 2 ^ tower b x + d
                     ≤ 2 ^ tower b x * 2 ^ d := by
        rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd; simp
        · have h_pow_ge : 2 ^ d ≥ d + 1 := by
            have := Nat.lt_two_pow_self (n := d)
            omega
          have h_pos : 1 ≤ 2 ^ tower b x :=
            Nat.one_le_pow _ _ (by omega)
          have : 2 ^ tower b x + d
                   ≤ 2 ^ tower b x * (d + 1) := by
            have := Nat.mul_le_mul_left
                      (2 ^ tower b x)
                      (show 1 + d ≤ d + 1 from by omega)
            calc 2 ^ tower b x + d
                ≤ 2 ^ tower b x * 1 + 2 ^ tower b x * d := by
                  have := h_pos
                  nlinarith
              _ = 2 ^ tower b x * (1 + d) := by ring
              _ ≤ 2 ^ tower b x * (d + 1) := by
                  exact Nat.mul_le_mul_left _ (by omega)
          calc 2 ^ tower b x + d
              ≤ 2 ^ tower b x * (d + 1) := this
            _ ≤ 2 ^ tower b x * 2 ^ d := by
                exact Nat.mul_le_mul_left _ h_pow_ge
      calc 2 ^ tower b x + d
          ≤ 2 ^ tower b x * 2 ^ d := h_mul
        _ = 2 ^ (tower b x + d) := by rw [← Nat.pow_add]
        _ ≤ 2 ^ tower b (x + d) :=
            Nat.pow_le_pow_right (by omega) ih
```

(The proof's tactic shape — `nlinarith` vs explicit
`Nat.mul_succ`/`Nat.left_distrib` rewriting — may need
adjustment.  The implementer's fallback if `nlinarith`
fails: explicit `calc` chain via
`Nat.left_distrib` + `Nat.one_mul` + `Nat.add_le_add_left`.)

- [ ] **Step 8.2: Add `tower_compose_offsets`**

```lean
/-- Two-stage tower composition with an outer offset:
`tower a (tower b (x + c) + d) ≤ tower (a + b) (x + c + d)`.
Used in the `comp` case of `majorize_by_A_two_iter` to
telescope two child A_2 bounds. -/
private theorem tower_compose_offsets
    {a b : ℕ} (x c d : ℕ) :
    tower a (tower b (x + c) + d)
      ≤ tower (a + b) (x + c + d) := by
  have h_inner : tower b (x + c) + d
                   ≤ tower b (x + c + d) :=
    tower_add_offset_le b (x + c) d
  have h_outer : tower a (tower b (x + c) + d)
                   ≤ tower a (tower b (x + c + d)) :=
    tower_mono_right a h_inner
  rw [tower_comp] at h_outer
  exact h_outer
```

- [ ] **Step 8.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 8: tower_add_offset_le + tower_compose_offsets

Tower arithmetic auxiliary lemmas.
tower_add_offset_le: tower b x + d ≤ tower b (x + d) by
induction on b plus the multiplicative bound
2^N + d ≤ 2^N · 2^d for N ≥ 0.  tower_compose_offsets
chains it with tower_mono_right and tower_comp to
telescope two-stage tower composition with an outer
offset.  Used in the comp case of
majorize_by_A_two_iter."
```

---

## Task 9 — γ.1 `linearBound_le_A_one_iter`

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 9.1: State and prove `linearBound_le_A_one_iter`**

```lean
/-- Translate a linear bound `c · x + d` into an `A_1^r`
bound, with explicit `r := max (Nat.log 2 (c + 1) + 1)
(Nat.log 2 (d + 2) + 1)`.  Master design §3.4 lines
884-898; Tourlakis 2018 §0.1.0.10. -/
theorem linearBound_le_A_one_iter (c d : ℕ) :
    let r := max (Nat.log 2 (c + 1) + 1)
                 (Nat.log 2 (d + 2) + 1)
    ∀ x, c * x + d ≤ (ERMor1.A_one_iter r).interp ![x] := by
  intro x
  rw [ERMor1.interp_A_one_iter]
  have h_pow_c : c + 1 ≤ 2 ^ (Nat.log 2 (c + 1) + 1) := by
    have h := Nat.lt_pow_succ_log_self
                (b := 2) (by decide) (c + 1)
    omega
  have h_pow_d : d + 2 ≤ 2 ^ (Nat.log 2 (d + 2) + 1) := by
    have h := Nat.lt_pow_succ_log_self
                (b := 2) (by decide) (d + 2)
    omega
  have h_r1 : 2 ^ (Nat.log 2 (c + 1) + 1)
                ≤ 2 ^ (max (Nat.log 2 (c + 1) + 1)
                           (Nat.log 2 (d + 2) + 1)) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h_r2 : 2 ^ (Nat.log 2 (d + 2) + 1)
                ≤ 2 ^ (max (Nat.log 2 (c + 1) + 1)
                           (Nat.log 2 (d + 2) + 1)) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  set r := max (Nat.log 2 (c + 1) + 1)
               (Nat.log 2 (d + 2) + 1)
  have h_c : c ≤ 2 ^ r := by
    calc c ≤ c + 1 := by omega
      _ ≤ 2 ^ (Nat.log 2 (c + 1) + 1) := h_pow_c
      _ ≤ 2 ^ r := h_r1
  have h_d : d + 2 ≤ 2 ^ (r + 1) := by
    calc d + 2 ≤ 2 ^ (Nat.log 2 (d + 2) + 1) := h_pow_d
      _ ≤ 2 ^ r := h_r2
      _ ≤ 2 ^ (r + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  have h_pow_pos : 1 ≤ 2 ^ (r + 1) :=
    Nat.one_le_pow _ _ (by omega)
  show c * x + d ≤ 2 ^ r * (![x] (0 : Fin 1))
                    + (2 ^ (r + 1) - 2)
  simp only [Matrix.cons_val_zero]
  have h_mul : c * x ≤ 2 ^ r * x :=
    Nat.mul_le_mul_right _ h_c
  omega
```

(Tactic shape; the implementer adjusts simp / `show` /
`change` based on the exact `(A_one_iter r).interp ![x]`
unfolding.  Critical sub-lemmas: `Nat.lt_pow_succ_log_self`
gives `n < 2 ^ (Nat.log 2 n + 1)` for `n > 0`; combined
with `c + 1 ≥ 1` and `d + 2 ≥ 2`.)

- [ ] **Step 9.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 9: linearBound_le_A_one_iter (γ.1)

Translation lemma: c * x + d ≤ (A_one_iter r).interp ![x]
with explicit r = max (Nat.log 2 (c+1) + 1)
                       (Nat.log 2 (d+2) + 1).
Master design §3.4 lines 884-898; Tourlakis 2018
§0.1.0.10.  Routes through interp_A_one_iter's closed
form, mathlib's Nat.lt_pow_succ_log_self, and omega."
```

---

## Task 10 — `A_one_iter_le_two_pow_succ` (γ.2)

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 10.1: State and prove `A_one_iter_le_two_pow_succ`**

```lean
/-- γ.2 closed-form bound: `A_1^k(x) ≤ 2^{k+1} · (x + 1)`.
Master design §3.4 lines 1015-1019. -/
theorem A_one_iter_le_two_pow_succ (k x : ℕ) :
    (ERMor1.A_one_iter k).interp ![x]
      ≤ 2 ^ (k + 1) * (x + 1) := by
  rw [ERMor1.interp_A_one_iter]
  show 2 ^ k * (![x] 0) + (2 ^ (k + 1) - 2)
         ≤ 2 ^ (k + 1) * (x + 1)
  simp only [Matrix.cons_val_zero]
  have h_succ : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [Nat.pow_succ]; ring
  have h_pow_pos : 1 ≤ 2 ^ k :=
    Nat.one_le_pow _ _ (by omega)
  omega
```

- [ ] **Step 10.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 10: A_one_iter_le_two_pow_succ (γ.2)

A_1^k(x) ≤ 2^{k+1} · (x + 1) via the closed form
2^k · x + (2^{k+1} - 2) ≤ 2^{k+1} · x + 2^{k+1}.
Master design §3.4 lines 1015-1019."
```

---

## Task 11 — `two_pow_succ_mul_succ_le_tower_two` (γ.3)

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 11.1: State and prove `two_pow_succ_mul_succ_le_tower_two`**

```lean
/-- γ.3 cross-family bound: `2^{k+1} · (x + 1) ≤
tower 2 (x + k + 2)`.  Master design §3.4 lines 1027-1029. -/
theorem two_pow_succ_mul_succ_le_tower_two (k x : ℕ) :
    2 ^ (k + 1) * (x + 1) ≤ tower 2 (x + k + 2) := by
  have h_succ_le : x + 1 ≤ 2 ^ (x + 1) :=
    le_two_pow_self (x + 1)
  have h_step1 : 2 ^ (k + 1) * (x + 1)
                   ≤ 2 ^ (k + 1) * 2 ^ (x + 1) :=
    Nat.mul_le_mul_left _ h_succ_le
  have h_step2 : 2 ^ (k + 1) * 2 ^ (x + 1)
                   = 2 ^ (k + x + 2) := by
    rw [← Nat.pow_add]; ring_nf
  have h_step3 : k + x + 2 ≤ 2 ^ (k + x + 2) :=
    le_two_pow_self _
  have h_step4 : 2 ^ (k + x + 2) ≤ 2 ^ (2 ^ (x + k + 2)) := by
    apply Nat.pow_le_pow_right (by omega)
    have : k + x + 2 = x + k + 2 := by ring
    rw [this]
    exact h_step3
  calc 2 ^ (k + 1) * (x + 1)
      ≤ 2 ^ (k + 1) * 2 ^ (x + 1) := h_step1
    _ = 2 ^ (k + x + 2) := h_step2
    _ ≤ 2 ^ (2 ^ (x + k + 2)) := h_step4
    _ = tower 2 (x + k + 2) := by
        change 2 ^ (2 ^ (x + k + 2))
                 = 2 ^ tower 1 (x + k + 2)
        rw [tower_succ]
        change 2 ^ (2 ^ (x + k + 2))
                 = 2 ^ (2 ^ tower 0 (x + k + 2))
        rw [tower_zero]
```

(The final `tower 2` unfolding may simplify with
`change`/`rfl` or the `tower_succ`/`tower_zero` simp lemmas;
the implementer adjusts based on what builds.  Master
design's chain is preserved up to commutativity.)

- [ ] **Step 11.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 11: two_pow_succ_mul_succ_le_tower_two (γ.3)

2^{k+1} · (x+1) ≤ tower 2 (x + k + 2) via le_two_pow_self
applied at x+1 and at k+x+2 plus pow_add.  Master design
§3.4 lines 1027-1029."
```

---

## Task 12 — `A_one_iter_le_A_two_iter_two` (γ corollary)

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 12.1: State and prove the composed corollary**

```lean
/-- Combined cross-family bound: `A_1^k(x) ≤ A_2^2(x + k + 2)`.
Master design §3.4 lines 1015-1029; Tourlakis 2018
§0.1.0.10.  Used by the `raise` case of
`majorize_by_A_two_iter`. -/
theorem A_one_iter_le_A_two_iter_two (k x : ℕ) :
    (ERMor1.A_one_iter k).interp ![x]
      ≤ (ERMor1.A_two_iter 2).interp ![x + k + 2] := by
  rw [ERMor1.interp_A_two_iter]
  simp only [Matrix.cons_val_zero]
  exact le_trans (A_one_iter_le_two_pow_succ k x)
    (two_pow_succ_mul_succ_le_tower_two k x)
```

- [ ] **Step 12.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 12: A_one_iter_le_A_two_iter_two (γ corollary)

Compose γ.2 (A_one_iter_le_two_pow_succ) and γ.3
(two_pow_succ_mul_succ_le_tower_two) plus
interp_A_two_iter to land A_1^k(x) ≤ A_2^2(x + k + 2).
Used by the raise case of majorize_by_A_two_iter."
```

---

## Task 13 — `A_one_iter_linear_le_A_two_iter_two` (γ.5)

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 13.1: State and prove `A_one_iter_linear_le_A_two_iter_two`**

This is the load-bearing parametric γ-lemma: the level-2
simrec case's exponent depends linearly on the recursion
variable `m`, and master design lines 1027-1029 absorb that
into the additive offset of A_2^2.

```lean
/-- γ.5 parametric cross-family bound: when the A_1
exponent depends linearly on `m`, the result still fits
inside an A_2^2 with constant tower height and additive
offset linear in `r_H, r_G`.  Master design §3.4 lines
1027-1029.  Load-bearing for the level-2 simrec case. -/
theorem A_one_iter_linear_le_A_two_iter_two
    (r_H r_G m : ℕ) :
    (ERMor1.A_one_iter (r_H + m * r_G)).interp ![m]
      ≤ (ERMor1.A_two_iter 2).interp
          ![m + r_H + r_G + 2] := by
  rw [ERMor1.interp_A_two_iter]
  simp only [Matrix.cons_val_zero]
  have h_step_a :
      (ERMor1.A_one_iter (r_H + m * r_G)).interp ![m]
        ≤ 2 ^ (r_H + m * r_G + 1) * (m + 1) :=
    A_one_iter_le_two_pow_succ (r_H + m * r_G) m
  have h_int :
      r_H + m * r_G + 1 ≤ (r_H + r_G + 1) * (m + 1) := by
    nlinarith [Nat.zero_le r_H, Nat.zero_le r_G,
               Nat.zero_le m]
  have h_step_b :
      2 ^ (r_H + m * r_G + 1) * (m + 1)
        ≤ 2 ^ ((r_H + r_G + 1) * (m + 1)) := by
    have h_pow := Nat.pow_le_pow_right
                    (h := show 1 ≤ 2 from by omega) h_int
    have h_succ : m + 1 ≤ 2 ^ (m + 1) :=
      le_two_pow_self (m + 1)
    calc 2 ^ (r_H + m * r_G + 1) * (m + 1)
        ≤ 2 ^ ((r_H + r_G + 1) * (m + 1)) * (m + 1) :=
          Nat.mul_le_mul_right _ h_pow
      _ ≤ 2 ^ ((r_H + r_G + 1) * (m + 1))
          * 2 ^ (m + 1) :=
          Nat.mul_le_mul_left _ h_succ
      _ = 2 ^ ((r_H + r_G + 1) * (m + 1) + (m + 1)) := by
          rw [← Nat.pow_add]
      _ ≤ 2 ^ ((r_H + r_G + 2) * (m + 1)) := by
          apply Nat.pow_le_pow_right (by omega)
          nlinarith
  have h_factor_le :
      r_H + r_G + 2 ≤ 2 ^ (r_H + r_G + 1) := by
    have := le_two_pow_self (r_H + r_G + 1)
    have h_pow_pos : 1 ≤ 2 ^ (r_H + r_G + 1) :=
      Nat.one_le_pow _ _ (by omega)
    omega
  have h_step_c :
      (r_H + r_G + 2) * (m + 1)
        ≤ 2 ^ (r_H + r_G + 1) * 2 ^ (m + 1) := by
    calc (r_H + r_G + 2) * (m + 1)
        ≤ 2 ^ (r_H + r_G + 1) * (m + 1) :=
          Nat.mul_le_mul_right _ h_factor_le
      _ ≤ 2 ^ (r_H + r_G + 1) * 2 ^ (m + 1) :=
          Nat.mul_le_mul_left _
            (le_two_pow_self (m + 1))
  have h_step_d :
      2 ^ (r_H + r_G + 1) * 2 ^ (m + 1)
        = 2 ^ (m + r_H + r_G + 2) := by
    rw [← Nat.pow_add]; ring_nf
  have h_outer :
      2 ^ ((r_H + r_G + 2) * (m + 1))
        ≤ 2 ^ (2 ^ (m + r_H + r_G + 2)) := by
    apply Nat.pow_le_pow_right (by omega)
    calc (r_H + r_G + 2) * (m + 1)
        ≤ 2 ^ (r_H + r_G + 1) * 2 ^ (m + 1) := h_step_c
      _ = 2 ^ (m + r_H + r_G + 2) := h_step_d
  have h_tower :
      2 ^ (2 ^ (m + r_H + r_G + 2))
        = tower 2 (m + r_H + r_G + 2) := by
    change 2 ^ (2 ^ (m + r_H + r_G + 2))
             = 2 ^ tower 1 (m + r_H + r_G + 2)
    rw [tower_succ]
    change 2 ^ (2 ^ (m + r_H + r_G + 2))
             = 2 ^ (2 ^ tower 0 (m + r_H + r_G + 2))
    rw [tower_zero]
  calc (ERMor1.A_one_iter (r_H + m * r_G)).interp ![m]
      ≤ 2 ^ (r_H + m * r_G + 1) * (m + 1) := h_step_a
    _ ≤ 2 ^ ((r_H + r_G + 1) * (m + 1)) := h_step_b
    _ ≤ 2 ^ ((r_H + r_G + 2) * (m + 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        nlinarith
    _ ≤ 2 ^ (2 ^ (m + r_H + r_G + 2)) := h_outer
    _ = tower 2 (m + r_H + r_G + 2) := h_tower
```

(The proof is the largest single block in this cycle.  Per
spec §9.4 + master design lines 1027-1029, the implementer
may break this into 3-5 named sub-lemmas if the combined
block exceeds ~50 lines.  The `h_int` integer inequality
`r_H + m·r_G + 1 ≤ (r_H + r_G + 1)·(m + 1)` should close by
`nlinarith` directly; if not, expand RHS via `ring_nf` and
close by `omega` after introducing positivity hypotheses
on each variable.)

- [ ] **Step 13.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 13: A_one_iter_linear_le_A_two_iter_two (γ.5)

Parametric cross-family bound matching master design lines
1027-1029.  When the A_1 exponent depends linearly on m
(as r_H + m * r_G), the result fits inside A_2^2 with
constant tower height and additive offset r_H + r_G + 2.
This is the load-bearing arithmetic that closes the
level-2 simrec case where the simple
A_one_iter_le_A_two_iter_two corollary fails to absorb
the m-dependent exponent."
```

---

## Task 14 — `A_one_iter_compose`, `self_le_A_one_iter`, `A_one_iter_mono_left`

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 14.1: Add `A_one_iter_compose`**

```lean
/-- `A_one_iter` composes additively in the iteration count:
`A_1^a(A_1^b(x)) = A_1^{a+b}(x)`.  Master design §3.4 lines
994-1007 (used implicitly in the M_n closed-form inductive
proof). -/
theorem A_one_iter_compose (a b x : ℕ) :
    (ERMor1.A_one_iter a).interp
        ![(ERMor1.A_one_iter b).interp ![x]]
      = (ERMor1.A_one_iter (a + b)).interp ![x] := by
  rw [ERMor1.interp_A_one_iter, ERMor1.interp_A_one_iter,
      ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have h_pow_add : 2 ^ (a + b) = 2 ^ a * 2 ^ b := by
    rw [Nat.pow_add]
  have h_pow_succ_a : 2 ^ (a + 1) = 2 * 2 ^ a := by
    rw [Nat.pow_succ]; ring
  have h_pow_succ_b : 2 ^ (b + 1) = 2 * 2 ^ b := by
    rw [Nat.pow_succ]; ring
  have h_pow_succ_ab : 2 ^ (a + b + 1) = 2 * 2 ^ (a + b) := by
    rw [Nat.pow_succ]; ring
  have h_pow_pos_a : 1 ≤ 2 ^ a :=
    Nat.one_le_pow _ _ (by omega)
  have h_pow_pos_b : 1 ≤ 2 ^ b :=
    Nat.one_le_pow _ _ (by omega)
  have h_pow_pos_ab : 1 ≤ 2 ^ (a + b) :=
    Nat.one_le_pow _ _ (by omega)
  ring_nf
  -- residual: a Nat-linear identity in 2^a, 2^b, 2^(a+b),
  -- 2^(a+1), 2^(b+1), 2^(a+b+1), x.  After substituting
  -- via h_pow_add etc, omega closes.
  omega
```

(Tactic shape; if `ring_nf` + `omega` fail, the implementer
falls back to explicit `calc` chain unfolding both sides
to `2^a · 2^b · x + ...`.  Both sides are equal in `ℤ`; in
`ℕ` care needed for the subtraction-truncation argument
via the `1 ≤ 2^*` positivity hypotheses.)

- [ ] **Step 14.2: Add `self_le_A_one_iter`**

```lean
/-- `A_1^k` dominates the identity at every `x`:
`x ≤ (A_one_iter k).interp ![x]`.  Used in §6.2's step
bullet to bound the recursion variable `n` by an
`A_1`-iterate. -/
theorem self_le_A_one_iter (k x : ℕ) :
    x ≤ (ERMor1.A_one_iter k).interp ![x] := by
  rw [ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have h_pow_pos : 1 ≤ 2 ^ k :=
    Nat.one_le_pow _ _ (by omega)
  have h_mul : x ≤ 2 ^ k * x :=
    Nat.le_mul_of_pos_left _ h_pow_pos
  omega
```

- [ ] **Step 14.3: Add `A_one_iter_mono_left`**

```lean
/-- `A_1^k` is monotone in the iteration count for fixed
input.  Used in §6.3's simrec bullet to lift the exponent
from `r_H + (v 0) · r_G` to `r_H + (vMax v) · r_G` before
applying §4.5. -/
theorem A_one_iter_mono_left {k₁ k₂ x : ℕ} (h : k₁ ≤ k₂) :
    (ERMor1.A_one_iter k₁).interp ![x]
      ≤ (ERMor1.A_one_iter k₂).interp ![x] := by
  rw [ERMor1.interp_A_one_iter, ERMor1.interp_A_one_iter]
  simp only [Matrix.cons_val_zero]
  have h_pow_k : 2 ^ k₁ ≤ 2 ^ k₂ :=
    Nat.pow_le_pow_right (by omega) h
  have h_pow_succ : 2 ^ (k₁ + 1) ≤ 2 ^ (k₂ + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h_mul : 2 ^ k₁ * x ≤ 2 ^ k₂ * x :=
    Nat.mul_le_mul_right _ h_pow_k
  have h_pow_pos₁ : 1 ≤ 2 ^ (k₁ + 1) :=
    Nat.one_le_pow _ _ (by omega)
  have h_pow_pos₂ : 1 ≤ 2 ^ (k₂ + 1) :=
    Nat.one_le_pow _ _ (by omega)
  omega
```

- [ ] **Step 14.4: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 14: A_one_iter compose + self_le + mono_left

Three A_one_iter lemmas:
- A_one_iter_compose: A_1^a(A_1^b(x)) = A_1^{a+b}(x)
  via interp_A_one_iter closed-form arithmetic.
- self_le_A_one_iter: x ≤ A_1^k(x) since 2^k ≥ 1.
- A_one_iter_mono_left: monotonicity in iteration count
  for fixed input.
Master design §3.4."
```

---

## Task 15 — `KMor1.majorize_one` def + `majorize_by_A_one_iter`

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 15.1: Define `KMor1.majorize_one`**

```lean
/-- Level-≤1 majorize witness: returns `(r, offset)` such
that `f.interp v ≤ A_1^r (vMax v + offset)`.  Master design
§3.4.  Wrapper around `KMor1.linearBound` plus γ.1.  Offset
is uniformly `0` because γ.1 produces an A_1^r bound with
no input offset. -/
def KMor1.majorize_one : {a : ℕ} → (f : KMor1 a) →
    f.level ≤ 1 → ℕ × ℕ :=
  fun f h =>
    let p := KMor1.linearBound f h
    let r := max (Nat.log 2 (p.1 + 1) + 1)
                 (Nat.log 2 (p.2 + 2) + 1)
    (r, 0)
```

- [ ] **Step 15.2: Prove `KMor1.majorize_by_A_one_iter`**

```lean
/-- Level-≤1 majorization (Tourlakis 2018 §0.1.0.10
restricted to level 1).  Master design §3.4. -/
theorem KMor1.majorize_by_A_one_iter
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1)
    (v : Fin a → ℕ) :
    f.interp v ≤
      (ERMor1.A_one_iter
        (KMor1.majorize_one f h).1).interp
          ![vMax v + (KMor1.majorize_one f h).2] := by
  unfold KMor1.majorize_one
  simp only [Nat.add_zero]
  set p := KMor1.linearBound f h with hp
  have h_dom :
      f.interp v ≤ p.1 * vMax v + p.2 :=
    KMor1.linearBound_dominates f h v
  exact le_trans h_dom (linearBound_le_A_one_iter p.1 p.2 _)
```

- [ ] **Step 15.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 15: KMor1.majorize_one + majorize_by_A_one_iter

majorize_one wraps KMor1.linearBound (existing) plus γ.1's
explicit r formula, returning (r, 0).  Theorem
majorize_by_A_one_iter chains linearBound_dominates with
linearBound_le_A_one_iter.  Master design §3.4
parenthetical at line 933 (level-1 split)."
```

---

## Task 16 — `KMor1.simrecVec_le_A_one_iter`

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

This is the load-bearing iteration arithmetic per spec
§6.2.  The proof is the largest single block in the
cycle; per spec §9.4 the implementer may factor into
sub-lemmas if it grows past ~80 lines.

- [ ] **Step 16.1: State `simrecVec_le_A_one_iter`**

Skeleton with a `_` placeholder for the proof body so the
type signature elaborates first:

```lean
/-- Closed-form bound on simrecVec: every component at
step `n` is dominated by an A_1-iter applied to
`max n (vMax params)`, with iteration count linear in `n`.
Master design §3.4 lines 985-1007 (the M_n closed-form
inductive proof on n).  Tourlakis 2018 §0.1.0.10 proof
of the level-2 case.

The hypotheses are stated with zero offset on the A_1
input — matching the shape `majorize_one` produces. -/
theorem KMor1.simrecVec_le_A_one_iter
    {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hh : ∀ j, (h_fam j).level ≤ 1)
    (hg : ∀ j, (g_fam j).level ≤ 1)
    (r_H r_G : ℕ)
    (hbase : ∀ j x,
      (h_fam j).interp x
        ≤ (ERMor1.A_one_iter r_H).interp ![vMax x])
    (hstep : ∀ j y,
      (g_fam j).interp y
        ≤ (ERMor1.A_one_iter r_G).interp ![vMax y])
    (params : Fin a → ℕ) (n : ℕ) :
    ∀ j,
      KMor1.simrecVec h_fam g_fam params n j
        ≤ (ERMor1.A_one_iter (r_H + n * r_G)).interp
            ![max n (vMax params)] := by
  induction n with
  | zero => _
  | succ n ih => _
```

- [ ] **Step 16.2: Prove the base case (`n = 0`)**

```lean
  | zero =>
      intro j
      simp only [KMor1.simrecVec, Nat.zero_mul,
        Nat.add_zero]
      have h_zero_max : max 0 (vMax params) = vMax params :=
        Nat.zero_max _
      rw [h_zero_max]
      exact hbase j params
```

- [ ] **Step 16.3: Prove the step case (`n + 1`)**

The succ case follows master design lines 999–1007.  Build
up via several `have` blocks:

```lean
  | succ n ih =>
      intro j
      simp only [KMor1.simrecVec]
      -- The step computes (g_fam j).interp at the
      -- concatenated context (counter, params, prev-slots).
      set stepCtx :
          Fin (a + 1 + (k + 1)) → ℕ :=
        fun idx =>
          if h₁ : idx.val < a + 1 then
            if _ : idx.val = 0 then n
            else params ⟨idx.val - 1, by omega⟩
          else
            KMor1.simrecVec h_fam g_fam params n
              ⟨idx.val - (a + 1), by omega⟩
        with hstepCtx
      -- IH bounds the prev-slots; counter and params
      -- bounded by max n (vMax params).
      have h_prev_le_M :
          ∀ j',
            KMor1.simrecVec h_fam g_fam params n j'
              ≤ (ERMor1.A_one_iter (r_H + n * r_G)).interp
                  ![max n (vMax params)] := ih
      -- Set M := max n (vMax params).
      set M := max n (vMax params) with hM
      have h_iterate_M :
          (ERMor1.A_one_iter (r_H + n * r_G)).interp ![M]
            = M.succ.pred + 0 := by sorry
      -- (placeholder: iterate value, not actually needed
      -- as a separate `have` — the bound goes through ih
      -- directly)
      -- Bound vMax stepCtx by an A_1^{r_H + n·r_G} of M.
      have h_stepCtx_bound :
          vMax stepCtx
            ≤ (ERMor1.A_one_iter (r_H + n * r_G)).interp
                ![M] := by
        apply vMax_le_of_pointwise
        intro idx
        unfold_let stepCtx
        by_cases h₁ : idx.val < a + 1
        · simp only [h₁, dite_true]
          by_cases h₂ : idx.val = 0
          · simp only [h₂, dite_true]
            have : n ≤ M := by exact le_max_left _ _
            exact le_trans this
              (self_le_A_one_iter _ _)
          · simp only [h₂, dite_false]
            have : params ⟨idx.val - 1, by omega⟩
                     ≤ vMax params :=
              vMax_apply_le _ _
            have : params ⟨idx.val - 1, by omega⟩ ≤ M :=
              le_trans this (le_max_right _ _)
            exact le_trans this
              (self_le_A_one_iter _ _)
        · simp only [h₁, dite_false]
          exact h_prev_le_M _
      -- Apply hstep at j: (g_fam j).interp stepCtx
      -- ≤ A_1^{r_G}(vMax stepCtx).
      have h_apply_step := hstep j stepCtx
      -- Compose: (g_fam j).interp stepCtx
      -- ≤ A_1^{r_G}(vMax stepCtx)
      -- ≤ A_1^{r_G}(A_1^{r_H + n·r_G}(M))
      -- = A_1^{r_G + (r_H + n·r_G)}(M)
      -- by A_one_iter_mono on the input + A_one_iter_compose.
      sorry
```

Replace each `sorry`/`_` with the actual proof body.  The
key chain after `h_apply_step`:

```text
(g_fam j).interp stepCtx
  ≤ A_1^{r_G}(vMax stepCtx)              (h_apply_step)
  ≤ A_1^{r_G}(A_1^{r_H + n·r_G}(M))      (mono on input,
                                          using
                                          h_stepCtx_bound)
  = A_1^{r_G + (r_H + n·r_G)}(M)         (A_one_iter_compose)
  = A_1^{r_H + (n + 1)·r_G}(M)           (Nat.mul_succ)
  ≤ A_1^{r_H + (n + 1)·r_G}(max (n+1) (vMax params))
                                          (mono on input,
                                          using
                                          M ≤ max (n+1) ...)
```

Each step uses one of the lemmas from Task 14
(`self_le_A_one_iter`, `A_one_iter_compose`,
`A_one_iter_mono_left`) plus monotonicity of `A_1^k` in
its input slot (which is a one-liner `omega` after
`interp_A_one_iter`).

(The implementer should not actually leave `sorry` in the
committed code — the `sorry`s above are scaffolding for
the proof structure.  After dropping them all, the proof
should be ~50-80 lines.  If it grows past 100, factor the
`h_stepCtx_bound` and the post-`hstep` chain into named
private sub-lemmas: `simrecVec_step_input_bound` and
`simrecVec_step_apply`.)

- [ ] **Step 16.4: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings, no `sorry`.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 16: KMor1.simrecVec_le_A_one_iter

Closed-form bound on simrecVec via induction on n,
mirroring master design lines 985-1007.  Base case
trivially from hbase.  Step case bounds vMax of the
concatenated stepCtx (counter, params, prev-slots) by
self_le_A_one_iter and IH, applies hstep, composes via
A_one_iter_compose with the IH iterate.  Tourlakis 2018
§0.1.0.10 proof of the level-2 case."
```

---

## Task 17 — `KMor1.majorize` def

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 17.1: Define `KMor1.majorize`**

```lean
/-- Level-≤2 majorize witness: returns `(r, offset)` such
that `f.interp v ≤ A_2^r (vMax v + offset)`.  Structural
recursion on `f`.  Master design §3.4 lines 916-937.

All atomic cases use uniform `r = 2`: tighter atom-level
`r` would force per-case upcasting at every comp/simrec
node.  The simrec offset matches master design lines
1051-1053 exactly: `r_2 = 2`, `offset_2 = r_H + r_G + 2`. -/
def KMor1.majorize : {a : ℕ} → (f : KMor1 a) →
    f.level ≤ 2 → ℕ × ℕ
  | _, .zero,         _ => (2, 2)
  | _, .succ,         _ => (2, 3)
  | _, .proj _,       _ => (2, 2)
  | _, .comp f gs,    h =>
      have hf  : f.level ≤ 2 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i => by
        unfold KMor1.level at h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          (le_trans (le_max_right _ _) h)
      let p_f  := KMor1.majorize f hf
      let r_g  := Fin.foldr _ (fun i acc =>
                    max acc
                      (KMor1.majorize (gs i) (hgs i)).1) 0
      let o_g  := Fin.foldr _ (fun i acc =>
                    max acc
                      (KMor1.majorize (gs i) (hgs i)).2) 0
      (p_f.1 + r_g, p_f.2 + o_g)
  | _, .raise f,      h =>
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact Nat.le_of_succ_le_succ h
      let p := KMor1.majorize_one f hf
      (2, p.1 + 2)
  | _, .simrec _ h_fam g_fam, hyp =>
      have hh : ∀ j, (h_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_left _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j)) this
      have hg : ∀ j, (g_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_right _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j)) this
      let r_H := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (h_fam j) (hh j)).1) 0
      let r_G := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (g_fam j) (hg j)).1) 0
      (2, r_H + r_G + 2)
```

- [ ] **Step 17.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.  Lean's structural-
recursion checker should accept this pattern (mirroring
`KMor1.linearBound`).  If termination fails, the
implementer adds explicit `termination_by` annotations
matching `linearBound`'s.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 17: KMor1.majorize structural recursion

Level-≤2 majorize witness via structural recursion on f.
Atomic cases uniformly (r := 2, offset := small const).
Comp accumulates p_f.1 + r_g (tower height) and
p_f.2 + o_g (offset).  Raise routes through majorize_one
and γ corollary giving (2, p.1 + 2).  Simrec uses
master design's exact (r_2 := 2, offset_2 := r_H + r_G + 2)
with majorize_one's zero offset on each child eliminating
o_H + o_G accumulation.  Mirrors KMor1.linearBound's
structural-recursion shape."
```

---

## Task 18 — `KMor1.majorize_by_A_two_iter` (atomic + raise cases)

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

The level-≤2 dominance theorem.  Build up by structural
induction on `f`; this task lands the atomic cases
(`zero`, `succ`, `proj`) and the `raise` case in a single
`match`-skeleton with `comp` and `simrec` cases done in
Task 19.

- [ ] **Step 18.1: State `majorize_by_A_two_iter` with full skeleton**

```lean
/-- Level-≤2 majorization (Tourlakis 2018 §0.1.0.10).
Master design §3.4 lines 916-937. -/
theorem KMor1.majorize_by_A_two_iter :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
      (v : Fin a → ℕ),
      f.interp v ≤
        (ERMor1.A_two_iter
          (KMor1.majorize f h).1).interp
            ![vMax v + (KMor1.majorize f h).2]
  | _, .zero,         _, v => by
      simp only [KMor1.majorize, KMor1.interp,
        ERMor1.interp_A_two_iter,
        Matrix.cons_val_zero]
      have h_self : vMax v + 2 ≤ tower 2 (vMax v + 2) :=
        self_le_tower 2 _
      omega
  | _, .succ,         _, v => by
      simp only [KMor1.majorize, KMor1.interp_succ,
        ERMor1.interp_A_two_iter,
        Matrix.cons_val_zero]
      have h_self : vMax v + 3 ≤ tower 2 (vMax v + 3) :=
        self_le_tower 2 _
      have h_v0 : v 0 ≤ vMax v := vMax_apply_le v 0
      omega
  | _, .proj i,       _, v => by
      simp only [KMor1.majorize, KMor1.interp_proj,
        ERMor1.interp_A_two_iter,
        Matrix.cons_val_zero]
      have h_self : vMax v + 2 ≤ tower 2 (vMax v + 2) :=
        self_le_tower 2 _
      have h_vi : v i ≤ vMax v := vMax_apply_le v i
      omega
  | _, .raise f,      h, v => by
      have hf : f.level ≤ 1 := by
        unfold KMor1.level at h
        exact Nat.le_of_succ_le_succ h
      simp only [KMor1.majorize, KMor1.interp_raise]
      set p := KMor1.majorize_one f hf with hp
      have h_dom_one :
          f.interp v ≤
            (ERMor1.A_one_iter p.1).interp ![vMax v + p.2] :=
        KMor1.majorize_by_A_one_iter f hf v
      have h_p2_zero : p.2 = 0 := by
        unfold KMor1.majorize_one at hp
        simp only at hp
        exact congrArg Prod.snd hp.symm |>.trans rfl
        -- (or simply `rfl` if majorize_one's Prod
        -- definitional unfolding goes through)
      rw [h_p2_zero, Nat.add_zero] at h_dom_one
      have h_cross :
          (ERMor1.A_one_iter p.1).interp ![vMax v]
            ≤ (ERMor1.A_two_iter 2).interp
                ![vMax v + p.1 + 2] :=
        A_one_iter_le_A_two_iter_two p.1 (vMax v)
      have h_input_eq :
          vMax v + p.1 + 2 = vMax v + (p.1 + 2) := by ring
      rw [h_input_eq] at h_cross
      exact le_trans h_dom_one h_cross
  | _, .comp f gs,    h, v => sorry  -- Task 19
  | _, .simrec _ h_fam g_fam, hyp, v => sorry  -- Task 19
```

(The `sorry` placeholders in the `comp` and `simrec`
cases are dropped in Task 19.  Lean's pattern-completion
checker will complain about missing cases until both are
filled, so this task does NOT yet build cleanly — Task
18 ends in a temporarily broken state, and Task 19 closes
it.)

Alternative: use `_` instead of `sorry` so the build
fails with "unsolved goals" (which is the expected state
after Task 18) — Lean's error messages remain accurate
about what's left.

- [ ] **Step 18.2: Build (expecting "unsolved goals" on comp/simrec)**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -10
```

Expected: build fails with "unsolved goals" on the `comp`
and `simrec` branches; no other errors or warnings.  This
locks in the atomic / raise proof structure before
moving to the harder cases.

DO NOT commit yet — Task 19 closes the remaining cases.

---

## Task 19 — `KMor1.majorize_by_A_two_iter` (comp + simrec cases)

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean`
  (replace the two `_` placeholders from Task 18)

- [ ] **Step 19.1: Replace the `comp` placeholder**

```lean
  | _, .comp f gs,    h, v => by
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i => by
        unfold KMor1.level at h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          (le_trans (le_max_right _ _) h)
      simp only [KMor1.majorize, KMor1.interp_comp]
      set p_f := KMor1.majorize f hf with hp_f
      set r_g := Fin.foldr _ (fun i acc =>
                   max acc
                     (KMor1.majorize (gs i) (hgs i)).1) 0
        with hr_g
      set o_g := Fin.foldr _ (fun i acc =>
                   max acc
                     (KMor1.majorize (gs i) (hgs i)).2) 0
        with ho_g
      -- Each child is bounded.
      have h_child : ∀ i,
          (gs i).interp v ≤
            (ERMor1.A_two_iter r_g).interp
              ![vMax v + o_g] := fun i => by
        have h_i :=
          KMor1.majorize_by_A_two_iter (gs i) (hgs i) v
        have h_r_le :
            (KMor1.majorize (gs i) (hgs i)).1 ≤ r_g :=
          Fin.foldr_max_ge _ i
        have h_o_le :
            (KMor1.majorize (gs i) (hgs i)).2 ≤ o_g :=
          Fin.foldr_max_ge _ i
        rw [ERMor1.interp_A_two_iter] at h_i ⊢
        simp only [Matrix.cons_val_zero] at h_i ⊢
        calc (gs i).interp v
            ≤ tower (KMor1.majorize (gs i) (hgs i)).1
                (vMax v + (KMor1.majorize (gs i) (hgs i)).2) :=
              h_i
          _ ≤ tower r_g
                (vMax v + (KMor1.majorize (gs i) (hgs i)).2) :=
              tower_mono_left h_r_le _
          _ ≤ tower r_g (vMax v + o_g) := by
              exact tower_mono_right r_g (by omega)
      -- Bound vMax of the composed result.
      have h_compose_max :
          vMax (fun i => (gs i).interp v) ≤
            (ERMor1.A_two_iter r_g).interp
              ![vMax v + o_g] := by
        apply vMax_le_of_pointwise
        intro i
        exact h_child i
      -- Apply IH to f at the composed context.
      have h_outer :=
        KMor1.majorize_by_A_two_iter f hf
          (fun i => (gs i).interp v)
      rw [ERMor1.interp_A_two_iter] at h_outer
      simp only [Matrix.cons_val_zero] at h_outer
      -- Compose via tower_compose_offsets.
      rw [ERMor1.interp_A_two_iter, ERMor1.interp_A_two_iter]
        at h_compose_max
      simp only [Matrix.cons_val_zero] at h_compose_max
      rw [ERMor1.interp_A_two_iter]
      simp only [Matrix.cons_val_zero]
      calc f.interp (fun i => (gs i).interp v)
          ≤ tower p_f.1 (vMax (fun i => (gs i).interp v)
                          + p_f.2) := h_outer
        _ ≤ tower p_f.1 (tower r_g (vMax v + o_g)
                          + p_f.2) := by
            apply tower_mono_right
            exact Nat.add_le_add_right h_compose_max _
        _ ≤ tower (p_f.1 + r_g) (vMax v + o_g + p_f.2) :=
            tower_compose_offsets _ _ _
        _ = tower (p_f.1 + r_g)
              (vMax v + (p_f.2 + o_g)) := by
            congr 1; ring
```

- [ ] **Step 19.2: Replace the `simrec` placeholder**

```lean
  | _, .simrec i h_fam g_fam, hyp, v => by
      have hh : ∀ j, (h_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_left _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (h_fam l).level)
            (Finset.mem_univ j)) this
      have hg : ∀ j, (g_fam j).level ≤ 1 := by
        unfold KMor1.level at hyp
        intro j
        have := le_trans (le_max_right _ _)
          (Nat.le_of_succ_le_succ hyp)
        exact le_trans
          (Finset.le_sup
            (f := fun l => (g_fam l).level)
            (Finset.mem_univ j)) this
      simp only [KMor1.majorize, KMor1.interp_simrec]
      set r_H := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (h_fam j) (hh j)).1) 0
        with hr_H
      set r_G := Fin.foldr _ (fun j acc =>
                   max acc
                     (KMor1.majorize_one (g_fam j) (hg j)).1) 0
        with hr_G
      -- Per-child A_1 bounds (with offset 0 since
      -- majorize_one returns (·, 0)).
      have h_base : ∀ j x,
          (h_fam j).interp x
            ≤ (ERMor1.A_one_iter r_H).interp ![vMax x] := by
        intro j x
        have h_dom :=
          KMor1.majorize_by_A_one_iter (h_fam j) (hh j) x
        have h_r_le :
            (KMor1.majorize_one (h_fam j) (hh j)).1 ≤ r_H :=
          Fin.foldr_max_ge _ j
        have h_offset_zero :
            (KMor1.majorize_one (h_fam j) (hh j)).2 = 0 := by
          unfold KMor1.majorize_one
          rfl
        rw [h_offset_zero, Nat.add_zero] at h_dom
        exact le_trans h_dom
          (A_one_iter_mono_left h_r_le)
      have h_step : ∀ j y,
          (g_fam j).interp y
            ≤ (ERMor1.A_one_iter r_G).interp ![vMax y] := by
        intro j y
        have h_dom :=
          KMor1.majorize_by_A_one_iter (g_fam j) (hg j) y
        have h_r_le :
            (KMor1.majorize_one (g_fam j) (hg j)).1 ≤ r_G :=
          Fin.foldr_max_ge _ j
        have h_offset_zero :
            (KMor1.majorize_one (g_fam j) (hg j)).2 = 0 := by
          unfold KMor1.majorize_one
          rfl
        rw [h_offset_zero, Nat.add_zero] at h_dom
        exact le_trans h_dom
          (A_one_iter_mono_left h_r_le)
      -- Apply simrecVec_le_A_one_iter at n := v 0,
      -- params := Fin.tail v.
      have h_simrec_bound :=
        KMor1.simrecVec_le_A_one_iter
          h_fam g_fam hh hg r_H r_G
          h_base h_step (Fin.tail v) (v 0) i
      -- Rewrite max (v 0) (vMax (Fin.tail v)) as vMax v.
      have h_cons_v : v = Fin.cons (v 0) (Fin.tail v) :=
        (Fin.cons_self_tail v).symm
      have h_max_eq :
          max (v 0) (vMax (Fin.tail v)) = vMax v := by
        conv_rhs => rw [h_cons_v]
        rw [vMax_cons]
      rw [h_max_eq] at h_simrec_bound
      -- Lift exponent: r_H + (v 0) * r_G ≤ r_H + vMax v * r_G.
      have h_v0 : v 0 ≤ vMax v := vMax_apply_le v 0
      have h_exp_le :
          r_H + (v 0) * r_G ≤ r_H + vMax v * r_G :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_right _ h_v0) _
      have h_lift :
          (ERMor1.A_one_iter (r_H + (v 0) * r_G)).interp
              ![vMax v]
            ≤ (ERMor1.A_one_iter (r_H + vMax v * r_G)).interp
                ![vMax v] :=
        A_one_iter_mono_left h_exp_le
      -- Apply γ.5 at m := vMax v.
      have h_gamma :=
        A_one_iter_linear_le_A_two_iter_two
          r_H r_G (vMax v)
      rw [ERMor1.interp_A_two_iter]
      simp only [Matrix.cons_val_zero]
      rw [ERMor1.interp_A_two_iter] at h_gamma
      simp only [Matrix.cons_val_zero] at h_gamma
      calc KMor1.simrecVec h_fam g_fam (Fin.tail v) (v 0) i
          ≤ (ERMor1.A_one_iter (r_H + (v 0) * r_G)).interp
              ![vMax v] := h_simrec_bound
        _ ≤ (ERMor1.A_one_iter (r_H + vMax v * r_G)).interp
              ![vMax v] := h_lift
        _ ≤ tower 2 (vMax v + r_H + r_G + 2) := h_gamma
        _ = tower 2 (vMax v + (r_H + r_G + 2)) := by
            congr 1; ring
```

- [ ] **Step 19.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings, no `sorry`.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 tasks 18+19: KMor1.majorize_by_A_two_iter

Level-≤2 dominance theorem via structural induction.
- Atomic cases (zero, succ, proj): self_le_tower at r=2.
- Raise: majorize_by_A_one_iter + γ corollary
  (A_one_iter_le_A_two_iter_two).
- Comp: tower_compose_offsets telescopes child A_2
  bounds with the outer A_2 bound.
- Simrec: simrecVec_le_A_one_iter (Task 16) plus γ.5
  (A_one_iter_linear_le_A_two_iter_two) plus
  A_one_iter_mono_left for the v 0 ≤ vMax v exponent
  lift.
Master design §3.4 lines 916-937; Tourlakis 2018
§0.1.0.10."
```

---

## Task 20 — `KMor1.majorize_by_componentBound` step-5 bridge

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (append
  inside `namespace GebLean`)

- [ ] **Step 20.1: State and prove the bridge lemma**

```lean
/-- Step-5 plug-in: combines `majorize_by_A_two_iter` with
`sumCtxERPlusOffset` to produce the dominance hypothesis
shape that
`ERMor1.simultaneousBoundedRec_interp_correct` consumes.
Master design §3.5 lines 1099-1116. -/
theorem KMor1.majorize_by_componentBound
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
    (v : Fin a → ℕ) :
    let p := KMor1.majorize f h
    f.interp v ≤
      (ERMor1.comp (ERMor1.A_two_iter p.1)
        (fun _ : Fin 1 =>
          ERMor1.sumCtxERPlusOffset a p.2)).interp v := by
  set p := KMor1.majorize f h with hp
  have h_dom :
      f.interp v ≤
        (ERMor1.A_two_iter p.1).interp ![vMax v + p.2] :=
    KMor1.majorize_by_A_two_iter f h v
  rw [ERMor1.interp_A_two_iter] at h_dom
  simp only [Matrix.cons_val_zero] at h_dom
  -- The ERMor1.comp call has interp = (A_two_iter p.1)
  -- applied to (fun _ : Fin 1 => sumCtxERPlusOffset.interp v).
  -- After interp_comp + interp_sumCtxERPlusOffset, the
  -- inner `fun _ : Fin 1 => ...` is pointwise constant
  -- with value (∑ v i) + p.2.
  rw [ERMor1.interp_comp]
  rw [ERMor1.interp_A_two_iter]
  simp only [ERMor1.interp_sumCtxERPlusOffset, Fin.isValue,
    Matrix.cons_val_zero]
  have h_sum_dom :
      vMax v + p.2 ≤ (∑ i : Fin a, v i) + p.2 :=
    Nat.add_le_add_right (ERMor1.vMax_le_sumCtxER v) _
  exact le_trans h_dom (tower_mono_right p.1 h_sum_dom)
```

(The `simp only` invocation reduces the
`fun _ : Fin 1 => ...` family pointwise; the implementer
may need `funext` or an explicit `change` step if `simp`
leaves residual `Fin 1`-indexing artifacts.)

- [ ] **Step 20.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereKSimMajorization.olean
lake build GebLean.LawvereKSimMajorization 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "Step 4 task 20: KMor1.majorize_by_componentBound

Step-5 bridge lemma combining majorize_by_A_two_iter with
sumCtxERPlusOffset.  RHS unfolds via interp_comp +
interp_A_two_iter + interp_sumCtxERPlusOffset to
tower (majorize.1) ((∑ v i) + majorize.2).  LHS bounded
by tower (majorize.1) (vMax v + majorize.2) plus
vMax_le_sumCtxER monotonicity.  Master design §3.5
lines 1099-1116."
```

---

## Task 21 — Test module: witness `#guard`s + `example` proofs

**Files:**

- Modify: `GebLeanTests/LawvereKSimMajorization.lean`
  (replace empty skeleton with full content)

- [ ] **Step 21.1: Write the test content**

```lean
import GebLean.LawvereKSimMajorization

namespace GebLean

/-- Level-1 simrec witness used in tests.
addK = simrec_0 base=proj 0 step=succ(prev). -/
private def addK : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 0) ⟨0, by decide⟩
    (fun _ => KMor1.proj 0)
    (fun _ => KMor1.comp KMor1.succ
                fun _ : Fin 1 =>
                  KMor1.proj ⟨2, by decide⟩)

example : addK.level ≤ 1 := by decide
example : addK.level = 1 := by decide

-- Atomic majorize_one witnesses: offset = 0.
#guard (KMor1.majorize_one (KMor1.zero (n := 1))
          (by decide)).2 = 0
#guard (KMor1.majorize_one (KMor1.proj (0 : Fin 2))
          (by decide)).2 = 0
#guard (KMor1.majorize_one KMor1.succ (by decide)).2 = 0

-- addK exercises level-1 simrec: r positive.
#guard (KMor1.majorize_one addK (by decide)).1 ≥ 1
#guard (KMor1.majorize_one addK (by decide)).2 = 0

-- Atomic majorize witnesses: r = 2 uniform.
#guard (KMor1.majorize (KMor1.zero (n := 1))
          (by decide)).1 = 2
#guard (KMor1.majorize KMor1.succ (by decide)).1 = 2
#guard (KMor1.majorize (KMor1.proj (0 : Fin 2))
          (by decide)).1 = 2

-- addK exercises level-1 path through KMor1.majorize's
-- raise / structural branches; r still 2.
#guard (KMor1.majorize addK (by decide)).1 = 2

-- Concrete-input dominance via the proven theorem.
-- These bypass kernel reduction of A_two_iter's expER
-- tree (intractable per CLAUDE.md memory) by invoking
-- the universal theorem at concrete inputs.

example : addK.interp ![1, 1] ≤
    (ERMor1.A_two_iter
      (KMor1.majorize addK (by decide)).1).interp
        ![(Finset.univ : Finset (Fin 2)).sup
            (![1, 1] : Fin 2 → ℕ)
          + (KMor1.majorize addK (by decide)).2] :=
  KMor1.majorize_by_A_two_iter addK (by decide) ![1, 1]

example : KMor1.succ.interp ![3] ≤
    (ERMor1.A_two_iter
      (KMor1.majorize KMor1.succ (by decide)).1).interp
        ![(Finset.univ : Finset (Fin 1)).sup
            (![3] : Fin 1 → ℕ)
          + (KMor1.majorize KMor1.succ (by decide)).2] :=
  KMor1.majorize_by_A_two_iter KMor1.succ (by decide) ![3]

end GebLean
```

(The `vMax` private abbrev is not exported, so the test
module spells out `Finset.univ.sup` directly.  This
matches the way `KMor1.linearBound_dominates`'s tests
work.)

- [ ] **Step 21.2: Build and run tests**

```bash
rm -f .lake/build/lib/lean/GebLeanTests/LawvereKSimMajorization.olean
lake build GebLeanTests.LawvereKSimMajorization 2>&1 | tail -5
lake test 2>&1 | tail -10
```

Expected: clean build of the test module; all `#guard`s
pass; both `example` proofs typecheck.

- [ ] **Step 21.3: Commit**

```bash
git add GebLeanTests/LawvereKSimMajorization.lean
git commit -m "Step 4 task 21: tests for majorize witnesses + dominance

Witness #guards lock in the (r, offset) shapes:
- majorize_one: offset = 0 uniformly.
- majorize: r = 2 uniformly.
- addK exercises level-1 simrec via majorize_one and
  level-1-via-structural-recursion via majorize.

example proofs verify dominance closure at concrete
inputs by direct application of majorize_by_A_two_iter,
bypassing kernel reduction of A_two_iter's expER tree."
```

---

## Task 22 — Final verification + workstream update

**Files:**

- Modify: `.session/workstreams/er-ksim2-equiv-via-urm.md`

- [ ] **Step 22.1: Run a clean rebuild + test pass**

```bash
lake build 2>&1 | tail -5
lake test 2>&1 | tail -10
```

Expected: full rebuild + test pass with no warnings, no
`sorry`, no `admit`.

- [ ] **Step 22.2: Markdown lint check**

```bash
markdownlint-cli2 \
  docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md \
  docs/superpowers/plans/2026-05-03-step-4-ksim-majorization.md \
  docs/research/2026-05-03-step-4-spec-adversarial-review-round-1.md \
  docs/research/2026-05-03-step-4-spec-adversarial-review-round-2.md \
  2>&1 | tail -10
```

Expected: 0 errors.

- [ ] **Step 22.3: Update workstream session file**

Edit `.session/workstreams/er-ksim2-equiv-via-urm.md`,
appending to the Progress section:

```markdown
- Step 4 (K^sim majorization theorems):
  complete.  Lands `KMor1.majorize_one` /
  `majorize_by_A_one_iter` (level-≤1 in A_1),
  `KMor1.majorize` / `majorize_by_A_two_iter`
  (level-≤2 in A_2), `KMor1.simrecVec_le_A_one_iter`
  (level-2 iteration arithmetic transcribing master
  design lines 985-1007), the cross-family translation
  lemmas (`linearBound_le_A_one_iter`,
  `A_one_iter_le_A_two_iter_two`,
  `A_one_iter_linear_le_A_two_iter_two`,
  `A_one_iter_compose`), ER-side `sumCtxER` /
  `sumCtxERPlusOffset` named composites with closed-form
  interp + dominance helpers, and the step-5 bridge
  lemma `KMor1.majorize_by_componentBound`.  Plan at
  `docs/superpowers/plans/2026-05-03-step-4-ksim-majorization.md`.
  Spec at
  `docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`.
  2 rounds adversarial review on the spec; round 2
  reports clean (0 blockers, 0 majors).

## Next steps

- Step 5: `kToER` structural-induction definition + its
  correctness theorem (master design §3.5).  Uses
  `KMor1.majorize_by_componentBound` as a black box.
```

(Replace the existing "Next steps" section with the new
one.)

- [ ] **Step 22.4: Commit and verify**

```bash
git add .session/workstreams/er-ksim2-equiv-via-urm.md
git commit -m "Step 4 task 22: final verification + workstream update

Full lake build + lake test clean.  All four docs pass
markdownlint-cli2.  Workstream session file updated to
reflect step 4 completion; next steps point at step 5
(kToER definition + functoriality proof, master design
§3.5)."
```

```bash
git log --oneline origin/terence/develop..HEAD
```

Expected: ~22 step-4 commits on top of step 3, all green.

DO NOT push to origin without explicit user authorization.

---

## Self-review

After writing the spec back through this plan one more time:

1. **Spec coverage.**  §1.2 in scope: every entity has a
   task.
   - `vMax` abbrev → Task 1.
   - `vMax_apply_le`, `vMax_le_of_pointwise`, `vMax_cons`
     → Task 2.
   - `Fin.foldr_max_ge` re-export → Task 3.
   - `sumCtxER` def + `interp_sumCtxER` +
     `vMax_le_sumCtxER` → Tasks 4, 5, 6.
   - `sumCtxERPlusOffset` + interp + dominance → Task 7.
   - `tower_add_offset_le`, `tower_compose_offsets` →
     Task 8.
   - `linearBound_le_A_one_iter` → Task 9.
   - `A_one_iter_le_two_pow_succ` (γ.2) → Task 10.
   - `two_pow_succ_mul_succ_le_tower_two` (γ.3) →
     Task 11.
   - `A_one_iter_le_A_two_iter_two` (γ corollary) →
     Task 12.
   - `A_one_iter_linear_le_A_two_iter_two` (γ.5) →
     Task 13.
   - `A_one_iter_compose`, `self_le_A_one_iter`,
     `A_one_iter_mono_left` → Task 14.
   - `KMor1.majorize_one` + `majorize_by_A_one_iter` →
     Task 15.
   - `KMor1.simrecVec_le_A_one_iter` → Task 16.
   - `KMor1.majorize` def → Task 17.
   - `KMor1.majorize_by_A_two_iter` → Tasks 18 + 19.
   - `KMor1.majorize_by_componentBound` → Task 20.
   - Tests → Task 21.
   - Final verification + workstream update → Task 22.

2. **Placeholder scan.**  No "TBD" / "TODO" / "implement
   later".  Tasks 16 and 18-19 use `_` placeholders inside
   the proof body that are explicitly filled in within the
   same task; no inter-task placeholders.

3. **Type consistency.**  `KMor1.majorize` returns
   `ℕ × ℕ` and is consumed via `.1` / `.2` projections in
   Tasks 19, 20, 21.  `KMor1.majorize_one` likewise.  The
   `vMax` abbrev is private to the implementation file;
   tests spell out `Finset.univ.sup` directly (Task 21).
   `sumCtxER` and `sumCtxERPlusOffset` live under
   `namespace ERMor1`; consumed at Task 20 via
   `ERMor1.sumCtxERPlusOffset`.

## Execution handoff

Plan complete and saved to
`docs/superpowers/plans/2026-05-03-step-4-ksim-majorization.md`.

Two execution options:

1. **Subagent-Driven (recommended)** — dispatch a fresh
   subagent per task with two-stage review (spec
   compliance + code quality) for substantive tasks.
2. **Inline Execution** — execute tasks in this session
   using `superpowers:executing-plans` with batch
   checkpoints.
