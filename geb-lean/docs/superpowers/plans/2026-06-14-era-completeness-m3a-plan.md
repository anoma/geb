# Era completeness — M3a engine foundation implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope and staging](#scope-and-staging)
- [File structure](#file-structure)
- [Task 1: The `Finset.sum` bridge for `natBSum`](#task-1-the-finsetsum-bridge-for-natbsum)
- [Task 2: The geometric closed form over `ℕ`](#task-2-the-geometric-closed-form-over-%E2%84%95)
- [Task 3: The geometric sum as an `Era` term](#task-3-the-geometric-sum-as-an-era-term)
- [Deferred to the M3b re-gate](#deferred-to-the-m3b-re-gate)
- [Self-review](#self-review)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the route-independent, search-free foundation of the
bounded-sum engine — the `Finset` bridge for `natBSum` and the geometric
closed-form sum as both an `ℕ` identity and an `Era` term — leaving the
`σ` digit-sum machinery and the counting reduction to the M3b re-gate.

**Architecture:** A new `ℕ`-level utilities module
`GebLean/Utilities/EraBoundedSum.lean` proves `natBSum` equals
`Finset.sum` (unlocking Mathlib's big-operator and `GeomSum` APIs) and
the geometric closed form `Σ_{i<n} q^i = (q^n − 1)/(q − 1)`. The bridge
module `GebLean/EraCompleteness.lean` then realises that closed form as
an `Era` term `eraGeomSum` with its `eval` agreement lemma. No `σ`,
power-weighted sum, or counting work is in scope (M3b gate).

**Tech stack:** Lean 4, Mathlib (`Finset.sum`, `Finset.sum_range_succ`,
`Nat.mul_div_cancel`, `Matrix.cons_val`),
`lake build`/`lake test`/`lake lint`, `scripts/check-axioms.sh`, `jj`.

---

## Scope and staging

The companion spec
(`docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`)
and the construction-choice decision
(`docs/superpowers/notes/2026-06-14-erabsum-construction-decision.md`)
fix the bounded-sum engine to the Marchenkov `σ` route, layered:

1. geometric / power-sum closed forms (search-free),
2. the digit sum `σ = exp₂ C(2x, x)`,
3. the counting reduction (`eraBSum` proper).

Milestone correspondence. In the spec's M-numbering (spec § 9), layers
1–2 are milestone M2 and layer 3 is milestone M3. The "M3a"/"M3b"
labels are session-local sub-divisions introduced by the decision note
and adopted in the planning decision; "M3a" here denotes the
search-free geometric base of spec milestone M2, and the "M3b re-gate"
covers the M2 remainder (power-weighted sums, `σ`) together with spec
milestone M3 (the counting reduction).

The decision note's M3a covers layers 1–2; this plan narrows that scope
further, to the parts that are search-free and route-independent under
the "then re-gate" staging:

- the `Finset` bridge for `natBSum` (every later step uses it);
- the geometric closed form `Σ q^i` (the one sum that closes without a
  bounded search, needed by every layer-3 sub-method).

Deferred to the M3b re-gate (planned after the rich-basis-bypass
assessment): the power-weighted sums `Σ z^i q^z`, the digit sum `σ` as
an `ℕ` identity and as an `Era` term, and the counting reduction that
assembles `eraBSum`. The `σ`-term realisation is deferred deliberately:
it requires `exp₂` (2-adic valuation) and `C(2x, x)` as search-free
`Era` terms, whose constructibility is entangled with the layer-3
method and is the M3b gate's first question.

Each task lands at a sorry-free, axiom-clean, committable state (`sorry`
permitted only between commits, never in a commit). The unit test is the
build plus `scripts/check-axioms.sh`; proof tactics are discovered
interactively during execution, so proof steps state the goal and the
exact lemmas rather than guaranteed-final tactic scripts.

## File structure

- Create: `GebLean/Utilities/EraBoundedSum.lean` — `ℕ`-level lemmas
  about `natBSum`. Responsibility: relate `natBSum` to `Finset.sum` and
  prove the geometric closed form. Imports `GebLean.LawvereER` (for
  `natBSum`) and the specific Mathlib big-operator / geometric-sum
  modules; does not import the heavy number-theory modules (`σ` work is
  out of scope).
- Modify: `GebLean/EraCompleteness.lean` — add `eraGeomSum` and its
  `eval` lemmas, plus `import GebLean.Utilities.EraBoundedSum`.
- Test: assertions live in the modules (the build is the test); no
  separate `GebLeanTests` file is required.

The new utilities module enters the build graph through
`EraCompleteness.lean` (imported by `GebLean.lean`); no separate
registration is needed.

---

## Task 1: The `Finset.sum` bridge for `natBSum`

`natBSum bound f` is `Nat.rec 0 (fun i acc => acc + f i) bound`. Bridge
it to `∑ i ∈ Finset.range bound, f i` so Mathlib's big-operator and
`GeomSum` APIs apply to it.

**Files:**

- Create: `GebLean/Utilities/EraBoundedSum.lean`

- [ ] **Step 1: Create the module with header and namespace**

Mirror the header style of `GebLean/Utilities/ERArith.lean`
(import-first, no copyright header, module docstring with the required
sections). Content:

```lean
import GebLean.LawvereER
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# `natBSum` bridge and geometric closed form

`ℕ`-level lemmas supporting the Era bounded-sum engine
(`GebLean/EraCompleteness.lean`). Relates the recursion-defined
`natBSum` (`GebLean/LawvereER.lean`) to `Finset.sum`, and proves the
geometric closed form `Σ_{i<n} q^i = (q^n − 1)/(q − 1)`.

## Main statements

* `natBSum_eq_sum` — `natBSum bound f = ∑ i ∈ Finset.range bound, f i`.
* `natGeomSum_eq` — the geometric closed form for `2 ≤ q`.

## References

* Marchenkov 2007, § 5 (geometric closed forms).

## Tags

elementary recursive, bounded summation, geometric series
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Build the skeleton**

Run: `lake build GebLean.Utilities.EraBoundedSum`
Expected: builds with no errors (empty namespace).

- [ ] **Step 3: State and prove the bridge lemma**

Add inside the namespace:

```lean
/-- `natBSum` agrees with the `Finset.range` sum. -/
theorem natBSum_eq_sum (bound : ℕ) (f : ℕ → ℕ) :
    natBSum bound f = ∑ i ∈ Finset.range bound, f i := by
  induction bound with
  | zero => simp [natBSum]
  | succ b ih => ?_
```

Strategy: `natBSum (b + 1) f = natBSum b f + f b` holds definitionally
(`Nat.rec` on `succ`; the same `rfl` used by `natBSum_succ` in the
deleted probe), and `Finset.sum_range_succ` gives
`∑ i ∈ range (b + 1), f i = (∑ i ∈ range b, f i) + f b`. Rewrite both
and close with `ih`. Confirm `natBSum (b + 1) f = natBSum b f + f b`
reduces by `rfl` during execution; if the `Nat.rec` unfolding needs
coaxing, introduce it as a local `have hstep : natBSum (b + 1) f =
natBSum b f + f b := rfl` first.

- [ ] **Step 4: Verify**

Run: `lake build GebLean.Utilities.EraBoundedSum && lake lint`
Run: `bash scripts/check-axioms.sh` (expect only `propext`,
`Quot.sound`, `Classical.choice`)
Expected: no errors; `natBSum_eq_sum` sorry-free.

- [ ] **Step 5: Commit**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): bridge natBSum to Finset.sum

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: The geometric closed form over `ℕ`

Prove `Σ_{i<n} q^i = (q^n − 1)/(q − 1)` for `2 ≤ q`. Mathlib's
`geom_sum_mul` is stated over a `Ring`, but `ℕ` is only a semiring
(truncated subtraction), so the multiplication identity is proved
directly by induction and then divided through, rather than reusing the
ring lemma.

**Files:**

- Modify: `GebLean/Utilities/EraBoundedSum.lean`

- [ ] **Step 1: State and prove the geometric multiplication identity**

```lean
/-- `(Σ_{i<n} q^i) * (q - 1) = q ^ n - 1` over `ℕ`, for `1 ≤ q`. -/
theorem natGeomSum_mul (q n : ℕ) (hq : 1 ≤ q) :
    (∑ i ∈ Finset.range n, q ^ i) * (q - 1) = q ^ n - 1 := by
  induction n with
  | zero => simp
  | succ m ih => ?_
```

Strategy: `Finset.sum_range_succ` then distribute; rearrange to an
addition identity (`A * (q - 1) + q^m * (q - 1) = q^(m+1) - 1`) and
discharge with `omega` after introducing the local facts
`have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)` and
`q ^ m ≤ q ^ (m + 1)` via `Nat.pow_le_pow_right` (the verified
load-bearing step; `omega` fails without `h1`). A `ℤ`-cast fallback
(`push_cast`, `geom_sum_mul`) is available but unnecessary.

- [ ] **Step 2: State and prove the closed form**

```lean
/-- Geometric closed form: `Σ_{i<n} q^i = (q^n - 1)/(q - 1)` for
`2 ≤ q`. -/
theorem natGeomSum_eq (q n : ℕ) (hq : 2 ≤ q) :
    ∑ i ∈ Finset.range n, q ^ i = (q ^ n - 1) / (q - 1) := by
  have hpos : 0 < q - 1 := by omega
  rw [← natGeomSum_mul q n (by omega), Nat.mul_div_cancel _ hpos]
```

Strategy: divide `natGeomSum_mul` through by `q - 1`, which is positive
since `2 ≤ q`, using `Nat.mul_div_cancel`. Verify the exact name
(`Nat.mul_div_cancel` vs `Nat.mul_div_cancel_left`) and its argument
order against the goal during execution.

- [ ] **Step 3: State the `natBSum` form**

```lean
/-- The geometric closed form in `natBSum` shape, for `2 ≤ q`. -/
theorem natBSum_geom (q bound : ℕ) (hq : 2 ≤ q) :
    natBSum bound (fun i => q ^ i) = (q ^ bound - 1) / (q - 1) := by
  rw [natBSum_eq_sum]; exact natGeomSum_eq q bound hq
```

- [ ] **Step 4: Verify**

Run: `lake build GebLean.Utilities.EraBoundedSum && lake lint`
Run: `bash scripts/check-axioms.sh` (expect only `propext`,
`Quot.sound`, `Classical.choice`)
Expected: no errors; all three lemmas sorry-free.

- [ ] **Step 5: Commit**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): prove the geometric closed form over the naturals

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 3: The geometric sum as an `Era` term

Realise the closed form `(q^bound − 1)/(q − 1)` as an `Era` term
`eraGeomSum : ETm 2` over `{pow, tsub, div}`, with variable `0` the base
`q` and variable `1` the bound, and prove its `eval` agreement with
`natBSum`.

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

- [ ] **Step 1: Add the utilities import**

Add `import GebLean.Utilities.EraBoundedSum` to the import block of
`GebLean/EraCompleteness.lean` (next to `import GebLean.LawvereER`).

- [ ] **Step 2: Confirm the basis term-formers in scope**

`Era.lean` provides `eadd`, `emod`, `epow2` and the constructors; verify
the exact helper names for `pow`, `tsub`, `div`, and the constant `1`
during execution (search `Era.lean` for `epow`, `etsub`/`esub`, `ediv`,
and the literal-one term). The `app`/`fcons` forms
(`Tm.app .pow (fcons s (fcons t Fin.elim0))`, etc.) are the fallback if
a named helper is absent. The constant `1` is `Tm.succ Tm.zero`.

- [ ] **Step 3: Define the term**

```lean
/-- The geometric bounded sum `Σ_{i<bound} q^i` as a closed `Era` term:
`(q^bound - 1) / (q - 1)`, with variable `0` the base and variable `1`
the bound. -/
def eraGeomSum : ETm 2 :=
  ediv
    (etsub (epow (.var 0) (.var 1)) (.succ .zero))
    (etsub (.var 0) (.succ .zero))
```

(Use whichever named helpers Step 2 confirms; the shape is
`div (sub (pow v0 v1) 1) (sub v0 1)`.)

- [ ] **Step 4: Build to confirm it elaborates**

Run: `lake build GebLean.EraCompleteness`
Expected: builds (total `def`, no `sorry`).

- [ ] **Step 5: State and prove the raw `eval` lemma**

```lean
theorem eraGeomSum_eval (ctx : Fin 2 → ℕ) :
    Tm.eval eraInterp eraGeomSum ctx =
      (ctx 0 ^ ctx 1 - 1) / (ctx 0 - 1) := by
  simp [eraGeomSum, Tm.eval, eraInterp]
```

Strategy: unfold `eraGeomSum`, `Tm.eval`, and `eraInterp`; the basis
operations reduce to `Nat` `^`, `-`, `/`. Adjust the `simp` set during
execution (it may need the helper-term unfolding lemmas, e.g. `ediv`,
`epow`, `etsub`, and `fcons`/`Fin.cons` simp lemmas).

- [ ] **Step 6: State and prove the `natBSum` agreement lemma**

```lean
/-- `eraGeomSum` computes the geometric bounded sum when the base is at
least `2`. -/
theorem eraGeomSum_natBSum (q bound : ℕ) (hq : 2 ≤ q) :
    Tm.eval eraInterp eraGeomSum ![q, bound] =
      natBSum bound (fun i => q ^ i) := by
  rw [eraGeomSum_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [natBSum_geom q bound hq]
```

Strategy: `eraGeomSum_eval` at `![q, bound]` gives
`(![q, bound] 0 ^ ![q, bound] 1 - 1)/(![q, bound] 0 - 1)`; the `simp
only` reduces the vector indices (`![q, bound] 0 = q`,
`![q, bound] 1 = bound`) so `natBSum_geom` then rewrites to
`natBSum bound (fun i => q ^ i)`. The `Matrix.cons_val_*`/`head_cons`
set was verified to close this; adjust if the pin's vector simp lemmas
differ.

- [ ] **Step 7: Verify**

Run: `lake build GebLean.EraCompleteness && lake lint`
Run: `bash scripts/check-axioms.sh` (expect only `propext`,
`Quot.sound`, `Classical.choice`)
Expected: `eraGeomSum`, `eraGeomSum_eval`, `eraGeomSum_natBSum`
sorry-free and axiom-clean.

- [ ] **Step 8: Commit**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): realise the geometric bounded sum as an Era term

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Deferred to the M3b re-gate

Planned after the rich-basis-bypass assessment (spec § 13; decision
note § 5, § 9):

- power-weighted geometric sums `Σ_{z≤t} z^i q^z` as `ℕ` identities and
  `Era` terms (derived; absent from Mathlib);
- the digit sum `σ` as the `ℕ` identity `σ x = padicValNat 2
  (centralBinom x)` (Kummer assembly) and as an `Era` term (gated on
  `exp₂` / `C(2x, x)` term realisability);
- the counting reduction assembling `eraBSum` with its `eval` lemma
  (`eval (eraBSum t) ctx = natBSum (ctx 0) (fun i => eval t (Fin.cons i
  (Fin.tail ctx)))`);
- thereafter `eraBProd` (M4), `era_complete` and the K-sim-2 corollary
  (M5).

---

## Self-review

- **Spec coverage.** This plan implements the search-free, route-
  independent base of spec milestone M2 layer 1 (§ 5: geometric closed
  forms) and the `natBSum` infrastructure every later layer uses. The
  M2 remainder (`σ`, power-weighted sums) and milestone M3 (counting)
  are explicitly deferred to the M3b gate with their spec and
  decision-note references — a staging decision matching the "M3a only,
  then re-gate" scope, not a gap.
- **Placeholders.** No "TBD"/"add error handling" steps. Where proof
  tactics are left to interactive execution, the goal statement and the
  exact candidate lemmas are given (`Finset.sum_range_succ`,
  `Nat.one_le_pow`, `Nat.pow_le_pow_right`, `Nat.mul_div_cancel`,
  `Matrix.cons_val_zero`/`Matrix.cons_val_one`), because Lean proofs
  over truncated `ℕ` subtraction are not reliably writable ahead of the
  build.
- **Type consistency.** `natBSum_eq_sum` feeds `natBSum_geom`, which
  feeds `eraGeomSum_natBSum`; `natGeomSum_mul` feeds `natGeomSum_eq`
  feeds `natBSum_geom`. `eraGeomSum : ETm 2` and its two `eval` lemmas
  use the variable convention (var 0 base, var 1 bound) consistently.
  Names are used identically across tasks.
- **Verification.** Every task ends with `lake build`, `lake lint`, and
  `scripts/check-axioms.sh`, and a sorry-free commit.
