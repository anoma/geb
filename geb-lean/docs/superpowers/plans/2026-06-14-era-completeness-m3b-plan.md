# Era completeness M3b implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [How to work this plan](#how-to-work-this-plan)
- [De-cycling: term-level `HW` uses the slow, log-free `ν₂`](#de-cycling-term-level-hw-uses-the-slow-log-free-%CE%BD%E2%82%82)
- [File structure](#file-structure)
- [Phase map and the Phase-4 re-checkpoint](#phase-map-and-the-phase-4-re-checkpoint)
- [Phase 1 — Generalised geometric progressions (`G₁`, `G₂`)](#phase-1--generalised-geometric-progressions-g%E2%82%81-g%E2%82%82)
  - [Task 1.1: `natLinGeomSum` — the `G₁` identity over ℕ](#task-11-natlingeomsum--the-g%E2%82%81-identity-over-%E2%84%95)
  - [Task 1.2: `natSqGeomSum` — the `G₂` identity over ℕ](#task-12-natsqgeomsum--the-g%E2%82%82-identity-over-%E2%84%95)
- [Phase 2 — Number-theoretic ingredient closed forms](#phase-2--number-theoretic-ingredient-closed-forms)
  - [Task 2.1: the slow `2`-adic valuation `nu2Closed`](#task-21-the-slow-2-adic-valuation-nu2closed)
  - [Task 2.2: central binomial closed form `centralBinomClosed`](#task-22-central-binomial-closed-form-centralbinomclosed)
  - [Task 2.3: Hamming weight `hwClosed`](#task-23-hamming-weight-hwclosed)
  - [Task 2.4: the digit-block indicator `δ`](#task-24-the-digit-block-indicator-%CE%B4)
- [Phase 3 — `Era`-term realisations of the ingredients](#phase-3--era-term-realisations-of-the-ingredients)
  - [Task 3.1: the largest-power-of-two-divisor term (gcd-light)](#task-31-the-largest-power-of-two-divisor-term-gcd-light)
  - [Task 3.2: `eraNu2`, `eraCentralBinom`, `eraSigma`](#task-32-eranu2-eracentralbinom-erasigma)
  - [Task 3.3: `eraDelta` (the indicator term)](#task-33-eradelta-the-indicator-term)
- [Phase 3.5 — The monotone `ETm` majorant (gates Phases 4–5)](#phase-35--the-monotone-etm-majorant-gates-phases-45)
- [Phase 4 — Lemma 2: `ETm`-to-Diophantine reduction (RE-CHECKPOINT)](#phase-4--lemma-2-etm-to-diophantine-reduction-re-checkpoint)
- [Phase 5 — The counting engine and the recurrence read-off](#phase-5--the-counting-engine-and-the-recurrence-read-off)
- [Phase 6 — `eraBSum` and `eraBProd`](#phase-6--erabsum-and-erabprod)
  - [Task 6.1: `eraBSum`](#task-61-erabsum)
  - [Task 6.2: `eraBProd`](#task-62-erabprod)
- [Phase 7 — Capstones: `era_complete` and the K-sim-2 corollary](#phase-7--capstones-era_complete-and-the-k-sim-2-corollary)
  - [Task 7.1: `era_complete`](#task-71-era_complete)
  - [Task 7.2: the K-sim-2 corollary](#task-72-the-k-sim-2-corollary)
- [Self-review checklist (run before execution)](#self-review-checklist-run-before-execution)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the `eraBSum` and `eraBProd` term formers with their
`eval` lemmas, then assemble `era_complete` (every `ERMor1` function is
an `Era` term) and the K-sim-2 corollary.

**Architecture:** Transcribe the Prunescu–Sauras-Altuzarra hypercube
counting method and the Istrate–Prunescu–Shunia recurrence-to-term
metatheorem (decision note
`docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md`).
Ingredient closed forms (generalised geometric progressions, `gcd`,
`2`-adic valuation, central binomial, Hamming weight, the digit-block
indicator) are proved as `ℕ`-identities against Mathlib reference
functions, realised as `Era` terms, then composed by the counting
engine into `eraBSum`/`eraBProd`. `era_complete` is a structural
induction on `ERMor1` whose only non-routine cases are `bsum`/`bprod`.
The decision note is the binding construction source; the companion
spec's construction narrative (spec § 5, § 6) describes the superseded
Marchenkov-2007/2003 route and is stale, but the spec's `eval`-lemma
statements, completeness statement, soundness reuse, corollary, and
acceptance criteria (§ 3, § 4, § 7, § 8, § 11, § 12) remain binding and
are matched verbatim here.

**Tech stack:** Lean 4, Mathlib (pin `v4.29.0-rc6`), `lake build` /
`lake test` / `lake lint`, `scripts/check-axioms.sh`. Constructive-only
(no `noncomputable`); axiom-clean (`propext`, `Quot.sound`,
`Classical.choice` only).

---

## How to work this plan

- **One declaration at a time** (`.claude/rules/lean-coding.md`): write a
  `def`/`theorem`, get it building with no `sorry`/underscore, then move
  on. `sorry` is an audited stand-in *between* steps only; never in a
  commit.

- **Numeric sanity checks** use `#eval` on plain-`ℕ` closed forms (fast
  and safe). Do **not** `#guard`/`#eval` symbolic `Tm.eval`/`ERMor1.interp`
  reductions — they expand the Gödel-style composite and hang (memory:
  "ER / Gödel-numbering interp not safe for `#guard`"). Test `Era` terms
  only through proven `@[simp]`/`eval` lemmas. Numeric checks are
  throwaway: delete every `#eval` line before committing.

- **Slow vs fast `ν₂`** (a load-bearing distinction, see the de-cycling
  note below): the **slow**, log-free `ν₂` (Theorem 2.1,
  `gcd(n, 2ⁿ)`, exponent `n+1`) is the one realised as an `Era` *term*;
  its term is not numerically evaluable on large inputs, but its `eval`
  lemma is *proved*, never computed. The **fast** `ν₂` (Theorem 9.4,
  log-bounded) is used **only** in throwaway numeric probes for
  validation; it never appears in committed terms, because it depends on
  `⌊log₂⌋`, which the count engine realises via `HW`, which uses `ν₂` —
  a cycle (see "De-cycling" below).

- **Per-commit**: `bash scripts/pre-commit.sh` (runs `lake test` +
  `lake lint`) before every `.lean` commit. Commit messages: imperative,
  lowercase subject, no trailing period; end with the
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
  trailer.

- **VCS**: `jj` only; no raw mutating `git`. Each task is one or more
  `jj` commits authored by the controller (subagent-driven: implementers
  edit and verify, controller commits and reviews).

- **`ℕ`-truncated-subtraction proofs**: prefer an additive
  (subtraction-free) statement so `omega` closes the inductive step;
  feed it the nonlinear facts as hypotheses (`Nat.one_le_pow`,
  `Nat.mul_sub_one`, `Nat.le_mul_of_pos_right`); it treats
  products/powers as opaque atoms otherwise (memory).

- **Mathlib search** before each from-scratch proof: `lean_leansearch`,
  `lean_loogle`, `lean_local_search` (do not assume a lemma name).

## De-cycling: term-level `HW` uses the slow, log-free `ν₂`

The count engine read-off is `d = HW(M)/w − tᵏ`. If the term-level `HW`
used the fast `ν₂` (Theorem 9.4), it would need `⌊log₂⌋`, which Theorem
9.3 realises *through the count engine* (`HW` again) — a def/proof cycle
`count → HW → ν₂(fast) → ⌊log₂⌋ → count`. The source avoids this by
realising the count-engine `HW` with the **slow** `ν₂` (Theorem 2.1,
log-free). This plan does the same: the committed `HW`/`ν₂` *terms* use
the slow form; `⌊log₂⌋` and the fast `ν₂` are **not** on the term
critical path (no `eraIlog2` term is built). The `ℕ`-level `ilog2`
(`Nat.log 2`) is used only for magnitude bounds in proofs.

This **supersedes** the decision note's earlier fast-`ν₂`/`⌊log₂⌋`
layering (note § 4.1, § 5, § 8 item 2), which the plan's adversarial
review found to be circular for the term construction; the decision
note is corrected to match. The fast `ν₂` is correct only as a numeric
probe, where "infeasible to evaluate the slow form" — not "unusable as a
term" — is the operative concern.

## File structure

- `GebLean/Utilities/EraBoundedSum.lean` (exists; has `G₀` as
  `natGeomSum_eq`/`natBSum_geom`): extend with the generalised geometric
  progressions `G₁`, `G₂` (`ℕ`-identities, additive forms).
  Responsibility: bounded sums with closed forms.

- `GebLean/Utilities/ArithClosedForms.lean` (new): the number-theoretic
  ingredient `ℕ`-identities — the slow `2`-adic valuation, the central
  binomial closed form, the Hamming weight, and the `δ` digit-block
  indicator — each equated to a Mathlib reference function.
  Responsibility: search-free closed forms for number theory.

- `GebLean/Utilities/EraHypercube.lean` (new): the `ℕ`-level hypercube
  counting identity (`count = HW(M)/w − tᵏ`), the packed-number `M`
  closed form via the cube-sum factorisation, the mixed-radix
  enumeration bijection, and the positional-coding read-off
  `a(n) = ⌊H/Aⁿ⌋`. Responsibility: the counting engine at `ℕ` level.

- `GebLean/Utilities/EraDiophantine.lean` (new): Lemma 2 — the recursion
  on `ETm` producing a bounded, unique-witness, sum-of-squares
  Diophantine system for a term's graph; the monotone `ETm` majorant;
  the Identity-(4) exponent reduction. Responsibility: the
  term-to-Diophantine reduction (the dominant cost).

- `GebLean/EraCompleteness.lean` (exists; has `era_sound_er`,
  `eraGeomSum`): the `Era`-term realisations (`eraNu2`,
  `eraCentralBinom`, `eraSigma`, `eraDelta`, the count term, `eraBSum`,
  `eraBProd`) and the capstones (`era_complete`, the K-sim-2 corollary).

## Phase map and the Phase-4 re-checkpoint

Phases 1–3 plus the majorant (Phase 3.5) are concretely specified below.
Phase 4 (`EraDiophantine`) and Phase 5 (the counting read-off and
Theorem 2) are the discovery-heavy core; they are decomposed into
sub-lemma signatures with strategy here, and the decision note (§ 8)
designates the **start of Phase 4 as the re-checkpoint**: when Phases
1–3.5 land, write a detailed Phase-4/5 sub-plan against the then-exact
`ℕ`-shapes before executing. Phases 6–7 assemble the formers and the
capstones. Dependency order: 1, 2, 3, **3.5 (majorant)**, 4, 5, 6, 7 —
the majorant gates Phases 4 and 5 (it fixes the witness bounds and the
packing width), so it precedes them.

---

## Phase 1 — Generalised geometric progressions (`G₁`, `G₂`)

Extends M3a's `G₀`. These are the bounded sums `Σ_{i<n} iʳ qⁱ` used by
the counting engine (Phase 5). The decision note § 4.1 gives the
`Σ_{k≤t}` forms; re-indexed to `Finset.range n` (`t = n−1`) the
**verified** cleared constants are, for `G₁`,
`(Σ_{i<n} i·qⁱ)·(q−1)² = (n−1)·q^{n+1} − n·qⁿ + q`, and for `G₂`,
`(Σ_{i<n} i²·qⁱ)·(q−1)³ = (n−1)²·q^{n+2} − (2n²−2n−1)·q^{n+1} + n²·qⁿ − q² − q`.
These have interior `ℕ` truncation at small `n`, so state them additively
(subtraction-free) and numeric-check over `range 8` (including
`n = 0, 1`) before proving.

### Task 1.1: `natLinGeomSum` — the `G₁` identity over ℕ

**Files:**

- Modify: `GebLean/Utilities/EraBoundedSum.lean`

- [ ] **Step 1: State the additive (ℕ-safe) identity**

```lean
/-- Linear-weighted geometric sum `Σ_{i<n} i·qⁱ`, cleared of division
and stated additively (no `ℕ` truncation, valid for all `n`), for
`2 ≤ q`. `G₁` re-indexed to `Finset.range n` (decision note § 4.1). -/
theorem natLinGeomSum_mul (q n : ℕ) (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range n, i * q ^ i) * (q - 1) ^ 2 + q ^ (n + 1)
        + n * q ^ n =
      n * q ^ (n + 1) + q := by
  sorry
```

Note: the additive form `LHS·(q−1)² + q^{n+1} + n·qⁿ = n·q^{n+1} + q`
is equivalent over `ℤ` to `(n−1)·q^{n+1} − n·qⁿ + q` but avoids every
`ℕ` subtraction, so it holds for all `n ≥ 0` and `omega` can close the
step.

- [ ] **Step 2: Numeric check FIRST (over `range 8`, incl. `n=0,1`)**

```lean
#eval (List.range 8).all (fun n =>
  ((List.range n).foldl (fun s i => s + i * 3 ^ i) 0) * (3 - 1) ^ 2
      + 3 ^ (n + 1) + n * 3 ^ n
    = n * 3 ^ (n + 1) + 3)
```

Expected: `true`. Remove before commit.

- [ ] **Step 3: Build to confirm the statement elaborates**

Run: `lake build GebLean.Utilities.EraBoundedSum`
Expected: builds with a `declaration uses 'sorry'` warning, no
elaboration errors.

- [ ] **Step 4: Prove by induction on `n`**

Strategy: `induction n`; base `simp`. Step: `Finset.sum_range_succ`,
`pow_succ`, the IH, then `omega` fed `Nat.one_le_pow` and the product
facts. The additive form keeps every term non-negative, so `omega`
closes after the nonlinear atoms are supplied. Mirror
`natGeomSum_mul`'s structure.

- [ ] **Step 5: `/`-form corollary (for `n ≥ 1`, optional consumer
convenience)**

```lean
theorem natLinGeomSum_eq (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, i * q ^ i =
      ((n - 1) * q ^ (n + 1) - n * q ^ n + q) / (q - 1) ^ 2 := by
  sorry
```

Strategy: derive from `natLinGeomSum_mul` by clearing; only stated for
`n ≥ 1` so `(n − 1)` is exact. If the engine consumes the `_mul` form
directly, this corollary may be dropped.

- [ ] **Step 6: Verify axiom-clean and commit**

Run: `bash scripts/pre-commit.sh`
Run: `bash scripts/check-axioms.sh` (expect `propext`, `Quot.sound`,
`Classical.choice` only)

```bash
jj describe -m "feat(era): prove the linear-weighted geometric sum over naturals

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

### Task 1.2: `natSqGeomSum` — the `G₂` identity over ℕ

Higher-effort than Task 1.1: degree-3 in the cleared bracket, and the
middle coefficient `2n²−2n−1` is negative for `n ≤ 1`, so the cleared
`ℕ` identity is meaningful only for `n ≥ 2`. Prove the additive form for
`n ≥ 2` and discharge `n = 0, 1` as trivial base cases (the sum is `0`).

**Files:**

- Modify: `GebLean/Utilities/EraBoundedSum.lean`

- [ ] **Step 1: Numeric check FIRST (pin the constants, incl. small n)**

```lean
#eval (List.range 8).all (fun n =>
  ((List.range n).foldl (fun s i => s + i ^ 2 * 3 ^ i) 0) * (3 - 1) ^ 3
      + (2 * n ^ 2 - 2 * n - 1) * 3 ^ (n + 1) + 3 ^ 2 + 3
    = (n - 1) ^ 2 * 3 ^ (n + 2) + n ^ 2 * 3 ^ n)
```

Expected: `true` for `n ≥ 2`; inspect `n = 0, 1` separately (the
`2n²−2n−1` underflows in `ℕ` there). Adjust until the `n ≥ 2` cases all
pass; remove before commit.

- [ ] **Step 2: State the additive identity for `n ≥ 2`**

```lean
/-- Square-weighted geometric sum `Σ_{i<n} i²·qⁱ`, cleared and additive,
for `2 ≤ q` and `2 ≤ n`. `G₂` re-indexed to `Finset.range n`
(decision note § 4.1). -/
theorem natSqGeomSum_mul (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range n, i ^ 2 * q ^ i) * (q - 1) ^ 3
        + (2 * n ^ 2 - 2 * n - 1) * q ^ (n + 1) + q ^ 2 + q =
      (n - 1) ^ 2 * q ^ (n + 2) + n ^ 2 * q ^ n := by
  sorry
```

- [ ] **Step 3: Base cases `n = 0, 1`**

```lean
theorem natSqGeomSum_zero (q : ℕ) :
    ∑ i ∈ Finset.range 0, i ^ 2 * q ^ i = 0 := by simp
theorem natSqGeomSum_one (q : ℕ) :
    ∑ i ∈ Finset.range 1, i ^ 2 * q ^ i = 0 := by simp
```

- [ ] **Step 4: Prove Step 2 by induction on `n` from `2`**

Strategy: induct with the base at `n = 2` (compute directly) and the
step via `Finset.sum_range_succ`, `pow_succ`, IH, `omega` with the
nonlinear atoms. The additive form keeps coefficients non-negative for
`n ≥ 2`. Budget a `lean4:sorry-filler-deep` pass — this is materially
harder than `G₁`.

- [ ] **Step 5: build, axiom-check, commit**

```bash
jj describe -m "feat(era): prove the square-weighted geometric sum over naturals

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

## Phase 2 — Number-theoretic ingredient closed forms

Each ingredient: a closed-form `ℕ` `def`, an identity equating it to a
Mathlib reference function (for `n ≥ 1`, with explicit `n = 0` handling
where the closed form degenerates), and (Phase 3) an `Era` term. The
`ν₂` realised here is the **slow, log-free** form (see De-cycling).

### Task 2.1: the slow `2`-adic valuation `nu2Closed`

**Files:**

- Create: `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **Step 1: Module docstring + imports**

```lean
import GebLean.LawvereER
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Search-free closed forms for number-theoretic functions

`ℕ`-level closed-form identities supporting the Era bounded-sum engine
(`GebLean/EraCompleteness.lean`): the slow `2`-adic valuation, the
central binomial coefficient, the binary Hamming weight, and the
digit-block indicator, each equated to a Mathlib reference function.

## Main definitions

* `nu2Closed` — the slow, log-free `2`-adic valuation closed form.
* `centralBinomClosed` — `C(2n,n)` as an arithmetic-term closed form.
* `hwClosed` — the binary Hamming weight via `ν₂(C(2n,n))`.
* `deltaBlock` — the digit-block indicator.

## Main statements

* `nu2Closed_eq` — `nu2Closed n = padicValNat 2 n` for `n ≥ 1`.
* `centralBinomClosed_eq` — `= Nat.centralBinom n` for `n ≥ 1`.
* `hwClosed_eq` — `= (Nat.digits 2 n).sum` for `n ≥ 1`.
* `hwClosed_deltaBlock` — the indicator's Hamming weight.

## References

* Prunescu, Sauras-Altuzarra, arXiv:2407.12928 (the method; `ν_p`
  Theorem 2.1; central binomial; Hamming weight; `δ` Lemma 3.1).

## Tags

elementary recursive, closed form, p-adic valuation, Hamming weight
-/

namespace GebLean
```

- [ ] **Step 2: define the slow `ν₂`**

```lean
/-- The slow (log-free) `2`-adic valuation closed form
(arXiv:2407.12928, Theorem 2.1). `Nat.gcd n (2^n) = 2^(v₂ n)`, so the
binomial-mod read-off recovers `v₂ n`. Realised as an `Era` term
(Phase 3); not numerically evaluable on large inputs, but its `eval`
lemma is proved, not computed. -/
def nu2Closed (n : ℕ) : ℕ :=
  let base := 2 ^ (n + 1) - 1
  (Nat.gcd n (2 ^ n) ^ (n + 1) % base ^ 2) / base
```

- [ ] **Step 3: numeric check (small `n` only — the slow form forms
`2ⁿ`)**

```lean
#eval (List.range 60).all (fun n => n = 0 || nu2Closed n = padicValNat 2 n)
```

Expected: `true`. (`padicValNat 2` needs the `Fact (Nat.Prime 2)`
instance `fact_prime_two`, available in Mathlib.) Remove before commit.

- [ ] **Step 4: prove `nu2Closed n = padicValNat 2 n` for `n ≥ 1`**

```lean
theorem nu2Closed_eq (n : ℕ) (hn : 1 ≤ n) :
    nu2Closed n = padicValNat 2 n := by
  sorry
```

Strategy (method paper Theorem 2.1): set `x = padicValNat 2 n`. Facts:
`Nat.gcd n (2^n) = 2^x` (from `pow_padicValNat_dvd : 2^x ∣ n` and
`x ≤ n`); `x < base := 2^(n+1) − 1`. Then
`(2^x)^(n+1) = (2^(n+1))^x = (base+1)^x ≡ 1 + x·base (mod base²)` by the
binomial theorem, using `x < base` so `mod base²` isolates
`1 + x·base`; dividing by `base` gives `x`. Factor the binomial-mod step
as a generic lemma `pow_succ_mod_sq (a x : ℕ) (h : x < a + 1) :
(a + 1) ^ x % a ^ 2 = (1 + x * a) % a ^ 2` then specialise.

- [ ] **Step 5: build, axiom-check, commit**

```bash
jj describe -m "feat(era): prove the slow 2-adic valuation closed form

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

### Task 2.2: central binomial closed form `centralBinomClosed`

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **Step 1: define**

```lean
/-- `C(2n,n)` as the arithmetic-term closed form
`⌊(1+2^(2n))^(2n) / 2^(2n²)⌋ mod 2^(2n)` (arXiv:2407.12928). Agrees with
`Nat.centralBinom` for `n ≥ 1`; degenerates to `0` at `n = 0`
(`Nat.centralBinom 0 = 1`), handled separately. -/
def centralBinomClosed (n : ℕ) : ℕ :=
  ((1 + 2 ^ (2 * n)) ^ (2 * n) / 2 ^ (2 * n ^ 2)) % 2 ^ (2 * n)
```

- [ ] **Step 2: numeric check** for `n` in `1 .. 14`:
`centralBinomClosed n = Nat.centralBinom n`. Confirm separately that
`centralBinomClosed 0 = 0 ≠ 1 = Nat.centralBinom 0`. Remove before
commit.

- [ ] **Step 3: prove `centralBinomClosed n = Nat.centralBinom n` for
`n ≥ 1`**

```lean
theorem centralBinomClosed_eq (n : ℕ) (hn : 1 ≤ n) :
    centralBinomClosed n = Nat.centralBinom n := by
  sorry
```

Strategy: `(1 + 2^(2n))^(2n) = Σ_j C(2n,j) · 2^(2n·j)` (binomial
theorem, `add_pow` / `Commute.add_pow`). The base-`2^(2n)` digits are
`C(2n,j)`, which fit strictly (`C(2n,j) < 2^(2n)` for `n ≥ 1`: from
`Nat.choose_le_two_pow : C(m,k) ≤ 2^m` plus strictness via
`Nat.sum_range_choose : Σ_j C(2n,j) = 2^(2n)` having more than one
positive term), so `⌊·/2^(2n²)⌋ mod 2^(2n)` extracts the `j = n` digit
`C(2n,n)`. Factor a base-`b` digit-extraction lemma
`digit_extract (d : ℕ → ℕ) (b k : ℕ) (hfit : ∀ j, d j < b) :
(Σ_j d j · b^j) / b^k % b = d k`.

- [ ] **Step 4: build, axiom-check, commit**

```bash
jj describe -m "feat(era): prove the central binomial coefficient closed form

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

### Task 2.3: Hamming weight `hwClosed`

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **Step 1: define (slow `ν₂` ∘ central binomial)**

```lean
/-- Binary Hamming weight (digit sum) `σ`, as `ν₂(C(2n,n))` (Kummer),
using the slow log-free `ν₂`. -/
def hwClosed (n : ℕ) : ℕ := nu2Closed (centralBinomClosed n)
```

- [ ] **Step 2: numeric check** `hwClosed n = (Nat.digits 2 n).sum` for
`n` in `1 .. 10` (the slow `ν₂` on `C(2n,n)` is feasible only for small
`n` — it forms a `~2·C(2n,n)`-bit number and stalls past `n ≈ 12`, so
keep the probe range small; confirm `n = 0`
gives digit sum `0`). Remove before commit.

- [ ] **Step 3: prove `hwClosed n = (Nat.digits 2 n).sum` for `n ≥ 1`,
plus `n = 0`**

```lean
theorem hwClosed_eq (n : ℕ) (hn : 1 ≤ n) :
    hwClosed n = (Nat.digits 2 n).sum := by
  sorry
```

Strategy: chain `nu2Closed_eq` (needs `centralBinomClosed n ≥ 1`, from
`centralBinomClosed_eq` and `Nat.centralBinom_pos`) and
`centralBinomClosed_eq` to reduce to
`padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum`. Factor the
Kummer step as a named, moderate-effort sub-lemma
`padicValNat_centralBinom_two (n : ℕ) :
padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum`, assembled
from `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` at `p = 2`,
`k = n`, `m = 2n` (giving `(2−1)·v₂ = S₂(n) + S₂(n) − S₂(2n)`), with
`Nat.centralBinom_eq_two_mul_choose` and the `digits 2 (2n)` shift
`S₂(2n) = S₂(n)`. Handle `n = 0` directly (`hwClosed 0` and digit sum
both `0`).

- [ ] **Step 4: build, axiom-check, commit**

```bash
jj describe -m "feat(era): prove the Hamming weight closed form via Kummer

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

### Task 2.4: the digit-block indicator `δ`

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **Step 1: define and state the indicator lemma**

```lean
/-- The digit-block indicator (arXiv:2407.12928, Lemma 3.1):
`δ a w = (2^w - 1)(2^w - a + 1)`. -/
def deltaBlock (a w : ℕ) : ℕ := (2 ^ w - 1) * (2 ^ w - a + 1)

/-- `HW(δ a w) = 2w` when `a = 0`, else `w`, for `0 ≤ a < 2^w`. -/
theorem hwClosed_deltaBlock {a w : ℕ} (ha : a < 2 ^ w) :
    hwClosed (deltaBlock a w) = if a = 0 then 2 * w else w := by
  sorry
```

- [ ] **Step 2: numeric check** over `w ∈ 1 .. 6`, `a ∈ 0 .. 2^w − 1`
(confirm `deltaBlock a w ≥ 1` so `hwClosed` is in its proven range, and
`< 2^(2w)`). Remove before commit.

- [ ] **Step 3: prove**

Strategy: via `hwClosed_eq` reduce to `(Nat.digits 2 (δ a w)).sum`. For
`a = 0`: `δ = (2^w−1)(2^w+1) = 2^(2w)−1`, digit sum `2w`. For
`1 ≤ a < 2^w`: a direct base-`2`/base-`2^w` block computation showing
the `2w` bits split into two complementary runs summing to `w`. Fiddly;
budget a `lean4:sorry-filler-deep` pass.

- [ ] **Step 4: build, axiom-check, commit**

```bash
jj describe -m "feat(era): prove the digit-block indicator Hamming weight

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

## Phase 3 — `Era`-term realisations of the ingredients

For each `ℕ` closed form, build the `Era` term mirroring its arithmetic
composition and prove `eval` equals the `ℕ` closed form. Realisations
compose `eadd`/`etsub`/`emul`/`ediv`/`emod`/`epow`/`epow2`. Test only
through the `eval` lemma (never `#eval` on `Tm.eval`). All terms use the
slow `ν₂`, so there is no back-dependency on Phase 5: every Phase-3
`eval` lemma is committable here.

### Task 3.1: the largest-power-of-two-divisor term (gcd-light)

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

The slow `ν₂` needs only `Nat.gcd n (2^n)`, which equals `2^(v₂ n)` — a
power of two, not a general gcd. Realise this directly rather than
transcribing the full Mazzanti gcd term (record the choice in a comment;
this is the from-scratch ingredient, weighted toward the simpler
option).

- [ ] **Step 1: choose and define**

```lean
/-- `2^(v₂ n)`, the largest power of two dividing `n` (= `gcd n (2^n)`),
as an `Era` term in variable `0`. -/
def eraPow2Val : ETm 1 := sorry  -- e.g. n / oddPart, or a closed form

theorem eraPow2Val_eval (n : ℕ) :
    Tm.eval eraInterp eraPow2Val ![n] = Nat.gcd n (2 ^ n) := by
  sorry
```

Strategy: option A — realise the largest power of two dividing `n` as
`n / odd(n)` where `odd(n)` is built search-free; option B — transcribe
Mazzanti's base-2 gcd term specialised to `gcd n (2^n)`. Search Mathlib
for an existing `gcd`-as-arithmetic-term first (`lean_leansearch`); none
is expected. The `ℕ` identity `Nat.gcd n (2^n) = 2^(padicValNat 2 n)` is
the correctness target — search for it
(`Nat.gcd_pow`, `Nat.Coprime`, `pow_padicValNat_dvd`).

- [ ] **Step 2:** build (with `sorry`), prove, numeric `eval` check via
the lemma, axiom-check, commit.

```bash
jj describe -m "feat(era): realise the largest power-of-two divisor as an Era term

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

### Task 3.2: `eraNu2`, `eraCentralBinom`, `eraSigma`

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

Identical pattern each: a `def` mirroring the `ℕ` closed form, then an
`eval` lemma reducing to the Phase-2 identity. One commit each. No
`⌊log₂⌋` / `eraIlog2` is built (De-cycling).

- [ ] **Step 1: `eraNu2 : ETm 1`** composing `eraPow2Val`, `epow`,
`emod`, `ediv`, `etsub`, `epow2`; prove `eval eraNu2 ![n] = nu2Closed n`
by reduction to `nu2Closed`'s definition (using `eraPow2Val_eval`).

- [ ] **Step 2: `eraCentralBinom : ETm 1`** mirroring
`centralBinomClosed`; `eval = centralBinomClosed n`.

- [ ] **Step 3: `eraSigma : ETm 1`** as `eraNu2 ∘ eraCentralBinom`
(substitution via `Tm.subst`/`sub0`); prove
`eval eraSigma ![n] = hwClosed n` by `Tm.eval_subst` + the two `eval`
lemmas. (The bridge to the digit sum is `hwClosed_eq`, used by
consumers; `eraSigma`'s own `eval` lemma targets `hwClosed n`.)

- [ ] **Step 4: per sub-task** build, axiom-check, commit (three
commits, e.g. `feat(era): realise the 2-adic valuation as an Era term`).

### Task 3.3: `eraDelta` (the indicator term)

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

- [ ] `eraDelta : ETm 2` (variable `0` = `a`, `1` = `w`) mirroring
`deltaBlock`; `eval eraDelta ![a,w] = deltaBlock a w`. Build, prove
(direct reduction), axiom-check, commit.

---

## Phase 3.5 — The monotone `ETm` majorant (gates Phases 4–5)

The engine needs an arithmetic-term majorant `A(y, x̄)` with `f(i) < A`
for `i < y` (and a product majorant): it fixes the packing width `w`
(Phase 5) and the witness bounds `DiophEnc.bound` (Phase 4). This is the
first dependency-critical sub-task after the ingredients (decision note
§ 7, § 8 item 1) — it precedes Phase 4.

**Files:**

- Create/extend: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: reuse assessment.** `GebLean/Utilities/ERAMajorants.lean`
provides the Tourlakis `A_one`/`A_one_iter`/`A_two_iter`/`towerER`
majorant family, but typed for `ERMor1`, not `ETm` — so it does not
directly give an `ETm`-summand majorant. Record (one line) that
`ERAMajorants` is `ERMor1`-typed and that the `ETm` majorant is built
fresh; note whether the `PolyBound`/`towerER` magnitude bounds can be
reused for the width estimate.

- [ ] **Step 2: choose construction and define.** Two routes (record the
choice, as in Task 3.1): (A) structural recursion on `ETm` building a
monotone majorant term; (B) the recurrence-paper Claim-2 recipe (replace
every `tsub` by `add`, substitute the range bound for the loop index).

```lean
/-- A monotone arithmetic-term majorant: `eval (eraMajorant t) ctx`
strictly bounds `eval t ctx'` for all `ctx'` agreeing with `ctx` off the
loop index, over the loop range. -/
def eraMajorant {n : ℕ} (t : ETm n) : ETm n := sorry

theorem eraMajorant_spec {n : ℕ} (t : ETm n) (ctx : Fin n → ℕ) :
    Tm.eval eraInterp t ctx < Tm.eval eraInterp (eraMajorant t) ctx := by
  sorry
```

- [ ] **Step 3:** build, prove, axiom-check, commit.

```bash
jj describe -m "feat(era): build the monotone ETm majorant for the engine

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

## Phase 4 — Lemma 2: `ETm`-to-Diophantine reduction (RE-CHECKPOINT)

> **Re-checkpoint (decision note § 8).** Before executing Phase 4, with
> Phases 1–3.5 landed and the exact `ℕ`-shapes known, write a detailed
> Phase-4/5 sub-plan (`superpowers:writing-plans`) and adversarially
> review it. Phase 4 is the dominant cost and principal schedule risk.
> The decomposition below is the architecture that sub-plan refines; the
> `DiophEnc` field types must be finalised there (the skeleton below is
> illustrative — a field type cannot literally be `sorry`).

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

Goal: a recursion on `ETm` producing, for a term `t : ETm n`, a
Diophantine system with the four invariants (arXiv:2606.09336, Lemma 2):
sum-of-squares; simple (a simple exponential polynomial); unique
witness; explicit arithmetic-term witness bounds.

- [ ] **Sub-lemma 4.1: the carrier structure (all four invariants as
fields).** Finalise the field types in the sub-plan; the four invariants
are:

```lean
/-- A bounded, unique-witness, sum-of-squares Diophantine encoding of a
term's graph `t.eval ρ = y`. Variables: `n` inputs, the output `y`, and
`witArity` witnesses. -/
structure DiophEnc (n : ℕ) where
  witArity : ℕ
  /-- the sum-of-squares predicate term (vars: inputs, `y`, witnesses) -/
  sos : ETm (n + 1 + witArity)
  /-- per-witness bound terms (vars: inputs and `y`) -/
  bound : Fin witArity → ETm (n + 1)
  /-- correctness: `sos = 0` exactly characterises the graph -/
  sos_zero_iff : Prop        -- finalise: ∀ ρ y w, eval sos … = 0 ↔ …
  /-- uniqueness of the witness tuple when the graph holds -/
  uniq : Prop                -- finalise: ∀ ρ y, graph → ∃! w, …
  /-- the witnesses respect their bounds -/
  bound_spec : Prop          -- finalise: solution witnesses < bound
```

- [ ] **Sub-lemma 4.2: the Identity-(4) exponent reduction.** The
device reducing variable-exponent cases (`mul`, `div`, `tsub`, `pow`) to
base `2`:

```lean
/-- `a^b = 2^((ab+a+1)·b) mod (2^(ab+a+1) − a)` (arXiv:2407.12928,
Identity (4)), valid including `0^0 = 1`. -/
theorem pow_eq_two_pow_mod (a b : ℕ) :
    a ^ b = 2 ^ ((a * b + a + 1) * b) % (2 ^ (a * b + a + 1) - a) := by
  sorry
```

Numeric-check first over `a ∈ 0..29`, `b ∈ 0..14` (validated in the
gate probe), then prove.

- [ ] **Sub-lemmas 4.3–4.6: the induction cases** (one per `ETm`
constructor: `var`, `zero`, `succ`, and `app b` for each `b : EraB`).
Build the `DiophEnc` from sub-encodings following the paper's Cases 1–3
(projection; `2^B`; `B₁ + B₂`; `B₁ mod B₂`), extended to the full Era
basis (`tsub`, `mul`, `div`, `pow` via Sub-lemma 4.2). Each case
preserves the four invariants; the witness bounds compose via
`eraMajorant` (Phase 3.5).

- [ ] **Sub-lemma 4.7: the top-level reduction** assembling
`diophOf : ETm n → DiophEnc n` and its correctness theorem.

Strategy notes for the sub-plan: this mirrors `Tm.eval_subst`'s
structural induction but tracks the invariant bundle; expect heavy use
of `lean4:sorry-filler-deep` and factoring per constructor. Budget this
as the largest phase. Commit per sub-lemma.

---

## Phase 5 — The counting engine and the recurrence read-off

**Files:**

- Create: `GebLean/Utilities/EraHypercube.lean`

- [ ] **Sub-lemma 5.1: `HW`-additivity over non-overlapping blocks.**
`(Nat.digits 2 (Σ blocks)).sum = Σ (Nat.digits 2 block).sum` when blocks
occupy disjoint base-`2^(2w)` positions (recurrence paper Lemma 3.3); a
base-`2^(2w)` place-value / no-carry argument.

- [ ] **Sub-lemma 5.2: the mixed-radix enumeration bijection.** The map
`v(ā) = a₁ + a₂·t + ⋯ + a_k·t^(k−1)` is a bijection
`{0,…,t−1}^k ≅ {0,…,t^k−1}` (a `Finset`/`Fin`-product digit expansion);
isolate it, as the cube-sum factorisation depends on it.

- [ ] **Sub-lemma 5.3: the packed number `M` and the cube-sum
factorisation** (method paper Lemma 3.2):
`Σ_{ā∈cube} Πᵢ aᵢ^{uᵢ} vᵢ^{aᵢ} = Πᵢ G_{uᵢ}(vᵢ, t−1)`, reusing
`natGeomSum_eq` (`G₀`), `natLinGeomSum_mul` (`G₁`), `natSqGeomSum_mul`
(`G₂`).

- [ ] **Sub-lemma 5.4: the count read-off**
`#{ā : P ā = 0} = (Nat.digits 2 (M …)).sum / w − t^k` (method paper
Theorem 3.4 / Corollary 3.6), composing 5.1–5.3 and
`hwClosed_deltaBlock`. The `HW` here is the slow-`ν₂` term — state the
well-foundedness explicitly (no `⌊log₂⌋` dependency; no cycle).

- [ ] **Sub-lemma 5.5: positional coding read-off**
`a(n) = ⌊H/Aⁿ⌋` and the recurrence metatheorem specialisation
(recurrence paper Lemma 3, Theorem 2) for `k = 1`, consuming the Phase-4
`DiophEnc` and the Phase-3.5 majorant `A`.

Strategy: 5.1 is a place-value argument; 5.2 a digit-expansion bijection;
5.3 reduces to the `G_r` closed forms (Phase 1); 5.4 is arithmetic from
5.1–5.3. Re-checkpoint review applies (Phase 4 header). Commit per
sub-lemma.

---

## Phase 6 — `eraBSum` and `eraBProd`

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

### Task 6.1: `eraBSum`

- [ ] **Step 1: define**

```lean
/-- Bounded summation as an `Era` term: variable `0` is the bound;
`eval (eraBSum t)` sums `t` over the loop index. Built from the count
read-off (Phase 5) applied to the Diophantine encoding (Phase 4) of the
summand `t`, via `Σ_{i<y} f i = #{(i,w) : i<y, w<f i}`, with the width
fixed by `eraMajorant` (Phase 3.5). -/
def eraBSum {k : ℕ} (t : ETm (k + 1)) : ETm (k + 1) := sorry
```

- [ ] **Step 2: the `eval` lemma (the deliverable)**

```lean
theorem eraBSum_eval {k : ℕ} (t : ETm (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    Tm.eval eraInterp (eraBSum t) ctx =
      natBSum (ctx 0) (fun i =>
        Tm.eval eraInterp t (Fin.cons i (Fin.tail ctx))) := by
  sorry
```

Strategy: `natBSum (ctx 0) f = ∑ i ∈ Finset.range (ctx 0), f i`
(`natBSum_eq_sum`, M3a) `= #{(i,w) : i<ctx 0 ∧ w<f i}` (a
`Finset.card`/double-count identity `sum_eq_card_lt`) `=` the count
read-off (Sub-lemma 5.4) applied to the `DiophEnc` of `t` (Phase 4),
with the majorant fixing `w` (Phase 3.5). Reduce `eval (eraBSum t)` to
that count via the Phase-5 `eval` lemmas.

- [ ] **Step 3:** build, axiom-check, commit.

### Task 6.2: `eraBProd`

- [ ] **Step 1: define** `eraBProd` via the recurrence engine
(Sub-lemma 5.5) with step `·` (`p(m+1) = p(m) · f(m)`), product majorant
(Phase 3.5).

- [ ] **Step 2: the `eval` lemma**

```lean
theorem eraBProd_eval {k : ℕ} (t : ETm (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    Tm.eval eraInterp (eraBProd t) ctx =
      natBProd (ctx 0) (fun i =>
        Tm.eval eraInterp t (Fin.cons i (Fin.tail ctx))) := by
  sorry
```

- [ ] **Step 3:** build, axiom-check, commit.

---

## Phase 7 — Capstones: `era_complete` and the K-sim-2 corollary

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

### Task 7.1: `era_complete`

- [ ] **Step 1: state**

```lean
/-- Completeness: every `ERMor1` (elementary) function is the denotation
of some `Era` term. -/
theorem era_complete {n : ℕ} (f : ERMor1 n) :
    ∃ t : ETm n, ∀ ctx : Fin n → ℕ,
      Tm.eval eraInterp t ctx = f.interp ctx := by
  sorry
```

- [ ] **Step 2: prove by structural induction on `f`**

```text
zero      → ⟨Tm.zero, …⟩                       (ERMor1.interp_zero, eraInterp)
succ      → ⟨Tm.succ (Tm.var 0), …⟩            (interp_succ)
proj i    → ⟨Tm.var i, …⟩                      (interp_proj)
sub       → ⟨Tm.var 0 ∸ᵉ Tm.var 1, …⟩          (interp_sub, etsub_eval)
comp f g  → substitute g-witnesses into f-witness   (Tm.eval_subst + IHs)
bsum f    → ⟨eraBSum (IH-witness of f), …⟩      (eraBSum_eval + IH)
bprod f   → ⟨eraBProd (IH-witness of f), …⟩     (eraBProd_eval + IH)
```

Strategy: `induction f` with the seven cases; the five routine cases are
immediate from the `interp_*` and `*_eval` lemmas; `comp` uses
`Tm.eval_subst` with the `Fin.cons`/`Fin.tail` context juggling matching
`interp_comp`; `bsum`/`bprod` apply the Phase-6 `eval` lemmas to the
inductive witness. The `Fin.cons i (Fin.tail ctx)` shape is identical in
`ERMor1.interp_bsum` and `eraBSum_eval`, so the IH applies directly.

- [ ] **Step 3:** build, axiom-check, commit.

### Task 7.2: the K-sim-2 corollary

The function-class equality comes from the existing **term-level
interp-faithfulness** lemmas, not the categorical `erKSimEquiv`
(`erKSimEquiv` has no semantic readout). The forward bridge is
`erToK_interp` (`GebLean/LawvereERKSim/ErToK.lean`,
`(erToK e).interp v = e.interp v`); the reverse is `kToER_interp`
(`GebLean/LawvereKSimER.lean`, carrying an `f.level ≤ 2` premise that is
load-bearing for the K-sim-2 statement).

- [ ] **Step 1: pin the extraction.** Confirm `erToK_interp` and
`kToER_interp` (with its `level ≤ 2` premise) give the
`ERMor1` ↔ `K-sim-2` function-class equality directly; assess whether
`erKSimEquiv` is needed at all (likely not). State the exact corollary
signature in terms of the K-sim-2 morphism `interp`.

- [ ] **Step 2: state and prove the corollary** by composing
`era_complete` + `era_sound_er` (giving `Era ≃ E³` as denoted functions)
with the `ERMor1 ↔ K-sim-2` interp faithfulness. Keep it a thin
composition; implement no `K-sim` scheme over the basis (spec § 12).

- [ ] **Step 3:** build, axiom-check, commit. This commit closes M3b.

---

## Self-review checklist (run before execution)

- [ ] **Spec coverage.** Spec § 5 (bounded-sum engine) → Phases 1–6;
  § 6 (bounded product via the engine, no separate `2^x`-elimination) →
  Task 6.2; § 4/§ 3 (the induction, the two `eval` lemmas) → Phases 6–7;
  § 7 (soundness) → already `era_sound_er` (not redone); § 8 (K-sim-2
  corollary) → Task 7.2. Acceptance criteria § 11 (no
  `sorry`/`admit`/underscore in commits, 100-char, axiom-clean,
  `Era.lean` unmodified) → the per-task pre-commit + axiom-check gates
  and the file structure.

- [ ] **`Era.lean` untouched** (spec § 12): all new content lives in
  `Utilities/*` and `EraCompleteness.lean`.

- [ ] **Type consistency.** `eraBSum`/`eraBProd : ETm (k+1) → ETm (k+1)`;
  the `eval`-lemma RHS `natBSum (ctx 0) (fun i => Tm.eval … (Fin.cons i
  (Fin.tail ctx)))` matches `ERMor1.interp_bsum` verbatim. Ingredient
  names consistent across phases (`nu2Closed`/`eraNu2`,
  `centralBinomClosed`/`eraCentralBinom`, `hwClosed`/`eraSigma`,
  `deltaBlock`/`eraDelta`, `natLinGeomSum_mul`/`natSqGeomSum_mul`).

- [ ] **Mathlib name sweep (Phase-0 of execution).** Confirmed present
  in the pin: `Nat.pow_log_le_self` (arg `x ≠ 0`),
  `Nat.lt_pow_succ_log_self`, `Nat.centralBinom`, `Nat.centralBinom_pos`,
  `Nat.centralBinom_eq_two_mul_choose`, `padicValNat` (needs
  `Fact (Nat.Prime 2)` = `fact_prime_two`), `pow_padicValNat_dvd`,
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`,
  `Nat.choose_le_two_pow`, `Nat.sum_range_choose`, `Nat.digits`,
  `Nat.mul_div_cancel`, `Nat.log`. Note: `geom_sum_eq` lives at the
  Field path (`Mathlib/Algebra/Field/GeomSum.lean`) and is **not** used
  for the `ℕ`-level inductions (G₁/G₂ are proved by `ℕ` induction).
