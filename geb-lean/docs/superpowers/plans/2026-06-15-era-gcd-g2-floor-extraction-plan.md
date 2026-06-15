# Era gcd-term G2 micro-plan: floor digit extraction

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** prove the Prunescu–Shunia base-5 floor identity
`⌊Bᴱ / ((Bᵃ−1)(Bᵇ−1))⌋ % B = solCount a b (a·b)` (with `B = 5^(a·b)`),
the remaining hard core of the gcd sub-plan
(`2026-06-15-era-gcd-term-subplan.md`, Phase G2).

**Architecture:** read the integer division `F := num / den` as the
truncated base-`B` positional encoding of the generating function
`1/((1−tᵃ)(1−tᵇ)) = Σ s(m) tᵐ`. The single content is the exact
identity `F = S`, where `S = Σ_{k=0}^{n} s(n−k)·Bᵏ` and
`s = solCount a b`. Prove `F = S` by the two-sided Euclidean bound
`den·S ≤ num < den·(S+1)`; then `F % B = S % B = s(n) = gcd a b + 1`
follows from the window bound `s(n) < B` and G1. This reorganises the
parent sub-plan's G2.1 (`ModEq`) and G2.2 (`%`) around the stronger,
cleaner `num/den = S`.

**Tech Stack:** Lean 4, Mathlib (pin `v4.29.0-rc6`),
`lake build`/`lake test`/`lake lint`, `scripts/check-axioms.sh`.
Constructive-only; axiom-clean (`propext`/`Quot.sound`/`Classical.choice`).

---

## Validated mathematics (numeric evidence)

With `n := a·b`, `B := 5ⁿ`, `E := n+a+b`, `num := Bᴱ`,
`den := (Bᵃ−1)(Bᵇ−1)`, `s(m) := solCount a b m`,
`S := Σ_{k=0}^{n} s(n−k)·Bᵏ`:

- `num = den·S + R` with `0 ≤ R < den` (so `num/den = S`), and
  `S % B = s(n) = gcd a b + 1`. Verified by `#eval` for all
  `1 ≤ a,b ≤ 4` (including asymmetric `a≠b` and the `a=1`/`b=1`
  boundary): `F == S`, `num == den·S + R ∧ R < den`, and
  `F % B == gcd a b + 1` all `true`.

Coefficient structure of `den·S` in base `B` (write `m = E−p` for the
coefficient of `Bᵖ`): it is `s(m) − s(m−a) − s(m−b) + s(m−a−b)` with
each summand gated to `0` when its `solCount` argument leaves `[0,n]`.
For `1 ≤ m ≤ n` the defining recurrence
`s(m) − s(m−a) − s(m−b) + s(m−a−b) = 0` makes every coefficient vanish;
`m = 0` (i.e. `p = E`) contributes the single `Bᴱ`. Hence the remainder
`R = num − den·S` is supported only on the high-`m` band
`m ∈ [n+1, E]` (low powers `Bᵖ`, `p ∈ [0, a+b−1]`):

```text
R = Σ_{m=n+1}^{n+a+b} (gated removed terms)(m) · B^{E−m}
  = Σ_{m=n+1}^{n+a+b}
      ( [m ≤ n+b]·s(m−b) + [m ≤ n+a]·s(m−a) − s(m−a−b) ) · B^{E−m}
```

`R` is a `ℤ` quantity: its base-`B` coefficients are MIXED-SIGN — the
units coefficient (`m = n+a+b`, `B⁰`) is always `−s(n) < 0`, and the
higher-power coefficients carry the positive `s(m−a)`/`s(m−b)` terms.
So `0 ≤ R < den` is a GLOBAL fact (the negative units are dominated by
the `B^{≥1}`-scaled positive band terms), NOT a per-digit/no-carry one.
Numerically (`a,b ≤ 6`): `R = num − den·S` as a `ℤ` value matches this
formula exactly, and `0 ≤ R < B^{a+b} ≤ den`. The bound must therefore
be argued over `ℤ` (Task 4), not as a nonnegative `ℕ` digit sum.

## The solution-count recurrence (prerequisite, Task 1)

The inclusion–exclusion recurrence is the engine of the telescoping:

```text
solCount a b m
  = solCount a b (m−a) + solCount a b (m−b) − solCount a b (m−a−b)   (m ≥ 1)
solCount a b 0 = 1
```

read off from `(1 − tᵃ)(1 − tᵇ)·Σ s(m) tᵐ = 1`. It must be proved as a
finite `ℕ` identity over `solCount` (Finset.card), not via series.

## File structure

- `GebLean/Utilities/ArithClosedForms.lean` (extend, after
  `solCount_mul_eq_gcd_succ` at line ~449, before `end GebLean`): the
  recurrence, `gcdDigitSum`, the two Euclidean bounds, `num/den = S`,
  the mod extraction, and the public `solCount_eq_floor_mod`. Reuses
  this file's `solCount`, `solCount_le_succ`, `solCount_mul_eq_gcd_succ`,
  `mem_solCount_box`, and `natGeomSum_mul` (namespace `GebLean`, file
  `EraBoundedSum.lean`).

No change to `GebLean/EraCompleteness.lean` (that is sub-plan G3/G4).
`Era.lean` untouched.

---

### Task 1: the solution-count recurrence

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean` (after line ~449)

- [ ] **Step 1: state and prove `solCount_recurrence`.**

```lean
/-- Inclusion–exclusion recurrence for the linear-Diophantine count:
for `1 ≤ a, 1 ≤ b` and `a + b ≤ m`,
`solCount a b m = solCount a b (m−a) + solCount a b (m−b)
  − solCount a b (m−a−b)`. The coefficientwise content of
`(1 − tᵃ)(1 − tᵇ)·Σ solCount a b m · tᵐ = 1`. -/
private theorem solCount_recurrence (a b m : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : a + b ≤ m) :
    solCount a b m + solCount a b (m - a - b)
      = solCount a b (m - a) + solCount a b (m - b)
```

Strategy: phrase additively (`x + z = y + w`) to stay in `ℕ`. Prove by
a bijection / `Finset.card` identity on the four solution finsets.
Inclusion–exclusion: the solutions of `a·x+b·y=m` with `x ≥ 1` biject
(via `x ↦ x−1`) with solutions of `a·x+b·y = m−a`; with `y ≥ 1` to
`m−b`; the `x ≥ 1 ∧ y ≥ 1` ones to `m−a−b`. Every `a·x+b·y=m` solution
has `x ≥ 1 ∨ y ≥ 1` (else `m = 0 < a+b`). Reuse `mem_solCount_box`,
`Finset.card_union_add_card_inter` (or `Finset.filter` split on
`x = 0`), `Nat.sub_add_cancel`. Difficulty: medium-hard; budget
`lean4:sorry-filler-deep`. Numeric guard first (temporary `#eval`).

- [ ] **Step 2: verify.**

Run: `lake build GebLean.Utilities.ArithClosedForms`
Expected: builds; no `sorry`/underscore.
Then `bash scripts/check-axioms.sh` clean.

- [ ] **Step 3: commit.**

`feat(era): prove the linear-Diophantine count recurrence`

---

### Task 2: the digit sum `gcdDigitSum` and the window bound

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **Step 1: define `gcdDigitSum` (the value `S`).**

```lean
/-- Base-`5^(a·b)` digit sum encoding the linear-Diophantine counts:
`S = Σ_{k=0}^{a·b} solCount a b (a·b − k) · (5^(a·b))^k`. Equals
`⌊5^(a·b·(a·b+a+b)) / ((5^(a²·b)−1)(5^(a·b²)−1))⌋` (Task 5). -/
private def gcdDigitSum (a b : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (a * b + 1),
    solCount a b (a * b - k) * (5 ^ (a * b)) ^ k
```

- [ ] **Step 2: window bound `solCount a b (a·b) < 5^(a·b)`.**

```lean
private theorem solCount_mul_lt_base (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    solCount a b (a * b) < 5 ^ (a * b)
```

Strategy: `solCount a b (a·b) ≤ a·b + 1` by `solCount_le_succ`; then
`a·b + 1 < 5^(a·b)`. `Nat.lt_pow_self (1 < 5)` gives only `a·b < 5^(a·b)`
(`≤`, not the needed strict `+1`). Use the chain
`a·b < 2^(a·b)` (`Nat.lt_two_pow_self`; `Nat.lt_two_pow` is absent from
the pin — it is already used at `ArithClosedForms.lean:109`) so
`a·b + 1 ≤ 2^(a·b)`, then `2^(a·b) < 5^(a·b)`
(`Nat.pow_lt_pow_left`, exponent `a·b ≥ 1` from `ha`,`hb`); chain with
`omega`. Easy.

- [ ] **Step 3: `gcdDigitSum_mod`.**

```lean
private theorem gcdDigitSum_mod (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gcdDigitSum a b % 5 ^ (a * b) = solCount a b (a * b)
```

Strategy: split `gcdDigitSum` at `k = 0`: the `k = 0` term is
`solCount a b (a·b) · 1`; every `k ≥ 1` term is divisible by
`5^(a·b)`. So `gcdDigitSum a b = solCount a b (a·b) + 5^(a·b)·T`. Then
`Nat.add_mul_mod_self_left` + `Nat.mod_eq_of_lt` with Step 2's window
bound. Reuse `Finset.sum_range_succ'` (peel `k = 0`) or
`Finset.range_eq_Ico` + factor `5^(a·b)` from `(5^(a·b))^k = 5^(a·b)·(…)`
for `k ≥ 1`. Medium.

- [ ] **Step 4: verify + commit.**

`lake build`, `check-axioms.sh`. Commit:
`feat(era): define the gcd base-5 digit sum and window bound`.

---

### Task 3: exponent bridging to base `B = 5^(a·b)`

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **Step 1: the three exponent rewrites.**

```lean
private theorem gcd_num_pow (a b : ℕ) :
    5 ^ (a * b * (a * b + a + b)) = (5 ^ (a * b)) ^ (a * b + a + b)
private theorem gcd_dena_pow (a b : ℕ) :
    5 ^ (a ^ 2 * b) = (5 ^ (a * b)) ^ a
private theorem gcd_denb_pow (a b : ℕ) :
    5 ^ (a * b ^ 2) = (5 ^ (a * b)) ^ b
```

Strategy: each is `← pow_mul` after a `ring_nf`/`Nat.mul_comm` on the
exponent (`a·b·(a·b+a+b) = (a·b)·(a·b+a+b)`, `a²·b = (a·b)·a`,
`a·b² = (a·b)·b`). Trivial; bundle in one commit.

- [ ] **Step 2: verify + commit.**

`feat(era): bridge gcd closed-form exponents to base 5^(ab)`.

---

### Task 4: the Euclidean bounds (HARD CORE)

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean`

The single hard piece. After Task 3, all statements use `B := 5^(a·b)`,
`num := B^(a·b+a+b)`, `den := (B^a−1)(B^b−1)` (introduced by `set` over
the bridged forms).

- [ ] **Step 1: lower bound `den·S ≤ num`.**

```lean
private theorem gcd_den_mul_digitSum_le (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    ((5 ^ (a * b)) ^ a - 1) * ((5 ^ (a * b)) ^ b - 1) * gcdDigitSum a b
      ≤ (5 ^ (a * b)) ^ (a * b + a + b)
```

- [ ] **Step 2: upper bound `num < den·(S+1)`.**

```lean
private theorem gcd_num_lt_den_mul_digitSum_succ (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (5 ^ (a * b)) ^ (a * b + a + b)
      < ((5 ^ (a * b)) ^ a - 1) * ((5 ^ (a * b)) ^ b - 1)
          * (gcdDigitSum a b + 1)
```

Strategy (both). Work over `ℤ` throughout (these are theorems, so the
`ℤ` detour costs no computability): cast the goals via `Int.toNat`/
`Int.ofNat` and `Int.natCast` monotonicity (`Int.lt_iff_add_one_le`,
`Int.toNat_lt`, `Nat.cast_le`/`Nat.cast_lt`). Establish the exact `ℤ`
identity

```text
(num : ℤ) = (den : ℤ) * (S : ℤ) + R,
R = Σ_{m=n+1}^{n+a+b}
      ( [m ≤ n+b]·s(m−b) + [m ≤ n+a]·s(m−a) − s(m−a−b) ) · B^{E−m}
```

then prove `0 ≤ R` (⇒ `den·S ≤ num`, lower bound) and `R < den` (⇒
`num < den·(S+1)`, upper bound). `R` is MIXED-SIGN — do NOT model it as
a nonnegative `ℕ` digit sum or an `ℕ` `gcdRemainder` def; the units
coefficient `−s(n)` is negative and cancels only globally.

Derivation of the identity: over `ℤ`, expand
`den·S = (B^{a+b} − B^a − B^b + 1)·Σ_{k} s(n−k)Bᵏ` into four shifted
sums; collect by power of `B`; for each interior power apply
`solCount_recurrence` (Task 1, cast to `ℤ` so the alternating sum is
literally `0` — no truncation) so the coefficient telescopes to `0`;
the leading power gives `Bᴱ`; the surviving boundary terms are `R`. The
`ℤ` identity itself should fall to `ring`/`Finset.sum` manipulation once
the recurrence rewrites the interior; `linear_combination` over the
recurrence instances is a candidate.

Bounds over `ℤ`. `R < den`: `R ≤ Σ_{p=0}^{a+b−1} s_max·Bᵖ` with
`s_max ≤ n+b` (≤ `solCount_le_succ` on the largest argument), so
`R < B·(B^{a+b}−1)/(B−1) ≤ B^{a+b}`, while
`den = (B^a−1)(B^b−1) ≥ B^{a+b−1}·(…)`; compare with `natGeomSum_mul`.
`0 ≤ R`: the highest band power dominates the lone negative units term
(`s(n) < B ≤ B^{a+b−1}`). Reuse `natGeomSum_mul` (for
`(B^c−1) = (B−1)·Σ Bⁱ` and the shift identities), `Finset.sum_range_succ`
/`sum_range_succ'`, `Finset.mul_sum`, `Int`-arith lemmas. Boundary cases
`a = 1`, `b = 1` (empty interior band) handled by the same telescoping
with degenerate ranges; verify no off-by-one in `Finset.range` bounds
(the Task 4.3 numeric guard covers `(1,1)`,`(1,k)`,`(k,1)`). This is the
dominant cost; budget `lean4:sorry-filler-deep` and expect decomposition
into 2–4 private `ℤ`-valued helper lemmas discovered during execution
(e.g. `gcd_num_sub_den_mul_digitSum_eq : (num:ℤ) − den·S = R` plus
`R_nonneg` and `R_lt_den`). Re-checkpoint with the controller if the
helper set grows beyond ~4 or the `ℤ` identity resists `ring`.

- [ ] **Step 3: numeric guard.**

Temporary `#eval` (then delete) over `1 ≤ a,b ≤ 4` re-confirming
`den·S ≤ num` and `num < den·(S+1)` before trusting the proof shape.

- [ ] **Step 4: verify + commit per helper.**

`lake build`, `check-axioms.sh`. Commit(s):
`feat(era): bound the gcd base-5 floor between consecutive multiples`.

---

### Task 5: `num/den = S` and the floor extraction (G2.1 + G2.2)

**Files:**

- Modify: `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **Step 1: the division identity.**

```lean
private theorem gcd_div_eq_digitSum (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (5 ^ (a * b)) ^ (a * b + a + b)
        / (((5 ^ (a * b)) ^ a - 1) * ((5 ^ (a * b)) ^ b - 1))
      = gcdDigitSum a b
```

Strategy: `Nat.div_eq_of_lt_le {k n m} : k * n ≤ m → m < (k+1) * n →
m / n = k` (confirmed in the pin) with `k := gcdDigitSum a b`,
`n := den`, `m := num`; feed Tasks 4.1/4.2 after `mul_comm` to match
the `k * n` (i.e. `S * den`) order. Then rewrite the bridged exponents
(Task 3) so the goal matches the closed form's `5^(a²·b)` /
`5^(a·b²)` / `5^(a·b·(a·b+a+b))` shapes.

- [ ] **Step 2: the public extraction (supersedes G2.1+G2.2).**

```lean
/-- Prunescu–Shunia base-5 floor extraction: the units base-`5^(a·b)`
digit of `⌊5^(a·b·(a·b+a+b)) / ((5^(a²·b)−1)(5^(a·b²)−1))⌋` is the
linear-Diophantine count `solCount a b (a·b)`. -/
theorem solCount_eq_floor_mod (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (5 ^ (a * b * (a * b + a + b))
        / ((5 ^ (a ^ 2 * b) - 1) * (5 ^ (a * b ^ 2) - 1)))
        % 5 ^ (a * b)
      = solCount a b (a * b)
```

Strategy: rewrite via Task 3 to base `B`, apply `gcd_div_eq_digitSum`
(Step 1), then `gcdDigitSum_mod` (Task 2.3). One `rw` chain.

- [ ] **Step 3: update the module docstring.**

Add to `ArithClosedForms.lean`'s `## Main statements` section:

```text
* `solCount_eq_floor_mod` — the Prunescu–Shunia base-5 floor read-off
  `⌊5^(a·b·(a·b+a+b)) / ((5^(a²·b)−1)(5^(a·b²)−1))⌋ % 5^(a·b)
  = solCount a b (a·b)` for `1 ≤ a, 1 ≤ b`.
```

Add to `## References` (the gcd content — G1 and G2 — is from this
source, currently absent; required by the "cite the literature" rule):

```text
* Prunescu, Shunia, arXiv:2411.06430 (the base-5 gcd closed form;
  Theorem 4.1).
```

`gcdDigitSum` is `private`, so `## Main definitions` needs no change.

- [ ] **Step 4: verify + commit.**

`lake build`, `lake lint`, `check-axioms.sh`. Commit:
`feat(era): extract the gcd count as a base-5 floor digit`.

RE-CHECKPOINT: with G2 complete, return to the parent sub-plan and
confirm G3 (`gcdClosed5`/`gcdClosed5_eq`) and G4 (`eraGcd`/`eraPow2Val`)
shapes against the now-exact `solCount_eq_floor_mod`. `gcdClosed5_eq`
chains this with `solCount_mul_eq_gcd_succ` (G1.3) and a `Nat.add_sub`.

---

## Self-review checklist (run before execution)

- [ ] `solCount_recurrence` is stated additively (no `ℕ`-subtraction
  underflow) and its hypothesis `a + b ≤ m` matches every call site in
  Task 4. (It is FALSE for `m < a+b`, e.g. `(a,b,m)=(1,1,1)`.)
- [ ] Task 4's `R` is treated as a MIXED-SIGN `ℤ` quantity; the bounds
  `0 ≤ R` and `R < den` are proved over `ℤ`. No `ℕ`-valued
  `gcdRemainder` def, no per-digit/no-carry nonnegativity claim (the
  `B⁰` coefficient `−s(n)` is negative).
- [ ] `gcdDigitSum`, the bounds, and `gcd_div_eq_digitSum` all use the
  identical `den` expression `((5^(a·b))^a − 1)·((5^(a·b))^b − 1)`.
- [ ] No fabricated mathlib names: Phase-0 sweep DONE — all present in
  the pin with assumed signatures: `Nat.div_eq_of_lt_le`,
  `Nat.lt_pow_self`, `Nat.lt_two_pow_self`, `Nat.pow_lt_pow_left`,
  `Finset.sum_range_succ'`, `Finset.mul_sum`, `Nat.add_mul_mod_self_left`,
  `Nat.mul_sub`, `Nat.sub_mul`, `Finset.card_union_add_card_inter`,
  `Nat.div_div_eq_div_mul`, `Nat.mod_eq_of_lt`. (`Nat.lt_two_pow` is
  ABSENT — do not use it.)
- [ ] Boundary cases `a = 1`, `b = 1` exercised by the Task 4.3 numeric
  guard and produce no `Finset.range` off-by-one.
- [ ] `Era.lean` untouched; all new content in `ArithClosedForms.lean`.
- [ ] Each commit: no `sorry`/`admit`/underscore; axiom-clean; ≤ 100
  char lines; docstrings on `solCount_recurrence` and the public
  `solCount_eq_floor_mod`; pre-commit green; temporary `#eval`s deleted.
- [ ] `solCount_eq_floor_mod` supersedes the parent sub-plan's separate
  G2.1 (`gcd_floor_modEq_solCount`) and G2.2; update the parent sub-plan
  to point at it.
