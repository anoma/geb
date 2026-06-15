# Era gcd-term sub-plan (M3b Phase-3 re-checkpoint)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The closed form (target)](#the-closed-form-target)
- [File structure](#file-structure)
- [Re-checkpoint note](#re-checkpoint-note)
- [Phase G1 — the solution count and the gcd-count identity (HARD CORE 1)](#phase-g1--the-solution-count-and-the-gcd-count-identity-hard-core-1)
- [Phase G2 — no-carry digit extraction (HARD CORE 2)](#phase-g2--no-carry-digit-extraction-hard-core-2)
- [Phase G3 — assembly: `gcdClosed5` and `gcdClosed5_eq`](#phase-g3--assembly-gcdclosed5-and-gcdclosed5_eq)
- [Phase G4 — the `Era` terms `eraGcd` and `eraPow2Val`](#phase-g4--the-era-terms-eragcd-and-erapow2val)
- [Self-review checklist (run before execution)](#self-review-checklist-run-before-execution)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development to execute this sub-plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** realise `gcd` as a closed `Era` term and, from it,
`2^(v₂ n) = gcd(n, 2^n)` as an `Era` term, unblocking `eraNu2`/`eraSigma`
(M3b plan Phase 3 Task 3.1).

**Why this exists.** M3b plan Task 3.1 assumed a lightweight closed form
for `2^(v₂ n)`; investigation proved none exists over the basis
(exhaustive depth-≤3 search). The only route is a general
`gcd`-as-arithmetic-term. This sub-plan scopes that as a focused
development. Source: Prunescu–Shunia, arXiv:2411.06430, Theorem 4.1
(the base-5 div-mod form, cleaner than Mazzanti's and unconditional for
`a,b ≥ 1`).

**Architecture.** Prove the closed form as a finite `ℕ` identity (NOT via
formal power series). `gcd(a,b)` is the count
`s_{a,b}(ab) = #{(x,y) : a·x + b·y = ab} = gcd(a,b) + 1`, read off as a
base-5 digit by no-carry digit extraction. Then mirror the closed form as
an `ETm` and specialise to `gcd(n, 2^n)`.

**Tech stack:** Lean 4, Mathlib (pin `v4.29.0-rc6`),
`lake build`/`lake test`/`lake lint`, `scripts/check-axioms.sh`.
Constructive-only; axiom-clean.

---

## The closed form (target)

```text
gcdClosed5 a b =
  (⌊ 5 ^ (a*b*(a*b + a + b)) / ((5 ^ (a^2*b) − 1) * (5 ^ (a*b^2) − 1)) ⌋
     mod 5 ^ (a*b)) − 1
```

Theorem 4.1 (arXiv:2411.06430): for `1 ≤ a`, `1 ≤ b`,
`gcdClosed5 a b = Nat.gcd a b`. Base 5 is the smallest base making the
form unconditional (bases 2/3/4 fail only at `(a,b) = (1,1)`); base 5
also gives the carry bound `n + 1 < 5^(n−2)` for `n ≥ 3`. Numerically
validated for `1 ≤ a,b ≤ 7`.

Writing `n := a*b`, the numerator exponent is `n² + a·n + b·n` and the
denominator exponents are `a·n`, `b·n`; the extraction window is `5^n`.

## File structure

- `GebLean/Utilities/ArithClosedForms.lean` (extend): the `ℕ`
  development — the solution count, the two count identities, the
  digit-extraction lemma, and `gcdClosed5` / `gcdClosed5_eq`. Reuses the
  file's existing `private` digit infrastructure (`ofDigits_ofFn`, the
  `Nat.ofDigits_*` usage) and geometric-sum lemmas in
  `EraBoundedSum.lean`.
- `GebLean/EraCompleteness.lean` (extend): the `Era` terms `eraGcd`,
  `eraPow2Val` and their `eval` lemmas.

## Re-checkpoint note

Phases G1 and G2 are the two hard cores (the Diophantine count and the
no-carry extraction). They are decomposed into sub-lemma signatures with
strategy below, not fabricated proof bodies. After G1+G2 land, reassess
G3/G4 against the then-exact shapes. Budget `lean4:sorry-filler-deep` for
the cores. Each sub-lemma is one or more `jj` commits; implementers
verify (`lake build`/`lint`/`check-axioms`), controller commits.

---

## Phase G1 — the solution count and the gcd-count identity (HARD CORE 1)

**Files:** `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **G1.1 — define the solution count (finite).**

```lean
/-- The number of `(x,y) ∈ ℕ²` with `a·x + b·y = n`. Finite for
`1 ≤ a` (then `x ≤ n`), so realised as a `Finset.card`. -/
def solCount (a b n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => a * p.1 + b * p.2 = n)).card
```

Also prove the box-capture helper (needed by G1.2/G1.3 to reason about
membership):

```lean
private theorem mem_solCount_box (a b n x y : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * x + b * y = n) : x < n + 1 ∧ y < n + 1
```

For `1 ≤ a, 1 ≤ b`: `x ≤ a*x ≤ n` and `y ≤ b*y ≤ n` (`Nat.le_mul_of_pos_left`),
so both `< n + 1`. This shows the `range (n+1)²` box captures every
solution, so `solCount` counts them all.

- [ ] **G1.2 — `s_{a,b}(n) ≤ n + 1` (carry bound).**

```lean
theorem solCount_le_succ (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    solCount a b n ≤ n + 1
```

Use the NON-STRICT `≤` form: the strict `<` is FALSE at `a = b = 1`
(`solCount 1 1 n = n + 1` exactly), validated numerically. `≤ n + 1`
holds unconditionally and is all G2 needs (with `n + 1 ≤ 5^n` it gives
the window bound `solCount a b n < 5^n`). Strategy (Lemma 3.2): the map
`(x,y) ↦ (a*x, b*y)` injects the `a·x+b·y=n` solutions into
`{(X,Y) : X+Y=n}` (the `Finset.Nat.antidiagonal n`, card `n+1` via
`Finset.Nat.card_antidiagonal`). Reuse: `Finset.card_le_card` of the
injection. Medium difficulty.

- [ ] **G1.3 — `s_{a,b}(ab) = gcd(a,b) + 1` (the Diophantine count).**

```lean
theorem solCount_mul_eq_gcd_succ (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    solCount a b (a * b) = Nat.gcd a b + 1
```

Strategy (Lemma 3.1, the hardest piece). Let `d := Nat.gcd a b`,
`a = d*a'`, `b = d*b'` with `Nat.Coprime a' b'`. The solutions of
`a*x + b*y = a*b` are exactly `(x, y) = (b' - b'·... )`... precisely:
all integer solutions are `x = b − (b/d)·t`, `y = (a/d)·t`, `t ∈ ℤ`
(Bézout parametrisation from `(x₀,y₀) = (b, 0)`); non-negativity forces
`0 ≤ t ≤ d`, giving `d + 1` solutions. Formalise as a `Finset.card_bij`
(or `Finset.card_nbij'`) between the solution finset and
`Finset.range (d + 1)` via `t ↦ (b − (b/d)*t, (a/d)*t)` with inverse
`(x,y) ↦ y / (a/d)`. Reuse: `Nat.gcd_dvd_left`/`right` (`d ∣ a`, `d ∣ b`),
`Nat.div_mul_cancel`, `Nat.Coprime` to pin the step `b/d = b'`, and the
non-negativity range. The crux is the bijection's well-definedness and
the `0 ≤ t ≤ d` bound; keep all arithmetic in `ℕ` (truncated subtraction
`b − (b/d)*t` is exact because `t ≤ d` ⇒ `(b/d)*t ≤ b`). This is the
largest single proof — budget `lean4:sorry-filler-deep`.

Commit per sub-lemma.

---

## Phase G2 — no-carry digit extraction (HARD CORE 2)

**Files:** `GebLean/Utilities/ArithClosedForms.lean`

> SUPERSEDED AND DONE. Phase G2 was executed under the dedicated
> micro-plan `2026-06-15-era-gcd-g2-floor-extraction-plan.md`. Its
> separate G2.1 (`gcd_floor_modEq_solCount`) and G2.2
> (`solCount_eq_floor_mod`) below are subsumed by the single public
> theorem `solCount_eq_floor_mod` proved there (the stronger exact
> identity `num/den = gcdDigitSum a b` via the two-step `Bᵃ−1`/`Bᵇ−1`
> reduction, the tooth-count bijection `gcd_tooth_count`, and the
> carry-free comb split). G3 below consumes `solCount_eq_floor_mod`.

Target the CONGRUENCE form (both reviewers' recommendation): proving
`⌊…⌋ % 5^(ab) = solCount a b (ab)` factors into a `mod` congruence plus
the window bound, which avoids materialising the whole base-`5^(ab)`
digit list. If `Nat.ofDigits` is used, the base must be the SINGLE big
base `B := 5^(ab)` end-to-end (the lemma `Nat.ofDigits_mod_eq_head!`
extracts `% B`, NOT `% B^k`; do not mix base 5 with `% 5^(ab)`).

- [ ] **G2.1 — the floor congruence.** The floor is congruent to the
solution count modulo the window:

```lean
private theorem gcd_floor_modEq_solCount (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    Nat.ModEq (5 ^ (a*b))
      (5 ^ (a*b*(a*b + a + b)) / ((5 ^ (a^2*b) − 1) * (5 ^ (a*b^2) − 1)))
      (solCount a b (a * b))
```

Strategy: writing `n := a*b`, the floor is the truncated base-`5^n`
positional encoding `Σ_{k} solCount a b k · (5^n)^?` of the geometric
convolution `1/((5^(an)−1)(5^(bn)−1))` (finite geometric sums); modulo
`5^n` only the position-0 block survives, which is `solCount a b (ab)`.
The exponent identities `a^2*b = a*(a*b)`, `a*b^2 = b*(a*b)`,
`a*b*(a*b+a+b) = (a*b)^2 + a*(a*b) + b*(a*b)` connect the closed-form
exponents to the `n = a*b` form (`ring`/`Nat.pow_add`/`pow_mul`). Reuse:
`natGeomSum_eq`/`natGeomSum_mul` (`EraBoundedSum.lean`), the
`ofDigits_ofFn` infra in this file, `Nat.sub_one_mul`,
`(c^m − 1) ∣ (c^(km) − 1)`, `Nat.ModEq` API. HARD — the convolution
identity is the crux; budget `lean4:sorry-filler-deep`.

- [ ] **G2.2 — the no-carry extraction.**

```lean
private theorem solCount_eq_floor_mod (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (5 ^ (a*b*(a*b + a + b)) / ((5 ^ (a^2*b) − 1) * (5 ^ (a*b^2) − 1)))
        % 5 ^ (a*b)
      = solCount a b (a * b)
```

Strategy: from G2.1's congruence, `⌊…⌋ % 5^(ab) = solCount a b (ab) %
5^(ab)`; the window bound `solCount a b (ab) < 5^(ab)` (from G1.2
`solCount a b (ab) ≤ ab + 1` plus `ab + 1 ≤ 5^(ab)` via `Nat.one_le_pow`
/ `Nat.lt_pow_self`) then gives `solCount a b (ab) % 5^(ab) =
solCount a b (ab)` by `Nat.mod_eq_of_lt`. This case is `≤`-bound +
`Nat.ModEq` bookkeeping; the real work is G2.1.

Commit per sub-lemma. RE-CHECKPOINT here: with G1+G2 done, confirm
G3/G4 shapes.

---

## Phase G3 — assembly: `gcdClosed5` and `gcdClosed5_eq`

**Files:** `GebLean/Utilities/ArithClosedForms.lean`

- [ ] **G3.1 — define `gcdClosed5`** (the closed form above), with a
docstring.

```lean
/-- Prunescu–Shunia base-5 gcd closed form (arXiv:2411.06430, Thm 4.1). -/
def gcdClosed5 (a b : ℕ) : ℕ :=
  (5 ^ (a*b*(a*b + a + b)) / ((5 ^ (a^2*b) − 1) * (5 ^ (a*b^2) − 1))
    % 5 ^ (a*b)) − 1
```

- [ ] **G3.2 — `gcdClosed5_eq`.**

```lean
theorem gcdClosed5_eq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gcdClosed5 a b = Nat.gcd a b
```

Strategy: `gcdClosed5 a b = (solCount a b (ab)) − 1
= (gcd a b + 1) − 1 = gcd a b`, chaining G2.2
(`solCount_eq_floor_mod`) and G1.3 (`solCount_mul_eq_gcd_succ`). The
`(1,1)` case needs no special handling at base 5 (it is the reason base 5
was chosen); confirm `gcdClosed5 1 1 = 1` by `decide`/the chain. Numeric
guard: a TEMPORARY `#eval` over `1 ≤ a,b ≤ 6` (then delete) — feasible at
these sizes.

Commit.

---

## Phase G4 — the `Era` terms `eraGcd` and `eraPow2Val`

**Files:** `GebLean/EraCompleteness.lean`

- [ ] **G4.1 — `eraGcd : ETm 2`** mirroring `gcdClosed5` (variables 0=a,
1=b), built from `epow`/`etsub`/`emul`/`ediv`/`emod` and the constant
`5` (a `Tm.succ`-chain numeral) and `1`. Prove

```lean
theorem eraGcd_eval (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tm.eval eraInterp eraGcd ![a, b] = Nat.gcd a b
```

by reducing `eval` to `gcdClosed5` (simp over the term-formers, model
`eraCentralBinom_eval`) then `gcdClosed5_eq`. Note: `5` as an `ETm`
constant is the five-fold `Tm.succ` of `Tm.zero`; pick the cleanest. The
exponents (`a*b*(a*b+a+b)` etc.) are built from `var0`,`var1` via
`emul`/`eadd`/`epow`. The `eval` arithmetic-normalisation may need
`ring_nf` for the exponent shapes.

- [ ] **G4.2 — `eraPow2Val : ETm 1`** as `eraGcd` substituted at
`(var 0, epow2 (var 0))` (via `Tm.subst`/`sub0`), with

```lean
theorem eraPow2Val_eval (n : ℕ) (hn : 1 ≤ n) :
    Tm.eval eraInterp eraPow2Val ![n] = Nat.gcd n (2 ^ n)
```

proved by `Tm.eval_subst` + `eraGcd_eval n (2^n)` (needs `1 ≤ 2^n`,
trivial). The eval target is `Nat.gcd n (2^n)` (exactly what `nu2Closed`'s
body needs); by the existing private `gcd_pow_eq` this value equals
`2^(padicValNat 2 n)` — hence the name `eraPow2Val` — but the lemma is
stated in the `gcd` form so it slots directly into `eraNu2`. Downstream,
`eraNu2` mirrors `nu2Closed`'s `^ (n+1) % base^2 / base` shell around
`eraPow2Val` and closes via `nu2Closed_eq`.

All public theorems (`gcdClosed5_eq`, `eraGcd_eval`, `eraPow2Val_eval`)
and defs (`solCount`, `gcdClosed5`, `eraGcd`, `eraPow2Val`) carry `/-- … -/`
docstrings (lean-coding.md).

Commit per term. After G4, return to the M3b plan: `eraNu2`,
`eraSigma` (Phase 3 Task 3.2 remainder) are then unblocked.

---

## Self-review checklist (run before execution)

- [ ] Every sub-lemma signature is consistent across phases
  (`solCount`, `gcdClosed5`, `eraGcd`, `eraPow2Val`).
- [ ] No fabricated Mathlib names: confirm
  `Finset.card_bij`/`card_nbij'`, `Finset.Nat.antidiagonal`,
  `Nat.gcd_dvd_left`/`right`, `Nat.div_mul_cancel`,
  `Nat.ofDigits_div_pow_eq_ofDigits_drop`,
  `Nat.ofDigits_mod_eq_head!`, `Nat.sub_one_mul` exist in the pin
  (Phase-0 sweep, as in the M3b plan).
- [ ] `Era.lean` untouched; new content in `ArithClosedForms.lean` and
  `EraCompleteness.lean` only.
- [ ] Each committed step: no `sorry`/`admit`/underscore; axiom-clean;
  100-char; docstrings on public decls; pre-commit green.
- [ ] `gcd(n,2^n)` is realised by SUBSTITUTION into the general `eraGcd`,
  not a separate specialised term (no power-of-2 shortcut exists).
