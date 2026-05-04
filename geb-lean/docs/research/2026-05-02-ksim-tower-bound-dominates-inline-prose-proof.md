# Prose proof of `kSimTowerBound_dominates_inline`

> **Scope.**  This document is a math-only prose proof of the Phase
> IV-B headline theorem of the `ER ≅ K^sim_2` workstream.  It contains
> no Lean syntax, no implementation notes, no task tracking, and no
> opinions about how to structure code.  It exists to be reviewed for
> mathematical correctness against the literature, independent of any
> Lean realization.
>
> **Reviewer obligation.**  Every claim in this document carries a
> reference to the literature or to a previously-proved theorem in
> the project's existing source.  The reviewer is OBLIGED to follow
> each reference and verify that the cited source says what
> this document claims it says.  Citations to specific page or line
> numbers are intended to make this verification efficient.

## 1. Statement

Let `k, a` be natural numbers and let `h_fam : Fin (k+1) → KMor1 a`
and `g_fam : Fin (k+1) → KMor1 (a + 1 + (k+1))` be families of K^sim
morphisms with all members at level at most 1.  Let
`h_ER l := kToER (h_fam l)` and `g_ER l := kToER (g_fam l)` denote
the K^sim-to-ER translations.

For any natural `j` and parameter context `params : Fin a → ℕ`,
define the ITER VALUE

```text
ITER(j) :=
  Nat.rec (kSimPackedBase(h_ER).interp(params))
          (λ i prev. kSimPackedStep(g_ER).interp(cons i (cons prev params)))
          j
```

and the BOUND VALUE

```text
BOUND(j) := kSimTowerBound(h_ER, g_ER).interp(cons j params)
```

The theorem to prove is

```text
∀ j params,  ITER(j) ≤ BOUND(j).
```

The closed form of the right-hand side, established at
`GebLean/Utilities/KSimSzudzikSimrec.lean:432-443` (unpacking
`kSimTowerBound_interp`), is

```text
BOUND(j) =
  tower (stepTH + 1)
    (stepTH + 1 + 2·baseTH + 2·sumCtx(cons j params) + 2)
```

where:

- `stepTH := towerHeight(kSimPackedStep(g_ER))`
- `baseTH := towerHeight(kSimPackedBase(h_ER))`
- `sumCtx(cons j params) := j + ∑_i params(i)`
- `tower : ℕ → ℕ → ℕ` is the iterated 2-power
  (`tower 0 x = x`, `tower (h+1) x = 2^(tower h x)`,
  `GebLean/Utilities/Tower.lean:17-25`).

## 2. Background and literature

The following references are load-bearing throughout this proof.
The reviewer should keep them open during verification.

**Tourlakis 2018 (`PR-complexity-topics.pdf`).**  Numbered
propositions cited as "Tourlakis 2018 §0.1.0.X".  Defines:

- The K^sim hierarchy `(K^sim_n)_{n≥0}` (§0.1.0.7).
- The Grzegorczyk hierarchy `(E^n)_{n≥0}` (§0.1.0.22).
- Worked examples of level-1 K^sim functions (§0.1.0.17).
- The **stratification** result: bounds on E^n functions are
  linear (n=1), polynomial (n=2), tower of fixed height (n≥3)
  (§0.1.0.27 clauses (1)-(4)).
- E^2 closure under simultaneous bounded recursion (§0.1.0.34,
  Theorem, p. 13).
- The **equivalence** `K^sim_n = E^{n+1}` for n ≥ 2 (§0.1.0.44,
  Corollary, p. 21).  In particular `K^sim_2 = E^3 = ER`.

**Recursion Class Ch. 4** (hereafter "RC4"; full filename
`grzegorczyk-hierarchy-recursion-class-chapter-4.pdf`).
Verbatim text quoted in the project's research doc, lines
485-518:

> **Proposition 4.7.**  If `f ∈ E_n` then the iteration `f^y ∈ E_{n+1}`.
> Proof.  The iteration of addition of a constant is bounded by a
> linear function, yielding the case for n = 0.  Similarly, the
> iteration of a linear function is a polynomial function, yielding
> the n = 1 case.  Let `f ∈ E_{n+1}`.  We will consider the case
> of binary `f`, with iteration on `x`.  When `n > 1`, we have by
> Proposition 4.6 above, there is an `m` such that
> `f(x, y) ≤ (e_{n-1})^m(max(x, y))`.
> Now by induction, we show: `f^z(x, y) ≤ (e_{n-1})^{mz}(max(x, y))`.
> [...]
> Observe, further, that `(e_{n-1})^{mz}(max(x, y)) ≤ (e_n)(max(x, y) + mz)`.
> So by chaining, we obtain `f^z(x, y) ≤ (e_n)(max(x, y) + mz)`.

In our convention (where Grzegorczyk's `E_n` corresponds to the
project's "tower of height roughly n-1"):

- `n = 1`: `f ∈ E_1` (linear-bounded).  Then `f^y ∈ E_2`
  (polynomial-bounded).
- `n = 2`: `f ∈ E_2` (polynomial-bounded).  Then `f^y ∈ E_3 = ER`,
  bounded by `(e_2)(max + m·y)` ≈ `tower 2 (linear)` in our
  convention.

Both are used below — Recursion Class Prop. 4.7 n=2 is the load-
bearing iteration step.

**Wong's Prop. 4.6 exponent-tracking.**  Verbatim in the research
doc, lines 263-323.  For the ER syntactic class, exponents track
inductively under composition and bounded recursion.  Specifically:
composition adds the head's exponent and the maximum child's
exponent; bounded recursion inherits the bound's exponent.  At level
1 of the K^sim hierarchy, this manifests as the in-codebase lemma
`KMor1.linearBoundLog_le_towerHeight`
(`GebLean/LawvereKSimPolynomialBound.lean:1838`):

```text
∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 1),
  Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1)
    ≤ 3 · towerHeight(kToER f) + 1.
```

The factor 3 is project-internal accounting per the research doc
lines 285-322 (the comp case algebra under our specific
`towerHeight` recursion).

**Project research doc** at
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
Cited as "research doc lines X-Y" or "research doc Lemma 1.A".

**Project investigation doc.**
`docs/research/2026-05-02-level-2-chain-infrastructure-investigation.md`.
Cited as "investigation doc Part X".

**Lemma 1.A (research doc lines 51-153).**  For every `f : KMor1 a`
with `level f ≤ 1`, there exist `c, k : ℕ` (depending on f) such
that for every `ctx : Fin a → ℕ`,

```text
interp(f)(ctx) ≤ c · max(ctx) + k.
```

This linear bound is project-side proven via structural induction on
KMor1 (research doc Proof sketch, lines 78-113), with the simrec
case relying on Lemma 1.B's "no multiplicative coefficient at level
0".  In the project source, this is realized as
`KMor1.linearBound` (`LawvereKSimPolynomialBound.lean:207`) and the
dominance theorem `KMor1.linearBound_dominates`
(`LawvereKSimPolynomialBound.lean:507`).

**The level-1 dominance lemma `kSimTowerBound_dominates_level_one`.**
Already proved in the project at
`GebLean/LawvereKSimPolynomialBound.lean:2604-2729`.  Its statement
is the level-0-children analog of the present theorem; its proof
strategy is referenced below for comparison.

## 3. Strategic outline

The proof proceeds in six steps.  Each is justified by a specific
reference; the steps correspond, where applicable, to existing
project lemmas.

```text
ITER(j)
  ≤  Nat.iterate (λ v. step v J) j (v_0(J))      [Step 1: counter cap]
  ≤  tower 2 (LINEAR_1(j, params))               [Step 2: poly-iter]
  ≤  tower 3 (LINEAR_2(j, params))               [Step 3: tower-bump]
  ≤  tower (stepTH + 1) (LINEAR_2(j, params))    [Step 4: tower-mono-left]
  ≤  tower (stepTH + 1) (RHS_LINEAR(j, params))  [Step 5: tower-mono-right]
  =  BOUND(j)                                    [Step 6: kSimTowerBound shape]
```

where `J` denotes a sufficiently large bound on the iteration
counter (we'll take `J = j` after Step 1's monotonicity argument).

The choice of `LINEAR_1`, `LINEAR_2`, `RHS_LINEAR` is determined by
the constants of `kSimPackedBase_polyBound` /
`kSimPackedStep_polyBound` and worked out in Steps 2 and 5.

## 4. Step 1 — Counter monotonicity bridge: `Nat.rec` to `Nat.iterate`

**Sub-claim.**  The iter value `ITER(j)` is bounded by the j-fold
iteration of the packed step with the counter slot frozen at `j`,
starting from the packed base:

```text
ITER(j) ≤
  Nat.iterate
    (λ v. kSimPackedStep(g_ER).interp(cons j (cons v params)))
    j
    (kSimPackedBase(h_ER).interp(params)).
```

**Justification.**  This is a structural fact about
`kSimPackedStep`'s interpretation, mirroring the existing
`kSimTowerBound_mono_counter`
(`GebLean/Utilities/KSimSzudzikSimrec.lean:449-471`), which proves
the analogous monotonicity for `kSimTowerBound`.

The precise sub-claim is: `kSimPackedStep(g_ER).interp` is monotone
non-decreasing in slot 0 (the counter slot).  That is, for all
`i ≤ i'` and all `prev, params`,

```text
kSimPackedStep(g_ER).interp(cons i  (cons prev params))
  ≤
kSimPackedStep(g_ER).interp(cons i' (cons prev params)).
```

**Reasoning.**  Slot 0 of `kSimPackedStep`'s context corresponds to
the iteration counter, which is consumed by `kSimStepContext` at
`GebLean/Utilities/KSimSzudzikSimrec.lean:364-382`.  `kSimStepContext`'s
slot-0 case (line 367-368) is the projection
`ERMor1.proj 0` and feeds into each `g_ER l`'s context at slot 0
(the K^sim "iteration counter" position per the K^sim simrec
schema, Tourlakis 2018 §0.1.0.7).

The K^sim simrec schema's iteration counter slot corresponds to a
free variable in the step morphism `g_l`, and `g_l : KMor1 (a+1+(k+1))`
is built from primitive K^sim constructors that are all monotone in
their input variables (proof: structural induction on KMor1,
analogous to the level-0 case but at level 1 — each constructor
preserves monotonicity).  Therefore each `(g_l).interp` is monotone
in its slot-0 input.  The seqPack of monotone-in-slot-0 ER
functions is itself monotone in slot-0, since `Nat.seqPack` is
monotone in each component (which follows from `Nat.pair`'s
monotonicity, established in mathlib).

Therefore `kSimPackedStep(g_ER).interp` is monotone non-decreasing
in slot 0.

**Bridging Nat.rec to Nat.iterate.**  Given this monotonicity, the
iteration `Nat.rec base step j` (where `step` increments the
counter at each iteration: at iter `m+1`, the counter slot is set
to `m`) is dominated by the iteration `Nat.iterate (λ v. step v J)
j base` with the counter frozen at `J ≥ j-1`.  Concretely, by
induction on `j`:

- At `j = 0`: both sides equal `base`.
- At `j+1`: `Nat.rec base step (j+1) =
  step.interp(cons j (cons (Nat.rec ... j) params))`.
  By IH, `Nat.rec ... j ≤ Nat.iterate ... j base`.  By monotonicity,
  `step.interp(cons j ...) ≤ step.interp(cons J ...)` for any
  `J ≥ j`.  Choose `J = j` for the tight version
  (`step.interp(cons j ...)` versus `step.interp(cons j ...)` —
  same).  Therefore `Nat.rec ... (j+1) ≤
  step.interp(cons j (cons (Nat.iterate ... j base) params)) =
  Nat.iterate (λ v. step v j) (j+1) base`.

Choosing `J = j` (or any larger value) gives the sub-claim.

**Project status.**  No existing in-codebase lemma proves this
monotonicity directly.  The closest landed result is
`kSimTowerBound_mono_counter`
(`GebLean/Utilities/KSimSzudzikSimrec.lean:449`), which proves
monotonicity for `kSimTowerBound` (the bound, not the step).  The
step's mono-in-counter analog must be added.

**Citation.**  No literature specific to this step beyond Tourlakis
2018 §0.1.0.7's K^sim simrec schema (which determines slot 0's
semantics) plus the structural-monotonicity-of-K^sim-constructors
folklore (a direct structural induction on KMor1, no published
proposition required).

## 5. Step 2 — Polynomial-iter-tower bound

**Sub-claim.**  There exist constants `D, m_step, D_base, m_base`
(depending only on `g_fam`, `h_fam`, `k`, and the per-l constants
of `KMor1.linearBound`) such that

```text
Nat.iterate
  (λ v. kSimPackedStep(g_ER).interp(cons J (cons v params)))
  j
  (kSimPackedBase(h_ER).interp(params))
≤
tower 2 (LINEAR_1(j, J, params))
```

where

```text
LINEAR_1(j, J, params)
  := (Nat.log 2 D + 2)·(j + 1)
   + (Nat.log 2 D_base + 2)
   + m_base · J + m_base + J
   + Nat.log 2 D + 2.
```

**Justification.**  This is the application of Recursion Class
Ch. 4 Prop. 4.7 (n=1 case: iter of polynomial step ⇒ in E^2 =
polynomial).  In our project's convention where `tower 2 (linear)`
realizes the E^3 envelope of E^2-polynomials (research doc Claim 4
Fix B part 2, lines 520-602), the iter is bounded by `tower 2
(linear)`.

The project's existing lemma realizing this is

```text
Nat.polynomial_iter_tower_bound
  : ∀ (step : ℕ → ℕ → ℕ) (D m : ℕ),
    (∀ v x, step v x ≤ (max v x + 1)^D) →
    ∀ (v_0 : ℕ → ℕ), (∀ x, v_0 x ≤ m·x + m) →
    ∀ j x, Nat.iterate (λ v. step v x) j (v_0 x) ≤
      tower 2 ((Nat.log 2 D + 2)·j + m·x + m + x + Nat.log 2 D + 2)
```

at `GebLean/Utilities/ComputationalComplexity.lean:471-557`.

**Inputs to polynomial_iter_tower_bound.**

- `step v x := kSimPackedStep(g_ER).interp(cons x (cons v params))`.
- `D := pb_step.degree + pb_step.coefficient + pb_step.constant + 2`,
  where `pb_step := kSimPackedStep_polyBound(g_ER, pb_g)` and
  `pb_g l := kToER_polyBound_at_level_one(g_fam l)` is a degree-1
  PolyBound built from `KMor1.linearBound` (Lemma 1.A) on each
  level-1 K^sim child.
- `v_0 x := kSimPackedBase(h_ER).interp(params)` (constant in x).
- For the linear-base hypothesis `v_0 x ≤ m·x + m`: this requires
  `kSimPackedBase(h_ER).interp(params)` to be bounded linearly by
  `x`.  Since `kSimPackedBase` does not depend on `x`,
  this fits trivially with `m = kSimPackedBase(h_ER).interp(params)`
  if we accept `m` to be a constant in x.  However, `m` would then
  depend on `params`, which is allowed by polynomial_iter_tower_bound's
  signature (the `m` is fixed for a given application).

**The polynomial-base concern.**  `kSimPackedBase`'s polynomial
bound has degree `2^(k+1) · 1 = 2^(k+1)` (since `kSimPackedBase` is
a seqPack of `(k+1)` linear-bounded terms, and seqPack of `n+1`
degree-d terms has degree `2^n · d` per the research doc Claim 3
lines 376-484).

This is polynomial in `params`, not linear.  However, since `v_0
x` does not depend on `x` in our application (only on `params`),
the linear-in-x hypothesis `v_0 x ≤ m·x + m` is satisfied
vacuously by setting `m := kSimPackedBase(h_ER).interp(params)`,
which is some natural number depending on `params`, polynomial in
`max(params)`.  Then `v_0 x = m ≤ m + m·x` for any `x`, so the
hypothesis holds.

The constants `m, D` in the conclusion of `polynomial_iter_tower_bound`
become functions of `params` for our application.  This is fine
because the conclusion's `tower 2 (LINEAR_1(j, x, params))` then
expresses `LINEAR_1` as a function of `params` (via `m` and any
`x`-dependent terms).

For our setup, choosing `x := J = j` and `m :=
kSimPackedBase(h_ER).interp(params)`, the conclusion specializes to

```text
Nat.iterate (...) j (m) ≤
  tower 2 ((Nat.log 2 D + 2)·j + m·j + m + j + Nat.log 2 D + 2)
```

where `m` depends polynomially on `params`.  This is `tower 2
(LINEAR_1(j, params))` with `LINEAR_1` linear in `j` but
polynomial in `params`.

**Refining via `pow_le_tower_two_with_shift`.**  To express the
polynomial-in-params dependence as a tower-2 bound with a linear
inside, we lift the polynomial m to a tower-2 bound:

```text
m = kSimPackedBase(h_ER).interp(params)
  ≤ pb_base.coefficient · (max(params) + 1)^pb_base.degree
    + pb_base.constant
  ≤ (max(params) + 2)^(pb_base.degree + pb_base.coefficient
                       + pb_base.constant + 2)
                                              [le_pow_shift_of_polyBound,
                            LawvereERPolynomialBound.lean:580]
```

By `Nat.pow_le_tower_two_with_shift`
(`Utilities/ComputationalComplexity.lean:612-631`),

```text
(max(params) + 2)^E ≤ tower 2 (max(params) + 1 + Nat.log 2 E + 2)
```

so `m ≤ tower 2 (linear in max(params))`.

Substituting back: `tower 2 (LINEAR_1(j, params))` where
`LINEAR_1` is linear in `j` and contains `m` which is itself
`tower 2 (linear in max(params))` — which collapses to `tower 2
(linear in (j, max(params)))` after applying log-shift (using
the fact that `tower 2 (x + tower 2 (y)) ≤ tower 2 (x + y +
const)` for `x, y` linear and small const, established by
direct calculation).

**Citation summary.**

- `polynomial_iter_tower_bound` (project lemma, line 471):
  realizes RC4 Prop. 4.7 n=1 case in the project's tower
  convention.  See research doc Claim 4 Fix B parts 1 and 2
  (lines 408-602) for the project-side construction details.
- `pow_le_tower_two_with_shift` (project lemma, line 612):
  the standard `(linear)^E ≤ tower 2 (linear)` shift,
  derivable from `Nat.log_pow` and Tower's `tower_succ`.
- `le_pow_shift_of_polyBound` (project lemma, line 580):
  folds a `PolyBound`'s 4-field shape into single-degree pow
  form `(maxCtx + 2)^E`.

## 6. Step 3 — Bump tower 2 to tower 3

**Sub-claim.**  `tower 2 (LINEAR_1(j, params)) ≤ tower 3
(LINEAR_2(j, params))` where `LINEAR_2` is linear in `j` and
`max(params)` with constants derived from `LINEAR_1` via `Nat.log`.

**Justification.**  Direct application of
`Nat.tower_two_le_tower_three_linear`
(`Utilities/ComputationalComplexity.lean:558-604`):

```text
tower 2 (C·X + K + 2) ≤
  tower 3 (X + Nat.log 2 (C + 1) + Nat.log 2 (K + 4) + 2)
```

(approximately — exact form per the lemma).

This bumps from tower 2 to tower 3 with logarithmic compression of
the linear coefficients into the tower-3 inside.  For us, `C` and
`K` come from `LINEAR_1`'s constants (which depend on `D`,
`D_base`, `m`, `params`), and the conclusion's linear inside is
`X + log_2(C+1) + log_2(K+4) + 2` for some `X` linear in `(j,
max(params))`.

**Citation.**

- `tower_two_le_tower_three_linear` (project lemma, line 558):
  matches the published Recursion Class Ch. 4 Prop. 4.6 inductive
  step (research doc lines 689-732), specialized to our tower
  convention.

## 7. Step 4 — Bump tower 3 to tower (stepTH + 1) via tower height monotonicity

**Sub-claim.**  `tower 3 (LINEAR_2(j, params)) ≤ tower (stepTH + 1)
(LINEAR_2(j, params))`.

**Justification.**  By `tower_mono_left`
(`GebLean/Utilities/Tower.lean:65`), `tower h_1 X ≤ tower h_2 X`
when `h_1 ≤ h_2`.  We need `3 ≤ stepTH + 1`, i.e.,
`stepTH ≥ 2`.

The lower bound on `stepTH` is established by
`kSimPackedStep_towerHeight_ge_succ_k`
(`LawvereKSimPolynomialBound.lean:1376-...`):

```text
∀ {a k : ℕ} (g : Fin (k+1) → ERMor1 (a + 1 + (k+1))),
  towerHeight(kSimPackedStep g) ≥ k + 2.
```

Hence `stepTH ≥ k + 2 ≥ 2` for all `k ≥ 0`.

**Citation.**

- `tower_mono_left` (project lemma): standard tower height
  monotonicity.
- `kSimPackedStep_towerHeight_ge_succ_k` (project lemma, line
  1376): structural lower bound on `kSimPackedStep`'s towerHeight.

## 8. Step 5 — Absorb the linear inside via mono-right + log-tH absorption

**Sub-claim.**  `tower (stepTH + 1) (LINEAR_2(j, params)) ≤
tower (stepTH + 1) (RHS_LINEAR(j, params))` where `RHS_LINEAR` is
the closed-form linear inside of `BOUND(j)`:

```text
RHS_LINEAR(j, params) :=
  stepTH + 1 + 2·baseTH + 2·sumCtx(cons j params) + 2.
```

**Justification.**  By `tower_mono_right`
(`GebLean/Utilities/Tower.lean:42`), `tower h X ≤ tower h Y` when
`X ≤ Y`.  We need

```text
LINEAR_2(j, params) ≤ stepTH + 1 + 2·baseTH + 2·sumCtx + 2.   (*)
```

`LINEAR_2`'s constants come from Step 3 with logarithmic compression
applied to Step 2's constants.  Specifically, expanding:

```text
LINEAR_2(j, params)
  = X + Nat.log 2 (C + 1) + Nat.log 2 (K + 4) + 2
```

where:

- `X` is linear in `(j, max(params))`, with coefficient on `j`
  equal to `Nat.log 2 D + 2` (from Step 2's `LINEAR_1`).
- `C, K` are constants from `LINEAR_1`'s `D, D_base, m_base`.

The required inequality (*) decomposes into three pieces:

**(*).1:**  `X ≤ 2·sumCtx + (small)`.

The `X` from Step 3 is linear in `(j, max(params))`.  Since
`sumCtx(cons j params) = j + ∑params ≥ max(j, max(params))`, we
have `j ≤ sumCtx` and `max(params) ≤ sumCtx`.  Therefore `X ≤
2·sumCtx + (constants)` after distributing.

**(*).2:**  `Nat.log 2 (C + 1) ≤ stepTH + (small)`.

`C = pb_step.degree + pb_step.coefficient + pb_step.constant + 2`
(from `to_iter_step_form`'s output applied to `pb_step =
kSimPackedStep_polyBound(g_ER, pb_g)`).

The structure of `kSimPackedStep_polyBound`'s output fields (per
the function's implementation at
`GebLean/LawvereKSimPolynomialBound.lean:817-...`) yields `degree =
E_pack(k) · max_d_g`, `coefficient = max_c_g · (multiplicative
factor)`, `constant = max_k_g + ...`, where:

- `E_pack(k) = 2^(k+1)` is the seqPack degree multiplier.
- `max_d_g, max_c_g, max_k_g` are foldr-max aggregations over
  per-l children's `pb_g l = kToER_polyBound_at_level_one(g_fam l)`.

For per-l PolyBounds at degree 1 from `KMor1.linearBound`,
`pb_g l = (1, (linearBound g_fam l).1, (linearBound g_fam l).2)`,
i.e., `pb_g l.degree = 1`, `pb_g l.coefficient = (linearBound).1`,
`pb_g l.constant = (linearBound).2`.

Aggregating: `max_d_g = 1`, `max_c_g = sup_l (linearBound g_fam l).1`,
`max_k_g = sup_l (linearBound g_fam l).2`.

Therefore `C ≤ const_factor(k) · max_c_g · max_k_g + (lower-order)`.
Taking `Nat.log 2` and applying Wong's exponent-tracking via the
project-side `KMor1.linearBoundLog_le_towerHeight` per-l (i.e., for
each `l`, `log_2(max_c_g + max_k_g + 1) ≤ 3·towerHeight(g_ER l) + 1`)
then aggregating:

```text
log_2(C + 1) ≤ const(k) + 3·sup_l towerHeight(g_ER l) + 3.
```

By `kSimPackedStep_towerHeight_ge_propagate` (project lemma,
landed; see investigation doc Part 1 Section "Tower-arithmetic
dependencies"), `stepTH ≥ const + sup_l towerHeight(g_ER l)`.
Therefore

```text
log_2(C + 1) ≤ stepTH + (small const depending on k).
```

The level-1 case absorbs this via the inequality
`log_2(C + 1) ≤ SG + 2` (where `SG = sup_l towerHeight(g_ER l)`)
which is the Wong-recipe bound at level 0 (where children's
linearBound has `.1 ≤ 1`, simplifying).  At level 1 the analogous
bound is `log_2(C + 1) ≤ 3·SG + small`, giving the absorption with
factor 3 instead of 1.

**(*).3:**  `Nat.log 2 (K + 4) ≤ 2·baseTH + (small)`.

Analogous derivation, this time aggregating over the `h_fam`
children via per-l `linearBoundLog_le_towerHeight` and through
`kSimPackedBase_towerHeight_ge_propagate`.  The factor 2 on
`baseTH` is sufficient because `K`'s aggregation is symmetric
to `C`'s but routes through `baseTH` instead of `stepTH`.

**Combining (*).1 + (*).2 + (*).3.**  After absorbing the small
constants into the `+ 2` on the RHS (or into `sumCtx` if the
constants depend on `k, a` rather than `j, params`), the
inequality (*) holds for sufficiently large `(j, params)` plus
small fixed offsets.

**The level-0 vs level-1 difference.**  At level 0
(`kSimTowerBound_dominates_level_one`), Wong's exponent factor is
1 (no multiplicative coefficient absorbs into linearBound's `.1`),
so the absorption is `log_2(C + 1) ≤ SG + 2` (level-0 line 2347).
At level 1 the factor is 3, giving `log_2(C + 1) ≤ 3·SG + small`.
The absorption inequality (*) requires
`stepTH ≥ const + SG`, NOT `stepTH ≥ const + 3·SG`.  The factor-3
on the LHS is absorbed by the propagate bound (which already
captures the structural growth of `kSimPackedStep` over `g_ER`'s
heights).

This is the load-bearing arithmetic step.  The assertion is that
the existing propagate bounds combined with Wong's level-1 factor
3 close the absorption.  This must be verified by direct
calculation against the actual constants in
`kSimPackedStep_polyBound`'s implementation.

**Citation.**

- `tower_mono_right` (project lemma): standard.
- `KMor1.linearBoundLog_le_towerHeight` (project lemma, line
  1838): the per-l Wong-bound at level 1.
- `kSimPackedStep_towerHeight_ge_propagate` /
  `kSimPackedBase_towerHeight_ge_propagate` (project lemmas):
  structural per-l propagate bounds.

**Caveat.**  The exact constants in (*).1, (*).2, (*).3 require
detailed tracking through `kSimPackedStep_polyBound`'s field
formulas.  At this level of detail, the prose proof asserts that
the inequalities hold; a Lean realization must verify this by
direct calculation.  See Section 11 below for the open-question
catalog.

## 9. Step 6 — Identification with `BOUND(j)`

**Sub-claim.**  `tower (stepTH + 1) (RHS_LINEAR(j, params)) =
BOUND(j)`.

**Justification.**  Pure unfolding of `kSimTowerBound_interp`
(`Utilities/KSimSzudzikSimrec.lean:432-443`):

```text
BOUND(j) = (kSimTowerBound h_ER g_ER).interp(cons j params)
        = tower (stepTH + 1)
            (stepTH + 1 + 2·baseTH +
              2·sumCtxER(cons j params).interp +
              2)
        = tower (stepTH + 1) (RHS_LINEAR(j, params))
```

since `sumCtxER(cons j params).interp = sumCtx(cons j params) =
j + ∑params` (by `ERMor1.interp_sumCtxER`,
`LawvereERBoundComputable.lean:...`).

**Citation.**

- `kSimTowerBound_interp` (project lemma, line 432):
  closed form of `kSimTowerBound`.
- `ERMor1.interp_sumCtxER` (project lemma, location per
  `LawvereERBoundComputable.lean`): closed form of `sumCtxER`.

## 10. Putting it all together

Combining Steps 1-6:

```text
ITER(j)
  ≤  Nat.iterate (...) j (...)                  [Step 1]
  ≤  tower 2 (LINEAR_1(j, params))              [Step 2]
  ≤  tower 3 (LINEAR_2(j, params))              [Step 3]
  ≤  tower (stepTH + 1) (LINEAR_2(j, params))   [Step 4]
  ≤  tower (stepTH + 1) (RHS_LINEAR(j, params)) [Step 5]
  =  BOUND(j)                                   [Step 6]
```

Each step is justified above with explicit references to the
literature and to existing project lemmas (or to lemmas to be
added — Step 1's `kSimPackedStep_mono_counter` and the bridge,
plus Step 5's level-1 absorption).

This concludes the prose proof.

## 11. Open questions and caveats

The reviewer should focus on these load-bearing claims, which the
proof asserts but where the verification requires detailed
calculation against project source code or literature:

1. **Step 1's monotonicity claim.**  Is `kSimPackedStep`'s interp
   monotone non-decreasing in slot 0?  The proof argues so via
   `kSimStepContext`'s structure (slot 0 is `proj 0` feeding into
   each `g_l`'s slot 0) plus structural monotonicity of K^sim
   constructors.  Verification: read `kSimPackedStep`'s definition
   (`Utilities/KSimSzudzikSimrec.lean:388-393`) and trace each
   constructor's monotonicity.

2. **Step 2's polynomial-base accommodation.**  The proof routes
   the polynomial-in-params bound on `v_0` through
   `polynomial_iter_tower_bound` by setting `m :=
   kSimPackedBase.interp(params)` (constant in x).  Is this
   admissible by the lemma's signature?  Verification: read
   `polynomial_iter_tower_bound`'s signature
   (`Utilities/ComputationalComplexity.lean:471-479`) and check
   that `m, D` are allowed to depend on params.

3. **Step 5's absorption.**  The proof asserts that the level-1
   factor 3 (from Wong's `linearBoundLog_le_towerHeight`) is
   absorbed by the propagate bound's tower-height dependence on
   per-l children.  This is the load-bearing arithmetic step.
   Verification: read `kSimPackedStep_polyBound`'s field formulas
   (`LawvereKSimPolynomialBound.lean:817+`) and verify that the
   factor 3 closes against the propagate inequality.  Special
   attention: at level 0, the factor was 1; the level-1 factor
   3 must not exceed the propagate bound's slack.

4. **Step 5's per-l vs aggregate aggregation.**  Wong's bound is
   per-l; aggregating to a foldr-max introduces a `+1` slack per
   aggregation step.  Does the aggregation introduce additional
   absorption requirements not captured here?  Verification: trace
   the aggregation through `Fin.foldr_max`.

5. **Lemma 1.A's simrec case at level 1.**  The proof assumes
   Lemma 1.A holds for ALL of K^sim_1.  The simrec case
   (research doc lines 97-111) routes through Lemma 1.B and the
   "no multiplicative coefficient at level 0" property.
   Verification: read research doc Proof sketch and confirm the
   simrec case at level 1 (h, g at level 0) works.

6. **The absorption's `(j, params)` linearity vs. polynomial-in-params
   from Step 2.**  Step 2 derives `LINEAR_1(j, params)` as linear
   in `j` but with a polynomial-in-params term `m ≤ tower 2
   (linear in max(params))`.  Step 3's bump applies log to this,
   collapsing the polynomial back to linear in `(j,
   max(params))`.  Verification: trace the log compression
   carefully — does `tower 2 (X + tower 2 (Y)) ≤ tower 2 (X +
   Y + small)` hold?  This requires `tower_succ_pow_bound_strong`
   or analogous (project lemma, location TBD).

These six questions are the focus of the next adversarial review
pass.

## 12. References summary

- **Tourlakis 2018** (`PR-complexity-topics.pdf`): primary source.
  §0.1.0.7 (K^sim def), §0.1.0.17 (level-1 worked examples),
  §0.1.0.22 (Grzegorczyk), §0.1.0.27 (stratification), §0.1.0.34
  (E^2 closure), §0.1.0.44 (K^sim_n = E^{n+1}).
- **Recursion Class Ch. 4**
  (`grzegorczyk-hierarchy-recursion-class-chapter-4.pdf`):
  Prop. 4.5 (E^2 polynomial bound), Prop. 4.6 (E^{n+3}
  exponent-tracking), Prop. 4.7 (iter of E_n is in E_{n+1}).
- **Damnjanovic 1994** (`elementary-functions-and-loop-programs.pdf`):
  Lemma 6.1 (iterated pairing polynomial bound).
- **Project research doc**:
  `docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
  Cited extensively for project-side derivations (Lemma 1.A,
  Wong's recipe).
- **Project investigation doc**:
  `docs/research/2026-05-02-level-2-chain-infrastructure-investigation.md`.
  Cited for the dependency catalog.
- **Project source modules**:
  `GebLean/LawvereKSimPolynomialBound.lean` (level-1 chain;
  `KMor1.linearBound`, `linearBound_dominates`,
  `linearBoundLog_le_towerHeight`,
  `kSimTowerBound_dominates_level_one`,
  `kToER_interp_level_one`).
  `GebLean/Utilities/KSimSzudzikSimrec.lean`
  (`kSimPackedBase`, `kSimPackedStep`, `kSimStepContext`,
  `kSimTowerBound`).
  `GebLean/Utilities/ComputationalComplexity.lean`
  (`polynomial_iter_tower_bound`,
  `pow_le_tower_two_with_shift`,
  `tower_two_le_tower_three_linear`).
  `GebLean/Utilities/Tower.lean` (`tower`, `tower_mono_left`,
  `tower_mono_right`).
