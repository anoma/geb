# eraBSum construction-choice decision

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Purpose and decision](#1-purpose-and-decision)
- [2 The construction problem](#2-the-construction-problem)
- [3 Route 1 — Mathlib Dioph: rejected (Prop-level only)](#3-route-1--mathlib-dioph-rejected-prop-level-only)
- [4 Route 2 — direct rich-basis closed form: rejected as standalone](#4-route-2--direct-rich-basis-closed-form-rejected-as-standalone)
- [5 Route 3 — Marchenkov σ method: chosen construction](#5-route-3--marchenkov-%CF%83-method-chosen-construction)
- [6 Era-term obligations and the eval lemma](#6-era-term-obligations-and-the-eval-lemma)
- [7 eraBProd via the pow2 elimination](#7-erabprod-via-the-pow2-elimination)
- [8 Mathlib reuse and from-scratch cost](#8-mathlib-reuse-and-from-scratch-cost)
- [9 Magnitude estimate and recommended M3 staging](#9-magnitude-estimate-and-recommended-m3-staging)
- [10 References](#10-references)

<!-- END doctoc -->

## 1 Purpose and decision

This note records the Task 4 (spec M2/M3) gate decision for the
bounded-sum term former `eraBSum`, the engine of the Era-basis
completeness direction. It evaluates the three candidate routes (spec
§ 5, § 13), records the obstruction or cost of each, and names one
construction with its `Era`-term obligations and `eval` lemma,
sufficient to drive the follow-on engine plan.

Decision. `eraBSum` is built by the Marchenkov 2007 § 5 digit-sum
(`σ`) method (route 3). The two alternatives are rejected as the
source of the term:

- Route 1 (Mathlib `Dioph`) cannot supply a computable term under the
  `noncomputable` ban; it is `Prop`-level only (§ 3).
- Route 2 (a direct rich-basis closed form) does not close for an
  arbitrary summand: the `mod (β − 1)` digit-extraction identity is
  true (verified in Lean) but only recovers a sum from a base-`β`
  packing it cannot itself produce search-free (§ 4).

The rich basis `{add, mod, pow2, tsub, mul, div, pow}` does not change
the route choice, but it does reduce route 3's cost: the layer-1 and
`σ` closed forms are direct terms over the basis, and the `ℕ`-level
identities are Mathlib citations rather than fresh developments (§ 6).

## 2 The construction problem

The completeness induction (spec § 4) requires, for `bsum`, an `Era`
term `eraBSum t : ETm (k + 1)` with

```text
eval (eraBSum t) ctx
  = natBSum (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
```

where variable `0` of `t` is the loop index and `ctx 0` the bound
(`GebLean/LawvereER.lean`, `natBSum`; `ERMor1.interp_bsum`). The Era
basis carries no recursion or search scheme — only composition — so
`eraBSum t` must be a closed composition term.

Why this is hard. The naive route codes the partial-sum sequence by a
Gödel-`β` function and reads off the last term; producing that code
needs a bounded product (the moduli) and a bounded sum (the
Chinese-remainder reconstruction), so it presupposes the operation
being built (spec § 5). The repository's `ERMor1.beta`,
`ERMor1.boundedRec`, `ERMor1.boundedSearch`
(`GebLean/Utilities/ERArith.lean`) do not escape this: they are
`ERMor1` terms built from `bsum`/`bprod`. Induction on the summand
term does not close either: bounded sum is additive
(`Σ (g + h) = Σ g + Σ h`) but has no closed form for `Σ (g · h)`,
`Σ 2^g`, or `Σ (g mod h)` with both factors index-dependent. The only
sums with closed forms are geometric and power sums; route 3 is the
device that re-expresses an arbitrary bounded sum through them.

## 3 Route 1 — Mathlib Dioph: rejected (Prop-level only)

`Mathlib.NumberTheory.Dioph`
(`.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean`) defines

```text
def Dioph {α : Type u} (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type u) (p : Poly (α ⊕ β)), ∀ v, S v ↔ ∃ t, p (v ⊗ t) = 0
```

with `DiophFn f := Dioph {v | f (v ∘ some) = v none}` and
`pow_dioph : DiophFn f → DiophFn g → DiophFn (fun v => f v ^ g v)`.

Obstruction. `Dioph S` is `Prop`-valued and carries two nested
unbounded existentials: `∃ (β : Type u)` (an arbitrary witness type)
and, inside the iff, `∃ t` over an unbounded witness vector
`t : β → ℕ`. The file has no `Decidable`/`DecidablePred` instance and
no computable extractor for the witness `β`, `p`, or `t`. Recovering a
value therefore goes through `Classical.choice` (via `Exists.choose`),
which Lean marks `noncomputable`; `lake build` under
`-DwarningAsError` rejects it. `DiophFn`/`pow_dioph` inherit this: they
assert a function's graph is Diophantine — a classical existence fact —
and never compute the value.

Consequence. `Dioph` can support `ℕ`-level correctness proofs but
cannot define the constructive `eraBSum` term. It is not used.

## 4 Route 2 — direct rich-basis closed form: rejected as standalone

Route 2 asks whether the richer basis admits a search-free closed-form
bounded sum, bypassing the `σ` machinery. The probe (throwaway module,
since deleted) verified the candidate identity in Lean and located the
obstruction.

The `mod (β − 1)` digit-extraction identity. For `1 ≤ β`,

```text
Nat.ModEq (β - 1)
  (natBSum y (fun i => f i * β ^ i)) (natBSum y f)
```

(`β ≡ 1 (mod β − 1)`, so `β ^ i ≡ 1`, so the base-`β` packed number is
congruent to the plain sum modulo `β − 1`), and when
`natBSum y f < β − 1` the `mod` recovers the sum exactly:

```text
(natBSum y (fun i => f i * β ^ i)) % (β - 1) = natBSum y f
```

Both were proved by induction on `y` over `Nat.ModEq`; the proofs are
short.

Why it is insufficient. The packed number
`Σ_{i<y} f(i) · β^i` is itself a bounded sum over the arbitrary
sequence `f(i) · β^i`, with no closed form. The identity extracts a sum
from a packing it cannot itself produce. The circularity is independent
of the rich basis (§ 2). The identity is retained as a usable component
once a packing is available, not as the engine.

Genuine sub-cases that do close (the rich basis pays off here):

- Constant summand: `natBSum y (fun _ => c) = y * c`
  (`natBSum_const`), directly the `mul` term.
- Summand polynomial in the loop index: closed via the
  geometric/power-sum forms of § 5 (Faulhaber), expressible over
  `{add, mul, div, pow, tsub}`.

These do not generalise to an arbitrary `Era`-term summand, so route 2
is not the construction.

## 5 Route 3 — Marchenkov σ method: chosen construction

The construction has three layers (spec § 5; Marchenkov 2007 § 4–§ 5).

Layer 1 — geometric / power-sum closed forms. Sums `Σ_{z≤t} z^i q^z`
have closed forms `Q_i(q, q^t, t) / (q − 1)^{i+1}` with `Q_i` an
integer polynomial (Marchenkov 2007, Lemma 7, p. 358). Each is an
`Era` term over `{add, mul, pow, div, tsub}`; its correctness is an
`ℕ` identity proved by induction. These are the only sums used, and
they are closed-form.

Layer 2 — the digit sum `σ`. `σ(x)` is the number of `1`-bits of `x`,
equal to `exp₂ C(2x, x)` — the exponent of `2` in the central binomial
coefficient (Kummer; Mazzanti 2002). Marchenkov's Lemma 6 (p. 357)
packs the summand values into one number whose `σ` equals the bounded
sum (plus a zero-count correction). `Era` realises `σ`, `exp₂`, and
`C(2x, x)` over `{pow2, mod, div, mul}`.

Layer 3 — the counting reduction. A summand is turned into a count of
solutions in a cube (Marchenkov Lemma 7, Eq. (13); Theorem 2, p. 358),
which layers 1–2 then evaluate. In Marchenkov's minimal basis this
needs a single-valued exponential-diophantine representation of the
summand (the class `R`, § 4), because his basis cannot compute the
summand directly. In the Era basis the summand `f(i)` is itself a
basis term, computable directly; whether that lets the counting
reduction be encoded as a geometric sum without the full `R`-class is
the first question M3 settles, with Marchenkov § 5 as the proven
fallback. This layer is the dominant cost (§ 7).

## 6 Era-term obligations and the eval lemma

The follow-on plan delivers, in `GebLean/EraCompleteness.lean` (and
`Utilities/` for reusable `ℕ`-level lemmas):

- `eraGeomPowSum` family (layer 1): `Era` terms for the closed-form
  power sums, each with an `ℕ`-identity `eval` lemma proved by
  induction. Reuse `geom_sum_eq` and the `GeomSum` family for the base
  geometric series; the power-weighted forms `Σ z^i q^z` are derived
  (absent from Mathlib).
- `eraSigma` (layer 2): an `Era` term for `σ` with
  `eval (eraSigma t) ctx = σ (eval t ctx)`, where `σ` is `(Nat.digits
  2 ·).sum` (equivalently `(Nat.bitIndices ·).length`); the
  `σ = exp₂ C(2x, x)` bridge assembled from
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` at `p = 2`,
  `Nat.centralBinom`, and a `digits 2 (2x)`-shift step.
- `eraBSum` (layer 3): `eraBSum : ETm (k + 1) → ETm (k + 1)` with

  ```text
  eval (eraBSum t) ctx
    = natBSum (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
  ```

  built from the counting reduction over layers 1–2. The `eval` lemma
  is the substantial obligation; `natBSum` is the existing
  `LawvereER.lean` helper, matching `ERMor1.interp_bsum` verbatim.

## 7 eraBProd via the pow2 elimination

`eraBProd` is not a second from-scratch engine. In `E³`, bounded
multiplication is eliminable in favour of bounded summation once `2^x`
is available (Marchenkov 2007 § 1, p. 352, citing Statement 2.13 of
Marchenkov 2003). The Era basis carries `pow2`, so

```text
eraBProd : ETm (k + 1) → ETm (k + 1)
eval (eraBProd t) ctx
  = natBProd (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
```

is the `2^x`-elimination applied to `eraBSum`. The elimination
construction is in the 2003 monograph (Russian), not the 2007 article;
obtaining or reconstructing it is the M4 dependency (spec § 13). The
repository's `natBProd` and `ERMor1`-level product machinery
(`Utilities/ERArith.lean`) may shorten the reconstruction.

## 8 Mathlib reuse and from-scratch cost

Verified against the local pin (`v4.29.0-rc6`):

- Present, expected signatures: `geom_sum_eq` (`x ≠ 1`, over a
  `DivisionRing`), the `GeomSum` family (`geom_sum`, `geom_sum_mul`,
  `geom_sum₂` …); `Nat.centralBinom`
  (`= (2 * n).choose n`); `Nat.bitIndices`, `Nat.digits`,
  `digits_two_eq_bits`; the Kummer digit-sum lemma
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` and Legendre
  `sub_one_mul_padicValNat_factorial`; the full `Dioph` API.
- Absent, derive from scratch: power-weighted geometric sums
  `Σ i · x^i` and `Σ_{z≤t} z^i q^z` (no Mathlib lemma; induction or
  differentiation of the geometric identity); a named `popcount` and
  the `σ = exp₂ C(2x, x)` identity (assemble from the Kummer lemma at
  `p = 2`, the `padicValNat`↔`factorization` bridge, and a
  `digits 2 (2x)`-shift; ingredients all present).
- No prior Lean/Mathlib formalisation of the elementary class or of
  bounded-sum elimination exists; the term-level construction is new on
  a deep Mathlib base.

## 9 Magnitude estimate and recommended M3 staging

Estimated effort, relative:

- Layer 1 (`eraGeomPowSum` + `ℕ` identities): moderate. Base geometric
  series is Mathlib; power-weighted forms are induction proofs.
- Layer 2 (`eraSigma`, `σ = exp₂ C(2x, x)`): moderate. Ingredients
  present; the assembly and the `Era`-term realisation are the work.
- Layer 3 (counting reduction, `eraBSum` + `eval` lemma): high; the
  dominant cost and principal schedule risk (spec § 13).

Recommended follow-on staging. In the spec's M-numbering (spec § 9),
layers 1–2 are milestone M2 and layer 3 is milestone M3; the
`M3a`/`M3b` labels below are session-local sub-divisions of those
milestones (`M3a` ⊂ spec M2; `M3b` = the M2 remainder plus spec M3),
introduced here for the "then re-gate" staging:

- M3a — layers 1–2 (Mathlib-backed): the power-sum `Era` terms and
  `eraSigma`, each with its `eval`/identity lemma.
- M3b — layer 3: first assess whether the directly-computable summand
  lets the counting reduction be encoded as a geometric sum without the
  full exp-diophantine `R`-class; if not, transcribe Marchenkov § 5
  Lemma 7 / Theorem 2. Deliver `eraBSum` and its `eval` lemma.
- M4 — `eraBProd` via the `2^x` elimination (depends on the 2003
  monograph construction).
- M5 — assemble `era_complete`; the K-sim-2 corollary via
  `erKSimEquiv`.

## 10 References

- S. S. Marchenkov, "Superpositions of Elementary Arithmetic
  Functions", J. Appl. Ind. Math. 1(3) (2007) 351–360,
  doi:10.1134/S1990478907030106. (§ 4–§ 5 bounded-sum elimination; § 1
  bounded-product elimination.)
- S. S. Marchenkov, Elementary Recursive Functions (Moscow, 2003) [in
  Russian]. (Statement 2.13: bounded-product elimination via `2^x`.)
- S. Mazzanti, "Plain Bases for Classes of Primitive Recursive
  Functions", MLQ 48:1 (2002) 93–104. (`σ(x) = exp₂ C(2x, x)`.)
- Companion spec:
  `docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`.
- Phase-1 plan:
  `docs/superpowers/plans/2026-06-14-era-completeness-bounded-sum-plan.md`.
- Mathlib: `Mathlib.NumberTheory.Dioph`; `geom_sum_eq` and the
  `GeomSum` family; `Nat.centralBinom`, `Nat.bitIndices`,
  `Nat.digits`, `Mathlib.Data.Nat.Choose.Factorization`,
  `Mathlib.NumberTheory.Padics.PadicVal.Basic`.
- Repository: `GebLean/LawvereER.lean` (`ERMor1`, `natBSum`,
  `natBProd`, `interp_bsum`); `GebLean/Utilities/ERArith.lean`;
  `GebLean/Era.lean` (`ETm`, `Tm.eval`, `eraInterp`).
