# Era completeness via bounded summation — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [1 Scope and goal](#1-scope-and-goal)
- [2 Route selection](#2-route-selection)
- [3 The completeness statement and its module](#3-the-completeness-statement-and-its-module)
- [4 Architecture: the induction and its two obligations](#4-architecture-the-induction-and-its-two-obligations)
- [5 The bounded-sum engine (Marchenkov § 5)](#5-the-bounded-sum-engine-marchenkov--5)
- [6 The bounded-product engine (via `pow2`)](#6-the-bounded-product-engine-via-pow2)
- [7 Soundness: every term denotes an elementary function](#7-soundness-every-term-denotes-an-elementary-function)
- [8 Corollary: the K-sim-2 hierarchy](#8-corollary-the-k-sim-2-hierarchy)
- [9 Milestones](#9-milestones)
- [10 Transcription versus novel](#10-transcription-versus-novel)
- [11 Acceptance criteria](#11-acceptance-criteria)
- [12 Scope guardrails](#12-scope-guardrails)
- [13 Open questions and risks](#13-open-questions-and-risks)
- [14 References](#14-references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## 1 Scope and goal

The base Era result (`GebLean/Era.lean`) establishes a finite
substitution basis `{add, mod, pow2, tsub, mul, div, pow}` — with
generators `{add, mod, pow2}` per Prunescu–Sauras-Altuzarra–Shunia
(arXiv:2505.23787) — together with a standard interpretation
`Tm.eval eraInterp`, its soundness, and categoricity
(`eraInterp_unique`). What is not yet established is **adequacy**: that
the basis represents *exactly* the Kalmár elementary functions `E³`.

This sub-project proves the harder half, **completeness**: every
elementary function is `Tm.eval eraInterp` of some `ETm`. With the
matching easy half (soundness, every `ETm` denotes an elementary
function) it yields a representational equivalence `Era ≃ E³`.

The result is **semantic**: it concerns the functions denoted by terms
(`Tm.eval`), not derivability in the equation calculus (`Derivable`). It
therefore does not depend on the recovery problem, the order algebra, or
the object-level redundancy theorems E1–E5, which form a separate,
recovery-gated workstream (see § 12).

The reference formalisation of `E³` is `GebLean/LawvereER.lean`'s
`ERMor1` — the inductive transcription of the Wikipedia "Superposition
bases" definition, with bounded summation and bounded product as
primitive constructors.

## 2 Route selection

`E³` admits several equivalent generating systems. Two are available as
formalised targets in this repository:

- `ERMor1` — generators `{zero, succ, proj, sub}` closed under
  composition, **bounded summation**, and **bounded product**
  (Kalmár/Marchenkov presentation).
- `KMor1` / K-sim (`GebLean/LawvereKSim.lean`) — closed under
  **simultaneous primitive recursion** (`simrec`); its second level
  `K-sim-2` is the Axt–Heinermann / LOOP characterisation, and the
  equivalence `LawvereERCat ≌ LawvereKSimDCat 2` (`erKSimEquiv`) is
  already proven (`GebLean/LawvereERKSim/Equivalence.lean`).

Completeness is established by inducting on the target's generators and
implementing each generating *scheme* as an `Era` term. The two routes
differ in which scheme must be implemented:

- **Route A (via `ERMor1`).** The non-trivial cases are `bsum` and
  `bprod`. `ERMor1` is itself the bounded-sum/product presentation, so
  the induction targets its own constructors, with Marchenkov 2007 (§ 5)
  as a direct guidepost.
- **Route B (via `K-sim-2`).** The non-trivial case is `simrec`.
  Implementing primitive recursion as a closed term over a finite
  substitution basis is the Gödel-β maneuver: code the value-history as
  one number and read off `f(n)`. Locating that code is a *bounded
  search*, and bounded search decomposes into bounded sum and product
  (`μ_{z<B} = Σ_{z<B} ∏_{w≤z} …`). Route B is therefore Route A's engine
  *plus* sequence coding — a strict superset.

Route A is chosen. The existing `ERMor1 ≌ K-sim-2` equivalence is not
needed to shorten Route A; conversely, once `Era ≃ ERMor1` is proven,
composing with `erKSimEquiv` yields `Era ≃ K-sim-2 ≃ LOOP ≃
Axt–Heinermann` as a corollary (§ 8), so the hierarchy connection is
inherited rather than re-implemented.

## 3 The completeness statement and its module

Let `f.interp : (Fin n → ℕ) → ℕ` be `ERMor1.interp`
(`GebLean/LawvereER.lean`). The completeness theorem is

```text
theorem era_complete {n : ℕ} (f : ERMor1 n) :
    ∃ t : ETm n, ∀ ctx : Fin n → ℕ, Tm.eval eraInterp t ctx = f.interp ctx
```

proved by structural induction on `f`. The witness map `t` is the
content; the equation is its correctness.

The converse soundness direction (§ 7) is

```text
theorem era_sound_er {n : ℕ} (t : ETm n) :
    ∃ f : ERMor1 n, ∀ ctx, f.interp ctx = Tm.eval eraInterp t ctx
```

Together they give the representational equality `Era ≃ E³` at the level
of denoted functions.

Module placement. `Era.lean` is dependency-free (core Lean 4, no
Mathlib; `namespace Era`), whereas `ERMor1` lives in `namespace GebLean`
and imports Mathlib. The statement straddles both, so it lives in a new
bridge module `GebLean/EraCompleteness.lean` that `import`s
`GebLean.Era` and `GebLean.LawvereER`; `Era.lean` itself is not modified
and retains its no-Mathlib property. The two valuation types coincide
(`ℕ` is `Nat`); only the bridge module incurs the Mathlib dependency.

## 4 Architecture: the induction and its two obligations

The induction on `f : ERMor1 n` has five routine cases and two engine
cases.

- `zero`, `succ`, `proj i`, `sub` — the witnesses are `Tm.zero`,
  `Tm.succ (Tm.var 0)`, `Tm.var i`, and `Tm.var 0 ∸ᵉ Tm.var 1`; the
  equations are immediate from `eraInterp` and the `ERMor1.interp`
  equations.
- `comp f g` — the witness is the substitution of the `g`-witnesses into
  the `f`-witness; correctness is `Tm.eval_subst` (already in
  `Era.lean`) composed with the inductive hypotheses.
- `bsum f`, `bprod f` — these reduce to two term-formers with `eval`
  lemmas, the only mathematically substantial content:

```text
def eraBSum  {k : ℕ} (t : ETm (k + 1)) : ETm (k + 1)
def eraBProd {k : ℕ} (t : ETm (k + 1)) : ETm (k + 1)

eval (eraBSum  t) ctx = natBSum  (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
eval (eraBProd t) ctx = natBProd (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
```

`natBSum` / `natBProd` are the existing `ℕ`-level helpers in
`LawvereER.lean`, matching the `ERMor1.interp` equations for `bsum` /
`bprod` verbatim. With these two `eval` lemmas the induction is
mechanical; without them it does not proceed. The scaffold (§ 9, M1)
erects the induction and the bridge module with the two `eval` lemmas as
the open obligations.

## 5 The bounded-sum engine (Marchenkov § 5)

> **Superseded construction (2026-06-16).** The Marchenkov 2007 digit-sum
> `σ` method described in this section is not the one implemented. Both
> bounded-sum and bounded-product engines are built by the
> Istrate-Prunescu-Shunia recurrence-to-term metatheorem
> (arXiv:2606.09336, Theorem 2), realised through the
> Prunescu-Sauras-Altuzarra hypercube count (arXiv:2407.12928). See the
> Phase 6-7 sub-plan
> (`docs/superpowers/plans/2026-06-16-era-completeness-phase6-7-subplan.md`)
> § Route fidelity and the decision note
> (`docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md`).
> The binding *statements* of § 3, § 4, § 7, § 8, § 11, § 12 are unchanged;
> only this section's construction narrative is superseded.

`eraBSum` is the core. The functional content is a single `ℕ`-level
construction; the `eval` lemma is its correctness.

Why a search-free construction is required. The naive route — code the
sequence of partial sums by a Gödel-β function and recover `Σ` as the
last term — must produce the code `(c, d)` as `Era` terms. The standard
construction obtains `d` as a product of moduli (a bounded product) and
`c` by Chinese-remainder reconstruction from the partial sums (a bounded
sum). Both presuppose the operation being built, so the route is
circular over the bare basis. The repository's `ERMor1.beta`,
`ERMor1.boundedRec`, `ERMor1.boundedSearch` (`Utilities/ERArith.lean`)
do not escape this: they are `ERMor1` terms built *from* `bsum`/`bprod`,
so they presuppose bounded summation rather than supplying it. Marchenkov
2007 (§ 5) avoids the circularity by producing bounded sums from **closed
forms** that use no search; this is the reason for that section's
apparatus.

The construction has three layers.

1. **Geometric / power-sum closed forms.** Sums `Σ_{z≤t} z^i q^z` have
   closed forms `Q_i(q, q^t, t) / (q − 1)^{i+1}` with `Q_i` an integer
   polynomial — Marchenkov 2007, § 5, in the proof of Lemma 7 (p. 358),
   where he notes these are "well known in combinatorics" and does not
   prove them. Each is directly an `Era` term over
   `{add, mul, pow, div, tsub}`, and its correctness is an `ℕ` identity
   proved by induction at the Lean meta-level (no bounded sum
   presupposed). These are the search-free primitives the rest stands
   on.
2. **The digit-sum lemma.** Marchenkov 2007, § 5, Lemma 6 (p. 357),
   packs the summand values `v_i` (`0 ≤ v_i < 2^w`) into a single number
   so that `σ` of the packing equals `w(s + 1 + q)`, with `q` the count
   of zeros among the `v_i`; the bounded sum is recovered from this. Here
   `σ(x)` is the count of `1`-bits of `x`, equal to `exp₂ C(2x, x)` —
   the exponent of `2` in the central binomial coefficient (Kummer's
   theorem; Mazzanti 2002, as cited by Marchenkov p. 355). `Era` realises
   `exp₂` and `C(2x, x)` over `{pow2, mod, div, mul}`.
3. **Exp-diophantine packing.** A basis-term summand `f` is given a
   single-valued exponential-diophantine representation (the class `R`,
   Marchenkov § 4); the bounded sum then becomes a *count of solutions in
   a cube* (Lemma 7, Eq. (13)) by Theorem 2 (p. 358), which Lemma 7
   evaluates through layers 1 and 2. This layer is the heaviest
   transcription and the dominant cost (§ 9 M3, § 13).

Library reuse. The bridge module imports Mathlib, so the `ℕ`-level
number theory is largely available rather than built from scratch.
Layers 1–2: geometric/power-sum closed forms (`geom_sum_eq` and the
`GeomSum` family); the binary digit sum `σ` (`Nat.bitIndices`,
`Nat.digits 2`); and the central-binomial / Kummer identity via
Legendre's formula (`Nat.factorization`, `Nat.centralBinom`,
`Mathlib.Data.Nat.Choose.Factorization`). Layer 3: Mathlib carries the
full Davis–Putnam–Robinson–Matiyasevich development
(`Mathlib.NumberTheory.Dioph` — `Dioph`, `DiophFn`, the predicate
algebra `eq`/`le`/`lt`/`dvd`/`modEq`, closure under `∃`, and
`Dioph.pow_dioph` — over `Mathlib.NumberTheory.PellMatiyasevic`). It is,
however, existence-level: `Dioph S` is a classical `Prop` with unbounded
`∃`, so it supports correctness proofs but does not supply the
constructive, single-valued, bounded `eraBSum` term, which remains the
project's own content (the `noncomputable` ban forbids reading a term
off a classical existence proof). M3 opens by assessing how much of
`Dioph` transfers under these constraints (§ 13). No prior Lean/Mathlib
formalisation of the elementary class or of bounded-sum elimination was
found.

The output is `eraBSum` with its `eval` lemma.

## 6 The bounded-product engine (via `pow2`)

> **Superseded construction (2026-06-16).** Bounded product is not obtained
> by the separate `2^x`-elimination described here (which would depend on
> the untranslated Marchenkov 2003 monograph); it is the product instance
> of the recurrence engine (§ 5 supersession note), eliminating that
> dependency.

Bounded product is not redeveloped from scratch. In the definition of
`E³`, bounded multiplication is eliminable in favour of bounded
summation once `2^x` is available — Marchenkov 2007, § 1 (p. 352):
"in the definition of K we may eliminate bounded multiplication by
adding … the function `2^x`", citing Statement 2.13 of his monograph
*Elementary Recursive Functions* (Marchenkov 2003). His own proof of
`[S] = K` (Corollary 1, p. 359) then establishes only closure under
bounded summation. The `Era` basis carries `pow2`, so `eraBProd` is the
`2^x`-elimination applied to `eraBSum`, not an independent engine.

The construction underlying the elimination resides in the 2003
monograph rather than the 2007 article; obtaining or reconstructing it
is an explicit dependency (§ 13).

## 7 Soundness: every term denotes an elementary function

Each basis operation is an `ERMor1` function. Witnesses for most already
exist in `GebLean/Utilities/ERArith.lean` with proven interpretation
lemmas: `ERMor1.mod`, `ERMor1.div`, `ERMor1.mulN` (`natMul`),
`ERMor1.powN`, and `natAdd`; `tsub` is `ERMor1.sub`, and `pow2` is `pow`
at base `2`. The soundness theorem (§ 3) then follows by induction on
`ETm`, with `comp` discharged by `ERMor1`'s composition. This direction
is largely assembly of existing material and is included so the
deliverable is the equivalence `Era ≃ E³`, not a single inclusion.

## 8 Corollary: the K-sim-2 hierarchy

> **Construction note (2026-06-16).** The corollary is derived from the
> term-level interp-faithfulness lemmas `erToK_interp` / `kToER_interp`
> (the latter carrying its `level ≤ 2` premise), not by extracting an
> equality from the categorical `erKSimEquiv` (which has no semantic
> read-out). The corollary statement — the K-sim-2 function-class identity
> — is unchanged.

`era_complete` and `era_sound_er` give `Era ≃ E³` as denoted-function
classes. `ERMor1` underlies `LawvereERCat`, and `erKSimEquiv :
LawvereERCat ≌ LawvereKSimDCat 2` is proven
(`GebLean/LawvereERKSim/Equivalence.lean`). The induced equality of
denoted-function classes composes to identify `Era`'s functions with
`K-sim-2` — equivalently the Axt–Heinermann second level and the LOOP-2
hierarchy. This is recorded as a corollary; no `K-sim` scheme is
implemented over the basis.

## 9 Milestones

Each milestone is gated by the pre-commit triad
(`bash scripts/pre-commit.sh`), the axiom-clean check (`propext`,
`Quot.sound`, `Classical.choice` only), and a checkpoint commit.

| M | Content | Risk |
| --- | --- | --- |
| M1 | Bridge module `EraCompleteness.lean`; the completeness statement; the five routine cases; the two `eval` lemmas as named obligations | low |
| M2 | Assess whether the rich basis admits a simpler search-free construction (§ 13); then the arithmetic core: geometric/power-sum closed forms; `σ = exp₂ C(2x, x)`; Lemma 6 | moderate |
| M3 | Exp-diophantine class `R` (§ 4) and Theorem 2; `eraBSum` + `eval` lemma | high |
| M4 | Bounded product `eraBProd` via the `pow2` elimination (Marchenkov 2003, Statement 2.13) | moderate |
| M5 | Assemble `era_complete`; the soundness direction (reusing § 7 witnesses); the K-sim-2 corollary via `erKSimEquiv` | low |

M2 begins with an assessment gate; M3 is the dominant effort; M4 depends
on the 2003-monograph construction (§ 13).

## 10 Transcription versus novel

Per the cite-the-literature rule:

- Geometric/power-sum closed forms, the digit-sum lemma and
  `σ = exp₂ C(2x, x)`, the exp-diophantine class `R`, and the
  bounded-sum theorem (§ 5): transcription of Marchenkov 2007 § 4–§ 5
  and Mazzanti 2002.
- Bounded-product elimination via `2^x` (§ 6): transcription of
  Marchenkov 2007 § 1 / Marchenkov 2003, Statement 2.13.
- The completeness statement against `ERMor1`, the bridge module, the
  term-formers `eraBSum` / `eraBProd`, the structural induction, and the
  soundness direction: novel artifacts bridging the cited `ℕ`-level
  results to the `Era` term basis.
- Any `mod (β − 1)` digit-extraction shortcut (§ 13) would be novel, not
  a transcription of Marchenkov's `σ`-method.
- The K-sim-2 corollary: composition of the novel equivalence with the
  existing `erKSimEquiv`.

## 11 Acceptance criteria

- `lake build`, `lake test`, `lake lint` pass; the new content is free of
  `sorry`, `admit`, and underscores; new lines obey the 100-character
  limit.
- `scripts/check-axioms.sh` reports only `propext`, `Quot.sound`,
  `Classical.choice` for every new declaration.
- `eraBSum` and `eraBProd` are defined with their `eval` lemmas proven.
- `era_complete` is proven; the soundness direction `era_sound_er` is
  proven; the K-sim-2 corollary is stated and proven by composition.
- `Era.lean` retains its no-Mathlib property; the Mathlib dependency is
  confined to the bridge module.
- Tests follow the proven-`@[simp]`-lemma discipline; the Gödel-numbering
  interpretations are not exercised by kernel reduction (`#guard`), per
  the recorded hazard.

## 12 Scope guardrails

- Semantic (`Tm.eval`) only. No `Derivable`, no recovery, no order
  algebra, no E1–E5; those remain the separate recovery-gated
  object-level workstream. The verified reduction of recovery to
  `succ_sub_split` is recorded for that workstream, not used here.
- No changes to the generic calculus or to the seven-operation basis;
  `Era.lean` is not edited (the new theorem lives in the bridge module).
- `E³` is referenced through `ERMor1`; the class is not redefined.
- Bounded product is obtained by the `2^x` elimination, not a second
  from-scratch development.
- No `K-sim` scheme is implemented over the basis; the hierarchy
  connection is the § 8 corollary.

## 13 Open questions and risks

- **Search-free simplification (M2 gate).** The basis is richer than
  Marchenkov's minimal `{x+y, x∸y, ⌊x/y⌋, 2^x}` (it carries `mul`,
  `div`, `pow` directly). M2 opens by assessing whether a more direct
  *search-free* bounded-sum term exists over the richer basis — for
  instance a `mod (β − 1)` digit-extraction
  `Σ_{i<y} f(i) = (Σ_{i<y} f(i) · β^i) mod (β − 1)` once the packing is
  available — which could shorten or replace the § 5 transcription. Any
  such route must remain search-free (the Gödel-β route is circular,
  § 5); the `mod (β − 1)` identity in particular does not by itself
  supply the packing, so it is a candidate to evaluate, not a settled
  method. Marchenkov § 5 is the fallback baseline.
- **Exp-diophantine magnitude (M3).** Single-valued exponential-
  diophantine representations (§ 4) are the heaviest transcription;
  their formalisation cost is the principal schedule risk. Mathlib's
  `NumberTheory.Dioph` (`Dioph.pow_dioph`) and `PellMatiyasevic` supply
  the classical number theory, mitigating it, but they are existence-
  level and non-constructive (§ 5 Library reuse); the constructive
  bounded-term construction is not provided. M3 therefore opens by
  assessing how much of `Dioph` transfers, and whether the richer basis
  admits a construction that bypasses the exp-diophantine layer entirely
  (the latter overlaps the search-free assessment above).
- **Monograph dependency (M4).** The `2^x`-elimination construction for
  bounded product is in Marchenkov 2003 (Statement 2.13), a
  Russian-language monograph not yet obtained, rather than the 2007
  article. It must be obtained or reconstructed before M4; until then
  M4's magnitude is uncertain. The repository's `natBProd` and
  `ERMor1`-level product machinery (`Utilities/ERArith.lean`) may shorten
  the reconstruction.
- **`σ` support.** Mathlib supplies the layer-1/2 number theory
  (`geom_sum_eq`; `Nat.bitIndices` / `Nat.digits`; Legendre's formula
  and `Nat.centralBinom`), so `σ = exp₂ C(2x, x)` and the geometric
  closed forms are reuse, not from scratch. What remains project-specific
  is realising `σ` and the closed forms as `Era` *terms* with `eval`
  lemmas (the `ℕ`-level identities are then mathlib citations).
- **Corollary extraction (M5).** `erKSimEquiv` is a categorical
  equivalence; the corollary uses only the induced equality of
  denoted-function classes. The exact lemma extracting that equality
  from the equivalence is to be located during M5.

## 14 References

- R. L. Goodstein, "Logic-free formalisations of recursive arithmetic",
  *Math. Scand.* 2 (1954) 247–261. (Background for the deferred
  object-level workstream.)
- S. S. Marchenkov, "Superpositions of Elementary Arithmetic Functions",
  *J. Appl. Ind. Math.* 1(3) (2007) 351–360,
  doi:10.1134/S1990478907030106. (§ 4–§ 5: bounded-sum elimination via
  the digit-sum lemma and exp-diophantine representations; § 1:
  bounded-product elimination via `2^x`.)
- S. S. Marchenkov, *Elementary Recursive Functions* (Moskovskii Tsentr
  Nepreryvnogo Matematicheskogo Obrazovaniya, Moscow, 2003) [in Russian].
  (Statement 2.13: bounded-product elimination via `2^x`; cited as [6] in
  Marchenkov 2007.)
- S. Mazzanti, "Plain Bases for Classes of Primitive Recursive
  Functions", *MLQ* 48:1 (2002) 93–104. (`σ(x) = exp₂ C(2x, x)`.)
- M. Prunescu, L. Sauras-Altuzarra, J. M. Shunia, "A Minimal Substitution
  Basis for the Kalmár Elementary Functions", *J. Logic & Computation*
  (2026), arXiv:2505.23787. (The Era generator basis.)
- Mathlib (available through the bridge module):
  `Mathlib.NumberTheory.Dioph` (`Dioph`, `DiophFn`, `Dioph.pow_dioph`)
  and `Mathlib.NumberTheory.PellMatiyasevic` (the diophantine layer);
  `geom_sum_eq` and the `GeomSum` family (geometric closed forms);
  `Nat.bitIndices`, `Nat.digits`, `Nat.centralBinom`, and
  `Mathlib.Data.Nat.Choose.Factorization` (Legendre's formula, for `σ`).
- Repository: `GebLean/LawvereER.lean` (`ERMor1`, `interp`, `natBSum`,
  `natBProd`); `GebLean/Utilities/ERArith.lean` (`ERMor1.mod`, `div`,
  `mulN`, `powN`, `beta`, `boundedRec`, `boundedSearch`);
  `GebLean/LawvereKSim.lean` (`KMor1`, `simrec`);
  `GebLean/LawvereERKSim/Equivalence.lean` (`erKSimEquiv :
  LawvereERCat ≌ LawvereKSimDCat 2`); `GebLean/Era.lean` (the basis,
  `Tm.eval`, `eraInterp`, `Tm.eval_subst`).
