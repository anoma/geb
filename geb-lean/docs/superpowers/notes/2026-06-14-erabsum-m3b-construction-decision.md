# eraBSum / eraBProd construction — M3b re-gate decision

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Purpose and decision](#1-purpose-and-decision)
- [2 Relationship to the Task-4 decision and the spec](#2-relationship-to-the-task-4-decision-and-the-spec)
- [3 The construction problem (recalled)](#3-the-construction-problem-recalled)
- [4 The chosen construction](#4-the-chosen-construction)
  - [4.1 Ingredient closed forms](#41-ingredient-closed-forms)
  - [4.2 The hypercube counting engine](#42-the-hypercube-counting-engine)
  - [4.3 The recurrence-to-term engine and bsum/bprod](#43-the-recurrence-to-term-engine-and-bsumbprod)
- [5 Numeric validation](#5-numeric-validation)
- [6 Lean formalisation obligations](#6-lean-formalisation-obligations)
- [7 The majorant prerequisite](#7-the-majorant-prerequisite)
- [8 Recommended M3b staging](#8-recommended-m3b-staging)
- [9 Transcription versus novel](#9-transcription-versus-novel)
- [10 References](#10-references)

<!-- END doctoc -->

## 1 Purpose and decision

This note records the M3b re-gate decision for the bounded-sum and
bounded-product term formers `eraBSum` and `eraBProd`, the engines of
the Era-basis completeness direction (spec
`docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`,
§ 5, § 6, § 13; M2/M3 gate). It refines the Task-4 decision note
(`2026-06-14-erabsum-construction-decision.md`), which selected route 3
(the Marchenkov 2007 § 5 digit-sum `σ` method) but left the construction
of the `σ`-packing and the `exp₂` term as an open question entangled
with bounded search.

Decision. The construction is the Prunescu–Sauras-Altuzarra hypercube
counting method (the constructive realisation of route 3 in the Era
basis), packaged for `eraBSum` and `eraBProd` by the Istrate–Prunescu–
Shunia recurrence-to-term metatheorem. Concretely:

- The `σ` / `exp₂` crux is resolved: the `2`-adic valuation, the
  central binomial coefficient, the binary digit sum, and the
  generalised geometric progressions are all explicit closed-form
  arithmetic terms over the basis `{add, tsub, mul, div, mod, pow}`
  (equivalently `{add, mod, pow2}`), with literature references and
  numeric validation (§ 5).
- `eraBSum` and `eraBProd` are obtained as the `k = 1` instances of the
  general recurrence-to-term engine (`a(m+1) = a(m) + f(m)` and
  `a(m+1) = a(m) · f(m)`), each requiring only an arithmetic-term
  majorant of the summand. This eliminates the dependency on the
  untranslated Marchenkov 2003 monograph (Statement 2.13) that the spec
  flagged for `eraBProd` (§ 6, § 13).

Source. The construction is transcribed from peer-reviewed and arXiv
sources in the identical operation set, superseding a raw transcription
of Marchenkov 2007 § 5 (a Springer article leaning on the untranslated
2003 monograph). The chosen sources are the same research lineage that
the Era basis paper (arXiv:2505.23787) belongs to, and the project
already transcribes from it (`Era.lean`'s `esq` is that paper's
Theorem 1).

## 2 Relationship to the Task-4 decision and the spec

The Task-4 note rejected routes 1 (Mathlib `Dioph`, `Prop`-only) and 2
(direct `mod (β − 1)` digit-extraction, which cannot itself produce the
packing) and selected route 3. It identified the open question as
whether the directly-computable Era summand lets the counting reduction
be encoded without the full exponential-Diophantine `R`-class.

This re-gate answers that question and the spec's two M2/M3 gate items
(§ 13: "search-free simplification" and "exp-diophantine magnitude"):

- The directly-computable summand does not remove the need for a
  Diophantine encoding of the summand's graph. Forming the digit
  packing `Σ_{i<y} f(i) · βⁱ` is itself a bounded sum over an arbitrary
  sequence and has no closed form; structural recursion on the summand
  term fails for the `Σ (g · h)`, `Σ 2^g`, `Σ (g mod h)` cases (Task-4
  note § 2). The unique escape is the hypercube counting method, which
  re-expresses the packing as a count of Diophantine solutions that
  factors into the generalised geometric progressions (the only
  closed-form sums).
- The full Davis–Putnam–Robinson–Matiyasevich apparatus is not needed.
  The encoding required is the elementary term-to-Diophantine reduction
  of the recurrence paper's Lemma 2 (a sum-of-squares, simple,
  unique-witness, explicitly bounded system), by induction on term
  structure. This is the dominant formalisation cost (§ 6).

## 3 The construction problem (recalled)

The completeness induction (spec § 4) requires

```text
eval (eraBSum  t) ctx = natBSum  (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
eval (eraBProd t) ctx = natBProd (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
```

with variable `0` of `t` the loop index and `ctx 0` the bound
(`GebLean/LawvereER.lean`: `natBSum`, `natBProd`, `interp_bsum`,
`interp_bprod`). The Era basis carries no recursion or search scheme —
only composition — so each must be a closed composition term.

## 4 The chosen construction

### 4.1 Ingredient closed forms

Each is a closed-form arithmetic term over the basis. `Era` term
realisations compose the existing formers
`eadd`/`etsub`/`emul`/`ediv`/`emod`/`epow`/`epow2` (`Era.lean`).
`G₀` is already delivered as `eraGeomSum` / `natGeomSum_eq` (M3a). All
formulas were validated numerically (§ 5).

```text
G_r(q,t) = Σ_{k=0}^{t} k^r q^k        (generalised geometric progression)
  G0(q,t) = (q^(t+1) − 1) / (q − 1)
  G1(q,t) = (t·q^(t+2) − (t+1)·q^(t+1) + q) / (q − 1)^2
  G2(q,t) = (t^2·q^(t+3) − (2t^2+2t−1)·q^(t+2) + (t+1)^2·q^(t+1)
             − q^2 − q) / (q − 1)^3

gcd(m,n)  : Mazzanti base-2 closed form (method paper, Lemma 3.3);
            an alternative base-5 form appears in the recurrence
            paper § 3.

ν2(m)     = floor( ( gcd(m, 2^m)^(m+1) mod (2^(m+1) − 1)^2 )
                   / (2^(m+1) − 1) )
            (method paper, Theorem 2.1: the SLOW, log-free form — the
            one realised as an Era term; see the de-cycling note below.
            A faster log-bounded form (Theorem 9.4, exponent ⌊log₂ m⌋+3)
            exists but is used only for numeric probes, never in terms.).

C(2n,n)   = ( floor( (1 + 2^(2n))^(2n) / 2^(2n^2) ) ) mod 2^(2n)
            (central binomial coefficient).

HW(n)     = ν2( C(2n,n) )            (Hamming weight = binary digit sum
            σ; Kummer's theorem; method paper via Mazzanti Lemma 4.2).

δ(a,w)    = (2^w − 1)(2^w − a + 1)    for 0 ≤ a < 2^w; the indicator:
            HW(δ(a,w)) = 2w if a = 0, else w   (method paper Lemma 3.1).
```

### 4.2 The hypercube counting engine

Method paper (arXiv:2407.12928) Lemma 3.1–3.3, Theorem 3.4,
Corollary 3.6. To count the zeros of a simple exponential polynomial
`P` over a cube `{0,…,t−1}^k`, given an arithmetic-term width `w` with
`0 ≤ P(ā) < 2^w` on the whole cube:

```text
M = Σ_{ā ∈ cube} 2^(2 w · v(ā)) · δ( P(ā), w ),   v(ā) = mixed-radix index
#{ ā : P(ā) = 0 } = HW(M) / w − t^k
```

`M` is a closed-form term because the cube-sum factorises (Lemma 3.2):

```text
Σ_{ā ∈ cube} Πᵢ aᵢ^(uᵢ) vᵢ^(aᵢ) = Πᵢ G_{uᵢ}(vᵢ, t − 1)
```

so each monomial of `δ(P, w)` becomes a product of `G`-terms (Eqs (7),
(8)). Corollary 3.6: only `{HW, G₀, G₁, G₂}` are needed, since a chain
of auxiliary variables reduces every non-exponential occurrence to
degree ≤ 2.

### 4.3 The recurrence-to-term engine and bsum/bprod

Recurrence paper (arXiv:2606.09336) Theorem 2 / Corollary 2: a sequence
`a(m+k) = F(m, a(m),…,a(m+k−1))` with `F` an arithmetic term and an
arithmetic-term majorant `A` with `a(j) < A(j, ā)` for all `j ≤ n` has a
closed-form term

```text
a(n) = floor( H(n, ȳ) / A(n, ȳ)^n )
```

where `H` codes the whole value-history in base `A` (positional coding,
Lemma 3) and the read-off extracts the last digit; `H` is built by the
hypercube count of § 4.2 applied to the Diophantine encoding of the
recurrence step (Lemma 2). Specialisations (`k = 1`):

```text
eraBSum  :  s(0)=0, s(m+1) = s(m) + f(m)   ⇒  Σ_{i<y} f(i)  = floor(H/A^y)
eraBProd :  p(0)=1, p(m+1) = p(m) · f(m)   ⇒  Π_{i<y} f(i)  = floor(H/A^y)
```

Both `eraBSum` and `eraBProd` use the recurrence engine. A direct 2-D
count `Σ_{i<y} f(i) = #{ (i,w) : i<y, w<f(i) }` was considered but is not
used: it diverges from both source papers (which represent every bounded
sum only through the recurrence metatheorem, never a lattice-point count),
and its predicate `w < f(i)` is not separable for a general summand, so
the packed number would not factorise via the cube-sum identity. Building
the general engine once yields both formers and positions Route-B `simrec`
(a `k`-ary recurrence) for any later work, without committing to it here.
See the Phase 6-7 sub-plan
(`docs/superpowers/plans/2026-06-16-era-completeness-phase6-7-subplan.md`)
§ Route fidelity.

## 5 Numeric validation

A throwaway probe (pure-`ℕ` integer arithmetic, outside the repository;
the project's `#eval` hazard concerns symbolic `Tm.eval` reduction, not
plain `ℕ`) validated every ingredient closed form against a reference
implementation:

- `gcd` (base-2 and base-5), `C(2n,n)`, `ν2` (both the slow Theorem 2.1
  form and the fast Theorem 9.4 form), `HW = ν2(C(2n,n))` against
  population count, the `δ` indicator, and `G₀/G₁/G₂`: all agree.
- Two findings the probe surfaced, incorporated above:
  - `G₁`'s constant term is `+ q`, not `+ 1` (a transcription slip from
    the source's notation); corrected in § 4.1.
  - De-cycling (corrected by the M3b plan's adversarial review;
    supersedes an earlier conclusion in this note). The term-level `HW`
    must use the SLOW, log-free `ν2` (Theorem 2.1), NOT the fast one:
    the fast `ν2` (Theorem 9.4) depends on `⌊log₂⌋` (Theorem 9.3), which
    is realised through the count engine via `HW`, which uses `ν2` — a
    def/proof cycle `count → HW → ν2(fast) → ⌊log₂⌋ → count`. The slow
    `ν2` carries no logarithm and breaks the cycle. Its term forms
    `2^m`-sized numbers internally, so it is not numerically evaluable
    on large arguments such as `C(2n,n)` — but that is irrelevant: the
    term's `eval` lemma is proved, never computed. The fast `ν2` is
    correct only as a throwaway numeric probe (where evaluability is the
    concern), never in a committed term.

## 6 Lean formalisation obligations

The Lean obligation is the `eval` identity for each former (§ 3); the
closed term is the witness. Correctness rests on:

- the ingredient `ℕ`-identities of § 4.1 (each an induction or algebra
  proof; Mathlib supplies `geom_sum_eq`, `Nat.centralBinom`,
  `padicValNat`, the Kummer/Legendre lemma
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`, `Nat.gcd`);
- `HW`-additivity over non-overlapping base-`2^(2w)` blocks (Lemma 3.3);
- the cube-sum factorisation (Lemma 3.2) and the positional read-off
  (Lemma 3 / `floor(H/A^n)`);
- the dominant cost: Lemma 2, the induction on `ETm` producing a
  bounded, unique-witness, sum-of-squares Diophantine system for the
  recurrence step, carrying the four invariants (sum-of-squares, simple,
  unique witness, explicit bounds) through every term constructor.

All ingredients are closed terms with no `Classical.choice` in
computational content, so the `noncomputable` ban and axiom-clean
discipline (`propext`, `Quot.sound`, `Classical.choice` only) are
preserved; `Era.lean` retains its no-Mathlib property and the new
content lives in the bridge module and `Utilities/`.

## 7 The majorant prerequisite

The engine requires an arithmetic-term majorant `A(y, x̄)` with
`f(i) < A` for all `i < y` (and analogously a product majorant). It is
constructible by induction on the summand term `f` — the monotone
elementary majorant that the spec flagged as a likely first sub-task
(handoff) — or mechanically by the recurrence paper's Claim 2 recipe
(replace every `tsub` by `add` and substitute the range bound for each
unknown). The majorant fixes the packing width `w` and is independent of
the rest of the construction; it is the recommended first M3b sub-task.

## 8 Recommended M3b staging

For the follow-on plan (`superpowers:writing-plans`), in dependency
order:

1. Monotone arithmetic-term majorant for an `ETm` summand, with its
   `ℕ`-bound lemma.
2. Ingredient terms and `ℕ`-identities: `G₁`, `G₂` (extend M3a's `G₀`);
   `2^(v₂ n)` (gcd-light); the slow log-free `ν2` (Theorem 2.1);
   `C(2n,n)`; `HW`; the `δ` indicator with its `HW`-value lemma. (No
   `⌊log₂⌋`/fast-`ν2` term — see the de-cycling note in § 5.)
3. The hypercube engine: cube-sum factorisation, the packed number `M`,
   the count read-off `HW(M)/w − t^k` (Theorem 3.4 / Corollary 3.6).
4. Lemma 2: `ETm`-to-Diophantine reduction (the dominant task; consider
   isolating the four invariants as a structure carried by the
   induction).
5. The recurrence read-off (positional coding, `floor(H/A^n)`) and
   Theorem 2.
6. `eraBSum`, `eraBProd` as the `k = 1` instances, each with its `eval`
   lemma against `natBSum` / `natBProd`.
7. Assemble `era_complete` (spec § 4) and the K-sim-2 corollary
   (spec § 8); the soundness direction `era_sound_er` already exists
   (`EraCompleteness.lean`).

Stage 2 is partly Mathlib-citation work; stage 4 is the principal
schedule risk and the natural re-checkpoint.

## 9 Transcription versus novel

- The ingredient closed forms (§ 4.1), the hypercube counting engine
  (§ 4.2), and the recurrence-to-term metatheorem (§ 4.3): transcription
  of arXiv:2407.12928 and arXiv:2606.09336 (themselves building on
  Mazzanti 2002, Marchenkov 2007, Matiyasevich, Kummer/Legendre).
- The `Era`-term realisations, the `eval` lemmas against `natBSum` /
  `natBProd`, the `ETm`-to-Diophantine reduction specialised to the Era
  term language, and the structural-induction completeness assembly:
  novel artifacts bridging the cited results to the Era basis.

## 10 References

- M. Prunescu, L. Sauras-Altuzarra, "On the representation of
  number-theoretic functions by arithmetic terms", arXiv:2407.12928.
  (The method: `δ` indicator, cube-sum factorisation, packed number,
  Theorem 3.4 count, Corollary 3.6; `ν_p` Theorems 2.1 / 9.4; integer
  logarithm Theorem 9.3; central binomial; `HW`; `G_r`.)
- G. Istrate, M. Prunescu, J. M. Shunia, "Undecidability, Chaos and
  Universality in Arithmetic Terms", arXiv:2606.09336. (Theorem 2 /
  Corollary 2 recurrence-to-term; Lemma 2 term-to-Diophantine; Lemma 3
  positional coding.)
- M. Prunescu, L. Sauras-Altuzarra, J. M. Shunia, "A Minimal
  Substitution Basis for the Kalmár Elementary Functions",
  arXiv:2505.23787. (The Era basis; Theorem 1, transcribed as
  `Era.lean`'s `esq`.)
- J. M. Shunia, L. Sauras-Altuzarra, "Arithmetic Terms for Multinomial
  Coefficient Sums", arXiv:2312.00301. (Partial sums of binomial
  coefficients; an alternative source for the layer-2 sums.)
- S. S. Marchenkov, "Superpositions of Elementary Arithmetic Functions",
  J. Appl. Ind. Math. 1(3) (2007) 351–360. (Route 3, the digit-sum `σ`
  method that the above realise constructively.)
- S. Mazzanti, "Plain Bases for Classes of Primitive Recursive
  Functions", MLQ 48:1 (2002) 93–104. (`σ(x) = exp₂ C(2x, x)`; the
  base-2 `gcd` term.)
- Companion spec:
  `docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`.
- Task-4 decision:
  `docs/superpowers/notes/2026-06-14-erabsum-construction-decision.md`.
- Repository: `GebLean/Era.lean` (`ETm`, `Tm.eval`, `eraInterp`, term
  formers, `esq`); `GebLean/LawvereER.lean` (`ERMor1`, `natBSum`,
  `natBProd`, `interp_bsum`, `interp_bprod`);
  `GebLean/Utilities/EraBoundedSum.lean` (`natGeomSum_eq`, `natBSum_geom`
  — `G₀`); `GebLean/EraCompleteness.lean` (`era_sound_er`, `eraGeomSum`).
