# Era `packM`-as-term: faithful Corollary 3.6 design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Provenance: a design spike superseding the 6.4c-1..5 model](#provenance-a-design-spike-superseding-the-64c-15-model)
- [Background facts the spike confirmed](#background-facts-the-spike-confirmed)
- [Design decision: follow Corollary 3.6 exactly](#design-decision-follow-corollary-36-exactly)
- [The faithful pipeline (Corollary 3.6 in repository terms)](#the-faithful-pipeline-corollary-36-in-repository-terms)
  - [Step 1 — Signed monomial reflection](#step-1--signed-monomial-reflection)
  - [Step 2 — Lemma 3.5 (degree reduction)](#step-2--lemma-35-degree-reduction)
  - [Step 3 — Separable normal form and `cubeSum_factor`](#step-3--separable-normal-form-and-cubesum_factor)
  - [Step 4 — δ-affine assembly and read-off](#step-4--%CE%B4-affine-assembly-and-read-off)
  - [Step 5 — Witness-count preservation across Lemma 3.5](#step-5--witness-count-preservation-across-lemma-35)
- [Module layout](#module-layout)
- [Risks and hardest pieces](#risks-and-hardest-pieces)
- [References](#references)
- [Tags](#tags)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Realise the packed witness `packM k w t P` of arXiv:2407.12928,
Lemma 3.3, as an `Era` arithmetic term, for the predicate
`P = SosSystem.eval E` produced by `diophOf`. This is the one
obligation blocking `eraCount`/`eraCount_eval`
(`GebLean/EraHistCodeTerm.lean`), and through it Tasks 6.4d, 6.4e,
6.5, 6.6, and Phase 7 of the Era completeness work.

The read-off half (`eraCountOfPack`/`eraCountOfPack_eval`, the
`HW(packM)/w − tᵏ` count) is already built and committed. This
sub-project builds the term whose value is `packM` itself.

## Provenance: a design spike superseding the 6.4c-1..5 model

The parent sub-plan
(`docs/superpowers/plans/2026-06-16-era-task6.4-histcode-term-subplan.md`,
Task 6.4c) decomposed `packM`-as-term into five lemmas: 6.4c-1
`SimpleMonomial.mul`, 6.4c-2 `SosSystem.toSimpleSum` (flatten to a
single `SimpleSum`), 6.4c-3 a separable certificate, 6.4c-4
`packM_term`, 6.4c-5 wiring. A design spike — re-reading
arXiv:2407.12928 § 4 (Lemma 3.1 through Corollary 3.6, Eqs (7),(8))
against the actual `SimpleMonomial`/`SosTerm`/`SosSystem` definitions
and the `diophOf` combinators — found that decomposition rests on a
model that does not match either the paper's construction or the
repository's predicate representation. The corrected design is a
faithful transcription of Corollary 3.6, which the decomposition
above had partially elided.

## Background facts the spike confirmed

The `SimpleMonomial m` normal form (arXiv:2407.12928, Expression
(6)):

```text
coeff · ∏ᵢ (expBase i) ^ ((expCoeff i) · ρ i) · ∏ᵢ (ρ i) ^ (polyExp i)
```

with `coeff, expBase i, expCoeff i : ETm m` and `polyExp i : ℕ`
(`GebLean/Utilities/EraDiophantine.lean:318`).

Facts established by inspecting the `diophOf` atoms:

- Every `diophOf`-reachable monomial has `polyExp ≡ 0`
  (`EraSepReduce.lean`, `diophOf_polyExpZero`). The cube-coordinate
  dependence is carried in `coeff`: `SimpleMonomial.var j` sets
  `coeff = .var j`; `SimpleMonomial.mulVars j k` sets
  `coeff = .var j *ᵉ .var k`. The degree therefore lives in an
  opaque `ETm` `coeff`, not in the `polyExp` position that
  `cubeSum_factor` reads.
- The only populated exponential base is `2` (`pow2Var`); all other
  atoms set `expBase ≡ 0`.
- `SosTerm.eval (.sqDist P Q) ρ = (P.eval ρ − Q.eval ρ)² +
  (Q.eval ρ − P.eval ρ)²` (truncated subtraction). Because
  `x² + y² ≥ 2xy`, this equals `P.eval² + Q.eval² − 2·P.eval·Q.eval`
  with no underflow.
- `SosTerm.eval (.prod s t) ρ = SosSystem.eval s ρ ·
  SosSystem.eval t ρ`. `diophMod`/`diophDiv` emit `prod` atoms
  (`EraDiophantine.lean:1799,2029`) to encode their branch
  disjunctions, so the counted predicate contains products of
  sub-systems.
- `deltaBlock_affine` (already proven): for `a < 2 ^ w`,
  `δ(a, w) = (2^w − 1)(2^w + 1) − (2^w − 1)·a`.
- `cubeSum_factor` (already proven): `∑_{a ∈ cube} ∏ᵢ (a i)^(u i)·
  (vbase i)^(a i) = ∏ᵢ (∑_{j<t} j^(u i)·(vbase i)^j)`, consuming the
  cube-coordinate degrees `u i` from `polyExp`-position with
  coordinate-independent bases.

Three consequences contradict the 6.4c-1..5 model:

1. The cube-coordinate degree is in `coeff` (as `ETm` `var`
   products), not in `polyExp`. A normalisation moving each
   cube-coordinate variable power out of `coeff` into `polyExp` is
   mandatory before `cubeSum_factor` applies (6.4c-1's "merge
   `polyExp`" assumed the degree was already there).
2. The expansion is signed. `sqDist` contributes `−2PQ`; the
   δ-affine form contributes `−(2^w − 1)·P`. The repository's
   `SimpleSum = List SimpleMonomial` is non-negative, so flattening
   to a single `SimpleSum` (6.4c-2) cannot represent the
   construction. The paper works over ℤ.
3. `prod` atoms make the predicate value a product of sums, raising
   per-coordinate degree above 2. This is not a defect to work
   around: at the polynomial level a product of polynomials is
   simply more (higher-degree) monomials, and Corollary 3.6's
   Lemma 3.5 is the paper's instrument for reducing exactly this
   degree back to ≤ 2. `count_zeros_eq` already holds for an
   arbitrary `P`, so the prod-bearing predicate counts the correct
   set; only the term realisation needs the degree reduction.

## Design decision: follow Corollary 3.6 exactly

The governing constraint (user directive, 2026-06-16): transcribe
what the papers do, inventing no parallel machinery. The papers are
the authority; a home-grown shortcut (higher-kind geometric
progressions, a bespoke disjunction encoding) is more likely wrong
than the decades-studied construction. Concretely:

- Lemma 3.5 (the degree reduction) is written, not certified away.
  The route-(ii) "the `diophOf` predicate is already degree ≤ 2"
  position (recorded in the parent plan's Task 6.4b) is refuted by
  the spike: degree-≤2 holds for the raw atoms, but the relevant
  degree is that of the expanded predicate (after squaring `sqDist`
  and multiplying `prod`), which exceeds 2.
- The signed expansion uses a new ℤ-coefficient monomial type
  (user decision, 2026-06-16). ℤ is computable in Lean, and the type
  lives entirely on the proof side; the `Era` terms remain ℕ-valued
  and the final `packM` term is built from `etsub`, proven equal to
  the (non-negative) ℤ-valued polynomial on the cube.

## The faithful pipeline (Corollary 3.6 in repository terms)

The paper's Corollary 3.6 takes a predicate `P(n̄, x̄)` that is an
algebraic sum of arithmetic terms and produces a term counting
`#{ā ∈ cube : P(n̄, ā) = 0}`. The repository's
`P := fun a => SosSystem.eval E (Fin.append ctx a)` is such a
predicate. The pipeline:

### Step 1 — Signed monomial reflection

Define a ℤ-coefficient simple-exponential-monomial type
(`ZMonomial`). This type is **novel** (a project-side reflection
device, not a paper construct): the paper works over ℤ implicitly but
defines only the ℕ-valued Expression (6) monomial. The remainder of
the construction is **transcription**. `ZMonomial` is in
Expression-(6) form: an `ℤ` leading sign carrying
the signed expansion, a parameter-only coefficient term, per-cube-
coordinate exponential base/coefficient terms, and per-cube-
coordinate `polyExp : ℕ` (holding the cube degree, of any size before
Step 2). Provide `ZMonomial.eval : … → ℤ` and a
binary product `ZMonomial.mul` with `eval`-agreement (multiply
coefficients, merge `expBase` powers at the single populated base
`2`, add `expCoeff` and `polyExp`). Reflect the predicate value
`SosSystem.eval E` into a `List ZMonomial` (signed sum) with a
pointwise `eval`-agreement lemma on the cube: each `sqDist` expands
to `P² + Q² − 2PQ`, each `prod` to the distributed product, each via
`ZMonomial.mul`. This corrects 6.4c-1 (now ℤ-valued, with the
`coeff`→`polyExp` normalisation) and replaces 6.4c-2 (signed list,
not a single non-negative `SimpleSum`).

### Step 2 — Lemma 3.5 (degree reduction)

Transcribe arXiv:2407.12928, Lemma 3.5. For the reflected predicate,
introduce chain variables `y₁ = x, y₂ = y₁x, …, y_{h} = y_{h-1}x` for
each cube variable `x` with non-exponential exponent `h`, replace the
non-exponential occurrences, and form the sum of squares of the
introduced equations plus the replaced predicate squared. The output
`R ≥ 0` is a simple-in-(x̄, ȳ) exponential polynomial in which no
non-exponential occurrence of any variable has exponent > 2, with

- `R(r̄, ā, b̄) = 0 ⟹ P(r̄, ā) = 0`, and
- `P(r̄, ā) = 0 ⟹ ∃! b̄, R(r̄, ā, b̄) = 0`.

This is the centerpiece. The existing `EraSepReduce.lean`
`PolyExpZero` development characterises the raw-atom input
(multilinear, `expBase ∈ {0, 2}`) and is the starting point, not
discarded.

### Step 3 — Separable normal form and `cubeSum_factor`

Normalise each degree-≤2 monomial of `R` into Expression-(6)
separable form `α(n̄)·∏_c (a_c)^{u_c}·(vbase_c)^{a_c}` with
`u_c ∈ {0, 1, 2}` and `α`, `vbase_c` cube-coordinate-independent (the
`coeff`→`polyExp` move), then apply `cubeSum_factor` to obtain
`∏_c G_{u_c}(vbase_c, t)` realised by the already-built
`eraGeomSum` (`G₀`), `eraLinGeomSum` (`G₁`), `eraSqGeomSum` (`G₂`).
This is the work the parent plan called 6.4c-3 and 6.4c-4.

Side obligation: `eraLinGeomSum_eval`/`eraSqGeomSum_eval` require base
`≥ 2` (`EraCompleteness.lean`, `hq : 2 ≤ q`). The cube-sum bases are
`vbase_c = 2^(2w)·b_c^{β_c} ≥ 2` (arXiv:2407.12928, Eq (8)), so the
condition holds, but each Step-3 lemma must carry the `2 ≤ vbase_c`
hypothesis and discharge it from the `2^(2w)` factor.

### Step 4 — δ-affine assembly and read-off

Sign convention (pinned, since the paper's `A(m, k)` of Eq (8) is
already signed): write `Aᵤ(m, k)` for the **unsigned** per-monomial
cube-sum product `α·∏_c G_{u_c}(vbase_c, t)`, so the paper's signed
`A(m, k) = −(2^w − 1)·Aᵤ(m, k)`. Then the paper's
`M = C(ε, k) + ∑ⱼ A(mⱼ, k)` becomes

```text
packM = C(ε, k) − (2^w − 1)·∑ⱼ Aᵤ(mⱼ, k)
```

assembled with `etsub`, where `C(ε, k)` is the constant part (Eq (7)).
The single `−(2^w − 1)` factor is applied once, to the summed unsigned
products. Prove the non-underflow side condition (the value is `≥ 0`
because the underlying ℤ-polynomial is `δ ≥ 0`). Feed the resulting
`packMTerm` into the built `eraCountOfPack`/`eraCountOfPack_eval`.
This is 6.4c-4 and 6.4c-5.

### Step 5 — Witness-count preservation across Lemma 3.5

Lemma 3.5 enlarges the cube with the chain variables. Establishing
that the enlarged cube's zero-count equals the original
`#{ā : P(n̄, ā) = 0}` requires composing **three** distinct
`∃!`-witness layers, which the implementation plan must decompose
separately (this step is as load-bearing as Step 2):

1. The `diophOf` witnesses are themselves part of the original cube and
   already carry a `∃!` (`diophOf_unique`, `EraDiophantine.lean:2339`):
   `SosSystem.eval E (append ctx a) = 0` has, per parameter point,
   the unique-witness structure `diophOf` guarantees.
2. Lemma 3.5's Condition 3 (paper lines 743–744) gives a `∃!` for the
   chain variables `ȳ`, functionally determined by the cube point.
3. The count over the enlarged cube `(ā, ȳ)` collapses, via layers 1–2,
   to the count over `ā`, matching the paper's Corollary 3.6
   composition (lines 796–819), which itself threads Theorem-3.4's `y`
   then Lemma-3.5's `z`.

Constructive bounds (no `noncomputable`): the paper leaves `θ(n̄)` and
the enlarged `w(n̄)` existential ("there is some arithmetic term θ",
line 703; "find an arithmetic term w", line 707). They must be
**exhibited** as `Era` terms. The chain variables satisfy
`y_i ≤ x^i ≤ θ`, so `θ` is built from the cube side `t` via the
existing `eraMajorant` machinery (parent subplan:317–318); `w` is the
enlarged majorant bounding `R` on the product cube. Each must be a
concrete `ETm`, with its bound proven, before the `eraCount` of `R`
connects back to the count the downstream tasks (6.4d, 6.4e) require.

## Module layout

- `GebLean/Utilities/EraDiophantine.lean` (read-only here): the
  `SimpleMonomial`/`SosSystem` source of the predicate.
- `GebLean/Utilities/EraSepReduce.lean` (extend): the ℤ-monomial
  type, `ZMonomial.mul`, the reflection of `SosSystem.eval`, and
  Lemma 3.5 (Steps 1–2). Already imports `EraDiophantine`.
- `GebLean/EraHistCodeTerm.lean` (extend): the separable
  normalisation, `cubeSum_factor` application, δ-affine assembly,
  and `eraCount`/`eraCount_eval` wiring (Steps 3–5), built on the
  existing `eraCountOfPack` and the `eraGeomSum` family.

The layering `EraSepReduce → EraHistCodeTerm` is unchanged; no new
module is required, and `EraCompleteness` is not made to import
`EraRecurrence`.

## Risks and hardest pieces

- Lemma 3.5 (Step 2) is one of two dominant new constructions: the
  chain-variable bookkeeping, the squared-equation expansion's
  exponent bound, and the `∃!`-witness condition. It warrants its
  own task-level decomposition in the implementation plan.
- The count-preservation composition (Step 5) is the other dominant
  piece: it threads three `∃!` layers (`diophOf` witnesses, Lemma 3.5
  chain variables, the enlarged-cube collapse) and must exhibit the
  `θ`/`w` bounds as concrete `Era` terms (no `noncomputable`). It is as
  load-bearing as Step 2 and likewise warrants its own task-level
  decomposition.
- The signed reflection (Step 1) must prove `eval`-agreement through
  truncated subtraction (`sqDist`) and products (`prod`); the
  non-underflow argument (`x² + y² ≥ 2xy`, and `δ ≥ 0`) is the
  delicate part.
- The `coeff`→`polyExp` normalisation (Step 3) depends on the
  structured form of `coeff` (`var`/`mulVars` products); a general
  `ETm` `coeff` is not analysable, so the reflection in Step 1 must
  produce monomials whose cube-coordinate degree is already in
  `polyExp`.

## References

- M. Prunescu and L. Sauras-Altuzarra, *On the representation of
  number-theoretic functions by arithmetic terms*, arXiv:2407.12928.
  § 4: Lemma 3.1 (`δ` Hamming weight), Lemma 3.2 (`cubeSum_factor`),
  Lemma 3.3 (the `HW(packM)/w − tᵏ` read-off), Eqs (7),(8) (the
  δ-affine monomial expansion), Lemma 3.5 (degree reduction),
  Corollary 3.6 (`G₀`,`G₁`,`G₂` suffice). Local copy:
  `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`.
- V. Istrate, M. Prunescu, and L. Shunia,
  arXiv:2606.09336. Claims 1–5 (the recurrence count), Section-4
  read-off. Local copy:
  `/home/terence/wingeb/undecidability-chaos-universality-arithmetic-terms.pdf`.
- Parent sub-plan:
  `docs/superpowers/plans/2026-06-16-era-task6.4-histcode-term-subplan.md`
  (Task 6.4c, the superseded 6.4c-1..5 decomposition).

## Tags

elementary recursive, Diophantine, count, hypercube, arithmetic
term, simple exponential polynomial, degree reduction
