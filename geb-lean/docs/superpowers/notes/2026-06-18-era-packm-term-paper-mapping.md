# Era `packM`-as-term: Lean ↔ paper sentence mapping

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Sources](#sources)
- [P1 objects to Lean (the construction proper)](#p1-objects-to-lean-the-construction-proper)
- [P1 Lemma 3.5 to Phase B (the chain-variable degree reduction)](#p1-lemma-35-to-phase-b-the-chain-variable-degree-reduction)
- [P1 Corollary 3.6 to the overall `eraCount` and the count cube](#p1-corollary-36-to-the-overall-eracount-and-the-count-cube)
- [Representation-device justification (the non-paper Lean machinery)](#representation-device-justification-the-non-paper-lean-machinery)
- [Faithfulness obligations we discharge (P1 assumes; we prove)](#faithfulness-obligations-we-discharge-p1-assumes-we-prove)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Point-by-point correspondence between the Lean declarations of the
`packM`-as-term construction (branch `feat/era-packm-term`) and the exact
sentences/lemmas/equations of the source papers. Maintained so the
transcription can be audited for faithfulness and resumed across
sessions. Each row marks whether the Lean object is a **transcription**
of a paper object or a **representation device** (Lean machinery that
makes the paper's informal terms type-check; not new mathematics).

Methodological rule (governs this whole sub-project): when transcribing
known mathematics, the architecture is the paper's. Where a "design
question" appears to arise, the first move is to read what the paper
does; the paper supplies the construction, and our job is faithful
representation plus discharging the hypotheses the paper assumes.

## Sources

- **P1** = arXiv:2407.12928, Prunescu & Sauras-Altuzarra, *On the
  representation of number-theoretic functions by arithmetic terms*.
  Local: `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`.
  Extract for line refs: `pdftotext <pdf> /tmp/era2407.txt`. § 4 is
  lines ~360–820 of that extract.
- **P2** = arXiv:2606.09336, Istrate, Prunescu & Shunia. The outer
  recurrence pipeline (Claims 1–5); relevant to the downstream Tasks
  6.4d–6.6, not to this sub-project's internals.

## P1 objects to Lean (the construction proper)

| P1 object (sentence/eq) | Lean declaration | file | kind |
| --- | --- | --- | --- |
| Expression (6): simple-in-x̄ exponential monomial `α·∏ bᵢ^(βᵢaᵢ)·∏ aᵢ^γᵢ` | `SimpleMonomial` (pre-existing) | EraDiophantine | transcription |
| Expression (6), ℤ-signed, base specialised to 2 | `ZMonomial` (sign, coeff, expCoeff, polyExp); `eval` (ℤ), `evalNat` (ℕ), `eval_eq`, `evalNat_cast` | EraSepReduce | representation device |
| product of monomials (used forming squares/products) | `ZMonomial.mul`, `mul_eval`; `ZMonomial.listMul`, `listMul_eval` | EraSepReduce | representation device |
| "P a sum of monomials" — the predicate value as a signed simple exp polynomial | `SimpleMonomial.toZ`, `SimpleSum.toZ`, `SosTerm.toZ`, `SosSystem.toZ` (+ `_eval`); `negDouble`; `SosTerm.cast_sqDist` (`(A−B)²+(B−A)²=A²+B²−2AB`) | EraSepReduce | transcription (of the δ-expansion's `ε+Σmⱼ` form) |
| "non-exponential occurrences of xᵢ" carry the cube-coordinate degree | `ETm.extractCubeDegree` (+`_eval`); `ETm.IsVarProduct` (+`.weaken`); `CoeffVarProduct`/`BasePaired` (+`diophOf_*` capstones) | EraSepReduce | representation device (extracts the γᵢ the paper writes inline) |
| Lemma 3.1: `HW(δ(a,w)) = 2w` if `a=0`, else `w` | `count_zeros_eq`, `eraSigma`, `deltaBlock` (pre-existing, Phase 5) | EraHypercube / EraCompleteness | transcription |
| Lemma 3.2: `∑_{ā} ∏ aᵢ^{uᵢ}vᵢ^{aᵢ} = ∏ G_{uᵢ}(vᵢ,t−1)` | `cubeSum_factor` (pre-existing) | EraHypercube | transcription |
| Lemma 3.2 applied to one monomial (put `evalNat` in `∏_c aᶜ^{u}vᶜ^a` form, then factor) | `ZMonomial.cubeFactor` (C1), `ZMonomial.eraMonoCubeSum` (C2a), `weight_mixedRadix_factor` | EraHistCodeTerm | transcription |
| `G₀,G₁,G₂` generalized geometric progressions | `eraGeomSum`/`eraLinGeomSum`/`eraSqGeomSum` (pre-existing) | EraCompleteness | transcription |
| Lemma 3.3: `M(n̄)=∑_ā 2^{2w·v(ā)}δ(P(ā),w)`; `HW(M)/w−tᵏ = d` | `packM`, `count_zeros_eq` (pre-existing); `eraCountOfPack`/`_eval` (pre-existing read-off) | EraHypercube / EraHistCodeTerm | transcription |
| Eq (7): `C(ε,k)` constant part | `eraConstPart` (Phase D1, planned) | EraHistCodeTerm | transcription |
| Eq (8): `A(m,k) = −(2^w−1)·α·∏ G_{γᵢ}(…)` per monomial | `eraMonoTerm` (C2-term) + the signed assembly in `packM_term` (D2) | EraHistCodeTerm | transcription |
| Lemma 3.3 "express `M` as an arithmetic term" (full `δ`-affine assembly `M = C + Σⱼ A`) | `packM_term` (+`_eval`) (Phase D2, planned) | EraHistCodeTerm | transcription |
| `α(n̄)` is a term in `n̄` only (so realisable over the parameter scope) | `ETm.paramProject` (+`_eval`); `cubeConstTerm`/`cubeBaseTerm` (Phase C2-term, planned) | EraHistCodeTerm | representation device |

## P1 Lemma 3.5 to Phase B (the chain-variable degree reduction)

The paper's Lemma 3.5 (P1 lines ~739–787): for `P` a simple-in-x̄ exp
polynomial, introduce, for each variable and the global largest
non-exponential exponent `h`, the `h` chain equations `x−y₁=0`,
`y₁x−y₂=0`, …, `y_{h−1}x−y_h=0`; replace each non-exponential `xⁱ` by
`yᵢ`; set `Q = S₁²+…+S_f²+P_sub²`. Then (1) no non-exponential occurrence
in `Q` exceeds exponent 2; (2) `Q=0 ⟹ P=0`; (3) `P=0 ⟹ ∃! ȳ, Q=0`.

| P1 Lemma 3.5 piece | Lean declaration | kind |
| --- | --- | --- |
| the `h` chain equations `S_{c,i}` (uniform global `h`, every variable — P1 "the same procedure for all variables") | `chainEqList`, `chainEqs` (squared); `cubeSlot`/`chainSlot`/`chainIdx`/`castAddEmb` index layout | transcription (chains) + representation (indexing) |
| "replace non-exponential occurrences `xⁱ` by `yᵢ`" | `chainSub` (+ `chainSub_eval` on the `ChainHolds` sub-domain `yᵢ=xⁱ`) | transcription |
| `d := max 1 (maxCubeDegree …)` is the paper's global `h` (the `max 1` guards the all-linear `h=0` case) | `ZMonomial.maxCubeDegree`, `le_maxCubeDegree` | transcription |
| `Q = ΣSᵢ² + P_sub²` (the reduced system) | `sepReduce` | transcription |
| condition 1: no non-exp occurrence exceeds 2 | `sepReduce_degree` (needs `PolyExpZero`, the param-degree-0 invariant `toZ_polyExp_param_zero`) | transcription |
| condition 2: `Q=0 ⟹ P=0` | `sepReduce_sound` (via `sepReduce_eval_split`, `chainEqs_zero_imp_chainHolds`, `sepReduce_psub_eval`) | transcription |
| condition 3: `P=0 ⟹ ∃! ȳ, Q=0` | `sepReduce_unique` (explicit cube-power witness `b₀`) | transcription |
| `ZMonomial.weaken` (re-index monomials into the enlarged scope) | `ZMonomial.weaken`, `weaken_eval` | representation device |

## P1 Corollary 3.6 to the overall `eraCount` and the count cube

P1 Cor 3.6 (lines ~792–819): add `ȳ` (Theorem 3.4) and `z̄` (Lemma 3.5)
to get `R(n̄,x̄,ȳ,z̄)≥0` of non-exponential degree ≤ 2; **apply Lemma 3.3
to `R` with the full variable tuple `(x̄,ȳ,z̄)` and the terms
`max(t,θ)` and `w`**, counting `{(x̄,ȳ,z̄) ∈ {0..max(t,θ)−1}^{k+f} :
R=0}`; Condition 9 collapses this to `{x̄ ∈ {0..t−1}^k : P=0}`. Only
`G₀,G₁,G₂` are needed because every non-exponential degree is ≤ 2.

Consequences (paper-dictated, not design choices):

- The `packM` count for `R` is over the **full `k+f` tuple** (cube vars
  `x̄` and chain vars `z̄`/`ȳ` together), side `max(t,θ)`. So
  `eraMonoCubeSum`/`cubeFactor` are instantiated with the cube being all
  `k+f` non-parameter coordinates; the per-monomial `coeff` is
  parameter-only (first `p` slots) and so independent of all `k+f`
  coordinates — the chain witness `b₀` never enters `packM`.
- The collapse `#{(x̄,z̄):R=0} = #{x̄:P=0}` is Condition 9, realised by
  `sepReduce_sound`+`sepReduce_unique`, applied in **Phase E**
  (count preservation), not in `packM_term`.
- `max(t,θ)` is Phase E's enlarged cube side (the `θ` bounds the chain
  witnesses); the shell `[t, max(t,θ))` contributes no zeros (Phase E's
  shell-empty bridge, discharged by `eraMajorant`/`diophOf_bound`).

| P1 Cor 3.6 piece | Lean declaration | kind |
| --- | --- | --- |
| apply Lemma 3.3 to `R` over `(x̄,ȳ,z̄)`, side `max(t,θ)` | `eraCount`, `eraCount_eval` (Phase D3, planned) | transcription |
| Condition 9 collapse to the `x̄`-count | `reducedCount_eq` + the shell-empty bridge (Phase E, planned) | transcription |
| `θ`, `w` exhibited as arithmetic terms | `eraTheta`, `eraW` from `eraMajorant` (Phase E, planned) | transcription |

## Representation-device justification (the non-paper Lean machinery)

These exist only to represent P1's informal arithmetic terms in Lean's
typed `ETm`/`ZMonomial`; each is justified as faithful, not novel
mathematics:

- `ZMonomial` (ℤ, base-2): P1 works over ℤ implicitly (signed monomials,
  the `δ`-affine `−(2^w−1)P`); the base-2 specialisation is sound because
  every `diophOf` exponential is base 2 (carried safeguard in the
  `EraSepReduce` module docstring).
- `extractCubeDegree`/`IsVarProduct`/`paramProject`: P1 writes the
  cube-coordinate degree `γᵢ` and the coefficient `α(n̄)` inline; in Lean
  the degree must be moved into the `polyExp` field (for `cubeSum_factor`)
  and `α` projected to the parameter scope. These are scope/representation
  operations, proven value-faithful.
- the index layer (`chainIdx`/`chainSlot`/`cubeSlot`/`castAddEmb`): P1's
  `y_{c,i}` variables, given a concrete `Fin (p+k+k·d)` layout.
- ℕ-vs-ℤ non-underflow (`SosTerm.cast_sqDist`; planned `packM_term`
  `etsub` non-underflow): P1's quantities are manifestly `≥ 0`; we work
  over ℕ truncated subtraction and descend the equality from `M ≥ 0`.

## Faithfulness obligations we discharge (P1 assumes; we prove)

- Lemma 3.3 assumes `P` is a simple-in-x̄ exponential polynomial. We must
  prove our reduced `R` is in that form: the `IsVarProduct`/
  `CoeffVarProduct`/`BasePaired`/`polyExp ≤ 2` predicates and their
  `sepReduce`/`diophOf` propagation lemmas.
- Lemma 3.2 (`cubeSum_factor`) requires the bases `≥ 2`; discharged from
  the `2^{2w·tᶜ}` weight factor (`w,t ≥ 1`).

## References

- P1 § 4 anchors (in `/tmp/era2407.txt` after `pdftotext`): Expression
  (6) ~line 311; Lemma 3.1 ~362; Lemma 3.2 ~369; Lemma 3.3 ~401 with
  Eqs (7),(8) at ~607/678; Theorem 3.4 ~687; Lemma 3.5 ~739; Cor 3.6
  ~792.
- Design spec: `docs/superpowers/specs/2026-06-17-era-packm-term-design.md`.
- Implementation plan:
  `docs/superpowers/plans/2026-06-18-era-packm-term-plan.md`.
- Phase B construction note:
  `docs/superpowers/notes/2026-06-18-era-phaseB-sepReduce-design.md`.
