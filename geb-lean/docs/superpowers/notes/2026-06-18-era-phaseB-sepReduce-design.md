# Phase B design note: `sepReduce` (Lemma 3.5 chain reduction)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Chain scheme: uniform global degree (the paper's construction)](#chain-scheme-uniform-global-degree-the-papers-construction)
- [Reflect-then-reduce pipeline](#reflect-then-reduce-pipeline)
- [Index layout of `Fin (p + k + f)` = `Fin (p + k + k*d)`](#index-layout-of-fin-p--k--f--fin-p--k--kd)
- [Chain equations and substitution](#chain-equations-and-substitution)
- [B0–B4 task decomposition](#b0b4-task-decomposition)
- [Corrected signatures](#corrected-signatures)
- [Hardest steps (named for B4)](#hardest-steps-named-for-b4)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Pinned construction for Phase B of the `packM`-as-term plan
(`docs/superpowers/plans/2026-06-18-era-packm-term-plan.md`), produced by
a design spike and reviewed before implementation. Phase B transcribes
arXiv:2407.12928, Lemma 3.5 (chain-variable degree reduction) over the
Phase-A `ZMonomial` reflection. This note supersedes the plan's
sketch-level B1–B4 with a concrete, composable B0–B4 decomposition.

## Chain scheme: uniform global degree (the paper's construction)

Lemma 3.5 (paper lines 745–770) fixes `h` as the single global largest
non-exponential exponent over all cube variables, introduces `y₁,…,y_h`
for one variable, and runs "the same procedure for all variables
`x₁,…,x_k`, adding new variables each time" — i.e. every cube variable
receives its own length-`h` chain, for `k·h` new variables total. The
uniform global degree is therefore the paper's literal construction, not
an over-approximation; per-variable minimal chain lengths would reach the
same conclusion with fewer variables but are an optimisation the paper
does not perform, and they force ragged dependent `Fin`-sum indexing that
is far harder to verify.

Set `d := max 1 (ZMonomial.maxCubeDegree L₀)`, where `L₀ = SosSystem.toZ
s` is the reflected predicate; `maxCubeDegree` is the paper's `h`, and the
`max 1` guards the degenerate all-linear case `h = 0` (no reduction
needed) so chains are well-formed. The number of new variables is
`f = k * d`.

## Reflect-then-reduce pipeline

`sepReduce` reflects `s` to a `ZMonomial` list (calling Phase-A's
`SosSystem.toZ`), then chain-reduces. The `CoeffVarProduct`/`BasePaired`
hypotheses are consumed only at the reflection boundary (they gate
`SosSystem.toZ_eval`); the chain machinery is hypothesis-free.

```text
s : SosSystem (p+k)
  │  (requires s.CoeffVarProduct, s.BasePaired for SosSystem.toZ_eval)
  ▼  L₀ := SosSystem.toZ s : List (ZMonomial (p+k))
  ▼  d  := max 1 (maxCubeDegree L₀);  f := k * d
  ▼  L₁ := L₀.map (ZMonomial.weaken (Fin.castAdd f)) : List (ZMonomial (p+k+f))
  ▼  Psub := L₁.map chainSub                          -- cube degrees → chain slots
  ▼  (sepReduce s).2 := chainEqs ++ ZMonomial.listMul Psub Psub
     (sepReduce s).1 := f
```

`P_sub²` is the literal square `listMul Psub Psub` (a single polynomial
squared — no `negDouble` cross-terms; those exist only for `sqDist`'s
`(P−Q)²`). Each chain equation is squared by the same `sqDist`-square
recipe used in `SosTerm.toZ`.

## Index layout of `Fin (p + k + f)` = `Fin (p + k + k*d)`

Lean parses `p + k + f` as `(p + k) + f`, so `Fin.append (ρ : Fin (p+k) →
ℕ) (b : Fin f → ℕ)` typechecks with no re-association — matching the
`Fin.append ctx a` pattern already used in `SosSystem.toZ_eval`.

| region | index | meaning |
| --- | --- | --- |
| `i : Fin p` | first block | parameter `nᵢ` |
| `c : Fin k` | `cubeSlot c` (old `Fin.natAdd p c`) | cube coord `x_c` |
| `(c,i) : Fin k × Fin d` | `chainSlot c i := Fin.natAdd (p+k) (chainIdx c i)` | chain var `y_{c,i+1}` |

`chainIdx c i := ⟨c.val * d + i.val, _⟩ : Fin (k*d)`; `castAddEmb :=
Fin.castAdd f` (injective by `Fin.castAdd_injective`) embeds the old
scope. The chain slot holding `x_c^i` (for `i ≥ 1`) is
`chainSlot c ⟨i-1, _⟩`.

## Chain equations and substitution

For each `c : Fin k`, `i : Fin d`, the chain-equation left side `S_{c,i}`
is a two-monomial signed difference:

- `i = 0`: `x_c − y_{c,1}` = `[varMon (cubeSlot c), negVarMon (chainSlot c 0)]`
- `i ≥ 1`: `y_{c,i}·x_c − y_{c,i+1}` =
  `[mulVarMon (chainSlot c (i-1)) (cubeSlot c), negVarMon (chainSlot c i)]`

Every `S_{c,i}` monomial has per-slot `polyExp ≤ 1` (the `mulVarMon` case
sets two *distinct* slots to 1, never one slot to 2), so each squared
chain monomial has `polyExp ≤ 2`.

`chainSub` lowers each cube slot's `polyExp` to 0 and deposits the removed
degree as `polyExp = 1` at the matching chain slot; degree-0 cube slots
are untouched (no `y_{c,0}`). Its correctness lemma `chainSub_eval` holds
on the sub-domain `ChainHolds ρ : ∀ c i, ρ (chainSlot c i) = ρ (cubeSlot
c) ^ (i+1)`, with the side fact that weakened monomials carry `polyExp =
0` on all chain slots (a `preimage (Fin.castAdd f) = none` computation,
mirroring `SimpleMonomial.weaken_polyExpZero`).

## B0–B4 task decomposition

The plan's sketch is under-split; hoist the index infrastructure into its
own task (B0) and name the two shared proof helpers.

- **B0 — index infrastructure.** `chainIdx`, `chainSlot`, `cubeSlot`,
  `castAddEmb`; their injectivity; `preimage (Fin.castAdd f)` computes
  `none` on cube and chain slots; the `Fin k × Fin d ≅ Fin (k*d)`
  bijection lemmas. No semantics.
- **B1 — `ZMonomial.weaken` + `weaken_eval`** (with the
  `Function.Injective` hypothesis) and the list corollary. Mirrors
  `SimpleMonomial.eval_weaken` (strictly easier: no `expBase` factor).
- **B2 — chain equations + `chainSub` + `chainSub_eval`.**
  `maxCubeDegree`, `chainEqList`, `chainEqs`, `chainSub`, `ChainHolds`,
  the per-monomial `polyExp ≤ 1` facts for `Psub`.
- **B3 — `sepReduce` + `sepReduce_degree`.** Assembles the pipeline;
  proves the unconditional degree-≤2 bound (`Psub` monomials are degree
  ≤1, `ZMonomial.mul` adds, so the square is ≤2; chain block from B2).
- **B4 — `sepReduce_eval_split`, `sepReduce_sound`, `sepReduce_unique`.**
  The shared regrouping lemma `sepReduce_eval_split` (the flat reduced
  list's eval-sum equals `∑ S_{c,i}-eval² + (∑Psub-eval)²`) and
  `chainHolds_unique` (the chain induction pinning `b`), then the two
  correctness theorems.

## Corrected signatures

```lean
def sepReduce {p k : ℕ} (s : SosSystem (p+k)) : Σ f : ℕ, List (ZMonomial (p + k + f))

theorem sepReduce_degree {p k : ℕ} (s : SosSystem (p+k)) (hzero : s.PolyExpZero) :
    ∀ mon ∈ (sepReduce s).2, ∀ i, mon.polyExp i ≤ 2

theorem sepReduce_sound {p k : ℕ} (s : SosSystem (p+k))
    (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired)
    (ρ : Fin (p+k) → ℕ) (b : Fin (sepReduce s).1 → ℕ)
    (hR : (((sepReduce s).2).map (fun mon => mon.eval (Fin.append ρ b))).sum = 0) :
    SosSystem.eval s ρ = 0

theorem sepReduce_unique {p k : ℕ} (s : SosSystem (p+k))
    (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired)
    (ρ : Fin (p+k) → ℕ) (hP : SosSystem.eval s ρ = 0) :
    ∃! b : Fin (sepReduce s).1 → ℕ,
      (((sepReduce s).2).map (fun mon => mon.eval (Fin.append ρ b))).sum = 0
```

The `hcoeff`/`hbase` hypotheses on `sound`/`unique` are the correction
from the plan's sketch (needed to invoke `SosSystem.toZ_eval`); the
`hzero : s.PolyExpZero` hypothesis on `sepReduce_degree` (and, as needed,
on `sound`/`unique`) is a third such invariant — `SimpleMonomial.toZ`
retains the source monomial's parameter-slot `polyExp`, so the degree
bound is false without it. All three are `diophOf` invariants
(`diophOf_polyExpZero`/`diophOf_coeffVarProduct`/`diophOf_basePaired`)
discharged downstream, so they cost nothing. Together `sound` (each
`R`-zero `(ρ,b)` projects to an `s`-zero `ρ`) and `unique` (each `s`-zero
`ρ` has exactly one `b`) give
the fibrewise bijection Phase E's count collapse consumes.

## Hardest steps (named for B4)

- `sepReduce_eval_split`: recovering "this is `∑S² + P²`" from the flat
  `List (ZMonomial (p+k+f))` and applying non-negative-sum-zero. Prove it
  before either correctness theorem.
- `chainHolds_unique`: the chain induction on `i : Fin d` pinning
  `b (chainIdx c i) = (ρ (cubeSlot c))^(i+1)`; state it standalone,
  independent of the SEP machinery.

## References

- arXiv:2407.12928, Lemma 3.5 (lines 739–787) and Corollary 3.6
  (792–819). Local copy:
  `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`.
- Phase-A reflection API: `GebLean/Utilities/EraSepReduce.lean`
  (`ZMonomial`, `mul`/`listMul`/`negDouble`, `SosSystem.toZ`/`_eval`,
  `CoeffVarProduct`/`BasePaired`).
