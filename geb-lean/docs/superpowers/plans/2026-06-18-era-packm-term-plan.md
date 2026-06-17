# Era `packM`-as-term implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [How to work this plan](#how-to-work-this-plan)
- [Background API (already built; do not redo)](#background-api-already-built-do-not-redo)
- [File structure](#file-structure)
- [Phase A — `ZMonomial` signed reflection (spec Step 1)](#phase-a--zmonomial-signed-reflection-spec-step-1)
  - [Task A1: `ZMonomial` type and ℤ denotation](#task-a1-zmonomial-type-and-%E2%84%A4-denotation)
  - [Task A2: `ZMonomial.mul` and `mul_eval`](#task-a2-zmonomialmul-and-mul_eval)
  - [Task A2b: coeff grammar and the cube-degree extraction](#task-a2b-coeff-grammar-and-the-cube-degree-extraction)
  - [Task A3: reflect `SimpleMonomial`/`SimpleSum` into `ZMonomial`](#task-a3-reflect-simplemonomialsimplesum-into-zmonomial)
  - [Task A4: reflect `SosSystem.eval` into a signed `ZMonomial` list](#task-a4-reflect-sossystemeval-into-a-signed-zmonomial-list)
- [Phase B — Lemma 3.5 degree reduction (spec Step 2; dominant)](#phase-b--lemma-35-degree-reduction-spec-step-2-dominant)
  - [Task B1: chain-variable equations and substitution](#task-b1-chain-variable-equations-and-substitution)
  - [Task B2: degree bound of the squared system](#task-b2-degree-bound-of-the-squared-system)
  - [Task B3: soundness of the reduced system](#task-b3-soundness-of-the-reduced-system)
  - [Task B4: unique-witness condition](#task-b4-unique-witness-condition)
- [Phase C — separable normal form and `cubeSum_factor` (spec Step 3)](#phase-c--separable-normal-form-and-cubesum_factor-spec-step-3)
  - [Task C1: separable normal form (coeff to polyExp)](#task-c1-separable-normal-form-coeff-to-polyexp)
  - [Task C2: per-monomial cube-sum via `cubeSum_factor`](#task-c2-per-monomial-cube-sum-via-cubesum_factor)
- [Phase D — δ-affine assembly and read-off (spec Step 4)](#phase-d--%CE%B4-affine-assembly-and-read-off-spec-step-4)
  - [Task D1: the constant part `C(ε, k)` (Eq (7))](#task-d1-the-constant-part-c%CE%B5-k-eq-7)
  - [Task D2: the packed-witness term and `eval = packM`](#task-d2-the-packed-witness-term-and-eval--packm)
  - [Task D3: `eraCount` over the reduced system](#task-d3-eracount-over-the-reduced-system)
- [Phase E — witness-count preservation (spec Step 5; dominant)](#phase-e--witness-count-preservation-spec-step-5-dominant)
  - [Task E1: the bound terms `θ` and `w` as `Era` terms](#task-e1-the-bound-terms-%CE%B8-and-w-as-era-terms)
  - [Task E2: count collapse across the enlarged cube](#task-e2-count-collapse-across-the-enlarged-cube)
  - [Task E3: `eraCount`/`eraCount_eval` final contract](#task-e3-eracounteracount_eval-final-contract)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Realise the packed witness `packM k w t P` of
arXiv:2407.12928, Lemma 3.3, as an `Era` arithmetic term for the
`diophOf`-produced predicate `P = SosSystem.eval E`, completing
`eraCount`/`eraCount_eval` and unblocking Tasks 6.4d–6.6 and Phase 7.

**Architecture:** Faithful transcription of arXiv:2407.12928,
Corollary 3.6. A new ℤ-coefficient monomial type (`ZMonomial`) reflects
the signed expansion of the predicate; Lemma 3.5 reduces non-exponential
degrees to ≤ 2 with a unique-witness condition; `cubeSum_factor` plus the
`G₀`/`G₁`/`G₂` geometric-sum terms factor each monomial; the δ-affine
identity (Eqs (7),(8)) assembles `packM`; a three-level witness count
threads the result back to the original count.

**Tech Stack:** Lean 4, Mathlib (pin `v4.29.0-rc6`), `lake build` /
`lake test` / `lake lint`, `scripts/check-axioms.sh`. Constructive-only
(no `noncomputable`); axiom-clean (`propext`, `Quot.sound`,
`Classical.choice`).

Design spec:
`docs/superpowers/specs/2026-06-17-era-packm-term-design.md`.

---

## How to work this plan

One declaration at a time. `sorry` is permitted between commits as a
stand-in (audited away before each commit); never commit `sorry`,
`admit`, or an underscore. Verify every task with
`lake build <module>` **and** `bash scripts/pre-commit.sh` (the latter
runs `lake lint`, whose `unusedArguments` linter catches unused
arguments `lake build` misses), then `bash scripts/check-axioms.sh`.
Numeric `#eval` probes are on plain ℕ only (never on symbolic
`Tm.eval`); delete them before committing. Search mathlib before each
from-scratch proof. Cite the exact paper claim/equation in each
transcribed declaration's docstring. The controller commits;
implementers edit and verify only.

Proof bodies for the degree-reduction and witness-count lemmas
(Phases B, E) are discovered at execution; each task gives the exact
statement, the strategy, and the verification, following the repository
convention for proof-heavy Era plans.

## Background API (already built; do not redo)

```lean
-- GebLean/Utilities/EraDiophantine.lean
structure SimpleMonomial (m : ℕ) where
  coeff : ETm m; expBase expCoeff : Fin m → ETm m; polyExp : Fin m → ℕ
def SimpleMonomial.eval (mon : SimpleMonomial m) (ρ : Fin m → ℕ) : ℕ
def SimpleMonomial.var / one / mulVars / pow2Var      -- generators
inductive SosTerm (m) | sqDist : SimpleSum m → SimpleSum m → SosTerm m
                      | prod : List (SosTerm m) → List (SosTerm m) → SosTerm m
def SosTerm.eval / SosSystem.eval                      -- ℕ denotations
def diophOf {n} : ETm n → DiophEnc n
theorem diophOf_encodes / diophOf_unique / diophOf_bound
def eraMajorant {n} : ETm n → ETm n  -- with _spec (strict), _mono, _pos

-- GebLean/Utilities/EraHypercube.lean
def cubePoints (k t : ℕ) : Finset (Fin k → ℕ)
def mixedRadix (k t : ℕ) (a : Fin k → ℕ) : ℕ
def packM (k w t : ℕ) (P : (Fin k → ℕ) → ℕ) : ℕ
theorem cubeSum_factor (k) (u vbase : Fin k → ℕ) (t) :
  (∑ a ∈ cubePoints k t, ∏ i, (a i)^(u i) * (vbase i)^(a i))
    = ∏ i, (∑ j ∈ Finset.range t, j^(u i) * (vbase i)^j)
theorem count_zeros_eq (k w t) (hw : 0 < w) (P) (hP) :
  (Nat.digits 2 (packM k w t P)).sum / w - t^k
    = ((cubePoints k t).filter (fun a => P a = 0)).card

-- GebLean/EraCompleteness.lean
def eraGeomSum eraLinGeomSum eraSqGeomSum : ETm 2   -- G₀, G₁, G₂
theorem eraGeomSum_natBSum (q bound) (hq : 2 ≤ q) :
  Tm.eval eraInterp eraGeomSum ![q, bound] = ∑ i ∈ Finset.range bound, q^i
theorem eraLinGeomSum_eval (q n) (hq : 2 ≤ q) :
  Tm.eval eraInterp eraLinGeomSum ![q, n] = ∑ i ∈ Finset.range n, i * q^i
theorem eraSqGeomSum_eval (q n) (hq : 2 ≤ q) :
  Tm.eval eraInterp eraSqGeomSum ![q, n] = ∑ i ∈ Finset.range n, i^2 * q^i
def eraSigma : ETm 1   -- Hamming weight HW

-- GebLean/EraHistCodeTerm.lean
theorem deltaBlock_affine (ha : a < 2^w) :
  GebLean.deltaBlock a w = (2^w - 1) * (2^w + 1) - (2^w - 1) * a
def eraNumeral {p} : ℕ → ETm p   -- with eraNumeral_eval
def eraCountOfPack {p} (k) (packMTerm tTerm wTerm : ETm p) : ETm p
-- bounds are evaluated THROUGH the terms; `P` is explicit; `hpack` is last
theorem eraCountOfPack_eval {p} (k) (packMTerm tTerm wTerm) (ctx)
  (P : (Fin k → ℕ) → ℕ)
  (ht : 0 < Tm.eval eraInterp tTerm ctx)
  (hw : 0 < Tm.eval eraInterp wTerm ctx)
  (hP : ∀ a ∈ cubePoints k (Tm.eval eraInterp tTerm ctx),
          P a < 2 ^ Tm.eval eraInterp wTerm ctx)
  (hpack : Tm.eval eraInterp packMTerm ctx
            = packM k (Tm.eval eraInterp wTerm ctx) (Tm.eval eraInterp tTerm ctx) P) :
  Tm.eval eraInterp (eraCountOfPack k packMTerm tTerm wTerm) ctx
    = ((cubePoints k (Tm.eval eraInterp tTerm ctx)).filter (fun a => P a = 0)).card

-- GebLean/Utilities/EraSepReduce.lean
def SimpleMonomial.PolyExpZero / SosSystem.PolyExpZero
theorem diophOf_polyExpZero   -- every diophOf system has polyExp ≡ 0
```

ETm notation (`GebLean/Era.lean`): `+ᵉ` `*ᵉ` `∸ᵉ` (truncated sub) `/ᵉ`
`%ᵉ` `^ᵉ`; constructors `.var i`, `.zero`, `.succ`; `eraNumeral`.

---

## File structure

- `GebLean/Utilities/EraSepReduce.lean` (extend): Phases A and B — the
  `ZMonomial` type and algebra, the reflection of `SosSystem.eval`, and
  Lemma 3.5. Already imports `EraDiophantine`.
- `GebLean/EraHistCodeTerm.lean` (extend): Phases C, D, E — separable
  normal form, `cubeSum_factor` application, δ-affine assembly,
  `eraCount`/`eraCount_eval`, and the witness-count bridge. Built on the
  existing `eraCountOfPack` and the `eraGeomSum` family.

No new module; layering `EraSepReduce → EraHistCodeTerm` is unchanged.

---

## Phase A — `ZMonomial` signed reflection (spec Step 1)

### Task A1: `ZMonomial` type and ℤ denotation

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: define the type.** Base-2 normal form (no `expBase`
  field: every `diophOf` exponential is base `2`, confirmed by the
  spike; carry the safeguard below).

```lean
/-- A signed simple-exponential monomial over `m` variables, the ℤ-valued
reflection of arXiv:2407.12928, Expression (6) specialised to base `2`:
`(-1)^sign · coeff · ∏ᵢ 2 ^ (expCoeff i · ρ i) · ∏ᵢ (ρ i) ^ (polyExp i)`.
The single exponential base is `2`, so no per-variable base is stored. -/
structure ZMonomial (m : ℕ) where
  sign : Bool
  coeff : ETm m
  expCoeff : Fin m → ETm m
  polyExp : Fin m → ℕ
```

- [ ] **Step 2: define `eval`.**

```lean
def ZMonomial.eval {m : ℕ} (mon : ZMonomial m) (ρ : Fin m → ℕ) : ℤ :=
  (if mon.sign then -1 else 1) *
    ((Tm.eval eraInterp mon.coeff ρ
      * (∏ i, 2 ^ (Tm.eval eraInterp (mon.expCoeff i) ρ * ρ i))
      * (∏ i, ρ i ^ mon.polyExp i) : ℤ))
```

- [ ] **Step 3: `ZMonomial.evalNat`** (the unsigned ℕ magnitude) and
  `evalNat_cast`: `(mon.evalNat ρ : ℤ) = |mon.eval ρ|`, plus
  `eval_eq` relating `eval` to `sign` and `evalNat`. These let later
  ℕ-side proofs (the final `packM` term) avoid ℤ where the value is
  known non-negative.

- [ ] **Step 4: safeguard docstring.** Record in the module docstring:
  the reflection assumes every reflected exponential is base `2`; if a
  `diophOf` atom with another base is added, the base-2 normal form
  fails and this phase must regain an `expBase` field.

- [ ] **Step 5: build + lint + axioms.**

```bash
lake build GebLean.Utilities.EraSepReduce
bash scripts/pre-commit.sh
bash scripts/check-axioms.sh
```

- [ ] **Step 6: commit.** `feat(era): add the ZMonomial signed reflection type`

### Task A2: `ZMonomial.mul` and `mul_eval`

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: define the product.** Sign XOR, coefficient product,
  per-slot exponential-coefficient sum (the base-2 merge
  `2^(c₁ρ)·2^(c₂ρ) = 2^((c₁+c₂)ρ)`), per-slot polynomial-exponent sum.

```lean
def ZMonomial.mul {m : ℕ} (a b : ZMonomial m) : ZMonomial m where
  sign := xor a.sign b.sign
  coeff := a.coeff *ᵉ b.coeff
  expCoeff := fun i => a.expCoeff i +ᵉ b.expCoeff i
  polyExp := fun i => a.polyExp i + b.polyExp i
```

- [ ] **Step 2: state the agreement lemma.**

```lean
theorem ZMonomial.mul_eval {m : ℕ} (a b : ZMonomial m) (ρ : Fin m → ℕ) :
    (a.mul b).eval ρ = a.eval ρ * b.eval ρ := by
  sorry
```

- [ ] **Step 3: prove it.** Strategy: unfold `eval`/`mul`; the sign
  factor is `(-1)^(xor) = (-1)^a·(-1)^b` (`Bool.xor` case-split or
  `mul_self`); the coefficient product is `emul_eval`; the exponential
  product uses `Finset.prod_mul_distrib` with
  `2^((c₁+c₂)·ρ) = 2^(c₁ρ)·2^(c₂ρ)` (`pow_add`, after
  `add_mul`); the polynomial product likewise with
  `ρ^(p₁+p₂) = ρ^p₁·ρ^p₂`. Cast ℕ→ℤ once via `push_cast`.

- [ ] **Step 4: numeric probe (ℕ, scratch).** Pick a tiny `m`, concrete
  `ρ`, two monomials; check `(a.mul b).evalNat ρ = a.evalNat ρ *
  b.evalNat ρ` with `#eval`. Delete before commit.

- [ ] **Step 5: build + lint + axioms** (commands as A1 Step 5).

- [ ] **Step 6: commit.** `feat(era): define ZMonomial product with eval agreement`

### Task A2b: coeff grammar and the cube-degree extraction

This task resolves the spike's central obligation, which the first draft
of this plan omitted: a `diophOf` `SimpleMonomial` carries its
cube-coordinate degree inside `coeff` as an `ETm` product of `.var`
leaves (`var j` → `coeff = .var j`; `mulVars j k` →
`coeff = .var j *ᵉ .var k`), with `polyExp ≡ 0`. `cubeSum_factor` reads
degree from `polyExp`, so the var-powers of cube coordinates **must** be
moved out of `coeff` into `polyExp` before any of Phases B/C can use the
degree. This is only possible because `diophOf` coeffs lie in a
restricted grammar (`.var`, `*ᵉ`, `Era.one`); a general `ETm` `coeff` is
not analysable.

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: the coeff grammar predicate.** A monomial coeff is a
  *cube-variable product* when it is built only from `.var`, `*ᵉ`, and
  `Era.one` (the diophOf coeff grammar).

```lean
inductive ETm.IsVarProduct {m : ℕ} : ETm m → Prop
  | one  : ETm.IsVarProduct Era.one
  | var  (j : Fin m) : ETm.IsVarProduct (.var j)
  | mul  {a b : ETm m} : ETm.IsVarProduct a → ETm.IsVarProduct b →
            ETm.IsVarProduct (a *ᵉ b)
```

- [ ] **Step 2: the extraction.** Structural recursion over an
  `IsVarProduct` coeff, splitting cube slots (last `k` of `Fin (p + k)`)
  from parameter slots: cube-`.var` leaves accumulate into `polyExp`,
  everything else stays in the parameter coeff.

```lean
def ETm.extractCubeDegree {p k : ℕ} (e : ETm (p + k)) :
    ETm (p + k) × (Fin k → ℕ)
-- .one → (Era.one, 0); .var (natAdd p c) → (Era.one, single c 1);
-- .var (castAdd k i) → (.var (castAdd k i), 0); a *ᵉ b → componentwise
theorem ETm.extractCubeDegree_eval {p k : ℕ} (e : ETm (p + k))
    (he : e.IsVarProduct) (ctx : Fin p → ℕ) (a : Fin k → ℕ) :
    Tm.eval eraInterp e (Fin.append ctx a)
      = Tm.eval eraInterp (e.extractCubeDegree).1 (Fin.append ctx a)
          * ∏ c : Fin k, (a c) ^ ((e.extractCubeDegree).2 c) := by
  sorry
```

  Strategy: induction on `IsVarProduct`. The `mul` case multiplies the
  parameter parts and adds the degree vectors, using
  `Finset.prod_mul_distrib` and `pow_add`; the `var` cases evaluate
  `Fin.append` at the cube/parameter split (`Fin.append_left`/`_right`).

- [ ] **Step 3: `diophOf` coeffs satisfy the grammar.** Mirror
  `diophOf_polyExpZero`: a predicate `SosSystem.CoeffVarProduct` and the
  capstone `diophOf_coeffVarProduct` proving every monomial coeff in
  `(diophOf t).sys` is `IsVarProduct`, plus the *base pairing*
  `diophOf_basePaired` proving every slot has
  `expBase ≡ 0 ∧ expCoeff ≡ 0`, or `expBase = 2 ∧` (the `pow2Var`
  slot). These two are the hypotheses A3/A4 consume.

  Required helper (do not omit): `diophOf` systems are spliced and
  *weakened* from sub-systems (`spliceWeaken`/`binExtEmb`,
  `EraDiophantine.lean:639,1528`), and `SimpleMonomial.weaken` rewrites
  the coeff via `coeff.subst (fun i => .var (f i))` (`:447`). So
  `IsVarProduct` must be shown closed under variable-renaming `subst`
  (`.var j ↦ .var (f j)`, products and `one` preserved) — a structural
  lemma `ETm.IsVarProduct.weaken`, the coeff-grammar analog of the
  existing `SimpleMonomial.weaken_polyExpZero`/
  `SosSystem.weaken_polyExpZero` (`EraSepReduce.lean:182,216`). This is
  strictly more work than the index-level `polyExp` preservation
  (`subst` is structural over `ETm`, not a `Fin → ℕ` re-index); list it
  as an explicit sub-step of the capstone.

- [ ] **Step 4: build + lint + axioms.**

- [ ] **Step 5: commit.** `feat(era): extract cube-variable degree from coeff`

### Task A3: reflect `SimpleMonomial`/`SimpleSum` into `ZMonomial`

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: lift a single monomial (degree into `polyExp`).** Run
  `extractCubeDegree` on `coeff` to split off the cube-variable powers,
  giving a parameter-only coeff and a per-cube-coordinate degree vector;
  add that vector to the (already-zero) `polyExp`. Base-2 exponential
  slots keep their `expCoeff`; base-0 slots have `expCoeff 0` (factor
  `1`).

```lean
def SimpleMonomial.toZ {p k : ℕ} (mon : SimpleMonomial (p + k)) :
    ZMonomial (p + k) where
  sign := false
  coeff := (mon.coeff.extractCubeDegree).1
  expCoeff := fun i => mon.expCoeff i
  polyExp := fun i =>
    mon.polyExp i + (match i with
      | ⟨_, _⟩ => /- (extractCubeDegree).2 at the cube slot, else 0 -/ 0)
```

  The `polyExp` addend is `(mon.coeff.extractCubeDegree).2 c` at cube
  slot `Fin.natAdd p c` and `0` at parameter slots; finalise the
  `Fin.append`-index plumbing at execution.

- [ ] **Step 2: agreement.**

```lean
theorem SimpleMonomial.toZ_eval {p k : ℕ} (mon : SimpleMonomial (p + k))
    (ctx : Fin p → ℕ) (a : Fin k → ℕ)
    (hcoeff : mon.coeff.IsVarProduct)
    (hbase : ∀ i, (Tm.eval eraInterp (mon.expBase i) (Fin.append ctx a) = 0
                    ∧ Tm.eval eraInterp (mon.expCoeff i) (Fin.append ctx a) = 0)
                  ∨ Tm.eval eraInterp (mon.expBase i) (Fin.append ctx a) = 2) :
    mon.toZ.eval (Fin.append ctx a) = (mon.eval (Fin.append ctx a) : ℤ) := by
  sorry
```

  Strategy: `extractCubeDegree_eval` (A2b) rewrites the `coeff` factor
  into parameter-coeff times the cube-degree product, matching the
  `polyExp` addend; per slot, the base pairing gives `0^0 = 1` (base 0)
  or `2^(c·ρ)` (base 2) via `Finset.prod_congr`.

- [ ] **Step 3: lift a sum.** `SimpleSum.toZ : SimpleSum (p+k) → List
  (ZMonomial (p+k)) := p.map SimpleMonomial.toZ`, with
  `SimpleSum.toZ_eval`: `(p.toZ.map (·.eval (Fin.append ctx a))).sum =
  (p.eval (Fin.append ctx a) : ℤ)` under the per-monomial grammar/base
  hypotheses. Strategy: `List.map`/`sum` induction plus Step 2.

- [ ] **Step 4: build + lint + axioms.**

- [ ] **Step 5: commit.** `feat(era): reflect SimpleMonomial sums into ZMonomial`

### Task A4: reflect `SosSystem.eval` into a signed `ZMonomial` list

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: define the atom reflection.** For `sqDist P Q`, produce
  the list realising `P² + Q² − 2PQ`: the cross products via
  `ZMonomial.mul`, with the `−2PQ` block sign-negated and coefficient
  doubled (numeral `2` folded into `coeff`). For `prod s t`, distribute
  the product of the two sub-systems' reflections (pairwise
  `ZMonomial.mul`). Recurse over the mutual `SosTerm`/`SosSystem`
  structure.

```lean
-- over the (p + k) split, since the defs call SimpleMonomial.toZ {p k}
-- (a bare `m` cannot supply the param/cube split extractCubeDegree needs)
def SosTerm.toZ {p k : ℕ} (a : SosTerm (p + k)) : List (ZMonomial (p + k))
def SosSystem.toZ {p k : ℕ} (s : SosSystem (p + k)) : List (ZMonomial (p + k))
```

- [ ] **Step 2: the pointwise agreement on values.**

```lean
theorem SosSystem.toZ_eval {p k : ℕ} (s : SosSystem (p + k))
    (ctx : Fin p → ℕ) (a : Fin k → ℕ)
    (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired) :
    ((s.toZ).map (fun mon => mon.eval (Fin.append ctx a))).sum
      = (SosSystem.eval s (Fin.append ctx a) : ℤ) := by
  sorry
```

  Strategy: mutual induction. `sqDist` case uses
  `(A − B)² + (B − A)² = A² + B² − 2AB` over ℤ (the ℕ truncated form
  equals this; `sqDist_eval_eq_zero_iff` and `x²+y² ≥ 2xy` for the
  non-underflow) plus `SimpleSum.toZ_eval` (A3) and `ZMonomial.mul_eval`.
  `prod` case uses `Finset`/`List` product distribution and the
  recursion. Push casts with `push_cast`/`omega` for the ℕ↔ℤ bridge.

- [ ] **Step 3: discharge the hypotheses from `diophOf`.** Apply
  `diophOf_coeffVarProduct` and `diophOf_basePaired` (Task A2b Step 3)
  to obtain `(diophOf τ).sys.CoeffVarProduct` and `.BasePaired`, the two
  hypotheses `toZ_eval` consumes. (The existing `PolyExpZero` traversal
  is the pattern to mirror, but does not itself supply the coeff-grammar
  or base-pairing facts — those are the new A2b capstones.)

- [ ] **Step 4: build + lint + axioms.**

- [ ] **Step 5: commit.** `feat(era): reflect the SoS predicate value over ZMonomial`

---

## Phase B — Lemma 3.5 degree reduction (spec Step 2; dominant)

Transcribes arXiv:2407.12928, Lemma 3.5 (paper lines 739–787). For a
reflected predicate of per-coordinate non-exponential degree `> 2`,
introduce chain variables and re-express at degree ≤ 2 with a unique
witness. Operates on `List ZMonomial` over `Fin (p + k)`.

### Task B1: chain-variable equations and substitution

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: chain equations.** For a cube variable `x` of
  non-exponential degree `h`, define the `h` defining equations
  `x − y₁ = 0`, `y₁x − y₂ = 0`, …, `y_{h-1}x − y_h = 0` as `ZMonomial`
  lists (each a two-term signed difference), over an enlarged variable
  set `Fin (p + k + f)` (`f` = total chain variables). Provide the
  weakening of existing monomials into the enlarged scope (reuse
  `SimpleMonomial.weaken`/`SimpleSum.weaken` patterns; define
  `ZMonomial.weaken`).

```lean
def ZMonomial.weaken {m m' : ℕ} (mon : ZMonomial m) (f : Fin m → Fin m') :
    ZMonomial m'
-- mirrors SimpleMonomial.eval_weaken, which requires injectivity of `f`
theorem ZMonomial.weaken_eval {m m' : ℕ} (mon : ZMonomial m)
    (f : Fin m → Fin m') (hf : Function.Injective f) (ρ : Fin m' → ℕ) :
    (mon.weaken f).eval ρ = mon.eval (ρ ∘ f) := ...
```

  The chain-variable embeddings are injective, so `hf` discharges; the
  hypothesis is mandatory (omitting it, as the first draft did, makes the
  lemma unprovable — `SimpleMonomial.eval_weaken` carries the same).

- [ ] **Step 2: substitution.** Replace each non-exponential occurrence
  of `x^i` (i.e. a `polyExp` value `i ≥ 1` at slot `x`) with the chain
  variable `y_i` (a `polyExp 1` at the new slot), yielding a monomial of
  per-slot non-exponential degree ≤ 1. Define `ZMonomial.chainSub` and
  prove `chainSub_eval`: on the sub-domain where the chain equations
  hold (`y_i = x^i`), the substituted monomial agrees with the original.

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): build Lemma 3.5 chain variables and substitution`

### Task B2: degree bound of the squared system

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: define the reduced system.** `R := ∑ Sᵢ² + P_sub²`
  where the `Sᵢ` are the chain equations (Task B1) and `P_sub` is the
  substituted predicate. Each square is expanded via `ZMonomial.mul`
  (squares of degree-≤1 monomials → degree ≤ 2).

```lean
def sepReduce {p k : ℕ} (s : SosSystem (p + k)) :
    Σ f : ℕ, List (ZMonomial (p + k + f))
```

- [ ] **Step 2: state and prove the degree bound.** Every monomial of
  `(sepReduce s).2` has `polyExp i ≤ 2` for all `i`. Strategy: the chain
  substitution makes every factor degree ≤ 1; `ZMonomial.mul` adds
  `polyExp`, so a product of two degree-≤1 monomials is degree ≤ 2
  (paper lines 776–783: the `m²` and `2mm′` monomial kinds).

```lean
theorem sepReduce_degree {p k} (s : SosSystem (p + k)) :
    ∀ mon ∈ (sepReduce s).2, ∀ i, mon.polyExp i ≤ 2 := by
  sorry
```

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): bound the reduced system to degree 2`

### Task B3: soundness of the reduced system

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: state it** (paper Lemma 3.5, condition 2).

```lean
theorem sepReduce_sound {p k} (s : SosSystem (p + k))
    (ρ : Fin (p + k) → ℕ) (b : Fin (sepReduce s).1 → ℕ)
    (hR : (((sepReduce s).2).map (fun mon => mon.eval (Fin.append ρ b))).sum = 0) :
    SosSystem.eval s ρ = 0 := by
  sorry
```

- [ ] **Step 2: prove it.** `R = 0` is a sum of squares over ℤ, so each
  square is `0`: the chain equations hold (`y_i = x^i`) and `P_sub = 0`;
  by `chainSub_eval` (B1) `P_sub` agrees with `P`, so `P = 0`. Use
  `Finset`/`List` sum-of-squares-zero (`sq_eq_zero_iff` /
  non-negativity), and the A4 agreement to return to `SosSystem.eval`.

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): prove Lemma 3.5 soundness of the reduced system`

### Task B4: unique-witness condition

**Files:**

- Modify: `GebLean/Utilities/EraSepReduce.lean`

- [ ] **Step 1: state it** (paper Lemma 3.5, condition 3).

```lean
theorem sepReduce_unique {p k} (s : SosSystem (p + k))
    (ρ : Fin (p + k) → ℕ) (hP : SosSystem.eval s ρ = 0) :
    ∃! b : Fin (sepReduce s).1 → ℕ,
      (((sepReduce s).2).map (fun mon => mon.eval (Fin.append ρ b))).sum = 0 := by
  sorry
```

- [ ] **Step 2: prove it.** The chain equations force `y_i = x^i`
  uniquely (existence: set `b` from the powers of `ρ`'s cube
  coordinates; uniqueness: each `Sᵢ = 0` pins `y_i`). With those `b`,
  `P_sub = P = 0`, so `R = 0`. Strategy: `ExistsUnique.intro` with the
  explicit witness `b i := (ρ (cube slot))^(degree i)`; uniqueness by
  induction along the chain.

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): prove Lemma 3.5 unique witness`

---

## Phase C — separable normal form and `cubeSum_factor` (spec Step 3)

### Task C1: separable normal form (coeff to polyExp)

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: split parameter vs cube slots.** For a degree-≤2
  `ZMonomial` over `Fin (p + k)` (cube coordinates the last `k`),
  re-express its `eval` at `Fin.append ctx a` as
  `α(ctx) · ∏_{c<k} 2^(γ_c · a_c) · a_c^{u_c}` where `α` absorbs the
  parameter slots' `coeff`, exponential and polynomial factors, and
  `γ_c`, `u_c` are the cube slots' `expCoeff`-value and `polyExp`.

```lean
theorem ZMonomial.cubeFactor {p k : ℕ} (mon : ZMonomial (p + k))
    (ctx : Fin p → ℕ) (a : Fin k → ℕ) :
    mon.evalNat (Fin.append ctx a)
      = (/- α(ctx) : ℕ -/) * ∏ c : Fin k,
          2 ^ ((Tm.eval eraInterp (mon.expCoeff (Fin.natAdd p c)) (Fin.append ctx a))
                * a c) * (a c) ^ mon.polyExp (Fin.natAdd p c) := by
  sorry
```

  Strategy: `Fin.prod_univ_add` splits `∏_{i<p+k}` into the parameter
  block `∏_{i<p}` (constant in `a`) and the cube block `∏_{c<k}`. The
  cube polynomial exponents `u_c = mon.polyExp (natAdd p c)` are now
  populated by Task A3's `extractCubeDegree` normalisation (this was the
  step the first draft omitted; without it every `u_c` was `0` and this
  lemma was false). `cubeSum_factor`'s `vbase` argument is a fixed
  `Fin k → ℕ`, so it is evaluated once at the given `ctx`: set
  `vbase_c := 2^(γ_c(ctx))` where `γ_c = expCoeff (natAdd p c)` evaluated
  at `ctx` (for `diophOf` cube exponentials, `γ_c` is `1`, giving
  `vbase_c = 2`; a `ctx`-dependent `γ_c` is permitted since `vbase` need
  only be `a`-independent, which `Fin.append`'s parameter block is).

- [ ] **Step 2: build + lint + axioms.**

- [ ] **Step 3: commit.** `feat(era): put degree-2 ZMonomials in cube form`

### Task C2: per-monomial cube-sum via `cubeSum_factor`

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: the weighted cube sum of one monomial.** With the
  `packM` weight `2^(2w·mixedRadix k t a)` (= `∏_c (2^(2w·tᶜ))^(a c)`,
  the `mixedRadix` expansion), and a degree-≤2 monomial in separable
  form, the cube sum factors:

```lean
theorem eraMonoCubeSum {p k : ℕ} (mon : ZMonomial (p + k)) (ctx : Fin p → ℕ)
    (w t : ℕ) (hdeg : ∀ i, mon.polyExp i ≤ 2) :
    (∑ a ∈ cubePoints k t,
        2 ^ (2 * w * mixedRadix k t a) * mon.evalNat (Fin.append ctx a))
      = (/- α(ctx) -/) * ∏ c : Fin k, (/- ∑_{j<t} jᵘ · vbaseⱼ -/) := by
  sorry
```

  Strategy: substitute C1, fold the weight into `vbase_c := 2^(2w·tᶜ +
  γ_c(ctx))`, apply `cubeSum_factor` with `u c = polyExp`, then identify
  each inner `∑_{j<t} jᵘ·vbase^j` with `G_{u}` (`u ∈ {0,1,2}`).

- [ ] **Step 2: realise each `G_u` as a term and discharge base ≥ 2.**
  Map `u = 0,1,2` to `eraGeomSum`/`eraLinGeomSum`/`eraSqGeomSum`. Each
  eval lemma needs `2 ≤ vbase_c`; discharge from the `2^(2w·tᶜ)` factor
  (`hw : 0 < w`, `ht : 0 < t` give `2w·tᶜ ≥ 1` for the lowest block, and
  `≥ 1` overall, so `vbase_c ≥ 2`). State `eraMonoTerm : ETm p` (the
  product of `eraNumeral`-substituted `G` terms times the `α` term) with
  `eraMonoTerm_eval` equal to Step 1's right side.

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): factor a degree-2 monomial cube sum`

---

## Phase D — δ-affine assembly and read-off (spec Step 4)

### Task D1: the constant part `C(ε, k)` (Eq (7))

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: define and evaluate.** `ε` is the parameter-only
  (cube-degree-zero) monomial of the reflected `R`. Following Eq (7)
  (paper lines 605–611):

```lean
def eraConstPart {p} (epsTerm tTerm wTerm : ETm p) (k : ℕ) : ETm p
theorem eraConstPart_eval {p} (epsTerm tTerm wTerm) (k) (ctx) ... :
    Tm.eval eraInterp (eraConstPart epsTerm tTerm wTerm k) ctx
      = ∑ a ∈ cubePoints k t,
          2 ^ (2*w*mixedRadix k t a) * (2^w - 1) * (2^w - eps + 1) := by
  sorry
```

  Strategy: the `a`-independent factor `(2^w−1)(2^w−ε+1)` times the pure
  geometric `∑_a 2^(2w·v(a))` (a `u ≡ 0` instance of `eraMonoCubeSum` /
  `cubeSum_factor` with `G₀`), assembled with `∸ᵉ`, `*ᵉ`.

- [ ] **Step 2: build + lint + axioms.**

- [ ] **Step 3: commit.** `feat(era): realise the Eq (7) constant part as a term`

### Task D2: the packed-witness term and `eval = packM`

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: assemble `packM_term`** (spec Step 4, pinned sign
  convention). `packM_term := eraConstPart − (2^w−1)·∑ⱼ eraMonoTerm
  mⱼ`, where the `mⱼ` are the non-constant reflected monomials and
  `eraMonoTerm` is unsigned (Task C2); the `−(2^w−1)` factor is applied
  once with `∸ᵉ`.

```lean
def packM_term {p k} (s : SosSystem (p + k)) (tTerm wTerm : ETm p) : ETm p
```

- [ ] **Step 2: the master eval lemma.**

```lean
theorem packM_term_eval {p k} (s : SosSystem (p + k)) (tTerm wTerm) (ctx)
    (ht : 0 < t) (hw : 0 < w)
    (hP : ∀ a ∈ cubePoints k t, SosSystem.eval s (Fin.append ctx a) < 2^w) :
    Tm.eval eraInterp (packM_term s tTerm wTerm) ctx
      = packM k w t (fun a => SosSystem.eval s (Fin.append ctx a)) := by
  sorry
```

  Strategy: unfold `packM`, rewrite `deltaBlock` via `deltaBlock_affine`
  (needs `hP`), split the affine form into the constant part (D1) minus
  `(2^w−1)·∑_a 2^(2wv(a))·P(a)`; reflect `P(a)` into `∑ⱼ mⱼ` (A4) and
  apply `eraMonoCubeSum` (C2) per monomial; the non-underflow of the top
  `∸ᵉ` follows from `deltaBlock ≥ 0` (i.e. `δ ≥ 0`, `one_le_packM`-style
  reasoning). Signs: the signed `mⱼ` collect into the single subtraction
  via the ℤ reflection, then cast back to ℕ where `packM ≥ 0`.

- [ ] **Step 3: numeric probe (ℕ, scratch).** Tiny `s`, `k`, concrete
  `w`, `t`, `ctx`; check `Tm.eval … (packM_term …) ctx` equals
  `packM …` by `#eval` on ℕ. Delete before commit.

- [ ] **Step 4: build + lint + axioms.**

- [ ] **Step 5: commit.** `feat(era): assemble the packed-witness term via Eqs (7),(8)`

### Task D3: `eraCount` over the reduced system

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: define `eraCount`** by feeding `packM_term` of the
  reduced system into `eraCountOfPack`.

```lean
def eraCount {p k} (s : SosSystem (p + k)) (tTerm wTerm : ETm p) : ETm p :=
  eraCountOfPack k (packM_term s tTerm wTerm) tTerm wTerm
```

- [ ] **Step 2: `eraCount_eval` for the reduced system** (count of its
  zeros on the cube), by chaining `packM_term_eval` (D2) with
  `eraCountOfPack_eval`.

```lean
theorem eraCount_eval {p k} (s : SosSystem (p + k)) (tTerm wTerm) (ctx)
    (ht : 0 < t) (hw : 0 < w) (hP : ...) :
    Tm.eval eraInterp (eraCount s tTerm wTerm) ctx
      = ((cubePoints k t).filter
          (fun a => SosSystem.eval s (Fin.append ctx a) = 0)).card := by
  sorry
```

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): count a reduced system's cube zeros as a term`

---

## Phase E — witness-count preservation (spec Step 5; dominant)

Threads the three `∃!` layers so the count of `R`'s zeros over the
enlarged cube equals the original predicate's count over the base cube.

### Task E1: the bound terms `θ` and `w` as `Era` terms

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: build `θ`.** The chain variables satisfy `y_i ≤ x^i`;
  with `x < t`, `y_i < t^i ≤ t^h`. Define `eraTheta` as the
  `eraMajorant`-derived bound on the cube side that dominates every
  chain variable, a concrete `ETm`. Prove `eraTheta_spec`: every chain
  witness from `sepReduce_unique` is `< Tm.eval eraInterp eraTheta ctx`.

- [ ] **Step 2: build the enlarged `w`.** `eraW` dominates
  `R(ctx, a, b)` on the product cube `max(t, θ)`, from
  `eraMajorant` applied to the reduced system's value term. Prove
  `eraW_spec`: `R(...) < 2^(eval eraW ctx)` on the cube.

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): exhibit the Lemma 3.5 cube bounds as Era terms`

### Task E2: count collapse across the enlarged cube

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: fibre collapse at the enlarged side.** For each
  enlarged-cube point `a` (side `tθ = max(t, θ)`) with `P(a) = 0`, the
  `b`-fibre of `R = 0` is a singleton (`sepReduce_unique`, B4) **and**
  that unique `b` is `< tθ` (`eraTheta_spec`, E1); for `P(a) ≠ 0` it is
  empty (`sepReduce_sound`, B3, contrapositive). Hence

```lean
theorem reducedCount_eq {p k} (s : SosSystem (p + k)) (ctx : Fin p → ℕ)
    (tθ : ℕ) (hbounds : ...) :
    ((cubePoints ((sepReduce s).1) tθ ×ˢ cubePoints k tθ).filter
        (fun ab => /- R = 0 -/)).card
      = ((cubePoints k tθ).filter
          (fun a => SosSystem.eval s (Fin.append ctx a) = 0)).card := by
  sorry
```

  Strategy: `Finset.card_eq_of_bijective` / fibre cardinality
  (`Finset.card_filter` over the product) using the singleton/empty
  fibre.

- [ ] **Step 2: shell-empty bridge `tθ → t`.** The first draft left a
  gap here (the count above is at side `tθ`, but the downstream target
  is at the base side `t`). Close it with the majorant bound: the
  predicate `P = SosSystem.eval s` has **no** zero whose any coordinate
  lies in `[t, tθ)`, because `t` is the `eraMajorant`-derived side that
  dominates every solution coordinate (paper arXiv:2606.09336, Claims
  1–2). Discharge `hshell` from `diophOf_bound` (each solution
  coordinate `< (diophOf τ).bound i`) composed with `eraMajorant_mono`
  (`EraDiophantine.lean:239`), which uniformises the per-witness bounds
  to the single side `t`. Note `eraMajorant_spec` bounds a term *value*,
  not a solution *coordinate*, so it is **not** the lemma that
  discharges `hshell`. So the shell contributes no zeros and

```lean
theorem predCount_side_eq {p k} (s : SosSystem (p + k)) (ctx : Fin p → ℕ)
    (t tθ : ℕ) (htθ : t ≤ tθ)
    (hshell : ∀ a ∈ cubePoints k tθ,
      SosSystem.eval s (Fin.append ctx a) = 0 → ∀ c, a c < t) :
    ((cubePoints k tθ).filter (fun a => SosSystem.eval s (Fin.append ctx a) = 0)).card
      = ((cubePoints k t).filter (fun a => SosSystem.eval s (Fin.append ctx a) = 0)).card := by
  sorry
```

  with `hshell` discharged from `eraMajorant_spec` at the call site.
  Strategy: the filtered set is unchanged when restricting the cube from
  side `tθ` to side `t` (`Finset.filter_subset`/`card` with the shell
  membership ruled out by `hshell`).

- [ ] **Step 3: compose with `diophOf_unique`.** When `s = (diophOf
  τ).sys`, the base-cube count `#{a : SosSystem.eval s (append ctx a) =
  0}` is itself the `diophOf` `∃!`-witness count; record the corollary
  bridging to whatever downstream `solCount`-shaped quantity Task 6.4d/e
  consumes (state against `diophOf_unique`; finalise the exact target at
  6.4d/e). See Task E3 for the index-layout reconciliation `diophOf`'s
  `Fin (n+1+witArity)` needs against the `(p + k)` split.

- [ ] **Step 4: build + lint + axioms.**

- [ ] **Step 5: commit.** `feat(era): collapse enlarged-cube count to base`

### Task E3: `eraCount`/`eraCount_eval` final contract

**Files:**

- Modify: `GebLean/EraHistCodeTerm.lean`

- [ ] **Step 1: reconcile the `diophOf` index layout.** `diophOf τ` for
  `τ : ETm n` produces `sys : SosSystem (n + 1 + witArity)` (the `n`
  inputs, one output slot, then the witnesses) and `DiophEnc.ctx`/
  `diophOf_unique`/`diophOf_bound` are stated over that layout
  (`EraDiophantine.lean:656-664, 2339`), **not** over a bare
  `Fin (p + k)` with `Fin.append ctx a`. Before `eraCountPred` can be
  stated, fix the map: the `p` parameters are the `diophOf` inputs that
  stay free, and the `k = 1 + witArity` cube coordinates are the output
  slot plus the witnesses (the existentially-counted variables).
  Caution (do not type this as a bare `≃`): `DiophEnc.ctx ρ y w =
  Fin.append (Fin.snoc ρ y) w` (`EraDiophantine.lean:671-673`) places the
  output `y` on the `Fin.snoc ρ`/parameter-block side, whereas this
  phase's `Fin.append ctx a` puts the output on the cube side. So the
  re-indexing must *move* the output slot across the param/cube boundary
  — it is a `Fin.append`/`Fin.snoc`/`spliceEmb` composite, not the
  re-association `n + (1 + witArity) = (n + 1) + witArity`. State it as
  that composite plus a lemma equating `SosSystem.eval (diophOf τ).sys`
  under it with the `Fin.append ctx a` form the rest of this phase uses.
  This is the concrete obligation Task E2 Step 3 deferred.

- [ ] **Step 2: state the public combinator** that 6.4d/6.4e call:
  given a predicate term `τ`, `t`/`w` derived from `eraMajorant`,
  `eraCountPred τ` evaluates to the count of witness assignments making
  the `diophOf` system vanish, obtained by `eraCount` on
  `sepReduce (diophOf τ).sys` (D3) composed with `reducedCount_eq` +
  `predCount_side_eq` (E2) and the `θ`/`w` bounds (E1), all transported
  along the Step-1 re-indexing.

The RHS is concrete (it must typecheck standalone): the count of
cube points — output slot plus witnesses, side `tBase` the
`eraMajorant`-derived base bound — at which the `diophOf` system
vanishes, written via the Step-1 re-indexing `reindex`.

```lean
def eraCountPred {n : ℕ} (τ : ETm n) : ETm n
theorem eraCountPred_eval {n : ℕ} (τ : ETm n) (ctx : Fin n → ℕ)
    (htBase : /- tBase from eraMajorant, with the solution bound -/) :
    Tm.eval eraInterp (eraCountPred τ) ctx
      = ((cubePoints (1 + (diophOf τ).witArity) tBase).filter
          (fun a => SosSystem.eval (diophOf τ).sys (reindex ctx a) = 0)).card := by
  sorry
```

  This statement is complete and provable from D3 + E2 + E1 alone. The
  *corollary* relating this count to the downstream `solCount`-shaped
  quantity (via `diophOf_unique` collapsing the unique-witness fibre to a
  count over the output slot) is pinned jointly with Task 6.4d/6.4e,
  which consume it; it is a separate lemma on top of this one, not a hole
  in this RHS.

- [ ] **Step 3: build + lint + axioms.**

- [ ] **Step 4: commit.** `feat(era): expose the Era count combinator`

---

## Self-review checklist (run before adversarial review)

- [ ] **Spec coverage.** Step 1 → Phase A; Step 2 → Phase B; Step 3 →
  Phase C; Step 4 → Phase D; Step 5 → Phase E. Each spec obligation maps
  to a task.
- [ ] **No placeholders.** Every code step shows a signature; every
  proof step a strategy; every task a build/lint/axiom verify and a
  commit-message subject (≤ 72 char, imperative, lowercase, no period).
- [ ] **Type consistency.** `ZMonomial`, `ZMonomial.eval`/`evalNat`,
  `ZMonomial.mul`, `SosSystem.toZ`, `sepReduce`, `packM_term`,
  `eraCount`, `eraCountPred` carry consistent signatures across tasks.
- [ ] **Sign convention.** `eraMonoTerm` is unsigned; the single
  `−(2^w−1)` factor lives in `packM_term` (D2), matching the spec's
  pinned convention.
- [ ] **Base-2 safeguard.** `ZMonomial` drops `expBase` on the
  confirmed base-2 invariant; the safeguard docstring (A1) names the
  condition under which it must be regained.
- [ ] **Constructive bounds.** `θ`/`w` are exhibited as `ETm`
  (`eraTheta`/`eraW`, E1), never asserted existential.
- [ ] **Layering.** All new declarations live in `EraSepReduce`
  (Phases A,B) or `EraHistCodeTerm` (Phases C–E); no new module;
  `EraCompleteness` is not made to import `EraRecurrence`.
- [ ] **Markdownlint + doctoc** on this file.

## References

- arXiv:2407.12928, § 4: Lemma 3.1 (`δ`), Lemma 3.2 (`cubeSum_factor`),
  Lemma 3.3 (read-off), Eqs (7),(8), Lemma 3.5 (degree reduction),
  Corollary 3.6. Local copy:
  `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`.
- arXiv:2606.09336: Claims 1–5, the Section-4 read-off. Local copy:
  `/home/terence/wingeb/undecidability-chaos-universality-arithmetic-terms.pdf`.
- Design spec:
  `docs/superpowers/specs/2026-06-17-era-packm-term-design.md`.
- Parent sub-plan:
  `docs/superpowers/plans/2026-06-16-era-task6.4-histcode-term-subplan.md`.
