# Era completeness Phase-4/5 sub-plan: reduction and counting engine

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [How to work this plan](#how-to-work-this-plan)
- [Transcription provenance](#transcription-provenance)
- [Phase 4 architecture (the design the re-checkpoint settled)](#phase-4-architecture-the-design-the-re-checkpoint-settled)
  - [Carrier: typed squared-difference / product atoms](#carrier-typed-squared-difference--product-atoms)
  - [Induction: per-`EraB`-constructor gadgets, not basis translation](#induction-per-erab-constructor-gadgets-not-basis-translation)
- [File structure](#file-structure)
- [Phase 4 — `EraDiophantine.lean`: the term-to-Diophantine reduction](#phase-4--eradiophantinelean-the-term-to-diophantine-reduction)
  - [Task 4.0: numeric pre-validation (throwaway)](#task-40-numeric-pre-validation-throwaway)
  - [Task 4.1: the `SosSystem` algebra (squared-difference / product atoms)](#task-41-the-sossystem-algebra-squared-difference--product-atoms)
  - [Task 4.2: the `DiophEnc` carrier and its context assembly](#task-42-the-diophenc-carrier-and-its-context-assembly)
  - [Task 4.3: Identity (4) — the exponent reduction `pow_eq_two_pow_mod`](#task-43-identity-4--the-exponent-reduction-pow_eq_two_pow_mod)
  - [Task 4.4: `SosSystem` re-indexing and witness-extension helpers](#task-44-sossystem-re-indexing-and-witness-extension-helpers)
  - [Task 4.5: the base and structural cases (`var`, `zero`, `succ`)](#task-45-the-base-and-structural-cases-var-zero-succ)
  - [Task 4.6: the `add`, `mul`, `pow2` cases](#task-46-the-add-mul-pow2-cases)
  - [Task 4.7: the `mod` and `tsub` cases](#task-47-the-mod-and-tsub-cases)
  - [Task 4.8: the `div` case](#task-48-the-div-case)
  - [Task 4.9: the `pow` case via Identity (4)](#task-49-the-pow-case-via-identity-4)
  - [Task 4.10: assemble `diophOf` and prove the invariants](#task-410-assemble-diophof-and-prove-the-invariants)
- [Phase 5 — `EraHypercube.lean`: the counting engine and the read-off](#phase-5--erahypercubelean-the-counting-engine-and-the-read-off)
  - [Task 5.1: the mixed-radix enumeration (computable)](#task-51-the-mixed-radix-enumeration-computable)
  - [Task 5.2: the cube-sum factorisation through `G₀`/`G₁`/`G₂`](#task-52-the-cube-sum-factorisation-through-g%E2%82%80g%E2%82%81g%E2%82%82)
  - [Task 5.3: `HW`-additivity over disjoint blocks](#task-53-hw-additivity-over-disjoint-blocks)
  - [Task 5.4: the packed number `M` and the count read-off](#task-54-the-packed-number-m-and-the-count-read-off)
  - [Task 5.5: positional coding and the recurrence read-off](#task-55-positional-coding-and-the-recurrence-read-off)
- [Handoff to Phase 6 (interface confirmation, not re-specified here)](#handoff-to-phase-6-interface-confirmation-not-re-specified-here)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the term-to-Diophantine reduction (`diophOf : ETm n →
DiophEnc n`, the recurrence paper's Lemma 2) and the hypercube counting
engine (`HW(M)/w − tᵏ`, the method paper's Theorem 3.4 / Corollary 3.6),
the two discovery-heavy phases of the Era completeness construction,
delivering the interfaces that `eraBSum`/`eraBProd` (Phase 6) consume.

**Architecture:** Phase 4 represents a term's graph `t.eval ρ = y` as a
sum-of-squares system with a unique, explicitly-bounded witness tuple, by
structural induction on `ETm`. The predicate is carried as a typed
datatype of squared-difference and product atoms (`SosSystem`), so its
zero-set is an exact boolean combination of equalities and "sum of
non-negative squares" is structural — only uniqueness and witness bounds
remain as proof obligations. Phase 5 packs the per-cube-point values into
one natural number via the `δ` indicator and reads the solution count off
its binary Hamming weight, factoring the packed number through the
generalised geometric progressions `G₀`/`G₁`/`G₂` (Phase 1, already on
`main`). Witness bounds and the packing width come from the Phase-3.5
majorant `eraMajorant`.

**Tech stack:** Lean 4, Mathlib (pin `v4.29.0-rc6`), `lake build` /
`lake test` / `lake lint`, `scripts/check-axioms.sh`. Constructive-only
(no `noncomputable`); axiom-clean (`propext`, `Quot.sound`,
`Classical.choice` only).

---

## How to work this plan

This plan refines the M3b plan
(`docs/superpowers/plans/2026-06-14-era-completeness-m3b-plan.md`)
§ "Phase 4" and § "Phase 5" against the now-exact `ℕ`-shapes. It is the
deliverable of the Phase-4 re-checkpoint (M3b plan § "Phase map and the
Phase-4 re-checkpoint"; decision note
`docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md`
§ 8). Phases 1, 2, 3, 3.5 are merged to `main`; Phases 6, 7 remain
specified by the M3b plan (Tasks 6.1, 6.2, 7.1, 7.2) and are not
re-derived here — this plan ends by confirming the interface those tasks
consume.

- **One declaration at a time** (`.claude/rules/lean-coding.md`): write a
  `def`/`theorem`, get it building with no `sorry`/underscore, then move
  on. `sorry` is an audited stand-in between steps only; never in a
  commit.

- **Numeric checks first, on plain `ℕ`** (`#eval`), never on symbolic
  `Tm.eval`/`ERMor1.interp` (memory: "ER / Gödel-numbering interp not
  safe for `#guard`"). Every `#eval` is throwaway: delete before commit.

- **Lean-core order lemmas only.** Era terms evaluate over core
  `Nat.le`/`Nat.lt`; mathlib dot-projections (`.le`, `.trans_lt`) and
  bare order lemmas (`le_of_lt`, `le_trans`, `lt_of_le_of_lt`) do not
  resolve. Use `Nat.`-prefixed forms (`Nat.le_of_lt`, `Nat.le_trans`,
  `Nat.lt_of_le_of_lt`, `Nat.pow_le_pow_left`,
  `Nat.pow_le_pow_right (hx : 0 < n)`, `Nat.pow_lt_pow_right`,
  `Nat.mul_lt_mul''`, `Nat.mul_le_mul`), as `eraMajorant_spec` does.

- **`ℕ`-truncated-subtraction is not integer subtraction.** Over `ℕ`,
  `(a ∸ b) = 0` whenever `a ≤ b`; a single `(a ∸ b)²` does **not** force
  `a = b`. Encode every equality `a = b` as the symmetric squared distance
  `(a ∸ b)² + (b ∸ a)²` (zero iff `a = b`; the cross term vanishes because
  at most one of `a ∸ b`, `b ∸ a` is nonzero). This is the
  `SosSystem.sqDist` atom (Task 4.1); never write a lone truncated bracket
  in a graph gadget.

- **`simp only` unused-argument warnings are build errors** under
  `-DwarningAsError`. Keep simp sets minimal; an op with no outer `succ`
  wrapper does not need `Tm.eval` in the set, one with a `succ` does.

- **Whitespace linter** (`linter.style.whitespace`, build error under
  `-DwarningAsError`): write `n + 1`, `2 ^ y₁`, `(y₁ + 1)` with spaces in
  all committed code; the code blocks below follow this.

- **Constructive `Fin` elimination.** Lean-core `Fin.cases`
  (`i.cases`/`k.elim0`); index into `Fin (eraAr b)` after `cases b` via
  `⟨0, by decide⟩`. Never the mathlib `fin_cases` tactic (pulls
  `Classical.choice`; memory). Likewise never build a bijection as `Equiv`
  data via `Fintype.equivFinOfCardEq` (it is `noncomputable`; Task 5.1).

- **De-cycling guardrail.** The engine's `HW` is the slow, log-free `ν₂`
  (`eraSigma`/`hwClosed`, Phase 3). Build no `⌊log₂⌋`/`eraIlog2`/fast-`ν₂`
  term anywhere on the critical path (M3b plan § "De-cycling"); the fast
  `ν₂` is a numeric-probe only.

- **Imports.** `EraDiophantine.lean` currently imports only `GebLean.Era`
  (which is Mathlib-free and supplies `fcons`, not `Fin.cons`). Phase 4
  uses `Fin.snoc`/`Fin.append`/`Fin.cons`/`Fin.tail`, so it must add
  `import Mathlib.Data.Fin.Tuple.Basic` (the same import `LawvereER.lean`
  uses). The reduction file is therefore not Mathlib-free; only `Era.lean`
  is. Era *terms* still evaluate over core `ℕ`, so the order-lemma rule
  above still applies.

- **Per-commit:** `bash scripts/pre-commit.sh` (`lake test` +
  `lake lint`); add `bash scripts/check-axioms.sh <file>` for each
  deliverable. Commit messages: imperative, lowercase subject, no
  trailing period, under 72 characters; end with the
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
  trailer. VCS is `jj`; no raw mutating `git`. A fresh topic bookmark is
  needed before the next push (the era ones are merged); pushes/merges
  are user-gated.

- **Index discipline.** Each new `GebLean/Utilities/X.lean` must be added
  to `GebLean/Utilities.lean` (alphabetical) or it is never built/linted.

- **Mathlib search before each from-scratch proof:** `lean_leansearch`,
  `lean_loogle`, `lean_local_search`; do not assume a lemma name.

## Transcription provenance

Binding sources, both downloaded under `arXiv` and verified against the
PDFs during this re-checkpoint:

- Istrate, Prunescu, Shunia, "Undecidability, Chaos and Universality in
  Arithmetic Terms", arXiv:2606.09336 — **Lemma 2** (term-to-Diophantine,
  Phase 4), **Lemma 3** (positional coding, Phase 5.5), **Theorem 2 /
  Corollary 2** (recurrence-to-term, Phase 5.5).
- Prunescu, Sauras-Altuzarra, "On the representation of number-theoretic
  functions by arithmetic terms", arXiv:2407.12928 — **Identity (4)**
  (`pow` reduction, § 2), **δ** + **Lemma 3.1**, **Lemma 3.2** (cube-sum
  factorisation), **Lemma 3.3** (`HW`-additivity + count), **Theorem 3.4
  / Corollary 3.6** (the counting engine), **Theorem 2.1** (slow `ν₂`).

Verified facts carried into the architecture below (do not re-derive):

1. Lemma 2's proof inducts over the minimal basis `{2ˣ, +, mod}` plus a
   projection base case — exactly a projection case, a `2^{B₁}` case, a
   `B₁ + B₂` case, and a `B₁ mod B₂` case. No separate case for `·`,
   `⌊x/y⌋`, `∸`, or general `xʸ`; those are pre-expressed in the minimal
   basis (general `xʸ` via Identity (4)). This plan extends the induction
   to the Era basis directly (§ "Phase 4 architecture").
2. Identity (4): `nᵐ = 2^((nm+n+1)m) mod (2^(nm+n+1) ∸ n)`
   (arXiv:2407.12928 eq. (4); arXiv:2606.09336 § 3), Marchenkov. The
   `mod 0 = self` convention matches Mathlib `Nat.mod`; valid including
   `0⁰ = 1`. The `b = 0` modulus `2^(a+1) ∸ a ≥ 2` for all `a`.
3. Lemma 2 invariants and bounds are **strict** (`λᵢ < Lᵢ(x⃗, y)`), with
   the integer subtraction in the source's squared brackets read over `ℕ`
   as a symmetric squared distance (the `sqDist` atom; see the
   truncated-subtraction note above). The `mod`/`div` convention is
   `y₁ mod 0 = y₁`, `⌊y₁/0⌋ = 0` (matches Mathlib `Nat.mod`/`Nat.div`).
4. The cube is `{0,…,t−1}ᵏ` (0-indexed, side `t`, `tᵏ` points); each `δ`
   block occupies `2w` bits at radix `2^(2w·v(ā))`; `G`-argument upper
   limit is `side − 1` (`G_r(q, t−1)` for a side-`t` cube). `δ(a,w) <
   2^(2w)` for `a < 2^w`, so blocks do not overlap.
5. `G₁`'s correct constant is `+ q`, not the source's printed `+ 1` (the
   `+ 1` numerator gives the wrong value for every `t`, not only the
   `t = 0` boundary); already fixed in `natLinGeomSum_mul`. `G₂` matches
   `natSqGeomSum_mul`.

## Phase 4 architecture (the design the re-checkpoint settled)

Two design questions the M3b sketch left open, with the resolution this
plan adopts. The adversarial review and the user review adjudicate them.

### Carrier: typed squared-difference / product atoms

The M3b sketch's `DiophEnc` carried the predicate as a raw
`sos : ETm (n + 1 + witArity)` with `simple`/`sos`/`uniq`/`bound_spec` as
free-standing `Prop` fields. This plan instead represents the predicate as
a typed datatype of two atoms, so its non-negativity and zero-set are
structural:

- A `SimpleMonomial m` is the data of Expression (6) (arXiv:2407.12928):
  a coefficient, per-variable exponential base and exponential
  coefficient, and per-variable constant polynomial exponent, over `m`
  variables, all `ETm m`-valued (so monomials are non-negative and compose
  with the Era term language). `SimpleSum m := List (SimpleMonomial m)` is
  a non-negative sum of monomials.
- A `SosTerm m` is either `sqDist (P Q : SimpleSum m)`, denoting the
  symmetric squared distance `(eval P ∸ eval Q)² + (eval Q ∸ eval P)²`
  (zero iff `eval P = eval Q`), or `prod (s t : List (SosTerm m))`,
  denoting `(Σ s)·(Σ t)` (zero iff `Σ s = 0` or `Σ t = 0`, by
  `Nat.mul_eq_zero`). `SosSystem m := List (SosTerm m)` denotes `Σ`.

The two `Lemma 2` invariants "sum of squares" and "non-negative /
simple" are then structural (every `SosTerm` is `≥ 0`, and its monomials
are syntactically simple). Only uniqueness and witness bounds remain as
proof obligations. Rationale: this removes the need to define and thread a
`Simple : ETm → Prop` predicate through every induction case (a large,
brittle obligation the method paper discharges informally), gives Phase 5
a structured object to fold `δ` and the `Gᵣ` factorisation over, and — the
decisive point — makes the squared-distance / product encoding the only
way to write a graph gadget, structurally excluding the unsound lone
truncated bracket. The `prod` atom is what the `mod`/`div` Case-3 gadget
(two bracket factors) needs. Cost: `SimpleMonomial`/`SimpleSum`/`SosTerm`
need an `eval` and a small constructor algebra. The alternative
(raw-`ETm` carrier with a `Simple` predicate) is recorded as the fallback
if the typed algebra proves heavier than the predicate threading it
avoids; choose before Task 4.1 and record the choice in the module
docstring (as Phase 3.5 Step 2 recorded the majorant route).

### Induction: per-`EraB`-constructor gadgets, not basis translation

`diophOf` recurses directly on `ETm n` (cases `var`, `zero`, `succ`,
`app b`), with `app b` branching on `b : EraB`. Each constructor gets its
own gadget. The alternative — translate each `ETm` into a term over the
three-op basis `{pow2, add, mod}` and induct over three cases — is
rejected: it requires re-expressing `mul`/`div`/`tsub`/`pow` as three-op
closed forms, the precise hard content the project's rich seven-op basis
(M0b) was designed to avoid. Per-constructor gadgets keep each case local
and small. Gadget inventory (each is a `SosSystem` fragment; `Bᵢ` is the
sub-term, `yᵢ` its output witness; every equality `a = b` is a
`sqDist [a-monomials] [b-monomials]` atom):

- `var i` / `zero`: base cases, no witness. `[sqDist [xᵢ] [y]]` and
  `[sqDist [] [y]]` (the latter is `(0 ∸ y)² + (y ∸ 0)² = y²`).
- `succ B₁`: `sqDist [y₁, 1] [y]` plus weakened `sys(B₁)`, witness `y₁`,
  bound `eraMajorant (succ B₁)`.
- `app add (B₁,B₂)`: Lemma 2 Case 2, `sqDist [y₁, y₂] [y]` plus the two
  sub-systems.
- `app mul (B₁,B₂)`: direct gadget `sqDist [y₁·y₂] [y]` (`y₁·y₂` is a
  simple monomial, polynomial exponents `1`).
- `app pow2 B₁` (`2^{B₁}`): Lemma 2 Case 1, `sqDist [2^{y₁}] [y]`
  (`2^{y₁}` is a monomial, exponential base `2`, exponential coeff `1`).
- `app mod (B₁,B₂)`: Lemma 2 Case 3, a single `prod` atom of two bracket
  sub-systems (verbatim below), witnesses `y₁, y₂, y₃, q`.
- `app tsub (B₁,B₂)`: a `prod` two-branch gadget for
  `(y₂ ≤ y₁ ∧ y = y₁ − y₂) ∨ (y₁ ≤ y₂ ∧ y = 0)`; spelled out in Task 4.7.
- `app div (B₁,B₂)`: division-with-remainder `prod` gadget
  `(B₂ ≠ 0 ∧ B₁ = y·B₂ + r ∧ r < B₂) ∨ (B₂ = 0 ∧ y = 0)`; Task 4.8.
- `app pow (B₁,B₂)`: reduce via Identity (4) to the composite
  `2^((ab+a+1)b) mod (2^(ab+a+1) ∸ a)` with `a = B₁`, `b = B₂`, then reuse
  the `pow2`/`mul`/`add`/`mod`/`tsub` gadgets on that composite. No new
  exponential gadget.

Witness-bound terms come from `eraMajorant`/`eraMajorant_mono`/
`eraMajorant_pos` (Phase 3.5): a sub-term output `yᵢ = Bᵢ.eval ρ <
eval (eraMajorant Bᵢ) ρ`; the local witnesses (`q`, `r`, `y₃`) are bounded
by the relevant first-argument majorant. These bounds are looser than
Lemma 2's tight `Lᵢ = Bᵢ + 1`, which only inflates the Phase-5 packing
width and is otherwise harmless; `eraMajorant` is the majorant the project
has.

---

## File structure

- `GebLean/Utilities/EraDiophantine.lean` (exists; holds `eraMajorant`
  and its three lemmas; imports only `GebLean.Era`): add
  `import Mathlib.Data.Fin.Tuple.Basic`, then the
  `SimpleMonomial`/`SimpleSum`/`SosTerm`/`SosSystem` algebra, the
  `DiophEnc` carrier, Identity (4), the per-constructor gadgets, and
  `diophOf` with its correctness, uniqueness, and bound lemmas.
  Responsibility: the term-to-Diophantine reduction.

- `GebLean/Utilities/EraHypercube.lean` (new): the mixed-radix
  enumeration function, the cube-sum factorisation through `G₀`/`G₁`/`G₂`,
  the packed number `M`, the `HW`-additivity step, the count read-off
  `HW(M)/w − tᵏ`, and the positional coding read-off `⌊H/Aⁿ⌋`.
  Responsibility: the counting engine at `ℕ` level and its read-off. Add
  to `GebLean/Utilities.lean` immediately after the `EraDiophantine`
  entry (the next entry is `Families`).

---

## Phase 4 — `EraDiophantine.lean`: the term-to-Diophantine reduction

### Task 4.0: numeric pre-validation (throwaway)

**Files:** scratch only (no commit).

- [ ] **Step 1: validate Identity (4) over a grid.** In a scratch `#eval`
  (plain `ℕ`), confirm `a ^ b = 2 ^ ((a*b+a+1)*b) % (2 ^ (a*b+a+1) - a)`
  for `a ∈ 0..29`, `b ∈ 0..14`, including `a = 0` (so `0^0 = 1`,
  `0^(b+1) = 0`) and `a = 1`.

```lean
#eval (List.range 30).all (fun a => (List.range 15).all (fun b =>
  a ^ b = 2 ^ ((a * b + a + 1) * b) % (2 ^ (a * b + a + 1) - a)))
```

Expected: `true`. If any cell fails, stop and re-examine the exponent
before proceeding; the identity is load-bearing for the `pow` gadget.

- [ ] **Step 2: validate the `sqDist`, `mod`, `tsub`, `div` gadget
  encodings over `ℕ`.** Confirm that the symmetric squared distance is
  zero exactly on equality, and that the full `mod`/`tsub`/`div` gadgets
  (with truncated subtraction in every bracket) have no spurious zeros and
  always admit the intended witness:

```lean
-- symmetric squared distance is zero iff equal
#eval (List.range 12).all (fun a => (List.range 12).all (fun b =>
  ((a - b) ^ 2 + (b - a) ^ 2 = 0) = (a = b)))
-- mod gadget: for y₁,y₂ ∈ 0..7, the witnesses q=⌊y₁/y₂⌋ (q=0 if y₂=0),
-- y=y₁%y₂, y₃ (only used in the y₂=0 branch) make exactly the intended
-- y reachable and no other; encode each signed bracket as a sqDist pair
-- and the two brackets as a product, then scan all (y, q) for spurious 0s
#eval (List.range 8).all (fun y1 => (List.range 8).all (fun y2 =>
  let yIntended := y1 % y2
  -- product of the two bracket sub-systems, evaluated as ℕ
  let bracket (y q y3 : Nat) : Nat :=
    (((y1 - (q * y2 + y)) ^ 2 + ((q * y2 + y) - y1) ^ 2)
      + ((y2 - (y3 + y + 1)) ^ 2 + ((y3 + y + 1) - y2) ^ 2))
    * (y2 ^ 2 + y3 ^ 2 + ((y - y1) ^ 2 + (y1 - y) ^ 2) + q ^ 2)
  -- intended witness reaches 0
  (bracket yIntended (y1 / y2) y1 = 0) &&
  -- no spurious y' ≠ yIntended with some small q,y3 reaching 0
  (List.range 8).all (fun yp => (List.range 8).all (fun q =>
    (List.range 8).all (fun y3 =>
      bracket yp q y3 = 0 → yp = yIntended)))))
```

Expected: `true`. (Adjust the bracket transcription until it matches the
Task 4.7 gadget exactly; this probe is the authority for that gadget.)
Add an analogous `div` probe (witness `r = y1 % y2`, quotient `y`).
Remove all of Task 4.0 before any commit.

### Task 4.1: the `SosSystem` algebra (squared-difference / product atoms)

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean` (add the
  `Mathlib.Data.Fin.Tuple.Basic` import here if not already present).

- [ ] **Step 1: record the carrier-design choice** (one line in the
  module docstring Implementation notes), as Phase 3.5 Step 2 recorded the
  majorant route: typed `SosSystem` atoms vs raw-`ETm`+`Simple`-predicate
  fallback.

- [ ] **Step 2: define `SimpleMonomial` and its `eval`** (Expression (6),
  arXiv:2407.12928): coefficient, per-variable exponential base and
  exponential coefficient, per-variable constant polynomial exponent.

```lean
/-- A simple exponential monomial over `m` variables (arXiv:2407.12928,
Expression (6)): `coeff · ∏ᵢ (expBase i)^(expCoeff i · xᵢ) · ∏ᵢ xᵢ^(polyExp i)`.
The bases are `ETm m`-valued so monomials compose with the Era term
language; the value is a natural number. -/
structure SimpleMonomial (m : ℕ) where
  coeff : ETm m
  expBase : Fin m → ETm m
  expCoeff : Fin m → ETm m
  polyExp : Fin m → ℕ
```

Provide `SimpleMonomial.eval : SimpleMonomial m → (Fin m → ℕ) → ℕ`
folding the products with `Finset.prod`. Numeric-check the `eval` shape on
one hand-built monomial (`2^{x₀}`, `x₀ · x₁`).

- [ ] **Step 3: define `SimpleSum`, `SosTerm`, `SosSystem` with `eval`.**

```lean
/-- A non-negative sum of simple monomials. -/
abbrev SimpleSum (m : ℕ) := List (SimpleMonomial m)

/-- A sum-of-squares atom: a symmetric squared distance `(P − Q)²` (zero
iff `P = Q`), or a product of two sub-systems (zero iff one is zero). -/
inductive SosTerm (m : ℕ) where
  | sqDist : SimpleSum m → SimpleSum m → SosTerm m
  | prod : List (SosTerm m) → List (SosTerm m) → SosTerm m

/-- A sum-of-squares system; its denotation is `Σ` over its atoms. -/
abbrev SosSystem (m : ℕ) := List (SosTerm m)
```

Provide `SimpleSum.eval p ρ := (p.map (fun mon => mon.eval ρ)).sum` and
mutually-recursive `SosTerm.eval`/`SosSystem.eval`:
`sqDist P Q ↦ (P.eval ρ ∸ Q.eval ρ)^2 + (Q.eval ρ ∸ P.eval ρ)^2`;
`prod s t ↦ SosSystem.eval s ρ * SosSystem.eval t ρ`;
`SosSystem.eval s ρ := (s.map (fun a => SosTerm.eval a ρ)).sum`.

- [ ] **Step 4: prove the zero-set characterisation.**

```lean
/-- A system is zero exactly when each atom is. -/
theorem SosSystem.eval_eq_zero_iff (s : SosSystem m) (ρ : Fin m → ℕ) :
    SosSystem.eval s ρ = 0 ↔ ∀ a ∈ s, SosTerm.eval a ρ = 0 := by
  sorry

/-- A squared-distance atom is zero iff the two sums are equal. -/
theorem SosTerm.sqDist_eval_eq_zero_iff (P Q : SimpleSum m) (ρ : Fin m → ℕ) :
    SosTerm.eval (.sqDist P Q) ρ = 0 ↔ P.eval ρ = Q.eval ρ := by
  sorry

/-- A product atom is zero iff one factor is. -/
theorem SosTerm.prod_eval_eq_zero_iff (s t : List (SosTerm m)) (ρ : Fin m → ℕ) :
    SosTerm.eval (.prod s t) ρ = 0 ↔
      SosSystem.eval s ρ = 0 ∨ SosSystem.eval t ρ = 0 := by
  sorry
```

Strategy: `List.sum_eq_zero_iff` (the natural driver; do not use the
deprecated `Nat.add_eq_zero` — use `Nat.add_eq_zero_iff`) for the system;
for `sqDist`, `Nat.add_eq_zero_iff` then `pow_eq_zero_iff`
(note `Nat.pow_eq_zero : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0`, discharge `2 ≠ 0`)
and `Nat.sub_eq_zero_iff_le` on both directions (`a ≤ b ∧ b ≤ a → a = b`);
for `prod`, `Nat.mul_eq_zero`.

- [ ] **Step 5: build, axiom-check, commit** (`feat(era): add the
sum-of-squares atom algebra`).

### Task 4.2: the `DiophEnc` carrier and its context assembly

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: define `DiophEnc`.** Carry the witness arity, the system,
  and the per-witness bound terms; correctness/uniqueness/bound are
  theorems about `diophOf` (Task 4.10), not fields. Fix the variable
  layout convention once: `n` inputs at `Fin n`, output `y` at index `n`,
  then `witArity` witnesses, with association `(n + 1) + witArity` (Lean's
  `+` is left-associative, so `n + 1 + witArity` is the same term; keep
  every `SosSystem`, `ctx`, and bound application on this association).

```lean
/-- A bounded, unique-witness, sum-of-squares Diophantine encoding of an
`ETm n` term's graph `t.eval ρ = y` (arXiv:2606.09336, Lemma 2). System
variables: the `n` inputs, then the output `y` at index `n`, then
`witArity` witnesses. "Sum of squares" and "simple" are structural
(`SosSystem`). -/
structure DiophEnc (n : ℕ) where
  witArity : ℕ
  sys : SosSystem (n + 1 + witArity)
  bound : Fin witArity → ETm (n + 1)
```

- [ ] **Step 2: define the context assembly.** Combine inputs `ρ`, output
  `y`, witnesses `w` into the system's context.

```lean
/-- Assemble inputs `ρ`, output `y`, and witnesses `w` into the system's
context `Fin (n + 1 + e.witArity) → ℕ`. -/
def DiophEnc.ctx {n : ℕ} (e : DiophEnc n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin e.witArity → ℕ) : Fin (n + 1 + e.witArity) → ℕ :=
  Fin.append (Fin.snoc ρ y) w
```

`Fin.snoc ρ y : Fin (n + 1) → ℕ`, `Fin.append _ w : Fin ((n + 1) +
e.witArity) → ℕ`, which is defeq to the stated `Fin (n + 1 + e.witArity)`
(verified during review). If reassociation ever fights elaboration,
fall back to an explicit core `Fin.cases` definition.

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): define the
DiophEnc carrier for term graphs`).

### Task 4.3: Identity (4) — the exponent reduction `pow_eq_two_pow_mod`

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: state** (validated numerically in Task 4.0):

```lean
/-- Marchenkov's identity (arXiv:2407.12928, eq. (4); arXiv:2606.09336
§ 3): a variable-base, variable-exponent power as a base-2 power modulo a
term. Valid for all `a b : ℕ`, including `0 ^ 0 = 1`. -/
theorem pow_eq_two_pow_mod (a b : ℕ) :
    a ^ b = 2 ^ ((a * b + a + 1) * b) % (2 ^ (a * b + a + 1) - a) := by
  sorry
```

- [ ] **Step 2: prove.** Strategy: set `M = a * b + a + 1`, so `2 ^ M > a`
  (`2 ^ M ≥ M + 1 > a` from `a < a * b + a + 1`). Handle `b = 0` separately
  (`a ^ 0 = 1 = 2 ^ 0 % (2 ^ (a + 1) - a)` with `2 ^ (a + 1) - a ≥ 2`).
  For `b ≥ 1`: `2 ^ (M * b) = (2 ^ M) ^ b`, and `2 ^ M = (2 ^ M - a) + a`
  with `2 ^ M - a ≥ 1`, so `(2 ^ M) ^ b ≡ a ^ b [MOD 2 ^ M - a]` by
  `Nat.ModEq` (`(x + a) ^ b ≡ a ^ b` since `x + a ≡ a`); then
  `a ^ b < 2 ^ M - a` (geometric bound: `a ^ b + a < 2 ^ (a * b + a + 1)`)
  makes the `mod` exact via `Nat.mod_eq_of_lt`. Decompose into
  (i) `(2 ^ M) ^ b ≡ a ^ b [MOD 2 ^ M - a]`, (ii) `a ^ b < 2 ^ M - a`;
  search `Nat.ModEq`, `Nat.pow_mod`, `Nat.ModEq.pow`. Budget a
  `lean4:sorry-filler-deep` pass.

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): prove the
base-2 exponent reduction identity`).

### Task 4.4: `SosSystem` re-indexing and witness-extension helpers

The induction concatenates sub-systems whose variable counts differ
(`n + 1 + witArity₁` vs the compound's `n + 1 + witArity`). Factor the
plumbing once.

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: define `weaken` along a variable re-indexing.** Provide
  `SimpleMonomial.weaken`/`SimpleSum.weaken`/`SosTerm.weaken`/
  `SosSystem.weaken` mapping a system over `m` variables to one over `m'`
  along `Fin m → Fin m'`, with the `eval` compatibility lemma
  `eval (weaken f s) ρ = eval s (ρ ∘ f)`. Use it to splice a sub-term's
  system (variables: its inputs, its output, its witnesses) into the
  compound's layout (inputs, compound `y`, then `[y₁, …, sub-witnesses…]`).
  Strategy: structural `List.map`; the `eval` lemma is `Finset.prod`/
  `List.sum` plumbing (`Finset.prod_congr`).

- [ ] **Step 2: define the output-repointing helper.** A sub-term `Bᵢ`'s
  encoding has its output at its own index `nᵢ`; in the compound it is
  re-pointed to a witness slot `yᵢ`. Provide a helper taking `diophOf Bᵢ`
  and a target witness index, returning the weakened system with `Bᵢ`'s
  output identified with that witness; state its `eval` compatibility
  lemma.

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): add
sum-of-squares re-indexing helpers`).

### Task 4.5: the base and structural cases (`var`, `zero`, `succ`)

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

Define `diophOf` incrementally; stub the `app` cases via one helper to be
filled in Tasks 4.6–4.9. Build each case's local graph lemma as a
`private` lemma, then assemble in Task 4.10. One declaration at a time.

- [ ] **Step 1: `var i`** — `witArity = 0`, `sys = [sqDist [⟨xᵢ⟩] [⟨y⟩]]`
  (monomials for variable `i` and for the output slot `n`). Graph lemma:
  `SosSystem.eval (var-system) (ctx ρ y w) = 0 ↔ y = ρ i`, via
  `SosTerm.sqDist_eval_eq_zero_iff` (Task 4.1).

- [ ] **Step 2: `zero`** — `sys = [sqDist [] [⟨y⟩]]` (`= y²`), lemma
  `… = 0 ↔ y = 0`.

- [ ] **Step 3: `succ B₁`** — witnesses = `B₁`'s plus `y₁`; system =
  weakened `sys(B₁)` (output → `y₁`) `++ [sqDist [⟨y₁⟩, ⟨1⟩] [⟨y⟩]]`;
  bound for `y₁` is `eraMajorant B₁`. Lemma: the graph holds iff
  `y = B₁.eval ρ + 1`, using the `B₁` IH and `Tm.eval`/`eraInterp`.

- [ ] **Step 4: build, axiom-check, commit** (`feat(era): encode the
projection, zero, and successor cases`).

### Task 4.6: the `add`, `mul`, `pow2` cases

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: `app add (B₁,B₂)`** — Lemma 2 Case 2. Witnesses: `B₁`'s,
  `y₁`, `B₂`'s, `y₂`. System: weakened `sys(B₁)` `++` weakened `sys(B₂)`
  `++ [sqDist [⟨y₁⟩, ⟨y₂⟩] [⟨y⟩]]`. Bounds via `eraMajorant`. Graph lemma
  `↔ y = B₁.eval ρ + B₂.eval ρ` (via `eadd_eval`/`eraInterp`).

- [ ] **Step 2: `app mul (B₁,B₂)`** — direct gadget. Add `sqDist [⟨y₁·y₂⟩]
  [⟨y⟩]`; `y₁·y₂` is one `SimpleMonomial` (the two witness variables,
  `polyExp = 1`). Bounds via `eraMajorant`. Graph lemma:
  `y = B₁.eval ρ * B₂.eval ρ`.

- [ ] **Step 3: `app pow2 B₁`** (`2^{B₁}`) — Lemma 2 Case 1. Witnesses:
  `B₁`'s, `y₁`. Add `sqDist [⟨2^{y₁}⟩] [⟨y⟩]`; `2^{y₁}` is a monomial
  (`expBase 2`, `expCoeff 1` at the `y₁` slot). Bound `y₁ < eraMajorant
  B₁`. Graph lemma `↔ y = 2 ^ (B₁.eval ρ)`.

- [ ] **Step 4: build, axiom-check, commit** (`feat(era): encode the add,
mul, and base-2 power cases`).

### Task 4.7: the `mod` and `tsub` cases

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: `app mod (B₁,B₂)`** — Lemma 2 Case 3, as a single `prod`
  atom. Witnesses: `B₁`'s, `y₁`, `B₂`'s, `y₂`, `y₃`, `q`. Each of the
  source's signed brackets becomes a `sqDist` (symmetric squared
  distance), and the two brackets are combined with `prod`:
  - bracket A = `[sqDist [⟨y₁⟩] [⟨q·y₂⟩, ⟨y⟩], sqDist [⟨y₂⟩] [⟨y₃⟩, ⟨y⟩,
    ⟨1⟩]]` (encoding `y₁ = q·y₂ + y` and `y₂ = y₃ + y + 1`, the "`B₂ ≠ 0`,
    `y` is the remainder" branch);
  - bracket B = `[sqDist [⟨y₂⟩] [], sqDist [⟨y₃⟩] [], sqDist [⟨y⟩] [⟨y₁⟩],
    sqDist [⟨q⟩] []]` (encoding `y₂ = 0 ∧ y₃ = 0 ∧ y = y₁ ∧ q = 0`, the
    "`B₂ = 0`, `y = y₁`" branch).

  System: `[prod bracketA bracketB] ++` weakened `sys(B₁)` `++` weakened
  `sys(B₂)`. Bounds: `y₁, q < eraMajorant B₁`; `y₂, y₃ < eraMajorant B₂`.
  Graph lemma `↔ y = B₁.eval ρ % B₂.eval ρ` (the `% 0 = self` branch is
  bracket B; matches `Nat.mod`). Task 4.0 Step 2 is the authority for the
  exact bracket contents.

- [ ] **Step 2: `app tsub (B₁,B₂)`** (`B₁ ∸ B₂ = y`) — a non-disjunctive
  gadget (no `prod`), to keep the witness unique. Introduce one witness
  `s` (the opposite monus `y₂ ∸ y₁`) and assert `y + y₂ = y₁ + s` and
  `y · s = 0`: `[sqDist [⟨y⟩, ⟨y₂⟩] [⟨y₁⟩, ⟨s⟩], sqDist [⟨y·s⟩] []]` plus
  the two sub-systems. This pins `(y, s)` uniquely for every `(y₁, y₂)`
  (case `y₁ ≥ y₂`: `s = 0`, `y = y₁ − y₂`; case `y₁ < y₂`: `y = 0`,
  `s = y₂ − y₁`; both forced by the two equations), so — unlike a
  disjunction with a branch-local witness — no witness is left free.
  Witnesses: `B₁`'s, `y₁`, `B₂`'s, `y₂`, `s`. Bounds via `eraMajorant`
  (`s ≤ y₂ < eraMajorant B₂`). Graph lemma `↔ y = B₁.eval ρ - B₂.eval ρ`
  (`ℕ` monus). Numeric-check alongside the `mod` probe in Task 4.0,
  including a uniqueness scan over `s`.

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): encode the mod
and truncated-subtraction cases`).

### Task 4.8: the `div` case

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: `app div (B₁,B₂)`** (`⌊B₁/B₂⌋ = y`) — the
  division-with-remainder `prod` gadget, parallel to `mod`. Branch A
  (`B₂ ≠ 0`): `[sqDist [⟨y·y₂⟩, ⟨r⟩] [⟨y₁⟩], sqDist [⟨y₂⟩] [⟨r⟩, ⟨y₃⟩,
  ⟨1⟩]]` (`y₁ = y·y₂ + r` and `y₂ = r + y₃ + 1`, i.e. `r < y₂`). Branch B
  (`B₂ = 0`): `[sqDist [⟨y₂⟩] [], sqDist [⟨y⟩] [], sqDist [⟨r⟩] [],
  sqDist [⟨y₃⟩] []]` (`y₂ = 0 ∧ y = 0 ∧ r = 0 ∧ y₃ = 0` — branch B must
  pin `r` and `y₃` too, or they are free witnesses when `B₂ = 0` and
  uniqueness fails). System `[prod branchA branchB] ++` the two
  sub-systems. `y·y₂` is a simple degree-2 monomial. Witnesses: `B₁`'s,
  `y₁`, `B₂`'s, `y₂`, `r`, `y₃`. Bounds: `y ≤ y₁ < eraMajorant B₁`;
  `r, y₃ < eraMajorant B₂`. Graph lemma `↔ y = B₁.eval ρ / B₂.eval ρ`
  (`/ 0 = 0` matches `Nat.div`). Numeric-check alongside Task 4.0,
  including a uniqueness scan over `r, y₃`.

- [ ] **Step 2: build, axiom-check, commit** (`feat(era): encode the
division case`).

### Task 4.9: the `pow` case via Identity (4)

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: `app pow (B₁,B₂)`** (`B₁^{B₂} = y`). Do not write a new
  exponential gadget. Build the composite `ETm` witness
  `c := (epow2 ((B₁ *ᵉ B₂ +ᵉ B₁ +ᵉ one) *ᵉ B₂)) %ᵉ (epow2 (B₁ *ᵉ B₂ +ᵉ B₁
  +ᵉ one) ∸ᵉ B₁)` (smart constructors), whose `eval` equals `B₁^{B₂}.eval
  ρ` by `pow_eq_two_pow_mod` (Task 4.3) and the `_eval` lemmas. Then the
  `pow` case routes through the composite: `diophOf (app pow ts) :=
  diophOf c`, and the graph lemma chains `c`'s graph lemma with
  `pow_eq_two_pow_mod`. Confirm the existing `eraMajorant` `pow` case
  (`succ (… ^ᵉ …)`) still dominates the composite (it dominates `B₁^{B₂}`,
  hence `y`; the internal `2^{…} mod …` witnesses are bounded by `c`'s
  `pow2`/`mod` sub-majorants).

- [ ] **Step 2: build, axiom-check, commit** (`feat(era): encode the
general power case via the exponent identity`).

### Task 4.10: assemble `diophOf` and prove the invariants

**Files:**

- Modify: `GebLean/Utilities/EraDiophantine.lean`

- [ ] **Step 1: finalise `diophOf : ETm n → DiophEnc n`** by the
  structural recursion whose per-case data is Tasks 4.5–4.9 (remove the
  stubs).

- [ ] **Step 2: correctness + existence.**

```lean
/-- Some witness tuple satisfies the system exactly when the term's value
is `y`. -/
theorem diophOf_graph_iff {n : ℕ} (t : ETm n) (ρ : Fin n → ℕ) (y : ℕ) :
    (∃ w, SosSystem.eval (diophOf t).sys ((diophOf t).ctx ρ y w) = 0) ↔
      Tm.eval eraInterp t ρ = y := by
  sorry
```

Strategy: induction on `t` reusing each case's graph lemma; assemble the
witness tuple from the sub-encodings' witnesses plus the local ones.
`SosSystem.eval_eq_zero_iff` reduces each system to its atoms.

- [ ] **Step 3: uniqueness.**

```lean
/-- When the graph holds, the satisfying witness tuple is unique. -/
theorem diophOf_unique {n : ℕ} (t : ETm n) (ρ : Fin n → ℕ) (y : ℕ)
    (hy : Tm.eval eraInterp t ρ = y) :
    ∃! w, SosSystem.eval (diophOf t).sys ((diophOf t).ctx ρ y w) = 0 := by
  sorry
```

Strategy: induction on `t`; each witness is determined (`yᵢ = Bᵢ.eval ρ`
by the sub-IH; `q`, `r`, `y₃` by the `mod`/`div`/`tsub` brackets). Budget
`lean4:sorry-filler-deep`; the heaviest single proof in Phase 4.

- [ ] **Step 4: witness bounds.**

```lean
/-- Every satisfying witness respects its bound term. -/
theorem diophOf_bound {n : ℕ} (t : ETm n) (ρ : Fin n → ℕ) (y : ℕ)
    (w : Fin (diophOf t).witArity → ℕ)
    (hw : SosSystem.eval (diophOf t).sys ((diophOf t).ctx ρ y w) = 0) :
    ∀ i, w i < Tm.eval eraInterp ((diophOf t).bound i) (Fin.snoc ρ y) := by
  sorry
```

Strategy: induction on `t`; each `yᵢ = Bᵢ.eval ρ < eval (eraMajorant Bᵢ)`
by `eraMajorant_spec`; the local `q`/`r`/`y₃` are below the relevant
first-argument majorant.

- [ ] **Step 5: build, axiom-check, commit** (`feat(era): assemble the
reduction with its invariants`). This closes Phase 4.

---

## Phase 5 — `EraHypercube.lean`: the counting engine and the read-off

All `ℕ`-level; the `Era`-term realisations of `M`, `HW`, and the count are
assembled in Phase 6 (`EraCompleteness.lean`) using the Phase-3 terms
(`eraSigma`, `eraDelta`) and the Phase-1 `G`-terms (`eraGeomSum`). Phase 5
proves the counting identity over `ℕ` against Mathlib reference functions
so Phase 6 only mirrors it term-wise.

Module imports (verified available in the pin):
`GebLean.Utilities.EraBoundedSum`, `GebLean.Utilities.ArithClosedForms`,
`GebLean.Utilities.EraDiophantine`, `Mathlib.Data.Nat.Digits.Defs`,
`Mathlib.Data.Nat.Digits.Lemmas`, `Mathlib.Data.Fintype.BigOperators`
(for `Fintype.piFinset`/`Finset.prod_univ_sum`). Add `EraHypercube` to
`GebLean/Utilities.lean` after the `EraDiophantine` entry.

### Task 5.1: the mixed-radix enumeration (computable)

**Files:**

- Create: `GebLean/Utilities/EraHypercube.lean` (module docstring +
  imports above).

- [ ] **Step 1: define `cubePoints` and the index `v` as computable
  functions.** Do **not** build an `Equiv` via `Fintype.equivFinOfCardEq`
  (it is `noncomputable`; project ban). Keep `v` a plain function and
  carry bijectivity as `Prop`s.

```lean
/-- The side-`t` cube `{0,…,t−1}^k` as a `Finset` of total functions. -/
def cubePoints (k t : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range t)

/-- The base-`t` mixed-radix index `v(ā) = Σᵢ aᵢ · tⁱ` (0-indexed:
`a₀ + a₁ t + ⋯ + a_{k−1} t^{k−1}`, matching the paper's 1-indexed
`a₁ + a₂ t + ⋯` under the index shift). -/
def mixedRadix (k t : ℕ) (a : Fin k → ℕ) : ℕ :=
  ∑ i, a i * t ^ (i : ℕ)
```

- [ ] **Step 2: prove `mixedRadix` enumerates the cube.** State injectivity
  on `cubePoints` and the range bound `mixedRadix k t a < t ^ k` for
  `a ∈ cubePoints k t`, plus surjectivity onto `Finset.range (t ^ k)`.
  Strategy: base-`t` digit uniqueness; search `Nat.lt_base_pow_iff_digits`,
  `Finset.sum_range`, or build from `Nat.ofDigits`. Injectivity by digit
  recovery; the count `(cubePoints k t).card = t ^ k`
  (`Fintype.card_piFinset` / `Finset.card`) gives surjectivity.

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): define the
mixed-radix cube enumeration`).

### Task 5.2: the cube-sum factorisation through `G₀`/`G₁`/`G₂`

**Files:**

- Modify: `GebLean/Utilities/EraHypercube.lean`

- [ ] **Step 1: state and prove Lemma 3.2 over `ℕ`** as pure
  distributivity (no `1 < vbase i` hypothesis is needed for the
  factorisation itself; it is needed only when connecting each factor to a
  `Gᵣ` closed form, which has a `(q − 1)` denominator).

```lean
/-- Cube-sum factorisation (arXiv:2407.12928, Lemma 3.2): a product of
per-coordinate weighted geometric sums over the cube factors into a
product of single-variable sums. -/
theorem cubeSum_factor (k : ℕ) (u : Fin k → ℕ) (vbase : Fin k → ℕ)
    (t : ℕ) :
    (∑ a ∈ cubePoints k t,
        ∏ i, (a i) ^ (u i) * (vbase i) ^ (a i))
      = ∏ i, (∑ j ∈ Finset.range t, j ^ (u i) * (vbase i) ^ j) := by
  sorry
```

Strategy: `Finset.prod_univ_sum` over `Fintype.piFinset` (so `cubePoints`
matches the driver's index set directly; requires `DecidableEq (Fin k)`
and `CommSemiring ℕ`, both automatic). Then connect each single-variable
sum to the closed forms, only for `u i ∈ {0, 1, 2}` (Corollary 3.6: the
degree-≤2 auxiliary reduction keeps cube-variable polynomial exponents at
most `2`), via `natGeomSum_eq` (`G₀`), `natLinGeomSum_eq` (`G₁`),
`natSqGeomSum_mul` (`G₂`); these need `vbase i > 1` (true at the use,
`vbase i = 2 ^ (2w) > 1`).

- [ ] **Step 2: build, axiom-check, commit** (`feat(era): prove the
cube-sum factorisation`).

### Task 5.3: `HW`-additivity over disjoint blocks

**Files:**

- Modify: `GebLean/Utilities/EraHypercube.lean`

- [ ] **Step 1: secure the no-carry digit-sum lemma.** The needed fact is
  `(Nat.digits 2 (x + 2 ^ w * y)).sum = (Nat.digits 2 x).sum +
  (Nat.digits 2 y).sum` for `x < 2 ^ w`. This already exists in
  `ArithClosedForms.lean` as `sum_digits_two_add` (line 235) but is
  `private`. Decide and record: either (a) de-`private` it on a separate
  one-concern branch (per the one-concern rule) and import it, or (b)
  re-prove it locally here. Default: (a), since the gcd sub-plan already
  proved it; this plan's Task 5.3 then only assembles the block iteration.

- [ ] **Step 2: state and prove block additivity.**

```lean
/-- Hamming-weight additivity over non-overlapping base-`2^(2w)` blocks:
if `g i < 2 ^ (2 * w)` for every `i < N`, the binary digit sum of the
packed number is the sum of the per-block digit sums. -/
theorem hw_pack_additive (w N : ℕ) (g : ℕ → ℕ)
    (hg : ∀ i, i < N → g i < 2 ^ (2 * w)) :
    (Nat.digits 2 (∑ i ∈ Finset.range N, 2 ^ (2 * w * i) * g i)).sum
      = ∑ i ∈ Finset.range N, (Nat.digits 2 (g i)).sum := by
  sorry
```

Strategy: induction on `N`; split the top block at position
`2 ^ (2 * w * N)` over a low part `< 2 ^ (2 * w * N)` and apply the Step-1
no-carry lemma (generalised from base `2 ^ w` to `2 ^ (2 * w * N)`).
Useful Mathlib names (verified): `Nat.ofDigits_append`,
`Nat.digits_base_pow_mul` (`1 < b → 0 < m → b.digits (b ^ k * m) =
List.replicate k 0 ++ b.digits m`), `Nat.digits_add_two_add_one`. Do not
cite `Nat.digits_append` or `Nat.sum_digits_eq_sum_digits_add_sum_digits`
(neither exists). Budget `lean4:sorry-filler-deep`.

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): prove
Hamming-weight additivity over disjoint blocks`).

### Task 5.4: the packed number `M` and the count read-off

**Files:**

- Modify: `GebLean/Utilities/EraHypercube.lean`

- [ ] **Step 1: define `packM` and the `δ`-block range lemma.**

```lean
/-- The packed number (arXiv:2407.12928, Lemma 3.3): `δ(P ā, w)` placed at
base-`2^(2w)` position `v(ā)` over the cube. -/
def packM (k w t : ℕ) (P : (Fin k → ℕ) → ℕ) : ℕ :=
  ∑ a ∈ cubePoints k t, 2 ^ (2 * w * mixedRadix k t a) * deltaBlock (P a) w
```

State the range lemma `deltaBlock a w < 2 ^ (2 * w)` for `a < 2 ^ w` (so
`hw_pack_additive` applies); prove from `deltaBlock`'s definition.

- [ ] **Step 2: state and prove the count identity.** With width `w`, side
  `t`, and `P` valued in `{0,…,2^w − 1}` on the cube:

```lean
/-- The count read-off (arXiv:2407.12928, Lemma 3.3 / Theorem 3.4):
`HW(M)/w − tᵏ` equals the number of cube points where `P` vanishes. -/
theorem count_zeros_eq (k w t : ℕ) (ht : 1 < t) (hw : 0 < w)
    (P : (Fin k → ℕ) → ℕ)
    (hP : ∀ a ∈ cubePoints k t, P a < 2 ^ w) :
    (Nat.digits 2 (packM k w t P)).sum / w - t ^ k
      = ((cubePoints k t).filter (fun a => P a = 0)).card := by
  sorry
```

Strategy: `hw_pack_additive` (Task 5.3, re-indexing the cube sum by the
`mixedRadix` bijection of Task 5.1 onto `Finset.range (t ^ k)`; the side
lemma gives `deltaBlock (P a) w < 2 ^ (2 * w)`), then
`hwClosed_deltaBlock`/`hwClosed_eq` (`ArithClosedForms.lean`:
`HW(δ(a,w)) = 2w` if `a = 0` else `w`) makes the digit sum
`d · 2w + (tᵏ − d) · w = (d + tᵏ) · w` where `d` is the zero-count; then
`HW(M)/w − tᵏ = d` via `Nat.add_mul_div_left` and `Nat.add_sub_cancel`.
`DecidablePred (fun a => P a = 0)` resolves automatically (`ℕ` `decEq`).

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): prove the
hypercube count read-off`).

### Task 5.5: positional coding and the recurrence read-off

**Files:**

- Modify: `GebLean/Utilities/EraHypercube.lean`

- [ ] **Step 1: the positional read-off `⌊H/Aⁿ⌋`.** State and prove the
  top-digit extraction (arXiv:2606.09336, Lemma 3 / Theorem 2 read-off).

```lean
/-- Positional read-off (arXiv:2606.09336, Theorem 2): the top base-`A`
digit of a bounded positional code is recovered by floor division. -/
theorem positional_readoff (A n : ℕ) (a : ℕ → ℕ) (hA : 0 < A)
    (ha : ∀ k, k ≤ n → a k < A) :
    (∑ k ∈ Finset.range (n + 1), a k * A ^ k) / A ^ n = a n := by
  sorry
```

Strategy: `Finset.sum_range_succ` splits off `k = n`; the low part
`Σ_{k<n} aₖ·Aᵏ < Aⁿ` (geometric bound from `aₖ < A`), so
`Nat.add_mul_div_left` + `Nat.div_eq_of_lt` give `aₙ`. (`hA : 0 < A` is
the right hypothesis, including the `A = 1` edge.)

- [ ] **Step 2: define `recSeq`/`histCode` and prove the recurrence
  read-off.** Provide the sequence and its positional-code history, then
  the read-off; these are the objects Phase 6 reads off.

```lean
/-- A first-order recurrence sequence `s(0) = init`,
`s(m+1) = step m (s m)`. -/
def recSeq (init : ℕ) (step : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => init
  | m + 1 => step m (recSeq init step m)

/-- The base-`A` positional code of the value history `s(0),…,s(n)`. The
`Era`-term realisation (via `count_zeros_eq` applied to the step's
`diophOf` encoding) is Phase 6; here `histCode` is the `ℕ`-level code. -/
def histCode (init : ℕ) (step : ℕ → ℕ → ℕ) (A : ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), recSeq init step k * A ^ k

/-- First-order recurrence read-off (arXiv:2606.09336, Theorem 2,
specialised to `k = 1`): the `ℕ`-level value of a recurrence whose history
is `A`-bounded equals `⌊H/Aⁿ⌋`. The `Era`-term realisation is Phase 6. -/
theorem recurrence_readoff (init : ℕ) (step : ℕ → ℕ → ℕ) (A : ℕ)
    (n : ℕ) (hbound : ∀ j ≤ n, recSeq init step j < A) :
    recSeq init step n = histCode init step A n / A ^ n := by
  sorry
```

Strategy: direct from `positional_readoff` with `a k := recSeq init step
k`. The single base `A` (rather than the paper's per-index `A(j)`) is the
hypothesis `positional_readoff` needs; Phase 6 supplies `A := eval
(eraMajorant …)` at the loop bound and discharges `recSeq j < A` for all
`j ≤ n` via `eraMajorant_spec` + `eraMajorant_mono` (monotone, so the
single top value dominates every earlier one). No `⌊log₂⌋` dependency
(de-cycling). The `Era`-term construction of `histCode` — packing the
step's `diophOf` encoding (Phase 4) by `count_zeros_eq` (Task 5.4) — is
deferred to Phase 6; this `ℕ`-level `histCode` is the specification it
must meet.

- [ ] **Step 3: build, axiom-check, commit** (`feat(era): prove the
first-order recurrence read-off`). This closes Phase 5.

---

## Handoff to Phase 6 (interface confirmation, not re-specified here)

Phases 6 and 7 remain as the M3b plan specifies (Tasks 6.1, 6.2, 7.1,
7.2). This sub-plan delivers exactly what they consume:

- `eraBSum` (M3b Task 6.1) builds its term either from `recurrence_readoff`
  (Task 5.5) with `step m s = s + f m` and `A` the summand's `eraMajorant`,
  or from the direct 2-D count `Σ_{i<y} f i = #{(i,w) : i<y, w<f i}` via
  `count_zeros_eq` (Task 5.4); M3b Task 6.1 chooses the route. Either
  realises `M`/`HW`/`G` as the Phase-3/Phase-1 terms (`eraSigma`,
  `eraDelta`, `eraGeomSum`). Its deliverable `eraBSum_eval` targets
  `natBSum (ctx 0) (fun i => Tm.eval eraInterp t (Fin.cons i (Fin.tail
  ctx)))`, matching `ERMor1.interp_bsum` verbatim.
- `eraBProd` (M3b Task 6.2) uses `recurrence_readoff` with `step m s = s *
  f m` and the product majorant; `eraBProd_eval` targets `natBProd …`.
- `era_complete` and the K-sim-2 corollary (M3b Tasks 7.1, 7.2) consume
  the two `eval` lemmas unchanged.

## Self-review checklist (run before adversarial review)

- [ ] **Re-checkpoint coverage.** M3b Phase 4 Sub-lemmas 4.1–4.7 →
  Tasks 4.0 (numeric pre-validation), 4.1 (atom algebra), 4.2 (`DiophEnc`),
  4.3 (Identity (4)), 4.4 (re-indexing helpers), 4.5–4.9 (cases),
  4.10 (invariants). M3b Phase 5 Sub-lemmas 5.1–5.5 → Tasks 5.1
  (enumeration), 5.2 (cube-sum), 5.3 (`HW`-additivity), 5.4 (count
  read-off), 5.5 (positional + recurrence).
- [ ] **Soundness over `ℕ`.** Every graph gadget uses the symmetric
  squared-distance (`sqDist`) and product (`prod`) atoms, never a lone
  truncated bracket; Task 4.0 Step 2 numerically validates the `mod`/
  `tsub`/`div` gadgets for absence of spurious zeros.
- [ ] **Witness uniqueness in disjunctive gadgets.** In every `prod`
  two-branch gadget, each witness is constrained in *both* branches (else
  it is free when the other branch holds and `diophOf_unique` fails): `mod`
  and `div` branch B pin `q`/`y₃`/`r`; `tsub` avoids the hazard with a
  non-disjunctive encoding. Task 4.0 scans witness uniqueness.
- [ ] **Imports/computability.** `Mathlib.Data.Fin.Tuple.Basic` added to
  `EraDiophantine.lean`; the Phase-5 imports listed; `mixedRadix` is a
  plain computable function (no `Fintype.equivFinOfCardEq`); no
  `noncomputable`.
- [ ] **Lemma-name hygiene.** `Nat.ofDigits_append` (not
  `Nat.digits_append`); `Nat.add_eq_zero_iff` (not deprecated
  `Nat.add_eq_zero`); `List.sum_eq_zero_iff`; `Nat.pow_eq_zero` side
  condition discharged. `sum_digits_two_add` de-`private` decision recorded
  (Task 5.3 Step 1).
- [ ] **Carrier and induction decisions** stated with rationale and a
  fallback (§ "Phase 4 architecture") for the reviews to adjudicate.
- [ ] **De-cycling.** No `eraIlog2`/fast-`ν₂`/`⌊log₂⌋` term anywhere; `HW`
  is `eraSigma` (slow `ν₂`). Tasks 5.4, 5.5 state the no-`log` dependency.
- [ ] **Type consistency.** `diophOf : ETm n → DiophEnc n`; system arity
  `n + 1 + witArity`; bound terms `Fin witArity → ETm (n + 1)`; all
  `eval`s over `eraInterp`. The Phase-6 `eval`-lemma RHS shape matches
  `ERMor1.interp_bsum`/`interp_bprod` verbatim.
- [ ] **Commit subjects** under 72 characters, imperative, lowercase, no
  trailing period.
- [ ] **Markdownlint + doctoc.** `markdownlint-cli2` clean; doctoc TOC
  refreshed before the first commit.
