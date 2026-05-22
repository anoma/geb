# T4 — Runtime bound and `erToK` assembly (design spec)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [§1 Status and motivation](#1-status-and-motivation)
  - [§1.1 Position in the ER to Ksim2 equivalence](#11-position-in-the-er-to-ksim2-equivalence)
  - [§1.2 Goal](#12-goal)
  - [§1.3 Source-faithfulness contract](#13-source-faithfulness-contract)
- [§2 Tourlakis source structure](#2-tourlakis-source-structure)
  - [§2.1 Lemma 0.1.0.42 — per-constructor URM runtime](#21-lemma-01042--per-constructor-urm-runtime)
  - [§2.2 Lemma 0.1.0.27 — A-iterate majorant of E-class](#22-lemma-01027--a-iterate-majorant-of-e-class)
  - [§2.3 Lemma 0.1.0.37 — Ksim2 simulator v1](#23-lemma-01037--ksim2-simulator-v1)
  - [§2.4 Corollary 0.1.0.44 superset direction at n=2](#24-corollary-01044-superset-direction-at-n2)
- [§3 T4 decomposition](#3-t4-decomposition)
- [§4 Piece 1 — `boundExprKParams` recipe and Nat-level bound](#4-piece-1--boundexprkparams-recipe-and-nat-level-bound)
  - [§4.1 Signature](#41-signature)
  - [§4.2 Per-constructor recipe table](#42-per-constructor-recipe-table)
  - [§4.3 Joint runtime+value bound theorem](#43-joint-runtimevalue-bound-theorem)
- [§5 Piece 2 — Ksim composites](#5-piece-2--ksim-composites)
  - [§5.1 `KMor1.maxK`](#51-kmor1maxk)
  - [§5.2 `KMor1.maxOver`](#52-kmor1maxover)
  - [§5.3 `KMor1.pow2_iter`](#53-kmor1pow2_iter)
  - [§5.4 Level lemmas](#54-level-lemmas)
- [§6 Piece 3 — `boundExprK` assembly](#6-piece-3--boundexprk-assembly)
  - [§6.1 Shape](#61-shape)
  - [§6.2 Alternatives considered and rejected](#62-alternatives-considered-and-rejected)
  - [§6.3 Level, interp, and domination theorems](#63-level-interp-and-domination-theorems)
- [§7 Piece 4 — `erToK` assembly](#7-piece-4--ertok-assembly)
  - [§7.1 Definition](#71-definition)
  - [§7.2 Level theorem](#72-level-theorem)
  - [§7.3 Interpretation theorem](#73-interpretation-theorem)
- [§8 Piece 5 — `erToKFunctor`](#8-piece-5--ertokfunctor)
  - [§8.1 Multi-output extension `erToKN`](#81-multi-output-extension-ertokn)
  - [§8.2 Morphism component `erToKFunctor_map`](#82-morphism-component-ertokfunctor_map)
  - [§8.3 Functor laws](#83-functor-laws)
  - [§8.4 Functor assembly](#84-functor-assembly)
- [§9 File organisation](#9-file-organisation)
- [§10 Dependency DAG](#10-dependency-dag)
- [§11 Axiom budget](#11-axiom-budget)
- [§12 Test plan](#12-test-plan)
- [§13 Scope guardrails](#13-scope-guardrails)
- [§14 Size estimate](#14-size-estimate)
- [§15 References](#15-references)

<!-- END doctoc -->

## §1 Status and motivation

### §1.1 Position in the ER to Ksim2 equivalence

This spec governs T4 (Step 10) of the ER ↔ K^sim_2 categorical-
equivalence project. The forward direction `kToER` is complete
(Steps 0–5). The reverse direction `erToK` is split across
T1 (URM kernel, complete), T2 (ER → URM compiler, complete),
T3 (K^sim simulator for URM, complete via PR #22 merge
commit `db059ef4`), T4 (this spec), and T5 (strict categorical
iso, future).

| Workstream | Status | Surface produced |
| --- | --- | --- |
| T1 (Step 7) | Complete | `URMProgram`, `URMState.runFor` in `ZeroTestURM.lean` |
| T2 (Steps 6+8) | Complete | `compileER`, `compileER_runtime`, `compileER_runFor` |
| T3 (Step 9) | Complete | `simulate`, `simulate_interp`, `simulate_level ≤ 2` |
| T4 (Step 10) | This spec | `boundExprK`, `erToK`, `erToK_interp`, `erToK_level`, `erToKFunctor` |
| T5 (Step 11) | Future | Strict iso `LawvereERCat ≌ LawvereKSimDCat 2` |

### §1.2 Goal

Construct `erToK : ERMor1 a → KMor1 a` of level ≤ 2 satisfying
`(erToK e).interp v = e.interp v` for all `v : Fin a → ℕ`, and
package the result as the functor
`erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2`.

The construction composes T3's URM simulator `simulate`
(level ≤ 2) with a K^sim runtime bound `boundExprK e`
(level ≤ 2) supplied as the simulator's step-count argument,
plus input projections.

### §1.3 Source-faithfulness contract

The mathematical content of T4 is the `⊇` direction of
Tourlakis 2018 Corollary 0.1.0.44 specialised to `n = 2`:
`E^3 ⊆ K^sim_2`. T4 transcribes Tourlakis's proof of this
direction (`PR-complexity-topics.pdf` pp. 18–22).

The K^sim and ER object surfaces are non-negotiable (per
[`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md)
§ Non-negotiable interfaces). Implementation-side choices
(precise Nat constants in the recipe, choice of tactic, etc.)
may flex provided the source-faithfulness contract is
preserved.

## §2 Tourlakis source structure

### §2.1 Lemma 0.1.0.42 — per-constructor URM runtime

For `n ≥ 2`, every `f ∈ E^n` is URM-computable within time
`t_f ∈ E^n`. Proof by induction over E^n:

- Initial functions: `λx.x` and `λx.x+1` have URM
  implementations with `O(x)` time; `λxy.xy` has a URM
  implementation with `O(xy)` time via a Loop program; `A_n`
  has a URM running in `O((A_n^k(x))^2) = O(A_n^{k+1}(x))`
  time.
- Substitution preserves the E^n-runtime property: runtimes
  add as `t_g(y⃗) + t_f(x⃗, g(y⃗))`.
- Bounded recursion preserves the property via the explicit
  URM pseudo-code on `PR-complexity-topics.pdf` p. 21 with
  runtime `t_h(y⃗) + O(Σ_{i<x} t_g(i, y⃗, f(i, y⃗)))`.

For the T4 transcription, the per-constructor URM runtime is
already realised concretely by T2 as
`compileER_runtime : {a : ℕ} → ERMor1 a → (Fin a → ℕ) → ℕ`
in `GebLean/LawvereERKSim/Compiler.lean` (lines 1722–1770).
T4 does not need an existence theorem; it needs an explicit
majorant in `K^sim_2` form.

### §2.2 Lemma 0.1.0.27 — A-iterate majorant of E-class

Every `t : E^n` satisfies `t(x⃗) ≤ A_n^r(max x⃗)` for some
`r ∈ ℕ`. For `n = 2`, `A_2 = λx. 2^x` (approximately) and
`A_2^r` is the `r`-fold composition; the closed-form Nat
function `tower r x` already lives in
`GebLean/Utilities/ERAMajorants.lean` as the interp of
`ERMor1.A_two_iter`, with closed-form
`(ERMor1.A_two_iter r).interp ![x] = tower r x`.

### §2.3 Lemma 0.1.0.37 — Ksim2 simulator v1

The simulating function `v_1` for a URM's output variable
runs in `K^sim_2`. For T4, this is exactly T3's landed
`simulate : URMProgram a → KMor1 (a + 1)` with
`simulate_level ≤ 2` and `simulate_interp`. Slot 0 of the
arity-`(a+1)` input carries the step-count `y`.

### §2.4 Corollary 0.1.0.44 superset direction at n=2

For `f ∈ E^3`, write `f(x⃗) = v_1(t_f(x⃗), x⃗)`. Choose
`r` so that `t_f(x⃗) ≤ A_2^r(max x⃗)` (by §2.2). Then
`f(x⃗) ≤ v_1(A_2^r(max x⃗), x⃗)`. Since `v_1 ∈ K^sim_2`
(§2.3) and `A_2^r ∈ K^sim_2` (Tourlakis 0.1.0.9), and
`max x⃗` is in K^sim_2 (constructible from primitives),
`f ∈ K^sim_2`.

T4's transcription replaces `t_f` with our concrete
`compileER_runtime e v` (a Lean-Nat function), realises
`A_2^r ∘ max + offset` as a K^sim composite, and composes
with `simulate (compileER e)`.

## §3 T4 decomposition

T4 delivers five pieces:

1. **`boundExprKParams : ERMor1 a → ℕ × ℕ`** — a recursive
   recipe returning `(mu_e, offset_e)` per ER constructor —
   together with a joint Nat-level bound theorem
   bounding both `compileER_runtime e v` (runtime) and
   `e.interp v` (value) by the same
   `tower mu_e (Fin.maxOfNat _ v + offset_e)`. Bounding both
   quantities with the same tower height is the operational
   shortcut that absorbs comp's runtime-of-`f`-at-value-of-`gs`
   recursion (Tourlakis 0.1.0.42's substitution case requires
   the value of `gs` to feed `f`'s runtime account). This is §4.

2. **K^sim composites** `KMor1.maxK`, `KMor1.maxOver`,
   `KMor1.pow2_iter` in `KArith.lean`, with `@[simp]`
   closed-form interp lemmas and level-≤ 2 bounds. This is
   §5.

3. **`boundExprK : ERMor1 a → KMor1 a`** assembled from
   `pow2_iter`, `maxOver`, `natK'`, and `add`; with
   `boundExprK_level ≤ 2`, `boundExprK_interp`,
   `boundExprK_dominates`. This is §6.

4. **`erToK : ERMor1 a → KMor1 a`** composing
   `simulate (compileER e)` with
   `Fin.cons (boundExprK e) projections`; with
   `erToK_level ≤ 2` and `erToK_interp`. This is §7.

5. **Multi-output extension and functor**: `erToKN :
   ERMorN n m → KMorN n m` (componentwise application of
   `erToK`); `erToKFunctor : LawvereERCat ⥤
   LawvereKSimDCat 2` lifting through the ER quotient via
   `Quotient.liftOn` and packaging with the depth-2
   witness on the K side. Mirrors the existing
   `kToERFunctor` at `GebLean/LawvereKSimER.lean:474`. This
   is §8.

Bypassed (relative to a strictly Tourlakis-faithful
transcription): an explicit ER-side runtime function
`compileER_runtimeER : ERMor1 a → ERMor1 a` lifting
`compileER_runtime` to an ER term. T4 bounds at the Nat
level directly via `tower`; the ER-side composite
`ERMor1.A_two_iter` is reused for its closed-form
interp (`tower r x`) and not for ER-level induction.

## §4 Piece 1 — `boundExprKParams` recipe and Nat-level bound

### §4.1 Signature

```lean
def boundExprKParams : {a : ℕ} → ERMor1 a → ℕ × ℕ
```

A constructive Lean `def` (not a `theorem`) returning a
concrete `(mu_e, offset_e) : ℕ × ℕ` pair. Mathlib naming
convention: `lowerCamelCase` for `def`s. The pair shape
mirrors the kToER-side `KMor1.majorize : KMor1 a → f.level
≤ 2 → ℕ × ℕ` in `LawvereKSimMajorization.lean` (lines 622+),
differing in three ways: (1) the direction of induction
(`ERMor1` instead of `KMor1`); (2) the absence of a level
hypothesis (every `ERMor1` already has its
`compileER_runtime` defined); (3) the same `mu_e` bounds
both the URM-runtime and the ER-value of `e` simultaneously
(unifying §0.1.0.42 and §0.1.0.27 into a single recursive
account).

### §4.2 Per-constructor recipe table

The increments below are driven by the closed form of
`compileER_runtime` at
`GebLean/LawvereERKSim/Compiler.lean` lines 1722–1770 and by
the Nat-level Tower lemmas available in
`GebLean/Utilities/Tower.lean` (notably
`mul_tower_le_tower_add_two` at line 101 and `tower_comp`
for nested-tower absorption).

`mu_e` is the unified tower height bounding both runtime
(`compileER_runtime e v`) and value (`e.interp v`) by
`tower mu_e (Fin.maxOfNat _ v + offset_e)`.

| Constructor | `compileER_runtime` shape | Value shape | `mu_e` | `offset_e` |
| --- | --- | --- | --- | --- |
| `zero` | `3` | `0` | `0` | `3` |
| `succ` | `12 + 10·v 0` | `v 0 + 1` | `2` | `≤ 16` |
| `proj i` | `11 + 10·v i` | `v i` | `2` | `≤ 16` |
| `sub` | `20 + 10·v 0 + 10·v 1` | `v 0 ∸ v 1` | `2` | `≤ 24` |
| `comp f gs` | `Σ_i (rt(gs i) + 4 + 5·val(gs i) + 9·v_total + 2·a) + rt(f at gs_interp) + 2` | `f.interp (gs.interp v)` | `mu_f + Fin.maxOfNat k (fun i => mu_{gs i}) + 6` | `offset_f + Fin.maxOfNat k (fun i => offset_{gs i}) + 4·a + 8` |
| `bsum f` | `30 + 10·v 0 + Σ_{i<v 0} perIter_f(i)` | `Σ_{j<v 0} f.interp (Fin.cons j (Fin.tail v))` | `mu_f + 2` | `offset_f + 32` |
| `bprod f` | `40 + 10·v 0 + Σ_{i<v 0} (perIter_f(i) + 9·A_i·B_i + …)` | `Π_{j<v 0} f.interp (Fin.cons j (Fin.tail v))` | `mu_f + 7` | `offset_f + 44` |

Increment rationale (each tied to a specific Tower lemma):

- **Atoms** (`zero`, `succ`, `proj`, `sub`): runtime is
  linear-in-`Fin.maxOfNat _ v`; value is bounded by
  `Fin.maxOfNat _ v + 1` (or 0 for `zero`). Need `mu = 2`
  because the linear coefficient (10) must be absorbed.
  Writing `m := Fin.maxOfNat _ v + offset` with `m ≥ 10`
  (via offset ≥ 16), we have
  `10 · m ≤ m · m = m · tower 0 m ≤ tower 2 m` by a single
  application of `mul_tower_le_tower_add_two` from
  `Tower.lean:101` (the lemma adds `+ 2` to absorb a single
  multiplicative `m`-factor). `mu = 0` for `zero` because
  the runtime and value are both constants.
- **`comp f gs`**: per Tourlakis 0.1.0.42's substitution
  case (`PR-complexity-topics.pdf` p. 20), the runtime is
  `t_g + t_f(g(y⃗))`. Here `t_g`'s contribution is the
  prefix-sum `Σ_i (rt(gs i) + …)` and `t_f`'s contribution
  is `rt(f at gs_interp)`. Crucially, `t_f(g(y⃗))` requires
  a *value* bound on `g(y⃗) = (gs i).interp v`; by IH on
  `gs i`, this is bounded by
  `tower mu_{gs i} (Fin.maxOfNat _ v + offset_{gs i})`,
  which (folding over `i`) is at most
  `tower mu_g (Fin.maxOfNat _ v + offset_g)`, where
  `mu_g := Fin.maxOfNat k (fun i => mu_{gs i})` and
  `offset_g := Fin.maxOfNat k (fun i => offset_{gs i})`.
  The nested tower absorbs into a single tower of
  additive height in three discrete steps:
  (i) Inner-offset absorption: `Tower.tower_comp`
  (`Tower.lean:51`) is an equality
  `tower j (tower k x) = tower (j + k) x` with no offset
  inside, so the `+ offset_f` term inside the outer
  `tower mu_f (...)` must first be folded into a tower
  level. Writing `m := Fin.maxOfNat _ v + offset_e` and
  `X := tower mu_g m`, we have `X + offset_f ≤ X + m ≤ 2X
  ≤ m · X = m · tower 0 X ≤ tower 2 X = tower (mu_g + 2)
  m` (one `mul_tower_le_tower_add_two`).
  (ii) `tower_comp` then gives
  `tower mu_f (tower (mu_g + 2) m) = tower (mu_f + mu_g + 2) m`,
  bounding `rt(f at gs_interp)`.
  (iii) Outer glue: `glue` includes `9 · v_total` where
  `v_total = Σ_i v i ≤ a · Fin.maxOfNat _ v ≤ m · m` (for
  `offset_e ≥ a`). The constant `9` is absorbed by
  recognising `9 ≤ m` (offset_e ≥ 8 ensures `m ≥ 8`,
  bumped to ≥ 9 by including the per-subterm `4·a + 8`
  with `a ≥ 1`; for `a = 0` comp degenerates and the case
  is trivial). Then `9 · m · m ≤ m · m · m`, and
  `m · m · m ≤ m · tower 2 m ≤ tower 4 m` by two
  `mul_tower_le_tower_add_two` applications. So
  `9 · v_total ≤ tower (mu_f + mu_g + 6) m` (using
  `tower 4 m ≤ tower (mu_f + mu_g + 6) m` by
  `tower_mono_left`). The `glue + rt(f) + 2`
  sum-of-two-tower-bounded-terms (where `rt(f) ≤ tower
  (mu_f + mu_g + 2) m` from step (ii)) is dominated by
  `2 · tower (mu_f + mu_g + 6) m ≤ m · tower (mu_f + mu_g + 6) m
  ≤ tower (mu_f + mu_g + 6) m` — but the recipe's `+ 4`
  suffices because the `+ 2` slack between step (ii)'s
  `mu_f + mu_g + 2` and step (iii)'s `mu_f + mu_g + 6`
  margin handles the sum-of-pairs absorption without
  needing the additional `+ 2`. (The exact tightness
  depends on the precise discharge during implementation;
  the `+ 4` increment is the upper bound the spec
  commits to.)
  The `4·a + 8` offset accounts for the per-subterm
  overhead (`4 + 5·val + 9·v_total + 2·a`) plus glue's
  additive constants.
- **`bsum f`**: per Tourlakis 0.1.0.42's bounded-recursion
  case (`PR-complexity-topics.pdf` p. 21), the runtime is
  `t_h + O(Σ_{i<x} t_g(i, y⃗, f(i, y⃗)))`. For us, this is
  `30 + 10·v 0 + Σ_{i<v 0} perIter_f(i)`. By IH on `f`,
  `perIter_f(i) ≤ tower mu_f (Fin.maxOfNat _ v + offset_f)`
  (modulo the inner constants, which the offset absorbs).
  The outer `Σ_{i<v 0}` is a `v 0`-fold sum, bounded by
  `v 0 · tower mu_f m ≤ (Fin.maxOfNat _ v + offset) · tower
  mu_f m ≤ tower (mu_f + 2) m` via
  `mul_tower_le_tower_add_two` (with `m = Fin.maxOfNat _ v +
  offset ≥ 2`). Hence `mu = mu_f + 2`. The value bound is
  the same shape: `natBSum v_0 (f.interp ∘ …) ≤ v_0 ·
  tower mu_f m ≤ tower (mu_f + 2) m`.
- **`bprod f`**: value bound and runtime bound require
  different increments; the recipe carries the larger of
  the two (the runtime). The value
  `natBProd v_0 (f.interp ∘ …) = Π_{j<v_0} f.interp_j ≤
  (tower mu_f m)^{v_0} ≤ (tower mu_f m)^m`, and by
  `Tower.tower_pow_le_tower_add_three` (`Tower.lean:120`)
  this is `≤ tower (mu_f + 3) m`. So the value bound
  needs `+ 3`. The runtime contains
  `Σ_{i<v 0} 9·A_i·B_i` where
  `A_i · B_i ≤ natBProd (i+1) (f.interp ∘ …) ≤ tower (mu_f + 3) m`.
  Writing `T := tower (mu_f + 3) m`, the outer sum is
  `Σ_{i<v 0} 9·T ≤ 9·v_0·T ≤ 9·m·T`. The constant
  factor `9` is absorbed by recognising `9 ≤ m` (the
  spec offset 44 ensures `m ≥ 44`), giving
  `9·m·T ≤ m·m·T = m·(m·T)`. Then
  `m·T ≤ tower (mu_f + 5) m` by one
  `mul_tower_le_tower_add_two`, and
  `m·(m·T) ≤ m·tower (mu_f + 5) m ≤ tower (mu_f + 7) m`
  by a second `mul_tower_le_tower_add_two`. Total runtime
  increment: `+ 7`. The recipe carries
  `mu = mu_f + 7`, dominating both value (which only
  needs `+ 3`) and runtime. The remaining sub-terms
  `4·A_i + 9·B_i + nRegs_f` in `perIter_f(i)` are
  dominated by `A_i · B_i` (since `B_i ≥ 1` whenever
  `A_i · B_i > 0`).

The precise Nat constants in the offset column (the `16`,
`24`, `4·a + 8`, `32`, `44`) are derived but
implementation-flexible per
[`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md)
§ Non-negotiable interfaces (Lean-side flexibility around
the literature contract). The literature-fixed content is
the increment table for `mu_e` (the tower height) — `+ 2`
at atoms, `+ mu_{gs} + 2` at comp, `+ 2` at bsum, `+ 5` at
bprod. Constants may shrink during implementation if
tighter Tower lemmas prove out, but must not grow without
revising the spec. Specifically: comp's `+ 6`, bsum's
`+ 2`, and bprod's `+ 7` are explicit upper bounds; the
proof may discharge with smaller margins if a
`const_mul_tower_le_tower_add_two`-style lemma absorbs
constant factors at a cheaper cost than the
`9 ≤ m` route used above. Such a lemma is not currently
in `Tower.lean`; adding it is a possible plan-stage
refinement.

`Fin.maxOfNat` here takes the family directly (since
`Fin.maxOfNat (n : ℕ) (g : Fin n → ℕ) : ℕ` already accepts
a `Fin n → ℕ`-shaped folder); call sites write
`Fin.maxOfNat k (fun i => …)` with the arity explicit. This
keeps the `[propext, Quot.sound]`-only axiom profile;
mathlib's `Finset.univ.sup` is not used.

For the `Fin.maxOfNat _ v` portion of the bound input: this
replaces the kToER side's `vMax` (which is `private` to
`LawvereKSimMajorization.lean` and additionally uses
`Finset.univ.sup`, transitively pulling
`Classical.choice`). The constructive `Fin.maxOfNat : (Fin
n → ℕ) → ℕ` (T3, `GebLean/LawvereKSim.lean:106`) provides
the same Nat function axiom-cleanly. The K^sim composite
`KMor1.maxOver a` (§5.2) realises `Fin.maxOfNat` as a
level-≤ 2 K^sim morphism.

### §4.3 Joint runtime+value bound theorem

The recipe discharges a conjunctive inductive theorem
bounding both the URM-runtime and the ER-value of `e` by
the same `tower mu_e (Fin.maxOfNat _ v + offset_e)`. Bounding
both quantities together is structurally required by comp's
case: the runtime of `comp f gs` contains
`compileER_runtime f inner` evaluated at
`inner i = (gs i).interp v`, and the IH for `f` requires a
*value* bound on `inner` to specialise. The kToER-side
template `KMor1.majorize` does not face this problem
because it bounds only values of K^sim terms.

```lean
theorem boundExprKParams_dominates :
    {a : ℕ} → (e : ERMor1 a) → (v : Fin a → ℕ) →
    compileER_runtime e v ≤
        tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2) ∧
    e.interp v ≤
        tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2)
```

Proof: structural induction on `e`. The conjunctive shape
allows the comp case to extract the value bound from the
IH on each `gs i` and feed it to the IH for `f` at the
specialised `inner` vector.

- Atom cases (`zero`, `succ`, `proj`, `sub`) close via
  `omega` plus `Tower.mul_tower_le_tower_add_two`
  (`Tower.lean:101`) applied twice to absorb the linear
  coefficient `10`.
- `comp f gs` applies `Tower.tower_comp` to absorb
  `tower mu_f (tower mu_{gs} m + offset_f) ≤ tower (mu_f +
  mu_{gs}) m`, then `mul_tower_le_tower_add_two` for the
  `v_total = Σ v i ≤ a · Fin.maxOfNat _ v` factor.
- `bsum f` applies `mul_tower_le_tower_add_two` for the
  outer `v 0`-fold sum, giving the `+ 2` increment.
- `bprod f` applies the same `+ 2` for the outer sum plus
  the running-product Nat identity `T^k ≤ 2^(k · T)` plus
  `mul_tower_le_tower_add_two` for the resulting exponent,
  totalling `+ 3`.

Anticipated AXIOM_ALLOW points: the `bsum` and `bprod`
cases reduce `perIter`'s `ctx_f = Fin.cons i (Fin.tail v)`
via `simp`, the precise simp chain that surfaced
`Fin.lastCases_castSucc` in T3's `baseFamily_level`,
`stepFamily_level`, and `simulate_interp` (see
[`.claude/rules/lean-coding.md`](../../../.claude/rules/lean-coding.md)
§ Accepted exceptions). T4 inherits this exception for the
bsum and bprod conjunctive cases of
`boundExprKParams_dominates` and for `erToK_interp`
(which chains through `simulate_interp`'s existing
AXIOM\_ALLOW). Expected count: 2–4 theorems. The
annotation does not propagate further; the level theorems,
`boundExprK`, `boundExprKParams`, and `erToK` itself
remain `[propext, Quot.sound]`-only.

## §5 Piece 2 — Ksim composites

The three composites land in `GebLean/Utilities/KArith.lean`,
extending the existing arithmetic family (`pow2`, `mult`,
`monus`, `add`, `pred`, `cond`, `eq`, `natK`, `natK'`).

### §5.1 `KMor1.maxK`

```lean
def KMor1.maxK : KMor1 2
```

The binary maximum via truncated subtraction:
`max(x, y) = (x ∸ y) + y`. Built as a composition of
`KMor1.add`, `KMor1.monus`, and projections.

```lean
@[simp] theorem KMor1.interp_maxK (v : Fin 2 → ℕ) :
    KMor1.maxK.interp v = Nat.max (v 0) (v 1)
```

### §5.2 `KMor1.maxOver`

```lean
def KMor1.maxOver : (a : ℕ) → KMor1 a
```

The `a`-ary maximum over the input vector. Recursive:

- `maxOver 0 = KMor1.zero` (arity-0 constant 0; matches
  `Fin.maxOfNat (v : Fin 0 → ℕ) = 0`).
- `maxOver (a+1) = KMor1.maxK ∘ ⟨KMor1.proj 0,
    KMor1.maxOver a ∘ (Fin.tail-projection family)⟩`.

```lean
@[simp] theorem KMor1.interp_maxOver (a : ℕ) (v : Fin a → ℕ) :
    (KMor1.maxOver a).interp v = Fin.maxOfNat _ v
```

`Fin.maxOfNat : (n : ℕ) → (Fin n → ℕ) → ℕ` is the
constructive maximum helper introduced by T3 in
`GebLean/LawvereKSim.lean:106` (`n` explicit; call sites
write `Fin.maxOfNat _ v` to let Lean infer it from the
type of `v`, matching the codebase pattern at
`KSimURMSimulator.lean:978`). This composite realises that
exact Nat function in K^sim. The spec does not reuse
`LawvereKSimMajorization.lean`'s `vMax` because it is
declared `private` (file-local) and additionally uses
`(Finset.univ : Finset (Fin a)).sup v`, which transitively
pulls `Classical.choice` through mathlib's `Finset`/`Multiset`/
lattice machinery and would break T4's `[propext,
Quot.sound]`-only axiom budget on every theorem that
chains through `Fin.maxOfNat _`.

### §5.3 `KMor1.pow2_iter`

```lean
def KMor1.pow2_iter : (r : ℕ) → KMor1 1
```

The `r`-fold composition of `KMor1.pow2`:

- `pow2_iter 0` = arity-1 identity (`KMor1.proj 0`).
- `pow2_iter (r+1)` = `KMor1.pow2 ∘ KMor1.pow2_iter r`.

```lean
@[simp] theorem KMor1.interp_pow2_iter (r : ℕ) (x : ℕ) :
    (KMor1.pow2_iter r).interp ![x] = tower r x
```

`tower : ℕ → ℕ → ℕ` is the closed form of
`(ERMor1.A_two_iter r).interp ![x]`, already in
`ERAMajorants.lean`. The K^sim composite makes the same
function available on the K^sim side without re-defining
the Nat function.

### §5.4 Level lemmas

```lean
theorem KMor1.maxK_level      : KMor1.maxK.level ≤ 2
theorem KMor1.maxOver_level   : ∀ a, (KMor1.maxOver a).level ≤ 2
theorem KMor1.pow2_iter_level : ∀ r, (KMor1.pow2_iter r).level ≤ 2
```

Discharged via `KMor1.level` of compositions = `Nat.max`
of components, using `Fin.maxOfNat_le` and
`Fin.le_maxOfNat` from the T3 refactor. `pow2`, `mult`,
`monus`, `add` are all level ≤ 2 (existing KArith); their
compositions stay ≤ 2.

## §6 Piece 3 — `boundExprK` assembly

### §6.1 Shape

```lean
def boundExprK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  let p := boundExprKParams e   -- (mu_e, offset_e)
  KMor1.comp
    (KMor1.pow2_iter p.1)
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.add
        (fun i : Fin 2 =>
          match i with
          | ⟨0, _⟩ => KMor1.maxOver a
          | ⟨1, _⟩ => KMor1.natK' a p.2))
```

The inner morphism family uses the explicit-witness form
`match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => …` over `Fin 2`,
mirroring the established codebase convention (e.g.
`KArith.lean:537-543` and `KSimURMSimulator.lean:128-133`).
This avoids the `DecidableEq (Fin 2)` instance lookup that
`if i = 0` would require and avoids the literal-pattern
syntax (`| 0 =>`) which is less robust under instance
changes.

Reading: `(maxOver a) v = Fin.maxOfNat _ v` and
`(natK' a offset) v = offset`, so the inner `add`
composition produces `Fin.maxOfNat _ v + offset`. Feeding that
into `pow2_iter mu` produces `tower mu (Fin.maxOfNat _ v +
offset)`.

### §6.2 Alternatives considered and rejected

- **Augmented-arity** uses
  `pow2_iter mu ∘ maxOver (a+1) ∘ Fin.cons (natK' 0 offset) projections`.
  This computes `tower mu (Nat.max offset (Fin.maxOfNat _ v))`,
  which is mathematically tighter than the spec's
  `tower mu (Fin.maxOfNat _ v + offset)` (since
  `Nat.max offset (Fin.maxOfNat _ v) ≤ offset + Fin.maxOfNat _ v`,
  monotonicity of `tower` in its second argument gives the
  inequality). Rejected on proof-shape grounds: the
  kToER-side `KMor1.majorize` carries an explicit
  `(r, offset)` pair whose offset is *added* to the max in
  the bound shape; the bsum/bprod increment proofs in §4
  rely on `mul_tower_le_tower_add_two`, which is stated in
  terms of `m = Fin.maxOfNat _ v + offset` (an additive
  form). The augmented-arity shape would require restating
  those Tower lemmas in `Nat.max` form, with no semantic
  gain.
- **Offset-absorbed-into-mu** (`pow2_iter (mu + g(offset))
  ∘ maxOver a`): folds offset into the tower height;
  requires the recipe to surrender the `(mu, offset)`
  shape and computes a strictly larger bound. Breaks the
  kToER-mirror pattern.

### §6.3 Level, interp, and domination theorems

```lean
theorem boundExprK_level
    {a : ℕ} (e : ERMor1 a) : (boundExprK e).level ≤ 2

theorem boundExprK_interp
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (boundExprK e).interp v
      = tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2)

theorem boundExprK_dominates
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    compileER_runtime e v ≤ (boundExprK e).interp v
```

`boundExprK_interp` unfolds the composition via the
`@[simp]` interp lemmas for `pow2_iter`, `maxOver`, `add`,
`natK'`. `boundExprK_dominates` chains `boundExprK_interp`
with `boundExprKParams_dominates`'s runtime conjunct (the
left half of the conjunction in §4.3). `boundExprK_level`
chains level lemmas of the underlying composites.

## §7 Piece 4 — `erToK` assembly

### §7.1 Definition

```lean
def erToK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  KMor1.comp
    (KSimURMSimulator.simulate (compileER e))
    (Fin.cons (boundExprK e) (fun i : Fin a => KMor1.proj i))
```

Type sanity:

- `compileER` has signature
  `{a : ℕ} → ERMor1 a → URMProgram a` (Compiler.lean:1590),
  so `compileER e : URMProgram a`. The `URMProgram` type is
  arity-indexed by `numInputs`, hence `(compileER e).numInputs
  = a` holds *definitionally by type*, not by a separate
  invariant theorem. T3's `simulate` then specialises to
  `simulate (compileER e) : KMor1 (a + 1)`.
- `Fin.cons (boundExprK e) (fun i => KMor1.proj i) :
    Fin (a + 1) → KMor1 a`; slot 0 carries the step-count
  bound, slots 1..a are input projections.
- `KMor1.comp` of `KMor1 (a+1)` with `a+1` arity-`a`
  morphisms yields `KMor1 a`.

### §7.2 Level theorem

```lean
theorem erToK_level
    {a : ℕ} (e : ERMor1 a) : (erToK e).level ≤ 2
```

By `KMor1.level` of `comp` = `Nat.max` over components.
Head: `simulate_level (compileER e) ≤ 2`. Components:
`boundExprK_level e ≤ 2`; projections are level 0. Folded
via `Fin.maxOfNat_le`.

### §7.3 Interpretation theorem

```lean
theorem erToK_interp
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (erToK e).interp v = e.interp v
```

Proof chain:

```text
(erToK e).interp v
  = (simulate (compileER e)).interp
      (Fin.cons ((boundExprK e).interp v) v)
                                            -- KMor1.interp_comp + projection interp
  = ((URMState.init (compileER e) v).runFor
        ((boundExprK e).interp v)).regs
      (compileER e).outputReg
                                            -- T3 simulate_interp
  = e.interp v
                                            -- T2 compileER_runFor
                                            --   hypothesis discharged by
                                            --   boundExprK_dominates
```

T2's `compileER_runFor` takes a hypothesis `s ≥
compileER_runtime e v` and yields equality with
`e.interp v`. `boundExprK_dominates` provides this hypothesis
with `s := (boundExprK e).interp v`.

## §8 Piece 5 — `erToKFunctor`

T4's functor maps the multi-output ER quotient category
`LawvereERCat` (hom = `ERMorNQuo n m`) to the depth-2 K^sim
quotient category `LawvereKSimDCat 2` (hom = `KSimMor 2 n m`,
a structure with a `KMorNQuo n m` field plus a depth-2
witness). The single-output `erToK` from §7 lifts to a
multi-output `erToKN` componentwise, passes through the ER
quotient via `Quotient.liftOn`, and packages with the
depth-2 witness on the K side. The construction mirrors the
forward functor `kToERFunctor` at
`GebLean/LawvereKSimER.lean:474`.

### §8.1 Multi-output extension `erToKN`

```lean
def erToKN {n m : ℕ} (e : ERMorN n m) : KMorN n m :=
  fun j => erToK (e j)

theorem erToKN_interp {n m : ℕ} (e : ERMorN n m)
    (v : Fin n → ℕ) (j : Fin m) :
    (erToKN e j).interp v = (e j).interp v :=
  erToK_interp (e j) v

theorem erToKN_level {n m : ℕ} (e : ERMorN n m)
    (j : Fin m) : (erToKN e j).level ≤ 2 :=
  erToK_level (e j)

theorem erToKN_compat_extEq {n m : ℕ}
    {e₁ e₂ : ERMorN n m}
    (he : ∀ v j, (e₁ j).interp v = (e₂ j).interp v) :
    ∀ v j, (erToKN e₁ j).interp v
            = (erToKN e₂ j).interp v := by
  intro v j
  rw [erToKN_interp, erToKN_interp]
  exact he v j
```

`erToKN` is componentwise application of `erToK`. The
interp lemma is a thin wrapper over §7's `erToK_interp`;
the level lemma is a thin wrapper over §7's `erToK_level`;
the extEq-compat lemma is what
`Quotient.liftOn` will consume to discharge
well-definedness.

### §8.2 Morphism component `erToKFunctor_map`

```lean
def erToKFunctor_map {n m : ℕ}
    (e : ERMorNQuo n m) : KSimMor 2 n m :=
  Quotient.liftOn e
    (fun rec => ⟨Quotient.mk (kMorNSetoid n m) (erToKN rec),
                 /- depth-2 witness via erToKN_level -/⟩)
    (fun e₁ e₂ h => by
      /- KSimMor equality via depth-witness Quotient.sound +
         erToKN_compat_extEq -/
      sorry)
```

The lift produces a `KSimMor 2 n m` value, which packages:

- a `KMorNQuo n m` term (the quotient class of `erToKN
  rec`), and
- a depth-2 witness `KMorNQuo.atDepth 2 _`, discharged by
  the per-component level lemma `erToKN_level`.

Well-definedness of the lift (the `Quotient.sound`
obligation) uses `erToKN_compat_extEq`: two ER families
that agree pointwise produce K^sim families that agree
pointwise.

### §8.3 Functor laws

```lean
theorem erToKFunctor_map_id (n : LawvereERCat) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.id
          (obj := LawvereERCat) n)
      = CategoryTheory.CategoryStruct.id
          (obj := LawvereKSimDCat 2)
          (n : LawvereKSimDCat 2)

theorem erToKFunctor_map_comp {n m k : ℕ}
    (e : ERMorNQuo n m) (f : ERMorNQuo m k) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.comp
          (obj := LawvereERCat) e f)
      = CategoryTheory.CategoryStruct.comp
          (obj := LawvereKSimDCat 2)
          (erToKFunctor_map e) (erToKFunctor_map f)
```

Both proofs are by `Quotient.inductionOn` (or
`inductionOn₂`) over the ER quotient witnesses, reducing
to a `Quotient.sound` step on the K side that
`erToKN_compat_extEq` discharges. `map_id` uses
`erToK_interp` on `ERMor1.proj` to recognise the all-
projections identity. `map_comp` uses `erToK_interp` on
both sides of `e ≫ f` to recognise the composition; the
nested `KMor1.comp` interp identity follows from `erToK`'s
construction (the simulator applied to the compiled
composition equals the value of the composition). This
mirrors `kToERFunctor_map_comp` at
`LawvereKSimER.lean:427-468` in proof shape.

### §8.4 Functor assembly

```lean
def erToKFunctor : CategoryTheory.Functor
    LawvereERCat (LawvereKSimDCat 2) where
  obj n     := n
  map       := erToKFunctor_map
  map_id    := erToKFunctor_map_id
  map_comp  := erToKFunctor_map_comp
```

The `obj n := n` is identity by def-unfolding
(`LawvereERCat = ℕ` and `LawvereKSimDCat 2 = ℕ`), matching
the `kToERFunctor` shape at `LawvereKSimER.lean:476`.

## §9 File organisation

| File | Status | T4 changes |
| --- | --- | --- |
| `GebLean/Utilities/KArith.lean` | exists, ~1188 LOC | + `maxK`, `maxOver`, `pow2_iter` + interp + level lemmas |
| `GebLean/Utilities/KSimURMSimulator.lean` | exists (T3), ~986 LOC | unchanged; consumed only |
| `GebLean/LawvereERKSim/Compiler.lean` | exists (T2) | unchanged; `compileER`, `compileER_runtime`, `compileER_runFor` consumed |
| `GebLean/LawvereKSim.lean` (Fin.maxOfNat) | exists (T3) | unchanged; consumed only |
| `GebLean/LawvereKSimMajorization.lean` | exists | unchanged; `vMax`, `tower` consumed |
| `GebLean/Utilities/ERAMajorants.lean` | exists (Step 3) | unchanged; `tower` Nat function and `A_two_iter` closed-form interp consumed |
| `GebLean/LawvereERKSim/RuntimeBound.lean` | new | `boundExprKParams`, `boundExprKParams_dominates`, `boundExprK`, `boundExprK_level`, `boundExprK_interp`, `boundExprK_dominates` |
| `GebLean/LawvereERKSim/ErToK.lean` | new | `erToK`, `erToK_level`, `erToK_interp` |
| `GebLean/LawvereERKSim/ErToKFunctor.lean` | new | `erToKN`, `erToKN_interp`, `erToKN_level`, `erToKN_compat_extEq`, `erToKFunctor_map`, `erToKFunctor`, `erToKFunctor_map_id`, `erToKFunctor_map_comp` |
| `GebLean/LawvereERKSim.lean` | exists (index) | `public import` the three new modules |
| `GebLean.lean` | exists (top index) | `erToKFunctor` enters the public surface |
| `GebLeanTests/Utilities/KArith.lean` | exists | + `#guard` tests on small inputs for the three new composites |
| `GebLeanTests/LawvereERKSim/ErToK.lean` | new | `#guard` smoke tests for `erToK` on small ER atoms (succ, proj); no bsum/bprod tests, per [`feedback_godel_interp_not_decidable_in_tests`](../../memory/feedback_godel_interp_not_decidable_in_tests.md) |

## §10 Dependency DAG

```text
                      KArith.lean
                          │
                          │ + maxK, maxOver, pow2_iter
                          ▼
              ERAMajorants.lean (tower)
                          │
                          ▼
        LawvereKSimMajorization.lean (vMax)
                          │
                          ▼
             RuntimeBound.lean (new)
                          │
                          ▼   ← T3 KSimURMSimulator.lean
                  ErToK.lean (new)
                          │
                          ▼   ← T2 Compiler.lean
              ErToKFunctor.lean (new)
                          │
                          ▼
            GebLean.lean (re-export)
```

Linear; no cycles. The implementation plan will linearise
this DAG into ~12–15 tasks.

## §11 Axiom budget

Expected per-declaration axiom profiles after `lake build`:

- `[propext, Quot.sound]` (or no axioms) for:
  `maxK`, `maxOver`, `pow2_iter`, their interp lemmas,
  their level lemmas, `boundExprKParams` (Lean `def`),
  `boundExprK`, `boundExprK_interp`, `boundExprK_level`,
  `erToK`, `erToK_level`, `erToKFunctor.obj`,
  `erToKFunctor.map`, `erToKFunctor.map_id`,
  `erToKFunctor.map_comp`.
- `[propext, Classical.choice, Quot.sound]` with explicit
  `-- AXIOM_ALLOW: Classical.choice (Fin.lastCases_castSucc
  via simp on Fin.cons/Fin.tail)` annotations at exactly the
  following declarations:
  1. `boundExprKParams_dominates`, bsum case (manipulates
     `perIter`'s `ctx_f = Fin.cons i (Fin.tail v)` via
     `simp only [Fin.lastCases_castSucc, ...]` to reduce
     `f.interp ctx_f`).
  2. `boundExprKParams_dominates`, bprod case (same simp
     chain on `ctx_f`).
  3. `erToK_interp` (chains through `simulate_interp` whose
     existing AXIOM\_ALLOW propagates via the `=` step).

This commitment is definite, not conditional: the simp
chain is the same one used in T3 (see
`KSimURMSimulator.lean`'s `baseFamily_level`,
`stepFamily_level`, `simulate_step_match`, `simulate_interp`,
`simulate_level`), and `Fin.lastCases_castSucc` is the
mathlib equation lemma for `Fin.lastCases` on the
`castSucc` branch — the only known constructive
alternative (restructuring `compileER_runtime` to avoid
`Fin.cons`/`Fin.tail` in `ctx_f`) is rejected as
incompatible with T2's landed surface.

The AXIOM\_ALLOW annotation does not propagate further than
these three sites. Notably: `erToKFunctor.map_id` and
`erToKFunctor.map_comp` rely on `erToK_interp`'s value
identity (`(erToK e).interp v = e.interp v`) but the
quotient operations themselves
(`Quotient.sound`, `Quotient.lift`) are
`[propext, Quot.sound]`-only, so the functor laws inherit
the AXIOM\_ALLOW only via `erToK_interp`.

No new axioms requested. No `noncomputable`. No `admit`.
`sorry` permitted only between commits during
skill-driven development, never in committed code.

## §12 Test plan

K^sim composites (`GebLeanTests/Utilities/KArith.lean`):

```lean
#guard (KMor1.maxK).interp ![3, 5] = 5
#guard (KMor1.maxOver 4).interp ![3, 5, 2, 4] = 5
#guard (KMor1.pow2_iter 2).interp ![2] = 16
```

`erToK` smoke tests (`GebLeanTests/LawvereERKSim/ErToK.lean`):

```lean
#guard (erToK ERMor1.succ).interp ![3] = 4
#guard (erToK ERMor1.zero).interp Fin.elim0 = 0
```

Tests on `comp`, `bsum`, `bprod` are not viable as
`#guard`s — the tower expansion of `boundExprK` for
non-trivial `e` exceeds practical Nat-reduction budgets,
mirroring the limitations recorded in
[`feedback_godel_interp_not_decidable_in_tests`](../../memory/feedback_godel_interp_not_decidable_in_tests.md).
Compositional correctness is verified by `lake build` of
`erToK_interp` and the functor laws, not by runtime `#guard`.

Functor laws are `Prop` and are verified by `lake build`'s
type-check, not by `#guard`.

## §13 Scope guardrails

In scope:

- Definitions and theorems listed in §3 (Pieces 1–5).
- File creation per §9.
- Tests per §12.

Out of scope (deferred to T5):

- Strict natural-isomorphism `kToERFunctor ∘ erToKFunctor ≅
  𝟙 _` and `erToKFunctor ∘ kToERFunctor ≅ 𝟙 _`.
- Equivalence packaging
  `LawvereERCat ≌ LawvereKSimDCat 2`.

Out of scope (not anyone's job for this transcription):

- Tightening the per-constructor numeric constants
  (`c_succ`, `c_proj`, etc.) beyond what suffices to
  discharge `boundExprKParams_dominates`. The literature
  contract is the recipe shape; numeric constants are
  Lean-side flexible.
- An ER-side intermediate runtime function
  `compileER_runtimeER : ERMor1 a → ERMor1 a`. T4 bounds at
  the Nat level via `tower`.
- A `PolyBound` for any new composite. `tower r x` for
  `r ≥ 1` is super-polynomial, mirroring the carve-out
  recorded in the 2026-05-03 Step 3 ER-Tourlakis A-majorants
  spec.
- Refactoring T2's `compileER_runtime` shape. Taken as
  given.

## §14 Size estimate

| Piece | Estimated LOC |
| --- | --- |
| KArith composites (§5) | ~300 |
| `RuntimeBound.lean` (§4, §6) | ~600 |
| `ErToK.lean` (§7) | ~150 |
| `ErToKFunctor.lean` (§8, incl. multi-output passage mirroring kToERFunctor) | ~350 |
| Tests (§12) | ~80 |
| Total | ~1480 |

Comparable to T3 (~1000 LOC) and well below T2 (~12 kLOC).
One workstream; no further split anticipated.

## §15 References

Tourlakis 2018, *Topics in PR Complexity*
(`.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`):

- §0.1.0.27 (`A_n^r` majorant of every E^n function).
- §0.1.0.37 (K^sim_2 simulator `v_1`).
- §0.1.0.42 (Lemma: every E^n function has E^n URM runtime).
- §0.1.0.43 (Ritchie–Cobham property).
- §0.1.0.44 (Corollary: `K^sim_n = E^{n+1}`).

Project documents:

- Master research design:
  [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md).
- Master ER-to-K spec:
  [`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
- T3 spec:
  [`docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](2026-05-21-step-t3-urm-to-ksim-simulator-design.md).
- T3 plan:
  [`docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](../plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).
- Step 3 ER-Tourlakis A-majorants spec:
  [`docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`](2026-05-03-step-3-er-tourlakis-A-majorants-design.md).
- Post-T3 handoff:
  [`docs/superpowers/plans/2026-05-22-post-t3-handoff.md`](../plans/2026-05-22-post-t3-handoff.md).

Project source files consumed:

- `GebLean/LawvereERKSim/Compiler.lean` (T2 compiler +
  `compileER_runtime` + `compileER_runFor`).
- `GebLean/Utilities/KSimURMSimulator.lean` (T3 simulator).
- `GebLean/Utilities/KArith.lean` (existing K^sim
  arithmetic).
- `GebLean/Utilities/ERAMajorants.lean` (ER `A_two_iter`
  and `tower`).
- `GebLean/LawvereKSimMajorization.lean` (`vMax`, kToER
  template).
- `GebLean/LawvereKSim.lean` (`Fin.maxOfNat` constructive
  helper).

Project rules:

- [`CLAUDE.md`](../../../CLAUDE.md).
- [`.claude/rules/lean-coding.md`](../../../.claude/rules/lean-coding.md).
- [`.claude/rules/fork-upstream-flow.md`](../../../.claude/rules/fork-upstream-flow.md).
- [`.claude/rules/markdown-writing.md`](../../../.claude/rules/markdown-writing.md).
