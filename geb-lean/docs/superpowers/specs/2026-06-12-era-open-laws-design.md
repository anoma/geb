# Open-term recursion laws for the minimal-basis ERA — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Scope and goal](#1-scope-and-goal)
- [2 Sources and provenance](#2-sources-and-provenance)
- [3 Current state](#3-current-state)
- [4 Deliverables](#4-deliverables)
- [5 Method: translating `Nat`-level proofs to object level](#5-method-translating-nat-level-proofs-to-object-level)
- [6 Derivation plan](#6-derivation-plan)
  - [Phase 0 — infrastructure](#phase-0--infrastructure)
  - [Phase 1 — additive algebra by `uniq`](#phase-1--additive-algebra-by-uniq)
  - [Phase 2 — mod corollaries](#phase-2--mod-corollaries)
  - [Phase 3 — laws not requiring domination](#phase-3--laws-not-requiring-domination)
  - [Phase 4a — the subtraction cluster](#phase-4a--the-subtraction-cluster)
  - [Phase 4b — the multiplicative cluster](#phase-4b--the-multiplicative-cluster)
- [7 Shape conversions and domination](#7-shape-conversions-and-domination)
  - [7.1 The requirement](#71-the-requirement)
  - [7.2 The exponent-parametric subtraction template](#72-the-exponent-parametric-subtraction-template)
  - [7.3 The domination family](#73-the-domination-family)
  - [7.4 The subtraction cluster](#74-the-subtraction-cluster)
  - [7.5 Mod-of-multiple](#75-mod-of-multiple)
  - [7.6 Powers](#76-powers)
  - [7.7 The recovery equation](#77-the-recovery-equation)
- [8 Approaches explored and rejected](#8-approaches-explored-and-rejected)
- [9 Acceptance criteria](#9-acceptance-criteria)
- [9a Design revision: restore truncated subtraction as a primitive](#9a-design-revision-restore-truncated-subtraction-as-a-primitive)
  - [Basis and axioms](#basis-and-axioms)
  - [Consequence: the impasse dissolves](#consequence-the-impasse-dissolves)
  - [The redundancy theorem](#the-redundancy-theorem)
- [10 Scope guardrails](#10-scope-guardrails)
- [11 References](#11-references)

<!-- END doctoc -->

## 1 Scope and goal

In `GebLean/Era.lean` (equation calculus over the minimal basis
`{x + y, x mod y, 2^x}`, seven defining equations), derive the
open-term recursion laws that were axioms before the basis
reduction, so that the full pre-reduction equational API is again
available — now as theorems. The axiom set `eraDefs` is not
extended: deriving every law from the seven equations is the point
of the workstream.

The pre-reduction file (thirteen-axiom basis) is at git revision
`daab65a9` ("Closed-term ERA consistency"); the basis reduction is
`ed0b6752` ("Minimize ERA substitution basis"). The eleven target
statements are reproduced verbatim in §4.

## 2 Sources and provenance

| Item | Status | Source |
| --- | --- | --- |
| Schemata K, U₁, E₁, E₂, E₃ | Transcription | [Goo54] pp. 248, 251 |
| Additive algebra: `0+a=a` (6), `a+Sb=Sa+b` (7), `a+b=b+a` (8), associativity (10) | Transcription | [Goo54] pp. 249–250 |
| Multiplicative algebra: `Sa·b=a·b+b` (11), commutativity (14), distributivity (15), associativity (15.1) | Transcription | [Goo54] p. 250, modulo replacing the `·`-axiom inputs by the Phase-4 theorems |
| Predecessor/subtraction ladder: `(a∸b)∸1=(a∸1)∸b` (1), `Sa∸Sb=a∸b` (2), `a∸a=0` (3), `0∸a=0` (4), `(a+b)∸b=a` (5) | Transcription of statements | [Goo54] p. 249; the derivations do not transcribe (§7.4) |
| Recursion laws for `∸`, `·`, `/`, `^` as theorems over the three-element basis | Novel | Transposition of the `Nat`-level identities `tsub_identity`, `dmul_identity`, `div_identity`, `pow_identity`, `sq_identity` (already in `Era.lean`, after [PSS26] Lemmas 2–3) into object-level derivations |
| Exponent-parametric subtraction template and its shape-decided laws (§7.2) | Novel | This spec |
| Object-level exponential domination family (§7.3) | Novel | No published object-level derivation over this basis is known |
| Mod-of-multiple law (§7.5) | Novel | Object-level analogue of `Nat.mul_add_mod` |
| Mod corollaries `0 mod v = 0`, `v mod v = 0` | Novel | Direct from `axMod0`/`axModLt`/`axModAdd` |

In [Goo54] the recursion equations for `∸` and `·` are *defining
axioms* (p. 249) and equations (1)–(5), (9), (13), (16), (17) are
derived from them. Here the direction is reversed: `∸`, `·`, `/`,
`^` are defined terms over `{+, mod, 2^x}`, so Goodstein's axioms
are the theorems to derive, and his derivations apply only after
their `∸`-axiom inputs have been established from the `esub`
unfolding. This reversal is where the novel content lies; the
additive layer (6)–(10) transcribes directly because the addition
axioms are shared.

## 3 Current state

`GebLean/Era.lean` provides, over the unchanged calculus
(`ax`/`refl`/`euclid`/`subst`/`uniq`):

- equational rules `Derivable.symm`/`trans`/`inst`/`succ_congr`;
- per-operation congruences `eadd_congr`, `emod_congr`,
  `eexp2_congr`, and `_congr` for every derived operation
  (`esq`, `edelta`, `esub`, `edmul`, `ediv`, `emul`, `epow`);
- `derivable_def` plus seven axiom-instance lemmas
  (`derivable_add_zero`, `derivable_add_succ`,
  `derivable_mod_zero`, `derivable_mod_lt`, `derivable_mod_add`,
  `derivable_exp2_zero`, `derivable_exp2_succ`);
- numeral computation lemmas `numeral_add/exp2/mod/sq/delta/sub/`
  `dmul/div/mul/pow` (closed bases for inductions);
- a machine-checked example `0 + x = x` exhibiting the full
  `uniq` invocation pattern (axiom instances via
  `Derivable.subst`, normalization by
  `simp only [Tm.subst, eadd_subst]`).

The `uniq` rule is more general than Goodstein's U₁: the step
functional `H` may use the parameters (variables 2..n+1), not only
the recursion variable and the previous value.

## 4 Deliverables

Eleven theorems (`u v : ETm n` arbitrary; statements verbatim; the
two addition laws are axioms and already exist as
`derivable_add_zero` / `derivable_add_succ`):

```lean
theorem derivable_sub_zero : Derivable eraDefs ⟨u ∸ᵉ .zero, u⟩
theorem derivable_sub_succ :
    Derivable eraDefs ⟨u ∸ᵉ .succ v, (u ∸ᵉ v) ∸ᵉ one⟩
theorem derivable_pred_zero :
    Derivable eraDefs ⟨(.zero : ETm n) ∸ᵉ one, .zero⟩
theorem derivable_pred_succ : Derivable eraDefs ⟨.succ u ∸ᵉ one, u⟩
theorem derivable_mul_zero : Derivable eraDefs ⟨u *ᵉ .zero, .zero⟩
theorem derivable_mul_succ :
    Derivable eraDefs ⟨u *ᵉ .succ v, (u *ᵉ v) +ᵉ u⟩
theorem derivable_pow_zero : Derivable eraDefs ⟨u ^ᵉ .zero, one⟩
theorem derivable_pow_succ :
    Derivable eraDefs ⟨u ^ᵉ .succ v, (u ^ᵉ v) *ᵉ u⟩
theorem derivable_div_zero : Derivable eraDefs ⟨u /ᵉ .zero, .zero⟩
theorem derivable_zero_div :
    Derivable eraDefs ⟨(.zero : ETm n) /ᵉ .succ u, .zero⟩
theorem derivable_div_succ :
    Derivable eraDefs ⟨.succ u /ᵉ .succ v,
      (u /ᵉ .succ v) +ᵉ
        (one ∸ᵉ (v ∸ᵉ (u ∸ᵉ .succ v *ᵉ (u /ᵉ .succ v))))⟩
```

Supporting theorems produced by the phases (additive and
multiplicative algebra, mod corollaries, the extensionality rule,
the subtraction template, the domination family) are part of the
public API and follow the same naming scheme.

## 5 Method: translating `Nat`-level proofs to object level

Each open law is derived by unfolding the derived operation's
definition and mirroring its `Nat`-side identity proof
(`tsub_identity`, `div_identity`, `pow_identity`, `sq_identity`,
`dmul_identity`) step by step in the object calculus:

| `Nat`-side step | Object-level counterpart |
| --- | --- |
| `omega` (additive) | Phase-1 additive algebra |
| `Nat.add_mod_right` | `axModAdd` instance |
| `Nat.mod_eq_of_lt h` | `axModLt` instance plus a derivable shape conversion `divisor = dividend +ᵉ .succ t` for an explicit term `t` (§7.1) |
| `Nat.mul_add_mod` (open multiplier) | mod-of-multiple law, by `uniq` on the multiplier (§7.5) |
| algebra on products | multiplicative layer, Goodstein (11)–(15.1) (Phase 4b) |
| existential witness (`pow_mod_rep`) | explicit witness term plus a `uniq` derivation of its recursion equation (§7.6) |
| case split (`x < y` / `x ≥ y`) | `uniq` induction or the extensionality rule E₃ (Phase 0); where the comparison is decided by the term shape, the shape-decided template laws of §7.2 |

## 6 Derivation plan

### Phase 0 — infrastructure

- Promote the `0 + x = x` example to a named theorem
  `derivable_zero_add`.
- Derive the zero/successor extensionality rule (Goodstein's E₃):
  from agreement at `.zero` and agreement at successors, conclude
  equality. Conjectured derivation: apply `uniq` with a step
  functional `H` that ignores the previous-value slot; verify
  against the generalized `uniq` (the `H` here may use the
  recursion variable itself, which Goodstein's U₁ does not need).

### Phase 1 — additive algebra by `uniq`

[Goo54] equations (6), (7), (8), (10): `succ_add`, `add_comm`,
`add_assoc` (and (6) `zero_add` from Phase 0). Multi-variable
laws: the `uniq` base premise is at scope `n`, hence open in the
parameters; order the derivations so each base instance is already
available (the base of `add_comm` is `zero_add`).

### Phase 2 — mod corollaries

- `derivable_zero_mod : 0 %ᵉ v = 0` by `uniq` on `v` with
  `H := .zero`; base from `axMod0` at `0`; step from
  `axModLt (0, v)` plus `zero_add`.
- `derivable_mod_self : v %ᵉ v = 0` from `axModAdd (0, v)` plus
  `zero_add` plus `zero_mod` (no induction).

### Phase 3 — laws not requiring domination

Verified proof sketches:

- `derivable_zero_sub : 0 ∸ᵉ w = 0`: by E₃ on `w`. Zero case
  (`w = .zero`): unfold `esub`; both remainders close by
  `axAdd0`, `mod_self`, and `zero_mod`. Successor case
  (`w = .succ x`, `x` a fresh variable): the inner remainder
  `(P +ᵉ .zero) %ᵉ (P +ᵉ .succ x)` is an `axModLt` instance after
  `axAdd0`; the outer remainder is `mod_self`. (`axModLt` matches
  only a successor-shaped addend, so the split is required.)
- `derivable_sub_self : t ∸ᵉ t = 0`: inner is `mod_self`, outer is
  `zero_mod`. No case split: the shapes coincide.
- `derivable_pred_zero` = `zero_sub` at `w := one`.
- `derivable_edmul_zero : edmul t .zero = .zero` via
  `esq (t +ᵉ .zero) = esq t` (congruence plus `axAdd0`),
  `esq .zero = .zero` (numeral), `sub_self`.
- `derivable_mul_zero` from `edmul_zero` plus `ediv_congr` plus
  numerals.
- `derivable_div_zero` from `axMod0`, `sub_self`, `edmul_zero`,
  `zero_sub`, `axMod0`.
- `derivable_zero_div`: rewrite the dividend's inner argument by
  `zero_mod` (`0 %ᵉ .succ u = 0`) under `esub_congr`, so the
  subtraction becomes the closed instance `0 ∸ᵉ 0` (`sub_self` at
  `.zero`) and the dividend reduces by numerals to `.zero`; the
  modulus stays open in `u`, and the outer remainder closes by
  `zero_mod` under `emod_congr`.

### Phase 4a — the subtraction cluster

Order: domination instances (§7.3) → `sub_zero`, `pred_succ`
(§7.4, verified reductions) → cluster entry for
{(1), (2), `sub_succ`} (§7.4, open) → `sub_succ`.

### Phase 4b — the multiplicative cluster

Reachable only after Phase 4a. Cluster entry is open (§7.5):
the open-term squaring law (`esq t = t *ᵉ t`, mirroring
`sq_identity`) consumes mod-of-multiple, whose step consumes
`mul_succ`, whose derivation through `edmul` consumes the
squaring law. One member must be entered from the template and
domination layers alone; the dependency order among the entry
members is fixed by §7.5 (`mul_succ` before mod-of-multiple's
step; the squaring law after mod-of-multiple). Order after the
entry members: multiplicative algebra (11), (14), (15), (15.1)
as needed → `pow_zero` (§7.6, verified reduction) →
`pow_mod_rep` transposition (§7.6) → `pow_succ` → `div_succ`.

## 7 Shape conversions and domination

### 7.1 The requirement

Every `Nat.mod_eq_of_lt` site needs, at object level,
`Derivable ⟨divisor, dividend +ᵉ .succ t⟩` for an explicit term
`t`. The sites in the identity proofs designated by §5, with
their dividend and modulus shapes:

| Identity | Dividend | Modulus |
| --- | --- | --- |
| `tsub_identity`, case `x < y` | `2^E + x` | `2^E + y` |
| `tsub_identity`, case `x ≥ y` (twice) | `x − y` | `2^E + y`, then `2^E + x` |
| `sq_identity` | `n·n` | `2^n + n` |
| `div_identity` | `x / y` | `2(x+1)y − 1` |
| `pow_identity` | `x^y` | `2^c − x`, `c = xy+x+1` |

The moduli of the last two rows are `∸`-shaped, and the
`sq_identity` dividend is not below `2^n` (at `n = 3`, `9 > 8`;
the available bound is `n·n < 2^n + n`). No single divisor form
covers the chain; the conversions are organised as follows.

### 7.2 The exponent-parametric subtraction template

Generalize the `esub` unfolding to an explicit exponent: for
terms `s t e`, write `esubAt e s t` for
`((eexp2 e +ᵉ s) %ᵉ (eexp2 e +ᵉ t)) %ᵉ (eexp2 e +ᵉ s)`, so that
`s ∸ᵉ t = esubAt (s +ᵉ t) s t` definitionally. Two laws are
decided purely by term shape, given domination hypotheses
(verified sketches):

- `esubAt_of_add`: if `Derivable ⟨u, w +ᵉ v⟩` and
  `Derivable ⟨eexp2 e, u +ᵉ .succ p⟩`, then
  `Derivable ⟨esubAt e u v, w⟩`. Inner remainder: rewrite
  `eexp2 e +ᵉ u` as `w +ᵉ (eexp2 e +ᵉ v)` (additive algebra),
  apply `axModAdd`, then `axModLt` after exhibiting
  `eexp2 e +ᵉ v = w +ᵉ .succ (…)` from the domination hypothesis
  by additive algebra. Outer remainder: `axModLt` after
  exhibiting `eexp2 e +ᵉ u = w +ᵉ .succ (…)` likewise.
- `esubAt_of_lt`: if `Derivable ⟨v, u +ᵉ .succ d⟩`, then
  `Derivable ⟨esubAt e u v, 0⟩`. Inner remainder: the divisor is
  the dividend `+ᵉ .succ d` by additive algebra, so `axModLt`
  applies and yields `eexp2 e +ᵉ u`; the outer remainder is
  `mod_self`. No domination hypothesis is consumed.

These two laws cover every `∸`-shaped modulus in the chain: a
modulus `2^c ∸ x` with `2^c = d +ᵉ x +ᵉ .succ p` derivable
converts to `d +ᵉ .succ p` by `esubAt_of_add`, after which the
site is shape-decided. In particular Goodstein's (5)
`(a+b) ∸ b = a` is the `esubAt_of_add` instance at
`e := (a+b) +ᵉ b`, and his (17) is not needed for the chain
(§7.7).

### 7.3 The domination family

The remaining inputs are domination instances
`Derivable ⟨eexp2 e, a +ᵉ .succ t⟩` for specific exponents `e`
and minorants `a`. The schema members are stated at variable
scope and consumed by instantiation (`Derivable.inst`), with
compound terms — including `eexp2`-headed terms, as in §7.2's
conversion and §7.6's `pow_zero` — substituted for the
variables. The members:

- the summand family: `e` a sum of distinct variables and
  constants, `a` a sub-sum of `e` (true in the standard model
  since `x + 1 ≤ 2^x`);
- the squared instance for `esq`:
  `eexp2 e +ᵉ e = (e *ᵉ e) +ᵉ .succ t` (mirror of
  `mul_self_lt_two_pow_add`);
- the power instance for `epow`:
  `eexp2 c = (u ^ᵉ v) +ᵉ u +ᵉ .succ t` at `c = uv + u + 1`
  (mirror of the `hbound` step of `pow_identity`).

Status: open. No derivation of any non-closed instance is
verified. The witness `t` "is" `2^e ∸ .succ a`, but the `∸` laws
are exactly what is being derived — the circularity recorded in
§8. A candidate approach: mod-expressible witnesses, e.g.
`t := eexp2 (.succ a') %ᵉ (eexp2 a' +ᵉ .succ a')` for
`2^{Sa'} mod (2^{a'} + Sa') = 2^{a'} − Sa'`; the witness term
exists, but deriving its defining equation is itself a mod fact
of the same kind, so the approach is unverified. This family is
the workstream's central unresolved obligation; it is gated by
the staged acceptance of §9.

### 7.4 The subtraction cluster

With the template and domination instances available:

- `sub_zero` (verified reduction): inner remainder by additive
  algebra and `axModAdd` to `u %ᵉ (eexp2 (u +ᵉ .zero) +ᵉ .zero)`,
  then `axModLt` from the domination instance at `e := u +ᵉ 0`,
  `a := u`; outer remainder by `axModLt` from the same instance
  via additive algebra. Equivalently: the `esubAt_of_add`
  instance at `u = u +ᵉ 0`.
- `pred_succ` (verified reduction): inner remainder by additive
  algebra (`2^E +ᵉ .succ u = u +ᵉ .succ (…)` needs only
  Phase-1 algebra and the domination instance at
  `e := .succ u +ᵉ one`, `a := u`); outer by additive algebra
  alone (`2^E +ᵉ .succ u = u +ᵉ .succ (eexp2 E')` exactly).
- Cluster entry (open): Goodstein derives (1) from his axiom
  `a ∸ Sb = (a∸b) ∸ 1` and (2) from (1) plus `Sa ∸ 1 = a`
  ([Goo54] p. 249), and conversely `sub_succ` follows from (1)
  and (2) by `uniq` on `u` with a parameter-using step
  functional ignoring the previous-value slot (the F-premise
  closes by (2), the G-premise by (1) plus `pred_succ`). The
  three are thus mutually derivable, but no member of
  {(1), (2), `sub_succ`} has a verified derivation from the
  template alone: each candidate `uniq` step is an instance of
  another member. Candidate routes, in order:
  (i) derive (2) directly at the `esubAt` level by E₃ on one
  variable with the other as parameter, using the template laws
  to evaluate both sides at `.zero` and at successors;
  (ii) an exponent-stability lemma
  (`esubAt e u v = esubAt e' u v` given domination of both
  exponents), which would let inductions fix one exponent;
  (iii) transpose Goodstein's two-variable induction I₂
  ([Goo54] p. 253) — costly, as its derivation consumes (13),
  (16), and (17). If all routes fail, the staged exit of §9
  applies.

### 7.5 Mod-of-multiple

Object-level analogue of `Nat.mul_add_mod`, stated with the
multiplier as the second `*ᵉ`-argument (matching the
multiplier-second form in which the three consuming identity
proofs use it, after the `Nat.mul_comm` rewrite in
`pow_identity`): `(m *ᵉ k +ᵉ r) %ᵉ m = r %ᵉ m`, by `uniq` on
`k` (stated at scope `n + 1` with `k` as variable 0 and
instantiated by `Derivable.inst`). Base: `mul_zero` plus
`zero_add`. Step: `mul_succ` (`m *ᵉ Sk = m *ᵉ k +ᵉ m`) plus
`axModAdd` and additive algebra.

The multiplicative cluster entry (Phase 4b) is open: the
squaring law mirrors `sq_identity`, whose `key` step peels the
open `∸`-shaped multiplier `2^n ∸ n` by exactly this law, whose
step consumes `mul_succ`, whose derivation through `edmul`
consumes the squaring law. Candidate route: derive `mul_succ`
not through the squaring law but by mirroring `numeral_mul`'s
composition at open terms with the `edmul` recursion
`edmul u (Sv) = edmul u v +ᵉ u +ᵉ u` derived first — whose own
site analysis is part of the obligation. If no entry member is
derivable, the staged exit of §9 applies.

### 7.6 Powers

- `pow_zero` (verified reduction, no `pow_mod_rep` needed): the
  exponent argument reduces by `mul_zero`, `zero_add`, and
  numerals to `eexp2 .zero = one`; the site `1 %ᵉ (2^{u+1} ∸ u)`
  closes by `esubAt_of_add` from the domination instance
  `2^{u+1} = u +ᵉ .succ (.succ t)` and `axModLt`.
- `pow_succ`, `div_succ`: mirror `pow_identity` (via the
  transposed `pow_mod_rep`: witness by explicit term, recursion
  equation by `uniq`, mod-peeling by §7.5) and `div_identity`
  (multiplicative algebra plus §7.5). Routes sketched only;
  these are the deepest targets and depend on every prior layer.

### 7.7 The recovery equation

Goodstein's (17) `a +ᵉ (b ∸ᵉ a) = b +ᵉ (a ∸ᵉ b)` is not on the
critical path: the `∸`-shaped modulus conversions need only
`esubAt_of_add` (§7.2). Its transposition is blocked before
Phase 4a in any case — the proof ([Goo54] pp. 251–252) consumes
`b ∸ 0 = b` and (2), and introduces an auxiliary function φ by a
fresh recursive definition, a move unavailable with `eraDefs`
fixed (φ must become an explicit basis term with derived
recursion equations). After Phase 4a it becomes a candidate
corollary; it is recorded here as out of scope.

## 8 Approaches explored and rejected

Recorded so they are not retried:

- `uniq` on the domination equation with `H := prev +ᵉ prev`
  requires the witness recursion `w(Sa) = w(a) +ᵉ w(a) +ᵉ a`,
  itself an `esub` equation — circular before the `∸` laws exist.
- `uniq` on `u %ᵉ eexp2 u = u` directly: the step is a
  mod-of-successor-dividend equation that the three mod axioms do
  not support.
- Two-variable domination by `uniq` on either variable: the base
  remains open in the other variable and poses the same problem.
- Deriving domination from (17) ([Goo54] pp. 251–252) as the
  primary route: circular — the proof of (17) consumes
  `b ∸ 0 = b` and (2), both Phase-4 targets that themselves
  require domination, and its auxiliary function φ has no
  counterpart under fixed `eraDefs` (§7.7).

## 9 Acceptance criteria

Staged:

- Phases 0–3 unconditional: the named theorems of §6 Phases 0–3,
  including four of the eleven §4 statements (`pred_zero`,
  `mul_zero`, `div_zero`, `zero_div`).
- Phase 4: the remaining seven §4 statements, verbatim. The
  domination family (§7.3), the subtraction cluster entry
  (§7.4), and the multiplicative cluster entry (§7.5) have no
  verified derivation at spec time; if implementation reaches a
  genuine impasse on any of the three, the defined exit is to
  pause and
  report (stuck-and-ask template of
  `.claude/rules/lean-coding.md`) with the partial results
  committed and the obstruction documented — not to extend the
  axiom set, which is excluded by recorded decision.
- Throughout: `eraDefs` unchanged; `bash scripts/pre-commit.sh`
  green; axioms of every new theorem contained in
  {`propext`, `Quot.sound`} (verified per declaration;
  `scripts/check-axioms.sh` at pre-push); `Era.lean` stays
  core-Lean-only (no mathlib import).

Optional cleanup if time permits: re-derive
`numeral_sub/mul/div/pow` as corollaries of the open laws.

Execution outcome (2026-06-12): Phases 0–3 and the §7.2
`esubAt` template completed, committed, axiom-clean — four of
the eleven statements delivered. The domination family (§7.3)
reached the staged-exit impasse; the obstruction is documented
in `2026-06-12-era-open-laws-domination-impasse.md`, which the
`uniq` base case and F-step premise derive while the G-step
premise (the `esub` doubling recursion) closes the circle. The
seven domination-dependent statements await the user decision
recorded in that report; the axiom set was not extended.

## 9a Design revision: restore truncated subtraction as a primitive

Decided 2026-06-12 after the domination impasse (§9, the
impasse report). The minimal three-element basis is faithful to
the substitution-basis literature (Marchenkov 2007; [PSS26])
for *expressibility* — every Kalmár-elementary function is a
composition term over `{+, mod, 2^x}` — but is in tension with
Goodstein's logic-free *proof* calculus, which draws its power
from each operation carrying its own recursion equations as
axioms. Eliminating `∸` as a function silently eliminated the
order relation it encoded (`a ≤ b ⟺ a ∸ b = 0`), and order is
not equationally recoverable from the three basis recursions
without the witness-circularity of §2–§4 of the impasse report.

Resolution: keep the basis finite and close to minimal, but
restore truncated subtraction as a fourth primitive with its
natural recursion axioms, while leaving multiplication, division,
and two-variable exponentiation derived (unlike the
pre-reduction five-primitive basis at `daab65a9`). The basis
becomes `{x+y, x mod y, 2^x, x ∸ y}`.

### Basis and axioms

- `EraB` gains a constructor `tsub` of arity 2; `∸ᵉ` denotes the
  primitive application.
- Four defining equations, verbatim from `daab65a9`:
  `x ∸ 0 = x` (`axSub0`), `x ∸ S y = (x ∸ y) ∸ 1` (`axSubS`),
  `0 ∸ 1 = 0` (`axPred0`), `S x ∸ 1 = x` (`axPredS`).
- `eraInterp` interprets `tsub` as `Nat` truncated subtraction;
  `eraDefs_sound` discharges the four equations by `omega`. The
  generic soundness, consistency, and closed-completeness
  theorems generalize unchanged (they quantify over `defs`).

### Consequence: the impasse dissolves

With `∸` primitive, Goodstein's 1954 development applies: the
recovery equation (17) `a + (b ∸ a) = b + (a ∸ b)` is derived
from the `∸` recursion axioms, the `+` axioms, `uniq`, and
`ext_succ`; domination then follows by induction. The four
subtraction-cluster deliverables become axiom instances
(`derivable_sub_zero`, `derivable_sub_succ`,
`derivable_pred_zero`, `derivable_pred_succ`). `pow_zero` lands
once domination is available (§7.6). The multiplicative cluster
(`mul_succ`, `pow_succ`, `div_succ`) carries a separate
squaring↔multiplication bootstrap (§7.5) that domination does
not by itself break, since multiplication remains derived through
the `esq`/`edmul` chain; those three are derived where the
bootstrap permits and otherwise reported.

### The redundancy theorem

The former `esub` body — the Mazzanti mod-expression — is
retained as a named `def subFormula` over `{+, mod, 2^x}`. The
object-language theorem

```text
Derivable eraDefs ⟨x ∸ᵉ y, subFormula x y⟩
```

is proved (its proof needs only domination, now derivable, and
no multiplication). It expresses the redundancy of `∸` as a
*basis* element — it equals a composition over the other three —
while the four `∸` axioms witness that `∸` is *not* redundant as
part of the axioms: the composition's correctness is provable
only once `∸`'s recursion is assumed. `subFormula` also remains
available to rewrite the primitive into its closed form (and
back) via the redundancy theorem where a proof benefits.

The derived operations (`esq` uses only `+/mod/2^x`; `edmul`,
`ediv`, `epow`) are re-pointed so `∸ᵉ` is the primitive
throughout; `subFormula` is used solely for the redundancy
theorem and as an optional rewrite target.

## 10 Scope guardrails

- The `Derivable` rules are unchanged; the only axiom-set change
  is the §9a restoration of the four `∸` equations (sound in the
  standard model, discharged in `eraDefs_sound`).
- No mathlib import into `Era.lean`.
- The eleven statements are fixed by the pre-reduction interface;
  weakening them to ease implementation is excluded
  (non-negotiable-interface rule of
  `.claude/rules/lean-coding.md`).
- Statement-preserving strengthening of supporting lemmas (e.g.
  proving a law at general `defs` containing the basis equations,
  or at a general exponent as in §7.2) is permitted.
- Goodstein's (17) and the induction schemata I₁–I₃ are in scope
  under §9a as the route to domination and the redundancy
  theorem.

## 11 References

- [Goo54] R. L. Goodstein, "Logic-free formalisations of
  recursive arithmetic", Math. Scand. 2 (1954) 247–261.
  Open access: <https://www.mscand.dk/article/view/10412>.
  Schemata K, U₁, E₁, E₂ (p. 248), E₃ (p. 251); defining axioms
  for `∸`, `·` and equations (1)–(6) (p. 249); (7)–(15.1)
  (p. 250); (16), (17), (17.1) (pp. 251–252); I₁–I₃
  (pp. 252–253).
- [PSS26] M. Prunescu, L. Sauras-Altuzarra, J. M. Shunia, "A
  Minimal Substitution Basis for the Kalmár Elementary
  Functions", J. Logic & Computation (2026), arXiv:2505.23787.
  Lemmas 2–3 (truncated subtraction, division).
- `GebLean/Era.lean` landmarks: the `uniq` rule and the example
  derivation `0 + x = x`; section "The Mazzanti operations,
  derived"; the `Nat`-level identities `sq_identity`,
  `tsub_identity`, `dmul_identity`, `div_identity`,
  `pow_identity` with their `Nat.mod_eq_of_lt` sites.
- Pre-reduction statements: git revision `daab65a9`.
