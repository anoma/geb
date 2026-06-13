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
  - [Phase 4 — laws requiring domination](#phase-4--laws-requiring-domination)
- [7 Object-level exponential domination](#7-object-level-exponential-domination)
- [8 Approaches explored and rejected](#8-approaches-explored-and-rejected)
- [9 Acceptance criteria](#9-acceptance-criteria)
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
| Predecessor/subtraction ladder: `(a∸b)∸1=(a∸1)∸b` (1), `Sa∸Sb=a∸b` (2), `a∸a=0` (3), `0∸a=0` (4) | Transcription | [Goo54] p. 249 |
| Recovery equation `a+(b∸a)=b+(a∸b)` (17), via (17.1) and E₃ | Transcription | [Goo54] pp. 251–252 |
| Recursion laws for `∸`, `·`, `/`, `^` as theorems over the three-element basis | Novel | Transposition of the `Nat`-level identities `tsub_identity`, `dmul_identity`, `div_identity`, `pow_identity`, `sq_identity` (already in `Era.lean`, after [PSS26] Lemmas 2–3) into object-level derivations |
| Object-level exponential domination family | Novel | §7; no published object-level derivation over this basis is known |
| Mod corollaries `0 mod v = 0`, `v mod v = 0` | Novel | Direct from `axMod0`/`axModLt`/`axModAdd` |

In [Goo54] the recursion equations for `∸` and `·` are *defining
axioms* (p. 249) and equations (1)–(5), (9), (13), (16), (17) are
derived from them. Here the direction is reversed: `∸`, `·`, `/`,
`^` are defined terms over `{+, mod, 2^x}`, so Goodstein's axioms
are the theorems to derive, and his derivations of (1)–(17) apply
only after their `∸`-axiom inputs have been established from the
`esub` unfolding. This reversal is where the novel content lies;
the additive layer (6)–(10) transcribes directly because the
addition axioms are shared.

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

Supporting theorems produced along the way (additive algebra, mod
corollaries, the extensionality rule, the domination family, the
recovery equation) are part of the public API and follow the same
naming scheme.

## 5 Method: translating `Nat`-level proofs to object level

Each open law is derived by unfolding the derived operation's
definition and mirroring its `Nat`-side identity proof
(`tsub_identity`, `div_identity`, `pow_identity`, `sq_identity`,
`dmul_identity`) step by step in the object calculus:

- `omega` steps become additive algebra from Phase 1 (§6);
- `Nat.add_mod_right` becomes an `axModAdd` instance;
- `Nat.mod_eq_of_lt h` becomes an `axModLt` instance plus a
  derivable shape conversion `divisor = dividend +ᵉ .succ t` for
  an explicit term `t` — the recurring requirement analysed in §7;
- case splits (`x < y` versus `x ≥ y`) are not expressible in the
  logic-free calculus; they are replaced by `uniq` inductions or
  by the extensionality rule E₃ (Phase 0).

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

- `derivable_zero_sub : 0 ∸ᵉ w = 0`: unfold `esub`; the inner
  remainder `(P +ᵉ 0) %ᵉ (P +ᵉ .succ w)` is an `axModLt` instance
  after `axAdd0`; the outer remainder is `mod_self`.
- `derivable_sub_self : t ∸ᵉ t = 0`: inner is `mod_self`, outer is
  `zero_mod`.
- `derivable_pred_zero` = instance of `zero_sub`.
- `derivable_edmul_zero : edmul t .zero = .zero` via
  `esq (t +ᵉ .zero) = esq t` (congruence plus `axAdd0`),
  `esq .zero = .zero` (numeral), `sub_self`.
- `derivable_mul_zero` from `edmul_zero` plus `ediv_congr` plus
  numerals.
- `derivable_div_zero` from `axMod0`, `sub_self`, `edmul_zero`,
  `zero_sub`, `axMod0`.
- `derivable_zero_div` from `zero_mod` (dividend `0`), `zero_sub`,
  numerals.

### Phase 4 — laws requiring domination

`sub_zero`, `pred_succ`, `sub_succ`, then `mul_succ`, `pow_zero`,
`pow_succ`, `div_succ`. Each requires the domination family of §7.
`sub_succ` additionally needs either an exponent-stability lemma
(the `esub` expression is unchanged when its exponent `x + y` is
padded, given domination) or the Goodstein ladder
`Sa ∸ Sb = a ∸ b` (2) followed by `(a ∸ b) ∸ 1 = (a ∸ 1) ∸ b` (1).

## 7 Object-level exponential domination

Every `Nat.mod_eq_of_lt` site needs
`divisor = dividend +ᵉ .succ t` derivable for an explicit term
`t`. All divisors in the derivation chain have the form
`2^E + s` with the dividend provably below `2^E`, so the recurring
requirement is the domination family `2^E = a +ᵉ .succ t` for `a`
a subterm-sum of `E`.

Plan: after Phase 3, derive domination as theorems. The central
target is Goodstein's recovery equation (17)
`a +ᵉ (b ∸ᵉ a) = b +ᵉ (a ∸ᵉ b)`, by his derivation
([Goo54] pp. 251–252) transposed to `esub` unfoldings; domination
for exponential `b` then follows. An intermediate target of
independent interest is the family
`eexp2 x = x +ᵉ .succ (eexp2 x ∸ᵉ .succ x)` (true in the standard
model since `x + 1 ≤ 2^x`): once derived, every shape conversion
follows by Phase-1 algebra alone, padding the exponent as
`2^(x+c) = (x+c) +ᵉ .succ d = x +ᵉ .succ (c +ᵉ d)`.

Risk: Goodstein's proof of (17) uses the `∸` axioms being derived
here, so the transposed derivation may itself reach a domination
prerequisite. If a genuine impasse is reached, pause and report
(stuck-and-ask template of `.claude/rules/lean-coding.md`) rather
than extending the axiom set; the latter option is excluded by
decision recorded in §9.

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

## 9 Acceptance criteria

- The eleven statements of §4, verbatim.
- `eraDefs` unchanged: the user has decided against extending the
  axiom set.
- `bash scripts/pre-commit.sh` green.
- Axioms of every new theorem exactly `propext`, `Quot.sound`
  (verified per declaration; `scripts/check-axioms.sh` at
  pre-push).
- `Era.lean` stays core-Lean-only (no mathlib import).

Optional cleanup if time permits: re-derive
`numeral_sub/mul/div/pow` as corollaries of the open laws.

## 10 Scope guardrails

- No new axioms, no change to `eraDefs`, no change to the
  `Derivable` rules.
- No mathlib import into `Era.lean`.
- The eleven statements are fixed by the pre-reduction interface;
  weakening them to ease implementation is excluded
  (non-negotiable-interface rule of
  `.claude/rules/lean-coding.md`).
- Statement-preserving strengthening of supporting lemmas (e.g.
  proving a law at general `defs` containing the seven equations)
  is permitted but not required.

## 11 References

- [Goo54] R. L. Goodstein, "Logic-free formalisations of
  recursive arithmetic", Math. Scand. 2 (1954) 247–261.
  Open access: <https://www.mscand.dk/article/view/10412>.
  Schemata K, U₁, E₁–E₃ (pp. 248, 251); equations (1)–(17)
  (pp. 249–252); recovery equation (17) and its derivation
  (pp. 251–252).
- [PSS26] M. Prunescu, L. Sauras-Altuzarra, J. M. Shunia, "A
  Minimal Substitution Basis for the Kalmár Elementary
  Functions", J. Logic & Computation (2026), arXiv:2505.23787.
  Lemmas 2–3 (truncated subtraction, division).
- `GebLean/Era.lean` landmarks: the `uniq` rule and the example
  derivation `0 + x = x`; section "The Mazzanti operations,
  derived".
- Pre-reduction statements: git revision `daab65a9`.
