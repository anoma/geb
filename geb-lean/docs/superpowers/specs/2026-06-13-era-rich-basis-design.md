# Convenient rich-basis ERA with object-level redundancy — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Scope and goal](#1-scope-and-goal)
- [2 Decision history](#2-decision-history)
- [3 Basis and axioms](#3-basis-and-axioms)
- [4 Soundness and categoricity](#4-soundness-and-categoricity)
- [5 Deliverable: the five redundancy theorems](#5-deliverable-the-five-redundancy-theorems)
- [6 Method and disposition of the existing layer](#6-method-and-disposition-of-the-existing-layer)
- [7 The recovery problem](#7-the-recovery-problem)
- [8 Milestones](#8-milestones)
- [9 File, bookmark, and naming](#9-file-bookmark-and-naming)
- [10 Transcription versus novel](#10-transcription-versus-novel)
- [11 Acceptance criteria](#11-acceptance-criteria)
- [12 Scope guardrails](#12-scope-guardrails)
- [13 References](#13-references)

<!-- END doctoc -->

## 1 Scope and goal

In `GebLean/Era.lean` (the logic-free equation calculus of the
Skolem–Curry–Goodstein tradition), replace the near-minimal basis
`{add, mod, pow2, tsub}` with a convenient finite basis of seven
primitives, each carrying its own recursion axioms, then derive the
five superposition identities of Prunescu–Sauras-Altuzarra–Shunia (the
"Further examples" of the Wikipedia article on elementary recursive
functions) as open `Derivable` equations inside ERA.

The pivot rests on one observation: "logic-free" requires a finite
basis, not a minimal one. The minimal three-element basis
`{add, mod, pow2}` is computationally minimal but every operation
beyond the three generators must be derived rather than defined, and
that derivation incurs a minimization cost — deriving, over
`{add, mod, pow2}`, recursion laws that were axioms when the operations
were primitive. The convenient finite basis pays no such cost: every
operation is primitive with its own axioms.

The deliverable splits into two parts with different risk profiles:

- A recovery-independent result: a sound, categorical, finite
  logic-free ERA over the seven primitives (§3, §4). This stands on its
  own and depends on no unsolved problem.
- A recovery-gated result: the object-level redundancy theorems that
  recover the minimal-basis result inside ERA (§5). These rest on
  domination facts discharged by the recovery equation (§7), the same
  problem the prior line did not resolve; the recovery strength each
  theorem needs is fixed at its checkpoint (§7, §8).

## 2 Decision history

The minimal-basis line (`feat/era-open-laws`) established the calculus
and proved seven of eleven open recursion laws, then stopped on a
structural obstruction: the remaining four (`mul_succ`, `pow_zero`,
`pow_succ`, `div_succ`) reduce to the recovery equation
`b ≤ c ⟹ b + (c ∸ b) = c`, not reachable from elementary `∸`-algebra
alone. The analysis is in
`docs/superpowers/specs/2026-06-12-era-open-laws-domination-impasse.md`.

The convenient-basis decision was recorded at the close of that line.
This document is its design realization. The basis combines material
from two already-committed, green states: Mazzanti's five operations
`{add, tsub, mul, div, pow}` and their soundness proof from commit
`daab65a9` ("Closed-term ERA consistency"), and the two PSS generators
`{mod, pow2}` from the current head. The two states use different
internal representations (per §3), so the work transcribes the
`daab65a9` axioms and `Nat`-soundness lemmas into the head's
representation rather than concatenating two files.

User decisions taken during brainstorming:

- The five "Further examples" are to be proven as open object-level
  `Derivable` theorems, not merely numeral-level witnesses. This
  commits the project to proving the recovery equation; recovery is not
  made easier by the basis enrichment (§7).
- The recovery problem is attempted by its narrowest sufficient proof
  first (direct domination-with-witness), escalating only as the
  division and exponentiation redundancy proofs force it.
- The axiom set is to be certified sufficient by categoricity theorems
  (§4).
- The work continues the linear history, stacked on
  `feat/era-open-laws` as a new bookmark; it is not a divergent branch.

## 3 Basis and axioms

Seven primitives, partitioned by role.

| Role | Symbols | Arity |
| --- | --- | --- |
| Generators (irreducible reduction target) | `add`, `mod`, `pow2` | 2, 2, 1 |
| Convenience (provably redundant) | `tsub`, `mul`, `div`, `pow` | 2, 2, 2, 2 |

The eighteen defining equations. Generator axioms are transcribed from
the current head; convenience axioms are transcribed from `daab65a9`,
with one refinement: `axDivS` spells the remainder as the primitive
`x mod S y` (available now that `mod` is in the basis) rather than
`daab65a9`'s `x ∸ S y · (x / S y)`.

Generators:

```text
axAdd0    x + 0          = x
axAddS    x + S y        = S (x + y)
axMod0    x mod 0        = x
axModLt   x mod (x + S y) = x
axModAdd  (x + y) mod y  = x mod y
axPow2Z   2^0            = 1
axPow2S   2^(S x)        = 2^x + 2^x
```

Convenience:

```text
axSub0    x ∸ 0          = x
axSubS    x ∸ S y        = (x ∸ y) ∸ 1
axPred0   0 ∸ 1          = 0
axPredS   S x ∸ 1        = x
axMul0    x · 0          = 0
axMulS    x · S y        = x · y + x
axPow0    x ^ 0          = 1
axPowS    x ^ S y        = x^y · x
axDivZ    x / 0          = 0
axDiv0    0 / S y        = 0
axDivS    S x / S y      = x / S y + (1 ∸ (y ∸ (x mod S y)))
```

`pow2` retains the `x + x` form for `2 · pow2 x` because `mul` is a
convenience primitive, not available to a generator's axiom; the
reconciliation `pow2 x + pow2 x = 2 · pow2 x` is a downstream fact.

Representation. The current head defines one smart constructor per
operation (`eadd`, `emod`, `eexp2`, `etsub`) with one `subst`-commutation
and one congruence lemma each, and binds the infix notation. This design
keeps that representation and adds three new per-operation constructors
for the new primitives (`emul`, `ediv`, `epow`), each with its own
`subst` and congruence lemma and bound to the corresponding infix. The
generic calculus (`Tm`, `subst`, the clone laws, `Eqn`, `Defs`,
`Derivable`, the derived rules, `eval`, `Derivable.sound`) is unchanged.
The `daab65a9` representation collapses the six binary symbols onto a
single `bin` constructor; adopting that here would rewrite the head's
existing proof layer, so it is out of scope (§12). The head renames its
base-two exponentiation symbol — the `EraB` constructor `exp2` to
`pow2`, the smart constructor `eexp2` to `epow2`, the axioms
`axExp0`/`axExpS` to `axPow2Z`/`axPow2S` — with the equations unchanged.
New `.lean` lines obey the 100-character limit, so `axDivS` and similar
long terms are wrapped.

## 4 Soundness and categoricity

`eraInterp` maps each symbol to the corresponding `Nat` operation
(`+`, `%`, `2^·`, `-`, `·`, `/`, `^`); `eraDefs_sound` proves all
eighteen axioms hold of it, combining the head's generator proof with
`daab65a9`'s `mul`/`pow`/`div` proof. Because the spec's `axDivS`
spells the remainder as `x mod S y`, `daab65a9`'s `succ_div_succ`
lemma — stated with the remainder `x ∸ S y · (x / S y)` — is not
reusable verbatim; the `div` step of `eraDefs_sound` adds a rewrite
identifying `x % S y` with that term.

Because the axioms are invented here — no logic-free equational ERA
exists in the literature — soundness alone does not certify them. The
complementary guarantee is categoricity: the intended operations are
the only `Nat` functions satisfying the axioms.

- Per-operation uniqueness lemmas: for each symbol `f`, any
  `Nat`-valued function satisfying `f`'s axioms equals the intended
  operation, given that the operations `f`'s axioms depend on are
  already pinned.
- Capstone `eraInterp_unique`: any interpretation `I` satisfying all
  eighteen axioms equals `eraInterp`, by composing the per-operation
  lemmas in dependency order: `add` (axioms mention only `add`);
  `tsub`/`pred`; `mul` (axMulS mentions `add`); `pow` (mentions `mul`);
  `pow2` (axPow2S mentions `add`); `mod` (mentions `add`); `div`
  (axDivS mentions `add`, `mod`, and `tsub`).

For the five structurally-recursive operations (`add`, `mul`, `pow`,
`tsub`/`pred`, `pow2`) the axioms are exactly parallel to Lean's `Nat`
recursion, so uniqueness is a structural induction matching the inner
induction the `uniq` case of `Derivable.sound` runs. For `mod` and
`div`, Lean's definitions are well-founded (with a conditional), so
there is no literal structural parallel; the axioms are equational
characterizations, and the categoricity theorem is where their
sufficiency is earned, by a well-founded argument on the dividend (the
meta-level analogue of the head's `numeral_mod`, which itself needs
`termination_by`/`decreasing_by`):

- `mod`: `axModLt` anchors the below-divisor regime (`x < y ⟹
  x mod y = x`), `axModAdd` supplies periodicity, and induction on the
  dividend closes it. All three axioms are necessary.
- `div`: `axDivZ` (divisor zero), `axDiv0` (base), and `axDivS` (the
  structural recursion on the dividend) jointly determine `div` by
  induction on the dividend, given `add`, `mod`, and `tsub` pinned.

Soundness and categoricity together state: the standard model is the
unique model of `eraDefs`. Neither depends on the recovery equation, so
this result (with §3) is the recovery-independent base of the
deliverable.

This categoricity is the sense in which `mod` and `div` provably match
Lean's well-founded definitions: their `Nat`-level uniqueness is proven
with Lean's own well-founded induction. An object-level counterpart —
deriving their course-of-values recursion inside `Derivable` — is
reachable but rests on bounded sum and product (the history-coding that
reduces course-of-values recursion to the single-variable `uniq`) and
the `tsub` order algebra. ERA has no recursion scheme and no binders, so
bounded sum and product are not basis symbols: each is a metalanguage
term-former sending a body term to a composite ERA term, its recursion a
derived theorem downstream of recovery (§7). That object-level
characterization is a deferred follow-on (§12); the categoricity match is
what the base result requires.

## 5 Deliverable: the five redundancy theorems

Each convenience primitive equals an encoding over the generators
(plus `tsub`), as an open `Derivable` equation. The encodings and their
`Nat`-level identities already exist in the head file (currently as the
derived-operation definitions); their disposition is in §6.

| # | Theorem | Statement |
| --- | --- | --- |
| E1 | `derivable_sub_eq_subFormula` | `x ∸ᵉ y = subFormula x y` |
| E2 | `derivable_two_mul_eq_edmul` | `numeral 2 *ᵉ (x *ᵉ y) = edmul x y` |
| E3 | `derivable_div_eq_divFormula` | `x /ᵉ y = divFormula x y` |
| E4 | `derivable_mul_eq_mulFormula` | `x *ᵉ y = mulFormula x y` |
| E5 | `derivable_pow_eq_powFormula` | `x ^ᵉ y = powFormula x y` |

The encodings:

```text
subFormula x y  = ((2^(x+y) + x) mod (2^(x+y) + y)) mod (2^(x+y) + x)
esq x           = 2^(x+x) mod (2^x + x)
edmul x y       = esq (x + y) ∸ (esq x + esq y)
divFormula x y  = edmul (S x) (x ∸ (x mod y)) mod (edmul (S x) y ∸ 1)
mulFormula x y  = divFormula (edmul x y) (numeral 2)
powFormula x y  = 2^((x·y + x + 1)·y) mod (2^(x·y + x + 1) ∸ x)
```

Generator content of each encoding: `subFormula` and `esq` use only
`{add, mod, pow2}`; `edmul`, `divFormula`, `mulFormula` additionally use
`tsub`; `powFormula` additionally uses `mul` (the `·` in its exponents).
`divFormula` does not use `mul`.

Pure-generator closure. Substituting E1 into E2–E5 eliminates the
residual `tsub`; substituting E4 into E5's `powFormula` eliminates the
residual `mul`. The resulting corollaries express every convenience
operation over the bare `{add, mod, pow2}`. That transitive closure is
the object-level statement of PSS minimality, proven inside ERA.

Each theorem in this section rests on a domination fact that the
recovery equation (§7) discharges, so the section is sequenced after M2
(§8). The recovery strength each theorem requires — and, for E2, whether
its step reduces to the recovery-free `derivable_add_sub_cancel_left` —
is fixed at that theorem's checkpoint. If recovery is not obtained within
budget, the theorems that need it do not land, and the deliverable is
the §3–§4 result plus a documented obstruction (§11).

## 6 Method and disposition of the existing layer

Each redundancy theorem is proven by one move: show the encoding
satisfies the primitive's own recursion axioms, then `uniq` (or
`ext_succ`) against those axioms forces equality. For example, E4
reduces to deriving `mulFormula x 0 = 0` and
`mulFormula x (S y) = mulFormula x y + x`; since `mul` satisfies
`axMul0`/`axMulS`, `uniq` concludes `mul = mulFormula`. Having the
primitives present with axioms is what makes the recursion-matching
expressible — `uniq` needs both solutions to exhibit, and now both
exist. It does not make the recovery sublemma easier; that is addressed
separately in §7.

- Base cases are the open zero-laws at recursion-variable `0` with the
  parameter still open (for E4, `x *ᵉ 0 = mulFormula x 0` for open `x`),
  not closed `numeral_*` facts. The head already proves the open
  encoding zero-laws (`derivable_edmul_zero`, and the analogous laws for
  the division and multiplication encodings); those are the base-case
  inputs.
- Step cases consume the domination/recovery facts; this is why E1 is
  proven first and the recovery proof precedes it.
- The `Nat`-level identities already proven (`subFormula_eval`,
  `sq_identity`, `dmul_identity`, `div_identity`, `pow_identity`) are
  the blueprints for the object-level step inductions: the arithmetic is
  verified in `Nat`; the work is lifting each derivation to `Derivable`.

Disposition of the head's derived-operation layer. The head currently
defines `mul`/`div`/`pow` as derived operations (`emul`, `ediv`, `epow`)
bound to `*ᵉ`/`/ᵉ`/`^ᵉ`, with congruence and numeral lemmas over those
derived definitions. Under the new basis those notations rebind to the
new primitive constructors. The transition:

- The derived bodies become the named encodings: `ediv`'s body becomes
  `divFormula`, `epow`'s becomes `powFormula`, and `emul`'s
  (`⌊2xy/2⌋`) becomes `mulFormula`. `edmul`, `esq`, `subFormula` keep
  their names.
- The names `emul`/`ediv`/`epow` are reused for the new primitive
  constructors, carrying the infix notation.
- The derived-operation congruence and numeral lemmas
  (`numeral_mul`/`div`/`pow` over the old derived ops) split: the
  encoding-level versions are renamed (`numeral_mulFormula`, etc.) and
  serve as redundancy base-case inputs; the primitive-level
  `numeral_mul`/`div`/`pow` are re-derived from the new axioms, with
  `daab65a9`'s versions as templates (`numeral_div` there needs
  `succ_div_succ` and a nested induction).
- `numeral_mod` and `numeral_exp2` (head, over the primitives `mod`,
  `pow2`) survive; `numeral_mod`'s well-founded proof is preserved under
  the surviving per-operation `mod` lemmas.
- Trivial derived corollaries over the old derived ops (for instance
  `u /ᵉ 0 = 0`) are replaced by direct axiom instances under the
  primitive basis.

## 7 The recovery problem

The recovery equation `b ≤ c ⟹ b + (c ∸ b) = c` has a trivial witnessed
form (`c = b + d ⟹ c ∸ b = d`, by the proven
`derivable_add_sub_cancel_left`); the difficulty is producing the
witness `d` for an un-witnessed domination such as `x ≤ 2^(x+y)`, which
requires deriving `2^(x+y) = x + (…)` by induction.

This problem is unchanged by the basis enrichment. Recovery concerns
`+` and `∸` only; `∸` is already primitive at the head, with its four
axioms, and the recovery obstruction recorded for the prior line is over
that same primitive `∸`. Adding `mul`/`div`/`pow` does not touch it. The
user has chosen to invest in solving it; the chosen route attempts the
narrowest sufficient proof first, escalating as forced:

1. Approach 2 (chosen, attempted first). Derive domination-with-witness
   directly — `x + (2^e ∸ x) = 2^e` and the strict `2^e = x + S p` form
   that `derivable_esubAt_of_add` consumes — by an induction tailored to
   the exponential, reusing the domination lemmas already built
   (`derivable_self_sub_add`, `derivable_add_sub_add_left`,
   `derivable_one_le_two_pow`). The minimal proof sufficient for E1.
2. Approach 1 (escalation). The general symmetric identity
   `a + (b ∸ a) = b + (a ∸ b)`, by `uniq` on the first argument. The
   first-solution step collapses via
   `sub_succ`/`succ_add`/`add_sub_cancel_left`; the difficulty isolates
   into the single lemma `(b + (a ∸ b)) ∸ a = b ∸ a`, proven by a
   dedicated nested `uniq`.
3. Approach 3 (fallback). Transcribe Goodstein's *Recursive Number
   Theory* bounded-sum order-algebra development. In ERA bounded sum is
   not a primitive scheme but a metalanguage term-former (body term to
   composite ERA term, §4), so this route first builds that term-former
   and its derived recursion — shared infrastructure with the future
   `ERMor1`-equivalence work, hence not throwaway, but most likely itself
   downstream of recovery. It is therefore the last resort, not the
   default.

The strength of Approach 2's output required downstream is not yet
pinned: E3 (division) and E5 (exponentiation) step inductions may need
the general symmetric identity (Approach 1) rather than the narrow
`2^e`-tailored form (Approach 2). That dependency is resolved at the M2
and M6/M7 checkpoints.

Terminal contingency. If recovery is not obtained after Approach 3
within budget, the redundancy section does not land. The deliverable is
then the §3–§4 result (a sound, categorical, finite ERA) plus a
documented obstruction; the spec is amended to record this and the
bookmark merges that result. Recovery (M2) is the same problem the prior
line did not resolve, and its budget is set with that in view.

## 8 Milestones

Each milestone is gated by the pre-commit triad
(`bash scripts/pre-commit.sh`), the axiom-clean check (`propext`,
`Quot.sound`, `Classical.choice` only), and a checkpoint commit.

| M | Content | Risk |
| --- | --- | --- |
| M0a | Rename `exp2`→`pow2`; rename derived bodies to `subFormula`/`divFormula`/`mulFormula`/`powFormula`; rebind notation | moderate |
| M0b | Add `mul`/`div`/`pow` primitives, constructors, `subst`/congruence lemmas, seven convenience axioms; eighteen-axiom `eraDefs` | moderate |
| M0c | Merged `eraDefs_sound` (with the `axDivS` remainder rewrite) and re-derived primitive `numeral_mul`/`div`/`pow` | moderate |
| M1a | Categoricity for the structural operations | low |
| M1b | Categoricity for `mod`/`div` and the `eraInterp_unique` capstone | moderate |
| M2 | Recovery, Approach 2 (exploratory) — gate; escalation decision recorded | high |
| M3 | E1 (proven first; validates recovery suffices) | high |
| M4 | E2 | moderate |
| M5 | E4 | moderate |
| M6 | E3 | high |
| M7 | E5 | high |
| M8 | Pure-generator closure corollaries (substituting E1, E4) | moderate |

M0–M1 are recovery-independent and constitute the base result (§11).
M3–M8 are gated on M2.

## 9 File, bookmark, and naming

- File: monolithic `GebLean/Era.lean`, consistent with the current
  layout. The file grows past ~2000 lines, which signals a future
  module split (`Era/Core`, `Era/Basis`, `Era/Algebra`,
  `Era/Redundancy` under an `Era.lean` index); that split is a distinct
  concern, deferred (§12).
- Content order: generic core → ERA instance and eighteen axioms →
  `eraInterp`/`eraDefs_sound` → categoricity → numeral, consistency,
  closed-completeness → additive and order algebra → recovery proof →
  encodings → E1–E5 and pure-generator corollaries.
- Bookmark: a new bookmark stacked linearly on `feat/era-open-laws`.
- Naming: primitives carry the infix notation (`+ᵉ`, `%ᵉ`, `∸ᵉ`, `*ᵉ`,
  `/ᵉ`, `^ᵉ`) and unary `pow2`; encodings use the `…Formula`/`esq`/
  `edmul` names; redundancy theorems use the `<op>_eq_<encoding>` form
  under the file's `derivable_` prefix.

## 10 Transcription versus novel

Per the cite-the-literature rule:

- Generator axioms (`axAdd0`/`axAddS`, `axMod0`/`axModLt`/`axModAdd`,
  `axPow2Z`/`axPow2S`): transcription of Lean's `Nat` recursions and the
  PSS generators (arXiv:2505.23787).
- Convenience axioms (`axSub0`/`axSubS`/`axPred0`/`axPredS`,
  `axMul0`/`axMulS`, `axPow0`/`axPowS`, `axDivZ`/`axDiv0`):
  transcription of `daab65a9` (themselves parallel to Lean's `Nat`
  recursions and Mazzanti's basis, Mazzanti 2002).
- `axDivS`: transcription of `daab65a9` modified to use the primitive
  `mod`; the modification is marked novel.
- E1–E5: transcription of PSS's "Further examples" (arXiv:2505.23787,
  Lemma 2 for subtraction, Lemma 3 for division), lifted from `Nat`
  identities to object-level `Derivable` equations.
- Pure-generator closure corollaries: transcription of the PSS
  minimality result to the object level.
- Recovery: transcription of Goodstein's order algebra (Goodstein 1954,
  equations (2)–(10); *Recursive Number Theory* 1957 for the
  bounded-sum development).
- Categoricity (per-operation uniqueness lemmas and `eraInterp_unique`):
  novel artifacts, by a standard meta-level uniqueness technique.

## 11 Acceptance criteria

- `lake build`, `lake test`, `lake lint` pass; the file is free of
  `sorry`, `admit`, and underscores; new lines obey the 100-character
  limit.
- `scripts/check-axioms.sh` reports only `propext`, `Quot.sound`,
  `Classical.choice` for every new declaration.
- Base result (required for the bookmark to merge): eighteen named
  axioms; `eraDefs_sound`; `eraInterp_unique` with its per-operation
  uniqueness lemmas. This part is recovery-independent.
- Redundancy result (gated on recovery): E1–E5 as open `Derivable`
  theorems and the pure-generator closure corollaries. If recovery is
  not obtained, the redundancy result is recorded as a documented
  obstruction and the spec is amended; it is not silently reduced to a
  subset. No partial set of E1–E5 is accepted as "complete" without that
  record.
- The retained encodings and surviving `numeral_*`/`*_identity` lemmas
  remain green under the new primitive basis; the `eraDefs` membership
  witnesses are re-verified for all eighteen axioms.

## 12 Scope guardrails

- No `bin` constructor refactor on this bookmark: the head keeps its
  per-operation constructors. The `bin` collapse is a separate
  refactor, deferred.
- No module split on this bookmark (deferred).
- No changes to the generic calculus.
- PSS function-level expressibility (Marchenkov's theorem) remains a
  citation; it is not formalized here.
- The double product `2xy` is the E2 helper, not a separate primitive.
- Bounded sum and product, and the object-level course-of-values
  recursion they enable (including the object-level `mod`/`div`
  well-founded-recursion characterization of §4), are deferred: they are
  metalanguage term-formers shared with the future `ERMor1`-equivalence
  work, built downstream of recovery, not on this bookmark.

## 13 References

- R. L. Goodstein, "Logic-free formalisations of recursive arithmetic",
  *Math. Scand.* 2 (1954) 247–261; *Recursive Number Theory*
  (North-Holland, 1957).
- S. Mazzanti, "Plain Bases for Classes of Primitive Recursive
  Functions", *MLQ* 48:1 (2002) 93–104.
- M. Prunescu, L. Sauras-Altuzarra, J. M. Shunia, "A Minimal
  Substitution Basis for the Kalmár Elementary Functions", *J. Logic &
  Computation* (2026), arXiv:2505.23787 (Lemma 2, Lemma 3, and the
  "Further examples"). Citation matches the `Era.lean` module
  docstring.
- Wikipedia, "Elementary recursive function", § Superposition bases for
  elementary functions, "Further examples",
  <https://en.wikipedia.org/wiki/Elementary_recursive_function>.
- `docs/superpowers/specs/2026-06-12-era-open-laws-design.md` and
  `docs/superpowers/specs/2026-06-12-era-open-laws-domination-impasse.md`.
