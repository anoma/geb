# Adversarial review — era-open-laws design, round 1

Reviewer: fresh-context agent. Artifact:
`docs/superpowers/specs/2026-06-12-era-open-laws-design.md`.
Sources checked: `GebLean/Era.lean` (working tree), the
pre-reduction file at git revision `daab65a9`, the [Goo54] PDF
(pp. 247–254), and the project rules (`CLAUDE.md`,
`.claude/rules/*.md`, `docs/process.md`).

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Findings](#findings)
  - [R1-B1 (Blocker) — §7's divisor-shape claim is false](#r1-b1-blocker--7s-divisor-shape-claim-is-false)
  - [R1-M1 (Major) — the (17)-first domination route is circular](#r1-m1-major--the-17-first-domination-route-is-circular)
  - [R1-M2 (Major) — §5's translation table omits proof obligations](#r1-m2-major--5s-translation-table-omits-proof-obligations)
  - [R1-M3 (Major) — Phase 3 `zero_sub` sketch covers only successor `w`](#r1-m3-major--phase-3-zero_sub-sketch-covers-only-successor-w)
  - [R1-m1 (Minor) — §9 axiom criterion says "exactly"](#r1-m1-minor--9-axiom-criterion-says-exactly)
  - [R1-m2 (Minor) — style: value-laden label and colloquialism](#r1-m2-minor--style-value-laden-label-and-colloquialism)
- [Checks with no finding](#checks-with-no-finding)
- [Verdict](#verdict)

<!-- END doctoc -->

## Summary

| # | Severity | Title |
| --- | --- | --- |
| R1-B1 | Blocker | §7's claim "all divisors have the form `2^E + s` with the dividend provably below `2^E`" is false for the `esq`, `ediv`, and `epow` sites |
| R1-M1 | Major | The (17)-first domination route is circular as described, and Goodstein's auxiliary-function introduction (φ) has no counterpart in the fixed-`eraDefs` calculus |
| R1-M2 | Major | §5's translation table omits the mod-of-multiple step (`Nat.mul_add_mod`), the `pow_mod_rep` existential witness, and the multiplicative algebra the mirrored proofs use |
| R1-M3 | Major | The Phase 3 `zero_sub` sketch covers only successor `w`; `zero_div` depends on the missing zero case |
| R1-m1 | Minor | §9's "axioms … exactly `propext`, `Quot.sound`" overconstrains |
| R1-m2 | Minor | Style: "of independent interest" (§7), "along the way" (§4) |

## Findings

### R1-B1 (Blocker) — §7's divisor-shape claim is false

§7 states: "All divisors in the derivation chain have the form
`2^E + s` with the dividend provably below `2^E`, so the
recurring requirement is the domination family
`2^E = a +ᵉ .succ t` for `a` a subterm-sum of `E`."

Evidence, from the `Nat.mod_eq_of_lt` sites of the identity
proofs in `GebLean/Era.lean` that §5 designates as the proofs to
mirror:

- `div_identity` (lines 900–922): the site at line 922 (bound
  `hqM`, line 915) has dividend `x / (k + 1)` and modulus
  `2 * ((x + 1) * (k + 1)) - 1`. The modulus is not of the form
  `2^E + s`.
- `pow_identity` (lines 991–1006): the site at line 1006 (bound
  `hbound`, line 1003) has dividend `x ^ y` and modulus
  `2 ^ (x * y + x + 1) - x`. Not of the form `2^E + s`.
- `sq_identity` (lines 725–737): the site at line 737 (bound
  `hsq`) has modulus `2 ^ n + n` — the claimed form — but
  dividend `n * n`, which is not below `2^E = 2^n`: at `n = 2`,
  `n·n = 4 = 2^2`; at `n = 3`, `9 > 8`. The available bound is
  `n·n < 2^n + n` (`mul_self_lt_two_pow_add`, line 713).

(A further instance: the small-dividend branch of
`tsub_identity`, lines 835–838, has dividend `2^(x+y) + x`,
which is not below `2^(x+y)` either.)

Consequence: the shape conversions required at the `esq`,
`ediv`, and `epow` sites are `M = d +ᵉ .succ t` for moduli of
the forms `2^E ∸ x` and `2(x+1)y ∸ 1`, and for the dividend
`n·n` against `2^n + n` — none of which follows from the stated
family "by Phase-1 algebra alone". Phase 4's reduction of
`mul_succ`, `pow_zero`, `pow_succ`, and `div_succ` to "the
domination family of §7" is therefore unsupported, and §7's
analysis covers at most the `esub`-only laws (`sub_zero`,
`pred_succ`, `sub_succ`).

Fix: inventory the `Nat.mod_eq_of_lt` sites per identity with
their actual dividend/modulus shapes; state the conversion lemma
each one needs (including the `∸`-shaped moduli); give a
derivation route for each, or restructure Phase 4 around the
actual obligations.

### R1-M1 (Major) — the (17)-first domination route is circular

§7's risk note says the transposed derivation of (17) "may
itself reach a domination prerequisite". The circularity is
definite, not potential. Evidence ([Goo54] p. 251): the proof of
(17) defines `f(a,b) = a + (b ∸ a)` "so that f(a,0) = a,
f(0,b) = b, f(Sa,Sb) = Sf(a,b)". `f(0,b) = b` requires
`b ∸ 0 = b` — Goodstein's defining axiom, here
`derivable_sub_zero`, a Phase-4 target that itself requires
domination (its inner remainder reduces to `u %ᵉ eexp2 (u +ᵉ 0)`
via `axModAdd`, and discharging that requires
`2^E = u +ᵉ .succ t`). `f(Sa,Sb) = Sf(a,b)` requires equation
(2) `Sa ∸ Sb = a ∸ b`, also Phase 4. So the route
(17) → domination → Phase 4 consumes Phase-4 outputs.

Separately, the proof of (17) introduces the auxiliary function
`φ(0,a,b) = 0`,
`φ(Sn,a,b) = φ(n,a,b) + {1 ∸ [1 ∸ ((a∸n)+(b∸n))]}` by a fresh
recursive definition ([Goo54] p. 251). That move is legitimate
in Goodstein's system, whose axioms are an open-ended supply of
"explicit and recursive function definitions" (p. 247), but has
no counterpart here: `eraDefs` is fixed at seven equations, so φ
must be replaced by an explicit term over the basis whose
recursion equations are *derived* — and φ's step equation
involves `∸` on open terms, again Phase-4 material. The spec
does not analyse this.

The alternative intermediate family
`eexp2 x = x +ᵉ .succ (eexp2 x ∸ᵉ .succ x)` is given no
derivation route, and §8 records the adjacent attempts as
rejected. Meanwhile §9 requires the eleven theorems
unconditionally, so Phase 4 currently rests on no verified
route, with the stuck-and-ask fallback contradicting the
acceptance criteria.

Fix: before execution, exhibit a dependency-ordered route —
identify exactly which `∸` facts the transposed (17) needs and
show each is Phase-3-derivable, and state how φ is replaced by a
basis term; or derive domination first by another argument; or
stage §9 so that the §7 fallback is a defined exit rather than a
failure to meet the acceptance criteria.

### R1-M2 (Major) — §5's translation table omits proof obligations

§5 maps `omega`, `Nat.add_mod_right`, `Nat.mod_eq_of_lt`, and
case splits. The identity proofs that the method mirrors use
three further ingredients with no table entry:

- `Nat.mul_add_mod` — `(k·M + r) % M = r % M` with an *open*
  multiplier `k` — closes `sq_identity` (line 737),
  `div_identity` (line 922), and `pow_identity` (line 1006).
  `axModAdd` peels one `M`; peeling an open multiple needs its
  own object-level induction, whose statement involves `*ᵉ` —
  an operation whose laws are themselves Phase-4 targets.
- `pow_mod_rep` (lines 970–986) concludes with an existential
  (`∃ q, 2 ^ (c * y) = q * (2 ^ c - x) + x ^ y`) whose witness
  is built by induction. At object level the witness must be an
  explicit term and the equation derived by `uniq`; the spec
  does not say how.
- The rewriting steps of the three identity proofs (`key`, line
  734; `hZ`, lines 910–912; `hkey`, lines 918–921) use
  multiplicative algebra — distributivity, associativity,
  commutativity, i.e. Goodstein (11)–(15.1), p. 250 — which no
  phase derives.

Phase 4's scoping ("Each requires the domination family of §7")
understates these obligations; an implementer reaching
`mul_succ` could not proceed from the spec as written.

Fix: add translation rows for the mod-of-multiple step and the
existential-witness pattern, and add the multiplicative-algebra
layer to the phase plan (or record an argument that the open-law
derivations avoid these sites).

### R1-M3 (Major) — Phase 3 `zero_sub` sketch covers only successor `w`

Evidence: `esub` (lines 848–849) at `s := .zero`, `t := w` has
inner remainder `(P +ᵉ .zero) %ᵉ (P +ᵉ w)` for
`P := eexp2 (.zero +ᵉ w)`. The sketch writes the divisor as
`P +ᵉ .succ w` and resolves it by `axModLt`; `axModLt` (lines
270–271) matches only a successor-shaped addend, so the sketch
applies only when `w` is a successor — but the deliverable is
for arbitrary `w`. At `w = .zero` the inner remainder is a
`mod_self` instance (value `.zero`) and the outer is `zero_mod`;
the intermediate values differ between the two cases (`P` versus
`.zero`), so no single equational path exists and an E₃ split
(per §5) is required. The sketch, presented under "Verified
proof sketches", omits it. Downstream, the `zero_div` sketch
applies `zero_sub` at the argument rewritten by
`0 %ᵉ .succ u = 0` — exactly the missing `w = .zero` case
(`sub_self` at `.zero` covers it).

Fix: restate the sketch as an E₃ split (zero case via `axAdd0`,
`mod_self`, `zero_mod`; successor case as currently sketched),
and in `zero_div` route `0 ∸ᵉ 0` through `sub_self` or the
repaired `zero_sub`.

### R1-m1 (Minor) — §9 axiom criterion says "exactly"

"Axioms of every new theorem exactly `propext`, `Quot.sound`"
overconstrains: `#print axioms` reports only the axioms
reachable from a proof term, and a derivation that avoids
`simp`-driven membership reasoning can report fewer.
`scripts/check-axioms.sh` enforces an upper bound, not an exact
set.

Fix: "contained in {`propext`, `Quot.sound`}".

### R1-m2 (Minor) — style: value-laden label and colloquialism

"An intermediate target of independent interest" (§7) is a
value-laden label; "produced along the way" (§4) is colloquial.
See `CLAUDE.md` § Style guidelines and `docs/process.md`
§ Avoid colloquialisms and metaphors.

Fix: "An intermediate target is the family …"; "Supporting
theorems produced by the phases …".

## Checks with no finding

- §4 statements compared against the `daab65a9` declarations
  (`derivable_sub_zero` … `derivable_div_succ`): names, equation
  shapes, argument order, and parses identical. The infix
  precedences are unchanged between the two revisions (`+ᵉ` and
  `∸ᵉ` at 65; `%ᵉ`, `*ᵉ`, `/ᵉ` at 70; `^ᵉ` at 75), so in
  particular `u ∸ᵉ .succ v *ᵉ (u /ᵉ .succ v)` parses the same
  way in both. Explicit binders are elided in favour of the
  prose declaration `u v : ETm n`.
- The pre-reduction `eraDefs` has thirteen members, as §1
  states.
- [Goo54] citations: K, U₁, E₁, E₂ on p. 248 (E₂'s proof
  completes on p. 249), E₃ on p. 251; equations (1)–(4) and (6)
  on p. 249, (7), (8), (10) on p. 250, (17)/(17.1) on
  pp. 251–252; the `∸` and `·` recursion equations are defining
  axioms on p. 249; U₁'s step function "is a function of not
  more than two variables" (p. 247), supporting §3's generality
  claim. The equation statements in §2's table match the PDF.
- §6 Phase 0 (E₃ by `uniq` with a step functional ignoring the
  previous-value slot): sound against the rule at `Era.lean`
  lines 145–149 (take `H` := the weakening of `G.subst bump`
  past variable 1; the premises become the two hypotheses and a
  reflexivity).
- §6 Phase 2: both sketches type-check conceptually against the
  `uniq` premise shapes (recursion variable in position 0, the
  open law then by `Derivable.inst`), with `zero_add` instances
  closing the steps as stated; `mod_self` needs no induction.
- §6 Phase 3 `sub_self`, `edmul_zero`, `mul_zero`, `div_zero`:
  sound against the `esub`/`esq`/`edmul`/`ediv` definitions.
- §7's arithmetic claim `x + 1 ≤ 2^x` holds for all `Nat` `x`
  (equality at `x = 0, 1`); the claim that Goodstein's proof of
  (17) uses the `∸` axioms is verified on pp. 251–252 — see
  R1-M1 for the consequence the spec does not draw.
- Process: transcription/novel markings present (§2); doctoc TOC
  present; `markdownlint-cli2` reports zero errors on the spec;
  no new axioms, mathlib imports, or interface weakenings are
  proposed (§10).

## Verdict

Fail (revision required): one Blocker (R1-B1) and three Major
findings (R1-M1, R1-M2, R1-M3). The §4 interface, the
citations, and Phases 0–2 are sound; §5–§7 require rework
before an implementation plan can be written.
