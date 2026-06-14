# Adversarial review — era-open-laws design, round 3 (convergence check)

Reviewer: fresh-context agent. Artifact:
`docs/superpowers/specs/2026-06-12-era-open-laws-design.md`
(revised after round 2). Sources checked: `GebLean/Era.lean`
(working tree, full read), the pre-reduction declarations at git
revision `daab65a9` (via `git show`), the round-1 and round-2
reviews, the round-2 fix commit's diff, the branch commit
messages, and the project rules (`CLAUDE.md`,
`.claude/rules/*.md`). Each round-2 finding was re-verified
against the revised text; the revision diff was checked
hunk-by-hunk; the whole spec was swept for internal consistency.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Findings](#findings)
  - [R3-m1 (Minor) — Phase 4b's post-entry order contradicts §7.5](#r3-m1-minor--phase-4bs-post-entry-order-contradicts-75)
  - [R3-m2 (Minor) — style: metaphor in §7.5](#r3-m2-minor--style-metaphor-in-75)
- [Checks with no finding](#checks-with-no-finding)
- [Verdict](#verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Summary

| # | Severity | Title |
| --- | --- | --- |
| R3-m1 | Minor | §6 Phase 4b's "Order after entry: mod-of-multiple → `mul_succ` → …" contradicts §7.5, whose step consumes `mul_succ` and whose candidate route enters the cluster at `mul_succ` |
| R3-m2 | Minor | Style: "If the entry resists" (§7.5) |

## Findings

### R3-m1 (Minor) — Phase 4b's post-entry order contradicts §7.5

§6 Phase 4b gives "Order after entry: mod-of-multiple →
`mul_succ` → multiplicative algebra (11), (14), (15), (15.1)
as needed → …". §7.5 states that mod-of-multiple's step
consumes `mul_succ`, and records as the candidate route an
entry at `mul_succ` (via the `edmul` recursion). The order
line is inconsistent under every choice of entered member:

- entry = `mul_succ` (the recorded candidate): `mul_succ`
  should not appear in the post-entry order at all, and
  certainly not after a law whose step consumes it;
- entry = the squaring law: mod-of-multiple still consumes
  `mul_succ` first, so the listed order inverts the recorded
  dependency;
- entry = mod-of-multiple: no recorded route supports it, and
  listing it first in "after entry" double-counts the entry.

R2-M1's substantive asks are met — the entry is recorded as
open in §7.5 with its cycle stated, and §9's exit covers it —
so this is a residual wording defect, recoverable from §7.5,
not a hidden obligation.

Fix: "Order after entry (candidate entry: `mul_succ`, §7.5):
mod-of-multiple → multiplicative algebra (11), (14), (15),
(15.1) as needed → …", or equivalently state the remaining
members in the dependency order of §7.5 (`mul_succ` before
mod-of-multiple).

### R3-m2 (Minor) — style: metaphor in §7.5

"If the entry resists, the staged exit of §9 applies" (§7.5,
introduced by the round-2 revision) attributes agency to a
derivation obligation; same category as round 2's "Candidate
attacks" (R2-m5). See `docs/process.md` § Avoid colloquialisms
and metaphors. Replacement: "If the entry remains open, the
staged exit of §9 applies."

## Checks with no finding

- R2-M1 fix otherwise adequate. The multiplicative cluster
  entry is recorded as open in §7.5 with the cycle stated, and
  each link re-verified: the squaring law's only `Nat`-side
  source is `sq_identity`, whose closing step
  (`rw [key, Nat.mul_add_mod, Nat.mod_eq_of_lt hsq]`,
  `Era.lean` line 737) peels the open multiplier `2^n ∸ n` by
  mod-of-multiple; §7.5's step is `mul_succ`; and a `mul_succ`
  derivation through `emul = ediv (edmul · ·) 2`
  (lines 881, 951) reaches `esq` behaviour. Restating the
  cycle through the squaring law `esq t = t *ᵉ t` (round 2
  phrased it through the `esq` successor law) is consistent:
  both sit downstream of mod-of-multiple by the same
  `sq_identity` mirror. §9's exit now names the three
  obstructions (§7.3, §7.4, §7.5).
- R2-m1 fix verified. `(m *ᵉ k +ᵉ r) %ᵉ m = r %ᵉ m` is the
  exact analogue of `Nat.mul_add_mod : (a * b + c) % a = c % a`
  (modulus first factor, multiplier second). Base re-derived:
  `mul_zero` (Phase 3) plus `zero_add` (Phase 0). Step
  re-derived: `mul_succ` plus `axModAdd` after commuting the
  peeled `m` to the right by additive algebra. The
  multiplier-second form matches all three consuming sites:
  `sq_identity` `key` (line 734, modulus `2^n + n` first),
  `div_identity` `hkey` (lines 918–921, modulus
  `2((x+1)(k+1)) − 1` first), `pow_identity` (line 1006, after
  `Nat.mul_comm q`). (11) and (12) drop off the §7.5 path; (12)
  appears nowhere in the spec, correctly.
- R2-m2 fix verified. The `zero_div` sketch re-derived against
  `ediv` (lines 925–926): the dividend
  `edmul one (.zero ∸ᵉ (.zero %ᵉ .succ u))` closes by
  `zero_mod` under `esub_congr`, `sub_self` at `.zero`, and
  numerals to `.zero`; the modulus
  `edmul one (.succ u) ∸ᵉ one` stays open in `u`; the outer
  remainder closes by Phase-2 `zero_mod` under `emod_congr`.
- R2-m3 fix verified. §7.3 states the derive-at-variables,
  instantiate-at-compound-terms reading explicitly, names
  `eexp2`-headed instantiation with §7.2's conversion and
  §7.6's `pow_zero` as consumers, and renames the first bullet
  to "the summand family". The `pow_zero` instance
  `2^{u+1} = u +ᵉ .succ (.succ t)` is the summand-family member
  at `e := x₀ +ᵉ one`, `a := x₀ +ᵉ one` (sub-sum read
  inclusively) plus additive algebra; it holds in the standard
  model (`2^{u+1} ≥ u + 2`, equality at `u = 0`).
- R2-m4 fix verified. `esubAt_of_lt` now carries the single
  hypothesis `Derivable ⟨v, u +ᵉ .succ d⟩`; the sketch
  re-derived (inner `axModLt` after additive algebra, outer
  `mod_self`), and "No domination hypothesis is consumed" is
  correct.
- R2-m5 fixed: "cover" (§7.2), "Candidate routes" (§7.4);
  "avenue" → "approach" in §7.3 likewise.
- §7.5 candidate-route arithmetic. `edmul` interprets as `2xy`
  (`dmul_identity`, lines 874–878; `edmul`, line 881), and
  `2x(v+1) = 2xv + 2x`, so the recursion
  `edmul u (Sv) = edmul u v +ᵉ u +ᵉ u` (left-associated parse)
  is correct in the standard model. The route's open
  obligations — the recursion's own site analysis, and the
  open-term mirror of `numeral_mul`'s `ediv … 2` composition
  step — fall within the entry's recorded-open status and §9's
  exit; the spec claims no feasibility.
- §7.3 candidate-witness arithmetic re-verified:
  `2^{Sa'} = (2^{a'} + Sa') + (2^{a'} − Sa')` with
  `2^{a'} − Sa' < 2^{a'} + Sa'`, using `Sa' ≤ 2^{a'}` (all
  `a'`), so `2^{Sa'} mod (2^{a'} + Sa') = 2^{a'} − Sa'`.
- Internal consistency sweep. All section cross-references
  resolve (§1→§4; §2→§7.2/§7.3/§7.4/§7.5; §5→§7.1, §7.2, §7.5,
  §7.6, Phase 4b; §6→§7.3–§7.6, §9; §7.2→§7.7; §7.3→§8, §9;
  §7.4→§9; §7.5→§9; §8→§7.7; §10→§7.2). §9's "four of the
  eleven" matches Phase 3's outputs (`pred_zero`, `mul_zero`,
  `div_zero`, `zero_div`) and "the remaining seven" is the
  complement. Phase 4a's order matches §7.4's analyses. Apart
  from R3-m1, no stated order contradicts a recorded
  dependency, and §6, §7, §9 agree on which obligations are
  verified, sketched, and open.
- §4 statements re-verified verbatim against the `daab65a9`
  declarations via `git show`: all eleven names, equation
  shapes, and binders match; the round-2 revision did not touch
  §4.
- §3 inventory matches the working tree: congruences exist for
  all seven derived operations (`esq`, `edelta`, `esub`,
  `edmul`, `ediv`, `emul`, `epow`); the numeral lemmas and the
  `uniq` generality claim match lines 101–149.
- Earlier verified sketches spot-checked again: Phase 2
  `zero_mod` (base `axMod0` at `0`, step `axModLt (0, v)` plus
  `zero_add`) and `mod_self`; Phase 3 `zero_sub` E₃ split,
  `sub_self`, `edmul_zero`, `mul_zero`, `div_zero`; §7.2
  `esubAt_of_add` and Goodstein's (5) as its instance at
  `e := (a+b) +ᵉ b`; §7.4 `sub_zero` and `pred_succ`
  reductions against `esub` (lines 848–849), `axModLt`
  (line 270), `axModAdd` (line 274); §7.6 `pow_zero` reduction.
- No new [Goo54] citation claims were introduced by the
  round-2 revision (verified against the commit diff); the
  round-1/round-2-verified citations stand unchanged.
- Process: `markdownlint-cli2` reports zero errors on the
  spec; `doctoc --dryrun --update-only` reports the TOC up to
  date; transcription/novel markings present in §2; no new
  axioms, mathlib imports, or interface weakenings. The three
  branch commits (`a549f4ffd`, `4d0380537`, `c26b453d8`)
  conform to the mathlib commit conventions: type `doc(era)`,
  lowercase imperative subjects without trailing periods,
  imperative bodies. The two trunk commits visible in the
  supplied revset (`ed0b67521`, `daab65a99`) predate the
  branch and are outside the forward-only style scope.

## Verdict

Pass with minors. Two Minor findings: R3-m1 (a wording-level
ordering inconsistency between §6 Phase 4b and §7.5) and R3-m2
(one metaphor). Every round-2 fix is present and otherwise
correct, the round-1 fixes remain intact, and the consistency
sweep found no other defect. The two corrections are local and
do not require a further review round.
