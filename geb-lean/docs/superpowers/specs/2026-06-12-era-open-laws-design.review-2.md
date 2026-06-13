# Adversarial review — era-open-laws design, round 2

Reviewer: fresh-context agent. Artifact:
`docs/superpowers/specs/2026-06-12-era-open-laws-design.md`
(revised after round 1). Sources checked: `GebLean/Era.lean`
(working tree), the pre-reduction file at git revision
`daab65a9`, the [Goo54] PDF (pp. 247–253), the round-1 review,
and the project rules (`CLAUDE.md`, `.claude/rules/*.md`,
`docs/process.md`). Each round-1 fix was re-verified; new
content (§7.1–§7.6) was re-derived step by step.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Findings](#findings)
  - [R2-M1 (Major) — Phase 4b's entry is circular and unrecorded as open](#r2-m1-major--phase-4bs-entry-is-circular-and-unrecorded-as-open)
  - [R2-m1 (Minor) — §7.5's base lemma is misidentified](#r2-m1-minor--75s-base-lemma-is-misidentified)
  - [R2-m2 (Minor) — `zero_div` sketch's closing step](#r2-m2-minor--zero_div-sketchs-closing-step)
  - [R2-m3 (Minor) — "one-variable family" mislabels its members](#r2-m3-minor--one-variable-family-mislabels-its-members)
  - [R2-m4 (Minor) — `esubAt_of_lt`'s second hypothesis](#r2-m4-minor--esubat_of_lts-second-hypothesis)
  - [R2-m5 (Minor) — style: metaphors](#r2-m5-minor--style-metaphors)
- [Checks with no finding](#checks-with-no-finding)
- [Verdict](#verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Summary

| # | Severity | Title |
| --- | --- | --- |
| R2-M1 | Major | Phase 4b's order is circular at entry: the `esq` successor law needs §7.5, which needs (11)/`mul_succ`, which needs the `esq` successor law; the multiplicative cluster entry is an unrecorded open obligation outside §9's exit clause |
| R2-m1 | Minor | §7.5's base premise needs `zero_mul` (Goodstein (12)), not `mul_zero`; stating the law with the multiplier second repairs the base and removes (11) from the path |
| R2-m2 | Minor | The `zero_div` sketch's closing step is `zero_mod`, not numerals (the modulus is open in `u`) |
| R2-m3 | Minor | §7.3's label "one-variable family" contradicts the two-variable members the §7.2 conversion and §7.6 `pow_zero` consume |
| R2-m4 | Minor | `esubAt_of_lt`'s second hypothesis is unused by its verified sketch; the "to be dropped if unused" hedge is resolvable now |
| R2-m5 | Minor | Style: "absorb" (§7.2), "Candidate attacks" (§7.4) |

## Findings

### R2-M1 (Major) — Phase 4b's entry is circular and unrecorded as open

§6 Phase 4b gives the order: squared domination instance and
the `esq` successor law → `mul_succ` → left-successor law (11)
→ mod-of-multiple (§7.5) → multiplicative algebra → `pow_zero`
→ `pow_succ` → `div_succ`. The order presents itself as a
dependency order, but its first element depends on its fourth:

- By §5's own translation table, the `Nat.mul_add_mod` step of
  a mirrored proof translates to the mod-of-multiple law
  (§7.5). The only `Nat`-side source for the `esq` successor
  law's behaviour is `sq_identity` (`Era.lean` line 737:
  `rw [key, Nat.mul_add_mod, Nat.mod_eq_of_lt hsq]`), whose
  proof peels an *open* `∸`-shaped multiple `2^n − n` of the
  modulus (`key`, line 734). No `uniq` or E₃ derivation can
  substitute: both rules conclude equality of two solutions
  from step premises, and the step premise for
  `esq (.succ x) = esq x +ᵉ x +ᵉ .succ x` is the law itself.
  So the `esq` successor law sits downstream of §7.5.
- §7.5's step consumes (11), which is derived from `mul_succ`
  ([Goo54] p. 250), which per the stated order consumes the
  `esq` successor law. (Restating §7.5 with the multiplier
  second, per R2-m1, replaces (11) by `mul_succ` in this chain
  but does not break the cycle.)

The cycle `esq`-successor-law → §7.5 → `mul_succ` →
`esq`-successor-law is the multiplicative analogue of the
subtraction cluster entry that §7.4 records as open — but the
spec does not record it: §6 Phase 4b carries no hedge, §7.6's
"Routes sketched only" covers only `pow_succ` and `div_succ`,
and §9's staged exit names exactly two obstructions ("The
domination family (§7.3) and the cluster entry (§7.4)"), so an
impasse here falls outside the defined exit. Round 1's R1-M2
observed that "an implementer reaching `mul_succ` could not
proceed from the spec as written"; the revision added the
missing obligations to the phase plan but ordered them without
analysing the entry, so the fix is incomplete on this point.

Fix: record the multiplicative cluster entry as an open
obligation in §7 (with candidate routes, if any, in the style
of §7.4), restate the Phase 4b order to reflect the actual
dependencies, and widen §9's exit clause to cover it; or
exhibit a non-circular derivation of the `esq` successor law
or of `mul_succ`.

### R2-m1 (Minor) — §7.5's base lemma is misidentified

§7.5 states the law as `(u *ᵉ m +ᵉ r) %ᵉ m = r %ᵉ m` by `uniq`
on the multiplier `u`, with "Base: `mul_zero` plus `zero_add`".
With the multiplier as the *first* factor, the base instance is
`(.zero *ᵉ m +ᵉ r) %ᵉ m`, which needs `0 *ᵉ m = 0` — Goodstein's
(12) (`zero_mul`, [Goo54] p. 250), not `mul_zero`
(`u *ᵉ .zero = .zero`). (12) appears nowhere in the spec: §2's
multiplicative row lists (11), (14), (15), (15.1) only, and no
phase derives it.

Two repairs, either sufficient:

- State the law with the multiplier second,
  `(m *ᵉ u +ᵉ r) %ᵉ m = r %ᵉ m`. The base is then genuinely
  `mul_zero` plus `zero_add`, and the step is `mul_succ`
  (`m *ᵉ .succ u = m *ᵉ u +ᵉ m`) plus `axModAdd` — (11) drops
  out of the §7.5 path entirely. This form also matches all
  three consumers directly: `sq_identity`'s `key` (line 734),
  `div_identity`'s `hkey` (line 919), and `pow_identity`
  (line 1006 commutes `q` to put the modulus first).
- Keep the multiplier first and add (12), derivable by `uniq`
  from `mul_zero`, `mul_succ`, and `add_zero` once `mul_succ`
  exists.

### R2-m2 (Minor) — `zero_div` sketch's closing step

§6 Phase 3's `zero_div` sketch ends "then numerals". After the
dividend reduces to `.zero` (via `zero_mod`, `sub_self` at
`.zero`, and `numeral_dmul`), the remaining term is
`.zero %ᵉ (edmul one (.succ u) ∸ᵉ one)`, whose modulus is open
in `u`; numerals cannot close it. The closing step is the
Phase-2 `zero_mod` under `emod_congr`. The route exists with
Phase 0–2 tools, so this is a sketch-wording defect only.

Fix: "…then numerals for the dividend and `zero_mod` for the
remaining open-modulus remainder."

### R2-m3 (Minor) — "one-variable family" mislabels its members

§7.2's conversion ("a modulus `2^c ∸ x` … converts to
`d +ᵉ .succ p` by `esubAt_of_add`") and §7.6's `pow_zero` apply
`esubAt_of_add` at `u := eexp2 c`, `v := x`, whose own
domination hypothesis is
`eexp2 (eexp2 c +ᵉ x) = eexp2 c +ᵉ .succ q` — an exponent
containing `eexp2` and a minorant that is not a sum of
variables. These instances are covered by §7.3's first bullet
only as `Derivable.inst` instantiations (at `x₀ ↦ eexp2 c`,
`x₁ ↦ x`) of the *two-variable* member
`eexp2 (x₀ +ᵉ x₁) = x₀ +ᵉ .succ t`. The bullet's description
("`e` a sum of variables and constants, `a` a sub-sum of `e`")
does cover that member, but the label "one-variable family"
contradicts it, and the derive-at-variables-then-instantiate
reading that makes the coverage work is left implicit.

Fix: rename (e.g. "the variable-sum family"), and state
explicitly that members are derived at variable scope and
instantiated at compound terms, naming the two-variable member
the conversion consumes.

### R2-m4 (Minor) — `esubAt_of_lt`'s second hypothesis

The verified sketch of `esubAt_of_lt` closes the inner
remainder by `axModLt` from the first hypothesis alone and the
outer by `mod_self`; the second hypothesis
(`Derivable ⟨eexp2 e, v +ᵉ .succ p⟩`) is not consumed at any
step. The hedge "(the second hypothesis to be dropped if
unused)" can therefore be resolved now: state the law without
it.

### R2-m5 (Minor) — style: metaphors

"These two laws absorb every `∸`-shaped modulus" (§7.2) and
"Candidate attacks, in order" (§7.4) are metaphors; see
`docs/process.md` § Avoid colloquialisms and metaphors.
Replacements: "cover", "Candidate routes".

## Checks with no finding

- R1-B1 fix adequate. §7.1's site inventory matches the actual
  `Nat.mod_eq_of_lt` sites: `sq_identity` line 737 (dividend
  `n·n`, modulus `2^n + n`), `tsub_identity` lines 837 and
  842–843 (one site in the `x < y` case, two in `x ≥ y`),
  `div_identity` line 922, `pow_identity` line 1006; dividend
  and modulus shapes as tabulated. `delta_identity`'s sites are
  correctly excluded: `edelta` occurs in none of the
  `esq`/`esub`/`edmul`/`ediv`/`emul`/`epow` definitions, so it
  is outside the derivation chain of the eleven laws.
  `numeral_mod`'s site (line 643) is not an identity-proof site.
- R1-M1 fix adequate as far as it reaches. §7.3 is marked open
  with the circularity recorded; §7.7 demotes (17) off the
  critical path, and its analysis is verified against [Goo54]
  pp. 251–252 (`f(0,b) = b` consumes `b ∸ 0 = b`;
  `f(Sa,Sb) = Sf(a,b)` consumes (2); φ is a fresh recursive
  definition with no counterpart under fixed `eraDefs`). The
  §9 staging is internally consistent for Phases 0–3: every
  Phase 0–3 sketch was re-derived and uses only the seven
  axioms, Phase 1–2 outputs, congruences, and numerals — no
  domination instance and no hidden `Nat.mod_eq_of_lt`
  analogue. (The residual Phase 4b gap is R2-M1, charged to
  R1-M2's fix rather than this one.)
- R1-M3 fix adequate. The repaired `zero_sub` is a correct E₃
  split: at `w = .zero` both remainders close by `axAdd0`,
  `mod_self`, `zero_mod`; at `w = .succ x` the inner remainder
  is an `axModLt` instance after `axAdd0` and the outer is
  `mod_self` after `axAdd0`. `zero_div` now routes `0 ∸ᵉ 0`
  through `sub_self` at `.zero` (R2-m2 concerns only its final
  step's wording).
- R1-m1 fixed ("contained in {`propext`, `Quot.sound`}");
  R1-m2 fixed (both phrasings replaced as recommended).
- §7.2 `esubAt_of_add` verified by re-derivation: inner
  remainder `w %ᵉ (eexp2 e +ᵉ v)` after rewriting
  `eexp2 e +ᵉ u = w +ᵉ (eexp2 e +ᵉ v)` and `axModAdd`, with
  `eexp2 e +ᵉ v = w +ᵉ .succ (v + p + v)` from the domination
  hypothesis by Phase-1 algebra; outer remainder with
  `eexp2 e +ᵉ u = w +ᵉ .succ (v + p + w + v)` likewise.
  `esubAt_of_lt` verified (inner `axModLt` at `.succ d`, outer
  `mod_self`).
- §7.4 `sub_zero` and `pred_succ` verified reductions
  re-derived, including the `esubAt_of_add` restatement of
  `sub_zero` and the fact that `pred_succ`'s outer remainder
  needs no domination
  (`2^E +ᵉ .succ u = u +ᵉ .succ (eexp2 E)` exactly).
- §7.4 cluster-entry mutual derivability verified. Forward
  direction matches [Goo54] p. 249 ((1) from the `∸`-axioms by
  U₁; (2) from (1) plus `Sa ∸ 1 = a`). Converse re-derived:
  `sub_succ` by `uniq` on `u` with `H := u ∸ᵉ v` ignoring the
  previous-value slot; base `0 ∸ᵉ .succ v = (0 ∸ᵉ v) ∸ᵉ one`
  by Phase-3 `zero_sub` and `pred_zero`; the `G`-premise closes
  by (1) plus `pred_succ` as stated. One detail: the
  `F`-premise (`.succ u ∸ᵉ .succ v = u ∸ᵉ v`) closes by (2)
  alone, so the parenthetical's "(2)-then-(1)" over-lists (1);
  harmless, since over-listing inputs cannot hide a gap.
- §7.5's `uniq` shape conceptually typechecks: stated at scope
  `n + 1` with the recursion variable in position 0 and the
  other operands weakened, the open base premise closes by
  instantiating term-general theorems, the same pattern as
  `derivable_add_zero` (modulo the R2-m1 base-lemma repair).
  The claim that (11) is derived by `uniq` from `mul_zero` and
  `mul_succ` is verified against [Goo54] p. 250 (Goodstein
  additionally uses (8) and (10), which Phase 1 supplies).
- §7.6 `pow_zero` verified reduction re-derived: the dividend's
  exponent closes by `mul_zero` and numerals to `one`; the
  modulus exponent reduces by `mul_zero` and `zero_add` to
  `u + 1`; `esubAt_of_add` at the domination instance
  `2^{u+1} = u +ᵉ .succ (.succ t)` (true in the standard model,
  with equality at `u = 0`) converts the modulus to
  `.succ (.succ t) = one +ᵉ .succ t`, and `axModLt` yields
  `one`. The needed `esubAt_of_add` domination hypothesis is
  the two-variable family member of R2-m3, instantiated.
- §4 statements re-checked verbatim against the `daab65a9`
  declarations: all eleven names, equation shapes, and binders
  match; the prose change since round 1 touched only the
  preamble sentence.
- [Goo54] citations newly load-bearing this round: (12) exists
  as Goodstein's equation (12) on p. 250 (relevant to R2-m1);
  (14) commutativity, (15) distributivity, (15.1) associativity
  on p. 250 as §2 states; I₂'s derivation (pp. 252–253)
  consumes (13) (via I₁), (16), and (17) (via the `|a, b|`
  schema) and introduces fresh recursive definitions (`q`, φ),
  supporting §7.4(iii)'s cost assessment; E₃ on p. 251.
- Process: `markdownlint-cli2` reports zero errors on the spec;
  `doctoc --dryrun --update-only` reports the TOC up to date;
  transcription/novel markings present in §2; no new axioms,
  mathlib imports, or interface weakenings. The two branch
  commits (`a549f4ffd`, `4d0380537`) conform to the mathlib
  commit conventions: type `doc(era)`, lowercase imperative
  subjects without trailing periods, imperative bodies.

## Verdict

Fail (revision required), narrowly: one Major (R2-M1) and five
Minors. All round-1 Blocker/Major fixes are otherwise sound,
the §7.2 template and the §7.4 analyses are verified, and the
required revision is targeted — record the multiplicative
cluster entry as open (or exhibit its route), reorder Phase 4b,
widen §9's exit clause, and apply the Minor corrections. No
structural rework is needed.
