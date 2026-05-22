# T4 spec adversarial review — round 4 (convergence verification)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Round-3 fix verifications](#round-3-fix-verifications)
  - [B2'(r3) — verified](#b2r3--verified)
  - [N2(r3) — verified](#n2r3--verified)
  - [Round-3 minor findings (N1(r3), M1(r3), M2(r3), M3(r3))](#round-3-minor-findings-n1r3-m1r3-m2r3-m3r3)
- [Residual blockers](#residual-blockers)
- [Residual serious](#residual-serious)
- [New issues introduced by round-3 fixes](#new-issues-introduced-by-round-3-fixes)
  - [N1(r4). §4.3 bprod increment narrative `totalling + 3` is stale](#n1r4-43-bprod-increment-narrative-totalling--3-is-stale)
  - [N2(r4). §4.3 comp absorption shape `tower (mu_f + mu_{gs}) m` is stale](#n2r4-43-comp-absorption-shape-tower-mu_f--mu_gs-m-is-stale)
  - [N3(r4). §4.2 comp rationale closing sentence mentions `recipe's + 4`](#n3r4-42-comp-rationale-closing-sentence-mentions-recipes--4)
- [Minor](#minor)
- [Methodology](#methodology)

<!-- END doctoc -->

## Summary

0 blockers, 0 serious, 3 minor (all new; introduced by the round-3
fixes). **CONVERGED.**

The round-3 blocker (B2'(r3)) and the round-3 new-issue (N2(r3))
are both verified closed. The round-3 minor findings remain
deferred to plan stage, which is acceptable for a spec. Three new
minor inconsistencies were introduced when §4.2's increments were
bumped without the corresponding edits propagating to §4.3 and to
one closing sentence in §4.2 itself; none are logic errors, all
are documentation-stage residue, and all are mechanical to fix at
plan-stage transcription.

## Round-3 fix verifications

### B2'(r3) — verified

Round-3 identified that the bprod runtime increment `+ 5` failed
to close the bound on `Σ_{i<v 0} 9·A_i·B_i` because the constant
factor `9` could not be absorbed: `9·v_0 ≤ m` is not a valid
inequality for arbitrary `Fin.maxOfNat _ v`, only the weaker
`v_0 ≤ m` is. The required increment was `+ 7` via two
applications of `mul_tower_le_tower_add_two` after rewriting
`9·m·T ≤ m·m·T`.

The revised §4.2 (lines 321–345) now reads:

> The runtime contains `Σ_{i<v 0} 9·A_i·B_i` where
> `A_i · B_i ≤ natBProd (i+1) (f.interp ∘ …) ≤ tower (mu_f + 3) m`.
> Writing `T := tower (mu_f + 3) m`, the outer sum is
> `Σ_{i<v 0} 9·T ≤ 9·v_0·T ≤ 9·m·T`. The constant factor `9` is
> absorbed by recognising `9 ≤ m` (the spec offset 44 ensures
> `m ≥ 44`), giving `9·m·T ≤ m·m·T = m·(m·T)`. Then
> `m·T ≤ tower (mu_f + 5) m` by one `mul_tower_le_tower_add_two`,
> and `m·(m·T) ≤ m·tower (mu_f + 5) m ≤ tower (mu_f + 7) m` by a
> second `mul_tower_le_tower_add_two`. Total runtime increment:
> `+ 7`.

Verification of each step:

- `A_i = natBProd i (f.interp ∘ …)`, `B_i = f.interp ctx_f`. Then
  `A_i · B_i = natBProd (i+1) (f.interp ∘ …)` because the i-th
  running product times the i-th factor equals the (i+1)-th
  running product. ✓
- `natBProd (i+1) ≤ (tower mu_f m)^(i+1) ≤ (tower mu_f m)^m` since
  `i + 1 ≤ v_0 ≤ m`. By `tower_pow_le_tower_add_three`
  (`Tower.lean:120`), `(tower mu_f m)^m ≤ tower (mu_f + 3) m`. ✓
- `v_0 ≤ m`: since `m = Fin.maxOfNat _ v + offset` and `v_0 = v 0`
  is a component of `v`, `v 0 ≤ Fin.maxOfNat _ v ≤ m`. ✓
- `9 ≤ m`: `m ≥ offset_e ≥ offset_f + 44 ≥ 44 ≥ 9`. ✓
- `9·m·T ≤ m·m·T`: from `9 ≤ m`. ✓
- `m·T = m · tower (mu_f + 3) m ≤ tower (mu_f + 5) m` by
  `mul_tower_le_tower_add_two` with `m ≥ 2`. ✓
- `m · tower (mu_f + 5) m ≤ tower (mu_f + 7) m` by a second
  `mul_tower_le_tower_add_two`. ✓

The recipe in §4.2's table at line 241 shows `mu_e = mu_f + 7`
and `offset_e = offset_f + 44`, consistent with this chain.

The spec also handles the per-iteration `compileER_runtime f
ctx_f` term (by IH `≤ tower mu_f m`, summed over `v_0 ≤ m`
iterations gives `m · tower mu_f m ≤ tower (mu_f + 2) m`,
absorbed into `tower (mu_f + 7) m`) and the secondary constants
(`60 + 2·(k+1) + 10·(i + outerSum) + nRegs_f`, polynomial in
`m`, absorbed). These are not spelled out in the rationale but
follow from the same constant-absorption pattern; this is
spec-level brevity, not a logic gap.

Status: **verified.**

### N2(r3) — verified

Round-3 identified that the comp `+ 4` increment elided the
constant factor `9` in `9·v_total`. The revised §4.2 step (iii)
(lines 282–304) now explicitly states:

> The constant `9` is absorbed by recognising `9 ≤ m` (offset_e
> ≥ 8 ensures `m ≥ 8`, bumped to ≥ 9 by including the per-subterm
> `4·a + 8` with `a ≥ 1`; for `a = 0` comp degenerates and the
> case is trivial). Then `9 · m · m ≤ m · m · m`, and `m · m · m
> ≤ m · tower 2 m ≤ tower 4 m` by two
> `mul_tower_le_tower_add_two` applications.

Verification:

- `9 ≤ m`: offset_e contains the `4·a + 8` term per recipe at
  line 239 (`offset_f + Fin.maxOfNat k offset_{gs i} + 4·a + 8`).
  For `a ≥ 1`, `4·a + 8 ≥ 12 ≥ 9`, so `m ≥ 9`. ✓
- `9·m·m ≤ m·m·m`: from `9 ≤ m`. ✓
- `m·m ≤ m · tower 0 m = m · m`; then `m · m ≤ tower 2 m` by
  `mul_tower_le_tower_add_two` (one application). Then
  `m · (m · m) ≤ m · tower 2 m ≤ tower 4 m` (second application).
  Hence `9 · v_total ≤ 9·m·m ≤ tower 4 m`. ✓
- `tower 4 m ≤ tower (mu_f + mu_g + 6) m` by `tower_mono_left`. ✓

The recipe in §4.2 (line 239) shows `mu_e = mu_f + max mu_{gs} +
6`, consistent.

The `a = 0` degenerate case is a stated trivial case: with `a =
0`, there are no inputs, so `comp f gs` for `a = 0` has empty
`gs : Fin k → ERMor1 0` and the entire bound reduces to a closed
form on a constant context. This is acceptable as a boundary
argument.

Status: **verified.**

### Round-3 minor findings (N1(r3), M1(r3), M2(r3), M3(r3))

Round 3 classified these as plan-stage:

- **N1(r3)** (literal `sorry` and bracket comments in §8.2
  pseudo-Lean): the project rule "no `sorry` in committed code"
  binds `.lean` files, not pseudo-Lean inside Markdown code
  blocks. The pseudo-Lean form is acceptable for a spec; the
  comment `/- depth-2 witness via erToKN_level -/` and the
  `sorry` body for the well-definedness obligation are
  legitimate elisions for a spec layer. Round-3 itself flagged
  this as "spec-form, not a logic error."
- **M1(r3)** (`AXIOM_ALLOW` vs `AXIOM\_ALLOW` underscore
  escape): markdownlint accepts both forms; consistency is a
  documentation-polish item.
- **M2(r3)** (line 472 informal `Fin.maxOfNat (v : Fin 0 → ℕ) =
  0` ill-typing): a parenthetical note in informal prose, not
  intended as compilable Lean. The intent is unambiguous to a
  reader.
- **M3(r3)** (erToKN_compat_extEq shape vs setoid bridge): the
  one-line `congr_fun` bridge is a standard quotient
  programming pattern; mentioning it in the spec is optional.

Round 4 verdict: **acceptable** for all four. None are blockers
or serious; all are plan-stage documentation refinements. The
spec-vs-plan boundary the round-3 author invoked is the correct
classification.

## Residual blockers

(none)

## Residual serious

(none)

## New issues introduced by round-3 fixes

The round-3 fixes correctly updated §4.2's table and §4.2's
per-constructor rationale, but the corresponding edits did not
propagate to §4.3 (the bound-theorem proof outline) or to one
closing sentence of §4.2's comp rationale. These are
documentation-stage stale phrasings, not logic errors.

### N1(r4). §4.3 bprod increment narrative `totalling + 3` is stale

§4.3 (lines 422–425):

> `bprod f` applies the same `+ 2` for the outer sum plus the
> running-product Nat identity `T^k ≤ 2^(k · T)` plus
> `mul_tower_le_tower_add_two` for the resulting exponent,
> totalling `+ 3`.

This text predates round 3 (and round 2 — it appears to be the
original spec narrative for an even earlier `+ 3` increment).
After round-3's bump to `mu_f + 7` in the §4.2 table (line 241)
and rationale (lines 339–340 `tower (mu_f + 7) m`), §4.3's
"totalling `+ 3`" is mathematically inconsistent with the rest of
the spec. The proof-outline narrative also does not reflect the
two `mul_tower_le_tower_add_two` applications and the `9 ≤ m`
constant-absorption step in the canonical rationale.

Resolution (plan-stage edit): replace lines 422–425 with a
sentence matching §4.2's rationale, e.g., "`bprod f` applies
`tower_pow_le_tower_add_three` for the value bound
`(tower mu_f m)^m ≤ tower (mu_f + 3) m`, then two applications
of `mul_tower_le_tower_add_two` to absorb the constant 9 and the
outer `v_0`-fold sum, totalling `+ 7`."

Severity: minor. Documentation-stage inconsistency between two
sections of the same spec.

### N2(r4). §4.3 comp absorption shape `tower (mu_f + mu_{gs}) m` is stale

§4.3 (lines 416–419):

> `comp f gs` applies `Tower.tower_comp` to absorb
> `tower mu_f (tower mu_{gs} m + offset_f) ≤ tower (mu_f +
> mu_{gs}) m`, then `mul_tower_le_tower_add_two` for the
> `v_total = Σ v i ≤ a · Fin.maxOfNat _ v` factor.

The bound `tower mu_f (tower mu_{gs} m + offset_f) ≤
tower (mu_f + mu_{gs}) m` skips the `+ 2` step (i) inner-offset
absorption that §4.2's rationale spells out (lines 270–278): the
correct intermediate is `tower (mu_f + mu_{gs} + 2) m`, not
`tower (mu_f + mu_{gs}) m`. The "+ 2" inner-offset cost from
step (i) and the additional `+ 4` margin from step (iii)'s
constant-9 absorption are both absent from §4.3.

Resolution (plan-stage edit): replace §4.3's comp bullet with a
sentence matching §4.2 step (i)/(ii)/(iii), e.g., "`comp f gs`
applies `mul_tower_le_tower_add_two` (inner-offset absorption,
adding 2), `tower_comp` (height summation), and two more
`mul_tower_le_tower_add_two` applications (outer
`9·v_total` constant-9 absorption, adding 4), reaching
`tower (mu_f + mu_g + 6) m`."

Severity: minor. Same class as N1(r4) — documentation
inconsistency between §4.2 (canonical) and §4.3 (stale outline).

### N3(r4). §4.2 comp rationale closing sentence mentions `recipe's + 4`

§4.2 step (iii) closing parenthetical (lines 297–304):

> the recipe's `+ 4` suffices because the `+ 2` slack between
> step (ii)'s `mu_f + mu_g + 2` and step (iii)'s `mu_f + mu_g +
> 6` margin handles the sum-of-pairs absorption without needing
> the additional `+ 2`. (The exact tightness depends on the
> precise discharge during implementation; the `+ 4` increment
> is the upper bound the spec commits to.)

The recipe table at line 239 commits to `+ 6` for comp, but the
narrative inside step (iii) still says "the recipe's `+ 4`" and
"the `+ 4` increment is the upper bound the spec commits to."
These two mentions of `+ 4` are residue from round-2's
`+ 4`-era text. They are inside the same step-(iii) paragraph
that elsewhere correctly reaches `tower (mu_f + mu_g + 6) m`.

Resolution (plan-stage edit): rewrite this parenthetical to read
"the recipe's `+ 6` suffices because step (iii) reaches
`tower (mu_f + mu_g + 6) m` from step (ii)'s
`tower (mu_f + mu_g + 2) m` with `+ 4` of slack, which absorbs
the sum-of-pairs `glue + rt(f)` cleanly."

Severity: minor. Within-section textual inconsistency.

## Minor

(no minor findings beyond the three N(r4) items above)

## Methodology

Sources consulted:

- Spec under review:
  `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`,
  jj revision `a4dc422f` on bookmark `feat/ertok-runtime-bound`.
- Round-3 review:
  `docs/research/2026-05-22-step-t4-spec-adversarial-review-round-3.md`.
- Round-2 review:
  `docs/research/2026-05-22-step-t4-spec-adversarial-review-round-2.md`.
- Round-1 review:
  `docs/research/2026-05-22-step-t4-spec-adversarial-review-round-1.md`.
- Tower lemmas: `GebLean/Utilities/Tower.lean`, lines 51
  (`tower_comp`), 65 (`tower_mono_left`), 101
  (`mul_tower_le_tower_add_two`), 120
  (`tower_pow_le_tower_add_three`). Re-checked the file for any
  newly-added constant-absorbing lemma; none present beyond the
  three cited.
- T2 compiler runtime: `GebLean/LawvereERKSim/Compiler.lean`,
  lines 1720–1772 (`compileER_runtime` for all six ER
  constructors, confirming bprod's per-iteration cost contains
  `9·A_i·B_i + 4·A_i + 9·B_i + nRegs_f + …`).
- ERMorN / ERMorNQuo / setoid:
  `GebLean/LawvereER.lean:151`, `GebLean/LawvereERQuot.lean:23,38`.
- KMorN / kMorNSetoid / KSimMor: `GebLean/LawvereKSim.lean:65`,
  `GebLean/LawvereKSimQuot.lean:21,372–397,402–407,445–447,
  475–481`.
- kToER multi-output passage:
  `GebLean/LawvereKSimER.lean:336–479`.
- Markdownlint: `markdownlint-cli2` on the spec — 0 errors at
  review time.
- Mathlib upstream guides (re-fetched per CLAUDE.md): coding
  style and naming conventions; spec's `def`/`theorem` casing,
  Unicode operators, and reference-format conventions remain
  compliant.

Tactics used:

- **B2'(r3) verification**: re-derived
  `Σ_{i<v 0} 9·A_i·B_i ≤ tower (mu_f + 7) m` step by step from
  the IH on `f`, `tower_pow_le_tower_add_three`, `9 ≤ m` (offset
  44), and two applications of `mul_tower_le_tower_add_two`.
  Confirmed the chain closes with the spec's
  `mu_e = mu_f + 7`.
- **N2(r3) verification**: re-derived `9 · v_total ≤ tower 4 m`
  for comp from `9 ≤ m` (offset includes `4·a + 8`), `v_total ≤
  m · m`, and two applications of `mul_tower_le_tower_add_two`.
  Confirmed `tower 4 m ≤ tower (mu_f + mu_g + 6) m` by
  `tower_mono_left`. Confirmed the spec's `mu_e = mu_f + max
  mu_{gs} + 6` carries the margin.
- **Cross-section consistency sweep**: compared §4.2's recipe
  table (line 239–241), §4.2's per-constructor rationale (lines
  243–345), §4.3's bound-theorem proof outline (lines 412–425),
  and §4.2's closing paragraph on literature-fixed vs upper-
  bound increments (lines 347–364). Identified three stale
  phrasings in §4.3 and §4.2 step (iii) closing that did not
  propagate from round 3's `+ 5 → + 7` and `+ 4 → + 6` bumps.
- **§8 multi-output passage**: re-checked the structural shape
  against the kToER analogue at `LawvereKSimER.lean:336–479`.
  No new type-correctness issues beyond the four round-3 minors
  (the literal `sorry`, the bracket-comment depth-witness, the
  setoid-bridge omission, and the ill-typed informal note).
- **Markdownlint**: ran `markdownlint-cli2` on the spec; 0
  errors.
