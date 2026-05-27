# T5 spec adversarial review — round 3

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings](#findings)
  - [Round-2 status](#round-2-status)
  - [N6 — §5 / §11.10 LOC estimate for T5.C inconsistent](#n6--5--1110-loc-estimate-for-t5c-inconsistent)
  - [N7 — §3 `Equivalence.lean` LOC delta does not add up from §5](#n7--3-equivalencelean-loc-delta-does-not-add-up-from-5)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

Zero blockers, zero serious findings, zero minor findings, two
nits. The two nits are LOC-arithmetic inconsistencies internal
to the spec; neither blocks implementation. All round-2 serious
findings (S6, S7) and minor findings (M8, M9) are resolved, and
the round-2 nits (N4, N5) are addressed. Active `lean_run_code`
verification of the §6.7 explicit-instance form and §6.6's
`Equivalence.mk'` / `cat_disch` path succeeds end-to-end on the
current mathlib pin. The spec is converged.

## Methodology

Read end-to-end:

- The revised spec at
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`.
- Round-1 findings at
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.review-1.md`.
- Round-2 findings at
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.review-2.md`.
- `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `docs/process.md` § Adversarial review.
- The post-T4 handoff at
  `docs/superpowers/plans/2026-05-25-post-t4-handoff.md`.
- Mirror code in `GebLean/LawvereKSimER.lean` lines 480–571.
- `GebLean/LawvereERKSim/ErToKFunctor.lean` (full file), in
  particular the lift function at lines 99–114.

Re-fetched the four mathlib upstream guides via the in-repo
digest at `.claude/rules/lean-coding.md` §§ Authoritative
upstream guides. Cross-checked against the revised spec's
declaration names, suggested commit messages, and docstring
placeholders.

Active verification via `lean_run_code`:

- Confirmed `@CategoryTheory.Equivalence.mk'` has signature
  `(functor : C ⥤ D) → (inverse : D ⥤ C) →
   (unitIso : 𝟭 C ≅ functor ⋙ inverse) →
   (counitIso : inverse ⋙ functor ≅ 𝟭 D) →
   autoParam … Equivalence.functor_unitIso_comp._autoParam →
   (C ≌ D)`. The autoparam name is exactly as spelled by the
  round-2 review; matches §6.6.
- Confirmed `@CategoryTheory.Equivalence.mk` (the smart
  constructor) takes the four data fields without an autoparam;
  consistent with §6.6's prose distinction.
- Confirmed `@Equivalence.isEquivalence_functor (F : C ≌ D) :
  F.functor.IsEquivalence` and the dual `isEquivalence_inverse`
  exist at the names and signatures the spec relies on.
- Constructed a stand-in `MyObj` category with identity-on-objects
  `F`, `G`, identity-shaped `η`, `ε`, packaged as
  `def myEquiv : MyObj ≌ MyObj := Equivalence.mk' F G η ε` (the
  autoparam `cat_disch` closes the triangle), then declared
  `instance : F.IsEquivalence := myEquiv.isEquivalence_functor`
  and `instance : G.IsEquivalence := myEquiv.isEquivalence_inverse`.
  Both elaborate; both `example : F.IsEquivalence := inferInstance`
  / `example : G.IsEquivalence := inferInstance` then succeed.
  Confirms the §6.7 commitment under the current pin.

Cross-checked the §6.1 motive's spelled-out lift function
against the actual `erToKFunctor_map` body at
`GebLean/LawvereERKSim/ErToKFunctor.lean:99–114`. The two are
character-identical in the `{ hom, depth_witness }` builder:
same `Quotient.mk (kMorNSetoid n m) (erToKN rec)` for `hom`,
same `Quotient.mk _ { rep := erToKN rec, rep_level := fun i =>
erToKN_level rec i, rep_eq := rfl }` for `depth_witness`. The
spelled-out form is exact, so the post-`unfold erToKFunctor_map`
goal's `Quotient.liftOn` placeholder unifies on the lift-function
slot by `rfl`; the well-definedness underscore is the only piece
left for elaboration to fill, which it can do from the post-
`unfold` goal type.

## Findings

### Round-2 status

- **S6 — Resolved.** §6.7 now commits to two explicit
  `IsEquivalence` instances on `erToKFunctor` and `kToERFunctor`,
  each as a one-line projection
  `erKSimEquiv.isEquivalence_functor` /
  `.isEquivalence_inverse`. §4.3's table lists both instance
  rows. §1's T5-C bullet mentions "two explicit
  `Functor.IsEquivalence` instances". `lean_run_code` confirms
  the form elaborates and `inferInstance` then succeeds for
  both functors. The typeclass-search bridging concern is
  explicitly called out in §4.3 and §6.7.
- **S7 — Resolved.** §11.6 now references `Equivalence.mk'`
  (raw structure constructor, four data + one autoparam,
  defaulted to `by cat_disch`), `Functor.IsEquivalence`,
  `Equivalence.isEquivalence_functor` and
  `Equivalence.isEquivalence_inverse`. §11.8 references
  `Equivalence.mk'` and `cat_disch`. Neither punch-list entry
  mentions the smart `mk` or `aesop_cat` outside of the
  intended contrast.
- **M8 — Resolved.** §6.6 line 495 now reads
  `h : (𝟭 LawvereERCat).obj X = (erToKFunctor ⋙
  kToERFunctor).obj X`, an object-equality type as required
  by `eqToHom`. The trace conclusion (`eqToHom rfl = 𝟙 X`)
  remains correct.
- **M9 — Resolved.** §1 now references §5 for stub
  operational semantics, and §5 includes a four-bullet
  block specifying (a) the stub lives in
  `/tmp/t5-equivalence-stubs.lean` outside the committed
  Lean source tree; (b) the stub contains three `example`
  blocks (§6.3 proof shape, §6.7 instance form, §6.1 motive
  shape); (c) if any `example` fails, T5.0 reports the
  divergence, the implementation phase pauses, and the spec
  is revised via a follow-up adversarial round before any
  T5.A/B/C commit; (d) the scratch file is not committed.
- **N4 — Resolved.** §6.1 commits to the spell-out lift
  function form (the `{ hom, depth_witness }` builder is
  spelled out in the motive); only the well-definedness proof
  is left as a single underscore. Cross-checked against
  `ErToKFunctor.lean:99–114`: the spelled-out form in §6.1
  is character-identical to the actual lift, so elaboration
  unifies on the lift slot by `rfl` and only the
  well-definedness slot needs inference. The mirror at
  `LawvereKSimER.lean:497–501` follows the same pattern
  (spell-out lift, underscore for well-definedness),
  confirming the convention.
- **N5 — Resolved.** §6.6 cites
  `Mathlib/CategoryTheory/EqToHom.lean` inline at the
  `eqToIso_symm` / `eqToIso_hom` invocation.

### N6 — §5 / §11.10 LOC estimate for T5.C inconsistent

**Location**: §5 table (T5.C row) and §11.10 punch list.

**Claim in spec**: §5's table gives T5.C ≈ 45 LOC. §11.10's
"LOC estimates plausible" claim quotes "T5.C ≈ 60".

**Observation**: The two figures should match; §11.10 is the
adversary's check that the §5 table's numbers are sound, but it
quotes a different number from the §5 table. The discrepancy
likely originates from round-2 fixes (S6 added two explicit
instances to T5.C, raising the LOC estimate). Either §5 was
updated and §11.10 was not, or vice versa.

This is purely a spec-internal arithmetic mismatch; it does
not affect implementation correctness. The implementer reads
§5 as the canonical task table.

**Recommendation**: Reconcile the two figures. Either bump §5's
T5.C row to ≈ 60 (consistent with §11.10) or lower §11.10's
quote to ≈ 45 (consistent with §5). Either choice is acceptable.

### N7 — §3 `Equivalence.lean` LOC delta does not add up from §5

**Location**: §3 table (`GebLean/LawvereERKSim/Equivalence.lean`
row) and §5 task table (T5.B.1 + T5.B.2 + T5.C rows).

**Claim in spec**: §3 states `Equivalence.lean` is "≈ 130" LOC.
§5 splits this file's content across T5.B.1 (≈ 60),
T5.B.2 (≈ 12), T5.C (≈ 45 in §5; ≈ 60 in §11.10 per N6). Sums:
60 + 12 + 45 = 117; 60 + 12 + 60 = 132.

**Observation**: With §5's 45-figure for T5.C, the sum (117) is
shy of §3's 130 by 13 LOC. With §11.10's 60-figure (per N6),
the sum (132) is within 2 LOC of §3's 130. The §3 figure of 130
is therefore consistent with the §11.10 reading, not the §5
reading.

This is purely arithmetic; the discrepancy is ≤ 13 LOC and
within the ±50% LOC-estimate envelope §11.10 sets for
adversarial review. Implementation does not turn on this.

**Recommendation**: After resolving N6, reconcile §3's 130 with
the chosen T5.C figure (130 fits the 60-figure resolution
directly; the 45-figure resolution requires reducing §3's
estimate to ≈ 117 or accepting the gap as within budget).

## Convergence verdict

CONVERGED — 0 blockers, 0 serious, 0 minor, 2 nits. The two
nits are spec-internal LOC-arithmetic inconsistencies (N6 and
N7) that do not affect implementation correctness; they can
either be applied as a single small reconciliation edit or
accepted as within the ±50% LOC envelope §11.10 itself sets.

No unaddressed round-1 or round-2 findings remain.
