# T5 equivalence plan — adversarial review round 5

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings](#findings)
  - [Round-4 status](#round-4-status)
  - [New findings](#new-findings)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

Verdict: CONVERGED — 0 blockers, 0 serious, 0 minor, 0 nits.

All four round-4 findings (B6, S1, S2, N1) are resolved at the
documented load-bearing surfaces. Active MCP verification of
the full T5 stack — T5.A.1, T5.A.2, T5.B.1 (both directions,
real proofs), T5.B.2, T5.C `Equivalence.mk'` with the minimal
explicit fifth-argument discharge, and both explicit
`IsEquivalence` instances — succeeds end-to-end with
`success: true` and zero diagnostics.

Residual `cat_disch` / `eqToIso.hom` / `eqToIso.inv` mentions
in both files are confined to expository content that
explains why the explicit fifth argument is load-bearing and
why the smaller simp set suffices. That material is
persistent, technically accurate, and necessary for a future
reader to understand the proof-strategy choice; it is not
stale text.

## Methodology

1. Read the revised plan
   ([`2026-05-25-step-t5-equivalence-plan.md`](2026-05-25-step-t5-equivalence-plan.md))
   end-to-end.
2. Read the revised spec
   ([`2026-05-25-step-t5-equivalence-design.md`](../specs/2026-05-25-step-t5-equivalence-design.md))
   end-to-end, focusing on the four sites the round-5 prompt
   names: spec §3 module-docstring narrative, spec §5 T5.0
   table row, spec §6.6, spec §11.8, plan Task 3 Step 1
   module-docstring template, plan Task 5 Step 1 code, plan
   Task 5 Step 2 prose.
3. Read all four prior plan reviews and three prior spec
   reviews to enumerate every prior finding and its resolution
   target.
4. Re-fetched the four mathlib upstream guides via the in-repo
   digest at `.claude/rules/lean-coding.md` § Authoritative
   upstream guides; cross-checked commit-message conventions,
   declaration-name conventions, docstring-section
   conventions.
5. Active MCP integration test (round-5 prompt check 5): ran
   the full T5 stack — T5.A.1 `erToKFunctor_map_interp`, T5.A.2
   `erToKFunctor_comp_kInterpFunctor`, T5.B.1
   `erToKFunctor_comp_kToERFunctor` and
   `kToERFunctor_comp_erToKFunctor` (the real
   `Functor.hext + hcongr_hom + Faithful.map_injective` proof
   shape, not axiomatised), T5.B.2 isos, T5.C `erKSimEquiv` via
   `Equivalence.mk'` with the minimal discharge
   `(by intro X; simp [erToKKToErIso, kToErErToKIso])`, and
   both `IsEquivalence` instances — via
   `mcp__lean-lsp__lean_run_code`. Result: `{"success": true,
   "timed_out": false, "diagnostics": []}`.
6. Sweep search of plan and spec for `cat_disch`,
   `eqToIso.hom`, `eqToIso.inv`, `§6.7's typeclass-search`
   (round-5 prompt check 7). Catalogued each hit and
   classified as either expository (load-bearing technical
   explanation, persistent content) or stale (pre-round-3
   residue). All hits classified as expository; see Round-4
   status below.
7. Cross-checked B6 (plan Task 3 Step 1 module-docstring
   template) location: the `## Implementation notes` section
   at plan lines 575–595 now describes the explicit fifth
   argument as the discharge mechanism, with `cat_disch`
   mentioned only as the alternative that was tested and
   rejected.
8. Cross-checked S1 (spec §3 module-docstring narrative):
   spec line 166 now reads "the explicit triangle-discharge
   `simp` recipe per §6.6".
9. Cross-checked S2 (spec §5 T5.0 table row): spec line 248
   now reads "§6.1's motive-elaboration shape" in the
   deliverable cell.
10. Cross-checked N1 (simp set minimality): spec §6.6 line
    522, spec §11.8 line 833, plan Task 5 Step 1 line 870,
    plan Task 5 Step 2 line 882 all use the minimal form
    `[erToKKToErIso, kToErErToKIso]`. MCP verification
    confirmed this discharges the triangle with no
    diagnostics under the current pin.
11. Cross-checked commit-message conventions against
    `commit.html`: all five suggested subjects in spec §10 and
    plan Tasks 1–5 are lowercase, imperative present tense, no
    trailing period, ≤ 72 chars including prefix.
12. Cross-checked banned-command compliance: no `lake env
    lean`, no `lake clean`, no bash process substitution, no
    raw mutating `git`. Compliant.
13. Cross-checked markdownlint cleanliness by structural
    inspection: heading hierarchy, code-fence languages, list
    indentation, line lengths. No violations spotted.
14. Cross-checked Task 0 step numbering against round-4's
    confirmed renumbering (1, 2, 2.5, 3, 4, 5, 6, 7): Step 5
    = §6.1 motive stub, Step 6 = combined-buffer type-check,
    Step 7 = `jj status`. Match.
15. Cross-checked plan TOC at lines 46–55 against actual
    section structure. Match.

## Findings

### Round-4 status

- **B6 — RESOLVED.** Plan Task 3 Step 1 module-docstring
  template (lines 575–595) now describes the discharge as:
  "The `functor_unitIso_comp` obligation is discharged by an
  explicit fifth argument `(by intro X; simp [erToKKToErIso,
  kToErErToKIso])` — the `cat_disch` autoparam alone is
  insufficient here because it cannot unfold the two
  `def`-bound natural isomorphisms `erToKKToErIso` and
  `kToErErToKIso` (each defined via `eqToIso`)." The
  `cat_disch` mention is now expository, describing the
  rejected alternative — not the chosen discharge mechanism.
  This is persistent technical content per
  `.claude/rules/lean-coding.md`, equivalent in form to the
  spec §6.6 narrative.
- **S1 — RESOLVED.** Spec §3 line 166 now reads:
  "`## Implementation notes` (commits to the
  `Equivalence.mk'` constructor choice and the explicit
  triangle-discharge `simp` recipe per §6.6)". No `cat_disch`
  mention.
- **S2 — RESOLVED.** Spec §5 line 248 (T5.0 row) now reads:
  "stub type-check of §6.3's proof shape and §6.1's
  motive-elaboration shape". The "§6.7's typeclass-search
  assumption" phrasing is gone. Consistent with the prose
  paragraph at spec lines 258–271.
- **N1 — RESOLVED.** All four sites — spec §6.6 line 522,
  spec §11.8 line 833, plan Task 5 Step 1 line 870, plan Task
  5 Step 2 line 882 — use the minimal simp set
  `[erToKKToErIso, kToErErToKIso]`. Plan Task 5 Step 2 (line
  883) records the minimality observation: "is the minimal
  simp set (adding `eqToIso.hom` or `eqToIso.inv` would
  trigger `unusedSimpArgs` warnings)". Spec §6.6 line 534
  records the same. MCP-confirmed: the minimal form
  elaborates with `success: true` and zero diagnostics, while
  the full T5 stack (T5.A.1 → T5.A.2 → T5.B.1 → T5.B.2 → T5.C
  with both `IsEquivalence` instances, using the real proof
  shapes throughout) also elaborates with zero diagnostics.

### New findings

None. All round-5 prompt checks pass:

- Check 1 (B6 status): verified — plan Task 3 Step 1
  docstring template describes the explicit fifth argument.
- Check 2 (S1 status): verified — no remaining `cat_disch`
  mention in spec §3 narrative.
- Check 3 (S2 status): verified — no remaining
  "§6.7's typeclass-search assumption" mention in spec §5
  table.
- Check 4 (N1 status): verified — minimal simp set at all
  four sites, MCP-confirmed.
- Check 5 (integration check): verified — full T5 stack
  elaborates end-to-end with `success: true`, zero
  diagnostics.
- Check 6 (standard checks): spec coverage matches plan task
  decomposition; no value-laden adjectives spotted; AXIOM_ALLOW
  comments present on every applicable declaration per spec
  §7's table; commit messages conform; banned commands
  absent; naming consistent with mathlib conventions and
  project precedent.
- Check 7 (stale-text sweep): every remaining `cat_disch` /
  `eqToIso.hom` / `eqToIso.inv` mention is in expository
  content explaining either why the explicit fifth argument
  is required (spec §6.6 lines 491, 507–511; spec §11.6 line
  804; spec §11.8 lines 835, 846; plan Task 3 Step 1 lines
  588–589; plan Task 5 Step 1 lines 858–859) or why the
  smaller simp set suffices (spec §6.6 line 535; plan Task 5
  Step 2 line 885). All such mentions are persistent
  technical content, not pre-round-3 residue.

## Convergence verdict

CONVERGED — 0 blockers, 0 serious, 0 minor, 0 nits.

All four round-4 findings (B6 blocker, S1 / S2 serious, N1
nit) are resolved at the documented load-bearing surfaces:
the plan Task 3 Step 1 module-docstring template describes
the explicit fifth argument, spec §3 omits the stale
`cat_disch` reference, spec §5 T5.0 row references the §6.1
motive-elaboration shape, and all four simp-set sites use the
minimal form `[erToKKToErIso, kToErErToKIso]`.

Active MCP verification confirms the minimal simp set
discharges the `functor_unitIso_comp` obligation with zero
diagnostics, and the full T5 stack (T5.A.1 → T5.C, including
both explicit `IsEquivalence` instances) elaborates
end-to-end with zero diagnostics.

No unaddressed prior findings remain across rounds 1–4 of
either the spec or the plan. The plan and spec are converged
and ready for execution.
