# T5 equivalence plan — adversarial review round 4

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings](#findings)
  - [Round-3 status](#round-3-status)
  - [B6 — Stale `cat_disch` claim in committed `Equivalence.lean` docstring](#b6--stale-cat_disch-claim-in-committed-equivalencelean-docstring)
  - [S1 — Spec §3 module-docstring template still names `cat_disch`](#s1--spec-3-module-docstring-template-still-names-cat_disch)
  - [S2 — Spec §5 T5.0 row still lists the §6.7 stub](#s2--spec-5-t50-row-still-lists-the-67-stub)
  - [N1 — `eqToIso.hom` and `eqToIso.inv` are redundant in the simp set](#n1--eqtoisohom-and-eqtoisoinv-are-redundant-in-the-simp-set)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

Verdict: BLOCK — 1 blocker, 2 serious, 0 minor, 1 nit.

All three round-3 blockers (B3 `cat_disch` failure for the real
`erKSimEquiv`, B4 broken fallback recipes, B5 opaque-variable
stub failure) are resolved at the load-bearing code surface:

- Spec §6.6 and plan Task 5 Step 1 now both carry the explicit
  fifth argument
  `(by intro X; simp [erToKKToErIso, kToErErToKIso,
  eqToIso.hom, eqToIso.inv])`.
- Plan Task 0's §6.7 instance-availability stub is gone; the
  steps are correctly renumbered (Step 5 = §6.1 motive stub,
  Step 6 = combined-buffer type-check, Step 7 = `jj status`).
- Spec §11.8 is updated to the explicit-discharge claim.
- Spec §5's prose paragraph at lines 257–270 correctly lists
  only the §6.3 and §6.1 stubs.
- Plan Task 5 Step 2 prose no longer references fallback
  recipes.

Active MCP verification (check 7 below) confirms the full T5
stack — T5.A.1 `erToKFunctor_map_interp`, T5.A.2
`erToKFunctor_comp_kInterpFunctor`, T5.B.1 round-trip strict
equalities (both directions, full proofs, not axiomatised),
T5.B.2 named natural isos, T5.C `erKSimEquiv` via
`Equivalence.mk'` with the explicit discharge, and both
explicit `IsEquivalence` instances — elaborates end-to-end
with no diagnostics. This is the strongest MCP-level
verification short of a `lake build`.

However, round-4 review surfaces one new blocker (B6) and two
new serious findings (S1, S2), each a stale `cat_disch`-era
reference the author missed when updating §6.6 / Task 5
Step 1. The blocker (B6) is load-bearing because the stale
text is inside the module docstring the plan instructs the
implementer to write verbatim into a committed Lean source
file; the docstring contradicts the actual code body in the
same file. S1 and S2 are spec-level inconsistencies that
would mislead a future reader but do not break code
elaboration.

One nit (N1) records a thoroughness finding: MCP verification
shows that `eqToIso.hom` and `eqToIso.inv` are unnecessary in
the simp set — the two `def`-bound natural-iso unfolds alone
suffice. This is a minor surface simplification, not a
correctness issue; per the round-4 prompt's check 6, a smaller
working set is a nit, not a blocker.

## Methodology

1. Read the revised plan
   ([`2026-05-25-step-t5-equivalence-plan.md`](2026-05-25-step-t5-equivalence-plan.md))
   end-to-end.
2. Read the revised spec
   ([`2026-05-25-step-t5-equivalence-design.md`](../specs/2026-05-25-step-t5-equivalence-design.md))
   end-to-end, focusing on §§3, 5, 6.6, 6.7, 11.8.
3. Read all three rounds of prior plan and spec reviews
   (`.review-1.md`, `.review-2.md`, `.review-3.md` on each).
4. Re-fetched the four mathlib upstream guides via the in-repo
   digest at `.claude/rules/lean-coding.md` § Authoritative
   upstream guides; cross-checked against the revised plan's
   commit messages and the spec's declaration names.
5. Active MCP verification of the load-bearing discharge
   (round-4 prompt check 1): assembled `erToKKToErIso`,
   `kToErErToKIso`, `erKSimEquiv` via `Equivalence.mk'` with
   the explicit fifth argument, plus both `IsEquivalence`
   instances, against axiomatised `erToKFunctor_comp_kToERFunctor`
   and `kToERFunctor_comp_erToKFunctor`. Result: `success: true`,
   no diagnostics.
6. Active MCP minimality probe of the simp set (round-4 prompt
   check 6): tested removal of each of the four lemmas
   individually, then in combination.

   - Drop `erToKKToErIso`: fails (unsolved goal on the unit
     side).
   - Drop `kToErErToKIso`: fails (unsolved goal on the counit
     side).
   - Drop `eqToIso.hom`: succeeds.
   - Drop `eqToIso.inv`: succeeds.
   - Drop both `eqToIso.hom` and `eqToIso.inv`: succeeds.
   - Drop one of the iso unfolds: fails for both choices.
   - Plain `simp` with no extra lemmas: fails for all
     configurations.

   Conclusion: the minimal working set is
   `[erToKKToErIso, kToErErToKIso]`. The two `Iso`-projection
   lemmas `eqToIso.hom` and `eqToIso.inv` are redundant —
   `simp` already knows them via mathlib's default tag-based
   collection. See N1.
7. Active MCP integration test against the full landed proofs
   (round-4 prompt check 7): assembled the full T5 stack with
   the actual T5.A.1 `erToKFunctor_map_interp`, T5.A.2
   `erToKFunctor_comp_kInterpFunctor`, T5.B.1
   `erToKFunctor_comp_kToERFunctor` and
   `kToERFunctor_comp_erToKFunctor` (the `Functor.hext +
   hcongr_hom + Faithful.map_injective` proof shape), T5.B.2
   isos, and T5.C packaging + both instances. Result:
   `success: true`, no diagnostics. This is the deepest
   MCP-level integration test; the only step the MCP cannot
   take is `lake build` itself.
8. Searched plan and spec for the strings `cat_disch`,
   `fallback`, `§6.7`, `Step 7`, `Step 8` to detect stale
   references the author may have missed during the
   round-3-to-round-4 update.

   - Plan line 585 (inside the Equivalence.lean module
     docstring template in Task 3 Step 1) still claims the
     triangle is "discharged by the `cat_disch` autoparam".
     Blocker B6.
   - Spec §3 line 165 still describes the module docstring as
     committing to "the `cat_disch` triangle discharge per
     §6.6". Serious S1.
   - Spec §5 row T5.0 (line 247) still describes the
     stub-verification step as "stub type-check of §6.3's
     proof shape and §6.7's typeclass-search assumption", in
     direct contradiction to §5's own prose paragraph at lines
     257–270 (which correctly lists only §6.3 and §6.1).
     Serious S2.
9. Cross-checked commit-message conventions against
   `commit.html`: all-lowercase subject, imperative present
   tense, no trailing period, ≤ 72 chars. All five subjects in
   the plan conform (re-confirmed from round 3).
10. Cross-checked banned-command compliance: no `lake env lean`,
    no `lake clean`, no bash process substitution, no raw
    mutating `git`. Compliant.
11. Cross-checked markdownlint-cleanliness of the plan and
    spec by structural inspection (heading hierarchy, fence
    languages, list indentation). No violations spotted.
12. Verified the plan TOC at lines 49–54 matches the section
    structure at lines 106, 299, 438, 512, 754, 828. Match.
13. Verified Task 0 step numbering (1, 2, 2.5, 3, 4, 5, 6, 7)
    against the prompt's expected renumbering: Step 5 = §6.1
    motive-elaboration stub (matches line 225), Step 6 =
    combined-buffer type-check (matches line 264), Step 7 =
    `jj status` confirmation (matches line 285). Match.

## Findings

### Round-3 status

- **B3 — RESOLVED.** Spec §6.6 (lines 505–524) replaces the
  `cat_disch` claim with the explicit fifth argument
  `(by intro X; simp [erToKKToErIso, kToErErToKIso,
  eqToIso.hom, eqToIso.inv])`. Plan Task 5 Step 1 (lines
  862–871) uses the same form verbatim. Both MCP-verified end
  to end (check 1).
- **B4 — RESOLVED.** Spec §6.6 no longer carries any fallback
  bullets — the explicit discharge is the load-bearing recipe.
  Plan Task 5 Step 2 (lines 873–886) describes the discharge
  as "MCP-verified against axiomatised strict equalities"
  with no fallback prose.
- **B5 — RESOLVED.** Plan Task 0 no longer contains the
  §6.7 instance-availability stub. Renumbering is correct:
  Step 5 = §6.1 motive stub, Step 6 = combined-buffer
  type-check, Step 7 = `jj status` confirmation. Spec §5's
  prose paragraph at lines 257–270 correctly omits §6.7 from
  the stub list (it is verified directly at T5.C `lake build`
  time per the parenthetical).

### B6 — Stale `cat_disch` claim in committed `Equivalence.lean` docstring

**Locations.** Plan Task 3 Step 1, lines 583–587 — inside
the literal-text block the plan instructs the implementer to
write into `GebLean/LawvereERKSim/Equivalence.lean` as the
module docstring.

**Symptom.** The module docstring's `## Implementation notes`
section reads:

> Using `mk'` preserves `erKSimEquiv.unitIso = erToKKToErIso.symm`
> and `erKSimEquiv.counitIso = kToErErToKIso` definitionally.
> The triangle identity `functor_unitIso_comp` is discharged
> by the `cat_disch` autoparam (both unit and counit component
> applications reduce to `eqToHom rfl = 𝟙 _` since both
> functors are identity on objects).

This is a direct copy of the pre-round-3 narrative and is now
factually false: the triangle is NOT discharged by `cat_disch`
(round-3 B3 MCP-confirmed it fails). The actual code in plan
Task 5 Step 1 supplies an explicit fifth argument and the
spec §6.6 prose explains why `cat_disch` is insufficient.

**Why this is a blocker.** The plan instructs the implementer
to write this docstring verbatim into a committed `.lean` file.
The docstring contradicts the same file's `erKSimEquiv`
definition (which supplies the explicit fifth argument).
CLAUDE.md § Style guidelines and `.claude/rules/lean-coding.md`
require docstrings to describe persistent properties of the
code as it is; this docstring describes a hypothetical
`cat_disch` discharge that the code does not use. A reader
inspecting `Equivalence.lean` post-merge would be misled
about the actual proof strategy.

**Fix.** Replace lines 583–587 of the plan with a docstring
sentence that matches the spec §6.6 narrative. Suggested
wording:

```text
Using `mk'` preserves `erKSimEquiv.unitIso = erToKKToErIso.symm`
and `erKSimEquiv.counitIso = kToErErToKIso` definitionally. The
triangle identity `functor_unitIso_comp` is supplied as an
explicit fifth argument (rather than left to the `cat_disch`
autoparam, which cannot unfold `eqToIso.hom` / `eqToIso.inv`
on `eqToIso _ |>.symm`-shaped inputs); the `simp` set unfolds
the two natural-iso definitions and the resulting `eqToHom`s,
reducing the triangle to `𝟙 _` via mathlib's standard category
simp set.
```

This sentence is persistent (it describes the proof strategy
as-is, not transient history) and matches the spec §6.6 trace.

### S1 — Spec §3 module-docstring template still names `cat_disch`

**Location.** Spec §3, line 165.

**Symptom.** Spec §3 describes the planned `Equivalence.lean`
module docstring template:

> The module docstring's sections will be: `# Title`, brief
> summary, `## Main definitions`, `## Main statements`,
> `## Implementation notes` (commits to the `Equivalence.mk'`
> constructor choice and the `cat_disch` triangle discharge
> per §6.6), `## References`, and `## Tags`.

The parenthetical "the `cat_disch` triangle discharge per
§6.6" is stale: §6.6 no longer discharges by `cat_disch`; it
supplies an explicit fifth argument. The parenthetical
should read "the explicit fifth-argument triangle discharge
per §6.6" or similar.

**Why this is serious, not a blocker.** This is spec-side
prose only; it does not migrate verbatim into committed
code. A reader of the spec would be momentarily confused
but would resolve the contradiction by reading §6.6 itself.
The risk surface is small but non-zero (a future
spec-revision pass might propagate the stale phrasing).

**Fix.** Replace "the `cat_disch` triangle discharge per
§6.6" with "the explicit fifth-argument triangle discharge
per §6.6".

### S2 — Spec §5 T5.0 row still lists the §6.7 stub

**Location.** Spec §5, line 247 — the T5.0 row of the
step-decomposition table.

**Symptom.** The table row reads:

> | T5.0 | Baseline verification: `lake build`,
> `scripts/check-axioms.sh`, `markdownlint-cli2`, doctoc-check,
> plus stub type-check of §6.3's proof shape **and §6.7's
> typeclass-search assumption** — all clean on fresh branch
> | 0 | — |

The trailing clause "and §6.7's typeclass-search assumption"
contradicts the same §5's prose paragraph at lines 257–270,
which correctly says:

> The stub contains: one `example` block implementing §6.3's
> proof shape … one `example` block for §6.1's
> `Quotient.inductionOn` motive-elaboration shape. (The §6.7
> instance declarations are not stubbed separately because
> they are one-liners against the concrete `erKSimEquiv`
> value; their elaboration is verified directly at T5.C
> `lake build` time.)

**Why this is serious, not a blocker.** Plan Task 0 Step 5
correctly implements only the §6.1 stub (the §6.7 stub is
deleted, per round-3 B5 resolution); the plan does not
inherit the stale row from the table. A reader of the spec
alone, however, would see contradictory claims about what
T5.0 stubs cover.

**Fix.** Update the table row's "Deliverable" cell to:

> Baseline verification: `lake build`, `scripts/check-axioms.sh`,
> `markdownlint-cli2`, doctoc-check, plus stub type-check of
> §6.3's proof shape and §6.1's motive-elaboration shape —
> all clean on fresh branch

(replacing "§6.7's typeclass-search assumption" with "§6.1's
motive-elaboration shape").

### N1 — `eqToIso.hom` and `eqToIso.inv` are redundant in the simp set

**Location.** Spec §6.6 line 522–523, plan Task 5 Step 1
lines 869–870.

**Symptom.** The explicit fifth-argument form names four
`simp` arguments: `erToKKToErIso`, `kToErErToKIso`,
`eqToIso.hom`, `eqToIso.inv`. MCP verification (check 6):

- Removing `eqToIso.hom` alone: succeeds (with a
  `linter.unusedSimpArgs` warning suggesting omission).
- Removing `eqToIso.inv` alone: succeeds (with the same
  warning).
- Removing both: succeeds.
- Removing one of the iso unfolds: fails (the corresponding
  side of the triangle stays unreduced).

So the minimal working set under the current pin is
`[erToKKToErIso, kToErErToKIso]`. The two
`eqToIso.*` lemmas are already in `simp`'s default tag-based
collection and are pulled in automatically once the iso
unfolds expose them.

**Why this is a nit.** Per the round-4 prompt's check 6:
"If a smaller set works, that's a minor nit. If a larger set
is needed, that's a blocker." The redundancy is harmless
beyond emitting a `linter.unusedSimpArgs` warning at build
time — that warning would not break `lake build` but
contradicts the project's "no warnings other than
AXIOM_ALLOW-suppressed Classical.choice" expectation stated
in plan lines 91–94 ("`lake build` must report no errors
and no warnings (other than the AXIOM_ALLOW-suppressed
Classical.choice usages)").

**Caveat on severity.** If the linter `unusedSimpArgs` is
on by default and fires at warning level, the plan's "no
warnings" expectation is violated, which would re-raise
this to a serious finding or blocker. The author should
either:

- Drop `eqToIso.hom` and `eqToIso.inv` from the simp set
  (preferred — smallest surface), or
- Confirm the linter is disabled / non-default and document
  why the redundant args are retained (e.g., as a defensive
  hedge against future mathlib reorganisations).

The simpler fix is the first. MCP-verified (check 6):

```lean
(by intro X; simp [erToKKToErIso, kToErErToKIso])
```

closes the triangle under the current pin with no warnings.

## Convergence verdict

BLOCK — 1 blocker (B6), 2 serious (S1, S2), 0 minor, 1 nit
(N1).

The load-bearing T5.C surface is correct: §6.6 and Task 5
Step 1 carry the MCP-verified explicit fifth argument, and
the full T5 stack elaborates end-to-end with the actual
landed proof shapes (check 7). All three round-3 blockers
are resolved at the code level.

The single round-4 blocker (B6) is a stale `cat_disch`
sentence inside the committed `Equivalence.lean` module
docstring (Task 3 Step 1 template). It contradicts the code
body in the same file and would mislead a future reader; it
must be replaced before the plan is executed.

S1 (spec §3 module-docstring template still names
`cat_disch`) and S2 (spec §5 T5.0 row still lists the §6.7
stub) are both stale-text artefacts the author missed when
updating the cluster of §§ touched in the round-3-to-round-4
amendment. Neither affects code; both should be fixed for
spec self-consistency.

N1 (redundant `eqToIso.hom` / `eqToIso.inv` simp args) is a
nit per the round-4 prompt rubric — but caveated by the
plan's "no warnings" expectation, which the
`linter.unusedSimpArgs` warning would violate. The author
should drop the two redundant args.

No unaddressed round-1, round-2, or round-3 findings remain
in either the spec or the plan. Round-3 B3 / B4 / B5 are all
resolved at the load-bearing surface; the round-4 findings
are residue from the same amendment pass not propagating
through every stale reference.

Re-dispatch order suggested:

1. Plan amendment: replace lines 583–587's stale `cat_disch`
   docstring sentence with B6's suggested wording.
2. Spec amendment: fix S1 (line 165) and S2 (line 247) per
   the suggested wording.
3. Optional N1 simplification: drop `eqToIso.hom` and
   `eqToIso.inv` from the simp set in both spec §6.6 and
   plan Task 5 Step 1.
4. Round-5 plan and spec re-review (likely brief, since all
   changes are textual).
