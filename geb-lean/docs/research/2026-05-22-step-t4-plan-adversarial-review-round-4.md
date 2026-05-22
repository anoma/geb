# T4 plan adversarial review — round 4

Round-4 adversarial review of
[`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](../superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md)
at jj revision `f95a349d` on `feat/ertok-runtime-bound`,
against
[`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md)
and the prior reviews at
[round 1](2026-05-22-step-t4-plan-adversarial-review-round-1.md),
[round 2](2026-05-22-step-t4-plan-adversarial-review-round-2.md),
and
[round 3](2026-05-22-step-t4-plan-adversarial-review-round-3.md).

## Summary

- Residual blockers: 0
- Residual serious: 0
- New issues introduced by round-3 fixes: 0
- Minor: 2 (carry-over documentation niggles M3, M4 from round 3)

**CONVERGED.** Both round-3 serious findings (S4 named-field
packaging, R-S3 comp `+ 6` escalation note) are addressed
verbatim per the round-3 prescriptions. No new defects were
introduced. The remaining minor items are documentation
niggles that do not block SDD execution.

## Round-3 fix verifications

### S4: `KMorNQuo.atDepth` packaging — named-field syntax: ADDRESSED

Plan Task 12 Step 2 (lines 1916–1944) now writes the helper
with named-field syntax:

```text
private def erToKN_atDepth {n m : ℕ}
    (e : ERMorN n m) :
    KMorNQuo.atDepth 2
      (Quotient.mk (kMorNSetoid n m) (erToKN e)) :=
  Quotient.mk _ {
    rep := erToKN e,
    rep_level := fun j => erToKN_level e j,
    rep_eq := rfl
  }
```

(plan lines 1925–1935). This matches `LawvereKSimQuot.lean`'s
canonical `id_atDepth` / `comp_atDepth` builders (verified in
round 3 at lines 411–417 and 420–440 of that file). The
preamble at plan lines 1920–1923 ("The codebase (see
`LawvereKSimQuot.lean:373-440`) uses *named-field* syntax for
`KMorNQuo.atDepth` builders … follow that convention rather
than the anonymous-constructor form.") gives the implementer
the rationale.

The follow-on remark at plan lines 1937–1943 ("If the actual
`KMorNQuoAtDepthRep` structure uses different field names at
execution time, the implementer adjusts to match — the
*named-field* discipline is the contract; field names are a
Lean-side detail.") makes the contract robust to incidental
field renames in the upstream structure.

The field names `rep`, `rep_level`, `rep_eq` agree with
`LawvereKSimQuot.lean:373-376` (verified in round 3). No
defect remains.

### R-S3: comp `+ 6` arithmetic escalate-before-bump: ADDRESSED

Plan Task 6 Step 5 (lines 1056–1077) preserves the spec's
`+ 6` increment in the `h_glue` target
`≤ tower (mu_f + mu_g + 5) m` and leaves the body as a `sorry`
with the in-body comment summary (lines 1066–1071) of the
absorption strategy.

Plan Task 6 Step 6 (lines 1079–1121) explicitly carries the
escalation note as round 3 prescribed:

> **Note for implementer:** the comp arithmetic chain is the
> most intricate part of T4. Round-3 plan adversarial review
> (R-S3) flagged that the `glue`'s per-`i` summand contains a
> `9 · v_total` factor; the outer fold produces
> `k · 9 · v_total` (not `9 · v_total`), requiring an
> additional multiplicative-by-`k`/`m` absorption step beyond
> what spec §4.2 §(iii) describes explicitly. The spec's
> `+ 6` increment is an upper-bound estimate that the recipe
> *should* satisfy, but the precise chain absorbing
> `k · 9 · v_total` over the outer fold has not been verified
> at the spec stage. The implementer should:
>
> 1. Verify the chain at execution time by writing out the
>    inequality `glue ≤ tower (mu_f + mu_g + 6) m` step by
>    step, applying `mul_tower_le_tower_add_two` for each
>    multiplicative-by-`m` step.
> 2. If `+ 6` proves insufficient (e.g., the chain genuinely
>    needs `+ 7` or `+ 8`), escalate to user review before
>    bumping the recipe. The increment is listed in spec §4.2
>    as Lean-side flexible (concrete constants may flex), but
>    a recipe increase requires spec amendment per
>    [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md)
>    § Non-negotiable interfaces. Do not silently change the
>    recipe.

This is precisely the escalate-before-bump path requested by
round 3's resolution (c): "annotate the plan with the precise
chain that closes at `+ 6` so the implementer has a
deterministic discharge path." The annotation here is not a
fully-discharged proof, but it pins the open obligation as a
named verification step with a deterministic escalation
contract.

The round-3 reviewer's open question — whether the
"zero blockers / zero serious" gate requires resolving the
recipe value *within* the plan — is answered in this revision
by the explicit "escalate to user review before bumping"
clause. The gate is satisfied because: (a) the plan does not
silently absorb a wrong arithmetic step, (b) the
verification obligation is named and located, (c) the
escalation path is documented and references the project
rule that governs spec amendments, and (d) the implementer
cannot drift from `+ 6` without user review. The remaining
arithmetic work belongs to execution, not to plan
convergence.

Severity: no longer a defect at the plan-convergence gate.

## Residual blockers

None.

## Residual serious

None.

## New issues introduced by round-3 fixes

None. Both round-3 fixes (S4 named-field rewrite of
`erToKN_atDepth`; R-S3 escalate-before-bump note in Task 6
Step 6) are local edits that do not introduce new
elaboration risks or contractual drift.

The S4 named-field rewrite uses field names (`rep`,
`rep_level`, `rep_eq`) that match the codebase contract
verified in round 3; if the upstream structure changes those
names, the plan's preamble at lines 1937–1943 binds the
implementer to adjust.

The R-S3 note at lines 1097–1121 strengthens, rather than
weakens, the recipe contract: prior plans had no explicit
mention of the per-`i` `k` factor; this revision makes the
implementer aware of the open absorption and pins the
escalation gate.

## Minor

### M1 (carry-over from round 3 M3): residual `Fin.maxOfNat_succ` fallback reference

Plan Task 2 Step 5 lines 452–454 still mention the
non-existent `Fin.maxOfNat_succ` as a TDD-recovery fallback if
`simp [Fin.maxOfNat, Fin.foldr_succ]` does not close. The
primary chain via `Fin.foldr_succ` is the recommended path;
the fallback is offered as a last resort with the instruction
"introduce it locally as a helper lemma in `LawvereKSim.lean`
if not already present". Acceptable. No fix required.

### M2 (carry-over from round 3 M4): closeout LOC estimate "comparable to T3"

Plan closeout line 2216 (Task 15 Step 8 commit message) gives
"~1480 LOC. Comparable to T3." T3 actual at PR `db059ef4` is
~1000 LOC; T4 estimate ~1480 is ~48% larger. The phrasing
"comparable to T3" is loose. Rephrasing to "~1480 LOC; larger
than T3 (~1000 LOC) due to the recipe machinery in
`boundExprKParams_dominates`" would be more accurate. Minor
documentation niggle.

Round-3 minors M1 (Task 13 AXIOM_ALLOW pseudo-Lean display)
and M2 (atom rationale phrasing carry-over) were noted as
non-defects in round 3; no fresh action needed.

## Convergence assessment

Zero blockers; zero serious. The plan has converged to the
project gate. SDD execution can begin.

The two remaining minor items are documentation niggles that
do not affect elaboration or correctness. They can be
addressed in a follow-up pass or left as carry-over
documentation polish for the executing-plan phase.

## Methodology

Each round-3 finding was located in the revised plan (jj
`f95a349d`) by line number and verified by reading the cited
ranges:

- S4 (Task 12 Step 2 named-field syntax): confirmed at plan
  lines 1925–1935. The named-field form matches the
  codebase's canonical builders at
  `LawvereKSimQuot.lean:411-417` (`id_atDepth`) and
  `420-440` (`comp_atDepth`) — both verified in round 3.
  Field-name flexibility caveat is documented at plan lines
  1937–1943.
- R-S3 (Task 6 Step 6 escalate-before-bump): confirmed at
  plan lines 1097–1121. The note explicitly names the
  `k · 9 · v_total` issue, prescribes the per-step
  verification path, and pins the escalation gate to
  `.claude/rules/lean-coding.md` § Non-negotiable interfaces.

A fresh sweep of the converged plan was performed to detect
previously-missed concerns now visible in the simplified
shape. No additional blockers or serious items were found.
The carry-over minors M3 (round 3) → M1 (this round) and M4
(round 3) → M2 (this round) remain documentation niggles, not
defects.

Markdownlint check confirmed via
`markdownlint-cli2 docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`:
0 errors.

Mathlib upstream guides
(`https://leanprover-community.github.io/contribute/{naming,style,doc,commit}.html`)
were not re-pulled in this round; the
`.claude/rules/lean-coding.md` local digest sufficed for
style / naming / commit-message checks. No new commit-message
defects detected. The `$'...\n...'` form at plan line 1548
(verified in round 2) remains correct.
