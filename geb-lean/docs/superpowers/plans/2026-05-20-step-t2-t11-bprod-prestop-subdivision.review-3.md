# Round 3 adversarial review — bprod pre-stop sub-division

Review target:
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
post round-2 fixes (commit `dc9d6649`). Reviewer scope:
verification of the two round-2 severity-1 fixes and five
round-2 severity-2 fixes, plus a fresh defect sweep for issues
introduced by the round-2 fixes or missed in earlier rounds.
Cross-checks: the landed `compileFrag_bsum_size`
(`Compiler.lean` line 1113), the structure declaration at
plan line 850, and the round-2 review document.

## Severity 1 — blocking defects

None. The two round-2 severity-1 defects are fixed.

## Severity 2 — important corrections

1. **Phase_i3 clause-count audit still mis-splits the invariant
   structure.** Plan line 1163 now reads
   `The per-clause split is 2 + 5 + 5 = 12`. The five
   "via accUpdate" clauses are enumerated at lines 1180-1186
   as `accClone_zero, factor_zero, mulTmp_zero, acc_eq` plus
   "f-output zero (a corollary of factor_zero and the prep
   destructive copy)". The structure declaration at lines
   860-872 carries exactly 12 fields: `hi_le, pc_eq,
   zReg_zero, outer_inputs, vX_eq, vI_eq, tmp1_zero,
   tmp2_zero, accClone_zero, factor_zero, mulTmp_zero,
   acc_eq` — 12 fields. The plan explicitly states at lines
   1190-1193 that "`hi_le` is a Prop parameter carried via the
   structure's default value, not a state-bearing clause; it
   does not count toward the 12-clause split". With `hi_le`
   excluded, the data-clause count is 11, not 12. The
   `2 + 5 + 5 = 12` arithmetic is being made to balance only
   by counting `f-output zero` as a member of the
   accUpdate-established set, but the plan itself flags
   `f-output zero` at lines 1183-1186 as "not an invariant
   clause but… needed for the next iteration's phase_i0
   zero-sweep". A non-clause cannot contribute to a
   clause-count split. The corrected split is either
   `2 + 4 + 5 = 11` (excluding `hi_le` and `f-output zero`,
   matching the structure's data-clause count) or
   `2 + 5 + 5 = 12` (counting `hi_le` and dropping
   `f-output zero`). Recommended: rewrite the prose at lines
   1163-1167 to use the `2 + 4 + 5 = 11` split, and
   relocate the `f-output zero` reasoning to a separate
   paragraph identified as a phase_i3 post-state supplement
   (consumed only by the next phase_i0). Subsidiary
   correction at line 1199: "These four zero-state facts
   plus `acc_eq`" should read "These three zero-state facts
   (`accClone_zero`, `factor_zero`, `mulTmp_zero`) plus
   `acc_eq` constitute the four 'via accUpdate' clauses".

2. **Sub-task 1.c.1's docstring is now internally inconsistent
   with sub-task 1.c.3's preservation conjunct.** Plan line
   574 says "Preservation of the four mul-scratch registers'
   surroundings is *not* a clause of the structure". Plan
   line 698 says "three registers, not four (`V_acc_clone` =
   k+7 is read-only inside the inner loop, since
   `preservingTransfer` preserves its source)". The two counts
   refer to the same set of registers (the inner-mul block's
   written-to registers); 1.c.1's "four" is incorrect.
   Recommended: change "four mul-scratch registers" to "three
   mul-scratch registers" at line 574, and add a brief note
   that `V_acc_clone` is read-only inside the inner loop
   (mirroring 1.c.3's note).

3. **Sub-task 0's `bprod_exitPC` documentation gap (cosmetic,
   bordering Sev 2).** Plan lines 358-361 explain that
   `bprod_trBase`'s use of `frag_f.instrs.size - 1` is safe
   under `lastInstr_isStop`. By contrast, `bprod_exitPC`'s
   use of `bprod_trBase frag_f + 23` (line 322) carries no
   such note about whether the `+ 23` matches the canonical
   `instrs.size - 1` predecessor. The size lemma
   `bprod_exitPC_eq_size_pred` at lines 330-333 is the
   formal counterpart, but the inline prose would benefit
   from a one-line annotation that `bprod_exitPC` *equals*
   `instrs.size - 1` by `bprod_exitPC_eq_size_pred`. This
   matters because two distinct downstream lemmas
   (bprod.3.phase_i3, bprod.6) consume the equation as a
   precondition for the final-`stopR` discharge.

## Severity 3 — minor / cosmetic

1. **Followup item 3's "structurally analogous" still reads
   slightly awkwardly in context.** Line 1510: "structurally
   analogous to bsum's pre-stop chain". The phrase is correct
   but the prose around it on lines 1509-1514 reads as a
   list of structural ingredients; consider tightening to
   "the inner-mul loop's structure (jumpZR + decR +
   preservingTransfer + goto over a counter `j`) is the
   same as bsum's outer loop".

2. **Sub-task 1.c.0's docstring note is present but verbose.**
   Plan lines 528-538. The note correctly records the design
   decision (per round-2 Sev 3 item 2). The paragraph could
   be tightened to a single sentence: "The preservation
   conjunct excludes f-body non-output registers; their
   preservation is delegated to phase_i2's `f_other_zero`
   carry-over."

3. **Summary intro line 35 mentions "seventeen
   implementer-sized sub-tasks" but the DAG enumerates 18
   sub-tasks** when counting bprod.1.c.0 through bprod.1.c.4
   as five tasks (plus 0, 1.a, 1.b, 1.d, 2, 3.phase_i0,
   3.phase_i1, 3.phase_i2, 3.phase_i3, 4, 5, 6 = 13 + 5 =
   18). Or, if 1.c.0 through 1.c.4 are counted as a single
   "1.c" task subdivided five ways, the chain enumerates 14
   sub-tasks. Either count is reasonable; the 17 figure
   matches neither. Recommended: update the count to 18 (or
   to the canonical "thirteen outer plus five accUpdate
   internal sub-tasks" phrasing).

## Confirmed correct

The following round-2 fixes were verified sound:

- **Round-2 Sev 1 #1 (`f` argument at all five sites).** All
  five occurrences of
  `compileFrag_bprod_partial_invariant (compileERFrag f)`
  at lines 880, 1132, 1234, 1287, 1301 are followed by
  `f v` in the canonical argument order. Cross-check against
  the structure declaration at lines 850-872 confirms the
  signature `(frag_f) (f) (v) (i) (hi) (s)`.
- **Round-2 Sev 1 #2 (inner-mul preservation propagation).**
  The plan at lines 694-702 explicitly states that each of
  `compileFrag_bprod_mul_partial_step`,
  `compileFrag_bprod_mul_partial_aux`, and
  `compileFrag_bprod_mul_partial` carries the preservation
  conjunct excluding `r.val ≠ 1, ≠ k+8, ≠ k+9` (three
  registers, with the noted exception that `V_acc_clone`
  is read-only inside the inner-mul loop because
  `preservingTransfer` preserves its source). The
  composition at lines 788-799 (1.c.4) combines the prep
  exclusion list `{V_acc (1), V_acc_clone (k+7),
  V_factor (k+8), f-output (k+10 + outputReg)}` (four
  registers) with the inner-mul exclusion list
  `{V_acc (1), V_factor (k+8), V_mul_tmp (k+9)}` (three
  registers) to obtain the union
  `{V_acc, V_acc_clone, V_factor, V_mul_tmp, f-output}`
  (five registers), matching the 1.c.4 conjunct at lines
  751-757.
- **Round-2 Sev 2 #1 (`bprod_exitPC - 1` typo).** Plan line
  1258 now reads
  `to the step-level bound < bprod_exitPC (equivalently
  < instrs.size - 1)`. The `- 1` is removed.
- **Round-2 Sev 2 #4 (size lemma co-location).** Verified
  via `grep -n compileFrag_bsum_size GebLean/LawvereERKSim/`:
  `Compiler.lean:1113:theorem compileFrag_bsum_size` is the
  declaration site, and `BSum.lean:163, 168, 4808` are
  consumption sites only. The bsum size lemma lives in
  `Compiler.lean` co-located with `compileFrag_bsum`, and
  the plan's claim that the bprod size lemma will
  similarly land in `Compiler.lean` (lines 336-341) is
  consistent with the bsum analogue. The round-2
  reviewer's recommendation was incorrect; no plan
  revision is needed for this item.
- **Round-2 Sev 2 #5 (1.c.4 five-register conjunct prose).**
  Plan lines 788-799 enumerate five register exclusions
  (`V_acc`, `V_acc_clone`, `V_factor`, `V_mul_tmp`,
  f-output) consistently. The earlier reference to "four
  mul-scratch registers" at the deleted location is gone.
  However, 1.c.1's docstring at line 574 still references
  "four mul-scratch registers" (logged as Sev 2 #2 above).
- **Round-2 Sev 3 #3 (followup item 3 "miniature" →
  "structurally analogous").** Plan line 1510 now reads
  "structurally analogous to bsum's pre-stop chain". The
  word "miniature" no longer appears in this context (it
  remains in the document summary at line 69 in a
  different context, "on a miniature scale", referring to
  the accUpdate's internal structure).
- **Round-2 Sev 3 #2 (1.c.0 docstring note).** Plan lines
  528-538 carry a note that the preservation conjunct does
  not assert preservation of f-body non-output registers,
  with a forward reference to `f_other_zero` in phase_i2.
- **Markdownlint cleanliness.** `markdownlint-cli2
  docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
  reports `Summary: 0 error(s)`.
- **Preservation-conjunct register counts.** The inner-mul
  body writes to `V_acc` (preservingTransfer destination),
  `V_factor` (decR), and `V_mul_tmp` (preservingTransfer
  scratch). Reads: `V_factor` (jumpZR, decR),
  `V_acc_clone` (preservingTransfer source). The
  preservation conjunct correctly excludes the three
  written registers; `V_acc_clone` is read-only and
  therefore preserved, consistent with the invariant's
  `acc_clone_eq` carrying value `vAccIn` unchanged through
  the inner loop.

## Summary

CONVERGED. The round-2 fixes for both severity-1 defects
are correct and complete. The size-lemma co-location
question (round-2 Sev 2 #4) is resolved in favour of the
plan's original wording. Three severity-2 items remain
(phase_i3 clause-count split arithmetic; 1.c.1 docstring
inconsistency with 1.c.3's "three not four" correction;
optional `bprod_exitPC = instrs.size - 1` annotation in
sub-task 0). All three are local prose-level corrections
that do not block execution; they can be addressed
inline during sub-task implementation or in a final
round-4 pass at the author's discretion. No new severity-1
defects were introduced by the round-2 fixes.
