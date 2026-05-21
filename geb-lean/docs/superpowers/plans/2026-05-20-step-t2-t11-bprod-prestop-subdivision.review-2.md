# Round 2 adversarial review — bprod pre-stop sub-division

Review target:
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
post round-1 fixes (commit `60e1539c`). Reviewer scope:
verification of the four round-1 severity-1 defect fixes, plus
a fresh defect sweep for issues introduced by the fixes or
missed by round 1. Cross-checks: the landed bsum chain
(`GebLean/LawvereERKSim/BSum.lean`, 5036 lines), the
`compileFrag_bprod` definition (`Compiler.lean` lines
1190-1440), and the round-1 review document.

## Severity 1 — blocking defects

1. **`compileFrag_bprod_partial_invariant` consumer at sub-task
   4 (line 1195) drops the `f` parameter.** The round-1 fix
   added `f` as the second positional argument of the
   invariant structure (between `frag_f` and `v`) and
   threaded it through every other downstream site
   correctly: lines 855 (base), 925-926 (phase_i0), 1107-1108
   (phase_i3 conclusion), 1183-1184 (partial_step h_inv),
   1246 (partial_aux conclusion), 1260 (partial conclusion).
   The single site at line 1195
   (`compileFrag_bprod_partial_step` conclusion) reads
   `compileFrag_bprod_partial_invariant (compileERFrag f) v
   (i.val + 1) ...` — the `f` between `(compileERFrag f)` and
   `v` is missing. Cross-check with the landed bsum analogue
   `BSum.lean` line 4708 confirms the canonical argument
   order is `(compileERFrag f) f v ...`. Recommended
   correction: insert `f` between `(compileERFrag f)` and
   `v` at line 1195.

2. **Sub-task 1.c.3 / 1.c.4 lost the inner-mul preservation
   propagation.** Round-1 fix #3 dropped the
   `outside_preserved` clause from
   `compileFrag_bprod_mul_partial_invariant`. The structure
   now carries only seven clauses (`hj_le, pc_eq, zReg_zero,
   acc_clone_eq, factor_eq, mulTmp_zero, acc_eq`); none of
   them tracks the preservation of registers outside `{1,
   k+7, k+8, k+9, (k+10) + f.outputReg.val}` across the
   inner-mul loop. Consumer-side, the accUpdate assembly
   lemma `compileFrag_bprod_accUpdate_correct` (sub-task
   1.c.4, lines 734-740) still claims an explicit
   preservation conjunct in its conclusion that covers
   exactly those five registers. But the plan no longer
   states where the inner-mul-loop step of that preservation
   comes from. The notes at lines 770-774 still read "Use
   `outside_preserved` in 1.c.0's post combined with the
   inner-mul partial invariant's `outside_preserved` clause
   (which only touches the four mul-scratch registers)" —
   the second referent no longer exists. Recommended
   correction: either (a) add an explicit preservation
   conjunct to `compileFrag_bprod_mul_partial_step`,
   `compileFrag_bprod_mul_partial_aux`, and
   `compileFrag_bprod_mul_partial`'s conclusions (mirroring
   the prep lemma's tail conjunct), so 1.c.4 can compose
   prep-preservation with inner-mul-preservation; or (b)
   inline the preservation reasoning across the whole
   inner-mul block inside 1.c.4. Option (a) is the minimal
   correction and keeps 1.c.4's LOC estimate intact. The
   prose at lines 770-774 must be rewritten in either case.

## Severity 2 — important corrections

1. **Sub-task 4's strict-bound prose says `bprod_exitPC - 1`
   where the lemma signature gives `instrs.size - 1`.** Plan
   line 1217: "Each phase's strict bound relaxes to
   `bprod_exitPC - 1`." Since `bprod_exitPC =
   instrs.size - 1` (per
   `bprod_exitPC_eq_size_pred`, lines 330-333), the prose
   `bprod_exitPC - 1` denotes `instrs.size - 2`, which is
   strictly less than the lemma's actual bound
   `instrs.size - 1` (line 1200). The intended phrasing is
   either `< bprod_exitPC` or `< instrs.size - 1`.
   Recommended correction: replace "relaxes to
   `bprod_exitPC - 1`" with "relaxes to `bprod_exitPC`
   (equivalently `instrs.size - 1`)".

2. **Sub-task 1.c.4's notes still reference the deleted
   `outside_preserved` clauses.** Plan lines 770-774. Even
   under Severity-1 #2's option (a), the phrasing "inner-mul
   partial invariant's `outside_preserved` clause" is
   inaccurate: the preservation would be carried as a
   conjunct of the producing lemma's conclusion, not as a
   field of the invariant. Same wording-level fix as Sev 2
   #2 from round 1 (which addressed the structure
   definitions). Recommended: rewrite the paragraph as
   "Compose 1.c.0's preservation conjunct with 1.c.3's
   preservation conjunct (which covers the four mul-scratch
   registers) via `URMState.runFor_add`."

3. **Phase i.3 clause-count audit understates carry-over.**
   Plan line 1142 claims `6 + 2 + 4 = 12` clause splits
   (six re-establish via accUpdate, two via epilogue, four
   carry over). The carry-over enumeration at lines
   1157-1160 lists five names: `zReg_zero, outer_inputs,
   tmp1_zero, tmp2_zero, hi_le`. Additionally, `vX_eq`
   (line 1145) is described as "carry-over" but the value
   `v 0 - i.val - 1` at iteration `i + 1` actually equals
   `v 0 - (i.val + 1)` — re-established via phase_i0's
   `decR vX` step, not carry-over from phase_i2. The split
   should read `6 + 2 + 5 = 13` (which exceeds the 12-clause
   count), so one of the splits is mis-categorised.
   Recommended: re-enumerate the clauses and confirm the
   per-clause attribution.

4. **`compileFrag_bprod_size` co-location wording.** Plan
   lines 336-341 say the size lemma "lands co-located with
   `compileFrag_bprod` in `Compiler.lean` (not in
   `BProd.lean`)". The bsum analogue
   `compileFrag_bsum_size` lives in `BSum.lean` (verifiable
   via `grep -n compileFrag_bsum_size BSum.lean`), not in
   `Compiler.lean`. If the intent is to follow bsum's
   landing pattern, the prose should say "lands in
   `BProd.lean` co-located with the PC-bound constants",
   not in `Compiler.lean`. Either revise the prose or
   intentionally diverge from bsum's pattern and document
   the rationale.

5. **Sub-task 1.c.4's preservation conjunct enumeration is
   incomplete.** Plan lines 734-740 list `r.val ≠ 1`,
   `≠ k+7`, `≠ k+8`, `≠ k+9`, `≠ (k+10) +
   frag_f.outputReg.val` (five register exclusions). But
   the accUpdate-block prep transferLoops also write to
   `V_acc_clone` (= k+7) and `V_factor` (= k+8); the inner
   mul body writes to `V_acc` (= 1), `V_factor` (= k+8),
   `V_mul_tmp` (= k+9); the reset writes to `V_acc_clone`.
   The list of five register exclusions is complete, but
   the prose at line 770-774 says "four mul-scratch
   registers" — the count is actually five (including
   f-output). Recommended: align the prose count with the
   five-register exclusion list, or specify that f-output
   is preserved across the inner-mul loop separately from
   the four `{V_acc, V_acc_clone, V_factor, V_mul_tmp}`
   mul-scratch registers.

## Severity 3 — minor / cosmetic

1. **Plan line 1217's intent could be sharpened.** Beyond
   the Sev 2 #1 typo, the phrase "Each phase's strict bound
   relaxes to" elides which direction the inequality
   relaxes (a tighter phase bound is weakened to the
   step-level bound). A rephrasing such as "each phase's
   strict bound is weakened to the step-level bound `<
   instrs.size - 1` via transitivity with the phase's
   intra-block invariant" makes the relaxation direction
   explicit.

2. **Sub-task 1.c.0's prep lemma `outside_preserved`
   conjunct list omits the f-body non-output registers
   (lines 499-504).** The notes at lines 528-534 correctly
   explain that f-body non-output registers are preserved
   in fact, just not asserted in the conjunct (delegated to
   phase_i2's `f_other_zero` carry-over). This is
   structurally fine, but consider promoting the note to a
   docstring fragment in the lemma itself to forestall an
   implementer wondering why those registers are not
   asserted preserved.

3. **Followup item 1 still says "five segment-peeling
   helpers" but the actual list enumerates five.** Plan
   lines 1441-1453: the list is complete and the count
   matches. No correction needed; this resolves round-1
   Sev 2 #2 cleanly.

4. **Followup item 3's "miniature bsum pre-stop chain"
   phrasing.** Plan lines 1465-1472. The word "miniature"
   is colloquial; "structurally analogous" or "internally
   bsum-shaped" would match the prose style guideline of
   the repository (formal, dry).

5. **Followup item 10 (line 1510-1517) correctly mirrors
   bsum followup item 3.** Confirmed correct; flagged here
   only for completeness.

## Confirmed correct

The following round-1 fixes were verified sound:

- **Sev 1 #1 (mostly).** `compileFrag_bprod_partial_invariant`
  now carries `(f : ERMor1 (k + 1))` between `frag_f` and
  `v` at the structure declaration (line 828). The `acc_eq`
  clause's reference to `f.interp` is now well-bound.
  Downstream consumers at lines 855, 925-926, 1107-1108,
  1183-1184, 1246, 1260 all pass `f` in the correct
  position. Only line 1195 still has the regression
  (logged as Sev 1 #1 above).
- **Sev 1 #2.** Phase i.3's strict PC bound (line 1112) now
  reads
  `< (compileFrag_bprod (compileERFrag f)).instrs.size - 1`.
  The `bprod_topPC` regression is corrected.
- **Sev 1 #3 (structure declarations).** Both
  `compileFrag_bprod_accUpdate_prep_post` (lines 470-482)
  and `compileFrag_bprod_mul_partial_invariant` (lines
  541-554) no longer reference unbound `s_pre` or `sPrep`.
  The prep lemma's preservation is correctly moved to a
  conjunct of `compileFrag_bprod_accUpdate_prep_correct`
  (lines 498-504). The mul partial invariant's preservation
  is dropped from the structure (per the round-1 fix), but
  this leaves a gap in the chain to 1.c.4 (logged as Sev 1
  #2 above).
- **Sev 1 #4.** The runtime defect is now flagged as a
  prerequisite to bprod.6 with an actionable five-step
  checklist (lines 1375-1392). The recommended `List.range
  bound`-fold shape is consistent with bsum's runtime
  shape and with bprod.5's `_aux` `perIter` fold.
- **Sub-task DAG (Sev 2 #3 from round 1).** Lines 219-258
  now show the 1.c.* chain sequentially (1.c.0 → 1.c.1 →
  1.c.2 → 1.c.3 → 1.c.4) inside the bracket layout. The
  prose at lines 264-270 matches.
- **`perIter` definition explicit in sub-task 5.** Lines
  1232-1242. The expression matches bprod.4's phase_i3
  step glue (with `A_j := natBProd j (...)` as the
  start-of-iter-j accumulator and
  `B_j := f.interp (Fin.cons j (Fin.tail v))`). The per-iter
  accUpdate cost
  `((4 * A_j + 1) + (4 * B_j + 1) + B_j * (9 * A_j + 5) + 1 + 1 + 2)`
  matches the phase_i3 T0 expression at line 1106.
- **Base case run-time `7 + 9 * (v 0)`** (line 857, 869,
  1244). Decomposition at lines 871-877 is
  `4 + (9 * (v 0) + 2) + 1 = 7 + 9 * (v 0)`, normalised.
  Cross-check against bprod's compileFrag prelude (4
  assignR + preservingTransfer 9*(v 0) + 2 + incR vAcc)
  confirms the form.
- **Followup item 10's `fBody_zero` audit** (lines
  1510-1517) mirrors bsum followup item 3's intent.
- **Closed-form arithmetic at 1.c.4** (line 764):
  `9 * vAccIn * vFOut + 9 * vFOut + 4 * vAccIn + 4`
  matches `(4*A + 1) + (4*B + 1) + B*(9*A + 5) + 1 + 1`.
  (Round-1's "Confirmed correct" section mentioned `+ 6`;
  the correct closed form is `+ 4`, which the plan now
  uses.)
- **Followup item 4's `+ 10` slack** (lines 1474-1481) now
  has the bsum followup item 7d rationale embedded, and a
  trim-headroom audit is recommended after bprod.6 lands.
- **Markdownlint cleanliness.** `markdownlint-cli2
  docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
  reports `Summary: 0 error(s)`.
- **`bprod_incIPC` / `bprod_gotoTopPC` / `bprod_exitPC`
  uniformity** across sub-tasks. The PC-layout constants
  introduced in sub-task 0 (lines 296-322) are consumed
  consistently in 1.c.2 (`bprod_mul_resetPC`, line 611),
  1.c.3 (`bprod_mul_resetPC`, line 671 and 684), 1.c.4
  (`bprod_incIPC`, line 728), 3.phase_i3 (no direct
  reference; uses `instrs.size - 1`).

## Summary

The round-1 fixes are substantively correct but two
follow-on defects remain at severity-1 level. Sev 1 #1
(missing `f` argument at line 1195) is a localised typo:
adding `f` between `(compileERFrag f)` and `v` discharges
it. Sev 1 #2 (loss of inner-mul preservation propagation
across the dropped `outside_preserved` clause) is more
substantive: either the
`compileFrag_bprod_mul_partial_step` / `_aux` / `_partial`
lemmas need an explicit preservation conjunct in their
conclusions, or 1.c.4 must inline the preservation
reasoning. The lingering prose at lines 770-774 is the
symptom of this gap and must be rewritten in tandem with
whichever option is chosen. Beyond these, five severity-2
items (the `bprod_exitPC - 1` typo, prose alignment, clause-
count audit, size-lemma co-location, preservation conjunct
register count) and five severity-3 cosmetics warrant
cleanup. Recommendation: address Sev 1 #1 and #2 in a third
revision, after which execution can begin. The runtime
defect (round-1 Sev 1 #4) is correctly flagged as a
separate prerequisite commit and does not block the
plan-revision cycle.
