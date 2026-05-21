# Round 1 adversarial review — bprod pre-stop sub-division

Review target:
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
(commit `5ffb2b44`). Reviewer scope: defect-finding against
the landed bsum chain, the `compileFrag_bprod` definition
(`GebLean/LawvereERKSim/Compiler.lean` lines 1190-1440), the
session handoff (`docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`),
and the `compileER_runtime` formula (`Compiler.lean` lines
1594-1639).

## Severity 1 — blocking defects

1. **`compileFrag_bprod_partial_invariant` structure omits
   the `f : ERMor1 (k + 1)` parameter.** Sub-task 2 (plan
   lines 806-812) declares the structure with parameters
   `frag_f`, `v`, `i`, `hi`, `s` but the `acc_eq` clause
   (lines 825-827) refers to `f.interp`, an unbound name.
   The landed bsum analogue
   (`BSum.lean` lines 1138-1143) takes both `frag_f` and `f`
   as parameters precisely for this reason. The base lemma
   `compileFrag_bprod_partial_base` (plan lines 829-838)
   accordingly passes four explicit arguments, omitting `f`.
   Phase-preservation lemmas downstream (3.phase_i0,
   3.phase_i1, 3.phase_i2, 3.phase_i3) all consume the
   partial invariant and would inherit the elaboration
   failure. Recommended correction: add `(f : ERMor1
   (k + 1))` to the structure between `frag_f` and `v`, and
   thread it through every consuming sub-task signature.

2. **Phase i.3 strict PC bound uses `bprod_topPC` where the
   landed bsum analogue uses `instrs.size - 1`.** Plan
   sub-task 3.phase_i3 (lines 1092-1093) writes
   `(URMState.runFor _ sPre k').pc < bprod_topPC`. But
   phase i.3 executes the accUpdate block at PCs
   `[trBase, trBase + 22]` followed by the goto restoring
   `topPC = 14`. Intermediate PCs during the accUpdate are
   all `> topPC`, so the proposed bound is unsatisfiable on
   any step except the final one. The bsum landed lemma
   (`BSum.lean` line 3696) uses `< (compileFrag_bsum
   frag_f).instrs.size - 1`. Recommended correction: replace
   `bprod_topPC` with `bprod_exitPC frag_f` (equivalently
   `(compileFrag_bprod frag_f).instrs.size - 1`). The bsum
   sub-division had the analogous defect in the planned
   form; it was corrected during implementation. This plan
   replicates the defect verbatim.

3. **`compileFrag_bprod_accUpdate_prep_post` and
   `compileFrag_bprod_mul_partial_invariant` reference
   `s_pre.regs` / `sPrep.regs` in their `outside_preserved`
   clauses, but those identifiers are not structure
   parameters.** Plan sub-task 1.c.0 (lines 461-480)
   declares the structure with parameters
   `frag_f, vAccIn, vFOut, s` and writes
   `s'.regs q = s_pre.regs q` — neither `s'` nor `s_pre` is
   bound. Plan sub-task 1.c.1 (lines 528-545) repeats the
   pattern: `s.regs q = sPrep.regs q` where `sPrep` is not a
   parameter. As written, both structures fail to elaborate.
   Recommended correction: add a pre-state parameter to the
   structure (`(sPre : URMState ...)`) or move the
   preservation clause out of the structure into the lemma
   conclusion that produces the structure. Bsum's
   `compileFrag_bsum_phase_*_post` structures avoid this by
   either passing the pre-state explicitly or restating the
   preservation in the producing lemma.

4. **`compileER_runtime (.bprod f) v` cannot bound the
   actual per-iteration cost.** The plan flags this in
   sub-task 6 (the "Critical risk" block, lines 1264-1310)
   and the arithmetic is correct: per-iter actual is
   `compileER_runtime f ctx_f + (5 + nRegs_f + 9*outerSum +
   2*(k+1) + 9*A*B + 9*B + 4*A + 6)`, while the runtime
   offers `compileER_runtime f ctx_f + 60 + 2*(k+1) +
   10*(i + outerSum) + 5*B + nRegs_f`. The slack
   `52 + 10*i + outerSum - 9*A*B - 4*A - 4*B` becomes
   negative for `A ≥ 2` and `B ≥ 1`, and since
   `A = natBProd i (...)` grows multiplicatively across
   iterations, the runtime is insufficient at all but the
   first iteration of any non-trivial bprod. This is a
   blocking defect for sub-task 6 (final assembly) as the
   plan acknowledges. Recommended correction: amend
   `compileER_runtime`'s bprod branch in `Compiler.lean`
   *before* starting sub-task 6, then re-verify
   `compileER_numRegs_eq_compileERFrag_numRegs` is
   undisturbed. The plan's candidate 1 (recursive embedding
   of `natBProd`) is the minimal correction. Note that
   candidate 1 introduces a dependency of
   `compileER_runtime` on `natBProd`, which is acceptable
   (the runtime is already semantics-dependent through
   `f.interp ctx_f`), but the recursion structure must
   match `natBProd`'s `Nat.rec` shape so that the per-iter
   sum decomposes cleanly. Reviewer suggestion: rather than
   inlining `9 * f.interp ctx_f * natBProd i (...) + 4 *
   natBProd i (...) + 9 * f.interp ctx_f + 8`, write the
   bprod runtime explicitly as `(List.range bound).foldr`
   with the per-iter cost depending on the accumulator at
   `i`, mirroring `natBProd`'s recursive shape; this avoids
   the `Nat.rec`-vs-`List.range`-fold mismatch when
   discharging the slack in bprod.5.

## Severity 2 — important corrections

1. **Clause-count text inconsistency in sub-task 2.** Plan
   line 842 says the invariant carries 11 clauses; the
   listed clauses are `hi_le, pc_eq, zReg_zero,
   outer_inputs, vX_eq, vI_eq, tmp1_zero, tmp2_zero,
   accClone_zero, factor_zero, mulTmp_zero, acc_eq` — that
   is 12, not 11. The "vs bsum's 9" comparison is right
   (bsum's landed invariant has nine clauses including
   `hi_le`; bprod adds three mul-scratch clauses). The
   prose miscount makes the diff against bsum harder to
   verify. Correct to "12 clauses (vs bsum's 9)" or drop
   `hi_le` from the bprod count and say "11 clauses (vs
   bsum's 8)".

2. **Sub-task 1.c.0's segment-peeling helper is missing
   from followup item 1.** Followup item 1 (lines 1369-1379)
   enumerates four helpers to consolidate
   (`zeroSweep_instr_at`, `prologueBlock_instr_at`,
   `accUpdateBlock_instr_at`, `accUpdate_innerBody_instr_at`)
   but sub-task 1.c.0 (lines 502-506) introduces a fifth
   helper, `compileFrag_bprod_accUpdate_instr_at`, which is
   distinct from `accUpdateBlock_instr_at` (the former
   covers the prep transferLoops; the latter covers all 21
   accUpdate instructions plus epilogue prefix per
   sub-task 3.phase_i3 lines 1131-1136). Either consolidate
   the two into one helper consumed by both 1.c.0 and
   3.phase_i3, or extend followup item 1 to enumerate five
   helpers. As written, the plan understates the
   duplication.

3. **Sub-task DAG diagram conflates 1.c.0-1.c.4 as parallel
   with 1.a and 1.b.** Plan lines 219-258. The diagram
   draws `[bprod.1.a]`, `[bprod.1.b]`, and `[bprod.1.c.*]`
   as siblings under bprod.0, but the bsum.1.c chain
   `1.c.0 → 1.c.1 → 1.c.2 → 1.c.3 → 1.c.4` is internally
   sequential. The DAG should expose the internal
   ordering: 1.c.0 → 1.c.1 → 1.c.2 → 1.c.3 → 1.c.4. The
   prose does explain the sub-task numbering scheme, but
   the diagram itself is misleading and complicates
   implementer scheduling.

4. **Sub-task 1.c.3 outer-iteration strict bound stated as
   `< bprod_mul_resetPC`.** Plan line 657: this is correct
   for the inner-mul loop in isolation, but it should be
   noted that consumers (sub-task 1.c.4) need a strict bound
   `< bprod_incIPC` for assembly into the broader chain.
   1.c.4 then takes the exit jumpZR + reset assignR, and
   the strict bound on those two final steps is also
   `< bprod_incIPC`. Recommended: clarify in 1.c.3's notes
   that the bound's purpose is to feed 1.c.4's
   composition, and that 1.c.4 strengthens to
   `< bprod_incIPC`.

5. **Sub-task 5's `perIter` is referenced but not defined.**
   Plan lines 1197-1224 use `perIter` as an opaque per-iter
   step-count without giving an explicit body. Bsum's
   `compileFrag_bsum_partial_aux` (BSum.lean lines
   4585-4590) does write `perIter` as a `let`-bound
   function; the bprod plan inherits the underspecification
   from its bsum analogue, but for bprod the perIter cost
   must reference `A_i = natBProd i (...)` and `B_i = f.interp
   (...)`, which interacts with the runtime correction in
   defect #4. Recommended: state the bprod perIter
   explicitly:

   ```text
   perIter (j : ℕ) :=
     (2 + nRegs_f)
       + (9 * vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
           + 2 * (k + 1))
       + compileER_runtime f (Fin.cons j (Fin.tail v))
       + (9 * A_j * B_j + 9 * B_j + 4 * A_j + 6)
   ```

   where `A_j := natBProd j (fun i' => f.interp (Fin.cons
   i'.val (Fin.tail v)))` and `B_j := f.interp (Fin.cons
   j (Fin.tail v))`.

6. **`bprod_trBase` reduces only as `bodyPCBase + (size -
   1)` when `frag_f.instrs.size ≥ 1`.** Plan lines
   292-294. Bsum.0's followup item 7d
   (`2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`
   line 984-985) flagged needing a rationale comment.
   The bprod plan doesn't repeat the recommendation. Add
   a note that `frag_f.instrs.size ≥ 1` is guaranteed by
   `lastInstr_isStop`, so `frag_f.instrs.size - 1` is the
   f-body length without underflow concerns.

7. **`compileFrag_bprod_prelude_pc_strict_bound` mentioned
   in sub-task 5 has no signature.** Plan lines 1240-1243
   introduce it as a thin helper for the prelude PC ladder
   but no signature is given. Recommended: add the
   signature explicitly. The bsum analogue (if landed)
   should be cited; if not, this is genuinely new and
   deserves its own slot in 5 with an LOC estimate.

8. **Sub-task 3.phase_i3's `outside_preserved` carry-over
   is asserted without listing which clauses re-establish
   via that route.** Plan lines 1127-1129 say "Other
   clauses: carry-over from phase_i2's `outside_preserved`
   for all registers untouched by the accUpdate." The
   accUpdate touches `V_acc`, `V_acc_clone`, `V_factor`,
   `V_mul_tmp`, and `f.outputReg`. The carried clauses are
   therefore `zReg_zero`, `outer_inputs`, `vX_eq`, `vI_eq`,
   `tmp1_zero`, `tmp2_zero` — six clauses. Re-establishing
   `pc_eq` and `vI_eq` happens through the goto and incR
   respectively, not via carry-over. Recommended: enumerate
   the carry-over clauses explicitly to confirm the count
   against phase_i2's `outside_preserved` clause's
   coverage.

## Severity 3 — minor / cosmetic

1. **Base-case run-time written as `6 + 9 * (v 0) + 1`
    instead of the equivalent `7 + 9 * (v 0)`.** Plan lines
    836-838 and 856-859. The decomposition prose
    (4 assignR + preservingTransfer + 1 incR) reads
    naturally as `4 + (9 * (v 0) + 2) + 1`. The chosen form
    `6 + 9 * (v 0) + 1` mixes the four `assignR` count
    (4) with the `preservingTransfer` slack (`+ 2`) into a
    single `6`, which obscures the per-block split. Either
    use the unfolded `4 + (9 * (v 0) + 2) + 1` form (matches
    the prose), or the closed `7 + 9 * (v 0)` form (matches
    omega's preferred normal form), but not the hybrid
    `6 + ... + 1`.

2. **Bsum followup item 3 (re-evaluate `fBody_zero`
    placement) has no bprod analogue.** The bsum chain's
    Session 6 dropped `fBody_zero` from the top-of-loop
    invariant per Pattern 18. The bprod plan (sub-task 2
    notes, line 845) correctly inherits this design.
    However, no followup item flags revisiting the
    placement decision for bprod once landed, parallel to
    bsum followup item 3. Add a followup item to audit the
    bprod `fBody_zero` decision against bsum's after both
    chains have landed.

3. **Followup item 4 cites
    `compileER_runtime` constants `40 + 10*bound` (bprod)
    vs `30 + 10*bound` (bsum) as if the `+10` slack is
    coincidental.** Plan lines 1394-1399. The actual prelude
    delta is 1 step (`incR vAcc`); the `+10` slack
    over-pays by 9 per-bound. Cleaner phrasing: "the `+10`
    slack pads the additional `incR vAcc` step (1 step)
    plus 9 slots of unused per-iteration headroom; verify
    after bprod.6 whether the headroom is necessary or can
    be trimmed."

4. **References section line numbers.** Plan line 1444
    cites `compileER_runtime` lines 1625-1639, which is
    only the bprod branch; the full definition starts at
    line 1594. Cite the full range `1594-1639` or label
    the cited range as "bprod branch only".

5. **The `compileFrag_bprod_zeroSweep_correct` signature
    in sub-task 1.a (lines 366-379) writes the `h_outside`
    return type as `True`.** Plan line 281 for bsum's
    analogue had the same vacuous clause; that was a bsum
    sub-division typo. Recommended: drop the `h_outside`
    hypothesis entirely (it's dead) and align with the
    landed `compileFrag_bsum_zeroSweep_correct` form.

6. **Plan line 1380-1385's followup item 2 — "rename
    `bsum_zeroSweep` to a neutral name" — risks breaking
    `bsum_zeroSweep`'s existing consumers if executed
    aggressively.** Recommend phasing: extract a
    constructor-agnostic alias, leave `bsum_zeroSweep`
    in place as a re-export, and migrate consumers
    incrementally.

## Confirmed correct

The following claims were spot-checked against the cited
sources and found sound:

- **PC-layout offsets** in sub-task 0 (plan lines 153-203)
  match `compileFrag_bprod`'s actual layout
  (`Compiler.lean` lines 1248-1287). The 14-instruction
  prelude (`assignR`×4 + `preservingTransfer` 9 instrs +
  `incR vAcc`) yields `topPC = 14`, `bodyStartPC = 15`,
  `zeroSweepBase = 16`. The 21-instruction accUpdate
  matches `mul_resetPC = trBase + 20`,
  `incIPC = trBase + 21`, `gotoTopPC = trBase + 22`,
  and `exitPC = trBase + 23`.
- **`compileFrag_bprod_size = 39 + frag_f.numRegs + 9 *
  (k + 1) + frag_f.instrs.size`** (sub-task 0). Manual
  re-count: 14 + 2 + numRegs + 9(k+1) + (size-1) + 21 + 3
  = 39 + numRegs + 9(k+1) + size.
- **`bprod_exitPC = instrs.size - 1`** is internally
  consistent with the size formula.
- **`fBase = k + 10` matches the bprod compiler.** Plan
  line 138, `Compiler.lean` line 1218.
- **Inner-mul step count `9 * vAccIn + 5`** (sub-task 1.c.2)
  matches the inner-body composition: 1 jumpZR + 1 decR +
  `(9 * A + 2)` preservingTransfer + 1 goto.
- **accUpdate total `9*A*B + 9*B + 4*A + 4`** (sub-task
  1.c.4 closed form) matches `(4*A + 1) + (4*B + 1) +
  B*(9*A + 5) + 1 + 1`.
- **`acc_eq` re-establishment at i + 1 via `natBProd_rec`**
  (sub-task 3.phase_i3). The recurrence `natBProd (i + 1)
  g = natBProd i g * g i` holds by `natBProd_rec` (
  `LawvereERPrimrec.lean` line 21).
- **`bprod_exitPC` is the trailing stopR PC** (the
  `epilogue = [incR vI, goto topPC, stopR]` has stopR at
  the rightmost position, position `trBase + 23`).
- **`incR vAcc` at PC 13 makes the base-case accumulator
  `1` rather than `0`.** Correctly observed by the plan
  (sub-task 2 notes, lines 872-877). Aligns with
  `natBProd 0 _ = 1`.
- **Cited Compiler.lean line numbers** are accurate:
  `compileFrag_bprod` starts at 1190; `bsum_prologueSrc`
  at 817; `bsum_prologueBlock` at 832; `bsum_zeroSweep`
  at 867; `compileER_numRegs_eq_compileERFrag_numRegs` at
  1542.
- **Markdownlint cleanliness.** `markdownlint-cli2`
  produces 0 errors.
- **Pattern coverage.** Plan applies Pattern 1 (Lean-core
  `Fin.cases` instead of `fin_cases`, sub-task 1.a notes),
  Pattern 9 (`let` over `set`, sub-task 0 notes),
  Pattern 16 (inlined-conjunction T0 for phase_i0/i1/i3),
  Pattern 17 (`URMState.init` inline before binding,
  sub-task 3.phase_i2 notes lines 1065-1067), Pattern 14
  (.pop-emitted body → `size - 1`, sub-task 1.d notes
  lines 776-778).

## Summary

The plan reproduces the bsum sub-division's overall
structure faithfully and correctly identifies a real
runtime defect in `compileER_runtime`'s bprod branch
(severity 1 #4) that must be resolved before sub-task 6
can be discharged. Four severity-1 defects need
correction before execution: a missing `f` parameter in
the partial-invariant structure, a wrong strict-PC bound
in phase_i3 (regression from bsum's planned form that was
caught only during implementation), unbound `s_pre` /
`sPrep` identifiers in two preservation-clause structures,
and the runtime defect itself. Several severity-2 issues
(clause counts, missing perIter body, DAG ordering)
warrant cleanup but do not block execution. Recommend a
second pass once severity-1 defects are addressed.
