# Step T2 Task 11 — Partial-completion handoff

> **Status (2026-05-20). T2 complete.** Task 11g (bprod runFor
> wrapper), Task 11h (top-level structural induction in the new
> `GebLean/LawvereERKSim/Top.lean` submodule), Task 12 (axiom
> audit), and the final holistic code-quality review all landed.
> The climactic theorem `compileER_runFor` is at
> `GebLean/LawvereERKSim/Top.lean`. Every public declaration in
> `GebLean/LawvereERKSim/*.lean` is `[propext, Quot.sound]`-only.
>
> The "What remains" section below is preserved for historical
> reference; the items listed there have all landed. The
> "Followup branch (post-T2)" section near the end of this
> document remains live and authoritative — see the per-item
> annotations there for which items have since landed and which
> remain pending for the follow-up cleanup branch. The live
> reconciled list lives in task #654's description.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Execution mode for the next session](#execution-mode-for-the-next-session)
- [Session summary](#session-summary)
- [What is landed](#what-is-landed)
  - [Tasks 0-10 (compiler infrastructure)](#tasks-0-10-compiler-infrastructure)
  - [Task 11 — landed sub-tasks](#task-11--landed-sub-tasks)
    - [Session 1 (through 2026-05-18, ending at phase i.1)](#session-1-through-2026-05-18-ending-at-phase-i1)
    - [Session 5 (2026-05-19, bsum.0–bsum.1.d landed)](#session-5-2026-05-19-bsum0bsum1d-landed)
    - [Session 6 (2026-05-20, bsum pre-stop chain complete + 11f wrapper)](#session-6-2026-05-20-bsum-pre-stop-chain-complete--11f-wrapper)
    - [Session 4 (2026-05-19, file split landed)](#session-4-2026-05-19-file-split-landed)
    - [Session 3 (2026-05-19, Task 11e.7 wrap-up)](#session-3-2026-05-19-task-11e7-wrap-up)
    - [Session 2 (2026-05-19, finishing the comp story)](#session-2-2026-05-19-finishing-the-comp-story)
  - [Cumulative output](#cumulative-output)
- [What remains](#what-remains)
  - [Task 11e.6.a.iii-bprod — bprod pre-stop](#task-11e6aiii-bprod--bprod-pre-stop)
  - [Task 11g — bprod runFor wrapper](#task-11g--bprod-runfor-wrapper)
  - [Task 11h — top-level structural induction](#task-11h--top-level-structural-induction)
  - [Task 12 — axiom audit](#task-12--axiom-audit)
  - [Final holistic code-quality review](#final-holistic-code-quality-review)
  - [Followup branch (post-T2)](#followup-branch-post-t2)
- [Resolved design for 11e.7 (option a-bridge)](#resolved-design-for-11e7-option-a-bridge)
- [Patterns learned (lessons for resumption)](#patterns-learned-lessons-for-resumption)
- [Resumption recipe](#resumption-recipe)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Resumption guide for a future session picking up T11
(compileER_runFor correctness theorem) where the present
session paused.

## Execution mode for the next session

The next session resumes execution against the plan at
`docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`
using the **`superpowers:subagent-driven-development`**
skill. The plan was produced by
`superpowers:writing-plans` and converged through five
adversarial-review rounds; remaining sub-tasks are listed
in this handoff's [Resumption recipe](#resumption-recipe)
and reproduced as discrete TodoWrite items.

For each sub-task, dispatch a fresh implementer subagent
with a self-contained brief (do not let the subagent read
the plan file; paste the relevant task text into the
prompt). Then run the spec-compliance reviewer subagent
and the code-quality reviewer subagent, looping until both
pass. Lemma signatures and structure-clause shapes
declared in this handoff and in the plan are non-negotiable
(per the project's "Non-negotiable interfaces for
formalising pre-existing objects" rule); subagents may
adjust internal proof tactics freely.

## Session summary

A multi-session SDD execution of T2 has completed Tasks 0-10
(compileER + compileER_runtime + 7 per-constructor
combinators), the four atom cases of Task 11, the full comp
pre-stop correctness chain through its `≤ t'` wrapper, the file
split into six topical submodules under `GebLean/LawvereERKSim/`,
the full bsum pre-stop correctness chain (14 sub-tasks: PC
layout, three sub-block helpers, f-body embedding, partial
invariant + base case, four per-iteration phase preservation
lemmas, induction glue, outer iteration, final assembly), and
the bsum `≤ t'` wrapper (Task 11f). Two latent specification
bugs surfaced during the bsum slack-matching arithmetic and were
fixed: Task 10's `compileER_runtime` had insufficient
`+ 50`/`+ 60` per-iter constants for bsum/bprod (negative slack
for arity > 22; fixed by adding `+ 2 * (k + 1)`), and Task 9's
`compileER_numRegs (.bprod f)` was off-by-one (`k + 9` should
have been `k + 10`; would have aliased `vMulTmp` with `fBase`).

Remaining: bprod pre-stop chain (~3000-4000 LOC mirror of
bsum, ~14 sub-tasks), 11g (bprod `≤ t'` wrapper), 11h
(top-level structural induction), Task 12 (axiom audit), and
the final holistic code-quality review.

Current `@-`: commit `5bc623a1` (this docs commit, session-5
session-progress notes, just rebased onto the bsum-chain tip
to consolidate the previously-orphaned sibling head). The
immediately-preceding code commit is `40b93026`
(`compileER_runFor_bsum` wrapper, Task 11f). Build clean (1531
jobs). Axiom hygiene clean (`[propext, Quot.sound]` only on
every new declaration; verified via
`mcp__lean-lsp__lean_verify`). Source: six submodules under
`GebLean/LawvereERKSim/` totalling ~13260 lines (Compiler
1790, Embedding 898, Loops 2538, Atoms 1635, Comp 5444, BSum
5038) plus the 38-line index.

No sibling heads remain after the session-6 rebase. The
previously-orphaned `75d79e2f` (session-5 docs commit) was
folded into the main chain at `5bc623a1` once the bsum chain
had landed all the code it described.

## What is landed

### Tasks 0-10 (compiler infrastructure)

- **Task 0**: T1 refactor — arity-indexed `URMProgram (numInputs : ℕ)`.
  Commit `5c16a133`.
- **Task 1**: `GebLean/LawvereERKSim.lean` module skeleton.
  Commits `ea33702e`, `7fab38da`.
- **Task 2**: `URMInstrRaw` + `URMInstrRaw.toBoundedArray`
  (via `List.attach`). Commits `d7c518eb`, `67bbd26b`.
- **Task 3**: `CompiledFragment a extends URMProgram a`
  with `numRegs_pos`, `zeroReg_not_input`,
  `zeroReg_not_output`, `lastInstr_isStop`.
  Commits `00cf4532`, `18afd527`.
- **Task 4**: emission helpers — `URMRaw.goto`,
  `URMRaw.transferLoop`, `URMRaw.preservingTransfer`.
  Commit `64416825`.
- **Task 5**: atom fragment compilers — `compileFrag_zero`,
  `compileFrag_succ`, `compileFrag_proj`,
  `compileFrag_sub`. Commits `6b44e40e`, `523eae2a`.
- **Task 6**: `compileFrag_comp` with reindex/shiftPC.
  Commits `07e6e0b1`, `18afd527`, `87ec2b37`.
- **Task 7**: `compileFrag_bsum` with zero-sweep
  per-iteration prologue. Commits `fb3bef67`, `db97c587`,
  `87ec2b37`.
- **Task 8**: `compileFrag_bprod` with R^XY_Z
  multiplication. Commit `6245df3d`.
- **Task 9**: top-level `compileER` and `compileERFrag`.
  Commit `9aa1f53d`.
- **Task 10**: `compileER_runtime` structural recursion.
  Commit `b340590e`; runtime patched in `1642bfb5`.

### Task 11 — landed sub-tasks

#### Session 1 (through 2026-05-18, ending at phase i.1)

- **11a**: T1 helpers `URMState.runFor_halted_invariant`
  and `URMState.runFor_stop`; `compileER_runFor_zero`.
  Commits `102ca3ac`, `4fa29689`.
- **11b**: `URMInstrRaw.toBoundedArray_size/getElem/getElem?`.
  Commit `c99b1abb`.
- **11c.1**: `transferLoop_correct` (4n + 1 steps).
  Commit `56e38df9`.
- **11c.2**: `preservingTransfer_correct` (9n + 2 steps),
  plus structural helpers
  (`step_of_getElem?_{jumpZ,dec,inc}`,
  `preservingTransferInstrs`, `preservingTransfer_loop1`,
  `preservingTransfer_loop2`). Commit `ab91e0ad`.
- **11c.3**: `compileER_runFor_succ`. Commit `1754926f`.
- **11c.4**: `compileER_runFor_proj` +
  `List.find?_finRange_inputRegs`,
  `URMState.init_regs_inputRegs`. Commit `9a53b051`.
- **11c.5**: `compileER_runFor_sub` +
  `subInnerLoop_correct`. Commit `a77d231a`.
- **11d**: program-embedding framework —
  `ProgramEmbedsFragment`, `StateEmbedsFrag`,
  `stateEmbedsFrag_step`, `stateEmbedsFrag_runFor` + two
  new step helpers (`step_of_getElem?_{assign,stop}`).
  Commit `9c8fb974`.
- **11e.1**: `URMProgram.WellBounded`, `runFor_pc_le_size`,
  `compileER_runFor_pc_le_size`, and
  `fragment_runFor_pc_le_size`. Commit `d7530418`.
- **11e.2-3**: `URMState.init_regs_zero_outside_inputs`,
  `compileFrag_comp_subBlock_length`,
  `compileFrag_comp_subBlocks_length`,
  `foldr_acc_add_eq_sum_map`,
  `ProgramEmbedsFragment_compileFrag_comp_fBody`, and
  `URMInstrRaw.toBounded_congr`. Commit `3881209d`.
- **11e.4**: `flatMap_finRange_split` +
  `ProgramEmbedsFragment_compileFrag_comp_gsBody`.
  Commit `74b2f1bf`.
- **11e.5**: `compileER_runFor_comp_k_zero` (k=0 case),
  `stateEmbedsFrag_step_tail`, and
  `stateEmbedsFrag_runFor_tail`. Commit `4108665c`.
- **11e.6.a-zero**: `compileER_pre_stop_correct_atom_zero`.
  Commit `0ad6fbb7`.
- **11e.6.a.i**: per-step PC bounds —
  `transferLoop_correct_pc_bound`,
  `subInnerLoop_correct_pc_bound`,
  `preservingTransfer_loop1_pc_bound`,
  `preservingTransfer_loop2_pc_bound`. Commit `51ede208`.
- **11e.6.a.ii**: atom pre-stop for succ/proj/sub +
  four strict PC bound helpers
  (`preservingTransfer_loop2_pc_strict_bound`,
  `preservingTransfer_correct_pc_bound`,
  `preservingTransfer_correct_pc_strict_bound`,
  `subInnerLoop_correct_pc_strict_bound`).
  Commit `743f0bda`.
- **11e.6.a.iii-comp.0**: `transferLoop_correct_pc_strict_bound`.
  Commit `cd32d580`.
- **11e.6.a.iii-comp.1.a-c**: three abstract sub-block
  phase helpers (`compileFrag_comp_subBlock_{inputCopies,
  gsBody, outputTransfer}_correct`), `vPrefixSum`,
  `inputCopies_disj`, and their `_pc_strict_bound`
  counterparts. Commits `0c08e3ce`, `b5c05d41`, `a78d27f2`.
- **Outside-preserved helpers**:
  `stateEmbedsFrag_step_outside_preserved` +
  `stateEmbedsFrag_runFor_outside_preserved`.
  Commit `8947b0ac`.
- **11e.6.a.iii-comp.2.pre1, pre2**: instruction-presence
  dischargers for Phase i.1 and Phase i.3. Commits
  `e52a9601`, `8f410639`.
- **11e.6.a.iii-comp.2.base**:
  `compileFrag_comp_partial_invariant` (8-clause structure),
  `compileFrag_comp_subBlocks_partial_base` (m=0 case),
  `compileFrag_comp_pcOf`, `_zero`. Commit `b9f4dc47`.
- **11e.6.a.iii-comp.2.inv-prereq**:
  `compileFrag_comp_pcOf_succ` (constructive). Commit
  `e66f7681`.
- **f_body_zero clause correction**: weaken to "off filled
  inputs". Commit `3ddd7280`.
- **11e.6.a.iii-comp.2.inv-phase_i1**:
  `compileFrag_comp_phase_i1_post` (10-clause) and
  `compileFrag_comp_subBlocks_partial_phase_i1`. Commit
  `7c8dfb56`.

#### Session 5 (2026-05-19, bsum.0–bsum.1.d landed)

- **Sub-division plan**: produced
  `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`
  (964 lines, markdownlint-clean), 14 implementer-sized
  sub-tasks. Commit `lyltwlls 161f2d57`.
- **11e.6.a.iii-bsum.0**: PC-layout constants
  (`bsum_topPC`, `bsum_bodyStartPC`, `bsum_zeroSweepBase`,
  `bsum_prologueBase`, `bsum_bodyPCBase`, `bsum_trBase`,
  `bsum_incIPC`, `bsum_gotoTopPC`, `bsum_exitPC`) plus
  `bsum_exitPC_eq_size_pred`. Initial 201 LOC; code-quality
  review extracted `compileFrag_bsum_size` to `Compiler.lean`
  (co-located with `compileFrag_bsum`, line 1113) and
  un-`private`d `URMInstrRaw.toBoundedArray_size`
  (`Compiler.lean:160`); refactored BSum.lean shrunk to 115
  LOC. Commits `pxqvvpzk 7fe30c84`, `kmltktxs 5d20e28e`.
- **11e.6.a.iii-bsum.1.a**: `compileFrag_bsum_zeroSweep_correct`
  and `_pc_strict_bound`. Induction on `numRegs_f`,
  end-peeled via `URMState.runFor_add`; each `assignR` step
  discharged by `URMState.step_of_getElem?_assign`. Lean-core
  `Fin.cases` + decidable `by_cases` (no `Classical`). Commit
  `tsyrsqxr 191f0033`. +134 LOC.
- **11e.6.a.iii-bsum.1.b**: `compileFrag_bsum_prologue_correct`
  and `_pc_strict_bound` as thin private wrappers around
  `compileFrag_comp_subBlock_inputCopies_correct` /
  `_pc_strict_bound`. Un-`private`d the comp helpers plus
  `inputCopies_disj` and `vPrefixSum` in `Comp.lean`. BSum.lean
  import changed from `Atoms` to `Comp` (Comp transitively
  brings Atoms). Commit `rytrkvqo cc1ec282`. +68 LOC.
  Followup item recorded: extract shared helpers to neutral
  names in `Loops.lean` once bprod also consumes them.
- **11e.6.a.iii-bsum.1.c**: `compileFrag_bsum_accUpdate_correct`
  and `_pc_strict_bound` as thin private wrappers around the
  already-public `transferLoop_correct` /
  `transferLoop_correct_pc_strict_bound` in `Loops.lean`.
  Implementer preserved the underlying `zReg`/`tmp`/`h_disj_*`
  parameters rather than hiding them (matches the
  `compileFrag_bsum_prologue_correct` precedent). Commit
  `msvqmuum 344ce1af`. +53 LOC.
- **11e.6.a.iii-bsum.1.d**:
  `ProgramEmbedsFragment_compileFrag_bsum_fBody` (~410 LOC of
  proof). Mirrors `ProgramEmbedsFragment_compileFrag_comp_fBody`
  (Comp.lean:105+); the bsum analogue is structurally simpler
  because the f-body comes after a flat prologue rather than a
  per-iteration `flatMap`. Signature corrected from the
  sub-division's `frag_f.instrs.size` to
  `frag_f.instrs.size - 1` because `compileFrag_bsum`'s f-body
  segment is `frag_f.instrs.pop.toList.map ...` (Compiler.lean
  line 965), matching the comp gsBody precedent. Un-`private`d
  `ProgramEmbedsFragment_compileFrag_comp_fBody` (Comp.lean
  line 105) and four `Compiler.lean` helpers
  (`bsum_prologueSrc`, `bsum_prologueBlock`,
  `boundedBy_bsum_prologueBlock`, `boundedBy_bsum_zeroSweep`)
  so BSum.lean's proof can reconstruct the f-body's
  boundedness witness. Commit `xwssqwxu a9b6e361`. +416 LOC.

Cumulative session-5 output: 6 commits (plus the sub-division
plan = 7), ~733 LOC added to BSum.lean, +80 LOC to Compiler.lean
(co-located `compileFrag_bsum_size`), 6 declarations un-`private`d
across Comp.lean / Compiler.lean / Loops.lean. All axiom checks
return `[propext, Quot.sound]`. Build clean throughout.
Final BSum.lean size: 786 lines. The followup-item list in the
sub-division doc has grown; consolidate at session end.

#### Session 6 (2026-05-20, bsum pre-stop chain complete + 11f wrapper)

- **bsum.2 — partial invariant + base case**: 10-clause
  `compileFrag_bsum_partial_invariant` (later refactored to 9
  clauses; see phase_i3 below) and `compileFrag_bsum_partial_base`
  for `i = 0` after the prelude's actual `6 + 9 * (v 0)` URM
  steps. The sub-division doc's "13-step" base figure conflated
  PC slots with URM steps: `preservingTransfer` occupies 9 PC
  slots but executes as a loop of `9 * n + 2` URM steps where
  `n = v 0` at entry. Correction applied during implementation.
  +451 LOC. Commit `upytlpyq 2ace1546`.

- **bsum.3.phase_i0 — zero-sweep preservation**: 2 control steps
  (`jumpZR vX → bodyStart` plus `decR vX`) followed by
  `frag_f.numRegs` zero-sweep `assignR` steps. T0 =
  `2 + (compileERFrag f).numRegs`, closed-form, so the outer
  `∃ T0` was dropped per the **adjudicated inlined-conjunction
  convention** (applied uniformly to phase_i0/i1/i3 thereafter;
  phase_i2 keeps the existential because its T0 comes from
  `ih_f`). Added helper `compileFrag_bsum_zeroSweep_instr_at`
  (~200 LOC) — symbolic-`r.val` instruction-presence over the
  swept segment cannot be discharged by `rfl`. +684 LOC. Commit
  `qrkxnlor 9da494eb`.

- **bsum.3.phase_i1 — prologue preservation**: T0 equals
  `9 * vPrefixSum (Fin.cons i.val (Fin.tail v)) (k + 1) + 2 * (k + 1)`
  via `compileFrag_bsum_prologue_correct`. Added helper
  `compileFrag_bsum_prologueBlock_instr_at` (~520 LOC) — second
  instance of the segment-peeling pattern. Required per-declaration
  `set_option maxHeartbeats 4000000 in` because the prologue's
  source-map `bsum_prologueSrc k s = if s.val = 0 then k + 4 else s.val + 2`
  has a conditional shape that inflates unifier cost (versus
  comp's unconditional `2 + j.val`). +994 LOC. Commit
  `zymxmqnu fb5a7494`.

- **bsum.3.phase_i2 — f-body preservation**: Consumes `ih_f`,
  so conclusion remains existential in `T0 ≤ compileER_runtime f
  (Fin.cons i.val (Fin.tail v))`. Uses the existing
  `ProgramEmbedsFragment_compileFrag_bsum_fBody` (bsum.1.d) via
  `stateEmbedsFrag_runFor` + `_outside_preserved`. No new
  `_instr_at` helper needed (the f-body embedding is structurally
  singular). Surfaced the `URMState.init` reduction quirk: a
  `let f_init := URMState.init ...` blocks reduction of
  `f_init.regs r` to its underlying `match` form, so the
  regs-equation lemma must be introduced with `URMState.init ...`
  inline before the `let` binding. +375 LOC. Commit
  `qrormswv 0e02db8a`.

- **Refactor: drop `fBody_zero` from
  `compileFrag_bsum_partial_invariant`**: phase_i2 establishes
  only `f_output` (one register), not the full f-body block, so
  the partial invariant cannot maintain `fBody_zero` across
  iterations. The zero-sweep at the next iteration's phase_i0
  re-establishes it. The sub-division plan's notes for phase_i3
  explicitly anticipated this revision ("implementers should
  adjust the invariant"). The field was dropped from the
  structure; `compileFrag_bsum_partial_base`'s discharge
  simplified. phase_i0 was independently verified to not depend
  on the precondition's `fBody_zero` (it *establishes* the
  post-state version via the zero-sweep). +5/-34 LOC. Commit
  `ymnzntyr 32327610`.

- **bsum.3.phase_i3 — accUpdate + incR + goto**: Composes the
  4-instruction accUpdate `transferLoop` (`4 * f.interp(...) + 1`
  URM steps) with `incR vI` + `goto topPC` (1 URM step each).
  T0 = `4 * f.interp (Fin.cons i.val (Fin.tail v)) + 3`,
  closed-form, inlined-conjunction. Direct conclusion is
  `partial_invariant @ (i.val + 1)`. Added helper
  `compileFrag_bsum_accUpdateBlock_instr_at` (~400 LOC) — third
  instance of the segment-peeling pattern. +836 LOC. Commit
  `tmpzvqwr 0e910ec1`.

- **bsum.4 — induction glue (i → i+1)**: Composes the four
  phase-preservation lemmas via `URMState.runFor_add`; the
  conclusion is existential because phase_i2's T0 is from
  `ih_f`. PC-window case split over four intervals, each phase's
  strict bound relaxed to `bsum_exitPC`. Notably compact at +194
  LOC (the four-phase contracts compose cleanly). Commit
  `opykmsnx 8c1ba576`.

- **bsum.5 — outer iteration (i = 0 → v 0)**: Strengthened
  `compileFrag_bsum_partial_aux` (∀ i ≤ v 0) by induction on
  `i : ℕ`; base case via `compileFrag_bsum_partial_base`, step
  case via `compileFrag_bsum_partial_step`. Bound shape:
  `(6 + 9 * (v 0)) + ((List.range i).map perIter).foldl (· + ·) 0`.
  Added `compileFrag_bsum_prelude_pc_strict_bound` (a third copy
  of the s0→s4 step ladder; ~75% overlap with `partial_base`).
  Thin specialisation `compileFrag_bsum_partial` at i = v 0.
  +424 LOC. Commit `mmsvvnoz b2c6d3c4`.

- **Fix: bsum/bprod runtime per-iter prologue overhead**: Task
  10's `compileER_runtime` had insufficient `+ 50` constant for
  bsum perIter (and `+ 60` for bprod) — negative slack for
  arity > 22. Added `+ 2 * (k + 1)` to both branches. The
  defect surfaced only at the runtime-bound discharge in bsum.6;
  no earlier proof exercised the bound symbolically over `k`.
  Minimal correction (the `2 * (k + 1)` term comes from the
  prologue's `+ 2` summand across `k + 1` slots). Commit
  `vpxorvpw f8e7a28a`.

- **Refactor: structural numRegs identity + bprod off-by-one**:
  Added `compileER_numRegs_eq_compileERFrag_numRegs : ∀ {a}
  (e : ERMor1 a), compileER_numRegs e = (compileERFrag e).numRegs`
  by structural induction. Independently uncovered Task 9's
  `compileER_numRegs (.bprod f)` off-by-one (`k + 9` → `k + 10`;
  the original would have aliased `vMulTmp` at index `k + 9`
  with `fBase` at the same index, corrupting f's first register).
  Both fixes interlocked: the structural identity does not hold
  under the original `k + 9`. +104 LOC. Commit `xxwysuvu b39b48e7`.

- **bsum.6 — `compileER_pre_stop_correct_bsum` final
  assembly**: Composes `compileFrag_bsum_partial` (i = v 0 at
  loop top with V_x = 0) with the exit jumpZR step (taken via
  zero branch to `bsum_exitPC`). Slack arithmetic against the
  fixed `compileER_runtime` closed using the structural numRegs
  identity. Un-`private`d `vPrefixSum_succ` and
  `vPrefixSum_eq_foldl_finRange` in `Comp.lean` for cross-module
  consumption (re-`private` candidate once
  `h_outerSum_eq`-style helper migrates from BSum.lean to
  Comp.lean). +298 LOC. Commit `wlsnlkvx f10bdb02`.

- **11f — `compileER_runFor_bsum`**: 3-line wrapper composing
  `compileER_pre_stop_correct_bsum` with the existing bridge
  `compileER_pre_stop_to_runFor` (mirrors `compileER_runFor_comp`
  at Comp.lean:5402). +33 LOC. Commit `zpoqzoxk 40b93026`.

Cumulative session-6 output: 11 commits (9 feat + 1 fix + 1
refactor), ~4252 LOC on BSum.lean (786 → 5038), +104 LOC on
Compiler.lean, 2 privacy lifts in Comp.lean. All axiom checks
`[propext, Quot.sound]` only. Build clean throughout. Two
latent specification bugs fixed (compileER_runtime per-iter
constants; bprod numRegs off-by-one) — exactly the value
proposition of formal correctness proofs.

#### Session 4 (2026-05-19, file split landed)

- **File split (followup item 9)**: extracted the
  11,943-line monolith `GebLean/LawvereERKSim.lean` into
  five topical submodules under `GebLean/LawvereERKSim/`
  plus a pure-import index. Layered design: Compiler →
  Embedding → Loops → {Atoms, Comp}. Two minor
  dependency-forced deviations from the spec recorded:
  `compileFrag_comp_subBlock_length` and
  `flatMap_finRange_split` moved into `Compiler.lean`
  (Loops's dischargers consume them); `Comp.lean` imports
  `Atoms` instead of `Loops` because it references
  `URMState.init_regs_inputRegs`. Spec/plan converged via
  three rounds of adversarial review (43 defects across
  rounds, all resolved). SDD execution: 7 implementer
  subagent runs + 7 spec reviewers + 7 code-quality
  reviewers + Task 1 + Task 7 + Task 8 done inline. All
  spec §7 flagship `lean_verify` checks return
  `[propext, Quot.sound]` only. Final per-file sizes:
  index 38, Compiler 1606, Embedding 898, Loops 2538,
  Atoms 1635, Comp 5444. Commits `3e8319cb..6bdbbad5`.

#### Session 3 (2026-05-19, Task 11e.7 wrap-up)

- **11e.7**: `compileER_pre_stop_to_runFor` — a generic,
  constructor-agnostic bridge from the existential pre-stop
  form (∃ T0 ≤ runtime ∧ PC = size-1 ∧ output correct) to
  the output-only `≤ t'` form, plus `compileER_runFor_comp`
  (the comp wrapper). The bridge uses `URMState.runFor_add`
  to split `t' = T0 + (t' - T0)` and `URMState.runFor_stop`
  to absorb slack at the stop instruction at `size - 1`
  (discharged via `CompiledFragment.lastInstr_isStop`).
  Bridge is reusable by 11f (bsum) and 11g (bprod). Commits
  `nozsnnzwruvn`, `rskrmpzkuqnt`, `ysonuwwvpkox` (the third
  is a code-quality follow-up that drops the unused strict-
  PC conjunct from the bridge's `h_pre`, sweeps two dead
  `with` bindings, rephrases the wrapper docstring, and adds
  a comment clarifying the `generalize`-`subst` shuffle).

#### Session 2 (2026-05-19, finishing the comp story)

- **11e.6.a.iii-comp.2.inv-phase_i2**:
  `compileFrag_comp_phase_i2_post` (9-clause post-state,
  drops `gs_m_inputs`/`gs_m_other_zero`, adds
  `gs_m_output`) and `compileFrag_comp_subBlocks_partial_phase_i2`.
  Threads the structural IH `ih_gs_m` (existential form)
  and wraps `compileFrag_comp_subBlock_gsBody_correct`.
  Conclusion existential in `T0 ≤ compileER_runtime (gs m) v`
  with PC strict bound up to `pcOf m + 9*a + (size - 1)`.
  Commit `7608ee31` (after followup fix of a dead `with
  hf_init_def` binding).
- **11e.6.a.iii-comp.2.inv-phase_i3**:
  `compileFrag_comp_subBlocks_partial_phase_i3`. No
  intermediate `phase_i3_post` — the conclusion is
  `partial_invariant @ (m.val + 1)` directly. Wraps
  `compileFrag_comp_subBlock_outputTransfer_correct` and
  its `_pc_strict_bound` counterpart. Deterministic step
  count `4 * (gs m).interp v + 1`. Commit `2cca954b`.
- **11e.6.a.iii-comp.2.ind**:
  `compileFrag_comp_subBlocks_partial_step` — the
  induction-glue lemma threading phases i.1, i.2, i.3
  across a single `m → m + 1` advance. Plus the extracted
  helper `compileFrag_comp_subBlocks_partial_phase_i1_pc_strict_bound`
  (~170 LOC; mirrors phase i.1's preservation setup but
  concludes the strict PC bound from
  `compileFrag_comp_subBlock_inputCopies_pc_strict_bound`).
  Commit `54f8b256`.
- **11e.6.a.iii-comp.3.a**:
  `compileFrag_comp_subBlocks_partial` — the outer
  iteration from m=0 to m=k via induction on m. Plus
  helpers `compileFrag_comp_subBlocks_partial_aux`
  (strengthened `∀ m ≤ k` form) and
  `compileFrag_comp_finRange_filter_lt_succ` (filter-snoc
  identity on `List.finRange`). Conclusion existential in
  `T_total ≤ 1 + ∑_{i<k} (T1+runtime_i+T2)` with strict PC
  bound `< compileFrag_comp_pcOf frag_gs k = fPcBase`.
  Commit `58a3c1dc`.
- **11e.6.a.iii-comp.3.b**:
  `compileER_pre_stop_correct_comp` — the final comp
  pre-stop assembly. Composes comp.3.a's outer iteration
  with the f-body embedding (Task 11e.2-3's
  `ProgramEmbedsFragment_compileFrag_comp_fBody`) and the
  structural IH on f. Plus bridge helpers
  `vPrefixSum_eq_foldl_finRange` and `_aux` that connect
  comp.3.a's bound shape to `compileER_runtime` for comp's
  `v_total` term. Commit `99d5fd91`.

### Cumulative output

Approximately 74 commits, ~19550 LOC of correctness proof +
infrastructure. `GebLean/LawvereERKSim/` six submodules total
~13260 lines (Compiler 1790, Embedding 898, Loops 2538, Atoms
1635, Comp 5444, BSum 5038) plus the 38-line pure-import index.
All build clean. Axiom hygiene clean (`[propext, Quot.sound]`
only on every declaration; verified via
`mcp__lean-lsp__lean_verify` per-declaration).

## What remains

### Task 11e.6.a.iii-bprod — bprod pre-stop

Mirror of the landed bsum chain, with multiplicative accumulator
in place of additive and a doubled-`transferLoop` for the
`R^XY_Z` register update. ~3000-4000 LOC across ~14 sub-tasks.
New work lands in `GebLean/LawvereERKSim/BProd.lean`.

The bsum sub-division at
`docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`
is the template; the next session begins by drafting an analogous
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
that mirrors the bsum doc with the per-iteration phase adjustments
for the multiplicative case. Per the project's "Non-negotiable
interfaces for formalising pre-existing objects" rule, lemma
signatures should mirror the bsum versions exactly, substituting
`.bprod` for `.bsum`, `natBProd` for `natBSum`, and the multi
`transferLoop` pair for the additive single. Adversarial review
of the bprod sub-division before SDD execution begins.

The infrastructure carried over from bsum:

- `compileER_pre_stop_to_runFor` bridge (Embedding.lean) consumes
  the standard pre-stop existential — bprod will produce the same
  shape.
- `compileER_numRegs_eq_compileERFrag_numRegs` (Compiler.lean
  session 6) closes the slack-arithmetic gap for bprod's final
  assembly the same way it did for bsum.
- The corrected `compileER_runtime` for `.bprod` already carries
  the `+ 2 * (k + 1)` per-iter constant (session-6 fix).
- The bprod `numRegs = k + 10 + frag_f.numRegs` is now correct
  (session-6 off-by-one fix).

### Task 11g — bprod runFor wrapper

3-line wrapper around the bridge once
`compileER_pre_stop_correct_bprod` lands. ~30 LOC. Mirrors
`compileER_runFor_bsum` (BSum.lean tail).

### Task 11h — top-level structural induction

`compileER_runFor` by structural induction on `e`
dispatching to per-constructor `_runFor_*` lemmas
(zero/succ/proj/sub/comp/bsum/bprod). ~50-100 LOC. Consider
landing in a new `GebLean/LawvereERKSim/Top.lean` submodule.

### Task 12 — axiom audit

Manual lint pass over every submodule under
`GebLean/LawvereERKSim/`. The earlier-flagged defect with
`scripts/check-axioms.sh` not seeing nested namespaces is
documented but unresolved
upstream — `mcp__lean-lsp__lean_verify` is the per-declaration
authoritative tool.

### Final holistic code-quality review

Per the original SDD plan, after all 13 tasks land:
dispatch a final fresh-context reviewer over the entire T2
implementation.

### Followup branch (post-T2)

Tracked as task #654. Accumulated across phase i.1/i.2/i.3,
comp.2.ind, comp.3.a, comp.3.b reviews, plus file-split SDD
reviews.

> **Status (2026-05-20). Reconciled list.** Of the 22 items
> below, three have landed during subsequent T2 sessions:
> item 5 (dead `with hf_init_def`, landed in chore commit
> `4677a7b5`), item 9 (file split, landed in session 4), and
> item 14 (`Top.lean` submodule, landed in Task 11h commit
> `30f570dd`). The remaining 19 items are open for the
> follow-up cleanup branch, joined by three new findings from
> the T2-final holistic review (see task #654's description
> for the current curated list): renaming Prop-valued
> structures `preservingTransferInstrs`/`transferLoopInstrs`/
> `subInnerLoopInstrs`/`inputCopies_disj` to `UpperCamelCase`,
> renaming theorems prefixed by a structure name to
> `snake_case`, and the speculative bsum/bprod scaffold
> factorisation. The live, deduplicated tracker lives in task
> #654's description; the per-item annotations below remain as
> the historical context for each item.

Items 1-8 are the original comp-era followups; items 9-13 are
file-split-era; items 14-22 are bsum-era (sessions 5-6):

1. Rename `gsPrefixSum_mono`'s `{n m : ℕ}` binders to
   `{n n' : ℕ}` so inlined `h_aux_mono` in phases i.1, i.2,
   i.3 can be replaced.
2. Extract `fin_pack` helpers per register family.
3. Extract `disj_triple_for_reg` helper.
4. Extract `compileFrag_comp_subBlocks_partial_phase_i1_setup`
   shared between phase i.1 preservation and the strict-bound
   helper (~140 LOC dedup).
5. ~~Sweep dead `with hf_init_def` at lines 6085 and 7067.~~
   **DONE in chore commit `4677a7b5` (2026-05-20).**
6. Replace inline `h_filter_snoc` block in
   `compileFrag_comp_pcOf_succ` with the new
   `compileFrag_comp_finRange_filter_lt_succ`.
7. comp.3.b cleanups: dead `have` deletion, docstring
   rephrase on `vPrefixSum_eq_foldl_finRange_aux`,
   `h_compEq`/`h_initEq` triple dedup, promote `h_foldl_le`
   and `h_foldl_map_eq` to top-level helpers.
8. Extract `compileFrag_comp_size` and
   `compileFrag_comp_pcOf_top` for bsum/bprod reuse.
9. **File split**: DONE in Session 4 (see above).
10. Move `URMState.init_regs_inputRegs` from `Atoms.lean`
    to `Embedding.lean` so `Comp.lean` can import `Loops`
    rather than `Atoms`, restoring spec §3.1's parallel
    Atoms/Comp DAG.
11. Re-evaluate `private` promotions across submodules
    once bsum and bprod extractions absorb the remaining
    consumers, restoring `private` where no inter-file
    consumer remains. Two known cases at file-split
    landing:
    (a) `Loops.lean` has 10 declarations promoted to public
        (3 hypothesis-bundle structures plus 7 correctness/
        PC-bound theorems), each with at least one current
        cross-file consumer — restore `private` only if a
        future task removes that consumer.
    (b) `Embedding.lean` has 6 declarations pre-emptively
        promoted to public without current cross-file
        consumers (`getElem_of_getElem?_some`,
        `stateEmbedsFrag_step`,
        `stateEmbedsFrag_step_outside_preserved`,
        `compileER_runFor_pc_le_size`,
        `fragment_runFor_pc_le_size`,
        `stateEmbedsFrag_step_tail`). Final reviewer flagged
        these as Important; either restore `private` now or
        confirm they are needed by bsum/bprod tasks and
        keep public.
12. Audit the `## Main definitions` / `## Main statements`
    sections in each submodule docstring against the
    file's actual public surface (Task 2 review flagged
    `Compiler.lean` listing `private` decls in
    `## Main statements`; same pattern may exist elsewhere).
13. Add `/-! ### ... -/` section markers to `Comp.lean`
    around the six logical phases (length, k=0, sub-block,
    m-step, outer iteration, assembly, runFor wrapper) for
    navigability of the 5444-line file.
14. ~~After Task 11h lands, consider adding a `Top.lean`
    submodule for the top-level structural induction and
    re-evaluate the index file's responsibilities.~~
    **DONE in Task 11h commit `30f570dd` (2026-05-20).**
    `GebLean/LawvereERKSim/Top.lean` (100 LOC) contains both
    `compileER_pre_stop_correct` and `compileER_runFor`; the
    index `LawvereERKSim.lean` was updated to import it.
15. Extract a shared `compileFrag_bsum_rawList_scaffold` lemma
    (or `compileFrag_bsum_segment_at` parameterised by segment
    offset and extractor) to deduplicate ~70% overlap across
    `compileFrag_bsum_zeroSweep_instr_at`,
    `compileFrag_bsum_prologueBlock_instr_at`, and
    `compileFrag_bsum_accUpdateBlock_instr_at` (each in BSum.lean
    after their respective phase landings). The same scaffold
    will be reused four-fold across the upcoming bprod chain.
16. Extract a shared s0→s4 prelude step-ladder lemma between
    `compileFrag_bsum_partial_base` (BSum.lean) and
    `compileFrag_bsum_prelude_pc_strict_bound` (~75% duplication).
17. Extract an `outside_preserved_at r h_outside` tactic-level
    macro for the 5-line ritual (`let r / have h_out / have
    h_pres / have h_idx_eq / rw + h.field`) that repeats 8 times
    in phase_i2 lemmas across bsum and comp, and will repeat in
    bprod's phase_i2.
18. Extract `h_foldl_le`, `h_foldl_map_eq`, and `h_outerSum_eq`
    helpers from their inline appearances in `BSum.lean`
    (~4843+) and `Comp.lean` (~5272+) into a shared location
    (Loops.lean or a new utilities slot in Comp.lean). After
    `h_outerSum_eq` migrates out of BSum.lean, restore `private`
    on `vPrefixSum_succ` and `vPrefixSum_eq_foldl_finRange` in
    `Comp.lean`.
19. Sweep dead bindings: `have h_eq` at BSum.lean:3078 (inside
    phase_i2 destructuring), `have h_numRegs_pos` at
    BSum.lean:3703 (inside phase_i3), and any further dead
    `with` bindings in BSum.lean introduced after `set`-based
    abbreviations.
20. Update `BSum.lean`'s module docstring's `## Main statements`
    section to include the session-6 additions
    (`compileFrag_bsum_partial_phase_i2`,
    `compileFrag_bsum_partial_step`,
    `compileFrag_bsum_partial_aux`,
    `compileFrag_bsum_partial`,
    `compileER_pre_stop_correct_bsum`,
    `compileER_runFor_bsum`,
    `compileFrag_bsum_prelude_pc_strict_bound`). Per the
    project convention, do **not** list private declarations
    there; either restore the previously-listed private decls
    to a separate section (e.g. `## Implementation notes`) or
    promote the small subset that warrants public visibility.
21. Replace the `set sPost := …`/`set sFinal := …` bindings in
    `compileER_pre_stop_correct_bsum` (BSum.lean tail) with
    plain `let` (Pattern 9): their RHSes are intermediate
    states not referenced from any parameter type.
22. `simp only [if_pos h]` was found to leak `sorryAx` into the
    enclosing declaration's axiom set in the current
    toolchain; `rw [if_pos h]` does not. Audit BSum.lean and
    Comp.lean for `simp only [if_*]` occurrences and convert
    each to `rw` to harden the axiom-hygiene story. See
    `feedback_simp_if_pos_sorryAx_leak.md` in user memory.

## Resolved design for 11e.7 (option a-bridge)

The existing `compileER_runFor_*` lemmas (`_zero`, `_succ`,
`_proj`, `_sub`, `_comp_k_zero`) are in the `≤ t'` form
(output-only conclusion, slack absorbed). The existing
`compileER_pre_stop_correct_*` atom lemmas plus
`compileER_pre_stop_correct_comp` are in the *existential*
form (∃ T0 ≤ runtime, with PC = size-1, output = interp,
strict PC bound on earlier steps).

Resolved at session-3 start: **option (a-bridge)**. The
existential and `≤ t'` forms are bridged by a single shared
helper that does not depend on the constructor:

```lean
private theorem compileER_pre_stop_to_runFor {a : ℕ}
    (e : ERMor1 a) (v : Fin a → ℕ) (t' : ℕ)
    (ht' : compileER_runtime e v ≤ t')
    (h_pre : ∃ T0 : ℕ,
      T0 ≤ compileER_runtime e v ∧
      (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) T0).pc
          = (compileER e).instrs.size - 1 ∧
      (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) T0).regs
          (compileER e).outputReg
        = e.interp v ∧
      (∀ k' < T0,
        (URMState.runFor (compileER e)
            (URMState.init (compileER e) v) k').pc
          < (compileER e).instrs.size - 1)) :
    (URMState.runFor (compileER e)
        (URMState.init (compileER e) v) t').regs
        (compileER e).outputReg
      = e.interp v
```

Proof sketch: write `t' = T0 + (t' - T0)`; apply
`URMState.runFor_add` then `URMState.runFor_stop` at PC
`size - 1` (which is `URMInstr.stop` by
`CompiledFragment.lastInstr_isStop`).

11e.7 (`compileER_runFor_comp` general k) becomes a thin
wrapper: invoke `compileER_pre_stop_correct_comp` to obtain
the existential, then `compileER_pre_stop_to_runFor`. 11f,
11g (bsum, bprod) follow the same wrapper pattern once
their pre-stop lemmas land. The four existing atom
`compileER_runFor_*` lemmas (zero/succ/proj/sub) are kept as
landed (no rewrite cost); Task 11h dispatches structurally
in the `≤ t'` form over all 7 constructors.

The bridge approach also collapses the IH-shape mismatch
inside 11e.7: 11e.7 takes IHs on f and gs in existential
form (matching comp.3.b's signature exactly); the user-
facing `compileER_runFor_comp` conclusion is the `≤ t'`
form. Task 11h supplies the existential-form IHs to 11e.7
via the per-constructor `_pre_stop_correct_*` lemmas, then
collects the `≤ t'` conclusions via the corresponding
`_runFor_*` lemmas.

## Patterns learned (lessons for resumption)

1. **mathlib's `fin_cases` pulls in `Classical.choice`**.
   Use Lean-core `Fin.cases` eliminator or explicit
   `match p, q with | ⟨0, _⟩, ⟨0, _⟩ => …` for `Fin n`
   case-splits. Same applies to `List.nodup_finRange` and
   `List.filter_eq_nil_iff` — both Classical-dependent.

2. **`by_cases` can pull `Classical.choice`** depending on
   the decidability instances in scope. For three-way PC
   interval splits in compositional proofs, use
   `Nat.lt_or_ge a b` with `rcases ... with h | h`. Verified
   constructively across phase i.1/i.2/i.3, comp.2.ind,
   comp.3.a, comp.3.b.

3. **`URMInstrRaw.toBoundedArray`** definitionally reduces
   on concrete `rawList` values. The 9 `rfl`-form
   instruction-presence equalities work out by definitional
   reduction.

4. **`Function.update`** commutation requires explicit
   per-pair disjointness in `Fin numRegs`. Discharge via
   `congrArg Fin.val + omega` (clean, no `simp`).

5. **`runFor_succ` peeling** doesn't generalize past
   "concrete step count" arguments. For bounded
   correctness theorems, use `URMState.runFor_add` to split
   intervals and `URMState.runFor_stop` for slack
   absorption.

6. **`stateEmbedsFrag_runFor` strict precondition**
   (`∀ k < T, .pc < L`) is the central tightness in
   compositional proofs. The pre-stop lemma chain
   (compileER_pre_stop_correct) is built specifically to
   discharge it. The non-tail variant suffices when the IH
   provides the strict bound; the `_tail` variant is for
   embedded programs that end at the outer's tail without
   an IH-provided strict bound.

7. **Disjoint register blocks** for sub-fragments
   (compileFrag_comp's design) simplify the embedding
   bounds proof at the cost of slightly more registers.

8. **Architecture diverges from Tourlakis at granularity,
   not at structure**. We follow his structural induction
   over ER constructors but trace per-instruction; he
   argues semantically per program. The depth-of-subdivision
   is the formalization tax on his "essentially concatenate
   M_g and M_f" type sentences.

9. **`set` re-elaborates function parameter types**. Prefer
   `let` over `set` when the abbreviation's RHS appears in
   an existing parameter's type. The cost is omega's loss
   of syntactic identity across `frag_gs i` vs
   `compileERFrag (gs i)`; restore via explicit `have h_eq
   : ... := rfl` bridges before each `omega`. Verified
   across all session-2 lemmas.

10. **Field-projection over destructure for partial
    invariants**. `obtain ⟨..⟩ := h_inv` introduces fresh
    bindings that can carry stale parameter-shadow names;
    `h_inv.fieldName` evaluates per-projection.

11. **`List.find?` case-split via `generalize` + `match`**
    is the constructive alternative to `∃ j, P j` plus
    `Classical.em`. Phase i.2 used this for the
    `inputRegs` membership test; comp.3.b reused the
    pattern.

12. **Dead `with name` bindings** in `set`-based
    abbreviations: phase i.2 inherited a dead `with
    hf_init_def` from `subBlock_gsBody_correct`. Code
    quality review caught it; pre-existing copies remain
    at lines 6085 and 7067 (deferred to followup #654).

13. **IH-form mismatch in compositional vs. `≤ t'` lemmas**
    was surfaced when designing 11e.7 and resolved via the
    bridge `compileER_pre_stop_to_runFor`: compositional
    `_pre_stop_correct_*` lemmas take and return existential
    pre-stop form; the bridge is the single, constructor-
    agnostic mechanism for producing the `≤ t'` form from
    any pre-stop existential. Future `_runFor_*` wrappers
    (bsum, bprod) reuse the same bridge.

14. **`.pop`-emitted body vs. embedded length**: bsum's f-body
    is `frag_f.instrs.pop.toList.map ...` (dropping the trailing
    stop). The `ProgramEmbedsFragment` embedding length is
    `frag_f.instrs.size - 1`, not `frag_f.instrs.size`. The
    same `-1` pattern applies to comp's `gsBody` and will apply
    to bprod's f-body. Sub-division specs that quote a body's
    embedded length should default to `size - 1` when the
    fragment compiler uses `.pop`.

15. **`simp only` with size-class lemmas can leak `sorryAx`**.
    During the bsum.0 review, `simp only [bsum_exitPC,
    bsum_trBase, bsum_bodyPCBase, compileFrag_bsum_size]; omega`
    pulled `sorryAx` into the lemma's axiom list (likely via
    `simp`'s discrimination-tree traversal touching environment
    lemmas marked `@[simp]` that themselves depend on `sorryAx`
    transitively). The precise alternative — `rw
    [compileFrag_bsum_size]; change ...; rw [...]; omega` —
    restricts the axiom set. Pattern: when an axiom audit
    matters, prefer surgical `rw` over `simp only` on
    layout/size lemmas.

16. **Inlined-conjunction convention for closed-form T0**:
    when a phase-preservation lemma's T0 is closed-form (a
    function of parameters, not an existential witness), drop
    the outer `∃ T0, T0 = const ∧ post ∧ pc_bound` wrapping
    and write `post ∧ pc_bound` at `URMState.runFor _ sPre
    const` directly. The existential carries no information
    when T0 is determined; consumers find the inlined form
    easier to consume (no `obtain` needed). Applied uniformly
    to bsum phase_i0/i1/i3 and the bsum.4 glue's two
    deterministic sub-terms. Phase_i2 keeps the existential
    because its T0 comes from `ih_f`'s witness.

17. **`let`-bound `URMState.init` blocks regs-projection
    reduction**: `let f_init := URMState.init frag.toURMProgram
    v` makes `f_init.regs r` opaque to the unifier; the
    underlying `match`-form does not reduce through the `let`.
    Workaround: introduce the regs-equation lemma with
    `URMState.init ...` written inline (and `unfold URMState.init
    ; simp only []` to beta-reduce the struct projection), then
    bind `let f_init := ...` for subsequent
    `stateEmbedsFrag_*` consumption. Comp's analogous proofs
    avoid the issue because their `frag_gs i := compileERFrag
    (gs i)` is a function applied to a parameter rather than a
    fully-applied `URMState.init`. See
    `feedback_urmstate_init_let_reduction.md` in user memory.

18. **Partial-invariant boundary placement**: if a clause of
    the loop's partial invariant cannot be carried across an
    iteration boundary (because some intra-iteration phase
    invalidates it and a later phase re-establishes it),
    drop the clause from the invariant entirely and let the
    next iteration's first phase re-establish it for its own
    post-state. Surfaced for bsum's `fBody_zero`: phase_i2
    only tracks `f_output`, not the full f-body; the next
    iteration's phase_i0 zero-sweep restores the full block.
    Cleaner than carrying a vacuous "or some state we don't
    track" disjunction. Anticipated by the sub-division
    plan's notes for phase_i3.

19. **Closed-form T0 elaboration via `change` + type
    ascription**: when chaining phase lemmas via
    `URMState.runFor_add`, omega and the dispatched lemma
    outputs need to share syntactic form. Use `let`-bound
    abbreviations (`frag_f`, `outer`, `v_iter`, etc.), then
    a `change` block immediately after introducing them to
    rewrite the goal in `let`-bound form. Use a type-
    ascribed `have h : T0 ≤ <fold> := ih_value` to force a
    let-folded shape when the dispatched value carries the
    unfolded form. Generalisation of the `URMState.init`
    quirk above.

## Resumption recipe

1. `lake build` (whole tree) — should be clean. Run
   `markdownlint-cli2 '**/*.md'` and `doctoc '**/*.md'
   --check` to confirm doc state.

2. **Draft the bprod pre-stop sub-division** at
   `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
   following the structure of the bsum sub-division at
   `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`,
   adapted for the multiplicative case (`natBProd` for
   `natBSum`, multiplicative accumulator, R^XY_Z's doubled
   `transferLoop`, +1 register `vFactor`/`vMulTmp`). Bind
   lemma signatures to the bsum versions where possible.
   Adversarially review the bprod sub-division to convergence
   before SDD execution begins. The bprod chain will land in
   a new `GebLean/LawvereERKSim/BProd.lean` submodule.

3. **Execute bprod pre-stop** via
   `superpowers:subagent-driven-development`, sub-task by
   sub-task with fresh implementer + spec reviewer + code
   reviewer per task. Carry the patterns learned during the
   bsum chain (especially the inlined-conjunction
   convention for closed-form T0 phases, the
   `URMState.init` reduction quirk, the `simp only [if_pos]`
   sorryAx leak, and the structural-numRegs identity that
   closes the slack arithmetic in the final assembly).
   Estimated ~3000-4000 LOC across ~14 sub-tasks.

4. **Task 11g** — `compileER_runFor_bprod` wrapper. 3-line
   composition of `compileER_pre_stop_correct_bprod` with
   `compileER_pre_stop_to_runFor`. Mirror of
   `compileER_runFor_bsum` (BSum.lean tail).

5. **Task 11h** — top-level structural induction in `≤ t'`
   form, dispatching to `compileER_runFor_*` per
   constructor (zero/succ/proj/sub/comp/bsum/bprod). Land
   in a new `GebLean/LawvereERKSim/Top.lean` submodule;
   re-evaluate the index file's role.

6. **Task 12** — axiom audit + manual lint. Per-submodule
   `mcp__lean-lsp__lean_verify` sweep is authoritative;
   `scripts/check-axioms.sh` has a documented nested-namespace
   defect.

7. **Final holistic code-quality review** per the original
   SDD plan. Single fresh-context reviewer over the entire
   T2 implementation.

8. **Followup branch** — task #654's accumulated items
   (22 entries as of session 6). Address as a single
   refactor branch after final review.

## References

- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- Plan (binding for next-session execution):
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- bsum sub-division (template for bprod):
  `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`.
- Execution skill (binding for next session):
  `superpowers:subagent-driven-development`.
- Source: six submodules under `GebLean/LawvereERKSim/`
  totalling ~13260 lines (Compiler 1790, Embedding 898,
  Loops 2538, Atoms 1635, Comp 5444, BSum 5038) plus the
  38-line `GebLean/LawvereERKSim.lean` index.
