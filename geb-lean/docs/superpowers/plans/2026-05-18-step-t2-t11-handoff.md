# Step T2 Task 11 — Partial-completion handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Execution mode for the next session](#execution-mode-for-the-next-session)
- [Session summary](#session-summary)
- [What is landed](#what-is-landed)
  - [Tasks 0-10 (compiler infrastructure)](#tasks-0-10-compiler-infrastructure)
  - [Task 11 — landed sub-tasks](#task-11--landed-sub-tasks)
    - [Session 1 (through 2026-05-18, ending at phase i.1)](#session-1-through-2026-05-18-ending-at-phase-i1)
    - [Session 5 (2026-05-19, bsum.0–bsum.1.d landed)](#session-5-2026-05-19-bsum0bsum1d-landed)
    - [Session 4 (2026-05-19, file split landed)](#session-4-2026-05-19-file-split-landed)
    - [Session 3 (2026-05-19, Task 11e.7 wrap-up)](#session-3-2026-05-19-task-11e7-wrap-up)
    - [Session 2 (2026-05-19, finishing the comp story)](#session-2-2026-05-19-finishing-the-comp-story)
  - [Cumulative output](#cumulative-output)
- [What remains](#what-remains)
  - [Task 11e.6.a.iii-bsum — bsum pre-stop (in progress)](#task-11e6aiii-bsum--bsum-pre-stop-in-progress)
  - [Task 11e.6.a.iii-bprod — bprod pre-stop](#task-11e6aiii-bprod--bprod-pre-stop)
  - [Tasks 11f, 11g — bsum/bprod runFor wrap-ups](#tasks-11f-11g--bsumbprod-runfor-wrap-ups)
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

A multi-session SDD execution of T2 completed Tasks 0-10
(compileER + compileER_runtime + 7 per-constructor
combinators), the four atom cases of Task 11, the
compositional-case infrastructure, and the full comp pre-stop
correctness chain (phases i.1, i.2, i.3, m-step induction
glue, outer iteration, and final assembly). The present
session ended with `compileER_pre_stop_correct_comp` landed,
closing the comp pre-stop story. Remaining: 11e.7 (the comp
runFor `≤ t'` wrap-up), bsum/bprod pre-stop chains, their
runFor wrap-ups, Task 11h top-level structural induction,
and Task 12 axiom audit.

Current `@-`: commit `99d5fd91` (comp.3.b
`compileER_pre_stop_correct_comp`). Build clean. Axiom
hygiene clean (`[propext, Quot.sound]` only on all new
declarations; verified via `mcp__lean-lsp__lean_verify`).
Source: `GebLean/LawvereERKSim.lean`, 11823 lines.

Sibling head `pnlwkzms f29a83bf` (the previous-session
in-progress doc edit) is preserved across all session-2
commits via jj auto-rebase. The current session is updating
this handoff doc to integrate the session-2 progress.

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

Approximately 62 commits, ~15300 LOC of correctness proof +
infrastructure. `GebLean/LawvereERKSim/` six submodules total
~13000 lines (Compiler 1686, Embedding 898, Loops 2538, Atoms
1635, Comp 5444, BSum 786) plus the 38-line pure-import index.
All build clean. Axiom hygiene clean (`[propext, Quot.sound]`
only on every declaration; verified via
`mcp__lean-lsp__lean_verify` per-declaration).

## What remains

### Task 11e.6.a.iii-bsum — bsum pre-stop (in progress)

Sub-divided into 14 implementer-sized sub-tasks; see
`docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`.

Session 5 landed: sub-tasks bsum.0 (PC layout), bsum.1.a
(zero-sweep), bsum.1.b (prologue alias), bsum.1.c (accumulator
update alias), and bsum.1.d (f-body embedding). BSum.lean is now
786 lines.

Remaining sub-tasks (in dependency order):

- **bsum.2** — partial invariant and base case (10-clause
  `compileFrag_bsum_partial_invariant` structure plus
  `compileFrag_bsum_partial_base` for `i = 0` after the prelude's
  13-step initial run).
- **bsum.3.phase_i0** — zero-sweep preservation.
- **bsum.3.phase_i1** — prologue preservation (instantiates
  bsum.1.b's wrapper).
- **bsum.3.phase_i2** — f-body preservation (consumes the
  structural IH on f).
- **bsum.3.phase_i3** — accumulator-update + `incR` + `goto`
  back to top.
- **bsum.4** — induction glue (`i → i + 1`).
- **bsum.5** — outer iteration (`i = 0` to `i = v 0`).
- **bsum.6** — final assembly: `compileER_pre_stop_correct_bsum`
  in the existential form, ready for the constructor-agnostic
  `compileER_pre_stop_to_runFor` bridge.

### Task 11e.6.a.iii-bprod — bprod pre-stop

Mirror of the bsum sub-division, with multiplicative accumulator
in place of additive and the doubled-`transferLoop` for `R^XY_Z`.
~3000-4000 LOC across ~14 sub-tasks. New work lands in
`GebLean/LawvereERKSim/BProd.lean`. Sub-division to be drafted
once bsum is complete (the sub-division will mostly track the
bsum doc with the per-iteration phase adjustments).

### Tasks 11f, 11g — bsum/bprod runFor wrap-ups

Analogues of 11e.7 for bsum and bprod. Each small once the
corresponding pre-stop lemma exists. ~100-200 LOC each.

### Task 11h — top-level structural induction

`compileER_runFor` by structural induction on `e`
dispatching to per-constructor `_runFor_*` lemmas
(zero/succ/proj/sub/comp/bsum/bprod). ~50-100 LOC.

### Task 12 — axiom audit

Manual lint pass over the entire `GebLean/LawvereERKSim.lean`.
The implementer-flagged defect with `scripts/check-axioms.sh`
not seeing nested namespaces is documented but unresolved
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

Items 1-8 are the original followups; items 9-13 are new
items surfaced during the file-split work:

1. Rename `gsPrefixSum_mono`'s `{n m : ℕ}` binders to
   `{n n' : ℕ}` so inlined `h_aux_mono` in phases i.1, i.2,
   i.3 can be replaced.
2. Extract `fin_pack` helpers per register family.
3. Extract `disj_triple_for_reg` helper.
4. Extract `compileFrag_comp_subBlocks_partial_phase_i1_setup`
   shared between phase i.1 preservation and the strict-bound
   helper (~140 LOC dedup).
5. Sweep dead `with hf_init_def` at lines 6085 and 7067.
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
14. After Task 11h lands, consider adding a `Top.lean`
    submodule for the top-level structural induction and
    re-evaluate the index file's responsibilities.

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

## Resumption recipe

1. `lake build` (whole tree) — should be clean.

2. **Continue bsum pre-stop** in
   `GebLean/LawvereERKSim/BSum.lean`. Sub-tasks bsum.0,
   bsum.1.{a,b,c,d} landed in Session 5. Next: bsum.2
   (partial invariant + base case) — large structure
   declaration plus the 13-step prelude base lemma. Then
   bsum.3.{phase_i0, phase_i1, phase_i2, phase_i3} (four
   per-iteration phase preservation lemmas), bsum.4
   (induction glue), bsum.5 (outer iteration), bsum.6 (final
   pre-stop assembly). The sub-division doc at
   `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`
   has the lemma signatures and dependency DAG. One correction
   recorded: bsum.1.d's signature uses
   `frag_f.instrs.size - 1` (not the originally-stated
   `frag_f.instrs.size`).

3. Then bprod pre-stop in
   `GebLean/LawvereERKSim/BProd.lean`. Sub-divide first; the
   structure largely mirrors bsum with multiplicative
   accumulator and doubled `transferLoop` for R^XY_Z.

4. Then 11f, 11g (bsum/bprod runFor wrappers via the
   shared bridge `compileER_pre_stop_to_runFor` in
   `Embedding.lean`).

5. Then 11h (top-level structural induction in `≤ t'`
   form, dispatching to `compileER_runFor_*` per
   constructor). Add a new `GebLean/LawvereERKSim/Top.lean`
   submodule for this.

6. Then Task 12 (axiom audit + manual lint).

7. Then the final holistic code-quality review per the
   original SDD plan.

## References

- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- Plan (binding for next-session execution):
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- Execution skill (binding for next session):
  `superpowers:subagent-driven-development`.
- Source: `GebLean/LawvereERKSim.lean` (current size
  ~11940 lines).
