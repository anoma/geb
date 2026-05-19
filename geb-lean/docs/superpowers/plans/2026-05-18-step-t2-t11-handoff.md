# Step T2 Task 11 — Partial-completion handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Session summary](#session-summary)
- [What is landed](#what-is-landed)
  - [Tasks 0-10 (compiler infrastructure)](#tasks-0-10-compiler-infrastructure)
  - [Task 11 — landed sub-tasks](#task-11--landed-sub-tasks)
  - [Cumulative session output](#cumulative-session-output)
- [What remains](#what-remains)
  - [Task 11e.6.a.iii — compositional pre-stop correctness](#task-11e6aiii--compositional-pre-stop-correctness)
  - [Task 11e.7](#task-11e7)
  - [Tasks 11f, 11g](#tasks-11f-11g)
  - [Task 11h](#task-11h)
  - [Task 12](#task-12)
  - [Final holistic code-quality review](#final-holistic-code-quality-review)
- [Patterns learned (lessons for resumption)](#patterns-learned-lessons-for-resumption)
- [Resumption recipe](#resumption-recipe)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Resumption guide for a future session picking up T11
(compileER_runFor correctness theorem) where the present
session paused.

## Session summary

A multi-day SDD execution of T2 completed Tasks 0-10
(compileER + compileER_runtime + 7 per-constructor
combinators) plus substantial groundwork on Task 11
(compileER_runFor structural correctness theorem). The
present session ended with all four atom cases proven,
the compositional-case infrastructure built, and the comp
m-step induction base case landed. The comp m-step
induction step, comp final assembly, bsum/bprod
pre-stop correctness, and top-level assembly remain.

Current `@-`: commit `e66f7681` (compileFrag_comp_pcOf_succ
constructively). Build clean. Axiom hygiene clean
(`[propext, Quot.sound]` only on all new declarations).

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
- **11e.6.a.iii-comp.1.a**: abstract Phase i.1 helper
  `compileFrag_comp_subBlock_inputCopies_correct` +
  `vPrefixSum`, `inputCopies_disj`,
  `inputCopies_prefix_correct`,
  `compileFrag_comp_subBlock_inputCopies_pc_strict_bound`.
  Commit `0c08e3ce`.
- **11e.6.a.iii-comp.1.b**: abstract Phase i.2 helper
  `compileFrag_comp_subBlock_gsBody_correct`.
  Commit `b5c05d41`.
- **11e.6.a.iii-comp.1.c**: abstract Phase i.3 helper
  `compileFrag_comp_subBlock_outputTransfer_correct` +
  `_pc_strict_bound`. Commit `a78d27f2`.
- **Outside-preserved helpers**:
  `stateEmbedsFrag_step_outside_preserved` +
  `stateEmbedsFrag_runFor_outside_preserved`.
  Commit `8947b0ac`.
- **11e.6.a.iii-comp.2.pre1**:
  `PreservingTransferInstrs_compileFrag_comp_inputCopies`
  — discharges the 9*a instruction-presence equalities
  for Phase i.1 inside compileFrag_comp. Commit
  `e52a9601`.
- **11e.6.a.iii-comp.2.pre2**:
  `TransferLoopInstrs_compileFrag_comp_outputTransfer`
  — discharges the 4 instruction-presence equalities
  for Phase i.3 inside compileFrag_comp. Commit
  `8f410639`.
- **11e.6.a.iii-comp.2.base**:
  `compileFrag_comp_partial_invariant` (8-clause
  structure) + `compileFrag_comp_subBlocks_partial_base`
  (m = 0 case) + `compileFrag_comp_pcOf` +
  `compileFrag_comp_pcOf_zero`. Commit `b9f4dc47`.
- **11e.6.a.iii-comp.2.inv-prereq**:
  `compileFrag_comp_pcOf_succ` (constructive,
  Classical-free). Commit `e66f7681`.

### Cumulative session output

Approximately 44 commits, ~12000 LOC of correctness
proof + infrastructure. All build clean. Axiom hygiene
clean (`[propext, Quot.sound]` only on every
declaration; `scripts/check-axioms.sh` passes).

## What remains

### Task 11e.6.a.iii — compositional pre-stop correctness

- **11e.6.a.iii-comp.2.inv**: three preserves-under-phase
  lemmas
  (`compileFrag_comp_subBlocks_partial_phase_i1`, `_i2`,
  `_i3`). ~250 LOC each. The `pcOf_succ` foundation is
  in place.
- **11e.6.a.iii-comp.2.ind**: induction-glue lemma
  composing the three phase preservations across
  `m → m + 1`. ~150-200 LOC.
- **11e.6.a.iii-comp.3**: final
  `compileER_pre_stop_correct_comp` assembling
  `compileFrag_comp_subBlocks_partial` at `m = k` +
  f-body embedding + trailing stop step + global PC
  bound assembly. ~600-900 LOC.
- **11e.6.a.iii-bsum**: analogous pre-stop chain for
  `compileFrag_bsum`. Likely sub-subdivides into:
  outer-loop induction; per-iteration zero-sweep +
  prologue + f-body + accumulator-update phases.
  Estimated 3000-4000 LOC across ~6-10 sub-sub-sub-tasks.
- **11e.6.a.iii-bprod**: analogous for `compileFrag_bprod`.
  Estimated similar magnitude to bsum.

### Task 11e.7

`compileER_runFor_comp` from `compileER_pre_stop_correct_comp`
plus slack absorption. ~100-200 LOC. Straightforward once
the pre-stop lemma is in place.

### Tasks 11f, 11g

Analogues of 11e.7 for `bsum` and `bprod`. Each is
similarly small once the corresponding pre-stop lemma
exists. ~100-200 LOC each.

### Task 11h

Top-level `compileER_runFor` by structural induction on
`e` dispatching to per-constructor correctness lemmas
(zero/succ/proj/sub/comp/bsum/bprod). ~50-100 LOC.

### Task 12

Axiom audit + manual lint pass over the entire
`GebLean/LawvereERKSim.lean`. The implementer-flagged
defect with `scripts/check-axioms.sh` not seeing nested
namespaces is documented but unresolved upstream.

### Final holistic code-quality review

Per the original SDD plan, after all 13 tasks land:
dispatch a final fresh-context reviewer over the entire
T2 implementation.

## Patterns learned (lessons for resumption)

1. **mathlib's `fin_cases` pulls in `Classical.choice`**.
   Use Lean-core `Fin.cases` eliminator or explicit
   `match p, q with | ⟨0, _⟩, ⟨0, _⟩ => …` for `Fin n`
   case-splits. Same applies to `List.nodup_finRange` and
   `List.filter_eq_nil_iff` — both Classical-dependent;
   constructive alternatives needed.

2. **`URMInstrRaw.toBoundedArray`** definitionally reduces
   on concrete `rawList` values. The 9 `rfl`-form
   instruction-presence equalities work out by definitional
   reduction; no explicit indexing-lemma invocation needed.

3. **`Function.update`** commutation requires explicit
   per-pair disjointness in `Fin numRegs`. Discharge via
   `congrArg Fin.val + omega` (clean, no `simp`).

4. **`runFor_succ` peeling** doesn't generalize past
   "concrete step count" arguments. For bounded
   correctness theorems, use `runFor_add` to split
   `t' = (prefix) + slack` and `runFor_stop` for slack
   absorption.

5. **`stateEmbedsFrag_runFor` strict precondition**
   (`∀ k < T, .pc < L`) is the central tightness in
   compositional proofs. The pre-stop lemma chain
   (compileER_pre_stop_correct) is built specifically to
   discharge it.

6. **Disjoint register blocks** for sub-fragments
   (compileFrag_comp's design) simplify the embedding
   bounds proof at the cost of slightly more registers.
   Chosen by Task 6's implementer; documented in the
   commit message.

7. **Architecture diverges from Tourlakis at granularity,
   not at structure**. We follow his structural induction
   over ER constructors but trace per-instruction; he
   argues semantically per program. The depth-of-subdivision
   is the formalization tax on his "essentially concatenate
   M_g and M_f" type sentences.

## Resumption recipe

1. Check `jj log -r '0914f03b..@-'` — confirm 44 commits
   from `5c16a133` (T1 refactor) through `e66f7681`
   (pcOf_succ).

2. `lake build GebLean.LawvereERKSim` — should be clean.

3. Dispatch `compileFrag_comp_subBlocks_partial_phase_i1`
   (Phase i.1 preservation) — first of three preserves
   lemmas. Implementer-template: build the
   pre-state-to-post-state argument using
   `compileFrag_comp_subBlock_inputCopies_correct`
   (existing helper) with the `preservingTransferInstrs`
   discharged by `PreservingTransferInstrs_compileFrag_comp_inputCopies`
   (existing helper). Repackage the 8 invariant clauses.

4. Then Phase i.3, then Phase i.2 (most complex due to
   embedding + outside-preserved), then comp.2.ind glue.

5. Then comp.3 (final pre-stop), then comp.k>0 case of
   `compileER_runFor_comp` (≈ 11e.7).

6. Repeat for bsum (likely sub-subdivides like comp).

7. Repeat for bprod (likely the same pattern).

8. Top-level assembly (11h).

9. Axiom audit (Task 12).

## References

- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- Plan:
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- Source: `GebLean/LawvereERKSim.lean` (current size
  ~8400 lines).
