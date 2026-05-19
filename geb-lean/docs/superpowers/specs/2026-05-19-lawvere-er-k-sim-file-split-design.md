# LawvereERKSim file split — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Scope](#1-scope)
- [2 Approach: hybrid layered](#2-approach-hybrid-layered)
- [3 Module map](#3-module-map)
  - [3.1 Dependency DAG](#31-dependency-dag)
- [4 Survey: line ranges in the current monolith](#4-survey-line-ranges-in-the-current-monolith)
- [5 Per-submodule contents](#5-per-submodule-contents)
  - [5.1 `Compiler.lean` (Section A)](#51-compilerlean-section-a)
  - [5.2 `Embedding.lean` (Section B + the bridge from Section F)](#52-embeddinglean-section-b--the-bridge-from-section-f)
  - [5.3 `Loops.lean` (Section C)](#53-loopslean-section-c)
  - [5.4 `Atoms.lean` (Section D)](#54-atomslean-section-d)
  - [5.5 `Comp.lean` (Section E + Section F's comp wrapper)](#55-complean-section-e--section-fs-comp-wrapper)
  - [5.6 `GebLean/LawvereERKSim.lean` (index)](#56-gebleanlawvereerksimlean-index)
- [6 Mechanical procedure](#6-mechanical-procedure)
  - [6.1 Visibility adjustments](#61-visibility-adjustments)
  - [6.2 Sectional comments](#62-sectional-comments)
  - [6.3 Module docstrings](#63-module-docstrings)
- [7 Verification](#7-verification)
- [8 Risks and mitigations](#8-risks-and-mitigations)
- [9 Out of scope](#9-out-of-scope)
- [10 References](#10-references)

<!-- END doctoc -->

## 1 Scope

Split the monolithic `GebLean/LawvereERKSim.lean`
(11,943 lines as of commit `a1ff2ff7`) into an index file
and five topical submodules under
`GebLean/LawvereERKSim/`. The split is an
organisational refactor; lemma signatures, proof tactics,
docstrings, and behaviour do not change.

Trigger: Task 11 of T2 (`compileER_runFor` correctness)
has landed all atom cases, comp pre-stop, comp m-step
induction, comp outer iteration, comp final assembly, and
the constructor-agnostic pre-stop-to-runFor bridge. The
remaining bsum and bprod pre-stop chains are projected at
3000–4000 LOC each. Without a split, the file projects to
18,000–19,000 LOC; build cost, reader load, and tactic
parser context all degrade past 12,000 LOC.

Out of scope: bsum/bprod work; new declarations; tightening
of any existing signature; followup-branch items #1–8 from
`docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`
§"Followup branch (post-T2)". Item 9 (the file split itself)
is what this spec covers.

## 2 Approach: hybrid layered

Layered compilation, layered embedding/runtime, layered
loop correctness, per-constructor correctness. Two
alternatives were considered and rejected:

- *Constructor-by-constructor* (one file per ER
  constructor, each containing both compiler and
  correctness) scatters the small atom compilers and
  forces shared infrastructure
  (`URMRaw.preservingTransfer`,
  `URMRaw.transferLoop`, the three loop-correctness
  theorems) into a separate core file.
- *Pure layer-by-layer* (compiler, embedding,
  loop-correctness, correctness) collapses Sections D
  (atom correctness) and E (comp correctness) into one
  ~7000-LOC `Correctness.lean`, deferring the size problem
  rather than solving it before bsum lands.

The hybrid approach keeps compilation tight in one file
(`compileERFrag` reads end-to-end), keeps shared loop
correctness tight in another, and isolates per-constructor
correctness so each can grow independently.

## 3 Module map

```text
GebLean/LawvereERKSim.lean              pure index, ~50 LOC
GebLean/LawvereERKSim/
├── Compiler.lean    ~1450 LOC          Section A
├── Embedding.lean    ~770 LOC          Section B + Section F bridge
├── Loops.lean       ~2500 LOC          Section C
├── Atoms.lean       ~2000 LOC          Section D
└── Comp.lean        ~3500 LOC          Section E + comp runFor wrapper
```

Future submodules (out of scope here; placed during their
own work):

```text
GebLean/LawvereERKSim/
├── BSum.lean        ~3000–4000 LOC     Task 11f
├── BProd.lean       ~3000–4000 LOC     Task 11g
└── Top.lean          ~100 LOC          Task 11h structural induction
```

Section letters refer to the survey in §4 below.

### 3.1 Dependency DAG

```text
Compiler ─→ Embedding ─→ Loops ─→ Atoms
                  │             └→ Comp
                  └─────────────────↑
```

`Comp` and `Atoms` both import `Embedding` and `Loops`.
`Embedding` imports `Compiler`. `Loops` imports `Embedding`
(it uses `step_of_getElem?_*` and PC-bound predicates).
The index `GebLean/LawvereERKSim.lean` imports the leaves
(`Atoms`, `Comp`), pulling in the rest transitively.

No cyclic dependencies are introduced; each submodule is
self-contained at the namespace level (nested
`namespace GebLean` then `namespace LawvereERKSim`).

## 4 Survey: line ranges in the current monolith

Line numbers refer to commit `a1ff2ff7`
(`GebLean/LawvereERKSim.lean`, 11,943 lines).

| Section | Line range | LOC | Contents |
| --- | --- | --- | --- |
| A | 1–1473 | ~1450 | `URMInstrRaw`, `boundedBy`, `toBounded`, `toBoundedArray`, `CompiledFragment`, `URMRaw.{goto,transferLoop,preservingTransfer}`, `compileFrag_{zero,succ,proj,sub,comp,bsum,bprod}`, `compileERFrag`, `compileER`, `compileER_runtime` |
| B | 1474–2137 | ~700 | `step_of_getElem?_{jumpZ,dec,inc,assign,stop}`, `ProgramEmbedsFragment`, `StateEmbedsFrag`, `stateEmbedsFrag_{step,runFor}` and `_tail`/`_outside_preserved` variants, `URMProgram.WellBounded`, `runFor_pc_le_size`, `compileER_runFor_pc_le_size`, `fragment_runFor_pc_le_size` |
| C | 2956–4915, 5414–5853 | ~2500 | `preservingTransfer_correct` and its `_loop1`/`_loop2` helpers; `transferLoop_correct`; `subInnerLoop_correct`; per-step and strict PC bounds for all three |
| D | 4917–5853, 6199–8023 | ~2000 | `compileER_runFor_{zero,succ,proj,sub}`; atom pre-stop lemmas `compileER_pre_stop_correct_{zero,succ,proj,sub}`; `List.find?_finRange_inputRegs`, `URMState.init_regs_inputRegs` |
| E | 2138–2955, 5854–6198, 6321–7208, 8024–11820 | ~5000 | Length lemmas (`compileFrag_comp_subBlock_length`, `subBlocks_length`, `foldr_acc_add_eq_sum_map`); f-body and gs-body embedding setup; `compileFrag_comp_subBlock_{inputCopies,gsBody,outputTransfer}_correct` and strict PC bounds; `compileER_runFor_comp_k_zero`; `vPrefixSum`, `inputCopies_disj`, `disj_triple_for_reg`; `compileFrag_comp_partial_invariant` 8-clause structure; `compileFrag_comp_phase_i{1,2}_post`; `compileFrag_comp_subBlocks_partial_{base,phase_i1,phase_i2,phase_i3,step,aux,partial}`; outer iteration; `compileER_pre_stop_correct_comp`; `vPrefixSum_eq_foldl_finRange` and `_aux`; `compileER_runFor_comp` (general k) |
| F | 11821–11940 | ~120 | `compileER_pre_stop_to_runFor` (the constructor-agnostic bridge); also placed in `Embedding.lean`, since the comp-specific wrapper `compileER_runFor_comp` rides into `Comp.lean` |

Section line numbers reflect the *origin* of declarations.
Some sections are non-contiguous in the monolith because
later additions (atom pre-stop, comp m-step machinery)
landed after the loop-correctness work; the split
recontiguates each section's content into its target
submodule.

## 5 Per-submodule contents

### 5.1 `Compiler.lean` (Section A)

```text
-- Imports
import GebLean.LawvereER
import GebLean.Utilities.ZeroTestURM
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

namespace GebLean
namespace LawvereERKSim
```

Declarations, in source order: `URMInstrRaw`,
`URMInstrRaw.maxReg`, `URMInstrRaw.toBounded`,
`URMInstrRaw.toBounded_congr`,
`URMInstrRaw.boundedBy`, `URMInstrRaw.toBoundedArray`,
`URMInstrRaw.lastInstr_isStop_of_concat`,
`URMInstrRaw.toBoundedArray_size`,
`URMInstrRaw.toBoundedArray_getElem`,
`URMInstrRaw.toBoundedArray_getElem?`,
`CompiledFragment` structure (with `numRegs_pos`,
`zeroReg_not_input`, `zeroReg_not_output`,
`lastInstr_isStop`), `CompiledFragment.zeroReg`,
`URMRaw.goto`, `URMRaw.transferLoop`,
`URMRaw.transferLoop.size`,
`URMRaw.preservingTransfer`,
`URMRaw.preservingTransfer.size`,
`compileFrag_zero`, `compileFrag_succ`,
`compileFrag_proj`, `compileFrag_sub_inputRegs`,
`compileFrag_sub_inputRegs_zero`,
`compileFrag_sub_inputRegs_one`,
`compileFrag_sub`,
`URMInstr.toRawOfBounded`,
`URMInstrRaw.reindexShift`,
`gsPrefixSum`, `gsBlockSize`, `gsPrefixSum_mono`,
`URMInstrRaw.preservingTransfer.reindexShift_bounded`,
`URMInstrRaw.transferLoop.reindexShift_bounded`,
`URMInstrRaw.reindexShift_bounded`,
`compileFrag_comp_subBlock`,
`compileFrag_comp_subBlock_bounded`,
`compileFrag_comp`,
`bsum_prologueSrc`,
`bsum_prologueBlock`,
`bsum_prologueBlock_bounded`,
`bsum_zeroSweep`,
`bsum_zeroSweep_bounded`,
`compileFrag_bsum`,
`compileFrag_bprod`,
`compileERFrag`,
`compileER`,
`compileER_numRegs_bound`,
`compileER_runtime`.

Visibility: declarations that the monolith marks
`private` and that no other section references stay
`private`. Declarations marked `private` that *are*
referenced from `Embedding.lean`, `Loops.lean`,
`Atoms.lean`, or `Comp.lean` are promoted to non-`private`
during the move (audited per-declaration in the plan; the
spec lists no such cases pre-emptively because Lean's
elaborator will surface them as build failures during the
split).

### 5.2 `Embedding.lean` (Section B + the bridge from Section F)

```text
import GebLean.LawvereERKSim.Compiler
```

Declarations:
`URMState.runFor_halted_invariant`,
`URMState.runFor_stop`,
`getElem_of_getElem?`,
`step_of_getElem?_jumpZ`,
`step_of_getElem?_dec`,
`step_of_getElem?_inc`,
`step_of_getElem?_assign`,
`step_of_getElem?_stop`,
`ProgramEmbedsFragment`,
`StateEmbedsFrag`,
`stateEmbedsFrag_step`,
`stateEmbedsFrag_step_tail`,
`stateEmbedsFrag_runFor`,
`stateEmbedsFrag_runFor_tail`,
`stateEmbedsFrag_step_outside_preserved`,
`stateEmbedsFrag_runFor_outside_preserved`,
`URMProgram.WellBounded`,
`URMProgram.WellBounded.runFor_pc_le_size`,
`compileER_runFor_pc_le_size`,
`fragment_runFor_pc_le_size`,
`compileER_pre_stop_to_runFor` (the bridge — placed here
because it depends only on `Compiler.lean` and
`URMState.runFor_{add,stop}`).

### 5.3 `Loops.lean` (Section C)

```text
import GebLean.LawvereERKSim.Embedding
```

Declarations:
`preservingTransferInstrs`,
`preservingTransfer_loop1`,
`preservingTransfer_loop1_pc_bound`,
`preservingTransfer_loop2`,
`preservingTransfer_loop2_pc_bound`,
`preservingTransfer_loop2_pc_strict_bound`,
`preservingTransfer_hyps`,
`preservingTransfer_correct`,
`preservingTransfer_correct_pc_bound`,
`preservingTransfer_correct_pc_strict_bound`,
`transferLoop_hyps`,
`transferLoop_correct`,
`transferLoop_correct_pc_bound`,
`transferLoop_correct_pc_strict_bound`,
`subInnerLoop_hyps`,
`subInnerLoop_correct`,
`subInnerLoop_correct_pc_bound`,
`subInnerLoop_correct_pc_strict_bound`.

The three "correct" theorems and their PC-bound siblings
group together; per-loop helpers (`_loop1`/`_loop2` for
`preservingTransfer`) stay adjacent to the loop they
support.

### 5.4 `Atoms.lean` (Section D)

```text
import GebLean.LawvereERKSim.Loops
```

Declarations, grouped per constructor:

- `compileER_runFor_zero`.
- `compileER_runFor_succ`.
- `List.find?_finRange_inputRegs`,
  `URMState.init_regs_inputRegs`,
  `compileER_runFor_proj`.
- `compileER_runFor_sub`.
- `compileER_pre_stop_correct_atom_zero`.
- `compileER_pre_stop_correct_succ`.
- `compileER_pre_stop_correct_proj`.
- `compileER_pre_stop_correct_sub`.

The `_runFor_*` lemmas precede the `_pre_stop_correct_*`
lemmas because the latter were added later in the
monolith; preserving that order avoids reshuffling proof
context.

### 5.5 `Comp.lean` (Section E + Section F's comp wrapper)

```text
import GebLean.LawvereERKSim.Loops
```

Declarations, in monolith order:

Length / embedding lemmas:
`compileFrag_comp_subBlock_length`,
`compileFrag_comp_subBlocks_length`,
`foldr_acc_add_eq_sum_map`,
`flatMap_finRange_split`,
`URMState.init_regs_zero_outside_inputs`,
`ProgramEmbedsFragment_compileFrag_comp_fBody`,
`ProgramEmbedsFragment_compileFrag_comp_gsBody`.

Sub-block phase lemmas:
`compileFrag_comp_subBlock_inputCopies_correct`,
`compileFrag_comp_subBlock_gsBody_correct`,
`compileFrag_comp_subBlock_outputTransfer_correct`,
`vPrefixSum`,
`vPrefixSum_succ`,
`inputCopies_disj`,
`disj_triple_for_reg`,
`compileFrag_comp_subBlock_inputCopies_pc_strict_bound`,
`compileFrag_comp_subBlock_gsBody_pc_strict_bound`,
`compileFrag_comp_subBlock_outputTransfer_pc_strict_bound`.

k=0 case wrapper:
`compileER_runFor_comp_k_zero`.

m-step partial invariant:
`compileFrag_comp_partial_invariant`,
`compileFrag_comp_pcOf`,
`compileFrag_comp_pcOf_zero`,
`compileFrag_comp_pcOf_succ`,
`compileFrag_comp_subBlocks_partial_base`,
`compileFrag_comp_phase_i1_post`,
`compileFrag_comp_subBlocks_partial_phase_i1`,
`compileFrag_comp_subBlocks_partial_phase_i1_pc_strict_bound`,
`compileFrag_comp_phase_i2_post`,
`compileFrag_comp_subBlocks_partial_phase_i2`,
`compileFrag_comp_subBlocks_partial_phase_i3`,
`compileFrag_comp_subBlocks_partial_step`.

Outer iteration and assembly:
`compileFrag_comp_finRange_filter_lt_succ`,
`compileFrag_comp_subBlocks_partial_aux`,
`compileFrag_comp_subBlocks_partial`,
`vPrefixSum_eq_foldl_finRange_aux`,
`vPrefixSum_eq_foldl_finRange`,
`compileER_pre_stop_correct_comp`,
`compileER_runFor_comp` (general k wrapper, via the
bridge in `Embedding.lean`).

### 5.6 `GebLean/LawvereERKSim.lean` (index)

```text
import GebLean.LawvereERKSim.Atoms
import GebLean.LawvereERKSim.Comp

/-!
# LawvereERKSim index

Re-exports of the ER → URM compiler and its correctness
infrastructure. Submodules:

- `Compiler`: raw and bounded instructions, fragment
  emission for each ER constructor, top-level `compileER`
  and `compileER_runtime`.
- `Embedding`: step lemmas, the program-embedding
  framework, well-boundedness, and the constructor-agnostic
  `compileER_pre_stop_to_runFor` bridge.
- `Loops`: correctness of `transferLoop`,
  `preservingTransfer`, and `subInnerLoop`.
- `Atoms`: per-constructor correctness for `zero`, `succ`,
  `proj`, `sub` (both `_runFor_*` and `_pre_stop_correct_*`
  forms).
- `Comp`: comp m-step machinery, outer iteration, final
  pre-stop assembly, and the comp runFor wrapper.

Future submodules `BSum`, `BProd`, and `Top` follow once
Tasks 11f, 11g, 11h land.
-/
```

The index file is import-only; it contains no `namespace`,
no declarations, and no proofs. This matches the existing
`GebLean/PLang.lean` and `GebLean/Utilities.lean` patterns.

## 6 Mechanical procedure

The split is performed in this order:

1. Create the directory `GebLean/LawvereERKSim/`.
2. Create `Compiler.lean`: write header (imports +
   docstring + namespaces), then move all Section A
   declarations from the monolith. Move means: cut from
   the monolith, paste into the new file. Do not edit
   declarations.
3. `lake build GebLean.LawvereERKSim.Compiler`.
4. Create `Embedding.lean`: write header, move Section B
   declarations plus the bridge from Section F.
5. `lake build GebLean.LawvereERKSim.Embedding`.
6. Create `Loops.lean`: write header, move Section C
   declarations.
7. `lake build GebLean.LawvereERKSim.Loops`.
8. Create `Atoms.lean`: write header, move Section D
   declarations.
9. `lake build GebLean.LawvereERKSim.Atoms`.
10. Create `Comp.lean`: write header, move Section E
    declarations plus the `compileER_runFor_comp` wrapper
    from Section F.
11. `lake build GebLean.LawvereERKSim.Comp`.
12. Replace the monolithic `GebLean/LawvereERKSim.lean`
    with the index file (import-only).
13. `lake build` (whole tree).
14. Run `scripts/check-axioms.sh` over the new submodules.
15. Per-declaration axiom check via
    `mcp__lean-lsp__lean_verify` on a sampled set of
    flagship declarations from each new submodule.

The order is chosen so each step lands a self-contained
build target, isolating fix-up effort. Steps 3, 5, 7, 9,
11 may surface `private`-promotion needs or
`open`/`variable` scoping adjustments; those are fixed in
the same commit that introduces the submodule.

### 6.1 Visibility adjustments

The monolith uses `private` on internal helpers. The split
preserves `private` wherever a `private` declaration is
referenced only within its target submodule. Where a
`private` declaration is referenced across the new file
boundary, two options:

(a) Promote to non-`private` (drop the modifier).

(b) Duplicate the declaration in each consumer file.

Option (a) is preferred unless the declaration is purely
proof-internal scaffolding that would clutter the
submodule's public surface. Plan-time enumeration of
affected declarations is impractical without running the
build; the implementation plan instead specifies the
discharge mechanism (Option (a) by default; reviewer flags
any non-trivial case).

### 6.2 Sectional comments

The monolith contains four `/-! ### …` sub-section
headings:

```text
Line 1551: ### Program-embedding lemmas
Line 2084: ### PC-in-range for `compileER` outputs
Line 2138: ### Length lemmas for `compileFrag_comp`
Line 8024: ### Comp m-step partial invariant
```

Each `###`-level comment moves with its surrounding
declarations into the appropriate submodule. All four stay
at `###` because each submodule has a single section.

### 6.3 Module docstrings

Each new submodule gets a `/-! … -/` module docstring
under its imports with the required sections per
`.claude/rules/lean-coding.md` § Documentation: title,
brief summary, `## Main definitions`, `## Main statements`,
`## Implementation notes` (if any), `## References` (if
any), `## Tags` (omit if empty). The references section
points back at the relevant Tourlakis sub-section
(§0.1.0.37 et seq.) and at this design document via a
repo-relative path.

The monolith's existing module docstring (lines 5–75) is
trimmed to belong to the index file: the index docstring
carries the top-level summary plus the submodule
overview from §5.6 above. Per-submodule docstrings carry
the structural and reference content that matches each
submodule's contents.

## 7 Verification

After step 13 (whole-tree build):

- Whole-tree `lake build` succeeds.
- `lake test` passes (no test references the monolith
  directly; `GebLean.LawvereERKSim` resolves to the new
  index).
- `scripts/check-axioms.sh` reports clean
  (`[propext, Quot.sound]` only) for each new submodule.
- For a sampled set of flagship declarations
  (`compileER_pre_stop_correct_comp`,
  `compileER_runFor_comp`,
  `compileER_pre_stop_to_runFor`,
  `compileER_runFor_zero/succ/proj/sub`,
  `transferLoop_correct`,
  `preservingTransfer_correct`,
  `subInnerLoop_correct`), `mcp__lean-lsp__lean_verify`
  reports axioms `[propext, Quot.sound]` only.
- `markdownlint-cli2` clean on this spec and any plan
  written from it.

## 8 Risks and mitigations

| Risk | Mitigation |
| --- | --- |
| Cross-file `private` promotion cascades | Per-step builds (procedure §6 steps 3, 5, 7, 9, 11) localise the cascade to one submodule at a time. |
| Declaration order shifts break `omega`-by-`rfl` bridges (the project-memory pattern about `set` vs `let`) | The split preserves declaration order within each submodule; the only reordering is sectional re-contiguation. Implementer reviews each submodule against the monolith with `diff` after the move. |
| `open`/`variable` blocks scoped to the monolith file lose context across submodules | Plan-time audit; explicit re-`variable`-declaration per submodule where used. |
| Build-time degradation from import fan-out | Submodule sizes are bounded ≤ 3500 LOC; cumulative cost stays below monolithic compile time. |
| Module docstring redistribution loses references | Each submodule docstring carries the references it transitively uses. |

## 9 Out of scope

- Followup-branch items #1–8 from the T2 Task 11 handoff
  (renaming `gsPrefixSum_mono` binders, extracting
  `fin_pack` helpers, replacing inline filter-snoc blocks,
  comp.3.b cleanups, `compileFrag_comp_size`/`pcOf_top`
  extraction). Each is its own followup commit, executed
  after this split lands.
- bsum and bprod pre-stop proofs (Tasks 11e.6.a.iii-bsum
  and -bprod).
- Tasks 11f, 11g (bsum/bprod runFor wrappers).
- Task 11h (top-level structural induction).
- Task 12 (axiom audit + manual lint).
- New mathematical content of any kind.

## 10 References

- Project rule: nested narrow-and-deep directories with
  one indexing file per directory (`CLAUDE.md`
  § "Repo structure (one-line)").
- Existing patterns: `GebLean/PLang.lean`,
  `GebLean/Utilities.lean` (pure-import index files);
  `GebLean/PLang/`, `GebLean/Utilities/` (submodule
  directories).
- Handoff context: `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`
  § "Followup branch (post-T2)", item 9.
- Lean coding rules: `.claude/rules/lean-coding.md`
  § "Lean 4 module system", § "Documentation".
- Markdown rules: `.claude/rules/markdown-writing.md`.
