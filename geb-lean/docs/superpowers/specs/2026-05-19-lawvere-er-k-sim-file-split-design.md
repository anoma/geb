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
  - [5.2 `Embedding.lean` (Section B parts + the bridge)](#52-embeddinglean-section-b-parts--the-bridge)
  - [5.3 `Loops.lean` (Section C parts)](#53-loopslean-section-c-parts)
  - [5.4 `Atoms.lean` (Section D parts)](#54-atomslean-section-d-parts)
  - [5.5 `Comp.lean` (Section E parts + the comp runFor wrapper)](#55-complean-section-e-parts--the-comp-runfor-wrapper)
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
├── Compiler.lean    ~1400 LOC          Section A
├── Embedding.lean    ~800 LOC          Section B + tail variants + bridge
├── Loops.lean       ~2750 LOC          Section C + non-contiguous PC bounds
├── Atoms.lean       ~2000 LOC          Section D
└── Comp.lean        ~5000 LOC          Section E + comp runFor wrapper
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
(`GebLean/LawvereERKSim.lean`, 11,943 lines). Sub-ranges
within a section are *non-contiguous* — they are
intermixed in the monolith because later proof work was
appended after earlier work. The split recontiguates each
section's content into its target submodule.

| Submodule | Source sub-ranges | Approx LOC |
| --- | --- | --- |
| Compiler.lean | 76–1473 | ~1400 |
| Embedding.lean | 1474–2137, 5201–5232, 5854–5932, 11821–11895 | ~800 |
| Loops.lean | 2956–4916, 5414–5654, 6321–6602 | ~2750 |
| Atoms.lean | 4917–5200, 5233–5413, 5655–5853, 6199–6320, 7209–8023 | ~2000 |
| Comp.lean | 2138–2955, 5933–6198, 6603–7208, 8024–11820, 11896–11940 | ~5000 |

Each sub-range start equals the line of the leading
`/--` of the first declaration in the sub-range (so the
docstring travels with the declaration). Each sub-range
end equals the line just before the next sub-range or
section's leading `/--` (typically a blank line).

Notable non-contiguities:

- `stateEmbedsFrag_step_tail` (5866) and
  `stateEmbedsFrag_runFor_tail` (5903) sit between the
  proj-runFor block and the comp-k=0 wrapper but belong
  with the rest of `stateEmbedsFrag_*` lemmas in
  Embedding.lean.
- `URMState.init_regs_zero_outside_inputs` (5210) sits
  among the proj helpers but is used by comp; belongs in
  Embedding.lean.
- Four loop strict-PC-bound theorems sit at 6321–6606
  (post atom-pre-stop work) but belong with their
  corresponding loop correctness theorems in Loops.lean:
  `preservingTransfer_loop2_pc_strict_bound` (6326),
  `preservingTransfer_correct_pc_strict_bound` (6423),
  `subInnerLoop_correct_pc_strict_bound` (6463),
  `preservingTransfer_correct_pc_bound` (6561).
- Two `compileFrag_comp`-specific instruction-presence
  dischargers sit *inside* the loops-correctness range
  but operate on `compileFrag_comp_subBlock`'s layout:
  `PreservingTransferInstrs_compileFrag_comp_inputCopies`
  (2990–3564) and
  `TransferLoopInstrs_compileFrag_comp_outputTransfer`
  (4187–4593). They consume the `preservingTransferInstrs`
  and `transferLoopInstrs` private structures defined in
  Loops; they stay in Loops.lean so those structures
  remain file-private (see §5.3).

The monolith carries one significant directive at the
file level: `open GebLean.ZeroTestURM` on line 80. Every
submodule must include this `open` clause after its
namespace declarations.

## 5 Per-submodule contents

Each declaration list below is empirically verified
against the monolith at commit `a1ff2ff7`. Names exactly
match the monolith's `theorem` / `def` / `structure`
identifiers.

### 5.1 `Compiler.lean` (Section A)

Imports and header (in this order):

```lean
import GebLean.LawvereER
import GebLean.Utilities.ZeroTestURM
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! module docstring -/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM
```

Declarations, in source order (line numbers attached):

- `URMInstrRaw` (92, inductive).
- `URMInstrRaw.regBound` (110, def).
- `URMInstrRaw.toBounded` (121, def).
- `URMInstrRaw.toBounded_congr` (136, private theorem).
- `URMInstrRaw.boundedBy` (144, def).
- `URMInstrRaw.toBoundedArray` (152, def).
- `URMInstrRaw.toBoundedArray_back?_of_last_stopR` (162,
  private theorem).
- `URMInstrRaw.toBoundedArray_size` (177, private theorem).
- `URMInstrRaw.toBoundedArray_getElem` (186, private theorem).
- `URMInstrRaw.toBoundedArray_getElem?` (202, private theorem).
- `CompiledFragment` (structure, ~lines 213–245, with fields
  `numRegs_pos`, `zeroReg_not_input`, `zeroReg_not_output`,
  `lastInstr_isStop`).
- `CompiledFragment.zeroReg` (247, def).
- `URMRaw.goto` (257, def).
- `URMRaw.transferLoop` (270, def).
- `URMRaw.transferLoopLen` (279, def).
- `URMRaw.preservingTransfer` (286, def).
- `URMRaw.preservingTransferLen` (304, def).
- `compileFrag_zero` (310, def).
- `compileFrag_succ` (335, def).
- `compileFrag_proj` (370, def).
- `compileFrag_sub_inputRegs` (423, def).
- `compileFrag_sub` (439, def).
- `toRawOfBounded` (501, def).
- `regBound_toRawOfBounded_le` (512, theorem).
- `URMInstrRaw.reindexShift` (525, def).
- `gsPrefixSum` (537, private def).
- `gsPrefixSum_succ_eq` (547, private theorem).
- `gsPrefixSum_mono` (557, private theorem).
- `boundedBy_preservingTransfer` (572, theorem).
- `boundedBy_transferLoop` (585, theorem).
- `regBound_reindexShift_le_offset_add` (597, theorem).
- `compileFrag_comp_subBlock` (613, private def).
- `boundedBy_compileFrag_comp_subBlock` (642, private theorem).
- `compileFrag_comp` (702, def).
- `bsum_prologueSrc` (834, private def).
- `bsum_prologueBlock` (849, private def).
- `boundedBy_bsum_prologueBlock` (864, private theorem).
- `bsum_zeroSweep` (884, private def).
- `boundedBy_bsum_zeroSweep` (893, private theorem).
- `compileFrag_bsum` (914, def).
- `compileFrag_bprod` (1127, def).
- `compileERFrag` (1382, def).
- `compileER` (1399, def).
- `compileER_numRegs` (1407, def).
- `compileER_runtime` (1427, def).

### 5.2 `Embedding.lean` (Section B parts + the bridge)

Imports:

```lean
import GebLean.LawvereERKSim.Compiler
```

Plus `open GebLean.ZeroTestURM` after the namespace
declarations.

Declarations (with monolith line numbers; all are
`private theorem` unless noted):

- `getElem_of_getElem?_some` (1478).
- `URMState.step_of_getElem?_jumpZ` (1493).
- `URMState.step_of_getElem?_dec` (1504).
- `URMState.step_of_getElem?_inc` (1515).
- `URMState.step_of_getElem?_assign` (1529).
- `URMState.step_of_getElem?_stop` (1543).
- `ProgramEmbedsFragment` (1573, private structure).
- `StateEmbedsFrag` (1594, private def).
- `stateEmbedsFrag_step` (1609).
- `stateEmbedsFrag_runFor` (1861).
- `stateEmbedsFrag_step_outside_preserved` (1897).
- `stateEmbedsFrag_runFor_outside_preserved` (2039).
- `compileER_runFor_pc_le_size` (2109).
- `fragment_runFor_pc_le_size` (2130).
- `URMState.init_regs_zero_outside_inputs` (5210, moved
  from the Section D proj-helpers cluster because the
  Comp-side phase-i.1 work uses it).
- `stateEmbedsFrag_step_tail` (5866, moved from the
  middle of the monolith).
- `stateEmbedsFrag_runFor_tail` (5903, moved similarly).
- `compileER_pre_stop_to_runFor` (11830, the
  constructor-agnostic bridge from the existential
  pre-stop form to the output-only `≤ t'` form).

The bridge depends on `URMState.runFor_add`,
`URMState.runFor_stop`, and
`CompiledFragment.lastInstr_isStop`. The first two are
upstream declarations in
`GebLean/Utilities/ZeroTestURM.lean`; the third is in
`Compiler.lean`. No new transitive imports are required.

### 5.3 `Loops.lean` (Section C parts)

Imports:

```lean
import GebLean.LawvereERKSim.Embedding
```

Plus `open GebLean.ZeroTestURM`.

Declarations (with monolith line numbers):

- `preservingTransferInstrs` (2962, private structure).
- `PreservingTransferInstrs_compileFrag_comp_inputCopies`
  (2990, private theorem).
- `preservingTransfer_loop1` (3565, private theorem).
- `preservingTransfer_loop1_pc_bound` (3741, private theorem).
- `preservingTransfer_loop2` (3872, private theorem).
- `preservingTransfer_loop2_pc_bound` (3983, private theorem).
- `preservingTransfer_correct` (4107, private theorem).
- `transferLoopInstrs` (4164, private structure).
- `TransferLoopInstrs_compileFrag_comp_outputTransfer`
  (4187, private theorem).
- `transferLoop_correct` (4594, private theorem).
- `transferLoop_correct_pc_bound` (4714, private theorem).
- `transferLoop_correct_pc_strict_bound` (4824, private theorem).
- `subInnerLoopInstrs` (5419, private structure).
- `subInnerLoop_correct` (5436, private theorem).
- `subInnerLoop_correct_pc_bound` (5554, private theorem).
- `preservingTransfer_loop2_pc_strict_bound` (6326,
  private theorem, moved from the post-atom-pre-stop
  cluster).
- `preservingTransfer_correct_pc_strict_bound` (6423,
  same).
- `subInnerLoop_correct_pc_strict_bound` (6463, same).
- `preservingTransfer_correct_pc_bound` (6561, same).

The two `compileFrag_comp`-specific dischargers
(`PreservingTransferInstrs_compileFrag_comp_inputCopies`,
`TransferLoopInstrs_compileFrag_comp_outputTransfer`)
stay in this submodule because they consume the
`preservingTransferInstrs` and `transferLoopInstrs`
private structures defined here. Moving the dischargers
to `Comp.lean` would require promoting those structures
to non-`private`, weakening encapsulation for no
semantic gain. The Loops submodule therefore hosts both
loop correctness theorems and the per-comp-layout
instruction-presence dischargers; this is acknowledged
in the module docstring.

### 5.4 `Atoms.lean` (Section D parts)

Imports:

```lean
import GebLean.LawvereERKSim.Loops
```

Plus `open GebLean.ZeroTestURM`.

Declarations (all `private theorem` with monolith line
numbers; the four pre-stop lemmas use the `_atom_` infix
per the monolith's actual naming):

- `compileER_runFor_zero` (4919).
- `compileER_runFor_succ` (5012).
- `List.find?_finRange_inputRegs` (5157).
- `URMState.init_regs_inputRegs` (5191).
- `compileER_runFor_proj` (5239).
- `compileER_runFor_sub` (5663).
- `compileER_pre_stop_correct_atom_zero` (6208).
- `compileER_pre_stop_correct_atom_succ` (7215).
- `compileER_pre_stop_correct_atom_proj` (7456).
- `compileER_pre_stop_correct_atom_sub` (7684).

The proj helpers `List.find?_finRange_inputRegs` and
`URMState.init_regs_inputRegs` are used only by
`compileER_runFor_proj` and stay file-local to Atoms.

### 5.5 `Comp.lean` (Section E parts + the comp runFor wrapper)

Imports:

```lean
import GebLean.LawvereERKSim.Loops
```

Plus `open GebLean.ZeroTestURM`.

Declarations, grouped, with monolith line numbers (all
`private` unless noted):

Length / embedding setup:

- `compileFrag_comp_subBlock_length` (2145, theorem).
- `foldr_acc_add_eq_sum_map` (2183, theorem).
- `compileFrag_comp_subBlocks_length` (2196, theorem).
- `ProgramEmbedsFragment_compileFrag_comp_fBody` (2225,
  theorem).
- `flatMap_finRange_split` (2425, theorem).
- `ProgramEmbedsFragment_compileFrag_comp_gsBody` (2536,
  theorem).

k=0 wrapper:

- `compileER_runFor_comp_k_zero` (5946, theorem).

Sub-block phase correctness:

- `vPrefixSum` (6607, def).
- `vPrefixSum_succ` (6614, theorem).
- `inputCopies_disj` (6627, structure).
- `inputCopies_prefix_correct` (6653, theorem).
- `inputCopies_prefix_pc_strict_bound` (6785, theorem).
- `compileFrag_comp_subBlock_inputCopies_correct` (6878,
  theorem).
- `compileFrag_comp_subBlock_inputCopies_pc_strict_bound`
  (6914, theorem).
- `compileFrag_comp_subBlock_gsBody_correct` (6949,
  theorem). (No `gsBody_pc_strict_bound` exists in the
  monolith; the gsBody case derives its strict PC bound
  from the structural IH on `gs m`.)
- `compileFrag_comp_subBlock_outputTransfer_correct`
  (7160, theorem).
- `compileFrag_comp_subBlock_outputTransfer_pc_strict_bound`
  (7191, theorem).

m-step partial invariant and induction:

- `compileFrag_comp_pcOf` (8038, def).
- `compileFrag_comp_pcOf_zero` (8047, theorem).
- `compileFrag_comp_pcOf_succ` (8070, theorem).
- `compileFrag_comp_partial_invariant` (8237, structure).
- `compileFrag_comp_subBlocks_partial_base` (8358,
  theorem).
- `compileFrag_comp_phase_i1_post` (8533, structure).
- `compileFrag_comp_subBlocks_partial_phase_i1` (8689,
  theorem).
- `compileFrag_comp_phase_i2_post` (9267, structure).
- `compileFrag_comp_subBlocks_partial_phase_i2` (9402,
  theorem).
- `compileFrag_comp_subBlocks_partial_phase_i3` (9958,
  theorem).
- `compileFrag_comp_subBlocks_partial_phase_i1_pc_strict_bound`
  (10587, theorem).
- `compileFrag_comp_subBlocks_partial_step` (10772,
  theorem).

Outer iteration and assembly:

- `compileFrag_comp_finRange_filter_lt_succ` (10913,
  theorem).
- `compileFrag_comp_subBlocks_partial_aux` (11030,
  theorem).
- `compileFrag_comp_subBlocks_partial` (11185, theorem).
- `vPrefixSum_eq_foldl_finRange_aux` (11244, theorem).
- `vPrefixSum_eq_foldl_finRange` (11288, theorem).
- `compileER_pre_stop_correct_comp` (11339, theorem).
- `compileER_runFor_comp` (11901, theorem; general-k
  `≤ t'` wrapper; composes
  `compileER_pre_stop_correct_comp` with the bridge
  `compileER_pre_stop_to_runFor` from Embedding).

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
