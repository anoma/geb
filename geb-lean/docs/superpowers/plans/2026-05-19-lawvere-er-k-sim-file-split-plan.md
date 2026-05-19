# LawvereERKSim file split — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Conventions used by every move task](#conventions-used-by-every-move-task)
- [Task 1: Create directory and verify monolith baseline](#task-1-create-directory-and-verify-monolith-baseline)
- [Task 2: Create `Compiler.lean` (Section A move)](#task-2-create-compilerlean-section-a-move)
- [Task 3: Create `Embedding.lean` (Section B parts + bridge)](#task-3-create-embeddinglean-section-b-parts--bridge)
- [Task 4: Create `Loops.lean` (Section C parts)](#task-4-create-loopslean-section-c-parts)
- [Task 5: Create `Atoms.lean` (Section D parts)](#task-5-create-atomslean-section-d-parts)
- [Task 6: Create `Comp.lean` (Section E parts + comp runFor wrapper)](#task-6-create-complean-section-e-parts--comp-runfor-wrapper)
- [Task 7: Replace monolith with pure-import index](#task-7-replace-monolith-with-pure-import-index)
- [Task 8: Final verification and documentation](#task-8-final-verification-and-documentation)
- [Self-review against the spec](#self-review-against-the-spec)

<!-- END doctoc -->

**Goal.** Split the 11,943-line
`GebLean/LawvereERKSim.lean` into a pure-import index file
and five topical submodules under
`GebLean/LawvereERKSim/`, preserving every lemma
signature, proof tactic, docstring, and axiom-hygiene
profile.

**Architecture.** Layered compilation
(`Compiler.lean`), embedding/runtime plus the
constructor-agnostic pre-stop-to-runFor bridge
(`Embedding.lean`), shared loop-correctness theorems
(`Loops.lean`), per-constructor correctness for the atoms
(`Atoms.lean`), and the comp m-step machinery plus final
comp assembly (`Comp.lean`). Dependency DAG:
`Compiler → Embedding → Loops → {Atoms, Comp}`. Index
file `GebLean/LawvereERKSim.lean` re-exports the leaves.

**Tech stack.** Lean 4, mathlib, lake build system, jj for
VCS, `mcp__lean-lsp__lean_verify` for per-declaration axiom
audit, `scripts/check-axioms.sh` for batch axiom audit,
`markdownlint-cli2` for `.md` files, `doctoc` for TOCs.

**Spec.**
[`docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`](../specs/2026-05-19-lawvere-er-k-sim-file-split-design.md)

---

## Conventions used by every move task

Each move task follows the same shape:

1. Read the source line range from the monolith.
2. Write the target submodule with header (imports +
   docstring + namespaces) and the moved content.
3. Delete the moved range from the monolith; insert
   `import GebLean.LawvereERKSim.<Submodule>` at the
   top of the monolith.
4. Run `lake build` to surface any cross-file
   `private`-promotion needs, `open`/`variable` scoping
   gaps, or namespace adjustments.
5. Fix any surfaced errors in-place (per the spec §6.1
   policy: promote `private` declarations by default).
6. `lake build` again to confirm clean.
7. `mcp__lean-lsp__lean_verify` on the flagship
   declarations listed for that submodule.
8. Commit.

The submodule header template is:

```lean
-- imports (submodule-specific; see each task)

/-!
# <Submodule title>

<one-paragraph summary>

## Main definitions

<list>

## Main statements

<list>

## Implementation notes

<list, if any>

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` § …
- Spec: `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM
```

The `open GebLean.ZeroTestURM` directive is *required* in
every submodule: it lives at monolith line 80 and brings
`URMProgram`, `URMState`, `URMInstr`, `runFor`, etc. into
scope unqualified. Without it, every submodule will fail
to build with thousands of "unknown identifier" errors.

Submodule-specific imports are listed in each task. The
namespace block stays the same across submodules; closing
`end LawvereERKSim` and `end GebLean` go at the bottom of
each file.

`private` declarations referenced across the new file
boundary are promoted to non-`private` by default during
the move (spec §6.1). The non-negotiable interfaces rule
applies: lemma signatures stay identical; tactics stay
identical; the only edits are visibility-modifier removal
and per-submodule re-`open`.

`lake build` should never use `lake clean` (project rule:
forces full mathlib rebuild). Use `lake build` only. The
project uses `lake build <module-path>` for narrow
isolation builds; this is verified during Task 1 Step 5.

Each task lands as a single jj working-copy commit. Do
not run `jj new` between steps within a task. The
end-of-task `jj describe` names the accumulated commit;
`jj new` advances to a fresh working copy for the next
task.

All `jj` operations in this plan are local-only; no
`jj git push`. The pre-tool-use hook for mutating git
operations may prompt; surface to user if needed.

---

## Task 1: Create directory and verify monolith baseline

**Files:**

- Create: `GebLean/LawvereERKSim/` (directory; first file
  creation will create it).
- Verify: `GebLean/LawvereERKSim.lean` (current monolith,
  unchanged at this task).

- [ ] **Step 1: Verify clean build baseline**

```bash
lake build GebLean.LawvereERKSim 2>&1 | tail -5
```

Expected: `Build completed successfully (619 jobs).` (job
count may vary; absence of error lines is what matters).

- [ ] **Step 2: Record current file size**

```bash
wc -l GebLean/LawvereERKSim.lean
```

Expected: `11943 GebLean/LawvereERKSim.lean` (give or take
a few lines from interim edits).

- [ ] **Step 3: Verify current jj working-copy state is clean**

```bash
jj status
```

Expected: `The working copy is clean` or a single new
working-copy commit on top of the spec commit. If there are
unrelated edits in the working copy, pause and surface them
to the user before proceeding.

- [ ] **Step 4: Make a checkpoint commit if needed**

If `jj status` showed a clean working copy at a named
commit, skip this step. Otherwise:

```bash
jj describe -m "wip: file-split start checkpoint"
jj new
```

This pins the pre-split state for rollback if needed.

- [ ] **Step 5: Confirm dependency-graph readiness**

```bash
grep -c "^import " GebLean/LawvereERKSim.lean
grep -n "^open " GebLean/LawvereERKSim.lean
grep -c "^variable " GebLean/LawvereERKSim.lean
```

Expected:

- First command: 4 imports (`GebLean.LawvereER`,
  `GebLean.Utilities.ZeroTestURM`,
  `Mathlib.Data.Fintype.Basic`,
  `Mathlib.Tactic.FinCases`).
- Second command: one match, `80:open GebLean.ZeroTestURM`.
- Third command: 0 (no file-scope `variable` blocks).

If the `open` clause is missing or there are non-zero
`variable` blocks, halt and surface to the user — the
plan's submodule templates assume the
`open GebLean.ZeroTestURM` clause and zero `variable`
blocks.

- [ ] **Step 6: Verify `lake build <module-path>` works**

```bash
lake build GebLean.LawvereERKSim 2>&1 | tail -3
```

Expected: clean build, completes in a few seconds (no
mathlib rebuild). The narrow-target form
`lake build GebLean.LawvereERKSim.<Submodule>` is used in
every move task's isolation build. If the narrow-target
form is unsupported in this project's lake version, fall
back to `lake build` (whole tree) in subsequent isolation
builds — document this in a comment on the relevant task.

No commit at this task — it is verification only.

---

## Task 2: Create `Compiler.lean` (Section A move)

**Files:**

- Create: `GebLean/LawvereERKSim/Compiler.lean` (~1400 LOC).
- Modify: `GebLean/LawvereERKSim.lean` (delete moved range,
  add forwarding import).

Source range (spec §4 row Compiler.lean): monolith lines
82–1473 inclusive (the first declaration `inductive
URMInstrRaw` starts at line 92; the namespace declarations
at lines 76 and 78 and the `open` clause at line 80 are
written fresh in `Compiler.lean`'s header per Step 1 below;
the monolith pre-namespace block at lines 1–75 stays in
the monolith for Task 7). Cross-reference: spec §5.1 lists
each declaration with its source line number.

- [ ] **Step 1: Write the `Compiler.lean` header**

Write the file with exactly this content, in order:

```lean
import GebLean.LawvereER
import GebLean.Utilities.ZeroTestURM
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# LawvereERKSim — compiler

Per-constructor URM-fragment compilation for the ER → URM
half of the erToK construction. Emits a `URMProgram` from
an `ERMor1 a` term; correctness lives in sibling submodules
under `GebLean/LawvereERKSim/`.

## Main definitions

- `URMInstrRaw`, `URMInstrRaw.regBound`,
  `URMInstrRaw.toBounded`, `URMInstrRaw.boundedBy`,
  `URMInstrRaw.toBoundedArray`,
  `URMInstrRaw.reindexShift`: raw-instruction
  intermediate and its conversion to `URMInstr r`.
- `CompiledFragment`: bundled sub-fragment with invariants
  (`numRegs_pos`, `zeroReg_not_input`,
  `zeroReg_not_output`, `lastInstr_isStop`).
- `CompiledFragment.zeroReg`, `URMRaw.goto`,
  `URMRaw.transferLoop`, `URMRaw.transferLoopLen`,
  `URMRaw.preservingTransfer`,
  `URMRaw.preservingTransferLen`: emission helpers.
- `compileFrag_zero`, `compileFrag_succ`,
  `compileFrag_proj`, `compileFrag_sub`,
  `compileFrag_comp`, `compileFrag_bsum`,
  `compileFrag_bprod`: per-ER-constructor compilers.
- `compileFrag_sub_inputRegs`,
  `compileFrag_comp_subBlock`, `bsum_prologueSrc`,
  `bsum_prologueBlock`, `bsum_zeroSweep`: per-compiler
  building blocks.
- `gsPrefixSum`, `toRawOfBounded`: arithmetic and
  conversion helpers.
- `compileERFrag`, `compileER`, `compileER_numRegs`,
  `compileER_runtime`: top-level compiler and runtime
  witness.

## Main statements

- `URMInstrRaw.toBoundedArray_size`,
  `URMInstrRaw.toBoundedArray_getElem`,
  `URMInstrRaw.toBoundedArray_getElem?`,
  `URMInstrRaw.toBoundedArray_back?_of_last_stopR`:
  bounded-array indexing and last-instruction lemmas.
- `URMInstrRaw.toBounded_congr`: conversion congruence.
- `regBound_toRawOfBounded_le`,
  `regBound_reindexShift_le_offset_add`: register-bound
  preservation.
- `gsPrefixSum_succ_eq`, `gsPrefixSum_mono`: arithmetic
  lemmas on the prefix-sum helper.
- `boundedBy_preservingTransfer`,
  `boundedBy_transferLoop`,
  `boundedBy_compileFrag_comp_subBlock`,
  `boundedBy_bsum_prologueBlock`,
  `boundedBy_bsum_zeroSweep`: per-emission-helper
  register-bound theorems.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37
  (URM kernel), p. 19 (succ), §0.1.0.43 (Ritchie–Cobham).
- Spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM
```

The `open GebLean.ZeroTestURM` is required (monolith line
80); it brings `URMProgram`, `URMState`, `URMInstr`,
`runFor` etc. into scope.

- [ ] **Step 2: Extract and append the declaration content**

Confirm the end-of-range marker:

```bash
sed -n '1470,1476p' GebLean/LawvereERKSim.lean
```

Expected: line 1473 is `compileER_runtime`'s closing
brace or its trailing blank line; line 1474 begins
Section B's first declaration (the docstring for
`getElem_of_getElem?_some`).

Extract the declarations to a temporary file:

```bash
sed -n '82,1473p' GebLean/LawvereERKSim.lean > /tmp/section_a.lean
```

(Line 82 is the start of `URMInstrRaw`'s docstring; this
skips the `namespace GebLean`, `namespace LawvereERKSim`,
and `open GebLean.ZeroTestURM` lines, which we already
wrote in Step 1.)

Append `/tmp/section_a.lean`'s content to `Compiler.lean`
using the `Read` tool followed by the `Write` tool with
the combined content (header from Step 1 + extracted
declarations).

- [ ] **Step 3: Close the namespaces at the end of `Compiler.lean`**

Append at the very end of `Compiler.lean`:

```lean
end LawvereERKSim
end GebLean
```

- [ ] **Step 4: Build `Compiler.lean` in isolation**

```bash
lake build GebLean.LawvereERKSim.Compiler 2>&1 | tail -30
```

Expected: `Build completed successfully`. Likely fix-up
needs:

- "unknown identifier `URMProgram`" or similar: confirm
  `open GebLean.ZeroTestURM` is present after the
  namespace declarations.
- "unknown identifier `ERMor1`" or similar: confirm
  `import GebLean.LawvereER` is in place. The monolith
  uses `ERMor1`, `ERMor1.interp`, etc. unqualified;
  these come from `GebLean.LawvereER`.
- `private` declarations referenced from later submodules
  (Task 3 onward): drop `private` only when a later task's
  build surfaces the cross-file reference. At Task 2's
  isolation build, no `private` promotion is needed (no
  later submodule yet exists).
- Spurious unused-variable warnings: leave as-is
  (signatures preserved verbatim).

Iterate Step 4 until build is clean.

- [ ] **Step 5: Delete the moved range from the monolith**

In `GebLean/LawvereERKSim.lean`, delete lines 76–1473 (the
`namespace GebLean`, `namespace LawvereERKSim`,
`open GebLean.ZeroTestURM`, and all of Section A's
declarations). The monolith retains lines 1–75 (the
existing module docstring) plus lines 1474–end (subsequent
sections).

Note: line numbers in the original 11,943-line file. After
deletion, the file shrinks to ~10,544 lines and Section B
starts at the new line 76.

- [ ] **Step 6: Add forwarding import to the monolith**

In `GebLean/LawvereERKSim.lean`, after the existing four
imports, add:

```lean
import GebLean.LawvereERKSim.Compiler
```

The original four imports stay (subsequent sections still
need them); they will be cleaned up wholesale by Task 7.
Add `open GebLean.ZeroTestURM` and re-instate the
namespaces `namespace GebLean` and `namespace LawvereERKSim`
in the monolith if the build complains about unknown
identifiers — Section B (still in the monolith) expects
these in scope.

- [ ] **Step 7: Build the monolith**

```bash
lake build GebLean.LawvereERKSim 2>&1 | tail -30
```

Expected: `Build completed successfully`.

- [ ] **Step 8: Verify axiom hygiene on flagship declarations**

Use `mcp__lean-lsp__lean_verify` with the fully-qualified
name of each:

- `GebLean.LawvereERKSim.compileER`
- `GebLean.LawvereERKSim.compileER_runtime`
- `GebLean.LawvereERKSim.compileFrag_comp`
- `GebLean.LawvereERKSim.compileFrag_bsum`
- `GebLean.LawvereERKSim.compileFrag_bprod`
- `GebLean.LawvereERKSim.boundedBy_compileFrag_comp_subBlock`

Expected for each: axioms `[propext, Quot.sound]` only.
If `Classical.choice` appears, halt and surface the
finding to the user.

- [ ] **Step 9: Commit**

```bash
jj describe -m "refactor(ertok): extract Compiler.lean from LawvereERKSim"
jj new
```

---

## Task 3: Create `Embedding.lean` (Section B parts + bridge)

**Files:**

- Create: `GebLean/LawvereERKSim/Embedding.lean` (~800 LOC).
- Modify: `GebLean/LawvereERKSim.lean` (delete moved
  ranges, add forwarding import).

Source ranges (spec §4 row Embedding.lean): four
non-contiguous sub-ranges in the monolith.

- Main Section B block: 1474–2137 (step lemmas,
  `ProgramEmbedsFragment`, `StateEmbedsFrag`,
  `stateEmbedsFrag_*` family, PC-in-range lemmas).
- `URMState.init_regs_zero_outside_inputs`: line 5210
  (single declaration, ~25 lines spanning the docstring +
  body; the surrounding proj helpers
  `List.find?_finRange_inputRegs` and
  `URMState.init_regs_inputRegs` stay in Atoms.lean —
  Task 5).
- Tail-variant lemmas: lines 5866–5944
  (`stateEmbedsFrag_step_tail`,
  `stateEmbedsFrag_runFor_tail`). Anchor:
  `/-- Variant of \`stateEmbedsFrag_step\` for the case where`.
- Bridge: lines 11821–11895
  (`compileER_pre_stop_to_runFor`). Anchor:
  `/-- Generic bridge from the existential pre-stop form`.

The general-k wrapper `compileER_runFor_comp` at lines
11896–11940 stays for Task 6 (goes into `Comp.lean`).

Note: `URMProgram.WellBounded`,
`URMState.runFor_halted_invariant`, `URMState.runFor_stop`
are *not* in the monolith — they live in
`GebLean/Utilities/ZeroTestURM.lean`. They are *used* by
`Embedding.lean` (via `open GebLean.ZeroTestURM`), not
defined in it.

- [ ] **Step 1: Write the `Embedding.lean` header**

Write the file with this content, in order:

```lean
import GebLean.LawvereERKSim.Compiler

/-!
# LawvereERKSim — runtime embedding and the pre-stop bridge

Step-relation lemmas and the `ProgramEmbedsFragment` /
`StateEmbedsFrag` framework used to lift correctness from
sub-fragment to enclosing program. Plus the
constructor-agnostic
`compileER_pre_stop_to_runFor` bridge that converts the
existential pre-stop form (∃ T₀ ≤ runtime witness, PC at
size-1, output correct) to the output-only `≤ t'` form.

## Main definitions

- `ProgramEmbedsFragment` (`private structure`): predicate
  asserting that one URM program's instructions at PCs
  `pcBase ..+ L` realise another's.
- `StateEmbedsFrag` (`private def`): per-state instance of
  `ProgramEmbedsFragment` carrying current PC and register
  alignment.

## Main statements

- `URMState.step_of_getElem?_{jumpZ,dec,inc,assign,stop}`,
  `getElem_of_getElem?_some`: helpers for stepping when
  the instruction at the current PC is known via
  `getElem?`.
- `stateEmbedsFrag_step`, `stateEmbedsFrag_runFor`: per-step
  and multi-step simulation under embedding.
- `stateEmbedsFrag_step_tail`,
  `stateEmbedsFrag_runFor_tail`: variants for sub-programs
  whose embedded code ends at the outer's tail.
- `stateEmbedsFrag_step_outside_preserved`,
  `stateEmbedsFrag_runFor_outside_preserved`: register
  preservation outside the embedded sub-program's
  register block.
- `compileER_runFor_pc_le_size`,
  `fragment_runFor_pc_le_size`: PC-in-range during
  bounded execution.
- `URMState.init_regs_zero_outside_inputs`: initial
  register block is zero outside the input slots.
- `compileER_pre_stop_to_runFor`: the constructor-agnostic
  bridge from existential pre-stop to `≤ t'` output form.

## References

- Spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM
```

- [ ] **Step 2: Extract Section B main block (lines 1474–2137)**

```bash
sed -n '1474,2137p' GebLean/LawvereERKSim.lean > /tmp/emb_main.lean
```

This captures: `getElem_of_getElem?_some` through
`fragment_runFor_pc_le_size`.

- [ ] **Step 3: Extract `URMState.init_regs_zero_outside_inputs` (line 5210)**

Locate the exact line range using the anchor:

```bash
grep -n "^private theorem URMState.init_regs_zero_outside_inputs" GebLean/LawvereERKSim.lean
```

Expected: `5210:private theorem URMState.init_regs_zero_outside_inputs`.

Find its docstring start (a few lines earlier) and its
body end (the next blank line before `private theorem
compileER_runFor_proj`):

```bash
sed -n '5203,5237p' GebLean/LawvereERKSim.lean
```

Extract the precise range (typically 5203–5236, but
confirm visually that the next declaration line begins
with `private theorem compileER_runFor_proj`):

```bash
sed -n 'START,ENDp' GebLean/LawvereERKSim.lean > /tmp/emb_init_zero.lean
```

- [ ] **Step 4: Extract tail variants (lines 5866–5944)**

Locate via anchor:

```bash
grep -n "^private theorem stateEmbedsFrag_step_tail\|^private theorem stateEmbedsFrag_runFor_tail" GebLean/LawvereERKSim.lean
```

Expected:

- `5866:private theorem stateEmbedsFrag_step_tail`
- `5903:private theorem stateEmbedsFrag_runFor_tail`

Find the docstring start (a few lines before 5866) and
the body end (one line before line 5945, which begins
`/-- k=0 special case of \`compileER_runFor_comp\``).
Extract:

```bash
sed -n '5854,5944p' GebLean/LawvereERKSim.lean > /tmp/emb_tail.lean
```

Confirm with `sed -n '5944,5946p'` that line 5945 begins
the k=0 wrapper's docstring (not part of this extract).

- [ ] **Step 5: Extract the bridge (lines 11821–11895)**

Locate via anchor:

```bash
grep -n "^private theorem compileER_pre_stop_to_runFor" GebLean/LawvereERKSim.lean
```

Expected: `11830:private theorem compileER_pre_stop_to_runFor`.

The docstring begins at line 11821 (`/-- Generic bridge
from the existential pre-stop form`); the body ends one
line before line 11896 (`/-- Output-only \`≤ t'\` form\``).
Extract:

```bash
sed -n '11821,11895p' GebLean/LawvereERKSim.lean > /tmp/emb_bridge.lean
```

- [ ] **Step 6: Assemble `Embedding.lean`**

Append the four extracted parts to `Embedding.lean`, in
this order: Section B main block, `init_zero`, tail
variants, bridge. Use the `Read` and `Write` tools to
combine. Add `end LawvereERKSim` and `end GebLean` at the
end.

- [ ] **Step 7: Build `Embedding.lean` in isolation**

```bash
lake build GebLean.LawvereERKSim.Embedding 2>&1 | tail -30
```

Expected: clean. Possible fix-ups (per spec §6.1):

- Cross-file references to declarations that are
  `private` in `Compiler.lean`: drop the `private`
  modifier on the named declaration in `Compiler.lean`
  and rebuild.
- Identifiers unqualified that need re-`open`: confirm
  `open GebLean.ZeroTestURM` is present.

- [ ] **Step 8: Delete the four moved ranges from the monolith**

Important: deletions must happen in reverse line-number
order so earlier line numbers stay valid.

After Task 2's deletion (76–1473), the monolith shrank to
~10,544 lines and Section B starts at the new line 76.
However, the source line numbers cited below are the
*original* monolith coordinates. Use the `Read` tool to
find the current line numbers using the anchors:

- Bridge anchor: `/-- Generic bridge from the existential pre-stop form`.
- Tail variants anchor: `/-- Variant of \`stateEmbedsFrag_step\``.
- `init_regs_zero_outside_inputs` anchor:
  `^private theorem URMState.init_regs_zero_outside_inputs`.
- Section B main block anchor:
  `^/-- Convert a \`getElem?\` equality` (the first
  declaration `getElem_of_getElem?_some`'s docstring).

Use `Edit` to remove each range, in reverse order:

1. Delete bridge range (original 11821–11895; new
   coordinates after Task 2 delta = subtract 1398 from
   original).
2. Delete tail variants range (original 5854–5944).
3. Delete `init_regs_zero_outside_inputs` range
   (original 5203–5236, or whatever the Step 3 extract
   range was).
4. Delete Section B main block (original 1474–2137).

- [ ] **Step 9: Add forwarding import to the monolith**

```lean
import GebLean.LawvereERKSim.Embedding
```

Insert directly below the
`import GebLean.LawvereERKSim.Compiler` line.

- [ ] **Step 10: Build the monolith**

```bash
lake build GebLean.LawvereERKSim 2>&1 | tail -30
```

Expected: clean.

- [ ] **Step 11: Verify axiom hygiene on flagship declarations**

Use `mcp__lean-lsp__lean_verify` on:

- `GebLean.LawvereERKSim.ProgramEmbedsFragment`
- `GebLean.LawvereERKSim.StateEmbedsFrag`
- `GebLean.LawvereERKSim.stateEmbedsFrag_runFor`
- `GebLean.LawvereERKSim.stateEmbedsFrag_runFor_tail`
- `GebLean.LawvereERKSim.compileER_runFor_pc_le_size`
- `GebLean.LawvereERKSim.URMState.init_regs_zero_outside_inputs`
- `GebLean.LawvereERKSim.compileER_pre_stop_to_runFor`

Expected: `[propext, Quot.sound]` only on each.

- [ ] **Step 12: Commit**

```bash
jj describe -m "refactor(ertok): extract Embedding.lean from LawvereERKSim"
jj new
```

---

## Task 4: Create `Loops.lean` (Section C parts)

**Files:**

- Create: `GebLean/LawvereERKSim/Loops.lean` (~2750 LOC).
- Modify: `GebLean/LawvereERKSim.lean` (delete moved
  ranges, add forwarding import).

Source ranges (spec §4 row Loops.lean): three
non-contiguous monolith sub-ranges. The three blocks are
non-contiguous because `compileER_runFor_*` (Section D)
and atom pre-stop work were appended later.

- `preservingTransfer`/`transferLoop` block: 2956–4915.
  Includes the two `compileFrag_comp`-specific
  dischargers
  (`PreservingTransferInstrs_compileFrag_comp_inputCopies`
  at 2990, `TransferLoopInstrs_compileFrag_comp_outputTransfer`
  at 4187) — these stay in Loops because they consume the
  `preservingTransferInstrs` / `transferLoopInstrs`
  private structures (spec §5.3).
- `subInnerLoop` block: 5414–5853 (specifically
  5414–5664 for the `subInnerLoop_correct` material;
  5665–5853 is the `compileER_runFor_sub` declaration
  which goes to Atoms — exclude it from this Task 4
  range).
- Non-contiguous PC-bound cluster: 6321–6606
  (`preservingTransfer_loop2_pc_strict_bound` at 6326,
  `preservingTransfer_correct_pc_strict_bound` at 6423,
  `subInnerLoop_correct_pc_strict_bound` at 6463,
  `preservingTransfer_correct_pc_bound` at 6561).

Anchors (re-derive current line numbers at execution time
after Tasks 2–3 deletions):

- Start of `preservingTransfer` block:
  `^private structure preservingTransferInstrs`.
- End of `preservingTransfer`/`transferLoop` block (just
  before Atoms range begins): `^private theorem compileER_runFor_zero`.
- Start of `subInnerLoop` block:
  `^private structure subInnerLoopInstrs`.
- End of `subInnerLoop` block (just before sub-runFor):
  `^private theorem compileER_runFor_sub`.
- Start of PC-bound cluster:
  `^private theorem preservingTransfer_loop2_pc_strict_bound`.
- End of PC-bound cluster (just before `vPrefixSum`):
  `^private def vPrefixSum`.

- [ ] **Step 1: Write the `Loops.lean` header**

Write the file with this content:

```lean
import GebLean.LawvereERKSim.Embedding

/-!
# LawvereERKSim — loop-correctness theorems

Correctness theorems for the three URM loop combinators
used by the atom and comp compilers:
`URMRaw.transferLoop` (4n+1 steps),
`URMRaw.preservingTransfer` (9n+2 steps via two inner
loops), and the inner loop of `compileFrag_sub`. Each
"correct" theorem comes with per-step and strict per-step
PC-bound siblings.

Also includes two `compileFrag_comp`-specific
instruction-presence dischargers
(`PreservingTransferInstrs_compileFrag_comp_inputCopies`,
`TransferLoopInstrs_compileFrag_comp_outputTransfer`)
that exhibit `compileFrag_comp_subBlock`'s layout as
instances of the loop patterns. They live here because
they consume the `preservingTransferInstrs` and
`transferLoopInstrs` private structures defined in this
file; promoting those structures out of file scope is
avoided.

## Main definitions

- `preservingTransferInstrs`, `transferLoopInstrs`,
  `subInnerLoopInstrs` (all `private structure`):
  packaged hypothesis bundles for each loop.

## Main statements

- `preservingTransfer_correct`,
  `preservingTransfer_correct_pc_bound`,
  `preservingTransfer_correct_pc_strict_bound`, with
  inner helpers `preservingTransfer_loop1`,
  `preservingTransfer_loop1_pc_bound`,
  `preservingTransfer_loop2`,
  `preservingTransfer_loop2_pc_bound`,
  `preservingTransfer_loop2_pc_strict_bound`.
- `transferLoop_correct`, `transferLoop_correct_pc_bound`,
  `transferLoop_correct_pc_strict_bound`.
- `subInnerLoop_correct`, `subInnerLoop_correct_pc_bound`,
  `subInnerLoop_correct_pc_strict_bound`.
- `PreservingTransferInstrs_compileFrag_comp_inputCopies`,
  `TransferLoopInstrs_compileFrag_comp_outputTransfer`:
  comp-layout dischargers.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37
  (URM kernel and Tourlakis-style transfer loops).
- Spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM
```

- [ ] **Step 2: Extract the three Section C sub-ranges**

Use the anchors from this task's preamble to compute
current line numbers. Extract each to a temporary file:

```bash
sed -n 'START_PRES,END_TLOOPp' GebLean/LawvereERKSim.lean > /tmp/loops_pres_tloop.lean
sed -n 'START_SUB,END_SUBp' GebLean/LawvereERKSim.lean > /tmp/loops_subinner.lean
sed -n 'START_PCB,END_PCBp' GebLean/LawvereERKSim.lean > /tmp/loops_pcbounds.lean
```

(Replace `START_*` and `END_*` with concrete line numbers
from the anchors.)

- [ ] **Step 3: Assemble `Loops.lean`**

Append the three extracted parts to `Loops.lean` in this
order: `loops_pres_tloop`, `loops_subinner`,
`loops_pcbounds`. Add `end LawvereERKSim` and
`end GebLean` at the end.

- [ ] **Step 4: Build `Loops.lean` in isolation**

```bash
lake build GebLean.LawvereERKSim.Loops 2>&1 | tail -30
```

Expected: clean. Likely fix-ups:

- The two comp dischargers reference `compileFrag_comp`,
  `compileFrag_comp_subBlock` from `Compiler.lean`; these
  should be visible via `import
  GebLean.LawvereERKSim.Embedding` (which imports
  Compiler).
- `private` references from Atoms/Comp will surface in
  Tasks 5–6, not Task 4 (since Atoms and Comp do not yet
  exist). Tasks 5–6's isolation builds may require
  promoting some Loops declarations.

- [ ] **Step 5: Delete the moved ranges from the monolith**

Three deletions, in reverse line-number order:

1. PC-bound cluster (original 6321–6606).
2. `subInnerLoop` block (original 5414–5664; the
   sub-runFor at 5665+ stays for Task 5).
3. `preservingTransfer`/`transferLoop` block (original
   2956–4915).

Use the `Read` tool to compute current line numbers via
anchors after Tasks 2–3 deletions.

- [ ] **Step 6: Add forwarding import to the monolith**

```lean
import GebLean.LawvereERKSim.Loops
```

Insert below `import GebLean.LawvereERKSim.Embedding`.

- [ ] **Step 7: Build the monolith**

```bash
lake build GebLean.LawvereERKSim 2>&1 | tail -30
```

Expected: clean.

- [ ] **Step 8: Verify axiom hygiene on flagship declarations**

Use `mcp__lean-lsp__lean_verify` on:

- `GebLean.LawvereERKSim.preservingTransfer_correct`
- `GebLean.LawvereERKSim.preservingTransfer_correct_pc_strict_bound`
- `GebLean.LawvereERKSim.transferLoop_correct`
- `GebLean.LawvereERKSim.transferLoop_correct_pc_strict_bound`
- `GebLean.LawvereERKSim.subInnerLoop_correct`
- `GebLean.LawvereERKSim.subInnerLoop_correct_pc_strict_bound`
- `GebLean.LawvereERKSim.PreservingTransferInstrs_compileFrag_comp_inputCopies`
- `GebLean.LawvereERKSim.TransferLoopInstrs_compileFrag_comp_outputTransfer`

Expected: `[propext, Quot.sound]` only on each.

- [ ] **Step 9: Commit**

```bash
jj describe -m "refactor(ertok): extract Loops.lean from LawvereERKSim"
jj new
```

---

## Task 5: Create `Atoms.lean` (Section D parts)

**Files:**

- Create: `GebLean/LawvereERKSim/Atoms.lean` (~2000 LOC).
- Modify: `GebLean/LawvereERKSim.lean` (delete moved
  ranges, add forwarding import).

Source ranges (spec §4 row Atoms.lean): five
non-contiguous monolith sub-ranges. Re-derive current
line numbers via anchors at execution time after Tasks
2–4 deletions.

- zero+succ `_runFor`: 4917–5156 (lines for
  `compileER_runFor_zero` 4919 and `compileER_runFor_succ`
  5012, plus surrounding docstrings).
- proj helpers + `_runFor_proj`: 5157–5209 plus
  5237–5413. Note: lines 5210–5236 contain
  `URMState.init_regs_zero_outside_inputs` which moves to
  Embedding (Task 3 Step 3); exclude from this extract.
- sub `_runFor`: 5654–5853.
- zero atom pre-stop: 6199–6325.
- succ + proj + sub atom pre-stop: 7209–8023.

All eight target declarations (the four `_runFor_*` and
the four `_pre_stop_correct_atom_*`) use the empirically-
verified names below. The atom pre-stop lemmas carry the
`_atom_` infix; the `_runFor_*` lemmas do not.

Anchors (use to compute current line numbers at execution
time):

- `^private theorem compileER_runFor_zero` (4919).
- `^private theorem compileER_runFor_succ` (5012).
- `^private theorem List.find?_finRange_inputRegs` (5157).
- `^private theorem URMState.init_regs_inputRegs` (5191).
- `^private theorem URMState.init_regs_zero_outside_inputs`
  (5210, EXCLUDE — goes to Embedding).
- `^private theorem compileER_runFor_proj` (5239).
- `^private theorem compileER_runFor_sub` (5663).
- `^private theorem compileER_pre_stop_correct_atom_zero`
  (6208).
- `^private theorem compileER_pre_stop_correct_atom_succ`
  (7215).
- `^private theorem compileER_pre_stop_correct_atom_proj`
  (7456).
- `^private theorem compileER_pre_stop_correct_atom_sub`
  (7684).

- [ ] **Step 1: Write the `Atoms.lean` header**

Write the file with:

```lean
import GebLean.LawvereERKSim.Loops

/-!
# LawvereERKSim — atom-constructor correctness

Per-constructor `compileER_runFor_*` and
`compileER_pre_stop_correct_atom_*` lemmas for the four
ER atoms (`zero`, `succ`, `proj`, `sub`). Each constructor
appears twice: once in the slack-absorbing `≤ t'` form
(the `_runFor_*` lemma) and once in the existential
pre-stop form used by the comp pre-stop assembly (the
`_pre_stop_correct_atom_*` lemma).

## Main statements

- `compileER_runFor_zero`, `_succ`, `_proj`, `_sub`:
  output-only `≤ t'` form for each atom.
- `compileER_pre_stop_correct_atom_zero`, `_succ`,
  `_proj`, `_sub`: existential pre-stop form for each
  atom (with PC strict bound on earlier steps).
- `List.find?_finRange_inputRegs`,
  `URMState.init_regs_inputRegs`: proj-specific helpers
  for `URMState.init`'s register block on input slots.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37,
  p. 19 (succ realisation).
- Spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM
```

- [ ] **Step 2: Extract the five Section D sub-ranges**

In monolith source order:

1. zero+succ block: extract lines 4917–5156 (covers
   `compileER_runFor_zero` and `compileER_runFor_succ`).
2. proj helpers (find? + init_regs_inputRegs): extract
   lines 5157–5209.
3. `compileER_runFor_proj`: extract lines 5237–5413
   (this skips the 5210–5236 `init_regs_zero_outside_inputs`
   range that goes to Embedding).
4. sub `_runFor`: extract lines 5654–5853.
5. zero atom pre-stop: extract lines 6199–6325.
6. succ + proj + sub atom pre-stop: extract lines
   7209–8023.

Use one `sed` extraction per range; append all six in
order to `Atoms.lean` using the `Read`/`Write` tools.

- [ ] **Step 3: Close the namespaces**

```lean
end LawvereERKSim
end GebLean
```

- [ ] **Step 4: Build `Atoms.lean` in isolation**

```bash
lake build GebLean.LawvereERKSim.Atoms 2>&1 | tail -30
```

Expected: clean. Likely fix-ups:

- References to `private` declarations in `Loops.lean`
  (e.g., `transferLoop_correct`,
  `preservingTransfer_correct`,
  `subInnerLoop_correct`): drop the `private` modifier
  on the named declarations in `Loops.lean` and rebuild.
- References to `URMState.init_regs_zero_outside_inputs`
  should resolve via the `Embedding` import (transitively
  via `Loops`).

- [ ] **Step 5: Delete the moved ranges from the monolith**

Six deletions, in reverse line-number order. Use the
`Read` tool with the anchors above to find current line
numbers. Original monolith ranges:

1. 7209–8023 (succ+proj+sub pre-stop).
2. 6199–6325 (zero pre-stop).
3. 5654–5853 (sub `_runFor`).
4. 5237–5413 (proj `_runFor`).
5. 5157–5209 (proj helpers).
6. 4917–5156 (zero+succ `_runFor`).

- [ ] **Step 6: Add forwarding import to the monolith**

```lean
import GebLean.LawvereERKSim.Atoms
```

Insert below `import GebLean.LawvereERKSim.Loops`.

- [ ] **Step 7: Build the monolith**

```bash
lake build GebLean.LawvereERKSim 2>&1 | tail -30
```

Expected: clean.

- [ ] **Step 8: Verify axiom hygiene on flagship declarations**

Use `mcp__lean-lsp__lean_verify` on:

- `GebLean.LawvereERKSim.compileER_runFor_zero`
- `GebLean.LawvereERKSim.compileER_runFor_succ`
- `GebLean.LawvereERKSim.compileER_runFor_proj`
- `GebLean.LawvereERKSim.compileER_runFor_sub`
- `GebLean.LawvereERKSim.compileER_pre_stop_correct_atom_zero`
- `GebLean.LawvereERKSim.compileER_pre_stop_correct_atom_succ`
- `GebLean.LawvereERKSim.compileER_pre_stop_correct_atom_proj`
- `GebLean.LawvereERKSim.compileER_pre_stop_correct_atom_sub`

Expected: `[propext, Quot.sound]` only on each.

- [ ] **Step 9: Commit**

```bash
jj describe -m "refactor(ertok): extract Atoms.lean from LawvereERKSim"
jj new
```

---

## Task 6: Create `Comp.lean` (Section E parts + comp runFor wrapper)

**Files:**

- Create: `GebLean/LawvereERKSim/Comp.lean` (~5000 LOC).
- Modify: `GebLean/LawvereERKSim.lean` (delete moved
  ranges, add forwarding import).

Source ranges (spec §4 row Comp.lean): five non-contiguous
monolith sub-ranges. Re-derive current line numbers via
anchors at execution time after Tasks 2–5 deletions.

- Length / embedding setup: 2138–2955. Contains
  `compileFrag_comp_subBlock_length` (2145),
  `foldr_acc_add_eq_sum_map` (2183),
  `compileFrag_comp_subBlocks_length` (2196),
  `ProgramEmbedsFragment_compileFrag_comp_fBody` (2225),
  `flatMap_finRange_split` (2425),
  `ProgramEmbedsFragment_compileFrag_comp_gsBody` (2536).
- k=0 wrapper: 5945–6198. Contains
  `compileER_runFor_comp_k_zero` (5946). The
  immediately-preceding range 5866–5944 is tail variants
  (Embedding, Task 3), not Comp.
- Sub-block phase correctness: 6607–7208. Contains
  `vPrefixSum` (6607), `vPrefixSum_succ` (6614),
  `inputCopies_disj` (6627, private structure),
  `inputCopies_prefix_correct` (6653),
  `inputCopies_prefix_pc_strict_bound` (6785),
  `compileFrag_comp_subBlock_inputCopies_correct` (6878),
  `compileFrag_comp_subBlock_inputCopies_pc_strict_bound`
  (6914),
  `compileFrag_comp_subBlock_gsBody_correct` (6949; note
  the monolith has no `gsBody_pc_strict_bound` — gsBody's
  strict PC bound is provided by the structural IH on
  `gs m`),
  `compileFrag_comp_subBlock_outputTransfer_correct`
  (7160),
  `compileFrag_comp_subBlock_outputTransfer_pc_strict_bound`
  (7191).
- Comp m-step partial invariant: 8024–11820. Contains
  the `compileFrag_comp_pcOf` family, the partial
  invariant 8-clause structure, the three phase
  preservation lemmas, the induction-glue step,
  the outer iteration, and `compileER_pre_stop_correct_comp`.
- Section F wrapper: 11896–11940. Contains
  `compileER_runFor_comp` (general k).

Anchors at execution time (each unique in the monolith):

- `/-! ### Length lemmas for \`compileFrag_comp\``
  (Section E start, monolith line 2138).
- `^private theorem compileFrag_comp_subBlock_length`
  (2145).
- `^private theorem ProgramEmbedsFragment_compileFrag_comp_fBody`
  (2225, unique start of f-body embedding setup).
- `^private theorem ProgramEmbedsFragment_compileFrag_comp_gsBody`
  (2536, unique start of gs-body embedding setup).
- `^private theorem compileER_runFor_comp_k_zero` (5946).
- `^private def vPrefixSum` (6607, sub-block phase
  correctness start).
- `^private theorem compileFrag_comp_subBlock_outputTransfer_pc_strict_bound`
  (7191, last line of sub-block phase correctness block;
  ends at 7208).
- `/-! ### Comp m-step partial invariant`
  (m-step partial invariant start, monolith line 8024).
- `^private theorem compileER_pre_stop_correct_comp`
  (11339, comp assembly).
- `^private theorem compileER_runFor_comp` (11901,
  general-k runFor wrapper).

- [ ] **Step 1: Write the `Comp.lean` header**

Write the file with:

```lean
import GebLean.LawvereERKSim.Loops

/-!
# LawvereERKSim — comp-constructor correctness

Length lemmas, sub-block phase correctness, m-step partial
invariant, outer iteration, and final pre-stop assembly for
`compileFrag_comp f gs`. Plus the `≤ t'`-form wrapper
`compileER_runFor_comp` that combines
`compileER_pre_stop_correct_comp` with the constructor-
agnostic bridge `compileER_pre_stop_to_runFor` from
`Embedding.lean`.

## Main definitions

- `vPrefixSum`, `compileFrag_comp_pcOf`: prefix-sum
  helpers parametrising the m-step partial invariant.
- `inputCopies_disj`, `compileFrag_comp_partial_invariant`,
  `compileFrag_comp_phase_i1_post`,
  `compileFrag_comp_phase_i2_post` (all `private structure`):
  packaged predicates threaded through the m-step
  machinery.

## Main statements

- `compileFrag_comp_subBlock_length`,
  `compileFrag_comp_subBlocks_length`,
  `foldr_acc_add_eq_sum_map`, `flatMap_finRange_split`:
  length lemmas.
- `ProgramEmbedsFragment_compileFrag_comp_fBody`,
  `ProgramEmbedsFragment_compileFrag_comp_gsBody`: f-body
  and gs-body embedding witnesses.
- `compileFrag_comp_subBlock_{inputCopies,gsBody,
  outputTransfer}_correct`: per-phase correctness of the
  m-th sub-block. `inputCopies_correct` and
  `outputTransfer_correct` have `_pc_strict_bound`
  siblings; `gsBody_correct`'s strict bound is supplied
  by the structural IH on `gs m`.
- `compileER_runFor_comp_k_zero`: k=0 special case.
- `compileFrag_comp_subBlocks_partial_{base,phase_i1,
  phase_i2,phase_i3,step,aux,partial}`: m-step induction
  from base case through outer iteration.
- `compileER_pre_stop_correct_comp`: final pre-stop
  assembly.
- `compileER_runFor_comp`: general-k `≤ t'` wrapper (via
  the bridge in Embedding.lean).

## Implementation notes

The m-step machinery threads three phases per advance:

- Phase i.1: leading `inputCopies` (zero-sweep + a-source
  copies into the `gs m` body's input slots).
- Phase i.2: `gs m`'s body running on the structural IH.
- Phase i.3: trailing output transfer from `gs m`'s output
  register into the prefix-sum slot of f's input vector.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37.
- Spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/

namespace GebLean
namespace LawvereERKSim

open GebLean.ZeroTestURM
```

- [ ] **Step 2: Extract the five Section E sub-ranges plus the F wrapper**

In monolith source order:

1. Length / embedding setup: lines 2138–2955.
2. k=0 wrapper: lines 5945–6198.
3. Sub-block phase correctness: lines 6607–7208.
4. m-step partial invariant + assembly: lines
   8024–11820.
5. General-k runFor wrapper: lines 11896–11940.

Use one `sed` extraction per range; append all five in
order to `Comp.lean` using the `Read`/`Write` tools.

- [ ] **Step 3: Close the namespaces**

```lean
end LawvereERKSim
end GebLean
```

- [ ] **Step 4: Build `Comp.lean` in isolation**

```bash
lake build GebLean.LawvereERKSim.Comp 2>&1 | tail -30
```

Expected: clean. Likely fix-ups:

- References to `private` declarations from `Compiler.lean`
  (`compileFrag_comp_subBlock`, `compileFrag_comp`,
  `gsPrefixSum`, etc.) or from `Loops.lean`
  (`PreservingTransferInstrs_compileFrag_comp_inputCopies`,
  `TransferLoopInstrs_compileFrag_comp_outputTransfer`,
  `preservingTransfer_correct`,
  `transferLoop_correct`): drop the `private` modifier on
  each cross-file reference.
- `URMState.init_regs_zero_outside_inputs` must be
  visible (resolves via `Embedding` transitively through
  `Loops`).

- [ ] **Step 5: Delete the moved ranges from the monolith**

Five deletions, in reverse line-number order:

1. 11896–11940 (general-k runFor wrapper).
2. 8024–11820 (m-step partial invariant + assembly).
3. 6607–7208 (sub-block phase correctness).
4. 5945–6198 (k=0 wrapper).
5. 2138–2955 (length / embedding setup).

Use the `Read` tool with anchors to compute current line
numbers after Tasks 2–5 deletions.

After Task 6's deletions, the monolith contains only the
original imports, the existing module docstring, the
namespace declarations, the `open` clause, and the five
forwarding imports
(`Compiler/Embedding/Loops/Atoms/Comp`). Task 7
wholesale-overwrites the file with the final pure-import
index.

- [ ] **Step 6: Add forwarding import to the monolith**

```lean
import GebLean.LawvereERKSim.Comp
```

The intermediate file state has nine imports (the four
original plus the five forwarding). Task 7 collapses to
five. This transient excess is fine — the index-file
overwrite at Task 7 Step 1 cleans it up.

- [ ] **Step 7: Build the monolith**

```bash
lake build GebLean.LawvereERKSim 2>&1 | tail -30
```

Expected: clean.

- [ ] **Step 8: Verify axiom hygiene on flagship declarations**

Use `mcp__lean-lsp__lean_verify` on:

- `GebLean.LawvereERKSim.compileFrag_comp_subBlock_length`
- `GebLean.LawvereERKSim.ProgramEmbedsFragment_compileFrag_comp_fBody`
- `GebLean.LawvereERKSim.ProgramEmbedsFragment_compileFrag_comp_gsBody`
- `GebLean.LawvereERKSim.compileFrag_comp_subBlock_inputCopies_correct`
- `GebLean.LawvereERKSim.compileFrag_comp_subBlock_gsBody_correct`
- `GebLean.LawvereERKSim.compileFrag_comp_subBlock_outputTransfer_correct`
- `GebLean.LawvereERKSim.compileER_runFor_comp_k_zero`
- `GebLean.LawvereERKSim.compileFrag_comp_subBlocks_partial`
- `GebLean.LawvereERKSim.compileER_pre_stop_correct_comp`
- `GebLean.LawvereERKSim.compileER_runFor_comp`

Expected: `[propext, Quot.sound]` only on each.

- [ ] **Step 9: Commit**

```bash
jj describe -m "refactor(ertok): extract Comp.lean from LawvereERKSim"
jj new
```

---

## Task 7: Replace monolith with pure-import index

**Files:**

- Replace: `GebLean/LawvereERKSim.lean` (entire content
  becomes a pure-import index file).

After Tasks 2–6 the monolith retains only the original
imports, original module docstring, and the four/five
forwarding imports. Task 7 cleans this up into the
canonical index-file shape.

- [ ] **Step 1: Overwrite the monolith with the index content**

Write the entire file content as:

```lean
import GebLean.LawvereERKSim.Compiler
import GebLean.LawvereERKSim.Embedding
import GebLean.LawvereERKSim.Loops
import GebLean.LawvereERKSim.Atoms
import GebLean.LawvereERKSim.Comp

/-!
# erToK: ER → K^sim_2 via zero-test URM simulation

The compiler half of the erToK construction: emit a
`URMProgram` from an `ERMor1 a` term such that running the
URM long enough produces `e.interp v` in the output
register. This file re-exports the five submodules under
`GebLean/LawvereERKSim/`:

- `Compiler`: raw and bounded instructions, fragment
  emission for each ER constructor, top-level `compileER`
  and `compileER_runtime`.
- `Embedding`: step lemmas, the program-embedding
  framework, well-boundedness, and the constructor-agnostic
  `compileER_pre_stop_to_runFor` bridge.
- `Loops`: correctness of `URMRaw.transferLoop`,
  `URMRaw.preservingTransfer`, and the inner loop of
  `compileFrag_sub`.
- `Atoms`: per-constructor correctness for `zero`, `succ`,
  `proj`, `sub` (both `_runFor_*` and
  `_pre_stop_correct_*` forms).
- `Comp`: comp m-step machinery, outer iteration, final
  pre-stop assembly, and the comp `_runFor` wrapper.

Future submodules `BSum`, `BProd`, and `Top` (for the
top-level structural induction `compileER_runFor`) follow
once Tasks 11f, 11g, 11h land.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37
  (URM kernel, p. 15–16), §0.1.0.43 (Ritchie–Cobham,
  p. 21), §0.1.0.44 (proof, p. 22).
- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- File-split spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
-/
```

The file is now import-only; no `namespace`, no
declarations.

- [ ] **Step 2: Build the whole tree**

```bash
lake build 2>&1 | tail -20
```

Expected: `Build completed successfully` (full repository).

- [ ] **Step 3: Run lake test**

```bash
lake test 2>&1 | tail -20
```

Expected: tests pass. No test references the monolith
directly; `GebLean.LawvereERKSim` resolves to the new
index.

- [ ] **Step 4: Run scripts/check-axioms.sh**

```bash
bash scripts/check-axioms.sh GebLean/LawvereERKSim/Compiler.lean 2>&1 | tail -20
bash scripts/check-axioms.sh GebLean/LawvereERKSim/Embedding.lean 2>&1 | tail -20
bash scripts/check-axioms.sh GebLean/LawvereERKSim/Loops.lean 2>&1 | tail -20
bash scripts/check-axioms.sh GebLean/LawvereERKSim/Atoms.lean 2>&1 | tail -20
bash scripts/check-axioms.sh GebLean/LawvereERKSim/Comp.lean 2>&1 | tail -20
```

Expected: clean (no `Classical.choice` warnings). The
project memory notes that `check-axioms.sh` does not see
nested namespaces; treat any spurious flagging as a
known defect. The
`mcp__lean-lsp__lean_verify` per-declaration check (Steps
8 of Tasks 2–6) is the authoritative source.

- [ ] **Step 5: Verify the index file is pure-import**

```bash
grep -c "^import " GebLean/LawvereERKSim.lean
grep -cE "^(theorem|lemma|def|private theorem|private lemma|private def|abbrev|private abbrev|structure|inductive|namespace|end )" GebLean/LawvereERKSim.lean
```

Expected:

- First command: 5 (five submodule imports).
- Second command: 0 (no declarations, no namespace, no
  end markers in the index).

- [ ] **Step 6: Commit**

```bash
jj describe -m "refactor(ertok): replace LawvereERKSim.lean with pure-import index"
jj new
```

---

## Task 8: Final verification and documentation

**Files:**

- Update (if needed):
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`
  to note the file-split completion and update the
  "Resumption recipe".

- [ ] **Step 1: Verify clean tree-wide build**

```bash
lake build 2>&1 | tail -5
```

Expected: clean.

- [ ] **Step 2: Verify per-submodule line counts are within ±10% of the spec estimates**

```bash
wc -l GebLean/LawvereERKSim.lean GebLean/LawvereERKSim/*.lean
```

Expected ranges (per spec §3):

- `LawvereERKSim.lean`: 40–60 lines (pure-import index).
- `Compiler.lean`: ~1300–1600 lines.
- `Embedding.lean`: ~720–880 lines.
- `Loops.lean`: ~2500–3000 lines.
- `Atoms.lean`: ~1800–2200 lines.
- `Comp.lean`: ~4500–5500 lines.

If a submodule is significantly outside its estimate
range, halt and surface the discrepancy.

- [ ] **Step 2.5: Re-run the spec §7 `lean_verify` sample**

The spec §7 sample is the minimum end-to-end axiom check.
While Tasks 2–6 each ran `lean_verify` per-submodule, the
final tree state may differ from the per-task isolation
state. Re-run:

```text
mcp__lean-lsp__lean_verify on each of:
- GebLean.LawvereERKSim.compileER
- GebLean.LawvereERKSim.compileER_runtime
- GebLean.LawvereERKSim.preservingTransfer_correct
- GebLean.LawvereERKSim.transferLoop_correct
- GebLean.LawvereERKSim.subInnerLoop_correct
- GebLean.LawvereERKSim.compileER_runFor_zero
- GebLean.LawvereERKSim.compileER_runFor_succ
- GebLean.LawvereERKSim.compileER_runFor_proj
- GebLean.LawvereERKSim.compileER_runFor_sub
- GebLean.LawvereERKSim.compileER_runFor_comp
- GebLean.LawvereERKSim.compileER_pre_stop_to_runFor
- GebLean.LawvereERKSim.compileER_pre_stop_correct_comp
```

Expected: `[propext, Quot.sound]` only on each.

- [ ] **Step 3: Run the project's pre-push checklist**

```bash
bash scripts/pre-push.sh 2>&1 | tail -30
```

Expected: clean. `scripts/pre-push.sh` is the project's
standard pre-push checklist (per CLAUDE.md and the
project memory note). It runs `markdownlint-cli2`,
`lake lint`, `check-axioms.sh`, and `doctoc --check`.

- [ ] **Step 4: Markdownlint the modified docs**

```bash
npx markdownlint-cli2 'docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md' 'docs/superpowers/plans/2026-05-19-lawvere-er-k-sim-file-split-plan.md'
```

Expected: 0 errors.

- [ ] **Step 5: Update the T2 Task 11 handoff doc to note file-split completion**

In `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`:

- Add a "Session 4" sub-entry under "Task 11 — landed
  sub-tasks" naming the file split (item 9 from the
  followup branch).
- In the "Resumption recipe", remove step 2 ("File split
  is the next priority …") and renumber the remaining
  steps.

- [ ] **Step 6: Regenerate the handoff TOC**

```bash
npx doctoc docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md 2>&1 | tail -5
```

Expected: `Everything is OK.`

- [ ] **Step 7: Markdownlint the updated handoff**

```bash
npx markdownlint-cli2 'docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md'
```

Expected: 0 errors.

- [ ] **Step 8: Commit the documentation updates**

```bash
jj describe -m "docs(ertok): record file-split completion in T2 handoff"
jj new
```

---

## Self-review against the spec

- **§1 Scope**: covered by Tasks 2–6 (the five submodule
  moves) plus Task 7 (the index replacement). No new
  declarations introduced.
- **§2 Approach**: hybrid layered. Tasks 2–6 follow the
  declared layering exactly.
- **§3 Module map**: each submodule's file path and
  dependency-DAG position is named in its task header.
- **§4 Survey**: each task's "Source range" section cites
  the spec §4 row and lists the search anchors for
  re-deriving line numbers at execution time (since they
  shift across tasks).
- **§5 Per-submodule contents**: each task's docstring
  template lists the declarations the spec assigns to that
  submodule.
- **§6 Mechanical procedure**: the 8-task plan matches the
  spec's 15-step procedure (steps 1–2 → Task 1; steps
  3–11 → Tasks 2–6; step 12 → Task 7; steps 13–15 →
  Task 8). §6.1 (`private` promotion) and §6.2
  (sectional-comment moves) are referenced in the per-task
  Step 4 (build → fix-up) instructions.
- **§7 Verification**: Task 7 Steps 2–4 cover whole-tree
  `lake build`, `lake test`, and
  `scripts/check-axioms.sh`. Per-declaration
  `mcp__lean-lsp__lean_verify` is woven into every move
  task's Step 8.
- **§8 Risks and mitigations**: cross-file `private`
  promotion is addressed in each task's Step 4. Build-time
  degradation is bounded by per-task isolation builds.
  Module-docstring redistribution is handled by each
  task's Step 1 (write header).
- **§9 Out of scope**: respected. No new declarations, no
  followup-branch items #1–8.
