# Plan adversarial review — round 1

## Summary

The plan is structurally sound (8 tasks, dependency-respecting
order, per-step build verification) but contains a substantial
number of concrete defects that an executor following the plan
verbatim could not unambiguously act on. The largest classes of
defect are: (a) declaration names listed in the spec/plan that
do not match the names actually present in the monolith
(`compileER_pre_stop_correct_atom_*`, `URMRaw.transferLoopLen`
vs `URMRaw.transferLoop.size`, `inputCopies_prefix_correct` vs
unmentioned `inputCopies_disj`); (b) declarations attributed to
`Embedding.lean` that do not live in the monolith at all but
instead in `GebLean/Utilities/ZeroTestURM.lean`
(`URMProgram.WellBounded`, `URMState.runFor_stop`, etc.); (c)
line-range coverage that systematically omits the
`stateEmbedsFrag_step_tail` / `_runFor_tail` lemmas (located at
monolith lines 5866–5944) from every task's source range while
the spec puts them in Embedding; (d) two large Comp-specific
discharger lemmas (`PreservingTransferInstrs_compileFrag_comp_inputCopies`
and `TransferLoopInstrs_compileFrag_comp_outputTransfer`,
interleaved inside Section C's line range) that the plan would
silently move into `Loops.lean` because Task 4's anchors do not
exclude them; and (e) several mechanical issues (the
`open GebLean.ZeroTestURM` clause at monolith line 80 is not
mentioned anywhere; `scripts/pre-commit.sh` does not exist;
the Section A end-line is misidentified; the post-strip
duplicate-namespace cleanup step instructs deleting a line that
will not be present). Recommend another round of revision
before execution.

## Defects

### D1: `compileER_pre_stop_correct_*` atom names are wrong everywhere

**Where**: spec §5.4; plan Task 5 (declarations list at lines
281–286 of the spec and lines 699–702, 713, 819–821 of the
plan).

**Defect**: The spec and plan name the four atom pre-stop
lemmas as `compileER_pre_stop_correct_atom_zero`,
`compileER_pre_stop_correct_succ`,
`compileER_pre_stop_correct_proj`, and
`compileER_pre_stop_correct_sub`. The actual names in the
monolith (verified by `grep` against
`GebLean/LawvereERKSim.lean`) are:

- `compileER_pre_stop_correct_atom_zero` (line 6208)
- `compileER_pre_stop_correct_atom_succ` (line 7215)
- `compileER_pre_stop_correct_atom_proj` (line 7456)
- `compileER_pre_stop_correct_atom_sub` (line 7684)

Three of four names in the spec/plan are wrong (missing the
`_atom_` infix). The plan's Task 5 Step 8 `lean_verify` list
contains three names that do not exist, so the executor's
`lean_verify` calls will fail.

**Impact**: Three `lean_verify` invocations in Task 5 Step 8
will report "declaration not found"; Task 5 Step 1 docstring
will reference non-existent declarations; the
`/-- Pre-stop PC and output for the \`.succ\` atom\`` etc.
anchors at Task 5 lines 711–713 do match the actual decls'
docstrings, but the executor will then write the wrong names
into the moved-content's `## Main statements` section.

**Suggested fix**: Globally rename in spec §5.4 and plan
Task 5 (declarations list, anchors, and Step 8 verify list) to
`compileER_pre_stop_correct_atom_{zero,succ,proj,sub}`.

### D2: Spec §5.2 lists declarations that live in ZeroTestURM, not the monolith

**Where**: spec §5.2 (Embedding.lean declarations list).

**Defect**: Spec §5.2 lists `URMState.runFor_halted_invariant`,
`URMState.runFor_stop`, `URMProgram.WellBounded`, and
`URMProgram.WellBounded.runFor_pc_le_size` as declarations of
`Embedding.lean`. None of these is defined in the monolith:

- `URMState.runFor_halted_invariant` (line 213 of
  `GebLean/Utilities/ZeroTestURM.lean`)
- `URMState.runFor_stop` (line 226, same file)
- `URMProgram.WellBounded` (line 273, same file)
- `URMState.runFor_pc_le_size` (line 336, same file)

These are upstream declarations from `ZeroTestURM`; they are
*used* by the monolith but cannot be "moved" to `Embedding.lean`
because they are not in `LawvereERKSim.lean` to begin with.

**Impact**: An executor relying on §5.2 as the inventory of
"declarations to move" will be confused; if the executor then
adds these names to the Task 3 Step 2 sed-extract or to the
Embedding module docstring's `## Main definitions`, the file
will fail to build (duplicate definitions) or carry a docstring
that lies about file content. The `## Main definitions`
template at plan lines 410–414 already lists
`URMProgram.WellBounded` as an Embedding definition, which it
is not.

**Suggested fix**: Remove these four declarations from spec
§5.2 and plan Task 3 Step 1 docstring template. Note them
separately as "upstream dependencies imported via
`GebLean.LawvereERKSim.Compiler` (transitively from
`GebLean.Utilities.ZeroTestURM`)" if a reference is needed.

### D3: Tail-variant lemmas dropped between Task 3 and Task 6 ranges

**Where**: spec §5.2 vs §5.5 and §4; plan Task 3 source range
(plan lines 376–386); plan Task 6 source range (plan lines
846–882).

**Defect**: `stateEmbedsFrag_step_tail` (monolith line 5866)
and `stateEmbedsFrag_runFor_tail` (monolith line 5903) appear
in spec §5.2's declaration list (assigned to Embedding) but
sit at lines 5866–5944, which:

- is *not* inside spec §4 Section B's claimed range (1474–2137);
- *is* inside spec §4 Section E's claimed range (5854–6198);
- is *not* inside plan Task 3's source range (1474–2137 plus
  11821–11895);
- *is* inside plan Task 6's "5854–6198" range (plan lines
  863–865, "Sub-block phase correctness lemmas …
  approximately 5854–6198 and 6321–7208").

Therefore, executing the plan as written would move these two
lemmas into `Comp.lean`, in direct contradiction with spec §5.2
which assigns them to `Embedding.lean`.

**Impact**: If executor follows the plan ranges, the lemmas
end up in `Comp.lean`. The k=0 wrapper
`compileER_runFor_comp_k_zero` (also Comp content) imports them
and would still build, so no test would surface the
inconsistency. The Embedding module docstring would falsely
claim these as `Main statements`, and the spec/plan would
disagree.

**Suggested fix**: In plan Task 3 Step 3 (or as a new step), add
an explicit extraction of monolith lines 5866–5944 (use
anchor `/-- Variant of \`stateEmbedsFrag_step\``) into
`Embedding.lean`. Update plan Task 6's "5854–6198" range to
"5946–6198" (or whatever current range is at execution time
after the Embedding extraction). Equivalently, move
`compileER_runFor_comp_k_zero` and its setup into Embedding,
and update spec §5.5 to drop k_zero. The latter is cleaner
because k_zero is conceptually a Comp lemma; the former is the
faithful execution of spec §5.2.

### D4: Two Comp-specific dischargers buried inside Loops's range

**Where**: plan Task 4 (source ranges at plan lines 535–561).

**Defect**: The monolith contains two private theorems that
specialise the loop-instruction bundles to the comp sub-block
layout:

- `PreservingTransferInstrs_compileFrag_comp_inputCopies`
  (line 2990, ~575 LOC up to line 3564)
- `TransferLoopInstrs_compileFrag_comp_outputTransfer`
  (line 4187, ~407 LOC up to line 4593)

These lemmas talk about `compileFrag_comp` and belong topically
to `Comp.lean` per the spec's per-constructor grouping (their
proofs are entirely about comp's sub-block structure), but they
sit *inside* spec §4's Section C line range (2956–4915) because
they were proved adjacent to the `preservingTransferInstrs`
/ `transferLoopInstrs` definitions they bundle.

The plan's Task 4 anchors for `preservingTransfer_correct` start
at `/-- Hypothesis bundle for \`preservingTransfer_correct\``
(line 2956) and "end just before
`/-- Correctness of \`compileER\` on \`.zero\``" (line 4917).
This range silently sweeps both Comp-specific lemmas into
`Loops.lean`.

The spec §5.3 and plan Task 4 Step 1 docstring do *not* list
these declarations under Loops's main statements.

**Impact**: Either (a) the executor extracts these lemmas
into `Loops.lean`, contradicting the spec's topical-grouping
intent and forcing `Loops.lean` to depend on `compileFrag_comp`
(currently emitted in `Compiler.lean` — there is no cycle, but
the topical contract is broken), and `Loops.lean`'s module
docstring will lie about its content; or (b) the executor
notices the mismatch at execution time and has no plan-time
guidance for how to disentangle the interleaving.

**Suggested fix**: Add an explicit step to Task 4 to skip these
two declarations during the Section C extract (move them later
in Task 6), or alternatively decide that they belong in
`Loops.lean` and update spec §5.3 and the Task 4 docstring to
list them. Either way, name the decision explicitly. If the
former: provide the exact line-range deletions
(2990–3564 and 4187–4593, monolith coordinates) that Task 4
should *exclude*, and route these declarations into Task 6's
extract list with their own search anchors.

### D5: `URMRaw.transferLoop.size` / `preservingTransfer.size` are misnamed

**Where**: spec §5.1 (Compiler declarations list).

**Defect**: Spec §5.1 lists `URMRaw.transferLoop.size` and
`URMRaw.preservingTransfer.size`. The actual monolith
declarations (lines 279 and 304) are
`URMRaw.transferLoopLen` and `URMRaw.preservingTransferLen`
(no dot, suffix `Len` not `size`).

**Impact**: An executor cross-checking the spec's declaration
list against `grep` results in the monolith will find a
mismatch and may waste time hunting for the named decls.
The `## Main definitions` template in plan Task 2 docstring
does not name these specifically — only one consequence — but
spec accuracy is normative for the move.

**Suggested fix**: Rename in spec §5.1 to
`URMRaw.transferLoopLen` and `URMRaw.preservingTransferLen`.

### D6: Spec §5.1 lists numerous declarations that do not exist

**Where**: spec §5.1 (Compiler declarations list).

**Defect**: The following names listed in spec §5.1 do not
appear in the monolith (verified by `grep`):

- `URMInstrRaw.lastInstr_isStop_of_concat` — actual name is
  `URMInstrRaw.toBoundedArray_back?_of_last_stopR` (line 162).
- `gsBlockSize` — not found.
- `URMInstrRaw.preservingTransfer.reindexShift_bounded`,
  `URMInstrRaw.transferLoop.reindexShift_bounded`,
  `URMInstrRaw.reindexShift_bounded` — not found.
- `compileFrag_comp_subBlock_bounded` — actual name is
  `boundedBy_compileFrag_comp_subBlock` (line 642).
- `bsum_prologueBlock_bounded`, `bsum_zeroSweep_bounded` —
  actual names are `boundedBy_bsum_prologueBlock` (line 864)
  and `boundedBy_bsum_zeroSweep` (line 893).
- `compileER_numRegs_bound` — actual `def` is
  `compileER_numRegs` (line 1407), with no `_bound` suffix
  declaration in the monolith.

**Impact**: Spec's authoritative inventory is unreliable; an
executor cross-checking the spec list against the monolith will
hit ~6–7 phantom names and 4 misnamed names. Module-docstring
templates pulling from §5.1 will list non-existent
declarations.

**Suggested fix**: Audit spec §5.1 against the monolith and
rewrite the declarations list to match actual names. Same
audit should cover spec §5.3 and §5.5 (D4 and D7 below find
analogous issues there).

### D7: Spec §5.3 omits the loop "hyps" structures and uses wrong helper names

**Where**: spec §5.3 (Loops declarations list at design.md
lines 244–261).

**Defect**: Spec §5.3 names `preservingTransfer_hyps`,
`transferLoop_hyps`, `subInnerLoop_hyps`. The actual monolith
declarations are `preservingTransferInstrs` (line 2962),
`transferLoopInstrs` (line 4164), `subInnerLoopInstrs` (line
5419). All three are `private structure`s, not "hyps" helper
theorems.

Spec §5.3 also lists `preservingTransfer_loop2_pc_strict_bound`
under the `preservingTransfer` group; the monolith actually
has this declaration at line 6326, *non-contiguous* with the
other preservingTransfer helpers (which are at 3565–4156).
The plan Task 4 Step 2 anchors do not capture this
non-contiguity: a single `preservingTransfer` extraction will
miss line 6326's `_loop2_pc_strict_bound`. Similar
non-contiguity holds for `preservingTransfer_correct_pc_bound`
(line 6561), `preservingTransfer_correct_pc_strict_bound`
(line 6423), `subInnerLoop_correct_pc_strict_bound` (line
6463) — all in the 6326–6606 cluster.

**Impact**: (a) The Loops module docstring would list
non-existent decls. (b) Task 4's extraction would miss four
PC-bound theorems that Loops needs to host per the spec,
silently leaving them in the monolith for Task 5/6 to encounter
out-of-place.

**Suggested fix**: Rename "hyps" to "Instrs" everywhere in
spec §5.3, plan Task 4 docstring (plan line 588 has
`_loop1_correct`, `_loop2_correct`, `_loop2_pc_strict_bound` —
again wrong names since helpers are `_loop1`, `_loop2`, not
`_loop1_correct`, `_loop2_correct`). Add explicit extraction
of the 6326–6606 cluster to Task 4 (anchor:
`/-- Strict per-step PC bound for \`preservingTransfer_loop2\``
or similar). Update spec §4 row C to list the additional
6326–6606 range.

### D8: Spec §5.5 inputCopies_disj group has wrong consumer-lemma names

**Where**: spec §5.5 (Comp declarations list).

**Defect**: Spec §5.5 lists
`compileFrag_comp_subBlock_inputCopies_correct`,
`vPrefixSum`, `inputCopies_disj`, `disj_triple_for_reg`,
`compileFrag_comp_subBlock_inputCopies_pc_strict_bound`.
The monolith actually has:

- `vPrefixSum` (def, line 6607) — OK.
- `vPrefixSum_succ` (line 6614) — listed in spec, OK.
- `inputCopies_disj` (line 6627, `private structure`) — OK as
  a structure name, though spec lists it as if a theorem.
- `inputCopies_prefix_correct` (line 6653) and
  `inputCopies_prefix_pc_strict_bound` (line 6785) — *not*
  listed in spec §5.5.
- No declaration named `disj_triple_for_reg` exists in the
  monolith.

**Impact**: Spec inventory is incomplete (missing two
declarations that Task 6 must move) and contains a phantom
declaration (`disj_triple_for_reg`).

**Suggested fix**: Replace `disj_triple_for_reg` in spec §5.5
with `inputCopies_prefix_correct` and
`inputCopies_prefix_pc_strict_bound`. Audit the rest of §5.5
for analogous omissions/phantoms.

### D9: Task 2's claim that Section A ends at line 1473 is off-by-one or misidentified

**Where**: plan Task 2 (lines 196, 256–272).

**Defect**: Plan Task 2 says "monolith lines 76–1473 inclusive
(i.e. everything from `namespace GebLean` through the end of
`compileER_runtime`)". The monolith's `namespace GebLean` is at
line 76, but `compileER_runtime` runs from line 1427. Line
1473 is the blank line before line 1474's docstring (which
begins "Convert a getElem? equality...") that starts Section B.
The plan also says elsewhere
"Copy lines 78–1473" (Step 2, line 270), inconsistent with
"76–1473 inclusive" (Step header, line 196). Line 76 is
`namespace GebLean`, line 78 is `namespace LawvereERKSim`.
Task 2 Step 1's header template (line 251) writes both
`namespace GebLean` and `namespace LawvereERKSim`, so the copy
must start *after* both (line 80 or later), not at 76 or 78.

Also: line 80 is `open GebLean.ZeroTestURM`. The plan never
mentions transferring this `open`. Without it in `Compiler.lean`,
references to `URMProgram`, `URMState`, etc. (which live in the
`GebLean.ZeroTestURM` namespace) become unqualified and the
file fails to build. See D10 for full impact.

**Impact**: (a) The Step 2 sed extraction `sed -n '78,1473p'`
would double-copy `namespace LawvereERKSim` (line 78), which
Step 2 anticipates and tells the executor to delete
(plan lines 278–282) — but the prose at line 280 says "the
first line of the appended content should be the
`namespace LawvereERKSim` (which we already wrote in Step 1
above)". Line 78 *is* `namespace LawvereERKSim`. So the
extraction does include it once and the cleanup is needed.
But Step 2 line 196 ("76–1473 inclusive") contradicts line
270 ("Copy lines 78–1473"). Two distinct ranges are stated.
(b) Without explicit `open GebLean.ZeroTestURM`, the file
fails (see D10).

**Suggested fix**: Make Task 2 use a single consistent source
range: lines 80–1473 (just past the `open` clause), plus an
explicit instruction at Step 1 to *also* write
`open GebLean.ZeroTestURM` after the namespace lines.
Alternatively: extract 78–1473 (including the duplicate
namespace and the open clause), then strip the duplicate
namespace in Step 2 as currently described, *and* mention
that the `open` clause survives.

### D10: `open GebLean.ZeroTestURM` is unmentioned in every submodule

**Where**: plan Tasks 2–6 (header templates; lines 207–253,
389–434, 564–605, 715–755, 897–952).

**Defect**: The monolith at line 80 has
`open GebLean.ZeroTestURM`. Every submodule references
`URMProgram`, `URMState`, `URMInstr` etc. unqualified. None of
the per-task header templates includes `open GebLean.ZeroTestURM`
after the namespace lines.

**Impact**: As soon as Task 2's `Compiler.lean` is built in
isolation (Step 4), the lake build will fail with "unknown
identifier `URMProgram`" or similar across thousands of
references. The plan's Step 4 fix-up policy (line 301–305)
mentions adding `open` clauses, but the executor would have
to discover this and add the right namespace by trial and
error. Same for every other submodule.

**Suggested fix**: Update the submodule header template
(plan lines 73–105) to include
`open GebLean.ZeroTestURM` after the `namespace LawvereERKSim`
line. Mention explicitly in each task's Step 1 that the
`open` clause must be carried forward.

### D11: Spec §5.5 misnames `phase_i1_post` / `phase_i2_post` as theorems

**Where**: spec §5.5 (lines 333–335) and plan Task 6 docstring
(plan lines 927–928).

**Defect**: Spec §5.5 lists `compileFrag_comp_phase_i1_post`
and `compileFrag_comp_phase_i2_post` interleaved with theorems
in the declarations list. In the monolith both are `private
structure`s (lines 8533 and 9267). The plan's Task 6 docstring
at line 928 lists
`compileFrag_comp_subBlocks_partial_{base,phase_i1,phase_i2,phase_i3,step,aux,partial}`
which conflates the structures with the theorems and omits
`phase_i1_post` / `phase_i2_post` as line items.

**Impact**: Docstring's `## Main statements` section will be
mis-categorising structures as statements. Minor compared to
D1–D8 but inconsistent.

**Suggested fix**: In spec §5.5 separate structures from
theorems; in plan Task 6 Step 1 docstring add a `## Main
definitions` listing the structures (`compileFrag_comp_pcOf`,
`compileFrag_comp_partial_invariant`,
`compileFrag_comp_phase_i1_post`,
`compileFrag_comp_phase_i2_post`).

### D12: `scripts/pre-commit.sh` does not exist

**Where**: plan Task 8 Step 3 (lines 1179–1188).

**Defect**: Plan Task 8 Step 3 invokes
`bash scripts/pre-commit.sh`. The `scripts/` directory contains
`check-axioms.sh`, `check-jj-setup.sh`, `hooks`, `nolints.json`,
`pre-push.sh`. There is no `pre-commit.sh`. The plan
acknowledges "If this script does not exist in the project,
skip", but the project does have `pre-push.sh` which is the
relevant analogue.

**Impact**: The conditional ("skip if missing") means this is
not a hard breakage, but the plan misses the actual project
script and falls back to nothing.

**Suggested fix**: Replace `pre-commit.sh` with `pre-push.sh`
and verify what it runs (markdownlint, lake lint,
check-axioms). The project memory documents `pre-push.sh` as
part of the standard checklist.

### D13: Plan Task 4 docstring uses wrong helper names

**Where**: plan Task 4 Step 1 (plan lines 586–594).

**Defect**: Task 4 docstring template lists
`preservingTransfer_correct, with _loop1_correct,
_loop2_correct, _loop2_pc_strict_bound, _correct_pc_bound,
_correct_pc_strict_bound.`. The actual helper names are
`preservingTransfer_loop1` and `preservingTransfer_loop2`
(no `_correct` suffix; lines 3565, 3872). The plan's spec
§5.3 lists the names correctly (`preservingTransfer_loop1`,
`_loop2`, `_loop1_pc_bound`, `_loop2_pc_bound`), but the
plan's docstring template uses the `_loop1_correct`,
`_loop2_correct` variants which do not exist.

**Impact**: `Loops.lean`'s module docstring would name
non-existent declarations.

**Suggested fix**: Sync the docstring with the actual names
(`_loop1`, `_loop2`, `_loop1_pc_bound`, `_loop2_pc_bound`,
`_loop2_pc_strict_bound`).

### D14: Task 2 Step 4 fix-up overstates "open" remedy

**Where**: plan Task 2 Step 4 (lines 293–308).

**Defect**: The fix-up bullets say "Missing identifiers from
`GebLean.LawvereER`: add the appropriate `open` clause." The
likely missing identifiers come from `GebLean.ZeroTestURM`
(URMProgram, URMState, URMInstr, runFor, etc.), not
`GebLean.LawvereER` (which provides `ERMor1`, `ERMor1.interp`,
etc.). The executor following this hint would `open` the wrong
namespace.

**Impact**: Wasted debug cycles; in the worst case, an `open
GebLean.LawvereER` that shadows or shifts elaboration in an
unintended way.

**Suggested fix**: Update Task 2 Step 4 to mention
`open GebLean.ZeroTestURM` as the likely fix, alongside
LawvereER if needed.

### D15: Plan Task 7 contradicts plan Task 2/3/4/5/6 on the index file's final state

**Where**: plan Task 6 Step 6 (lines 980–988) vs Task 7
(lines 1021–1085).

**Defect**: Task 6 Step 6 says "After this step, the monolith
should retain only the original module docstring and the
imports (now five imports + the four submodule imports). All
declarations have been moved." Then Task 7 Step 1 overwrites
the file with a brand-new 5-import index plus a fresh
docstring.

This is fine, but there is a subtle issue: across Tasks 2–6
each task's Step 6 says "add forwarding import
`import GebLean.LawvereERKSim.<Submodule>`" to the monolith.
The plan never tells the executor to *also remove* the four
original imports (`GebLean.LawvereER`,
`GebLean.Utilities.ZeroTestURM`, `Mathlib.Data.Fintype.Basic`,
`Mathlib.Tactic.FinCases`) at any point — but Task 7's index
file does not include them. Task 7 Step 5's verification
demands "5 imports" (the submodule imports), not "5 imports +
the original four". If the executor sees 9 imports after
Task 6 Step 6 and the Task 7 overwrite drops them, that's
fine. But Task 6 Step 6's prose says "five imports + the
four submodule imports" (i.e. 9), and Task 7 Step 5 expects
5.

**Impact**: Minor confusion about intermediate vs final
state; resolved by Task 7's wholesale overwrite. But the
executor verifying intermediate state will see the discrepancy.

**Suggested fix**: Add a note to Task 6 Step 6 that "Task 7
will wholesale-overwrite this file, so the intermediate state
(nine imports + docstring) is transient; the canonical
import-only form is established in Task 7 Step 1." Alternatively,
remove the four original imports during Task 2 (or earlier) and
verify intermediate state cleanly throughout.

### D16: Anchor `/-- For \`compileFrag_comp\`'s \`i\`-th sub-block\`` is ambiguous

**Where**: plan Task 6 (anchor list at lines 884–895).

**Defect**: The anchor
`/-- For \`compileFrag_comp\`'s \`i\`-th sub-block\``
is used to demarcate a Comp range. The phrase
"For compileFrag_comp's i-th sub-block" is the start of
several docstrings in the monolith
(`ProgramEmbedsFragment_compileFrag_comp_fBody`,
`ProgramEmbedsFragment_compileFrag_comp_gsBody`,
`TransferLoopInstrs_compileFrag_comp_outputTransfer` at line
4174, `compileFrag_comp_subBlock_outputTransfer_correct` at
~line 7152, etc.). The plan should specify which occurrence
is intended.

**Impact**: Executor's anchor-based `Read` calls return
multiple matches; without disambiguation the executor cannot
unambiguously locate the start of the target range.

**Suggested fix**: Quote enough of the docstring's first line
to make each anchor unique (e.g.,
`/-- For \`compileFrag_comp\`'s \`i\`-th sub-block, the leading\``
vs `/-- For \`compileFrag_comp\`'s \`i\`-th sub-block, the trailing\``).
Better: list the exact first 60 characters of each anchor's
docstring.

### D17: Section A "1450 LOC" is misstated and Task 2 ranges contradict

**Where**: spec §3 and §4 row A; plan Task 2.

**Defect**: Spec §3 says Section A is `~1450 LOC` and §4 row A
says "1–1473 / ~1450 LOC". The monolith preamble (imports,
docstring) is lines 1–75; `namespace GebLean` starts at line
76. Section A's declarations live from line 76 to line 1473
inclusive — that's ~1398 LOC of declarations plus 75 LOC of
preamble = 1473. The "~1450" estimate is for the *whole
prefix* (including preamble), but the plan's task at line
196 says "monolith lines 76–1473" and at line 270 says "lines
78–1473". The actual Section A *content* (post-`namespace
LawvereERKSim` and the `open`) is lines 80–1473 = ~1394 LOC.

This is small and won't break a build, but Task 8 Step 2's
"Expected ranges: Compiler.lean ~1300–1600 lines" makes the
estimate fit.

**Impact**: Confusion only. Verifier sees the file size and
must reason which estimate matches.

**Suggested fix**: State that the "~1450 LOC" estimate
includes module docstring, imports, namespace, and `open`
clause as new file headers, and that the move's source range
is monolith lines 80–1473 (i.e., 1394 LOC of declarations).

### D18: jj `describe`/`new` workflow ambiguous on commit identity

**Where**: every task's Step 9 commit step (Tasks 2–6) and
Task 7 Step 6.

**Defect**: The plan uses
`jj describe -m "<message>"; jj new`. In a colocated jj
working-copy model, this names the *current* working-copy
commit and then creates a new empty one on top. But the
preceding step is `lake build`, which leaves files in the
working copy; `jj describe -m` operates on the working-copy
commit which already contains the changes. This is correct
*if* the working copy has been kept on a single commit
throughout the task. If the executor ran `jj new` in the
middle (perhaps after Step 4's build to "checkpoint" — the
plan does not say), the description would land on an empty
commit.

The plan never establishes that "all changes from one task
land in one working-copy commit". It just describes the
end-of-task commit.

**Impact**: An executor that uses `jj new` defensively between
steps could fragment the task into multiple commits, breaking
the one-concern-per-commit alignment.

**Suggested fix**: Add a `Conventions used by every move task`
bullet: "Each task lands as a single jj commit. Do not run
`jj new` between steps within a task. The Step 9
`jj describe`+`jj new` sequence names the accumulated commit
and starts the next task on a fresh empty working copy."

### D19: `lake build GebLean.LawvereERKSim.Compiler` target may not exist

**Where**: plan Task 2 Step 4 (line 296) and every per-task
isolation-build step.

**Defect**: The lakefile (`lakefile.toml`) declares one library
target `GebLean` with default target `["GebLean"]`. `lake
build GebLean.LawvereERKSim.Compiler` works only if lake
resolves module-path targets; in lake 4 this *does* work for
modules under the configured lib, but the plan should verify
this assumption or fall back to `lake build` (whole tree). The
plan also says "Iterate Step 4 until build is clean", implying
the executor iterates per-submodule, which is best done with a
narrow target.

**Impact**: If `lake build <module-path>` does not work in this
project's lake version, every per-task isolation build will
either build the whole tree (slower) or fail outright.

**Suggested fix**: Add a verification step at Task 1
(baseline-build) to confirm `lake build
GebLean.LawvereERKSim` works in this project's lake version,
and document the fallback to `lake build` if the
module-path target form is not supported. The CLAUDE.md memory
note "Always use lake build … never lake env lean" supports
using `lake build` but does not confirm module-path targets.

### D20: Task 8 verification omits CSLib axiom-allowlist check

**Where**: plan Task 8 vs spec §7.

**Defect**: Spec §7 verification list:

- whole-tree `lake build`;
- `lake test`;
- `scripts/check-axioms.sh` clean on each new submodule;
- per-declaration `lean_verify` axiom check.

Plan Task 8 Steps 1, 3, 4 cover three of these (build, lint,
markdownlint), but `lake test` is in Task 7 Step 3 (one task
earlier) and `scripts/check-axioms.sh` is in Task 7 Step 4
(also one task earlier). Task 8 doesn't independently re-run
them, which is fine, but Task 8 Step 3's reference to
`scripts/pre-commit.sh` (D12) is not actually equivalent.

More substantively: the spec §7 sample of `lean_verify`
flagship declarations includes `compileER_pre_stop_correct_comp`,
`compileER_runFor_comp`, `compileER_pre_stop_to_runFor`,
`compileER_runFor_zero/succ/proj/sub`, `transferLoop_correct`,
`preservingTransfer_correct`, `subInnerLoop_correct`.
Plan Tasks 4 and 6 cover all of these; plan Tasks 2–6 add
many more, but none of the per-task `lean_verify` lists
include `compileER_pre_stop_to_runFor` (Task 3 line 511 *does*
list it — OK). The spec-required samples are present, but
distributed across tasks rather than re-run at Task 8.

**Impact**: Minor. Distribution is fine if every commit goes
through, but a final "regression run" at Task 8 would catch
late breakage.

**Suggested fix**: Add a Task 8 Step that re-runs the spec §7
sample of `lean_verify` calls (a single bulleted list of 9
fully-qualified names) against the final tree to confirm
axiom hygiene end-to-end.

### D21: Task 6 sub-block "k=0 wrapper in 5854–6198 region" is geographically wrong

**Where**: plan Task 6 (lines 866–867).

**Defect**: Plan says "k=0 wrapper (`compileER_runFor_comp_k_zero`):
in the 5854–6198 region." The actual line is 5946. The
range 5854–6198 (per Task 6 line 864) also covers the
tail-variant lemmas (5866–5944, see D3), the rest of k_zero
(5946–6198), and *the start of `compileER_pre_stop_correct_atom_zero`*
which is at line 6208 — just outside. OK, line 6208 > 6198.
But the boundary at 6198 is exact only because of `private
theorem compileER_pre_stop_correct_atom_zero` declaration
at 6208 with prior comments/blank lines from 6199.
The plan's coarse-grained description ("approximately
5854–6198") doesn't acknowledge the interior structure: tail
variants (D3 conflict), then k_zero. An anchor-based extract
of "k=0 wrapper" alone (not 5854–6198) would be more precise.

**Impact**: Coupled with D3, this region is over-claimed for
Comp.

**Suggested fix**: Split the 5854–6198 range into:
(a) tail-variant lemmas → Embedding (per spec §5.2);
(b) k_zero wrapper (5946–6198) → Comp. Use anchors not line
ranges.

### D22: TOC entries do not match heading anchors after `'`

**Where**: spec §3 and elsewhere; plan TOC at plan lines 11–19.

**Defect**: Plan TOC entry
`(#task-6-create-complean-section-e-move--section-f-comp-wrapper)`
encodes the heading
`Task 6: Create \`Comp.lean\` (Section E move + Section F comp wrapper)`.
The doctoc convention strips backticks but preserves single
characters; both the plus sign and the space character become
hyphens in anchors. Anchor generation is consistent in most
renderers.

Spec TOC entries `(#52-embeddinglean-section-b--the-bridge-from-section-f)`
embed `--` (double hyphen) in the anchor where the heading has
`+`. Both files have the same convention. Doctoc is
auto-generated, so this is mostly correct, but the spec's
manual edits (e.g., backticks in headings) sometimes cause
anchor mismatches when re-run.

**Impact**: TOC link rot if doctoc is re-run with different
sanitization rules. Markdownlint passes either way.

**Suggested fix**: After applying any other fixes, re-run
`doctoc` on both spec and plan to canonicalise anchors.

### D23: Plan does not handle the `variable` scoping case

**Where**: Plan Task 2 Step 4 fix-up bullets; spec §8 risks
table row 3.

**Defect**: The monolith has no `variable` declarations at
file scope (only `open GebLean.ZeroTestURM`), so the
spec-risk-table mitigation ("Plan-time audit; explicit
re-`variable`-declaration per submodule where used") trivially
holds. The plan does not document this finding. An executor
encountering errors in Step 4 might waste time looking for
`variable` blocks that aren't there.

**Impact**: Minor; just documentation completeness.

**Suggested fix**: Add a Task 1 verification step:
"Confirm the monolith has no file-scope `variable` blocks
(`grep -c '^variable ' GebLean/LawvereERKSim.lean`; expected
0). If non-zero, halt and audit." The plan currently checks
the import count but not the `variable`/`open` count.

### D24: Plan never invokes the project's hook-allow-list mutating git policy

**Where**: Plan-wide (the task commit steps).

**Defect**: The project's `CLAUDE.md` § Hard rules require
that mutating git operations go via `jj`, gated by a
PreToolUse hook. The plan correctly uses `jj describe` /
`jj new`. However, the plan does not mention that `jj`
commands themselves may trigger the PreToolUse permission
prompt for certain forms (e.g., `jj git push`). The plan
explicitly does *not* push anywhere (which is correct), but
each task commit may trigger interactive prompts depending on
the hook's allow-list configuration.

**Impact**: Minor; executor will see prompts and either
approve or surface to the user, which matches the project's
human-gate rule.

**Suggested fix**: Add a Conventions note: "All jj operations
in this plan are local-only; no `jj git push`. If the
PreToolUse hook prompts, surface to user." No procedural
change needed; just an expectation-setter.

### D25: Empty `## Main statements` section in Compiler module docstring

**Where**: Plan Task 2 Step 1 (lines 218–249).

**Defect**: The Compiler.lean module docstring template lists
`## Main definitions` but no `## Main statements`. The
project's `.claude/rules/lean-coding.md` § Documentation
documents the required sections (title, summary, Main
definitions, Main statements, Implementation notes, References,
Tags). The Compiler.lean *does* contain provable statements
(e.g., `regBound_toRawOfBounded_le`,
`boundedBy_preservingTransfer`, `boundedBy_transferLoop`,
`regBound_reindexShift_le_offset_add`,
`boundedBy_compileFrag_comp_subBlock`,
`boundedBy_bsum_prologueBlock`, `boundedBy_bsum_zeroSweep`).
Omitting `## Main statements` from the docstring loses the
documentation contract for these.

**Impact**: Docstring incomplete; lean-coding rule violation.

**Suggested fix**: Add a `## Main statements` section to
Compiler.lean docstring template listing the boundedness
theorems.

### D26: `lake test` should run before commits, not only at Task 7

**Where**: Plan Task 7 Step 3 vs Tasks 2–6.

**Defect**: Plan defers `lake test` to Task 7 Step 3 only.
Each per-task commit (Tasks 2–6 Step 9) lands without
running tests. If a per-submodule extraction breaks a test
(unlikely since no test imports the monolith by name, but
possible if a test imports `GebLean.LawvereERKSim` and depends
on a `private` that got promoted to a public name that
shadows something), the breakage is hidden until Task 7.

**Impact**: Late discovery of test breakage forces rework
across multiple commits.

**Suggested fix**: Add `lake test` (or `lake test
GebLeanTests` if more narrowly targeted) to each Task 2–6
Step 8 before commit, or document why it is safe to defer.

## Summary of findings

- **Total defects**: 26 (D1–D26).
- **High-severity** (break execution or require non-trivial
  re-derivation by executor): D1, D2, D3, D4, D6, D7, D8,
  D9, D10, D13.
- **Medium-severity** (executor must intervene but plan
  guidance is partially correct): D5, D11, D12, D14, D15,
  D16, D17, D19, D20, D21, D25, D26.
- **Low-severity** (documentation polish or minor friction):
  D18, D22, D23, D24.

**Verdict**: plan needs another round.
