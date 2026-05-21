# Plan adversarial review — round 2

## Summary

Round 1's catalogue of name and structural defects (D1–D25)
has been substantially resolved. The atom pre-stop names now
carry the `_atom_` infix uniformly; `URMRaw.transferLoopLen`
and `URMRaw.preservingTransferLen` are corrected; the
"hyps" → "Instrs" rename is applied; the tail-variant lemmas
(`stateEmbedsFrag_step_tail`, `stateEmbedsFrag_runFor_tail`)
and `URMState.init_regs_zero_outside_inputs` are explicitly
routed to Embedding; the 6321–6606 PC-bound cluster is named
out and routed to Loops; the two Comp-specific dischargers
are explicitly assigned to Loops with rationale; the upstream
declarations previously misattributed to Embedding
(`URMProgram.WellBounded` etc.) are removed; the
`open GebLean.ZeroTestURM` clause is required in every
submodule header template; the missing `## Main statements`
section in Compiler.lean is added; `pre-push.sh` replaces the
non-existent `pre-commit.sh`. Round-1 D26 (per-task vs
Task-7 `lake test`) is still unaddressed and is now
re-affirmed below.

What remains is a small cluster of off-by-N source-range
boundaries (spec §4 row Atoms's "5665" should be "5655" or
"5654"; spec §5.2 line "5210" for `URMState.init_regs_zero_outside_inputs`
refers to the `theorem` keyword line, while the docstring it
must move with starts at 5201; analogous five- to nine-line
docstring undercoverage at every Section-D and Atoms-pre-stop
sub-range boundary). The plan's actual move steps rely on
anchors and reverse-line-number deletes, so most of these
boundary errors are recoverable at execution time, but the
spec §4 table is normative and should be tightened. One new
issue (D27 below) concerns Loops's range and its overlap with
the `compileER_runFor_sub` docstring; a second (D28) concerns
the `compileER_runFor_proj` docstring start.

## Verification of round-1 defects

All declaration names listed in spec §5.1–§5.5 were
`grep`-verified against the monolith at the claimed line
numbers. Every name and line resolved correctly. The
round-1 closure status is:

- D1 (atom pre-stop names) — FIXED. Spec §5.4 and plan
  Task 5 Step 8 list all four as
  `compileER_pre_stop_correct_atom_{zero,succ,proj,sub}`.
- D2 (ZeroTestURM upstream decls in §5.2) — FIXED. Spec
  §5.2 lists the bridge's upstream dependencies separately
  in the prose paragraph after the declaration list;
  upstream names are gone from the Embedding inventory.
- D3 (tail-variant lemmas dropped) — FIXED. Spec §5.2
  lists `stateEmbedsFrag_step_tail` (5866) and
  `stateEmbedsFrag_runFor_tail` (5903) under Embedding.
  Plan Task 3 Step 4 extracts lines 5866–5944.
- D4 (Comp dischargers buried in Loops) — RESOLVED BY
  EXPLICIT POLICY. Spec §5.3 documents the decision to
  keep `PreservingTransferInstrs_compileFrag_comp_inputCopies`
  (2990) and `TransferLoopInstrs_compileFrag_comp_outputTransfer`
  (4187) in Loops to avoid promoting the
  `preservingTransferInstrs` / `transferLoopInstrs`
  private structures; the plan Task 4 docstring template
  lists them under "comp-layout dischargers". The
  per-file-organisation cost (`Loops.lean` carries
  comp-specific lemmas) is acknowledged.
- D5 (transferLoop.size / preservingTransfer.size) — FIXED.
  Spec §5.1 now reads `URMRaw.transferLoopLen` and
  `URMRaw.preservingTransferLen`.
- D6 (phantom Compiler decls) — FIXED. Spec §5.1's
  declaration list now matches every monolith name
  verbatim; `lastInstr_isStop_of_concat`, `gsBlockSize`,
  the `reindexShift_bounded` phantoms,
  `compileFrag_comp_subBlock_bounded`,
  `bsum_prologueBlock_bounded`, `bsum_zeroSweep_bounded`,
  and `compileER_numRegs_bound` are gone, replaced with
  `URMInstrRaw.toBoundedArray_back?_of_last_stopR`,
  `boundedBy_compileFrag_comp_subBlock`,
  `boundedBy_bsum_prologueBlock`,
  `boundedBy_bsum_zeroSweep`, and `compileER_numRegs`.
- D7 (hyps → Instrs and 6321–6606 cluster) — FIXED. Spec
  §5.3 uses `preservingTransferInstrs`,
  `transferLoopInstrs`, `subInnerLoopInstrs`; the
  6321–6606 cluster has all four PC-bound lemmas
  enumerated; spec §4 row Loops lists "6321–6606" as a
  sub-range.
- D8 (inputCopies group) — FIXED. Spec §5.5 lists
  `inputCopies_disj` as a structure,
  `inputCopies_prefix_correct` (6653), and
  `inputCopies_prefix_pc_strict_bound` (6785); the
  phantom `disj_triple_for_reg` is gone.
- D9 (Section A line 1473) — FIXED. Plan Task 2 uses a
  single source range 82–1473 (Step 2); plan Task 2 Step
  1 writes namespace+open clauses freshly in the header.
- D10 (`open GebLean.ZeroTestURM` unmentioned) — FIXED.
  Every per-task header template (Tasks 2–6 Step 1)
  includes `open GebLean.ZeroTestURM`; the conventions
  block at the top of the plan documents it as required.
- D11 (`phase_i1_post` / `phase_i2_post` as statements) —
  FIXED. Spec §5.5 marks them as `private structure`;
  plan Task 6 Step 1 docstring lists them under `## Main
  definitions`.
- D12 (`pre-commit.sh` doesn't exist) — FIXED. Plan Task
  8 Step 3 calls `scripts/pre-push.sh`.
- D13 (Loops helper names) — FIXED. Plan Task 4 Step 1
  docstring uses `preservingTransfer_loop1`,
  `_loop1_pc_bound`, `_loop2`, `_loop2_pc_bound`,
  `_loop2_pc_strict_bound`.
- D14 (Task 2 Step 4 mentions wrong namespace) — FIXED.
  Plan Task 2 Step 4 names `GebLean.ZeroTestURM` and
  `GebLean.LawvereER` as the two likely open clauses,
  with `ZeroTestURM` as the primary fix.
- D15 (intermediate vs final import state) — FIXED. Plan
  Task 6 Step 6 notes "intermediate file state has nine
  imports … Task 7 collapses to five" and that the
  transient excess is fine.
- D16 (ambiguous anchor `For \`compileFrag_comp\`'s
  \`i\`-th sub-block\``) — FIXED. Plan Task 6's anchor
  list uses theorem-name anchors
  (`^private theorem compileFrag_comp_subBlock_length`,
  `^private theorem ProgramEmbedsFragment_compileFrag_comp_fBody`,
  etc.), each of which is unique in the monolith.
- D17 (Section A "1450 LOC" estimate) — FIXED (silently).
  Plan Task 8 Step 2 lists Compiler.lean expected range
  1300–1600 lines; spec §3 keeps the rough ~1400 LOC
  figure.
- D18 (`jj describe`/`new` workflow) — FIXED. Plan
  conventions block now reads "Each task lands as a
  single jj working-copy commit. Do not run `jj new`
  between steps within a task."
- D19 (narrow `lake build <module-path>` target) — FIXED.
  Plan Task 1 Step 6 verifies the narrow target works
  and documents the fallback to `lake build` (whole
  tree) if it does not.
- D20 (Task 8 omits §7 sample re-run) — FIXED. Plan Task
  8 Step 2.5 explicitly re-runs `lean_verify` on the
  spec §7 flagship sample.
- D21 (k=0 wrapper region overlap with tail variants) —
  FIXED. Plan Task 6 Source ranges row 2 reads
  "k=0 wrapper: 5945–6198" with a note that 5866–5944 is
  the tail-variant range that belongs to Embedding.
- D22 (TOC anchors) — REGENERATED. Both spec and plan
  TOCs are doctoc-managed; the anchors match the
  headings.
- D23 (`variable` scoping case) — FIXED. Plan Task 1
  Step 5 includes `grep -c "^variable " …; expected 0`
  and instructs halt if non-zero.
- D24 (mutating-git hook policy) — FIXED. Plan
  conventions block notes "All jj operations in this
  plan are local-only; no `jj git push`. The pre-tool-use
  hook for mutating git operations may prompt; surface
  to user if needed."
- D25 (Compiler `## Main statements` section empty) —
  FIXED. Plan Task 2 Step 1 docstring includes a
  `## Main statements` section listing the boundedness,
  arithmetic, and indexing theorems.

## Remaining defects

### D27: Atoms sub-range starts at 5665, cutting compileER_runFor_sub docstring

**Where**: spec §4 row Atoms (sub-range `5665–5853`); plan
Task 4 Step 5 deletion list ("subInnerLoop block (original
5414–5664; the sub-runFor at 5665+ stays for Task 5)"); plan
Task 5 Step 2 row 4 ("sub `_runFor`: extract lines
5654–5853").

**Defect**: `compileER_runFor_sub`'s docstring (the
`/-- Correctness of compileER on .sub ...`) starts at
**monolith line 5655** (theorem keyword at 5663). The
preceding declaration `subInnerLoop_correct_pc_bound` ends
at ~line 5653 with a blank line at 5654. So Atoms's natural
start boundary for the sub-runFor sub-range is **5654 or
5655**, not 5665. Symmetrically, Loops's natural end
boundary for the `subInnerLoop` block is **5653 or 5654**,
not 5664. Spec §4 misnames both boundaries (it places them
~10 lines past the actual gap).

Plan Task 5 Step 2 row 4 reads "sub `_runFor`: extract lines
**5654**–5853" — which is correct and contradicts spec §4
row Atoms which reads "5665–5853". Plan Task 4 Step 5 row
2 reads "subInnerLoop block (original 5414–**5664**); the
sub-runFor at **5665+** stays for Task 5" — which is
incorrect and contradicts plan Task 5 Step 2.

**Impact**: An executor consulting spec §4 to verify their
extracts will see Loops's claim ranging 5414–5664 and Atoms's
starting at 5665, missing the ten-line range 5654–5664
entirely. An executor following plan Task 4 Step 5 will
delete 5414–5664 from the monolith, which includes lines
5655–5664 — the first ten lines of the `compileER_runFor_sub`
docstring. Plan Task 5 Step 2's "5654–5853" extract then
either re-captures the (already deleted) docstring lines
from a stale anchor or, more likely, the executor will
notice the inconsistency mid-task and have to debug. The
plan's anchor `^private theorem compileER_runFor_sub` will
correctly locate line 5663, but the docstring above (lines
5655–5662) will already be in Loops's extract.

**Suggested fix**: In spec §4 row Atoms, change `5665–5853`
to `5655–5853`. In spec §4 row Loops, change `5414–5664` to
`5414–5654` (or `5414–5653`). In plan Task 4 Step 5 row 2,
change "5414–5664" to "5414–5654" and remove "the sub-runFor
at 5665+" or change to "5655+".

### D28: `compileER_runFor_proj` docstring starts at 5233, not 5237

**Where**: spec §4 row Atoms (sub-range `5237–5413`); plan
Task 5 Step 2 row 3 ("`compileER_runFor_proj`: extract lines
5237–5413"); plan Task 5 Step 5 row 4 (`5237–5413 (proj
_runFor)`).

**Defect**: The `compileER_runFor_proj` docstring
(`/-- Correctness of compileER on .proj i ...`) starts at
**monolith line 5233**, four lines before line 5237 (where
the theorem keyword appears). The preceding declaration
`URMState.init_regs_zero_outside_inputs` ends at line
~5232 (`rw [h_none]` followed by a blank line). Spec §4 and plan
Task 5 cut off the docstring by starting the extract at 5237.

**Impact**: If an executor follows the plan's literal sed
range, the resulting `Atoms.lean` will have
`private theorem compileER_runFor_proj` with no docstring
attached, violating the spec §1 "docstrings do not change"
contract. The executor will likely notice (orphan docstring
fragment is visible) and fix by hand, but the spec/plan
contract is broken.

**Suggested fix**: Change `5237–5413` to `5233–5413` in spec
§4 row Atoms, plan Task 5 Step 2 row 3, and plan Task 5
Step 5 row 4.

### D29: `URMState.init_regs_zero_outside_inputs` docstring start is 5201, not 5210

**Where**: spec §4 row Embedding (sub-range `5210–5236`);
spec §5.2 line annotation `(5210)`; plan Task 3 Step 3
expected output (`Expected: \`5210:private theorem
URMState.init_regs_zero_outside_inputs\``); plan Task 3 Step
3 prose ("typically 5203–5236").

**Defect**: The `URMState.init_regs_zero_outside_inputs`
docstring (`/-- For a URMProgram whose inputRegs maps slot
j ...`) starts at **monolith line 5201**, not 5203 or
5210. The preceding declaration
`URMState.init_regs_inputRegs` ends at ~line 5199
(`rw [List.find?_finRange_inputRegs ...]`), followed by a
blank at 5200. Spec §4 row Embedding range `5210–5236`
skips the entire docstring (lines 5201–5209).

Compounding: spec §4 row Atoms includes `5237–5413` which
covers the proj_runFor block (per D28, this should start at
5233). Spec §4 row Embedding includes `5210–5236` (per this
finding, should start at 5201). The gap 5200–5200 between
Atoms's first sub-range `5157–5209` and the next sub-range
`5237–5413` would, with corrected boundaries, become
Atoms's `5157–5200`, Embedding's `5201–5232`, Atoms's
`5233–5413`. Spec §4 row Atoms's first sub-range `5157–5209`
is too long by nine lines (covers 5201–5209 which is part of
the Embedding docstring).

**Impact**: The plan Task 3 Step 3 prose acknowledges
imprecision ("typically 5203–5236, but confirm visually that
the next declaration line begins with `private theorem
compileER_runFor_proj`") and instructs the executor to
verify. The plan's mitigation is functional, but the spec
§4 table — which the plan's per-task source-range
documentation cites — is empirically wrong for the
Embedding/Atoms boundary across nine lines on both sides.

**Suggested fix**: Change spec §4 row Embedding sub-range
`5210–5236` to `5201–5232`. Change spec §4 row Atoms first
sub-range `5157–5209` to `5157–5200`. Plan Task 3 Step 3 can
keep its anchor-based "confirm visually" prose; update the
expected `sed` start to `5201` rather than `5203`.

### D30: Round-1 D26 (per-task `lake test`) still unaddressed

**Where**: Plan Task 7 Step 3 (`lake test`) vs Tasks 2–6
Step 8 (no test invocation).

**Defect**: Round-1 D26 flagged that `lake test` runs only
once, at Task 7 Step 3, after all five submodule extractions
are complete. Tasks 2–6 commit each submodule extraction
without running the test suite. If any per-submodule
extraction breaks a test (low risk per D26, since no test
imports the monolith by name), the breakage surfaces only
at Task 7. The fix would be ~10 LOC: add a Step 8.5 (or
amend Step 8) to each of Tasks 2–6 invoking `lake test`
before commit. The current plan does not do this; the
round-2 spec/plan does not mention D26 in any commit, and
D26 is unaddressed.

**Impact**: Same as round 1. Low probability of test
breakage; if it occurs, the executor must back out several
commits to bisect.

**Suggested fix**: Add to each Tasks 2–6 Step 8: "Run
`lake test 2>&1 | tail -10`; expected clean. If tests fail,
halt and surface the failing test to the user before
proceeding to Step 9 (commit)."

Alternatively (and acceptable): document in plan §
"Conventions" that the test-suite-on-every-commit policy is
deferred to Task 7 because no `GebLeanTests/` file imports
`GebLean.LawvereERKSim` declarations directly, so test
breakage from this refactor is not possible by construction.
That assertion should be verified by `grep -r "LawvereERKSim"
GebLeanTests/` at Task 1 baseline; the current plan does
not verify it.

### D31: Spec §5.2 line annotations conflate keyword and docstring start

**Where**: spec §5.2 line annotations `(5210)`, `(5866)`,
`(5903)`, `(11830)`.

**Defect**: Spec §5.2's line annotations attach to the
**theorem keyword line** (`private theorem X`), not the
docstring start. This is consistent with how §5.1, §5.3,
§5.4, §5.5 also annotate. But the move task must extract
the docstring **with** the theorem (the docstring is part
of the declaration). The plan Task 3 Step 3 acknowledges
this in prose ("Find its docstring start (a few lines
earlier)"), but the spec §4 sub-ranges then re-use the
theorem-keyword line for the range start (e.g., `5210–5236`
for `URMState.init_regs_zero_outside_inputs`), which
silently amputates the docstring.

This is the systematic source of D28 and D29: both arise
because spec §4 sub-ranges start at the theorem-keyword line
rather than the docstring-start line.

**Impact**: Every spec §4 sub-range whose start coincides
with a declaration's theorem-keyword line silently
amputates that declaration's docstring. Affected ranges:

- Embedding: `5210–5236` (drops docstring 5201–5209,
  ~9 lines).
- Embedding: `11821–11895` (this one *is* docstring-anchored
  — `compileER_pre_stop_to_runFor` docstring starts at
  line 11820 or 11821, theorem keyword at 11830; spec is
  approximately correct here).
- Atoms: `5237–5413` (drops `compileER_runFor_proj`
  docstring 5233–5236, ~4 lines).
- Atoms: `5665–5853` (drops `compileER_runFor_sub`
  docstring 5655–5664, ~10 lines).
- Atoms: `6199–6325` (this one starts at the docstring;
  `compileER_pre_stop_correct_atom_zero` docstring begins
  at 6199, theorem keyword at 6208 — correct).
- Atoms: `7209–8023` (starts at
  `compileER_pre_stop_correct_atom_succ` docstring 7209,
  theorem keyword 7215 — correct).
- Loops: `6321–6606` (starts at
  `preservingTransfer_loop2_pc_strict_bound` docstring
  6321, theorem keyword 6326 — correct).
- Loops: `5414–5664` (per D27, end should be 5653 or 5654).

**Suggested fix**: For every spec §4 sub-range, replace the
range start with the docstring-start line (i.e., the line
of the leading `/--` of the first declaration in the
sub-range), and replace the range end with the line just
before the next sub-range or section's leading `/--`. The
plan's anchor-based extraction already does this in prose,
so executor behaviour will be correct; the fix is to make
the spec §4 table match.

### D32: Plan does not verify `GebLeanTests/` does not transitively name moved declarations

**Where**: Plan Task 1 (no step), Plan Task 7 Step 3.

**Defect**: The plan assumes the refactor is test-neutral
because no test imports the monolith "by name", but does
not verify this at Task 1 baseline. The check
`grep -rn "LawvereERKSim" GebLeanTests/` would confirm.
If a test does refer to a now-private-promoted declaration
by fully-qualified name, the rename surface (`private` →
public) might shadow or change a `simp` lemma's
applicability. Probability is low; the verification cost is
~one grep.

**Impact**: Defensive completeness; without this check,
round 1 D26's risk is unbounded.

**Suggested fix**: Add a Task 1 Step 5.5 (or fold into Step
5): "`grep -rn 'LawvereERKSim' GebLeanTests/ 2>/dev/null
| tail -20`; expected: 0 matches, or only matches in test
files that import `GebLean.LawvereERKSim` as a whole
module (no by-name references to currently-`private`
declarations). If a private declaration is named, document
the consumer and confirm the promotion in Tasks 2–6 will
not change test behaviour."

### D33: compileFrag_sub at 439 and compileFrag_sub_inputRegs ordering (confirmation)

**Where**: spec §5.1 (rows for `compileFrag_sub_inputRegs`
and `compileFrag_sub`).

**Defect**: Spec §5.1 has rows
`compileFrag_sub_inputRegs (423, def)` and
`compileFrag_sub (439, def)`. Both verified empirically:
`compileFrag_sub_inputRegs` at line 423, `compileFrag_sub`
at line 439. The ordering in spec §5.1 matches the
monolith.

This is not a defect; this entry exists to confirm the
verification.

## Summary of findings

- **Total new defects**: 6 (D27–D32). D33 is a
  verification confirmation, not a defect.
- **High-severity** (blocks unambiguous execution): D27
  (Atoms/Loops boundary mis-stated by ~10 lines on a
  declaration boundary), D28 (proj_runFor docstring
  amputation), D29 (init_regs_zero docstring
  amputation), D31 (systematic root cause of the
  three docstring-amputation issues).
- **Medium-severity** (executor will notice but plan is
  formally wrong): D30 (carried over from round 1, still
  unaddressed).
- **Low-severity** (defensive completeness): D32.

Round-1 closure: 25 of 26 defects resolved; D26 carried
forward as D30. The substantive new findings are all
boundary-arithmetic errors in spec §4's range table that
arise from a single root cause (D31): the table attaches
sub-range starts to theorem-keyword lines rather than
docstring-start lines. The plan's per-task anchor-based
extraction recovers from these in execution-time prose, but
the normative table is empirically wrong at four boundaries
totalling ~23 lines of misallocation.

**Verdict**: Plan close to ready. One more revision pass
fixing the spec §4 table boundaries (D27, D28, D29, D31)
and addressing D30 (decide per-task `lake test` policy)
would clear the boundary class of defects. Plan Task 5 Step
2 already uses the correct boundary for sub `_runFor`
(5654), so the substantive risk is the discrepancy between
spec §4 and plan Task 4 Step 5 (D27). Recommend one further
revision round, primarily a spec §4 table rewrite.
