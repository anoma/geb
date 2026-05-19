# Plan adversarial review — round 3

## Summary

Round 2 closure: D27 (Atoms/Loops sub-runFor boundary
at 5654/5655), D28 (`compileER_runFor_proj` docstring
at 5233), D29 (`URMState.init_regs_zero_outside_inputs`
docstring at 5201), D31 (the systematic docstring-
amputation root cause), D30 (`lake test` policy), and
D32 (`grep GebLeanTests/` verification) are all
formally addressed. The plan's Task 5 Step 2 ranges
match the user-stated target
`4917–5156, 5157–5200, 5233–5413, 5655–5853,
6199–6325, 7209–8023`; Task 3 Step 3-5 ranges match
`5201–5232, 5854–5944, 11820–11895`; Task 4 Step 2
ranges match `2956–4915, 5414–5654, 6320–6606`; Task 6
Step 2 ranges match
`2138–2955, 5945–6198, 6607–7208, 8024–11819,
11896–11940`. Plan Task 1 Step 7 narrows to
`GebLeanTests/`, which is empirically the only test
directory and the only `.lean` consumer of
`LawvereERKSim`.

What was *not* fixed in round 2 is the round-2 reviewer's
core finding (D31): the spec §4 table still attaches
several sub-range starts to lines that are blank lines
or theorem-keyword lines rather than the leading `/--`
of the first declaration in the sub-range. The round-2
fix re-stated the rule ("Each sub-range start equals
the line of the leading `/--`") in the spec preamble
but did not update the table to satisfy it. Concrete
verification against the monolith reveals at least
seven sub-range boundaries that violate the stated
rule, plus one direct overlap of 6 lines between Atoms
and Loops. The plan inherits these table errors and
propagates them into the per-task extraction prose.

The plan is *operationally close to working* because
each task's Step 2 / Step 5 uses anchors (declaration
keyword names) to re-derive line numbers at execution
time, and several anchor-based steps will land on the
correct lines despite the table being wrong. But the
spec's table is normative for documentation purposes,
and the cumulative cross-checking the user requested
(union of sub-ranges) reveals defects that the plan
must address before execution.

## Verification of round-2 defects

All boundary line numbers were verified against the
monolith at commit `a1ff2ff7` by `sed -n '<line>p'`.

- D27 (Atoms/Loops boundary at 5654/5655) — FIXED.
  Spec §4 row Atoms reads `…, 5655–5853, …`; row
  Loops reads `…, 5414–5654, …`. L5654 is blank;
  L5655 is `compileER_runFor_sub`'s docstring `/--`.
  Plan Task 4 Step 5 row 2 deletes 5414–5654; Plan
  Task 5 Step 2 row 4 extracts 5655–5853. Consistent.
- D28 (`compileER_runFor_proj` docstring at 5233) —
  FIXED. Spec §4 row Atoms reads `…, 5233–5413, …`.
  L5233 is `/-- Correctness of compileER on .proj i`.
  Plan Task 5 Step 2 row 3 uses 5233–5413.
- D29 (`URMState.init_regs_zero_outside_inputs`
  docstring at 5201) — FIXED. Spec §4 row Embedding
  reads `…, 5201–5232, …`. L5201 is the docstring
  start; L5232 is blank.
- D30 (per-task `lake test`) — RESOLVED VIA POLICY.
  Plan Task 1 Step 7 verifies `grep -rn LawvereERKSim
  GebLeanTests/`; expected 0 matches. The plan
  documents that this verification justifies deferring
  `lake test` to Task 7 Step 3. Empirically:
  `grep -rn 'LawvereERKSim' /home/terence/git-
  workspaces/geb/geb-lean --include='*.lean'`
  returns *only* the monolith's own `namespace
  LawvereERKSim` (line 78) and `end LawvereERKSim`
  (line 11941). No test file or other `.lean` consumer
  references the namespace. The deferral is sound.
- D31 (systematic docstring-amputation) — PARTIALLY
  ADDRESSED. The spec preamble after the §4 table now
  states the rule ("Each sub-range start equals the
  line of the leading `/--`"). But the table itself
  contains at least seven boundaries that violate the
  rule (see new defects D34, D35, D36 below).
- D32 (verify `GebLeanTests/` doesn't transitively
  name moved decls) — FIXED. Plan Task 1 Step 7 is
  the verification, with halt instructions if matches
  are found.

## Remaining defects

### D34: Sub-range boundaries violate the stated docstring rule (recurrence of D31)

**Where**: Spec §4 table; plan Tasks 3–6 extraction
ranges that cite the table verbatim.

**Defect**: Spec §4's preamble states "Each sub-range
start equals the line of the leading `/--` of the
first declaration in the sub-range (so the docstring
travels with the declaration). Each sub-range end
equals the line just before the next sub-range or
section's leading `/--` (typically a blank line)."

Verified violations (line numbers from monolith at
commit `a1ff2ff7`):

| Sub-range | Stated start | Actual `/--` line | Off by |
| --- | --- | --- | --- |
| Atoms second `5157–5200` | 5157 | 5152 (`/-- Auxiliary: (List.finRange a).find?`) | -5 |
| Embedding bridge `11820–11895` | 11820 | 11821 (`/-- Generic bridge from the existential pre-stop`) | +1 |
| Loops PC-bound `6320–6606` | 6320 | 6321 (`/-- Strict per-step PC bound for preservingTransfer_loop2`) | +1 |
| Comp `6607–7208` | 6607 | 6603 (`/-- Sum of v over a prefix Fin m of Fin a`) | +4 |

`sed -n '5157p'` returns `private theorem
List.find?_finRange_inputRegs ...` (keyword line, not
docstring start; 5 lines after the docstring at 5152).

`sed -n '11820p'` returns blank; L11821 is the bridge
docstring.

`sed -n '6320p'` returns blank; L6321 is the
`preservingTransfer_loop2_pc_strict_bound` docstring.

`sed -n '6607p'` returns `private def vPrefixSum
{a : ℕ} (v : Fin a → ℕ) : ℕ → ℕ` (keyword line, not
docstring); L6603 is `/-- Sum of v over a prefix
Fin m of Fin a`.

The mirror-image end-boundary errors (the previous
sub-range's end runs into the next declaration's
docstring) follow mechanically:

| Sub-range | Stated end | Should end at | Cause |
| --- | --- | --- | --- |
| Atoms first `4917–5156` | 5156 | 5151 | overlaps 5152–5156, which is `List.find?_finRange_inputRegs`'s docstring |
| Embedding `5854–5944` | 5944 | 5932 | overlaps 5933–5944, which is `compileER_runFor_comp_k_zero`'s docstring (Comp content) |
| Loops first `2956–4915` | 4915 | 4916 | drops the blank line at 4916 (gap, not overlap) |
| Atoms zero pre-stop `6199–6325` | 6325 | 6320 (or 6319) | overlaps 6321–6325, which is `preservingTransfer_loop2_pc_strict_bound`'s docstring (Loops content) |
| Loops PC-bound `6320–6606` | 6606 | 6602 | overlaps 6603–6606, which is `vPrefixSum`'s docstring (Comp content) |
| Comp `8024–11819` | 11819 | 11820 | drops the blank line at 11820 (gap, not overlap) |

The "Atoms `6199–6325` vs Loops `6320–6606`" pair
also produces a direct *overlap* of 6 lines
(6320–6325) — see D35.

The "Embedding `5854–5944` vs Comp `5945–6198`" pair
silently absorbs 12 lines (5933–5944) of
`compileER_runFor_comp_k_zero`'s docstring into the
Embedding range. If the plan extracts 5854–5944 to
`Embedding.lean` per spec §4, the k=0 wrapper's
docstring will be split across two files, breaking
the spec §1 "docstrings do not change" contract.

**Impact**: An executor who follows the spec §4 table
literally produces submodules with amputated and/or
duplicated docstrings. The plan partially recovers
because each task's Step 2 uses anchor-based prose
(e.g., "Verify the extract begins with the docstring
`/-- Generic bridge from the existential pre-stop form`")
or theorem-keyword anchors. But the spec is normative
and the per-task numeric ranges in the plan still
match the broken spec values.

Specific plan consequences:

- Plan Task 3 Step 5 says `sed -n '11820,11895p' >
  /tmp/emb_bridge.lean`. This includes one leading
  blank line (11820) before the docstring (11821).
  Harmless (blank line at the top of the extracted
  block won't affect Lean parsing), but the boundary
  is wrong per the rule.
- Plan Task 4 Step 5 anchors PC-bound cluster start
  to `^private theorem
  preservingTransfer_loop2_pc_strict_bound` (L6326);
  the docstring (L6321) is *not* in the extract
  unless the anchor-based logic includes it. The
  Read-and-extract via anchor will likely include
  L6321 if the executor reads the preceding 5 lines,
  but the deletion range "original 6320–6606" in
  Step 5 *does* sweep up L6320 (blank) and L6321–6325
  (docstring). Plan Task 5 Step 5 deletes "6199–6325"
  which *also* sweeps L6321–6325 — they overlap.
- Plan Task 5 Step 2 row 2 extracts `5157–5200`,
  which begins at the `private theorem` keyword for
  `List.find?_finRange_inputRegs` and therefore does
  *not* extract that declaration's docstring (lines
  5152–5156, which the plan Task 5 row 1 sweeps into
  the previous "zero+succ" extract at 4917–5156).

**Suggested fix**: Update spec §4 sub-ranges to
satisfy the stated rule:

```text
Compiler:  76–1473
Embedding: 1474–2137, 5201–5232, 5854–5932, 11821–11895
Loops:     2956–4916, 5414–5654, 6321–6602
Atoms:     4917–5151, 5152–5200, 5233–5413, 5655–5853,
           6199–6320, 7209–8023
Comp:      2138–2955, 5933–6198, 6603–7208,
           8024–11820, 11896–11940
```

(End boundaries are the line just before the next
sub-range's docstring or section heading. Verify
each by `sed -n '<line>p'` against the monolith.)

Update plan Tasks 3–6 Step 2 (extraction) and Step 5
(deletion) numeric ranges in lockstep with the spec
table.

### D35: Atoms and Loops sub-ranges overlap at 6320–6325 (6 lines)

**Where**: Spec §4 row Atoms (`6199–6325`); row Loops
(`6320–6606`); plan Task 4 Step 5 row 1
(delete 6320–6606); plan Task 5 Step 5 row 2
(delete 6199–6325).

**Defect**: Spec §4 stipulates Atoms `6199–6325` and
Loops `6320–6606`. These overlap on lines 6320–6325.
The content at L6320 is blank; L6321–6325 is the
docstring of `preservingTransfer_loop2_pc_strict_bound`
(which is a Loops declaration).

If the plan is executed in order (Task 4 before Task
5), Task 4 Step 5 deletes original 6320–6606 first.
After this deletion, the monolith no longer contains
lines 6320–6325. Task 5 Step 5 then attempts to
delete original 6199–6325, but the anchor-based
re-derivation should locate the new boundary at the
end of `compileER_pre_stop_correct_atom_zero`'s body
(now adjacent to whatever was at original 6607).

The plan's anchor for the end of Atoms `_atom_zero` is
not explicitly listed; the plan Task 5 Step 5 reads
"6199–6325" verbatim from the spec table. If an
executor uses the literal range, the second deletion
either fails (range past EOF after Task 4 deletion)
or silently drops 6 lines that no longer exist.

The Atoms zero pre-stop range should end at the line
just before the next sub-range's docstring (L6321),
i.e., at L6320. The corrected Atoms range is
`6199–6320` (or `6199–6319` if blank-line-exclusion
is preferred). With the corrected boundaries, Atoms
ends at 6320 and Loops starts at 6321; no overlap.

**Impact**: Same as D34. Plan executor will recover
via anchor-based re-derivation but the table is wrong
and the plan inherits the wrong numbers.

**Suggested fix**: Same as D34's table revision.

### D36: Spec §4 Atoms is one range; plan Task 5 splits into two pieces inconsistently

**Where**: Spec §4 row Atoms; plan Task 5 Step 2.

**Defect**: Spec §4 row Atoms enumerates *five*
sub-ranges: `4917–5200, 5233–5413, 5655–5853,
6199–6325, 7209–8023`. Plan Task 5 Step 2 lists *six*
extractions: `4917–5156, 5157–5200, 5233–5413,
5655–5853, 6199–6325, 7209–8023`. The plan splits
Atoms's first range at the boundary 5156/5157, which
is the `List.find?_finRange_inputRegs` declaration's
keyword line (its docstring is at 5152).

The split itself is fine (it isolates the
zero+succ runFor declarations from the proj helpers),
but the spec doesn't reflect it, and the boundary
(5156/5157) violates the docstring rule (D34). With
the rule applied, the correct split is at 5151/5152.

Plan Task 5 Step 5 deletion list lists the
*six* ranges in reverse order, matching Step 2. But
spec §4's *five*-range Atoms means the spec table is
slightly out of sync with the plan even ignoring D34.

**Impact**: Documentation inconsistency between spec
and plan. An executor checking the plan against the
spec table sees six extractions but five sub-ranges,
and must decide which is authoritative.

**Suggested fix**: Either add the 5151/5152 split to
spec §4 row Atoms (preferred — keeps spec authoritative
and aligned with the plan), or collapse plan Task 5
into five extractions (`4917–5200, 5233–5413,
5655–5853, 6199–6320, 7209–8023`). The former is
mechanically simpler; the latter reduces extraction
count by one.

### D37: Spec §4 boundary rule preamble does not match the table boundary semantics

**Where**: Spec §4 preamble after the table.

**Defect**: The preamble after the table states the
docstring-anchored rule (D34's "Each sub-range start
equals the line of the leading `/--`..."). The table
above the preamble doesn't satisfy that rule
(D34 lists seven violations). The result is internal
inconsistency: a reader applies the rule to compute
sub-range boundaries and gets different numbers from
the ones the table claims.

**Impact**: A reviewer cross-checking the spec
internally cannot tell which of (table, rule) is
authoritative. Round 2 fixed three of these (5201
for Embedding, 5233 for Atoms proj_runFor, 5655 for
Atoms sub_runFor) but missed others.

**Suggested fix**: Update the spec §4 table so every
entry satisfies the preamble rule. After the update,
add a verification note: "Verified at commit
`a1ff2ff7` by `sed -n '<line>p'` against the
monolith." The remaining violations are at:
5157→5152, 5156→5151, 5944→5932, 11820→11821, 6320→6321,
6606→6602, 6607→6603, 6325→6320, 4915→4916, 11819→11820.

### D38: No coverage check for the file preamble (lines 1–75)

**Where**: Spec §4; plan Task 7 (index overwrite).

**Defect**: The spec §4 table covers lines 76–11940
collectively (per the docstring rule, Compiler starts
at 76 = `namespace GebLean`). Lines 1–75 (the
monolith's existing module docstring) are not
explicitly enumerated. The plan handles them in Task
7 Step 1 by wholesale-overwriting the file with a
new index-only docstring; the existing module
docstring at 1–75 is discarded.

This is correct, but neither the spec nor the plan
explicitly accounts for lines 1–75. A reviewer
computing the union of spec §4 sub-ranges to verify
coverage will see lines 1–75 uncovered. The plan
documents in Task 2 Step 5 that "the monolith retains
lines 1–75 (the existing module docstring)"; after
Task 7 those lines are replaced.

**Impact**: Minor documentation completeness gap. An
executor or reviewer reading spec §4 alone may
wonder whether 1–75 is "missing" from coverage.

**Suggested fix**: Add a sentence to spec §4: "Lines
1–75 are the monolith's existing module docstring,
imports, namespace declarations, and `open`
directive. They are handled by Task 7's index-file
overwrite, not by the sub-range moves in Tasks 2–6."

### D39: Plan Task 4 anchor description for PC-bound cluster start says line 6320

**Where**: Plan Task 4 (preamble describing the
non-contiguous PC-bound cluster).

**Defect**: Plan Task 4 preamble says:
"Non-contiguous PC-bound cluster: 6320–6606
(`preservingTransfer_loop2_pc_strict_bound` docstring
at 6320 theorem at 6326, ...)". The docstring is
actually at L6321 (verified by `sed -n '6321p'`
returning `/-- Strict per-step PC bound for
preservingTransfer_loop2`). L6320 is blank.

The same task lists the search anchor `^private
theorem preservingTransfer_loop2_pc_strict_bound`
which finds L6326 (the keyword line) correctly. So
the anchor recovers, but the docstring line annotation
is wrong.

**Impact**: Same as D34; the docstring start is
mis-stated in the prose.

**Suggested fix**: Change "docstring at 6320" to
"docstring at 6321" in plan Task 4 preamble. Update
the spec §4 row Loops boundary 6320 → 6321 in
lockstep.

### D40: Plan Task 6 vPrefixSum docstring at 6607 vs 6603

**Where**: Plan Task 6 preamble (sub-block phase
correctness range).

**Defect**: Plan Task 6 preamble reads "Sub-block
phase correctness: 6607–7208. Contains `vPrefixSum`
(6607), ...". `vPrefixSum` is a `private def` at
L6607 (keyword line); its docstring `/-- Sum of v
over a prefix Fin m of Fin a` is at L6603. Per the
spec's docstring-anchored rule, the Comp sub-range
should start at L6603, not L6607.

**Impact**: If plan Task 6 Step 2 extracts literal
6607–7208, the `vPrefixSum` declaration arrives in
`Comp.lean` without its docstring (a 4-line
amputation). The spec §1 "docstrings do not change"
contract is broken.

**Suggested fix**: Change spec §4 row Comp third
sub-range from `6607–7208` to `6603–7208`. Update
plan Task 6 Step 2 row 3 from "6607–7208" to
"6603–7208". Update Loops's end boundary from
6606 to 6602 (= 6603 − 1) in spec §4 row Loops and
plan Task 4 Step 5 row 1.

### D41: Plan Task 3 Step 5 expected extract anchor docstring line

**Where**: Plan Task 3 Step 5.

**Defect**: Plan Task 3 Step 5 reads `sed -n
'11820,11895p' GebLean/LawvereERKSim.lean >
/tmp/emb_bridge.lean` and "Verify the extract begins
with the docstring `/-- Generic bridge from the
existential pre-stop form` (line 11820)". The
docstring is actually at L11821 (`sed -n '11821p'`
returns `/-- Generic bridge from the existential
pre-stop form to the`). L11820 is blank.

The `sed` command with start 11820 will include the
blank at 11820 plus the docstring starting at 11821.
The "Verify ... line 11820" verification will fail
because L11820 is blank, not the docstring.

**Impact**: The Step 5 verification step explicitly
asserts "line 11820" is the docstring start. An
executor reading this will be confused and may
either (a) note the discrepancy and proceed, or (b)
halt and try to debug the spec.

**Suggested fix**: Change Plan Task 3 Step 5 sed
range from `11820,11895` to `11821,11895` and update
the verification text to "line 11821". Update spec §4
row Embedding bridge from `11820–11895` to
`11821–11895`.

### D42: Plan Task 4 deletion 6320–6606 overlaps Task 5 deletion 6199–6325

**Where**: Plan Task 4 Step 5 row 1 vs Plan Task 5
Step 5 row 2.

**Defect**: Plan Task 4 Step 5 row 1 deletes "PC-bound
cluster (original 6320–6606)". Plan Task 5 Step 5
row 2 deletes "6199–6325 (zero pre-stop)". The
ranges overlap on lines 6320–6325 (6 lines). After
Task 4 executes, those lines no longer exist in the
monolith; Task 5's anchor-based re-derivation must
recompute. The plan does not explicitly note this
overlap-and-anchor-recompute interaction.

**Impact**: With anchor-based re-derivation
(`^private theorem compileER_pre_stop_correct_atom_zero`),
Task 5 will correctly identify the start of its
range. But the end of its range (the line just
before the next docstring) is now the post-Task-4
boundary line, which equates to "just before the
first surviving declaration after `_atom_zero`"
which is now `vPrefixSum` (Comp content) since Loops
has been removed. The Task 5 deletion end would
sweep too far unless explicitly bounded.

**Suggested fix**: In plan Task 5 Step 5 preamble,
add an explicit note: "After Task 4's deletion of
lines 6320–6606, the next declaration after
`compileER_pre_stop_correct_atom_zero` (now at the
adjusted-line equivalent of L6199) is `vPrefixSum`
(originally at L6603, now at L6603 − 287 = L6316)
because Task 4 removed the 287-line range 6320–6606
preceding it." Equivalently: fix the Atoms zero
pre-stop range in spec §4 to end at 6320 (not 6325)
so the deletions never overlap.

### D43: Plan Task 1 Step 3 doesn't account for an in-progress feature branch

**Where**: Plan Task 1 Step 3.

**Defect**: Plan Task 1 Step 3 expects `jj status` to
report "The working copy is clean or a single new
working-copy commit on top of the spec commit". This
matches a fresh-branch workflow. If the executor is
working on a branch that already has spec, plan, and
review work (this is the current state — `jj status`
will show the spec and plan and the review-3 doc as
edits in progress), the status will not be "clean".
The plan's instruction "If there are unrelated edits
in the working copy, pause and surface them to the
user" is too restrictive — the spec+plan+reviews ARE
the immediate predecessor, not "unrelated edits".

**Impact**: Plan executor may halt at this step
unnecessarily.

**Suggested fix**: Soften Step 3's halt criterion:
"If `jj status` shows commits *outside* the file-split
spec/plan/review series, pause and surface to the
user. The spec, plan, and review docs in
`docs/superpowers/{specs,plans}/2026-05-19-lawvere-
er-k-sim-file-split-*.md` are expected predecessors;
the file-split execution begins from the tip of that
series."

### D44: Plan Task 6 preamble cites "structural IH on gs m" with no anchor

**Where**: Plan Task 6 preamble (sub-block phase
correctness item).

**Defect**: Plan Task 6 preamble reads
"`compileFrag_comp_subBlock_gsBody_correct` (6949;
note the monolith has no `gsBody_pc_strict_bound` —
gsBody's strict PC bound is provided by the
structural IH on `gs m`)". This is informative prose
but not actionable: the executor cannot test
"structural IH on `gs m`" against the source. The
note is correct but not load-bearing for the
extraction; consider whether the prose belongs in
the spec docstring rather than the plan task preamble.

**Impact**: Low. Prose is helpful but not necessary
for execution.

**Suggested fix**: No change required. The prose is
sound; it's just non-actionable for the extraction
step.

## Coverage gap / overlap report (per user request)

Union of spec §4 sub-ranges as currently stated:

```text
Compiler:  76–1473
Embedding: 1474–2137, 5201–5232, 5854–5944, 11820–11895
Loops:     2956–4915, 5414–5654, 6320–6606
Atoms:     4917–5200, 5233–5413, 5655–5853, 6199–6325, 7209–8023
Comp:      2138–2955, 5945–6198, 6607–7208, 8024–11819, 11896–11940
```

Result:

- **GAP at L4916** (1 line, blank). Between Loops's
  first range end (4915) and Atoms's first range
  start (4917). The blank line at 4916 is not
  assigned to any submodule. Trivial in practice (a
  blank line is non-load-bearing) but the spec rule
  says end = line-before-next-docstring, i.e., 4916.
- **GAP at L11820** (1 line, blank). Between Comp's
  m-step range end (11819) and Embedding bridge
  start (11820). Same trivial nature; per rule end
  should be 11820, but spec assigns 11820 to
  Embedding's start. Either form is acceptable; both
  endpoints can't simultaneously be authoritative.
- **OVERLAP at L6320–6325** (6 lines). Atoms's zero
  pre-stop range ends at 6325; Loops's PC-bound
  range starts at 6320. L6320 is blank; L6321–6325 is
  the docstring of `preservingTransfer_loop2_pc_strict_bound`
  (a Loops declaration). The overlap means that if
  both sub-ranges are taken literally, the docstring
  appears in two submodules. (In practice, Task 4
  executes first and removes the lines; Task 5's
  anchor-based deletion then proceeds.) See D35.
- **Implicit miss at lines 5933–5944 and 6603–6606**
  (12 + 4 lines = 16 lines total) which are
  *assigned to the wrong submodule*: Embedding range
  5854–5944 absorbs k_zero's docstring (Comp
  content); Loops range 6320–6606 absorbs vPrefixSum's
  docstring (Comp content). These are not gaps but
  mis-allocations. See D34.

Lines 1–75 (preamble) are correctly outside all
sub-ranges; Task 7 handles them via index overwrite.

## Plan executability assessment

A fresh executor with no project knowledge would:

1. Read Task 1 Step 1–7 verifications and run them.
   Step 7's `grep GebLeanTests/` is sound and
   sufficient — verified empirically that no other
   `.lean` file references `LawvereERKSim`.
2. Read each Task 2–6 Step 1 (header template) and
   write the new submodule's preamble.
3. Read each Task 2–6 Step 2 (extraction). For
   Tasks 4 and 5, the prose says "use anchors to
   compute current line numbers at execution time",
   which masks the table errors at the cost of
   imposing extra anchor work on the executor.
4. Iterate per-task build, fix, commit.

Remaining ambiguities (the plan should resolve
before execution):

- The spec §4 table is normative; the plan's per-
  task numeric ranges cite it. With the table broken
  at the docstring-amputation boundaries, the
  executor's anchor-based recovery happens "behind"
  the formally-stated ranges. A documentation-clean
  plan should not require anchor-based recovery for
  spec-literal numeric ranges.
- Plan Task 5 Step 2 row 2 (`5157–5200`) and row 1
  (`4917–5156`) split the spec §4 row Atoms's
  first single range. The split itself is fine but
  the boundary 5156/5157 amputates a docstring.
- Plan Task 4 Step 5 deletes "6320–6606" and Plan
  Task 5 Step 5 deletes "6199–6325"; the overlap
  6320–6325 is left for anchor-based recovery.

## Summary of findings

- **Total new defects**: 11 (D34–D44). D43 and D44
  are documentation-only; the others are normative
  inconsistencies between spec §4's table, the stated
  docstring rule, the plan's per-task ranges, and
  the monolith's actual content.
- **High-severity** (the spec/plan numeric ranges
  break the spec rule and the per-task extracts can
  amputate or duplicate docstrings if not
  anchor-corrected): D34 (root cause), D35 (overlap),
  D36 (spec §4 vs plan Task 5 range count mismatch),
  D37 (spec §4 table doesn't satisfy its own
  preamble rule).
- **Medium-severity** (per-task prose contradicts
  spec §4 or asserts wrong line numbers): D39, D40,
  D41, D42.
- **Low-severity** (documentation polish): D38
  (preamble lines 1–75 not enumerated), D43 (Task 1
  Step 3 status criterion), D44 (Task 6 informational
  prose).

Round-1 closure: 25 of 26 defects resolved; D26
carried as D30, resolved via policy in round 2.

Round-2 closure: 5 of 6 defects resolved; D31's
root cause (sub-range starts at theorem-keyword or
blank lines rather than `/--` docstring lines) is
partially fixed (three boundaries corrected, seven
remain).

**Verdict**: Plan needs one more revision round. The
core remaining work is a spec §4 table rewrite
synchronised with plan per-task numeric ranges, so
that the union of sub-ranges has no gaps, no
overlaps, and every boundary satisfies the stated
docstring-anchored rule. The recommended target
table is:

```text
Compiler:  76–1473
Embedding: 1474–2137, 5201–5232, 5854–5932, 11821–11895
Loops:     2956–4916, 5414–5654, 6321–6602
Atoms:     4917–5151, 5152–5200, 5233–5413, 5655–5853,
           6199–6320, 7209–8023
Comp:      2138–2955, 5933–6198, 6603–7208,
           8024–11820, 11896–11940
```

(Empirically verified at commit `a1ff2ff7` by
`sed -n '<line>p'` against the monolith. Every
sub-range start is the leading `/--` line of the
first declaration in the sub-range or a section
heading; every sub-range end is the line just before
the next sub-range's leading docstring or section
heading.)

With this table in place, the union covers
76–11940 with no gaps (every blank-line boundary is
assigned to exactly one submodule's end-of-range)
and no overlaps. Plan Tasks 3–6 Step 2 (extraction)
and Step 5 (deletion) numeric ranges should be
updated in lockstep with the spec table; the
existing anchor-based prose can remain as
defence-in-depth against future monolith edits.
