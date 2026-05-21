# Step T2 Task 11e.6.a.iii-bprod — session-2 execution handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Session-1 summary](#session-1-summary)
- [Landed commits](#landed-commits)
- [Patterns surfaced during session 1](#patterns-surfaced-during-session-1)
- [Open followup items](#open-followup-items)
- [Remaining sub-task execution order](#remaining-sub-task-execution-order)
- [Per-sub-task workflow (unchanged)](#per-sub-task-workflow-unchanged)
- [Operational rules (unchanged)](#operational-rules-unchanged)
- [Definition of done](#definition-of-done)
- [Resumption recipe (one-line)](#resumption-recipe-one-line)
- [References](#references)

<!-- END doctoc -->

Continuation handoff for the bprod pre-stop sub-division execution
chain. Session 1 landed sub-tasks bprod.0 through bprod.1.d
(9 sub-tasks of 18). Session 2 picks up at bprod.2 and runs
through bprod.6 plus the runtime correction (9 sub-tasks
remaining).

## Session-1 summary

The plan at
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`
(adversarially converged in commit `ad6c1b4a`) was executed via
`superpowers:subagent-driven-development` per the original
execution handoff at
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-handoff.md`.

Sub-tasks landed (9):

- bprod.0 — PC-bound infrastructure
- bprod.1.a — zero-sweep correctness alias
- bprod.1.b — prologue correctness alias
- bprod.1.c.0 — accUpdate prep (two transferLoops)
- bprod.1.c.1 — inner-mul partial invariant + base
- bprod.1.c.2 — inner-mul step `(j → j + 1)`
- bprod.1.c.3 — inner-mul outer iteration
- bprod.1.c.4 — accUpdate assembly
- bprod.1.d — f-body embedding

The complete `compileFrag_bprod_accUpdate_correct` chain
(including the `R^XY_Z` multiplicative correctness) and the
f-body `ProgramEmbedsFragment` witness are landed. All
declarations axiom-clean (`[propext, Quot.sound]`); the helper
`CompiledFragment.size_pos` extracted during bprod.0 is
`[propext]`-only.

`BProd.lean` grew from 0 lines (new file) to 3886 lines across
session 1. `Compiler.lean` gained two declarations:
`CompiledFragment.size_pos` (extracted in bprod.0 fix-up) and
`compileFrag_bprod_size`. `BSum.lean` gained un-`private`
modifier-removals on four declarations
(`compileFrag_bsum_zeroSweep_correct`,
`compileFrag_bsum_zeroSweep_pc_strict_bound`,
`compileFrag_bsum_prologue_correct`,
`compileFrag_bsum_prologue_pc_strict_bound`). The index file
`LawvereERKSim.lean` gained the `BProd` import and docstring
update.

## Landed commits

In order (oldest first), all on the current topic branch:

| change-id | description |
| --- | --- |
| `ulo` | feat(ertok): bprod PC-layout constants and size lemma |
| `or` | refactor(ertok): extract CompiledFragment.size_pos; fix LawvereERKSim docstring rot |
| `xu` | docs(ertok): remove forward-development reference in LawvereERKSim index |
| `vs` | feat(ertok): bprod zero-sweep correctness wrappers; un-private bsum analogs |
| `tn` | feat(ertok): bprod prologue correctness wrappers; un-private bsum analogs |
| `lyp` | feat(ertok): bprod accUpdate prep correctness |
| `wpt` | style(ertok): drop unused with binding in bprod accUpdate prep proof |
| `wsk` | feat(ertok): bprod inner-mul partial invariant and base case |
| `szo` | feat(ertok): bprod inner-mul step j to j+1 |
| `squ` | feat(ertok): bprod inner-mul outer iteration j=0 to vFOut |
| `qxo` | feat(ertok): bprod accUpdate assembly |
| `pyr` | feat(ertok): bprod f-body program embedding |

12 commits total (9 `feat`, 1 `refactor`, 1 `style`, 1 `docs`).

## Patterns surfaced during session 1

The following patterns emerged during session-1 implementation
and review iterations. The next session's implementer briefs
should bake these in:

1. **`h_zReg_zero` / `h_sPrep_z` parameter additions**: the
   plan's signatures for `_accUpdate_prep_correct`,
   `_mul_partial_base`, `_mul_partial_aux`, `_mul_partial`, and
   `_accUpdate_correct` all omit an explicit hypothesis that
   the reserved zero register (index 0) holds 0. The
   downstream callers supply this from the outer partial
   invariant's `zReg_zero` field; the lemmas need it because
   `transferLoop_correct` and `preservingTransfer_correct`
   demand `s.regs zReg = 0`. The bsum analogs carry it under
   the name `h_z`. Add `h_zReg_zero` or `h_sPrep_z` to each
   downstream consumer's signature; document the addition in
   the lemma's docstring. Same pattern will recur in any
   bprod.2/bprod.3.* sub-task that calls into the inner-mul or
   accUpdate chain.
2. **Stale-cache LSP behavior**: `mcp__lean-lsp__lean_verify`
   serves stale cached results for ~30 seconds after an edit,
   sometimes reporting fake `sorryAx` leaks. ALWAYS run
   `lake build GebLean.LawvereERKSim.BProd` before
   `lean_verify`; re-verify after rebuild if the first attempt
   shows unexpected axioms. Reproduced three times in
   session 1 (bprod.0 fix-up, bprod.1.a, bprod.1.b).
3. **`set` is load-bearing for goal rewriting**: `set sX := ...`
   has a side-effect of rewriting subsequent occurrences in the
   goal. Pattern 9's "prefer `let` over `set`" guideline applies
   ONLY when the rewriting side-effect is unused. Bprod.1.c.0's
   review recommended a `set → let` conversion that broke
   elaboration; the rewriting was load-bearing. Only convert
   `set X with hX_def` to `let` when both (a) `hX_def` is never
   referenced and (b) the proof body never relies on `set`'s
   goal-context rewriting.
4. **`show` is forbidden for goal-changing**: the project
   linter flags `show <goal-type>` used as a goal-changing
   tactic. Use `change` instead. Caught during bprod.1.c.2's
   implementation. The bsum analogs may use `show` (older
   landed code); new bprod code must use `change`.
5. **`rcases Nat.lt_or_ge` over `by_cases`**: `by_cases` and
   `push_neg` pull `Classical.choice`. Use
   `rcases Nat.lt_or_ge` or `Nat.lt_or_eq_of_le` for binary
   case splits on natural numbers (Pattern 2 in the project
   memory). Surfaced in bprod.1.c.4 where the implementer
   initially used `by_cases` and the axiom audit flagged
   `Classical.choice`; replacing with `rcases Nat.lt_or_ge`
   restored constructive purity.
6. **`set_option maxHeartbeats` is acceptable with
   justification**: large-state segment-peeling helpers and
   multi-phase correctness lemmas may need `maxHeartbeats`
   bumps. Add a brief justifying comment above the option line
   (project convention).
7. **`refine ⟨T0, rfl, ?_, ?_⟩` placement**: must come AFTER
   all `let`/`have`/`set` setup; otherwise the `?_` metavariables
   capture only the pre-setup context. Surfaced in bprod.1.c.2.
8. **`change ... 0 + 1` over `rw [show (1 : ℕ) = 0 + 1]`**: the
   latter triggers `motive is not type correct` errors in
   dependently-typed `URMState P` contexts. Use the `change`
   form. Surfaced in bprod.1.c.2.
9. **Single-line `set sX := ...; change ...`-pattern fallback**:
   `rw [Nat.succ_mul]` can fail after `change j' * (...) + (...)
   = (j' + 1) * (...)` if Lean displays `9 * vAccIn` as
   `8 * vAccIn + vAccIn` after an unrelated unfolding. Replace
   with `have ... := by rw [Nat.succ_mul]; omega`. Surfaced in
   bprod.1.c.3.

## Open followup items

The plan's followup section (lines 1484+ of the sub-division)
already enumerates 10 items. Session-1 execution surfaced no
new items; the existing list still applies. Notable items
deferred to the post-T2 followup branch (task #654):

- Item 1: shared `compileFrag_bprod_segment_at` scaffold to
  deduplicate ~70% overlap across the five segment-peeling
  helpers in the bprod chain. Session 1 landed three of the
  five planned segment-peeling helpers
  (`_prep_instr_at`, `_innerBody_instr_at`, `_reset_instr_at`);
  the remaining two (`_zeroSweep_instr_at`,
  `_prologueBlock_instr_at`) will land in bprod.3.phase_i0 and
  bprod.3.phase_i1.
- Item 3: extract a shared `multiplicative_loop_correct`
  template. The `_aux` / `_partial` "induct twice" pattern
  used in bprod.1.c.3 has ~75-line duplication that the
  template would eliminate.
- Item 9: post-bprod.6 runtime-formula audit across bsum and
  comp; the bprod runtime correction (sub-task 18) will inform
  this.

## Remaining sub-task execution order

Pick up at sub-task bprod.2. Execute in order:

1. **bprod.2** — partial invariant + base case (~500-600 LOC).
2. **bprod.3.phase_i0** — zero-sweep preservation (~650-750
   LOC). First instance of `_zeroSweep_instr_at` helper.
3. **bprod.3.phase_i1** — prologue preservation (~600-700
   LOC). First instance of `_prologueBlock_instr_at` helper.
4. **bprod.3.phase_i2** — f-body preservation, consumes
   `ih_f` (~550-650 LOC). Uses
   `ProgramEmbedsFragment_compileFrag_bprod_fBody` (landed in
   bprod.1.d).
5. **bprod.3.phase_i3** — accUpdate + incR + goto (~700-850
   LOC). Uses `compileFrag_bprod_accUpdate_correct` (landed
   in bprod.1.c.4).
6. **bprod.4** — induction glue `(i → i + 1)` (~300-400 LOC).
7. **bprod.5** — outer iteration `(i = 0 → v 0)` (~450-550
   LOC).
8. **(runtime correction)** — separate `fix(ertok):` commit on
   `Compiler.lean`. Patches `compileER_runtime`'s bprod branch
   to account for the multiplicative cost `9 * A_i * B_i`. The
   sub-division plan's sub-task 6 documents the recommended
   `List.range bound`-fold rewrite mirroring `natBProd`'s
   `Nat.rec` shape.
9. **bprod.6** — final assembly
   `compileER_pre_stop_correct_bprod` (~350-450 LOC).

After bprod.6 lands, the wrapper Task 11g
(`compileER_runFor_bprod`) is a three-line composition with
the existing `compileER_pre_stop_to_runFor` bridge.

## Per-sub-task workflow (unchanged)

Per the original execution handoff, use
`superpowers:subagent-driven-development`:

1. Mark task `in_progress` in `TaskList`.
2. Dispatch implementer subagent with self-contained brief
   (paste sub-task text from the sub-division plan).
3. Verify `lake build` and `mcp__lean-lsp__lean_verify` on
   every new declaration.
4. Dispatch spec-compliance reviewer (fresh-context). Re-loop
   to convergence.
5. Dispatch code-quality reviewer (fresh-context). Re-loop to
   convergence.
6. Commit via `jj describe -m 'feat(ertok): <short
   description>'`. Use `jj new -m ''` to advance `@`.
7. Mark task `completed`.

For small sub-tasks (thin-wrapper aliases like bprod.1.a/1.b,
field-projection bases like bprod.1.c.1), the combined
spec + code-quality reviewer can be dispatched in one
subagent. For substantive sub-tasks (≥300 LOC implementations
involving structures, segment-peeling, or multi-phase
composition), separate the reviewers.

## Operational rules (unchanged)

The hard rules from the original execution handoff still
apply:

- No `jj git push` without user line-by-line review.
- No raw mutating `git` subcommands.
- No `noncomputable`, no `admit`, minimal `Classical`.
- One concern per branch; followup candidates go to task #654.
- Markdownlint cleanliness on any `.md` touched.
- `lake build` only (never `lake env lean`, never `lake clean`).

## Definition of done

Bprod execution is complete when:

1. All 9 remaining sub-tasks + the runtime correction have
   landed as commits on the current branch.
2. `lake build` clean across the whole tree (target ~1545+
   jobs after the new sub-task code lands).
3. Every new declaration's `mcp__lean-lsp__lean_verify`
   output is `[propext, Quot.sound]` only.
4. `markdownlint-cli2 '**/*.md'` reports 0 errors.
5. `doctoc '**/*.md' --check` reports clean.
6. New followup items appended to task #654.

After "done", recipe step 4 of the broader Task 11 handoff
(`compileER_runFor_bprod` wrapper) is the next step.

## Resumption recipe (one-line)

```text
Read docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-session2-handoff.md
and dispatch the bprod.2 implementer subagent per the workflow above.
```

## References

- Original execution handoff:
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-handoff.md`.
- Sub-division (binding):
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`.
- Broader Task 11 handoff (session 0):
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.
- T2 plan (binding):
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- Bsum sub-division (template for bprod):
  `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`.
- Project rules:
  `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `.claude/rules/fork-upstream-flow.md`.
