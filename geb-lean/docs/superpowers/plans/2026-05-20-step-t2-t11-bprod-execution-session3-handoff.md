# Step T2 Task 11 — session-3 execution handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Session-2 summary](#session-2-summary)
- [Landed commits](#landed-commits)
- [Patterns surfaced during session 2](#patterns-surfaced-during-session-2)
- [Open followup items](#open-followup-items)
- [Remaining work for Task 11](#remaining-work-for-task-11)
  - [Task 11g — bprod runFor wrapper (~30 LOC)](#task-11g--bprod-runfor-wrapper-30-loc)
  - [Task 11h — top-level structural induction (~50-100 LOC)](#task-11h--top-level-structural-induction-50-100-loc)
  - [Task 12 — axiom audit (~no LOC, manual pass)](#task-12--axiom-audit-no-loc-manual-pass)
  - [Final holistic code-quality review (~no LOC, manual pass)](#final-holistic-code-quality-review-no-loc-manual-pass)
- [Per-task workflow (unchanged)](#per-task-workflow-unchanged)
- [Operational rules (unchanged)](#operational-rules-unchanged)
- [Definition of done](#definition-of-done)
- [Resumption recipe (one-line)](#resumption-recipe-one-line)
- [References](#references)

<!-- END doctoc -->

Continuation handoff after sessions 1 and 2 of the bprod
pre-stop sub-division execution. Session 1 landed sub-tasks
bprod.0 through bprod.1.d (9 of 18); session 2 landed the
remaining 9 (bprod.2 through bprod.6 plus the runtime
correction). The entire bprod pre-stop chain is now complete.
Session 3 picks up at Task 11g (the bprod runFor wrapper) and
runs through Task 11h (top-level structural induction), Task 12
(axiom audit), and the final holistic code-quality review.

## Session-2 summary

Session 2 executed sub-tasks bprod.2 through bprod.6 plus the
runtime correction via
`superpowers:subagent-driven-development`, per the session-2
handoff at
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-session2-handoff.md`.

Sub-tasks landed (9):

- bprod.2 — partial invariant + base case
- bprod.3.phase_i0 — zero-sweep preservation
- bprod.3.phase_i1 — prologue preservation
- bprod.3.phase_i2 — f-body preservation (consumes `ih_f`)
- bprod.3.phase_i3 — accUpdate + incR + goto
- bprod.4 — induction glue `(i → i + 1)`
- bprod.5 — outer iteration `i = 0` to `v 0`
- bprod runtime correction (`fix(ertok)` on `Compiler.lean`)
- bprod.6 — final assembly `compileER_pre_stop_correct_bprod`

`BProd.lean` grew from 3886 lines (start of session 2) to
8651 lines (+4765 LOC across the session). `Compiler.lean`
gained 3 lines for the runtime correction (the bprod branch of
`compileER_runtime` now embeds the multiplicative cost
`9 * A_i * B_i + 4 * A_i + 9 * B_i` via `A_i := natBProd i (...)`
and `B_i := f.interp ctx_f` let-bindings). All new declarations
are axiom-clean (`[propext, Quot.sound]`); the runtime
correction `compileER_runtime` itself is `[propext]` only as a
`def`.

The top-level theorem `compileER_pre_stop_correct_bprod` is
landed at `GebLean/LawvereERKSim/BProd.lean:8332`. It composes
`compileFrag_bprod_partial` (the outer-loop correctness lemma
at `i = v 0`) with a single `jumpZR vX exitPC bodyStartPC` URM
step at the loop-top PC, taking the zero branch (because
`vX = v 0 - v 0 = 0`) to the exit PC.

## Landed commits

In order (oldest first), all on the current topic branch:

| change-id | description |
| --- | --- |
| `osmstnpl` | feat(ertok): bprod partial invariant and base case |
| `wpronlkw` | feat(ertok): bprod phase i.0 zero-sweep preservation |
| `nwkktvux` | feat(ertok): bprod phase i.1 prologue preservation |
| `wxlvokts` | feat(ertok): bprod phase i.2 f-body preservation |
| `tlwuruux` | feat(ertok): bprod phase i.3 accUpdate, incR, goto |
| `vpplyktz` | feat(ertok): bprod induction glue i to i + 1 |
| `lrzlstnl` | feat(ertok): bprod outer iteration i=0 to v 0 |
| `wlplzssz` | fix(ertok): account for multiplicative cost in bprod runtime |
| `xotpowwk` | feat(ertok): bprod final assembly compileER_pre_stop_correct |

9 commits total (8 `feat(ertok)`, 1 `fix(ertok)`).

## Patterns surfaced during session 2

Adds to the session-1 patterns list (in
`2026-05-20-step-t2-t11-bprod-execution-session2-handoff.md` § Patterns).
The next session's implementer briefs should bake these in:

1. **`set_option maxHeartbeats N in` placement is linter-enforced**:
   the Lean style linter (`linter.style.maxHeartbeats`) requires the
   justifying comment to sit BETWEEN the `set_option ... in` line and
   the declaration's docstring, NOT above the `set_option`. Correct
   order: `set_option maxHeartbeats N in` → `-- justification comment`
   → `/-- declaration docstring -/` → declaration. Confirmed across
   bprod.2, bprod.3.phase_i0/i1/i2/i3, bprod.4, bprod.5, bprod.6, and
   the bprod runtime correction. Bumps used in session 2 ranged from
   `400000` (legacy) through `1000000` (most phase lemmas) to
   `4000000` (the heaviest preservation and final-assembly proofs).
2. **Named single-step helper hypotheses are easier on elaboration**:
   for any multi-stage `URMState.runFor` collapse, prefer named
   intermediate hypotheses
   `have h_runFor_sX_1 : URMState.runFor P sX 1 = sY := by change
   URMState.runFor P (URMState.step P sX) 0 = _; rw [URMState.runFor_zero,
   h_stepX]` over chained inline `change` expressions. Surfaced in
   bprod.2 (the 6-stage prelude collapse) and confirmed across all
   subsequent phase preservation proofs.
3. **`change` chains are sanctioned for definitional unfolding**:
   the project rule "use `change`, not `show <goal-type>`, for
   goal-changing tactics" specifically targets the forbidden `show`
   form. Multiple sequential `change`s that progressively unfold
   named PC constants (`bprod_topPC`, `bprod_bodyPCBase`,
   `bprod_trBase`, etc.) into their numeric definitions are
   idiomatic and load-bearing — the Lean unifier requires the
   *syntactic* shape of expressions to match for tactics like
   `omega`, not just propositional equality. Code-quality reviewers
   should distinguish these (real work) from no-op `change`s after
   `rw`s that produce already-equal goals.
4. **`set sX := ...` vs `let sX := ...`**: `set` has a load-bearing
   side-effect of rewriting subsequent occurrences in the goal; the
   "prefer `let` over `set`" guideline (session-1 pattern 3) applies
   only when the rewriting is unused. Confirmed across the phase
   preservation proofs where `set` is consistently used for the
   intermediate state variables whose names need to appear in
   downstream `change` lines.
5. **Pattern 17 — inline `URMState.init` before projection-matching**:
   `let`-bound `URMState.init` blocks regs-projection reduction;
   use `URMState.init` inline (not let-bound) before pattern-matching
   on its `regs` projection, then let-bind afterward. Surfaced in
   bprod.3.phase_i2; same pattern in the analogous bsum step. Honor
   this in any new sub-task that does case-splits on `URMState.init`'s
   regs at specific input slots.
6. **Folded-body bridging for `omega`**: when `omega` needs to relate
   two `List.foldl`-of-`map` atoms whose bodies are definitionally
   equal but syntactically different (e.g., one uses
   `have A_j := ...; ... B_j * (9 * A_j + 5)` from a `let`-elaborated
   `perIter`, while the other uses the inline form
   `... f.interp ... * (9 * natBProd j ... + 5)` from a lemma's LHS),
   introduce a `have h_bound' : T ≤ <inline form> := h_bound` to coerce
   the foldl body's syntactic form. Definitional equality alone does
   not let `omega` unify two foldl atoms. Surfaced in bprod.6's
   final-assembly slack arithmetic.
7. **Nonlinear-product re-association for `omega`**: `omega` treats
   `9 * A * B` and `9 * (A * B)` as distinct atoms; re-associate via
   `Nat.mul_assoc` and `set C := A * B` before linearizing. Surfaced
   in bprod.6's slack arithmetic with the multiplicative
   `9 * A_i * B_i` term.
8. **`ring` is unavailable under this project's import surface**: use
   `Nat.mul_add`, `Nat.mul_comm`, `Nat.mul_assoc` manually for ℕ
   distributivity/commutativity. Surfaced in bprod.6.
9. **Minimal-scope segment-peeling helpers**: when a phase lemma needs
   only a small subset of an instruction block's lookups (e.g., the
   2 epilogue instructions of bprod's 23-instruction accUpdate block,
   the inner 21 already exposed by granular `_prep_instr_at`,
   `_innerBody_instr_at`, `_reset_instr_at` helpers), define the
   segment-peeling helper to expose only the needed lookups rather
   than mirroring the broader-scope bsum analog. Surfaced in
   bprod.3.phase_i3's `compileFrag_bprod_accUpdateBlock_instr_at`.

## Open followup items

The session-2 handoff's "open followup items" section (the
deferred-to-task-#654 list) is unchanged. No new followup items
surfaced during session 2. The followup list at task #654
should be promoted to its own session when convenient.

## Remaining work for Task 11

### Task 11g — bprod runFor wrapper (~30 LOC)

Three-line wrapper around `compileER_pre_stop_to_runFor`
(in `Embedding.lean`) once `compileER_pre_stop_correct_bprod`
has landed. Mirrors `compileER_runFor_bsum` at
`GebLean/LawvereERKSim/BSum.lean:5009`. Lands at the tail of
`BProd.lean`. Sub-task is task #625 in the task list.

Signature (per the broader Task 11 handoff at
`docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`
line 544):

```lean
private theorem compileER_runFor_bprod
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ, T0 ≤ compileER_runtime f v' ∧ ...)
    (v : Fin (k + 1) → ℕ) :
    ∃ T0 : ℕ,
      T0 = compileER_runtime (.bprod f) v ∧
      <runFor stops at exit PC> ∧
      <output reg holds (.bprod f).interp v>
```

(See `compileER_runFor_bsum`'s signature for the exact form.)

The proof is a direct composition with
`compileER_pre_stop_to_runFor`. ~30 LOC. Use a single
combined spec + code-quality reviewer subagent (thin wrapper
sub-task).

### Task 11h — top-level structural induction (~50-100 LOC)

`compileER_runFor` proved by structural induction on
`e : ERMor1 k`, dispatching to the per-constructor `_runFor_*`
lemmas (zero/succ/proj/sub/comp/bsum/bprod). Sub-task is
task #626 in the task list. Per the broader handoff (line 550), the
spec recommends landing this in a new
`GebLean/LawvereERKSim/Top.lean` submodule.

Signature (per the spec at `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`):

```lean
theorem compileER_runFor
    {k : ℕ}
    (e : ERMor1 k)
    (v : Fin k → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime e v ∧
      <runFor stops at exit PC> ∧
      <output reg holds e.interp v>
```

(See the `## Top-level statement` section of the broader Task 11
handoff for the exact form.)

The proof is `induction e` with each constructor's case
delegated to its per-constructor lemma:

- `.zero` → `compileER_runFor_zero` (Atoms.lean:35)
- `.succ` → `compileER_runFor_succ` (Atoms.lean:128)
- `.proj i` → `compileER_runFor_proj i` (Atoms.lean:323)
- `.sub f i` → `compileER_runFor_sub` (Atoms.lean:506)
- `.comp f gs` → `compileER_runFor_comp` (Comp.lean:5402)
- `.bsum f` → `compileER_runFor_bsum` (BSum.lean:5009)
- `.bprod f` → `compileER_runFor_bprod` (Task 11g, BProd.lean)

The induction supplies each per-constructor lemma's `ih_f` /
`ih_gs` parameters from the structural induction hypothesis.

Consider creating `GebLean/LawvereERKSim/Top.lean` for the
new module; alternatively, the top-level theorem may land in
`LawvereERKSim.lean` (the index file) directly. Defer the
file-placement decision to the implementer.

Dispatch a substantive-tier subagent (separate spec and
code-quality reviewers).

### Task 12 — axiom audit (~no LOC, manual pass)

Per `CLAUDE.md` § Constructive-only Lean code: manual
`mcp__lean-lsp__lean_verify` pass over every public declaration
in `GebLean/LawvereERKSim/{Atoms,Comp,Embedding,Loops,Compiler,BSum,BProd,Top}.lean`
plus the index file. Confirm every declaration is
`[propext, Quot.sound]`-only.

The earlier-flagged defect with `scripts/check-axioms.sh` not
seeing nested namespaces is documented in the broader handoff
(line 559); `lean_verify` is the authoritative per-declaration
tool. No code changes expected. Sub-task is task #617.

If any declaration leaks `Classical.choice` (the most likely
suspect — see project memories on the `simp only [if_pos h]`
sorryAx leak and `fin_cases`/`by_cases`/`push_neg` Classical
pulls), open a small fix-up branch.

### Final holistic code-quality review (~no LOC, manual pass)

Per the original SDD plan: after Task 11h and Task 12 land,
dispatch a final fresh-context reviewer over the entire T2
implementation. The reviewer should walk every submodule under
`GebLean/LawvereERKSim/` and flag stylistic, structural, or
naming issues for a possible followup branch. Sub-task is
task #618.

After the final review:

- Any findings that touch the binding code go to a `chore(ertok)`
  cleanup commit on the current branch.
- Any findings that touch shared abstractions go to followup
  task #654 for a separate post-T2 cleanup branch.

## Per-task workflow (unchanged)

Per the session-1 and session-2 execution handoffs, use
`superpowers:subagent-driven-development`:

1. Mark task `in_progress` in `TaskList`.
2. Dispatch implementer subagent with self-contained brief.
3. Verify `lake build` and
   `mcp__lean-lsp__lean_verify` on every new declaration.
4. Dispatch spec-compliance reviewer (fresh-context). Re-loop
   to convergence.
5. Dispatch code-quality reviewer (fresh-context). Re-loop to
   convergence.
6. Commit via `jj describe -m '<conventional commit message>'`.
   Use `jj new -m ''` to advance `@`.
7. Mark task `completed`.

Task 11g is a thin wrapper (~30 LOC) — use a single combined
reviewer subagent.

Task 11h is substantive (~50-100 LOC of structural induction
plus possibly a new submodule) — use separate spec and
code-quality reviewers.

Task 12 is a read-only audit — no implementer, just a reviewer
subagent confirming axiom-cleanliness across every public
declaration.

The final code-quality review is a read-only audit — no
implementer, just a single fresh-context reviewer with a broad
scope.

## Operational rules (unchanged)

The hard rules from the original execution handoffs still
apply:

- No `jj git push` without user line-by-line review.
- No raw mutating `git` subcommands.
- No `noncomputable`, no `admit`, minimal `Classical`.
- One concern per branch; followup candidates go to task #654.
- Markdownlint cleanliness on any `.md` touched.
- `lake build` only (never `lake env lean`, never `lake clean`).

## Definition of done

Session 3 (Task 11 completion) is done when:

1. Task 11g (`compileER_runFor_bprod`) lands as a `feat(ertok)`
   commit.
2. Task 11h (top-level `compileER_runFor`) lands as a
   `feat(ertok)` commit (and the `Top.lean` submodule, if the
   implementer chooses that placement).
3. Task 12 (axiom audit) confirms every public declaration in
   `GebLean/LawvereERKSim/*.lean` is `[propext, Quot.sound]`-only.
4. The final holistic code-quality review reports either no
   blocking findings or a followup-only finding set.
5. `lake build` clean across the whole tree.
6. `markdownlint-cli2 '**/*.md'` reports 0 errors.
7. `doctoc '**/*.md' --check` reports clean.

After "done", Task 11 (#616) and Tasks 12/Final (#617, #618)
can all be marked `completed`. T2 is then ready for whatever
follow-on phase the user chooses (Task 13 onward; or shift to
the followup branch at task #654).

## Resumption recipe (one-line)

```text
Read docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-session3-handoff.md
and dispatch the Task 11g implementer subagent per the workflow above.
```

## References

- Session-2 execution handoff (just-completed work):
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-session2-handoff.md`.
- Session-1 execution handoff:
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-handoff.md`.
- Bprod sub-division plan (binding for sub-tasks bprod.0–6):
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`.
- Broader Task 11 handoff (binding for Task 11g/11h):
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.
- T2 plan (binding):
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- Bsum sub-division (template precedent):
  `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`.
- Project rules:
  `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `.claude/rules/fork-upstream-flow.md`.
