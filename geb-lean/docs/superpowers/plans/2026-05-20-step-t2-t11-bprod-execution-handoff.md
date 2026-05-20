# Step T2 Task 11e.6.a.iii-bprod — execution handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Execution mode](#execution-mode)
- [Required reading (in order)](#required-reading-in-order)
- [Prerequisite: runtime correction](#prerequisite-runtime-correction)
- [Sub-task execution order](#sub-task-execution-order)
- [Per-sub-task workflow](#per-sub-task-workflow)
- [Operational rules (binding)](#operational-rules-binding)
- [Patterns to apply](#patterns-to-apply)
- [Definition of done](#definition-of-done)
- [Resumption recipe (one-line)](#resumption-recipe-one-line)
- [References](#references)

<!-- END doctoc -->

Resumption prompt for the session that executes the bprod
pre-stop chain. The sub-division plan it implements has been
adversarially reviewed to convergence (three rounds; commit
`ad6c1b4a`).

## Execution mode

Use the `superpowers:subagent-driven-development` skill. For
each sub-task, dispatch a fresh implementer subagent with a
self-contained brief (paste the relevant sub-task text into
the prompt; do not let the subagent read the sub-division
plan file directly). After the implementer reports, dispatch
a spec-compliance reviewer subagent and a code-quality
reviewer subagent (both fresh-context). Loop until both pass.

Lemma signatures, structure-clause shapes, and the sub-task
DAG declared in the sub-division plan are non-negotiable (per
the project's "Non-negotiable interfaces for formalising
pre-existing objects" rule). Subagents may adjust internal
proof tactics freely.

## Required reading (in order)

The next session, before dispatching any subagent, must read:

1. **Sub-division plan (binding)**:
   `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`.
2. **Session handoff (prior context)**:
   `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`
   — focus on the "Patterns learned" section (19 patterns)
   and the "What remains" section.
3. **Bsum landed chain (reference model)**:
   `GebLean/LawvereERKSim/BSum.lean` (5036 lines). The bprod
   chain mirrors bsum structurally; reading the landed proofs
   gives the implementer the cleanest template.
4. **Bprod compiler source (target)**:
   `GebLean/LawvereERKSim/Compiler.lean` lines 1190-1440
   (`compileFrag_bprod`); lines 1594-1639
   (`compileER_runtime`, including the bprod branch).

The other landed submodules (`Compiler.lean`, `Embedding.lean`,
`Loops.lean`, `Atoms.lean`, `Comp.lean`) are consumed via
their public API; do not re-read end-to-end unless a subagent
returns with an unresolved API question.

## Prerequisite: runtime correction

**Before starting any work on sub-task bprod.6 (final
assembly), the `compileER_runtime` bprod branch must be
patched.** The current per-iter slack `5 * f.interp ctx_f`
cannot bound the actual multiplicative cost `9 * A_i * B_i`
(where `A_i = natBProd i (...)` grows multiplicatively). The
sub-division plan's sub-task 6 documents two candidate
corrections; the recommended one rewrites the bprod branch as
a `List.range bound`-fold mirroring `natBProd`'s `Nat.rec`
shape.

The runtime fix lands as a separate `fix(ertok):` commit on
`Compiler.lean`, before bprod.6 begins. After the fix:

1. `lake build` must complete cleanly.
2. `mcp__lean-lsp__lean_verify compileER_runtime` must show
   `[propext, Quot.sound]` only (no new axiom dependencies).
3. `compileER_numRegs_eq_compileERFrag_numRegs` must still
   type-check (it does not depend on the runtime).

Sub-tasks bprod.0 through bprod.5 do *not* depend on the
runtime; they can proceed without the patch. The runtime
correction blocks only bprod.6 specifically.

## Sub-task execution order

The sub-division plan's DAG (lines 219-258 of the plan)
enumerates 17 sub-tasks. Execute them in this order:

1. **bprod.0** — PC-bound infrastructure (~200-250 LOC in
   `BProd.lean` + ~80-100 LOC in `Compiler.lean` for the
   size lemma co-located with `compileFrag_bprod`).
2. **bprod.1.a** — zero-sweep correctness alias (~80-120
   LOC).
3. **bprod.1.b** — prologue correctness alias (~80-120 LOC).
4. **bprod.1.c.0** — accUpdate prep (two transferLoops)
   (~400-500 LOC).
5. **bprod.1.c.1** — inner-mul partial invariant + base
   (~250-350 LOC).
6. **bprod.1.c.2** — inner-mul step `(j → j + 1)` (~550-700
   LOC).
7. **bprod.1.c.3** — inner-mul outer iteration `(j = 0 → B)`
   (~350-450 LOC).
8. **bprod.1.c.4** — accUpdate assembly (~400-500 LOC).
9. **bprod.1.d** — f-body embedding (~400-500 LOC).
10. **bprod.2** — outer partial invariant + base case
    (~500-600 LOC).
11. **bprod.3.phase_i0** — zero-sweep preservation (~650-750
    LOC).
12. **bprod.3.phase_i1** — prologue preservation (~600-700
    LOC).
13. **bprod.3.phase_i2** — f-body preservation, consumes
    `ih_f` (~550-650 LOC).
14. **bprod.3.phase_i3** — accUpdate + incR + goto (~700-850
    LOC).
15. **bprod.4** — induction glue `(i → i + 1)` (~300-400 LOC).
16. **bprod.5** — outer iteration `(i = 0 → v 0)` (~450-550
    LOC).
17. **(runtime correction)** — separate `fix(ertok):` commit
    on `Compiler.lean`.
18. **bprod.6** — final assembly
    `compileER_pre_stop_correct_bprod` (~350-450 LOC).

After bprod.6 lands, the bprod pre-stop chain is complete.
The wrapper Task 11g (`compileER_runFor_bprod`) is then a
three-line composition with the existing
`compileER_pre_stop_to_runFor` bridge — recipe step 4 of the
broader Task 11 handoff.

## Per-sub-task workflow

For each sub-task `bprod.X`:

1. **Mark the task `in_progress`** in `TaskList`.
2. **Dispatch the implementer subagent**: paste the sub-task
   text from the sub-division plan into the prompt. Include
   the project rules summary (no `noncomputable`, no
   `admit`, no `Classical.choice` beyond mathlib transitives,
   constructive Lean only). The implementer writes the
   declarations into the appropriate location (`BProd.lean`
   for bprod-specific work; `Compiler.lean` for the size
   lemma in bprod.0 and the runtime correction).
3. **Verify the implementer's claim**: run `lake build` and
   confirm no errors. Run `mcp__lean-lsp__lean_verify` on
   every new declaration the implementer adds; the axiom
   list must be `[propext, Quot.sound]` only.
4. **Dispatch the spec-compliance reviewer subagent**: brief
   it with the sub-task signature shape from the sub-division
   plan and ask it to verify the implementer's declarations
   match. Findings are returned to the implementer for fixes;
   loop until clean.
5. **Dispatch the code-quality reviewer subagent**: brief it
   with the project style rules (`.claude/rules/lean-coding.md`,
   `.claude/rules/markdown-writing.md`, the mathlib upstream
   guides) and ask it to flag style issues. Findings are
   applied; loop until clean.
6. **Commit the landed sub-task** via `jj describe -m`. Use
   commit message form `feat(ertok): <sub-task short
   description>` (e.g. `feat(ertok): bprod accUpdate prep
   correctness`). Run `jj new -m ''` afterwards to move `@`
   to a fresh empty descendant.
7. **Mark the task `completed`** in `TaskList`. Update the
   T2 followup item list if the sub-task surfaced new
   followup candidates.
8. **Move to the next sub-task.**

## Operational rules (binding)

These rules from `CLAUDE.md` and `.claude/rules/` apply
throughout execution:

- **No `jj git push` without user line-by-line review.** All
  pushes are gated; the next session must not push to origin
  or upstream without explicit user approval.
- **No raw mutating `git` subcommands.** Use `jj` for all
  state-mutating operations.
- **No `noncomputable` anywhere.** Minimise `Classical`.
- **No `admit` ever.** `sorry` is permitted as a temporary
  stand-in *between* commits when working with skills that
  need it (e.g. `lean4:sorry-filler-deep`), but never in a
  committed file.
- **One concern per branch.** All bprod sub-tasks land on
  the current branch; refactoring opportunities surfaced
  during execution go to followup task #654 (do not bundle
  them with sub-task commits).
- **Markdownlint cleanliness.** Run `markdownlint-cli2` and
  `doctoc` (via `npx -y doctoc`) before each commit that
  touches `.md`.
- **No LLM-drafted text in user-facing channels.** Commit
  messages, PR descriptions, GitHub issue/PR comments are
  user-authored. The bprod sub-task commits are *not* user-
  facing in this sense (they live in the local branch's
  history) and the implementer drafts them.

## Patterns to apply

The session-1 handoff lists 19 patterns learned across the
comp and bsum chains. The patterns most relevant to bprod
execution:

- **Pattern 1**: Lean-core `Fin.cases` over mathlib's
  `fin_cases` (Classical-pulling).
- **Pattern 9**: `let` over `set` for omega-syntactic
  identity.
- **Pattern 14**: `.pop`-emitted body's embedded length is
  `frag.instrs.size - 1`.
- **Pattern 16**: inlined-conjunction convention for
  closed-form T0 phases (applies to bprod
  phase_i0/phase_i1/phase_i3 and to bprod.1.c.{0,2}).
- **Pattern 17**: `URMState.init` reduction quirk —
  introduce regs-equation lemmas with `URMState.init` inline
  *before* binding `let f_init := ...`; this surfaced during
  bsum phase_i2 and will recur in bprod phase_i2.

The sub-division plan calls out each pattern at the relevant
sub-task. The implementer must respect them.

## Definition of done

The bprod execution phase is complete when:

1. All 17 sub-tasks + the runtime correction have landed as
   commits on the current branch.
2. `lake build` completes cleanly across the whole tree
   (target: ~1545+ jobs after BProd.lean lands).
3. Every new declaration's `mcp__lean-lsp__lean_verify`
   output shows `[propext, Quot.sound]` only.
4. `markdownlint-cli2 '**/*.md'` reports 0 errors.
5. `doctoc '**/*.md' --check` (or `npx -y doctoc --check`)
   reports clean.
6. The bprod followup items accumulated during execution are
   appended to task #654.

After "done", recipe step 4 of the broader Task 11 handoff
(`compileER_runFor_bprod` wrapper) is the next step.

## Resumption recipe (one-line)

```text
Read docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-handoff.md
and dispatch the bprod.0 implementer subagent per the workflow above.
```

## References

- Sub-division (binding):
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.md`.
- Sub-division round-1 review:
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.review-1.md`.
- Sub-division round-2 review:
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.review-2.md`.
- Sub-division round-3 review (CONVERGED):
  `docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-prestop-subdivision.review-3.md`.
- Broader Task 11 handoff (prior session):
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.
- T2 plan (binding):
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- Bsum sub-division (template for bprod):
  `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`.
- Project rules:
  `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `.claude/rules/fork-upstream-flow.md`.
