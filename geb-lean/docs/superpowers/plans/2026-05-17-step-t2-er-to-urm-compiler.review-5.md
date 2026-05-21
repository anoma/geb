# T2 plan adversarial review — round 5

## Author responses

- **N1** (T1 module docstring doesn't mention arity
  parameter): **fix.** Step 0.1 now includes a one-line
  instruction to update the T1 module's
  `## Main definitions` entry for `URMProgram` to
  describe it as the arity-indexed structure.
- **N2** (rename "T1 prerequisite" subsection for naming
  symmetry with "Divergence from spec §5.1"): **fix.**
  Renamed to "Divergence from spec §4.1's `URMProgram`
  field shape". TOC regenerated.

## Summary

Round 5 reviews the architecture refactor applied between
rounds 4 and 5: lifting `URMProgram`'s `numInputs` from a
field to a type parameter (Task 0) and re-expressing
`CompiledFragment a` as `extends URMProgram a`. The refactor
is empirically verified to elaborate against current mathlib:
the T1 refactor (parameterised `URMProgram`, `URMState`,
`URMState.step`, `URMState.runFor` with reduction lemmas,
`URMState.init`) elaborates cleanly; the new
`CompiledFragment a extends URMProgram a` factoring composes
correctly with both the `where`-clause and the `let .. ;
{ .. }` structure-literal idioms used by the atom-compiler
bodies (Steps 5.1–5.4); the auto-generated `.toURMProgram`
projection is exposed at the spec-named-declarations list and
referenced in `compileER`. All round-3 fix mechanisms
(`URMInstr.fromRawList`, `fin_cases <;> first | rfl | ...`,
`URMInstr.reindex`, `URMInstr.shiftPC`) survive the refactor
unchanged.

Counts: 0 blockers, 0 serious, 0 minor, 2 nits.

The plan is converged for the purposes of this review cycle.

## Architecture refactor verification

### Task 0 T1 refactor elaborates

Harness reproducing all six Task-0 sub-steps:

```lean
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Basic

namespace GebLean
namespace ZeroTestURM

inductive URMInstr (r : ℕ) : Type
  | assign (i : Fin r) (c : ℕ) : URMInstr r
  | inc (i : Fin r) : URMInstr r
  | dec (i : Fin r) : URMInstr r
  | jumpZ (i : Fin r) (l₁ l₂ : ℕ) : URMInstr r
  | stop : URMInstr r
  deriving Repr, DecidableEq, Inhabited

@[ext] structure URMProgram (numInputs : ℕ) where
  numRegs : ℕ
  instrs : Array (URMInstr numRegs)
  outputReg : Fin numRegs
  inputRegs : Fin numInputs → Fin numRegs
  inputRegs_inj : Function.Injective inputRegs
  outputReg_not_input : ∀ i, inputRegs i ≠ outputReg

@[ext]
structure URMState {a : ℕ} (P : URMProgram a) where
  pc : ℕ
  regs : Fin P.numRegs → ℕ

-- step, runFor, runFor_zero, runFor_succ, runFor_add, init
-- per the plan's Steps 0.3–0.5
end ZeroTestURM
end GebLean
```

Result: `{"success":true,"timed_out":false,"diagnostics":[]}`.

The `runFor_add` proof (the only non-trivial proof in T1)
elaborates verbatim with the refactored signature. The
`URMState.init` body's switch from `Fin P.numInputs` /
`List.finRange P.numInputs` to `Fin a` / `List.finRange a`
type-checks.

### `extends URMProgram a` factoring elaborates

Two structure-literal forms appear in atom-compiler bodies:

1. `where`-block syntax (Step 5.1 `compileFrag_zero`).
2. `let rawList := ..; have hBound := ..; { ..fields.. }`
   structure-literal syntax (Steps 5.2–5.4).

Both forms compose correctly with `extends URMProgram a`.
The flat-literal syntax provides all nine fields directly
(six inherited from `URMProgram a` plus three reserved-zero
additions); Lean's elaborator accepts this without requiring
a `toURMProgram := ...` parent field. Empirical confirmation
via `lean_run_code`:

```text
def compileFrag_zero : CompiledFragment 0 where
  numRegs := 2 ; numRegs_pos := by decide ; ...
  -- (full plan Step 5.1 body)
-- Result: success, no diagnostics.

def compileFrag_succ : CompiledFragment 1 :=
  let rawList := ...
  have hBound : URMRaw.boundedBy 4 rawList := ...
  { numRegs := 4 ; numRegs_pos := by decide ; ... }
-- Result: success, no diagnostics.

#check @CompiledFragment.toURMProgram
example : URMProgram 0 := compileFrag_zero.toURMProgram
-- Result: well-typed.
```

The auto-generated `.toURMProgram` projection has the
expected signature `{a : ℕ} → CompiledFragment a →
URMProgram a` and is correctly referenced in Step 9.2's
`compileER` definition (`(compileERFrag e).toURMProgram`).

### Round-3 fix mechanisms unaffected

- **`URMInstr.fromRawList`** (round-3 S2'): unchanged at
  Step 2.4 (plan lines 862–867); referenced at Steps 5.2,
  5.3, 5.4 (lines 1249, 1337, 1459).
- **`fin_cases <;> first | rfl | ...`** (round-3 S1'):
  unchanged at Step 5.4 (plan lines 1465–1466,
  `inputRegs_inj`) and the disjointness invariants (lines
  1469, 1472).
- **`URMInstr.reindex`, `URMInstr.shiftPC`**: unchanged at
  Steps 6.1–6.2 (plan lines 1550–1577).
- **Four `sorry` placeholders**: at Tasks 6.3 (line 1604),
  7.1 (line 1747), 8.1 (line 1933), 11.1 (line 2226), plus
  the seven per-case `sorry`s in Step 11.2 (lines 2237–2249).
  Each carries its Lean-syntax skeleton scaffold from earlier
  rounds.

### Task numbering consistency

Spot-checks:

- Commit messages: task 0 of 13 (line 630); task 1 of 13
  (line 756); task 2 of 13 (line 909); task 3 of 13 (line
  991); task 4 of 13 (line 1150); task 5 of 13 (line 1495);
  task 6 of 13 (line 1707); task 7 of 13 (line 1868); task 8
  of 13 (line 1962); task 9 of 13 (line 2035); task 10 of 13
  (lines 2196–2197); task 11 of 13 (line 2337); task 12 of
  13 — Step T2 complete (line 2490).
- "13 tasks: Task 0 prerequisite plus 12 T2 tasks" at plan
  line 265.
- TOC includes Task 0 entry at line 102.

All consistent.

### Markdownlint

`markdownlint-cli2 'docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md'`
yields `Summary: 0 error(s)`.

## Spec deviation note

Spec §4.1 presents `URMProgram` with `numInputs : ℕ` as a
field; the refactor lifts it to a type parameter. The plan
records this at lines 301–333 under the "T1 prerequisite:
arity-indexing `URMProgram`" subsection of "Architecture
overview", showing the before/after structure declarations
side by side and noting "The refactor is mathematically
vacuous". This is a presentational deviation only (no
semantic content change). The existing "Divergence from spec
§5.1's global prelude discipline" subsection (lines 354–379)
is a separate, more substantive deviation that warrants its
explicit "Divergence" heading; the arity-indexing change is
sufficiently transparent under "T1 prerequisite" without
requiring a parallel "Divergence" heading. See nit N2 below
for an optional naming-symmetry suggestion.

## Nits

### N1. T1 module docstring at `## Main definitions` could mention arity

The T1 module's docstring at
`GebLean/Utilities/ZeroTestURM.lean` lines 30–46 lists
`URMProgram`, `URMState`, etc. as bullet entries without
mentioning the arity parameter. After Task 0's refactor:

- Line 30–33: `URMProgram` description does not reference
  `numInputs` as a field, so the abstract description
  remains accurate without edits.
- Line 36–37: `URMState` description does not mention the
  `{a : ℕ}` parameter; remains accurate.

The plan does not direct an edit to this docstring under
Task 0. Per CLAUDE.md's "Document only the persistent"
rule, the existing prose remains persistent (it describes
the abstract notion of `URMProgram`/`URMState` rather than
their concrete field shape). No action required; flagging
for transparency in case the user prefers a one-line
"Arity is a type parameter of `URMProgram`" insertion.

### N2. Optional naming symmetry with "Divergence from spec §5.1"

The plan's "Divergence from spec §5.1's global prelude
discipline" subsection (lines 354–379) and the new "T1
prerequisite: arity-indexing `URMProgram`" subsection (lines
301–333) both document deviations from the spec. The latter
is mathematically vacuous and presentational, the former is
substantive. The asymmetric naming ("T1 prerequisite" vs
"Divergence from spec") is acceptable but a user wanting
maximum consistency could rename the T1 subsection to
"Divergence from spec §4.1's URMProgram field shape" or
similar, with an explicit "Mathematically vacuous;
presentational only." qualifier. Strictly cosmetic.

## Sign-off

Plan converged on round-5 review (zero blocker, zero
serious).

The architecture refactor (Task 0 T1 prerequisite plus
`extends URMProgram a` factoring at Task 3) has been
empirically verified to elaborate against current mathlib via
`lean_run_code`. All round-3 fix mechanisms (S1'
invariant-proof patterns, S2' `URMInstr.fromRawList`),
`URMInstr.reindex` / `URMInstr.shiftPC` helpers, and the
four-`sorry`-with-scaffold structure for Tasks 6.3, 7.1, 8.1,
11 survive the refactor unchanged. Task numbering ("task N
of 13") is consistent across all 13 commit messages. The
plan remains `markdownlint-cli2`-clean. Two nits (N1 T1
module-docstring update; N2 naming symmetry) are
informational and do not require a round 6.
