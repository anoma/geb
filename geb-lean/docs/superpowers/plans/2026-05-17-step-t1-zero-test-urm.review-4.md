# Round-4 plan adversarial review — step T1

Reviewer: fresh-context `general-purpose` Agent (round 4).
Artefact under review:
[`2026-05-17-step-t1-zero-test-urm.md`](2026-05-17-step-t1-zero-test-urm.md).
Prior rounds:
[`.review-1.md`](2026-05-17-step-t1-zero-test-urm.review-1.md),
[`.review-2.md`](2026-05-17-step-t1-zero-test-urm.review-2.md),
[`.review-3.md`](2026-05-17-step-t1-zero-test-urm.review-3.md).

## Verification log

All structural and code-content obligations of rounds
1–3 are met:

- `URMInstr` 5 constructors, `URMProgram` invariants
  (both), `URMState` / `step` / `runFor` / `init`
  signatures, `runFor_add` tactic discipline (`simp
  only` + `change`), Task 6's file-path axiom check
  and §4.4 absent-declarations check — all present and
  correct.
- No `sorry`, `admit`, `noncomputable`, `Classical.*`,
  bare `simp`, `show`-where-`change`-belongs.
- Spec coverage complete.
- No banned style words.

## Findings

### Blocker

#### B1. Raw mutating `git` subcommands

CLAUDE.md § Rules: "No raw mutating `git` subcommands.
... Use `jj` for state-mutating operations." Tasks 1.5,
2.3, 3.4, 4.4, 5.3, 6.4 each instruct `git add` and
`git commit -m "..."`. These are blocked-prompt forms
under the project's PreToolUse hook.

**Response:** fix. Replace each `git add ...; git
commit -m "..."` block with the project's `jj`
equivalent:

```bash
jj describe -m "..."
jj new
```

`jj describe` sets the description on the current
working-copy commit; `jj new` creates a fresh
working-copy commit for the next task's edits to land
on. Both are `jj` operations and pass the hook's
allowlist.

### Serious

None.

### Minor

#### M1. `Nat.zero_add` rewrite chain wording

**Response:** reject-as-cosmetic-taste (the prose
correctly identifies the rewrite chain even if the
phrasing is loose; `simp only` will discharge).

#### M2. `deriving Inhabited` fallback rationale

**Response:** reject-as-cosmetic-taste (defence-in-depth
note; the kept-or-dropped fallback does not affect
correctness).

#### M3. `rm -f .olean` cache reach

**Response:** reject-as-cosmetic-taste (the project uses
this pattern across kToER plans; consistent).

### Cosmetic-taste

#### C1. Tourlakis citation duplication

**Response:** reject-as-cosmetic-taste (the two copies
serve plan-level and source-level readers
separately).

#### C2. Banned-adjective list partial

**Response:** reject-as-cosmetic-taste.

#### C3. Test-discipline alignment with `MEMORY.md`

**Response:** reject-as-cosmetic-taste.

## Convergence assessment

Round 4 does NOT converge: 1 blocker, 0 serious findings.

After replacing the `git commit -m` invocations with
`jj describe -m / jj new`, the plan is convergent.
