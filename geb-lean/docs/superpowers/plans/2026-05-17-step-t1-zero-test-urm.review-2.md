# Round-2 plan adversarial review — step T1

Reviewer: fresh-context `general-purpose` Agent (round 2).
Artefact under review:
[`2026-05-17-step-t1-zero-test-urm.md`](2026-05-17-step-t1-zero-test-urm.md).
Round-1 review:
[`.review-1.md`](2026-05-17-step-t1-zero-test-urm.review-1.md).

## Spec-coverage verification

All §4, §10, §12.1, §12.2 obligations covered by Tasks
1–6. ✓.

## Executability verification

Three executability defects: stale `Files:` headers
(B1), `runFor_add` base case (S1), Step 4.3 duplication
(S2). See Findings.

## Type-consistency verification

`URMState.step` / `URMState.runFor` signatures match
spec §4.2 (explicit `P`). ✓.

Dot-notation receiver inference for `.runFor` works
(elaborates `P` from the receiver's `URMState P` type).

## Constructive-discipline verification

No `Classical.*`, no `noncomputable`. `List.find?` over
`List.finRange` per spec §4.3. ✓.

## Findings

### Blocker

#### B1. Task 3, 4, 5 `Files:` headers contradict their bodies

Task 3 lists `Create: GebLeanTests/Utilities/ZeroTestURM.lean`
and `Modify: GebLeanTests.lean (add import)` in its
`Files:` block. Task 4 and 5 file-blocks repeat the
contradiction (`Modify: GebLeanTests/Utilities/ZeroTestURM.lean
(append)`). The bodies of Tasks 3, 4, 5 do not create
or modify these test artefacts; the round-1 fix
explicitly dropped the test module. The headers are
stale.

**Response:** fix. Remove the `GebLeanTests/...` entries
from Task 3, 4, 5 `Files:` blocks. Each `Files:` block
should list only the main-module modification.

### Serious

#### S1. `runFor_add` base case `| zero => rfl` likely unsound

Goal in the zero case is `s.runFor (0 + n) = (s.runFor
0).runFor n`. RHS reduces to `s.runFor n` by defeq
(`runFor 0 = s`). LHS does NOT reduce: Lean 4's
`Nat.add` is recursion on the right argument
(`n + 0 = n` defeq; `0 + n = n` is the theorem
`Nat.zero_add`, not defeq). So `rfl` fails.

**Response:** fix. Replace `| zero => rfl` with
`| zero => simp [URMState.runFor]` (or `| zero =>
rw [Nat.zero_add]`). The `simp` form is more robust
since `runFor 0 = s` is registered as a simp lemma in
Step 4.2.

#### S2. Step 4.3 duplicates Steps 4.1 and 4.2

Step 4.3 re-quotes the `runFor` definition and
`runFor_zero`/`runFor_succ` lemmas. Literal execution
double-declares them, breaking the build.

**Response:** fix. Delete Step 4.3 entirely. Its content
was redundant after the round-1 P-explicit revision.
Renumber: Step 4.4 → Step 4.3, Step 4.5 → Step 4.4.

### Minor

#### M1. Step 6.4 commit-body cites module-dotted name; Step 6.2 uses file-path

**Response:** fix. Update the Step 6.4 commit message to
cite the file path `GebLean/Utilities/ZeroTestURM.lean`
that Step 6.2 actually invokes.

#### M2. Plan's claim "downstream call sites pass `P` explicitly" is misleading

Dot-notation `(URMState.step P s).runFor n` does NOT
pass `P` explicitly to `runFor`; Lean's
generalised-field-notation infers `P` from the
receiver's `URMState P` type.

**Response:** fix. Reword Step 3.2's trailing paragraph
to "The signature has `P` explicit (matching spec
§4.2); dot-notation call sites such as `s.runFor n`
rely on Lean's generalised field notation to infer
`P` from the receiver's `URMState P` type."

#### M3. `show` vs `change` (lean-coding rule)

Step 4.2's `runFor_add` proof uses `show ... = ...`.
Project rule prefers `change`.

**Response:** fix. Replace both `show` lines in the
`succ` case with `change`.

#### M4. `deriving Inhabited` may not derive for parameterised inductive

If `deriving Inhabited` on `URMInstr r` fails in the
current mathlib pin, the plan should provide a fallback.

**Response:** fix. Add a Step 1.4.1 note: "If `deriving
Inhabited` fails to elaborate (possible on parameterised
inductives in older mathlib pins), fall back to
`instance : Inhabited (URMInstr r) := ⟨.stop⟩` as a
separate declaration."

### Cosmetic-taste

#### C1. Step 3.2 and 5.1 lines near 100-char bound

**Response:** reject-as-cosmetic-taste (lines are within
the limit; linter will flag any overshoot).

#### C2. `Architecture` and `Tech Stack` paragraphs overlap

**Response:** reject-as-cosmetic-taste (the two
paragraphs serve different reader needs — Architecture
for design intent, Tech Stack for build commands).

#### C3. Per-step `rm -f olean; lake build` repetition

**Response:** reject-as-cosmetic-taste (each task is a
separate commit; per-task build verification is the
discipline, not a redundancy).

## Convergence assessment

Round 2 does NOT converge: 1 blocker, 2 serious findings.

After the B1/S1/S2 fixes (each a localised edit), the
plan is plausibly convergent.
