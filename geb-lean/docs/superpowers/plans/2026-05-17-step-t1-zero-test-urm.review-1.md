# Round-1 plan adversarial review — step T1 (zero-test URM kernel)

Reviewer: fresh-context `general-purpose` Agent (round 1).
Artefact under review:
[`2026-05-17-step-t1-zero-test-urm.md`](2026-05-17-step-t1-zero-test-urm.md).
Spec under transcription:
[`../specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](../specs/2026-05-16-er-to-k-via-cslib-urm-design.md).

Author response convention as in spec rounds.

## Spec-coverage verification

All §4, §10, §12.1, §12.2 obligations covered by Tasks
1–6. ✓.

## Executability verification

Two executability gaps in Task 5 (B1, B3) and one in
Task 4 (B2). See Findings.

## Type-consistency verification

`URMState.step`'s `P` argument explicit-vs-implicit
divergence between plan (implicit) and spec (explicit).
See S1.

## Constructive-discipline verification

`Fin.find` correctly avoided (round-6 spec fix
respected); `List.find?` used. ✓.

## Findings

### Blocker

#### B1. Task 5 duplicates `initSmokeProgram` (broken first; correct second)

Step 5.2 emits two `private def initSmokeProgram`
declarations into the same namespace with intermediate
prose telling the executor to use the second. An
executor copy-pasting verbatim hits a duplicate
definition.

**Response:** fix. Remove the first (broken)
`initSmokeProgram`; keep only the 2-register version.
The disjoint-register version respects
`outputReg_not_input` straightforwardly.

#### B2. Task 4 smoke-test `example` proof body is unprovable as written

The `by_cases ... unfold ... simp only [↓reduceDIte] ...
rw [h0] ... rfl` chain does not elaborate because
`match smokeProgram.instrs[s.pc]'h` does not reduce
with `s.pc` symbolic, and `rw [h0]` cannot rewrite
inside dependent array indices.

**Response:** fix. Remove the Task 4 smoke test
entirely. The universal `runFor_zero` / `runFor_succ`
/ `runFor_add` lemmas suffice for T1; program-specific
tests defer to T2's `compileER_runFor` correctness
statement.

#### B3. Task 5 example hits the kernel-reduction trap

`simp only [List.finRange, List.find?] ... rfl` won't
close the goal because `List.find?` reduction needs the
specific `List.find?_cons` simp lemmas, and `List.finRange`
unfolds to a `pmap` that obstructs `rfl`.

**Response:** fix. Remove the Task 5 final `example`
entirely. The smoke-test discipline of T1 is confined to
universal reduction lemmas; program-specific examples
defer to T2 / T3.

### Serious

#### S1. `step` and `runFor` argument convention diverges from spec

Spec §4.2 declares `(P : URMProgram)` explicit; plan
Task 3 makes it implicit `{P : URMProgram}`.

**Response:** fix. Use explicit `(P : URMProgram)` in
both `URMState.step` and `URMState.runFor`'s signatures
per spec.

#### S2. Task 3 commits an empty test module

Empty `GebLeanTests/Utilities/ZeroTestURM.lean` is
committed with vacuous "all tests pass" claim.

**Response:** fix. Drop the test-module creation from
Task 3 entirely. Tasks 4–5 add inline universal
reduction lemmas to the main module; no separate
GebLeanTests module is needed for T1. (Subsequent steps
T2+ will introduce a test module when programs are
actually compiled and run.)

#### S3. `runFor_add` proof outline has arithmetic-form mismatch

The `change (URMState.step s).runFor (m + n) = ...`
tactic will fail because `m + 1 + n` does not reduce to
`(m + n) + 1` definitionally.

**Response:** fix. Rewrite the proof using `simp only
[Nat.succ_add, URMState.runFor]` and `ih`:

```lean
theorem URMState.runFor_add
    (P : URMProgram) (s : URMState P) (m n : ℕ) :
    s.runFor (m + n) = (s.runFor m).runFor n := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    show s.runFor (m + 1 + n) = (s.runFor (m + 1)).runFor n
    rw [Nat.add_right_comm m 1 n, Nat.add_one]
    show (URMState.step s).runFor (m + n)
      = (URMState.step s |>.runFor m).runFor n
    exact ih (URMState.step s)
```

If this still does not elaborate cleanly, fall back to
`omega`-driven arithmetic rewrites.

#### S4. Mathlib imports contradict spec §9.1's claim

Verified: `List.finRange` lives in
`.lake/packages/mathlib/Mathlib/Data/List/FinRange.lean`
(mathlib, not Lean core). The spec's "no mathlib reach"
claim is wrong.

**Response:** fix. Two complementary edits:

- (Spec) Update spec §9.1 to acknowledge the mathlib
  dependency: "depends on Lean core and on
  `Mathlib.Data.List.FinRange` for `List.finRange`; uses
  `List.find?` (Lean core), `Function.update` (mathlib),
  and basic `Fin`/`Array` machinery."
- (Plan) Replace `Mathlib.Data.Fin.Basic` and
  `Mathlib.Data.List.Basic` with the specific minimal
  imports: `Mathlib.Data.List.FinRange` (for
  `List.finRange`) and `Mathlib.Logic.Function.Basic`
  (for `Function.update`). Document the exact
  dependency in the file-structure section.

#### S5. Module docstring grammar: "A unlimited register machine"

**Response:** fix. "A unlimited" → "An unlimited".

#### S6. `check-axioms.sh` argument grammar is wrong

The script (read at `scripts/check-axioms.sh` lines
27–32) takes a file or directory path, not a Lean
module name. Correct invocation:

```bash
bash scripts/check-axioms.sh GebLean/Utilities/ZeroTestURM.lean
```

**Response:** fix. Replace the Task 6 Step 6.2
invocation with the file-path form. Also clarify the
expected output format ("STANDARD_AXIOMS allowlist
covers `propext`, `Quot.sound`, `quot.sound`; any other
axiom dependency emits a `FAIL` line").

### Minor

#### m1. Tourlakis uses "Unbounded Register Machine" not "unlimited"

**Response:** fix. Replace "unlimited" with
"unbounded" in the module docstring (matches Tourlakis
2018's term and is the standard expansion of URM in
the literature).

#### m2. `deriving` claim could be brittle

Plan asserts `deriving Repr, DecidableEq, Inhabited`
will succeed but doesn't test it.

**Response:** reject-as-cosmetic-taste (the `deriving`
mechanism is well-tested in Lean 4 + mathlib for these
classes on inductive types over `ℕ` + `Fin`; if it
fails, Step 1.5's `lake build` catches it immediately).

#### m3. Task 4 commit message accuracy depends on B2 fix

Subsumed by B2's response (remove the smoke test).

**Response:** fix. After B2's fix, update Task 4's
commit message to "feat(urm): URMState.runFor with
universal reduction lemmas".

#### m4. "structurally invalid" language

**Response:** reject-as-cosmetic-taste ("invalid" in
this context means "fails the structural invariant
`outputReg_not_input`", which is precise; the prose
follows the fix).

#### m5. Internal consistency note (non-finding)

Reviewer notes the file-structure section's import
order matches Task 1's import order; no fix needed.

**Response:** reject-as-cosmetic-taste (no finding).

#### m6. `GebLean.lean` import-placement convention unclear

The reviewer notes that `GebLean.lean` currently has
only `GebLean.<TopLevel>` imports, not
`GebLean.Utilities.*` imports.

**Response:** fix. Per the kToER-side convention
(`GebLean.lean` does NOT import `GebLean.Utilities.*`
directly; utility modules are imported only by their
consumers), drop the "Modify: `GebLean.lean`" step
from Task 1. The new `Utilities/ZeroTestURM.lean`
will be imported by the consuming module
`LawvereERKSim.lean` in T2; T1's plan only creates the
module, doesn't expose it via the umbrella import.

### Cosmetic-taste

#### c1. "Adversarial-review readiness" section is meta-process

**Response:** fix. Remove the section; it's redundant
with `docs/process.md`.

#### c2. Commit-message footer "step T1" vs "Step T1"

**Response:** fix. Capitalise "Step" to match spec §11.

#### c3. Task 1 docstring "structurally distinct" cross-reference

**Response:** reject-as-cosmetic-taste (current wording
is precise; the spec §2.1 link is implicit via the
Tourlakis citation in the same docstring).

## Convergence assessment

Round does NOT converge: 3 blockers, 6 serious
findings.
