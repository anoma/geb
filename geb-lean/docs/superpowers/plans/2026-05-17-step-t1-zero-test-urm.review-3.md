# Round-3 plan adversarial review — step T1

Reviewer: fresh-context `general-purpose` Agent (round 3).
Artefact under review:
[`2026-05-17-step-t1-zero-test-urm.md`](2026-05-17-step-t1-zero-test-urm.md).
Round-1 / round-2 reviews:
[`.review-1.md`](2026-05-17-step-t1-zero-test-urm.review-1.md),
[`.review-2.md`](2026-05-17-step-t1-zero-test-urm.review-2.md).

## Spec-coverage verification

All §4, §10, §12.1, §12.2 obligations covered. ✓.

## Executability verification

Lean code blocks syntactically valid; `check-axioms.sh`
file-path argument matches script header (verified).
`URMState.step`'s `match P.instrs[s.pc]'h with` is valid
Lean 4 syntax. `runFor` and reduction lemmas elaborate
in the expected shape under explicit-`P` signature.

## Type-consistency verification

`URMInstr r` → `URMProgram.instrs : Array (URMInstr
numRegs)` → `URMState (P : URMProgram)` with `regs :
Fin P.numRegs → ℕ`. `URMState.step` and `URMState.runFor`
both have `P : URMProgram` explicit per spec §4.2. ✓.

## Constructive-discipline verification

`List.find?` over `List.finRange`; no `Classical.*`,
no `noncomputable`. ✓.

## Findings

### Blocker

None.

### Serious

#### S1. Bare `simp` violates `simp only` discipline

Step 4.2's `runFor_add` proof, `| zero` case, uses
`simp [URMState.runFor]` (bare `simp` with an unfolding
hint). The plan's own style block (line 112) requires
`simp only [...]`. Under `warningAsError = true`,
the flexible-tactic linter will fail this build.

**Response:** fix. Replace `| zero => simp
[URMState.runFor]` with
`| zero => simp only [Nat.zero_add, URMState.runFor]`.

### Minor

#### M1. `git commit -m` rather than `jj describe`

CLAUDE.md prefers `jj` for state-mutating operations.
The kToER side's plans used `git commit -m` and hit the
hook's permission prompt at execution time; the
implementer must approve interactively.

**Response:** reject-as-cosmetic-taste. Consistency with
the kToER-side plans (which all use `git commit -m`)
matters more than switching mid-project; the permission
prompt is recoverable. Future plans may adopt `jj
describe -m / jj new` if the convention shifts.

#### M2. Step 1.4 fallback covers only `Inhabited`, not `DecidableEq`

**Response:** reject-as-cosmetic-taste. `DecidableEq
(URMInstr r)` derives cleanly when all field types are
`Fin r`/`ℕ`/empty — no fallback needed in practice.

#### M3. Coverage table cites §4.4 as "Implicit" without explicit lint

**Response:** fix (subsumed by M7).

#### M5. PC-label phrasing off-by-one

`URMProgram` docstring (line 322): "PC labels range over
`{0, …, instrs.size}`". Should be `{0, …, instrs.size −
1}` per spec lines 252–253.

**Response:** fix. Update the docstring text to match
spec phrasing.

#### M6. `runFor_succ` shape vs mathlib `Function.iterate_succ` convention

**Response:** reject-as-cosmetic-taste. The
left-fold-style shape matches `runFor`'s definition; a
complementary `runFor_succ'` (right-fold) can be added in
T2 if a compiler-correctness proof needs it.

#### M7. Step 6.3 lint should include the §4.4 absent-declarations check

**Response:** fix. Extend Step 6.3 lint to enumerate
explicitly: "No `URMComputes` structure, no `urmSeq` /
`urmIf` / `urmLoop` combinators, no `urmDecToReg` /
`urmCopyReg` helpers — these are explicitly forbidden
by spec §4.4."

### Cosmetic-taste

#### C1-C6 acceptable as written

**Response:** reject-as-cosmetic-taste.

## Convergence assessment

Round 3 does NOT converge: 0 blocker, 1 serious finding.

After S1 (the one-line `simp` → `simp only` fix), plus
the M5/M7 prose fixes, the plan is convergent.
