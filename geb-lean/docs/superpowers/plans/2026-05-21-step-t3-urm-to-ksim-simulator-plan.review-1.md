# Round-1 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 1).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

## Verification log

- Read `docs/process.md` § Adversarial review (lines 131 – 227):
  protocol binding; reviewer is read-only; severity definitions
  confirmed. Pass.
- Read the artefact in full (1833 lines). Confirmed task layout:
  Task 0 through Task 9, ten tasks.
- Read the binding spec
  (`docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`);
  tabulated spec coverage. Pass.
- Verified cited line numbers in
  `GebLean/Utilities/ZeroTestURM.lean`: `URMInstr` at `:89`,
  `URMProgram` at `:122`, `URMState` at `:143`, `URMState.step`
  at `:155`, `URMState.runFor` at `:179`, `URMState.runFor_succ`
  at `:192`, `URMState.runFor_add` at `:199`,
  `URMState.runFor_halted_invariant` at `:213`, `URMState.init`
  at `:254`. Pass.
- Verified cited line numbers in `GebLean/LawvereKSim.lean`:
  `KMor1` inductive at `:34`, `KMor1.simrec` constructor at
  `:50`, `KMor1.level` at `:105`. Pass.
- Verified cited line numbers in
  `GebLean/LawvereKSimInterp.lean`: `KMor1.interp_zero` at
  `:86`, `KMor1.interp_proj` at `:98`, `KMor1.interp_simrec`
  at `:162`, `KMor1.simrecVec_zero` at `:180`,
  `KMor1.simrecVec_succ` at `:193`. Pass.
- Verified cited line numbers in
  `GebLean/Utilities/KArith.lean`: `KMor1.one` precedent at
  `:31`, `KMor1.pred` at `:44`, `KMor1.cond` at `:222`,
  `KMor1.interp_cond` at `:249`, `KMor1.notEq1` at `:278`.
  Pass.
- Confirmed `GebLean.LawvereERKSim.compileER_runFor` exists at
  `GebLean/LawvereERKSim/Top.lean:89`. Pass.
- Confirmed `Fin.lastCases_last` and `Fin.lastCases_castSucc`
  are available (used in `GebLean/LawvereBTInterp.lean:627,
  637, 669`).
- Confirmed `Fin.lastCases_eq_last_or_castSucc` is not a
  mathlib name reachable in `.lake/packages/mathlib`.
- Confirmed `private def KMor1.X` pattern is valid inside
  `namespace GebLean` (`KArith.lean:358` shows
  `private def KMor1.monusSwapped`).
- Confirmed `GebLean.lean` imports `Utilities.KArith` at line
  161 and follows alphabetical order.
- Cross-checked project-memory warnings at
  `feedback_fin_cases_pulls_classical_choice.md` and
  `feedback_simp_if_pos_sorryAx_leak.md` against the plan's
  tactic choices.
- Re-read mathlib `commit.html` convention; scanned commit
  messages in the plan for tense compliance.

## Findings

### Blocker

1. **Step 7.8's register-`j` step case is a `sorry` placeholder
   with a "Mirror Step 7.7's structure" instruction.** Violates
   the writing-plans skill's "Similar to Task N (without
   repeating the code)" and "Steps that describe what to do
   without showing how" rules.

   *Author response — fix.* Step 7.8 replaced with concrete
   tactic blocks for each of the five `URMInstr` constructor
   cases plus past-end, mirroring Step 7.7's six-block
   structure with `Function.update` propagation. Each case
   ~12 – 15 LOC; total ~80 LOC for the register-`j` branch.
   The implementer-subagent uses `mcp__lean-lsp__lean_goal`
   per case for goal-shape verification (matching T2's
   per-fragment plan style).

2. **Steps 3.5 and 3.6 are draft / replace iterations
   embedded in the plan, not implementable steps.** A fresh
   implementer following them verbatim would commit `sorry`-
   laden code, violating "`sorry` only between commits".

   *Author response — fix.* Steps 3.5 and 3.6 deleted; Step
   3.7's complete two-lemma decomposition
   (`interp_pcDispatchFrom_match`, `_default`) stands alone.
   Numbering of subsequent steps adjusted.

3. **`fin_cases` in Step 3.11 is a known `Classical.choice`
   leak per project memory
   `feedback_fin_cases_pulls_classical_choice.md`.** The
   "if Classical.choice appears, replace …" after-the-fact
   note is not the right pattern.

   *Author response — fix.* Step 3.11 replaced to use Lean-
   core `Fin.cases` plus explicit `match i with | ⟨0, _⟩ =>
   exact hpred | ⟨1, _⟩ => exact hb0 | ⟨2, _⟩ => exact
   hrecur` for the inner discharge, guaranteeing axiom-clean
   compilation on the first attempt.

### Serious

1. **Step 3.11's level-closure step is broken.**
   `Nat.le_of_eq_of_le (max_eq_right hsup) hsup` does not
   type-check.

   *Author response — fix.* Replaced with
   `Nat.max_le.mpr ⟨le_refl 1, hsup⟩` (or `omega` after the
   `rw [hcond_level]` reveals a `Nat.max 1 hsup ≤ 1` goal
   with `hsup : … ≤ 1` in scope).

2. **Step 7.7's `rw [interp_pcDispatch_match]` cannot fire on
   the unevaluated `stepCtx (Fin.last _)` form produced by
   `simrecVec_succ`.** A bridging `show` / `simp only` step is
   missing.

   *Author response — fix.* Step 7.7 amended: before the
   `rw [interp_pcDispatch_match …]` invocation, insert
   `show (stepFamily P (Fin.last P.numRegs)).interp stepCtx
   = _; simp only [Fin.last]` to align
   `stepCtx (Fin.last _)` with the simrec previous-component
   slot, then apply `h_pc_eq`. The same bridging applies
   inside the register-`j` case (Step 7.8's new content).

3. **`Fin.last (a + P.numRegs + 1)`'s arity may not unify
   with `Fin (a + 1 + (P.numRegs + 1))` definitionally.**

   *Author response — fix.* Step 5.1's `I_prev` rewritten to
   construct the index explicitly:
   `KMor1.proj ⟨a + 1 + P.numRegs, by omega⟩`. This pins the
   `Fin` index numerically and avoids elaboration depending
   on `Nat.add`'s associativity normal form.

4. **Step 1.5 / 1.6's `simp only [Finset.univ.sup, …]` is not
   a valid simp invocation** (`Finset.univ.sup` is dot
   notation, not a lemma).

   *Author response — fix.* Step 1.5's `natK_level` body
   rewritten to `unfold KMor1.level; simp only
   [Finset.sup_singleton, KMor1.succ, ih]` (and analogously
   for Step 1.6's `natK'_level`, using `Finset.sup_empty`
   for the empty `Fin 0` family).

5. **Step 8.1's `convert ... using 1` is order-dependent.**

   *Author response — fix.* Step 8.1 replaced with an
   explicit chain: `simp only [simulate, KMor1.interp_simrec,
   Fin.cons_zero, Fin.cons_succ]`, then
   `exact (simulate_step_match P v y).2 P.outputReg`.
   `Fin.cons_zero` and `Fin.cons_succ` are existing mathlib
   `@[simp]` lemmas that handle the context-splitting
   deterministically.

6. **Step 5.6's `split <;> split <;> simp <;> decide` chain
   is brittle.**

   *Author response — fix.* Step 5.6 amended to do one
   explicit `cases` per `URMInstr` constructor and close each
   with `decide` on the level-bound goal (or `omega` after a
   concrete numeric reduction). Each per-constructor block is
   ~3 – 5 LOC; total ~40 LOC.

7. **`URMState.runFor_succ_back`'s namespace placement
   creates `GebLean.KSimURMSimulator.URMState.runFor_succ_back`,
   confusingly parallel to `GebLean.ZeroTestURM.URMState`.**

   *Author response — fix.* Helper renamed to
   `runFor_succ_init_back` and placed inside
   `namespace GebLean.KSimURMSimulator` directly (not under a
   sub-namespace `URMState`). The `URM` half of the helper's
   role is then clear from its body, not its name. Step
   7.1's insertion point and Step 7.10's axiom-audit name
   updated accordingly.

### Minor

1. **Commit messages use past tense / past participles.**
   "interp simp lemmas and level=0 lemmas included" →
   "include …"; "axiom hygiene confirmed" → "confirm axiom
   hygiene".

   *Author response — fix.* All commit message bodies
   rewritten in imperative present tense; "confirmed" →
   "confirm" throughout.

2. **Step 1.1's `grep` expectation cites line ~270, but the
   `cond` block ends at line 264.**

   *Author response — fix.* Step 1.1's expected-output prose
   corrected: insertion point is between lines 264 (end of
   `cond`'s `example`) and 266 (start of `notEq1`'s
   docstring).

3. **Step 0.3's commit-hash check is uninformative.**

   *Author response — fix.* Step 0.3 reworded to check by
   description glob:
   `jj log -r 'description(glob:"docs(ertok)*plan*")'
   --no-graph` returning the plan commit's description.

4. **Step 2.1's empty `namespace … end namespace` skeletons
   are structural placeholders.**

   *Author response — fix.* Step 2.1 amended to commit
   directly to the two-namespace layout without empty
   skeletons. Later steps reference the existing namespaces
   by inserting at clearly named points.

5. **`Fin.lastCases_eq_last_or_castSucc` is not a mathlib
   name.**

   *Author response — fix.* Steps 4.3 and 5.6 rewritten to
   use `induction j using Fin.lastCases with | last => … |
   cast r => …` (the project-idiomatic form per
   `GebLean/LawvereBTInterp.lean:627, 637, 669`).

6. **`grep` commands need cwd context.**

   *Author response — fix.* All `grep` invocations in Steps
   1.1 and 9.1 now use absolute paths
   (`/home/terence/git-workspaces/geb/geb-lean/GebLean/…`).

7. **Plan narration of why back-peel is needed talks past the
   helper-lemma proof shape.**

   *Author response — fix.* Step 7.1's prose amended: "inside
   the helper lemma the fixed-`s` problem does not arise (the
   `s` parameter is fully general); only the consumer (the
   step case of `simulate_step_match`) hits the
   fixed-`s := init P v` trap, which is why the helper is
   needed at all."

### Cosmetic-taste

1. **Step 0.3's expected-output names a specific round-4
   commit description.**

   *Author response — fix.* Per Minor M3, Step 0.3 now
   matches by description glob rather than naming a specific
   commit message verbatim.

2. **The plan's `**Architecture:**` block uses `**bold**`
   markup-for-emphasis.**

   *Author response — reject-as-cosmetic-taste.* The
   `**Goal:** ... **Architecture:** ... **Tech Stack:**`
   triple is the writing-plans skill's prescribed plan
   header format (it ships verbatim in the skill template).
   Stripping the bold deviates from the skill's template
   without project benefit.

3. **Steps 1.2 through 1.6 emit five separate code blocks
   followed by five separate `lake build` invocations.**

   *Author response — reject-as-cosmetic-taste.* The
   "one declaration at a time" project rule is binding (per
   `.claude/rules/lean-coding.md` § Proof guidelines § One
   definition at a time). Consolidating the build
   invocations would defeat the per-declaration verification
   discipline that catches type errors before they
   compound.

4. **The plan uses "the implementer" in workflow notes but
   "the user" in Step 9.7 ("Hand off the topic branch for
   user line-by-line review").**

   *Author response — fix.* Step 9.7's "user" retained (per
   `CLAUDE.md` § Style guidelines, "the user" is the correct
   generic). Workflow-note references to "the implementer"
   tightened to "the implementer (subagent during SDD
   execution)" where the distinction matters; otherwise
   left as-is.
