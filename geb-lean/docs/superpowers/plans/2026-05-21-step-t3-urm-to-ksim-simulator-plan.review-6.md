# Round-6 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 6).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

Round 5 was in-context (the same agent that applied the R4 fixes
authored the review). This round re-examines R4-B1, R4-B2, the
R4 `step_ctx_eval_simrec` helper extraction, and the R5-B1 /
R5-B2 / R5-S1 fixes from a fresh context.

## Verification log

- Read [`docs/process.md`](../../process.md) § Adversarial review
  (lines 131 – 227): reviewer protocol, severity ladder,
  convergence criterion. Confirmed read-only constraint.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  end-to-end; cross-checked spec §§ 3 – 6 against the plan's
  Task 1 – Task 9 layout.
- Read the plan in full (2347 lines). Task and step numbering
  intact; Step 7.1.5 (R4 helper extraction) sits between Step 7.1
  and Step 7.2 with no downstream collisions.
- Read prior reviews
  [`review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md),
  [`review-2.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-2.md),
  [`review-3.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-3.md),
  [`review-4.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-4.md),
  and
  [`review-5.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-5.md);
  catalogued open items and re-verified the R4 / R5 fixes
  independently rather than trusting round 5's verification.
- Read the landed
  [`GebLean/LawvereKSimInterp.lean`](../../GebLean/LawvereKSimInterp.lean)
  at the `KMor1.simrecVec_succ` definition (lines 193 – 209):
  confirmed the dite-context's else-branch yields
  `KMor1.simrecVec h g params n ⟨idx.val - (a + 1), _⟩`.
- Read the landed
  [`GebLean/Utilities/KArith.lean`](../../GebLean/Utilities/KArith.lean)
  at `KMor1.cond` / `KMor1.interp_cond` (lines 222 – 262):
  confirmed `interp_cond` rewrites to
  `if ctx 0 = 0 then ctx 1 else ctx 2`.
- Read the landed
  [`GebLean/Utilities/ZeroTestURM.lean`](../../GebLean/Utilities/ZeroTestURM.lean)
  at `URMState.step` (lines 150 – 172) and the
  `runFor_zero` / `runFor_succ` / `runFor_add` reduction lemmas
  (lines 184 – 209): confirmed the `.jumpZ` case returns
  `{pc := if s.regs i = 0 then l₁ else l₂, regs := s.regs}`,
  and that `runFor_succ` is `@[simp]` in the front-peel
  direction `runFor s (n + 1) = runFor (step s) n` (matching the
  Step 7.1 derivation of the back-peel form).
- Re-verified the R4-B1 fix (Steps 7.8 / 7.9 in-bounds branches
  no longer carry `rw [← hpc] at h_ctx_last_pc`): confirmed three
  `rw [← hpc]` strings remain in the plan but all three lie in
  `--`-comment narrative explaining the round-3 misstep
  (plan lines 1674, 1843, 1882). No tactic-position occurrence.
- Re-verified the R4-B2 fix (Fin.ext bridge from
  `Fin.last (a + P.numRegs + 1)` to the explicit-index form):
  Step 7.1.5's `step_ctx_eval_simrec` helper is invoked at the
  `h_ctx_last_pc` derivations (Steps 7.8 / 7.9) and at the
  per-instruction discharges; the bridge `rw [show … = …
  from by apply Fin.ext; simp [Fin.last]; omega]` is inserted
  after each helper call.
- Re-verified R5-B1 (`rw [ih_pc]` replacing `exact ih_pc` in
  Step 7.8 `.assign`/`.inc`/`.dec`): see Finding B1 below — the
  R5-B1 fix is correct for the goal shape it targets.
- Re-verified R5-B2 (`rw [show i = j from Fin.ext h_eq]` in
  Step 7.9 `.inc`/`.dec` h_eq=true sub-cases): see Finding S2
  below — the rewrite as written may fail in one direction.
- Re-verified R5-S1 (jumpZ whitelist replacement with
  `simp only [KMor1.interp_cond]; rw [if_pos h_zero] / [if_neg
  h_zero]; simp only [KMor1.interp_natK']`): see Finding B1 below.
- Re-fetched mathlib upstream guides
  ([`naming.html`](https://leanprover-community.github.io/contribute/naming.html),
  [`style.html`](https://leanprover-community.github.io/contribute/style.html),
  [`doc.html`](https://leanprover-community.github.io/contribute/doc.html),
  [`commit.html`](https://leanprover-community.github.io/contribute/commit.html))
  via the digest in
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md).
- Cross-referenced project memories
  `feedback_simp_if_pos_sorryAx_leak.md`,
  `feedback_mathlib_choice_in_functor_cat.md`,
  `feedback_urmstate_init_let_reduction.md`,
  `feedback_fin_cases_pulls_classical_choice.md` against the
  plan's tactic choices.

## Findings

### Blocker

1. **Step 7.8's `.jumpZ` block calls `rw [ih_regs i]` without
   first bridging the dispatcher's dite-context slot
   `a + 1 + i.val` to the `simrecVec ... y i.castSucc` form
   that `ih_regs i` requires; the rewrite cannot fire.** Plan
   lines 1758 – 1796. After
   `simp only [branches_pc, h_instr, KMor1.interp_comp,
   KMor1.interp_cond, v_j_prev, KMor1.interp_proj,
   KMor1.interp_natK']` the K-side becomes
   `if (dite-ctx ⟨a + 1 + i.val, _⟩) = 0 then l₁ else l₂`,
   where `dite-ctx` is the `simrecVec_succ`-produced context
   ([`LawvereKSimInterp.lean:193 – 209`](../../GebLean/LawvereKSimInterp.lean#L193)).
   `ih_regs i` has type
   `KMor1.simrecVec _ _ y i.castSucc =
   ((URMState.init P v).runFor P y).regs i`. The post-`simp`
   K-side contains the dite-context evaluation, not a literal
   `simrecVec _ _ y i.castSucc` subterm; `rw [ih_regs i]`
   therefore cannot find an instance of `ih_regs i`'s LHS to
   rewrite and fails with "did not find instance of the
   pattern". All other Step 7.8 `.jumpZ` discharge steps depend
   on this rewrite firing; the entire `.jumpZ` block is blocked.
   The fix is to insert, between the first `simp only` chain
   (line 1759 – 1761) and `rw [ih_regs i]` (line 1767), the
   same `step_ctx_eval_simrec` + Fin.ext bridge applied in
   Step 7.9's `.jumpZ` block (plan lines 2013 – 2018):
   `rw [step_ctx_eval_simrec P v y (a + 1 + i.val) (by omega)
   (by omega)]; rw [show (⟨a + 1 + i.val - (a + 1), by omega⟩
   : Fin (P.numRegs + 1)) = i.castSucc from by apply Fin.ext;
   simp [Fin.castSucc]; omega]`. After the bridge, the K-side's
   `dite-ctx ⟨a + 1 + i.val, _⟩` reduces to
   `simrecVec _ _ y i.castSucc`, and `rw [ih_regs i]` fires.
   The defect was masked in round 5: R5-S1 focused on the
   whitelist form but did not trace the goal shape past the
   first `simp only`. Note the asymmetry — Step 7.9's `.jumpZ`
   block does include this bridge (line 2013 invokes
   `step_ctx_eval_simrec` at `a + 1 + j.val`); Step 7.8's
   `.jumpZ` block is missing the analogous bridge at
   `a + 1 + i.val` (where `i` is the jumpZ-tested register).

   *Author response — TBD.*

### Serious

1. **The `step_ctx_eval_simrec` helper's body uses
   `show (if h₁ : slot < a + 1 then _ else
   KMor1.simrecVec … ⟨slot - (a + 1), by omega⟩) = _`, then
   `rw [dif_neg (by omega)]`; the `by omega` inside the helper
   body's `show` discharges `slot - (a + 1) < P.numRegs + 1`
   under the hypotheses `h_slot_bound`, `h_slot_ge` already in
   scope.** Plan lines 1494 – 1497. The `show` replaces
   `(fun idx => …) ⟨slot, h_slot_bound⟩` with the
   beta-reduced if-form. Beta-reduction does fire definitionally
   in Lean 4, so the `show` succeeds; the trailing
   `rw [dif_neg (by omega)]` then selects the else branch
   using `h_slot_ge : a + 1 ≤ slot`. The helper as written is
   correct, but the `_` placeholder in the then-branch and the
   inline `by omega` proofs of the Fin-index sub-bounds make
   the proof's surface form fragile: any future change to the
   `simrecVec_succ` dite-shape (for example, replacing the
   inner `if h₂ : idx.val = 0` with a `match`) would break the
   `show`'s pattern match. Defensive alternative:
   `unfold_let; rw [dif_neg (by omega)]` (which forces beta
   reduction explicitly without committing the helper to a
   specific then-branch shape). This is not a correctness
   defect at the current `simrecVec_succ` definition, but the
   coupling between the helper body and the precise dite-form
   shape warrants a comment at the helper site noting that the
   `show` is the only `simrecVec_succ`-shape coupling in T3.

   *Author response — TBD.*

2. **Step 7.9's `.inc`/`.dec` h_eq=true sub-cases close with
   `rw [show i = j from Fin.ext h_eq]` after `rw [ih_regs j]`,
   but the rewrite direction is wrong-way on the K-side
   (which already mentions `j`, not `i`).** Plan lines 1958 –
   1961 (`.inc`) and 1990 – 1992 (`.dec`). After
   `rw [ih_regs j]`, the K-side is
   `((URMState.init P v).runFor P y).regs j + 1` (for `.inc`).
   The URM-side after `rw [Function.update_apply, if_pos
   (Fin.ext h_eq).symm]` is `((URMState.init P v).runFor P y).
   regs i + 1` (the updated value passed to `Function.update`
   for `.inc i` is `s.regs i + 1`, not `s.regs j + 1`). The
   goal is `(runFor y).regs j + 1 = (runFor y).regs i + 1`.
   The plan's discharge `rw [show i = j from Fin.ext h_eq]`
   substitutes `i := j` throughout the goal. Since the K-side
   contains no `i`, the rewrite affects only the URM-side,
   yielding `(runFor y).regs j + 1 = (runFor y).regs j + 1`,
   which closes by implicit `rfl`. This works in the
   `.inc`/`.dec` direction, but is brittle: `rw` will fail
   with "did not find instance of the pattern `i`" if Lean's
   elaborator has already substituted `i` for `j` elsewhere in
   the goal (for example, if `Function.update_apply`'s
   propagation gives `regs j` instead of `regs i` in some
   step). Defensive form: `rw [show i = j from Fin.ext h_eq]
   at *` (rewriting in all hypotheses too is harmless and
   more robust), or
   `exact (congrArg (· + 1) (congrArg _ (Fin.ext h_eq))).symm`
   (avoiding `rw` entirely). Additionally, the `.assign`
   h_eq=true sub-case (plan lines 1918 – 1927) closes
   implicitly after `rw [Function.update_apply, if_pos
   (Fin.ext h_eq).symm]` — both sides reduce to constant `c`
   — but this implicit `rfl` depends on `KMor1.interp_natK'`
   firing fully to expose the literal `c`; the round-5 S2
   comment-only fix (adding a justification comment) does not
   address the implicit-`rfl` fragility itself.

   *Author response — TBD.*

3. **Step 7.9's `.jumpZ` discharge at plan lines 2004 – 2019
   includes `simp only [URMState.step]; rw [dif_pos
   h_inbounds]; simp only [h_instr]` even though `.jumpZ`'s
   URM-side `regs` field is unchanged (the chain rewrites the
   `pc` field which is then discarded by the `.regs j`
   projection).** The chain operates on the URM-side's
   `(URMState.step P (runFor y)).regs j` expression, reducing
   it to `(runFor y).regs j` (since `.jumpZ` leaves `.regs`
   alone). Whether the `simp only` invocations fire
   silently-noop or emit a warning depends on whether
   `URMState.step`'s `.jumpZ` arm's `regs := s.regs` literally
   matches after the case-split — most likely it does, in
   which case the chain is operationally redundant but
   harmless. Round 5 flagged this as S3 hygiene concern;
   re-flagging in round 6 with no severity change. The
   `unused-tactic` linter (if enabled) would flag the
   redundant `simp only [h_instr]` in this block; the cleaner
   form is `simp only [URMState.step]; rw [dif_pos h_inbounds,
   h_instr]; rfl` or simply omit the URM-side chain entirely
   and observe that the URM-side is already
   `(runFor y).regs j` after `cases h_instr`.

   *Author response — TBD.*

### Minor

1. **The Step 7.1.5 helper docstring claims the helper
   "supplies the per-register-component bridging that
   round 3 left implicit in Step 7.9's `.jumpZ` and `.stop`
   discharges" but the helper does not by itself perform that
   bridging.** Plan lines 1466 – 1469. The helper performs only
   the dite-context evaluation; the per-component bridging
   requires the helper plus a `Fin.ext` rewrite. The docstring
   conflates the two steps. Re-phrase to "supplies the
   dite-context evaluation step of the per-register-component
   bridging" (the `Fin.ext` half is inlined at each call site).

   *Author response — TBD.*

2. **Spec § 3.4's `branches_pc` pseudocode still references the
   wildcard `_` arm even though plan Step 5.2 enumerates
   `.assign`, `.inc`, `.dec` explicitly (R4-S3, R5-M1).**
   Re-flagged from round 5. The spec is upstream of the plan
   and should be updated to match the plan's explicit
   enumeration; alternatively, the plan should cite the spec's
   prose justification for the divergence. Neither path has
   been taken between round 5 and round 6.

   *Author response — TBD.*

3. **Step 7.8 and Step 7.9 each re-derive `h_ctx_last_pc`
   inside their respective refine branches; the derivation is
   character-identical except for the comment text** (R3-M3 /
   R4-M3 / R5 closed). Round 5 declared R3-M3 / R4-M3 closed
   on the basis that the `step_ctx_eval_simrec` extraction
   reduced the duplication "substantially". Round 6 disagrees:
   the duplication remaining is ~10 LOC per refine branch
   (the helper call plus the Fin.ext bridge), and a single
   `have h_ctx_last_pc : … := …` binding above the
   `refine ⟨?_, ?_⟩` (with proper context generalisation)
   would eliminate the duplication. Marked Minor (not Serious)
   because the duplication does not affect correctness or
   buildability; reaffirming the prior round's flag rather
   than re-elevating.

   *Author response — TBD.*

4. **The `set pcVal := ... with hpc` declarations in Steps 7.8
   and 7.9 bind `hpc` but never use it post-R4-B1 fix**
   (R5-C7 / round 5's cosmetic). Re-flagged at minor level
   because Lean's `unusedVariable` linter will flag this at
   execution. The clean form is `set pcVal := ((URMState.init
   P v).runFor P y).pc` (without `with hpc`).

   *Author response — TBD.*

5. **The defer-to-execution `mcp__lean-lsp__lean_goal` notes
   (R3-M1 / R4-M2 / R5-M3) remain at plan lines 717 – 719,
   1289 – 1293, 1828 – 1830, 1843 – 1845, 1859 – 1862.**
   Re-flagged from round 5. The notes accumulate at each
   substantive tactic-fork point. The plan's "every step is
   independently executable" claim weakens with each new note.

   *Author response — TBD.*

6. **The plan's Step 8.6 commit-message body still enumerates
   19 declaration names inline (R3-M4 / R4-M4 deferred).**
   Re-flagged at minor level.

   *Author response — TBD.*

7. **The Step 7.4 base case's `unfold URMState.init` discharge
   ends without an explicit trailing `rfl` (R5-M2).** Plan
   line 1551 – 1552 reads
   `show (0 : ℕ) = (URMState.init P v).pc; unfold URMState.init`.
   `unfold` does not close goals; the closing `rfl` is
   implicit. The defensive form is an explicit trailing `rfl`.
   Re-flagged from round 5.

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's "Note:" paragraphs after each Lean code block
   describe lemma-name provenance rather than step-outcome
   (R3-C1 / R4-C1 / R5-C1 reaffirmed).** Reaffirming.

   *Author response — TBD.*

2. **Step 0.3's `jj log` filter is broad** (R3-C2 / R4-C2 /
   R5-C2). Reaffirming.

   *Author response — TBD.*

3. **The 19 enumerated `bash scripts/check-axioms.sh`
   invocations across Tasks 1 – 8 and Step 9.3 inflate plan
   LOC** (R3-C3 / R4-C3 / R5-C3). Reaffirming.

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat
   `per spec § X.Y` references in a fixed format** (R3-C4 /
   R4-C4 / R5-C4). Reaffirming.

   *Author response — TBD.*

5. **The `step_ctx_eval_simrec` + Fin.ext bridge is invoked
   ~10 times across Steps 7.8 / 7.9** (R5-C5). Each invocation
   is ~7 LOC. A second helper bridging directly from the
   dite-ctx slot to `simrecVec ... y k.castSucc` (with `k` a
   parameter and the slot computed as `a + 1 + k.val`) would
   collapse the ~70 LOC of duplication to a single call per
   site. Re-flagged from round 5 at cosmetic-taste level.

   *Author response — TBD.*

## Convergence status

**NOT CONVERGED.** Round 6 found:

- 1 Blocker (B1: Step 7.8 `.jumpZ` block missing
  `step_ctx_eval_simrec` + Fin.ext bridge before
  `rw [ih_regs i]`).
- 3 Serious (S1: helper-body fragility against future
  `simrecVec_succ` shape changes; S2: `rw [show i = j …]`
  fragility and `.assign` implicit-`rfl` reliance; S3: Step
  7.9 `.jumpZ` URM-side simp chain redundant).
- 7 Minor (M1 docstring conflation; M2 spec wildcard not
  updated; M3 `h_ctx_last_pc` duplication; M4 unused `hpc`
  binding; M5 lean_goal notes; M6 commit message enumeration;
  M7 trailing `rfl`).
- 5 Cosmetic-taste (reaffirmed).

The blocker is a structural omission masked by the in-context
round-5 review's focus on the whitelist form rather than the
goal shape past the first `simp only`. Round 5 verified that
`KMor1.interp_cond` rewrites to `if ctx 0 = 0 then ctx 1 else
ctx 2`, but did not trace that the `ctx 0` argument — the
`v_j_prev P i` projection at slot `a + 1 + i.val` — is the
dispatcher's dite-context, not a `simrecVec ... y i.castSucc`
subterm. Without the bridge, `rw [ih_regs i]` cannot fire.

Recommended fix: insert the `step_ctx_eval_simrec` + Fin.ext
bridge for slot `a + 1 + i.val` (with target `i.castSucc`)
between plan lines 1761 and 1767. The discharge then continues
as currently written; the `by_cases h_zero` / `rw [if_pos /
if_neg h_zero]` chain may become unnecessary (both sides
reduce to the same `if (runFor y).regs i = 0 then l₁ else l₂`
form and close by `rfl`), but is harmless if retained.

Serious findings S1 – S3 should be addressed but each is a
hygiene / fragility concern rather than a correctness defect.
Minor and cosmetic-taste findings are non-blocking per the
project's convergence criterion.

A round-7 dispatch is required after B1's fix is applied.
