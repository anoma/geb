# Round-7 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 7).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

Round 6 was a fresh-context review and produced one blocker
(R6-B1), three serious (R6-S1, R6-S2, R6-S3), seven minor, and
five cosmetic-taste findings. Author applied R6-B1, R6-S1,
R6-S2, R6-S3 inline; minors and cosmetic-taste findings were
deferred. This round re-examines those four applied fixes from a
fresh context and rechecks the R4 / R5 fixes underneath.

## Verification log

- Read [`docs/process.md`](../../process.md) § Adversarial
  review (lines 131 – 227): reviewer protocol, severity ladder,
  convergence criterion. Confirmed read-only constraint.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  end-to-end (892 lines); cross-checked spec §§ 3 – 6 against
  the plan's Task 1 – Task 9 layout.
- Read the plan in full (2381 lines). Task and step numbering
  intact; Step 7.1.5 (R4 helper extraction) remains between
  Step 7.1 and Step 7.2 with no downstream collisions.
- Read prior reviews
  [`review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md),
  [`review-2.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-2.md),
  [`review-3.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-3.md),
  [`review-4.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-4.md),
  [`review-5.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-5.md),
  and
  [`review-6.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-6.md);
  catalogued open items and re-verified the R4 / R5 / R6 fixes
  independently rather than trusting round 6's verification.
- Read landed
  [`GebLean/LawvereKSimInterp.lean`](../../GebLean/LawvereKSimInterp.lean)
  at `KMor1.simrecVec_succ` (lines 193 – 209): confirmed the
  dite-context's else-branch yields
  `KMor1.simrecVec h g params n ⟨idx.val - (a + 1), _⟩`.
- Read landed
  [`GebLean/Utilities/KArith.lean`](../../GebLean/Utilities/KArith.lean)
  at `KMor1.cond` / `KMor1.interp_cond` (lines 222 – 262):
  confirmed `interp_cond` rewrites to
  `if ctx 0 = 0 then ctx 1 else ctx 2`.
- Read landed
  [`GebLean/Utilities/ZeroTestURM.lean`](../../GebLean/Utilities/ZeroTestURM.lean)
  at `URMState.step` (lines 155 – 173): confirmed that
  `URMState.step` is `if h : s.pc < P.instrs.size then match
  P.instrs[s.pc]'h with | … else s`. The body's `match` arms
  produce record literals for `.assign` / `.inc` / `.dec` /
  `.jumpZ` and return `s` for `.stop`. The `.jumpZ` arm sets
  `{ pc := if s.regs i = 0 then l₁ else l₂, regs := s.regs }`;
  the projection `(URMState.step P s).regs j` is therefore
  opaque until `URMState.step` is unfolded.
- Re-verified the R6-B1 fix (Step 7.8 `.jumpZ` block now
  includes `step_ctx_eval_simrec` + `Fin.ext` bridge before
  `rw [ih_regs i]`): plan lines 1767 – 1817. The bridge at
  slot `a + 1 + i.val` to `i.castSucc` is structurally analogous
  to Step 7.9's `.jumpZ` bridge. The fix is correct as written.
- Re-verified the R6-S1 fix (helper-coupling comment in
  Step 7.1.5 docstring): plan lines 1481 – 1488 add a paragraph
  noting that the helper is the sole `simrecVec_succ`-shape
  coupling site in T3. The comment accurately describes the
  coupling.
- Re-verified the R6-S2 fix (`at *` defensive rewrite in Step
  7.9 `.inc` / `.dec` h_eq=true sub-cases): plan lines 1987 and
  2023 now read `rw [show i = j from Fin.ext h_eq] at *`. The
  fix is correct as written; see Finding S1 for a hygiene
  concern about its interaction with the previously-rewritten
  hypothesis `h_eq : i.val = j.val`.
- Re-verified the R6-S3 fix (drop URM-side chain in Step 7.9
  `.jumpZ`): plan lines 2035 – 2052 now omit
  `simp only [URMState.step]; rw [dif_pos h_inbounds]; simp
  only [h_instr]`. **This fix introduces a new blocker — see
  Finding B1 below.** The R6-S3 review's rationale (that the
  URM-side is "already `(runFor y).regs j` after `cases
  h_instr`") presupposes that `(URMState.step P s).regs j`
  reduces definitionally to `s.regs j` for the jumpZ arm,
  which is not the case in landed Lean because
  `URMState.step`'s outer `if` must first be eliminated.
- Re-verified R5-B1 (`rw [ih_pc]` in Step 7.8 `.assign` /
  `.inc` / `.dec`): plan lines 1738, 1752, 1766. The K-side at
  each site reduces to a `simrecVec`-then-`+ 1` form after the
  `step_ctx_eval_simrec` + `Fin.ext` bridge; `rw [ih_pc]`
  rewrites the `simrecVec` term to the URM-side `pc`, leaving
  `pcVal + 1 = pcVal + 1` closed by implicit `rfl`. The fix is
  correct as written. See Finding M1 for a defensive-form
  alternative.
- Re-verified R5-B2 (`rw [show i = j from Fin.ext h_eq]` in
  Step 7.9 `.inc` / `.dec` h_eq=true): see R6-S2 verification
  above. The R5-B2 substantive rewrite is preserved (and
  R6-S2's `at *` is layered on top).
- Re-verified the R4 helper extraction (`step_ctx_eval_simrec`
  in Step 7.1.5, plan lines 1489 – 1507): body uses `show (if
  h₁ : slot < a + 1 then _ else KMor1.simrecVec … ⟨slot - (a +
  1), by omega⟩) = _; rw [dif_neg (by omega)]`. Beta reduction
  on the LHS `(fun idx => …) ⟨slot, h_slot_bound⟩` exposes the
  dite; the `dif_neg` selects the else-branch under
  `h_slot_ge : a + 1 ≤ slot`. The body is correct.
- Re-fetched mathlib upstream guides
  ([`naming.html`](https://leanprover-community.github.io/contribute/naming.html),
  [`style.html`](https://leanprover-community.github.io/contribute/style.html),
  [`doc.html`](https://leanprover-community.github.io/contribute/doc.html),
  [`commit.html`](https://leanprover-community.github.io/contribute/commit.html))
  via the digest in
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md).
- Cross-referenced project memories
  [`feedback_simp_if_pos_sorryAx_leak.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_simp_if_pos_sorryAx_leak.md),
  [`feedback_mathlib_choice_in_functor_cat.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_mathlib_choice_in_functor_cat.md),
  [`feedback_urmstate_init_let_reduction.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_urmstate_init_let_reduction.md),
  [`feedback_fin_cases_pulls_classical_choice.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_fin_cases_pulls_classical_choice.md)
  against the plan's tactic choices.

## Findings

### Blocker

1. **Step 7.9's `.jumpZ` block (plan lines 2035 – 2052) omits
   the URM-side reduction chain after the R6-S3 fix; the final
   `exact ih_regs j` cannot close because the URM-side remains
   `(URMState.step P (URMState.runFor P (URMState.init P v) y)).
   regs j`, not `((URMState.init P v).runFor P y).regs j`.** The
   R6-S3 review reasoned that "the URM-side is already `(runFor
   y).regs j` … because the `step` result is `{s with pc := …,
   regs := s.regs}` and `.regs j` reads `s.regs j` unchanged."
   This reasoning requires `(URMState.step P s).regs j` to
   reduce definitionally to `s.regs j` for the `.jumpZ` arm. In
   landed Lean
   ([`GebLean/Utilities/ZeroTestURM.lean:155 – 173`](../../GebLean/Utilities/ZeroTestURM.lean#L155)),
   `URMState.step` is `if h : s.pc < P.instrs.size then match
   P.instrs[s.pc]'h with | … else s`. The outer `if` is not
   eliminated until the proof tactically commits to one branch
   (via `simp only [URMState.step]; rw [dif_pos h_inbounds]`
   or `unfold URMState.step` plus `dif_pos`), and the inner
   `match` is not reduced until `simp only [h_instr]` propagates
   the case-equation. Without those reductions, the URM-side
   stays as `(URMState.step P s).regs j` — an opaque term that
   is not syntactically `(runFor y).regs j`.

   The other five constructors of Step 7.9 (`.assign`, `.inc`,
   `.dec`, `.stop`) all retain the chain `simp only
   [URMState.step]; rw [dif_pos h_inbounds]; simp only
   [h_instr]`; only `.jumpZ` was stripped per R6-S3. The chain
   is operationally necessary for the URM-side reduction; R6-S3
   misdiagnosed it as redundant. The Step 7.8 `.jumpZ` block
   (PC component, plan lines 1767 – 1817) retains the chain
   correctly.

   The fix is to restore the URM-side chain in the Step 7.9
   `.jumpZ` block:

   ```lean
   | jumpZ i l₁ l₂ =>
     simp only [branches_j, h_instr, v_j_prev, KMor1.interp_proj]
     simp only [URMState.step]
     rw [dif_pos h_inbounds]
     simp only [h_instr]
     -- K^sim returns v_j_prev = ih_regs j after bridging …
     rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
           (by omega) (by omega)]
     rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
             : Fin (P.numRegs + 1))
           = j.castSucc
           from by apply Fin.ext; simp [Fin.castSucc]; omega]
     exact ih_regs j
   ```

   This mirrors the `.stop` block immediately below (plan lines
   2053 – 2064), which retains the chain even though `.stop`
   also leaves `.regs` unchanged. After the chain reduces the
   URM-side to `s.regs j`, where `s := URMState.runFor P
   (URMState.init P v) y`, the `exact ih_regs j` discharge
   matches the goal.

   The defect was masked in round 6 by an incorrect
   definitional-reduction assumption. The R6-S3 finding should
   have been re-categorised as Cosmetic-taste (an unused-tactic
   linter warning at execution, no correctness consequence) and
   the URM-side chain retained.

   *Author response — TBD.*

### Serious

1. **Step 7.9's `.inc` / `.dec` h_eq=true sub-cases close with
   `rw [show i = j from Fin.ext h_eq] at *` after `rw [ih_regs
   j]`; the `at *` rewrites the hypothesis `h_eq : i.val =
   j.val` to `j.val = j.val`, which is benign but emits an
   `unusedHypothesis` linter warning at execution.** Plan lines
   1987 and 2023. The `at *` form rewrites in the goal and in
   every hypothesis; `h_eq` is in scope as `i.val = j.val`,
   and after the rewrite becomes `j.val = j.val`. Lean's
   `unusedHypothesis` linter (if enabled) will flag the
   degenerate `h_eq`. The cleaner defensive form per the R6-S2
   review's alternative suggestion is `exact (congrArg (· + 1)
   (congrArg _ (Fin.ext h_eq))).symm` (avoiding `rw` entirely),
   or alternatively `rw [show i = j from Fin.ext h_eq]`
   (without `at *`, since the K-side does not need the rewrite
   propagated to hypotheses — only the URM-side mention of `i`
   in the goal needs to become `j`). The `at *` form is
   correct but over-broad. The same `at *` applies in the
   `.dec` h_eq=true sub-case (plan line 2023).

   *Author response — TBD.*

2. **The Step 7.8 `.jumpZ` block (plan lines 1767 – 1817)
   contains two `simp only [KMor1.interp_natK']` invocations
   after the `by_cases h_zero` split (plan lines 1814 and
   1817), but the earlier `simp only` at line 1768 – 1770
   already includes `KMor1.interp_natK'`.** The K-side after
   the first simp already has `natK' …`-occurrences reduced
   to literal constants `l₁` and `l₂`. The post-`if_pos`/
   `if_neg` `simp only [KMor1.interp_natK']` invocations are
   operationally noops; they will either silently succeed
   without effect or emit `Simp made no progress` warnings
   (per Lean's `simp`-noop linter behavior).

   This is a hygiene concern parallel to R6-S3 (operationally
   redundant simp invocations), but in this case the rewrite
   genuinely is a noop, not load-bearing. The fix is to drop
   the second `simp only [KMor1.interp_natK']` from each
   sub-branch of the `by_cases`, leaving the closure to
   implicit `rfl`:

   ```lean
   by_cases h_zero : ((URMState.init P v).runFor P y).regs i = 0
   · simp only [KMor1.interp_cond]
     rw [if_pos h_zero]
   · simp only [KMor1.interp_cond]
     rw [if_neg h_zero]
   ```

   *Author response — TBD.*

3. **Step 7.8's `.jumpZ` block comment at plan line 1780
   reads "mirroring Step 7.9's `.jumpZ` block" but the Step
   7.9 `.jumpZ` block (post-R6-S3) is now structurally
   different (no URM-side chain) and references the register
   index `j` not `i`.** After Finding B1 above is fixed (URM-
   side chain restored in Step 7.9's `.jumpZ`), the two blocks
   will be structurally analogous again, differing only in the
   register index (`i` for Step 7.8 because `.jumpZ` reads
   register `i` for the PC update; `j` for Step 7.9 because the
   register-`j` component reads its own previous value). Until
   B1 is fixed, the comment is doubly inaccurate: it claims
   structural parity that does not hold and references a block
   whose URM-side discharge is currently broken.

   *Author response — TBD.*

### Minor

1. **The R5-B1 `rw [ih_pc]` closure in Step 7.8 `.assign` /
   `.inc` / `.dec` (plan lines 1738, 1752, 1766) relies on
   implicit `rfl` after the `simrecVec _ _ y (Fin.last P.numRegs)`
   subterm is rewritten to `pcVal`.** The goal post-rewrite is
   `pcVal + 1 = pcVal + 1`, closed by implicit `rfl`. This
   works in the current goal shape but is more fragile than
   `rfl` made explicit. The defensive form is `rw [ih_pc]; rfl`
   or `exact congrArg (· + 1) ih_pc`. Re-flagged from round 5
   M-class.

   *Author response — TBD.*

2. **The Step 7.1.5 helper docstring (plan lines 1473 – 1488)
   states that "All call sites consume the helper through its
   declared signature only — per plan round-6 serious finding
   R6-S1," but this claim describes the call-site contract, not
   the helper-body coupling that R6-S1 raised.** R6-S1's
   substantive concern was that the helper-body's `show` clause
   directly pattern-matches the `simrecVec_succ` dite-shape,
   creating a single-point-of-failure if the upstream lemma
   changes shape. The docstring's added paragraph does
   acknowledge this ("If that lemma's shape changes … the
   body's `show` will need to be re-stated"), so the coupling
   is described; the "consume … through its declared signature
   only" claim is true but tangential to R6-S1's substantive
   concern. The docstring is acceptable as written; a minor
   re-phrasing would make the helper-body-vs-call-site
   distinction sharper. Not blocking.

   *Author response — TBD.*

3. **Spec § 3.4's `branches_pc` pseudocode (lines 211 – 219 of
   the design doc) still uses the wildcard `_` arm; the plan
   (Step 5.2 at plan lines 1075 – 1092) enumerates `.assign`,
   `.inc`, `.dec` explicitly (per R4-S3 / R5-M1 / R6-M2).** The
   spec-plan synchronisation gap remains. The plan diverges
   from the spec; either the spec's pseudocode should be
   updated to enumerate the three constructors or the plan
   should cite a spec § noting the divergence. Re-flagged
   from rounds 5 and 6.

   *Author response — TBD.*

4. **The Step 7.4 base case at plan lines 1551 – 1552 ends
   `show (0 : ℕ) = (URMState.init P v).pc; unfold URMState.init`
   without an explicit trailing `rfl`.** `unfold` does not
   close goals; the closing `rfl` is implicit. The defensive
   form is an explicit trailing `rfl`. Re-flagged from round 5
   (R5-M2) and round 6 (R6-M7).

   *Author response — TBD.*

5. **The Step 7.8 and Step 7.9 `set pcVal := … with hpc`
   declarations (plan lines 1685 and 1920) bind `hpc` but
   never use it post-R4-B1.** Re-flagged from rounds 5 (R5-S7
   reclassified Minor) and 6 (R6-M4). Lean's `unusedVariable`
   linter will flag this. The defensive form is `set pcVal :=
   ((URMState.init P v).runFor P y).pc` (without `with hpc`).

   *Author response — TBD.*

6. **The defer-to-execution `mcp__lean-lsp__lean_goal` notes
   accumulate** (R3-M1 / R4-M2 / R5-M3 / R6-M5). Re-flagged.
   Plan lines 717 – 719, 1289 – 1293, 1862 – 1866. Each new
   note documents a tactic-fork at execution time; the plan's
   "every step is independently executable" property weakens
   with each. Consider extracting the notes into a separate
   "Execution-time tactical reference" section so that the
   per-step instructions remain self-contained.

   *Author response — TBD.*

7. **Plan Step 8.6 commit-message body still enumerates 19
   declaration names inline** (R3-M4 / R4-M4 / R6-M6). Re-flagged.

   *Author response — TBD.*

8. **The Step 7.10 `lake build` expectation "zero `sorry`
   warnings, zero errors, zero warnings"** (R4-M6 / R5-M5
   deferred). Re-flagged at minor level. If the implementation
   emits expected unused-variable warnings (e.g., from `hpc`
   per M5 above, or the simp-noop warnings per Serious 2
   above), the "zero warnings" target is unachievable without
   first applying the M-class fixes.

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's "Note:" paragraphs after each Lean code block
   describe lemma-name provenance rather than step-outcome**
   (R3-C1 / R4-C1 / R5-C1 / R6-C1 reaffirmed). Reaffirming.

   *Author response — TBD.*

2. **Step 0.3's `jj log` filter is broad** (R3-C2 / R4-C2 /
   R5-C2 / R6-C2). Reaffirming.

   *Author response — TBD.*

3. **The 19 enumerated `bash scripts/check-axioms.sh`
   invocations across Tasks 1 – 8 and Step 9.3 inflate plan
   LOC** (R3-C3 / R4-C3 / R5-C3 / R6-C3). Reaffirming.

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat
   `per spec § X.Y` references in a fixed format** (R3-C4 /
   R4-C4 / R5-C4 / R6-C4). Reaffirming.

   *Author response — TBD.*

5. **The `step_ctx_eval_simrec` + `Fin.ext` bridge is invoked
   ~10 times across Steps 7.8 / 7.9** (R5-C5 / R6-C5).
   Reaffirming. A second helper bridging directly from the
   dite-ctx slot to `simrecVec ... y k.castSucc` (with `k` a
   parameter and the slot computed as `a + 1 + k.val`) would
   collapse the ~70 LOC of duplication to a single call per
   site.

   *Author response — TBD.*

## Convergence status

**NOT CONVERGED.** Round 7 found:

- 1 Blocker (B1: Step 7.9 `.jumpZ` URM-side chain incorrectly
  removed by R6-S3; `exact ih_regs j` cannot close against an
  opaque `(URMState.step ...).regs j` URM-side).
- 3 Serious (S1: `at *` in R6-S2 fix over-broadens to `h_eq`;
  S2: redundant `simp only [KMor1.interp_natK']` after the
  R6-B1 `by_cases h_zero` split; S3: Step 7.8 `.jumpZ` comment
  now inaccurate given Step 7.9 `.jumpZ`'s post-R6-S3 form).
- 8 Minor (M1 R5-B1 implicit `rfl`; M2 docstring framing;
  M3 spec-plan wildcard sync; M4 `unfold` without `rfl`;
  M5 unused `hpc` binding; M6 lean_goal notes; M7 commit
  message enumeration; M8 lake-build zero-warnings target).
- 5 Cosmetic-taste (reaffirmed).

The blocker is a regression introduced by the R6-S3 fix.
Round 6's reviewer reasoned that `URMState.step`'s `.jumpZ`
arm's `regs := s.regs` field would reduce definitionally,
making the `simp only [URMState.step]; rw [dif_pos h_inbounds];
simp only [h_instr]` chain redundant on the URM-side. In
landed Lean, the outer `if` of `URMState.step` is not
eliminated definitionally; the simp chain is operationally
necessary to expose the `.regs := s.regs` field. The fix is
straightforward: restore the URM-side chain in Step 7.9's
`.jumpZ` block, leaving it parallel to the other five
constructors in that block.

Serious findings S1 – S3 should be addressed but each is a
hygiene concern rather than a correctness defect. Minor and
cosmetic-taste findings are non-blocking per the project's
convergence criterion.

A round-8 dispatch is required after B1 is fixed (and ideally
after S1 – S3 are addressed as well, since each is a
foreseeable build-warning trap at execution time).
