# Round-8 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 8).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

Round 7 was a fresh-context review and produced one blocker
(R7-B1: restore the Step 7.9 `.jumpZ` URM-side chain that
round 6's R6-S3 had stripped), three serious (R7-S1: drop
`at *` from the `Fin.ext` rewrite in Step 7.9 `.inc` / `.dec`
h_eq=true sub-cases; R7-S2: drop the post-`by_cases` `simp
only [KMor1.interp_natK']` invocations in Step 7.8 `.jumpZ`;
R7-S3: Step 7.8 `.jumpZ` block comment about parity with
Step 7.9 `.jumpZ`), eight minor, and five cosmetic-taste
findings. The author applied R7-B1, R7-S1, and R7-S2 inline at
commit `0bc73bc6`. R7-S3 and the eight minor / cosmetic-taste
items were deferred. This round re-examines the three applied
fixes from a fresh context and rechecks R6-B1, R5-B1, R5-B2,
and the R4 helper extraction underneath.

## Verification log

- Read [`docs/process.md`](../../docs/process.md) § Adversarial
  review: reviewer protocol, severity ladder, convergence
  criterion. Confirmed read-only constraint and round-isolation
  discipline.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  §§ 3 – 6 end-to-end; cross-checked the spec's `branches_pc`
  (lines 211 – 219), `branches_j` (lines 221 – 234), and
  `stepFamily` level bound (lines 236 – 238) against the
  plan's Task 5 – Task 7 fragments.
- Read the plan in full (2381 lines). Task and step numbering
  intact; Step 7.1.5 (R4 helper extraction) remains between
  Step 7.1 and Step 7.2 with no downstream collisions.
- Read prior reviews
  [`review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md),
  [`review-2.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-2.md),
  [`review-3.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-3.md),
  [`review-4.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-4.md),
  [`review-5.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-5.md),
  [`review-6.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-6.md),
  and
  [`review-7.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-7.md);
  catalogued open items and re-verified the R4 / R5 / R6 / R7
  fixes independently rather than trusting round 7's
  verification.
- Read landed
  [`GebLean/Utilities/KArith.lean`](../../GebLean/Utilities/KArith.lean)
  at `KMor1.cond` / `KMor1.interp_cond` (lines 222 – 262):
  confirmed `interp_cond` is `@[simp]` and rewrites to
  `if ctx 0 = 0 then ctx 1 else ctx 2`.
- Read landed
  [`GebLean/Utilities/ZeroTestURM.lean`](../../GebLean/Utilities/ZeroTestURM.lean)
  at `URMState.step`: confirmed the `.jumpZ` arm sets
  `{ pc := if s.regs i = 0 then l₁ else l₂, regs := s.regs }`
  and the outer `if h : s.pc < P.instrs.size` is not eliminated
  definitionally; therefore the `simp only [URMState.step]; rw
  [dif_pos h_inbounds]; simp only [h_instr]` chain remains
  operationally necessary on the URM-side.
- Re-verified the R7-B1 fix (plan lines 2040 – 2063, Step 7.9
  `.jumpZ`): the URM-side chain `simp only [URMState.step]; rw
  [dif_pos h_inbounds]; simp only [h_instr]` is restored, and
  the block is now structurally analogous to the surrounding
  `.assign`, `.inc`, `.dec`, `.stop` blocks in Step 7.9. The
  fix is correct as written. The R7 reviewer's diagnosis that
  R6-S3 was a misapplication has been honoured.
- Re-verified the R7-S1 fix (plan lines 1992 and 2028, Step 7.9
  `.inc` / `.dec` h_eq=true sub-cases): the `at *` qualifier is
  dropped from `rw [show i = j from Fin.ext h_eq]`. The rewrite
  now targets the goal only; the hypothesis `h_eq : i.val =
  j.val` remains in scope but is not rewritten to a degenerate
  `j.val = j.val`. The fix is correct as written and avoids the
  unusedHypothesis linter trap that R7-S1 identified.
- Re-verified the R7-S2 fix (plan lines 1818 – 1822, Step 7.8
  `.jumpZ` post-`by_cases h_zero` block): the prior two
  `simp only [KMor1.interp_natK']` invocations are removed.
  However, the fix is internally inconsistent and leaves a
  parallel hygiene defect — see Finding S1 below.
- Re-verified R6-B1 (plan lines 1767 – 1822, Step 7.8 `.jumpZ`):
  the `step_ctx_eval_simrec` + `Fin.ext`-to-`i.castSucc` bridge
  precedes `rw [ih_regs i]`; structurally parallel to Step 7.9
  `.jumpZ` post-R7-B1. The fix is correct as written.
- Re-verified R5-B1 (`rw [ih_pc]` in Step 7.8 `.assign` /
  `.inc` / `.dec`, plan lines 1738, 1752, 1766): the K-side
  post-bridge reduces to a `simrecVec`-then-`+ 1` form;
  `rw [ih_pc]` rewrites the `simrecVec` term to URM-side
  `pcVal`, leaving `pcVal + 1 = pcVal + 1` closed by implicit
  `rfl`. The fix is correct.
- Re-verified R5-B2 (`rw [show i = j from Fin.ext h_eq]` in
  Step 7.9 `.inc` / `.dec` h_eq=true): the substantive rewrite
  is preserved post-R7-S1.
- Re-verified the R4 helper extraction
  (`step_ctx_eval_simrec` in Step 7.1.5, plan lines 1489 –
  1507): body uses `show (if h₁ : slot < a + 1 then _ else
  KMor1.simrecVec … ⟨slot - (a + 1), by omega⟩) = _;
  rw [dif_neg (by omega)]`. The `show` exposes the dite; the
  `dif_neg` selects the else-branch under the hypothesis
  `a + 1 ≤ slot`. The body is correct.
- Re-fetched the mathlib upstream guides
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

None.

### Serious

1. **The R7-S2 fix is internally inconsistent: it dropped the
   post-`by_cases` `simp only [KMor1.interp_natK']` invocations
   in Step 7.8 `.jumpZ` (plan lines 1818 – 1822) but retained
   the equally-redundant `simp only [KMor1.interp_cond]`
   invocations on the same lines.** The R7-S2 rationale was
   that the first `simp only` chain at lines 1768 – 1770
   already includes `KMor1.interp_natK'`, so post-`by_cases`
   `simp only [KMor1.interp_natK']` would be a noop and emit
   a `Simp made no progress` warning. The same first chain
   also includes `KMor1.interp_cond` (line 1769), so by
   parallel reasoning `simp only [KMor1.interp_cond]` at lines
   1819 and 1821 is also a noop and will emit the same warning.

   Either (a) both `simp only [KMor1.interp_natK']` and
   `simp only [KMor1.interp_cond]` should be dropped from the
   post-`by_cases` sub-branches, leaving each sub-branch as
   `rw [if_pos h_zero]` (resp. `rw [if_neg h_zero]`), or
   (b) the R7-S2 fix should be reverted and both `simp only`
   invocations retained for symmetry.

   The deeper question is whether the `by_cases h_zero` split
   is needed at all. After the first chain at lines 1768 –
   1770 plus `rw [step_ctx_eval_simrec …]; rw [show … =
   i.castSucc …]; rw [ih_regs i]`, the K-side becomes
   `if (URMState.runFor … y).regs i = 0 then l₁ else l₂`
   (the literal constants because `KMor1.interp_natK'` is
   `@[simp]`-rewritten to `c`). The URM-side, post-`simp only
   [URMState.step]; rw [dif_pos h_inbounds]; simp only
   [h_instr]`, becomes the `.jumpZ` arm's record-literal `pc`
   field, namely `if s.regs i = 0 then l₁ else l₂` for `s :=
   URMState.runFor P (URMState.init P v) y`. The two sides
   are syntactically identical; an implicit `rfl` closes the
   goal without any `by_cases` split. The cleaner fix is to
   drop the `by_cases h_zero` block entirely:

   ```lean
   | jumpZ i l₁ l₂ =>
     simp only [branches_pc, h_instr, KMor1.interp_comp,
       KMor1.interp_cond, v_j_prev, KMor1.interp_proj,
       KMor1.interp_natK']
     simp only [URMState.step]
     rw [dif_pos h_inbounds]
     simp only [h_instr]
     rw [step_ctx_eval_simrec P v y (a + 1 + i.val) (by omega)
         (by omega)]
     rw [show (⟨a + 1 + i.val - (a + 1), by omega⟩
           : Fin (P.numRegs + 1)) = i.castSucc
           from by apply Fin.ext; simp [Fin.castSucc]; omega]
     rw [ih_regs i]
   ```

   At execution, `mcp__lean-lsp__lean_goal` should be invoked
   after the final `rw [ih_regs i]` to confirm syntactic
   equality; if Lean displays the two `if`-shapes differently
   (e.g. one uses `Decidable.decide` and the other unfolds
   the decidability instance), then a single `rfl` or a single
   `simp only [KMor1.interp_cond]` (with no `by_cases`) should
   close the goal.

   *Author response — TBD.*

2. **Step 7.8's `.jumpZ` block comment (plan line 1780) reads
   "mirroring Step 7.9's `.jumpZ` block" — re-flagged from R7-S3
   as still-deferred even though the structural-parity premise
   is now restored by R7-B1.** Post-R7, Step 7.9's `.jumpZ`
   block (plan lines 2040 – 2063) has its URM-side chain
   restored, so it is structurally parallel to Step 7.8's
   `.jumpZ` block again. The comment is now factually correct.
   However, the post-R7-S2 reduction of Step 7.8 `.jumpZ`'s
   `by_cases h_zero` block (lines 1818 – 1822) does diverge
   from Step 7.9 `.jumpZ`: Step 7.9 closes with `exact ih_regs
   j` after the bridge; Step 7.8 currently closes with the
   `by_cases h_zero` split plus `simp only [KMor1.interp_cond]`
   plus `rw [if_pos h_zero]` / `rw [if_neg h_zero]`. Either the
   comment should be tightened to reflect the partial-parity
   (the URM-side and K-side chains are parallel; the closing
   discharge differs because the PC-component branches on the
   register value while the register-`j` component reads its
   own previous value unconditionally), or — preferably — the
   Step 7.8 `.jumpZ` block should be simplified per Finding S1
   above to match Step 7.9's structure more closely.

   *Author response — TBD.*

3. **The Step 7.9 past-end branch (plan lines 2076 – 2101) uses
   `unfold URMState.step` while the in-bounds branch (line
   2051) uses `simp only [URMState.step]`; the same asymmetry
   appears in Step 7.8 (past-end uses `unfold URMState.step` at
   line 1857; in-bounds branches use `simp only [URMState.step]`
   at lines 1726, 1742, 1756, 1771, 1825).** Both `unfold` and
   `simp only` should produce the same dite-form on the
   URM-side; the asymmetry is cosmetic but introduces two
   distinct reduction paths for the same definition. The
   `unfold` form is slightly more fragile because mathlib's
   `unfold` tactic does not respect `@[reducible]` or
   `@[irreducible]` attributes in the same way `simp only`
   does. Recommend unifying on `simp only [URMState.step]` for
   both branches in both Step 7.8 and Step 7.9. Re-flagged as
   a hygiene concern; no correctness consequence in this
   specific case because `URMState.step` carries neither
   attribute in landed Lean.

   *Author response — TBD.*

### Minor

1. **The R5-B1 `rw [ih_pc]` closure in Step 7.8 `.assign` /
   `.inc` / `.dec` (plan lines 1738, 1752, 1766) relies on
   implicit `rfl` after the `simrecVec _ _ y (Fin.last
   P.numRegs)` subterm is rewritten to `pcVal`.** Re-flagged
   from rounds 5 (M1), 7 (M1). The defensive form is `rw
   [ih_pc]; rfl` or `exact congrArg (· + 1) ih_pc`.

   *Author response — TBD.*

2. **The Step 7.1.5 helper docstring (plan lines 1473 – 1488)
   addresses R6-S1's call-site contract claim but only obliquely
   addresses the helper-body's direct coupling to
   `KMor1.simrecVec_succ`'s dite-shape.** Re-flagged from R7-M2.
   Not blocking; a sharper re-phrasing would distinguish the
   helper-body coupling site (the `show` clause) from the
   call-site signature contract.

   *Author response — TBD.*

3. **Spec § 3.4's `branches_pc` pseudocode (lines 214 – 217 of
   the design doc) uses the wildcard `_` arm; the plan (Step
   5.2 at plan lines 1075 – 1092) enumerates `.assign`, `.inc`,
   `.dec` explicitly.** Re-flagged from rounds 5 (M3), 6 (M2),
   7 (M3). Spec-plan synchronisation gap remains; either the
   spec's pseudocode should be updated or the plan should cite
   a spec § noting the divergence.

   *Author response — TBD.*

4. **The Step 7.4 base case at plan lines 1551 – 1552 ends
   `show (0 : ℕ) = (URMState.init P v).pc; unfold URMState.init`
   without an explicit trailing `rfl`.** Re-flagged from
   rounds 5 (M2), 6 (M7), 7 (M4). Defensive form is an
   explicit trailing `rfl`.

   *Author response — TBD.*

5. **The Step 7.8 and Step 7.9 `set pcVal := … with hpc`
   declarations (plan lines 1685 and 1925) bind `hpc` but
   never reference it post-R4-B1.** Re-flagged from rounds 5
   (S7 reclassified Minor), 6 (M4), 7 (M5). Lean's
   `unusedVariable` linter will flag this at execution.
   Defensive form is `set pcVal := ((URMState.init P
   v).runFor P y).pc` (without `with hpc`).

   *Author response — TBD.*

6. **The `mcp__lean-lsp__lean_goal` defer-to-execution notes
   continue to accumulate** (R3-M1 / R4-M2 / R5-M3 / R6-M5 /
   R7-M6). Re-flagged. Plan lines 717 – 719, 1289 – 1293,
   1862 – 1866, 1797 – 1810. Each note documents a
   tactic-fork at execution time; the plan's
   "every step is independently executable" property weakens
   with each. Consider extracting these notes into a separate
   "Execution-time tactical reference" section.

   *Author response — TBD.*

7. **Plan Step 8.6 commit-message body still enumerates 19
   declaration names inline** (R3-M4 / R4-M4 / R6-M6 / R7-M7).
   Re-flagged.

   *Author response — TBD.*

8. **The Step 7.10 `lake build` expectation "zero `sorry`
   warnings, zero errors, zero warnings"** (R4-M6 / R5-M5 /
   R7-M8). Re-flagged. If the implementation emits expected
   unused-variable warnings (e.g., from `hpc` per M5 above) or
   `Simp made no progress` warnings (per Serious 1 above), the
   "zero warnings" target is unachievable without first
   applying the M-class and S-class fixes.

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's "Note:" paragraphs after each Lean code block
   describe lemma-name provenance rather than step-outcome.**
   Reaffirmed from R3-C1 / R4-C1 / R5-C1 / R6-C1 / R7-C1.

   *Author response — TBD.*

2. **Step 0.3's `jj log` filter is broad.** Reaffirmed from
   R3-C2 / R4-C2 / R5-C2 / R6-C2 / R7-C2.

   *Author response — TBD.*

3. **The 19 enumerated `bash scripts/check-axioms.sh`
   invocations across Tasks 1 – 8 and Step 9.3 inflate plan
   LOC.** Reaffirmed from R3-C3 / R4-C3 / R5-C3 / R6-C3 /
   R7-C3.

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat `per spec
   § X.Y` references in a fixed format.** Reaffirmed from
   R3-C4 / R4-C4 / R5-C4 / R6-C4 / R7-C4.

   *Author response — TBD.*

5. **The `step_ctx_eval_simrec` + `Fin.ext` bridge is invoked
   approximately ten times across Steps 7.8 / 7.9.**
   Reaffirmed from R5-C5 / R6-C5 / R7-C5. A second helper
   bridging directly from the dispatcher's dite-ctx slot to
   `simrecVec _ _ y k.castSucc` (with `k` a parameter and the
   slot computed as `a + 1 + k.val`) would collapse the bridge
   duplication to a single call per site.

   *Author response — TBD.*

## Convergence status

**NOT CONVERGED.** Round 8 found:

- 0 Blockers.
- 3 Serious (S1: R7-S2 internal inconsistency — `simp only
  [KMor1.interp_cond]` left in place when `simp only
  [KMor1.interp_natK']` was dropped, both equally redundant;
  S2: Step 7.8 `.jumpZ` comment partial-parity; S3:
  `unfold URMState.step` vs `simp only [URMState.step]`
  asymmetry between in-bounds and past-end branches in both
  Step 7.8 and Step 7.9).
- 8 Minor (re-flagged from prior rounds).
- 5 Cosmetic-taste (reaffirmed).

The R7-B1 fix (Step 7.9 `.jumpZ` URM-side chain restored) is
correct and aligned with the parallel constructors. The R7-S1
fix (`at *` dropped) is correct and avoids the linter trap.
The R7-S2 fix is partial: dropping `simp only [KMor1.interp_natK']`
without also dropping `simp only [KMor1.interp_cond]` leaves
the same `Simp made no progress` warning trap that R7-S2
intended to fix. The cleaner resolution is to drop the
`by_cases h_zero` block entirely (the post-`rw [ih_regs i]`
K-side and URM-side are syntactically identical and close by
`rfl`).

A round-9 dispatch is warranted after Serious 1 is addressed.
Serious 2 and 3 are hygiene concerns; minor and cosmetic-taste
findings are non-blocking per the project's convergence
criterion.
