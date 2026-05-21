# Round-9 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 9).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

Round 8 was a fresh-context review and produced zero blockers
and three serious findings (R8-S1: drop the `by_cases h_zero`
block from Step 7.8 `.jumpZ` because the post-`rw [ih_regs i]`
goal closes by implicit `rfl`; R8-S2: the Step 7.8 `.jumpZ`
block comment's "mirroring Step 7.9's `.jumpZ` block" claim
loses its partial-parity caveat once R8-S1 is applied; R8-S3:
the `unfold URMState.step` vs `simp only [URMState.step]`
asymmetry between past-end and in-bounds branches in both
Step 7.8 and Step 7.9 should be unified on `simp only`). The
author applied all three at commit `d8aa4a65`: R8-S1 by
dropping the `by_cases h_zero` block and replacing the closing
`simp only [KMor1.interp_cond]` plus `rw [if_pos h_zero]` /
`rw [if_neg h_zero]` sub-branches with a single
`rw [ih_regs i]`; R8-S2 auto-resolved by R8-S1 since the two
`.jumpZ` blocks are now structurally parallel; R8-S3 by
replacing both past-end `unfold URMState.step` occurrences
(plan lines 1857 and prior 2076-area) with `simp only
[URMState.step]`. This round re-examines the three applied
fixes from a fresh context and rechecks R7-B1, R6-B1, R5-B1,
R5-B2, and the R4 helper extraction underneath.

## Verification log

- Read [`docs/process.md`](../../docs/process.md) § Adversarial
  review: reviewer protocol, severity ladder, convergence
  criterion. Confirmed read-only constraint and round-isolation
  discipline.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  §§ 3 – 6 end-to-end; cross-checked the spec's `branches_pc`
  (lines 210 – 219), `branches_j` (lines 221 – 234), and
  `stepFamily` level bound (lines 236 – 238) against the
  plan's Task 5 – Task 7 fragments.
- Read the plan in full. Task and step numbering intact;
  Step 7.1.5 (R4 helper extraction) remains between Step 7.1
  and Step 7.2 with no downstream collisions.
- Read prior reviews
  [`review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md),
  [`review-2.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-2.md),
  [`review-3.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-3.md),
  [`review-4.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-4.md),
  [`review-5.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-5.md),
  [`review-6.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-6.md),
  [`review-7.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-7.md),
  and
  [`review-8.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-8.md);
  catalogued open items and re-verified the R4 / R5 / R6 / R7
  / R8 fixes independently rather than trusting round 8's
  verification.
- Read landed
  [`GebLean/Utilities/KArith.lean`](../../GebLean/Utilities/KArith.lean)
  at `KMor1.cond` / `KMor1.interp_cond` (lines 222 – 262):
  confirmed `KMor1.interp_cond` is `@[simp]` and rewrites to
  `if ctx 0 = 0 then ctx 1 else ctx 2`. The decidability
  instance is `Nat.decEq` (standard `Nat = Nat`).
- Read landed
  [`GebLean/Utilities/ZeroTestURM.lean`](../../GebLean/Utilities/ZeroTestURM.lean)
  at `URMState.step` (lines 155 – 172): confirmed the `.jumpZ`
  arm constructs `{ pc := if s.regs i = 0 then l₁ else l₂,
  regs := s.regs }` using the same `Nat.decEq` instance for
  the `=` test on `s.regs i`. Outer `if h : s.pc <
  P.instrs.size` is not eliminated definitionally; the
  `simp only [URMState.step]; rw [dif_pos h_inbounds]; simp
  only [h_instr]` chain remains operationally necessary on the
  URM-side.
- Re-verified R8-S1 (plan lines 1767 – 1799, Step 7.8 `.jumpZ`):
  the `by_cases h_zero` block is dropped; the block closes
  with `rw [step_ctx_eval_simrec …]; rw [show … = i.castSucc
  …]; rw [ih_regs i]` and an in-line comment block (lines
  1789 – 1799) explaining the implicit-`rfl` closure and the
  fallback `simp only [KMor1.interp_cond]` if the elaborator
  displays the two `if` forms differently. Independent
  goal-state derivation: after the K-side `simp only
  [branches_pc, h_instr, KMor1.interp_comp, KMor1.interp_cond,
  v_j_prev, KMor1.interp_proj, KMor1.interp_natK']` chain at
  lines 1768 – 1770, the K-side reduces to `if (ctx slot) = 0
  then l₁ else l₂` for `slot = a + 1 + i.val` and `ctx` the
  dispatcher's `dite`-form context (the two `natK' _ l₁` and
  `natK' _ l₂` branches reduce to literal constants `l₁` and
  `l₂` via the `@[simp]` `KMor1.interp_natK'`). After the
  bridge to `i.castSucc` and `rw [ih_regs i]`, the K-side
  becomes `if ((URMState.init P v).runFor P y).regs i = 0
  then l₁ else l₂`. The URM-side, after `simp only
  [URMState.step]; rw [dif_pos h_inbounds]; simp only
  [h_instr]`, exposes the `.jumpZ` arm's structure literal
  `{ pc := if s.regs i = 0 then l₁ else l₂, regs := s.regs
  }`; the outer `.pc` projection iota-reduces to the same
  `if s.regs i = 0 then l₁ else l₂` for `s := (URMState.init
  P v).runFor P y`. Both `if`s use `Nat.decEq` and produce
  syntactically identical terms. The implicit-`rfl` claim is
  sound under standard Lean 4 elaboration semantics.
- Re-verified R8-S3 (plan lines 1836 and 2074): both past-end
  branches in Step 7.8 and Step 7.9 now use `simp only
  [URMState.step]` followed by `rw [dif_neg …]`; no `unfold
  URMState.step` remains anywhere in the plan (verified by
  `grep -n "URMState.step" plan.md` returning only `simp only
  [URMState.step]` or commentary occurrences). The
  in-bounds and past-end branches are now hygiene-symmetric;
  R8-S3 is correctly applied.
- Re-verified R8-S2 (resolved by R8-S1): the Step 7.8 `.jumpZ`
  block (plan lines 1767 – 1799) and the Step 7.9 `.jumpZ`
  block (plan lines 2019 – 2042) are now structurally
  parallel: both perform `simp only [branches_*, h_instr, …];
  simp only [URMState.step]; rw [dif_pos h_inbounds]; simp
  only [h_instr]; rw [step_ctx_eval_simrec …]; rw [show … =
  *.castSucc …]; rw [ih_regs *]`. Step 7.8 closes there
  (implicit `rfl`); Step 7.9 closes with `exact ih_regs j`.
  The "mirroring Step 7.9's `.jumpZ` block" comment at plan
  line 1780 is now factually correct without caveat.
- Re-verified R7-B1 (plan lines 2019 – 2042, Step 7.9
  `.jumpZ`): the URM-side chain `simp only [URMState.step];
  rw [dif_pos h_inbounds]; simp only [h_instr]` is intact;
  structurally parallel to the surrounding `.assign`, `.inc`,
  `.dec`, `.stop` blocks in Step 7.9 and to the post-R8-S1
  Step 7.8 `.jumpZ` block. The fix continues to hold.
- Re-verified R7-S1 (plan lines 1971 and 2007, Step 7.9
  `.inc` / `.dec` h_eq=true sub-cases): the `at *` qualifier
  is absent from `rw [show i = j from Fin.ext h_eq]`; the
  rewrite targets the goal only; the hypothesis `h_eq : i.val
  = j.val` remains unrewrited. The fix continues to hold.
- Re-verified R6-B1 (plan lines 1767 – 1788, Step 7.8 `.jumpZ`):
  the `step_ctx_eval_simrec` + `Fin.ext`-to-`i.castSucc`
  bridge precedes `rw [ih_regs i]`; structurally parallel to
  Step 7.9 `.jumpZ` post-R7-B1. The fix continues to hold.
- Re-verified R5-B1 (`rw [ih_pc]` in Step 7.8 `.assign` /
  `.inc` / `.dec`, plan lines 1738, 1752, 1766): the K-side
  post-bridge reduces to a `simrecVec`-then-`+ 1` form;
  `rw [ih_pc]` rewrites the `simrecVec` term to URM-side
  `pcVal`, leaving `pcVal + 1 = pcVal + 1` closed by implicit
  `rfl`. The fix continues to hold.
- Re-verified R5-B2 (`rw [show i = j from Fin.ext h_eq]` in
  Step 7.9 `.inc` / `.dec` h_eq=true): the substantive
  rewrite is preserved post-R7-S1.
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
  plan's tactic choices. The R8-S1 fix retains the `rw
  [dif_pos h_inbounds]` form (per
  `feedback_simp_if_pos_sorryAx_leak.md`) and does not
  introduce any new `simp only [if_pos h]` or `simp only
  [dif_pos h]` patterns.

## Findings

### Blocker

None.

### Serious

None.

### Minor

1. **The R5-B1 `rw [ih_pc]` closure in Step 7.8 `.assign` /
   `.inc` / `.dec` (plan lines 1738, 1752, 1766) relies on
   implicit `rfl` after the `simrecVec _ _ y (Fin.last
   P.numRegs)` subterm is rewritten to `pcVal`.** Re-flagged
   from rounds 5 (M1), 7 (M1), 8 (M1). The defensive form is
   `rw [ih_pc]; rfl` or `exact congrArg (· + 1) ih_pc`. A
   parallel minor now applies to the post-R8-S1 Step 7.8
   `.jumpZ` closure (plan lines 1788 – 1799), which also
   relies on implicit `rfl` after `rw [ih_regs i]`. The
   in-line commentary at plan lines 1795 – 1799 explicitly
   documents the implicit-`rfl` closure and the fallback
   `simp only [KMor1.interp_cond]` if the elaborator displays
   the two `if` forms differently; this commentary mitigates
   but does not eliminate the implicit-`rfl` dependency. A
   defensive `rfl` at the end of the block would harden the
   fix.

   *Author response — TBD.*

2. **The Step 7.1.5 helper docstring (plan lines 1473 – 1488)
   addresses R6-S1's call-site contract claim but only obliquely
   addresses the helper-body's direct coupling to
   `KMor1.simrecVec_succ`'s dite-shape.** Re-flagged from
   rounds 7 (M2), 8 (M2). Not blocking; a sharper re-phrasing
   would distinguish the helper-body coupling site (the `show`
   clause) from the call-site signature contract.

   *Author response — TBD.*

3. **Spec § 3.4's `branches_pc` pseudocode (lines 214 – 217 of
   the design doc) uses the wildcard `_` arm; the plan (Step
   5.2 at plan lines 1075 – 1092) enumerates `.assign`,
   `.inc`, `.dec` explicitly.** Re-flagged from rounds 5 (M3),
   6 (M2), 7 (M3), 8 (M3). Spec-plan synchronisation gap
   remains; either the spec's pseudocode should be updated or
   the plan should cite a spec § noting the divergence.

   *Author response — TBD.*

4. **The Step 7.4 base case at plan lines 1551 – 1561 ends
   `show (0 : ℕ) = (URMState.init P v).pc; unfold
   URMState.init` without an explicit trailing `rfl`.**
   Re-flagged from rounds 5 (M2), 6 (M7), 7 (M4), 8 (M4).
   Defensive form is an explicit trailing `rfl`.

   *Author response — TBD.*

5. **The Step 7.8 and Step 7.9 `set pcVal := … with hpc`
   declarations (plan lines 1685 and 1904) bind `hpc` but
   never reference it post-R4-B1.** Re-flagged from rounds 5
   (S7 reclassified Minor), 6 (M4), 7 (M5), 8 (M5). Lean's
   `unusedVariable` linter will flag this at execution.
   Defensive form is `set pcVal := ((URMState.init P
   v).runFor P y).pc` (without `with hpc`).

   *Author response — TBD.*

6. **The `mcp__lean-lsp__lean_goal` defer-to-execution notes
   continue to accumulate** (R3-M1 / R4-M2 / R5-M3 / R6-M5 /
   R7-M6 / R8-M6). Re-flagged. Plan lines 717 – 719, 1289 –
   1293, 1846 – 1851, and the post-R8-S1 commentary at lines
   1789 – 1799. Each note documents a tactic-fork at
   execution time; the plan's "every step is independently
   executable" property weakens with each. Consider extracting
   these notes into a separate "Execution-time tactical
   reference" section.

   *Author response — TBD.*

7. **Plan Step 8.6 commit-message body still enumerates 19
   declaration names inline** (R3-M4 / R4-M4 / R6-M6 / R7-M7
   / R8-M7). Re-flagged.

   *Author response — TBD.*

8. **The Step 7.10 `lake build` expectation "zero `sorry`
   warnings, zero errors, zero warnings"** (R4-M6 / R5-M5 /
   R7-M8 / R8-M8). Re-flagged. If the implementation emits
   expected unused-variable warnings (e.g., from `hpc` per M5
   above), the "zero warnings" target is unachievable without
   first applying the M-class fixes. With R8-S1 applied, the
   prior `Simp made no progress` warning concern from R8-S1
   itself (the post-`by_cases` `simp only [KMor1.interp_cond]`
   noop) is resolved.

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's "Note:" paragraphs after each Lean code block
   describe lemma-name provenance rather than step-outcome.**
   Reaffirmed from R3-C1 / R4-C1 / R5-C1 / R6-C1 / R7-C1 /
   R8-C1.

   *Author response — TBD.*

2. **Step 0.3's `jj log` filter is broad.** Reaffirmed from
   R3-C2 / R4-C2 / R5-C2 / R6-C2 / R7-C2 / R8-C2.

   *Author response — TBD.*

3. **The 19 enumerated `bash scripts/check-axioms.sh`
   invocations across Tasks 1 – 8 and Step 9.3 inflate plan
   LOC.** Reaffirmed from R3-C3 / R4-C3 / R5-C3 / R6-C3 /
   R7-C3 / R8-C3.

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat `per spec
   § X.Y` references in a fixed format.** Reaffirmed from
   R3-C4 / R4-C4 / R5-C4 / R6-C4 / R7-C4 / R8-C4.

   *Author response — TBD.*

5. **The `step_ctx_eval_simrec` + `Fin.ext` bridge is invoked
   approximately ten times across Steps 7.8 / 7.9.**
   Reaffirmed from R5-C5 / R6-C5 / R7-C5 / R8-C5. A second
   helper bridging directly from the dispatcher's dite-ctx
   slot to `simrecVec _ _ y k.castSucc` (with `k` a parameter
   and the slot computed as `a + 1 + k.val`) would collapse
   the bridge duplication to a single call per site.

   *Author response — TBD.*

## Convergence status

**CONVERGED.** Round 9 found:

- 0 Blockers.
- 0 Serious.
- 8 Minor (re-flagged from prior rounds; non-blocking per the
  project's convergence criterion).
- 5 Cosmetic-taste (reaffirmed; non-blocking).

All three R8 fixes (R8-S1 dropping the `by_cases h_zero` block;
R8-S2 auto-resolved by R8-S1; R8-S3 unifying past-end and
in-bounds branches on `simp only [URMState.step]`) are
correctly applied and independently verified against landed
`KMor1.interp_cond` (`KArith.lean:249`), `URMState.step`
(`ZeroTestURM.lean:155 – 172`), and the surrounding plan
structure. The R8-S1 implicit-`rfl` claim is sound under
standard Lean 4 elaboration semantics: after the K-side
`simp only` chain and the bridge, both sides reduce to
`if ((URMState.init P v).runFor P y).regs i = 0 then l₁ else
l₂` using the same `Nat.decEq` decidability instance. The
plan's in-line commentary at lines 1789 – 1799 documents the
fallback `simp only [KMor1.interp_cond]` should the
elaborator display the two `if` forms differently — a
reasonable defensive note.

The R7 / R6 / R5 / R4 fixes underneath continue to hold under
independent re-verification.

Per the project's convergence criterion (zero blockers and
zero serious findings), this plan is ready to hand off to the
user for line-by-line review.
