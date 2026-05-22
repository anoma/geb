# Round-5 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 5).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

## Verification log

- Read [`docs/process.md`](../../process.md) § Adversarial review:
  reviewer protocol, severity definitions, convergence criterion.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  end-to-end. Cross-checked §§ 3.1 – 6 against the plan's
  Task 1 – Task 9 layout. The round-4 R4-S3 plan-side change to
  `branches_pc` (explicit per-constructor enumeration) is not
  mirrored in the spec; the spec §§ 3.4 prose still references the
  wildcard form. Flagged below as M1.
- Read the plan in full. Task and step numbering: Step 7.1.5 is
  newly inserted between 7.1 and 7.2; Steps 7.2 – 7.12 retain
  their numbers. No downstream numbering collisions observed.
- Read prior reviews
  [`review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md),
  [`review-2.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-2.md),
  [`review-3.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-3.md),
  [`review-4.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-4.md);
  catalogued open items.
- Audited R4-B1 — `rw [← hpc] at h_ctx_last_pc` removed from
  Steps 7.8 and 7.9. The lines remain only inside narrative
  `--`-comments (plan lines 1674, 1843, 1882). Tactic body is
  clean. Confirmed via
  `grep -n 'rw \[← hpc\]' .../plan.md`: three hits, all in
  comment text.
- Audited R4-B2 — `step_ctx_eval_simrec` helper added in
  Step 7.1.5 at plan lines 1472 – 1498. Helper is invoked at
  Step 7.8 PC component (`h_ctx_last_pc`, `.assign`, `.inc`,
  `.dec`, `.stop` discharges) and Step 7.9 register component
  (`h_ctx_last_pc`, `.assign`/`.inc`/`.dec` h_eq false branches,
  `.jumpZ`, `.stop`, past-end). The Fin.ext bridge to
  `Fin.last P.numRegs` (PC) and `j.castSucc` (register) is
  inserted after each helper application. Substantive
  correctness reviewed below — see B1.
- Audited R4-S1 — fallback note added at plan lines 1696 – 1707
  documenting `subst h_instr` and explicit `generalize` paths if
  `simp only [branches_pc, h_instr]` fails on the bound-proof-
  object difference. Documentation-level fix; correct.
- Audited R4-S2 — Step 7.8 `.jumpZ` block at plan lines
  1768 – 1778 replaces bare `simp` / `simp [h_zero]` with two
  `simp only` invocations whose whitelists enumerate
  `KMor1.interp_cond`, `Fin.cons_zero`, `Fin.cons_succ`,
  `if_pos rfl` / `if_neg h_zero`, `decide_True` / `decide_False`,
  `KMor1.interp_natK'`. Substantive correctness reviewed below —
  see S1.
- Audited R4-S3 — `branches_pc` in Step 5.2 now enumerates
  `.assign`, `.inc`, `.dec` explicitly (plan lines 1078 – 1083).
  Wildcard `_` removed. Spec mirror not updated (M1 below).
- Audited R4-S4 — Step 7.4 PC base case at plan lines 1546 – 1551
  adds `show (0 : ℕ) = (URMState.init P v).pc; unfold URMState.init`
  before the trailing `rfl`. The `rfl` is now implicit; the
  `unfold` rewrites the LHS shape. Correct.
- Audited R4-S5 — Steps 7.8 / 7.9 per-instruction blocks replace
  `simp only [URMState.step, dif_pos h_inbounds, h_instr]` with
  the three-step sequence `simp only [URMState.step]` /
  `rw [dif_pos h_inbounds]` / `simp only [h_instr]`. Confirmed at
  all 10 sites in Step 7.8 and 10 sites in Step 7.9. Correct
  per `feedback_simp_if_pos_sorryAx_leak.md`.
- Audited R4-S6 — Step 7.9's `.jumpZ` and `.stop` discharges
  (and `.assign`/`.inc`/`.dec` h_eq=false branches) now include
  the `step_ctx_eval_simrec` + Fin.ext bridge to `j.castSucc`.
- Audited R4-S7 — Step 4.3's `cases h` arms now close with
  `unfold KMor1.level; omega` rather than bare `rfl`. Correct.
- Re-checked deferred round-3 minors (R3-M1, R3-M3, R3-M4,
  R3-M5, R3-M7) and cosmetic items (C1 – C4):
  - R3-M1 (defer-to-execution `lean_goal` notes): still present
    at plan lines 717 – 719, 1289 – 1293; round 4 re-flagged as
    R4-M2 and that author response was deferred. Re-flagged as
    M-class below.
  - R3-M3 (duplicate `h_ctx_last_pc` derivation): the
    `step_ctx_eval_simrec` extraction reduces the duplication
    substantially. The two refine branches still re-derive
    `h_ctx_last_pc` inline (calling the helper rather than
    re-deriving `dif_neg`). The remaining duplication is the
    `show`/`rw` chain wrapping the helper call; this is ~7 LOC
    per branch rather than the prior ~10. Acceptable; closed.
  - R3-M4 / R3-M7 / C1 – C4: unchanged; not re-elevated.
- Re-fetched mathlib upstream guides via
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md);
  scanned commit-message subjects, declaration names, and
  docstring sections against each.
- Cross-referenced project memories
  [`feedback_simp_if_pos_sorryAx_leak.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_simp_if_pos_sorryAx_leak.md),
  [`feedback_mathlib_choice_in_functor_cat.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_mathlib_choice_in_functor_cat.md),
  and
  [`feedback_urmstate_init_let_reduction.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_urmstate_init_let_reduction.md)
  against the plan's tactic choices.

## Findings

### Blocker

1. **Steps 7.8 / 7.9 per-instruction PC-increment discharges
   close with `exact ih_pc` against a goal whose two sides each
   carry a `+ 1`; `ih_pc` lacks the trailing `+ 1` and cannot
   close.** Affects `.assign`, `.inc`, `.dec` in Step 7.8 (plan
   lines 1716 – 1761, three blocks). For `.assign i c`, the
   K^sim-side reduces via
   `simp only [..., KMor1.interp_succ, I_prev, KMor1.interp_proj]`
   to `ctx ⟨a + 1 + P.numRegs, _⟩ + 1` where `ctx` is the
   dispatcher's `dite`-form context. The URM-side reduces via
   `simp only [URMState.step]; rw [dif_pos h_inbounds]; simp only
   [h_instr]` to `(URMState.runFor P (URMState.init P v) y).pc +
   1`, which (after `set pcVal := … with hpc` substitutes
   uniformly) is `pcVal + 1`. After
   `rw [step_ctx_eval_simrec P v y (a + 1 + P.numRegs) _ _]` and
   the Fin.ext bridge to `Fin.last P.numRegs`, the K-side becomes
   `KMor1.simrecVec _ _ y (Fin.last P.numRegs) + 1`. The
   hypothesis `ih_pc : KMor1.simrecVec _ _ y (Fin.last P.numRegs)
   = ((URMState.init P v).runFor P y).pc` post-`set` becomes
   `ih_pc : … = pcVal` — its LHS matches the K-side's
   under-the-`+ 1` term, but its RHS lacks the trailing `+ 1`.
   `exact ih_pc` therefore cannot close the goal
   `KMor1.simrecVec _ _ y (Fin.last P.numRegs) + 1 = pcVal + 1`.
   The fix is `rw [ih_pc]` (which rewrites the K-side's
   `simrecVec` occurrence, leaving `pcVal + 1 = pcVal + 1` then
   closed by `rfl`), or equivalently
   `exact congrArg (· + 1) ih_pc`. The `.stop` case is unaffected
   (URM-side has no `+ 1`); the `.jumpZ` case has a different
   discharge path (uses `ih_regs i`, not `ih_pc` directly). The
   defect affects 3 sites in Step 7.8 (`.assign`, `.inc`,
   `.dec`).

   *Author response — TBD.*

2. **Step 7.9's `.assign`/`.inc`/`.dec` h_eq = true sub-cases
   close after `rw [ih_regs j]` (or `rw [Function.update_apply,
   if_pos (Fin.ext h_eq).symm]; …; rw [ih_regs j]`) against a
   goal whose URM-side is `(runFor y).regs i + …` and whose
   K-side after the rewrite is `(runFor y).regs j + …`; `i` and
   `j` are propositionally but not syntactically equal, so the
   `rfl` (or implicit final step) cannot close.** For `.inc i`
   with `h_eq : i.val = j.val` true (plan lines 1908 – 1922 in
   Step 7.9): after
   `rw [if_pos h_eq]; simp only [KMor1.interp_comp,
   KMor1.interp_succ, v_j_prev, KMor1.interp_proj]; rw
   [Function.update_apply, if_pos (Fin.ext h_eq).symm]`,
   URM-side is `((URMState.init P v).runFor P y).regs i + 1` (the
   `Function.update_apply, if_pos …` discharge yields
   `s.regs i + 1`, not `s.regs j + 1`, because the updated value
   passed to `Function.update` is `s.regs i + 1`). After
   `rw [step_ctx_eval_simrec …]; rw [show … = j.castSucc …]; rw
   [ih_regs j]`, K-side is `((URMState.init P v).runFor P y).regs
   j + 1`. The goal `(runFor y).regs j + 1 = (runFor y).regs i +
   1` is true iff `i = j`, which holds via `Fin.ext h_eq`, but
   the `rw` chain produces no concluding step to bridge the
   `i`-vs-`j` mismatch. Implicit `rfl` cannot close. Same defect
   for `.dec i` h_eq = true (plan lines 1934 – 1947) and
   `.assign i c` h_eq = true (plan lines 1880 – 1885: the K-side
   becomes `c` via `KMor1.interp_natK'`, URM-side becomes `c`
   via `Function.update_apply, if_pos`; this one may close
   because both reduce to a constant `c` with no register
   reference — verify). The fix for `.inc` / `.dec` is to add
   `rw [Fin.ext h_eq]` (rewriting `i` to `j` or vice-versa) or
   `congr 1; exact Fin.ext h_eq` before the implicit `rfl`. Three
   sites in Step 7.9; the `.assign` h_eq = true case needs
   verification but plausibly works.

   *Author response — TBD.*

### Serious

1. **Step 7.8's `.jumpZ` block whitelist closures include
   `Fin.cons_zero, Fin.cons_succ` even though the post-`simp` goal
   does not necessarily contain a `Fin.cons` expression at the
   point of the closure.** Plan lines 1770 – 1772, 1773 – 1775.
   After `simp only [branches_pc, h_instr, KMor1.interp_comp,
   KMor1.interp_cond, v_j_prev, KMor1.interp_proj,
   KMor1.interp_natK']`, the K-side becomes
   `KMor1.cond.interp (fun ix => match ix with | ⟨0,_⟩ => ctx … |
   ⟨1,_⟩ => l₁ | ⟨2,_⟩ => l₂)`, which by `KMor1.interp_cond`
   unfolds to an `if`-`then`-`else` over a `Fin 3`-indexed
   match. The match arms are accessed by literal `Fin 3` indices
   (`⟨0,_⟩`, `⟨1,_⟩`, `⟨2,_⟩`), not by `Fin.cons` projections.
   The `Fin.cons_zero` / `Fin.cons_succ` lemmas therefore do not
   fire. The actual lemmas needed are pattern-match reductions
   (e.g., `match ⟨0,_⟩ with | ⟨0,_⟩ => … | …` reduces to the
   first arm by `rfl`). The plan's whitelist will likely fail to
   close. A safer whitelist is `KMor1.interp_cond,
   KMor1.interp_natK', if_pos rfl` / `if_neg h_zero`,
   `decide_True` / `decide_False`, plus whatever lemma name
   reduces the inner `Fin 3` match (likely none needed if
   pattern-matching reduces definitionally). Re-examine at
   execution against `KMor1.interp_cond`'s definition in
   `LawvereKSimInterp.lean`; if `cond` is defined as
   `if (cond-arg).interp ctx = 0 then …` then the discharge can
   close via `if_pos`/`if_neg`. If `KMor1.interp_cond` produces
   a `Fin.cases` or `Decidable.rec` form, additional reductions
   are needed.

   *Author response — TBD.*

2. **Step 7.9's `.assign i c` h_eq = true branch closes
   implicitly after
   `rw [Function.update_apply, if_pos (Fin.ext h_eq).symm]`
   with no explicit final tactic; the goal at that point may
   not be closed by `rfl` if both sides have not normalised to
   the same `c` form.** Plan lines 1880 – 1885. The K-side
   reduces via `simp only [KMor1.interp_natK']` to `c`. The
   URM-side after `Function.update_apply, if_pos` reduces to
   `c`. Both are `c`. Likely closes by implicit `rfl` after
   the final `rw`. The block is missing the explicit
   `step_ctx_eval_simrec` bridge that other Step 7.9 blocks
   have because no `simrecVec` term appears post-reduction
   (the K-side is a literal `c`). This is correct in principle
   but the block ends abruptly without commenting on why no
   bridge is needed — the implementer reading the block in
   isolation will not immediately see this. Add a single-line
   comment ("K-side and URM-side both reduce to `c`; no
   `simrecVec` bridge needed for this sub-case.").

   *Author response — TBD.*

3. **Step 7.9's `.jumpZ i l₁ l₂` discharge at plan lines
   1973 – 1985 reads `simp only [branches_j, h_instr, v_j_prev,
   KMor1.interp_proj]; simp only [URMState.step]; rw [dif_pos
   h_inbounds]; simp only [h_instr]; rw [step_ctx_eval_simrec …];
   rw [show … = j.castSucc …]; exact ih_regs j`.** The
   `branches_j` for `.jumpZ` returns `v_j_prev P j` directly (no
   `cond`-wrap), so the K-side after the simp chain is
   `ctx ⟨a + 1 + j.val, _⟩` (the `v_j_prev` projection). The
   URM-side for `.jumpZ` does not modify `regs`, so it stays
   `((URMState.init P v).runFor P y).regs j`. After
   `step_ctx_eval_simrec` and the Fin.ext bridge, K-side is
   `KMor1.simrecVec _ _ y j.castSucc`. `ih_regs j` has type
   `KMor1.simrecVec _ _ y j.castSucc = (runFor y).regs j` —
   matches exactly. `exact ih_regs j` closes. Correct.
   However, the `simp only [URMState.step]; rw [dif_pos
   h_inbounds]; simp only [h_instr]` chain is operationally
   redundant on the URM-side since the URM `step` for jumpZ
   does not change `regs`; the URM-side is already
   `(runFor y).regs j` before any of these tactics fire (because
   the `step` result is `{s with pc := …, regs := s.regs}` and
   `.regs j` reads `s.regs j` unchanged). The chain may emit
   tactic-noop warnings or have no effect; the `simp only`
   invocations may also fail silently. Verify at execution. Not
   a correctness issue but a hygiene one.

   *Author response — TBD.*

4. **Step 7.9's past-end branch at plan lines 2005 – 2012
   includes `rw [step_ctx_eval_simrec P v y (a + 1 + j.val) _ _]`
   after `rw [dif_neg (Nat.not_lt_of_ge h_inbounds)]`. The
   `dif_neg` rewrites the URM-side's `URMState.step` to return
   `s` unchanged; the K-side at that point is `(v_j_prev P j).
   interp (pcDispatch's default ctx)` = `ctx ⟨a + 1 + j.val,
   _⟩` — and the dispatcher-context `ctx` here is the same
   `dite`-form context as in the in-bounds branch, so
   `step_ctx_eval_simrec` is applicable. Confirmed correct.**
   Minor: the past-end branch did not previously need this
   bridge in round 3 because the K-side `v_j_prev P j` was
   thought to reduce directly; the round-4 addition is a
   consequence of removing the implicit reduction reliance.
   This is the right call; not a defect.

   *No action required.*

5. **The Step 7.1.5 helper `step_ctx_eval_simrec`'s proof body
   uses `show (if h₁ : slot < a + 1 then _ else KMor1.simrecVec
   … ⟨slot - (a + 1), _⟩) = _; rw [dif_neg (by omega)]` — but
   `show` only succeeds if the LHS reduces definitionally to
   the goal's LHS.** The goal's LHS is `(fun idx => …) ⟨slot, …⟩`,
   which by beta-reduction equals `if h₁ : slot < a + 1 then …`.
   Beta-reduction does fire definitionally in Lean 4, so the
   `show` should succeed. However, the inner `omega` proofs
   inside the `dite` arms (`by omega` for the `idx.val - 1` and
   `idx.val - (a + 1)` Fin-bound proofs) carry the hypotheses
   from the dite-arm context (`h₁ : idx.val < a + 1` and `h₂ :
   idx.val = 0` for the inner if, and the negation for the outer
   else). After beta and `show`, the proof obligation in the
   else-arm is reconstructed with `slot` instead of `idx.val`;
   the corresponding `by omega` proof must close
   `slot - (a + 1) < P.numRegs + 1` given `h_slot_bound : slot <
   a + 1 + (P.numRegs + 1)` and `h_slot_ge : a + 1 ≤ slot`. The
   helper's hypothesis list provides these, so the inner `omega`
   should succeed under the elaborator. Correct, but worth a
   spot-check at implementation time.

   *Author response — TBD.*

6. **The Step 7.8 / 7.9 `h_ctx_last_pc` derivations now invoke
   the helper at `slot := a + P.numRegs + 1`, but the helper's
   `slot - (a + 1)` evaluates to `P.numRegs` (not `P.numRegs +
   1 - 1` or similar), and the subsequent Fin.ext bridge maps
   `⟨P.numRegs, _⟩` to `Fin.last P.numRegs`.** `Fin.last
   P.numRegs : Fin (P.numRegs + 1)` has `.val = P.numRegs` by
   definition. The bridge `apply Fin.ext; simp [Fin.last];
   omega` closes by Fin extensionality plus `Fin.last`'s
   `simp`-normal form. Correct. Minor note: the bridge form is
   identical at all four call sites (PC `h_ctx_last_pc` PC and
   register branches), so could in principle be extracted into
   a second helper or `local notation`. Not flagged as defect;
   the duplication is each ~3 LOC.

   *No action required.*

7. **The Step 7.8 and Step 7.9 `set pcVal := … with hpc`
   declarations bind `pcVal` and `hpc`, but after R4-B1's
   removal of `rw [← hpc] at h_ctx_last_pc`, `hpc` is never
   used in either tactic block.** Plan lines 1700 (Step 7.8)
   and 1877 (Step 7.9). The `set … with hpc` form binds `hpc :
   pcVal = ((URMState.init P v).runFor P y).pc` (the equation
   between the new name and the original expression). With
   `hpc` now unused, the binding can be simplified to `set
   pcVal := ((URMState.init P v).runFor P y).pc` (without
   `with hpc`); Lean will warn on unused-binding via
   `unusedVariable` linter. Cosmetic-taste / minor; not a
   correctness defect.

   *Author response — TBD.*

### Minor

1. **Spec § 3.4 still references the wildcard `_` arm in
   `branches_pc` even though plan Step 5.2 was updated to
   enumerate `.assign`, `.inc`, `.dec` explicitly (R4-S3).**
   Per
   [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md` §3.4](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md#34-step-family),
   the prose informally describes the PC-component branches
   with "otherwise (`.assign`, `.inc`, `.dec`) → I_prev + 1"
   without committing to wildcard-vs-enumeration syntax. The
   spec's pseudocode (if any) and the plan's Lean code must
   agree on the enumeration form. If the spec's pseudocode
   uses `_`, update it to the explicit form to maintain
   spec-plan parity. This is a spec-plan synchronisation issue
   surfaced by R4-S3.

   *Author response — TBD.*

2. **The Step 7.4 `unfold URMState.init` closing in the
   R4-S4 fix leaves the goal as `(0 : ℕ) = 0` after the
   `unfold` exposes `URMState.init`'s `pc := 0` field.** The
   `unfold` is not followed by an explicit `rfl`; whether the
   goal closes depends on whether `unfold` itself
   triggers the closing `rfl` (`unfold` typically does not
   close goals; it only rewrites). Add an explicit trailing
   `rfl` after `unfold URMState.init` to defensively close.
   Plan lines 1548 – 1553.

   *Author response — TBD.*

3. **The defer-to-execution `mcp__lean-lsp__lean_goal` notes
   (R3-M1 / R4-M2) remain at plan lines 717 – 719, 1289 – 1293,
   1828 – 1830, 1840 – 1842.** Round 3 marked R3-M1 as Minor;
   round 4 marked R4-M2 as Minor; both deferred. Re-flagged in
   round 5 as Minor.

   *Author response — TBD.*

4. **The `step_ctx_eval_simrec` helper is `private` but its
   docstring is `/-- … -/` rather than `/-! … -/`.** Per
   mathlib `doc.html`, private declarations may carry either
   form; `/-- … -/` attaches to the declaration directly
   (queryable via `#check` and the doc-gen tool) while
   `/-! … -/` is a free-floating "module-section" docstring.
   The declaration-attached form is preferred for `private`
   helpers that may be cited from other declarations'
   docstrings. The current `/-- … -/` form at plan line 1473
   is correct.

   *No action required.*

5. **The Step 7.10 `lake build` expectation "zero `sorry`
   warnings, zero errors, zero warnings" remains identical to
   round 4 (R4-M6 deferred).** Not re-elevated.

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's "Note:" paragraphs after each Lean code block
   describe lemma-name provenance rather than step-outcome
   (R3-C1 / R4-C1 reaffirmed).** Reaffirming as
   cosmetic-taste in round 5.

   *Author response — TBD.*

2. **Step 0.3's `jj log` filter is still broad** (R3-C2 /
   R4-C2). Reaffirming as cosmetic-taste in round 5.

   *Author response — TBD.*

3. **The 19 enumerated `bash scripts/check-axioms.sh`
   invocations across Tasks 1 – 8 and Step 9.3 inflate plan
   LOC** (R3-C3 / R4-C3). Reaffirming as cosmetic-taste in
   round 5.

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat
   `per spec § X.Y` references in a fixed format** (R3-C4 /
   R4-C4). Reaffirming as cosmetic-taste in round 5.

   *Author response — TBD.*

5. **The new `step_ctx_eval_simrec` helper plus the Fin.ext
   bridge are invoked verbatim ~10 times across Steps 7.8 /
   7.9.** Each invocation is ~7 LOC (`rw [step_ctx_eval_simrec
   …]; rw [show … = … from by apply Fin.ext; simp …; omega]`).
   A `local notation` or a second helper bridging directly
   from the `dite`-ctx to `ih_pc` / `ih_regs j` would reduce
   ~60 LOC. The current form is acceptable (the per-call site
   benefits from local visibility of the bridge), but the
   sub-helper extraction is worth a TODO note for execution
   time.

   *Author response — TBD.*

## Convergence status

**NOT CONVERGED.** Round 5 found:

- 2 Blockers (B1: `+ 1` mismatch on PC-increment closures;
  B2: `i`-vs-`j` mismatch on register-update closures).
- 3 Serious findings (S1: `.jumpZ` whitelist questionable;
  S2: `.assign` h_eq=true block ends abruptly; S3:
  `.jumpZ` register-side simp chain is redundant-noop).
- 4 Minor findings (M1 spec-plan sync; M2 unfold without rfl;
  M3 lean_goal notes; M5 lake build expectation).
- 5 Cosmetic-taste findings (C1 – C5).

The two blockers are arithmetic-form mismatches arising from
the `step_ctx_eval_simrec` extraction's interaction with the
`set pcVal` substitution. Neither was present in round 4's
diagnosis (round 4 caught the structural Fin-index mismatch
but did not trace the trailing-`+ 1` and `i`-vs-`j`
arithmetic differences). Both fixes are mechanical:

- B1 (`+ 1` mismatch): replace `exact ih_pc` with
  `rw [ih_pc]` (3 sites in Step 7.8 — `.assign`, `.inc`,
  `.dec`).
- B2 (`i`-vs-`j` mismatch): insert `rw [Fin.ext h_eq]` (or
  `congr 1; exact Fin.ext h_eq`) before the implicit `rfl` in
  3 sites in Step 7.9 (`.inc`/`.dec` h_eq=true; verify
  `.assign` h_eq=true reduces both sides to constant `c`).

Serious finding S1 may turn out to be benign if
`KMor1.interp_cond` reduces straightforwardly to `if`-`then`
-`else`; if so, downgrade to Minor at round 6. Otherwise,
the `.jumpZ` whitelist needs the inner-match-reduction
lemma names enumerated.

The remaining Minor and Cosmetic-taste findings are
non-blocking and (per the prior reviews' convention)
deferrable; reach convergence after R5-B1 and R5-B2 are
fixed and a re-review confirms the per-instruction closure
chains type-check end-to-end.
