# Round-4 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 4).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

## Verification log

- Read [`docs/process.md`](../../process.md) § Adversarial review
  (lines 131 – 227): reviewer protocol, severity definitions,
  convergence criterion. Confirmed read-only constraint.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  end-to-end (892 lines); cross-checked spec §§ 3.1 – 6 against
  the plan's Task 1 – Task 9 layout.
- Read the plan in full (2113 lines). Task and step numbering
  intact across all ten tasks.
- Read prior reviews
  [`review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md),
  [`review-2.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-2.md),
  and
  [`review-3.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-3.md);
  recorded which findings were marked fix vs deferred.
- Spot-checked the round-3 fix applications:
  - R3-B1: the `interp_pcDispatchFrom_match` proof at plan lines
    662 – 692 now uses `rw [if_neg hsub]` on the open goal (no
    metavariable-laden `have`-block). Confirmed.
  - R3-S1: Steps 7.8 and 7.9 add
    `rw [← hpc] at h_ctx_last_pc` after
    `set pcVal := … with hpc`. The substantive correctness of
    this rewrite is the subject of Blocker 1 below.
  - R3-S2: Steps 7.8 / 7.9 per-instruction blocks now use
    `simp only [branches_pc, h_instr, …]` (PC) and
    `simp only [branches_j, h_instr, …]` (register) followed
    by `simp only [URMState.step, dif_pos h_inbounds, h_instr]`.
    The pattern matches R3-S2's proposed discharge.
  - R3-S3: Step 4.3 uses named `cases h : …` (lines 971 – 974);
    no anonymous `cases` remains. Confirmed.
  - R3-S4: Steps 4.3 and 5.6 now use
    `refine Fin.lastCases ?_ ?_ j` (plan lines 964, 1160) per
    the project precedent at
    [`GebLean/LawvereBTInterp.lean:625, 627, 637, 668, 669`](../../GebLean/LawvereBTInterp.lean#L625).
    Confirmed.
  - R3-S5: a file-layout reference table is inserted at plan
    lines 425 – 440 spelling out Task → namespace placement for
    Tasks 2 – 8. Cross-checked against the per-task
    "append inside `namespace …`" instructions in Step 3.1,
    Step 4.1, Step 5.1, Step 6.1, Step 7.1, Step 8.1; the table
    matches each per-task header verbatim.
  - R3-S6: Step 1.6's `natK'_level` proof at plan line 279 uses
    `show (Finset.univ : Finset (Fin 0)) = ∅ from
    Finset.univ_eq_empty` (no underscore argument). Confirmed.
  - R3-S7: Step 7.8 per-instruction blocks chain
    `rw [h_ctx_last_pc]` after the `simp only` step (plan lines
    1634, 1639, 1644, 1660). The substantive correctness of
    this rewrite is the subject of Blocker 2 below.
- Verified line numbers cited in the plan against landed code:
  - `URMState.step` at
    [`GebLean/Utilities/ZeroTestURM.lean:155`](../../GebLean/Utilities/ZeroTestURM.lean#L155);
    `URMState.runFor_succ` `@[simp]` at `:192`;
    `URMState.runFor_add` at `:199`; `URMState.runFor_zero` at
    `:186`; `URMState.init` at `:254`.
  - `KMor1.simrecVec_succ` `@[simp]` at
    [`LawvereKSimInterp.lean:193 – 209`](../../GebLean/LawvereKSimInterp.lean#L193);
    confirmed the dite-form context whose last-slot value for
    `idx.val ≥ a + 1` is
    `KMor1.simrecVec h g params n ⟨idx.val - (a + 1), _⟩`.
  - `KMor1.interp_proj` at
    [`LawvereKSimInterp.lean:98`](../../GebLean/LawvereKSimInterp.lean#L98)
    rewrites `(KMor1.proj i).interp ctx = ctx i` (the `i` is the
    `Fin` index as supplied to `proj`; no normalisation of the
    index occurs).
- Verified mathlib `set` tactic semantics by reading
  [`Mathlib/Tactic/Set.lean`](../../.lake/packages/mathlib/Mathlib/Tactic/Set.lean)
  (mathlib pin at `lake-manifest.json`): the `set` body runs
  `try rewrite [show vale = a from rfl] at *`, replacing the
  expression in **both** the goal and all hypotheses (the `at *`
  qualifier). This is load-bearing for Blocker 1.
- Cross-checked `Fin.lastCases_castSucc` / `Fin.lastCases_last`
  lemma names against mathlib (verified used at
  [`AlgebraicTopology/SimplexCategory/GeneratorsRelations/EpiMono.lean:35 – 37`](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/GeneratorsRelations/EpiMono.lean#L35)).
  Both names exist.
- Re-fetched mathlib upstream guides
  ([`naming.html`](https://leanprover-community.github.io/contribute/naming.html),
  [`style.html`](https://leanprover-community.github.io/contribute/style.html),
  [`doc.html`](https://leanprover-community.github.io/contribute/doc.html),
  [`commit.html`](https://leanprover-community.github.io/contribute/commit.html))
  via the digest in
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md);
  scanned commit-message subjects, declaration names, and
  docstring sections against each.
- Cross-referenced project memories
  [`feedback_fin_cases_pulls_classical_choice.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_fin_cases_pulls_classical_choice.md),
  [`feedback_simp_if_pos_sorryAx_leak.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_simp_if_pos_sorryAx_leak.md),
  [`feedback_urmstate_init_let_reduction.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_urmstate_init_let_reduction.md),
  and
  [`feedback_mathlib_choice_in_functor_cat.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_mathlib_choice_in_functor_cat.md)
  against the plan's tactic choices.
- Re-read the unapplied round-3 items (R3-M1, R3-M3, R3-M4,
  R3-M5, R3-M7, all cosmetic-taste) against the current plan;
  assessed whether each remains a defect in round 4.

## Findings

### Blocker

1. **Steps 7.8 and 7.9's `rw [← hpc] at h_ctx_last_pc` (the
   R3-S1 fix) cannot fire, because `set` has already rewritten
   the RHS.** At plan lines 1610 – 1611 (Step 7.8 PC branch)
   and 1738 – 1739 (Step 7.9 register branch), the proof reads
   `set pcVal := ((URMState.init P v).runFor P y).pc with hpc`
   followed by `rw [← hpc] at h_ctx_last_pc`. Per mathlib's
   `Set.lean` (lines 30 – 31), the `set` body runs
   `try rewrite [show vale = a from rfl] at *`, replacing the
   expression in all hypotheses, including
   `h_ctx_last_pc`. After `set`, the hypothesis is already
   `h_ctx_last_pc : (fun idx => …) (Fin.last (a + P.numRegs + 1)) =
   pcVal`, and `h_inbounds` is already
   `h_inbounds : pcVal < P.instrs.size`. The subsequent
   `rw [← hpc] at h_ctx_last_pc` looks for an occurrence of
   `((URMState.init P v).runFor P y).pc` in `h_ctx_last_pc`,
   finds none (the `set` consumed it), and fails with
   "did not find instance of the pattern" — halting the
   proof at the in-bounds branch entry, repeated for both
   refine sub-goals (PC and register). The
   round-3 reviewer's premise that "`set` only substitutes in
   the goal, not in already-bound hypotheses" is incorrect;
   the round-3 fix is built on that incorrect premise. The
   corrective is to delete the
   `rw [← hpc] at h_ctx_last_pc` line entirely (the `set`
   already does what was wanted) — or, alternatively, to
   replace `set` with the non-substituting `set!` (so the
   subsequent `rw [← hpc]` then has work to do). Either path
   requires re-stating the plan instruction.

   *Author response — TBD.*

2. **Step 7.8's `rw [h_ctx_last_pc]` after the per-instruction
   `simp only` chain cannot fire because the goal's reduced
   Fin-index form does not match `h_ctx_last_pc`'s
   `Fin.last (a + P.numRegs + 1)` form.** At plan lines 1634,
   1639, 1644, 1660 (Step 7.8 per-instruction discharges,
   including `.stop`), the proof closes each block with
   `rw [h_ctx_last_pc]` (or `exact h_ctx_last_pc` for `.stop`).
   The hypothesis `h_ctx_last_pc` is stated for
   `(dite-ctx) (Fin.last (a + P.numRegs + 1)) =
   ((URMState.init P v).runFor P y).pc` (plan lines
   1579 – 1588). But the post-`simp only` goal contains
   `(dite-ctx) ⟨a + 1 + P.numRegs, _⟩` (the Fin-index form
   produced by `I_prev`'s deliberate explicit construction
   `KMor1.proj ⟨a + 1 + P.numRegs, by omega⟩` per Step 5.1's
   R1-S3-motivated explicit-index choice, then unfolded by
   `simp only [I_prev, KMor1.interp_proj]`). The two Fin-index
   forms differ syntactically (`a + 1 + P.numRegs` vs
   `a + P.numRegs + 1`), are propositionally equal via
   `Fin.ext` and Nat commutativity, but are not definitionally
   equal under Lean's `Nat.add` reduction. `rw` requires
   syntactic pattern-match of the LHS; without an intermediate
   `Fin.ext`-bridge step (analogous to the `hidx` rewrite at
   plan lines 1594 – 1597 inside the `h_ctx_last_pc`
   derivation itself), the closing `rw [h_ctx_last_pc]` does
   not fire. The same defect propagates to all
   `.assign`/`.inc`/`.dec`/`.stop` blocks in both Step 7.8
   (PC component) and Step 7.9 (register component); the
   `.jumpZ` block does not depend on
   `h_ctx_last_pc` at this site, so it is unaffected. The plan
   needs an explicit bridging `hidx` or a `show … = …` rewrite
   in each per-instruction block, or an alternative
   formulation of `h_ctx_last_pc` stated for the
   `⟨a + 1 + P.numRegs, _⟩` form directly.

   *Author response — TBD.*

### Serious

1. **The plan's `cases h_instr : P.instrs[pcVal]'h_inbounds
   with` discharge in Steps 7.8 / 7.9 may fail at the inner
   match because of the bound-proof-object difference between
   `h_inbounds` and `⟨pcVal, h_inbounds⟩.isLt`.** The
   round-3 review (R3-S2) raised this same concern and the
   plan's response was to apply `simp only [branches_pc,
   h_instr, …]` to propagate the case-equation. However,
   the case-equation `h_instr : P.instrs[pcVal]'h_inbounds =
   URMInstr.assign i c` and the inner-match subject
   `P.instrs[⟨pcVal, h_inbounds⟩.val]'⟨pcVal,
   h_inbounds⟩.isLt` (after `branches_pc` unfolds) involve
   different `GetElem`-bound proofs. While `GetElem.getElem`
   is proof-irrelevant in its bound argument (so the two
   expressions are propositionally equal), `simp only
   [h_instr]` rewrites only syntactically. Without a
   `congr` step or a `show … = …` to align the bound-proof
   shape, `simp only [h_instr]` will not rewrite the inner
   match. The plan's note at lines 1620 – 1627 acknowledges
   the issue but proposes `simp only [branches_pc, h_instr,
   URMState.step, dif_pos h_inbounds]` "in one stroke" —
   that single-pass simp call may or may not chain past the
   bound-proof difference, but the plan does not commit to
   any specific bridge if it fails. An executable plan step
   needs either a deterministic discharge or an explicit
   fallback (e.g. `subst h_instr` if substitution is
   permitted, or an intermediate `show` rewrite). As
   currently written, this step requires the implementer to
   debug 10 sites in Step 7.8 plus 10 sites in Step 7.9.

   *Author response — TBD.*

2. **Step 7.8's `.jumpZ` block closes with `simp` and
   `simp [h_zero]` without a `simp only` whitelist, risking
   `Classical.choice` introduction.** At plan lines 1655 – 1656
   the proof discharges the `.jumpZ` PC sub-case via
   `· rw [h_zero]; simp` and `· rw [if_neg h_zero]; simp
   [h_zero]`. Bare `simp` (no `only`) pulls in the entire
   default simp set, which on goals involving `Fin.cons`,
   propositional `if`, and possibly `Decidable` instances has
   a non-trivial probability of inducing
   `Classical.choice` use (per project memory
   [`feedback_mathlib_choice_in_functor_cat.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_mathlib_choice_in_functor_cat.md);
   `NatTrans.id` and similar bare-`simp` artifacts route
   through `Classical.choice`). The
   `scripts/check-axioms.sh` audit in Step 7.11 will catch
   this post-hoc, but the plan's discharge as written does
   not pre-empt it. Use `simp only [list-of-lemmas]` and
   enumerate the closing simp set (likely
   `[if_pos h_zero]` or `[if_neg h_zero, Nat.succ_ne_zero,
   …]`); pre-empt the audit failure.

   *Author response — TBD.*

3. **Step 5.2's `branches_pc` definition consumes `URMInstr`
   non-exhaustively via the wildcard `_` arm.** At plan lines
   1062 – 1076, `branches_pc` uses `URMInstr.stop`,
   `URMInstr.jumpZ`, and `_` to catch the remaining three
   constructors (`.assign`, `.inc`, `.dec`). Round-3 (R3-M5)
   flagged the wildcard as Minor; the author response was
   unrecorded. Per mathlib's `style.html` and project
   precedent in
   [`GebLean/Utilities/ZeroTestURM.lean:155 – 172`](../../GebLean/Utilities/ZeroTestURM.lean#L155)
   (where `URMState.step` enumerates all five constructors
   explicitly), the exhaustive form is preferred. The
   wildcard is unstable against future `URMInstr` extensions
   and silently catches mis-named constructors. The spec
   `§ 3.4` lines 213 – 219 mirrors the wildcard, so this
   review elevates the finding from Minor to Serious only
   because the wildcard interacts directly with the
   case-equation propagation in Steps 7.8 / 7.9 (Serious 1):
   if the plan switches the case-discharge to explicit
   per-constructor `match` arms, the K^sim side must also
   enumerate all five constructors, requiring a spec edit and
   plan re-issue.

   *Author response — TBD.*

4. **Step 7.4's base-case `URMState.runFor_zero` invocation
   followed by `rfl` may fail at the PC component because
   `(URMState.init P v).pc = 0` is `rfl`, but the goal
   contains `KMor1.zero.interp …` reduced through
   `interp_zero` to `0` and then needs to match
   `((URMState.init P v).runFor P 0).pc` which after
   `runFor_zero` reduces to `(URMState.init P v).pc`.** The
   `URMState.init`'s `pc := 0` field is definitional, so
   `(URMState.init P v).pc` should reduce to `0` by structure
   projection. The Step 7.4 discharge at plan lines
   1485 – 1486 reads `rw [URMState.runFor_zero]; rfl`. The
   `rw` succeeds (`runFor_zero` reduces `runFor P s 0` to
   `s`); the trailing `rfl` then needs
   `0 = (URMState.init P v).pc`. Whether `rfl` closes this
   depends on whether structure-projection reduction fires
   automatically on `(URMState.init P v).pc`. In Lean 4 this
   usually works via `iota`-reduction, but for structures
   built with `where` (as `URMState.init` is — see
   [`ZeroTestURM.lean:254 – 261`](../../GebLean/Utilities/ZeroTestURM.lean#L254)),
   the projection may need an explicit `simp only
   [URMState.init]` or `unfold URMState.init` to expose the
   field value. The plan should add an explicit
   `simp only [URMState.init]` (or use `show 0 = (0 : ℕ);
   rfl` with a preceding `unfold`) to defend the `rfl`.

   *Author response — TBD.*

5. **Step 7.8 / 7.9's `simp only [URMState.step, dif_pos
   h_inbounds, h_instr]` pattern includes
   `dif_pos h_inbounds` in a `simp only` invocation, which
   per project memory
   [`feedback_simp_if_pos_sorryAx_leak.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_simp_if_pos_sorryAx_leak.md)
   risks silent `sorryAx` leakage.** The memory entry
   documents that `simp only [if_pos h]` (with `h` as a
   local hypothesis) leaks `sorryAx` because of an
   internal failure mode in the simp engine; the
   recommended substitute is `rw [if_pos h]`. `dif_pos` is
   the `dite` variant of the same pattern and likely
   exhibits the same internal pathway. The plan invokes
   this pattern at plan lines 1633, 1638, 1643, 1649,
   1659, 1681 (Step 7.8); 1752, 1768, 1782, 1797, 1802,
   1822 (Step 7.9). Each invocation should be rewritten
   as `rw [dif_pos h_inbounds]` (then a separate
   `simp only [URMState.step, h_instr]` or
   `rw [URMState.step]` to unfold) — at least until the
   audit confirms `[propext, Quot.sound]`-only hygiene.
   The Step 7.11 axiom audit will detect the leak post-hoc,
   but pre-emptively switching to `rw` is defensive
   against the documented pattern.

   *Author response — TBD.*

6. **Step 7.9's `.jumpZ` discharge at plan lines 1794 – 1799
   asserts `exact ih_regs j` without first reducing the
   goal's K^sim side past the `pcDispatch_match` →
   `branches_j` → `v_j_prev` → `interp_proj` chain.** After
   `simp only [branches_j, h_instr, v_j_prev,
   KMor1.interp_proj]` and `simp only [URMState.step,
   dif_pos h_inbounds, h_instr]`, the LHS becomes
   `(dite-ctx) ⟨a + 1 + j.val, _⟩` (per `v_j_prev`'s
   explicit-index form). The RHS is
   `((URMState.init P v).runFor P y).regs j` (URM-side regs
   field untouched by jumpZ). `ih_regs j` has type
   `KMor1.simrecVec … y j.castSucc =
   ((URMState.init P v).runFor P y).regs j`. The
   `dite-ctx` on `⟨a + 1 + j.val, _⟩` needs to reduce to
   `KMor1.simrecVec … y ⟨(a + 1 + j.val) - (a + 1), _⟩` via
   the `dif_neg` branch of the dite (since
   `(a + 1 + j.val) ≥ a + 1`), then the
   `⟨j.val, _⟩` sub-Fin needs to be bridged to `j.castSucc`
   via `Fin.ext`. The plan's `exact ih_regs j` does not
   discharge this bridging. The same gap is present in
   Step 7.9's `.stop` discharge at plan line 1803, and is
   structurally identical to the `h_ctx_last_pc` reduction
   already done for the PC slot (lines 1594 – 1598) — but
   for each register component the analog has not been
   stated. The plan needs a per-component bridging lemma
   `h_ctx_reg_j : (dite-ctx) ⟨a + 1 + j.val, _⟩ =
   ((URMState.init P v).runFor P y).regs j` derived in
   parallel with `h_ctx_last_pc`, and applied to close
   `.jumpZ` and `.stop` in Step 7.9.

   *Author response — TBD.*

7. **Step 4.3's `cases h : (List.finRange a).find? …`
   discharge closes both `some i` and `none` arms with bare
   `rfl`, depending on whether `(KMor1.proj i).level` and
   `(KMor1.zero).level` both reduce to `0` definitionally
   through `simp only [baseFamily,
   Fin.lastCases_castSucc]`.** At plan lines 971 – 974,
   the discharges are `| some i => rfl` and `| none =>
   rfl`. The `KMor1.level` recursive clauses
   ([`LawvereKSim.lean:105`](../../GebLean/LawvereKSim.lean#L105))
   compute `proj.level = 0` and `zero.level = 0` by `rfl`,
   so the discharge plausibly succeeds. The risk is that
   after `simp only [baseFamily, Fin.lastCases_castSucc]`,
   the goal's form contains the
   `match (List.finRange a).find? … with | some i => … |
   none => …` expression whose `level` projection inside
   would need first to reduce through the `match`. After
   `cases h : (List.finRange a).find? …`, the match
   reduces in each branch (`cases` substitutes the cased
   expression in the goal), so `(KMor1.proj i).level = 0`
   and `(KMor1.zero).level = 0` should each be `rfl`. The
   step should still compile, but the discharge form is
   fragile against future changes in
   `KMor1.level`'s reduction strategy (e.g., if the field
   becomes `@[reducible]` rather than definitionally `0`).
   A more robust closing would be `simp only
   [KMor1.level]` or `unfold KMor1.level; omega`.

   *Author response — TBD.*

### Minor

1. **The plan's Step 7.8 PC `.stop` discharge at plan line
   1660 reads `exact h_ctx_last_pc`, treating
   `h_ctx_last_pc` as the goal's closing equality.**
   `h_ctx_last_pc` has type
   `(dite-ctx) (Fin.last (a + P.numRegs + 1)) =
   ((URMState.init P v).runFor P y).pc`. The `.stop` goal
   after `simp only [branches_pc, h_instr, I_prev,
   KMor1.interp_proj]` is `(dite-ctx) ⟨a + 1 + P.numRegs,
   _⟩ = (URMState.step P (URMState.runFor P (URMState.init
   P v) y)).pc`. After `simp only [URMState.step, dif_pos
   h_inbounds, h_instr]`, the RHS reduces to the `.stop`
   case's identity body, i.e.
   `(URMState.runFor P (URMState.init P v) y).pc` (since
   the `.stop` case in `URMState.step` returns `s`
   unchanged). The goal then is
   `(dite-ctx) ⟨a + 1 + P.numRegs, _⟩ =
   ((URMState.runFor P (URMState.init P v) y)).pc`. This
   matches `h_ctx_last_pc`'s shape modulo the same
   Fin-index form mismatch flagged in Blocker 2. The
   `exact h_ctx_last_pc` will not close until Blocker 2
   is addressed; the more fundamental issue is captured in
   Blocker 2.

   *Author response — TBD.*

2. **The defer-to-execution
   `mcp__lean-lsp__lean_goal` notes (R3-M1)
   accumulate at Steps 3.6, 5.6, 7.8, 7.9.** Round-3
   re-flagged R3-M1; the author response was deferred.
   The notes remain at plan lines 717 – 719 (Step 3.6),
   1289 – 1293 (Step 5.6), 1690 – 1693 (Step 7.8 closing
   note), and 1703 – 1706 (Step 7.9 opening note). Each
   accumulation makes the plan's "every step is
   independently executable" claim weaker. The notes
   should be replaced with explicit fallback tactics or
   removed; the implementer can fall back to
   `lean_goal` without the plan instructing them to do
   so.

   *Author response — TBD.*

3. **Step 7.8 and Step 7.9 still duplicate the
   `h_ctx_last_pc` derivation (R3-M3 deferred).** Plan
   lines 1579 – 1598 and 1716 – 1735 are
   character-for-character identical except for one
   comment line. R3-M3 marked extraction as Minor; the
   round-3 author response was deferred. Once Blocker 1
   and Blocker 2 are resolved, the duplication will
   likely need additional per-branch parametrisation
   (because the in-bounds vs past-end fork sits below the
   shared derivation), but the prelude itself is fully
   shareable as a `have`-binding before
   `refine ⟨?_, ?_⟩` in the succ case. The cleanup is
   modest (~10 LOC saved) but tightens the plan's
   "code is cost" alignment.

   *Author response — TBD.*

4. **The plan's Step 8.6 commit-message body still
   enumerates 19 declaration names inline (R3-M4
   deferred).** Plan lines 2074 – 2082; line 2074 alone is
   the long enumeration. The body wraps to multiple lines
   when `jj describe -m` reflows; the body's structure
   does not strictly violate mathlib's `commit.html`
   72-character target, but the long-paragraph form is
   harder to read than a bulleted list. Minor; the
   round-3 author chose to defer.

   *Author response — TBD.*

5. **Step 2.6's `predIter_level` proof body at plan lines
   500 – 521 contains `unfold KMor1.level` followed by
   `have hsup : Finset.univ.sup (fun _ : Fin 1 => …) ≤ 1`
   plus `omega`, but the `omega` call must close
   `max KMor1.pred.level hsup ≤ 1` which requires
   `KMor1.pred.level = 1` (a `rfl`-reducible numeric
   identity) plus the bound from `hsup`.** The proof
   does not include the `KMor1.pred.level` reduction
   explicitly; `omega` alone with `hsup` in scope as a
   numeric ≤-fact and the goal as a Nat `max` inequality
   should close, but only if the `max` is exposed as
   `max 1 hsup_witness ≤ 1` after the `unfold`. The
   `unfold KMor1.level` on a `pred` term reduces to
   `1` by the `.pred` clause; the result is
   `max 1 (Finset.univ.sup …) ≤ 1`, which `omega` plus
   `hsup` closes. The proof should compile but the
   reasoning chain is sparser than the comparable
   `natK_level` proof; an explicit `have hpred :
   KMor1.pred.level = 1 := rfl` would clarify.

   *Author response — TBD.*

6. **Step 7.10's `lake build` expectation is "zero `sorry`
   warnings, zero errors, zero warnings"; this overlooks
   the docstring-required `def` placeholder
   warning.** At plan line 1837. If the implementer
   follows Step 7.6's `sorry`-skeleton pattern, the
   succ case is built incrementally (Steps 7.6 → 7.7
   intermediate-build → 7.8 → 7.9). By Step 7.10 all
   `sorry`s should be replaced. The "zero warnings"
   claim is correct provided every public declaration
   has a `/-- … -/` docstring and the
   `set!`-vs-`set` distinction does not emit a warning.
   Minor; the expectation can be tightened to
   "zero errors, only acceptable warnings (e.g.
   markdownlint suggestions)".

   *Author response — TBD.*

7. **The plan's Step 9.6 commit message subject
   `chore(ertok): re-export KSimURMSimulator from
   GebLean.lean` is `chore` while the body discusses
   axiom-audit results.** Per mathlib `commit.html` the
   type prefix names the principal change; re-export is
   `chore` per project precedent (audit-only commits
   also `chore`). The body's discussion of
   axiom-hygiene of 19 declarations is acceptable as
   chore-body context. Minor; the type is consistent.

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's "Note:" paragraphs after each Lean code
   block describe lemma-name provenance rather than
   step-outcome.** R3-C1 reaffirmed the same point;
   neither author response converted them to inline
   `--` comments. Reaffirming as cosmetic-taste in
   round 4.

   *Author response — TBD.*

2. **Step 0.3's `jj log` filter is still broad** (R3-C2;
   round-2 C3). Reaffirming as cosmetic-taste in round
   4.

   *Author response — TBD.*

3. **The 19 enumerated `bash scripts/check-axioms.sh`
   invocations across Tasks 1 – 8 and Step 9.3 inflate
   plan LOC** (R3-C3; round-2 C2). Reaffirming as
   cosmetic-taste in round 4.

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat
   `per spec § X.Y` references in a fixed format** (R3-C4;
   round-2 C4). Reaffirming as cosmetic-taste in round 4.

   *Author response — TBD.*
