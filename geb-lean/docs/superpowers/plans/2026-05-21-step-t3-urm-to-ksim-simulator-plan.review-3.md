# Round-3 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 3).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

## Verification log

- Read [`docs/process.md`](../../process.md) § Adversarial review
  (lines 131 – 227): reviewer protocol, severity definitions,
  convergence criterion. Confirmed read-only constraint and
  severity labels.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  end-to-end (892 lines); tabulated § 3 – § 6 against the plan
  task layout.
- Read the plan in full (2089 lines). Confirmed ten-task layout
  (Task 0 – Task 9) and that Task 7 carries the inserted Step 7.7
  intermediate-build step (R2-S7); subsequent step numbers Step
  7.8 – Step 7.12 align.
- Read prior reviews
  [`review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md)
  and
  [`review-2.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-2.md);
  recorded which findings the round-1 and round-2 authors marked
  fix vs reject-as-cosmetic-taste.
- Spot-checked the round-1 and round-2 fix applications:
  - R1-B1 (Step 7.8 register-case fill): present at plan lines
    1665 – 1799. Confirmed.
  - R1-B2 (Steps 3.5/3.6 deletion + renumber): the single
    `interp_pcDispatchFrom_*` block sits at Step 3.5. Confirmed.
  - R1-B3 (Step 3.11 `fin_cases` → `match`): the inner
    discharge of `pcDispatchFrom_level` at plan lines 796 – 799
    uses Lean-core `match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => … |
    ⟨2, _⟩ => …`. Confirmed.
  - R1-S1 (level closure): plan line 801 uses
    `Nat.max_le.mpr ⟨le_refl 1, hsup⟩`. Confirmed.
  - R1-S3 (`I_prev` explicit `Fin` index): plan line 1010 uses
    `KMor1.proj ⟨a + 1 + P.numRegs, by omega⟩`. Confirmed.
  - R1-S5 (Step 8.1 explicit chain): plan lines 1883 – 1885 use
    `simp only [simulate, KMor1.interp_simrec, Fin.cons_zero,
    Fin.cons_succ]` plus
    `exact (simulate_step_match P v y).2 P.outputReg`.
    Confirmed.
  - R1-S6 (Step 5.6 explicit per-`URMInstr` cases): plan lines
    1144 – 1258 enumerate each constructor. Confirmed.
  - R1-S7 (rename to `runFor_succ_init_back`): declaration at
    plan line 1397, axiom audit at line 1817. Confirmed.
  - R2-B1 (Step 7.7 / 7.8 / 7.9 bridging via the `dite`-form
    last-slot reduction): the `h_ctx_last_pc` hypothesis with
    the explicit `dite`-form lambda appears at plan lines
    1552 – 1571 (PC branch) and 1686 – 1704 (register branch).
    The `dif_neg (by omega)` and `hidx` discharge of
    `⟨a + P.numRegs + 1 - (a + 1), _⟩ = Fin.last P.numRegs`
    appear at lines 1566 – 1570 and 1699 – 1703. Confirmed.
  - R2-S1 (Steps 1.5 / 1.6 sup-lemma fix): plan lines 237 – 241
    use `Finset.sup_le` with the inhabitant
    `intro _ _; rw [ih]`; plan lines 279 – 281 use
    `Finset.univ_eq_empty _` plus `Finset.sup_empty`. The
    lemma names exist in mathlib (`Finset.sup_le` at
    `Mathlib.Order.SetNotation`; `Finset.univ_eq_empty` at
    `Mathlib/Data/Finset/BooleanAlgebra.lean:71`).
  - R2-S2 (Step 2.6 `predIter_level` body): plan lines
    480 – 502 use `unfold KMor1.level` + `Finset.sup_le` +
    `omega`. The dead `cases h` block flagged in R2-S2 is gone.
    Confirmed.
  - R2-S3 (`pcDispatchFrom_level` recursive unfold): plan
    lines 776 – 783 use `change max (KMor1.cond.level)
    (Finset.univ.sup (fun i : Fin 3 => match i with …)) ≤ 1`
    rather than `simp only [KMor1.level]`. Confirmed.
  - R2-S4 (`runFor_succ_init_back` `rw` order): plan lines
    1408 – 1410 use explicit positional arguments
    `URMState.runFor_add P s y 1`,
    `URMState.runFor_succ P (URMState.runFor P s y) 0`,
    `URMState.runFor_zero`. Confirmed.
  - R2-S5 (Step 5.6 `KMor1.succ/pred` simp args): plan lines
    1146 – 1156 (assign), 1158 – 1166 (inc), 1167 – 1176 (dec)
    use the `unfold KMor1.level I_prev` + `Finset.sup_le` +
    `omega` discharge in place of `simp […, KMor1.succ]`.
    Confirmed.
  - R2-S6 (Step 7.4 `URMState.init` reduction): plan lines
    1477 – 1484 use
    `show … = (URMState.init P v).regs j; unfold URMState.init;
    simp only [h]`. Confirmed.
  - R2-S7 (Step 7.6 / 7.7 intermediate-build discipline): new
    Step 7.7 inserted at plan lines 1517 – 1529. Subsequent
    step numbers shifted; the doctoc TOC reflects ten tasks
    only at the section level (not per-step). Confirmed.
- Verified line numbers cited in the plan against landed code:
  - `URMState.step` at
    [`GebLean/Utilities/ZeroTestURM.lean:155`](../../GebLean/Utilities/ZeroTestURM.lean#L155);
    the `.stop` case returns `s` unchanged.
  - `URMState.runFor_succ` `@[simp]` at
    [`ZeroTestURM.lean:192`](../../GebLean/Utilities/ZeroTestURM.lean#L192);
    `URMState.runFor_add` at
    [`ZeroTestURM.lean:199`](../../GebLean/Utilities/ZeroTestURM.lean#L199);
    `URMState.runFor_zero` at
    [`ZeroTestURM.lean:186`](../../GebLean/Utilities/ZeroTestURM.lean#L186).
  - `KMor1.simrecVec_succ` `@[simp]` body at
    [`LawvereKSimInterp.lean:193 – 209`](../../GebLean/LawvereKSimInterp.lean#L193);
    confirmed the dite-form context whose last-slot value is
    `KMor1.simrecVec h g params n
    ⟨idx.val - (a + 1), _⟩` for `idx.val ≥ a + 1`.
  - `Finset.univ_eq_empty` at
    `.lake/packages/mathlib/Mathlib/Data/Finset/BooleanAlgebra.lean:71`
    (signature: `[IsEmpty α] : (univ : Finset α) = ∅`).
- Re-fetched mathlib upstream guides
  ([`naming.html`](https://leanprover-community.github.io/contribute/naming.html),
  [`style.html`](https://leanprover-community.github.io/contribute/style.html),
  [`doc.html`](https://leanprover-community.github.io/contribute/doc.html),
  [`commit.html`](https://leanprover-community.github.io/contribute/commit.html))
  via the digest in
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md);
  scanned commit-message bodies, declaration names, and
  docstring sections against each.
- Cross-referenced project memories
  [`feedback_fin_cases_pulls_classical_choice.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_fin_cases_pulls_classical_choice.md),
  [`feedback_simp_if_pos_sorryAx_leak.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_simp_if_pos_sorryAx_leak.md),
  [`feedback_mathlib_choice_in_functor_cat.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_mathlib_choice_in_functor_cat.md),
  and
  [`feedback_urmstate_init_let_reduction.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_urmstate_init_let_reduction.md)
  against the plan's tactic choices.
- Re-read the unapplied round-1 items (M2, M4, M6, all
  cosmetic-taste) and the unapplied round-2 items (M2, M4, M7,
  all cosmetic-taste) against the current plan; assessed
  whether each remains a defect in round 3.

## Findings

### Blocker

1. **Step 3.5's `interp_pcDispatchFrom_match` proof contains
   an `if ... then _ else _ = _` `have`-block whose
   placeholder unification cannot succeed.** At plan lines
   658 – 661, the proof writes
   `have hreduce : (if ctx (Fin.last n) - k = 0 then _ else
   _) = _ := by rw [if_neg hsub]`. Each `_` in the `have`
   type is an unconstrained metavariable: Lean cannot
   determine the then-branch, else-branch, or RHS without
   first elaborating the `rw`. The `rw [if_neg hsub]` is
   inside the `by` block whose target is the metavariable-
   laden equation; `rw` requires a concrete LHS pattern in
   the goal to match against. The metavariables would not be
   pinned by the local context. After this `have` fails to
   elaborate, the subsequent `rw [hreduce]` (line 661)
   cannot fire either. The intended discharge — apply
   `if_neg hsub` to the post-simp goal directly — would be
   written as `rw [if_neg hsub]` against the open goal (with
   no `have`), or by adding `if_neg hsub` to the preceding
   `simp only`. The block as written will not compile.

   *Author response — TBD.*

### Serious

1. **The bridged `h_ctx_last_pc` hypothesis in Steps 7.8 /
   7.9 will not unify with `KMor1.interp_pcDispatch_match`
   /`_default`'s `h` argument.** At plan lines 1552 – 1571
   (PC branch) and 1686 – 1704 (register branch), the
   author derives the hypothesis form
   `(dite-ctx) (Fin.last (a + P.numRegs + 1)) = …`. When
   the `rw [KMor1.interp_pcDispatch_match … h_ctx_last_pc]`
   call (line 1578) fires, the lemma's `h` parameter has
   type `ctx (Fin.last n) = k.val` with `n = a + P.numRegs +
   1` (per Step 5.1's typing of `stepFamily P` as
   `Fin (P.numRegs + 1) → KMor1 (a + 1 + (P.numRegs + 1))`
   and the dispatcher's return arity `n + 1 = a + 1 +
   (P.numRegs + 1)`, so `n = a + P.numRegs + 1`). The form
   of `n` Lean infers is `a + P.numRegs + 1` (left-
   associated), while `h_ctx_last_pc` is stated for
   `Fin.last (a + P.numRegs + 1)`. So the literal `n`
   should match. The defect is on a different axis: the
   `set pcVal := ((URMState.init P v).runFor P y).pc` at
   line 1576 plus the explicit
   `⟨pcVal, h_inbounds⟩ h_ctx_last_pc` argument supply
   `k.val = pcVal`. The lemma requires
   `ctx (Fin.last n) = k.val`; `h_ctx_last_pc` claims
   `ctx (Fin.last (a + P.numRegs + 1)) =
   ((URMState.init P v).runFor P y).pc`. After `set pcVal
   := …`, the RHS of `h_ctx_last_pc` is still spelled
   `((URMState.init P v).runFor P y).pc` (the `set` only
   substitutes in the goal, not in already-bound
   hypotheses unless invoked with `with hpc`). The author
   adds `with hpc` (line 1576), which records the equality
   but does not rewrite `h_ctx_last_pc`. The implementer
   must add an explicit
   `rw [← hpc] at h_ctx_last_pc` (or include `hpc.symm` in
   the `rw` chain) before the `KMor1.interp_pcDispatch_match`
   invocation. Otherwise the `h` argument's
   `ctx (Fin.last n) = pcVal` cannot be discharged by
   `h_ctx_last_pc`'s `… = ((URMState.init P v).runFor P y).pc`.

   *Author response — TBD.*

2. **Step 7.8's per-instruction `rw [h_instr]` after
   `cases h_instr : P.instrs[pcVal]'h_inbounds with | …`
   is redundant or wrong-directional.** In Lean 4, `cases
   h_instr : expr with | ctor a b => …` substitutes
   `expr → ctor a b` in the branch's goal AND introduces
   `h_instr : expr = ctor a b`. After `cases`, the goal
   already contains `URMInstr.assign i c` in place of
   `P.instrs[pcVal]'h_inbounds`. The plan's subsequent
   `rw [h_instr]` (e.g. plan lines 1586, 1591) attempts to
   rewrite `P.instrs[pcVal]'h_inbounds` (already absent
   from the goal) to `URMInstr.assign i c` — a no-op at
   best, or `rw` failure ("did not find instance of the
   pattern") at worst. The `unfold branches_pc` (line
   1585) substitutes `branches_pc`'s body, exposing the
   inner `match P.instrs[k]'k.isLt with …`. Here `k` is
   from the dispatcher's `branches : Fin size →
   KMor1 (n + 1)` parameter, so the index inside
   `branches_pc` is the dispatcher's `k`, NOT `pcVal`. The
   plan supplies the dispatcher's branch argument as
   `⟨pcVal, h_inbounds⟩`, so the inner match becomes
   `match P.instrs[⟨pcVal, h_inbounds⟩]'_ with …`. The
   `rw [h_instr]` needs to rewrite this inner-match
   subject, not the outer one. The Fin-index proof object
   `h_inbounds` versus `k.isLt` (the inner match's bound
   proof) may differ, blocking `rw`. The intended
   discharge would be `subst h_instr` (if substitution is
   permitted) or to thread the case-equation directly
   into the match via `simp only [h_instr]`. As written,
   the implementer will need to debug the rewrite at
   every per-constructor block (5 cases × 2 PC/reg = 10
   sites in Step 7.8, plus 10 more in Step 7.9).

   *Author response — TBD.*

3. **The `cases h : (List.finRange a).find? …` blocks in
   Step 4.3 and Step 7.4 omit the `with` clause's
   equation-naming and may not generalise the matched
   expression.** At plan lines 946 – 949 (Step 4.3) the
   proof writes `cases (List.finRange a).find? … with |
   some i => rfl | none => rfl`. Without `h :` to name
   the equation, `cases` substitutes the matched
   expression in the goal but does not introduce a
   hypothesis. The Step 4.3 body's `rfl` then closes only
   if the `match` inside `baseFamily`'s `castSucc` branch
   reduces to the same form after substitution. The
   `baseFamily` definition (plan lines 905 – 916) uses
   `match (List.finRange a).find? …` — the same
   syntactic match, so `cases` on the matched expression
   reduces both occurrences. The `rfl` should close
   provided Lean's `cases` rewrites all occurrences (it
   does for non-dependent positions). Step 7.4's
   counterpart (line 1473) DOES use `cases h : …`, so the
   discrepancy is between the two sites. Confirm whether
   the unnamed `cases` form at line 946 still reduces
   `baseFamily`'s inner match; if Lean's `cases` does not
   propagate the rewrite under `simp only [baseFamily,
   Fin.lastCases_castSucc]`'s normal form, the proof
   fails.

   *Author response — TBD.*

4. **Step 4.3's `induction j using Fin.lastCases with |
   last => … | cast r => …` does not match the
   project-idiomatic Fin.lastCases call form.** At plan
   lines 938 – 945, the proof opens with `induction j
   using Fin.lastCases with`. The plan's note (line 936)
   claims this is "project-idiomatic per
   GebLean/LawvereBTInterp.lean:627, 637, 669". Verified
   `LawvereBTInterp.lean:625, 627, 637, 668, 669`: the
   project uses `refine Fin.lastCases ?_ ?_ i` followed
   by `simp only [Fin.lastCases_last]` and `simp only
   [Fin.lastCases_castSucc]`, NOT the `induction …
   using` named-pattern syntax. `Fin.lastCases` is
   defined in mathlib as a `def` returning a function,
   not (necessarily) tagged `@[elab_as_elim]`; whether
   `induction … using Fin.lastCases with | last | cast`
   accepts those particular alternative names depends on
   the underlying constructor names and the
   `induction`-eliminator elaborator's binding rules.
   The project-precedent form is `refine`. Step 5.6 uses
   the same `induction j using Fin.lastCases with`
   syntax (plan lines 1131 – 1134, 1205 – 1206). If
   neither name resolves, both Step 4.3 and Step 5.6
   level lemmas will fail at the case-split.

   *Author response — TBD.*

5. **Step 2.1's `KMor1.predIter` is declared inside
   `namespace GebLean` but the surrounding two
   `namespace … end` blocks are empty placeholders.**
   At plan lines 405 – 417, the file's namespace skeleton
   is two empty namespaces with `open` statements that
   have no consumers; the `KMor1.predIter` declaration
   from Step 2.3 onward is meant to be inserted "inside
   the `namespace GebLean` block (replacing or
   augmenting the empty body)" (line 430). The
   instruction is ambiguous about whether subsequent
   tasks (Tasks 3 – 6) insert into the same `namespace
   GebLean` block or into the `namespace GebLean.
   KSimURMSimulator` block. Step 3.1 says "inside
   `namespace GebLean`, after `predIter_level`" (line
   557 – 558); Step 4.1 says "inside `namespace
   GebLean.KSimURMSimulator`" (line 882). The file
   skeleton has `end GebLean` BEFORE `namespace GebLean.
   KSimURMSimulator`. So the implementer must insert
   Tasks 2 – 3 content before the first `end GebLean`,
   then Tasks 4 – 8 content between `namespace GebLean.
   KSimURMSimulator` and `end GebLean.KSimURMSimulator`.
   The plan does not state the insertion-discipline
   explicitly; the implementer following Steps 2.1 →
   2.3 → 3.1 → 4.1 may end up inserting Step 3.1's
   content inside the wrong namespace block (between the
   `namespace GebLean.KSimURMSimulator` opening and
   the start of the `baseFamily` body, since both
   instructions name `namespace GebLean`). Step 4.1's
   instruction at line 887 says only "Insert inside
   `namespace GebLean.KSimURMSimulator`", which would be
   correct if it's been clear that Tasks 4 – 8 live in
   the second namespace. The plan would benefit from a
   one-line file-layout reference table at the top of
   Task 2 spelling out which task's content goes in
   which namespace block.

   *Author response — TBD.*

6. **The `Finset.univ_eq_empty _` call in Step 1.6 passes
   an explicit underscore for an instance argument.** At
   plan line 280, the proof writes `show (Finset.univ :
   Finset (Fin 0)) = ∅ from Finset.univ_eq_empty _`. The
   lemma's signature is `Finset.univ_eq_empty [IsEmpty α]
   : (univ : Finset α) = ∅` (verified at
   `.lake/packages/mathlib/Mathlib/Data/Finset/BooleanAlgebra.lean:71`).
   It takes no explicit positional arguments. Passing
   `_` in the positional position is syntactically
   accepted by Lean only when the instance argument is
   the next argument to be filled; here, `Finset.univ_eq_empty`
   has no explicit positional arguments at all. The
   correct form is `Finset.univ_eq_empty` (no underscore),
   relying on Lean's instance-resolution to infer
   `IsEmpty (Fin 0)`. If Lean fails to resolve the
   instance, the explicit form is `@Finset.univ_eq_empty
   (Fin 0) (inferInstance)` or `Finset.univ_eq_empty
   (α := Fin 0)`. The `Finset.univ_eq_empty _` as written
   may or may not parse, depending on whether Lean
   interprets the underscore as a positional argument or
   as a hint for the next instance slot.

   *Author response — TBD.*

7. **Step 7.8's `simp [ih_pc]` close at the end of each
   `.assign`/`.inc`/`.dec` block (plan lines 1592, 1600,
   1608) depends on goal shape that is not reachable
   from the preceding `simp only` chain.** After
   `rw [KMor1.interp_pcDispatch_match …]`, the LHS is
   `(branches_pc P ⟨pcVal, h_inbounds⟩).interp ctx`
   where `ctx` is still the `dite`-form. The
   `unfold branches_pc; rw [h_instr]` exposes the
   `.assign` branch: `KMor1.comp KMor1.succ (fun _ : Fin
   1 => I_prev P)`. After `simp only [KMor1.interp_comp,
   KMor1.interp_succ, I_prev, KMor1.interp_proj]`, the
   LHS becomes `ctx ⟨a + 1 + P.numRegs, _⟩ + 1` (with
   the `ctx` still being the `dite`-form lambda). The
   plan never bridges this to
   `((URMState.init P v).runFor P y).pc + 1`. The
   `simp [ih_pc]` (line 1592) gives `simp` access to
   `ih_pc : KMor1.simrecVec … y (Fin.last P.numRegs) =
   ((URMState.init P v).runFor P y).pc`, but the LHS
   expression does NOT contain
   `KMor1.simrecVec … y (Fin.last P.numRegs)`
   syntactically — it contains
   `(dite-ctx) ⟨a + 1 + P.numRegs, _⟩`, which would
   have to reduce through the `dite` to the simrecVec
   form first. `simp` with no further hints may or may
   not perform that reduction. The plan should add
   `h_ctx_last_pc` to the `simp` set (e.g.
   `simp [ih_pc, h_ctx_last_pc]`) and rewrite the
   `dite`-ctx form before invoking `ih_pc`. The same
   gap appears in Step 7.9's per-instruction blocks
   when `Function.update_apply` plus `if_neg` reduces
   to `s.regs j` and then needs to be bridged to the
   K^sim side.

   *Author response — TBD.*

### Minor

1. **The plan's note at Step 3.6 (line 696 – 699), Step
   5.6 (line 1261 – 1266), Step 7.8 (line 1654 – 1663),
   and Step 7.9 (line 1801 – 1805) defers goal-shape
   verification to `mcp__lean-lsp__lean_goal` at execution
   time.** Round-2 finding M4 flagged this pattern as a
   code-smell that degrades the plan's "each step
   independently executable" property. Round 2 marked the
   item as Minor; the author response was unrecorded
   (Minor R2-M4 is not in the listed-applied round-2
   fixes). The defer-to-execution-time notes still
   accumulate across at least four steps. The
   accumulation remains a Minor concern.

   *Author response — TBD.*

2. **Step 2.1's `open GebLean.ZeroTestURM` duplication
   persists (round-2 finding M2 was not applied).** At
   plan lines 407 and 413, `open GebLean.ZeroTestURM`
   appears in both the empty `namespace GebLean` block
   and the empty `namespace GebLean.KSimURMSimulator`
   block. The first `open` has no consumers within its
   namespace (the `GebLean`-namespace block is structural
   placeholder content per the file skeleton, and the
   later `KMor1.predIter` insertion at Step 2.3 — if
   placed inside `namespace GebLean` — uses bare
   `URMProgram`/`URMState` references only inside its
   helper consumers). Since neither this finding nor the
   round-2 author response addressed it, the duplicate
   `open` remains stylistically incorrect against
   `lean-coding.md` § Coding style "do not mix
   `namespace X` blocks with content outside them in the
   same file".

   *Author response — TBD.*

3. **Step 7.8 and Step 7.9 duplicate the entire
   `h_ctx_last_pc` derivation block (plan lines
   1552 – 1571 vs 1686 – 1704).** The two blocks are
   character-for-character identical. The author's
   parenthetical note at plan lines 1683 – 1685
   acknowledges the duplication and defers extraction
   ("consider extracting a Task-7-prelude helper if the
   inline form proves duplicative during execution").
   For a plan whose discipline includes "code is cost"
   (`CLAUDE.md` § Rules), the redundancy ought to be
   eliminated before user review by extracting a private
   helper lemma `h_step_ctx_last_eq_pc` at the top of
   Step 7 (before the `simulate_step_match` declaration),
   then invoking it from both branches. Each block adds
   ~20 LOC × 2 = ~40 LOC of duplicated proof; the helper
   would be ~10 LOC plus 1 LOC of invocation per branch.

   *Author response — TBD.*

4. **The plan's Step 9.6 commit-message body uses a
   colon-introduced enumeration that exceeds the
   ~72-character line target.** At plan lines
   2050 – 2057, the commit message body lists 19
   declaration names in a paragraph that exceeds 72
   characters per line. The body wrapping is not
   guaranteed when the commit subsequently goes through
   `jj describe -m`. The mathlib `commit.html` guide
   recommends keeping body lines within 72 characters;
   the enumeration could be split into one-per-line
   list items or shortened to "all 19 T3-introduced
   public declarations (see plan Task 9)".

   *Author response — TBD.*

5. **The plan's `branches_pc` definition at Step 5.2
   uses `URMInstr.stop => I_prev P` for the stop case
   and `_ => KMor1.comp KMor1.succ (fun _ : Fin 1 =>
   I_prev P)` as the default-arm for `.assign`/`.inc`/
   `.dec`.** The wildcard `_` arm catches all
   constructors not explicitly named, including future
   additions to `URMInstr` (none are planned, but the
   pattern is brittle). Mathlib `style.html` and
   project-idiomatic discipline prefer exhaustive
   constructor enumeration over wildcards in
   pattern-match arms, both for readability and for the
   exhaustiveness checker's pinpoint diagnostics. The
   plan would be more robust with explicit `URMInstr.assign`,
   `URMInstr.inc`, `URMInstr.dec` arms.

   *Author response — TBD.*

6. **Step 7.8 cites `h_pc_eq` and `h_pc_ge` in its closing
   note (plan lines 1654 – 1655) but the proof body uses
   `h_ctx_last_pc` and `h_ctx_ge`.** The closing note
   appears to be stale prose carried over from an earlier
   draft. Tightening the note to reference the actual
   hypothesis names would reduce reader confusion.

   *Author response — TBD.*

7. **The doctoc TOC at plan lines 34 – 46 lists nine
   tasks (Task 0 through Task 9 by their renamed
   headings) but the auto-update region's heading
   anchors do not encode step-level granularity.** The
   TOC is correctly markdownlint-clean; the
   plan-internal "Step 7.7" anchor inserted by R2-S7 is
   not exposed in the TOC, so cross-references to "Step
   7.7" (e.g. "per plan round-2 finding R2-S7") are not
   navigable from the TOC. This is acceptable per
   `markdown-writing.md` § Tables of contents (the TOC
   carries only `##`-level headings), but readers
   navigating from an external link to a specific step
   number must use full-text search.

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's "Note:" paragraph after each `lake build`
   step describes the previous step's mechanics rather
   than the build's expected outcome.** Examples: Step
   1.4 closing note (lines 244 – 249), Step 2.5 closing
   note (lines 504 – 508). The notes' content is
   substantive (lemma-name justifications) but the
   "Note:" label is overused. Suggestion: replace with
   inline `--` comments inside the Lean code block where
   the lemma names are cited.

   *Author response — TBD.*

2. **Step 0.3's `jj log` filter (plan line 137) glob-
   matches `'docs(ertok)*plan*'`.** Round-2 cosmetic-
   taste C3 noted the glob is broad. The current form
   `jj log -r 'description(glob:"docs(ertok)*plan*")'
   --no-graph --limit 3` adds `--limit 3` but does not
   tighten the match itself. A `--limit 1` plus a
   stricter glob (`'docs(ertok)*round-2*plan*'`) would
   reduce ambiguity. Cosmetic-taste because the
   implementer can read the listing.

   *Author response — TBD.*

3. **Repeated `bash scripts/check-axioms.sh
   <Fully.Qualified.Name>` enumerations across Tasks
   1 – 8 and Step 9.3 inflate plan LOC.** Round-2
   cosmetic-taste C2 raised this; the round-2 author
   response was to retain the form for per-declaration
   discipline. Reaffirming as Cosmetic-taste in round 3.

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat
   spec-section references in a fixed format (`per spec
   § X.Y`).** Round-2 cosmetic-taste C4 raised the same
   point. Reaffirming as Cosmetic-taste in round 3.

   *Author response — TBD.*
