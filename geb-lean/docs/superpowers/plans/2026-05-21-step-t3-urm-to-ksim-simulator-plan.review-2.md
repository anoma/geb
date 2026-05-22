# Round-2 adversarial review — T3 implementation plan

Reviewer: fresh-context `general-purpose` Agent (round 2).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.md).

## Verification log

- Read [`docs/process.md`](../../process.md) § Adversarial
  review (lines 131 – 227): reviewer protocol, severity
  definitions, convergence criterion. Confirmed read-only
  constraint and severity labels.
- Read the binding spec
  [`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
  end-to-end (892 lines); tabulated spec sections § 3 – § 6 and
  § 10 punch list.
- Read the round-1 review
  [`2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md`](2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-1.md)
  in full; recorded which findings the round-1 author marked
  fix vs reject-as-cosmetic-taste.
- Read the plan in full (1942 lines). Confirmed task layout
  preserved at ten tasks (Task 0 – Task 9). Spot-checked
  Task 3's renumbering after the B2 deletion of Steps 3.5/3.6
  (now Step 3.5 — `interp_pcDispatchFrom_*` inner lemmas; old
  Step 3.7 content; subsequent steps renumbered through 3.13).
- Verified the round-1 fix application:
  - B1 (Step 7.8): plan lines 1534 – 1668 contain six explicit
    `URMInstr` constructor blocks plus past-end; no `sorry`
    placeholder remains. Confirmed.
  - B2 (Steps 3.5 / 3.6 deletion): inner lemma decomposition
    appears at Step 3.5 (plan lines 611 – 675) as a single
    block with two inner lemmas. Numbering of subsequent steps
    updated. Confirmed.
  - B3 (Step 3.11 → now Step 3.9 in the renumbered plan,
    lines 759 – 778): the `Finset.sup_le` discharge uses
    explicit `match i with | ⟨0, _⟩ => exact hpred | ⟨1, _⟩
    => exact hb0 | ⟨2, _⟩ => exact hrecur`. No `fin_cases`
    invocation. Confirmed.
  - S1 (level-closure): plan line 777 uses `Nat.max_le.mpr
    ⟨le_refl 1, hsup⟩`. Lemma-name verification deferred to
    findings.
  - S2 (Step 7.7 bridging): `show` plus `simp only [Fin.last]`
    appears at plan lines 1419 – 1427 and 1496 – 1504. The
    form of the `show` term is itself a defect; see Blocker 1.
  - S3 (Step 5.1 `I_prev` explicit `Fin` index): plan lines
    986 – 987 use `KMor1.proj ⟨a + 1 + P.numRegs, by omega⟩`.
    Confirmed.
  - S5 (Step 8.1 explicit chain): plan lines 1746 – 1748 use
    `simp only [simulate, KMor1.interp_simrec, Fin.cons_zero,
    Fin.cons_succ]` plus `exact (simulate_step_match P v
    y).2 P.outputReg`. Confirmed.
  - S6 (Step 5.6 explicit cases per `URMInstr`): plan lines
    1111 – 1156 enumerate each `URMInstr` constructor. The
    body of several cases is itself defective; see Serious
    findings below.
  - S7 (rename `runFor_succ_back` → `runFor_succ_init_back`):
    confirmed at plan line 1294 (declaration), 1680 (axiom
    audit). The old name does not appear in the plan.
- Verified line numbers cited in the plan and spec against the
  landed code:
  - `URMState.runFor_succ` `@[simp]` at
    [`GebLean/Utilities/ZeroTestURM.lean:192`](../../GebLean/Utilities/ZeroTestURM.lean#L192).
    Confirmed.
  - `URMState.runFor_add` (not `@[simp]`) at
    [`ZeroTestURM.lean:199`](../../GebLean/Utilities/ZeroTestURM.lean#L199).
    Confirmed; signature is
    `(P : URMProgram a) (s : URMState P) (m n : ℕ)`.
  - `URMState.init` body at
    [`ZeroTestURM.lean:254`](../../GebLean/Utilities/ZeroTestURM.lean#L254);
    `regs := fun r => match (List.finRange a).find? (fun i
    => decide (P.inputRegs i = r)) with | some i => v i |
    none => 0`. Matches `baseFamily`. Confirmed.
  - `URMState.step` at
    [`ZeroTestURM.lean:155`](../../GebLean/Utilities/ZeroTestURM.lean#L155);
    five-constructor case split with `Function.update` for
    `assign`/`inc`/`dec`. Confirmed.
  - `KMor1.simrec` constructor at
    [`GebLean/LawvereKSim.lean:50`](../../GebLean/LawvereKSim.lean#L50);
    `i` is explicit; `{a k : ℕ}` are implicit; return type
    `KMor1 (a + 1)`. Confirmed.
  - `KMor1.interp_simrec` `@[simp]` at
    [`GebLean/LawvereKSimInterp.lean:162`](../../GebLean/LawvereKSimInterp.lean#L162);
    `KMor1.simrecVec_succ` `@[simp]` at
    [`LawvereKSimInterp.lean:193`](../../GebLean/LawvereKSimInterp.lean#L193).
    Confirmed.
  - `KMor1.cond : KMor1 3` at
    [`GebLean/Utilities/KArith.lean:222`](../../GebLean/Utilities/KArith.lean#L222);
    `KMor1.interp_cond (ctx : Fin 3 → ℕ) : KMor1.cond.interp
    ctx = if ctx 0 = 0 then ctx 1 else ctx 2` `@[simp]` at
    [`KArith.lean:249`](../../GebLean/Utilities/KArith.lean#L249).
    Confirmed.
- Read the actual context shape produced by `simrecVec_succ`
  ([`LawvereKSimInterp.lean:193 – 209`](../../GebLean/LawvereKSimInterp.lean#L193)):
  it is a `dite`-form
  `fun idx => if idx.val < a + 1 then (if idx.val = 0 then n
  else params ⟨idx.val - 1, _⟩) else simrecVec h g params n
  ⟨idx.val - (a + 1), _⟩`, NOT a `Fin.cons`-form. This shapes
  Blocker 1.
- Cross-referenced project memories
  [`feedback_fin_cases_pulls_classical_choice.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_fin_cases_pulls_classical_choice.md),
  [`feedback_simp_if_pos_sorryAx_leak.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_simp_if_pos_sorryAx_leak.md),
  and
  [`feedback_mathlib_choice_in_functor_cat.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_mathlib_choice_in_functor_cat.md)
  against the plan's `simp only [if_pos h]` invocations and
  `by_cases` usages.
- Re-fetched the four mathlib upstream guides
  (`naming.html`, `style.html`, `doc.html`, `commit.html`) by
  reading
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md)
  § Authoritative upstream guides; checked plan against the
  bullet-point digest.
- Re-read the unapplied round-1 items (S4, all minors, all
  cosmetic-taste) against the current plan to assess whether
  any remain meaningful defects in round 2's context.

## Findings

### Blocker

1. **Step 7.7's `show` term misrepresents the step context's
   arity and content (Step 7.8 inherits the same defect).**
   At plan lines 1419 – 1426 and again at 1496 – 1503 (PC
   branch) and 1556 – 1563 and 1641 – 1648 (register branch),
   the bridging `show` claims the dispatcher's interpretation
   context is `Fin.cons (KMor1.simrecVec (baseFamily P)
   (stepFamily P) v y (Fin.last P.numRegs)) (fun r =>
   KMor1.simrecVec (baseFamily P) (stepFamily P) v y
   r.castSucc)`. This is a `Fin.cons` of arity
   `1 + P.numRegs = P.numRegs + 1`, but the dispatcher's
   actual interpretation context has arity
   `a + 1 + (P.numRegs + 1) = a + P.numRegs + 2` (the
   dispatcher returns `KMor1 (n + 1)` with `n + 1 = a + 1 +
   (P.numRegs + 1)`, by `stepFamily`'s declared type at plan
   line 1078). Beyond the arity mismatch, the actual context
   produced by `KMor1.simrecVec_succ` is a `dite`-form (per
   [`LawvereKSimInterp.lean:193 – 209`](../../GebLean/LawvereKSimInterp.lean#L193)),
   not a `Fin.cons` of two arguments: slot 0 carries the
   recursion variable `y`, slots `1..a` carry the input vector
   `v` (parameters), and only slots `a + 1 .. a + P.numRegs +
   1` carry the previous-component values
   `simrecVec h g v y ⟨idx.val - (a + 1), _⟩`. The Step 7.7 /
   7.8 `show` invocations as written will fail to type-check
   on the first attempt; the implementer cannot follow them
   verbatim. The intended S2 bridging requires the implementer
   to write a `show` term that names the dispatcher's
   interpretation argument as the full `dite`-form context (or
   to rely on `Fin.last`-projection reduction, e.g.
   `simp only [Fin.last]` against the actual `dite`-form),
   not as a `Fin.cons` re-shape of it.

   *Author response — TBD.*

### Serious

1. **Step 1.5's `natK_level` proof rewrites by an unverified
   mathlib lemma name (`Finset.sup_apply_eq_image`).** At
   plan line 235, the proof contains
   `rw [Finset.sup_apply_eq_image]  -- if needed`. The
   accompanying note (lines 239 – 246) explicitly states "if
   `Finset.sup_apply_eq_image` is not the right lemma, use
   `mcp__lean-lsp__lean_local_search` for 'Finset.sup' on a
   `Fin 1 →` family and substitute the correct lemma name."
   The reviewer searched the project's local-search index and
   the lemma does not appear; loogle did not return a match
   either. A plan step that asks the implementer to substitute
   the right lemma name is not an independently executable
   step. The correct discharge for `Finset.univ.sup
   (f : Fin 1 → ℕ) = f ⟨0, _⟩` is most likely
   `Finset.sup_singleton` (after rewriting
   `(Finset.univ : Finset (Fin 1))` to `{⟨0, by decide⟩}`),
   or an `Fin.sum_univ_one`-style identity, neither of which
   is named in the plan. Step 1.6's `natK'_level` (lines
   266 – 274) carries the same defect with
   `Finset.univ_eq_empty_of_isEmpty` and `Finset.sup_empty` —
   the former is not verifiable from project search.

   *Author response — TBD.*

2. **Step 2.6's `predIter_level` body has a dead `cases h`
   block whose outcome is never used.** At plan lines
   480 – 487, the proof finishes with `cases h :
   (KMor1.predIter n k).level with | zero => omega | succ m
   => omega`. The preceding `simp only [KMor1.predIter,
   KMor1.level, Finset.univ.sup]` first invokes
   `Finset.univ.sup`, which is dot notation, not a lemma
   name (the exact issue flagged by round-1's Serious S4 for
   Step 1.5; here it is reintroduced for the level case).
   The `Finset.univ.sup` `simp only` argument cannot fire,
   and even if the goal somehow reduced to a `max` statement,
   `cases h : (KMor1.predIter n k).level` followed by two
   `omega` closes cannot succeed because `ih :
   (KMor1.predIter n k).level ≤ 1` is in scope but is not
   linked to the cased `h`. The note at lines 489 – 493 says
   "if `Finset.univ.sup` does not reduce cleanly, replace
   with `unfold KMor1.level Finset.univ.sup` plus
   `by_cases`/`omega`", which is a debug instruction, not an
   executable plan step.

   *Author response — TBD.*

3. **Step 3.9 / 3.10's `pcDispatchFrom_level` proof shares
   the same `Finset.univ.sup` simp-argument defect.** At
   plan line 744, the recursive case starts with
   `simp only [KMor1.pcDispatchFrom, KMor1.level]`. After
   unfolding `KMor1.pcDispatchFrom` to its `KMor1.comp
   KMor1.cond (fun i : Fin 3 => match i with …)` form and
   `KMor1.level` to `max f.level (Finset.univ.sup
   (fun i => (gs i).level))`, the goal contains a
   `Finset.univ.sup` over a `Fin 3` family that the
   subsequent `Finset.sup_le` step attempts to handle. The
   issue: the `simp only [KMor1.level]` will also unfold the
   inner `(KMor1.pcDispatchFrom (k+1) size' …).level` inside
   the `Fin 3` family (since `KMor1.level` is being unfolded
   transparently), producing an opaque deeply-nested
   `Finset.univ.sup` expression that does not match the
   `hpred` / `hb0` / `hrecur` hypotheses cleanly. The
   reviewer cannot determine whether the final
   `Nat.max_le.mpr ⟨le_refl 1, hsup⟩` close succeeds without
   re-shaping the inner family. The intended structure (use
   the recursive `pcDispatchFrom`'s level as an opaque ≤-1
   bound via `hrecur`) requires the `simp only [KMor1.level]`
   to NOT descend into `hrecur`, which is not how `simp
   only` works on a global definition. A safer formulation
   would `unfold KMor1.pcDispatchFrom` first, then
   `rw [KMor1.level]` (or `show KMor1.level (...) ≤ 1`) to
   pin the outer unfold without recursing.

   *Author response — TBD.*

4. **`runFor_succ_init_back`'s `rw` chain is order-fragile
   (Step 7.1).** At plan line 1300, the proof body is
   `rw [URMState.runFor_add P s y 1, URMState.runFor_succ,
   URMState.runFor_zero]`. After the first rewrite, the goal
   becomes `URMState.runFor P (URMState.runFor P s y) 1 =
   URMState.step P (URMState.runFor P s y)`. The next
   `rw [URMState.runFor_succ]` rewrites `runFor _ (n + 1)`
   patterns. Two occurrences match: `runFor s y` if `y = y' +
   1` (the LHS's outer `runFor`'s inner argument, when `y` is
   a successor) and `runFor (runFor s y) 1`. Lean's `rw`
   picks the first occurrence; without an explicit positional
   selector, the rewrite may rewrite the wrong site for
   generic `y`. The intended close (`rw` at `runFor _ 1` only)
   requires either an `at` clause or `show` rewriting. As
   written, the proof either fails or accidentally relies on
   `y` being a concrete numeral. The fix is to `change` the
   goal to `URMState.runFor P (URMState.runFor P s y) 1 = …`
   explicitly, or invoke `URMState.runFor_succ P
   (URMState.runFor P s y) 0` with explicit arguments.

   *Author response — TBD.*

5. **Step 5.6's `simp [..., KMor1.succ]` and `simp [...,
   KMor1.pred]` invocations are not valid simp arguments.**
   At plan lines 1145 and 1149 (the `inc i` and `dec i`
   sub-cases of `branches_j`), the proof tries
   `simp [h, KMor1.level, v_j_prev, KMor1.succ]; decide` and
   `simp [h, KMor1.level, v_j_prev, KMor1.pred]; decide`.
   `KMor1.succ` and `KMor1.pred` are constructors / definitions,
   not simp lemmas; `simp` with a definition unfolds it (when
   it has a `@[simp]`-marked equation lemma) or fails. The
   relevant level facts are `KMor1.succ.level = 0` (rfl) and
   `KMor1.pred.level = 1` (by inspection). The implementer
   would need to substitute `show KMor1.succ.level = 0 from
   rfl` or `KMor1.pred.level = 1` (the latter would itself
   require a `decide` or unfolding). The note at line 1158 —
   "Inspect each goal state via `mcp__lean-lsp__lean_goal` if
   `decide` or `omega` does not close" — concedes the
   discharge is not pinned down. The same issue affects
   `branches_pc`'s `jumpZ` case at line 1128
   (`simp [KMor1.level, v_j_prev, KMor1.natK'_level]; decide`):
   `KMor1.natK'_level` is the level lemma, fine as a simp arg,
   but the broader simp may not pin a deterministic close.

   *Author response — TBD.*

6. **Step 7.4's `URMState.init` reduction relies on `simp only
   [URMState.init, h]` (lines 1363, 1365), which surfaces the
   pattern flagged by project memory `feedback_urmstate_init_let_reduction.md`.**
   `URMState.init` returns a structure with `let`-style record
   syntax; `simp only [URMState.init]` will not reduce the
   `regs` field through to the inner `match (List.finRange a).find?`
   on its own. The plan additionally `simp only [..., h]`
   where `h : (List.finRange a).find? (fun i => decide
   (P.inputRegs i = j)) = some i`. The combined `simp only
   [URMState.init, h]` may not reach the goal `(URMState.init
   P v).regs j = v i` without an intermediate `unfold
   URMState.init` plus an `rfl`-style projection (the project
   memory shows the equivalent reduction-blocked issue in T2's
   bsum phase_i2). A more reliable form is
   `show (URMState.init P v).regs j = v i; unfold URMState.init;
   simp only [h]; rfl`.

   *Author response — TBD.*

7. **The plan has no module-level concurrency or atomicity
   discipline for the per-step `lake build` between Steps 7.6
   – 7.8.** At plan lines 1375 – 1395 (Step 7.6) the body
   replaces the `sorry` with a structure that contains TWO
   `sorry` placeholders (one per branch of the conjunction).
   Step 7.5's expected output is "build with one `sorry`
   warning", but after Step 7.6's edit, the build will have
   two `sorry` warnings. The plan does not insert an
   intermediate build step between 7.6 and 7.7 to verify the
   structural skeleton; the implementer must rely on the
   final 7.9 build to discover any issue. This violates the
   plan's own workflow rule (lines 65 – 73, "Axiom audit per
   declaration. After each task's final build is clean…") in
   spirit; more directly, it violates the writing-plans skill's
   "each step is independently executable, includes verifiable
   expected output". Step 7.6's "Expected" output is not
   stated (the step itself merely says "Replace the `| succ y
   ih => sorry` line"). Add an intermediate build step (or
   merge 7.6 into 7.5).

   *Author response — TBD.*

### Minor

1. **The plan's commit-message bodies in Tasks 5, 7, 8, 9 mix
   imperative-present and noun-phrase fragments.** For
   example, Step 5.9 (line 1183) opens "introduce stepFamily
   …" (good imperative present) but later inserts
   "include `stepFamily_level` showing every component is at
   level ≤ 1" (good), then closes with
   "[propext, Quot.sound]-only axiom hygiene confirmed."
   ("confirmed" is past participle, against the `commit.html`
   imperative-present rule that round-1 Minor M1 flagged the
   author as fixing throughout). The same pattern recurs at
   Step 7.11 line 1709, Step 8.6 line 1812, Step 9.6 line
   1914. The round-1 M1 author response claimed all commit
   message bodies were rewritten in imperative present;
   "confirmed" was specifically called out as a fix target,
   but it persists.

   *Author response — TBD.*

2. **Step 2.1's `open GebLean.ZeroTestURM` appears inside
   both `namespace GebLean` (line 402) and `namespace
   GebLean.KSimURMSimulator` (line 408).** The first `open`
   has no consumers in the empty `GebLean` block; the second
   is the one that matters. The duplicate `open` adds nothing
   and breaks the per-file style of opening once. (Minor
   because it does not impede compilation; flagged only because
   `lean-coding.md` § Coding style emphasises "do not mix
   `namespace X` blocks with content outside them in the same
   file".)

   *Author response — TBD.*

3. **Step 4.3's `baseFamily_level` body uses an unverified
   mathlib lemma name (`Fin.lastCases_eq_last_or_castSucc`).**
   At plan line 910 the proof opens with `rcases
   Fin.lastCases_eq_last_or_castSucc j with hL | ⟨r, hR⟩`.
   The accompanying note (lines 922 – 927) acknowledges the
   name "may be a different name in current mathlib" and
   suggests fallbacks. Round-1 Minor M5 flagged the same name
   in this step and Step 5.6; the author response stated
   "Steps 4.3 and 5.6 rewritten to use `induction j using
   Fin.lastCases with | last => … | cast r => …`". Step 5.6
   was rewritten as promised; Step 4.3 was not. The
   `Fin.lastCases_eq_last_or_castSucc` rcases form remains
   at plan line 910. (Minor because Step 4.3 is for a level
   lemma whose body can be rewritten to follow Step 5.6's
   `induction … using Fin.lastCases` pattern; the structural
   case-split exists, only the discharge form needs swapping.)

   *Author response — TBD.*

4. **The plan's "Note:" paragraphs frequently invite the
   implementer to "use `mcp__lean-lsp__lean_local_search` /
   `lean_goal` and substitute the correct lemma name / adjust
   the discharge".** Examples: Step 1.5 note (lines 239 – 246),
   Step 1.6 note (lines 276 – 281), Step 2.6 note (lines
   489 – 493), Step 4.3 note (lines 922 – 927), Step 5.6 note
   (lines 1158 – 1163), Step 7.7 closing paragraph (lines
   1523 – 1532), Step 7.8 closing paragraph (lines 1664 – 1668).
   Each one is a deferred decision that pushes name-resolution
   or discharge-shape work into execution time. The
   accumulation degrades the plan's "each step independently
   executable" property: the implementer cannot follow the
   plan verbatim and must repeatedly stop to determine the
   right form. (Individually minor; collectively a code-smell
   the author should weigh before handing to user review.)

   *Author response — TBD.*

5. **The plan's Step 8.3 `simulate_level` proof contains an
   irrelevant simp-arg.** At plan line 1770 the proof body
   uses `simp only [KMor1.level]`. Since `simulate` is a
   `def` whose body is a single `KMor1.simrec`, `unfold
   simulate` (already invoked at line 1769) followed by
   `KMor1.level`'s `.simrec` clause is the relevant reduction.
   The subsequent `apply Nat.add_le_add_right` requires the
   goal to be `… + 1 ≤ 2`, which `simp only [KMor1.level]`
   should produce as `max sup_h sup_g + 1 ≤ 2`. But `simp
   only [KMor1.level]` may recursively unfold `KMor1.level`
   inside `sup_h` and `sup_g`, producing a goal more verbose
   than needed. A cleaner approach uses `show (max sup_h
   sup_g) + 1 ≤ 2`, or `rw` with the `.simrec` clause's
   definitional equation explicitly. (Minor because the
   `apply Nat.add_le_add_right` then `apply max_le` chain
   should still close if `simp only` reaches the right shape.)

   *Author response — TBD.*

6. **Step 9.7's verification command list runs `markdownlint-cli2
   'docs/**/*.md'` against the entire docs tree** (plan line
   1927). The repository contains historical / archived `.md`
   files (under `docs/research/`, `docs/superpowers/specs/`,
   `docs/superpowers/plans/` for past workstreams) that may
   not all be markdownlint-clean. The Step 9.4 invocation
   (lines 1885 – 1890) scopes lint to the four T3 artefacts,
   which is the appropriate scope. Step 9.7's wildcard scope
   risks reporting lint failures unrelated to T3 and stalling
   the closing checklist.

   *Author response — TBD.*

7. **Round-1 Minor M2's expected-output correction at Step
   1.1 (`KMor1.cond` example ends at line 264) was applied
   (plan line 174), but the surrounding prose still hints at
   an inserted "approximately line 270" target** (plan line
   157 ("around line 270; before `KMor1.notEq1` at line
   278")). The "around line 270" hint conflicts with the
   corrected expected-output that insertion is between lines
   264 and 266. (Minor; the implementer can reconcile, but
   the discrepancy is misleading.)

   *Author response — TBD.*

### Cosmetic-taste

1. **The plan's `## Workflow notes` section uses bolded
   inline labels** (for example "Build with `lake build`."
   and "One declaration at a time." at plan lines 56 – 91,
   each wrapped in `**…**`). The project rule
   ([`.claude/rules/markdown-writing.md`](../../.claude/rules/markdown-writing.md)
   § Prose style) discourages markup for emphasis, reserving
   it for delineation. The writing-plans skill template uses
   bolded section labels (the round-1 author response to C2
   defended the practice as skill-template). The same defence
   covers these labels; flagged for the author's confirmation
   that this is the intended scope of the C2 exception.

   *Author response — TBD.*

2. **The plan repeats the same `bash scripts/check-axioms.sh
   <Fully.Qualified.Name>` block (Steps 1.8, 2.8, 3.12, 4.5,
   5.8, 6.3, 7.10, 8.5, 9.3).** Step 9.3 (plan lines
   1855 – 1879) repeats all 19 audit commands from scratch.
   This is consistent with the plan's "axiom audit per
   declaration" rule but inflates plan LOC; a reference
   ("re-run all per-task audit commands from Steps 1.8 …
   8.5") would communicate the same. (Cosmetic-taste: the
   redundancy is intentional per the plan's
   per-declaration discipline.)

   *Author response — TBD.*

3. **The plan's Step 0.3 expected-output prose says "the most
   recent matching commit's description includes the phrase
   'implementation plan' and references T3"** (line 140). The
   `glob:"docs(ertok)*plan*"` filter is broad; multiple T3
   plan-iteration commits may match, and "most recent" is
   ambiguous when the plan-author's `jj` log lists multiple
   description-modifying commits. A `--limit 1` or `description
   like '%T3%'` clause would tighten the check. (Cosmetic-taste;
   the implementer can read the listing.)

   *Author response — TBD.*

4. **The plan's per-task commit-message bodies repeat
   spec-section references in a fixed format** ("per spec §
   X.Y"). This is consistent and helpful for traceability;
   the cosmetic note is that the format could be standardised
   into a footer ("Spec: § 3.6") rather than inline prose.
   (Cosmetic-taste; the inline form reads naturally.)

   *Author response — TBD.*
