# Round-4 adversarial review — T3 URM to Ksim simulator

**Convergence record.** This round reports zero blocker and zero
serious findings; per `docs/process.md` § Convergence criterion,
the adversarial-review loop terminates here. Minor and
cosmetic-taste findings remain open per author-response policy.

Reviewer: fresh-context `general-purpose` Agent (round 4).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](2026-05-21-step-t3-urm-to-ksim-simulator-design.md).

## Verification log

- `docs/process.md` § Adversarial review (lines 131–227) read;
  reviewer protocol followed; no mutating operations performed.
- `GebLean/Utilities/ZeroTestURM.lean:89` is `inductive URMInstr`
  with five cases (`assign`, `inc`, `dec`, `jumpZ`, `stop`);
  matches spec § 2 table. Pass.
- `GebLean/Utilities/ZeroTestURM.lean:122` is the arity-indexed
  `structure URMProgram (numInputs : ℕ)`. Pass.
- `GebLean/Utilities/ZeroTestURM.lean:143` is `structure URMState
  {a : ℕ} (P : URMProgram a)`. Pass.
- `GebLean/Utilities/ZeroTestURM.lean:155` is `def URMState.step`
  with the `else s` past-end branch confirmed at `:172`. Pass.
- `GebLean/Utilities/ZeroTestURM.lean:179` is `def
  URMState.runFor`; `runFor_succ` at `:192`, `runFor_add` at
  `:199`. Pass.
- `GebLean/Utilities/ZeroTestURM.lean:213` is
  `URMState.runFor_halted_invariant`. Pass.
- `GebLean/Utilities/ZeroTestURM.lean:254` is `def
  URMState.init`; the `List.find?` predicate is
  `decide (P.inputRegs i = r)`, matching spec § 3.3. Pass.
- `GebLean/LawvereKSim.lean:34` is `inductive KMor1`. Pass.
- `GebLean/LawvereKSim.lean:50` is the `simrec` constructor,
  returning `KMor1 (a + 1)`. Pass.
- `GebLean/LawvereKSim.lean:105` is `def KMor1.level`; the
  `comp` clause takes `max`, the `simrec` clause adds 1. Pass.
- `GebLean/LawvereKSimInterp.lean:86` is `@[simp]
  KMor1.interp_zero`. Pass.
- `GebLean/LawvereKSimInterp.lean:98` is `@[simp]
  KMor1.interp_proj`. Pass.
- `GebLean/LawvereKSimInterp.lean:162` is `@[simp]
  KMor1.interp_simrec`. Pass.
- `GebLean/LawvereKSimInterp.lean:180` is `@[simp]
  KMor1.simrecVec_zero`. Pass.
- `GebLean/LawvereKSimInterp.lean:193` is `@[simp]
  KMor1.simrecVec_succ`. Pass.
- `GebLean/Utilities/KArith.lean:44` is `def KMor1.pred`. Pass.
- `GebLean/Utilities/KArith.lean:222` is `def KMor1.cond :
  KMor1 3`. Pass.
- `GebLean/Utilities/KArith.lean:249` is `@[simp]
  KMor1.interp_cond` with semantics `if ctx 0 = 0 then ctx 1
  else ctx 2`. Pass.
- Tourlakis § 0.1.0.2 p. 1, § 0.1.0.8 p. 3, § 0.1.0.17(4) p. 6,
  § 0.1.0.17(6) p. 6, § 0.1.0.20 p. 7, § 0.1.0.37 pp. 15–16:
  all verified against PDF. Pass.
- Dispatcher arity claim: step-context arity `a + 1 +
  (numRegs + 1) = a + numRegs + 2`, with `n := a + numRegs +
  1` giving `n + 1 = a + numRegs + 2` and `Fin.last n` reading
  the PC slot at index `a + 1 + numRegs`. Pass.
- `predIter` level: `predIter 0 = proj (Fin.last n)` at level
  0; `predIter (k + 1) = comp pred [predIter k]` at level 1
  for `k ≥ 0`. Pass.
- `pcDispatch` level induction: with branches and default at
  level ≤ 1, base case at level ≤ 1; recursive case
  `comp cond [predIter k, branches[0], recur]` at level
  `max 1 (max 1 1 1) = 1`. End-to-end ≤ 1. Pass.
- `simulate` level: base sup 0, step sup ≤ 1, simrec adds 1 →
  ≤ 2. Pass.
- Bottom-up fall-through traced for `size = 3, PC = 1`: outer
  `cond` test `predIter 0 = 1 ≠ 0`, falls through; inner test
  `predIter 1 = pred(1) = 0`, selects
  `(branches ∘ Fin.succ) ⟨0, _⟩ = branches ⟨1, _⟩`. Pass.
- Past-end propagation: for `PC ≥ size`, every test
  `predIter k = pred^k(PC) ≥ 1 > 0` for `k < size`, all cond
  tests fall through, reaching `default`. Pass.
- § 4.3 back-peel derivation `runFor s (y + 1) =
  step (runFor s y)`: derived as `runFor s (y + 1) =
  runFor (runFor s y) 1` (by `runFor_add`), then
  `= step (runFor s y)` (by `runFor_succ` at `n = 0` plus
  `runFor_zero`). Sound. Pass.
- § 4.3 base-case Option case-split: in the `some i` branch,
  both sides reduce to `v i`; in the `none` branch, both to
  0. Case-split closes. Pass.
- § 4.2 conjunctive IH necessity: traced. PC step family reads
  `v_i_prev` (cross-register read) in the `.jumpZ` branch;
  register-`j` step family reads only `I_prev` and
  `v_j_prev`. The cross-register read forces the joint IH.
  Pass.
- `simulate_step_match` register-component projection at
  `j := P.outputReg`: output index `P.outputReg.castSucc`
  matches simrec's `i` parameter; `interp_simrec` reduces
  `(simulate P).interp (Fin.cons y v)` to the conjunctive
  IH's register clause at `j := P.outputReg`. Pass.
- Markdownlint clean: `markdownlint-cli2` v0.22.1 reports 0
  errors on the spec with the project config. Pass.
- Mathlib `naming.html`, `style.html`, `doc.html` re-fetched on
  this round (the lean-coding rule pins re-fetch per round).
  Spec § 6.4 (naming) and § 6.3 (file outline) match the
  upstream conventions. Pass.
- Independence claim (item 10.9): § 6.2 lists imports
  `Utilities/ZeroTestURM`, `LawvereKSim`, `LawvereKSimInterp`,
  `Utilities/KArith` — no ER, ERKSim, KSimER, KSimMajorization,
  or CSLib imports. Pass.
- Scope (item 10.11): § 8 defers `boundExprK`, `maxK`,
  `maxOver`, `pow2_iter`, `erToK`, `erToKN`, `erToKFunctor`,
  strict iso; § 6.3 file outlines do not include these. Pass.

## Findings

### Blocker

None.

### Serious

None.

### Minor

1. **`pcDispatchFrom` visibility not stated.** § 3.5 introduces
   `pcDispatchFrom k size branches default` as an auxiliary,
   but neither § 3.5 nor § 6.3's file outline says whether it
   should be `private`. The existing `KArith.lean` precedent
   (`KMor1.cond_aux : private`) suggests `private`.

   *Author response — fix.* § 3.5 and § 6.3 amended to mark
   `pcDispatchFrom` as `private`. Only `pcDispatch` and its
   three lemmas (`interp_pcDispatch_match`,
   `interp_pcDispatch_default`, `pcDispatch_level`) are
   public.

2. **`predIter` declaration site not stated.** § 3.5 uses
   `predIter k`, but does not say whether it is a standalone
   `private def KMor1.predIter` with its own `@[simp]` interp
   lemma or an inline term inside `pcDispatch`'s body.

   *Author response — fix.* § 3.5 amended: `predIter k`
   declared as a standalone `private def`
   `GebLean.KMor1.predIter (n k : ℕ) : KMor1 (n + 1)` with
   `@[simp] theorem KMor1.interp_predIter
   (k : ℕ) (ctx : Fin (n + 1) → ℕ) :
   (KMor1.predIter n k).interp ctx = (ctx (Fin.last n)) ∸ k`
   (using `Nat.sub` after `k` applications of `Nat.pred`),
   and `theorem KMor1.predIter_level
   : (KMor1.predIter n k).level ≤ 1`. § 6.3 file outline
   updated.

3. **Joint-induction structure for `interp_pcDispatch_match` /
   `_default` not surfaced.** § 3.5 mentions "by induction on
   `size`, simultaneously over `pcDispatch` and
   `pcDispatchFrom k`" but does not state that `k` must be
   generalised (universally quantified) in the inductive
   hypothesis on `pcDispatchFrom`.

   *Author response — fix.* § 3.5's "Level analysis" prose
   amended to state: "Both `pcDispatch_level` and the simp
   lemmas' proofs proceed by induction on `size`, with `k`
   universally quantified in the inductive hypothesis on
   `pcDispatchFrom`. The recursive call's `branches ∘
   Fin.succ` is consumed by the IH's branch-family
   parameter, which the universal quantification accommodates."

4. **Tourlakis "otherwise = I + 1" vs spec `default_pc :=
   I_prev` divergence not explicitly flagged.** Tourlakis §
   0.1.0.37 p. 16's I-recursion has "otherwise" branch
   `I(y) + 1`. The spec follows the landed `URMState.step`'s
   `else s` (self-loop), which matches Tourlakis's prose
   immediately preceding § 0.1.0.37 but contradicts his own
   equation's "otherwise".

   *Author response — fix.* § 11.1's § 0.1.0.37 citation
   amended with a footnote: "Tourlakis's I-recursion (p. 16)
   has 'otherwise = I + 1'; this spec follows the prose
   immediately preceding § 0.1.0.37 ('computation continues
   forever trivially, without changing either the V_i or the
   instruction number') and the landed `URMState.step`'s
   past-end `else s` self-loop, which matches the prose."

5. **`Task 2`'s 80 LOC estimate is tight.** § 9 Task 2
   allocates ≈ 80 LOC for `pcDispatch` plus its three lemmas
   plus `pcDispatchFrom`, `predIter`, and the auxiliary
   `interp_predIter` simp lemma. The conditional-simp
   semantics and the `Fin.succ` arithmetic inside the
   inductive proofs push this closer to 120 – 150 LOC.

   *Author response — fix.* § 9 Task 2 estimate revised to
   "approximately 120 – 150 LOC" to account for `predIter`
   and the joint induction over `pcDispatchFrom`.

6. **TOC line-length.** A few TOC entries (e.g., § 3.5,
   § 4.4) produce 80+-char lines in the doctoc-managed block.
   markdownlint does not flag (doctoc-generated content is
   treated laxly), but next regeneration may shift.

   *Author response — defer-with-rationale.* doctoc owns the
   TOC anchor format; markdownlint passes; manual shortening
   of headings to fit a TOC width budget would distort the
   section descriptions. Defer.

7. **Termination of `pcDispatch` / `pcDispatchFrom` recursion
   not justified.** Lean's structural recursion on `size : ℕ`
   accepts both definitions, but the spec does not state this.

   *Author response — defer-with-rationale.* Standard
   structural recursion on a `Nat` parameter; Lean's
   elaborator handles it automatically and the implementer
   will see immediately if it fails (it will not). No spec
   change needed.

### Cosmetic-taste

1. **Tourlakis `∸` symbol vs Lean `Nat.sub`.** § 11.1's
   `λx.x ∸ 1` citation does not state that Tourlakis's `∸` is
   truncated decrement matching Lean's `Nat.sub`.

   *Author response — fix.* § 11.1 amended: the § 0.1.0.17(4)
   bullet now ends with "(Tourlakis's `∸` is truncated
   decrement, matching Lean's `Nat.sub` clamped at zero;
   `KMor1.pred` realises `λx.x ∸ 1` as defined.)".

2. **`KMor1.level` simrec formula not named in § 5.** The
   breakdown derives `max 0 1 + 1 = 2` without quoting the
   formula from `LawvereKSim.lean:111`.

   *Author response — fix.* § 5's breakdown bullet for
   `simrec` amended: "The `KMor1.level`'s `.simrec` clause
   (`LawvereKSim.lean:111`) is
   `max (Finset.univ.sup (·.level over h))
   (Finset.univ.sup (·.level over g)) + 1`. With `sup_h = 0`
   and `sup_g ≤ 1`, this yields `max 0 1 + 1 = 2`."

3. **§ 6.3 / § 6.4 redundancy.** Both sections cover
   namespace placement.

   *Author response — reject-as-cosmetic-taste.* § 6.3 is the
   file-content outline; § 6.4 is the naming-convention
   summary. Their overlap in namespace text is intentional —
   the convention statement lives in § 6.4, and § 6.3's
   outline cites § 6.4. Collapsing them would force one
   subsection to carry two different framings (file content
   vs. naming convention), losing the structural separation.

4. **§ 11.1's § 0.1.0.20 entry uses two phrasings.**

   *Author response — fix.* § 11.1 amended: the entry now
   reads "Tourlakis § 0.1.0.20 p. 7 — `λx.x ≤ a, λx.x < a,
   λx.x = a ∈ K_{1,*}` (the predicate sub-class of `K_1`).
   Chained with § 0.1.0.8 (`K_n ⊆ K^sim_n`, p. 3) for the
   `K^sim_{1,*}` containment." (single phrasing).

5. **Previous-PC symbol inconsistency.** The spec uses both
   `I_prev`, `PC`, and `I` in different sections.

   *Author response — fix.* § 3.5's recursive-case prose and
   § 3.5's Tourlakis-citation prose tightened: `PC` is the
   level-0 projection `KMor1.proj (Fin.last n)` (the
   K^sim term); `I_prev` is its concrete role inside
   `stepFamily` as the previous PC value. The spec uses
   `PC` inside `pcDispatch` descriptions and `I_prev`
   inside `stepFamily` descriptions; Tourlakis's `I` appears
   only inside § 11.1 citations.
