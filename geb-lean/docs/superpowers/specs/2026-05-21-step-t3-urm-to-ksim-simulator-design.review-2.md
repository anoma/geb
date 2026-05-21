# Round-2 adversarial review — T3 URM to Ksim simulator

Reviewer: fresh-context `general-purpose` Agent (round 2).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](2026-05-21-step-t3-urm-to-ksim-simulator-design.md).

## Verification log

- § 2 / § 11.2 line-number citations re-verified against current
  `GebLean/Utilities/ZeroTestURM.lean`: `URMInstr` at `:89`,
  `URMProgram` at `:122`, `URMState` at `:143`, `URMState.step`
  at `:155`, `URMState.runFor` at `:179`, `URMState.runFor_zero`
  at `:186`, `URMState.runFor_succ` at `:192`,
  `URMState.runFor_halted_invariant` at `:213`, `URMState.init`
  at `:254` — pass.
- `GebLean/LawvereKSim.lean:34` (`KMor1`), `:50`
  (`KMor1.simrec`), `:105` (`KMor1.level`) — pass.
- `GebLean/LawvereKSimInterp.lean:162` (`KMor1.interp_simrec`),
  `:180` (`KMor1.simrecVec_zero`), `:193`
  (`KMor1.simrecVec_succ`) — pass.
- `GebLean/Utilities/KArith.lean:44` (`KMor1.pred`), `:222`
  (`KMor1.cond`), `:249` (`KMor1.interp_cond`), `:31`
  (`KMor1.one`) — pass.
- Tourlakis § 0.1.0.2 p. 1, § 0.1.0.17(4) p. 6, § 0.1.0.17(6)
  p. 6, § 0.1.0.37 pp. 15–16 — pass on PDF inspection.
- Tourlakis § 0.1.0.20 p. 7 — partial pass. The PDF states the
  predicates `λx.x ≤ a` etc. are in `K_{1,*}` (not
  `K^sim_{1,*}`). The `K^sim_{1,*}` containment follows from
  Proposition 0.1.0.8 (`K_n ⊆ K^sim_n`); the spec's notation is
  reachable but is a one-step inference, not the literal
  statement of § 0.1.0.20.
- `pcDispatch_level` recursive argument traced: shift's
  `Fin.last` image is `KMor1.comp pred [proj (Fin.last n)]` at
  level 1; all other shift components are `proj` at level 0;
  `comp recur shift` at level `max (IH-recur) 1 = 1`; outermost
  `cond` composed with three level-≤-1 children at level 1.
  Recursive case preserves level ≤ 1. Base case
  `comp default [proj …]` has level `default.level`. Overall
  `pcDispatch_level` claim holds.
- `KMor1.simrec`-level computation traced: the `KMor1.level`
  clause for `.simrec` is `max (sup_h) (sup_g) + 1`. With
  `sup_h = 0` and `sup_g ≤ 1`, simrec level ≤ 2. Confirms
  `simulate_level ≤ 2`.
- `URMState.runFor_succ` at `ZeroTestURM.lean:192` is the
  *front-peel* form (`runFor s (n+1) = runFor (step s) n`).
  The spec § 4.3 step case asserts
  `runFor (y + 1) = step (runFor y)` (back-peel). The two
  forms are equal via `URMState.runFor_add` (at `:199`), but
  the spec cites only `runFor_succ`.
- `GebLean.lean` currently uses plain `import …`, not
  `public import …`, for every leaf-module entry. The spec
  § 6.3 prescribes `public import GebLean.Utilities.\
  KSimURMSimulator`, diverging from the existing pattern.
- Master design § 6.1 (`URMSubroutinesER.lean`) does not
  contain the Tourlakis simulation lemma's `v_i` / `I`
  recursion equations; those equations reside in Tourlakis
  § 0.1.0.37 pp. 15–16 and are paraphrased in master § 7.

## Findings

### Blocker

1. **`pcDispatch`'s `default_pc := I_prev` is unrealisable
   under the stated signature (§ 3.4, § 3.5).** The signature
   in § 3.5 fixes `default : KMor1 n`, and the simp lemma
   `interp_pcDispatch_default` returns
   `default.interp (Fin.init ctx)`. `Fin.init` strips the last
   slot of `ctx`, which is the PC slot. § 3.4 then asserts
   `default_pc := I_prev` (a projection at the PC slot), but
   `I_prev` is the projection at the slot stripped by
   `Fin.init`. The `default` term, of arity `n = a + 1 +
   numRegs`, cannot read a slot outside its context. The URM
   identity required by past-end is `step s = s`
   (`ZeroTestURM.lean:155`, `else s` branch), so for any
   past-end state the K^sim PC output must equal the previous
   PC. The previous PC is carried only in the stripped slot,
   so no `KMor1 n` `default` can reproduce it. An implementer
   following § 3.4 verbatim would have no constructive way to
   satisfy the stated `simulate_interp` for past-end traces.

   *Author response — fix.* `pcDispatch` redesigned so both
   branches and default share arity `n + 1` (full context
   access including the PC slot). The simp lemmas drop
   `Fin.init`: `interp_pcDispatch_match` now returns
   `(branches k).interp ctx`, and `interp_pcDispatch_default`
   returns `default.interp ctx`. With this signature,
   `default_pc := I_prev` and `default_j := v_j_prev` are
   both projections at slots of the full step context
   (arity `a + 1 + (numRegs + 1)` = `n + 1` with
   `n = a + numRegs + 1`), realising the past-end identity
   directly. The recursive case's branch lift falls away
   (Serious S1 below subsumes into the same fix). Edits
   applied in §§ 3.4 (remove the trailing note paragraph; the
   branches and default now live at the full step-context
   arity), 3.5 (new signature, new simp lemmas, new
   `pcDispatch_level` hypothesis, revised recursion
   description and level analysis), 4.3 (proof outline
   tightened to invoke the new simp lemmas).

2. **§ 4.3's step-case identity does not match the cited
   `URMState.runFor_succ`.** `URMState.runFor_succ` at
   `ZeroTestURM.lean:192` is the front-peel form
   `runFor P s (n + 1) = runFor P (step P s) n`. The proof
   outline at § 4.3 asserts the back-peel form
   `runFor (y + 1) = step (runFor y)`. They are equal via
   `URMState.runFor_add` (at `:199`), but they are not the
   same lemma. An induction on `y` with `s := init P v` held
   fixed cannot use the front-peel form `runFor_succ`
   directly. The spec presents the step as a one-line
   application of `runFor_succ`, which an implementer
   following verbatim would find inapplicable.

   *Author response — fix.* § 4.3 step case rewritten to
   derive the back-peel form: `runFor s 1 = step s` by
   `runFor_succ` with `n = 0`; then
   `runFor s (y + 1) = runFor s (y + 1) = runFor (runFor s y)
   1 = step (runFor s y)` by `runFor_add` at `:199`. Cite
   both lemmas. The spec also notes the back-peel form as
   the consumed equality so an implementer expecting a
   one-line `rw [runFor_succ]` is redirected to the proper
   composition.

### Serious

1. **`pcDispatch`'s recursive case has an inadequately
   specified branch lift (§ 3.5).**

   *Author response — fix (subsumed by Blocker B1).* The B1
   fix makes branches and default both at arity `n + 1`, so
   no per-branch lift is needed in the recursive case;
   `cond(PC, branches ⟨0, _⟩, recur)` composes three
   `KMor1 (n + 1)`-typed inputs directly.

2. **§ 4.3's "closed by `rfl` after simp chains" for the base
   case overpromises.** The proof needs an explicit case-split
   on the `Option (Fin a)` result of `List.find?`.

   *Author response — fix.* § 4.3 base case rewritten to call
   out the case-split: "case-split on the `Option (Fin a)`
   result of `(List.finRange a).find? (fun i => decide
   (P.inputRegs i = r))`; in the `some i` branch, both sides
   reduce by `interp_proj` plus the `URMState.init` register
   definition to `v i`; in the `none` branch, both reduce to
   `0`."

3. **Tourlakis § 0.1.0.20 citation overstates the literal
   class.** PDF p. 7's Corollary 0.1.0.20 says `K_{1,*}`, not
   `K^sim_{1,*}`. The containment follows from Proposition
   0.1.0.8 (`K_n ⊆ K^sim_n`).

   *Author response — fix.* § 11.1's § 0.1.0.20 entry
   corrected: cite the literal `K_{1,*}` and chain via
   § 0.1.0.8 (`K_n ⊆ K^sim_n`, p. 3) to reach
   `K^sim_{1,*}`. The bottom-up dispatch chain's level-1
   inference still holds (every level-1 component in `K_1`
   or `K^sim_1`).

4. **§ 10.15 punch-list item misroutes the obligation.**
   "Tabulate § 6.1 of the master spec" — master § 6.1
   (`URMSubroutinesER.lean`) does not contain Tourlakis's
   `v_i` / `I` recursion equations. Those equations are in
   Tourlakis § 0.1.0.37 pp. 15–16 and are paraphrased in
   master § 7.

   *Author response — fix.* Item 10.15 rerouted to "Tabulate
   master design § 7 (and Tourlakis § 0.1.0.37 pp. 15–16,
   the literal source) against `stepFamily` of this spec;
   flag any mismatch."

5. **§ 6.3 prescribes `public import` against the existing
   repository pattern.** `GebLean.lean` uses plain
   `import …` for all leaf modules; the cited files do not
   declare `module` at top.

   *Author response — fix.* § 6.3 changed to plain
   `import GebLean.Utilities.KSimURMSimulator`, matching the
   existing `GebLean.lean` pattern. The Lean-4 module-system
   convention in `.claude/rules/lean-coding.md` is
   forward-going; T3 does not introduce the `module` keyword.

### Minor

1. **§ 1's scope bullets cite file-level locations only for
   the simulator's three outputs, not for the helpers.**

   *Author response — defer-with-rationale.* § 1 is the
   scope summary; § 6.1's file-placement table is the
   authoritative location reference. Cross-references back
   into § 6.1 would clutter § 1.

2. **§ 3.2's "component `j` ↔ register `j`" is loosely
   worded.** Conflates component-index `j.castSucc` with
   register-index `j`.

   *Author response — fix.* § 3.2 clarified: "component
   `j.castSucc` (for `j : Fin P.numRegs`) holds register
   `j`'s value".

3. **§ 3.4's slot table uses `Fin.last (a + numRegs + 1)`
   without naming the arity.**

   *Author response — fix.* § 3.4 slot table revised: the PC
   row now notes the step-context arity explicitly
   (`a + numRegs + 2`) and `Fin.last (a + numRegs + 1)
   : Fin (a + numRegs + 2)`.

4. **§ 8 "Out of scope" repeats `boundExprK` and `maxK /
   maxOver / pow2_iter` deferral in two bullets.**

   *Author response — defer-with-rationale.* The two
   bullets are kept separate because they cite different
   master-design sections (§ 9 vs. § 3.1 of the T1/T2 spec)
   and the K^sim composites carry their own deferral note
   about T4 being their consumer. Merging loses the
   citation distinction.

5. **§ 9 LOC estimate for T3-Task-5 at ≈ 100 LOC is
   optimistic.**

   *Author response — fix.* T3-Task-5's estimate revised to
   "approximately 150–250 LOC, with case-by-case
   instruction discharge plus per-instruction
   `Function.update` propagation". Total T3 estimate
   adjusted to approximately 400–500 LOC.

### Cosmetic-taste

1. **"Most important obligation:" in § 10 intro uses
   value-laden "important".**

   *Author response — fix.* Rephrased to "Primary
   obligation:".

2. **§ 4.1 phrase "Total over `URMProgram a`; no
   `WellBounded` precondition." reads as framing.**

   *Author response — fix.* Rephrased to "Holds for every
   `URMProgram a`; no `WellBounded` precondition is
   required."

3. **§ 11.1's first bullet inserts a discursive aside on
   `KMor1.one`.**

   *Author response — reject-as-cosmetic-taste.* The aside
   was inserted in round 1 specifically to tighten the
   Tourlakis cite (the project-internal `KMor1.one`
   precedent is what actually grounds the `succ ∘ zero`
   pattern; Tourlakis § 0.1.0.2 alone does not). Moving it
   to § 11.2 loses the binding between the Tourlakis
   citation and the project-internal pattern.

4. **Doctoc anchor for "5 Level analysis" uses
   `#5-level-analysis`.**

   *Author response — defer-with-rationale.* doctoc
   auto-generates TOC anchors from heading text; the anchor
   shape is determined by the heading. Section 5 has no
   subsection structure (no § 5.1 / § 5.2), so no
   subsection-numbered alternative would apply.
