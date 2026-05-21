# Round-3 adversarial review — T3 URM to Ksim simulator

Reviewer: fresh-context `general-purpose` Agent (round 3).
Artefact under review:
[`2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](2026-05-21-step-t3-urm-to-ksim-simulator-design.md).

## Verification log

- Reviewer protocol re-read: `docs/process.md` §§ Adversarial
  review, Reviewer protocol, Defect categorisation. Pass.
- `GebLean/Utilities/ZeroTestURM.lean` cited line numbers
  (`:89` `URMInstr`, `:122` `URMProgram`, `:143` `URMState`,
  `:155` `step`, `:179` `runFor`, `:186` `runFor_zero`,
  `:192` `runFor_succ` (front-peel), `:199` `runFor_add`,
  `:213` `runFor_halted_invariant`, `:254` `init`) — all
  verified. Pass.
- `GebLean/LawvereKSim.lean:34, :50, :105` (`KMor1`, `simrec`,
  `level`) — verified. Pass.
- `GebLean/LawvereKSimInterp.lean:162, :180, :193`
  (`interp_simrec`, `simrecVec_zero`, `simrecVec_succ`) —
  verified. Pass.
- `GebLean/Utilities/KArith.lean:31, :44, :222, :249`
  (`KMor1.one`, `pred`, `cond`, `interp_cond`) — verified.
  Pass.
- Tourlakis 2018 § 0.1.0.2 (p. 1), § 0.1.0.8 (p. 3),
  § 0.1.0.17(4), § 0.1.0.17(6) (p. 6), § 0.1.0.20 (p. 7),
  § 0.1.0.37 (pp. 15–16) — verified in PDF. Pass.
- Arity chain: `KMor1.simrec` returns `KMor1 (a + 1)`; the step
  family at component index `i : Fin (numRegs + 1)` has type
  `KMor1 (a + 1 + (numRegs + 1))`. § 3.4's "instantiated with
  `n := a + numRegs + 1`" matches the chain. Pass.
- Back-peel derivation in § 4.3 from `runFor_succ` plus
  `runFor_add`: correct. Pass.
- `pcDispatch`'s bottom-up `shift` construction (§ 3.5): the
  recursive case nests branches inside `KMor1.comp _ shift`,
  so branches with index `k ≥ 1` are interpreted at a context
  with `pred^k(PC)` substituted for the PC slot. The simp
  lemmas claim equality with `(branches k).interp ctx` at the
  unshifted context. Fail — see Blocker 1.
- Naming compliance per
  `https://leanprover-community.github.io/contribute/naming.html`:
  `def`s in `lowerCamelCase`; theorems in `snake_case` with
  embedded declaration identifiers. Pass.
- Markdownlint cleanliness: 0 errors. Pass.

## Findings

### Blocker

1. **`pcDispatch`'s bottom-up `shift` construction contradicts
   its simp lemmas and the `stepFamily` branch design.**
   Location: §§ 3.4 – 3.5. The recursive case of
   `pcDispatch (size + 1) branches default` is defined as

   ```text
   cond(PC, branches ⟨0, _⟩,
        KMor1.comp (pcDispatch size (branches ∘ Fin.succ)
                                default) shift)
   ```

   where `shift` substitutes `pred(PC)` for the PC slot. By
   unrolling, `branches ⟨k, _⟩` (for `k ≥ 1`) ends up nested
   inside `k` copies of `KMor1.comp _ shift`, and `default`
   inside `size` copies. Their interpretations therefore
   evaluate at a context whose `Fin.last n` slot reads
   `pred^k(PC)` instead of `PC`. The simp lemmas
   `interp_pcDispatch_match` and `interp_pcDispatch_default`
   (§ 3.5) claim equality with `(branches k).interp ctx` and
   `default.interp ctx` — evaluation at the *original*
   unshifted context. These lemmas fail whenever a branch or
   the default reads the PC slot.

   The `stepFamily` design in § 3.4 explicitly relies on
   branches and the default reading the PC slot via the
   level-0 helper
   `I_prev := proj (Fin.last (a + numRegs + 1))`:
   `branches_pc[.stop] = I_prev`,
   `branches_pc[_otherwise] = succ ∘ I_prev`, and
   `default_pc := I_prev`. Under the bottom-up construction,
   selecting `branches_pc[k]` for an instruction at PC `k > 0`
   returns `pred^k(k) = 0` rather than `k`; selecting
   `default_pc` for `PC = size + r` returns
   `pred^size(size + r) = r` rather than `size + r`. Both
   yield incorrect new-PC values.

   *Author response — fix.* Drop the `shift` substitution
   entirely. Rebuild `pcDispatch` as a single fold over
   `Fin size`: each `cond(pred^k(PC), branches[k], rest)`
   sits at the *original* context (no nested `KMor1.comp _
   shift`), so branches and default remain at the unshifted
   context throughout. `pred^k(PC)` is an inlined level-1
   composition `KMor1.comp pred (… KMor1.comp pred (proj
   (Fin.last n)) …)` of `pred` `k`-fold; `cond` composes
   three level-≤-1 children at level 1; the chain stays at
   level 1 by induction on `size`. The simp lemmas
   `interp_pcDispatch_match` and `interp_pcDispatch_default`
   now hold verbatim because the only context manipulation
   inside the chain is `cond`'s case-selection, not a
   substitution. Bottom-up fall-through semantics are
   preserved: `cond(PC, branches[0], cond(pred(PC),
   branches[1], cond(pred²(PC), branches[2], …default)))`
   selects `branches[k]` exactly when
   `pred^j(PC) ≠ 0` for `j < k` and `pred^k(PC) = 0`,
   i.e., when `PC > j` for `j < k` and `PC ≤ k`, i.e.,
   `PC = k`. § 3.5 rewritten accordingly; the helper
   `pred^k(PC) : KMor1 (n + 1)` is named and its level is
   stated (level 1, by `pred.level = 1` and `comp` taking
   max).

### Serious

1. **The adversarial-review punch list does not probe
   dispatcher interpretation correctness.** Item 10.4 traces
   only `KMor1.level` on `pcDispatch`; item 10.3 tabulates
   the URM step cases but not the dispatcher's interp
   delivery; item 10.6 covers the IH shape but not the simp
   lemmas. The blocker above slipped past two rounds because
   no item directs the reviewer to verify the simp lemmas
   hold under the stated construction.

   *Author response — fix.* New punch-list item 10.16 added:
   "Trace the recursive case of `pcDispatch (size + 1)`
   under `KMor1.interp`; confirm that `interp_pcDispatch_match`
   and `interp_pcDispatch_default` are provable as stated.
   Specifically: that branches' and default's interpretation
   contexts inside the dispatcher remain identical to the
   surrounding context (no PC-slot substitution by the
   recursion structure)."

2. **`interp_zero` and `interp_proj` are referenced in the
   correctness proof outline but not cited in § 2 or
   § 11.2.** Location: § 4.3 base case.

   *Author response — fix.* § 2 input table extended with
   `KMor1.interp_zero` at `LawvereKSimInterp.lean:86` and
   `KMor1.interp_proj` at `:98`; § 11.2 internal-reference
   list extended likewise.

3. **Past-end behaviour under the bottom-up dispatcher is
   under-specified.** Location: §§ 3.5, 4.3 past-end row.

   *Author response — fix (subsumed by Blocker B1).* The
   restructured `pcDispatch` keeps `default` at the
   unshifted context, so `default_pc := I_prev` reads the
   original PC slot directly. The `interp_pcDispatch_default`
   lemma's RHS becomes `default.interp ctx` without any
   contextual obligation on the implementer. Past-end
   self-loop now follows from `I_prev` at the unshifted
   context.

4. **`runFor_succ` is `@[simp]` but used in the spec via
   front-peel, while `simulate_step_match`'s step case needs
   the back-peel form.** A note clarifying that the proof
   must use the back-peel form would prevent an
   implementation trap.

   *Author response — fix.* § 4.3 amended with a parenthetical
   warning: "(note: `runFor_succ` is `@[simp]` in the
   front-peel direction; the back-peel form derived above is
   *not* `@[simp]` and must be invoked manually inside the
   step case, since adding `runFor_succ` to a `simp` set
   under the fixed `s := init P v` would rewrite the wrong
   direction.)"

### Minor

1. **The arity chain `n + 1 = a + numRegs + 2` is derived
   verbally but not surfaced as an equation.** Location:
   § 3.4 second paragraph.

   *Author response — fix.* § 3.4 amended with the explicit
   equation: "`n + 1 = a + 1 + (numRegs + 1) = a + numRegs +
   2`, so `n = a + numRegs + 1`."

2. **`interp_pcDispatch_match`'s hypothesis is a runtime
   hypothesis on a `@[simp]` lemma.**

   *Author response — fix.* § 3.5 closing prose extended:
   "Both `interp_pcDispatch_match` and
   `interp_pcDispatch_default` are `@[simp]` but
   conditionally so: their hypotheses (`ctx (Fin.last n) =
   k.val` or `≥ size`) must be in the local proof context
   for the rewrite to fire. In the `simulate_step_match`
   step case, these hypotheses arise from the case-split on
   the instruction at the previous PC, and the
   `URMState.step` case analysis pins `ctx (Fin.last n) =
   pc.val` at the relevant simp invocation."

3. **`Fin.lastCases` argument order in § 3.3 is not
   cross-checked against mathlib.**

   *Author response — defer-with-rationale.* The mathlib
   signature `Fin.lastCases : motive (Fin.last n) → (∀ i :
   Fin n, motive i.castSucc) → ∀ i, motive i` is stable
   project-wide (per `Mathlib.Data.Fin.Basic`); the spec
   relies on this established API, and adding a
   `file:line` citation for a mathlib stalwart would clutter
   § 3.3. The implementation will catch any mismatch via
   `lake build` type-checking.

4. **`natK'` lifting pattern is inlined but not factored.**

   *Author response — defer-with-rationale.* T3's only
   consumer of the `KMor1 0 → KMor1 n` lift is `natK'`; T4
   may introduce another instance and at that point the
   pattern can be factored out (e.g. as `KMor1.lift0 : KMor1
   0 → (n : ℕ) → KMor1 n`). Premature factoring without a
   second consumer would add abstraction without benefit.

5. **§ 9's LOC range "350–450 LOC" understates the per-task
   lower bound by 10 LOC.**

   *Author response — fix.* § 9's total estimate adjusted to
   "approximately 360–500 LOC" to bracket the per-task sum
   (Task 1 in `KArith.lean` plus Tasks 2–7 in the new file).

### Cosmetic-taste

1. **§ 3.5 uses "the bottom-up realisation avoids this
   trap".**

   *Author response — fix (subsumed by Blocker B1).* The
   restructured § 3.5 drops this sentence; the issue no
   longer arises because the new construction never
   substitutes the PC slot in branch contexts.

2. **§ 3.3 closing sentence uses "leaf".**

   *Author response — fix.* "Every leaf is `zero` or `proj`"
   rephrased as "Each subterm is `KMor1.zero` or
   `KMor1.proj _`".

3. **Master-design line-range citation
   (`lines 1902–1943`) at § 1.**

   *Author response — defer-with-rationale.* The line range
   is a coarse pointer for reader navigation; a doctoc-
   generated anchor reference would require master design
   maintenance to keep stable, which the spec cannot
   guarantee. The current line range is informational; if it
   drifts, the section reference (§ 7) remains correct.
