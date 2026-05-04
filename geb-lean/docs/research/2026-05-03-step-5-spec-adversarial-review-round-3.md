# Step 5 spec — Adversarial review round 3

## Summary

The two round-2 fixes (the `congr 2` line and the bridge-lemma proof-size
estimate) are verified sound by direct empirical testing. Two of round 2's
remaining minors (m1' on the `rw [show ... from rfl]` IH-adapter, and
m2' on the simp set augmentation) remain real but are appropriately
soft-flagged in the spec. One new finding emerges from the round-3 sweep:
a small under-specification on whether the `dite_true` / `dite_false`
unfolding survives the round-2 simplification of step 3 (clean to fix at
task time but worth flagging). No new blockers, no new majors, and
otherwise the spec reads cleanly.

Counts of new findings: **0 blockers, 0 majors, 3 minors**. The spec is
ready to transition to writing-plans without further adversarial-review
rounds.

## Status of round-2 fixes

### Verified-sound

- **Round-2 finding A (`congr 2 <;> simp` build error)**. Verified by
  direct lean-lsp test in a scratch file inside the project tree. The
  bare `congr 2` after `rw [KMor1.interp_simrec]` closes the goal
  `KMor1.simrecVec h_fam g_fam x m j = (KMor1.simrec j h_fam g_fam).interp
  (Fin.cons m x)` with no residual subgoals. The spec text at §6.2.2
  step 3 (line 559) and §6.2.4 step 5 (line 759) now reads `congr 2`
  and `congr 1` respectively, with explanatory prose. No "tactic does
  nothing" warning fires. Fix is clean.

- **Round-2 finding B (bridge-lemma proof-size estimate)**. The spec at
  §6.1 (lines 426–446) now estimates "~25–40 lines" with the IH
  quantified over the output index `j`. Verified by attempting the
  proof: the IH from a step-case `induction n` is fixed at one `j`,
  but the previous-iteration vector inside the `Fin.append` requires
  the IH at every component index. The fix `intro n; induction n with
  | zero => intro j; rfl | succ n ih => intro j; ...` is the correct
  shape; the `congr_fun ih ⟨...⟩` pattern dispatches the outer-branch
  case. A full proof attempt in scratch confirmed the architectural
  shape is right (the residual mathlib-lemma-name decisions on
  `Fin.append_left` / `Fin.append_right` are implementer-time work, not
  a spec defect). The 35-line analogue at lines 121–155 of
  `LawvereKSimInterp.lean` is genuine.

- **Round-1 minor m4 / round-2 callout (`simp only [KMor1.majorize]` on
  `majorize_simrec_index_indep`)**. Verified: `simp only [KMor1.majorize]`
  closes the goal cleanly. Empirical check passed in scratch file
  (after `simp only`, no residual goals). The simrec branch's `match`
  arm (lines 632-657 of `LawvereKSimMajorization.lean`) discards the
  index argument as `_`, and the proof-irrelevance over the
  level-discharge `have hh j` and `have hg j` propagates through
  `Fin.foldr` cleanly. The fallback "hand-construction" path in §6.2.1
  remains as documented insurance, but the primary path works.

- **`Quotient.liftOn_mk` and `Quotient.lift_mk` lemma names**. Both
  exist in current mathlib (lines 297 and 325 of
  `.lake/packages/mathlib/Mathlib/Data/Quot.lean`). The §8.3 simp set
  augmentation listing both names is sound.

- **NF3 (`kToERFunctor_obj n = n` via `rfl`)**. Verified: both
  `LawvereKSimDCat 2` and `LawvereERCat` are definitionally `ℕ`. A
  trial coercion `(n : LawvereERCat) = n` for `n : LawvereKSimDCat 2`
  closes by `rfl`; literal `(5 : LawvereKSimDCat 2) = (5 : LawvereERCat)`
  also closes by `rfl`. The opportunistic `@[simp]` lemma in §8.4 is
  realisable.

- **NF4 (import list audit against §§4–8 API usage)**. The spec's §3.2
  list includes `GebLean.LawvereER` (used directly via `ERMor1.zeroN`,
  `ERMor1.succ`, `ERMor1.proj`, `ERMor1.comp`),
  `GebLean.LawvereERQuot` (used for `ERMorNQuo` / `erMorNSetoid` /
  `LawvereERCat`), `GebLean.LawvereKSim` (KMor1),
  `GebLean.LawvereKSimInterp` (interp lemmas),
  `GebLean.LawvereKSimMajorization` (`KMor1.majorize`,
  `majorize_by_componentBound`, `sumCtxERPlusOffset`),
  `GebLean.LawvereKSimQuot` (KSimMor, KMorNQuo),
  `GebLean.Utilities.ERAMajorants` (`A_two_iter`,
  `interp_A_two_iter`), and
  `GebLean.Utilities.ERSimultaneousBoundedRec`
  (`simultaneousBoundedRec`, `simultaneousBoundedRec_interp_correct`).
  The spec also notes implementer prunes per `lean_unused_imports`.
  Coverage is correct.

- **NF5 (`addK` inline construction round-2 verification)**. Spec §9.2
  text matches what round 2 tested (KMor1.simrec with k:=0, base = proj
  0, step = comp succ ![proj 2]). No regression.

### Still problematic

- **Round-2 minor m1' (§5.3 `rw [show ... from rfl]`)**. The fragile
  `rw` pattern remains in the spec text. The idiom
  `rw [show kToER (h_fam j) h' = kToER (h_fam j) _ from rfl]` differs
  from a true `rfl` only in the level-proof slot. Lean's `rw` requires
  finding a pattern in the goal that matches `kToER (h_fam j) h'` on
  the LHS; if the goal already has `kToER (h_fam j) (h_h j)` (where
  `h_h j` is the IH-internal level proof), the `rw` may or may not
  fire depending on whether Lean's pattern matcher treats the two Prop
  terms as syntactically equal. The standard idiom is propagation via
  proof-irrelevance, e.g. `convert ih_h j v' using 0` or
  `exact ih_h j v' |>.trans (by congr; apply Subsingleton.elim)`.
  Round-2 explicitly recommended marking this as
  "implementer verifies via lean-lsp; one of the alternatives below
  will close cleanly", but the spec text still has only the single
  `rw [show ...]` pattern without alternatives. Implementer-time risk
  is small but real.

  Recommendation: add a one-line callout at §5.3 enumerating the two
  fallback patterns (`convert ... using 0` or hand-coercion via
  `proof_irrel_heq`).

## New findings

### Blockers

None.

### Majors

None.

### Minors

#### m1''. §6.2.2 Step 3 prose under-specifies dite reduction

The spec at §6.2.2 step 3 now reads (after the round-2 fix):

```text
-- Empirically: bare `congr 2` closes both residual
-- goals; `(Fin.cons m x) 0` reduces to `m` and
-- `(fun j' => (Fin.cons m x) (Fin.succ j'))` reduces
-- to `x` by `Fin.cons`'s computation rules without
-- explicit simp.
```

Empirically the `congr 2` in fact closes the *whole* goal, not just
"both residual goals" — there are no residual goals after `congr 2`
because Lean's `congr` already drives both arguments to `rfl` via the
`Fin.cons` reduction. The prose is ambiguous; an implementer reading
it might expect to see two residual goals and add unnecessary `simp`
follow-ups (which would then trigger the unused-tactic warning under
`warningAsError = true`).

Recommendation: tighten the prose to "`congr 2` closes the goal
entirely" or "after `rw [KMor1.interp_simrec]`, the resulting
equality between two `KMor1.simrecVec` calls reduces to reflexivity
via `Fin.cons`'s definitional reduction, and `congr 2` dispatches it
without residual subgoals".

#### m2''. §6.2.4 step 5 has the same prose ambiguity

Spec §6.2.4 step 5 (lines 753–759) reads:

```text
-- (Fin.cons n x) 0 reduces to n and
-- (fun j' => (Fin.cons n x) (Fin.succ j')) reduces to x
-- by Fin.cons's computation rules; `congr 1` (or `congr 2`
-- depending on residual structure) closes definitionally.
```

The spec hedges between `congr 1` and `congr 2`. From the §6.2.2
verification, it is more likely `congr 2` here too (since the goal
after the bridge-lemma rewrites and `KMor1.interp_simrec` rewrite has
the same shape). The prose hedge "or `congr 2` depending on residual
structure" is honest but invites the same unused-tactic-warning class
of mistake noted in m1''.

Recommendation: either commit to `congr 2` after empirical
verification at task time, or replace the hedge with explicit
implementer guidance: "if `congr 1` leaves residual goals, escalate to
`congr 2`; do *not* add a trailing `<;> simp [...]` (would trigger
unused-tactic warning under `warningAsError = true`)".

#### m3''. §5.3 IH-adapter alternatives not specified

Per round-2 m1', the spec leaves the §5.3 `rw [show ... from rfl]` as
a single recipe. Round 2 recommended "spec marks as implementer
verifies via lean-lsp; one of the alternatives below will close
cleanly". The current spec text does not list the alternatives.

If the recipe fails at task time, the implementer must improvise.
Listed alternatives that the spec could enumerate:

1. `exact ih_h j v'` (likely works if `induction f` produces an IH
   whose level argument is the same proof Lean infers in the simrec
   branch's context).
2. `convert ih_h j v' using 0` (forces reduction modulo Prop
   irrelevance).
3. Build the level-discharge inside `kToER_interp_simrec` so the IH
   can be passed without re-quantification (would require restating
   the helper signature).

Recommendation: add a short list of fallbacks at §5.3 to spare the
implementer the discovery loop.

## Empirical verifications performed

- **§6.2.2 `congr 2` closes goal**: written into a scratch file at
  `GebLeanTests/Round3Scratch.lean` (deleted post-verification), with
  a lemma signature equating `KMor1.simrecVec h_fam g_fam x m j` to
  `(KMor1.simrec j h_fam g_fam).interp (Fin.cons m x)`. After
  `rw [KMor1.interp_simrec]; congr 2`, `lean_goal` reports
  `goals_after: []`. Build clean, no warnings.

- **§6.2.1 `simp only [KMor1.majorize]` closes
  `majorize_simrec_index_indep`**: scratch lemma with
  `(KMor1.simrec i h_fam g_fam)` LHS and `(KMor1.simrec j h_fam g_fam)`
  RHS, level proofs `h_i` and `h_j` distinct. `simp only [KMor1.majorize]`
  closes; no residual goals; no warnings.

- **§8.4 `kToERFunctor.obj n = n` defeq**: confirmed via stub
  `def stubObj : LawvereKSimDCat 2 → LawvereERCat := fun n => n` and
  `example : stubObj 5 = 5 := rfl` plus
  `example (n : LawvereKSimDCat 2) : stubObj n = n := rfl`. Both
  close cleanly. The phantom-typeclass-resolution pattern of
  `LawvereKSimDCat (_d : ℕ) := ℕ` does not interfere.

- **`Quotient.liftOn_mk` and `Quotient.lift_mk` exist in mathlib**:
  confirmed at lines 297 and 325 of
  `.lake/packages/mathlib/Mathlib/Data/Quot.lean`.

- **§6.1 bridge-lemma proof shape**: scratch attempt confirmed the
  high-level structure (induction on n, intro j inside step case, case
  split on `idx.val < a + 1`, IH applied via `congr_fun`) is correct.
  The mathlib lemma names `Fin.append_left'` (note: `Fin.append_left`
  with `castAdd`-typed indices, vs `Fin.append_left'` with
  `castLE`-typed indices) and `Fin.append_right` may need careful
  selection at task time, but this is implementer-level concern, not
  a spec defect.

- **`vMax_cons` reference at line 875 of
  `LawvereKSimMajorization.lean`**: confirmed real; the `rw [vMax_cons]`
  call expands `vMax (Fin.cons n v) = max n (vMax v)` (lemma defined
  at line 62, proof body at 64–79 using `Fin.cases`). The shape is
  the right analogue for §6.2.3's `sumCtxER_cons_le_of_le` strategy
  outline.

- **`warningAsError = true` enforcement**: confirmed via
  `moreLeanArgs = ["-DwarningAsError=true"]` in `lakefile.toml`. Any
  unused-tactic / unused-simp-arg warning would be promoted to a build
  error.

## Recommendations

The spec is ready to transition to writing-plans. Three small
recommended edits remain (all minors):

1. **m1''** (and m2''): tighten the §6.2.2 step 3 and §6.2.4 step 5
   prose to commit to `congr 2` (after task-time verification) and
   explicitly note that no trailing `<;> simp [...]` should be added.

2. **m3''**: add a fallback list at §5.3 for the IH-adapter, listing
   `convert ih_h j v' using 0` and `exact ih_h j v'` as alternatives
   to the `rw [show ... from rfl]` pattern.

These are quality-of-implementer-experience improvements. None of them
blocks transition to writing-plans, and an implementer who hits any of
them at task time can resolve in <5 minutes by reading the round-2
review or this round-3 review.

## Round-4 trigger

A round 4 is **not warranted**. The round-2 fixes have been verified
sound by direct empirical testing in lean-lsp. The remaining minors are
implementer-discretion items where the spec already provides enough
guidance plus fallback prose. If the spec author wishes to apply the
three minor edits above before transitioning, that closes the round-3
findings; otherwise, round-3 findings can be deferred to spec-patch
iterations during implementation without disrupting the writing-plans
phase.
