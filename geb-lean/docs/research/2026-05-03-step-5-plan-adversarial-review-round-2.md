# Step 5 plan — Adversarial review round 2

## Summary

Round 1 raised 0 blockers, 7 majors, and 8 minors against the
step-5 plan.  The author has revised the plan (now 2073 lines,
20 tasks).  This round re-verifies each round-1 finding, looks
for new defects introduced by the fixes, and looks for holes
the prior round overlooked.

Round-2 result: **0 blockers, 1 major, 4 minors**.  M1, M2,
M3, M4, M5, M7, m2, m4, m5, m7 are resolved.  M6 and m1 are
still open but downgraded.  One new minor surfaces around the
shape of the bound after `simp only` reductions in Task 8.

The plan is approximately ready for dispatch.  The remaining
major (M6 carried forward as a downgraded major) is an
implementer-experience risk rather than a correctness gap;
recommended fix is one extra fallback line in Task 2's
"if errors occur" guidance.

## Status of round-1 findings

### Resolved

- **M1 (bound shape mismatch)**: resolved.  The plan's Task 5
  (line 700), Task 7 (line 871), Task 8 (lines 996-997), and
  Task 9 (lines 1122-1123) now all use the
  `fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset (a + 1) p.2`
  shape.  This matches what
  `KMor1.majorize_by_componentBound` produces (via
  `LawvereKSimMajorization.lean:917`) once `a` is
  instantiated to `a + 1` in the simrec context.  Task 7
  step 6's `rw [KMor1.majorize_simrec_index_indep ...]
  at h_dom` should bridge cleanly.
- **M2 (`hrel v' i'` shape)**: resolved.  Task 13 line 1455
  now uses `congr_fun (hrel v') i'`.  Empirically verified
  (probe in `GebLean/Round2Probe.lean`, since deleted): given
  `hrel : (kMorNSetoid n m).r f g` (i.e.,
  `∀ ctx, f.interp ctx = g.interp ctx`) and applying
  `congr_fun (hrel v) i` yields
  `f.interp v i = g.interp v i`, which beta-reduces by
  `KMorN.interp`'s definition to
  `(f i).interp v = (g i).interp v` — the exact shape
  `kToERN_compat_extEq`'s `(hfg : ∀ v i, ...)` consumes.
  Lean's unifier accepts the conversion definitionally.
- **M3 (level-proof synthesis)**: resolved.  Task 18 lines
  1792, 1797 now pass the level proof explicitly:
  `kToER_interp addK (by simp [addK, KMor1.level]) ![3, 5]`.
- **M4 (`kToER_comp` simp lemma)**: resolved.  Task 6 lines
  774-786 add `kToER_comp` as a `@[simp]` theorem with
  `rfl` as proof.  Tasks 14 and 15's simp sets now reference
  `kToER_comp` explicitly (line 1525 lists `kToER_comp` in
  Task 14's set; line 1591 in Task 15's).  Empirically
  verified: a stub mirroring `kToER`'s comp arm closes
  `kToER_comp` by `rfl`.  Lean's proof irrelevance handles
  the `Prop`-valued `hf`/`hgs` arguments in the def's
  internal `have`s.
- **M5 (`unfold kToERFunctor_map` prelude)**: resolved.
  Tasks 14 and 15 now begin with `unfold kToERFunctor_map`
  before `apply Quotient.sound` (Task 14 line 1515; Task 15
  line 1585).  Since the lemmas' goals are
  `kToERFunctor_map (𝟙 n) = ...` and
  `kToERFunctor_map (f ≫ g) = ...` literally (the bundled
  `kToERFunctor` is constructed only later in Task 16), the
  `unfold` target name matches.
- **M7 (`show` -> `change`)**: resolved.  Task 9 line 1116
  now uses `change` with a comment explaining the
  elaboration-robustness rationale.  The `change`'s target
  text is well-formed and matches the `kToER`'s simrec-arm
  reduction shape.
- **m2 (banned word "simple")**: resolved.  Plan line 2068
  now reads "trivially mechanical tasks (skeleton creation,
  atomic def additions)".  No other "simple" usages outside
  the banned-word list at line 134.
- **m4 (Task 1 bridge proof empirical verification)**:
  resolved insofar as the proof structure mirrors the
  existing `interp_simrec_eq_simrecVec` analogue and
  `Fin.append_left` / `Fin.append_right` exist in the
  current mathlib (verified via grep against
  `mathlib/Mathlib/Data/Fin/Tuple/Basic.lean:363,366,647,650`).
- **m5 (Tourlakis citations)**: largely resolved.  Tasks 1,
  6, 11, 12, 13, 14, 15 all carry literature references in
  their docstring text, although a few citations remain at
  master-design-only granularity (Tasks 11, 12, 13).  This
  is acceptable per CLAUDE.md's discipline (master design
  cross-references the Tourlakis paragraphs).
- **m7 (Task 18 `addK.level ≤ 2` proof)**: resolved.  Plan
  uses `simp [addK, KMor1.level]` consistently and the
  fallback list at line 1814 is appropriately concise.

### Still open

- **M6 (Task 7 step 4 `simp only [KMor1.level]`)**: still
  open in spirit but downgraded.  The fix in spec round-3
  / plan round-2 stayed with `simp only [KMor1.level]`.
  Round-1's empirical observation was that `rfl` likely
  suffices on its own (the simrec branch of `KMor1.level`
  ignores the index argument by definition).  The plan
  retains the fallback list of `show ... = ...; rfl` in
  Task 7 step 4 (lines 932-935), which is a less smooth
  fallback than the simpler `rfl`.  This is implementer-
  experience risk only, not a correctness gap.
- **m1 (banned word "block")**: still present at lines 181,
  195, 621, 636, 1282 ("import block", "namespace block",
  "by block").  CLAUDE.md's banned-word list does include
  "block".  Mitigation: rephrase as "import section",
  "namespace scope", or "the `by` tactic body".  Not a
  correctness issue.

## New findings

### Blockers

None.

### Majors

- **NM1 (downgrade of M6)**: Task 7 step 4 (line 908) inlines
  `simp only [KMor1.level]` inside a `have hfact : ... := by
  simp only [KMor1.level]` proof.  The simrec branch of
  `KMor1.level` (`LawvereKSim.lean:112-114`) ignores the
  output index, so `(KMor1.simrec j ...).level
  = (KMor1.simrec i ...).level` should close by `rfl` or by
  `simp only [KMor1.level]`.  Recommend documenting the
  faster `rfl` path as the primary, with `simp only` as
  fallback (current order is reversed).  This is a downgrade
  of round-1's M6 from major to minor implementer-experience
  risk; carrying it as a major only because Task 7 is
  load-bearing and its build-verify cycle stalls if the
  intermediate step does not close.

### Minors

- **Nm1 (Task 8 `Matrix.cons_val_zero` in simp set)**: Task 8
  step 1 (line 1004) lists `Matrix.cons_val_zero` in its
  simp set.  The bound's shape is `comp (A_two_iter p.1)
  (fun _ : Fin 1 => sumCtxERPlusOffset (a+1) p.2)`, which
  contains no `Matrix.cons` term.  After `interp_comp` and
  `interp_A_two_iter`, the goal reduces by beta to
  `tower p.1 ((sumCtxERPlusOffset (a+1) p.2).interp ctx)
  ≤ tower p.1 (...)`.  `Matrix.cons_val_zero` won't fire
  but is harmless (it just won't match).  Recommend
  removing it from the simp set for clarity — its presence
  suggests the `![...]` shape that round-1 M1 corrected
  away from.

- **Nm2 (Task 7 step 3 `congr 2` after `KMor1.interp_simrec`)**:
  Task 7 step 3 (line 900) applies `congr 2` after
  `rw [KMor1.interp_simrec]`.  The `KMor1.interp_simrec`
  rewrite produces a `simrecVec`-shaped term whose `j`
  index argument needs to align across `h_rev`'s LHS and
  RHS.  Whether `congr 2` closes depends on the exact
  internal shape Lean elaborates after the rewrite.  The
  plan's "If errors occur" list at line 928 suggests
  `congr 1` followed by `funext j'` and rewrites; that
  fallback may be more reliable.  Empirical verification
  pending implementer.

- **Nm3 (Task 14/15 `Quotient.lift_mk` and `Quotient.liftOn_mk`
  both in simp set)**: Tasks 14 (line 1524) and 15 (line
  1590) list both `Quotient.liftOn_mk` and `Quotient.lift_mk`
  in their simp sets.  The lifting actually used in
  `kToERFunctor_map` is `Quotient.liftOn` (Task 13 line 1436);
  `Quotient.lift_mk` is for `Quotient.lift` (different
  primitive).  Listing both is harmless but the
  `Quotient.lift_mk` entry is dead.  Recommend dropping it.

- **Nm4 (Task 7's `(a + 1 + (k + 1))` arity inside
  `(fun _ : Fin 1 => sumCtxERPlusOffset (a + 1) p.2)`)**:
  Plan Task 7 line 871's bound uses
  `sumCtxERPlusOffset (a + 1) p.2` because the simrec
  produces a morphism of arity `a + 1`.  This is the
  arity that gets passed when
  `majorize_by_componentBound (.simrec j h_fam g_fam) h_j
  (Fin.cons m x)` is applied — so `a` in
  `majorize_by_componentBound`'s signature gets specialised
  to `a + 1`.  This produces `sumCtxERPlusOffset (a + 1)
  p.2` correctly.  No bug, but the relationship deserves
  an explicit comment in Task 7's docstring.

## Empirical verifications performed

The following were tested in this round via `lake build` on a
probe file (since deleted):

1. **M2 fix typecheck**: a stub mirroring Task 13's structure
   (`Quotient.exact h_eq` → `congr_fun (hrel v) i`) compiled
   cleanly.  The conversion of `hrel : ∀ ctx, f.interp ctx
   = g.interp ctx` followed by `congr_fun (hrel v) i` to
   produce `(f i).interp v = (g i).interp v` works via
   beta-reduction of `KMorN.interp`'s definition.  No
   explicit `unfold` or `change` needed.

2. **M4 fix `kToER_comp` rfl**: a stub mirroring Task 5's
   `kToER` def's comp arm and Task 6's `kToER_comp` lemma
   compiled cleanly.  `rfl` closes the lemma; Lean's proof
   irrelevance for `Prop`-valued level proofs is sufficient.

3. **`Fin.append_left` / `Fin.append_right` lemma names**:
   verified via grep that both exist in current mathlib
   (`Mathlib/Data/Fin/Tuple/Basic.lean:363,366,647,650`).
   Task 1's bridge proof should compile against current
   mathlib without name shifts.

4. **Bound shape congruence**: verified that
   `KMor1.majorize_by_componentBound` (at
   `LawvereKSimMajorization.lean:917`) produces the bound
   shape `fun _ : Fin 1 => sumCtxERPlusOffset a p.2` —
   exact match to plan Task 5 line 700 (modulo `a` vs
   `a + 1` arity, where the plan's `a + 1` is correct
   because the simrec produces a morphism of arity `a + 1`
   and `componentBound` is invoked with that arity).

The probe file `GebLean/Round2Probe.lean` was created,
verified to build, and removed.

## Recommendations

1. **Plan revision before dispatch (small)**: address NM1 by
   re-ordering Task 7 step 4's fallback list to place `rfl`
   before `show ... = ...; rfl`.  Add a one-line comment in
   Task 7 step 4 explaining that `KMor1.level` at simrec
   ignores the index per `LawvereKSim.lean:112-114`, so
   `rfl` is the primary path.  The current
   `simp only [KMor1.level]` should remain as the fallback
   (in case the simrec-branch lambda contains hidden
   metavariables Lean wants to elaborate).

2. **m1 banned-word audit (cosmetic)**: replace "import
   block", "namespace block", and "by block" with "import
   section", "namespace scope", and "the `by` tactic body"
   at lines 181, 195, 621, 636, 1282.

3. **Nm1 simp-set cleanup (cosmetic)**: remove
   `Matrix.cons_val_zero` from Task 8 step 1's simp set; it
   does not fire on the `fun _ : Fin 1 => ...` shape and
   carries the legacy `![...]` resonance.

4. **Nm3 simp-set cleanup (cosmetic)**: remove
   `Quotient.lift_mk` from Tasks 14 and 15's simp sets; the
   functor uses `Quotient.liftOn`, not `Quotient.lift`.

5. **Nm4 docstring (cosmetic)**: add a comment to Task 7's
   docstring explaining the `a + 1` arity arithmetic
   (`majorize_by_componentBound`'s `a` parameter gets
   specialised to `a + 1` because the simrec produces a
   morphism of that arity).

6. **Empirical verification at task time**: implementer
   should run `lake build` after each task as the plan
   specifies, but particularly after Tasks 5, 7, 9, 13, 14,
   15.  These are the load-bearing tasks where round-1
   identified majors; even though round-2's fixes look
   sound, building empirically is the safety check.

## Round-3 trigger

Round 3 is **not** required.  The remaining items are minors
(Nm1, Nm3, Nm4, m1) and one downgraded major (NM1) that
amount to cosmetic improvements and one ordering tweak in a
fallback list.  The plan can dispatch as-is, with the
expectation that the implementer will fix Nm1, Nm3, Nm4 (or
the reviewer will catch them in the per-task subagent review)
and that NM1's `rfl` path will work without needing the
`simp only` fallback.

If a round 3 is run, it should focus on:

1. Verifying the implementer's per-task builds match the
   plan's predictions (no new error patterns).
2. Confirming Tasks 14 and 15's `simp only` simp sets
   actually reduce the goals as the plan claims.
3. Confirming Task 9's `change` target text matches the
   actual elaboration of `kToER`'s simrec arm.
