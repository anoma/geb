# Step 4 cycle-end code review

Review of commits `origin/terence/develop..HEAD` (20 commits)
implementing Step 4 K^sim majorization theorems
(Tourlakis 2018 §0.1.0.10) per spec
`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`
and master design §3.4 / §3.5. Build clean (`lake build`
1528 jobs successful), `lake test` exit 0, no warnings, no
`sorry` / `admit` / `axiom` / `noncomputable` / direct
`Classical` use.

## Findings

No blockers, no majors. Minor and nit notes only.

### 1. Minor — duplicated level-hypothesis derivations

Severity: minor.

Location: `GebLean/LawvereKSimMajorization.lean` lines
607-625 (def `KMor1.majorize` `comp` case), 632-657
(`simrec` case), and the parallel reconstruction at lines
716-725 / 794-812 inside `KMor1.majorize_by_A_two_iter`.

Issue: the level-derivation `have` blocks for `hf`, `hgs`,
`hh`, `hg` are duplicated verbatim between the def and the
companion theorem. Functionally fine — the theorem must
reconstruct them to match the def's term-mode hypothesis
slots — but factoring them as file-local lemmas
(`KMor1.level_le_of_comp_le_two`, `..._of_simrec_le_two`)
would shrink both call sites and remove a small drift
risk if either pattern changes later.

Proposed fix: optional follow-up extraction. Not a blocker
— current shape is the literal mirror prescribed by spec
§5.2 / §6.3.

### 2. Minor — dead level-bound parameters in `simrecVec_le_A_one_iter`

Severity: minor.

Location: `GebLean/LawvereKSimMajorization.lean` lines
480-481 (`_hh`, `_hg` parameters of
`KMor1.simrecVec_le_A_one_iter`).

Issue: the level-bound hypotheses `(_hh : ∀ j, (h_fam j).level ≤ 1)`
and `(_hg : ∀ j, (g_fam j).level ≤ 1)` are accepted but
unused inside the proof — the actual content travels
through `hbase` / `hstep`. The underscored names
suppress the unused-binder linter cleanly, and the spec
§6.2 explicitly lists them in the signature, so this is
intentional interface adherence rather than dead code.

Proposed fix: the spec already authorizes their
presence. Either keep as-is (documented spec contract)
or drop the parameters and update the spec. Current
state is consistent.

### 3. Nit — docstring substring "admit"

Severity: nit.

Location: `GebLean/LawvereKSimMajorization.lean` line
473 ("base and step families admit per-call A_1
bounds").

Issue: standard English usage of "admit" meaning
"permit". The CLAUDE.md banned-word list does not
include "admit" as English; only the Lean tactic `admit`
is forbidden. No change required.

### 4. Nit — `A_one_iter_mono_input` placement

Severity: nit.

Location: `GebLean/LawvereKSimMajorization.lean` line
460 (`private theorem A_one_iter_mono_input`).

Issue: this private helper sits between two public
theorems (`KMor1.majorize_by_A_one_iter` ends at line
455; `KMor1.simrecVec_le_A_one_iter` begins at line
476). Co-locating private helpers near their sole
caller is fine; just noting that the spec §6.4 lists
auxiliary lemmas as a separate group and the file
otherwise groups by visibility.

Proposed fix: none required.

## Acceptance criteria verification (spec §10)

1. **Module exists with required surface.**
   - Private `vMax` abbrev: line 43. Pass.
   - `ERMor1.sumCtxER` reused from
     `LawvereERBoundComputable.lean` line 280; the
     step-4 cross-module diff (line 287) marks
     `ERMor1.interp_sumCtxER` as `@[simp]`. Pass.
   - `ERMor1.sumCtxERPlusOffset` def + `@[simp]
     interp_sumCtxERPlusOffset` simp lemma +
     `vMax_add_offset_le_sumCtxERPlusOffset` /
     `vMax_le_sumCtxER` dominance helpers: lines 89,
     99, 107, 116. Pass.
   - γ.1 `linearBound_le_A_one_iter` (line 178), γ.2
     `A_one_iter_le_two_pow_succ` (line 218), γ.3
     `two_pow_succ_mul_succ_le_tower_two` (line 234),
     γ corollary `A_one_iter_le_A_two_iter_two` (line
     262), γ.5 `A_one_iter_linear_le_A_two_iter_two`
     (line 275), `A_one_iter_compose` (line 355),
     `self_le_A_one_iter` (line 396),
     `A_one_iter_mono_left` (line 410). Pass.
   - `KMor1.majorize_one` def (line 432) +
     `majorize_by_A_one_iter` theorem (line 442). Pass.
   - `KMor1.simrecVec_le_A_one_iter` (line 476). Pass.
   - `KMor1.majorize` def (line 602) +
     `majorize_by_A_two_iter` theorem (line 662). Pass.
   - `KMor1.majorize_by_componentBound` step-5 bridge
     (line 910). Pass.
   - Auxiliary lemmas `vMax_apply_le`,
     `vMax_le_of_pointwise`, `vMax_cons`,
     `tower_add_offset_le`, `tower_compose_offsets`:
     lines 48, 55, 62, 129, 161. Pass.

2. **Tests present.**
   - `GebLeanTests/LawvereKSimMajorization.lean` has the
     spec §8.1 `#guard`s on atomic majorize / majorize_one
     witnesses, the level-1 simrec witness `addK`
     exercising `majorize_one` (line 25-26) and
     `majorize` (line 37) through the simrec branch,
     and the two `example` proofs invoking the
     dominance theorem at concrete inputs (`addK
     ![1,1]` line 44, `succ ![3]` line 52). Pass.

3. **`GebLean.lean` imports
   `GebLean.LawvereKSimMajorization`** — confirmed in
   the diff (`+1` line in `GebLean.lean`). Pass.

4. **`GebLeanTests.lean` imports
   `GebLeanTests.LawvereKSimMajorization`** — confirmed
   in the diff (`+1` line in `GebLeanTests.lean`).
   Pass.

5. **No regressions.** `lake build` (1528 jobs),
   `lake test` exit 0. No prior tests removed; only the
   one-line edits to
   `GebLean/LawvereERBoundComputable.lean` (add `@[simp]`
   to `interp_sumCtxER`) and
   `GebLean/LawvereKSimPolynomialBound.lean` (drop
   `private` from `Fin.foldr_max_ge`) were made
   upstream, both strictly weaker than the prior
   surface. Pass.

6. **Markdown clean.** Not re-checked here; the spec /
   plan are pre-existing and unchanged in this diff.

## Citation discipline (CLAUDE.md transcription rule)

Spot check on the listed entities: every public def /
theorem in `GebLean/LawvereKSimMajorization.lean`
carries a Tourlakis 2018 §0.1.0.10 and/or master design
§3.4 / §3.5 citation in its docstring (e.g. lines 88-92
`vMax_le_sumCtxER` cites master design §3.5; lines
174-177 `linearBound_le_A_one_iter` cites master design
§3.4 + Tourlakis 2018 §0.1.0.10; lines 905-909
`majorize_by_componentBound` cites master design §3.5
lines 1099-1116). Pass.

## Constructive discipline

No `Classical` import / open / `classical` attribute in
the diff. `noncomputable` absent. `axiom` absent. The
`#print axioms` of the headline theorems
(`KMor1.majorize_by_A_two_iter`,
`KMor1.majorize_by_componentBound`,
`KMor1.majorize_by_A_one_iter`,
`linearBound_le_A_one_iter`) shows
`{propext, Classical.choice, Quot.sound}` — same set as
the upstream `KMor1.linearBound_dominates` from earlier
steps, inherited transitively through mathlib's
`Finset.le_sup` / `Nat.lt_pow_succ_log_self` API rather
than introduced in this cycle. CLAUDE.md's rule
forbids direct use; transitive mathlib inheritance is
unavoidable and pre-existing in the workstream. Pass.

## Style

- All lines ≤ 80 chars (`awk` check returns empty for
  both `LawvereKSimMajorization.lean` and the test
  file).
- All `simp` invocations are `simp only [...]`.
- One `show` token at line 298, used as a type
  ascription on `Nat.pow_le_pow_right`'s base argument
  — idiomatic, not a `change`-vs-`show` violation.
- No emojis, no copyright headers, no historical
  comments, no `TODO`s.

## Per-case `(r, offset)` audit on `KMor1.majorize`

Spec §1.3 / §5.2 fix `r_2 = 2`, `offset_2 = r_H + r_G + 2`
for the simrec case and uniform `r = 2` at atoms. The
implementation at lines 604-657 yields:

- `zero` → `(2, 2)` — bound closes via `self_le_tower 2`
  plus `omega` (theorem line 669-675).
- `succ` → `(2, 3)` — bound closes via
  `vMax_apply_le v 0` + `self_le_tower` + `omega`
  (line 676-683).
- `proj _` → `(2, 2)` — bound closes via
  `vMax_apply_le` + `self_le_tower` + `omega`
  (line 684-691).
- `comp` → `(p_f.1 + r_g, p_f.2 + o_g)` — bound closes
  via `tower_compose_offsets` (line 715-793).
- `raise` → `(2, p.1 + 2)` — bound closes via
  `A_one_iter_le_A_two_iter_two` (line 692-714).
- `simrec` → `(2, r_H + r_G + 2)` — bound closes via
  `simrecVec_le_A_one_iter` +
  `A_one_iter_linear_le_A_two_iter_two` (line 794-903).

All offset arithmetic in the theorem closes via
`omega` after `simp only [..., Matrix.cons_val_zero]`
and `tower`-chain rewrites; no manual gap arithmetic.
Pass.

## Cross-module edits review

- `GebLean/LawvereERBoundComputable.lean` line 287:
  `theorem ERMor1.interp_sumCtxER` gains `@[simp]`. The
  closed-form RHS `(Finset.univ : Finset (Fin n)).sum
  ctx` is a stable rewrite target. No regression.
- `GebLean/LawvereKSimPolynomialBound.lean` line 302:
  `Fin.foldr_max_ge` loses its `private` modifier. The
  lemma signature is unchanged, the body is unchanged,
  and de-privating is strictly weaker than the prior
  state. No regression.

Both edits match spec §2.4 (Fin.foldr_max_ge
de-privatization) and §3.1 (interp_sumCtxER
@[simp]-marking).

## Test surface review

`GebLeanTests/LawvereKSimMajorization.lean`:

- Lines 14-15: `addK.level ≤ 1` and `= 1` decided —
  ensures the test's level-1 simrec witness exists.
- Lines 18-22: atomic `majorize_one` offsets `= 0` —
  matches §5.1 contract.
- Lines 25-26: addK exercises level-1 simrec via
  `majorize_one` (`r ≥ 1`, offset `= 0`) — the simrec
  branch's `r_H + r_G` linearization gives a positive
  exponent.
- Lines 29-37: atomic `majorize` `r = 2` plus addK
  through `majorize`'s simrec branch giving `r = 2` —
  confirms uniform `r = 2`.
- Lines 44-58: two `example` proofs invoking the
  universal theorem at concrete inputs without forcing
  kernel evaluation of `A_two_iter`'s `expER` tree —
  matches CLAUDE.md memory note about ER /
  Gödel-numbering interp not being safe for `#guard`.
  These are not vacuous: each `example` typechecks
  iff the dominance theorem is sound at that input
  shape.

The addK case (a level-1 simrec) does flow through
`KMor1.majorize`'s `simrec` constructor branch —
verified by the structural match. Pass.

## Summary

Step 4 lands cleanly. No blockers, no majors, two
minors (both intentional / spec-driven), two nits
(both no-action). The 935-line module transcribes
Tourlakis 2018 §0.1.0.10 and master design §3.4 / §3.5
faithfully, with literature citations on every public
entity. The level-2 simrec arithmetic — flagged in
spec §9.4 as the cycle's largest single proof — is
factored into the documented sub-lemmas
(`simrecVec_le_A_one_iter`,
`A_one_iter_linear_le_A_two_iter_two`,
`tower_compose_offsets`, etc.) and closes without
admits or sorries.

Mergeability assessment: ready to merge.
