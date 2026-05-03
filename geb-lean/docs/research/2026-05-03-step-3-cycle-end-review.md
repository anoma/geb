# Step 3 cycle-end code review

## Summary

clean — no findings.

## Acceptance criteria verification

1. **Named composites present.**
   - `def ERMor1.A_one : ERMor1 1` at
     `GebLean/Utilities/ERAMajorants.lean:53`.
   - `def ERMor1.A_one_iter : ℕ → ERMor1 1` at
     `GebLean/Utilities/ERAMajorants.lean:79`.
   - `def ERMor1.A_two_iter : ℕ → ERMor1 1 := ERMor1.towerER`
     at `GebLean/Utilities/ERAMajorants.lean:141`, defined as
     an alias of `ERMor1.towerER` (single-line body
     `ERMor1.towerER r`). Pass.

2. **Closed-form `@[simp]` interp lemmas present.**
   - `@[simp] theorem ERMor1.interp_A_one` at
     `GebLean/Utilities/ERAMajorants.lean:65` with closed
     form `2 * (ctx 0) + 2`.
   - `@[simp] theorem ERMor1.interp_A_one_iter` at
     `GebLean/Utilities/ERAMajorants.lean:101` with closed
     form `2 ^ r * (ctx 0) + (2 ^ (r + 1) - 2)`.
   - `@[simp] theorem ERMor1.interp_A_two_iter` at
     `GebLean/Utilities/ERAMajorants.lean:147` with closed
     form `tower r (ctx 0)`.
   - All three closed forms match spec §4 exactly. Pass.

3. **PolyBound builders present, no `ofA_two_iter` shipped.**
   - `def ERMor1.PolyBound.ofA_one` at
     `GebLean/Utilities/ERAMajorants.lean:163` with field
     values `degree := 1`, `coefficient := 2`,
     `constant := 0`.
   - `def ERMor1.PolyBound.ofA_one_iter (r : ℕ)` at
     `GebLean/Utilities/ERAMajorants.lean:197` with
     `degree := 1`, `coefficient := 2 ^ r`,
     `constant := 2 ^ (r + 1) - 2`.
   - Both field tuples match spec §5 literally.
   - `git diff 829007cc..HEAD -- GebLean/Utilities/ERAMajorants.lean
     | grep -i ofa_two` returns nothing — no
     `ofA_two_iter` is shipped. Pass.

4. **Module docstring citations and polynomial-vs-tower split.**
   `GebLean/Utilities/ERAMajorants.lean:7-42` cites
   "Tourlakis 2018 page 22" (line 10),
   "master design §3.3" (line 37), and points at
   `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
   (line 40). The polynomial-vs-tower split paragraph at
   lines 19-33 explicitly documents the absence of
   `ofA_two_iter` and describes the downstream Nat-level
   consumer pattern (`tower_mono_right`, `tower_mono_left`,
   `self_le_tower`, `mul_tower_le_tower_add_two`,
   `tower_pow_le_tower_add_three`, fed to
   `simultaneousBoundedRec_interp_correct`). Pass.

5. **Per-entity docstrings carry §7 citations.**
   - `A_one` (line 48-49): "Tourlakis 2018 page 22",
     "Master design §3.3".
   - `interp_A_one` (line 62-64): "Tourlakis 2018 page 22,
     `A_1`", "Master design §3.3".
   - `A_one_iter` (line 72-74): "Tourlakis 2018 page 22
     iterated majorant `A_1^r`", "Master design §3.3".
   - `interp_A_one_iter` (line 84-87): "Tourlakis 2018
     page 22, `A_1^r` r-fold composition closed form",
     "Master design §3.3".
   - `A_two_iter` (line 128-133): "Tourlakis 2018 page 22
     iterated majorant `A_2^r`", "Tourlakis 2018 §0.1.0.17
     (c) `λx. 2^x ∈ ER`", "Master design §3.3".
   - `interp_A_two_iter` (line 143-146): "Tourlakis 2018
     page 22, `A_2^r = tower r x`", "Master design §3.3".
   - `ofA_one` (line 156-162): "Master design §3.3 amended
     polynomial-bound certification subsection".
   - `ofA_one_iter` (line 183-196): same. Pass.

6. **Index-module imports in case-insensitive alphabetical
   order.**
   - `GebLean.lean:148` adds `import GebLean.Utilities.ERAMajorants`
     immediately above `import GebLean.Utilities.ERArith`
     (line 149).
   - `GebLeanTests.lean:29` adds
     `import GebLeanTests.Utilities.ERAMajorants`
     immediately above `import GebLeanTests.Utilities.ERArith`
     (line 30).
   - In both files `ERAMajorants` correctly precedes
     `ERArith` (case-insensitive alphabetical:
     `eramajorants` < `erarith`). Pass.

## Cross-cutting checks

- **`lake build`**: clean, "Build completed successfully
  (1527 jobs)", no warnings or errors.
- **`lake test`**: clean, exit 0.
- **No `sorry`/`admit`**: `grep -E "\b(sorry|admit)\b"` over
  both new files finds no matches.
- **`markdownlint-cli2`**: 0 errors across the spec, plan,
  and 6 review documents touched in the step-3 range.
- **Banned words**: scanning code (`ERAMajorants.lean`,
  `GebLeanTests/Utilities/ERAMajorants.lean`) and commit
  messages with the full CLAUDE.md banned-word regex
  (`actually|fundamental|key|insight|core|advanced|complex|complicated|simple|advantage|benefit|important|challenge|yes|wait|hmm|careful|difficult|blocked|incomplete|future|issue|problem|block`)
  finds no matches. The only "sorry" hit on commit messages
  is the meta-statement "no sorry" in the task-10 verification
  message, which is the project-standard report phrasing.

## Items confirmed correct

- Definition order matches dependency order: `A_one` →
  `interp_A_one` → `A_one_iter` → `interp_A_one_iter` →
  `A_two_iter` → `interp_A_two_iter` →
  `PolyBound.ofA_one` → `PolyBound.ofA_one_iter`. Each
  `def` precedes its `@[simp]` interp lemma; each
  `PolyBound.of*` builder follows the corresponding interp
  lemma it routes through (`ofA_one` uses
  `interp_A_one`; `ofA_one_iter` uses `interp_A_one_iter`).
- The `namespace PolyBound` / `end PolyBound` pairs at
  lines 154/179 and 181/222 each balance independently.
  Re-opening the namespace between Task 7 and Task 8
  produced two well-formed pairs rather than nesting
  errors. The outer `namespace ERMor1` (line 46) /
  `end ERMor1` (line 224) and `namespace GebLean` (line 44)
  / `end GebLean` (line 226) brackets are also balanced.
- `A_two_iter` is implemented as a single-line alias
  (`:= ERMor1.towerER r`) per spec §3.3, not as a fresh
  composite. The interp lemma (line 147-152) routes through
  the existing `ERMor1.interp_towerER` lemma via
  `unfold A_two_iter; exact ERMor1.interp_towerER r ctx`
  rather than re-proving the closed form.
- The `ofA_one_iter` proof does not unfold the recursive
  definition of `A_one_iter` — it routes through the
  closed-form `interp_A_one_iter` simp lemma plus
  `Nat.mul_le_mul_left` + `omega`, matching the spec's
  proof outline.
- The test module's `#guard` selection respects the
  project ER-side `.interp` test discipline documented
  in user memory: only bprod-free composites at small
  inputs (`A_one`, `A_one_iter` at `r ≤ 2`,
  `A_two_iter` only at `r = 0`).
- The workstream document
  `.session/workstreams/er-ksim2-equiv-via-urm.md` is
  updated with the step-3 completion summary and the
  next-step pointer to step 4.

## Recommendation

approve.
