# Step 3 plan adversarial review — round 2

## Summary

Quick clean-bill-of-health pass over the round-1 fixes
landed in commit `25cd0a61`.  All four fixes (F1-F4) are
correctly applied and consistent with the current state
of `GebLean.lean` and `GebLeanTests.lean` on
`terence/develop`.  No new substantive issues were
introduced by the fixes.  No previously-missed
substantive issues were turned up by re-reading.

Recommendation: **approved**.

## Verification of round-1 fixes

### F1 (substantive) — import-position anchor

**Round-1 directive:** Replace "near
`ERSimultaneousBoundedRec`" with "immediately above
`ERArith`" in Plan §1.2 and §9.2.

**Current state:**

- Plan §1.2 line 203: "Add the new line **immediately
  above the existing `import GebLean.Utilities.ERArith`
  line** (case-insensitive alphabetical order:
  `ERAMajorants` < `ERArith` because `m` < `r`)".
- Plan §9.2 line 722: parallel rewording with
  `GebLeanTests.Utilities.ERArith`.
- `GebLean.lean` line 148 is `import
  GebLean.Utilities.ERArith` and `GebLeanTests.lean` line
  29 is `import GebLeanTests.Utilities.ERArith`, so the
  anchor lines exist as instructed.

Verified.

### F2 (minor) — Tasks 7 and 8 anchor rewording

**Round-1 directive:** Drop the inaccurate
"empirically verified during round-4 adversarial review"
annotation from Tasks 7 and 8; anchor instead to
`ofAddN`'s proof pattern.

**Current state:**

- Plan Task 7.1 lines 562-565: "The proof structure
  mirrors `def ERMor1.PolyBound.ofAddN` in
  `LawvereERPolynomialBound.lean`: simp through the
  constructor interp lemmas, introduce a
  `Finset.le_sup` hypothesis on `ctx 0`, close with
  `omega`."
- Plan Task 8.1 lines 638-641: identical anchor.
- The "empirically verified during round-4" claim
  remains only in Task 5 (line 434), where it is
  accurate (round-4 §"Empirical Lean verification of §4
  and §5 proofs" verified §4.2's proof, which Plan Task
  5 transcribes character-identically).

Verified.

### F3 (minor) — Task 10.7 reviewer brief

**Round-1 directive:** Inline the six §10 acceptance
criteria into the cycle-end-reviewer's brief, pick a
specific review skill, and name the diff range
explicitly.

**Current state:**

- Plan §10.7 lines 911-916 specify the dispatcher
  ("`superpowers:requesting-code-review` or
  `lean4:review`") and the diff range
  (`origin/terence/develop..HEAD`).
- Lines 921-944 enumerate six numbered items,
  organized as a slightly-different decomposition of
  spec §10 (sub-items of §10.1 split out, plus
  imports rolled into one combined item).  Lines
  945-951 add cross-cutting checks (`lake build` and
  `lake test` clean, `markdownlint-cli2` clean,
  banned-words clean).
- Lines 953-954 name the output document path
  `docs/research/2026-05-03-step-3-cycle-end-review.md`.

Verified.

### F4 (minor) — transitively-reachable imports note

**Round-1 directive:** Add a one-line note that
`LawvereERPolynomialBound` and `Utilities.Tower` are
imported directly by `ERAMajorants.lean` but reach
`GebLean.lean` transitively via existing entries.

**Current state:**

Plan §1.2 lines 212-216:

> Note: `Utilities/Tower.lean` and
> `LawvereERPolynomialBound` are imported directly by
> `ERAMajorants.lean` but are not listed in
> `GebLean.lean` (both are transitively reachable via
> existing entries).  No additional `GebLean.lean` lines
> are needed for this task.

Verified.

## Cross-checks for new issues introduced by the fixes

- **F1's rewording does not break the
  import-at-skeleton-creation discipline elsewhere.**
  Plan §"Import-at-skeleton-creation rule" lines 94-99
  still mandates the import landing in the same
  skeleton-creation commit, and §1.4's commit message
  references that rule.  Plan §9.6's commit message
  for the test-side counterpart references the same
  rule.  Both are unchanged by F1.

- **F3's brief is internally consistent with §10.3's
  checklist.**  §10.3 (lines 825-856) and §10.7
  (lines 921-944) ask for the same code-level
  conditions, decomposed slightly differently.  §10.3
  is task-oriented (open each file, check items);
  §10.7 is reviewer-oriented (verify against actual
  code).  The two are mutually consistent — if §10.3
  passes, §10.7's items 1-5 pass; §10.7 item 6
  enforces the alphabetical-order import discipline
  separately (verifying §10.3's plain-presence checks
  go further).

- **F2's anchor matches the actual `ofAddN` pattern.**
  Inspecting `GebLean/LawvereERPolynomialBound.lean`
  line 448-460: `ofAddN`'s `bounds` is exactly "simp
  only through the constructor interp lemmas;
  `Finset.le_sup (Finset.mem_univ _)` for each ctx
  index; close with omega".  Plan Tasks 7 and 8 use
  the more-verbose `Finset.le_sup (s := ...) (f := ...)
  (b := ...) (Finset.mem_univ _)` named-argument form
  instead of the bare `Finset.le_sup (Finset.mem_univ
  _)` form, but this is a stylistic difference, not a
  semantic one — both elaborate to the same proof
  term.  The anchor is informative ("simp + le_sup +
  omega" matches), even though the surface text
  differs.  Not a finding.

- **The `lake build` cache-bust commands consistently
  remove only the `ERAMajorants.olean` file.**  Plan
  §"Forced re-elaboration before commit" (lines
  101-114), Steps 1.3, 2.2, 3.2, 4.2, 5.2, 6.3, 7.2,
  8.2, 9.3, 9.5, 10.1 all consistently `rm -f` the
  expected `.olean`.  No drift was introduced.

## Pre-existing under-specification (non-blocking; inherited from spec §10)

Spec §10.2 mandates "the test file exists with the
`#guard`s from §6.1", but Plan §10.3 (line 825-856)
and §10.7 (lines 921-944) do not include an explicit
"verify the test file's `#guard` set matches §6.1"
check.  The closest checks are:

- §10.2 (line 820-823): runs `lake test` for clean
  output (catches missing-test-file via build error,
  not missing-#guard-content).
- §10.3 line 855-856: confirms
  `import GebLeanTests.Utilities.ERAMajorants` is
  registered.

This is inherited from spec §10's high-level
formulation; it was not introduced by the F3 rewording.
A fully-rigorous reviewer brief would add "verify the
`#guard`s in `GebLeanTests/Utilities/ERAMajorants.lean`
correspond to spec §6.1's list", but this is a polish
item, not blocking.  Flagged for the author's
discretion.

## Items checked and confirmed unchanged from round 1

- File paths (`GebLean/Utilities/ERAMajorants.lean`,
  `GebLeanTests/Utilities/ERAMajorants.lean`).
- Task ordering and per-task dependency soundness.
- `PolyBound` field signature alignment.
- `Fin 1` index convention.
- Banned-word discipline.
- Workstream entry format in §10.4.
- Out-of-scope list in §"Out of scope".

## Recommendation

**Approved.**  The plan is ready for execution.  The
single inherited under-specification (spec §10.2's
test-content check not explicitly enumerated in the
reviewer brief) is non-blocking and pre-dates the
plan; it can be addressed at the cycle-end review
step itself if desired, since the reviewer subagent
will read the plan and the spec together.
