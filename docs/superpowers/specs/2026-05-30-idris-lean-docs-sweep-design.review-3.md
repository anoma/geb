# Adversarial review 3: Idris/Lean docs sweep design

## Summary verdict

The spec has **CONVERGED** and is ready for the plan stage. All
round-2 fixes are present, sound, and mutually consistent: the
coverage check is now two explicit assertions (totality via
set-equality, disjointness via per-document occurrence count with
load-bearing within-file dedup) that together guarantee a total,
disjoint partition; every stale numeric count is gone (no "47",
"seven", "eleven", "80", "215" survives, and the live counts 77 /
214 / 51 / "ten Lean, nine Idris" all match the repository); the
`geb-idris/README.md` fate is now coherently "left in place, area 7
summarises and links, no root-README change on its account"; index
slimming explicitly preserves the framing paragraph and the
Directory-structure section without contradicting the Target-layout
spine description; and the explicit-naming-overrides-tie-break rule
plus the expanded overlap list contain no module that is both named
in one area and pre-resolved into another. The doctoc TOC matches the
headers exactly. I re-ran the repo counts and the round-2 fix
verifications and found no remaining real defect. The two notes below
are trivial polish, not gates.

## Verification performed

- Numeric grep across the whole spec for `47`, `51`, `seven`,
  `eleven`, `nine`, `ten`, `214`, `215`, `80`, `77`, `69`, `52`: only
  the intended live counts appear. `51` at lines 49, 110, 164, 327;
  `77` at 40, 224, 355; `214` at 45, 349; "ten Lean / nine Idris" at
  450. No stale survivor in intro, current-state, area lists, risks,
  or target-layout.
- Repo recount: `find geb-idris/src -name '*.idr' | grep -v /Test/` =
  77; `find geb-lean/GebLean -name '*.lean'` = 214;
  `find geb-lean/docs -maxdepth 1 -name '*.md'` = 52 (= 51 notes +
  `index.md`); `find geb-lean/GebLean/Utilities -name '*.lean'` = 51.
  All match the spec.
- Overlap modules `SlicePolyDifunc.idr`, `MLBundleCat.idr`,
  `MLDirichCat.idr`, `MLTwistPair.idr` all exist under
  `geb-idris/src/LanguageDef/` and are now in the pre-resolved overlap
  list (lines 232-233), all routed to area 3 by dominant
  `InternalCat` import.
- Doctoc TOC (lines 6-23, 18 entries) compared slug-by-slug to the
  18 `##`/`###` headers: exact match, correct order.

## Round-2 fix audit

1. **Coverage check split (round-2 MAJOR).** Lines 369-387 now state
   two assertions. Assertion 1 (totality and no stragglers): the set
   of distinct linked targets equals the enumerated source set.
   Assertion 2 (disjointness): dedup link occurrences within each area
   doc, then count distinct area docs per target, fail on count > 1.
   Together these are logically sufficient for a total disjoint
   partition: assertion 1 forces every source file to be linked from
   at least one area doc and nothing else to be linked; assertion 2
   forces each target into at most one area doc; the conjunction gives
   "exactly one area doc per source file." The within-file dedup is
   correctly identified as load-bearing (a file may legitimately be
   linked in both **Modules** and **Alternative formulations** of one
   doc) and does not weaken the cross-document count. No contradiction
   with the prose-only-area tolerance: assertion 1 ranges over source
   files and linked targets, so an area doc that contributes zero
   links is invisible to both sides of the set-equality and to the
   per-target count. Sound.

2. **Numeric consistency.** Verified clean above. Holds.

3. **`geb-idris/README.md` fate.** Area 7 (lines 206-213) says the
   README is left in place, the area doc is a prose summary linking to
   it, the area owns no `.idr` file, and "no root `README.md` link or
   description changes on its account." This is consistent with (a)
   the Goal section (lines 82-83: root README links "adjusted only as
   needed"), (b) the coverage rule (lines 384-387: prose-only area
   contributes no link and is expected), and (c) Process step 7 (line
   441: adjust root README links "if any target moved" — a no-op for
   area 7 since the README does not move). No internal tension.

4. **Index slimming.** Existing-material policy (lines 319-326)
   preserves the framing paragraph and `## Directory structure`
   section, compressing only per-workstream detail. Target layout
   (lines 119-121) describes the slimmed index as "spine: short
   identity + one paragraph and link per area; a coverage note." These
   do not contradict: the framing paragraph is the "short identity,"
   the Directory-structure section is part of the retained spine, and
   "one paragraph + link per area" describes exactly the compressed
   per-workstream detail. The Target-layout comment is a terse summary
   of the fuller policy, not a competing instruction.

5. **Explicit-naming-overrides-tie-break + overlap list.** Lines
   224-233 state that explicit naming in an area seed overrides the
   dominant-import tie-break (so `Figures`/`Telescope` stay in area 6),
   and list the pre-resolved overlaps (all to area 3). Cross-checked:
   none of the overlap-list modules (`PolyProfunctor`, `PolyProfEnd`,
   `PolyDifunc`, `SlicePolyDifunc`, `DiPolyFunc`, `MLDiPolyFunc`,
   `SlPolyIntCat`, `MLQuiv*`, `MLBundleCat`/`MLDirichCat`/`MLTwistPair`)
   is also named in another area's seed. `Figures`/`Telescope` are
   named only in area 6 and are not in the overlap list. No module is
   simultaneously named in one area and pre-resolved into another. No
   contradiction.

## Process-step coverage of body promises

- Calibration area doc (line 264): owned by the plan ("The plan
  includes one fully-written area document as a calibration reference
  before the rest are authored"), executed inside Process steps 3
  (Idris authoring) and 5 (Lean authoring). Covered, though not
  separately enumerated — see finding 1 below.
- Dead-note sign-off (lines 335-336): Process step 4 (line 437-438)
  explicitly records dead-note candidates for sign-off. Covered.
- Parallel-formulation seed list (lines 293, 307): the plan carries
  and extends it; Process step 6 records clusters and writes
  descriptions. Covered.

## Findings

1. **TRIVIAL (polish, non-gating) — the calibration area doc is a
   plan artifact, not a separately visible Process step.** The body
   (line 264) places the calibration reference "in the plan ... before
   the rest are authored," and Process steps 3 and 5 author the area
   docs, so the obligation is discharged. But a reader skimming the
   8-step Process list will not see the "write the calibration doc
   first" sequencing called out, and it is the one piece of authoring
   discipline most easily skipped. Evidence: line 264 vs Process steps
   3 and 5 (lines 434-439). Fix (optional): add a half-clause to step
   3 or 5, e.g. "(authoring the calibration reference doc first)," so
   the sequencing is visible at the process level. Not required for
   convergence.

2. **TRIVIAL (polish, non-gating) — Process step 7 is a tolerated
   no-op given the round-3 README/index decisions.** With
   `geb-idris/README.md` left in place and both indexes slimmed in
   place (no relocation), no link *target* actually moves, so step 7
   ("Adjust the root `README.md` links if any target moved") will
   typically do nothing. This is correct and safe (the step is
   conditional), but a plan author may wonder why it is listed. Fix
   (optional): note that step 7 is a verification step that confirms no
   root-README link is stale, expected to be a no-op under the current
   layout decisions. Not required for convergence.

## Counts by severity

- BLOCKER: 0
- MAJOR: 0
- MINOR: 0
- TRIVIAL: 2 (optional polish, non-gating)
