# Adversarial review 2: Idris/Lean docs sweep design

## Summary verdict

The three round-1 BLOCKERs are genuinely fixed: the Idris area list
now has 9 seeds with an explicit "seed, not claimed-total" framing
plus a "plan begins from the full enumeration" clause, so the
homelessness test passes (every one of the 77 non-test modules lands
in exactly one area under the dominant-import tie-break); the Lean
CSLib "area" is demoted to a cross-cutting note and the partition is
scoped to `.lean` files; and the coverage check now pins one relative
Markdown-link citation syntax and scopes the source set. The spec
otherwise holds together. What remains are smaller but real problems:
two leftover numeric inconsistencies the round-1 fixes did not
propagate ("47" loose notes vs the corrected "51"; Risks still says
"seven Idris areas" / "eleven Lean areas"); a genuine mechanism gap
where the stated coverage check ("assert set-equality") cannot detect
the multi-document duplication its own failure clause promises to
catch; an under-specified fate for `geb-idris/README.md` when its
circuit-frontend content is "refiled"; and a slimming risk to the
index-level topological/directory-structure prose the user values. No
new BLOCKERs. The set-equality-vs-disjointness gap is the one that
would actually let a defect through the mechanical gate, so it is the
most important finding.

## Findings

1. **MAJOR — the coverage check's stated mechanism ("assert
   set-equality") cannot detect the cross-document duplication its
   own failure clause promises to catch.** The spec says the script
   "extracts every source-file link target from `areas/*.md` only,
   normalises the relative paths, and asserts set-equality" (lines
   350-354), and then that the task "fails on any source file that is
   unlinked or linked from more than one area document" (line 354).
   Set-equality between the flat set of linked targets and the source
   set checks only totality (no file unlinked) and that nothing
   outside the source set is linked. It is blind to multiplicity: a
   file linked from two different area docs still appears once in the
   extracted *set*, so set-equality passes while the disjointness
   guarantee is violated. Detecting "linked from more than one area
   document" requires grouping link occurrences by source document
   (e.g. counting distinct `areas/*.md` files each target appears in
   and failing on count > 1), which a set-equality assertion does not
   do. Evidence: the two clauses are in tension on lines 350-354 of
   the spec. Fix: state the check as two assertions — (a) the *set* of
   linked targets equals the source set (totality + no stragglers),
   and (b) no target appears in more than one `areas/*.md` file
   (disjointness), computed by deduplicating within each file then
   counting across files. The brief's framing is right: the predicate
   is "linked from more than one area document," not "more than once
   total" (a file may legitimately be linked twice inside one area
   doc, e.g. in **Modules** and again in **Alternative
   formulations**), so the within-file dedup is load-bearing.

2. **MINOR — leftover "47" loose-note count contradicts the
   corrected "51".** Round-1 finding 10 corrected the loose-note count
   to 51 (52 top-level `*.md` minus `index.md`), and the
   Existing-material policy now says "The 51 loose `docs/*.md` notes
   (top-level, excluding `index.md`)" (line 311). But two earlier
   passages still say 47: line 49 ("47 loose `docs/*.md` files") and
   line 110 ("47 loose `*.md` notes"). Evidence:
   `find geb-lean/docs -maxdepth 1 -name '*.md'` = 52, so the notes
   count (excluding `index.md`) is 51; lines 49, 110, and 311 of the
   spec disagree among themselves. Fix: change both "47" occurrences
   to 51 (or, on line 49, "51 loose notes plus a stale `index.md`
   reference set") so all three agree.

3. **MINOR — Risks section still states the pre-fix area counts
   ("seven Idris areas" and "eleven Lean areas").** The area
   decomposition now lists 9 Idris areas (lines 191-215) and 10
   numbered Lean areas (lines 146-164), but the Risks "Scale" bullet
   (line 417) still reads "About eleven Lean areas and seven Idris
   areas." This is the stale count from before the round-1 partition
   fixes. Evidence: spec line 417 vs the 9 Idris / 10 Lean area lists.
   Fix: update line 417 to "about ten Lean areas and nine Idris areas"
   (and note the numbers are seeds the plan may adjust, consistent
   with lines 136-142).

4. **MINOR — the fate of `geb-idris/README.md` is left
   under-specified, and its content move is not sequenced against the
   root-README touch-up.** Idris area 7 (lines 206-207) refiles the
   circuit-frontend content "as one area document rather than the
   subproject front page," and the Goal restates this. But the spec
   never says what happens to `geb-idris/README.md` itself: is it
   gutted, replaced with a pointer, or left in place with its content
   also copied? The root `README.md` links to it at line 33 with the
   descriptive text "Geb as a circuit frontend" and the Idris
   `docs/index.md` would naturally cite it too. If the content is
   *moved* into an area doc, the README front page and those two
   descriptions become stale; if it is *copied*, the spec's
   "no-duplication" spirit is violated and there are now two homes for
   the same prose. Process step 7 ("adjust the root README links if
   any target moved") only covers link *targets* moving, not a
   description going stale when a target's *content* is hollowed out.
   Evidence: `geb-idris/README.md` is a 213-line circuit-frontend
   narrative; root `README.md` line 33 links to it by that
   description; spec area 7 says "rather than the subproject front
   page" without saying what the front page becomes. Fix: state
   explicitly whether `geb-idris/README.md` is left as-is (and area 7
   merely *summarises and links to* it, i.e. it is not a partition
   member with source files but a pointer area) or is replaced by a
   short pointer to the new area doc; if the latter, add the root
   README description update to the touch-up list.

5. **MINOR — "slim the Lean index" risks dropping the index-level
   topological narrative and the Directory-structure section the user
   values.** The existing `geb-lean/docs/index.md` opens with a
   framing paragraph (its lines 20-29) describing it as "a directory
   layout for the source tree" combined with "a topological narrative
   of the formalised mathematical content," and a dedicated
   `## Directory structure` section (its lines 31-42). The spec's
   slimming instruction is "each workstream's prose is compressed to a
   short paragraph plus a link to its area document" (lines 308-309)
   and the Target layout describes the slimmed index as "spine: short
   identity + one paragraph and link per area; a coverage note" (lines
   119-121). Neither passage mentions preserving the Directory-
   structure section or the cross-area topological ordering (the
   sequence in which workstreams build on one another), which is an
   index-level property that per-area **Dependencies** sections do not
   reconstruct. Evidence: index.md lines 20-42 carry the topology and
   directory-layout prose; the spec's slimming text addresses only
   per-workstream paragraphs. Fix: state that slimming preserves (a)
   the index's framing/topological-ordering paragraph and (b) the
   Directory-structure section, compressing only the per-workstream
   detail that migrates into area docs.

6. **MINOR — several Idris modules match two area seeds by name and
   are not in the pre-resolution list, though none is genuinely
   homeless.** The homelessness re-test passes: all 77 non-test
   modules land somewhere (the "seed, not total" framing at lines
   136-142 plus the dominant-import tie-break cover the residue). But
   beyond the overlaps the spec pre-resolves (lines 219-223:
   `PolyProfunctor`, `PolyProfEnd`, `PolyDifunc`, `DiPolyFunc`,
   `MLDiPolyFunc`, `SlPolyIntCat`, the `MLQuiv*` family), a few more
   match two seeds and are not called out: `SlicePolyDifunc` matches
   both the area-2 `*Poly*`/slice wildcard and the area-3 `*Difunc`
   wildcard; `MLBundleCat`, `MLDirichCat`, and `MLTwistPair` are
   `ML*`-prefixed but appear in no area's example list or wildcard at
   all (they import `InternalCat` dominantly, so the tie-break lands
   them in area 3, but no seed names them); `Figures` and `Telescope`
   are named in area 6 yet import `PolyCat`/`SlicePolyCat`/`PolyCat`
   dominantly, so the dominant-import tie-break would contradict their
   explicit area-6 placement. Evidence:
   `grep -E '^import public' MLBundleCat.idr` imports `InternalCat`,
   `IntEFamCat`, `IntTwistedArrowCat`, `IntParamCat`, `IntArena`,
   `PolyCat`; `Telescope.idr` imports `InternalCat`, `PolyCat`,
   `SlicePolyCat`, `PolySliceCat`. Fix: note in the spec that for
   modules explicitly named in an area seed, the explicit naming
   overrides the dominant-import tie-break (so `Figures`/`Telescope`
   stay in area 6), and add `SlicePolyDifunc` and the `MLBundleCat` /
   `MLDirichCat` / `MLTwistPair` trio to the pre-resolved overlap
   list (all to area 3 by dominant import) so the plan's matrix has no
   silent tie-breaks.

7. **MINOR — the Idris circuit-frontend area (area 7) is the only
   partition member with no source `.idr` file; confirm the coverage
   check tolerates a source-link-free area doc.** Because the Idris
   coverage check enumerates only `.idr` files (lines 337-339) and
   extracts source links from `areas/*.md`, an area doc with zero
   source links is fine for set-equality (it contributes nothing to
   the linked set). This is consistent, but the spec never states that
   a module-less area is expected; a reader implementing the check
   might add a "every area doc links at least one source" assertion
   and break area 7. Evidence: area 7 (lines 206-207) owns no module;
   the aggregator clause (lines 256-260) handles zero-*theorem* docs
   but not zero-*source-link* docs. Fix: one sentence noting that area
   7 is a prose-only area with no source-file links, and that the
   coverage check does not require every area doc to contribute a
   link.

## Round-1 fix verification (confirmed against the repo)

- Idris partition totality (round-1 BLOCKER 1): re-ran the
  homelessness test over the real 77-file list
  (`find geb-idris/src -name '*.idr' | grep -v /Test/` = 77). With the
  9 seeds plus the "plan enumerates everything / dominant-import
  tie-break" clauses, every previously-homeless module now has a home:
  `Atom`, `Logic`, `QType`, `RQFin`, `RefinedADT`, `FullLanguageDef`,
  `ComputationalEffects`, `Embedded` -> area 9; `Quiver`, `FinCat`,
  `FinCatPRA`, `Adjunctions`, `UniversalCategory`, `DiagramCat`,
  `SpanCospan`, `HelixCat`, `RopeCat`, `NatPrefixCat` -> area 8. The
  `Int*Cat` family (`IntArena`, `IntDepFamCat`, `IntDisheafCat`,
  `IntECofamCat`, `IntEFamCat`, `IntFactCat`, `IntFactCatFunc`,
  `IntParamCat`, `IntTwistedArrowCat`, `IntUCofamCat`, `IntUFamCat`)
  and `InternalHigherCat` import `InternalCat` dominantly -> area 3.
  `HigherPolyCat`, `GenPolyFunc`, `PolyIndTypes` import `PolyCat`/
  slice machinery -> area 2. `Theories` imports `RefinedADT` -> area 4
  (named there) or 9 by import; named in area 4 wins. `Nock`,
  `BinTree` -> area 5. `MLDirichCat`, `MLTwistPair` -> area 3 (see
  finding 6). No file is genuinely homeless. Fix holds.

- Lean CSLib demotion (round-1 BLOCKER 2): confirmed
  `geb-lean/docs/index.md` `## CSLib integration` (its line 434) names
  config files only; the spec now treats CSLib as a cross-cutting note
  (lines 166-171), not a partition member. Fix holds.

- Coverage citation syntax (round-1 BLOCKER 3): confirmed
  `index.md` has 0 Markdown links to `.lean`
  (`grep -cE '\]\([^)]*\.lean' index.md` = 0) and 149 backtick
  mentions; the spec now pins relative Markdown links in area docs
  only and excludes the slimmed index from the scan (lines 341-347).
  Path normalisation is uniform and trap-free: from `docs/areas/` both
  the root aggregator and `GebLean/**` targets resolve with a single
  `../../` prefix (`../../GebLean.lean`,
  `../../GebLean/PLang/CatJudgments.lean`), confirmed via
  `os.path.relpath`; no `..`-escape or depth mismatch. The "prose
  mention without a link fails coverage" risk is real but is the
  intended behaviour (the pinned syntax *is* a link), and the spec
  already says backtick-only is not used in area docs. Fix holds.

- Lean source-set count: confirmed `find geb-lean/GebLean -name
  '*.lean'` = 214, plus the root `geb-lean/GebLean.lean` = 215 total;
  `geb-lean/GebLeanTests.lean` and `GebLeanTests/` (49 files) are
  excluded. The spec is internally consistent: it says "214 files
  under `GebLean/` plus the one root aggregator" (lines 45-46, 332-334)
  and never asserts a bare "214 = whole source set." No leftover "214"
  usage contradicts the new text. Fix holds.

- Aggregator clause vs coverage: confirmed the four named aggregators
  exist (`GebLean.lean`, `GebLean/PLang.lean`, `GebLean/Utilities.lean`,
  `GebLean/LawvereERKSim.lean`). The clause (lines 256-260) says they
  count for coverage but carry no theorem list; the coverage check
  keys on links, not on theorem lists, so an aggregator with a source
  link but no declarations passes. Consistent.

- Doctoc TOC: the spec's own TOC (lines 6-23) matches its `##`/`###`
  headers exactly (18 headers, all present). Clean.

## Counts by severity

- BLOCKER: 0
- MAJOR: 1
- MINOR: 6
