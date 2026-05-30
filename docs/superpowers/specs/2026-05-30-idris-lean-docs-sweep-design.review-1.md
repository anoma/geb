# Adversarial review 1: Idris/Lean docs sweep design

## Summary verdict

The spec is well-motivated and its high-level claims (Lean 214
files, Lean index 21 KB, 69 unlisted Lean files, 47/52 loose notes,
existing area clusters) largely check out against the repository.
But it cannot be executed as written. Two of its load-bearing
guarantees are false in the repo as it stands: the proposed
partitions are neither total (the Idris 7-area scheme leaves roughly
18 foundational modules homeless; the Lean "CSLib integration" area
contains zero source files) nor mechanically checkable as described
(the coverage one-liner extracts "source paths linked from area
docs," but the established Lean index convention cites sources in
backtick code spans, not links, while the Idris index uses Markdown
links — so the two trees disagree and the naive check breaks). The
"parallel formulations" element is under-specified for two authors to
execute comparably. These are fixable, but the spec must (a) make
both partitions explicitly total over a defined file set, (b) pin one
source-citation syntax and write the check against it, and (c) sharpen
the parallel-formulation and overview-depth definitions. Findings
below, ranked by severity.

## Findings

1. **BLOCKER — the Idris 7-area partition is not total; ~18
   modules are homeless.** The spec asserts "Every non-test Idris
   source module is named in exactly one area document" and that the
   7 areas are the "agreed starting decomposition," with only the plan
   to "confirm." But the 7 area descriptions, read literally
   (Library; Polynomial functors; Internal categories and
   profunctors; The Geb language; Recursion and compilation targets;
   Metaprogramming and syntax; Circuit frontend), have no bucket for a
   large set of foundational category-theory modules that import only
   `Library.IdrisUtils`/`IdrisCategories` and belong to none of the
   named clusters. Verified homeless modules under
   `geb-idris/src/LanguageDef/`:
   `Atom.idr`, `Logic.idr`, `QType.idr`, `RQFin.idr`,
   `RefinedADT.idr`, `FullLanguageDef.idr` (imports `RefinedADT`),
   `SpanCospan.idr`, `ComputationalEffects.idr`, `Embedded.idr`
   (imports `ComputationalEffects`), `HelixCat.idr`, `RopeCat.idr`,
   `DiagramCat.idr`, `NatPrefixCat.idr`, `Adjunctions.idr`,
   `FinCat.idr`, `FinCatPRA.idr`, `Quiver.idr`,
   `UniversalCategory.idr`. That is 18 modules with no area. Of the 77
   non-test modules, only 22 are named explicitly in the area
   descriptions; of the remaining 55, the `*Poly*`, `Int*Cat`, `ML*`,
   and `*Profunctor` wildcards absorb most, but the 18 above are not
   covered by any wildcard or example.

   Evidence: `find geb-idris/src -name '*.idr' | grep -v /Test/`
   yields 77 files; module headers confirm the orphans import only
   `Library.*`. Suggested fix: add at least one "Logic, refinement,
   and miscellaneous category constructions" Idris area (or split into
   a "foundational categories" and a "logic/refinement types" area),
   and have the spec state that the named 7 areas are a partial seed,
   not a claimed-total list — and require the plan to begin from the
   full enumerated 77-file list, not from the area names.

2. **BLOCKER — the Lean 11-area partition is not a partition of the
   214 source files: area 11 (CSLib integration) contains zero
   source files.** The spec reuses the `index.md` workstreams as the
   area list and requires each area document to give "a per-module
   bullet naming the main definitions and theorems ... with a link to
   its source," with "every non-test Lean source file ... in exactly
   one area document." But the existing `index.md` "CSLib integration"
   section lists no `.lean` files at all — its "Source-tree paths" are
   `lakefile.toml`, `lake-manifest.json`, `.claude/rules/lean-coding.md`,
   and `CLAUDE.md`. So as a member of a partition of the 214 source
   files, area 11 is empty, and the config files it does describe are
   not source files and have no home in the "every source file in
   exactly one area" scheme.

   Evidence: `geb-lean/docs/index.md` lines 434-453 (the CSLib
   section) name only config files; `grep -rl CSLib geb-lean/GebLean`
   shows CSLib is *used* by `LawvereERKSim*` and
   `Utilities/ZeroTestURM.lean`, which already belong to area 8 / area
   10. Suggested fix: demote CSLib from a top-level area to a
   cross-cutting "Pointers"/infrastructure note (it documents
   dependencies, not source modules), and state explicitly that the
   coverage partition ranges over `.lean` files only, with the CSLib
   integration prose attached to whichever area it most informs.

3. **BLOCKER — the coverage check is not mechanizable as
   described, because the two indexes use different and
   non-link source-citation syntaxes.** The spec says the check
   "extracts every source path *linked* from the area documents" and
   "asserts the two sets are equal." But the established Lean
   `index.md` convention cites sources as backtick code spans
   (`` `GebLean/Foo.lean` ``), not Markdown links: a grep finds 149
   backtick `.lean` mentions and 0 Markdown links to `.lean`. The
   Idris `index.md`, by contrast, uses real Markdown links
   (`[`geb-syllabus.md`](geb-syllabus.md)`). So "linked" is wrong for
   Lean and right for Idris, and a single extraction regex cannot
   serve both. Worse, the spec also says the slimmed Lean `index.md`
   keeps source pointers and the spec's own area docs will "link to
   the source" — meaning sources are cited from *both* the index and
   the area docs, so a set-equality check that scans "the area
   documents" must define precisely which files it scans and must not
   double-count the index.

   Evidence: a grep for Markdown links to `.lean`
   (`\]\([^)]*\.lean\)`) in `geb-lean/docs/index.md` returns nothing,
   while a grep for backtick-wrapped `.lean` mentions returns 149; the
   Idris index uses `[...](...)` links. Suggested
   fix: pin a single citation syntax for area docs (e.g. relative
   Markdown link with the path as the visible text), write the
   extraction regex against exactly that syntax, scope the source
   enumeration to `geb-lean/GebLean/**/*.lean` and
   `geb-idris/src/**/*.idr` minus tests (NOT a bare
   `find geb-lean -name '*.lean'`, which would sweep in thousands of
   `.lake/packages/**` dependency files), and state whether the index
   is included in or excluded from the scanned set.

4. **MAJOR — "214 files" omits real source files outside
   `GebLean/`; coverage scope is under-defined.** The spec equates
   the Lean codebase with "`geb-lean/GebLean/`: 214 files" and the
   coverage rule with "every non-test Lean source file." But
   `geb-lean/GebLean.lean` (182-line root aggregator) and
   `geb-lean/GebLeanTests.lean` sit *outside* `GebLean/`.
   `find geb-lean/GebLean -name '*.lean'` is exactly 214, confirming
   the root `GebLean.lean` is not counted. If "source file" means all
   non-test `.lean`, the count is 215 and `GebLean.lean` needs a home;
   if it means "under `GebLean/`," say so. Relatedly, the per-directory
   aggregator/index modules — `GebLean.lean`, `GebLean/PLang.lean`
   (21 lines), `GebLean/Utilities.lean` (41 lines),
   `GebLean/LawvereERKSim.lean` (re-export) — are pure `import`
   re-exports with no "main definitions and theorems," so the
   per-module template ("naming the main definitions and theorems")
   does not fit them. Suggested fix: define the source set precisely,
   decide whether `GebLean.lean` is in scope, and add a template
   clause for re-export/index modules (document them as
   aggregators, one line, no theorem list).

5. **MAJOR — "PLang" subdirectory is invisible in the Lean area
   names, risking a coverage gap.** `geb-lean/GebLean/PLang/` holds
   14 files; the spec's 11 area names never mention PLang. In fact the
   existing index distributes PLang files across areas (CatJudgment*
   into area 2, TreeCalc* into area 7), so coverage is achievable —
   but the spec gives no signal of this, and `GebLean/PLang.lean` and
   `GebLean/PLang/CatJudgmentAdjunction.lean` are among the 69 files
   the index does not currently mention. An author working only from
   the spec's area list could leave the PLang subtree partly
   unassigned. Evidence:
   `find geb-lean/GebLean/PLang -name '*.lean'` = 14;
   `GebLean/PLang/CatJudgmentAdjunction.lean` appears in the
   "unmentioned" set. Suggested fix: have the spec note the PLang and
   Utilities subdirectories explicitly and which areas absorb them.

6. **MAJOR — Idris file count is wrong (~80 vs actual 77) and the
   two extra Test roots are not addressed.** The spec says "roughly 80
   non-test modules" (and Risks says "seven Idris areas"); the actual
   non-test count is 77. More importantly, the spec's test-exclusion
   rule for coverage names only `*/Test/*` and `GebLeanTests/`. The
   Idris tree has tests in three different roots:
   `geb-idris/src/LanguageDef/Test/`,
   `geb-idris/src/Library/Test/`, plus the singletons
   `geb-idris/src/Executable/Test/Main.idr` and
   `geb-idris/src/Test/TestLibrary.idr`. The glob `*/Test/*` does
   catch all four roots, so the mechanism survives — but the spec
   never states the Idris exclusion glob (it only gives Lean's), and
   the `Executable/` and top-level `Test/` directories are exactly the
   edge cases the brief flags. Suggested fix: state the Idris coverage
   command explicitly (enumerate `geb-idris/src/**/*.idr`, exclude
   `**/Test/**`), name `Executable/Test/Main.idr` and
   `Test/TestLibrary.idr` as excluded, and correct "~80" to 77.

7. **MAJOR — "overview depth" is not pinned sharply enough for two
   authors to converge.** The template asks for "the main definitions
   and theorems (the reasons the module exists, not the intermediate
   results)" but gives no rule for how many bullets a module gets, how
   long a per-module subsection may run, or how to decide what counts
   as a "reason the module exists" versus an "intermediate result."
   For a 51-file area (`GebLean/Utilities/`) versus a 3-file area
   (Recursion/compilation), "scaled to the area's size" is the only
   guidance, which two authors will read very differently. Evidence:
   `GebLean/Utilities/` has 51 files; the Lean areas range from 3 to
   50+ modules. Suggested fix: give a concrete budget (e.g. one to
   three sentences per module; name at most the 1-3 headline
   declarations; total area doc target length), and include one fully
   worked example area doc in the plan as the calibration reference.

8. **MAJOR — the new Idris docs and root README get no CI lint
   coverage, and the "project configuration" is Lean-scoped.** The
   spec requires all new/edited Markdown to be "markdownlint-clean
   under the project configuration," but CI
   (`.github/workflows/markdown-lint.yml`) lints only
   `geb-lean/**/*.md`, and the only config is
   `geb-lean/.markdownlint-cli2.jsonc`. So every `geb-idris/docs/**`
   file this sweep authors — the Idris index and all Idris area
   docs — is outside CI enforcement, and "the project configuration"
   does not unambiguously apply to the Idris tree. The predecessor
   spec already flagged extending parent-level lint coverage as an
   explicit out-of-scope follow-up. Suggested fix: state that Idris
   docs are linted locally against `geb-lean/.markdownlint-cli2.jsonc`
   (naming the path), acknowledge they are not CI-gated, and either
   pull CI extension in or restate it as a named follow-up.

9. **MAJOR — "parallel formulations" detection is too hand-wavy to
   execute repeatably.** The element relies on an author noticing
   "multiple modules whose central definitions or theorems target the
   same mathematical object or universal property," recorded
   "best-effort." There is no enumeration procedure, no definition of
   "same mathematical object" operationally, and the one named example
   (more than one Lean formulation of the `Cat` vs (co)presheaf
   adjunction from `CategoryJudgments.lean`) is not tied to specific
   modules. Two authors will produce different cluster lists, and the
   acceptance criteria do not test this at all (the coverage check
   does not verify parallel-formulation completeness). The repo
   visibly contains versioned re-formulations
   (`LawvereNatBT.lean` vs `LawvereNatBTV2.lean` and the `*V20`/`*V2`
   families; `LawvereKSimER.lean` vs `LawvereKSimERDirect.lean`;
   `PLang/plang-category-judgments-old.md` vs the non-old note) that
   are obvious candidates but unmentioned. Suggested fix: either (a)
   downgrade parallel-formulation detection to an explicitly
   best-effort, non-acceptance-gated "note what you happen to find"
   clause, or (b) make it executable by listing seed clusters in the
   plan (e.g. the V1/V2/V20 Lawvere families, KSimER vs KSimERDirect)
   and defining "parallel formulation" as "two modules whose headline
   `def`/`theorem` carry the same informal statement."

10. **MINOR — `geb-lean/docs` subdirectory inventory in the spec is
    incomplete and the "47 loose notes" count is approximate.** The
    spec says 47 loose `docs/*.md` notes and lists subdirs
    `research/`, `plans/`, `superpowers/`. Actual top-level
    `geb-lean/docs/*.md` count is 52 (51 notes plus `index.md`);
    there is also a `.claude/` subdirectory under `geb-lean/docs/` not
    mentioned. The existing `research/` already holds 39 files (prior
    adversarial reviews), so relocating 51 loose notes into it will
    mix narrative research notes with process artifacts. Evidence:
    `find geb-lean/docs -maxdepth 1 -name '*.md'` = 52;
    `find geb-lean/docs/research -type f` = 39;
    `geb-lean/docs/.claude/` exists. Suggested fix: correct the count,
    note `.claude/` is left in place, and decide whether mixing
    relocated narrative notes with existing process artifacts in
    `research/` is intended or whether a distinct destination is
    wanted.

11. **MINOR — `index.md` already links sources both ways, so
    "slimming" it could orphan files the coverage check then flags.**
    The spec slims `index.md` to "a short paragraph plus a link to its
    area document," moving per-module detail into area docs. If the
    coverage check scans area docs only, that is fine — but the spec
    elsewhere implies the index "continues to reach everything." The
    interaction between "index is slimmed (loses per-file citations)"
    and "coverage check over area docs" needs to be stated so the
    slimming does not race the check. Suggested fix: state that after
    slimming, the index cites only area docs (no per-file `.lean`
    citations), and that the coverage check's source-citation scan
    runs over `areas/*.md` exclusively.

12. **MINOR — multi-home ambiguities in the Idris Poly vs
    Internal split are real and unaddressed.** Several modules could
    sit in either "Polynomial functors" or "Internal categories and
    profunctors": `MLDiPolyFunc.idr`, `DiPolyFunc.idr`,
    `PolyProfunctor.idr`, `PolyProfEnd.idr`, `PolyDifunc.idr`,
    `SlPolyIntCat.idr` (Sl-Poly *Int*-Cat), and the `MLQuiv*` family
    (quiver-flavored but Poly-adjacent). The spec's disjointness
    guarantee depends on resolving these, but the area descriptions
    overlap ("`*Poly*` modules" in area 2 vs "`*Profunctor`" in area
    3, while `PolyProfunctor` matches both). Suggested fix: add a tie-
    break rule (e.g. assign by primary import / dominant namespace)
    and pre-resolve the named overlaps in the plan's matrix.

13. **MINOR — Process claims "at least three adversarial-review
    rounds" for the spec but the existing task list shows this is
    review round 1 only; ensure the gate is actually met before
    planning.** Not a defect in the document's content, but the
    spec's Process section asserts a property of its own lifecycle
    that the executor must enforce. Suggested fix: none to the text;
    flag for the author to run the remaining rounds before handing to
    the plan stage, per the project's "adversarial review before
    user-review handoff" rule.
