# Adversarial review 5: Verso ramified-recurrence manual design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round and protocol](#round-and-protocol)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Findings against the review artefacts](#findings-against-the-review-artefacts)
- [Verified without defect](#verified-without-defect)
- [Convergence](#convergence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Round and protocol

Round 5, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. Two fresh `Agent` invocations, one on
external and repository fact verification, one on internal
consistency, realizability, scope, and project-rule compliance.
Findings are deduplicated across both and categorised per
`docs/process.md` § Defect categorisation, each with a one-line
author response.

## Blockers

- B1 (sections 3.1, 4.4, 11, bibliography resolution). `Root.lean`
  importing `Bibliography.lean` does not make `citep` and `citet`
  resolve in the chapters. Both parse their arguments through
  `ValDesc.resolvedName`, which calls
  `realizeGlobalConstNoOverloadWithInfo` at elaboration time in the
  citing module's environment, and Lean imports flow downstream only:
  `Root.lean` imports `Tutorial.lean` imports `Ch1.lean`, so a chapter
  never sees what the root imports. Every citation in every chapter
  would fail with an unknown-constant error. The same asymmetry is why
  `{include}` requires an index to import the chapters it includes,
  which section 3.1 states correctly one paragraph earlier. **Fix**:
  each of the twelve chapter modules imports
  `GebLeanDocs.Bibliography` directly; the import graph and section
  3.3's guard invariant are restated against that tree, under which
  every library module remains reachable from `GebLeanDocs.lean`.

## Serious

- S1 (section 3.1, module keyword). "No `.lean` file in this
  repository currently uses `module`" is false: twenty-nine tracked
  files do, including the first-party `GebLeanMeta.lean` and the
  vendored `Geb/Mathlib` tree. The exemption is therefore a departure
  from existing practice, not the recording of a dormant rule. The
  technical ground holds — `finishDoc` emits a non-`public` `def`, and
  Verso's own document modules carry no `module` — but the
  justification attached to it did not. **Fix**: the sentence states
  the true position, and names `public section` as the untested
  alternative that is not relied on.
- S2 (sections 3.2, 9, the third diagnostic class). "The only control
  is the option that governs the warning" is false, and "Two bear on
  this design" under-enumerates. A sweep of Verso's `logWarning` sites
  finds four further warnings in this class governed by no option at
  all: an unused link definition, an unused footnote definition, and
  the deprecated forms of role and directive arguments (`x := v` for
  `(x := v)`, `show := false` for `-show`). The last bears on this
  design directly, since section 7 uses `signature`'s `show` option
  and section 5 uses the `lean` block's flags. **Fix**: the class is
  split into option-governed warnings and warnings remediable only by
  changing the document source, with both sets named; section 9
  follows.
- S3 (sections 3.1, 3.2, 11, the required option entry). Section 3.2
  declared a per-library entry raising `verso.code.warnLineLength`
  required before any Part I illustration is written, while section
  3.1's TOML sketch showed no `[lean_lib.leanOptions]` subtable and
  section 11's enumeration of `lakefile.toml` changes omitted it. A
  plan derived from section 11 would drop a change the spec calls
  mandatory, and the first Part I code block over 60 columns would
  fail the CI generator build. **Fix**: the subtable is in the sketch
  with its `weak.` prefix and a sentence on why, and section 11's
  bullet names it.

## Minor

- m1 (section 3.2, `warnLongLines`). The call is not unconditional: it
  sits under `if config.show`, `show` defaults true, and it is the
  only call site, so `leanTerm` and `signature` are unaffected —
  which matters because section 7's presentation exceeds 60 columns.
  **Fix**: stated.
- m2 (section 3.2, block code). The `elabMarkdown` bullet covered
  inline spans only. A fenced block in a rendered docstring warns on
  the same path and has no keyword fallback, so a fence that does not
  parse warns. No docstring in the twelve contributing modules
  contains a fence, so the exposure is currently zero. **Fix**: both
  stated.
- m3 (section 4.2 chapter 3, module attribution). `SortedSig` was
  listed under chapter 3, whose modules are `Term.lean`,
  `Interp.lean` and `SynCat.lean`; `structure SortedSig` is in
  `SortedSig.lean`, a chapter 2 module. Rendering it in both chapters
  would save the docstring domain object twice under one key. **Fix**:
  chapter 3 refers to it with the `name` role.
- m4 (section 3.3, linter prefix). `runLinter` lints declarations
  whose module is prefixed by the argument's *root component*, not by
  the argument. The two coincide for `GebLeanDocs`, so the design is
  unaffected. **Fix**: stated precisely.
- m5 (section 3.1, module-keyword scope). The exemption was scoped to
  "document modules" and justified by Verso's generated `def`, while
  three of the eighteen new files carry no `#doc`, and
  `Bibliography.lean`'s entry definitions would need `public` under
  `module`. **Fix**: the exemption covers the library and its
  executable root, and the path table says which modules carry no
  `#doc`.
- m6 (section 3.1, entry-point import). Every other path-table row
  states its module's imports; `GebLeanDocsMain.lean`'s did not,
  though `%doc GebLeanDocs.Root` requires one. **Fix**: stated.
- m7 (section 3.2, cross-reference). "open question 2 covers the
  residual in all three classes" — open question 3 covers the
  environment-linter residual. **Fix**: both cited.
- m8 (section 10, bullet 2). "The local scripts are unchanged"
  contradicts bullet 3 and section 11, which amend
  `scripts/pre-commit.sh`'s comment and extend
  `scripts/tests/test-lint-driver.sh`, the latter being step 7 of
  `scripts/pre-push.sh`. **Fix**: "No local script gains a build
  step", which is what the following sentence supports.
- m9 (section 12, chapter enumeration). "Part I chapters 1, 3, 4 and
  5 name legacy declarations directly" omits chapter 2, which
  forward-references `ramTwoPow`. **Fix**: chapters 1 to 5.
- m10 (section 12, taxonomy bullet). The bullet cited
  `docs/process.md` § Process self-update mechanism as ground for
  deferring the amendment elsewhere, while that section assigns a
  corrective rule edit to "the workstream that uncovered it" — the
  citation argued against the deferral it supported. The bullet also
  sat in a design spec, which is a design record and not a backlog.
  **Fix**: the item moves to `TODO.md`, and section 12 keeps a
  one-line pointer without the rule citations.
- m11 (section 11, `deftech` deliverable). Open question 4 pairs the
  Part II enumeration with the Part I `deftech` vocabulary, and
  section 6 independently requires the latter be recorded in the plan,
  but section 11 listed only the former. **Fix**: both.
- m12 (section 11, rule amendment). The deliverable named
  `.claude/rules/lean-coding.md` § Documentation, while the same
  mandate appears in § Comment and docstring rules, which would be
  left to contradict the `nolints.json` entries. **Fix**: both
  sections, and § Lean 4 module system for the exemption.
- m13 (section 2.3, caveat scope). The caveat named only the third of
  section 3.2's three diagnostic classes, so a reader could infer the
  other two were covered by the table. **Fix**: all three.
- m14 (section References, false universal). "Every work below is
  cited in Part I chapter 6" covers nine entries of which three are
  pointers, not citations, and section 4.4 fixes the count at six
  cited works. **Fix**: scoped.
- m15 (section 4.4, `Article` fields). The three works entered as
  `Article` need `volume`, `number` and `month`, none of which the
  reference list supplies for all three. **Fix**: recorded as gathered
  when `Bibliography.lean` is written.

## Cosmetic-taste

- c1 (sections 3.3, 11). "by hand" reintroduced a term review 1
  recorded as removed. **Fix**: "manually".
- c2 (section 4.2 chapter 6). "the modules deliberately absent"
  asserts intent against an unstated charge. **Fix**: "the modules
  section 4.3 names as absent".
- c3 (References). Ritchie carried no DOI where the other five
  published works do. **Fix**: added.

## Findings against the review artefacts

- A1 (review 1, preamble and convergence) — minor. Both correction
  counts were short: four dispositions were found overstated, not
  three, and four fixes rested on further false claims, not two.
  **Fix**: both corrected, and the preamble widened to the rounds
  actually represented.
- A2 (review 4, A5) — minor. The recorded fix was not applied: four
  bare-parenthesis correction records remained beside the italic
  marker form. **Fix**: converted.
- A3 (review 3, m11) — minor. The marker cited review 4's m1, an
  unrelated finding; the correcting entry is review 4's A7. **Fix**.
- A4 (reviews 1 and 3) — cosmetic-taste. Four citations used a
  hyphenated identifier form no other citation uses. **Fix**:
  normalised.
- A5 (review 1, S5) — minor. The disposition read "Fix on the
  merits", outside the three permitted forms, and named no resulting
  edit, so a reader could not tell what changed. **Fix**: "Fix", with
  decision 10 and section 8 named.
- A6 (review 1, S5) — minor. The required-by versus discovered-during
  criterion discriminates on the axis review 4 identified but is
  unbounded: a toolchain bump required to resolve Verso would equally
  be "required by the manual". **Fix**: bounded by whether the
  required change is itself an independently reviewable concern.

## Verified without defect

- **Section 4.3's counts reproduce exactly, twice independently**:
  309 total, 179 definitional (`def` 165, `structure` 9, `abbrev` 4,
  `inductive` 1), 130 theorems and instances (`theorem` 124,
  `instance` 6), with the per-module figures matching.
- **Section 8's source-side survey is exact**: twelve undocumented
  declarations across the twelve contributing modules, being the four
  anonymous instances in `RType.lean` and eight `@[simp]` theorems,
  none covered by section 4.3's rule.
- **The seven endpoint declarations** all exist at the cited lines and
  lie outside the 309, and `yonedaConstEmbedding_faithful` exists as
  the naming precedent with no collision.
- **Every mechanism claim in sections 2.1, 2.3, 3.3, 7 and 4.4 holds
  against source**, including the dependency-ordering argument in
  mechanism and direction, the `signature` block's fresh
  `Command.State` and discarded `compare` messages, the surviving type
  and level-parameter checks, `docBlame`'s exemption set, the
  `nolints.json` format and the `--update` wholesale-rewrite hazard,
  the `{include N NAME}` level parameter, and the four bibliography
  entry types.
- **All five published DOIs resolve** to the stated title, year and
  page range.
- **Every repository path, guard, workflow and rule-file claim** the
  spec makes checks out, and all four of section 12's publication
  clauses hold verbatim.
- **The round-4 numeral pass held**: across roughly seventy internal
  cross-references only two were wrong (m7, m9), and every count,
  declaration name, path and DOI in the spec checked out.
- Review 1's Rejected section is gone with both entries present
  intact, its convergence count is right, and every finding across the
  five artefacts carries exactly one response from the three permitted
  forms.

## Convergence

Not converged. One blocker and three serious findings against the
spec, six minor findings against the artefacts, all fixed at this
branch.

The blocker and S1 are both consequences of round 4's own fixes rather
than residue from before them. Round 4 placed the new
`Bibliography.lean` import at the one node in the tree that cannot
supply it, and attached to the new `module` exemption a repository
fact that was not checked. A fix written in the same pass as the
finding it answers is not covered by that pass's verification, and
round 4's mechanical numeral sweep ran over text predating the fixes
rather than over the fixes themselves. Round 6's sweep runs over the
text this round introduced.
