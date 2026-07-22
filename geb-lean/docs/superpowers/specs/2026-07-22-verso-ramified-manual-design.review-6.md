# Adversarial review 6: Verso ramified-recurrence manual design

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

Round 6, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. Two fresh `Agent` invocations, one on
external and repository fact verification, one on internal
consistency, realizability, scope, and project-rule compliance. Both
were directed at the text round 5 introduced, rounds 1 to 5 having
settled the rest. Findings are deduplicated across both and
categorised per `docs/process.md` § Defect categorisation, each with a
one-line author response. Where the two reviewers assigned different
severities to one finding, the higher governs.

## Blockers

None.

## Serious

- S1 (sections 3.1, 7, chapter imports). Round 5's blocker established
  that `citep` resolves in the citing module's environment and that
  Lean imports flow downstream only. That fact governs `docstring`,
  `name` and `signature` identically, and governs `VersoManual`, which
  supplies every facility of section 2.2. The fix reached only the
  citation case: the path table's chapter rows named
  `GebLeanDocs.Bibliography` as their sole import, and read against
  seven exhaustive neighbours that is the chapters' import list, under
  which every `docstring` in Part II fails elaboration. Section 7
  reasons about "a chapter module's `open GebLean.Ramified`", which is
  not writable unless the chapter imports those modules, and
  `Bibliography.lean`'s row named no import though it must reach
  Verso's bibliography facilities to define entries. The external
  reviewer rated this minor, on the ground that the first `docstring`
  block would fail and the implementer would add the import; the
  higher severity governs, since section 3.1 is where the library's
  shape and its guard invariant are fixed. **Fix**: the chapter rows
  name the `GebLean/Ramified/` modules they render or name, the
  `Bibliography.lean` row names `VersoManual`, and the import-graph
  paragraph states the governing fact once for all four mechanisms.
- S2 (section 3.1, module-keyword practice). Round 5 corrected a false
  claim that no file in the repository uses `module`, and the
  replacement — "a departure from existing practice, not a dormant
  rule" — overshot in the other direction. Measured: five of the
  repository's 414 first-party `.lean` files carry `module`, against
  all 29 files of the vendored `Geb` tree, which is generated from a
  repository that adopted the module system. *Corrected at round 7*:
  these figures were themselves wrong, a pattern matching
  `^module( |$)` having counted four wrapped docstring lines beginning
  with the word "module"; the count is one of 418, `GebLeanMeta.lean`
  (review 7, S1). A new first-party library without `module` follows
  prevailing first-party practice; what it departs from is the written
  rule. This is the failure mode round 5's
  own S1 recorded, reproduced in round 5's replacement text, and the
  justification is what carries a stated exemption that section 11
  schedules a rule amendment for. **Fix**: the paragraph states the
  measured position and locates the departure in the rule rather than
  in practice.
- S3 (`TODO.md`, taxonomy entry premise). "Every such artefact
  predating the branch uses a Majors / Minors / Nits taxonomy" is
  false; the artefacts under `docs/superpowers/specs/` and
  `docs/superpowers/plans/` predating this branch use several heading
  vocabularies, part of which match the mandated one. *Corrected at
  round 7*: this entry first recorded a 65 / 49 / 148 split that does
  not reproduce — 65 counts artefacts carrying a `Blocker`-or-`Serious`
  heading at any level, and `Blocker` is common to both taxonomies, so
  it includes non-compliant artefacts (review 7, S2). Both stated
  resolutions rest on the
  universal — amending `docs/process.md` "to admit the form in use"
  presupposes one form, and re-categorising "the existing artefacts"
  over-scopes by roughly a factor of two. The claim was inherited from
  review 3's convergence note and moved into `TODO.md` at round 5
  without being checked at the moment it was moved. **Fix**: the entry
  states the measured split and scopes itself to the non-compliant
  set; review 3's note is corrected in place.
- S4 (`TODO.md`, entry placement). The entry was appended at end of
  file, which placed it under `## To be done in geb-mathlib (not
  pending here)`, whose preamble reads "None of the items in this
  section are pending in the present repository" — while spec section
  12 points to `TODO.md` as the item's live destination. **Fix**:
  relocated under `## Active in geb-lean`.

## Minor

- m1 (section 3.1, orphan criterion). "a module in the directory that
  no index imports" no longer matches the round-5 graph, under which
  `Bibliography.lean` is imported by no index but by all twelve
  chapters. **Fix**: "a module that nothing in the library imports".
- m2 (section 3.2, deprecated-syntax cross-references). The clause
  asserted that section 7 uses `signature`'s `show` option and section
  5 uses the `lean` block's flags; section 7 records only that the
  option exists and sets none, and section 5 names no flag. **Fix**:
  the warning is stated to bind every role or directive argument the
  chapters write.
- m3 (section 3.1, TOML paragraph). "every chapter module importing
  `VersoManual`" does not cover `GebLeanDocs.lean` and
  `Bibliography.lean`, to which the option entry also applies.
  **Fix**: "every module of this library".
- m4 (section 3.1, exemption scope). The exemption covers eighteen
  files while its ground reaches only the fifteen carrying a `#doc`.
  **Fix**: the remaining three are stated as covered for uniformity.
- m5 (section 4.2 chapter 3). "rendered in chapter 2" breaches section
  4's own rule that every cross-reference names its part, the only
  such breach in the document. **Fix**: "Part II chapter 2".
- m6 (section 9). The Diagnostic-interaction paragraph omitted
  `verso.docstring.elabMarkdown`, which section 3.2 names. **Fix**:
  added, with its currently-zero exposure.
- m7 (section 13, open question 2). The consequent asked only which
  `leanOptions` entries are needed, which cannot answer for the
  option-less subclass section 3.2 had just separated out. **Fix**:
  the document-source conventions are named alongside.
- m8 (section 3.2 against section 3.1, `weak.` prefix). One paragraph
  said the prefix is required, the other that the non-weak form would
  also resolve. Both are true of different cases, but the document
  gave two accounts of one mechanism. **Fix**: required where the
  defining module may be unimported, used uniformly here.
- m9 (`TODO.md` entry shape). The entry was free prose where the
  active section's entries use bolded field labels. **Fix**:
  `**Status**` and `**Scope**`.
- m10 (section 8 against review 1's S5). The disposition claims
  section 8 states the required-versus-discovered criterion with the
  bound round 5 added; section 8 stated only part of it, so a
  criterion discharging a `CLAUDE.md` § one concern per branch
  objection lived only in a review record. **Fix**: the criterion and
  its bound are in section 8.
- m11 (sections 10, 11, cost figure). "Verso and its three transitive
  dependencies" counts `plausible`, already in the closure through
  mathlib and `cslib`. **Fix**: "the two dependencies not already in
  the closure".
- m12 (References, citation split). "Five are cited in Part I chapter
  6 … Leivant III is cited throughout" reads as a partition excluding
  Leivant III from chapter 6, which section 4.1 names it in. **Fix**:
  all six, Leivant III additionally throughout.

## Cosmetic-taste

- c1 (section 3.1). Comma splice in the reachability sentence.
  **Fix**: "by way of the chapters".
- c2 (section 3.1). "A `public section` around the `#doc`" implies a
  delimiter that cannot be written, `#doc` replacing the command
  parser for the remainder of the module. **Fix**: "preceding", with
  the reason.
- c3 (section 3.1). "the vendored `Geb/Mathlib` tree" understates:
  three of the vendored `module` files lie outside `Geb/Mathlib`.
  **Fix**: "the vendored `Geb` tree".
- c4 (References). The `Article`-fields sentence said the list carries
  none of `volume`, `number`, `month` for three works; it carries
  volume for all three. **Fix**: "only part".
- c5 (review 5). "both entries landed intact" uses a term
  `docs/process.md` names in its example list. **Fix**: "present".
- c6 (review 5, Convergence). "worth carrying forward" and "the one
  process change that demonstrably worked" are appraisal. **Fix**:
  the diagnosis is stated without it.

## Findings against the review artefacts

- A1 (review 3, convergence note) — serious. The false universal that
  produced S3 originated here and rode through three rounds
  unverified. **Fix**: corrected in place with the measured split and
  marked at round 6.
- A2 (review 1, preamble and convergence) — minor. The counts named
  eight corrected sites while eleven entries carry a correction
  marker, with no stated criterion distinguishing them. Round 5 had
  already revised these counts once. **Fix**: all eleven are
  accounted for, in three groups.
- A3 (review 4, m12) — cosmetic-taste. "appended by hand" reproduces
  the term review 1 recorded as removed. **Fix**: "manually".

## Verified without defect

- **`import VersoManual` suffices for every facility of section 2.2**,
  and `VersoManual.lean` carries no `module`, so its imports pass
  through to a legacy importer. Section 2.2's module attributions are
  correct.
- **The corrected import graph is right.** `citep`/`citet` resolve
  through `.resolvedName`, so a per-chapter import of
  `GebLeanDocs.Bibliography` is correct and sufficient; `{include}`
  resolves the generated document name, so an index must import its
  chapters. Under the corrected tree all seventeen library modules are
  reachable from `GebLeanDocs.lean`, so section 3.3's guard invariant
  holds. Imported `GebLean.*` declarations are outside the linter's
  reach, which filters on the `GebLeanDocs` prefix.
- **The `module` mechanism holds**: `finishDoc` emits a non-`public`
  `def`; under `module` neither `%doc` nor a cross-module `{include}`
  could reach it; Verso's document tree carries no `module`;
  `public section` is real syntax and the hedged claim about it is
  accurate; a legacy file importing a `module` file has in-repo
  precedent.
- **All four option-less warnings exist as described** and none is
  governed by an option; `SignatureConfig.show` is parsed as a flag,
  so `show := false` does reach the deprecated-flag path.
- **`warnLongLines` has one call site**, guarded by `if config.show`;
  `leanTerm` and `signature` never call it. `tryElabBlockCode` has no
  keyword fallback where `tryElabInlineCode` does.
- **The new TOML is valid** and binds to `GebLeanDocs`: the dotted key
  flattens at any depth, `100` decodes as a `Nat`, the `weak.` prefix
  is stripped after imports load, and the following `[[lean_exe]]`
  opens a new array.
- **The linter-prefix sentence is exact**, and `GebLeanDocs` is
  correctly not a `Name` prefix of `GebLeanDocsMain`.
- **The Ritchie DOI resolves** to the stated author, title, journal,
  volume, year and page range.
- **Every seam the round examined holds**: the path table against the
  import graph against section 3.3's guard against section 11;
  section 3.2's split against section 9 against open questions 2 and
  3; section 4.2 chapter 3 against chapter 2 and section 4.3; section
  10 bullet 2 against bullet 3 and section 11. Module counts close
  everywhere: eight table rows over eighteen files, fifteen carrying a
  `#doc` and three not, seventeen library modules and one executable
  root.
- **The mechanical pass over the round-5 numerals and cross-references
  found one breach** (m5); every other numeral and every internal
  reference resolves.
- **The register sweep is clean on the spec**: no term from any prior
  round's list survives outside quotation in the artefacts.
- All documents and `TODO.md` are markdownlint-clean and
  doctoc-current.

## Convergence

Not converged. Four serious findings, none against the spec's
substance: S1 and S2 are the justification and completeness of two
round-5 fixes, and S3 and S4 concern the backlog entry round 5
created. No blockers, for the third consecutive round. The external
lens reported no blockers and no serious findings at all; the
consistency lens supplied all four, and its severities govern.

The pattern round 5 named has now recurred twice in succession: every
serious finding this round is a defect in text written to answer the
previous round's findings, and none is a defect in text that has been
through a review. Round 7's reviewers are directed at the round-6 text
on the same principle.
