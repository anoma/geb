# Adversarial review 7: Verso ramified-recurrence manual design

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

Round 7, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. One fresh `Agent` invocation covering
both lenses, the material under review being one round's edits rather
than the whole document. Findings are categorised per
`docs/process.md` § Defect categorisation, each with a one-line author
response.

## Blockers

None.

## Serious

- S1 (section 3.1, module-keyword measurement). "Five of the
  repository's 414 first-party `.lean` files carry `module`" is false
  in both figures. 447 `.lean` files are tracked, 29 under `vendor/`,
  so 418 are first-party. Of the five first-party matches the author's
  pattern produced, four are wrapped prose lines inside module
  docstrings that begin with the word "module"
  (`GebLean/EraHistCodeTerm.lean`,
  `GebLean/Ramified/Polynomial/Collapse.lean`,
  `GebLean/Ramified/Soundness.lean`,
  `GebLean/Utilities/SimRec.lean`), each of those files beginning with
  `import` on line 1. Matching the command form
  `^module[[:space:]]*(--.*)?$` yields exactly one first-party file,
  `GebLeanMeta.lean`. The sentence is the sole stated ground for
  exempting a new library from `.claude/rules/lean-coding.md` § Lean 4
  module system, and section 11 schedules a rule amendment against it.
  This is the third consecutive round in which this one sentence has
  carried a false repository measurement. **Fix**: one of 418, named.
  The direction of the argument is unaffected and strengthened.
- S2 (`TODO.md`, and the same figures in reviews 3 and 6). The
  65 / 49 / 148 split does not reproduce. 149 review artefacts predate
  this branch, not 148. 65 reproduces only as "carries a
  `Blocker`-or-`Serious` heading at any level, case-insensitively",
  and `Blocker` is common to both taxonomies, so that set includes
  non-compliant artefacts. 49 reproduces under no criterion tried. The
  entry's two resolutions therefore rest on a two-form premise that
  the measurement contradicts — at least four heading vocabularies are
  in use — and the two figures do not partition the population, so
  "re-categorise the non-compliant set" has no determinate scope.
  Round 6 replaced a false universal with a false measurement.
  **Fix**: the entry is scoped by criterion, with no count recorded
  and the enumeration deferred to when the item is taken up.

## Minor

- m1 (section 3.1, exemption scope). "The three library files that
  carry no `#doc`" counts the executable root among the library's
  files, which the same paragraph, the path table and section 11 all
  place outside it. **Fix**: "The three files".
- m2 (section 3.1, orphan criterion). "a module that nothing in the
  library imports" is weaker than the invariant `test-lint-driver.sh`
  implements, which is root-reachability: a module imported only by an
  orphan is imported by something in the library and still unreachable
  from the root. **Fix**: "a module `GebLeanDocs.lean` does not
  transitively import".
- m3 (review 6, S3). "the 148 review artefacts predating this branch"
  — 149 are tracked, 148 being reachable only by excluding
  `2026-05-25-step-t5-equivalence-plan.holistic-review.md`, which is a
  review artefact. **Fix**: subsumed by S2's removal of the figures.

## Cosmetic-taste

- c1 (section 3.1). The reachability sentence's apposition still
  parses as a two-item list. **Fix**: semicolon.
- c2 (section 3.1). "It governs the sampling mechanisms equally" has
  its antecedent two sentences back. **Fix**: "The same asymmetry
  governs".

## Findings against the review artefacts

- A1 (review 6, S2) — serious. The finding recorded the false module
  measurement that entered the spec. **Fix**: corrected in place with
  the pattern error named, as spec S1.
- A2 (review 6, S3; review 3, convergence note) — serious. Both carry
  the unreproducible split. **Fix**: corrected in place, as spec S2.
- A3 (review 1, preamble) — cosmetic-taste. "Eleven entries carry a
  correction" counts findings, while a twelfth marker sits in the
  Verified-without-defect list. **Fix**: "eleven findings", with the
  twelfth noted.
- A4 (reviews 1 and 4) — cosmetic-taste. Round-6 edits to those two
  artefacts carry no in-place round-6 marker where review 3's does.
  **Reject as cosmetic-taste**: the marker convention has applied to
  finding entries and not to preamble or wording repairs since round
  5, and review 1's convergence note records the rounds represented.
  Making it uniform would mark every copy-edit, which is not what the
  convention is for.

## Verified without defect

- **Section 3.1's new middle paragraph holds in every clause**,
  including the transitivity question: `docstring`, `name` and
  `signature` all resolve in the citing module's environment, and
  every one of the eighteen files reaches `VersoManual` through
  `Bibliography.lean`, which reaches it directly and carries no
  `module`. Round 6's S1 fix is complete — the chapter rows' imports
  are what make section 7's `open GebLean.Ramified` writable and every
  Part II `docstring` resolvable.
- **The `public section` and `#doc` mechanics as reworded**: `#doc`
  does replace the command parser for the remainder of the module, so
  "preceding" is right and no closing `end` can follow; `public
  section` is used without one throughout Verso's own source.
- **The TOML paragraph, the three diagnostic classes, the `weak.`
  prefix reconciliation, the linter claims, the cost figure, section
  4.4's `Article` fields and the References corrections** all verify
  against source at the pinned tag.
- **Section 8's criterion and review 1's S5 disposition now agree**
  near-verbatim on the axis, the bound and both worked cases, and the
  criterion discriminates: it sorts section 8's two change kinds
  against its deferred refactors and against section 11's rule
  amendments consistently. Round 6's m10 is discharged.
- **`TODO.md`'s placement and format** are correct after round 6's S4
  and m9 fixes, and section 12's pointer is consistent with the new
  location.
- **The mechanical pass over the round-6 text** closes every numeral
  and every cross-reference except m1's mislabel.
- All documents and `TODO.md` are markdownlint-clean and
  doctoc-current; review 6 assigns one severity and one permitted
  response per finding.

## Convergence

Not converged. Two serious findings, no blockers, for the fourth
consecutive round without a blocker. Both are single-sentence
measurements in text round 6 wrote to answer round 5, and neither
touches the spec's mechanism or dependency substance, which verified
cleanly against Verso's source.

The recurring pattern is now specific enough to name precisely: the
defects are not in reasoning about Verso, which has held for three
rounds, but in counting things in this repository. S1 arose from a
pattern matching prose that begins with a keyword; S2 from a figure
reported without the criterion that produced it. Both are avoidable by
recording the command that produced a count beside the count, which
round 8's text does where it states any measurement at all.
