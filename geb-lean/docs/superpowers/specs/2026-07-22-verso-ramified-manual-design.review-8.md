# Adversarial review 8: Verso ramified-recurrence manual design

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

Round 8, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. One fresh `Agent` invocation covering
both lenses, directed at the round-7 corrections and instructed to
give the command behind any count it reported. Findings are
categorised per `docs/process.md` § Defect categorisation, each with a
one-line author response.

## Blockers

None.

## Serious

None.

## Minor

- M1 (`TODO.md`, taxonomy entry scope). "Re-categorise the artefacts
  that do not carry `## Serious` and `## Cosmetic-taste` headings" is
  scope-ambiguous over the negated conjunction, and the two readings
  differ by five artefacts of 149 — "carries neither" gives 134,
  "does not carry both" gives 139. The entry defers enumeration, so
  nothing downstream depends on it yet, but the criterion is the
  entry's only scope statement. **Fix**: "that do not use the
  blocker / serious / minor / cosmetic-taste headings at all".

## Cosmetic-taste

- C1 (section 3.1, orphan criterion). "a module `GebLeanDocs.lean`
  does not transitively import" is a zero-relative whose head is
  followed by a proper noun, so it first parses as apposition — the
  garden path round 7's c1 removed one sentence earlier. **Fix**:
  insert "that".
- C2 (section 3.1, consecutive paragraphs). "The same asymmetry is why
  an index must import the chapters it includes" is followed
  immediately by "The same asymmetry governs the sampling
  mechanisms"; round 7's c2 fixed a dangling antecedent by repeating
  the antecedent verbatim across the paragraph break. **Fix**: "That
  asymmetry also governs".

## Findings against the review artefacts

- A1 (review 7, S2) — minor. Two of S2's justifying figures do not
  reproduce, in the paragraph whose own conclusion is that unsourced
  measurements must go: "the figure is 12" appears under no criterion
  tried, and "64 artefacts carry neither discriminator" is the same
  criterion that yields 65 measured over a different population, so it
  was reported as though it were 65's complement, which is 84. S2's
  conclusion is independently confirmed — 149 artefacts predate the
  branch, 65 reproduces only under a loose case-insensitive any-level
  criterion, and 49 under nothing — and `TODO.md` records no count, so
  nothing propagated. **Fix**: both figures struck, since the
  conclusion does not rest on them, and the case-insensitivity of the
  65 criterion noted.
- A2 (review 7, Round and protocol) — cosmetic-taste. "the surface
  under review" uses a term review 1 records as removed from the
  artefacts. **Fix**: "the material under review".

## Verified without defect

- **The `module` measurement is settled**, with the commands recorded:
  447 tracked `.lean` files, 29 under `vendor/`, 418 first-party, and
  exactly one first-party file carrying the command form,
  `GebLeanMeta.lean`, against all 29 vendored files. The four
  round-7-identified false positives are wrapped docstring prose, and
  a broader sweep finds no further candidate. Section 3.1's sentence
  and section 11's scheduled amendment both hold, and the argument is
  strengthened: 1 of 418 makes no-`module` prevailing practice rather
  than a near-tie.
- **The rescoped `TODO.md` entry is sound**: "at least four distinct
  heading vocabularies" is a true lower bound, `docs/process.md`
  § Defect categorisation does define only the mandated form, and
  § Convergence criterion is stated over blocker and serious findings,
  so the premise and both resolutions hold. Placement and field shape
  are correct and section 12's pointer matches.
- **Section 3.1's other round-7 edits**: "The three files" is right,
  and the orphan criterion now matches what
  `scripts/tests/test-lint-driver.sh` implements — a transitive import
  closure from the umbrella root, compared against all modules, which
  is root-reachability and not "imported by something".
- **Review 1's preamble recount is exact**: twelve markers, eleven in
  finding entries mapping to the three named groups, one in the
  Verified-without-defect list.
- **Reviews 3 and 6's corrected notes** record the round-7 position
  correctly and carry their in-place markers.
- **Section 8's source-side measurement, independently rechecked**:
  exactly twelve undocumented top-level declarations across the twelve
  contributing modules, being the four anonymous instances in
  `RType.lean` and eight `@[simp]` theorems, matching section 8
  exactly; section 4.3's exclusion covers all four, so the contingent
  docstring deliverable holds.
- **Section 4.3's module partition is exhaustive and disjoint** over
  the 47 tracked files, and all the named endpoint declarations
  resolve in the two endpoint modules.
- **Every repository fact sections 3.1 to 3.3 and 11 rest on**
  verifies, including the `lakefile.toml` settings, the positional
  subtable hazard, the `weak.linter.hashCommand` precedent and its
  recorded reason, `.gitignore`, the three
  `.claude/rules/lean-coding.md` sections, and
  `scripts/pre-commit.sh`'s lockstep instruction.
- **The Verso mechanism, dependency-resolution and build-wiring
  substance verified without a finding for the fourth round running.**
- All documents and `TODO.md` are markdownlint-clean and
  doctoc-current; review 7 assigns one severity and one permitted
  response per finding.

## Convergence

Converged. Zero blockers and zero serious findings against the spec,
and five consecutive rounds without a blocker. The residual — one
minor, two cosmetic, and two findings against a review artefact — is
fixed at this branch, none of it a barrier to termination.

The record across eight rounds, as blockers and serious findings:
5 and 5, 6 and 11, 4 and 9, 0 and 3, 1 and 3, 0 and 4, 0 and 2, 0 and
0. Three phases are visible. Rounds 1 to 3 removed false claims about
what Verso, Lake and SubVerso do, which was where the design's
justification lived. Rounds 4 to 6 removed defects that the previous
round's fixes had introduced, the artefact's own repair being the
unreviewed surface each time. Rounds 7 and 8 removed repository
measurements reported without the command that produced them.

Round 7 named the discipline that closes the last of these — record
the command beside the count — and did not apply it to its own two
parenthetical figures, which is A1. The spec and `TODO.md` do apply
it, or record no count, which is why nothing propagated and why the
criterion is met.
