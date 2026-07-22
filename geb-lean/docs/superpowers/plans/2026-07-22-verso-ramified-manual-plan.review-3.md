# Adversarial review 3: Verso ramified-recurrence manual plan

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

Round 3, 2026-07-22, against the plan at branch
`docs/verso-ramified-manual`. One fresh `Agent` invocation covering
both lenses, directed at the text round 2 introduced. Findings are
categorised per `docs/process.md` § Defect categorisation, each with a
one-line author response.

## Blockers

None.

## Serious

- S1 (Task 5.1 against Appendix A, the row count). Round 2's own S4
  fix removed the `clone` row, leaving Appendix A with sixteen terms
  across its two tables, while Task 5.1 still read "seventeen rows".
  The executor would have written sixteen against a stated seventeen
  and stopped, or invented a seventeenth — most plausibly re-adding
  `clone`, which the same edit had demoted to plain prose, putting a
  non-`deftech` term in the correspondence table. **Fix**: Task 5.1
  derives the set from Appendix A's two tables rather than restating a
  count, so the number cannot fall out of step again.
- S2 (Appendix A, the `closed` row against its own exception). The
  table gave `closed` a referrer in Part I chapter 4; the exception
  paragraph added by the same edit said it has none outside chapter 1.
  Task 4.4's content settles it — the chapter names eq. (4) monotonic
  and eq. (5) flat and never discusses closed recurrence — so the
  paragraph is right and the row was false. Under the row's reading a
  chapter-4 author emits a `{tech}[closed]` into a chapter that never
  uses the term, which resolves and so no gate catches. **Fix**: the
  row reads "none; see the exception below".
- S3 (Task 4.1, two round-2 fixes absent). Round 2's S4 response
  recorded that Task 4.1's content would name the three algebra
  classifications as `deftech` definitions and that Tasks 4.1 and 4.3
  would carry a "Depends on: Appendix A" line. Neither reached the
  file: the substitution targeted "Carries the `deftech` definitions"
  where the text reads "Carries the **sole** `deftech` definitions",
  matched nothing, and was reported as applied. Task 4.1 therefore
  still closed its set at nine terms with the word "sole", against
  Appendix A's twelve, and carried no pointer to the appendix — so a
  Task 4.1 subagent would have defined nine, and Task 4.6 would either
  diverge silently or fail generation five tasks later. **Fix**:
  applied, and every substitution in this round was verified
  individually to have landed before the artefact was written.

## Minor

- M1 (Task 1.1 Step 3, a duplicated ignore line). Round 2 moved
  `/_out` to Task 0.2 Step 1 and stated that Task 1.1 "then has
  nothing to add there", but left Task 1.1's step in place. **Fix**:
  the step is removed and the Files list records where the line comes
  from.
- M2 (Task 0.1 Step 4, "Expected exactly"). The word contradicted the
  paragraph beneath it admitting further additions. **Fix**.
- M3 (Appendix A, the rule's circularity through Part II chapter 1).
  Task 5.1's table takes one row per `deftech` term, so "Part II
  ch. 1 refers to it" follows from being a defined term rather than
  evidencing it. Nine rows cite it, all nine having an independent
  referrer as well. **Defer with rationale**: nothing is wrongly
  admitted, and removing the citation would make the table's own
  dependency on Appendix A less visible; the rule's discriminating
  work is done by the other referrers, which the reviewer confirms
  hold for every row that needs them.
- M4 (Appendix A, two unsupported referrer claims). `tier` cites Part
  I chapter 6 and `r-type` cites chapter 5, neither of which the
  plan's chapter descriptions bear out. **Defer with rationale**: both
  terms earn their `deftech` from other referrers that do check out,
  so no row changes status; the chapter descriptions fix content at a
  coarser grain than every term occurrence, and tightening the claims
  would assert more than the plan can support before the chapters are
  written.
- M5 (Task 1.2 Step 1, `series`). The guidance named `booktitle`,
  `journal`, `volume`, `number` and `month` but not `series`, the one
  optional field the round-2 References edit newly requires, for
  `clote`. **Fix**.
- M6 (Task 3.1 Step 4, scratch files). `appendix-b.txt` was removed on
  the happy path only, in a repository whose `snapshot.auto-track` is
  `all()`, and the restore was a copy through `/tmp` in a plan whose
  Phase 0 argues against `/tmp` on this machine. **Fix**: `jj restore`
  for the module, `rm -f` on every exit path.

## Cosmetic-taste

- c1 (markup for emphasis, one survivor). Recorded as fixed at rounds
  1 and 2 and present at both. **Fix**: applied, and a grep now
  reports zero occurrences.
- c2 (rewrap raggedness at four sites). **Defer with rationale**: the
  reviewer confirms no list, code block or table was damaged and the
  file is markdownlint-clean; the wrapping is uneven but reading is
  unaffected, and a second programmatic pass risks more than it fixes.
- c3 (the horizontal rule closing Phase 1 before Task 1.5). An
  artefact of round 1's reordering. **Defer with rationale**: the rule
  separates phases visually and no rule is load-bearing; moving it is
  churn on a document under active revision.
- c4 (the absolute path, 42 occurrences). **Defer with rationale**, as
  at rounds 1 and 2: the same form appears in 44 files under `docs/`,
  so this document should not be the outlier.

## Findings against the review artefacts

- A1 (review 2, "Verified without defect"). It asserted "Appendix A's
  twelve plus five rows agree with Task 5.1's seventeen", describing
  the document before the same round's S4 fix removed a row. The
  verification pass affirmed a count its own fix had falsified.
  **Fix**: the claim is struck; S1 above records the correction.
- A2 (review 2, the S4 response). Two of its four recorded fixes are
  not in the commit. `docs/process.md` § Author response requires the
  corrected text or a pointer to the resulting edit. **Fix**: recorded
  at S3, with the cause — a string substitution that matched nothing
  and was not checked.
- A3 (review 2, the S2 response). "The ignore line moves to Task 0.2
  Step 1" describes a move that was only an addition. **Fix**: M1.
- A4 (review 2, the c2 response). "Applied and verified by grep" —
  one occurrence survived. **Fix**: c1.

## Verified without defect

- **`:::table +header` is correct and emits no warning.** The `+`
  form takes `getFlag`, which returns without logging; the deprecation
  warning is reachable only from the named-argument fallback the
  previous form took. Both sites are correct.
- **Both bibliography structures are now modelled correctly.**
  `InProceedings` has no `pages`, no `month`, no `volume`, no
  `number`; `Article` has all four, with `month` optional but
  undefaulted. Every claim in Task 1.2 Step 1 as rewritten holds, and
  the References table's three `Article` rows carry page ranges while
  its three `InProceedings` rows read "n/a".
- **All six Crossref records match**, including the two round 2
  changed. `clote`'s handbook title and series are correctly split;
  `dalLagoMartiniZorzi` as `InProceedings` is spec-mandated by §4.4
  rather than a plan choice, so dropping its month is required.
- **`inlines!` parses at `:max` with `noWs`**, so `some inlines!"…"`
  needs no parentheses, and the string gap in `leivant3`'s title
  elides correctly.
- **Gitignore-before-generate does prevent the snapshot**, `/_out`
  anchors correctly given every generator invocation is preceded by a
  `cd` into `geb-lean`, and Step 7's removal is consistent.
- **Task 3.1 Step 4's target module is elaborated.**
  `GebLeanTests.lean` reaches `GebLeanTests.Ramified.Characterization`
  transitively, the appended lines land outside any namespace, and the
  module's `GebLean` import closure contains all ten documented
  modules plus `Soundness/Collapse`, so no Appendix B name can produce
  a false negative.
- **The rewrap damaged nothing** — no list, code block or table — and
  both the plan and the review files are markdownlint-clean and
  doctoc-current.
- **Every count reproduces**: 312 raw matches with the three wrapped
  docstring lines named, 309 after stripping, 925 nolints entries, and
  the `plausible` revision matching Task 0.1's expectation.
- **The `plausible` collision is real, not theoretical**: Verso's
  manifest pins a different revision, so the whole-manifest diff and
  the explicit-pin fallback are aimed at a collision that exists.
- **`lake lint -- GebLeanDocs` is scoped as assumed**, the generated
  document object name is literally right, `manualMain`'s named
  arguments skip the auto-bound parameter correctly, and both instance
  sites resolve under `namespace GebLean.Ramified`.

## Convergence

Not converged. Three serious findings, no blockers, all three being
round-2 fixes failing in the class they answered.

The reviewer's closing recommendation is adopted: the cheapest closure
is mechanical. Task 5.1 now derives its row set from Appendix A rather
than restating a count, so that pair cannot fall out of step again;
and every substitution in this round was verified individually to have
landed, the round-2 failure having been a replacement that matched
nothing and was recorded as applied regardless. Nothing in the plan's
external facts was wrong this round — the Verso syntax, both
bibliography structures, the Crossref records, the jj semantics, the
`GebLeanTests` import closure and every numeric assertion all hold.
