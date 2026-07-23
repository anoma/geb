# Adversarial review 2: Verso ramified-recurrence manual design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round and protocol](#round-and-protocol)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Findings against the round-1 artefact](#findings-against-the-round-1-artefact)
- [Verified without defect](#verified-without-defect)
- [Convergence](#convergence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Round and protocol

Round 2, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. Two fresh `Agent` invocations, one on
external and repository fact verification, one on internal
consistency, realizability, scope, and project-rule compliance.
Findings are deduplicated across both and categorised per
`docs/process.md` § Defect categorisation. Each carries a one-line
author response: fix, defer with rationale, or reject as
cosmetic-taste.

Round 1's artefact used a Majors / Minors / Nits taxonomy, which
`docs/process.md` does not define and against which the convergence
criterion (no blockers, no serious findings) cannot be evaluated.
That artefact is re-categorised in place; see
[Findings against the round-1 artefact](#findings-against-the-round-1-artefact).

## Blockers

- B1 (section 3.1, require placement). Lake resolves root requires in
  reverse declaration order and takes the first entry per package
  name, so appending the `verso` require at the end of
  `lakefile.toml` — as the spec instructed — processes Verso first and
  lets its `plausible` pin (`650d4104`) displace mathlib's
  (`e84e3e16`). That is the mathlib-rebuild outcome section 9 declares
  unacceptable, caused by the spec's own instruction. The stated
  rationale for appending concerns positional
  `[lean_lib.leanOptions]` subtables and does not apply to
  `[[require]]` blocks. **Fix**: the require is placed ahead of
  `mathlib`; section 2.1 states the ordering rule; section 9 makes the
  unchanged `plausible` entry a literal acceptance criterion verified
  in a scratch clone.
- B2 (section 3.4, publication). The section was five sentences resting
  on one true fact, the workflow's permissions block. Verified:
  `anoma/geb` already serves a Pages site (`build_type: workflow`,
  `<title>The GEB Manual</title>`), and a repository has one site,
  which `actions/deploy-pages` replaces wholesale; `rokopt/geb` has
  `has_pages: false`, and the fork is where topic-branch CI runs; the
  workflow has no deployment job, no `environment: github-pages`, no
  artifact upload, and triggers on `pull_request`; the
  mandated upstream route is a cross-repository pull request, whose
  token is read-only and carries no `id-token`, so a deploy step fails
  on every upstream PR; `.claude/rules/ci-and-workflow.md` § Action
  pinning policy is unaddressed; and enabling Pages is a
  repository-settings deliverable. *Corrected at round 3*: this entry
  described the `pull_request` trigger as unfiltered; it carries a
  `paths:` filter and is unfiltered only by branch, and the error
  propagated into the spec (review 3, S8). **Fix**: publication is
  deferred to its own workstream by decision; section 12 records the
  facts above so the deferral is auditable.
- B3 (section 7, binder names). `SubVerso.Examples.checkSignature`
  compares binder names on every top-level `forallE` and reports
  `Mismatched parameter name`, recursing only into the body and never
  into a binder's type. The spec's claim that binder names are "chosen
  by the author" is false; the `FreeAlg.recurse` presentation is legal
  only because every renamed position lies inside `g`'s type.
  Relatedly, the four sites named were not four declarations: eq. (4)
  and eq. (5) are not declarations, and `RIdent.mrec` / `RIdent.frec`
  already name every binder, so the stated motivation does not apply
  there. **Fix**: section 7 states the actual rule, notes that a name
  mismatch is logged rather than thrown and so yields no editor
  suggestion, and names the three declarations presented and what each
  presentation is for.
- B4 (section 3.2, option precedence). The spec asserted that a
  per-library `leanOptions` entry "cannot override a package-level
  `moreLeanArgs` flag in any case". Precedence runs the other way:
  Lake passes `moreLeanArgs` on the command line and `leanOptions` in
  the module setup, and Lean merges setup-wins
  (`Lean/Elab/Frontend.lean`). A per-library
  `warningAsError = false` would defeat the package flag, in a library
  outside the axiom gates. **Fix**: the false reassurance is replaced
  by a statement that the retention is a rule this design observes,
  not a property the build enforces.
- B5 (section 3.3, `lake lint`). The exemption was named and accepted
  on grounds transferred from the axiom linter, which do not apply:
  `runLinter` catches `docBlame`, `unusedArguments`, `dupNamespace`
  and others, none of which `warningAsError` addresses. The repository
  already has the pattern for linting a non-default library —
  `lake lint -- Geb` in `geb-mathlib-refresh.yml`, guarded by
  `scripts/tests/test-lint-driver.sh`, which exists so that no module
  silently escapes the linter — and the spec did not reuse it, against
  `CLAUDE.md` § Reuse existing process code. **Fix**: the exemption is
  closed; CI runs `lake lint -- GebLeanDocs`.
- B6 (sections 3.1, 4.4, entry point). Two defects that together make
  the entry point unimplementable. The code sketch passed no `config`
  while the following sentence said `config` supplies the repository
  links, so an implementer cannot tell which parameter carries them;
  and `%doc` yields one `Part` while section 4.4 described "two
  top-level `Part` structures", which `manualMain` cannot consume.
  **Fix**: section 3.1 gives the entry point with `options` and
  `config` both passed; section 4.4 states one root `Part` with the
  two parts as children.

## Serious

- S1 (section 4.3, coverage). "Covered, declaration by declaration"
  across ten modules committed to 298 top-level declarations without
  saying so, leaving the document unsizable and admitting artifacts
  differing by an order of magnitude. **Fix**: section 4.3 states the
  count and its definitional subset (181), gives an explicit selection
  rule, and makes enumerating the resulting set the first task of Part
  II's phase, committed to the plan.
- S2 (sections 2.1, 9, reproducibility). "Not reproducible from
  Verso's tag alone" is false: Verso ships a `lake-manifest.json` at
  the tag pinning all three dependencies, and Lake resolves inherited
  dependencies from the dependency's own manifest. **Fix**: section
  2.1 states the manifest mechanism and relocates the real exposure to
  resolution order (B1).
- S3 (section 9, fallback). The Markdown fallback claimed to keep
  "signature checking against the real declarations", but
  `checkSignature` is `subverso`'s, and `subverso` failing to resolve
  is the fallback's trigger. **Fix**: the fallback is stated to lose
  signature checking with the rest, keeping only elaboration against
  the real declarations.
- S4 (section 11, primed layer). "The tutorial half is unaffected" is
  false: Part I chapters 1, 3, 4 and 5 sample legacy declarations by
  name, so retiring them fails every `name` role and `signature` block
  in Part I. **Fix**: section 12 states that Part I's prose is
  unaffected but its sampled declarations are repointed alongside Part
  II's.
- S5 (sections 3.3, 10, compensation). Section 3.3's forward reference
  to a compensation recorded in section 10 was unsatisfied; section 10
  recorded none. **Fix**: section 3.3 now states each exemption's own
  ground inline, and distinguishes the three accepted from the one
  closed.
- S6 (references). Four of eight references had no body citation.
  Round 1 raised this for one work and fixed only that instance.
  **Fix**: Part I chapter 6 cites Ritchie, Clote, Leivant I, and
  Bellantoni and Cook at the cells they establish; the reference list
  states where each is cited.
- S7 (sections 3.1, 4.4, module organisation). The library needs
  twelve chapter modules, a root, a bibliography module, an index and
  a main; the spec named three and specified no naming scheme.
  **Fix**: section 3.1 carries a path table.
- S8 (section 4.4, bibliography). Verso offers four entry types, and
  three of the six cited works are book chapters or proceedings
  contributions that must be entered as `InProceedings`; `Article`
  requires `volume`, `number` and an explicit `month`, none defaulted.
  **Fix**: section 4.4 records both.
- S9 (section 3.1, `manualMain`). `options` is an explicit parameter
  with no default, so the spec's prose describing an alternative in
  which arguments are not threaded described something that does not
  typecheck. **Fix**: the prose is corrected; the sketch was already
  right.
- S10 (section 4.3, partition). The partition named directories while
  the corresponding index modules `Definability.lean`,
  `Soundness.lean`, `Polynomial.lean` and the area index
  `GebLean/Ramified.lean` went unclassified. **Fix**: all four are
  named in the absent list.
- S11 (section 2.3, coverage decay). The check matrix had no row for a
  declaration added to a covered module, so "declaration by
  declaration" was a promise with nothing behind it and coverage could
  decay while every gate stayed green. **Fix**: the matrix carries the
  row with "nothing / never", and section 2.3 states the limitation.

## Minor

- m1 (section 1, decision 3). Listed three exclusions where section
  3.3 names four. **Fix**: the lint driver is added to the decision.
- m2 (section 3.2, weak linters). The remedy ignored the repository's
  own recorded hazard, that the non-weak `linter.<name>` form errors
  when the defining module is not imported. **Fix**: the remedy uses
  `weak.linter.<name>`.
- m3 (sections 2.2, 4.4, citations). `citep` / `citet` were assigned
  to Part I chapter 6 alone, while chapters 1 to 5 and Part II chapter
  6 also cite the paper. **Fix**: the facility table says "throughout
  both parts".
- m4 (sections 5, 8). "Part II, predominantly" admitted `docstring`
  use in Part I, whose declarations then fell outside section 8's
  change set while still failing elaboration if undocumented.
  **Fix**: `docstring` is Part II only, stated in both sections.
- m5 (section 12, open questions). Two open questions was not honest
  while chapter module names, the publication target, and the extent
  of the `deftech` vocabulary were all undecided. **Fix**: the first
  two are decided (sections 3.1, 12); the third is open question 3.
- m6 (section 8, branch count). The spec said "one plan" while
  `CLAUDE.md` § one concern per branch governs branches. **Fix**:
  decision 10 states one plan on one branch.
- m7 (throughout, deliverables). No consolidated deliverable list; the
  `lake-manifest.json` change was implied but never listed, though it
  is a committed file. **Fix**: section 11.
- m8 (section 6). "Four of the six terms name a binder" was at odds
  with the table, which concedes `g` is one. **Fix**: five of six,
  with the recurrence argument distinguished.
- m9 (section 3.1, module docstrings). Chapter modules must satisfy
  `.claude/rules/lean-coding.md` § Comment and docstring rules, and
  nothing was said about how. **Fix**: `main` carries a docstring and
  `lake lint` now reaches the library (B5), so the rule is enforced
  rather than described.
- m10 (section 7, fence). The presentation was shown in a `text`
  fence without stating the actual fence language or the `show`
  option. **Fix**: both stated.
- m11 (section 2.3, duplicate terms). The row overstated: a `deftech`
  duplicated but never referenced is not reported. **Fix**: the row
  and the prose distinguish the referenced case.
- m12 (section 6, row 1). "constructor label | `c_i` | none given" was
  not in the design spec's glossary, which applies "no dedicated name"
  to the subterms, not to `c_i`. **Fix**: row 1 reads "constructor".
- m13 (section 6, terminology). "object sort" and "`Omega`-sort" were
  used where the glossary says "object type" and "`Omega`-type".
  **Fix**: aligned to the glossary.
- m14 (section 10, action pinning). CI additions did not mention
  `.claude/rules/ci-and-workflow.md` § Action pinning policy.
  **Defer with rationale**: with publication deferred (B2), the CI
  addition is a `run:` step invoking `lake`, which uses no third-party
  action, so the policy has nothing to bind. It binds the publication
  workstream instead, and section 12 records it there.

## Cosmetic-taste

- c1 (throughout). Defensive register introduced by the round-1
  rewrite: "not an afterthought", "The consequence is recorded
  plainly", "This is a deliberate decision, not an omission", "Both
  are deliberate". **Fix**: removed or restated as plain statements.
- c2 (section 3.2). Filler: "Note that Lake composes …" and "… in any
  case". **Fix**: removed with the sentence they qualified (B4).
- c3 (section 2.3). "Three points govern the design and each was
  verified against Verso's source at the pinned tag" asserts the act
  of verifying, which `docs/process.md` § Document only the persistent
  excludes. **Fix**: the citations remain, the assertion goes.
- c4 (spec, ten occurrences). "gate" / "gates" appears in
  `docs/process.md` § Avoid colloquialisms and metaphors' example
  list. **Reject as cosmetic-taste**: that list reads "Examples (where
  not specific technical terms) include 'land', 'gap', and 'gate'",
  and the parenthetical is the carve-out. "Gate" is this repository's
  specific technical term for a mechanical build-time check, as
  `CLAUDE.md` and `.claude/rules/ci-and-workflow.md` both use it, so
  the carve-out applies and the rule is satisfied as written.
  *Corrected at round 3*: this entry previously asserted a
  disagreement between `docs/process.md` and the two rule files. There
  is none, and the claim is withdrawn (review 3, A4).

## Findings against the round-1 artefact

- R1. Round 1's M6 disposition claimed section 3.3 "records the
  exemptions as decisions with their compensation". No compensation
  was recorded anywhere. **Fix**: the disposition is corrected in
  place, and the underlying defect is S5 above.
- R2. Round 1's N1 claimed metaphor "Fixed throughout" while listing
  items that remained in the artefact, and listed "bridge equivalence"
  as a metaphor although it is established repository terminology
  (`docs/areas/ramified-recurrence.md`). **Fix**: the disposition is
  corrected and the term removed from the list.
- R3. Round 1's Disposition claimed all nine majors "fixed", including
  the publication major, while its "Verified without defect" list
  predated the publication decision and verified nothing in that
  section. **Fix**: the disposition is qualified; B2 records what
  verification then found.
- R4. Round 1's Rejected section answered a cost objection by raising
  cost to raise return without comparison, merged two distinct
  recommendations into one disposition, and gave a one-clause
  rationale for a finding it had itself classed major, against
  `docs/process.md` § Author response. **Fix**: the rationale is
  restated per finding; the publication half is superseded by B2's
  deferral.
- R5. Round 1's taxonomy departed from `docs/process.md` § Defect
  categorisation, leaving the round's convergence status formally
  undetermined. **Fix**: round 1 is re-categorised in place and this
  round uses the mandated severities. The same departure appears in
  earlier committed review artefacts in this repository; that is
  recorded in review 3's convergence note as a matter for the user,
  and is not acted on here.
- R6. Round 1 attributed outcomes to an unnamed decider ("Resolved by
  decision"), obscuring whether the author or the user decided.
  **Fix**: decisions referred to the user are marked as such.
- R7. Round 1 recorded how an error was made ("The original check used
  a URL-encoded path separator and returned 404") and a judgment about
  drafting rather than about the artefact. **Fix**: both removed per
  `docs/process.md` § Document only the persistent.
- R8. Round 1 used "gap" and "live option". **Fix**: restated.
  *Corrected at round 3*: "gap" survived the round-2 edit and is
  removed now (review 3, A3).
- R9. Round 1's m13 justified indexing from `docs/index.md` by citing
  a requirement `docs/process.md` does not state. **Fix**: the
  deliverable stands on its own terms; the citation is dropped.
- R10. Round 1's "Verified without defect" claimed every reference
  agreed with the design spec on title, while its own N7 changed the
  Dal Lago title case away from the design spec's. **Fix**: the claim
  is qualified; this spec follows the published EPTCS form.

## Verified without defect

- Reservoir indexes `leanprover/verso`; `scope = "leanprover"` is
  correct and matches the `mathlib` and `cslib` require form.
- Verso's toolchain matches this repository's; its requires are
  exactly `subverso`, `MD4Lean`, `plausible`;
  `precompileModules := false`.
- The `signature` block exists with category
  `("def" <|> "theorem")? declId declSig`, the leading keyword
  optional and ignored, and the spec's `FreeAlg.recurse` presentation
  parses and is legal against `GebLean/Ramified/AlgSig.lean`. A
  genuine retype throws and does record an editor suggestion.
- `manualMain`'s default output is `_out`; the error counter returns 1
  on any logged error, so the CI generator run does gate generation-
  time findings. `%doc` is well-formed over a module containing one
  `#doc (Manual)` command.
- Every row of the facility table resolves to a real declaration of
  the stated kind at the pinned tag.
- The `lintDriver`, `testDriver`, `defaultTargets`, `moreLeanArgs` and
  `mathlibStandardSet` claims, and the `GebLeanAxiomChecks` gate set
  verified from `GebLeanAxiomChecks/` sources.
- Every Lean declaration named in sections 4.1, 4.2 and 7 exists under
  `namespace GebLean.Ramified`; the module partition is exact on files
  apart from S10.
- Every reference agrees with the area document and the design spec on
  author list, venue, year, page range and DOI.
- Section 6's terminology rows agree with the design spec's glossary
  apart from m12; the paper-location claims for eqs. (1), (4), (5) and
  sections 2.4, 2.7 and 6.1 all check out.
- Sections 6 and 7 are consistent on anchor placement; the chapter-3
  type vocabulary has a defined home.
- Both documents are markdownlint-clean and doctoc-current.

## Convergence

Not converged. Round 2 raised six blockers and eleven serious
findings, all fixed in the spec at this branch except m14, deferred
with rationale, and c4, rejected as cosmetic-taste. Round 3 is
required: the fixes are extensive, three sections were rewritten
rather than repaired, and two decisions were referred to the user and
answered during the round, so the artefact round 3 reads differs
substantially from the one round 2 read.
