# Adversarial review 3: Verso ramified-recurrence manual design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round and protocol](#round-and-protocol)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Findings against the earlier review artefacts](#findings-against-the-earlier-review-artefacts)
- [Verified without defect](#verified-without-defect)
- [Convergence](#convergence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Round and protocol

Round 3, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. Two fresh `Agent` invocations, one on
external and repository fact verification, one on internal
consistency, realizability, scope, and project-rule compliance.
Findings are deduplicated across both and categorised per
`docs/process.md` § Defect categorisation, each with a one-line
author response.

## Blockers

- B1 (section 7, name resolution). The `signature` block constructs a
  fresh `Command.State` whose default scope carries no current
  namespace, no open declarations, and default options. A chapter
  module's `open GebLean.Ramified` therefore does not reach inside the
  block, and `autoImplicit` is in force there, so an unqualified
  `AlgSig` would auto-bind as an implicit and the presentation would
  fail obscurely. The Lean reference manual's own `signature` blocks
  are fully qualified even under an ambient `open`. **Fix**: every
  name inside a `signature` block is written fully qualified, and
  section 7 states that the `open` applies to `name`, `lean` and
  `docstring` but not to `signature`.
- B2 (sections 2.3, 5, 7, 9, binder checking). SubVerso's `compare`
  reports outer binder-name, binder-info and `optParam`-default
  mismatches with `logErrorAt`, which accumulates into the nested
  `Command.State` that the block constructs; the block then retains
  only `setInfoState st'.infoState` and discards that state's
  messages. The spec's matrix row "Presented declaration's binder
  renamed | `signature` | Elaboration" was therefore false, as was
  section 5's "a retype or a renamed outer binder fails elaboration".
  The mechanical content of a `signature` block is the
  definitional-equality check on the type plus the level-parameter
  count. **Fix**: the matrix row reads "nothing / never", sections 5
  and 9 are corrected, and section 7 states that matching outer binder
  names is a convention the author observes rather than a check.
- B3 (sections 3.3, 10, 11, `docBlame`). Verso's `#doc` command emits
  per module a `def <Module>.«the canonical document object name»`
  with no doc comment. `docBlame` is an `@[env_linter]`, so it is in
  `runLinter`'s default set, and it exempts only auto-declarations and
  instances; the generated name is neither. Closing the `lake lint`
  exemption at round 2 therefore created one `docBlame` report per
  document module, on a step section 10 makes mandatory in CI, and no
  docstring can be attached to a generated definition. **Fix**:
  section 3.3 records the interaction; `scripts/nolints.json`, which
  `runLinter` reads, gains one entry per document module and becomes a
  deliverable.
- B4 (section 4.2 against sections 4.3, 5, 8, faithfulness). Part II
  chapter 5's endpoints include `collapseFunctor`'s and
  `collapseKFunctor`'s faithfulness; both are anonymous `instance`
  declarations (`Soundness/Collapse.lean`, `Characterization.lean`),
  which `docstring` cannot name by identifier, and section 8 forbade
  the only remedy. One of six named endpoints had no mechanism.
  **Fix**: referred to the user, who ruled that adding a name to an
  anonymous instance is permitted, being additive and breaking no
  client. Decision 11 records the permission; section 8 names
  `collapseFunctor_faithful` and `collapseKFunctor_faithful`,
  following the existing `yonedaConstEmbedding_faithful`.

## Serious

- S1 (section 4.3, counts). Both declaration figures were wrong and
  were produced by two mutually inconsistent methods: 181 is
  reproducible only without stripping comments, three docstring lines
  in `OmegaShift.lean` and `Examples.lean` beginning at column zero
  with a declaration keyword; 298 additionally missed thirteen
  declarations written with a leading attribute group on one line.
  The stated arithmetic did not close, 298 − 181 being 117 rather than
  the actual theorem-and-instance count. **Fix**: the figures are 309
  total, 179 definitional, 130 theorems and instances, with the
  counting method stated so the numbers are reproducible.
- S2 (sections 3.2, 9, linter classes). The spec's only linter remedy
  was a per-library `weak.linter.<name>` entry, which cannot reach the
  `@[env_linter]` set that `runLinter` runs — those are selected by
  attribute, not by options. The section had just made that set
  mandatory in CI (B3). **Fix**: section 3.2 distinguishes frontend
  linters from environment linters and gives each its remedy; open
  question 3 covers the environment case.
- S3 (sections 4.2, 4.3, `Examples.lean`). The module was in the
  covered partition, and is the second largest of the ten, but no Part
  II chapter named it, so its declarations had nowhere to be rendered.
  **Fix**: Part II chapter 4 is extended to cover it, its narrative
  reading remaining Part I chapter 5.
- S4 (sections 3.1, 3.3, 11, lint coverage). The spec adopted the
  invocation form of the `lake lint -- Geb` precedent but not the
  guard that accompanies it. `scripts/tests/test-lint-driver.sh`
  checks two invariants for `Geb`, the invocation form and that no
  module is orphaned from the umbrella and so invisible to the
  root-module invocation; the second applies identically here, and the
  path table said only that `Root.lean` includes the chapters, not
  what `GebLeanDocs.lean` imports. **Fix**: section 3.1 states the
  import chain, section 3.3 records the guard, and the script's
  extension is a deliverable.
- S5 (sections 3.1, 11, index modules). The path table gave twelve
  chapter modules under two directories with no index module for
  either, against `CLAUDE.md` § Repo structure's one-indexing-file-
  per-directory rule. **Fix**: `GebLeanDocs/Tutorial.lean` and
  `GebLeanDocs/Reference.lean` are added to the table and to the
  deliverables, which now count eighteen modules.
- S6 (section 3.1, linter reach). "`main` carries a declaration
  docstring … `lake lint` will ask for it" is false: `GebLeanDocsMain`
  is not a `Name` prefix of `GebLeanDocs` and is not imported by it,
  so it lies outside `runLinter`'s reach. No linter checks module
  docstrings either, so the round-2 disposition claiming the rule was
  "enforced rather than described" did not hold. **Fix**: the
  enforcement claim is dropped; the docstring obligations are stated
  as authored, with the CI generator build noted as what compiles the
  module.
- S7 (section 4.3, selection rule). The rule was an inclusion list
  followed by an exclusion clause with no stated precedence, and
  diverged in practice on `AlgSig.polyEndo`, `FreeAlg.mk`,
  `FreeAlg.recurse_mk`, `natToFreeAlg`, and — because clause 3 said
  "function" — the seven interpretation lemmas that Part I chapter 5
  pairs with each operation. **Fix**: exclusion governs where both
  apply, with two stated exceptions for constructors and eliminators
  of covered type formers and for a schema's reduction rule; clause 3
  covers the interpretation lemmas explicitly; decidability instances
  are excluded and their predicates covered.
- S8 (section 12, publication rationale). The rationale stated the
  workflow "triggers on unfiltered `pull_request`" when the trigger
  carries a `paths:` filter and is unfiltered only by branch. A
  defer-with-rationale must itself withstand later review, so a false
  clause inside one is the defect that requirement exists to prevent.
  The rationale also omitted the workflow's existing `pages: write`
  and `id-token: write` permissions, the fact most favourable to
  reversing the deferral. **Fix**: both corrected. The error
  originated in review 2's B2 and propagated.
- S9 (sections 8, 10, 11, change set). Under section 4.3's rule the
  docstring change set was empty — the undocumented declarations in
  the covered modules are anonymous instances and `@[simp]` theorems,
  all excluded — leaving a deliverable that would produce no diff and
  a pre-commit bullet with nothing to cover. Section 8 also scoped
  itself to ten modules while twelve contribute rendered declarations,
  and said the set is "discovered by building rather than by
  inspection" while stating an answer obtained by inspection.
  **Fix**: the docstring deliverable is marked contingent and expected
  empty; the instance-naming change (B4) makes the source-side
  deliverable non-empty and bounded; the scope is widened to twelve
  modules; the discovery claim is dropped.

## Minor

- m1 (section 3.3, "subsumes"). The generator run does not subsume
  `lake test`; there is no test target to subsume. **Fix**: stated
  plainly.
- m2 (section 3.3, axiom gate). The reuse argument that closed the
  `lake lint` case applies verbatim to the axiom gate, and the spec
  reached the opposite conclusion without distinguishing them. The
  distinguishing reason is that `lake build GebLeanAxiomChecks` is
  step 3 of the local pre-commit triad, so gating there would pull
  Verso into every `.lean`-touching commit. **Fix**: stated.
- m3 (sections 3.1, 11, output directory). The round-2 rewrite dropped
  both the output directory name and the `.gitignore` entry that round
  1 had added. **Fix**: `_out` restored in both.
- m4 (sections 10, 11, script comment). `scripts/pre-commit.sh`'s
  comment instructs the opposite of what this design does, and only
  the rule file was scheduled for amendment. **Fix**: the comment is
  amended too.
- m5 (section 6, count). "Five of the six name a position within `g`'s
  type" was inconsistent with the table, since the fifth names `g`
  itself. **Fix**: four within `g`'s type, a fifth naming `g`.
- m6 (section 6, position column). Row 1 gave the source binder name
  `b` where every other row gave an ordinal. **Fix**: ordinals
  throughout.
- m7 (section 7). "`FreeAlg.recurse` names only its first argument" is
  false of the declaration, which names `A`, `P`, `C` and `g`. **Fix**:
  scoped to within `g`'s type.
- m8 (section 7, `deftech` location). "The `deftech` definitions live
  at the Part I chapter 1 presentation alone" contradicted section 6
  and Part I chapter 3, which hold the type vocabulary. **Fix**:
  qualified to the eq. (1) vocabulary.
- m9 (section 2.1, citation). The resolution-order claim carries the
  entire require placement and was the one load-bearing external claim
  with no source pointer. **Fix**: `Lake/Load/Resolve.lean` cited for
  both `addDependencyEntries` and the reversed traversal.
- m10 (section 2.1, scope). "The resolved revisions are determined by
  Verso's tag" holds for `subverso` and `MD4Lean` but not for
  `plausible`. **Fix**: scoped to the two.
- m11 (sections 4.2, 4.3, wording). Part II chapter 5 names seven
  declarations, of which two are statements and five are definitions
  or instances. **Fix**: "endpoint declarations". *Corrected at round
  4*: the disposition changed the noun without recounting, and the
  stale "six" propagated into section 4.3 (review 4, A7).
- m12 (section 4.2, subsetting). The chapter headings were bare module
  lists with no signal that only a subset is rendered, against
  decision 9. **Fix**: a lead-in clause.
- m13 (section 13, open questions). Three matters were undecided and
  unlisted. **Fix**: the environment-linter extent is open question 3;
  the others are decided in sections 3.1 and 4.2.
- m14 (section 9, fallback). The fallback's module contents were
  unspecified, so "keeps elaboration against the real declarations"
  named a property with nothing behind it, and placement under
  `GebLeanTests/` carries gate consequences the spec elsewhere avoids.
  **Fix**: contents stated as one `example` per presented signature by
  ascription, with the gate consequence noted and why it is acceptable
  under the fallback.
- m15 (section 7, citation). Two `checkSignature` implementations
  exist at the pinned subverso revision; Verso's block calls the one
  in `SubVerso/Examples.lean`. **Fix**: cited by file.

## Cosmetic-taste

- c1 (section 10). "This is deliberate:" reproduced the defensive
  register review 2 catalogued as removed. **Fix**: restated.
- c2 (section 8). Three sentences defending against an unstated
  objection. **Fix**: reduced to one.
- c3 (section 7). "narrower than it first appears" is rhetorical
  framing of a factual constraint. **Fix**: restated.
- c4 (section 4.3). "file-local plumbing" is a metaphor of the class
  review 1 catalogued. **Fix**: "file-local auxiliaries".

## Findings against the earlier review artefacts

- A1 (review 1, Rejected section) — serious. The section sits outside
  the four mandated severities and disposes of both entries by
  "Reject", while `docs/process.md` § Author response limits
  `reject-as-cosmetic-taste` to cosmetic-taste findings. The
  decomposition entry engages `CLAUDE.md` § one concern per branch and
  is blocker-shaped; "on the user's decision" is an appeal to
  authority, not a rationale that can withstand later review. **Fix**:
  both entries are re-categorised, and the decomposition entry states
  the merits — the manual is one concern and the source-side changes
  exist because it renders them — with the user's ruling recorded as
  the decision rather than as the argument.
- A2 (review 1, m14) — minor. "Superseded" is not one of the three
  permitted responses. **Fix**: restated as a fix.
- A3 (review 2, R8) — minor. R8 recorded "gap" as restated while
  review 1 still contained it. **Fix**: the occurrence is removed and
  the disposition made true.
- A4 (review 2, c4) — minor. The rejection's outcome is right and
  procedurally permitted, but its ground is false: `docs/process.md`
  reads "Examples (where not specific technical terms) include 'land',
  'gap', and 'gate'", and the parenthetical is the carve-out under
  which "gate" is this repository's specific technical term for a
  mechanical build-time check. Worse, the artefact asserted a
  disagreement between `docs/process.md` and two rule files that does
  not exist, which under § Process self-update mechanism would oblige
  a corrective edit that is not needed. **Fix**: the rationale is
  replaced by the carve-out and the disagreement claim withdrawn.
- A5 (reviews 1 and 2, forward commitments) — minor. Both closed
  findings with "raised separately", naming no destination. **Fix**:
  the phrase is dropped. *Corrected at round 4*: this round's
  convergence note was named as the destination, which is a round
  record rather than a backlog; the taxonomy question is recorded in
  the spec's section 12 instead, so that it survives the round
  (review 4, A6).
- A6 (review 1, m6) — minor. The disposition recorded `_out` and a
  `.gitignore` entry as fixed; the round-2 rewrite dropped both.
  **Fix**: corrected, and the underlying defect is m3 above.
- A7 (review 1, marker convention) — cosmetic-taste. The Rejected
  section was restructured without the "*Corrected at round 2*" marker
  every other corrected site carries. **Fix**: marked.
- A8 (review 2, B2) — minor. "triggers on unfiltered `pull_request`"
  is false, and propagated into the spec. **Fix**: corrected in both,
  and the underlying defect is S8 above.

## Verified without defect

- **The dependency-ordering fix is correct in mechanism and in
  direction.** Verso ships a manifest at the tag pinning all three
  dependencies; `addDependencyEntries` stores an entry only when the
  name is absent; root requires are traversed in reverse declaration
  order. Declaring `verso` before `mathlib` places it last in that
  traversal, so mathlib's `plausible` is already stored and Verso's
  pin is discarded — the direction the spec intends. `cslib` pins the
  same revision as mathlib. Mathlib's `plausible` is three commits
  later than Verso's, so open question 1 asks whether Verso builds
  against a newer revision.
- **Section 9's acceptance criterion is checkable and sufficient.** A
  bare `lake update` reuses nothing from the existing manifest,
  `mathlib` and `cslib` are tag-pinned and re-resolve identically, and
  `plausible` is the only package shared between the two closures.
- **Option precedence is now stated correctly**, and the `weak.`
  prefix behaviour matches `lakefile.toml`'s recorded rationale.
- **The entry point typechecks.** `options` is explicit without a
  default, `config` is a defaulted `RenderConfig`, and `sourceLink`
  and `issueLink` are `HtmlConfig` fields reached through it; the
  sketch correctly skips the defaulted `extensionImpls`.
- `lake lint -- <name>` takes a module name, and the library name
  coinciding with its root module name is what makes the invocation
  work for both `Geb` and `GebLeanDocs`.
- `RIdent.mrec` and `RIdent.frec` name every outer binder, carry no
  instance arguments, and have no universe parameters, so their
  presentations need no level annotation.
- The `signature` fence language, the `show` option, and the
  type-mismatch path throwing and recording a suggestion are all as
  stated.
- The module partition is exact and exhaustive over the forty-seven
  files under `GebLean/Ramified/` and its index module.
- Bibliography entry types, and `Article`'s undefaulted `volume`,
  `number` and `month`, are as stated.
- The `docstring`, `deftech` and `tech` timing claims, including that
  ambiguity is reported only when a `tech` reference resolves against
  a duplicated key.
- Every path named in section 11 exists or is correctly described as
  to be created; `scripts/pre-commit.sh` carries the comment section
  10 describes.
- All documents are markdownlint-clean and doctoc-current.

## Convergence

Not converged. Round 3 raised four blockers and nine serious findings,
all fixed in the spec at this branch. Round 4 is required: three
sections were rewritten rather than repaired, one decision was
referred to the user and answered during the round, and both blockers
B1 and B2 concern what a mechanism actually does, which is the class
of claim that has produced a defect in every round so far.

Two observations for the author. B3 and S2 are defects that a round-2
*fix* introduced: closing the `lake lint` exemption brought in a
linter class whose remedy the spec did not have. And S1's counting
error came from greps run without stripping comments, the same
verification shortfall that produced round 1's external errors.

A matter beyond this spec: the Majors / Minors / Nits taxonomy that
rounds 1 and 2 used is not defined by `docs/process.md` § Defect
categorisation, and is used by part of the repository's earlier
committed review artefacts. Whether those are re-categorised, or
`docs/process.md` is amended to admit the form in use, is for the user
to decide. *Corrected at rounds 6 and 7*: this note first claimed the
form was used by every earlier artefact, which is false; the round-6
correction then recorded a 65 / 49 / 148 split that does not reproduce
(review 6, S3 and A1; review 7, S2). The item lives in `TODO.md`,
scoped by criterion rather than by a count.
