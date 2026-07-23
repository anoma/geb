# Adversarial review 4: Verso ramified-recurrence manual design

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

Round 4, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. Two fresh `Agent` invocations, one on
external and repository fact verification, one on internal
consistency, realizability, scope, and project-rule compliance.
Findings are deduplicated across both and categorised per
`docs/process.md` § Defect categorisation, each with a one-line
author response.

## Blockers

None. This is the first round without one.

## Serious

- S1 (sections 2.3, 3.2, 5, 9, 13, a third diagnostic class). Verso's
  `lean` block calls `warnLongLines` unconditionally, gated by
  `verso.code.warnLineLength` with `defValue := 60`. It is not a
  linter, so neither the `weak.linter.<name>` remedy nor
  `scripts/nolints.json` reaches it, and `-DwarningAsError=true`
  promotes it to a build error. The effective limit is 60 columns plus
  indentation, against this project's 100-column style rule, so a
  single Part I illustration line at 72 columns would fail the CI
  generator build. The two-class taxonomy had no slot for it. A second
  instance of the same root cause: `verso.docstring.elabMarkdown`
  defaults true, and an inline code span that no elaboration heuristic
  accepts warns, though the last-resort keyword highlighter makes that
  rare. **Fix**: section 3.2 now states three classes with three
  remedies, naming both options; sections 2.3, 9 and open question 2
  follow.
- S2 (sections 3.1, 4.4, index modules). The path table described
  `Tutorial.lean` and `Reference.lean` as import indexes while section
  4.4 conscripted them into the `Part` hierarchy, describing a Lean
  import graph and a Verso document hierarchy as one structure.
  `{include NAME}` resolves
  `NAME.«the canonical document object name»`, which exists only where
  `NAME` itself carries a `#doc`, so import-only index modules would
  make `Root.lean` fail to elaborate. The shape the spec intends is
  valid — `doc/UsersGuide/Releases.lean` in Verso's own tree is both
  an import index and a `Part` with children — but the spec never said
  the index modules carry a `#doc`. **Fix**: the path table states
  that every module in the hierarchy carries exactly one `#doc`, with
  the two facts that force it, the `{include N NAME}` level parameter,
  and where part titles live.
- S3 (sections 3.1, 3.3, bibliography in the import graph). The stated
  chain omitted `GebLeanDocs/Bibliography.lean`, which the chapters
  must import for `citep` and `citet` to resolve, while section 3.3
  made that chain the invariant the extended guard checks. A guard
  written from the stated chain would report the delivered tree as
  orphaning it. **Fix**: `Root.lean` imports it, and section 3.3 names
  it.

## Minor

- m1 (section 8, count). "nine `@[simp] theorem`s" is eight. **Fix**.
- m2 (sections 3.3, 11, nolints scope). `lean` blocks keep their
  environment by default, so a `def` written in one becomes a real
  declaration of the chapter module and is seen by `docBlame`. One
  entry per document module undercounts. **Fix**: the scope is
  extended.
- m3 (section 3.1, prefix relation). The load-bearing fact is that
  `GebLeanDocs` is not a `Name` prefix of `GebLeanDocsMain`, not the
  converse the spec stated. **Fix**: reversed.
- m4 (section 3.1, orphan hazard). The stated hazard — a chapter
  reachable from `Root.lean` but not from `GebLeanDocs.lean` — cannot
  occur, since `{include}` requires the module to be imported. The
  real hazard is a module no index imports at all. **Fix**: restated.
- m5 (section 7, internal contradiction). "only the type is enforced"
  dropped the level-parameter count that the preceding sentence
  states, and that `checkSignature` throws on. **Fix**: both named.
- m6 (section 3.3, axiom gate). The decline presented two options when
  a CI-only placement is a third, and led with the placement argument
  rather than the substantive one. **Fix**: the substantive ground
  leads; the placement argument is qualified.
- m7 (section 11, wording). The "contingent" qualifier scoped over
  both the instance naming, which section 8 says is required, and the
  docstrings, which it says are contingent; and `GebLeanDocsMain.lean`
  was counted among the library's modules while section 3.1 states it
  is outside the library. **Fix**: split into two bullets;
  seventeen library modules and the executable root.
- m8 (sections 4.3, 8, decidability). `instance : DecidableEq RType`
  is a decidability instance of a covered *type*, which the exclusion
  clause named only for predicates. **Fix**: the clause covers both;
  section 8 says "none of which the rule covers" rather than "all of
  which the rule excludes".
- m9 (section 11, documentation consistency).
  `.claude/rules/ci-and-workflow.md` describes `test-lint-driver.sh`
  entirely in `geb-mathlib` terms, and
  `.claude/rules/lean-coding.md` § Documentation makes a docstring
  mandatory for every `def` while Verso's generated definitions can
  carry none. Leaving either to contradict the practice is what
  section 10 refuses to do for `scripts/pre-commit.sh`'s comment.
  **Fix**: both amendments are deliverables.
- m10 (section 13, open questions). Part II's covered-set enumeration
  received the same plan-committed treatment as the `deftech`
  vocabulary but was not listed alongside it. **Fix**: both are open
  question 4.
- m11 (section 7, failure mode). "fail obscurely" mischaracterises it:
  an auto-bound name changes the type or the level-parameter count,
  and both paths throw with both signatures printed and an editor
  suggestion recorded. **Fix**: restated.
- m12 (sections 11, 13, nolints production). The settling event was
  the first CI run, though a local `lake lint -- GebLeanDocs` settles
  it and section 11 needs the answer to author the file. Separately,
  `runLinter --update` rewrites `scripts/nolints.json` wholesale from
  the current run, which would discard the entries already there.
  **Fix**: the local run is the settling event, and section 3.3
  records that entries are appended manually.
- m13 (section 2.3, row 1). `signature` also resolves its target by
  name and so also fails elaboration on a rename or removal. **Fix**:
  added to the row.
- m14 (section 3.1, module keyword). `.claude/rules/lean-coding.md`
  § Lean 4 module system requires `module` in every `.lean` file,
  under which Verso's non-`public` generated `def` would not be
  exported and `%doc` could not reach it. No file in this repository
  currently uses `module`, so the rule is dormant. **Fix**: the
  exemption is recorded in section 3.1.

## Cosmetic-taste

- c1 (section 3.3). "fires" returned, being on the list review 1
  recorded as removed. **Fix**: "reports".
- c2 (section 2.3). "limitations this design accepts rather than
  oversights" is the defensive register review 2 catalogued. **Fix**:
  removed.
- c3 (section 4.2). Chapter 4's title used "instances" in the
  example-instantiation sense in a document that uses `instance` in
  the Lean sense nearby. **Fix**: "instantiations".
- c4 (section 7). The `signature` syntax category admits an optional
  leading `def` or `theorem`, unmentioned. **Fix**: stated.
- c5 (section 7). "Every name inside a `signature` block is written
  fully qualified" sat beside an example using `A.B` and `Fin`.
  **Fix**: "every global name", with the field-notation case stated.
- c6 (section 8, notation). "`collapseFunctor.Faithful` … are
  anonymous" names a type where a declaration is meant. **Reject as
  cosmetic-taste**: it follows the source modules' own docstring
  bullets, so it is the repository's notation for the instance rather
  than an error.
- c7 (naming digest). `.claude/rules/lean-coding.md` lists `instance`
  under lowerCamelCase and so does not literally endorse
  `collapseFunctor_faithful`. **Reject as cosmetic-taste**: mathlib's
  naming guide governs terms of `Prop`s, `Functor.Faithful` is a
  `Prop` class, the rule file states the full guides supersede its
  digest, and the repository precedent agrees. The spec is correct and
  the digest is what is imprecise.

## Findings against the earlier review artefacts

- A1 (review 3, S3) — minor. "`Examples.lean` … is the largest of the
  ten" is false; `OmegaShift.lean` is larger by declarations and by
  lines. The finding's substance stands. **Fix**: "second largest".
- A2 (review 1, Rejected section) — serious. Round 3's fix labelled
  the two entries but left them in a section headed *Rejected* that
  then contained an entry disposed as fixed — worse than the state it
  found, since `docs/process.md` admits four severities and no section
  named after a disposition. **Fix**: the section is removed, the
  first entry becomes cosmetic-taste c9 and the second serious S5.
- A3 (review 1, convergence count) — minor. The count did not follow
  the re-categorisation. **Fix**: five blockers and five serious.
- A4 (review 1, decomposition rationale) — serious. "The concern is
  the manual, and each component exists because of it" is satisfied by
  any bundle sharing a motivation, so it does not discriminate and the
  rule would never bind. The criterion that does the work is
  required-by versus discovered-during, which section 8 supplies and
  the rationale omitted. The closing sentence also treated deferring
  publication as answering the cost objection, when deferral removes
  the return the objection said was missing; the answer is section
  12's statement of the interim return. **Fix**: both restated in S5.
- A5 (review 1, marker convention) — minor. Six sites carry the italic
  correction marker and four record corrections in bare parentheses.
  **Fix**: one form throughout.
- A6 (review 3, referral destination) — minor. Naming this round's
  convergence note as the destination for the repository-wide taxonomy
  question puts a backlog item in a round record. **Fix**: it is a
  section 12 bullet in the spec, and review 3 points there.
- A7 (review 3, m11 arithmetic) — minor. The disposition changed the
  noun without recounting, and the stale figure propagated into
  section 4.3. **Fix**: seven declarations, two statements and five
  definitions or instances.
- A8 (review 1, B2) — cosmetic-taste. "hand-rolled". **Fix**:
  "defined".

A consequence worth recording: `docs/process.md`'s convergence
criterion is stated over a round's findings without distinguishing
their target, so a serious finding against a review artefact blocks
convergence exactly as one against the spec. Round 3 was therefore
non-converged on its own A1 independently of its four blockers, and
this round is non-converged on A2 and A4 independently of S1 to S3.

## Verified without defect

- **Every mechanism claim holds against source.** The `signature`
  block's empty scope and `autoImplicit`, the discarded binder
  diagnostics, the surviving type and level-parameter checks, the
  editor suggestion on any thrown error, and the fully-qualified
  `FreeAlg.recurse` presentation traced through to definitional
  equality against the real declaration. Generalized field notation
  resolves by the local's type head, so `A.B` and `A.ar` need no
  qualification; `FreeAlg.recurse` has zero level parameters.
- **The counts reproduce exactly**: 309 = 179 definitional + 130
  theorems and instances, per-module figures matching, the six
  declaration kinds exhaustive. Round 3's diagnosis of the earlier
  error is independently reproducible.
- **The `docBlame` interaction and its remedy both hold.**
  `scripts/nolints.json` exists at that path with 960 lines,
  `runLinter` reads it from the literal relative path that the
  workflow's `working-directory` resolves, the entry format is
  `[linterName, declarationName]`, and the generated name string is
  exact and round-trips through `String.toName`'s escape stripping.
  `docBlame` is the only plausible firing environment linter, the
  other twelve having been enumerated and excluded.
- **The dependency-ordering reasoning, end to end**, including that a
  bare `lake update` reuses nothing from the existing manifest, so
  section 9's acceptance criterion is a real test.
- **The instance naming.** `yonedaConstEmbedding_faithful` exists as
  cited; both targets are anonymous at the cited lines and already
  carry docstrings; neither new name collides.
- **The entry point, `_out` and its `html-multi` subdirectory, the
  facility table, the docstring and terminology timing, the
  `lake lint` precedent and guard, option precedence, the lakefile
  mechanics, the bibliography entry types, and section 12's four
  publication clauses** — all as stated.
- **Section 4.3's precedence rule now yields a near-determinate set.**
  Applied independently to `AlgSig.lean`, `RType.lean` and
  `Examples.lean` it resolves the cases round 3 named as divergent,
  and summed over the twelve contributing modules selects on the order
  of eighty to ninety declarations, inside the stated band.
- **Section 9's `example`-based fallback is not a reuse violation.**
  Round 1's objection was to hand-building the idiom in place of
  `signature`; the fallback is reached exactly when `subverso` cannot
  be resolved, which the section says.
- Sections 8, 10 and 11 are consistent on the source-side change set
  once m7's wording is fixed; decision 11's scope matches section 8's
  application, the four `RType.lean` instances included.
- All documents are markdownlint-clean and doctoc-current.

## Convergence

Not converged. Three serious findings against the spec (S1 to S3) and
two against the review artefacts (A2, A4), no blockers. All are fixed
at this branch.

The character of the round differs from its predecessors. No blocker
was raised, and the class of defect that produced one in each of the
first three rounds — a false claim about what a mechanism does — is
absent: every such claim in sections 2.1, 2.3, 3.2, 3.3, 7 and 9 was
checked against source and held. S1 is not a false claim but an
incomplete taxonomy, and S2 and S3 are under-specifications in a
section added at round 3. The residual class is bookkeeping: counts,
prefix relations, list scopes. A stated count has contradicted its
adjacent enumeration in four consecutive rounds, so a mechanical pass
over every numeral and cross-reference precedes the next dispatch.
