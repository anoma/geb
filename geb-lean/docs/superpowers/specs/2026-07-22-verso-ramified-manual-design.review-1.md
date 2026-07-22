# Adversarial review 1: Verso ramified-recurrence manual design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round and protocol](#round-and-protocol)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Verified without defect](#verified-without-defect)
- [Convergence](#convergence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Round and protocol

Round 1, 2026-07-22, against the spec at branch
`docs/verso-ramified-manual`. Two fresh `Agent` invocations, one on
external and repository fact verification, one on internal
consistency, realizability, scope, and project-rule compliance.
Findings are deduplicated across both and categorised per
`docs/process.md` § Defect categorisation, with a one-line author
response each.

This artefact was first written with a Majors / Minors / Nits
taxonomy, which `docs/process.md` does not define and against which
the convergence criterion cannot be evaluated. It is re-categorised
here. Eleven findings carry a correction recorded by a later round,
marked in place with the round that made it; a twelfth marker sits in
the Verified-without-defect list. Four record a disposition
that overstated what had been fixed (S2, S4, m11, c1); four record a
fix that rested on a further false claim (B2, B4, S1, c4); and three
record a change of substance made later (m6, m14, S5).

## Blockers

- B1 (sections 2.3, 5, 9). The spec asserted that `{docstring}` fails
  `lake build` on "a renamed or retyped declaration". The retype half
  is false: the block resolves its argument and then renders whatever
  signature the environment holds, so a retype is re-rendered without
  error. Declaration drift was the stated justification for the
  dependency, so half that justification did not exist. **Fix**:
  section 2.3 carries a per-change check matrix; retypes are assigned
  to the `signature` block.
- B2 (section 7). Verso ships
  `VersoManual/InlineLean/Signature.lean`, a `signature` code block
  that checks a written signature against the real declaration through
  `SubVerso.Examples.checkSignature`. The spec defined an
  `example`-with-real-right-hand-side idiom for the same purpose and
  deferred a custom block extension to future work, against
  `CLAUDE.md` § Reuse existing abstractions. **Fix**: section 7 is
  rebuilt on `signature`; the deferred extension is removed.
  *Corrected at round 2*: the accompanying claim about binder-name
  latitude is false (review 2, B3).
- B3 (section 2.1). "Verso is not published on Reservoir" is false;
  `leanprover/verso` is indexed with `v4.29.0-rc6` among its versions.
  The stated reason for the `git` / `rev` require form was therefore
  wrong, and the form diverged from the `scope` / `rev` form the
  existing `mathlib` and `cslib` requires use. **Fix**:
  `scope = "leanprover"`.
- B4 (sections 3, 9). The proposed per-library override of
  `-DwarningAsError=true` would have legalised `sorry` in a library
  the spec also placed outside the `GebLeanAxiomChecks` gates, against
  `CLAUDE.md` § `sorry`, `admit`, and underscores. **Fix**: section
  3.2 retains `warningAsError` and narrows any override to a named
  linter. *Corrected at round 2*: the accompanying precedence claim is
  itself false (review 2, B4).
- B5 (sections 1, 3, 9, 10). "Built on demand" was contradicted by
  section 10's addition of the generator to `scripts/pre-push.sh`,
  which is mandatory before every push regardless of files touched, so
  every contributor would build Verso and three transitive
  dependencies on every push. **Fix**: referred to the user, who chose
  a CI-only gate; the "on demand" framing is removed and section 10
  states what the local scripts no longer cover.

## Serious

- S1 (section 9). "`plausible` is required by both mathlib and Verso
  at different revisions" is false as a Lake-resolution problem: both
  request it at `main`, and the manifest pins it, so the stated risk
  and the first fallback were vacuous. **Fix**: section 9 restates the
  exposure. *Corrected at round 2*: the two manifests do pin different
  revisions, and the real exposure is resolution order (review 2, B1
  and S2).
- S2 (section 3). `lintDriver = "batteries/runLinter"` lints the root
  modules of the default targets, so the new library escapes
  `lake lint`, step 2 of the mandatory pre-commit triad. The spec
  enumerated three exclusions and did not mention the fourth.
  **Fix**: section 3.3 states all four. *Corrected at round 2*: the
  original disposition also claimed the exemptions were recorded "with
  their compensation", which they were not; the exemption was closed
  only at round 2 (review 2, B5).
- S3 (section 7 against sections 2.3 and 6). Reusing one presentation
  at four sites with binder names as `deftech` anchors would define
  each term four times, which `deftech` reports as ambiguous. **Fix**:
  the definitions are assigned to the first site alone.
- S4 (scope). The reviewer argued the spec bundles four separable
  workstreams and that the return did not justify the dependency while
  publication remained out of scope, an unpublished manual having no
  reader who is not already building the repository. **Fix**: referred
  to the user, who chose to bring publication into scope and to
  proceed as one plan. *Corrected at round 2*: bringing publication
  into scope proved not to be a fix, since the section written for it
  had none of its preconditions established; publication is now
  deferred to its own workstream (review 2, B2).
- S5 (scope, decomposition). The consistency reviewer recommended
  decomposing the work into four branches, on `CLAUDE.md` § one
  concern per branch. **Fix**: decision 10 records one plan on one
  branch, and section 8 states the criterion and defers discovered
  refactors to their own branch. The criterion the rule turns on is
  whether a change is *required* by the work or merely *discovered*
  during it, bounded by whether the required change is itself an
  independently reviewable concern: naming an instance so that
  `docstring` can address it is required and is not, so it is
  bundled; a toolchain bump or a CI repair would be required and
  would be, so it would take its own branch, sequenced first. A
  refactor noticed while writing is merely discovered. The user ruled
  that the work proceeds as one plan on one branch; that is the
  decision, and the criterion above is its ground. The reviewer's
  supporting argument, that the return did not justify the cost, is
  answered by section 12's statement of what the return is until
  publication is scheduled. *Recorded at round 4*, having been
  disposed at round 1 in a separate Rejected section that assigned no
  severity (review 4, A2). *Corrected at round 5*: the disposition
  label was outside the three permitted forms and named no resulting
  edit, and the criterion carried no magnitude bound (review 5, A5
  and A6).

## Minor

- m1 (section 5). `{lean}` is not an inline role at this tag; `lean`,
  `leanTerm` and `leanOutput` are code blocks. **Fix**: sections 2.2
  and 5 name each facility by its kind.
- m2 (section 3). There is no `GebLeanMeta/` directory. **Fix**.
- m3 (section 4.2). The design spec section 2.1 table has no
  Lean-module column; that correspondence is in the area document's
  Modules section. **Fix**: both cited.
- m4 (section 6). "Step function" was given as `g` as a whole; the
  paper's `g_ci` is one function per constructor. **Fix**: pluralised
  and distinguished.
- m5 (sections 1, 11). The labels "D1" and "D3" were cited but never
  assigned, and referred to a brainstorming artefact. **Fix**:
  removed.
- m6 (section 3). The output directory was unnamed. **Fix**: `_out`,
  added to `geb-lean/.gitignore`. *Corrected at round 3*: the round-2
  rewrite dropped both; they are restored (review 3, m3).
- m7 (section 3). The executable entry point's content was
  unspecified. **Fix**: section 3.1 gives it.
- m8 (sections 3, 4). Part and chapter registration and bibliography
  entry definition were unstated deliverables. **Fix**: section 4.4.
- m9 (section 4.2). Part II's module coverage boundary was
  under-specified. **Fix**: section 4.3 partitions the modules.
- m10 (section 4.1). Part I chapters 2 and 4 made mathematical claims
  without a searchable identifier, against `CLAUDE.md` § Cite the
  literature when transcribing. **Fix**: citations added.
- m11 (references). Dal Lago, Martini and Zorzi appeared unreferenced
  in the body. **Fix**: cited at the tree-algebra caveat.
  *Corrected at round 2*: the fix addressed one instance of a defect
  affecting four references (review 2, S6).
- m12 (section 11). No policy for the document's fate should
  `GebLean/Ramified/Polynomial/` become canonical. **Fix**: stated.
- m13 (section 3). The manual was not indexed from `docs/index.md`.
  **Fix**: added as a deliverable. The original justification cited a
  requirement `docs/process.md` does not state; the deliverable stands
  on its own terms.
- m14 (section 12). The docstring-coverage inventory was sequenced
  after Part I, leaving the source-side change set unsized. **Fix**:
  the open question is removed, missing docstrings being elaboration
  errors. *Corrected at round 3*: the set is in fact expected empty
  under section 4.3's rule, and the source-side change is the instance
  naming instead (review 3, S9).

## Cosmetic-taste

- c1 (throughout). Metaphor and jargon against `docs/process.md`
  § Avoid colloquialisms and metaphors: "tripwire", "fires",
  "substrate", "float", "hand", "friction", "weight", "restraining",
  "surface" as verb and noun, "spike". **Fix**. *Corrected at round
  2*: the original disposition claimed these were fixed throughout
  while several remained, and wrongly listed "bridge equivalence",
  which is established repository terminology
  (`docs/areas/ramified-recurrence.md`).
- c2 (sections 4.2, 8, 9). Conversational qualifiers: "a real table",
  "genuinely unresolvable", "a genuine refactoring opportunity".
  **Fix**.
- c3 (section 6). The table conflated the paper's symbols with its
  names in one column. **Fix**: split.
- c4 (section 3). `lakefile.toml` uses positional
  `[lean_lib.leanOptions]` subtables, so an insertion above the
  trailing one would rebind it. **Fix**: libraries are appended at the
  end. *Corrected at round 2*: this rationale does not extend to
  `[[require]]` blocks (review 2, B1).
- c5 (section 2.1). "Tags mirror Lean toolchain tags exactly"
  overstates; Verso `v4.17.0` is recorded against toolchain
  `v4.17.0-rc1`. **Fix**: "track".
- c6 (section 7). The presentation needs an enclosing
  `open GebLean.Ramified`. **Fix**.
- c7 (references). Dal Lago and others' title was down-cased against
  the published form. **Fix**.
- c8 (section 12). The bibliography-grouping question was an editorial
  decision left open in a document whose purpose is to fix decisions.
  **Fix**: decided in section 4.4.
- c9 (section 2.3, docstring behaviour). One reviewer held that a
  `docstring` on an undocumented declaration renders empty content
  rather than erroring, and inferred that missing docstrings are not
  machine-detected. **Reject as cosmetic-taste**: the other reviewer
  found the opposite and direct verification confirms it —
  `verso.docstring.allowMissing` has `defValue := false` and the false
  branch calls `Lean.logError`. The finding rests on a false premise,
  so there is nothing to fix; the dependent finding m14 resolves in
  the opposite direction from the one proposed. *Recorded at round 4*,
  having been disposed at round 1 in a separate Rejected section that
  assigned no severity (review 4, A2).

## Verified without defect

- Verso tag `v4.29.0-rc6` exists and its toolchain matches this
  repository's. Its requires are exactly `subverso`, `MD4Lean` and
  `plausible`, transitively closed; `precompileModules := false`.
- All named `VersoManual` modules exist at the tag, and the roles
  `deftech`, `tech`, `margin` and `name` carry the argument shapes the
  spec implies.
- `manualMain` counts logged errors and returns exit code 1 when
  non-zero, so a generator run gates generation-time findings.
- The proposed Lake TOML is valid at this toolchain.
- Every Lean declaration cited exists under
  `namespace GebLean.Ramified`, including
  `instance : collapseFunctor.Faithful` and the seven interpretation
  lemmas of Part I chapter 5.
- The lakefile claims and the `GebLeanAxiomChecks` gate set, the
  latter verified from `GebLeanAxiomChecks/` sources.
- Every reference agrees with the area document and the design spec on
  author list, venue, year, page range and DOI. *Corrected at round
  2*: the original also claimed agreement on title, which c7 had
  itself changed.
- Every row of section 6's terminology table agrees with the design
  spec's glossary, as do the paper-location claims.
- The spec is markdownlint-clean, carries doctoc markers, and contains
  no emojis, all-caps non-acronyms, or non-generic user references.

## Convergence

Not converged. Round 1 raised five blockers and five serious findings.
All were addressed in the spec; eleven entries carry a later
correction, distributed as the preamble records. Rounds 2 to 6 record
the outcomes.
