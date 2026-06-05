# Idris-2 and Lean overview-documentation sweep

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Overview](#overview)
- [Goal](#goal)
- [Non-goals](#non-goals)
- [Current state](#current-state)
- [Target layout](#target-layout)
- [Area decomposition](#area-decomposition)
  - [Lean areas](#lean-areas)
  - [Idris areas](#idris-areas)
- [Per-area document template](#per-area-document-template)
- [Parallel formulations](#parallel-formulations)
- [Novelty and prior-formalization status](#novelty-and-prior-formalization-status)
- [Existing-material policy (Lean)](#existing-material-policy-lean)
- [Coverage discipline](#coverage-discipline)
- [Accuracy discipline](#accuracy-discipline)
- [Markdownlint and doctoc](#markdownlint-and-doctoc)
- [Process](#process)
- [Risks](#risks)
- [Follow-ups (out of scope)](#follow-ups-out-of-scope)
- [References](#references)

<!-- END doctoc -->

## Overview

The `geb/` monorepo holds implementations of Geb in four languages.
The `2026-05-28-readme-docs-revamp` step established the navigation
skeleton: the root `README.md` is now a hand-authored index, the
obsolete Common Lisp manual lives under `docs/common-lisp/`, and each
subproject is reachable through its own `docs/index.md`. That step was
explicitly "structure and navigation only", deferring the authoring of
new explanatory content to a later phase.

This is that later phase. The two actively-relevant codebases carry
very little overview documentation relative to their size:

- **Idris-2** (`geb-idris/src/`): 77 non-test modules, about
  118 000 lines. The only narrative documentation is the README's
  account of Geb as a circuit frontend (one specific use), plus four
  research notes under `geb-idris/docs/`. There are no module-level
  doc headers anywhere in the source.
- **Lean** (`geb-lean/GebLean/`): 214 files under `GebLean/` plus the
  root aggregator `geb-lean/GebLean.lean`, about 292 000 lines.
  `geb-lean/docs/index.md` is a strong hand-curated topological
  narrative grouping modules into about ten workstreams, but 69 source
  files are not named in it and 51 loose `docs/*.md` files (mostly
  research notes) are unreferenced and partly stale.

The sweep produces overview-level documentation for both codebases:
enough that a reader starting at the root `README.md` can understand
what is implemented and how it fits together, with links down to
source, without descending to function-by-function detail.

## Goal

After this step:

- `geb-idris/docs/index.md` is a spine linking to a set of area
  documents under `geb-idris/docs/areas/`, one per coherent area of
  the Idris codebase. Every module in the Idris source set (see
  [Coverage discipline](#coverage-discipline)) is named in exactly one
  area document, with a one-line role and a link to its source.
- `geb-lean/docs/index.md` is slimmed to a spine: each workstream is a
  short paragraph plus a link to an area document under
  `geb-lean/docs/areas/`. Every file in the Lean source set (see
  [Coverage discipline](#coverage-discipline)) is named in exactly one
  area document.
- Each area document gives, at overview depth: the area's purpose in
  Geb, its mathematical context, a per-module bullet naming the main
  definitions and theorems (the reasons the module exists, not the
  intermediate results), and the area's dependencies on other areas.
- Cases where the codebase formulates the same mathematical concept in
  more than one way are identified and cross-referenced as alternative
  approaches (see [Parallel formulations](#parallel-formulations)).
- Each headline definition/result carries a best-effort
  **provenance** tag — novel mathematics, first formalization
  anywhere, first in Lean, or one of several Lean formalizations —
  determined by on-the-fly online research (see
  [Novelty and prior-formalization status](#novelty-and-prior-formalization-status)).
  Online literature/formalization search is therefore in scope for
  this sweep, even though no code or proof is written.
- The Lean loose research notes are relocated under
  `geb-lean/docs/research/`, cited from the area documents that use
  them; any note proposed for deletion is listed for sign-off, never
  deleted silently.
- The root `README.md` continues to reach everything; its subproject
  links are adjusted only as needed to point at the refreshed indexes.

## Non-goals

- **No source-code changes.** This step touches only Markdown under
  `docs/` trees. No `.lean` or `.idr` file is edited.
- **No function-by-function documentation.** Area documents describe
  modules at overview depth. Deep per-module documentation is a future,
  module-by-module effort.
- **No new per-module files.** Per-module detail lives as bullets or
  short subsections inside area documents, not as one file per module.
- **Agda and Common Lisp are untouched.** They are obsolete and already
  filed under their own indexes.
- **No proof or build work.** The sweep does not run `lake build`
  except where needed to confirm a claimed declaration still exists
  (see [Accuracy discipline](#accuracy-discipline)).

## Current state

- Root `README.md`: hand-authored index (from the predecessor step)
  linking to `geb-lean/`, `geb-idris/`, `geb-agda/`, and
  `docs/common-lisp/`.
- `geb-idris/docs/`: `index.md` (skeleton), `geb-syllabus.md`,
  `mldirichf-generalization.md`, `profunctor-end-characterization.md`,
  `twisted-arrow-copresheaf-analysis.md`. No `areas/` directory.
- `geb-idris/README.md`: the circuit-frontend narrative.
- `geb-lean/docs/`: `index.md` (about 21 KB, the workstream
  narrative), 51 loose `*.md` notes, plus `research/`, `plans/`,
  `superpowers/` subdirectories and several PDFs. No `areas/`
  directory.

## Target layout

For each of the two codebases:

```text
<lang>/docs/
  index.md          spine: short identity + one paragraph and link
                    per area; a coverage note
  areas/
    <area>.md       one per area; per-module bullet or subsection
  research/         (Lean only) relocated loose notes
```

The root `README.md` is adjusted only if a link target moves.

## Area decomposition

Each source file is assigned to exactly one area. The authoritative
file-to-area assignment is a coverage matrix maintained in the
implementation plan and verified mechanically (see
[Coverage discipline](#coverage-discipline)).

The area lists below are a **starting seed, not a claimed-total
enumeration.** The plan begins from the full mechanically-enumerated
source set (not from these area names), assigns every file, and may
add, split, or merge areas so the result is a total, disjoint
partition. Where a module could sit in two areas, the tie-break rule
is: assign it to the area of its dominant import / namespace; the plan
pre-resolves the known overlaps (noted per language below).

### Lean areas

The existing `index.md` workstreams are reused as the area list, since
they are already a sound partition; the 69 currently-unlisted files are
mostly unenumerated members of these workstreams (for example the
`LawvereGodelT*` and `LawvereNatBT*` clusters belong to the Lawvere
ER / K_sim area). Proposed areas:

1. Quivers, semicategories, acyclic categories.
2. Category-judgment encodings and the `L ⊣ Φ` adjunction.
3. Polynomial, W- and M-types, and PFunctors.
4. Profunctors and end machinery.
5. Internal-presheaf Grothendieck equivalence.
6. PshRelEdge and edge-of-presheaf machinery.
7. Tree calculus (Phase 2).
8. Lawvere ER, Gödel-T, the K_sim hierarchy, and the ER to K_sim_2
   equivalence.
9. NNO, arithmetic, and topos-theoretic primitives (`NatArith`,
   `NatNNO`, `PSO`, `PLO`, `PSTONat`, `ParanaturalTopos`,
   `PresheafPRA*`, and related).
10. Utilities (`GebLean/Utilities/`, 51 files).

CSLib integration is **not** a source-file area: the existing
`index.md` "CSLib integration" section names only configuration files
(`lakefile.toml`, `lake-manifest.json`, `CLAUDE.md`, …), no `.lean`
sources. CSLib is *used* by modules already in areas 8 and 10. It is
therefore documented as a cross-cutting dependency note attached to
the area it most informs, not as a member of the partition.

Subdirectories: `GebLean/PLang/` (14 files) is distributed across
existing areas (the `CatJudgment*` files into area 2, the tree-calculus
files into area 7); `GebLean/Utilities/` is area 10. The
per-directory aggregator modules (`GebLean.lean`, `GebLean/PLang.lean`,
`GebLean/Utilities.lean`, `GebLean/LawvereERKSim.lean`) are pure
`import` re-exports; they are assigned to the area they aggregate and
documented as one-line aggregators (see the template's aggregator
clause).

The plan confirms the final boundaries and assigns every file in the
Lean source set; areas 9 and the boundary between 3 and 8 are the ones
most likely to need adjustment.

### Idris areas

The Idris source has no module-level doc headers, so the decomposition
is derived from the module import graph and naming, then confirmed in
the plan. Proposed areas:

1. **Library** — Idris-level utilities and category-theory
   infrastructure (`IdrisUtils`, `IdrisCategories`, `IdrisAlgebra`,
   `CategoryTheory`).
2. **Polynomial functors** — `PolyCat`, `FinPoly`, the `*Poly*`
   modules, slice and polynomial categories.
3. **Internal categories and profunctors** — `InternalCat`, the
   `Int*Cat` family, `*Profunctor`, `*Difunc`, twisted-arrow and
   dialgebra machinery.
4. **The Geb language** — `Geb`, `GebTopos`, `Theories`, `ProgFinSet`,
   `Expression`, `Interpretation`, `ADTCat`.
5. **Recursion and compilation targets** — `TreeCalculus`, `Nock`,
   `BinTree`, recursive front-ends.
6. **Metaprogramming and syntax** — `Metaprogramming`, `Syntax`,
   `Figures`, `Telescope`.
7. **Circuit frontend** — `geb-idris/README.md` is **left in place**
   (its content is not moved or duplicated); this area document is a
   short prose summary that links to the README and situates the
   circuit-frontend use as one application among the areas above,
   rather than the subproject's defining front page. The area owns no
   `.idr` source file (it is a prose-only area; see the coverage
   note). Because `geb-idris/README.md` does not move, no root
   `README.md` link or description changes on its account.
8. **Foundational and finite-category machinery** — `Quiver`,
   `FinCat`, `FinCatPRA`, `Adjunctions`, `UniversalCategory`,
   `DiagramCat`, `SpanCospan`, `HelixCat`, `RopeCat`,
   `NatPrefixCat`, and similar constructions that import only the
   library layer and belong to none of areas 2–6.
9. **Logic, refinement types, and atoms** — `Logic`, `QType`,
   `RQFin`, `RefinedADT`, `Atom`, `ComputationalEffects`, `Embedded`,
   `FullLanguageDef`.

The plan builds the import graph, confirms this partition, and assigns
each of the 77 non-test modules. When a module is named explicitly in
an area seed, that explicit placement overrides the dominant-import
tie-break (so `Figures` and `Telescope`, although they import poly
machinery dominantly, stay in area 6 where they are named). Known
multi-home overlaps to pre-resolve in the matrix (by dominant import /
namespace) lie on the Poly-vs-Internal boundary between areas 2 and 3:
`PolyProfunctor`, `PolyProfEnd`, `PolyDifunc`, `SlicePolyDifunc`,
`DiPolyFunc`, `MLDiPolyFunc`, `SlPolyIntCat`, the `MLQuiv*` family, and
the `MLBundleCat` / `MLDirichCat` / `MLTwistPair` trio (all to area 3
by dominant `InternalCat` import). Test modules live under four
roots — `src/LanguageDef/Test/`, `src/Library/Test/`,
`src/Executable/Test/Main.idr`, and `src/Test/TestLibrary.idr` — all
excluded by the coverage glob (see
[Coverage discipline](#coverage-discipline)).

## Per-area document template

Each `areas/<area>.md` has these sections, scaled to the area's size:

- **Purpose** — one or two sentences: what the area is and why it
  exists in Geb.
- **Mathematical context** — the known mathematics the area
  formalises or implements, with external references where helpful.
- **Modules** — one bullet (or short subsection for larger modules)
  per source file, naming the main definitions and theorems and the
  module's one-line role, with a relative link to the source file.
- **Alternative formulations** — present only when the area, or the
  codebase across areas, formulates the same concept more than once
  (see [Parallel formulations](#parallel-formulations)).
- **Provenance** — for each headline definition/result named in
  **Modules**, a one-line novelty-and-prior-formalization tag stamped
  with its search date and scope (see
  [Novelty and prior-formalization status](#novelty-and-prior-formalization-status)).
  Empty for prose-only areas with no headline declarations (e.g. Idris
  area 7), mirroring the coverage carve-out.
- **Dependencies** — which other areas this one builds on.
- **Pointers** — (Lean) relocated research notes and
  `docs/superpowers/specs/` entries relevant to the area; (Idris)
  development status where it aids the reader.

**Depth budget** (so two authors converge): each module gets one to
three sentences; name at most the one to three headline declarations
that are the reason the module exists; do not list intermediate
lemmas, instances, or helper definitions. A "reason the module
exists" is a declaration another module imports or that states the
area's headline result; an "intermediate result" is one used only
within its own module to build a headline declaration. The plan
includes one fully-written area document as a calibration reference
before the rest are authored.

**Aggregator clause**: pure re-export / index modules (those whose
body is only `import` lines plus at most a namespace declaration —
e.g. `GebLean.lean`, `GebLean/Utilities.lean`) are documented in one
line as aggregators of their area, with no definitions-and-theorems
list. They still count for coverage.

## Parallel formulations

Because the repository is exploratory, the same mathematical concept is
sometimes formulated in more than one way, or pursued down several
routes. A known example: more than one Lean formulation of the
adjunction between `Cat` and the (co)presheaf category on a finite
category of the kind defined in `CategoryJudgments.lean`.

These are documented explicitly rather than presented as if each were
the only treatment:

- During each area's authoring, candidate parallel formulations are
  noted (multiple modules whose central definitions or theorems target
  the same mathematical object or universal property).
- Each confirmed cluster is described in one place — an **Alternative
  formulations** subsection in the most natural area document — naming
  each formulation, its module, and the respect in which the approaches
  differ (for example, pointwise versus categorical, or via judgments
  versus via copresheaves). Other affected area documents link to that
  single description rather than restating it.
- The plan carries a running list of suspected parallel-formulation
  clusters discovered while reading the source, so none is lost between
  areas.

**Operational definition.** A parallel-formulation cluster is a set
of two or more modules whose headline `def`/`theorem` (or Idris
top-level definition) carry the *same informal statement* — they
construct or characterise the same mathematical object, universal
property, or equivalence. The seed clusters the plan starts from,
discovered while surveying the source, include: the versioned Lawvere
families (`LawvereNatBT.lean` / `LawvereNatBTV2.lean` / the `*V2`,
`*V20` variants); `LawvereKSimER.lean` versus
`LawvereKSimERDirect.lean`; and the several Lean formulations of the
`Cat` ↔ (co)presheaf adjunction over the finite category of
`CategoryJudgments.lean`. The plan extends this seed list as the
survey proceeds.

**Status.** This detection is best-effort and explicitly **not** an
acceptance gate: the coverage check does not test
parallel-formulation completeness, and missing a cluster is not a
build failure. It records correspondences evident from the central
declarations, not an exhaustive proof that two formulations are
equivalent (proving such equivalences is a named follow-up).

## Novelty and prior-formalization status

For each headline definition/result named in an area document's
**Modules** section, the author records a one-line **Provenance** tag
placing it on two axes — is the *mathematics* known, and does a prior
*machine-checked formalization* exist — using on-the-fly online
research. The four categories (specialised to the Lean codebase; see
the Idris adaptation below) are decided as a decision tree on two
axes — first the *mathematics* axis, then, only for known mathematics,
the *prior-formalization* axis:

1. **Novel mathematics** — no prior appearance in the mathematical
   literature that we can find. The tag cites the known mathematics
   the result builds *directly* upon (its nearest established
   antecedents), so the novelty is legible. The novelty axis takes
   precedence: a result we judge novel stays category 1 even if an
   external formalization (e.g. concurrent independent work) turns up,
   with that formalization noted in the tag. Categories 2–4 apply only
   to *known* mathematics.
2. **Known maths, first formalization** — the result is established in
   the literature, but we find no prior machine-checked formalization
   in *any* proof assistant. The tag cites the mathematical source.
3. **Known maths, first Lean formalization** — known and formalized in
   some proof assistant(s), but we find no prior Lean (mathlib or
   other Lean project) formalization. The tag cites the non-Lean
   formalization(s) found.
4. **Known maths, existing Lean formalization** — a Lean formalization
   already exists in *another* project (this is about external Lean
   work, never our own Idris-then-Lean re-formulation, which is a
   [parallel formulation](#parallel-formulations)). The tag cites it
   and, where determinable (e.g. by commit/publication date against
   this repository's history), notes whether we plausibly missed it or
   it post-dates our work.

**Research method.** The author searches, in rough order: Lean and
mathlib (Mathlib docs, `leansearch`/`Moogle`/`loogle`, the mathlib4
repository, the Lean Zulip and reservoir/community index); other proof
assistants' libraries (Coq stdlib / mathcomp, Agda stdlib / 1lab,
Isabelle AFP, Rocq); and, for the novelty axis, the mathematical
literature (nLab, arXiv, standard references). The search scope
actually used is noted briefly so a later reader can re-check.

**The search is time-boxed.** Producing a *defensible negative*
("nobody has formalized this") is open-ended, and per-result search —
not the prose — is the largest potential time cost of the sweep, so it
is bounded explicitly: each headline result gets a small fixed search
budget (the ordered targets above, stopping at the first decisive hit,
and otherwise a bounded handful of queries per axis). On exhausting the
budget without a confident classification, the tag is **"provenance
unverified"** and the author moves on. The budget keeps total search
effort proportional to the `1`–`3`-headline-declarations-per-module
depth budget rather than unbounded; the plan fixes the concrete query
count.

**Relation to parallel formulations.** This is the *external*
counterpart of the [Parallel formulations](#parallel-formulations)
element: parallel formulations record multiple treatments *within our
own repositories*; the provenance tag records the relationship to
mathematics and formalizations *outside* this project. Category 4 is
specifically about Lean formalizations in *other* projects, not our
own internal re-formulations.

**Idris adaptation.** The Idris codebase predates and is largely
superseded by the Lean work, so its provenance tags use categories 1
and 2 (novel vs. known, with the first-formalization question asked
against *any* system including this Idris code), and, where the same
concept was later redone in our Lean, a cross-link to that area rather
than a categories-3/4 Lean-prior-art search. Re-running the full
external search for superseded Idris modules is out of scope.

**Status.** Like parallel-formulation detection, this is **best-effort
and not an acceptance gate.** Categories 1–3 assert a *negative* ("no
prior X found"), which cannot be proven exhaustively; every such tag
is implicitly "as far as we could find on \[date\], searching
\[scope\]" and may be revised. A missing or hedged provenance tag is
not a build failure, and the coverage check does not test provenance.
When the author cannot classify confidently at overview depth, the tag
says "provenance unverified" rather than guessing. Strong claims
(category 1 "novel", category 2 "first anywhere") are stated
conservatively and flagged in the plan for the user's eyes, since they
are the ones most costly to get wrong.

## Existing-material policy (Lean)

- `index.md` is kept as the spine. Slimming **preserves** the index's
  opening framing paragraph (the "directory layout plus topological
  narrative" prose) and the `## Directory structure` section, since
  the cross-area build order is an index-level property that per-area
  **Dependencies** sections do not reconstruct. Only the
  per-workstream detail is compressed: each workstream's prose becomes
  a short paragraph plus a link to its area document, and the
  per-module detail moves into the area document.
- The 51 loose `docs/*.md` notes (top-level, excluding `index.md`) are
  relocated to `geb-lean/docs/research/`. Notes that an area document
  draws on are cited from that document. The existing `research/`
  already holds dated process artifacts (prior adversarial reviews);
  the relocated narrative notes are distinguishable by their
  non-dated names, so the mix is acceptable and no third directory is
  introduced.
- Notes that appear dead (superseded duplicates, or write-ups of an
  explicitly abandoned approach) are **listed in the plan for
  sign-off**. None is deleted without approval; the default is to
  relocate and keep.
- The existing `docs/research/`, `docs/plans/`, `docs/superpowers/`,
  `docs/.claude/` subdirectories and the PDFs are left in place.

## Coverage discipline

Completeness is enforced mechanically, not by inspection.

**Source set.** Defined precisely per language:

- Lean: `geb-lean/GebLean/**/*.lean` plus the root
  `geb-lean/GebLean.lean`, minus the test tree (`GebLeanTests/` and
  `geb-lean/GebLeanTests.lean`). This is the 214 files under
  `GebLean/` plus the one root aggregator. The `.lake/` dependency
  tree is never enumerated.
- Idris: `geb-idris/src/**/*.idr`, minus every path containing a
  `Test/` segment (which excludes all four test roots:
  `LanguageDef/Test/`, `Library/Test/`, `Executable/Test/`, and the
  top-level `Test/`). This is the 77 non-test modules.

**Citation syntax.** Every area document cites a source file as a
relative Markdown link whose visible text is the path, e.g.
``[`GebLean/Polynomial.lean`](../../GebLean/Polynomial.lean)``. This
is the single syntax the check extracts; the existing `index.md`
backtick-only convention is *not* used in area docs. (The slimmed
`index.md` links only to area documents, not to source files, so it is
excluded from the scan and cannot double-count.)

**Check script.** A shell script (recorded verbatim in the plan)
enumerates the source set as defined above and extracts every
source-file link target from `areas/*.md` only, normalising the
relative paths. It then makes **two** assertions, because
set-equality alone checks totality but is blind to multiplicity:

1. *Totality and no stragglers*: the set of distinct linked targets
   equals the enumerated source set (every source file is linked from
   some area doc, and nothing outside the source set is linked).
2. *Disjointness*: no source file is linked from more than one
   `areas/*.md` file. This is computed by deduplicating link
   occurrences *within* each area document first, then counting the
   number of distinct area documents each target appears in, and
   failing on any count greater than one. The within-file dedup is
   load-bearing: a file may legitimately be linked twice inside one
   area doc (e.g. in **Modules** and again in **Alternative
   formulations**); that is allowed, while the same file linked from
   two different area docs is not.

The final SDD task runs both assertions per language. A prose-only
area (Idris area 7, the circuit frontend, owns no `.idr` file)
contributes no link and is expected to: the check does **not** require
every area document to contribute a source link.

## Accuracy discipline

- The current source is authoritative; existing prose (the Lean
  `index.md`, research notes, prior specs) is treated as a hint, not a
  source of truth.
- For each module, the author reads its top-level declarations to name
  the main definitions and theorems. When a named declaration is
  carried over from existing prose, its continued existence is
  confirmed against the source before it is asserted.
- Where a module's purpose cannot be determined confidently from the
  source at overview depth, the area document says so briefly rather
  than guessing.

## Markdownlint and doctoc

All new and edited Markdown is markdownlint-clean under the project
configuration, matching the predecessor step:

- ATX headers, prose wrapped to the project width, fenced code blocks
  with language tags, no bare URLs.
- Each `index.md` carries a doctoc-generated table of contents with the
  standard sentinel comments; area documents follow the same heading
  conventions.

CI scope: the markdown-lint workflow
(`.github/workflows/markdown-lint.yml`) lints only `geb-lean/**/*.md`,
and the only config is `geb-lean/.markdownlint-cli2.jsonc`. The Lean
docs this sweep authors are therefore CI-gated; the **Idris** docs and
any root-`README.md` edits are not. The Idris docs are linted locally
against `geb-lean/.markdownlint-cli2.jsonc` (named explicitly), and the
sweep accepts that they are not CI-enforced. Extending CI lint coverage
to the Idris tree and the root is a named follow-up, consistent with
the predecessor spec.

## Process

Per the project norm for this work: spec with at least three
adversarial-review rounds, then an implementation plan with adversarial
review, then SDD task-by-task execution, then a holistic review.

The Idris and Lean tracks share this one spec and one plan so that the
document template, index conventions, and coverage check stay identical
across both. The execution decomposes naturally into:

1. Build the Idris import graph; confirm the Idris partition and the
   coverage matrix.
2. Confirm the Lean partition and coverage matrix.
3. Write one calibration area document (the agreed depth-budget
   reference). Calibrate on an area expected to contain the
   highest-stakes provenance categories — the category-judgment /
   `L ⊣ Φ` area, which `geb-lean/docs/novelty-analysis.md` already
   analyses — so a worked category-1 or category-2 **Provenance** tag
   exists as an exemplar. Get it approved before authoring the rest.
4. Author the Idris index and area documents.
5. Relocate the Lean research notes; record dead-note candidates and
   obtain sign-off before any deletion.
6. Slim the Lean index (preserving the framing paragraph and the
   Directory-structure section); author the Lean area documents.
7. Maintain the parallel-formulation seed list as the survey proceeds;
   write each confirmed cluster's description in its home area doc.
   Run the per-result provenance research while authoring each area
   (Lean areas only for categories 3–4); collect category-1/2 claims
   into a list in the plan for the user's review.
8. Adjust the root `README.md` links only if a target moved (under the
   current layout decisions no target moves, so this is expected to be
   a no-op).
9. Run the two-assertion coverage check per language, markdownlint, and
   doctoc; holistic review.

## Risks

- **Accuracy drift.** Documents may assert "main theorems" that have
  moved or been renamed. Mitigated by treating source as authoritative,
  reading top-level declarations per module, and confirming carried-over
  names against the source.
- **Scale.** About ten Lean areas and nine Idris areas (seed counts
  the plan may adjust), each surveying several modules, is a large but
  bounded body of prose. The SDD tasks are one area each, keeping
  individual diffs reviewable.
- **Partition disputes.** A few modules sit between areas. Mitigated by
  the coverage matrix forcing an explicit, single assignment and by the
  plan flagging the contested boundaries for review.
- **Parallel-formulation misidentification.** Two formulations may be
  claimed equivalent when they differ. Mitigated by keeping the claim
  overview-level (evident correspondence of central definitions, not an
  equivalence proof) and stating the respect in which they differ.
- **Over-claimed novelty / false-negative search.** A "novel" or
  "first formalization" provenance tag asserts a negative that online
  search cannot prove exhaustively, and the literature/formalization
  landscape shifts. Mitigated by stamping each tag with its date and
  search scope, phrasing categories 1–3 as "none found", routing the
  strong category-1/2 claims to the user for review, and treating
  provenance as best-effort and non-gated. The existing
  `geb-lean/docs/novelty-analysis.md` is a starting input, not a
  substitute for per-result search.

## Follow-ups (out of scope)

- Deep, function-level documentation for individual modules, authored
  one module at a time.
- Migrating curated material into the `geb-mathlib` repository.
- Any documentation for the Agda or Common Lisp implementations.
- Proving the equivalence of identified parallel formulations where it
  is not already established in the source.
- Periodically refreshing provenance tags (the
  literature/formalization landscape shifts, so category-1/2/3 claims
  decay) and deepening the category-1 "novel" claims into a citable
  novelty write-up.

## References

- Predecessor spec:
  `docs/superpowers/specs/2026-05-28-readme-docs-revamp-design.md`.
- Lean documentation index: `geb-lean/docs/index.md`.
- Existing novelty analysis (provenance input):
  `geb-lean/docs/novelty-analysis.md`.
- Idris documentation index: `geb-idris/docs/index.md`.
- Idris circuit-frontend narrative: `geb-idris/README.md`.
- Reading-group background: `geb-idris/docs/geb-syllabus.md`.
