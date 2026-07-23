# A Verso manual for ramified recurrence

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [1. Decisions fixed during brainstorming](#1-decisions-fixed-during-brainstorming)
- [2. Verso](#2-verso)
  - [2.1 Version and dependency resolution](#21-version-and-dependency-resolution)
  - [2.2 Facilities used](#22-facilities-used)
  - [2.3 What each mechanism checks, and when](#23-what-each-mechanism-checks-and-when)
- [3. Build wiring](#3-build-wiring)
  - [3.1 Package and targets](#31-package-and-targets)
  - [3.2 Inherited options and the three diagnostic classes](#32-inherited-options-and-the-three-diagnostic-classes)
  - [3.3 Linter and gate coverage](#33-linter-and-gate-coverage)
- [4. Document structure](#4-document-structure)
  - [4.1 Part I, tutorial](#41-part-i-tutorial)
  - [4.2 Part II, reference](#42-part-ii-reference)
  - [4.3 What Part II covers](#43-what-part-ii-covers)
  - [4.4 Manual assembly](#44-manual-assembly)
- [5. Code sampling](#5-code-sampling)
- [6. Terminology discipline](#6-terminology-discipline)
- [7. Signature presentations](#7-signature-presentations)
- [8. Source-side changes](#8-source-side-changes)
- [9. Failure modes and fallbacks](#9-failure-modes-and-fallbacks)
- [10. Verification and gates](#10-verification-and-gates)
- [11. Deliverables](#11-deliverables)
- [12. Deferred and out of scope](#12-deferred-and-out-of-scope)
- [13. Open questions](#13-open-questions)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Purpose

A single Verso document serving as both tutorial and reference for
ramified recurrence, synthesising Leivant III, the area document
[`docs/areas/ramified-recurrence.md`](../../areas/ramified-recurrence.md),
and the design spec
[`2026-07-01-ramified-recurrence-approaches-design.md`](2026-07-01-ramified-recurrence-approaches-design.md),
with its Lean content sampled from `GebLean/Ramified/` rather than
transcribed.

The document introduces the types and definitions the paper
prescribes, states the complexity results the paper cites, and
records how this repository presents the system as a multi-sorted
Lawvere theory. It contains no proofs: the two proof routes are
described by shape, and every result is stated with a citation.

This is the repository's first use of Verso.

## 1. Decisions fixed during brainstorming

1. Scope is the paper's content plus this repository's Lawvere-theory
   packaging. Proofs are excluded throughout.
2. Genre is `VersoManual`, the genre of the Lean 4 reference manual.
3. The document target is outside `defaultTargets`, the `lake test`
   driver, the `GebLeanAxiomChecks` gates, and the default reach of
   `lake lint`. It is exercised in CI and not in the local pre-commit
   or pre-push scripts (section 10).
4. The assumed reader is comfortable with Lean 4, inductive types, and
   basic category theory, and has no prior exposure to ramification.
5. Lean content is sampled from `GebLean/Ramified/`. The
   polynomial-functor reimplementation under
   `GebLean/Ramified/Polynomial/` is mentioned and linked, not
   covered: its content is the correspondence, not the mathematics.
   Section 12 records the policy should that layer become canonical.
6. Terminology is carried by Verso's `deftech` and `tech` roles rather
   than by a hand-maintained table, and each term is introduced where
   the reader first needs it.
7. Signatures whose argument structure the prose discusses are
   presented with Verso's `signature` code block, within the limits
   section 7 records.
8. Dependency resolution is settled before any prose is written
   (section 9).
9. Part II covers a stated subset of the declarations in its modules,
   not all of them (section 4.3).
10. The work proceeds as one plan on one branch. Publication is not
    part of it (section 12).
11. Adding a name to an anonymous `instance` in `GebLean/Ramified/` is
    permitted where the reference half renders it (section 8).

## 2. Verso

### 2.1 Version and dependency resolution

`leanprover/verso` tags track Lean toolchain tags. The tag
`v4.29.0-rc6` matches this repository's `lean-toolchain`, and its own
`lean-toolchain` reads `leanprover/lean4:v4.29.0-rc6`. Verso is
indexed on Reservoir as `leanprover/verso`, so the dependency is
declared by `scope` and `rev`, the form the existing `mathlib` and
`cslib` requires use.

Verso requires `subverso`, `MD4Lean`, and `plausible` from `main`
branches, but it ships a `lake-manifest.json` at the tag pinning all
three, and Lake resolves an inherited dependency from the
dependency's own manifest (`Lake/Load/Resolve.lean`,
`addDependencyEntries`, which stores an entry only `unless` the name
is already present). For `subverso` and `MD4Lean`, which Verso alone
supplies, the resolved revisions are therefore determined by Verso's
tag.

`plausible` is the one package shared with mathlib's closure, and the
two disagree: Verso's manifest pins `650d4104`, while this
repository's carries `e84e3e16`, supplied by mathlib and `cslib`
alike. Lake resolves root requires in reverse declaration order
(`Lake/Load/Resolve.lean`, `let deps := ws.root.depConfigs.reverse`),
so a require declared earlier is traversed later. Declaring `verso`
**before** `mathlib` therefore reads mathlib's manifest first,
storing `e84e3e16`, and discards Verso's pin when Verso's manifest is
read afterwards. Section 9 records the acceptance criterion that
verifies this held.

### 2.2 Facilities used

| Facility | Kind | Module | Use here |
| --- | --- | --- | --- |
| `docstring` | block command | `VersoManual/Docstring.lean` | Renders an elaborated declaration and its doc comment. The reference half's primary content. |
| `signature` | code block | `VersoManual/InlineLean/Signature.lean` | Checks a written signature against the real declaration, within the limits of section 7. |
| `deftech` / `tech` | roles | `VersoManual/Glossary.lean` | Define and reference technical terms, hyperlinked, with a generated terminology index. |
| `margin` | role | `VersoManual/Marginalia.lean` | Annotates the signature presentation of Part I chapter 1. |
| `name` | role | `VersoManual/InlineLean.lean` | Resolves and hyperlinks a declaration named in prose. |
| `lean` / `leanTerm` | code blocks | `VersoManual/InlineLean.lean` | Elaborated illustrations in the tutorial half. |
| `table` | directive | `VersoManual/Table.lean` | The paper-to-code correspondence and the transcription map. |
| `citep` / `citet` | roles | `VersoManual/Bibliography.lean` | Citations throughout both parts. |
| `manualMain` | entry point | `VersoManual.lean` | The generator. |

### 2.3 What each mechanism checks, and when

| Change to the source | Detected by | When |
| --- | --- | --- |
| Covered declaration renamed or removed | `docstring`, `name`, `signature` | Elaboration |
| Covered declaration's docstring missing | `docstring` | Elaboration |
| Presented declaration retyped | `signature` | Elaboration |
| Presented declaration's level-parameter count changed | `signature` | Elaboration |
| Presented declaration's outer binder renamed | nothing | never |
| Technical term undefined | `tech` | Generation |
| Technical term defined twice and referenced | `tech` | Generation |
| Declaration added to a covered module | nothing | never |

The citations below are to Verso, SubVerso, and Lean source at the
pinned revisions.

A `docstring` block resolves its argument and then renders whatever
signature the environment holds. A rename or removal fails
elaboration; a retype does not, and is re-rendered without complaint.
Retypes are detected only where section 7's `signature` blocks are
used.

A missing docstring is an elaboration error, not a warning:
`verso.docstring.allowMissing` has `defValue := false`, and the false
branch calls `Lean.logError` (`VersoManual/Docstring/Config.lean`,
`VersoManual/Docstring/Basic.lean`). Docstring coverage of the
declarations Part II renders is therefore enforced by the build.

Terminology is checked at generation: an undefined key, and a
duplicated key that some `tech` reference resolves against, reach
`HtmlT.logError` (`VersoManual/Glossary.lean`). A `deftech` duplicated
but never referenced is not reported. `manualMain` counts logged
errors and returns exit code 1 when the count is non-zero, so a
generator run reports them.

The table lists what the sampling mechanisms detect. It is not a list
of everything that fails the build: section 3.2's three diagnostic
classes bear on the library independently of the sampling mechanisms.

Two rows read "nothing / never".

A renamed outer binder is computed and discarded. SubVerso's `compare`
reports parameter-name, binder-info, and `optParam`-default mismatches
with `logErrorAt` (`SubVerso/Examples.lean`), which accumulates into
the nested `Command.State` that Verso's `signature` block constructs;
the block then retains `setInfoState st'.infoState` and drops that
state's messages. The mechanical content of a `signature` block is
therefore the definitional-equality check on the type and the
level-parameter count. Section 7 states the naming convention that the
author observes in consequence.

A declaration added to a covered module is not detected, so Part II's
coverage decays as the source grows. Section 4.3's selection rule is
stated so that a reader can determine what is missing by inspection;
nothing mechanical does so.

## 3. Build wiring

### 3.1 Package and targets

`geb-lean/lakefile.toml` gains one dependency and two targets, in two
places.

The `[[require]]` block is inserted **before** the existing `mathlib`
require, for the resolution-order reason in section 2.1:

```toml
[[require]]
name = "verso"
scope = "leanprover"
rev = "v4.29.0-rc6"
```

The library and executable are appended at the end of the file.
`lakefile.toml` uses positional `[lean_lib.leanOptions]` subtables
that bind to the preceding `[[lean_lib]]`, so a library inserted above
the trailing subtable would rebind it away from `GebLeanAxiomChecks`.
This concerns library tables only, not the require above.

```toml
[[lean_lib]]
name = "GebLeanDocs"

[lean_lib.leanOptions]
weak.verso.code.warnLineLength = 100

[[lean_exe]]
name = "geblean-docs"
root = "GebLeanDocsMain"
supportInterpreter = true
```

The `leanOptions` subtable raises the line-length warning Verso would
otherwise emit at 60 columns (section 3.2). The `weak.` prefix matches
this repository's convention and Verso's own use of it for its manual
options. It is used uniformly rather than because it is needed here:
option names are rechecked after imports load, and every module of
this library reaches `VersoManual`, so the non-weak form would also
resolve.

Source layout follows the existing convention of a directory beside a
same-named index module, and `CLAUDE.md` § Repo structure's rule of
one indexing file per directory:

| Path | Content |
| --- | --- |
| `GebLeanDocs.lean` | Library index; imports `GebLeanDocs.Root`. |
| `GebLeanDocs/Root.lean` | Imports the two part modules; carries one `#doc (Manual)` command whose body includes them. |
| `GebLeanDocs/Tutorial.lean` | Imports its six chapters; carries one `#doc (Manual) "Part I …" =>` whose body includes them. |
| `GebLeanDocs/Tutorial/Ch1.lean` … `Ch6.lean` | Part I, one module per chapter, each importing `GebLeanDocs.Bibliography` and the `GebLean/Ramified/` modules it names, and carrying one `#doc (Manual)` command. |
| `GebLeanDocs/Reference.lean` | Imports its six chapters; carries one `#doc (Manual) "Part II …" =>` whose body includes them. |
| `GebLeanDocs/Reference/Ch1.lean` … `Ch6.lean` | Part II, one module per chapter, each importing `GebLeanDocs.Bibliography` and the `GebLean/Ramified/` modules it renders, and carrying one `#doc (Manual)` command. |
| `GebLeanDocs/Bibliography.lean` | Imports `VersoManual`; holds the bibliography entry definitions (section 4.4); carries no `#doc`. |
| `GebLeanDocsMain.lean` | The generator entry point; imports `GebLeanDocs.Root`, carries no `#doc`, and lies outside the library. |

Every module in the document hierarchy — the root, the two part
indexes, and the twelve chapters — carries exactly one
`#doc (Manual) "…" =>` command. `GebLeanDocs.lean`,
`GebLeanDocs/Bibliography.lean` and `GebLeanDocsMain.lean` carry none.
The rule is forced
by two facts. `{include NAME}` resolves
`NAME.«the canonical document object name»`
(`Verso/Doc/Elab.lean`, `includeSection`), which exists only where
`NAME` itself carries a `#doc`; and `#doc` derives that name from the
current module (`Verso/Doc/DocName.lean`), so a second `#doc` in one
module would collide. An index module is therefore both a Lean import
index and a `Part` with children, as `doc/UsersGuide/Releases.lean` is
in Verso's own tree. The header level at which each child is spliced
is given by `{include N NAME}`, and each part's title lives in its own
index module's `#doc` string rather than in `Root.lean`.

The Lean import graph runs `GebLeanDocs.lean → Root.lean →
Tutorial.lean / Reference.lean → chapters → Bibliography.lean`. Each
chapter imports `Bibliography.lean` directly, not through the root:
`citep` and `citet` resolve their arguments in the citing module's
environment, and Lean imports flow downstream only, so a chapter never
sees what `Root.lean` imports. The same asymmetry is why an index must
import the chapters it includes.

That asymmetry also governs the sampling mechanisms. `docstring`,
`name` and
`signature` each resolve their target in the citing module's
environment, so a chapter imports every `GebLean/Ramified/` module
whose declarations it renders or names. `Bibliography.lean` imports
`VersoManual`, which supplies every facility of section 2.2, and the
rest of the library reaches it transitively; `VersoManual` carries no
`module` keyword, so its own imports pass through.

The graph matters for the linter: `lake lint`'s root-module invocation
reaches only what the root module transitively imports, so a module
that `GebLeanDocs.lean` does not transitively import is neither linted
nor generated. Under the graph above every library module is reachable
from `GebLeanDocs.lean`; `Bibliography.lean` by way of the chapters.
Section 3.3 records the guard. Declarations imported from
`GebLean/Ramified/` are outside the linter's reach, which filters on
the `GebLeanDocs` prefix.

The new library and its executable root do not carry the `module`
keyword that `.claude/rules/lean-coding.md` § Lean 4 module system
requires. Verso's `#doc` emits a plain, non-`public` `def`, so under
`module` the document object would not be exported and neither `%doc`
nor a cross-module `{include}` could reach it; Verso's own document
modules carry no `module` either. A `public section` preceding the
`#doc` would in principle export it — `#doc` replaces the command
parser for the remainder of the module, so no closing `end` can
follow — but whether a Verso document elaborates under the module
system is untested and unexercised upstream, so it is not relied on
here.

This departs from the written rule and not from prevailing practice:
one of the repository's 418 first-party `.lean` files carries `module`
— `GebLeanMeta.lean` — against all 29 files of the vendored `Geb`
tree, which is generated from a repository that adopted the module
system. Section 11 schedules the rule amendment. The three files that
carry no `#doc` — `GebLeanDocs.lean`, `Bibliography.lean` and the
executable root — are covered by the same exemption for uniformity, no
per-file exception being useful.

`manualMain`'s `options` parameter is explicit and has no default, so
the entry point threads the process arguments through it; `config` is
`RenderConfig` and defaults to `{}`, and `sourceLink` and `issueLink`
are `HtmlConfig` fields reached through it:

```lean
def main (args : List String) : IO UInt32 :=
  manualMain (%doc GebLeanDocs.Root)
    (options := args)
    (config := { sourceLink := some "…", issueLink := some "…" })
```

`GebLeanDocs` is not a `Name` prefix of `GebLeanDocsMain`, and
`GebLeanDocs` does not import it, so `main` lies outside
`lake lint`'s reach as well as
outside the other three mechanisms; its declaration docstring and the
module docstrings of every chapter module are authored obligations
under `.claude/rules/lean-coding.md`, not linter-enforced ones. The
CI generator build is what compiles the module at all.

Generated HTML goes to `manualMain`'s default output directory `_out`,
overridable with `--output`; `_out` is added to `geb-lean/.gitignore`
beside the existing `/.lake`.

This is the repository's first `[[lean_exe]]`.

### 3.2 Inherited options and the three diagnostic classes

The package sets `moreLeanArgs = ["-DwarningAsError=true"]` and
`weak.linter.mathlibStandardSet = true`, both inherited by the new
library.

`-DwarningAsError=true` is retained. It is what promotes
`declaration uses 'sorry'` to an error, and the new library is outside
the `GebLeanAxiomChecks` gates (section 3.3), so relaxing it would
leave a `sorry` in a chapter module detected by nothing.

Nothing mechanical prevents that relaxation. Lake passes
`moreLeanArgs` on the command line and `leanOptions` in the module
setup, and Lean merges them setup-wins (`Lean/Elab/Frontend.lean`,
"override cmdline options with setup options"), so a per-library
`[lean_lib.leanOptions] warningAsError = false` would defeat the
package flag. The retention is a rule this design observes, not a
property the build enforces.

Three distinct classes of diagnostic bear on the new library, with
three distinct remedies:

- **Frontend linters**, configured by options. Silenced by a
  per-library `weak.linter.<name>` entry naming the linter. The
  `weak.` prefix is required wherever the module defining the option
  may be unimported, which is why `lakefile.toml` already uses it for
  `linter.hashCommand`, and is used uniformly here.
- **Environment linters**, the `@[env_linter]` set that
  `batteries/runLinter` runs. These are selected by attribute, not by
  options, so no `leanOptions` entry reaches them. They are silenced
  per declaration through `scripts/nolints.json`, which `runLinter`
  reads.
- **Verso's own warnings**, which are neither. They are emitted by
  `logWarningAt` during elaboration and reach the build as errors
  through `warningAsError`. Some are governed by an option and some
  by nothing at all.

  Option-governed, and silenced by a per-library `leanOptions` entry:
  `verso.code.warnLineLength`, whose default of 60 is below this
  project's 100-column style rule, and which the `lean` block checks
  on every block it shows (`show` defaults true; `leanTerm` and
  `signature` do not check it) — section 3.1 carries the entry. And
  `verso.docstring.elabMarkdown`, which defaults true, so a rendered
  docstring's inline code span or fenced block that no elaboration
  heuristic accepts warns. Inline spans have a last-resort keyword
  highlighter that accepts anything tokenizable; fenced blocks have
  none, and a fence that does not parse warns. No docstring in the
  twelve contributing modules contains a fence, so that exposure is
  currently zero.

  Governed by no option, and remediable only by changing the document
  source: an unused link definition, an unused footnote definition,
  and the deprecated forms of role and directive arguments — writing
  `x := v` for `(x := v)`, or `show := false` for `-show`. The last
  binds every argument the chapters write to a role or directive,
  including `signature`'s `show` and the `lean` block's flags.

Section 3.3 records the environment-linter interaction this design is
known to have; open questions 2 and 3 cover the residual across the
three classes.

### 3.3 Linter and gate coverage

The new library falls outside four existing mechanisms:
`defaultTargets = ["GebLean"]`, so `lake build` does not reach it;
`testDriver = "GebLeanTests"`, so `lake test` does not; the
`GebLeanAxiomChecks` gates name `GebLean`, `GebLeanTests`, and `Geb`,
so the axiom linter does not; and `lintDriver =
"batteries/runLinter"` lints the root modules of the default targets,
so a bare `lake lint` does not either.

`lake build` and `lake test`. The library has no test target, so there
is nothing for `lake test` to run; CI builds the library by running
the generator, which is its only execution. No separate provision is
made.

The axiom linter. Declined on the substance: chapter modules carry
prose and sampling directives rather than mathematical content, and
`-DwarningAsError=true` is retained (section 3.2), so `sorry` remains
an error there by the rule that section states. A CI-only placement
beside `lake lint -- GebLeanDocs` would be available if that ground
were judged insufficient; adding the gate to `GebLeanAxiomChecks`
would not, since `lake build GebLeanAxiomChecks` is step 3 of the
local pre-commit triad and would pull Verso into every commit that
touches a `.lean` file.

`lake lint`. Closed, following the repository's existing pattern for a
non-default library: the vendored `Geb` library is linted by
`lake lint -- Geb` in `geb-mathlib-refresh.yml`, guarded by
`scripts/tests/test-lint-driver.sh`. CI runs
`lake lint -- GebLeanDocs` in the same step as the generator.
`runLinter` takes a module name and lints every declaration whose
module is prefixed by that name's root component, so the library name
and its root module name coinciding is what makes the invocation work.

That guard script checks two invariants for `Geb`: the invocation
form, and that no module is orphaned from the umbrella and so
invisible to the root-module invocation. Both apply here, so the
script is extended to `GebLeanDocs` and the import graph of section
3.1 is what it checks, `Bibliography.lean` included.

Closing the exemption brings the environment linters into force, and
one of them reports by construction. Verso's `#doc` command emits, per
module, a `def <Module>.«the canonical document object name»` with no
doc comment; `docBlame` is an `@[env_linter]` that exempts only
auto-declarations and instances, and that name is neither. No
docstring can be attached to a generated definition, so the remedy is
an entry in `scripts/nolints.json`, which becomes a deliverable
(section 11): one per document module, plus one per declaration a Part
I `lean` block introduces without a docstring, since those blocks keep
their environment by default and so contribute real declarations to
the module.

The entries are appended manually. `runLinter --update` rewrites
`scripts/nolints.json` wholesale from the current run's results, which
would discard the entries already there.

## 4. Document structure

Six chapters in each of two parts. Every cross-reference in this spec
names the part.

### 4.1 Part I, tutorial

1. **Free algebras and recurrence.** `AlgSig`, `FreeAlg`,
   `FreeAlg.recurse`; Leivant III section 2.1, eq. (1); the standing
   convention that the algebra is infinite; word algebras (monadic and
   polyadic) against tree algebras. Contains the section 7 signature
   presentation of `FreeAlg.recurse` and the `deftech` definitions for
   the eq. (1) vocabulary and the schema's fragments.
2. **The need to restrict recurrence.** Unrestricted nesting reaches
   the `2_m` ladder (Leivant III section 2.4(4)), stated with a
   forward reference to `ramTwoPow`.
3. **Ramified types.** `RType` as `FreeAlg rTypeSig`; `RType.o`,
   `RType.arrow`, `RType.omega`; `RType.IsObj`, `RType.IsTower`,
   `RType.tower`; `RType.interp`, and Leivant III section 2.7's
   identification of every object type's denotation with the same
   carrier. Contains the `deftech` definitions for the type
   vocabulary. The first-order tier reading appears as an aside.
4. **The ramified schema.** Leivant III section 2.3, eq. (4) for
   monotonic ramified recurrence and eq. (5) for flat recurrence;
   `RIdent` and its three shapes `DefnShape`, `MrecShape`,
   `FrecShape`, with `RIdent.mrec` and `RIdent.frec` presented by
   section 7; the indexing that places the recurrence argument at
   `RType.omega τ` against an output at `τ`, so that ill-tiered
   recurrence is inexpressible rather than rejected; `RIdent.interp`
   as tier erasure.
5. **The section 2.4 ladder.** `ramKappa`, `ramDeltaIdent`, `ramAdd`,
   `ramMul`, `ramSize`, the second-order `ramExp`, and `ramTwoPow`,
   each paired with its interpretation lemma, stated to exhibit the
   semantics and not proved.
6. **Ramification and complexity.** The three cells, stated and cited,
   with no proof: monadic word algebras and linear space (`E^2`,
   Ritchie; Clote), polyadic word algebras and polynomial time
   (Leivant I; Bellantoni and Cook), with the tree-algebra cost-model
   caveat of Dal Lago, Martini and Zorzi; and higher-type ramification
   and the Kalmar elementary functions (Leivant III section 6.1,
   Theorem 14). Provenance follows the design spec section 2.2.

### 4.2 Part II, reference

Each chapter renders the covered declarations of the modules it names,
per section 4.3, not every declaration in them.

1. **Correspondence.** The paper-to-code table. Leivant's names are
   not this document's defined terms, so they need a table of their
   own; it is accompanied by a pointer to the generated terminology
   index.
2. **Signatures, free algebras, ramified types.** `AlgSig.lean`,
   `Algebras.lean`, `SortedSig.lean`, `RType.lean`.
3. **The Lawvere-theory layer.** `Term.lean`, `Interp.lean`,
   `SynCat.lean`: `Tm` with its clone laws, `SortedModel` /
   `Presentation` / `interpQuotRel`, and `SynCat` with its finite
   products. `SortedSig`, rendered in Part II chapter 2, is referred
   to here through the `name` role.
4. **The higher-order system and its instantiations.** `HigherOrder.lean`,
   `OmegaShift.lean`, `Examples.lean`: `appSig`, `RIdent`,
   `higherOrder`, `RMRecCat`, `identHom`; `RType.omegaShift`,
   `kappaHat`, `kappaIdent`, `deltaIdent`; and the section 2.4 ladder
   whose narrative reading is Part I chapter 5.
5. **The characterization.** `SynCatFO`, `collapseFunctor` with
   `collapseFunctor_faithful`, `ramified_definability`,
   `collapseKFunctor` with `collapseKFunctor_faithful`, and
   `ramified_definability_kSim`, as endpoint declarations. One
   paragraph each on the shape of the machine route and the
   encoding route.
6. **Transcription map and scope.** Paper section and equation from
   the design spec section 2.1's table, Lean modules from the area
   document's Modules section; then the modules section 4.3 names as
   absent.

### 4.3 What Part II covers

The ten modules Part II documents contain 309 top-level declarations,
of which 179 are definitional (`def` 165, `structure` 9, `abbrev` 4,
`inductive` 1) and 130 are theorems and instances (`theorem` 124,
`instance` 6). The count is of declarations beginning at column zero,
after stripping block and line comments, and admits a leading
attribute group and the `private`, `protected`, `partial`, `unsafe`,
`scoped` and `nonrec` modifiers. Part II does not render all of them.

A declaration is covered when it satisfies one of:

- it is a type former, or a field of one;
- it is an operation the paper names, or that this document's prose
  discusses;
- it is an interpretation or denotation function, or one of the
  interpretation lemmas that state such a function's value;
- it is a predicate classifying sorts or identifiers;
- it is one of the seven endpoint declarations of Part II chapter 5.

A declaration is excluded when its only role is to assemble a covered
declaration or to support a proof: `simp` lemmas that are not
interpretation lemmas, transport, cast and congruence lemmas,
renaming and substitution fusion lemmas, arity and index bookkeeping,
per-clause step-function and hole-index helpers, environment
constructions, and file-local auxiliaries.

Where both lists reach a declaration, the exclusion governs, with two
stated exceptions: the constructor and eliminator of a covered type
former are covered (so `FreeAlg.mk` is), and a schema's reduction rule
is covered (so `FreeAlg.recurse_mk` is, being eq. (1) itself).
Decidability instances of covered predicates and of covered types are
excluded; the predicates and types themselves are covered.

Applying the rule is expected to yield on the order of sixty to a
hundred rendered declarations: a subset of the 179 definitional
declarations above, together with the interpretation lemmas clause 3
admits, across Part II chapters 2 to 4, plus Part II chapter 5's seven
endpoint declarations, which come from the two endpoint modules and so
lie outside the 309. A covered structure's fields are rendered by the
structure's own `docstring` block and do not take blocks of their own.
Enumerating the set exactly is the first task of Part II's phase, and
the enumeration is committed to the plan, so that the chapter sizes
are fixed before writing begins and the estimate above becomes a check
rather than a discovery.

The three-way module partition:

- Covered under the rule above: `AlgSig.lean`, `Algebras.lean`,
  `SortedSig.lean`, `RType.lean`, `Term.lean`, `Interp.lean`,
  `SynCat.lean`, `HigherOrder.lean`, `OmegaShift.lean`,
  `Examples.lean`.
- Covered by endpoint declaration only, internals absent:
  `Soundness/Collapse.lean`, `Characterization.lean`.
- Named as absent, with a pointer and no declaration reference: the
  `Definability/` and `Polynomial/` directories and their index
  modules `Definability.lean` and `Polynomial.lean`; the remainder of
  the `Soundness/` directory and its index module `Soundness.lean`;
  `SigEquiv.lean`; `PresentationEquiv.lean`; and the area index module
  `GebLean/Ramified.lean`.

### 4.4 Manual assembly

`%doc M` yields the single `Part` that module `M`'s one
`#doc (Manual) "…" =>` command produces, and `manualMain` takes one
`Part`. `GebLeanDocs/Root.lean` therefore carries one root `Part`
whose two children are the parts, each of which includes its six
chapter modules through its index module (section 3.1). Chapter order
is include order, not module name order.

Bibliography entries are defined Lean-side in
`GebLeanDocs/Bibliography.lean` and cited with `citep` and `citet`.
Verso offers four entry types — `InProceedings`, `Thesis`, `ArXiv`,
`Article`. Three of the six cited works are book chapters or
proceedings contributions (Leivant I, Clote, Dal Lago and others) and
are entered as `InProceedings`; `Article` requires `volume`, `number`,
and an explicit `month`, none defaulted.

## 5. Code sampling

| Mechanism | Used in | Property |
| --- | --- | --- |
| `docstring` | Part II | Renders the declaration and its doc comment. A rename, removal, or missing docstring fails elaboration; a retype does not (section 2.3). |
| `signature` | Part I chapters 1 and 4 | Checks the written type against the declaration by definitional equality. A retype fails elaboration; a renamed outer binder does not (section 2.3). |
| `name` role | Both parts, in prose | Resolves and hyperlinks a declaration; an unresolvable name fails elaboration. |
| `lean` / `leanTerm` blocks | Part I | Elaborated illustrations, written against the real imports. |

Copy-pasted source text is not used in either part. Where section 7
discusses a signature, the manual shows the checked `signature` block
and not an unchecked reproduction.

`docstring` is used in Part II only. Part I refers to declarations
through the `name` role and the `signature` blocks, so the source-side
changes of section 8 are bounded by Part II's covered set.

## 6. Terminology discipline

Each technical term is defined exactly once with `deftech`, at the
point in Part I where the reader first needs it, and every subsequent
use is a `tech` reference. Verso reports undefined terms, and
duplicated terms that are referenced, at generation.

Terms introduced in Part I chapter 1, from Leivant III eq. (1):

| Term here | Leivant III's symbol | Leivant III's name | Position in `FreeAlg.recurse` |
| --- | --- | --- | --- |
| constructor label | `c_i` | constructor | first argument of `g` |
| recurrence parameters | `x_vec` | recurrence parameters | second argument of `g` |
| recurrence argument | `c_i (a_1 ... a_{r_i})` | recurrence argument | the matched `FreeAlg.mk` value |
| subterms | `a_1 ... a_{r_i}` | no dedicated name | third argument of `g` |
| recursive results | `phi_1 ... phi_{r_i}` | critical arguments | fourth argument of `g` |
| step functions | `g_ci` | recurrence functions | `g` at a label; `g` is the family |

Four of the six name a position within `g`'s type in the section 7
presentation; a fifth, the step functions, names `g` itself. The
recurrence argument is the matched value rather than an argument of
`g`.

Also in Part I chapter 1, the fragment names of Leivant III section
2.1: monotonic (the step does not see the subterms), closed (no
parameters), and flat (no recursive results).

Terms introduced in Part I chapter 3, which cannot be defined before
`RType` exists: r-type, object type, `Omega`-type, and tier.

Whether the further vocabulary of Part I chapters 1 and 6 — monadic
and polyadic word algebra, tree algebra, Kalmar elementary, tier
erasure, clone — is `deftech`-defined or left as prose is settled when
those chapters are written, and recorded in the plan. The discipline
binds whichever set is chosen.

## 7. Signature presentations

Verso's `signature` code block parses a written `declId declSig`,
optionally preceded by `def` or `theorem`, and checks it against the
real declaration through
`SubVerso.Examples.checkSignature`. Two properties of the block govern
how the presentations are written.

It checks definitional equality of the type and the level-parameter
count, and nothing else that survives. Either mismatch throws, and the
block's handler records an editor suggestion carrying the
declaration's actual pretty-printed signature before rethrowing. A
mismatch in an outer binder's name, binder info, or `optParam` default
is reported into a nested message log that the block discards
(section 2.3), so it does not reach the build. Matching the outer
binder names is therefore a convention the author observes; only the
type and the level-parameter count are enforced.

It resolves names in an empty scope. The block constructs a fresh
`Command.State`, whose default scope has no current namespace, no open
declarations, and default options — so a chapter module's
`open GebLean.Ramified` does not reach inside it, and `autoImplicit`
is in force there. An unqualified `AlgSig` would auto-bind as an
implicit, and the presentation would then fail on the type or
level-parameter comparison rather than on the name. Every global name
inside a `signature` block is therefore written fully qualified;
generalized field notation on a local, such as `A.B`, resolves by the
local's type head and needs no qualification. This
matches the Lean reference manual's own usage, whose `signature`
blocks are fully qualified even under an ambient `open`.

The case that motivates the presentation: within `g`'s type,
`FreeAlg.recurse` (`GebLean/Ramified/AlgSig.lean`) names only the
first argument, leaving three positions anonymous, two of which differ
only in codomain, so the vocabulary of section 6 is not recoverable
from the signature. Those positions lie inside `g`'s type, which
`checkSignature` does not inspect, so the author may name them:

````text
```signature
GebLean.Ramified.FreeAlg.recurse
    {A : GebLean.Ramified.AlgSig} {P C : Type}
    (g : (label : A.B) → (parameters : P) →
      (subterms : Fin (A.ar label) → GebLean.Ramified.FreeAlg A) →
      (results : Fin (A.ar label) → C) → C) :
    P → GebLean.Ramified.FreeAlg A → C
```
````

The fence language is `signature`; the block accepts a `show` option,
default true.

`RIdent.mrec` and `RIdent.frec` are presented the same way in Part I
chapter 4, likewise fully qualified. Both already name every outer
binder, so no naming arises there; the presentation exhibits the tier
indexing beside the prose that discusses it, and supplies the retype
check that `docstring` does not.

Part II uses `docstring` for these declarations rather than repeating
the presentation. The eq. (1) vocabulary's `deftech` definitions live
at the Part I chapter 1 presentation alone; the type vocabulary's live
in Part I chapter 3 (section 6), and every other site refers to both
with `tech`.

## 8. Source-side changes

Two kinds of change to `GebLean/Ramified/`, both additive and both
bounded by the covered set of section 4.3 across the twelve modules
that contribute rendered declarations.

Declaration docstrings, where a covered declaration carries none. The
set is expected to be empty: across the twelve modules the
undocumented declarations are four anonymous `instance` declarations
in `RType.lean` and eight `@[simp] theorem`s, none of which section
4.3's rule covers. The deliverable is therefore contingent
(section 11).

Names for anonymous instances the reference half renders. Two are
required: `collapseFunctor.Faithful` (`Soundness/Collapse.lean`) and
`collapseKFunctor.Faithful` (`Characterization.lean`) are anonymous,
and `docstring` names a declaration by identifier. They become
`collapseFunctor_faithful` and `collapseKFunctor_faithful`, following
the existing `yonedaConstEmbedding_faithful` in `GebLean/`. Naming an
anonymous instance is additive: it breaks no client, since resolution
is unaffected, and it makes the declaration reachable by name. The
four anonymous instances in `RType.lean` are not covered and stay as
they are.

No declaration is renamed, retyped, moved, or removed, and none is
added. Should writing the document reveal a refactoring opportunity in
`GebLean/Ramified/`, it is recorded and deferred to its own branch,
per `CLAUDE.md` § one concern per branch.

The criterion separating the two is whether a change is required by
the work or merely discovered during it, bounded by whether the
required change is itself an independently reviewable concern. The
docstrings and instance names are required, since the manual renders
them, and are not independently reviewable, so they are on this
branch. A change that were both — a toolchain bump, a repair to CI —
would take its own branch, sequenced first.

## 9. Failure modes and fallbacks

**Dependency resolution.** The exposure is ordering (section 2.1): a
resolution that adopted Verso's `plausible` pin over mathlib's would
change mathlib's build inputs, miss the `lake exe cache get`
artifacts, and cost every contributor and CI a mathlib rebuild from
source. The acceptance criterion is literal: the `plausible` entry in
`lake-manifest.json` is unchanged after `lake update`, verified in a
scratch clone before the change is committed. Section 3.1's require
placement is the means; the criterion is what is checked. Mathlib's
`plausible` is the later of the two revisions, so the open question is
whether Verso builds against a newer one.

Fallbacks in order: pin `plausible` explicitly at the mathlib
revision; and, if Verso does not build against it, reduce the
deliverable to Markdown plus a module under `GebLeanTests/` holding
one `example` per presented signature, ascribing the written type to
the real declaration. That fallback loses the rendering, the
terminology index, and the `checkSignature` machinery —
`checkSignature` is `subverso`'s, so it is unavailable exactly when
this fallback is reached — and keeps type-level checking against the
real declarations by ascription. A module there enters the test
driver's dependency graph and the `GebLeanAxiomChecks` gate over
`GebLeanTests`, hence the local pre-commit triad, which is the
placement sections 3.3 and 10 otherwise avoid; under the fallback
there is no Verso dependency to make that costly.

**Declaration drift.** A rename, a removal, or a missing docstring
fails the doc build. A retype fails it only at the three declarations
section 7 presents. A renamed outer binder and a declaration added to
a covered module are not detected at all (section 2.3).

**Terminology drift.** An undefined term, or a duplicated term that is
referenced, fails generation rather than the build, so it is caught by
CI's generator run (section 10).

**Diagnostic interaction.** Three classes (section 3.2). A frontend
linter is silenced by a per-library `weak.linter.<name>` entry; an
environment linter by an entry in `scripts/nolints.json`; a Verso
warning by its option where it has one, and otherwise only by changing
the document source. The known instances are `docBlame` against
Verso's generated document definitions (section 3.3),
`verso.code.warnLineLength`, whose default is below this project's
line-length rule, `verso.docstring.elabMarkdown`, whose fenced-block
exposure is currently zero, and the option-less warnings on unused
link and footnote definitions and on deprecated argument syntax.
`warningAsError` is retained.

**Build cost.** Verso sets `precompileModules := false` and is a
substantial dependency. The cost falls on CI and on contributors who
build the target explicitly; the local scripts do not build it
(section 10).

## 10. Verification and gates

- CI gains one step in the parent
  `.github/workflows/lean_action_ci.yml`, running
  `lake lint -- GebLeanDocs` and then the generator
  (`lake exe geblean-docs`), so that the linter, the
  elaboration-time checks, and the generation-time checks of section
  2.3 all run.
- No local script gains a build step. `scripts/pre-push.sh` is mandatory
  before every push regardless of the files touched, so adding the
  generator there would make every contributor build Verso and the two
  dependencies not already in the closure on every push; the same reasoning
  declines the axiom gate in the pre-commit triad (section 3.3).
- The consequence: a commit that adds or breaks a chapter module
  passes both local scripts, and the breakage is caught in CI.
  `scripts/pre-commit.sh` carries a comment instructing that a target
  outside the test driver's dependency graph be added there and to
  `pre-push.sh` in lockstep; this design declines that instruction,
  so both the comment and `.claude/rules/ci-and-workflow.md` are
  amended to record the exception rather than left to contradict it.
- Source-side changes under section 8 touch `.lean` files under
  `GebLean/`, so they are covered by `bash scripts/pre-commit.sh` in
  the ordinary way.
- The document is `.lean`, so it adds no markdownlint or doctoc
  coverage. This spec and its plan do.

## 11. Deliverables

- `geb-lean/lakefile.toml`: the `verso` require ahead of `mathlib`,
  and the `GebLeanDocs` library, its `[lean_lib.leanOptions]` subtable
  raising `verso.code.warnLineLength`, and the `geblean-docs`
  executable appended (sections 3.1, 3.2), together with whatever
  further entries open question 2 settles.
- `geb-lean/lake-manifest.json`: updated, with `plausible` unchanged
  (section 9).
- `geb-lean/.gitignore`: `_out` (section 3.1).
- Seventeen library modules — `GebLeanDocs.lean`, `Root.lean`,
  `Tutorial.lean`, `Reference.lean`, twelve chapter modules and
  `Bibliography.lean` — and the executable root
  `GebLeanDocsMain.lean` (section 3.1).
- `geb-lean/scripts/nolints.json`: `docBlame` entries per section 3.3,
  appended manually.
- `geb-lean/scripts/tests/test-lint-driver.sh`: extended to
  `GebLeanDocs` (section 3.3).
- `collapseFunctor_faithful` and `collapseKFunctor_faithful` named in
  `GebLean/Ramified/` (section 8).
- Any docstrings the covered set requires, contingent and expected
  empty (section 8).
- The Part II covered-declaration enumeration and the Part I
  `deftech` vocabulary, both committed to the plan (sections 4.3, 6).
- One CI step in the parent `.github/workflows/lean_action_ci.yml`
  (section 10).
- Amendments to `scripts/pre-commit.sh`'s comment and to
  `.claude/rules/ci-and-workflow.md` recording the exception
  (section 10), and to that file's description of
  `test-lint-driver.sh`, which is written in `geb-mathlib` terms and
  now governs a second library (section 3.3).
- Amendments to `.claude/rules/lean-coding.md` § Documentation and
  § Comment and docstring rules, which state the same mandate,
  recording that Verso's generated document definitions carry no
  docstring, so that neither contradicts the `nolints.json` entries
  (section 3.3); and to § Lean 4 module system, recording the
  `module`-keyword exemption (section 3.1).
- Entries for the manual in `docs/index.md` and in
  [`docs/areas/ramified-recurrence.md`](../../areas/ramified-recurrence.md).

## 12. Deferred and out of scope

- **Publication.** Deferred to its own workstream. The facts that make
  it a separate decision: `anoma/geb` already has a GitHub Pages site
  serving the Common Lisp "GEB Manual", and a repository has one Pages
  site, which `actions/deploy-pages` replaces wholesale; `rokopt/geb`
  has no Pages site, and per `.claude/rules/fork-upstream-flow.md` the
  fork is where topic-branch CI runs; the mandated upstream route is a
  cross-repository pull request, whose token is read-only and carries
  no `id-token`, so a deploy step would fail on every upstream PR; and
  the existing workflow has one job, no deployment job, no
  `environment: github-pages`, no artifact upload, and triggers on
  `pull_request` filtered by path but not by branch. In favour of the
  deferral being cheap to reverse: the workflow already declares
  `pages: write` and `id-token: write` under a comment naming Pages
  deployment. Until publication is scheduled, the deliverable's return
  is the compile-checked sampling and the machine-checked terminology
  index, read by contributors who build the target.
- Coverage of `GebLean/Ramified/Polynomial/`, beyond a pointer. Should
  the primed layer become canonical, Part I's prose is unaffected but
  its sampled declarations are repointed alongside Part II's, since
  Part I chapters 1 to 5 name legacy declarations directly; the
  bridge equivalences would become the subject of a new chapter.
- Any proof content. The two routes are described by shape only.
- Any Verso document for other areas of the repository.
- The deferred mathematical items of the ramified-recurrence
  workstream, catalogued in
  [the design spec](2026-07-01-ramified-recurrence-approaches-design.md)
  sections 9 and 10, are described as absent, not addressed.
- Consolidation of the area document and the design spec. The manual
  links to both and does not replace them; whether their overlapping
  material is retired is a separate decision, recorded here so that it
  is not made implicitly.
- Reconciling the repository's committed review artefacts with
  `docs/process.md` § Defect categorisation, raised by this branch's
  round-3 review and recorded in `TODO.md`.

## 13. Open questions

1. Whether Verso at `v4.29.0-rc6` builds against this repository's
   dependency set with the `plausible` pin undisturbed. Settled by the
   resolution investigation against section 9's acceptance criterion;
   the fallbacks there cover the negative case.
2. Which frontend linters and which Verso warnings object to a chapter
   module, and so which per-library `leanOptions` entries are needed
   beyond the `verso.code.warnLineLength` raise that section 3.2
   establishes, and which document-source conventions the option-less
   warnings impose. Settled by the same investigation.
3. Whether environment linters beyond `docBlame` report against
   Verso's generated definitions, and how many `scripts/nolints.json`
   entries the Part I `lean` blocks add. Settled by running
   `lake lint -- GebLeanDocs` locally, before the CI step is added.
4. Which of Part I chapters 1 and 6's further vocabulary is
   `deftech`-defined (section 6), and which declarations Part II's
   covered set contains (section 4.3). Both are settled during the
   phases that need them and recorded in the plan.

## References

The six published works below are the bibliography entries of section
4.4. All six are cited in Part I chapter 6, where the complexity cells
are stated; Leivant III is additionally cited throughout. The last
three entries are pointers rather than citations. Section 4.4's
`Article` entries require a `volume`, `number` and `month`, of which
this list carries only part for Leivant III, Bellantoni and Cook, and
Ritchie; the remainder are gathered when `Bibliography.lean` is
written.

- D. Leivant, "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity", Annals of Pure
  and Applied Logic 96 (1999) 209-229. DOI
  `10.1016/S0168-0072(98)00040-2`.
- D. Leivant, "Ramified recurrence and computational complexity I:
  Word recurrence and poly-time", in Feasible Mathematics II,
  Birkhauser, 1995, pp. 320-343. DOI
  `10.1007/978-1-4612-2566-9_11`.
- S. Bellantoni and S. Cook, "A new recursion-theoretic
  characterization of the polytime functions", Computational
  Complexity 2(2) (1992) 97-110. DOI `10.1007/BF01201998`.
- P. Clote, "Computation models and function algebras", Handbook of
  Computability Theory, North-Holland, 1999, pp. 589-681. DOI
  `10.1016/S0049-237X(99)80033-0`.
- R. W. Ritchie, "Classes of predictably computable functions",
  Transactions of the AMS 106 (1963) 139-173. DOI
  `10.1090/S0002-9947-1963-0158822-2`.
- U. Dal Lago, S. Martini, M. Zorzi, "General Ramified Recurrence is
  Sound for Polynomial Time", DICE 2010, EPTCS 23, pp. 47-62. DOI
  `10.4204/EPTCS.23.4`.
- Verso, `https://github.com/leanprover/verso`, tag `v4.29.0-rc6`.
- Area document:
  [`docs/areas/ramified-recurrence.md`](../../areas/ramified-recurrence.md).
- Design spec:
  [`2026-07-01-ramified-recurrence-approaches-design.md`](2026-07-01-ramified-recurrence-approaches-design.md).
