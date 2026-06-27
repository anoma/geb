# geb-mathlib vendoring: mirror-and-back-port design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
## Contents

- [Summary](#summary)
- [Context and motivation](#context-and-motivation)
  - [The two repositories](#the-two-repositories)
  - [The toolchain gap](#the-toolchain-gap)
  - [Why vendoring rather than an external dependency](#why-vendoring-rather-than-an-external-dependency)
- [Goals](#goals)
- [Non-goals](#non-goals)
- [Design](#design)
  - [Vendored scope and the built library](#vendored-scope-and-the-built-library)
  - [Layout and import-path identity](#layout-and-import-path-identity)
  - [Lakefile wiring, build scope, and lint scope](#lakefile-wiring-build-scope-and-lint-scope)
  - [The back-port patch and notes](#the-back-port-patch-and-notes)
  - [Refresh script](#refresh-script)
  - [Continuous-integration workflow](#continuous-integration-workflow)
  - [Smoke test](#smoke-test)
  - [Licensing and provenance](#licensing-and-provenance)
- [The build spike (evidence)](#the-build-spike-evidence)
- [Alternatives considered](#alternatives-considered)
  - [External Lake dependency (git revision or registry)](#external-lake-dependency-git-revision-or-registry)
  - [Compatibility shim instead of a patch](#compatibility-shim-instead-of-a-patch)
- [Cross-cutting guarantees](#cross-cutting-guarantees)
- [Documentation touched](#documentation-touched)
- [Risks and open questions](#risks-and-open-questions)
- [References](#references)
- [Tags](#tags)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Summary

This repository (`geb-lean`, experimental) gains the ability to build
on curated code that has been ported to its counterpart repository
`geb-mathlib`. Rather than depend on `geb-mathlib` as an external Lake
package, the design vendors a copy of `geb-mathlib`'s source tree into
a dedicated directory, builds the subset that this repository consumes
under a hand-authored patch ("back-port patch") that makes it compile on
this repository's current toolchain, and refreshes that copy on demand
and on a schedule through a continuous-integration workflow that opens
a pull request on success and an issue on failure.

Vendoring is chosen over an external Lake dependency because the two
repositories sit on different mathlib toolchains, and adapting the
small, curated body backward to this repository's toolchain is far
cheaper than migrating this repository's large body forward. Only
vendoring, where this repository owns the copy, makes that adaptation
possible. The version gap is bridged by editing the copy, not by moving
either repository's toolchain.

## Context and motivation

### The two repositories

`geb-lean` is the experimental formalisation hub. `geb-mathlib` is its
curated counterpart, holding material that meets upstream-contribution
standards. The intended flow is one-directional in provenance:
`geb-mathlib` never refers to uncurated `geb-lean` code, but once a
piece of `geb-lean` material is curated and ported to `geb-mathlib`,
this repository should be able to build further exploration on top of
the curated result instead of keeping a local copy.

### The toolchain gap

At the time of writing:

| Property | `geb-lean` | `geb-mathlib` |
| --- | --- | --- |
| `lean-toolchain` | `v4.29.0-rc6` | `v4.32.0-rc1` |
| mathlib `rev` | `v4.29.0-rc6` | `v4.32.0-rc1` |
| cslib `rev` | `v4.29.0-rc6` | `v4.32.0-rc1` |
| module-system use | classic `import` | `module` / `public import` |

The last row is a difference in what each repository's code uses, not a
capability gap: the build spike below confirms `v4.29.0-rc6` parses and
compiles the module system. Lake enforces a single toolchain and a
single resolved revision per package name across an entire dependency
graph, so any approach that compiles `geb-mathlib` code inside
`geb-lean` requires the two to agree on a toolchain. Two directions
close that gap:

- Forward: migrate `geb-lean` to `v4.32.0-rc1`. A scoping
  investigation measured this at roughly 45 to 70 engineer-hours,
  dominated by the Lean 4.30 `TypeCat` refactor across this
  repository's profunctor and functor-to-`Type` code, with a tail risk
  in scattered Lean-core transparency and defeq changes.
- Backward: adapt `geb-mathlib`'s consumed modules to compile under
  `v4.29.0-rc6`.

The backward direction is cheaper today. Two distinct facts support it,
and they must not be conflated:

- Code size. `geb-mathlib` is curated, carrying no dead-ends or
  duplicate formulations, so it stays small while this repository is
  under active experimentation. The body to adapt is therefore small.
- Adaptation cost. The cost is the size of the back-port patch, which
  tracks the mathlib API delta across the version gap, not the line
  count. Because `geb-mathlib` auto-bumps to newer mathlib while
  `geb-lean` stays pinned, that gap widens over time, so the patch is
  expected to accrue hunks even if `geb-mathlib`'s line count does not.
  The patch measured below is a snapshot at the current
  three-minor-version gap.

The design is correct so long as maintaining the patch stays cheaper
than the forward migration. The hard boundary at which it ceases to be
viable is named under Risks.

### Why vendoring rather than an external dependency

An external Lake dependency (`require` by git revision, or via the
Reservoir registry) cannot be edited by the consumer, so it forces the
forward migration. Vendoring places an editable copy in this
repository, which unlocks the backward adaptation. Vendoring has two
further consequences an external dependency does not:

- It removes a cross-repository build-time dependency edge. The
  canonical upstream (`anoma/geb`) would otherwise fetch
  `rokopt/geb-mathlib`, a personal-account repository, when building. A
  vendored copy is hermetic and fetches nothing at build time. (The
  refresh workflow that produces the copy is a separate matter; it is
  scoped to `origin`, see below.)
- It duplicates the curated code in this repository. The duplication is
  machine-managed (a mirror refresh, not a hand-maintained fork) and
  reviewable in pull-request diffs.

## Goals

- This repository can `import` curated `geb-mathlib` modules using the
  same module paths that `geb-mathlib` itself uses.
- This repository stays on its current toolchain; no forward migration
  is required to consume curated code.
- The vendored tree refreshes from the latest `geb-mathlib` on demand
  and on a schedule, as a complete overwrite that leaves behind no
  files removed upstream.
- The refresh attempts a build of the consumed subset and surfaces
  success as a reviewable pull request and failure as an issue.
- Local builds, third-party clones, and continuous integration on both
  the `origin` fork and the canonical `upstream` repository all work
  without credentials.

## Non-goals

- Migrating `geb-lean` to `v4.32.0-rc1`. That remains a separate,
  independently-motivated effort, out of scope here.
- Publishing `geb-mathlib` to the Reservoir registry.
- Vendoring `geb-mathlib`'s `GebMeta` or `GebTests` libraries or its
  build configuration; only the `Geb` namespace is mirrored.
- Pre-emptively adapting for cslib skew. `Geb.Cslib` is built (today an
  empty stub); if it gains content importing `Cslib.*` that does not
  compile on `geb-lean`'s cslib, the refresh fails and a human adds a
  patch hunk or excludes the module — it is not adapted ahead of need.
- Automatically rewriting vendored code (a codemod or rule engine).
  Adaptation is a hand-authored patch; when the patch no longer applies
  or the ensuing build fails, the refresh stops and a human decides the
  change. See "The back-port patch and notes".

## Design

### Vendored scope and the built library

The refresh mirrors `geb-mathlib`'s `Geb` namespace — the top-level
`Geb.lean` index and the `Geb/` tree — into `vendor/geb-mathlib/`, as a
complete overwrite of that subtree (so no file removed upstream lingers).
`geb-mathlib`'s separate `GebMeta` and `GebTests` libraries and its
repository build configuration (`lakefile.toml`, `lean-toolchain`,
`.github/`, manifest) are not vendored; the back-port patch drops the
`import GebMeta` line from the vendored `Geb` index so the namespace
builds without `GebMeta` (whose `@[env_linter]` would otherwise mis-audit
`geb-lean`'s accepted `Classical.choice` usage). `geb-mathlib`'s
`doc-gen4` requirement is documentation-only and is imported by no
vendored module, so it is not vendored.

The vendored `lean_lib Geb` globs the whole namespace
(`globs = ["Geb.*"]`), so the wiring names no `geb-mathlib` subdirectory
and tracks `geb-mathlib`'s growth automatically: a module added upstream
is vendored and built on the next refresh with no lakefile edit. The
back-port patch keeps every globbed module compiling under
`v4.29.0-rc6`; as the version gap widens the patch accrues hunks, and a
module that cannot be back-ported is handled by the build-and-issue
mechanism (a patch hunk, or removal from the vendored copy via an
exclusion list in the refresh script).

Two build scopes follow. Ordinary `lake build` / `lake test` (this
repository's default `GebLean` targets) compile only the vendored
modules that `geb-lean` actually imports, on demand through Lake's import
graph, so day-to-day builds stay fast. The refresh workflow additionally
builds and lints the whole vendored library (`lake build Geb`,
`lake lint Geb`), so a vendored module that nothing yet imports cannot
drift undetected and the patch is kept complete.

### Layout and import-path identity

`geb-mathlib`'s library root is `Geb`. The vendored copy is placed
under `vendor/geb-mathlib/`, preserving the upstream tree (so
`vendor/geb-mathlib/Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`, and so
on). The Lake configuration adds a `lean_lib Geb` whose
`srcDir = "vendor/geb-mathlib"` and whose `globs = ["Geb.*"]` cover the
whole vendored namespace, naming no `geb-mathlib` subdirectory. With that
mapping, a `geb-lean` module writes

```lean
import Geb.Mathlib.Data.PFunctor.Slice.Basic
```

byte-identically to the import as it reads inside `geb-mathlib`. The
`Geb` root does not collide with this repository's `GebLean` and
`GebLeanTests` libraries: the libraries have disjoint roots and globs
(`GebLean.*` and `GebLeanTests.*` versus `Geb.*`), so no module-name
collision or double-build results. The source
directories are not disjoint — `GebLean`'s `srcDir` defaults to the
package root, which contains `vendor/` — so it is the roots-and-globs
separation, not directory separation, that keeps the builds distinct.

### Lakefile wiring, build scope, and lint scope

- The vendored `lean_lib Geb` inherits the same hard `warningAsError`
  as the rest of the package; no per-library relaxation is added. The
  spike built the current built set clean under that flag (inside the
  `GebLean` library with all its strict `leanOptions`), so no exemption
  is needed. Keeping the vendored library under the standard discipline
  also means a future deprecation, linter, or `shake` warning in
  vendored code — which the patch does not repair — fails
  the refresh build and is surfaced by the build-and-issue mechanism,
  the same early signal the design relies on for hard breaks. A
  narrowly-scoped relaxation can be added later only if such warnings
  prove to be routine churn rather than meaningful drift.
- The vendored library is linted by the refresh workflow's
  `lake lint Geb` (the `batteries/runLinter` driver named on the vendored
  library), not excluded. Bare `lake lint` lints only the default
  `GebLean` target, so the refresh names `Geb` explicitly. `geb-mathlib`
  is the
  curated repository and runs at least as strict a linter set (it adds
  `linter.flexible` and `linter.style.header` over `geb-lean`'s), so
  vendored code that passed there is expected to pass here. A lint
  failure is a signal worth surfacing, not suppressing: it indicates
  either a `v4.29`-versus-`v4.32` linter difference or a lint issue
  introduced by the back-port patch (`geb-lean`'s linter set is
  currently a subset of `geb-mathlib`'s, so a check present only in
  `geb-lean` is not among the causes today). Both are handled like any
  other refresh failure, through the build-and-issue mechanism, with a
  patch hunk added only where a version difference produces a genuine
  false positive. (`GebMeta`'s `@[env_linter]` is not a concern:
  `GebMeta` is not vendored, so it is never registered in `geb-lean`.)
  The
  spike exercised the in-build linters (`mathlibStandardSet` under
  `warningAsError`, which the current set passes) but not the separate
  `runLinter` pass, so this is an expectation confirmed on first
  refresh, not yet spiked.
- Ordinary push CI (`lake build` / `lake test` on the default `GebLean`
  targets) builds only the vendored modules `geb-lean` imports,
  transitively through the smoke-test import and any consumer. The
  refresh workflow additionally builds and lints the whole vendored
  library (`lake build Geb`, `lake lint Geb`) so a vendored module that
  nothing yet imports cannot rot undetected and the patch stays complete.

### The back-port patch and notes

The refresh adapts the copied source to compile under `v4.29.0-rc6` by
applying a single hand-authored patch
(`scripts/geb-mathlib-backport.patch`), not by running a code-rewriting
rule engine. The patch is generated and regenerated as the `git diff` of
a pristine copy against a manually-adapted copy of the same source
revision, so its paths are rooted at `vendor/geb-mathlib/` and it is
applied with `git apply -p1` from the package root after the copy. It
records the exact edits a person decided on; it makes no decisions
itself. This mirrors how the mathlib-bump workflows this design is
modelled on handle version breakage: they do not rewrite code
automatically, they build and file an issue for a human to resolve.

The patch is paired with a notes document
(`docs/geb-mathlib-backport-notes.md`, a committed Markdown file subject
to the repository's `markdownlint` and `doctoc` rules) describing each
category of change the patch makes; each entry pairs a description of the
change with its rationale — the upstream cause and the `v4.29.0-rc6`
build symptom it produces. When a refresh fails, the notes let a
reviewer recognise whether the failure is an instance of a known
category (extend the corresponding hunk) or something genuinely new (a
fresh decision, and a new category). Both artefacts are versioned in
`geb-lean` and evolve as `geb-mathlib` develops: a refresh that requires
adaptation updates the patch, and the notes when a new category appears.

The edits the patch currently encodes, established by the build spike
below, fall into three categories:

- The vendored `Geb` index imports `GebMeta`, which is not vendored; the
  `import GebMeta` line is removed so the namespace builds without it.
- v4.32-only linter configuration absent in `v4.29.0-rc6`: the
  `set_option linter.checkUnivs false in` lines and the
  `@[nolint checkUnivs]` attributes are removed, because the
  `linter.checkUnivs` option does not exist in `v4.29.0-rc6`.
- The pre-versus-post-`HasForget` `ConcreteCategory` redesign in
  `Slice.Functor`: the `ConcreteCategory.hom` accessor is dropped (in
  `v4.29.0-rc6` an `Over` base map, a morphism in `Type`, is already a
  function, so the wrapper is the identity), the one `over_hom_comp`
  proof is rewritten to reach the commuting condition directly from
  `Over.w` (the `ConcreteCategory.comp_apply` lemma is absent), and the
  docstring naming the removed accessor is updated to match.

A patch is the right granularity because it fails loudly and locally:
`git apply` rejects when an upstream change has altered the context of a
patched region (a pure line-offset move still applies), and a clean
apply followed by a build failure is an
equally explicit signal. Either way the refresh stops and a human
decides how to adapt — the design never silently rewrites vendored code
or papers over a break. This also covers the maintenance boundary
directly: when a curated module comes to depend on a mathlib definition
absent in `v4.29.0-rc6` (a genuinely new result, not a rename), no patch
hunk can supply it; the build fails, an issue is filed, and the
resolution is one of those named under Risks.

### Refresh script

A script performs the refresh deterministically:

1. Clone `geb-mathlib` at the latest `main` (or a pinned revision when
   one is supplied).
2. Remove the existing vendored directory entirely and copy
   `geb-mathlib`'s `Geb` namespace (the top-level `Geb.lean` index and
   the `Geb/` tree, per Vendored scope) fresh, so files removed upstream
   do not persist. A maintained exclusion list may drop modules that
   cannot be back-ported (see Vendored scope).
3. Record the source revision (commit hash) and the patch version (the
   commit hash of the patch and notes) in a provenance file under the
   vendored directory, and copy `geb-mathlib`'s Apache `LICENSE` into
   the vendored directory.
4. Apply the back-port patch with `git apply`. If it does not apply
   cleanly, the refresh stops and the workflow files an issue: a patched
   region has drifted upstream and the patch needs manual re-authoring.

The vendored tree is a pure function of the source revision and the
patch version, both recorded in the provenance file, so it is
reproducible. `git read-tree` / `git subtree`-style subtree-replacement
semantics are the reusable concept this mirrors; the step-2 wipe is the
complete-overwrite guarantee.

### Continuous-integration workflow

The workflow file lives at the parent monorepo level
(`geb/.github/workflows/`), path-scoped to `geb-lean/**`, alongside the
existing `lean_action_ci.yml`; workflow files under
`geb-lean/.github/workflows/` are inert in this monorepo layout. It is
modelled on `geb-mathlib`'s `jj-bump.yml` (not its `update.yml`, whose
`leanprover-community/lean-update` action drives `lake update` of
dependency revisions and would not run a copy-and-patch refresh):

- `on: workflow_dispatch` for on-demand refresh and `on: schedule`
  (cron) for periodic refresh, with a `concurrency` group serialising
  overlapping runs.
- A run guard restricting the job to the `origin` fork (for example, on
  `github.repository_owner`), so the refresh never fires in the
  canonical `upstream` repository and re-introduces the personal-account
  clone there.
- A step running the refresh script, then `lake build Geb`, `lake test`
  (the smoke test), and `lake lint Geb` over the whole vendored library,
  so a build, test, or lint failure all reach the issue path below.
- On success, `peter-evans/create-pull-request` (pinned to a commit SHA
  with a tag comment, per the action-pinning policy) opens a pull
  request with the refreshed vendored tree and provenance file; that
  action's fixed-branch idempotency is what prevents duplicate refresh
  pull requests, not the concurrency group. On failure, the job
  searches for an existing open refresh-failure issue (by a fixed label
  or title) and opens one with `gh issue create` only if none exists,
  recording the failing source revision and the failure output (a patch
  rejection or a build log), so repeated scheduled failures do not
  accumulate duplicate issues.

Pull-request and issue body prose is user-authored and committed
verbatim into the workflow (as `geb-mathlib`'s `jj-bump.yml` body is);
the workflow interpolates only non-prose fields (source revision, run
URL, step outcomes). This satisfies the no-LLM-drafted-user-facing-text
rule. The merge of the resulting pull request is the human gate; the
bot's branch push to `origin` is a distinct automated actor, precedented
by `geb-mathlib`'s `jj-bump.yml`, and does not substitute for the
line-by-line review applied at merge.

### Smoke test

A single module under `GebLeanTests` imports a built vendored module
(for example `import Geb.Mathlib.Data.PFunctor.Slice.Basic`) and states
a trivial `example` or `#check` against an exported declaration. The
spike confirmed that a classic (non-`module`) file imports a
module-system file under `v4.29.0-rc6`, so this `GebLeanTests`-imports-
vendored-`Geb` direction compiles. The smoke test verifies the whole
chain — copy, patch, build, import — in continuous integration. It
hard-codes one module path, so an upstream rename or removal of that
module fails the smoke test until a human updates it; that is an
accepted, visible failure mode. It is replaced by the first genuine
ported import once `geb-lean` exploration consumes curated content
directly.

`geb-lean`'s `scripts/check-axioms.sh` accepts `propext`, `Quot.sound`,
and `Classical.choice`; the vendored `Slice.Functor` module uses `Over`
and so depends on `Classical.choice`, which the axiom check tolerates,
and curated content carries no `sorry`. The vendored built set
therefore passes the axiom check that runs in CI.

### Licensing and provenance

`geb-mathlib` is licensed under Apache 2.0 and its files carry Apache
notices that reference "the file LICENSE"; it has no `NOTICE` file.
Apache 2.0 is one-way compatible with this project's GPLv3 licence
(Apache-2.0 code may be incorporated into a GPLv3 work, not the
reverse), so the vendored files may be included. To satisfy Apache 2.0
section 4:

- The vendored directory carries a verbatim copy of `geb-mathlib`'s
  Apache `LICENSE` (section 4(a)), so the preserved per-file headers do
  not dangle.
- Each vendored file the patch modifies carries a prominent notice that
  it was changed by the back-port patch (section 4(b)); the central
  provenance file additionally records the source revision and patch
  version.

The vendored files remain under Apache 2.0; the combined `geb-lean`
work is GPLv3. This follows the repository's stated discipline for
vendored upstream content in `.claude/rules/lean-coding.md` § "No
copyright or author headers", which requires vendored upstream content
(for example files copied from mathlib or `lean4-skills`) to preserve
its per-file notices verbatim.

## The build spike (evidence)

The patch's edits and the verbatim-compile claims were established by
building `geb-mathlib`'s `Slice.Basic` and `Slice.Functor` modules
inside this repository under its real configuration:
`lake build GebLean.<scratch>.SliceBasic` and `... SliceFunctor`, which
elaborates them as part of the `GebLean` library and therefore inherits
the package `leanOptions` (`autoImplicit = false`,
`relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`,
`maxSynthPendingDepth = 3`) and the hard `-DwarningAsError=true`. Both
modules built clean after the back-port patch's edits; the module system
(`module`, `public import`, `public section`, `@[expose]`), the `↾`
notation (which resolves to `asHom` in `v4.29.0-rc6`), `Functor.toOver`,
the `Over` API, and `≫`/`⋙` compiled with no change. A separate spike
confirmed a classic-`import` file consuming a module-system file builds
under `v4.29.0-rc6`. The spike covered the current built set only;
generalisation to future content is bounded by the build-and-issue
mechanism, not assumed.

## Alternatives considered

### External Lake dependency (git revision or registry)

A `require` on `rokopt/geb-mathlib` by manifest-pinned revision, or via
the Reservoir registry, is the conventional way one Lean project
depends on another. Rejected as the primary mechanism because it cannot
be edited by the consumer and so forces the 45-to-70-hour forward
migration, and because it makes `upstream` builds fetch a
personal-account repository. It is the natural mechanism if and when
`geb-lean` is itself migrated to the shared toolchain, at which point
the vendored copy and its patch are dropped in favour of a direct
`require`. That swap is eased by the byte-identical import paths, and
the spike's classic-imports-module result shows `geb-lean`'s
classic-`import` modules can consume the real module-system
`geb-mathlib` without a separate module-system migration; the residual
forward cost is the `TypeCat`-dominated 45-to-70-hour estimate.

### Compatibility shim instead of a patch

Instead of editing the copied files, a shim module in `geb-lean` could
define the post-redesign names (`ConcreteCategory.hom`,
`ConcreteCategory.comp_apply`) in terms of `v4.29.0-rc6` equivalents,
letting the curated files copy verbatim. The spike showed two limits:
the `linter.checkUnivs` strips (the first patch category) cannot be
shimmed by a declaration, and the `over_hom_comp` edit rewrites a proof
body
depending on an absent lemma rather than a missing name, so a
name-providing shim would not cover it. A shim could shrink the patch
for recurring name-level breaks if they accumulate; the design keeps the
patch as the primary mechanism and treats a shim as an optional
refinement.

## Cross-cutting guarantees

| Consumer | Works | Why |
| --- | --- | --- |
| Local build | yes | Vendored built set compiles under the current toolchain; mathlib oleans come from `lake exe cache get` |
| Third-party clone | yes | Vendored sources are in-tree; no external fetch |
| `origin` continuous integration | yes | Same in-tree sources; refresh workflow is `origin`-scoped, on demand and on schedule |
| `upstream` continuous integration | yes | Hermetic at build time; the refresh workflow is guarded off on `upstream` |

`geb-mathlib` is a public repository, so the refresh workflow's clone
needs no credentials; were it private, the refresh would need a token,
but the in-tree consumption would still be credential-free.

## Documentation touched

- `docs/process.md` section "Relationship to geb-mathlib" currently
  frames consumption as extracting a module to `geb-mathlib` and
  "replacing the local copy with an import", and argues against a
  `Mathlib`-versus-`Internal` sub-tree boundary inside `geb-lean`. This
  design introduces a vendored sub-tree and a copy rather than an
  external import; that section must be revised to reconcile the two,
  and to explain why the `vendor/` sub-tree adds information the earlier
  argument did not contemplate (a toolchain bridge, not a namespace
  split).
- `TODO.md` "to be done in geb-mathlib" entries referenced from that
  section should be checked for consistency with the vendoring flow.
- `CLAUDE.md` Tooling and `docs/lean-resources.md` gain a pointer to
  the vendoring mechanism.
- New artefacts this design adds: the back-port patch (under `scripts/`)
  and its notes document (under `docs/`), both versioned in `geb-lean`
  and evolving as `geb-mathlib` develops.

## Risks and open questions

- The hard wall of back-porting. The patch repairs renamed or removed
  identifiers. When a curated module depends on a mathlib definition or
  theorem that simply does not exist in `v4.29.0-rc6` (a genuinely new
  result, not a rename), no patch hunk and no shim can supply it, and
  `sorry` / `admit` are banned. Back-porting that module
  is then impossible, not merely expensive. Decision rule: such a module
  is dropped from the vendored copy by the refresh script's exclusion
  list until either `geb-lean` is forward-migrated or the consuming
  exploration is deferred. Open question: whether reaching this wall for a module
  `geb-lean` actually wants is the trigger to schedule the forward
  migration.
- Patch-maintenance growth. The gap between `geb-mathlib`'s mathlib and
  `geb-lean`'s widens as `geb-mathlib` bumps, so the patch may accrue
  hunks over time; the build-and-issue mechanism surfaces this, but
  there is no a-priori bound. Open question: how far behind the
  vendored copy may fall before a failing refresh is treated as
  blocking.
- Lean-core syntax. The current vendored library uses no `v4.32`-only
  core syntax. Content that adopts such syntax would need patch hunks
  beyond mathlib-API adaptation, or exclusion from the vendored copy;
  surfaced by the same mechanism.
- Schedule cadence. The cron frequency for the scheduled refresh is a
  tuning parameter, unspecified here.

## References

- mathlib `TypeCat` refactor:
  <https://github.com/leanprover-community/mathlib4/pull/36613> (merged
  2026-04-14); follow-up
  <https://github.com/leanprover-community/mathlib4/pull/38655>;
  `HasForget` removal / `ConcreteCategory` redesign:
  <https://github.com/leanprover-community/mathlib4/pull/34741>.
- Lean release notes:
  <https://lean-lang.org/doc/reference/latest/releases/v4.30.0/>,
  <https://lean-lang.org/doc/reference/latest/releases/v4.31.0/>,
  <https://lean-lang.org/doc/reference/latest/releases/v4.32.0/>.
- `geb-mathlib` dependency-bump workflows: `update.yml`
  (`leanprover-community/lean-update`) and `jj-bump.yml`
  (`peter-evans/create-pull-request`); manifest-only bump pull requests
  <https://github.com/rokopt/geb-mathlib/pull/9>,
  <https://github.com/rokopt/geb-mathlib/pull/18>,
  <https://github.com/rokopt/geb-mathlib/pull/27>,
  <https://github.com/rokopt/geb-mathlib/pull/29>.
- Build spike: the `Geb.Mathlib.Data.PFunctor.Slice.Basic` and
  `.Functor` modules built under `v4.29.0-rc6` after the back-port
  patch, inside the `GebLean` library under its real `leanOptions`.

## Tags

vendoring, dependency management, toolchain, mathlib, continuous
integration, back-port
