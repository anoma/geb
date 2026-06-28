# Axiom-hygiene linter via Lean metaprogramming

Replace the `#print axioms` shell-scripting axiom check
(`scripts/check-axioms.sh`) with a Lean metaprogramming linter built on
`Lean.collectAxioms`, ported and adapted from `geb-mathlib`'s `GebMeta`.
Extend coverage to the vendored `Geb.*` tree.

## Status

Design. Brainstorming phase output. Awaiting user review before the
writing-plans phase.

## Motivation

`scripts/check-axioms.sh` (about 815 lines) audits axiom dependencies by
appending `#print axioms <decl>` lines to each `.lean` file, invoking
`lake env lean`, and parsing the textual output. This approach carries
structural costs documented in the script's own header:

- It mutates source files while running (creates `.axiom_check_backup`
  files, appends a marker block), so an interrupted run can leave a
  modified tree.
- It detects only the first `namespace` in a file and only top-level
  (unindented) declarations; nested namespaces, sections, and indented
  declarations are missed.
- It runs `lake env lean`, which ignores `lakefile.toml` `leanOptions`,
  producing spurious diagnostics that the script must filter with a
  bracket-state-machine output parser and several absorbed-error
  patterns.

`geb-mathlib` audits the same property with an `@[env_linter]` built on
`Lean.collectAxioms` — the same core primitive `#print axioms` uses —
inside the compiler environment. It reads every declaration with full
name resolution, mutates nothing, and parses no text. This design ports
that mechanism to `geb-lean`.

A second motivation, surfaced during brainstorming: the vendored `Geb.*`
tree is patched for compatibility with `geb-lean`'s older mathlib
(`scripts/geb-mathlib-backport.patch`). A patch could introduce an
unintended axiom dependency, which would be as much an error as an
unintended axiom in native `geb-lean` code. The current bash check audits
only `GebLean/` and `GebLeanTests/`, so a patch-introduced axiom in the
vendored tree is invisible. This design closes that gap.

## Goals

- Replace `scripts/check-axioms.sh` with a `collectAxioms`-based linter.
- Preserve the existing policy: `propext`, `Quot.sound`, and
  `Classical.choice` permitted project-wide; `sorryAx` and every other
  non-standard axiom fatal.
- Audit native code (`GebLean.*`, `GebLeanTests.*`) and the vendored
  `Geb.*` tree.
- Audit the vendored tree for axioms only, without subjecting
  upstream-derived code to the full Batteries style-linter set.
- Enforce the check at build time via an explicit
  `lake build GebLeanAxiomChecks` step, run at pre-commit alongside
  `lake test`, at pre-push, and in CI.

## Non-goals

- No per-module or per-declaration axiom allowlist. The dormant
  `-- AXIOM_ALLOW:` comment escape hatch of the bash script is dropped;
  the permitted set is fixed. (User decision, brainstorming phase.) If a
  future need to permit some other non-standard axiom arises, the
  linter source is the single place to revisit.
- No change to `lake lint`'s behavior or `lintDriver`/`lintDriverArgs`
  configuration. Axiom-checking remains a distinct check, separate from
  style linting.
- No full Batteries style-linting of the vendored `Geb.*` tree.
- The native style-lint scope is unchanged: `GebLeanTests.*` is not
  newly subjected to the full style-linter set (it is audited for
  axioms only, as today).

## Design

### The linter (`GebLeanMeta.lean`)

A new top-level `module`-system file `GebLeanMeta.lean`, namespace
`GebLeanMeta`, deliberately outside the `GebLean`, `GebLeanTests`, and
`Geb` namespaces so the linter never audits its own metaprogramming code.

It is a `module`-system file (mirroring `geb-mathlib`'s `GebMeta`)
because the `@[env_linter]` attribute requires its declaration to be
marked `public` and `meta` (module-system keywords). The native tree
contains no `module`-system files, but a legacy file already imports a
`module`-system file in this repository:
`GebLeanTests/Vendor/GebMathlibSmoke.lean` (legacy) imports the vendored
`module` file `Geb.Mathlib.Data.PFunctor.Slice.Basic` and builds today.
So every importer of `GebLeanMeta` — the legacy umbrellas and the
`module`-system vendored `Geb.lean` — resolves.

Definitions (all are adaptations of `geb-mathlib`'s `GebMeta`;
transcription, not novel):

- `permittedAxioms : NameSet` — the fixed set
  `{propext, Quot.sound, Classical.choice}`. (`geb-mathlib` uses a
  per-module allowlist that adds `Classical.choice` only for named
  modules; `geb-lean` permits it project-wide, so the set is a single
  constant and the module-resolution machinery — `moduleOf?`,
  `classicalAllowedModules`, `permittedAxioms (allowed) (mod)` — is
  dropped.)
- `offendingAxioms (used : Array Name) : Array Name` — the elements of
  `used` not in `permittedAxioms`.
- `detectNonstandardAxiom : Linter` — `@[env_linter disabled]`. Its
  `test` calls `collectAxioms declName` and reports the offending axioms,
  if any. Registered `disabled` so it is not part of the default
  `lake lint` set; it runs only where invoked explicitly (see below).

Sketch:

```lean
@[env_linter disabled] def detectNonstandardAxiom : Linter where
  test declName := do
    let bad := offendingAxioms (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on permitted axioms."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true
```

### The build-time gates (`GebLeanAxiomChecks` lib)

A new `lean_lib` `GebLeanAxiomChecks` containing one check file per
audited package. Each check file imports the package and `GebLeanMeta`,
then runs the linter over the package via the `#lint` command:

```lean
import GebLean
import GebLeanMeta
#lint only detectNonstandardAxiom in GebLean
```

`#lint only <linter> in <Pkg>` runs exactly the named linter over
`getDeclsInPackage <Pkg>` — the declarations whose defining module has
`<Pkg>` as a name-prefix. On any finding the `#lint` command elaborator
emits a `logError`, which fails `lake build` of the check file. Three
check files cover the three packages:

- `in GebLean` — native source.
- `in GebLeanTests` — native tests.
- `in Geb` — the vendored tree.

`getDeclsInPackage` filters by name-prefix, and `Geb`, `GebLean`,
`GebLeanTests`, and `GebLeanMeta` are disjoint single components, so each
gate audits exactly its package and nothing else. The vendored gate
audits `Geb.*` for axioms only; no Batteries style linter runs on it.

The check files live in their own `lean_lib`, not in `GebLeanTests`,
because the `GebLeanTests` self-check imports the `GebLeanTests` umbrella
and would form an import cycle if it were itself part of that library.
The library sets `linter.hashCommand = false` (as `GebLeanTests` does),
so the `#lint` `#`-command is not flagged.

### Wiring

| Concern | Change |
| --- | --- |
| linter | new `GebLeanMeta.lean`; `[[lean_lib]] GebLeanMeta` |
| gates | new `GebLeanAxiomChecks` lib (3 package gates + unit test) |
| build | `lake build GebLeanAxiomChecks` in pre-commit, pre-push, CI |
| old script | delete `scripts/check-axioms.sh` |
| smoke test | port `scripts/tests/test-axiom-linter.sh` (see below) |
| CI | replace the `Run axiom check` step and its artifact upload |

`lake lint`, `lintDriver`, `defaultTargets`, `testDriver`, the vendored
`Geb.lean`, and `scripts/geb-mathlib-backport.patch` are unchanged.

### Smoke test

Port `geb-mathlib`'s `scripts/tests/test-axiom-linter.sh`, which stages
throwaway fixtures (nothing axiom-violating is committed) and checks the
linter behaves. One fixture is inverted to reflect `geb-lean`'s looser
policy:

- `Bad.lean` — a theorem proved via a custom `axiom` — linter must
  reject, naming the offending axiom.
- `Good.lean` — a clean theorem — linter must accept.
- `Choice.lean` — a theorem using `Classical.choice` — linter must
  **accept** (`geb-lean` permits `Classical.choice` project-wide;
  `geb-mathlib`'s fixture asserts rejection in a non-allowlisted module).

### Documentation updates

Living docs that reference the bash script or the `AXIOM_ALLOW`
mechanism are updated to describe the linter: `CLAUDE.md`,
`.claude/rules/lean-coding.md`, `.claude/rules/ci-and-workflow.md`,
`docs/geb-mathlib-backport-notes.md`, `docs/lean-resources.md`, and
`TODO.md`. (`docs/process.md` and `README.md` carry no axiom-check or
`AXIOM_ALLOW` text, so they need no edit.) The note that pre-commit
"does not run the axiom check" is corrected: a
`lake build GebLeanAxiomChecks` step is added to pre-commit, so
pre-commit now covers axiom checking. Inert `-- AXIOM_ALLOW:` comments
in five `GebLean/` source files are also removed.

Historical artifacts under `docs/superpowers/specs/`,
`docs/superpowers/plans/`, `docs/plans/`, and `docs/research/` are not
edited (forward-only style rule; document-only-the-persistent rule).

## Components and interfaces

- `GebLeanMeta` (library, one file): the axiom-hygiene linter. Depends on
  `Lean.Util.CollectAxioms` and `Batteries.Tactic.Lint.Basic`. Consumed
  by the check files.
- `GebLeanAxiomChecks` (library): the three package gates (`in GebLean`,
  `in GebLeanTests`, `in Geb`) plus a unit-test file of pure-classifier
  `#guard`s, behind an umbrella. Depends on `GebLean`, `GebLeanTests`,
  `Geb`, and `GebLeanMeta`. A build failure of this library is an
  axiom-hygiene failure.
- `scripts/tests/test-axiom-linter.sh`: validates that the linter rejects
  a custom axiom and accepts `Classical.choice`.

## Testing

- Build `GebLeanAxiomChecks` cleanly on the current tree (no findings).
- `scripts/tests/test-axiom-linter.sh` passes (reject/accept behavior).
- A scratch verification that an injected `sorryAx`/custom axiom in a
  native declaration fails the relevant gate, then revert. (Not
  committed.)

## Risks

- API availability at `lean-toolchain` `v4.29.0-rc6` (`geb-mathlib` is on
  `v4.32.0-rc1`). Verified during brainstorming: `Lean.collectAxioms`,
  the Batteries `Linter` structure, the `@[env_linter]` attribute (and
  its `disabled` form), and the `#lint only <linter> in <pkg>` command
  are all present at `v4.29.0-rc6`.
- `module`/legacy import interop. Verified: the legacy file
  `GebLeanTests/Vendor/GebMathlibSmoke.lean` already imports a vendored
  `module`-system file and builds.
- Coverage holds because each gate audits the declarations present in
  its package umbrella's import closure, which the project's
  one-index-file-per-directory convention (and
  `scripts/refresh-geb-mathlib.sh` for the vendored index) keeps
  complete. A module compiled by globs but omitted from its umbrella
  would escape the gate; umbrella completeness is the invariant that
  matters. (Verified: zero orphans — every `GebLean` module is in
  the umbrella's import closure, and the vendored `Geb.lean` is a
  complete index.)

## References

- `geb-mathlib`: `GebMeta.lean`,
  `GebTests/Internal/AxiomLinter.lean`,
  `scripts/tests/test-axiom-linter.sh` (the ported source).
- `Lean/Util/CollectAxioms.lean` (core Lean) — `collectAxioms`.
- `Batteries/Tactic/Lint/Basic.lean` — the `Linter` interface and the
  `@[env_linter]` attribute.
- `Batteries/Tactic/Lint/Frontend.lean` — `getDeclsInPackage` and the
  `#lint` command.

## Tags

axioms, linter, metaprogramming, tooling, vendoring
