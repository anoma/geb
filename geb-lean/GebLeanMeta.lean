module

public meta import Lean.Util.CollectAxioms
public meta import Batteries.Tactic.Lint.Basic

/-!
# Axiom-hygiene linter

`detectNonstandardAxiom` is an `@[env_linter]` (registered `disabled`,
so it is not in the default `lake lint` set) that reports any
declaration depending on an axiom outside the permitted set
`{propext, Quot.sound, Classical.choice}`. It is built on
`Lean.collectAxioms` (core Lean), the same primitive `#print axioms`
uses. The module lives outside the `GebLean`, `GebLeanTests`, and `Geb`
namespaces so the linter does not audit its own metaprogramming code.
The `GebLeanAxiomChecks` library invokes it over each package via
`#lint only detectNonstandardAxiom in <Pkg>`.

`Classical.choice` is permitted project-wide: mathlib is classical from
its foundations, and the project-wide ban on `noncomputable` (enforced
by `lake build` under `-DwarningAsError`) is the independent guarantee
that `Classical.choice` reaches no computational content.

## References

- `Lean/Util/CollectAxioms.lean` (core Lean) — `collectAxioms`.
- `Batteries/Tactic/Lint/Basic.lean` — the `Linter` interface and the
  `@[env_linter]` attribute.
- Adapted from `geb-mathlib`'s `GebMeta.lean` (transcription); the
  per-module `Classical.choice` allowlist is dropped, since `geb-lean`
  permits it project-wide.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace GebLeanMeta

/-- Axioms permitted project-wide: `propext`, `Quot.sound`, and
`Classical.choice`. -/
def permittedAxioms : NameSet :=
  ((({} : NameSet).insert ``propext).insert ``Quot.sound).insert
    ``Classical.choice

/-- The elements of `used` not in `permittedAxioms`. -/
def offendingAxioms (used : Array Name) : Array Name :=
  used.filter (!permittedAxioms.contains ·)

/-- Flags a declaration depending on an axiom outside `permittedAxioms`.
Registered `disabled` so it runs only via explicit
`#lint only detectNonstandardAxiom`. -/
@[env_linter disabled] def detectNonstandardAxiom : Linter where
  test declName := do
    let bad := offendingAxioms (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on permitted axioms."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true

end GebLeanMeta
