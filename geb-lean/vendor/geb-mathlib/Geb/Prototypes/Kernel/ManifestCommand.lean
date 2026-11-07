/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public meta import Geb.Prototypes.Kernel.Manifest
public meta import Lean.Elab.Term

set_option doc.verso true in
/-!
# A program's text at elaboration

The term {lit}`include_manifest "M"` is the text of the program whose manifest is the file
{lit}`M`, its sources joined, each followed by a newline, as the host driver joins them. The path
is relative to the package's directory, in which Lake runs Lean. The file is read as
{lit}`include_str` reads one, so that no dependency on it, or on the sources it names, is
registered: a library reading it lists them in its {lit}`needs`.

## Implementation notes

The term's elaborator runs in Lean's elaboration monads, whose definitions depend on
{lit}`Classical.choice`; the module holds only the elaborator, so that the manifests' reader is
held to the strict axiom set.

## Main definitions

* {lit}`include_manifest` — a program's text, from its manifest.

## Tags

bootstrap, manifest, elaboration
-/

set_option doc.verso true

public section

namespace Geb.Kernel.ManifestCommand

open Lean Elab Term

/-- {lit}`include_manifest "M"` is the text of the program whose manifest is the file {lit}`M`. -/
syntax (name := includeManifest) "include_manifest " str : term

/-- The elaborator of {lit}`include_manifest`. -/
@[term_elab includeManifest] meta def elabIncludeManifest : TermElab := fun stx _ ↦ do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let m ← Manifest.read path
  let texts ← (Manifest.sourcePaths path m).mapM fun p ↦ (IO.FS.readFile p : IO String)
  return mkStrLit (String.join (texts.map (· ++ "\n")))

end Geb.Kernel.ManifestCommand
