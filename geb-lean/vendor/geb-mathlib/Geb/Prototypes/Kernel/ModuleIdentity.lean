/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Identity
public import Geb.Prototypes.Kernel.Modules

set_option doc.verso true in
/-!
# Identities of modules

A module is identified, as a definition is, by the CIDv1 \[RatajBerjon2026\] of its payload
in the canonical encoding \[RFC9804\]: {lit}`(geb-module/v1 (members…) (exports…))`, its
members in order, each a definition by the identifier of its payload or a module nested or
instantiated in it by the module's identifier, and its exports, each by the identifier of the
definition it denotes. The modules of a program form a tree, the root block its root, and the
identifiers are computed from the leaves up. Names are no part of a payload: a module's name and
the names of its exports are annotations, keyed by the module's identifier and an export's
position, so renaming leaves every identifier unchanged, and a change of a definition changes
the identifiers of the modules that contain it, up to the root. Type and numeral abbreviations
are expanded where they are used and have no identifiers of their own.

## Main definitions

* {lit}`moduleCid` — the identifier of a module from those of its members and exports.
* {lit}`moduleCids` — the identifiers of a program's tree of modules.
* {lit}`exportNotes` — the names of modules' exports as annotations.
* {lit}`programModules` — the identifiers of the modules of a program's text.

## References

* \[RatajBerjon2026\] — CIDs.
* \[RFC9804\] — the canonical encoding.

## Tags

content identity, module, CID, Merkle tree
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Identity

open Document

/-- The tag of a module's payload. -/
def moduleTag : List Char :=
  ['g', 'e', 'b', '-', 'm', 'o', 'd', 'u', 'l', 'e', '/', 'v', '1']

/-- A module's payload as an S-expression, from the identifiers of its members and of its
exports. -/
def moduleSExp (members exports : List (List UInt8)) : SExp :=
  RoseTree.node none [atom moduleTag, RoseTree.node none (members.map fun c ↦ atom (charsOf c)),
    RoseTree.node none (exports.map fun c ↦ atom (charsOf c))]

/-- A module's identifier: the CID of its payload in the canonical encoding. -/
def moduleCid (members exports : List (List UInt8)) : List UInt8 :=
  cidOf (bytesOf (canonOf (moduleSExp members exports)))

/-- The identifiers of a program's tree of modules, each after the modules nested in it, from the
identifiers of its definitions by their names in the flat program. -/
def moduleCids (defCid : Ident → Option (List UInt8)) (mods : List ModNode) :
    List (Ident × List UInt8) :=
  mods.foldl (fun acc m ↦
    let members := m.members.flatMap fun
      | .decl fl => (defCid fl).toList
      | .sub p => (acc.lookup p).toList
    acc ++ [(m.path, moduleCid members (m.exports.filterMap fun (_, fl) ↦ defCid fl))]) []

/-- The names of modules' exports as annotations keyed by the module's identifier and the
export's position. -/
def exportNotes (mods : List ModNode) (cids : List (Ident × List UInt8)) :
    List ((List UInt8 × ℕ) × Ident) :=
  mods.flatMap fun m ↦ (m.exports.zipIdx).map fun ((s, _), i) ↦
    (((cids.lookup m.path).getD [], i), s)

/-- The identifiers of the modules of a program's text, by their paths, the root block's path
empty: its modules elaborated, its definitions read and migrated to their payloads. -/
def programModules (text : List Char) : Option (List (Ident × List UInt8)) := do
  let (fs, mods) ← (elabTree (← readSExps text)).toOption
  let ds ← readForms (dropGeneric fs)
  let byName := (ds.map Prod.fst).zip ((migrate (ds.map Prod.snd)).map Payload.cid)
  pure (moduleCids (fun fl ↦ byName.lookup fl) mods)

end Geb.Kernel.Identity

end
