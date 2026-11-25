/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Durable
public import Geb.Prototypes.Kernel.Modules

set_option doc.verso true in
/-!
# Manifests

A manifest records what a host needs in order to read a program: its name, its edition, the
profile of its sources ({name}`Geb.Kernel.Document.Profile`), its sources in order and its entry
points. It is one form of the authoring profile,

```
(program NAME (edition N) (document …) (sources PATH…) (entries NAME…))
```

so that it holds comments and the formatter applies to it. In place of {lit}`(sources PATH…)` a
program whose sources are compiled a part at a time writes {lit}`(layers (NAME PATH…)…)`.
A layer {lit}`(NAME (manifest PATH))` takes the sources of the named manifest in order as one
layer. Each path is relative to the manifest that names it. The client supplies its own entries.

The grammar is as narrow as present programs require: the fields stand in this order, each once,
and nothing else is read. A source is a relative path of ASCII characters without white space,
resolved against the manifest's directory, none of whose components is empty, {lit}`.` or
{lit}`..`, so that a manifest resolves alike wherever the tree holding it lies and neither the
working directory nor a scan of a directory decides what a program holds.

An edition fixes the reader, its rules of resolution included, and the elaborator. The host holds
one edition, {lit}`Geb.Kernel.Manifest.currentEdition`, and rejects a manifest of any other. The
profile fixes the reading of the sources as documents, their notes included, and the host
rejects a profile it does not read ({name}`Geb.Kernel.Document.Profile.parse`).

## Main definitions

* {lit}`Geb.Kernel.Manifest` — what a manifest records.
* {lit}`Geb.Kernel.Manifest.parse` — the manifest of a text, or what rejects it.
* {lit}`Geb.Kernel.Manifest.read` — the manifest of a file.
* {lit}`Geb.Kernel.Manifest.sourcePaths` — the paths of a manifest's sources.
* {lit}`Geb.Kernel.Manifest.layerPaths` — the paths of the sources of a manifest's layers up to
  one of them.
* {lit}`Geb.Kernel.Manifest.checkEntries` — that a program defines a manifest's entry points.

## Tags

bootstrap, manifest, edition, program
-/

set_option doc.verso true

public section

namespace Geb.Kernel

/-- A part of a program's sources, compiled with the parts before it. -/
structure Manifest.Layer where
  /-- The name of the layer. -/
  name : String
  /-- The layer's sources, relative to the manifest's directory. -/
  sources : List String
  /-- The dependency manifest named in place of an explicit list of sources, if any. -/
  dependency : Option String := none

/-- What a manifest records of a program. -/
structure Manifest where
  /-- The name of the program. -/
  name : String
  /-- The program's edition. -/
  edition : Nat
  /-- The profile of the program's sources. -/
  profile : Document.Profile
  /-- The program's sources in order, by layer; a program without layers has one, of its name. -/
  layers : List Manifest.Layer
  /-- The definitions applied from outside the program. -/
  entries : List String
  /-- The dependency manifests and the sources each lists directly, relative to the root. -/
  dependencies : List (String × List String) := []

namespace Manifest

/-- The edition this host reads: the pre-release edition, whose rules change with the compiler
and whose sources are converted with them, so that it preserves nothing across revisions. -/
def currentEdition : Nat := 0

/-- The sources of a manifest, in order, relative to its directory. -/
def sources (m : Manifest) : List String := m.layers.flatMap (·.sources)

/-- The text of each atom of a list of S-expressions; the name of the list identifies it in the
failure. -/
def atoms (what : String) (es : List SExp) : Except String (List String) :=
  es.mapM fun e ↦ match e.label with
    | some s => .ok (String.ofList s)
    | none => .error s!"{what} holds a list where an atom belongs"

/-- The arguments of a field: a list headed by the atom of its keyword. -/
def field (k : String) (e : SExp) : Except String (List SExp) :=
  match e.children with
  | h :: args => if isKw h k then .ok args else .error s!"the field {k} is expected"
  | [] => .error s!"the field {k} is expected"

/-- Whether a source is a relative path of ASCII characters without white space, none of whose
components is empty, {lit}`.` or {lit}`..`. -/
def validSource (p : String) : Bool :=
  p.toList.all (fun c ↦ c.toNat < 128 && !c.isWhitespace) &&
    (p.splitOn "/").all fun c ↦ c != "" && c != "." && c != ".."

/-- The first element of a list that the list holds more than once. -/
def firstRepeated (xs : List String) : Option String := xs.find? (xs.count · > 1)

/-- A layer names its sources directly or takes them from a dependency manifest. -/
def layerOf (e : SExp) : Except String Layer := do
  if let [n, ref] := e.children then
    if ref.label.isNone then
      let some name := n.label.map String.ofList | throw "a layer's name is not an atom"
      let [path] ← atoms "the manifest field" (← field "manifest" ref)
        | throw "a manifest field holds one path"
      unless validSource path do
        throw s!"the dependency {path} is not a relative path within the manifest's directory"
      return ⟨name, [], some path⟩
  match ← atoms "a layer" e.children with
  | n :: s :: ss => return ⟨n, s :: ss, none⟩
  | _ => throw "a layer is a name followed by its sources"

/-- A program's layers, from its field of sources or of layers. -/
def layersOf (name : String) (e : SExp) : Except String (List Layer) :=
  match e.children with
  | h :: args =>
    if isKw h "sources" then return [⟨name, ← atoms "the sources" args, none⟩]
    else if isKw h "layers" then args.mapM layerOf
    else throw "the field sources or layers is expected"
  | [] => throw "the field sources or layers is expected"

/-- A program's edition, from its field, when this host reads it. -/
def editionOf (e : SExp) : Except String Nat := do
  match ← field "edition" e with
  | [a] =>
    match a.label.bind numeral? with
    | some k =>
      if k == currentEdition then return k
      else throw s!"the edition {k} is not this host's edition {currentEdition}"
    | none => throw "the edition is not a numeral"
  | _ => throw "the field edition holds one numeral"

/-- The manifest of a text in the authoring profile, or what rejects it. -/
def parse (text : List Char) : Except String Manifest := do
  let some [e] := readSExps text | throw "the text is not one well-formed form"
  match e.children with
  | [h, n, ed, doc, src, en] =>
    unless isKw h "program" do throw "the form is not a program"
    let some name := n.label.map String.ofList | throw "the program's name is not an atom"
    let edition ← editionOf ed
    let profile ← Document.Profile.parse doc
    let layers ← layersOf name src
    let entries ← atoms "the entries" (← field "entries" en)
    let m : Manifest := { name, edition, profile, layers, entries }
    if m.sources.isEmpty && layers.all (·.dependency.isNone) then throw "the program has no sources"
    if let some s := m.sources.find? (!validSource ·) then
      throw s!"the source {s} is not a relative path within the manifest's directory"
    if let some s := firstRepeated m.sources then throw s!"the source {s} is listed twice"
    if let some s := firstRepeated (layers.map (·.name)) then
      throw s!"the layer {s} is listed twice"
    if let some s := firstRepeated entries then throw s!"the entry {s} is listed twice"
    return m
  | _ => throw "a program is (program NAME (edition N) (document …) (sources PATH…) \
      (entries NAME…))"

/-- A source of a manifest at a path, resolved against the manifest's directory. -/
def resolve (path : System.FilePath) (source : String) : System.FilePath :=
  "/".intercalate ((path.toString.splitOn "/").dropLast ++ [source])

open scoped FinEnum in
/-- Read the manifests of a program, expanding each dependency in place. The supplied reader
also serves the editor, which reads open manifests from its buffers. The paths retained are
relative to the root even where a dependency is reached through a symbolic link. -/
def read (path : System.FilePath)
    (readBytes : System.FilePath → IO ByteArray := IO.FS.readBinFile) : IO Manifest := do
  let parseFile (p : System.FilePath) := do
    let bytes ← readBytes p
    IO.ofExcept <| (parse (bytes.data.toList.map fun b ↦ Char.ofNat b.toNat)).mapError
      (s!"{p}: {·}")
  let root ← parseFile path
  if root.layers.all (·.dependency.isNone) then return root
  let mut seen := [← IO.FS.realPath path]
  let mut dependencies := #[]
  let mut layers := #[]
  for layer in root.layers do
    let (sources, visited, deps) ← IO.iterate ([("", layer)], #[], seen, dependencies) fun
      (pending, sources, visited, deps) ↦ do
      let (parent, next) :: rest := pending | return .inr (sources, visited, deps)
      let rebase := fun s ↦ (resolve parent s).toString
      if let some ref := next.dependency then
        let relative := rebase ref
        let file := resolve path relative
        let real ← IO.FS.realPath file
        if visited.contains real then
          throw <| IO.userError s!"{path}: repeated or cyclic manifest dependency {relative}"
        let dep ← parseFile file
        unless decide (dep.profile.toSExp = root.profile.toSExp) do
          throw <| IO.userError s!"{path}: the document profile of dependency {relative} differs"
        let own := dep.sources.map fun s ↦ (resolve relative s).toString
        return .inl (dep.layers.map (relative, ·) ++ rest, sources, real :: visited,
          deps.push (relative, own))
      else
        return .inl (rest, sources ++ (next.sources.map rebase).toArray, visited, deps)
    layers := layers.push { layer with sources := sources.toList }
    seen := visited
    dependencies := deps
  let m := { root with layers := layers.toList, dependencies := dependencies.toList }
  if let some s := firstRepeated m.sources then
    throw <| IO.userError s!"{path}: the source {s} is listed twice"
  return m

/-- The paths of a manifest's sources, the manifest being at a path. -/
def sourcePaths (path : System.FilePath) (m : Manifest) : List System.FilePath :=
  m.sources.map (resolve path)

/-- The root manifest, its dependency manifests and all their sources. -/
def documentPaths (path : System.FilePath) (m : Manifest) : List System.FilePath :=
  path :: m.dependencies.map (fun d ↦ resolve path d.1) ++ sourcePaths path m

/-- The qualified names of the modules declared in a form, descending only into module bodies. -/
def moduleNames (form : SExp) : List String :=
  RoseTree.para (β := Ident → List String) (fun _ parts pre ↦ match parts with
    | (kw, _) :: (n, _) :: body =>
      if isKw kw "module" then
        match n.label with
        | some name =>
          let path := qualify pre name
          String.ofList path :: body.flatMap (·.2 path)
        | none => []
      else []
    | _ => []) form []

/-- Check that two dependencies do not declare the same module, even when their exports are
disjoint. A source check can restrict the comparison to the prefix it compiles. -/
def checkModules (path : System.FilePath) (m : Manifest)
    (included : System.FilePath → Bool := fun _ ↦ true)
    (readBytes : System.FilePath → IO ByteArray := IO.FS.readBinFile) : IO Unit := do
  if m.dependencies.length < 2 then return
  let mut owners : List (String × String) := []
  for (dep, files) in m.dependencies do
    for file in files do
      let p := resolve path file
      if included p then
        let text := (← readBytes p).data.toList.map fun b ↦ Char.ofNat b.toNat
        let forms := match Document.readBasic text with
          | some (_, doc) => doc.items.map RoseTree.erase
          | none => (readSExps text).getD []
        for name in forms.flatMap moduleNames do
          if let some other := owners.lookup name then
            if other != dep then
              throw <| IO.userError s!"{path}: the module {name} is declared by {other} and {dep}"
          else
            owners := (name, dep) :: owners

/-- A manifest for compilation, with its dependency modules checked for ambiguity. -/
def readProgram (path : System.FilePath) : IO Manifest := do
  let m ← read path
  checkModules path m
  return m

/-- The paths of the sources of a manifest's layers up to the layer of a name, that layer
included, the manifest being at a path. -/
def layerPaths (path : System.FilePath) (m : Manifest) (name : String) :
    Except String (List System.FilePath) :=
  match m.layers.findIdx? (·.name == name) with
  | some i => .ok (((m.layers.take (i + 1)).flatMap (·.sources)).map (resolve path))
  | none => .error s!"the program has no layer {name}"

/-- That a program with the given definitions defines each of a manifest's entry points. -/
def checkEntries (m : Manifest) (names : List String) : Except String Unit :=
  match m.entries.find? (!names.contains ·) with
  | some e => .error s!"the entry {e} names no definition of the program"
  | none => .ok ()

end Manifest

end Geb.Kernel
