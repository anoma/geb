/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Modules

set_option doc.verso true in
/-!
# Manifests

A manifest records what a host needs in order to read a program: its name, its edition, its sources
in order and its entry points. It is one form of the authoring profile,

```
(program NAME (edition N) (sources PATH…) (entries NAME…))
```

so that it holds comments and the formatter applies to it. In place of {lit}`(sources PATH…)` a
program whose sources are compiled a part at a time writes {lit}`(layers (NAME PATH…)…)`, its
sources being those of its layers in order.

The grammar is as narrow as present programs require: the fields stand in this order, each once,
and nothing else is read. A source is a relative path of ASCII characters without white space,
resolved against the manifest's directory, none of whose components is empty, {lit}`.` or
{lit}`..`, so that a manifest resolves alike wherever the tree holding it lies and neither the
working directory nor a scan of a directory decides what a program holds.

An edition fixes the reader, its rules of resolution included, and the elaborator. The host holds
one edition, {lit}`Geb.Kernel.Manifest.currentEdition`, and rejects a manifest of any other.

## Main definitions

* {lit}`Geb.Kernel.Manifest` — what a manifest records.
* {lit}`Geb.Kernel.Manifest.parse` — the manifest of a text, or what rejects it.
* {lit}`Geb.Kernel.Manifest.read` — the manifest of a file.
* {lit}`Geb.Kernel.Manifest.sourcePaths` — the paths of a manifest's sources.
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

/-- What a manifest records of a program. -/
structure Manifest where
  /-- The name of the program. -/
  name : String
  /-- The program's edition. -/
  edition : Nat
  /-- The program's sources in order, by layer; a program without layers has one, of its name. -/
  layers : List Manifest.Layer
  /-- The definitions applied from outside the program. -/
  entries : List String

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

/-- A layer: its name followed by at least one source. -/
def layerOf (e : SExp) : Except String Layer := do
  match ← atoms "a layer" e.children with
  | n :: s :: ss => return ⟨n, s :: ss⟩
  | _ => throw "a layer is a name followed by its sources"

/-- A program's layers, from its field of sources or of layers. -/
def layersOf (name : String) (e : SExp) : Except String (List Layer) :=
  match e.children with
  | h :: args =>
    if isKw h "sources" then return [⟨name, ← atoms "the sources" args⟩]
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
  | [h, n, ed, src, en] =>
    unless isKw h "program" do throw "the form is not a program"
    let some name := n.label.map String.ofList | throw "the program's name is not an atom"
    let edition ← editionOf ed
    let layers ← layersOf name src
    let entries ← atoms "the entries" (← field "entries" en)
    let m : Manifest := ⟨name, edition, layers, entries⟩
    if m.sources.isEmpty then throw "the program has no sources"
    if let some s := m.sources.find? (!validSource ·) then
      throw s!"the source {s} is not a relative path within the manifest's directory"
    if let some s := firstRepeated m.sources then throw s!"the source {s} is listed twice"
    if let some s := firstRepeated (layers.map (·.name)) then
      throw s!"the layer {s} is listed twice"
    if let some s := firstRepeated entries then throw s!"the entry {s} is listed twice"
    return m
  | _ => throw "a program is (program NAME (edition N) (sources PATH…) (entries NAME…))"

/-- The manifest of a file, read as bytes, one character per byte, raising what rejects it. -/
def read (path : System.FilePath) : IO Manifest := do
  match parse ((← IO.FS.readBinFile path).data.toList.map fun b ↦ Char.ofNat b.toNat) with
  | .ok m => return m
  | .error msg => throw <| IO.userError s!"{path}: {msg}"

/-- A source of a manifest at a path, resolved against the manifest's directory. -/
def resolve (path : System.FilePath) (source : String) : System.FilePath :=
  "/".intercalate ((path.toString.splitOn "/").dropLast ++ [source])

/-- The paths of a manifest's sources, the manifest being at a path. -/
def sourcePaths (path : System.FilePath) (m : Manifest) : List System.FilePath :=
  m.sources.map (resolve path)

/-- That a program with the given definitions defines each of a manifest's entry points. -/
def checkEntries (m : Manifest) (names : List String) : Except String Unit :=
  match m.entries.find? (!names.contains ·) with
  | some e => .error s!"the entry {e} names no definition of the program"
  | none => .ok ()

end Manifest

end Geb.Kernel
