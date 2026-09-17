/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.CanonicalSExpr

set_option doc.verso true in
/-!
# File I/O for canonical S-expressions

The file operations wrap the parsers and printers of
{name}`Geb.Csexp.parse` and {name}`Geb.Rose.parse`. A read returns {lit}`none` for a
syntax error or a label outside {lit}`Fin k`; filesystem errors remain
{name}`IO.Error` exceptions. The parsers retain their existing acceptance
rules, including their treatment of leading zeros and trailing input.

## Main definitions

* {lit}`Geb.Csexp.readFile`, {lit}`Geb.Csexp.writeFile`: the tagged binary encoding.
* {lit}`Geb.Rose.readFile`, {lit}`Geb.Rose.writeFile`: the canonical rose encoding.
* {lit}`Geb.CSexp.writeFile`: render an ASCII canonical expression.

## Implementation notes

{name}`IO.FS.readBinFile` supplies bytes, each mapped to the character with
that value. Both tree encodings use ASCII, so no Unicode decoding is needed.
{name}`IO.FS.writeFile` writes the ASCII rendering without a trailing newline,
creating or truncating the destination. Reads hold the complete file in memory.
Compose a canonical rose read with {name}`Option.map` {name}`Geb.Ast.ofRose`
to obtain a binary tree, or pass {name}`Geb.Ast.toRose` to the rose writer.

## Tags

canonical S-expression, file I/O, binary tree, rose tree
-/

set_option doc.verso true

public section

namespace Geb.Csexp

/-- Read a tagged canonical binary tree, requiring the parser to consume the whole file. -/
def readFile (k : Nat) (path : System.FilePath) : IO (Option (Ast k)) := do
  return parse k ((← IO.FS.readBinFile path).data.toList.map fun b ↦ Char.ofNat b.toNat)

/-- Write a binary tree in the tagged canonical encoding, without a trailing newline. -/
def writeFile {k : Nat} (path : System.FilePath) (a : Ast k) : IO Unit :=
  IO.FS.writeFile path (String.ofList (print a))

end Geb.Csexp

namespace Geb.CSexp

/-- Write an ASCII expression. Reject non-ASCII characters before opening the output,
since {name}`render` counts characters rather than UTF-8 bytes. -/
def writeFile (path : System.FilePath) (s : CSexp) : IO Unit := do
  let cs := render s
  unless cs.all (fun c ↦ c.toNat < 128) do
    throw <| IO.userError "canonical S-expression output requires ASCII atoms"
  IO.FS.writeFile path (String.ofList cs)

end Geb.CSexp

namespace Geb.Rose

/-- Read a canonical rose expression, leaving conversion by {name}`Ast.ofRose` to the caller. -/
def readFile (k : Nat) (path : System.FilePath) : IO (Option (Rose k)) := do
  return parse k ((← IO.FS.readBinFile path).data.toList.map fun b ↦ Char.ofNat b.toNat)

/-- Write a canonical rose expression, without a trailing newline. -/
def writeFile {k : Nat} (path : System.FilePath) (r : Rose k) : IO Unit :=
  IO.FS.writeFile path (String.ofList (print r))

end Geb.Rose
