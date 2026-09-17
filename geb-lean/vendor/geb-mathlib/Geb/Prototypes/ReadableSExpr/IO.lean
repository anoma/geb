/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.ReadableSExpr

set_option doc.verso true in
/-!
# File I/O for readable S-expressions

Read and write the readable rose syntax using {name}`Geb.Rsexp.parse` and
{name}`Geb.Rsexp.print`. Syntax errors and labels outside {lit}`Fin k` return
{lit}`none`; filesystem errors remain {name}`IO.Error` exceptions.

## Main definitions

* {lit}`Geb.Rsexp.readFile`: read a readable rose expression.
* {lit}`Geb.Rsexp.writeFile`: write its normalized readable spelling.

## Implementation notes

{name}`IO.FS.readBinFile` supplies bytes, mapped individually to characters.
The grammar uses ASCII labels, delimiters and whitespace; other bytes are
rejected by the parser. Reads hold the complete file in memory.
{name}`IO.FS.writeFile` creates or truncates the output, without adding a newline.
Compose a read with {name}`Option.map` {name}`Geb.Ast.ofRose` to obtain a binary
tree; compose {name}`Geb.Ast.toRose` with the writer to serialize one.

## Tags

readable S-expression, file I/O, binary tree, rose tree
-/

set_option doc.verso true

public section

namespace Geb.Rsexp

/-- Read a readable expression, accepting the parser's leading and trailing whitespace. -/
def readFile (k : Nat) (path : System.FilePath) : IO (Option (Rose k)) := do
  return parse k ((← IO.FS.readBinFile path).data.toList.map fun b ↦ Char.ofNat b.toNat)

/-- Write a readable expression, without a trailing newline. -/
def writeFile {k : Nat} (path : System.FilePath) (r : Rose k) : IO Unit :=
  IO.FS.writeFile path (String.ofList (print r))

end Geb.Rsexp
