/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.CanonicalSExpr.IO
public import Geb.Prototypes.ReadableSExpr.IO

set_option doc.verso true in
/-!
# S-expression file command

Validate or convert a file through the internal binary tree {name}`Geb.Ast`.

## Main definitions

* {lit}`Geb.Sexpr.readAst`: select a file parser and convert its result to a binary tree.
* {lit}`Geb.Sexpr.writeAst`: select a printer for a binary tree.
* {lit}`Geb.Sexpr.run`: the command-line interface.

## Implementation notes

Run {lit}`lake exe sexpr check FORMAT K INPUT` to validate a file, or
{lit}`lake exe sexpr convert FROM TO K INPUT OUTPUT` to convert it.
Formats are {lit}`canonical` (tagged binary), {lit}`canonical-rose` (canonical rose),
and {lit}`readable`. The natural number {lit}`K` bounds leaf labels: every label
must be strictly smaller. Conversion to the same format normalizes its spelling.
For example, {lit}`lake exe sexpr convert readable canonical 3 input.sexp output.sexp`.

Success is silent and returns exit status zero; errors go to standard error and
return status one. Parsing finishes before the output is opened, so a parse
failure leaves the output untouched and the input and output may be the same path.
Writes create or truncate the destination and are not atomic.

## Tags

S-expression, command line, file I/O, binary tree
-/

set_option doc.verso true

public section

namespace Geb.Sexpr

/-- Read one of the supported encodings, converting rose expressions to binary trees.
Unknown formats raise an {name}`IO.Error`. -/
def readAst (format : String) (k : Nat) (path : System.FilePath) : IO (Option (Ast k)) :=
  match format with
  | "canonical" => Csexp.readFile k path
  | "canonical-rose" => return (← Rose.readFile k path).map Ast.ofRose
  | "readable" => return (← Rsexp.readFile k path).map Ast.ofRose
  | _ => throw <| IO.userError s!"unknown input format: {format}"

/-- Write a binary tree in one of the supported encodings. Unknown formats raise an
{name}`IO.Error` before opening the destination. -/
def writeAst {k : Nat} (format : String) (path : System.FilePath) (a : Ast k) : IO Unit :=
  match format with
  | "canonical" => Csexp.writeFile path a
  | "canonical-rose" => Rose.writeFile path a.toRose
  | "readable" => Rsexp.writeFile path a.toRose
  | _ => throw <| IO.userError s!"unknown output format: {format}"

/-- Validate or convert a file. Errors propagate to Lean's executable runtime, which
reports them on standard error and exits with a nonzero status. -/
def run (args : List String) : IO UInt32 := do
  let (source, bound, input, output) ← match args with
    | ["check", source, bound, input] => pure (source, bound, input, none)
    | ["convert", source, target, bound, input, output] =>
      pure (source, bound, input, some (target, output))
    | _ =>
      throw <| IO.userError
        "usage: sexpr check FORMAT K INPUT | sexpr convert FROM TO K INPUT OUTPUT\n\
        formats: canonical, canonical-rose, readable; labels must be less than K"
  let some k := if bound.isEmpty then none else
      Csexp.digitsVal (bound.toUTF8.data.toList.map fun b ↦ Char.ofNat b.toNat)
    | throw <| IO.userError s!"invalid label bound: {bound}"
  let some a ← readAst source k input
    | throw <| IO.userError s!"{input}: invalid {source} expression for label bound {k}"
  if let some (target, path) := output then
    writeAst target path a
  return 0

end Geb.Sexpr
