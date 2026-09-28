/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Scanner
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Expr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Correct

set_option doc.verso true in
/-!
# The Elias-length tree recognizer in the logspace subalgebra

Index for the modules writing the recognizer of the Elias-length tree
encoding, {lit}`Geb.BitTree.Elias.validBool`, as an expression of
\[Kristiansen2005\]'s algebra {lit}`[I, C_W; comp, simn]`: the streaming
scanner on monotone counters, the expression, its correctness against the
scanner, and its logarithmic-space machine reading.
-/

set_option doc.verso true
