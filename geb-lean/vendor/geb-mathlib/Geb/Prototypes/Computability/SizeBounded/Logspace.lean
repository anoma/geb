/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Basic
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EndSegment
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Rep

set_option doc.verso true in
/-!
# The logspace subalgebra

Index for the modules on \[Kristiansen2005\]'s algebra
{lit}`[I, C_W; comp, simn]` as the successor-free subalgebra of
{name}`Geb.SizeBounded.S`: its expressions, the end-segment lemma, the
interpretation on the logarithmic-space representation of values, and the
machine calculus that interpretation compiles into, with the polynomial time
and logarithmic space bounds of every unary expression's machine.
-/

set_option doc.verso true
