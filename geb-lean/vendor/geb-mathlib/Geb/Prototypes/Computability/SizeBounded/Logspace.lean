/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Basic
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EndSegment
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Rep
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Combinators
public import Geb.Prototypes.Computability.SizeBounded.Logspace.SuffixCounter
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree

set_option doc.verso true in
/-!
# The logspace subalgebra

Index for the modules on \[Kristiansen2005\]'s algebra
{lit}`[I, C_W; comp, simn]` as the successor-free subalgebra of
{name}`Geb.SizeBounded.S`: its expressions, the end-segment lemma, the
interpretation on the logarithmic-space representation of values, and the
machine calculus that interpretation compiles into, with the polynomial time
and logarithmic space bounds of every unary expression's machine; and the
derived expressions, the counters as end segments of the input, the
recognizer of the Elias-length tree encoding written with them, and the
recognizer of the W-trees of a coded signature, specified as a composition of
streaming scans.
-/

set_option doc.verso true
