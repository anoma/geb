/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Spell
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Positions
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Numeral
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumScan
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumBits
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Sig

set_option doc.verso true in
/-!
# Recognizing the W-trees of a coded signature

Index for the modules that recognize a word as the spelling of an admissible
W-tree of a finitary slice polynomial endofunctor whose shapes are coded by
bitstrings: the spelling of a W-tree as an Elias-length tree of labels and the
tree-level characterization of admissibility; the events of the streaming
scanner and the positions of labels in an encoding; the scan over the nodes
and the scan over one node's children, each the streaming scanner with a
fixed number of further counters; the recognizer composed of them, with its
specification; the two scans and the recognizer as expressions of the
subalgebra, parameterized by the label and edge checks; the machine the
recognizer compiles to; the binary numerals of a shape's numeric fields,
their scanner, and the scanner as expressions; and the comparisons of
numerals, the check of a sum and the reading of a numeral into a counter,
each a lockstep fold over the bits of numerals; and the algebra's own
signature coded, its label and edge checks as expressions, and the
recognizer of the algebra's expressions they yield.
-/

set_option doc.verso true
