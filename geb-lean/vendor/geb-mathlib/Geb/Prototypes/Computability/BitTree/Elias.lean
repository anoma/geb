/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.Tree
public import Geb.Prototypes.Computability.BitTree.Elias.RepresentationSize
public import Geb.Prototypes.Computability.BitTree.Elias.CodeExamples

set_option doc.verso true

/-!
# Elias-length encoding of bitstring trees

Binary tree tags with delta-coded leaf lengths, raw payloads, and verified decoding.
The streaming recognizer has explicit quadratic-time and linear-work-space bounds.
Representation redundancy vanishes as average payload length grows, with a counting
lower bound for every competing lossless representation.
-/
