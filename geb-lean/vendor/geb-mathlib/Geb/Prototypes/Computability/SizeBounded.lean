/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Basic
public import Geb.Prototypes.Computability.SizeBounded.Combinators
public import Geb.Prototypes.Computability.SizeBounded.BitTree
public import Geb.Prototypes.Computability.SizeBounded.Cost

set_option doc.verso true

/-!
# The non-size-increasing function algebra

Index for the modules on \[Mazzanti2016\]'s algebra {lit}`S(sbs₀, sbs₁)` over
bitstrings: its syntax and non-size-increase theorem, its expression
combinators, the bit-tree recognizer written in it, and the cost model in
which every expression runs in polynomial time and linear space.
-/
