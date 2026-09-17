/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Kristiansen.Basic
public import Geb.Prototypes.Computability.Kristiansen.Suffix
public import Geb.Prototypes.Computability.Kristiansen.Reference

set_option doc.verso true in
/-!
# Kristiansen's word algebra

The constants-and-projections algebra closed under composition and simultaneous
recursion on notation of \[Kristiansen2005\]: its binary-word syntax and
semantics, suffix invariant, logarithmic-size reference representation, and
polynomial-time, linear-space CSLib machine bound. The representation theorem
does not supply a logarithmic-space evaluation machine.
-/

set_option doc.verso true
