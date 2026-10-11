/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeLCCC.Category
public import Geb.Prototypes.FreeLCCC.Examples
public import Geb.Prototypes.FreeLCCC.Syntax
public import Geb.Prototypes.FreeLCCC.Theory

set_option doc.verso true in
/-!
# A syntactic presentation of local cartesian closure

The partial Horn presentation has objects and arrows, finite limits, finite colimits, an NNO,
and dependent products along arbitrary arrows. A slice object is an arrow to its base; dependent
sum is composition, and base change is a pullback built from a product and an equalizer.
The dependent product is specified by evaluation and abstraction with beta and eta equations.
There are no additional generating objects or arrows.

The closed term model is a quotient of rose-tree syntax by derivable equality. The theorem
{name}`Geb.FreeLCCC.existsUnique_interpretation` proves strict initiality among models of the
presentation, in arbitrary universes. Equality of closed term classes is exactly derivable
equality, by {name}`Geb.FreeLCCC.ofTerm_eq_iff`. Interpretation in Lean types is not used to
identify arrows. {name}`Geb.FreeLCCC.syntacticModel` carries an underlying category; the examples
give typed objects and arrows in it.

## Implementation notes

The categorical comparison and coherence theorems are not formalized here. In particular,
the module does not yet package the universal equations as finite-limit, finite-colimit, or
slice-adjunction structures in mathlib, construct a model from each ordinary category with the
requested chosen structure, or prove freeness for functors preserving structure up to
isomorphism. Strict initiality alone does not supply that last assertion.

For toposes, \[ForssellLumsdaineSwan2026\], Proposition 1.22, proves the corresponding
upgrade by giving iso-comma categories chosen structure and applying strict initiality.
Adapting that argument requires proving closure of this particular class of structured
categories under the iso-comma construction, including dependent products and the NNO.

## References

* \[PalmgrenVickers2007\], Theorem 22, for initial models of partial Horn theories.
* \[Seely1984\], Section 2.4, for the slice adjunctions.
* \[ForssellLumsdaineSwan2026\], Proposition 1.22, for the topos coherence argument.

## Tags

syntactic category, locally cartesian closed category, partial Horn logic, initial model
-/

set_option doc.verso true
