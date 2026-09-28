/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.MType.Depth
public import Geb.Prototypes.MType.Approx
public import Geb.Prototypes.MType.Basic
public import Geb.Prototypes.MType.Equiv
public import Geb.Prototypes.MType.Hereditary
public import Geb.Prototypes.MType.Slice
public import Geb.Prototypes.MType.Presheaf

set_option doc.verso true in
/-!
# M-types constructed from W-types

Index for the modules constructing the M-type of an arbitrary polynomial
functor from W-types: the depths, a W-type; the observations of each depth,
the fibres of a presheaf W-type over the depths; the M-type, the agreeing
root trees of a slice W-type storing one observation at each depth, with its
constructor, destructor and corecursor; its equivalence with mathlib's
M-type; hereditary predicates, the coinductive counterpart of the conjunctive
inductive predicates on W-types; and the M-types of slice and presheaf
polynomial endofunctors, the slice M-type built on the M-type and the presheaf
M-type on the slice M-type, as the W-types are layered, each the terminal
coalgebra of its functor.
-/
