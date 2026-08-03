/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.ElementaryTopos
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances

/-!
# `FinSetSkel` is an elementary topos

The seven fields of `ElementaryTopos` are the terms the shapes, exponential,
equalizer, coequalizer and classifier modules export, assembled unchanged.
`HasInitial`, `HasBinaryCoproducts`, `HasCoequalizers` and
`HasFiniteCoproducts` are registered directly by the modules supplying the
fields and resolve without this one. `HasEqualizers`, `HasFiniteLimits`,
`HasFiniteColimits` and `HasPushouts` are derived through the class, and
registering the instance is what makes them resolve.

This module is allowlisted for `Classical.choice`, introducing no
dependence of its own and inheriting the whole of it from the seven field
terms.

## Main definitions

* `FinSetSkel.elementaryTopos` — the elementary-topos structure.

## Implementation notes

Nothing beyond the instance is registered. A direct
`HasFiniteColimits FinSetSkel` would be a second resolution route to a
`Prop` the class already derives.

The class carries the coequalizer as data rather than asserting finite
colimits because the choice decides which algorithm runs. That an
elementary topos has finite colimits is a theorem, but the construction a
general proof yields is not `FinSetSkel.Quotient.unionFind`.

## References

* [nLabFinSet], for `FinSet` being an elementary topos.

## Tags

elementary topos, finite set, skeleton, subobject classifier
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FinSetSkel

/-- `FinSetSkel` is an elementary topos. -/
instance elementaryTopos : ElementaryTopos FinSetSkel.{u} where
  cartesian := cartesianMonoidalCategory
  closed := monoidalClosed
  initialCocone := initialCocone
  binaryCoproductCocone := binaryCoproductCocone
  equalizerCone := equalizerCone
  coequalizerCocone := coequalizerCocone
  classifier := classifier

end FinSetSkel
