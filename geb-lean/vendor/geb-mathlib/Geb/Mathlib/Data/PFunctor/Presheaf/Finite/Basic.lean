/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
public import Geb.Mathlib.Data.FinEnum

/-!
# Finite presheaf polynomial functors

A presheaf polynomial functor whose shapes, directions, and domain index
category are all finite. Bundles the `FinEnum` evidence that
`PresheafDomPFunctorData.decidableIsNatural`,
`SliceDomPFunctor.decidableCompatible`, `SlicePFunctor.decidableShapeOver`, and
`SliceDomPFunctor.decidableDirectionOver` consume, and provides forwarding
instances that supply the bundled fields to those decision procedures.

## Main definitions

* `FinitePresheafPFunctor` — the bundled structure.
* `FinitePresheafPFunctor.decidableEqA` / `decidableEqI` / `decidableEqJ`
  — `DecidableEq` derived from the `FinEnum` fields.
* `FinitePresheafPFunctor.decidableIsNatural` / `decidableCompatible` /
  `decidableShapeOver` / `decidableDirectionOver` — forwarding instances
  for the general tier.

## Implementation notes

The finiteness evidence is bundled as structure fields rather than taken as
instance arguments because the fields' types (`FinEnum I`, `DecidableEq I`)
mention nothing from which instance resolution could recover the functor, so
they cannot themselves be instances. The forwarding declarations therefore pass
the fields positionally with `@`. The four forwarding declarations whose
conclusions do mention the functor are `instance`s and resolve normally against
a variable of the structure type; the three `decidableEq*` projections are
`def`s, since a `DecidableEq I` goal offers resolution no way to find the
functor.

`FinEnum` on the shape and direction fibers is deliberately absent: no
consumer needs it, and mathlib's `FinEnum.Subtype.finEnum` depends on
`Classical.choice` (as does `FinEnum.ofNodupList`), so supplying it would
require a bespoke choice-free construction. See `Geb/Mathlib/Data/FinEnum.lean`
for the same consideration applied to bounded quantifiers.

`linter.checkUnivs` is suppressed on the structure for the reason given in
`PresheafPFunctor`'s own declaration: the shape and direction universes `uA`
and `uB` appear only in the result sort, not in any argument.

## Tags

polynomial functor, presheaf, parametric right adjoint, finite, FinEnum,
decidability
-/

public section

open CategoryTheory

universe uI uJ uA uB vI vJ uZ uX

/-- A presheaf polynomial functor whose shapes, directions, and domain index
category are all finite. Bundles the `FinEnum` evidence the decidability
layers consume. -/
@[nolint checkUnivs]
structure FinitePresheafPFunctor (I : Type uI) [Category.{vI} I]
    (J : Type uJ) [Category.{vJ} J] :
    Type (max (uA + 1) (uB + 1) uI uJ vI vJ) where
  /-- The underlying presheaf polynomial functor. -/
  toPresheafPFunctor : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J
  /-- Finitely many objects in the domain category. -/
  finEnumI : FinEnum I
  /-- Finite hom-sets in the domain category. -/
  finEnumHomI : ∀ i i' : I, FinEnum (i' ⟶ i)
  /-- Finitely many objects in the codomain category. -/
  finEnumJ : FinEnum J
  /-- Finitely many shapes. -/
  finEnumA : FinEnum toPresheafPFunctor.A
  /-- Finitely many directions per shape. -/
  finitary : toPresheafPFunctor.toPFunctor.Finitary

namespace FinitePresheafPFunctor

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : FinitePresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)

set_option warn.classDefReducibility false in
/-- Decidable equality on shapes, derived from the `FinEnum` field. -/
@[expose] def decidableEqA : DecidableEq F.toPresheafPFunctor.A :=
  F.finEnumA.decEq

set_option warn.classDefReducibility false in
/-- Decidable equality on domain-category objects, derived from the `FinEnum`
field. -/
@[expose] def decidableEqI : DecidableEq I :=
  F.finEnumI.decEq

set_option warn.classDefReducibility false in
/-- Decidable equality on codomain-category objects, derived from the `FinEnum`
field. -/
@[expose] def decidableEqJ : DecidableEq J :=
  F.finEnumJ.decEq

/-- Naturality of a direction assignment is decidable for a finite
presheaf polynomial functor: forwards to
`PresheafDomPFunctorData.decidableIsNatural` with the bundled
finiteness evidence. -/
instance decidableIsNatural {Z : Iᵒᵖ ⥤ Type uZ} [∀ i : I, DecidableEq (Z.obj ⟨i⟩)]
    (x : F.toPresheafPFunctor.toSliceDomPFunctor.Obj
      (PresheafDomPFunctorData.elemProj Z)) :
    Decidable (F.toPresheafPFunctor.toPresheafDomPFunctorData.IsNatural x) :=
  @PresheafDomPFunctorData.decidableIsNatural I _
    F.toPresheafPFunctor.toPresheafDomPFunctorData Z
    F.finitary F.finEnumI F.finEnumHomI inferInstance x

/-- Compatibility of a direction assignment with a projection is
decidable for a finite presheaf polynomial functor: forwards to
`SliceDomPFunctor.decidableCompatible` with the bundled finiteness
evidence. -/
instance decidableCompatible {X : Type uX} (p : X → I) (a : F.toPresheafPFunctor.A)
    (v : F.toPresheafPFunctor.B a → X) :
    Decidable (F.toPresheafPFunctor.toSliceDomPFunctor.Compatible p a v) :=
  @SliceDomPFunctor.decidableCompatible I
    F.toPresheafPFunctor.toSliceDomPFunctor
    F.finitary F.decidableEqI _ p a v

/-- Whether a shape lies over a given output index is decidable for a
finite presheaf polynomial functor: forwards to
`SlicePFunctor.decidableShapeOver` with the bundled decidable
equality. -/
instance decidableShapeOver (j : J) :
    DecidablePred (F.toPresheafPFunctor.toSlicePFunctor.ShapeOver j) :=
  @SlicePFunctor.decidableShapeOver I J F.toPresheafPFunctor.toSlicePFunctor
    F.decidableEqJ j

/-- Whether a direction lies over a given base index is decidable for a
finite presheaf polynomial functor: forwards to
`SliceDomPFunctor.decidableDirectionOver` with the bundled decidable
equality. -/
instance decidableDirectionOver (a : F.toPresheafPFunctor.A) (i : I) :
    DecidablePred (F.toPresheafPFunctor.toSliceDomPFunctor.DirectionOver a i) :=
  @SliceDomPFunctor.decidableDirectionOver I
    F.toPresheafPFunctor.toSliceDomPFunctor F.decidableEqI a i

end FinitePresheafPFunctor
