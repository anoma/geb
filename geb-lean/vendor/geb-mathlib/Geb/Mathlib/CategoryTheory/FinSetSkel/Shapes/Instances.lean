/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The cartesian and coproduct structure of `FinSetSkel`

The mathlib packaging of the initial and terminal objects, binary
coproducts and binary products built over `Fin` and vectors in
`FinSetSkel.prodObj` and its neighbours, together with the finite
coproducts the initial object and the binary coproducts generate: the
chosen cones and cocones, the `CartesianMonoidalCategory` instance
built from the cones, and the colimit `Prop` instances.
mathlib's cone and cocone API depends on `Classical.choice` —
`CartesianMonoidalCategory` and the empty-diagram (co)cones
independently — so this module is allowlisted and the constructions
it packages are not.

## Main definitions

* `FinSetSkel.terminalCone`, `FinSetSkel.binaryProductCone`,
  `FinSetSkel.initialCocone`, `FinSetSkel.binaryCoproductCocone` —
  the chosen cones and cocones.
* `FinSetSkel.cartesianMonoidalCategory` — the cartesian structure.
* `FinSetSkel.isTerminalOne` — the one-element object is terminal.
* `FinSetSkel.hasInitial`, `FinSetSkel.hasColimit_pair`,
  `FinSetSkel.hasBinaryCoproducts`,
  `FinSetSkel.hasFiniteCoproducts` — the colimit `Prop` instances.

## Implementation notes

`CartesianMonoidalCategory.ofChosenFiniteProducts` takes a terminal
cone and a family of binary product cones and supplies the
associator, the unitors and the coherence conditions, so no
monoidal law is proved here. Its instance registers
`HasFiniteProducts` at priority 100, from which `HasTerminal` and
`HasBinaryProducts` follow, so none of the three is registered
separately.

## References

* [Freyd1972], for the axiomatisation whose terminal object, binary
  products, initial object and binary coproducts are the ones
  supplied here.

## Tags

finite sets, skeleton, cartesian, coproduct, topos
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FinSetSkel

/-- The chosen terminal cone: the one-element object. -/
def terminalCone : LimitCone (Functor.empty.{0} FinSetSkel.{u}) where
  cone := asEmptyCone (mk 1)
  isLimit := IsTerminal.ofUniqueHom (fun X ↦ toOne X) (fun _ f ↦ toOne_uniq f)

/-- The chosen binary product cone. -/
def binaryProductCone (X Y : FinSetSkel.{u}) : LimitCone (pair X Y) where
  cone := BinaryFan.mk (prodFst X Y) (prodSnd X Y)
  isLimit :=
    BinaryFan.IsLimit.mk _ (fun f g ↦ prodLift f g)
      (fun f g ↦ prodLift_fst f g) (fun f g ↦ prodLift_snd f g)
      (fun f g m hf hg ↦ prodLift_uniq f g m hf hg)

/-- The cartesian monoidal structure, from the chosen terminal cone
and the chosen binary product cones. -/
instance cartesianMonoidalCategory :
    CartesianMonoidalCategory FinSetSkel.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone
    binaryProductCone

/-- The one-element object is terminal. -/
def isTerminalOne : IsTerminal (mk 1 : FinSetSkel.{u}) :=
  SemiCartesianMonoidalCategory.isTerminalTensorUnit

/-- The chosen initial cocone: the empty object. -/
def initialCocone : ColimitCocone (Functor.empty.{0} FinSetSkel.{u}) where
  cocone := asEmptyCocone (mk 0)
  isColimit :=
    IsInitial.ofUniqueHom (fun Y ↦ fromZero Y) (fun _ f ↦ fromZero_uniq f)

/-- The chosen binary coproduct cocone. -/
def binaryCoproductCocone (X Y : FinSetSkel.{u}) :
    ColimitCocone (pair X Y) where
  cocone := BinaryCofan.mk (coprodInl X Y) (coprodInr X Y)
  isColimit :=
    BinaryCofan.IsColimit.mk _ (fun f g ↦ coprodDesc f g)
      (fun f g ↦ coprodInl_desc f g) (fun f g ↦ coprodInr_desc f g)
      (fun f g m hl hr ↦ coprodDesc_uniq f g m hl hr)

/-- `FinSetSkel` has an initial object. -/
instance hasInitial : HasInitial FinSetSkel.{u} :=
  IsInitial.hasInitial initialCocone.isColimit

/-- `FinSetSkel` has colimits of pairs. -/
instance hasColimit_pair {X Y : FinSetSkel.{u}} : HasColimit (pair X Y) :=
  ⟨⟨binaryCoproductCocone X Y⟩⟩

/-- `FinSetSkel` has binary coproducts. -/
instance hasBinaryCoproducts : HasBinaryCoproducts FinSetSkel.{u} :=
  hasBinaryCoproducts_of_hasColimit_pair FinSetSkel.{u}

/-- `FinSetSkel` has finite coproducts, from the initial object and
the binary coproducts. -/
instance hasFiniteCoproducts : HasFiniteCoproducts FinSetSkel.{u} :=
  hasFiniteCoproducts_of_has_binary_and_initial

end FinSetSkel
