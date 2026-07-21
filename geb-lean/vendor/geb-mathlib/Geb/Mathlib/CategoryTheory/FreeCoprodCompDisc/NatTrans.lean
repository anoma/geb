/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc

/-!
# Natural transformations between completion maps

Natural transformations between morphism-mapped object maps of free
coproduct completions (`FreeCoprodCompDisc.Map` paired with
`FreeCoprodCompDisc.MapMor`): the naturality condition, the
transformation space as a subtype, and the vertical structure
(identity, composition, and the category laws). Functor-law
predicates and composite maps support the horizontal structure.

## Main definitions

* `FreeCoprodCompDisc.IsNatTrans`, `FreeCoprodCompDisc.NatTrans` —
  the naturality condition and the transformation space.
* `FreeCoprodCompDisc.NatTrans.id`,
  `FreeCoprodCompDisc.NatTrans.vcomp` — the vertical structure.
* `FreeCoprodCompDisc.PreservesId`,
  `FreeCoprodCompDisc.PreservesComp` — functor-law predicates on a
  morphism map.
* `FreeCoprodCompDisc.mapComp`, `FreeCoprodCompDisc.mapMorComp` —
  the composite of two object maps and of their morphism maps.
* `FreeCoprodCompDisc.NatTrans.whiskerRight`,
  `FreeCoprodCompDisc.NatTrans.whiskerLeft`,
  `FreeCoprodCompDisc.NatTrans.hcomp` — whiskering and horizontal
  composition.
* `FreeCoprodCompDisc.idMap`, `FreeCoprodCompDisc.idMapMor` — the
  identity object map and its morphism-map component.
* `FreeCoprodCompDisc.NatTrans.IsInverse`,
  `FreeCoprodCompDisc.NatTrans.ofIsoFamily`,
  `FreeCoprodCompDisc.NatTrans.invOfIsoFamily` — inverse pairs and
  the conversion of a natural family of isomorphisms.
* `FreeCoprodCompDisc.NatTrans.equivOfInverseTarget`,
  `FreeCoprodCompDisc.NatTrans.equivOfInverseSource`,
  `FreeCoprodCompDisc.NatTrans.congrSource` — transport
  equivalences of transformation spaces.
* `FreeCoprodCompDisc.natCoprodEquiv` — the coproduct
  decomposition of transformation spaces.
* `FreeCoprodCompDisc.copowerHomMap`,
  `FreeCoprodCompDisc.plusMap` (with their morphism maps) and
  `FreeCoprodCompDisc.natCopowerPlusEquiv` — the copower–Yoneda
  adjunction: transformations out of the copowered map correspond
  to transformations into the `plus`-precomposed map (components
  `FreeCoprodCompDisc.natCopowerPlusToFun` and
  `FreeCoprodCompDisc.natCopowerPlusInvFun`).

## Main statements

* `FreeCoprodCompDisc.NatTrans.id_vcomp`,
  `FreeCoprodCompDisc.NatTrans.vcomp_id`,
  `FreeCoprodCompDisc.NatTrans.vcomp_assoc` — the vertical
  category laws.
* `FreeCoprodCompDisc.NatTrans.hcomp_eq_vcomp_whisker`,
  `FreeCoprodCompDisc.NatTrans.hcomp_id`,
  `FreeCoprodCompDisc.NatTrans.hcomp_id_right`,
  `FreeCoprodCompDisc.NatTrans.hcomp_id_left`,
  `FreeCoprodCompDisc.NatTrans.hcomp_vcomp` — the coherence and
  interchange laws of horizontal composition.
* `FreeCoprodCompDisc.NatTrans.whiskerRight_idMap`,
  `FreeCoprodCompDisc.NatTrans.whiskerLeft_idMap` — whiskering by
  the identity object map is the identity operation (with the
  functor-law witnesses `FreeCoprodCompDisc.idMapMor_preservesId`
  and `FreeCoprodCompDisc.idMapMor_preservesComp`).
* `FreeCoprodCompDisc.isNatTrans_invHom`,
  `FreeCoprodCompDisc.NatTrans.ofIsoFamily_isInverse` — naturality
  of the inverse family and the inverse laws of the packaged pair.
* `FreeCoprodCompDisc.natCopowerPlus_invFun_toFun`,
  `FreeCoprodCompDisc.natCopowerPlus_toFun_invFun` — the
  round-trip laws of the adjunction.

## Implementation notes

A transformation is a subtype over a `Prop`-valued naturality
condition, so equality of transformations is `Subtype.ext` plus
`funext`, and the vertical laws are componentwise consequences of
the `FreeCoprodCompDisc.Hom` category laws. Morphism maps carry no
functor laws; the operations that need one take the corresponding
`FreeCoprodCompDisc.PreservesId`/`FreeCoprodCompDisc.PreservesComp`
law as an explicit hypothesis.

## Tags

free coproduct completion, natural transformation, functor category
-/

@[expose] public section

universe u v w x

namespace CategoryTheory

namespace FreeCoprodCompDisc

/-- The naturality condition on a family of componentwise morphisms
between two morphism-mapped object maps. -/
def IsNatTrans.{w'} (I : Type v) (O : Type w') (F G : Map.{u, v, w'} I O)
    (mF : MapMor I O F) (mG : MapMor I O G)
    (η : (X : FreeCoprodCompDisc.{u, v} I) → Hom.{u, w', u} O (F X) (G X)) :
    Prop :=
  ∀ (X Y : FreeCoprodCompDisc.{u, v} I) (h : Hom.{u, v, u} I X Y),
    Hom.comp O (mF X Y h) (η Y) = Hom.comp O (η X) (mG X Y h)

/-- A natural transformation between two morphism-mapped object maps:
a componentwise family of morphisms satisfying the naturality
condition. -/
def NatTrans.{w'} (I : Type v) (O : Type w') (F G : Map.{u, v, w'} I O)
    (mF : MapMor I O F) (mG : MapMor I O G) : Type (max (u + 1) v) :=
  {η : (X : FreeCoprodCompDisc.{u, v} I) → Hom.{u, w', u} O (F X) (G X) //
    IsNatTrans I O F G mF mG η}

variable {I : Type v} {O : Type w} {P : Type x}

/-- The identity natural transformation. -/
def NatTrans.id (F : Map.{u, v, w} I O) (mF : MapMor I O F) :
    NatTrans I O F F mF mF :=
  ⟨fun X ↦ Hom.id O (F X),
    fun X Y h ↦
      (Hom.comp_id O (mF X Y h)).trans (Hom.id_comp O (mF X Y h)).symm⟩

/-- Vertical composition of natural transformations. -/
def NatTrans.vcomp {F G H : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} {mH : MapMor I O H}
    (η : NatTrans I O F G mF mG) (θ : NatTrans I O G H mG mH) :
    NatTrans I O F H mF mH :=
  ⟨fun X ↦ Hom.comp O (η.1 X) (θ.1 X),
    fun X Y h ↦
      (Hom.comp_assoc O (mF X Y h) (η.1 Y) (θ.1 Y)).symm.trans
        ((congrArg (fun t ↦ Hom.comp O t (θ.1 Y)) (η.2 X Y h)).trans
          ((Hom.comp_assoc O (η.1 X) (mG X Y h) (θ.1 Y)).trans
            ((congrArg (Hom.comp O (η.1 X)) (θ.2 X Y h)).trans
              (Hom.comp_assoc O (η.1 X) (θ.1 X) (mH X Y h)).symm)))⟩

/-- Vertical left identity. -/
theorem NatTrans.id_vcomp {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} (η : NatTrans I O F G mF mG) :
    NatTrans.vcomp (NatTrans.id F mF) η = η :=
  Subtype.ext (funext (fun X ↦ Hom.id_comp O (η.1 X)))

/-- Vertical right identity. -/
theorem NatTrans.vcomp_id {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} (η : NatTrans I O F G mF mG) :
    NatTrans.vcomp η (NatTrans.id G mG) = η :=
  Subtype.ext (funext (fun X ↦ Hom.comp_id O (η.1 X)))

/-- Vertical associativity. -/
theorem NatTrans.vcomp_assoc {F G H K : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {mH : MapMor I O H}
    {mK : MapMor I O K} (η : NatTrans I O F G mF mG)
    (θ : NatTrans I O G H mG mH) (ρ : NatTrans I O H K mH mK) :
    NatTrans.vcomp (NatTrans.vcomp η θ) ρ =
      NatTrans.vcomp η (NatTrans.vcomp θ ρ) :=
  Subtype.ext (funext (fun X ↦ Hom.comp_assoc O (η.1 X) (θ.1 X) (ρ.1 X)))

/-- Preservation of identities by a morphism map. -/
def PreservesId (F : Map.{u, v, w} I O) (mF : MapMor I O F) : Prop :=
  ∀ X : FreeCoprodCompDisc.{u, v} I,
    mF X X (Hom.id I X) = Hom.id O (F X)

/-- Preservation of composition by a morphism map. -/
def PreservesComp (F : Map.{u, v, w} I O) (mF : MapMor I O F) : Prop :=
  ∀ (X Y Z : FreeCoprodCompDisc.{u, v} I) (f : Hom I X Y) (g : Hom I Y Z),
    mF X Z (Hom.comp I f g) = Hom.comp O (mF X Y f) (mF Y Z g)

/-- The composite of two object maps. -/
def mapComp (F : Map.{u, v, w} I O) (F' : Map.{u, w, x} O P) :
    Map.{u, v, x} I P :=
  fun X ↦ F' (F X)

/-- The composite of two morphism maps, over the composite object
map. -/
def mapMorComp {F : Map.{u, v, w} I O} {F' : Map.{u, w, x} O P}
    (mF : MapMor I O F) (mF' : MapMor O P F') :
    MapMor I P (mapComp F F') :=
  fun X Y h ↦ mF' (F X) (F Y) (mF X Y h)

/-- Right whiskering: precomposition of a transformation with an
object map (no functor-law hypotheses). -/
def NatTrans.whiskerRight {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'} (F : Map.{u, v, w} I O)
    (mF : MapMor I O F) (θ : NatTrans O P F' G' mF' mG') :
    NatTrans I P (mapComp F F') (mapComp F G')
      (mapMorComp mF mF') (mapMorComp mF mG') :=
  ⟨fun X ↦ θ.1 (F X), fun X Y h ↦ θ.2 (F X) (F Y) (mF X Y h)⟩

/-- Left whiskering: postcomposition of a transformation with an
object map, whose naturality consumes the outer morphism map's
composition-preservation law. -/
def NatTrans.whiskerLeft {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} (η : NatTrans I O F G mF mG)
    (F' : Map.{u, w, x} O P) (mF' : MapMor O P F')
    (hF' : PreservesComp F' mF') :
    NatTrans I P (mapComp F F') (mapComp G F')
      (mapMorComp mF mF') (mapMorComp mG mF') :=
  ⟨fun X ↦ mF' (F X) (G X) (η.1 X),
    fun X Y h ↦
      (hF' (F X) (F Y) (G Y) (mF X Y h) (η.1 Y)).symm.trans
        ((congrArg (mF' (F X) (G Y)) (η.2 X Y h)).trans
          (hF' (F X) (G X) (G Y) (η.1 X) (mG X Y h)))⟩

/-- Horizontal composition of natural transformations, in the
`whiskerLeft`-then-`whiskerRight` orientation. -/
def NatTrans.hcomp {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'}
    (η : NatTrans I O F G mF mG) (θ : NatTrans O P F' G' mF' mG')
    (hF' : PreservesComp F' mF') :
    NatTrans I P (mapComp F F') (mapComp G G')
      (mapMorComp mF mF') (mapMorComp mG mG') :=
  NatTrans.vcomp (NatTrans.whiskerLeft η F' mF' hF')
    (NatTrans.whiskerRight G mG θ)

/-- The two orientations of the horizontal composite agree, by the
second transformation's naturality. -/
theorem NatTrans.hcomp_eq_vcomp_whisker {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'}
    (η : NatTrans I O F G mF mG) (θ : NatTrans O P F' G' mF' mG')
    (hF' : PreservesComp F' mF') (hG' : PreservesComp G' mG') :
    NatTrans.hcomp η θ hF' =
      NatTrans.vcomp (NatTrans.whiskerRight F mF θ)
        (NatTrans.whiskerLeft η G' mG' hG') :=
  Subtype.ext (funext (fun X ↦ θ.2 (F X) (G X) (η.1 X)))

/-- The horizontal composite of identity transformations is the
identity (consuming the outer morphism map's identity-preservation
law). -/
theorem NatTrans.hcomp_id {F : Map.{u, v, w} I O} {mF : MapMor I O F}
    {F' : Map.{u, w, x} O P} {mF' : MapMor O P F'}
    (hF'comp : PreservesComp F' mF') (hF'id : PreservesId F' mF') :
    NatTrans.hcomp (NatTrans.id F mF) (NatTrans.id F' mF') hF'comp =
      NatTrans.id (mapComp F F') (mapMorComp mF mF') :=
  Subtype.ext (funext (fun X ↦
    (congrArg (fun t ↦ Hom.comp P t (Hom.id P (F' (F X))))
        (hF'id (F X))).trans
      (Hom.comp_id P (Hom.id P (F' (F X))))))

/-- Whiskering by an identity-transformation on the right is left
whiskering. -/
theorem NatTrans.hcomp_id_right {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {F' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} (η : NatTrans I O F G mF mG)
    (hF' : PreservesComp F' mF') :
    NatTrans.hcomp η (NatTrans.id F' mF') hF' =
      NatTrans.whiskerLeft η F' mF' hF' :=
  Subtype.ext (funext (fun X ↦ Hom.comp_id P (mF' (F X) (G X) (η.1 X))))

/-- Whiskering by an identity-transformation on the left is right
whiskering. -/
theorem NatTrans.hcomp_id_left {F : Map.{u, v, w} I O}
    {mF : MapMor I O F} {F' G' : Map.{u, w, x} O P}
    {mF' : MapMor O P F'} {mG' : MapMor O P G'}
    (θ : NatTrans O P F' G' mF' mG') (hF'comp : PreservesComp F' mF')
    (hF'id : PreservesId F' mF') :
    NatTrans.hcomp (NatTrans.id F mF) θ hF'comp =
      NatTrans.whiskerRight F mF θ :=
  Subtype.ext (funext (fun X ↦
    (congrArg (fun t ↦ Hom.comp P t (θ.1 (F X))) (hF'id (F X))).trans
      (Hom.id_comp P (θ.1 (F X)))))

/-- The identity object map. -/
def idMap : Map.{u, v, v} I I :=
  fun X ↦ X

/-- The morphism-map component of the identity object map. -/
def idMapMor : MapMor I I (idMap : Map.{u, v, v} I I) :=
  fun _ _ h ↦ h

/-- The identity object map preserves identities. -/
theorem idMapMor_preservesId :
    PreservesId (idMap : Map.{u, v, v} I I) idMapMor :=
  fun _ ↦ rfl

/-- The identity object map preserves composition. -/
theorem idMapMor_preservesComp :
    PreservesComp (idMap : Map.{u, v, v} I I) idMapMor :=
  fun _ _ _ _ _ ↦ rfl

/-- Whiskering a transformation with the identity object map on the
precomposition side is the identity operation. -/
theorem NatTrans.whiskerRight_idMap {F' G' : Map.{u, v, w} I O}
    {mF' : MapMor I O F'} {mG' : MapMor I O G'}
    (θ : NatTrans I O F' G' mF' mG') :
    NatTrans.whiskerRight (idMap : Map.{u, v, v} I I) idMapMor θ = θ :=
  Subtype.ext rfl

/-- Whiskering a transformation with the identity object map on the
postcomposition side is the identity operation. -/
theorem NatTrans.whiskerLeft_idMap {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G}
    (η : NatTrans I O F G mF mG) :
    NatTrans.whiskerLeft η (idMap : Map.{u, w, w} O O) idMapMor
      idMapMor_preservesComp = η :=
  Subtype.ext rfl

/-- The interchange law between horizontal and vertical composition. -/
theorem NatTrans.hcomp_vcomp {F G H : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {mH : MapMor I O H}
    {F' G' H' : Map.{u, w, x} O P} {mF' : MapMor O P F'}
    {mG' : MapMor O P G'} {mH' : MapMor O P H'}
    (η : NatTrans I O F G mF mG) (η' : NatTrans I O G H mG mH)
    (θ : NatTrans O P F' G' mF' mG') (θ' : NatTrans O P G' H' mG' mH')
    (hF' : PreservesComp F' mF') (hG' : PreservesComp G' mG') :
    NatTrans.hcomp (NatTrans.vcomp η η') (NatTrans.vcomp θ θ') hF' =
      NatTrans.vcomp (NatTrans.hcomp η θ hF')
        (NatTrans.hcomp η' θ' hG') :=
  Subtype.ext (funext (fun X ↦
    (congrArg (fun t ↦ Hom.comp P t
        (Hom.comp P (θ.1 (H X)) (θ'.1 (H X))))
      (hF' (F X) (G X) (H X) (η.1 X) (η'.1 X))).trans
    (congrArg (fun t ↦
        Hom.comp P (Hom.comp P (mF' (F X) (G X) (η.1 X)) t)
          (θ'.1 (H X)))
      (θ.2 (G X) (H X) (η'.1 X)))))

/-- Two natural transformations are inverse when their vertical
composites in both orders are identities. -/
def NatTrans.IsInverse {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
    {mG : MapMor I O G} (α : NatTrans I O F G mF mG)
    (β : NatTrans I O G F mG mF) : Prop :=
  NatTrans.vcomp α β = NatTrans.id F mF ∧
    NatTrans.vcomp β α = NatTrans.id G mG

/-- The componentwise inverses of a natural family of isomorphisms
form a natural family. -/
theorem isNatTrans_invHom {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G}
    (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
    (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
    IsNatTrans I O G F mG mF (fun X ↦ Iso.invHom O (iso X)) :=
  fun X Y h ↦
    Subtype.ext (funext (fun b ↦
      (congrArg (fun t ↦ (iso Y).1.symm ((mG X Y h).1 t))
          ((iso X).1.apply_symm_apply b).symm).trans
        ((congrArg (fun t ↦ (iso Y).1.symm t)
            (congrFun (congrArg Subtype.val (hnat X Y h))
              ((iso X).1.symm b)).symm).trans
          ((iso Y).1.symm_apply_apply
            ((mF X Y h).1 ((iso X).1.symm b))))))

/-- Package a natural family of isomorphisms as a natural
transformation. -/
def NatTrans.ofIsoFamily {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G}
    (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
    (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
    NatTrans I O F G mF mG :=
  ⟨fun X ↦ Iso.hom O (iso X), hnat⟩

/-- Package the inverses of a natural family of isomorphisms as a
natural transformation. -/
def NatTrans.invOfIsoFamily {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G}
    (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
    (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
    NatTrans I O G F mG mF :=
  ⟨fun X ↦ Iso.invHom O (iso X), isNatTrans_invHom iso hnat⟩

/-- The two transformations packaged from a natural family of
isomorphisms are inverse. -/
theorem NatTrans.ofIsoFamily_isInverse {F G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G}
    (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
    (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
    NatTrans.IsInverse (NatTrans.ofIsoFamily iso hnat)
      (NatTrans.invOfIsoFamily iso hnat) :=
  ⟨Subtype.ext (funext (fun X ↦ Iso.hom_invHom O (iso X))),
    Subtype.ext (funext (fun X ↦ Iso.invHom_hom O (iso X)))⟩

/-- Postcomposition with one half of an inverse pair is an
equivalence on transformation spaces (target side). -/
def NatTrans.equivOfInverseTarget {F G G' : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mG : MapMor I O G} {mG' : MapMor I O G'}
    (α : NatTrans I O G G' mG mG') (β : NatTrans I O G' G mG' mG)
    (h : NatTrans.IsInverse α β) :
    NatTrans I O F G mF mG ≃ NatTrans I O F G' mF mG' :=
  { toFun := fun η ↦ NatTrans.vcomp η α,
    invFun := fun θ ↦ NatTrans.vcomp θ β,
    left_inv := fun η ↦
      (NatTrans.vcomp_assoc η α β).trans
        ((congrArg (fun t ↦ NatTrans.vcomp η t) h.1).trans
          (NatTrans.vcomp_id η)),
    right_inv := fun θ ↦
      (NatTrans.vcomp_assoc θ β α).trans
        ((congrArg (fun t ↦ NatTrans.vcomp θ t) h.2).trans
          (NatTrans.vcomp_id θ)) }

/-- Precomposition with one half of an inverse pair is an
equivalence on transformation spaces (source side). -/
def NatTrans.equivOfInverseSource {F F' G : Map.{u, v, w} I O}
    {mF : MapMor I O F} {mF' : MapMor I O F'} {mG : MapMor I O G}
    (α : NatTrans I O F' F mF' mF) (β : NatTrans I O F F' mF mF')
    (h : NatTrans.IsInverse α β) :
    NatTrans I O F G mF mG ≃ NatTrans I O F' G mF' mG :=
  { toFun := fun η ↦ NatTrans.vcomp α η,
    invFun := fun θ ↦ NatTrans.vcomp β θ,
    left_inv := fun η ↦
      (NatTrans.vcomp_assoc β α η).symm.trans
        ((congrArg (fun t ↦ NatTrans.vcomp t η) h.2).trans
          (NatTrans.id_vcomp η)),
    right_inv := fun θ ↦
      (NatTrans.vcomp_assoc α β θ).symm.trans
        ((congrArg (fun t ↦ NatTrans.vcomp t θ) h.1).trans
          (NatTrans.id_vcomp θ)) }

/-- Rewrite the source morphism map of a transformation space along an
equality of morphism maps. -/
def NatTrans.congrSource {F G : Map.{u, v, w} I O} {mF mF' : MapMor I O F}
    (e : mF = mF') (mG : MapMor I O G) :
    NatTrans I O F G mF mG ≃ NatTrans I O F G mF' mG :=
  Eq.rec (motive := fun mF'' _ ↦
      NatTrans I O F G mF mG ≃ NatTrans I O F G mF'' mG)
    (Equiv.refl (NatTrans I O F G mF mG)) e

/-- The generic coproduct decomposition of transformation spaces:
transformations out of a pointwise indexed coproduct of object maps
correspond to families of transformations out of the summands. -/
def natCoprodEquiv (A : Type u) (Fa : A → Map.{u, v, w} I O)
    (mFa : (a : A) → MapMor I O (Fa a)) (G : Map.{u, v, w} I O)
    (mG : MapMor I O G) :
    NatTrans I O (fun X ↦ coprod O A (fun a ↦ Fa a X)) G
        (fun X Y h ↦ coprodMor O A A _root_.id (fun a ↦ Fa a X)
          (fun a ↦ Fa a Y) (fun a ↦ mFa a X Y h)) mG ≃
      ((a : A) → NatTrans I O (Fa a) G (mFa a) mG) :=
  { toFun := fun η a ↦
      ⟨fun X ↦ Hom.comp O (coprodInj O A (fun a' ↦ Fa a' X) a) (η.1 X),
        fun X Y h ↦
          congrArg (Hom.comp O (coprodInj O A (fun a' ↦ Fa a' X) a))
            (η.2 X Y h)⟩,
    invFun := fun θ ↦
      ⟨fun X ↦ coprodDesc O A (fun a ↦ Fa a X) (G X) (fun a ↦ (θ a).1 X),
        fun X Y h ↦
          congrArg (coprodDesc O A (fun a ↦ Fa a X) (G Y))
            (funext (fun a ↦ (θ a).2 X Y h))⟩,
    left_inv := fun _ ↦ Subtype.ext (funext (fun _ ↦ Subtype.ext rfl)),
    right_inv := fun _ ↦
      funext (fun _ ↦ Subtype.ext (funext (fun _ ↦ Subtype.ext rfl))) }

/-- The object map `X ↦ Hom(c, X) ⊗ F X`: the copower of the value of
`F` by the hom-set out of `c`. -/
def copowerHomMap (c : FreeCoprodCompDisc.{u, v} I)
    (F : Map.{u, v, w} I O) : Map.{u, v, w} I O :=
  fun X ↦ copower.{u, w, u} O (Hom.{u, v, u} I c X) (F X)

/-- The morphism-map component of `copowerHomMap`. -/
def copowerHomMapMor (c : FreeCoprodCompDisc.{u, v} I)
    {F : Map.{u, v, w} I O} (mF : MapMor I O F) :
    MapMor I O (copowerHomMap c F) :=
  fun X Y h ↦
    coprodMor O (Hom I c X) (Hom I c Y) (fun e ↦ Hom.comp I e h)
      (fun _ ↦ F X) (fun _ ↦ F Y) (fun _ ↦ mF X Y h)

/-- The object map `(c +)`: the binary coproduct with fixed left
object `c`. -/
def plusMap (c : FreeCoprodCompDisc.{u, v} I) : Map.{u, v, v} I I :=
  fun X ↦ plus.{v, u, u} I c X

/-- The morphism-map component of `plusMap`. -/
def plusMapMor (c : FreeCoprodCompDisc.{u, v} I) :
    MapMor I I (plusMap c) :=
  fun _ _ h ↦ coprodPairMor I (Hom.id I c) h

/-- The forward direction of the copower–plus correspondence: from a
transformation out of the copowered map to one into the
`plus`-precomposed map. -/
def natCopowerPlusToFun (c : FreeCoprodCompDisc.{u, v} I)
    {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
    (hFcomp : PreservesComp F mF)
    (η : NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG) :
    NatTrans I O F (mapComp (plusMap c) G) mF
      (mapMorComp (plusMapMor c) mG) :=
  ⟨fun X ↦
    Hom.comp O (mF X (plus I c X) (coprodPairInr I c X))
      (Hom.comp O
        (coprodInj O (Hom I c (plus I c X)) (fun _ ↦ F (plus I c X))
          (coprodPairInl I c X))
        (η.1 (plus I c X))),
    fun X Y h ↦
      Subtype.ext (funext (fun a ↦
        (congrArg
            (fun t ↦ (η.1 (plus I c Y)).1 ⟨coprodPairInl I c Y, t⟩)
            ((congrFun (congrArg Subtype.val
                  (hFcomp X Y (plus I c Y) h (coprodPairInr I c Y)))
                a).symm.trans
              (congrFun (congrArg Subtype.val
                  (hFcomp X (plus I c X) (plus I c Y)
                    (coprodPairInr I c X)
                    (coprodPairMor I (Hom.id I c) h)))
                a))).trans
          (congrFun (congrArg Subtype.val
              (η.2 (plus I c X) (plus I c Y)
                (coprodPairMor I (Hom.id I c) h)))
            ⟨coprodPairInl I c X,
              (mF X (plus I c X) (coprodPairInr I c X)).1 a⟩)))⟩

/-- The backward direction of the copower–plus correspondence: from a
transformation into the `plus`-precomposed map to one out of the
copowered map. -/
def natCopowerPlusInvFun (c : FreeCoprodCompDisc.{u, v} I)
    {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
    (hGcomp : PreservesComp G mG)
    (θ : NatTrans I O F (mapComp (plusMap c) G) mF
      (mapMorComp (plusMapMor c) mG)) :
    NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG :=
  ⟨fun X ↦
    coprodDesc O (Hom I c X) (fun _ ↦ F X) (G X)
      (fun e ↦
        Hom.comp O (θ.1 X)
          (mG (plus I c X) X (coprodPairDesc I e (Hom.id I X)))),
    fun X Y h ↦
      Subtype.ext (funext (fun p ↦
        (congrArg
            (fun t ↦ (mG (plus I c Y) Y
                (coprodPairDesc I (Hom.comp I p.1 h) (Hom.id I Y))).1 t)
            (congrFun (congrArg Subtype.val (θ.2 X Y h)) p.2)).trans
          ((congrFun (congrArg Subtype.val
                (hGcomp (plus I c X) (plus I c Y) Y
                  (coprodPairMor I (Hom.id I c) h)
                  (coprodPairDesc I (Hom.comp I p.1 h) (Hom.id I Y))))
              ((θ.1 X).1 p.2)).symm.trans
            ((congrArg
                (fun k ↦ (mG (plus I c X) Y k).1 ((θ.1 X).1 p.2))
                (coprodPairMor_id_desc I h p.1)).trans
              (congrFun (congrArg Subtype.val
                  (hGcomp (plus I c X) X Y
                    (coprodPairDesc I p.1 (Hom.id I X)) h))
                ((θ.1 X).1 p.2))))))⟩

/-- The backward direction inverts the forward direction of the
copower–plus correspondence. -/
theorem natCopowerPlus_invFun_toFun (c : FreeCoprodCompDisc.{u, v} I)
    {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
    (hFid : PreservesId F mF) (hFcomp : PreservesComp F mF)
    (hGcomp : PreservesComp G mG)
    (η : NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG) :
    natCopowerPlusInvFun c hGcomp (natCopowerPlusToFun c hFcomp η) = η :=
  Subtype.ext (funext (fun X ↦ Subtype.ext (funext (fun p ↦
    (congrFun (congrArg Subtype.val
          (η.2 (plus I c X) X (coprodPairDesc I p.1 (Hom.id I X))))
        ⟨coprodPairInl I c X,
          (mF X (plus I c X) (coprodPairInr I c X)).1 p.2⟩).symm.trans
      (congrArg (fun t ↦ (η.1 X).1 ⟨p.1, t⟩)
        ((congrFun (congrArg Subtype.val
              (hFcomp X (plus I c X) X (coprodPairInr I c X)
                (coprodPairDesc I p.1 (Hom.id I X)))) p.2).symm.trans
          (congrFun (congrArg Subtype.val (hFid X)) p.2)))))))

/-- The forward direction inverts the backward direction of the
copower–plus correspondence. -/
theorem natCopowerPlus_toFun_invFun (c : FreeCoprodCompDisc.{u, v} I)
    {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
    (hGid : PreservesId G mG) (hGcomp : PreservesComp G mG)
    (hFcomp : PreservesComp F mF)
    (θ : NatTrans I O F (mapComp (plusMap c) G) mF
      (mapMorComp (plusMapMor c) mG)) :
    natCopowerPlusToFun c hFcomp (natCopowerPlusInvFun c hGcomp θ) = θ :=
  Subtype.ext (funext (fun X ↦ Subtype.ext (funext (fun a ↦
    (congrArg
        (fun t ↦ (mG (plus I c (plus I c X)) (plus I c X)
            (coprodPairDesc I (coprodPairInl I c X)
              (Hom.id I (plus I c X)))).1 t)
        (congrFun (congrArg Subtype.val
            (θ.2 X (plus I c X) (coprodPairInr I c X))) a)).trans
      ((congrFun (congrArg Subtype.val
            (hGcomp (plus I c X) (plus I c (plus I c X)) (plus I c X)
              (coprodPairMor I (Hom.id I c) (coprodPairInr I c X))
              (coprodPairDesc I (coprodPairInl I c X)
                (Hom.id I (plus I c X)))))
          ((θ.1 X).1 a)).symm.trans
        ((congrArg
            (fun k ↦ (mG (plus I c X) (plus I c X) k).1 ((θ.1 X).1 a))
            (coprodPairMor_inr_desc_inl I (Z := c) (X := X))).trans
          (congrFun (congrArg Subtype.val (hGid (plus I c X)))
            ((θ.1 X).1 a))))))))

/-- The copower–Yoneda adjunction: transformations out of the
copowered map correspond to transformations into the
`plus`-precomposed map. -/
def natCopowerPlusEquiv (c : FreeCoprodCompDisc.{u, v} I)
    {F G : Map.{u, v, w} I O} (mF : MapMor I O F) (mG : MapMor I O G)
    (hFid : PreservesId F mF) (hFcomp : PreservesComp F mF)
    (hGid : PreservesId G mG) (hGcomp : PreservesComp G mG) :
    NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG ≃
      NatTrans I O F (mapComp (plusMap c) G) mF
        (mapMorComp (plusMapMor c) mG) :=
  { toFun := natCopowerPlusToFun c hFcomp,
    invFun := natCopowerPlusInvFun c hGcomp,
    left_inv := natCopowerPlus_invFun_toFun c hFid hFcomp hGcomp,
    right_inv := natCopowerPlus_toFun_invFun c hGid hGcomp hFcomp }

end FreeCoprodCompDisc

end CategoryTheory
