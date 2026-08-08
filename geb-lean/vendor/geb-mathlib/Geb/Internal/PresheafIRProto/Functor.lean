/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Internal.PresheafIRProto.Basic
public import Geb.Internal.PresheafIRProto.Codes

/-!
# Prototype: the parts that write in a functor category

Collects what the choice-free core (`PresheafIRProto.Basic`,
`PresheafIRProto.Codes`) cannot state. Writing `⟶` between two objects of a
presheaf category, or `⥤` into one, invokes
`CategoryTheory.Functor.category`, which is `Classical.choice`-dependent, so
every declaration needing either lives here and this module alone is on
`GebMeta.classicalAllowedModules`.

Five things sit here. The p.r.a. formula `T Z ≃ Σ a, Hom(E(a), Z)` with its
hom written as `arityPresheaf F a ⟶ Z`, obtained by transporting the core's
`GebProto.objEquivSigmaArityHom` along the bundling isomorphism
`arityHomEquivNatTrans` — a `CategoryTheory.NatTrans` is its `app` field
together with `naturality`, and `GebProto.ArityHom` is that data unbundled, so
the isomorphism is the identity on both sides and no part of the formula is
re-proved. The two universe-formability demonstrations recording where the
bundled hom is formable. And `BaseArity.functor`, the output-indexed arity
bundled as a functor into the presheaf category, whose two functor laws are
proved here rather than transported.

## Main definitions

* `GebProto.arityHomEquivNatTrans` — the bundling isomorphism between the
  unbundled arity hom and the functor-category hom.
* `GebProto.objEquivSigmaHom` — the p.r.a. formula of [Weber2007] with the
  presheaf hom bundled.
* `GebProto.arityPresheafHomAtUB` / `GebProto.arityPresheafHomULifted` — the
  universes at which the bundled hom is formable.
* `GebProto.BaseArity.functor` — an output-indexed arity as a functor
  `J ⥤ (Iᵒᵖ ⥤ Type uB)`, the output base to discrete fibrations over the
  input base.

## References

* [Weber2007]

## Tags

prototype, presheaf, parametric right adjoint, functor category
-/

@[expose] public section

universe uI uJ uA uB uZ vI vJ

open CategoryTheory

namespace GebProto

section CoproductOfRepresentables

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The bundling isomorphism: an unbundled arity hom is a natural
transformation `E(a) ⟶ Z`. Forward is `natTransOfArityHom`, backward reads off
the components and re-states naturality elementwise; both round trips are
definitional. -/
def arityHomEquivNatTrans (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    (Z : Iᵒᵖ ⥤ Type uB) : ArityHom F a Z ≃ (arityPresheaf F a ⟶ Z) where
  toFun μ := natTransOfArityHom F a μ
  invFun α := ⟨fun i ↦ α.app ⟨i⟩, fun _ _ f b ↦ FunctorToTypes.naturality _ _ α f.op b⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The p.r.a. formula: the domain-restricted interpretation of `F` at `Z` is
the coproduct over shapes of the representables on the arity presheaves. The
core `objEquivSigmaArityHom` transported fibrewise along the bundling
isomorphism. -/
def objEquivSigmaHom (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (Z : Iᵒᵖ ⥤ Type uB) :
    F.toPresheafDomPFunctorData.obj Z ≃ Σ a : F.A, (arityPresheaf F a ⟶ Z) :=
  (objEquivSigmaArityHom F Z).trans
    (Equiv.sigmaCongrRight fun a ↦ arityHomEquivNatTrans F a Z)

/-- At `uZ := uB` the arity presheaf and the input presheaf are objects of one
category, so the hom the p.r.a. formula needs is formable with no transport. -/
def arityPresheafHomAtUB (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    (Z : Iᵒᵖ ⥤ Type uB) : Type (max uI uB) :=
  arityPresheaf F a ⟶ Z

/-- At an unrelated `uZ` the hom is formable after `ULift`ing both sides into
`Type (max uB uZ)`; `max` is commutative on levels, so the two composites are
objects of one category. -/
def arityPresheafHomULifted (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (a : F.A)
    (Z : Iᵒᵖ ⥤ Type uZ) : Type (max uI uB uZ) :=
  (arityPresheaf F a ⋙ uliftFunctor.{uZ, uB}) ⟶ (Z ⋙ uliftFunctor.{uB, uZ})

end CoproductOfRepresentables

/-- A functorial `BaseArity` is a functor from the output base to presheaves on
the input base — equivalently, to discrete fibrations over it. This is the
`δ` rule's arity datum in bundled form: `famPresheaf` is the object part,
`reindexHom` the morphism part, and the remaining two clauses of
`BaseArity.IsFunctorial` are the functor laws.

Kept here rather than in the choice-free core because the target
`Iᵒᵖ ⥤ Type uB` is a functor category, whose `Category` instance is
`Classical.choice`-dependent. -/
def BaseArity.functor {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (P : BaseArity.{uI, uJ, uB, vI, vJ} I J) (hP : P.IsFunctorial) :
    J ⥤ (Iᵒᵖ ⥤ Type uB) where
  obj j := P.famPresheaf hP j
  map g := P.reindexHom hP g
  map_id j := by
    ext i d
    exact congrFun (hP.reindex_id j i.unop) d
  map_comp g h := by
    ext i d
    exact congrFun (hP.reindex_comp h g i.unop) d

end GebProto
