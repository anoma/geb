/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Sigma.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Function.Basic
public import Geb.Mathlib.Logic.Equiv.Basic

/-!
# The free coproduct completion of a discrete category

`FreeCoprodCompDisc D` is the free coproduct completion of the type
`D` treated as a discrete category: the category `Fam |D|` of families
of elements of `D`, with objects the pairs of an index type `A` and an
assignment `A → D`, and morphisms the index functions commuting with
the assignments. This module provides the objects, morphisms, the
object-map and morphism-map components of functors between
completions, indexed coproducts, and the coproducts' functorial
action, constructively.

## Main definitions

* `FreeCoprodCompDisc` — the objects: index types with `D`-valued
  assignments.
* `FreeCoprodCompDisc.Hom` — the morphisms, with the codomain
  transport `FreeCoprodCompDisc.homOfEq`.
* `FreeCoprodCompDisc.Map`, `FreeCoprodCompDisc.MapMor` — the
  object-map and morphism-map components of functors between the free
  coproduct completions of two (generally different) types.
* `FreeCoprodCompDisc.Endo`, `FreeCoprodCompDisc.EndoMor` — the
  endofunctor specializations `FreeCoprodCompDisc.Map D D` and
  `FreeCoprodCompDisc.MapMor D D`.
* `FreeCoprodCompDisc.coprod`, `FreeCoprodCompDisc.coprodMor` — the
  indexed coproducts and their functorial action.
* `FreeCoprodCompDisc.Hom.id`, `FreeCoprodCompDisc.Hom.comp` — the
  identity and composition of morphisms, composition in diagrammatic
  order.
* `FreeCoprodCompDisc.coprodPair`, `FreeCoprodCompDisc.plus` — the
  binary coproduct (the cotuple object `[i, k]` of
  [HancockMcBrideGhaniMalatestaAltenkirch2013]) and its
  fixed-left-object specialization (the object map `(+i)`), with
  injections `coprodPairInl`/`coprodPairInr` and the universal
  cotuple `coprodPairDesc`.
* `FreeCoprodCompDisc.copower` — the copower `X ⊗ i` (the `X`-fold
  coproduct of `i`, [HancockMcBrideGhaniMalatestaAltenkirch2013],
  Lemma 3), with universal property `copowerEquiv`.
* `FreeCoprodCompDisc.lift` — the `ULift` renaming of an object,
  with universal property `homLiftEquiv`.
* `FreeCoprodCompDisc.Iso` — isomorphism of two objects (a
  name-type equivalence commuting with the decodings), with
  `refl`/`symm`/`trans` and the transport `isoOfEq`; `coprodIso` is
  the congruence of `coprod` along an index equivalence and a
  family of isomorphisms of the summands.
* `FreeCoprodCompDisc.emptyObj`, `FreeCoprodCompDisc.emptyDesc` —
  the initial object and its universal morphism.
* `FreeCoprodCompDisc.coprodInj`, `FreeCoprodCompDisc.coprodDesc`,
  `FreeCoprodCompDisc.coprodHomEquiv` — the injections, the
  cotuple, and the universal property of the indexed coproduct.
* `FreeCoprodCompDisc.coprodPairMor` — the functorial action of
  `FreeCoprodCompDisc.coprodPair` on morphisms.
* `FreeCoprodCompDisc.homSingletonEquiv` — morphisms out of a
  singleton object as the fiber of the decoding over its value.
* `FreeCoprodCompDisc.Iso.hom`, `FreeCoprodCompDisc.Iso.invHom` —
  the underlying morphisms of an isomorphism.

## Main statements

* `FreeCoprodCompDisc.Hom.id_comp`, `FreeCoprodCompDisc.Hom.comp_id`,
  `FreeCoprodCompDisc.Hom.comp_assoc` — the category laws.
* `FreeCoprodCompDisc.coprodMor_id`,
  `FreeCoprodCompDisc.coprodMor_comp` — the functoriality of
  `FreeCoprodCompDisc.coprodMor`.
* `FreeCoprodCompDisc.emptyDesc_unique` — initiality.
* `FreeCoprodCompDisc.coprodInj_desc`,
  `FreeCoprodCompDisc.coprodDesc_eta` — the computation and
  uniqueness laws of the cotuple, with the composition
  compatibilities `FreeCoprodCompDisc.coprodMor_desc`,
  `FreeCoprodCompDisc.coprodDesc_comp`,
  `FreeCoprodCompDisc.coprodInj_mor`.
* `FreeCoprodCompDisc.coprodPairMor_id`,
  `FreeCoprodCompDisc.coprodPairMor_comp` — the functoriality of
  `FreeCoprodCompDisc.coprodPairMor`, with the cotuple
  compatibilities `FreeCoprodCompDisc.coprodPairMor_desc`,
  `FreeCoprodCompDisc.coprodPairMor_id_desc`,
  `FreeCoprodCompDisc.coprodPairMor_inr_desc_inl`.
* `FreeCoprodCompDisc.Iso.hom_invHom`,
  `FreeCoprodCompDisc.Iso.invHom_hom` — the inverse laws of the
  underlying morphisms.

## Implementation notes

For a general category `C`, the family construction `Fam C` is the
total category of the family fibration over `Set` — a Grothendieck
construction — and is the free coproduct completion of `C`
([GhaniNordvallForsbergMalatesta2015], Remarks 2.3). This module
implements the discrete case `C = |D|` directly, without a mathlib
`Category` instance: the categorical packaging (which pulls in
`Classical.choice` through mathlib's category theory) is deferred to a
wrapper module.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

free coproduct completion, family, discrete category, Grothendieck
construction
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable (D : Type v)

/-- The free coproduct completion of `D` treated as a discrete
category. -/
def FreeCoprodCompDisc : Type (max (u + 1) v) :=
  Σ (A : Type u), A → D

namespace FreeCoprodCompDisc

/-- The (object-map components of) functors from the free coproduct
completion of `I` to that of `O` (both treated as discrete
categories). -/
def Map.{w} (I : Type v) (O : Type w) : Type (max (u + 1) v w) :=
  FreeCoprodCompDisc.{u, v} I → FreeCoprodCompDisc.{u, w} O

/-- The (object-map components of) endofunctors on
`FreeCoprodCompDisc`: the specialization
`FreeCoprodCompDisc.Map D D`. -/
def Endo : Type (max (u + 1) v) :=
  Map.{u, v, v} D D

/-- The morphisms of the free coproduct completion of `D` treated as a
discrete category. The two objects may sit at different index
universes. -/
def Hom.{u'} (X : FreeCoprodCompDisc.{u, v} D)
    (Y : FreeCoprodCompDisc.{u', v} D) : Type (max u u') :=
  {h : X.1 → Y.1 // Y.2 ∘ h = X.2}

/-- Rewrite the codomain of a `FreeCoprodCompDisc.Hom` along an
equality of objects. -/
def homOfEq {X Y Y' : FreeCoprodCompDisc.{u, v} D} :
    Y = Y' → Hom D X Y → Hom D X Y'
  | rfl => id

/-- Composition of morphisms of the free coproduct completion, in
diagrammatic order. -/
def Hom.comp {X Y Z : FreeCoprodCompDisc.{u, v} D} (f : Hom D X Y)
    (g : Hom D Y Z) : Hom D X Z :=
  ⟨g.1 ∘ f.1, (congrArg (· ∘ f.1) g.2).trans f.2⟩

/-- The identity morphism of the free coproduct completion. -/
def Hom.id (X : FreeCoprodCompDisc.{u, v} D) : Hom D X X :=
  ⟨_root_.id, rfl⟩

/-- The identity morphism is a left identity for composition. -/
theorem Hom.id_comp {X Y : FreeCoprodCompDisc.{u, v} D} (f : Hom D X Y) :
    Hom.comp D (Hom.id D X) f = f :=
  Subtype.ext rfl

/-- The identity morphism is a right identity for composition. -/
theorem Hom.comp_id {X Y : FreeCoprodCompDisc.{u, v} D} (f : Hom D X Y) :
    Hom.comp D f (Hom.id D Y) = f :=
  Subtype.ext rfl

/-- Composition is associative. -/
theorem Hom.comp_assoc {X Y Z W : FreeCoprodCompDisc.{u, v} D}
    (f : Hom D X Y) (g : Hom D Y Z) (h : Hom D Z W) :
    Hom.comp D (Hom.comp D f g) h = Hom.comp D f (Hom.comp D g h) :=
  Subtype.ext rfl

/-- The morphism-map component over an object map between the free
coproduct completions of two (generally different) types. -/
def MapMor.{w} (I : Type v) (O : Type w) (F : Map.{u, v, w} I O) :
    Type (max (u + 1) v) :=
  (X Y : FreeCoprodCompDisc.{u, v} I) → Hom.{u, v, u} I X Y →
    Hom.{u, w, u} O (F X) (F Y)

/-- The morphism-map component over an object map on
`FreeCoprodCompDisc`: the specialization
`FreeCoprodCompDisc.MapMor D D`. -/
def EndoMor (F : Endo D) : Type (max (u + 1) v) :=
  MapMor.{u, v, v} D D F

/-- The indexed coproduct in the free coproduct completion of `D`
treated as a discrete category. The result lives in the completion at
index universe `max u w`, which is the original completion — making
the result an in-category coproduct — exactly when `w ≤ u`. -/
def coprod.{w} (ι : Type w) (fi : ι → FreeCoprodCompDisc.{u, v} D) :
    FreeCoprodCompDisc.{max u w} D :=
  ⟨(Σ i : ι, (fi i).1), Sigma.uncurry (fun i ↦ (fi i).2)⟩

/-- The functorial action of `FreeCoprodCompDisc.coprod` on morphisms:
a reindexing function together with a componentwise family of
morphisms induces a morphism of indexed coproducts. -/
def coprodMor.{w} (ι κ : Type w) (r : ι → κ)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (gk : κ → FreeCoprodCompDisc.{u, v} D)
    (hom : (i : ι) → Hom D (fi i) (gk (r i))) :
    Hom D (coprod D ι fi) (coprod D κ gk) :=
  ⟨Sigma.map r (fun i ↦ (hom i).1),
    funext (fun p ↦ congrFun (hom p.1).2 p.2)⟩

/-- The functorial action of `coprod` preserves identities. -/
theorem coprodMor_id.{w} (ι : Type w)
    (fi : ι → FreeCoprodCompDisc.{u, v} D) :
    coprodMor D ι ι _root_.id fi fi (fun i ↦ Hom.id D (fi i)) =
      Hom.id D (coprod D ι fi) :=
  Subtype.ext rfl

/-- The functorial action of `coprod` preserves composition. -/
theorem coprodMor_comp.{w} (ι κ ρ : Type w) (r : ι → κ) (t : κ → ρ)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (gk : κ → FreeCoprodCompDisc.{u, v} D)
    (hr : ρ → FreeCoprodCompDisc.{u, v} D)
    (hom₁ : (i : ι) → Hom D (fi i) (gk (r i)))
    (hom₂ : (k : κ) → Hom D (gk k) (hr (t k))) :
    Hom.comp D (coprodMor D ι κ r fi gk hom₁)
        (coprodMor D κ ρ t gk hr hom₂) =
      coprodMor D ι ρ (t ∘ r) fi hr
        (fun i ↦ Hom.comp D (hom₁ i) (hom₂ (r i))) :=
  Subtype.ext rfl

/-- The initial object of the free coproduct completion: the empty
family. -/
def emptyObj : FreeCoprodCompDisc.{u, v} D :=
  ⟨PEmpty, PEmpty.elim⟩

/-- The unique morphism out of the initial object (the nullary
cotuple). -/
def emptyDesc (X : FreeCoprodCompDisc.{u, v} D) : Hom D (emptyObj D) X :=
  ⟨PEmpty.elim, funext (fun a ↦ a.elim)⟩

/-- Uniqueness of the morphism out of the initial object. -/
theorem emptyDesc_unique (X : FreeCoprodCompDisc.{u, v} D)
    (f : Hom D (emptyObj D) X) : f = emptyDesc D X :=
  Subtype.ext (funext (fun a ↦ a.elim))

section

universe w

/-- The injection into the `i`-th summand of an indexed coproduct. -/
def coprodInj (ι : Type w) (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (i : ι) : Hom.{u, v, max u w} D (fi i) (coprod D ι fi) :=
  ⟨fun a ↦ ⟨i, a⟩, rfl⟩

/-- The cotuple: the universal morphism out of an indexed
coproduct. -/
def coprodDesc.{u'} (ι : Type w) (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (Z : FreeCoprodCompDisc.{u', v} D)
    (m : (i : ι) → Hom D (fi i) Z) : Hom D (coprod D ι fi) Z :=
  ⟨fun p ↦ (m p.1).1 p.2, funext (fun p ↦ congrFun (m p.1).2 p.2)⟩

/-- The universal property of the indexed coproduct: morphisms out of
`coprod ι fi` correspond to `ι`-indexed families of morphisms out of
the summands (`copowerEquiv` is the constant-family case). -/
def coprodHomEquiv.{u'} (ι : Type w)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (Z : FreeCoprodCompDisc.{u', v} D) :
    Hom D (coprod D ι fi) Z ≃ ((i : ι) → Hom D (fi i) Z) :=
  { toFun := fun h i ↦
      ⟨fun a ↦ h.1 ⟨i, a⟩, funext (fun a ↦ congrFun h.2 ⟨i, a⟩)⟩,
    invFun := coprodDesc D ι fi Z,
    left_inv := fun _ ↦ Subtype.ext rfl,
    right_inv := fun _ ↦ funext (fun _ ↦ Subtype.ext rfl) }

end

/-- Restricting a cotuple along an injection recovers the
component (at one index universe). -/
theorem coprodInj_desc (ι : Type u)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (Z : FreeCoprodCompDisc.{u, v} D) (m : (i : ι) → Hom D (fi i) Z)
    (i : ι) :
    Hom.comp D (coprodInj D ι fi i) (coprodDesc D ι fi Z m) = m i :=
  Subtype.ext rfl

/-- Every morphism out of an indexed coproduct is the cotuple of its
restrictions (at one index universe). -/
theorem coprodDesc_eta (ι : Type u)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (Z : FreeCoprodCompDisc.{u, v} D)
    (h : Hom D (coprod D ι fi) Z) :
    coprodDesc D ι fi Z
        (fun i ↦ Hom.comp D (coprodInj D ι fi i) h) = h :=
  Subtype.ext rfl

/-- A reindexed coproduct morphism followed by a cotuple is the
cotuple of the reindexed composites. -/
theorem coprodMor_desc (ι κ : Type u) (r : ι → κ)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (gk : κ → FreeCoprodCompDisc.{u, v} D)
    (hom : (i : ι) → Hom D (fi i) (gk (r i)))
    (Z : FreeCoprodCompDisc.{u, v} D)
    (m : (k : κ) → Hom D (gk k) Z) :
    Hom.comp D (coprodMor D ι κ r fi gk hom) (coprodDesc D κ gk Z m) =
      coprodDesc D ι fi Z (fun i ↦ Hom.comp D (hom i) (m (r i))) :=
  Subtype.ext rfl

/-- A cotuple followed by a morphism is the cotuple of the
composites. -/
theorem coprodDesc_comp (ι : Type u)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (Z W : FreeCoprodCompDisc.{u, v} D)
    (m : (i : ι) → Hom D (fi i) Z) (g : Hom D Z W) :
    Hom.comp D (coprodDesc D ι fi Z m) g =
      coprodDesc D ι fi W (fun i ↦ Hom.comp D (m i) g) :=
  Subtype.ext rfl

/-- An injection followed by a reindexed coproduct morphism is the
component followed by the reindexed injection. -/
theorem coprodInj_mor (ι κ : Type u) (r : ι → κ)
    (fi : ι → FreeCoprodCompDisc.{u, v} D)
    (gk : κ → FreeCoprodCompDisc.{u, v} D)
    (hom : (i : ι) → Hom D (fi i) (gk (r i))) (i : ι) :
    Hom.comp D (coprodInj D ι fi i) (coprodMor D ι κ r fi gk hom) =
      Hom.comp D (hom i) (coprodInj D κ gk (r i)) :=
  Subtype.ext rfl

/-- The binary coproduct of two objects of the free coproduct
completion: the sum of the name types, the cotuple of the
decodings — the cotuple object `[i, k]` of
[HancockMcBrideGhaniMalatestaAltenkirch2013] (the discussion
preceding Theorem 2). The two objects may live at different
index universes. -/
def coprodPair.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
    (Y : FreeCoprodCompDisc.{uY, v} D) :
    FreeCoprodCompDisc.{max uX uY, v} D :=
  ⟨X.1 ⊕ Y.1, Sum.elim X.2 Y.2⟩

/-- The object map `(+i)` of [HancockMcBrideGhaniMalatestaAltenkirch2013]
(the discussion preceding Theorem 2): the binary coproduct with a
fixed left object. -/
def plus.{uJ, uK} (i : FreeCoprodCompDisc.{uJ, v} D)
    (k : FreeCoprodCompDisc.{uK, v} D) :
    FreeCoprodCompDisc.{max uJ uK, v} D :=
  coprodPair.{v, uJ, uK} D i k

/-- The left injection into a binary coproduct. The two summands
may sit at different index universes, mirroring `coprodPair`; at
`uX ≠ uY` the result is a heterogeneous `Hom` that cannot be fed to
`Hom.comp`, which pins its source, target, and codomain to a single
universe. -/
def coprodPairInl.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
    (Y : FreeCoprodCompDisc.{uY, v} D) :
    Hom D X (coprodPair.{v, uX, uY} D X Y) :=
  ⟨Sum.inl, rfl⟩

/-- The right injection into a binary coproduct. The two summands
may sit at different index universes, mirroring `coprodPair`; at
`uX ≠ uY` the result is a heterogeneous `Hom` that cannot be fed to
`Hom.comp`, which pins its source, target, and codomain to a single
universe. -/
def coprodPairInr.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
    (Y : FreeCoprodCompDisc.{uY, v} D) :
    Hom D Y (coprodPair.{v, uX, uY} D X Y) :=
  ⟨Sum.inr, rfl⟩

/-- The cotuple: the universal morphism out of a binary
coproduct. -/
def coprodPairDesc {X Y Z : FreeCoprodCompDisc.{u, v} D}
    (f : Hom D X Z) (g : Hom D Y Z) :
    Hom D (coprodPair.{v, u, u} D X Y) Z :=
  ⟨Sum.elim f.1 g.1,
    funext (fun s ↦
      Sum.casesOn s (fun a ↦ congrFun f.2 a) (fun b ↦ congrFun g.2 b))⟩

/-- The cotuple restricted along the left injection is the left
component. -/
theorem coprodPair_inl_desc (X Y Z : FreeCoprodCompDisc.{u, v} D)
    (f : Hom D X Z) (g : Hom D Y Z) :
    Hom.comp D (coprodPairInl D X Y) (coprodPairDesc D f g) = f :=
  Subtype.ext rfl

/-- The cotuple restricted along the right injection is the right
component. -/
theorem coprodPair_inr_desc (X Y Z : FreeCoprodCompDisc.{u, v} D)
    (f : Hom D X Z) (g : Hom D Y Z) :
    Hom.comp D (coprodPairInr D X Y) (coprodPairDesc D f g) = g :=
  Subtype.ext rfl

/-- Every morphism out of a binary coproduct is the cotuple of its
restrictions along the injections (uniqueness half of the
universal property). -/
theorem coprodPairDesc_eta (X Y Z : FreeCoprodCompDisc.{u, v} D)
    (h : Hom D (coprodPair.{v, u, u} D X Y) Z) :
    coprodPairDesc D (Hom.comp D (coprodPairInl D X Y) h)
      (Hom.comp D (coprodPairInr D X Y) h) = h :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- The functorial action of `coprodPair` on morphisms. The four
objects may sit at four different index universes, mirroring
`coprodPair`. -/
def coprodPairMor.{uX, uY, uX', uY'} {X : FreeCoprodCompDisc.{uX, v} D}
    {X' : FreeCoprodCompDisc.{uX', v} D}
    {Y : FreeCoprodCompDisc.{uY, v} D}
    {Y' : FreeCoprodCompDisc.{uY', v} D}
    (f : Hom D X X') (g : Hom D Y Y') :
    Hom D (coprodPair D X Y) (coprodPair D X' Y') :=
  ⟨Sum.map f.1 g.1,
    funext (fun s ↦
      Sum.casesOn s (fun a ↦ congrFun f.2 a) (fun b ↦ congrFun g.2 b))⟩

/-- `coprodPairMor` preserves identities (at one index universe per
side). -/
theorem coprodPairMor_id.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
    (Y : FreeCoprodCompDisc.{uY, v} D) :
    coprodPairMor D (Hom.id D X) (Hom.id D Y) =
      Hom.id D (coprodPair D X Y) :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- `coprodPairMor` preserves composition (at one index universe, where
`Hom.comp` is available). -/
theorem coprodPairMor_comp {X X' X'' Y Y' Y'' : FreeCoprodCompDisc.{u, v} D}
    (f : Hom D X X') (f' : Hom D X' X'') (g : Hom D Y Y')
    (g' : Hom D Y' Y'') :
    coprodPairMor D (Hom.comp D f f') (Hom.comp D g g') =
      Hom.comp D (coprodPairMor D f g) (coprodPairMor D f' g') :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- `coprodPairMor` commutes with the cotuple: reindexing then
descending is descending the composites (left component fixed). -/
theorem coprodPairMor_desc {X Y Y' Z : FreeCoprodCompDisc.{u, v} D}
    (g : Hom D Y Y') (l : Hom D X Z) (m : Hom D Y' Z) :
    Hom.comp D (coprodPairMor D (Hom.id D X) g) (coprodPairDesc D l m) =
      coprodPairDesc D l (Hom.comp D g m) :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- Reindexing the right summand and then cotupling against the
identity is cotupling against the identity and then composing. -/
theorem coprodPairMor_id_desc {Z X Y : FreeCoprodCompDisc.{u, v} D}
    (h : Hom D X Y) (e : Hom D Z X) :
    Hom.comp D (coprodPairMor D (Hom.id D Z) h)
        (coprodPairDesc D (Hom.comp D e h) (Hom.id D Y)) =
      Hom.comp D (coprodPairDesc D e (Hom.id D X)) h :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- Reindexing the right summand along the right injection and then
cotupling the left injection against the identity is the identity. -/
theorem coprodPairMor_inr_desc_inl {Z X : FreeCoprodCompDisc.{u, v} D} :
    Hom.comp D (coprodPairMor D (Hom.id D Z) (coprodPairInr D Z X))
        (coprodPairDesc D (coprodPairInl D Z X)
          (Hom.id D (coprodPair.{v, u, u} D Z X))) =
      Hom.id D (coprodPair.{v, u, u} D Z X) :=
  Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

/-- An isomorphism of two objects of the free coproduct completion of `D`
treated as a discrete category: a name-type equivalence commuting with the
decodings. -/
def Iso.{u₁, u₂} (X : FreeCoprodCompDisc.{u₁, v} D) (Y : FreeCoprodCompDisc.{u₂, v} D) :
    Type (max u₁ u₂) :=
  {e : X.1 ≃ Y.1 // Y.2 ∘ e = X.2}

/-- The identity isomorphism of an object. -/
def Iso.refl (X : FreeCoprodCompDisc.{u, v} D) : Iso D X X :=
  ⟨Equiv.refl X.1, rfl⟩

/-- The inverse of an isomorphism. -/
def Iso.symm.{u₁, u₂} {X : FreeCoprodCompDisc.{u₁, v} D}
    {Y : FreeCoprodCompDisc.{u₂, v} D} (e : Iso D X Y) : Iso D Y X :=
  ⟨e.1.symm, funext (fun y ↦
    (congrFun e.2 (e.1.symm y)).symm.trans (congrArg Y.2 (e.1.apply_symm_apply y)))⟩

/-- The composite of two isomorphisms. -/
def Iso.trans.{u₁, u₂, u₃} {X : FreeCoprodCompDisc.{u₁, v} D}
    {Y : FreeCoprodCompDisc.{u₂, v} D} {Z : FreeCoprodCompDisc.{u₃, v} D}
    (e : Iso D X Y) (f : Iso D Y Z) : Iso D X Z :=
  ⟨e.1.trans f.1, (congrArg (· ∘ ⇑e.1) f.2).trans e.2⟩

/-- Transport an isomorphism along an equality of objects. -/
def isoOfEq {X Y : FreeCoprodCompDisc.{u, v} D} : X = Y → Iso D X Y
  | rfl => Iso.refl D X

/-- The underlying morphism of an isomorphism. -/
def Iso.hom {X Y : FreeCoprodCompDisc.{u, v} D} (e : Iso D X Y) :
    Hom D X Y :=
  ⟨fun a ↦ e.1 a, e.2⟩

/-- The underlying morphism of the inverse of an isomorphism. -/
def Iso.invHom {X Y : FreeCoprodCompDisc.{u, v} D} (e : Iso D X Y) :
    Hom D Y X :=
  ⟨fun b ↦ e.1.symm b, (Iso.symm D e).2⟩

/-- The underlying morphisms of an isomorphism compose to the
identity, forward-then-backward. -/
theorem Iso.hom_invHom {X Y : FreeCoprodCompDisc.{u, v} D}
    (e : Iso D X Y) :
    Hom.comp D (Iso.hom D e) (Iso.invHom D e) = Hom.id D X :=
  Subtype.ext (funext (fun a ↦ e.1.symm_apply_apply a))

/-- The underlying morphisms of an isomorphism compose to the
identity, backward-then-forward. -/
theorem Iso.invHom_hom {X Y : FreeCoprodCompDisc.{u, v} D}
    (e : Iso D X Y) :
    Hom.comp D (Iso.invHom D e) (Iso.hom D e) = Hom.id D Y :=
  Subtype.ext (funext (fun b ↦ e.1.apply_symm_apply b))

/-- The congruence of `FreeCoprodCompDisc.coprod` along an index
equivalence and a family of isomorphisms of the summands. -/
def coprodIso.{u₁, u₂, w₁, w₂} (ι : Type w₁) (κ : Type w₂) (e : ι ≃ κ)
    (fi : ι → FreeCoprodCompDisc.{u₁, v} D)
    (gk : κ → FreeCoprodCompDisc.{u₂, v} D)
    (iso : (i : ι) → Iso D (fi i) (gk (e i))) :
    Iso D (coprod.{u₁, v, w₁} D ι fi) (coprod.{u₂, v, w₂} D κ gk) :=
  ⟨(sigmaCongrRight' (fun i ↦ (iso i).1)).trans
      (Equiv.sigmaCongrLeft (β := fun j ↦ (gk j).1) e),
    funext (fun p ↦ congrFun (iso p.1).2 p.2)⟩

/-- The copower `X ⊗ i`: the `X`-fold coproduct of `i`
([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 3). -/
def copower.{w} (X : Type w) (i : FreeCoprodCompDisc.{u, v} D) :
    FreeCoprodCompDisc.{max u w, v} D :=
  coprod.{u, v, w} D X (fun _ ↦ i)

/-- The universal property of the copower: morphisms out of `X ⊗ i`
correspond to `X`-indexed families of morphisms out of `i`
([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 3). -/
def copowerEquiv.{w} (X : Type w) (i : FreeCoprodCompDisc.{max u w, v} D)
    (Z : FreeCoprodCompDisc.{max u w, v} D) :
    Hom D (copower.{max u w, v, w} D X i) Z ≃ (X → Hom D i Z) :=
  { toFun := fun h x ↦
      ⟨fun a ↦ h.1 ⟨x, a⟩, funext (fun a ↦ congrFun h.2 ⟨x, a⟩)⟩,
    invFun := fun m ↦
      ⟨fun p ↦ (m p.1).1 p.2, funext (fun p ↦ congrFun (m p.1).2 p.2)⟩,
    left_inv := fun _ ↦ Subtype.ext rfl,
    right_inv := fun _ ↦ funext (fun _ ↦ Subtype.ext rfl) }

/-- The `ULift` renaming of an object: the same decodings, through
names raised to a (generally higher) universe. -/
def lift.{w} (X : FreeCoprodCompDisc.{u, v} D) :
    FreeCoprodCompDisc.{max u w, v} D :=
  ⟨ULift.{w} X.1, X.2 ∘ ULift.down⟩

/-- The universal property of `lift`: morphisms out of a lifted
object correspond to morphisms out of the un-lifted object, by
precomposing with `ULift.up`. -/
def homLiftEquiv.{w} (X : FreeCoprodCompDisc.{u, v} D)
    (Y : FreeCoprodCompDisc.{max u w, v} D) :
    Hom D (lift.{u, v, w} D X) Y ≃ Hom D X Y :=
  { toFun := fun f ↦
      ⟨f.1 ∘ ULift.up, funext (fun a ↦ congrFun f.2 (ULift.up a))⟩,
    invFun := fun h ↦
      ⟨h.1 ∘ ULift.down, funext (fun a ↦ congrFun h.2 a.down)⟩,
    left_inv := fun _ ↦ Subtype.ext rfl,
    right_inv := fun _ ↦ Subtype.ext rfl }

/-- Morphisms out of a singleton object are the fiber of the decoding
over its value. -/
def homSingletonEquiv (d : D) (Z : FreeCoprodCompDisc.{u, v} D) :
    Hom D (⟨ULift Unit, fun _ ↦ d⟩ : FreeCoprodCompDisc.{u, v} D) Z ≃
      {z : Z.1 // Z.2 z = d} :=
  { toFun := fun f ↦ ⟨f.1 (ULift.up Unit.unit),
      congrFun f.2 (ULift.up Unit.unit)⟩,
    invFun := fun z ↦ ⟨fun _ ↦ z.1, funext (fun _ ↦ z.2)⟩,
    left_inv := fun _ ↦ Subtype.ext rfl,
    right_inv := fun _ ↦ rfl }

end FreeCoprodCompDisc

end CategoryTheory
