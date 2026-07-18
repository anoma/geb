/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Sigma.Basic
public import Mathlib.Logic.Function.Basic

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
discrete category. -/
def Hom (X Y : FreeCoprodCompDisc.{u, v} D) : Type u :=
  {h : X.1 → Y.1 // Y.2 ∘ h = X.2}

/-- Rewrite the codomain of a `FreeCoprodCompDisc.Hom` along an
equality of objects. -/
def homOfEq {X Y Y' : FreeCoprodCompDisc.{u, v} D} :
    Y = Y' → Hom D X Y → Hom D X Y'
  | rfl => id

/-- The morphism-map component over an object map between the free
coproduct completions of two (generally different) types. -/
def MapMor.{w} (I : Type v) (O : Type w) (F : Map.{u, v, w} I O) :
    Type (max (u + 1) v) :=
  (X Y : FreeCoprodCompDisc.{u, v} I) → Hom.{u, v} I X Y →
    Hom.{u, w} O (F X) (F Y)

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

end FreeCoprodCompDisc

end CategoryTheory
