/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FinCardUniverse.Basic
public import Geb.Prototypes.PresheafIRProto.Basic

/-!
# Prototype: what the universe functor computes over a non-discrete base

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

`Basic` builds the universe endofunctor over a base of finite sets with all
functions between them as morphisms. This module computes its value on a family
of codes and records what the computation shows.

A family of codes `(U, d : U → Card)` — an object of the free coproduct
completion `Fam(Card)` — becomes the presheaf `famPresheaf U d`, the coproduct
of representables `Σ_u y(d u)`. The p.r.a. formula then reads the functor's
value at that presheaf off the arity homs, and `arityHomEquiv` computes them:
an arity hom for the shape at a code former is a choice, for each
summand `k` of its arity, of a code `u` together with a morphism `bound k ⟶ d u`.

That morphism is where the two presentations part. The inductive-recursive
presentation of the same universe
(`Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean`) works over `Type` treated as
discrete, so its corresponding datum is an equality: the bound code's decoding
*is* the declared object. Over a base with morphisms the equality relaxes to a
coercion, and `junkArity` exhibits a consequence: a binder shape declaring the
empty object accepts a code denoting the singleton. Since a shape's output index
is fixed by the shape (`out_emptyBind`), the code so formed decodes by its
declaration rather than by its children — the recursion of induction-recursion
is decoupled.

The relaxation is not a defect of the encoding but the price of functoriality.
`piFormer_not_covariant` reproduces, at this scale, the obstruction of Example
3.6 of [GhaniNordvallForsbergMalatesta2015]: the dependent-product former admits
no covariant action on the base's morphisms, while `sigmaFormer_covariant` shows
the dependent-sum former does at the same instance. The universe functor of
`Basic` is nonetheless total in the type former — `sigmaUniverse` and
`piUniverse` differ only in the shape-output map — precisely because the
declared decoding it carries is not required to match the decodings of its
children.

## Main definitions

* `famPresheaf` — a family of codes as a presheaf, the coproduct of
  representables `Σ_u y(d u)`.
* `arityHomEquiv` — the arity homs into such a presheaf: one code and one
  coercion per arity summand.
* `oneFam` / `emptyBindCode` / `junkShape` / `junkArity` / `junkObj` — the family
  with one code denoting the singleton, the binder code declaring the empty
  object, and the element of the functor's value that binds the one against the
  other.
* `counterFam` / `counterMap` / `counterFamReindexed` — the data of Example 3.6.

## Main statements

* `junk_decoding_ne` — the bound code's decoding differs from the object the
  shape declares, so the arity hom has no inductive-recursive counterpart.
* `out_emptyBind` — the shape's output object is fixed by the declaration.
* `sigmaFormer_covariant` / `piFormer_not_covariant` — Example 3.6 at this
  scale.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [Weber2007]

## Tags

prototype, inductive-recursive, presheaf, universe, parametric right adjoint,
finite set
-/

@[expose] public section

open CategoryTheory

namespace GebProto.FinCardUniverse

/-! ## Families as presheaves -/

/-- A family of codes as a presheaf: the coproduct of representables
`Σ_u y(d u)`. This is the embedding of the free coproduct completion `Fam(Card)`
into `PSh(Card)`; its fiber over `c` is not the codes decoding to `c` but the
codes admitting a morphism from `c`. -/
def famPresheaf (U : Type) (d : U → Card) : Cardᵒᵖ ⥤ Type where
  obj c := Σ u : U, (c.unop ⟶ d u)
  map f := ↾ fun x ↦ (⟨x.1, f.unop ≫ x.2⟩ : Σ u : U, (_ ⟶ d u))
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## The arity homs -/

/-- The arity homs into a family presheaf: an arity hom for the shape `a` is a
choice, for each arity summand `k`, of a code `u` together with a morphism
`bound k ⟶ d u`. Forward is evaluation at the summands' universal directions and backward is
precomposition, the two round trips being Yoneda.

The morphism is the point of the computation. The inductive-recursive
presentation over a discrete base has an equality `bound k = d u` here; over a
base with morphisms no arity can ask for that, since a direction constrains the
index of the value it receives and the index of a value in a family presheaf is
not its code's decoding. -/
def arityHomEquiv (former : Former) (a : Shp former) (U : Type) (d : U → Card) :
    ArityHom (universeFunctor former) a (famPresheaf U d) ≃
      ((k : Idx a.1) → Σ u : U, (bound a.1 k ⟶ d u)) where
  toFun α k := α.val (bound a.1 k) ⟨⟨k, bound a.1 k, 𝟙 _⟩, rfl⟩
  invFun F :=
    ⟨fun _i b ↦ ⟨(F b.val.1).1, (eqToHom b.property.symm ≫ b.val.2.2) ≫ (F b.val.1).2⟩,
      fun _i _i' _f _b ↦ rfl⟩
  left_inv α := by
    refine Subtype.ext (funext fun i ↦ funext fun b ↦ ?_)
    obtain ⟨⟨k, v, φ⟩, rfl⟩ := b
    exact (α.property φ ⟨⟨k, bound a.1 k, 𝟙 _⟩, rfl⟩).symm
  right_inv _F := rfl

/-! ## A code with no inductive-recursive counterpart -/

/-- The family with one code, denoting the singleton. -/
@[nolint unusedArguments] def oneFam : Unit → Card := fun _ ↦ ⟨1⟩

/-- The binder code declaring the empty object as the object it binds. -/
def emptyBindCode : Code := .bind ⟨0⟩ (fun i ↦ i.elim0)

/-- The shape at that code, over the object its dependent-sum output decodes
to. -/
def junkShape : Shp sigmaFormer := ⟨emptyBindCode, ⟨0⟩, 𝟙 _⟩

/-- An arity hom for `junkShape` binding the single code of `oneFam`: the
summand asks for a morphism `⟨0⟩ ⟶ ⟨1⟩`, which the empty function
supplies, where the inductive-recursive presentation would demand `⟨1⟩ = ⟨0⟩`.
The second summand family is empty. -/
def junkArity : (k : Idx emptyBindCode) → Σ u : Unit, (bound emptyBindCode k ⟶ oneFam u)
  | .inl _ => ⟨(), fun i ↦ i.elim0⟩
  | .inr s => s.elim0

/-- The bound code's decoding is not the object the shape declares. -/
theorem junk_decoding_ne :
    oneFam (junkArity (.inl ())).1 ≠ bound emptyBindCode (.inl ()) := by
  decide

/-- The shape's output object is fixed by its declaration, whatever code the
binder is applied to: the dependent sum over the declared empty object is the
empty object. -/
theorem out_emptyBind : out sigmaFormer emptyBindCode = ⟨0⟩ := rfl

/-- The arity hom as an element of the functor's value at the family presheaf,
through the p.r.a. formula. -/
def junkObj : (universeFunctor sigmaFormer).toPresheafDomPFunctorData.obj
    (famPresheaf Unit oneFam) :=
  (objEquivSigmaArityHom (universeFunctor sigmaFormer) (famPresheaf Unit oneFam)).symm
    ⟨junkShape, (arityHomEquiv sigmaFormer junkShape Unit oneFam).symm junkArity⟩

/-! ## Example 3.6 at this scale

The obstruction to interpreting the dependent-product universe over a base with
morphisms: reindexing the family along a morphism of the bound object must act
covariantly on the former's output. -/

/-- The family of the counterexample: the singleton indexes the empty object. -/
@[nolint unusedArguments] def counterFam : El ⟨1⟩ → Card := fun _ ↦ ⟨0⟩

/-- The morphism of the counterexample: the unique map from the empty object to
the singleton. -/
def counterMap : (⟨0⟩ : Card) ⟶ ⟨1⟩ := fun i ↦ i.elim0

/-- The counterexample's family reindexed along that morphism. -/
def counterFamReindexed : El ⟨0⟩ → Card := fun i ↦ counterFam (counterMap i)

/-- The dependent-sum former acts covariantly at the counterexample: both sides
are the empty object. -/
theorem sigmaFormer_covariant :
    Nonempty (sigmaFormer ⟨0⟩ counterFamReindexed ⟶ sigmaFormer ⟨1⟩ counterFam) :=
  ⟨fun i ↦ i.elim0⟩

/-- The dependent-product former does not: the empty product is the singleton
and the product of the counterexample family is empty, and there is no map from
the singleton to the empty object. This is Example 3.6 of
[GhaniNordvallForsbergMalatesta2015] at the smallest scale that hosts it. -/
theorem piFormer_not_covariant :
    IsEmpty (piFormer ⟨0⟩ counterFamReindexed ⟶ piFormer ⟨1⟩ counterFam) :=
  ⟨fun f ↦ (f ⟨0, Nat.zero_lt_one⟩).elim0⟩

/-- The counterexample's morphism admits no section: a section would be a map
from the singleton to the empty object. What the dependent-product former's
action needs is exactly such a section, which is the subject of
`Geb/Prototypes/UniverseVariance.lean`. -/
theorem counterMap_not_split : ¬ Nonempty ((⟨1⟩ : Card) ⟶ ⟨0⟩) :=
  fun ⟨g⟩ ↦ (g ⟨0, Nat.zero_lt_one⟩).elim0

end GebProto.FinCardUniverse
