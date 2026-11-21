/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic

/-!
# Prototype: the finite-type universe over a non-discrete base

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

The universe of [GhaniNordvallForsbergMalatesta2015], Examples 2.5 and 2.6, with
the decoding taking values in a category of finite sets — a genuine category,
not a discrete one. `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean` writes the
same universe over `Type` treated as discrete, which is what the
inductive-recursive presentation requires; this module asks what a presheaf
polynomial functor over a base with its morphisms restored computes instead. The
answer is in the sibling `Value` module.

The shape presheaf and the arities are coproducts of representables, which is
the presentation a family of objects acquires under the embedding of the free
coproduct completion `Fam(C)` into `PSh(C)` (`Fam(C)` is the free set-indexed
coproduct completion, Remarks 2.3 of [GhaniNordvallForsbergMalatesta2015]). The
type former is a parameter, so the dependent-sum and dependent-product universes
are two instances of one functor differing only in the shape-output map `q`.

## Main definitions

* `Card` / `El` — the base category's objects (the finite cardinals, with
  functions as morphisms) and their elements.
* `Code` / `Former` / `out` — the code formers, a type former, and the object a
  code former's output decodes to.
* `Idx` / `bound` — the representable summands of a code former's arity and the object each
  is indexed by: `bind`'s are the code being bound and the family under the
  binder.
* `Shp` / `Dir` — the shapes and directions: the total spaces of the shape
  presheaf `Σ_c y(out c)` and of the arity presheaf `Σ_k y(bound c k)`.
* `universeData` / `universeFunctor` — the operations and the functor with its
  seven functor laws, both parameterized by the type former.
* `sigmaFormer` / `piFormer` / `sigmaUniverse` / `piUniverse` — the dependent-sum
  and dependent-product formers and the two functors they give.

## Main statements

* `directionRestr_id_law` through `reindex_comp_law` — the seven functor laws.

## Implementation notes

The base is defined here rather than taken to be
`Geb/Mathlib/CategoryTheory/FinSetSkel`, which has the same objects. That
category seals `FinSetSkel.Hom` `irreducible` so that morphism equality is
decidable without `Classical.choice`; the seal blocks the definitional
reasoning this construction runs on. The p.r.a. laws `ReindexId` and
`ReindexComp` compare directions over shapes whose morphism components are
different composites, and the arity reindexing here is the identity map because
the arity depends on the shape only through its code former. Both rely on
composition being definitionally associative and unital, which holds for
functions and not past the seal: unfolding a sealed composite reaches a
projection out of the irreducible `Hom` and the elaborator fails rather than
getting stuck. `FinSetSkel.toIdxFun` and `FinSetSkel.ofIdxFun` exhibit the two
bases' correspondence.

`Shp` and `Dir` are the total spaces of presheaves of the form
`Σ_k y(bound k)`, so every restriction map — `directionRestr`, `shapeRestr` — is
precomposition. The shape restriction is written by projection and `eqToHom`
rather than by matching on the shape, which keeps `(shapeRestr g a).1.1`
definitionally equal to `a.1.1`; since `Dir` mentions only that component, the
arity reindexing is the identity.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [HancockMcBrideGhaniMalatestaAltenkirch2013]
* [Weber2007]

## Tags

prototype, inductive-recursive, presheaf, universe, parametric right adjoint,
finite set
-/

@[expose] public section

open CategoryTheory

namespace GebProto.FinCardUniverse

/-! ## The base category -/

/-- An object of the base: a finite cardinal. -/
@[ext] structure Card : Type where
  /-- The number of elements. -/
  len : ℕ
  deriving DecidableEq

/-- The elements of an object. -/
abbrev El (S : Card) : Type := Fin S.len

/-- The base category: finite cardinals and functions between their elements.
Composition is function composition, so the category laws hold definitionally. -/
instance cardCategory : SmallCategory Card where
  Hom X Y := El X → El Y
  id _ := _root_.id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## Codes -/

/-- The code formers: one nullary former per object of the base, and one binder
former taking an object and a family of objects indexed by its elements. -/
inductive Code where
  /-- The code of the object `c`. -/
  | iota (c : Card)
  /-- The binder former at the object `S` and the family `T`. -/
  | bind (S : Card) (T : El S → Card)

/-- A type former: what the binder does to an object and a family of objects
indexed by its elements. -/
abbrev Former : Type := (S : Card) → (El S → Card) → Card

/-- The object a code former's output decodes to. -/
def out (former : Former) : Code → Card
  | .iota c => c
  | .bind S T => former S T

/-- The representable summands of a code former's arity: `iota` has none, `bind` has the
code it binds and one code per element of the bound object. -/
def Idx : Code → Type
  | .iota _ => Empty
  | .bind S _ => Unit ⊕ El S

/-- The object a summand is indexed by. -/
def bound : (c : Code) → Idx c → Card
  | .iota _, k => k.elim
  | .bind S _, .inl _ => S
  | .bind _ T, .inr s => T s

/-! ## Shapes and directions -/

/-- The shapes: the total space of the shape presheaf `Σ_c y(out c)`. A shape is
a code former together with a morphism into the object its output decodes to. -/
def Shp (former : Former) : Type :=
  Σ c : Code, Σ j : Card, (j ⟶ out former c)

/-- The directions of a shape: the total space of the arity presheaf
`Σ_k y(bound c k)`. Only the shape's code former is used, so shapes sharing a
code former have the same directions. -/
def Dir {former : Former} (a : Shp former) : Type :=
  Σ k : Idx a.1, Σ i : Card, (i ⟶ bound a.1 k)

/-! ## The functor -/

/-- The operations of the universe endofunctor at a type former. Every
restriction map is precomposition. -/
def universeData (former : Former) : PresheafPFunctorData Card Card where
  A := Shp former
  B := Dir
  r := fun x ↦ x.2.2.1
  q := fun a ↦ a.2.1
  directionRestr := fun _a _i i' g d ↦
    ⟨⟨d.val.1, i', g ≫ eqToHom d.property.symm ≫ d.val.2.2⟩, rfl⟩
  shapeRestr := fun _j j' g a ↦
    ⟨⟨a.val.1, j', g ≫ eqToHom a.property.symm ≫ a.val.2.2⟩, rfl⟩
  reindex := fun _j _j' _g _a _i d ↦ d

/-! ### The functor laws

Every restriction map is precomposition, so the laws are the category laws,
which hold definitionally for functions. They are stated separately rather than
inline because `reindex_comp_law` needs `shapeRestr_comp_law` by name: the law
is stated relative to it. -/

/-- `directionRestr` preserves identities. -/
theorem directionRestr_id_law (former : Former) :
    (universeData former).DirectionRestrId := by
  intro a i
  funext d
  obtain ⟨⟨k, v, φ⟩, rfl⟩ := d
  exact Subtype.ext (congrArg (fun ψ ↦ (⟨k, v, ψ⟩ : Dir a)) rfl)

/-- `directionRestr` reverses composition. -/
theorem directionRestr_comp_law (former : Former) :
    (universeData former).DirectionRestrComp := by
  intro a _i i' i'' f g
  funext d
  obtain ⟨⟨k, v, φ⟩, rfl⟩ := d
  exact Subtype.ext (congrArg (fun ψ ↦ (⟨k, i'', ψ⟩ : Dir a)) rfl)

/-- `shapeRestr` preserves identities. -/
theorem shapeRestr_id_law (former : Former) :
    (universeData former).ShapeRestrId := by
  intro j
  funext a
  obtain ⟨⟨c, v, ψ⟩, rfl⟩ := a
  exact Subtype.ext (congrArg (fun χ ↦ (⟨c, v, χ⟩ : Shp former)) rfl)

/-- `shapeRestr` reverses composition. -/
theorem shapeRestr_comp_law (former : Former) :
    (universeData former).ShapeRestrComp := by
  intro _j j' j'' g h
  funext a
  obtain ⟨⟨c, v, ψ⟩, rfl⟩ := a
  exact Subtype.ext (congrArg (fun χ ↦ (⟨c, j'', χ⟩ : Shp former)) rfl)

/-- The arity reindexing is a morphism of arity presheaves. It is the identity
map, the arity depending on the shape only through its code former. -/
theorem reindex_naturality_law (former : Former) :
    (universeData former).ReindexNaturality := by
  intro _j _j' _g _a _i _i' _f
  rfl

/-- The arity reindexing along an identity is the identity. -/
theorem reindex_id_law (former : Former) :
    (universeData former).ReindexId (shapeRestr_id_law former) := by
  intro _j _a _i _b
  rfl

/-- The arity reindexing along a composite is the composite of the
reindexings. -/
theorem reindex_comp_law (former : Former) :
    (universeData former).ReindexComp (shapeRestr_comp_law former) := by
  intro _j _j' _j'' _g _h _a _i _b
  rfl

/-- The universe endofunctor at a type former: the operations with the seven
functor laws. -/
def universeFunctor (former : Former) : PresheafPFunctor Card Card where
  toPresheafPFunctorData := universeData former
  isFunctorial :=
    { directionRestr_id := directionRestr_id_law former
      directionRestr_comp := directionRestr_comp_law former
      shapeRestr_id := shapeRestr_id_law former
      shapeRestr_comp := shapeRestr_comp_law former
      reindex_naturality := reindex_naturality_law former
      reindex_id := reindex_id_law former
      reindex_comp := reindex_comp_law former }

/-! ## The two type formers -/

/-- The dependent-sum former: the object of pairs. -/
def sigmaFormer : Former :=
  fun S T ↦ ⟨(List.ofFn fun s : El S ↦ (T s).len).sum⟩

/-- The dependent-product former: the object of sections. -/
def piFormer : Former :=
  fun S T ↦ ⟨(List.ofFn fun s : El S ↦ (T s).len).prod⟩

/-- The universe closed under dependent sums. -/
def sigmaUniverse : PresheafPFunctor Card Card := universeFunctor sigmaFormer

/-- The universe closed under dependent products. -/
def piUniverse : PresheafPFunctor Card Card := universeFunctor piFormer

end GebProto.FinCardUniverse
