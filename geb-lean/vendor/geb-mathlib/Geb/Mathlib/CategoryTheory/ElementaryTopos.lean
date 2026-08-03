/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Elementary toposes

An elementary topos is a category with finite limits and finite
colimits that is cartesian closed and has a subobject classifier.
`ElementaryTopos C` carries chosen data for the generators of that
structure — the cartesian and closed structures, the initial object,
binary coproducts, equalizers, coequalizers, and the classifier — and
derives the finite-limit and finite-colimit properties from them.

## Main definitions

* `CategoryTheory.ElementaryTopos`
* `CategoryTheory.ElementaryTopos.cartesianMonoidalCategory`
* `CategoryTheory.ElementaryTopos.monoidalClosed`
* `CategoryTheory.ElementaryTopos.tensorUnitIsoΩ₀`
* `CategoryTheory.ElementaryTopos.isInitial`

## Implementation notes

The class is stated over `(C : Type u) [Category.{v} C]`, matching
mathlib convention. `SmallCategory C` is `Category.{u} C`, so a
formulation over it would admit small instances but foreclose every
non-small one.

Data is carried rather than asserted because a `Prop` form is
indifferent to a distinction that matters computationally: recovering
a cone from `Nonempty` is `getLimitCone`, which is `Classical.choice`
and `noncomputable`, so a class built on the `Prop` form computes
nothing. The finite-limit and finite-colimit properties are `Prop`
and are derived below rather than carried, chosen cones for an
arbitrary finite diagram not being computably derivable:
`FinCategory` carries a `Fintype`, whose underlying `Finset` yields a
list only through the `noncomputable` `Finset.toList`, and every
other route is `noncomputable` or `Trunc`-valued.

Accessors for the data-carrying classes are definitions, not
instances, two routes to data not needing to agree definitionally;
accessors for the `Prop` classes are instances, two resolution routes
being harmless there by proof irrelevance. A class-typed definition
carries `@[instance_reducible]`, without which it draws the
semireducibility warning such a definition otherwise attracts.

`cartesianMonoidalCategory` is marked `attribute [local instance]`,
in force for the rest of the module. Three declarations need it:
`monoidalClosed`, whose type mentions `MonoidalCategory C`;
`tensorUnitIsoΩ₀`, whose type mentions `𝟙_ C`; and `HasFiniteLimits`,
which needs `HasFiniteProducts C`. A consumer holding only
`[ElementaryTopos C]` must apply the same attribute before the
cartesian structure is in scope.

`Functor.empty.{0}` pins the universe deliberately. `HasInitial C`
unfolds to `HasColimitsOfShape (Discrete PEmpty.{1}) C` and `IsInitial`
is `IsColimit (asEmptyCocone _)` at the same level, so any other level
breaks the passage from the initial field to `HasInitial`.

The classifier's `Ω₀` is not required to be the cartesian terminal.
Both objects are terminal, hence canonically and uniquely isomorphic,
so no coherence condition arises; `tensorUnitIsoΩ₀` exports the
comparison. An equality of objects would not be invariant under
equivalence, and would oblige an instance whose natural classifier
yields an isomorphic but unequal `Ω₀` to rebuild it.

The class is `ElementaryTopos` and not `Topos`: the qualifier distinguishes
it from a Grothendieck topos, and mathlib reserves `Topos` for
sheaf-theoretic material, `Mathlib/CategoryTheory/Topos/` holding
`Sheaf.lean` and a deprecated classifier shim while declaring no `Topos`
class.

## References

* [Freyd1972], for the axiomatisation transcribed here, which
  includes the finite colimits.
* [Mikkelsen1976], whose Theorem 2.3 is that an elementary topos has
  finite colimits, so that the property is redundant as an axiom.
* [Pare1974], for a published proof of that theorem by the
  tripleability of the power-object functor.

## Tags

elementary topos, subobject classifier, cartesian closed, topos
-/

public section

universe v u

namespace CategoryTheory

open CategoryTheory.Limits MonoidalCategory

/-- An elementary topos: a cartesian closed category with a subobject
classifier, with chosen data for the generators of its finite limits
and finite colimits. -/
@[ext]
class ElementaryTopos (C : Type u) [Category.{v} C] where
  /-- The cartesian structure, supplying the terminal object and
  binary products. -/
  cartesian : CartesianMonoidalCategory C
  /-- Closure over the cartesian structure, supplying exponentials. -/
  closed : @MonoidalClosed C _ cartesian.toMonoidalCategory
  /-- A chosen initial object, as a cocone over the empty diagram. -/
  initialCocone : ColimitCocone (Functor.empty.{0} C)
  /-- Chosen binary coproducts. -/
  binaryCoproductCocone : ∀ X Y : C, ColimitCocone (pair X Y)
  /-- Chosen equalizers. -/
  equalizerCone : ∀ {X Y : C} (f g : X ⟶ Y), LimitCone (parallelPair f g)
  /-- Chosen coequalizers. -/
  coequalizerCocone : ∀ {X Y : C} (f g : X ⟶ Y), ColimitCocone (parallelPair f g)
  /-- A subobject classifier. -/
  classifier : Classifier C

namespace ElementaryTopos

variable (C : Type u) [Category.{v} C] [ElementaryTopos C]

/-- The cartesian structure, as a definition rather than an instance:
two routes to data need not agree definitionally. -/
@[instance_reducible] def cartesianMonoidalCategory :
    CartesianMonoidalCategory C :=
  cartesian

attribute [local instance] cartesianMonoidalCategory

/-- Closure over the cartesian structure. -/
@[instance_reducible] def monoidalClosed : MonoidalClosed C := closed

/-- The comparison of the cartesian terminal with the classifier's
`Ω₀`. Both are terminal, so this isomorphism is unique. -/
def tensorUnitIsoΩ₀ : 𝟙_ C ≅ (classifier (C := C)).Ω₀ :=
  IsTerminal.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
    Classifier.isTerminalΩ₀

/-- The chosen initial object is initial. -/
def isInitial : IsInitial (initialCocone (C := C)).cocone.pt :=
  IsColimit.ofIsoColimit initialCocone.isColimit
    (Cocone.ext (Iso.refl _) (by simp))

/-- The initial-object field, as the corresponding `Prop` class. -/
instance : HasInitial C := IsInitial.hasInitial (isInitial C)

/-- The binary-coproduct field, per diagram. -/
instance hasColimit_pair {X Y : C} : HasColimit (pair X Y) :=
  ⟨⟨binaryCoproductCocone X Y⟩⟩

/-- Binary coproducts, from the per-diagram form. -/
instance : HasBinaryCoproducts C := hasBinaryCoproducts_of_hasColimit_pair C

/-- The equalizer field, per diagram. -/
instance hasLimit_parallelPair {X Y : C} {f g : X ⟶ Y} :
    HasLimit (parallelPair f g) :=
  ⟨⟨equalizerCone f g⟩⟩

/-- Equalizers, from the per-diagram form. -/
instance : HasEqualizers C := hasEqualizers_of_hasLimit_parallelPair C

/-- The coequalizer field, per diagram. -/
instance hasColimit_parallelPair {X Y : C} {f g : X ⟶ Y} :
    HasColimit (parallelPair f g) :=
  ⟨⟨coequalizerCocone f g⟩⟩

/-- Coequalizers, from the per-diagram form. -/
instance : HasCoequalizers C := hasCoequalizers_of_hasColimit_parallelPair C

/-- Finite coproducts, from the initial object and binary coproducts. -/
instance : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_has_binary_and_initial (C := C)

/-- Finite limits, from the cartesian structure and equalizers. -/
instance : HasFiniteLimits C :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Finite colimits, from finite coproducts and coequalizers. -/
instance : HasFiniteColimits C :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end ElementaryTopos

end CategoryTheory
