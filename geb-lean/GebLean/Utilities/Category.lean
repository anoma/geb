import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

/-!
# Category Theory Utilities

Convenience notation and helpers for working with categories.

## Main definitions

* `HomSet`: The data of a quiver (the Hom type family)
* `CompositionalStruct`: Composition of morphisms
* `AssociativityLaw`: Associativity law for composition
* `SemicategoryStruct`: Semicategory structure (composition and associativity)
* `IdentityStruct`: Identity morphisms for each object
* `LeftIdentityLaw`: Left identity law for composition
* `RightIdentityLaw`: Right identity law for composition
* `IdentityLaws`: Both left and right identity laws
* `CategoryStruct`: Category structure (composition, associativity, identities,
  and identity laws)
* `≅Cat`: Notation for isomorphisms between categories without explicit
  `Cat.of`
-/

namespace GebLean

open CategoryTheory

universe v u

/-- The data of a quiver: a family of types indexed by pairs of vertices. -/
abbrev HomSet (U : Type u) := U → U → Sort v

/-- Compositional structure: composition of morphisms. -/
abbrev CompositionalStruct {U : Type u} (hs : HomSet.{v, u} U) :=
  ∀ {a b c : U}, hs a b → hs b c → hs a c

/-- Associativity law for composition. -/
abbrev AssociativityLaw {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) :=
  ∀ {a b c d : U} (f : hs a b) (g : hs b c) (h : hs c d),
    comp (comp f g) h = comp f (comp g h)

/-- Semicategory structure: composition and associativity. -/
structure SemicategoryStruct (U : Type u) (hs : HomSet.{v, u} U) where
  /-- Composition of morphisms -/
  comp : CompositionalStruct hs
  /-- Associativity of composition -/
  assoc : AssociativityLaw hs comp

/-- Identity structure: identity morphisms for each object. -/
abbrev IdentityStruct {U : Type u} (hs : HomSet.{v, u} U) :=
  ∀ (a : U), hs a a

/-- Left identity law for composition. -/
abbrev LeftIdentityLaw {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) :=
  ∀ {a b : U} (f : hs a b), comp (id a) f = f

/-- Right identity law for composition. -/
abbrev RightIdentityLaw {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) :=
  ∀ {a b : U} (f : hs a b), comp f (id b) = f

/-- Identity laws: both left and right identity laws. -/
structure IdentityLaws {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop where
  /-- Left identity law -/
  id_comp : LeftIdentityLaw hs comp id
  /-- Right identity law -/
  comp_id : RightIdentityLaw hs comp id

/-- Category structure: composition, associativity, identities, and
    identity laws. -/
structure CategoryStruct (U : Type u) (hs : HomSet.{v, u} U) where
  /-- Compositional structure -/
  toCompositionalStruct : CompositionalStruct hs
  /-- Associativity law -/
  toAssociativityLaw : AssociativityLaw hs toCompositionalStruct
  /-- Identity morphisms -/
  toIdentityStruct : IdentityStruct hs
  /-- Identity laws -/
  toIdentityLaws : IdentityLaws hs toCompositionalStruct toIdentityStruct

/-- Extract a `Quiver` typeclass instance from a `HomSet`. -/
instance {U : Type u} (hs : HomSet.{v, u} U) : Quiver.{v, u} U where
  Hom := hs

/-- Extract the `HomSet` from a `Quiver` typeclass instance. -/
abbrev homSetOfQuiver (U : Type u) [Quiver.{v, u} U] : HomSet.{v, u} U :=
  Quiver.Hom

end GebLean

namespace CategoryTheory

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

end CategoryTheory
