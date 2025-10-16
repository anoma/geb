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
* `IdComp`: Left identity law for composition
* `CompId`: Right identity law for composition
* `IdentityLaws`: Both left and right identity laws
* `CategoryOps`: Category operations (composition and identity)
* `CategoryLaws`: Category laws (associativity and identity laws)
* `CategoryData`: Category data (operations and laws)
* `≅Cat`: Notation for isomorphisms between categories without explicit
  `Cat.of`
-/

namespace GebLean

open CategoryTheory

universe v u

/-- The data of a quiver: a family of types indexed by pairs of vertices. -/
abbrev HomSet (U : Type u) := U → U → Sort v

/-- Compositional structure: composition of morphisms.

Note: Most presentations of category theory put composition in the opposite
order (e.g., `g ∘ f` for `f : a → b` and `g : b → c`). We follow the
convention of Lean's standard libraries, where composition is written
`f ≫ g` or `comp f g`, with the first morphism applied first. -/
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

/-- Left identity law: composing with identity on the left gives the
    original morphism. -/
abbrev IdComp {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) :=
  ∀ {a b : U} (f : hs a b), comp (id a) f = f

/-- Right identity law: composing with identity on the right gives the
    original morphism. -/
abbrev CompId {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) :=
  ∀ {a b : U} (f : hs a b), comp f (id b) = f

/-- Identity laws: both left and right identity laws. -/
structure IdentityLaws {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop where
  /-- Left identity law -/
  id_comp : IdComp hs comp id
  /-- Right identity law -/
  comp_id : CompId hs comp id

/-- Category operations: composition and identity morphisms. -/
structure CategoryOps {U : Type u} (hs : HomSet.{v, u} U) where
  /-- Composition of morphisms -/
  comp : CompositionalStruct hs
  /-- Identity morphisms -/
  id : IdentityStruct hs

/-- Category laws: associativity and identity laws. -/
structure CategoryLaws {U : Type u} (hs : HomSet.{v, u} U)
    (ops : CategoryOps hs) : Prop where
  /-- Associativity of composition -/
  assoc : AssociativityLaw hs ops.comp
  /-- Identity laws -/
  id_laws : IdentityLaws hs ops.comp ops.id

/-- Category data: composition, associativity, identities, and
    identity laws. -/
structure CategoryData (U : Type u) (hs : HomSet.{v, u} U)
    extends CategoryOps hs where
  /-- Category laws -/
  laws : CategoryLaws hs toCategoryOps

namespace CategoryData

variable {U : Type u} {hs : HomSet.{v, u} U}

/-- Associativity law from category data. -/
@[reducible] def assoc (cs : CategoryData U hs) :
    AssociativityLaw hs cs.comp :=
  cs.laws.assoc

/-- Identity laws from category data. -/
@[reducible] def id_laws (cs : CategoryData U hs) :
    IdentityLaws hs cs.comp cs.id :=
  cs.laws.id_laws

end CategoryData

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
