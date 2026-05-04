import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Constructive quotient of a category by isomorphism

Mathlib's `CategoryTheory.Skeleton` uses `Quotient.out`
(which is not constructive) to define morphisms between
isomorphism classes.  This module provides the quotient
type on objects alone, using only the constructive
`Quotient` API (`mk`, `lift`, `ind`, `sound`).

The type `Skeleton C` is `Quotient (isIsomorphicSetoid C)`,
the type of isomorphism classes of objects of `C`.
-/

namespace GebLean

open CategoryTheory

universe v u w w' w''

variable (C : Type u) [Category.{v} C]

/-- The type of isomorphism classes of objects of `C`,
defined as `Quotient (isIsomorphicSetoid C)`.  Uses only
the constructive `Quotient` API. -/
def Skeleton : Type u :=
  Quotient (isIsomorphicSetoid C)

/-- Send an object of `C` to its isomorphism class. -/
def toSkeleton (X : C) : Skeleton C :=
  Quotient.mk (isIsomorphicSetoid C) X

variable {C}

@[simp]
theorem toSkeleton_eq_iff {X Y : C} :
    toSkeleton C X = toSkeleton C Y ↔
      Nonempty (X ≅ Y) := by
  constructor
  · exact Quotient.exact
  · exact Quotient.sound
      (s := isIsomorphicSetoid C)

/-- Lift a function on `C` to a function on `Skeleton C`,
given a proof that it respects isomorphism. -/
def Skeleton.lift {β : Sort w}
    (f : C → β)
    (h : ∀ (X Y : C),
      Nonempty (X ≅ Y) → f X = f Y) :
    Skeleton C → β :=
  Quotient.lift f h

/-- Lift a binary function to `Skeleton`, given a proof
that it respects isomorphism in both arguments. -/
def Skeleton.lift₂
    {D : Type w} [Category.{w'} D]
    {β : Sort w''}
    (f : C → D → β)
    (h : ∀ (X₁ : C) (Y₁ : D) (X₂ : C) (Y₂ : D),
      Nonempty (X₁ ≅ X₂) → Nonempty (Y₁ ≅ Y₂) →
        f X₁ Y₁ = f X₂ Y₂) :
    Skeleton C → Skeleton D → β :=
  Quotient.lift₂ f h

/-- The functorial action of a functor on isomorphism
classes. -/
def Skeleton.map
    {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) :
    Skeleton C → Skeleton D :=
  Skeleton.lift
    (fun X => toSkeleton D (F.obj X))
    (fun _ _ ⟨e⟩ =>
      toSkeleton_eq_iff.mpr ⟨F.mapIso e⟩)

end GebLean
