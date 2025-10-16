import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Fintype Utilities

Structure-based representation of the Fintype interface.

## Main definitions

* `FintypeData`: Structure containing a `Finset` with the property that it
  contains all elements of the type
* `fintypeOfFintypeData`: Build a `Fintype` typeclass from `FintypeData`
* `fintypeDataOfFintype`: Extract `FintypeData` from a `Fintype` typeclass
-/

namespace GebLean

universe u

variable {α : Type u}

/-- Property that a finset contains all elements of a type. -/
abbrev FinsetComplete (s : Finset α) : Prop := ∀ x : α, x ∈ s

/-- Structure-based representation of a finite type: a finset containing
    all elements. -/
structure FintypeData (α : Type u) where
  /-- The finite set of all elements -/
  elems : Finset α
  /-- Property that the finset contains all elements -/
  complete : FinsetComplete elems

/-- Build a `Fintype` typeclass instance from `FintypeData`. -/
instance (data : FintypeData α) : Fintype α where
  elems := data.elems
  complete := data.complete

/-- Extract the `FintypeData` from a `Fintype` typeclass instance. -/
abbrev fintypeDataOfFintype (α : Type u) [ft : Fintype α] : FintypeData α where
  elems := ft.elems
  complete := ft.complete

end GebLean
