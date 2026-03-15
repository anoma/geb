import GebLean.Paranatural
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Dinatural numbers: endo-paranatural transformations of Hom are ℕ

This module proves that endo-paranatural transformations of the hom-profunctor
on `Type v` are in bijection with natural numbers.

Given the hom-profunctor `HomProf : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v` with
`HomProf x y = (x → y)`, an endo-paranatural transformation
`α : Paranat HomProf HomProf` assigns to each type `A` a function
`α(A) : (A → A) → (A → A)`.

The paranaturality condition says: if `f : A → B` and `d₀ : A → A`, `d₁ : B → B`
satisfy `f ∘ d₀ = d₁ ∘ f` (the endomorphisms "commute" through `f`), then
`f ∘ α(A)(d₀) = α(B)(d₁) ∘ f`.

The correspondence with natural numbers is:
- Forward: `n ↦ (A, f) ↦ f^n` (iterate n times)
- Backward: `α ↦ α(ℕ)(succ)(0)` (count iterations on ℕ)

This result holds for `Type v` because:
1. `ℕ` is an object of `Type v` to which we can apply α
2. The universal property of `ℕ` (as a natural numbers object) provides the
   "iteration" morphism needed to prove the round-trip properties

For a general category C, the analogous result would require C to have a
natural numbers object (NNO), and the correspondence would be with global
elements `1 → N` rather than external natural numbers.

## References

* Neumann, "Paranatural Category Theory"

-/

namespace GebLean

open CategoryTheory

section HomProfunctor

/-!
### The hom-profunctor

The hom-profunctor `HomProf : Typeᵒᵖ ⥤ Type ⥤ Type` sends `(x, y)` to
the function type `x → y`.

- Contravariant in the first argument: precomposition
- Covariant in the second argument: postcomposition

We use mathlib's `Functor.hom Type : Typeᵒᵖ × Type ⥤ Type` curried via
`Functor.curry`.
-/

/-- The hom-profunctor on `Type`, sending `(x, y)` to `x → y`.
This is mathlib's hom-pairing `Functor.hom Type` in curried form. -/
abbrev HomProf : Typeᵒᵖ ⥤ Type ⥤ Type :=
  Functor.curry.obj (Functor.hom Type)

@[simp]
theorem HomProf_obj_obj (A B : Type) : (HomProf.obj (Opposite.op A)).obj B = (A → B) := rfl

/-- The diagonal of `HomProf` at `A` is endomorphisms `A → A`. -/
theorem HomProf_diag (A : Type) : diagApp HomProf A = (A → A) := rfl

end HomProfunctor

section NatToParanat

/-!
### From natural numbers to paranatural transformations

Given `n : ℕ`, we define a paranatural transformation that iterates an
endomorphism `n` times: `α(A)(f) = f^n`.
-/

/-- Iterate a function `f : A → A` exactly `n` times. -/
def iterateN (n : ℕ) {A : Type} (f : A → A) : A → A :=
  match n with
  | 0 => id
  | n + 1 => f ∘ iterateN n f

@[simp]
theorem iterateN_zero {A : Type} (f : A → A) : iterateN 0 f = id := rfl

@[simp]
theorem iterateN_succ {A : Type} (n : ℕ) (f : A → A) :
    iterateN (n + 1) f = f ∘ iterateN n f := rfl

/-- Iteration commutes: if `g ∘ f₀ = f₁ ∘ g`, then `g ∘ f₀^n = f₁^n ∘ g`. -/
theorem iterateN_comm {A B : Type} (n : ℕ) (g : A → B) (f₀ : A → A) (f₁ : B → B)
    (hcomm : g ∘ f₀ = f₁ ∘ g) : g ∘ iterateN n f₀ = iterateN n f₁ ∘ g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterateN_succ]
    calc g ∘ (f₀ ∘ iterateN n f₀)
        = (g ∘ f₀) ∘ iterateN n f₀ := rfl
      _ = (f₁ ∘ g) ∘ iterateN n f₀ := by rw [hcomm]
      _ = f₁ ∘ (g ∘ iterateN n f₀) := rfl
      _ = f₁ ∘ (iterateN n f₁ ∘ g) := by rw [ih]
      _ = (f₁ ∘ iterateN n f₁) ∘ g := rfl

/-- Given `n : ℕ`, the paranatural transformation that iterates `n` times. -/
def natToParanat (n : ℕ) : Paranat HomProf HomProf where
  app A f := iterateN n f
  paranatural := fun A₀ A₁ g d₀ d₁ hcompat => by
    simp only [DiagCompat, HomProf_obj_obj] at hcompat ⊢
    exact iterateN_comm n g d₀ d₁ hcompat

end NatToParanat

section ParanatToNat

/-!
### From paranatural transformations to natural numbers

Given `α : Paranat HomProf HomProf`, we extract a natural number by applying
`α` to `ℕ` with the successor function, then evaluating at `0`.
-/

/-- Extract a natural number from a paranatural transformation by applying
it to `(ℕ, succ)` and evaluating at `0`. -/
def paranatToNat (α : Paranat HomProf HomProf) : ℕ :=
  α.app ℕ Nat.succ 0

end ParanatToNat

section RoundTrips

/-!
### The bijection between ℕ and endo-paranatural transformations

We prove that `natToParanat` and `paranatToNat` are inverses.
-/

/-- Iterating successor `n` times starting from `0` gives `n`. -/
theorem iterateN_succ_zero (n : ℕ) : iterateN n Nat.succ 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterateN_succ, Function.comp_apply, ih]

/-- The round-trip from `ℕ` to paranatural and back is the identity. -/
@[simp]
theorem paranatToNat_natToParanat (n : ℕ) : paranatToNat (natToParanat n) = n := by
  simp only [paranatToNat, natToParanat]
  exact iterateN_succ_zero n

/-- For any `a : A`, the function `fun k => iterateN k f a` satisfies the
compatibility condition relating `(ℕ, succ)` to `(A, f)`. -/
theorem iterate_compat {A : Type} (f : A → A) (a : A) :
    DiagCompat HomProf ℕ A (fun k => iterateN k f a) Nat.succ f := by
  simp only [DiagCompat, HomProf_obj_obj]
  funext k
  rfl

/-- The round-trip from paranatural to `ℕ` and back is the identity.
This uses paranaturality with the morphism `k ↦ f^k(a)` which relates
`(ℕ, succ)` to `(A, f)`. -/
@[simp]
theorem natToParanat_paranatToNat (α : Paranat HomProf HomProf) :
    natToParanat (paranatToNat α) = α := by
  apply Paranat.ext
  funext A f
  simp only [natToParanat, paranatToNat]
  funext a
  let evalIter : ℕ → A := fun k => iterateN k f a
  have hcompat : DiagCompat HomProf ℕ A evalIter Nat.succ f := iterate_compat f a
  have hpara := α.paranatural ℕ A evalIter Nat.succ f hcompat
  simp only [DiagCompat, HomProf_obj_obj] at hpara
  have h : evalIter (α.app ℕ Nat.succ 0) = α.app A f (evalIter 0) := by
    exact congrFun hpara 0
  simp only [evalIter, iterateN_zero, id_eq] at h
  exact h

/-- The bijection between natural numbers and endo-paranatural transformations
of the hom-profunctor. -/
def dinaturalNumbersEquiv : ℕ ≃ Paranat HomProf HomProf where
  toFun := natToParanat
  invFun := paranatToNat
  left_inv := paranatToNat_natToParanat
  right_inv := natToParanat_paranatToNat

end RoundTrips

end GebLean
