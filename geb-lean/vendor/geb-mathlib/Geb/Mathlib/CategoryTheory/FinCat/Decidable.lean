/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Hom2

/-!
# Decidable equality of specifications

Equality is decidable at each of the three levels: finite-category
specifications, functor specifications and 2-cell specifications. Each
level is decided field by field, transporting along the equality of an
earlier field wherever a later field's type mentions it. The `Bool`
equation fields are proof-irrelevant and contribute no decision.

## Main definitions

* `CategoryTheory.FinCat.decidableEqPiFin` — equality of functions out
  of `Fin n`, decided pointwise.
* `CategoryTheory.FinCat.decidableEqComp` — equality of composition
  tables at fixed counts.
* `CategoryTheory.FinCat.Hom₂.decidableEq`,
  `CategoryTheory.FinCat.Hom.decidableEq`,
  `CategoryTheory.FinCat.decidableEq` — the three levels.

## Implementation notes

`decidableEqPiFin` is dependent from the outset, `funext_iff` already
being so, and therefore covers the non-dependent case with no second
instance at the same head symbol.

It is `scoped`, and every `DecidableEq` argument at a Π-type use site
is supplied explicitly, one application per binder, so that the only
argument left to instance resolution is the innermost
`DecidableEq (Fin _)`, where core's instance is the sole candidate.
`Fintype.decidablePiFintype` is a competitor at the same head symbol
and is likewise dependent, so the two measures are needed together:
without the scoping, which of the two applies downstream would be a
matter of declaration order, and without the explicit arguments the
inner ones resolve through it.

The transports run in the order the fields are declared. At the
specification level `objCount` is a `Nat`, decided by core's
`Nat.decEq` through a `dif`, and `nonIdCount` and `comp` follow; at
the functor level `objMap` precedes `map`, whose type mentions it; at
the 2-cell level `app`'s type mentions only the fixed 1-cells `F` and
`G`, so no transport arises.

Beyond its own dependency this module needs no import: `funext_iff`
and `decidable_of_iff` are core.

## Tags

category, functor, natural transformation, finite category, decidable
equality, constructive, choice-free
-/

@[expose] public section

namespace CategoryTheory

namespace FinCat

/-- Decidable equality of functions out of `Fin n`, decided pointwise.
Dependent from the outset — `funext_iff` already is — so it covers the
non-dependent case with no second instance at the same head symbol. -/
scoped instance decidableEqPiFin.{v} {n : Nat} {Y : Fin n → Type v}
    [∀ i, DecidableEq (Y i)] : DecidableEq ((i : Fin n) → Y i) :=
  fun f g ↦ decidable_of_iff (∀ i, f i = g i) funext_iff.symm

/-- Decidable equality of composition tables at fixed counts. The
`DecidableEq` argument is supplied explicitly at every level: an
instance that still typechecks may silently acquire
`Classical.choice`, which is the hazard `Geb/Mathlib/Data/FinEnum.lean`
documents for the same head symbol. -/
def decidableEqComp {objCount : Nat} {nonIdCount : Fin objCount → Fin objCount → Nat} :
    DecidableEq ((i j k : Fin objCount) → Fin (nonIdCount i j) → Fin (nonIdCount j k) →
      Fin (homCountOf objCount nonIdCount i k)) :=
  @decidableEqPiFin _ _ (fun _ ↦
    @decidableEqPiFin _ _ (fun _ ↦
      @decidableEqPiFin _ _ (fun _ ↦
        @decidableEqPiFin _ _ (fun _ ↦
          @decidableEqPiFin _ _ (fun _ ↦ inferInstance)))))

/-- Decidable equality of 2-cell specifications. No transport: `app`'s
type mentions only the fixed parameters `F` and `G`. -/
instance Hom₂.decidableEq {S T : FinCat} {F G : Hom S T} :
    DecidableEq (Hom₂ F G) :=
  fun α β ↦
    match α, β with
    | ⟨a, _⟩, ⟨b, _⟩ =>
      match @decidableEqPiFin _ _ (fun _ ↦ inferInstance) a b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (fun e ↦ h (by injection e))

/-- Decidable equality of functor specifications: decide `objMap`,
transport along that equality — `map`'s type mentions `objMap` — then
decide `map`. -/
instance Hom.decidableEq {S T : FinCat} : DecidableEq (Hom S T) :=
  fun F G ↦
    match F, G with
    | ⟨o, m, _⟩, ⟨o', m', _⟩ =>
      match @decidableEqPiFin _ _ (fun _ ↦ inferInstance) o o' with
      | isFalse h => isFalse (fun e ↦ h (by injection e))
      | isTrue ho => by
        subst ho
        exact match @decidableEqPiFin _ _ (fun _ ↦
            @decidableEqPiFin _ _ (fun _ ↦
              @decidableEqPiFin _ _ (fun _ ↦ inferInstance))) m m' with
          | isTrue h => isTrue (by subst h; rfl)
          | isFalse h => isFalse (fun e ↦ h (by injection e))

/-- Decidable equality of specifications: decide `objCount`, transport,
decide `nonIdCount`, transport, decide `comp`. -/
instance decidableEq : DecidableEq FinCat := fun S T ↦
  match S, T with
  | ⟨n, nc, c, _⟩, ⟨n', nc', c', _⟩ =>
    if hn : n = n' then by
      subst hn
      exact match @decidableEqPiFin _ _ (fun _ ↦
          @decidableEqPiFin _ _ (fun _ ↦ inferInstance)) nc nc' with
        | isFalse h => isFalse (fun e ↦ h (by injection e))
        | isTrue hnc => by
          subst hnc
          exact match decidableEqComp c c' with
            | isTrue h => isTrue (by subst h; rfl)
            | isFalse h => isFalse (fun e ↦ h (by injection e))
    else isFalse (fun e ↦ hn (by injection e))

end FinCat

end CategoryTheory
