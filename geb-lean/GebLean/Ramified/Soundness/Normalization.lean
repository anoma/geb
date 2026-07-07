import GebLean.Ramified.Soundness.BarRep

/-!
# Ramified recurrence: the Lemma 12 normalization bound

The order measure `RType.ord` on ramified types and its role in Lemma 12's
normalization bound for the simply-typed calculus `1λ(A)` (Leivant III
section 4.2, p. 224), the last step of the soundness development bounding
the length of the reduction path of a bar-translated term
(`GebLean/Ramified/Soundness/BarRep.lean`).

This module currently supplies only the order layer: `RType.ord` measures
the arrow-nesting depth of an r-type, ignoring `Omega` shifts (decision P1:
the totalization choice `ord (Ω τ) = ord τ`, novel packaging — Leivant's
order measure is stated only on the simple types the bar-translation
produces, and `Omega` never appears in a simple type; extending `ord` over
all of `RType` by ignoring `Omega` lets later development state the bound
uniformly without a simplicity side condition on every occurrence).

## Main definitions

* `RType.ord` — the order of an r-type: `ord o = 0`,
  `ord (τ → σ) = max (1 + ord τ) (ord σ)`, `ord (Ω τ) = ord τ`.

## Main statements

* `RType.one_le_ord_arrow` — every arrow type has order at least `1`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied
Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.2
(p. 213): the order of a simple type.

## Tags

ramified recurrence, order, normalization, simply-typed lambda calculus
-/

namespace GebLean.Ramified

/-- The order of an r-type (Leivant III section 2.2, p. 213): `ord o = 0`,
`ord (τ → σ) = max (1 + ord τ) (ord σ)`. The `Omega` clause `ord (Ω τ) = ord
τ` is decision P1's totalization choice, ignoring the shift since Leivant's
order measure is stated only on the `Omega`-free simple types. Realized by
the dependent eliminator `PolyFix.ind` (decision 8), following `barTy`'s
pattern (`GebLean/Ramified/Soundness/BarRep.lean`). -/
def RType.ord (τ : RType) : ℕ :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => ℕ)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => 0
      | RTypeShape.arrow, _, ih =>
        max (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) + 1)
          (ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
      | RTypeShape.omega, _, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))) τ

@[simp] theorem RType.ord_o : RType.o.ord = 0 := rfl

@[simp] theorem RType.ord_arrow (τ σ : RType) :
    (RType.arrow τ σ).ord = max (τ.ord + 1) σ.ord := rfl

@[simp] theorem RType.ord_omega (τ : RType) : (RType.omega τ).ord = τ.ord := rfl

/-- Every arrow type has order at least `1` (Leivant III section 2.2, p. 213):
`ord (τ → σ) ≥ 1 + ord τ ≥ 1`. -/
theorem RType.one_le_ord_arrow (τ σ : RType) : 1 ≤ (RType.arrow τ σ).ord := by
  rw [RType.ord_arrow]
  omega

end GebLean.Ramified
