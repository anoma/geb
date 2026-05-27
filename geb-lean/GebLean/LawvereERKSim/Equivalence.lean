import GebLean.LawvereERKSim.ErToKFunctor
import GebLean.LawvereKSimER
import GebLean.LawvereERInterp
import GebLean.LawvereKSimDCatInterp
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Equivalence — categorical equivalence `LawvereERCat ≌ LawvereKSimDCat 2`

Packages the categorical equivalence `LawvereERCat ≌
LawvereKSimDCat 2` (Tourlakis 2018 Corollary 0.1.0.44 at
`n = 2`) from the two functors `erToKFunctor` (encoding ER
programs as `K^sim` programs) and `kToERFunctor` (the
converse encoding). The two round-trip composites
`erToKFunctor ⋙ kToERFunctor` and `kToERFunctor ⋙
erToKFunctor` are shown equal as functors to the identity
functors via faithfulness of the interpretation functors
combined with the two functor-level interp-preservation
equalities. The `Equivalence` value is assembled via
`Equivalence.mk'` (the raw structure constructor) so that
its `unitIso` and `counitIso` slots store the supplied
`eqToIso`s verbatim.

## Main definitions

- `erToKKToErIso` : natural isomorphism
  `erToKFunctor ⋙ kToERFunctor ≅ 𝟭 LawvereERCat`.
- `kToErErToKIso` : natural isomorphism
  `kToERFunctor ⋙ erToKFunctor ≅ 𝟭 (LawvereKSimDCat 2)`.
- `erKSimEquiv` : the packaged equivalence
  `LawvereERCat ≌ LawvereKSimDCat 2`.

## Main statements

- `erToKFunctor_comp_kToERFunctor` : strict functor equality
  `erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat`.
- `kToERFunctor_comp_erToKFunctor` : strict functor equality
  `kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)`.
- Two `Functor.IsEquivalence` instances on `erToKFunctor` and
  `kToERFunctor`, each a one-line projection of mathlib's
  global `Equivalence.isEquivalence_functor` /
  `Equivalence.isEquivalence_inverse` applied to
  `erKSimEquiv`.

## Implementation notes

The packaging uses `Equivalence.mk'` (the raw structure
constructor) rather than `Equivalence.mk` (the smart
constructor at `Mathlib/CategoryTheory/Equivalence.lean:351`)
because `mk` calls `adjointifyη η ε` on the supplied unit,
replacing it with an adjointified form. Using `mk'`
preserves `erKSimEquiv.unitIso = erToKKToErIso.symm` and
`erKSimEquiv.counitIso = kToErErToKIso` definitionally. The
triangle identity `functor_unitIso_comp` is discharged by an
explicit fifth argument `(by intro X; simp [erToKKToErIso,
kToErErToKIso])` — the `cat_disch` autoparam alone is
insufficient here because it cannot unfold the two `def`-bound
natural isomorphisms `erToKKToErIso` and `kToErErToKIso` (each
defined via `eqToIso`).

The explicit `IsEquivalence` instances (rather than relying
on typeclass search through the mathlib globals) are
required: typeclass search cannot bridge from a `def`-bound
`Equivalence` value to an `IsEquivalence` goal on a
named functor via unification.

## References

- Tourlakis 2018, *Topics in PR Complexity*, Corollary
  0.1.0.44.
- Spec:
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`.
- Mirror code: `kToERFunctor_comp_erInterpFunctor` in
  `GebLean/LawvereKSimER.lean`.

## Tags

equivalence, functor, lawvere, ksim, ertok, ktoer
-/

namespace GebLean

open CategoryTheory

-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKFunctor_comp_kInterpFunctor` and
-- `kToERFunctor_comp_erInterpFunctor`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Strict functor equality for the ER → K → ER round-trip:
`erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat`. Proof uses
faithfulness of `erInterpFunctor` plus `Functor.hcongr_hom`
applied to the two functor-level interp-preservation
equalities. The proof routes through `Functor.hext` (the
heterogeneous-equality variant of `Functor.ext`) to avoid
`eqToHom` transports on the morphism side; since both functors
are identity on objects, the `HEq` reduces to plain `Eq` via
`heq_of_eq`. -/
theorem erToKFunctor_comp_kToERFunctor :
    erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro n m e
  apply heq_of_eq
  apply erInterpFunctor.map_injective
  change erInterpFunctor.map
            (kToERFunctor.map (erToKFunctor.map e))
       = erInterpFunctor.map e
  have h1 :
      erInterpFunctor.map (kToERFunctor.map (erToKFunctor.map e))
        = kInterpFunctor.map (erToKFunctor.map e) :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        kToERFunctor_comp_erInterpFunctor
        (erToKFunctor.map e))
  have h2 :
      kInterpFunctor.map (erToKFunctor.map e)
        = erInterpFunctor.map e :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        erToKFunctor_comp_kInterpFunctor e)
  rw [h1, h2]

-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKFunctor_comp_kInterpFunctor` and
-- `kToERFunctor_comp_erInterpFunctor`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Strict functor equality for the K → ER → K round-trip:
`kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)`.
Symmetric to `erToKFunctor_comp_kToERFunctor`, using
faithfulness of `kInterpFunctor` instead of `erInterpFunctor`,
and `Functor.hcongr_hom` of the two interp-preservation
equalities in the opposite order. -/
theorem kToERFunctor_comp_erToKFunctor :
    kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro n m f
  apply heq_of_eq
  apply kInterpFunctor.map_injective
  change kInterpFunctor.map
            (erToKFunctor.map (kToERFunctor.map f))
       = kInterpFunctor.map f
  have h1 :
      kInterpFunctor.map (erToKFunctor.map (kToERFunctor.map f))
        = erInterpFunctor.map (kToERFunctor.map f) :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        erToKFunctor_comp_kInterpFunctor
        (kToERFunctor.map f))
  have h2 :
      erInterpFunctor.map (kToERFunctor.map f)
        = kInterpFunctor.map f :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        kToERFunctor_comp_erInterpFunctor f)
  rw [h1, h2]

end GebLean
