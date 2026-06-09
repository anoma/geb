import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Subobject classifier for `Type u` via `Prop`

`ULift.{u} Prop` is a subobject classifier for the category
`Type u`: the characteristic map of a monomorphism `m : U ⟶ X`
sends `x : X` to the proposition `∃ a, m a = x`, and the truth
morphism selects `True`. Impredicativity of `Prop` plays the
role of the propositional-resizing hypothesis of [UF13],
Theorem 10.1.12 (a small type `Ω` of all mere propositions),
and `propext` plays the role of univalence restricted to
propositions; together they discharge the universal property,
including the uniqueness clause.

## Main definitions

- `GebLean.typesIsTerminalPUnit`: computable terminality of
  `PUnit` in `Type u`.
- `GebLean.typesTruth`, `GebLean.typesCharMap`: the truth
  morphism and the characteristic map.

## Main statements

- `GebLean.typesCharMap_apply_eq_true`: the characteristic map
  holds at image points.
- `GebLean.typesCharMap_isPullback`: the classifying pullback
  square.

## References

- [UF13] The Univalent Foundations Program, *Homotopy Type
  Theory: Univalent Foundations of Mathematics*, 2013,
  §10.1.4–10.1.5, Theorem 10.1.12.
- [MM92] S. MacLane and I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, §I.3–I.4.
-/

open CategoryTheory

namespace GebLean

universe u

/-- `PUnit` is terminal in `Type u`. Computable variant of
mathlib's `noncomputable` `Limits.Types.isTerminalPUnit`
(which routes through the choice-based `⊤_ (Type u)`). -/
def typesIsTerminalPUnit :
    Limits.IsTerminal (PUnit.{u + 1} : Type u) :=
  Limits.IsTerminal.ofUniqueHom (fun _ _ => PUnit.unit)
    (fun _ _ => funext fun _ => rfl)

/-- The truth morphism for the subobject classifier of
`Type u`: the point of `ULift Prop` selecting `True`. -/
def typesTruth : PUnit.{u + 1} ⟶ ULift.{u} Prop :=
  fun _ => ULift.up True

/-- The characteristic map of a morphism `m : U ⟶ X` in
`Type u`: membership in the image of `m`. -/
def typesCharMap {U X : Type u} (m : U ⟶ X) :
    X ⟶ ULift.{u} Prop :=
  fun x => ULift.up (∃ a, m a = x)

/-- The characteristic map of `m` holds at every image point:
`typesCharMap m (m a) = ULift.up True`. -/
theorem typesCharMap_apply_eq_true {U X : Type u} (m : U ⟶ X)
    (a : U) : typesCharMap m (m a) = ULift.up True :=
  congrArg ULift.up (eq_true ⟨a, rfl⟩)

/-- The classifying pullback square: a monomorphism `m` is the
pullback of `typesTruth` along its characteristic map. -/
theorem typesCharMap_isPullback {U X : Type u} (m : U ⟶ X)
    [Mono m] :
    IsPullback m (typesIsTerminalPUnit.from U)
      (typesCharMap m) typesTruth := by
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · funext a
    simp only [types_comp_apply]
    exact typesCharMap_apply_eq_true m a
  · rintro a b ⟨hm, -⟩
    exact (mono_iff_injective m).mp inferInstance hm
  · intro x p hx
    obtain ⟨a, ha⟩ := of_eq_true (congrArg ULift.down hx)
    exact ⟨a, ha, Subsingleton.elim _ _⟩

end GebLean
