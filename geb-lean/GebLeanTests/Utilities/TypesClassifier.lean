import GebLean.Utilities.TypesClassifier

/-!
# Tests for `GebLean.Utilities.TypesClassifier`
-/

open CategoryTheory
open GebLean

universe u

-- `typesCharMap` of the even-naturals inclusion holds at a
-- member.
example :
    typesCharMap
      (Subtype.val : {n : Nat // n % 2 = 0} → Nat) 4 =
      ULift.up True :=
  typesCharMap_apply_eq_true _
    (⟨4, rfl⟩ : {n : Nat // n % 2 = 0})

-- The characteristic map fails at a non-member.
example :
    typesCharMap
      (Subtype.val : {n : Nat // n % 2 = 0} → Nat) 3 =
      ULift.up False :=
  congrArg ULift.up (propext (iff_false_intro
    fun ⟨a, ha⟩ => Nat.one_ne_zero (by
      have hp := a.property
      rw [ha] at hp
      exact hp)))

-- `mkOfTerminalΩ₀` does not obscure the classifier data.
example : (typesClassifier : Classifier (Type u)).Ω =
    ULift.{u} Prop := rfl

example : (typesClassifier : Classifier (Type u)).truth =
    typesTruth.{u} := rfl

-- `sievePUnitEquiv` round trips on the extreme sieves.
example :
    (sievePUnitEquiv (Discrete.mk PUnit.unit)).symm
      (sievePUnitEquiv (Discrete.mk PUnit.unit) ⊤) = ⊤ :=
  (sievePUnitEquiv _).symm_apply_apply ⊤

example :
    (sievePUnitEquiv (Discrete.mk PUnit.unit)).symm
      (sievePUnitEquiv (Discrete.mk PUnit.unit) ⊥) = ⊥ :=
  (sievePUnitEquiv _).symm_apply_apply ⊥
