/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Finite.Basic

/-!
# Decidable W-type membership for finite presheaf polynomial endofunctors

For a finite presheaf polynomial endofunctor `F : FinitePresheafPFunctor I I`,
the `Bool`-valued validator `wValidBool` conjoins slice admissibility and
hereditary naturality, and `memWBool` adds the index test. Deciding
`PresheafPFunctor.MemW` — membership of a raw W-tree in the carrier presheaf's
fiber — is `memWBool`'s correctness lemma read through `decidable_of_iff`, so
the fiber is decided by a single fold. Forwarding instances supply the bundled
finiteness evidence to the existing decision procedures.

## Main definitions

* `FinitePresheafPFunctor.wValidBool` — the combined admissibility-and-naturality
  validator.
* `FinitePresheafPFunctor.memWBool` — the fiber-membership validator.
* `FinitePresheafPFunctor.decidableEqW` — `DecidableEq` on raw W-trees.
* `FinitePresheafPFunctor.decidableWValid` / `decidableIsHereditarilyNatural` /
  `decidableMemW` — forwarding instances for the endofunctor tier.

## Main statements

* `FinitePresheafPFunctor.wValidBool_eq_true_iff` — the validator returns `true`
  exactly on the admissible, hereditarily natural trees.
* `FinitePresheafPFunctor.memWBool_eq_true_iff` — `memWBool` decides
  `PresheafPFunctor.MemW`.

## Implementation notes

`wValidBool`'s first conjunct is load-bearing, not merely conjoined:
`PresheafPFunctor.isHereditarilyNaturalBoolCore` is a total fold that returns
`true` on an inadmissible tree, because the index guards at each node fail and
every conjunct is skipped. Its correctness lemma is correspondingly stated only
for admissible trees. Since `&&` evaluates its left argument first and both
folds are total, the conjunction is sound and order-independent.

## Tags

polynomial functor, presheaf, W-type, decidability, FinEnum
-/

public section

open CategoryTheory

universe uI uA uB vI

namespace FinitePresheafPFunctor

variable {I : Type uI} [Category.{vI} I]
    (F : FinitePresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)

/-- The combined `Bool`-valued validator for a finite presheaf polynomial
endofunctor: conjoins slice admissibility (`SlicePFunctor.wValidBool`) and
hereditary naturality (`PresheafPFunctor.isHereditarilyNaturalBoolCore`). -/
@[expose] def wValidBool : F.toPresheafPFunctor.toPFunctor.W → Bool :=
  fun w ↦ @SlicePFunctor.wValidBool I F.toPresheafPFunctor.toSlicePFunctor
      F.finitary F.decidableEqI w
    && F.toPresheafPFunctor.isHereditarilyNaturalBoolCore
      F.decidableEqI F.finEnumI F.finEnumHomI F.finitary
      (@WType.instDecidableEq _ _ F.decidableEqA F.finitary) w

/-- The validator returns `true` exactly on the trees that are admissible and,
as slice W-trees, hereditarily natural. -/
theorem wValidBool_eq_true_iff (w : F.toPresheafPFunctor.toPFunctor.W) :
    F.wValidBool w = true ↔
      ∃ hw : F.toPresheafPFunctor.toSlicePFunctor.WValid w,
        F.toPresheafPFunctor.IsHereditarilyNatural ⟨w, hw⟩ := by
  rw [wValidBool, Bool.and_eq_true]
  constructor
  · rintro ⟨hv, hn⟩
    have hw := (@SlicePFunctor.wValidBool_eq_true_iff I
      F.toPresheafPFunctor.toSlicePFunctor F.finitary F.decidableEqI w).mp hv
    exact ⟨hw, (F.toPresheafPFunctor.isHereditarilyNaturalBoolCore_eq_true_iff
      F.decidableEqI F.finEnumI F.finEnumHomI F.finitary
      (@WType.instDecidableEq _ _ F.decidableEqA F.finitary) ⟨w, hw⟩).mp hn⟩
  · rintro ⟨hw, hn⟩
    exact ⟨(@SlicePFunctor.wValidBool_eq_true_iff I
        F.toPresheafPFunctor.toSlicePFunctor F.finitary F.decidableEqI w).mpr hw,
      (F.toPresheafPFunctor.isHereditarilyNaturalBoolCore_eq_true_iff
        F.decidableEqI F.finEnumI F.finEnumHomI F.finitary
        (@WType.instDecidableEq _ _ F.decidableEqA F.finitary) ⟨w, hw⟩).mpr hn⟩

/-- The fiber-membership validator: the combined validator together with the
test that the tree's root index is `j`. -/
@[expose] def memWBool (j : I) (w : F.toPresheafPFunctor.toPFunctor.W) : Bool :=
  F.wValidBool w &&
    @decide _ (F.decidableEqI (F.toPresheafPFunctor.toSlicePFunctor.wIndexRoot w) j)

/-- `memWBool` decides membership in the carrier presheaf's fiber. -/
theorem memWBool_eq_true_iff (j : I) (w : F.toPresheafPFunctor.toPFunctor.W) :
    F.memWBool j w = true ↔ F.toPresheafPFunctor.MemW j w := by
  rw [memWBool, Bool.and_eq_true]
  constructor
  · rintro ⟨hv, hq⟩
    obtain ⟨hw, hn⟩ := (F.wValidBool_eq_true_iff w).mp hv
    exact ⟨hw, @of_decide_eq_true _ (F.decidableEqI _ j) hq, hn⟩
  · rintro ⟨hw, hq, hn⟩
    exact ⟨(F.wValidBool_eq_true_iff w).mpr ⟨hw, hn⟩,
      @decide_eq_true _ (F.decidableEqI _ j) hq⟩

/-- Admissibility of a raw W-tree is decidable for a finite presheaf polynomial
endofunctor: forwards to `SlicePFunctor.decidableWValid` with the bundled
finiteness evidence. -/
instance decidableWValid (w : F.toPresheafPFunctor.toPFunctor.W) :
    Decidable (F.toPresheafPFunctor.toSlicePFunctor.WValid w) :=
  @SlicePFunctor.decidableWValid I F.toPresheafPFunctor.toSlicePFunctor
    F.finitary F.decidableEqI w

/-- Hereditary naturality of an admissible W-tree is decidable for a finite
presheaf polynomial endofunctor: forwards to
`PresheafPFunctor.decidableIsHereditarilyNatural` with the bundled finiteness
evidence. The argument is typed as `SlicePFunctor.W`, matching the general-tier
instance and `IsHereditarilyNatural`'s own argument, rather than as the
underlying admissibility subtype. `SlicePFunctor.W` is a semireducible `def`,
which instance resolution does not unfold, so exactly one of the two spellings
can be matched and this is the one downstream goals are stated in. -/
instance decidableIsHereditarilyNatural
    (z : F.toPresheafPFunctor.toSlicePFunctor.W) :
    Decidable (F.toPresheafPFunctor.IsHereditarilyNatural z) :=
  @PresheafPFunctor.decidableIsHereditarilyNatural I _
    F.toPresheafPFunctor F.finitary F.finEnumI F.finEnumHomI
    F.decidableEqA z

set_option warn.classDefReducibility false in
/-- Decidable equality on raw W-trees of a finite presheaf polynomial
endofunctor: forwards to `WType.instDecidableEq` with the bundled shape
decidable equality and finitary direction evidence. -/
@[expose] def decidableEqW :
    DecidableEq (WType F.toPresheafPFunctor.toPFunctor.B) :=
  @WType.instDecidableEq _ _ F.decidableEqA F.finitary

/-- Membership of a raw W-tree in the carrier presheaf's fiber over `j` is
decidable: `memWBool`'s correctness lemma read through `decidable_of_iff`, so
the whole fiber condition is decided by a single fold. -/
instance decidableMemW (j : I) (w : F.toPresheafPFunctor.toPFunctor.W) :
    Decidable (F.toPresheafPFunctor.MemW j w) :=
  decidable_of_iff _ (F.memWBool_eq_true_iff j w)

end FinitePresheafPFunctor
