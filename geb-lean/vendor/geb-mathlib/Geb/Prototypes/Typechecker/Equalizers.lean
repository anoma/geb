/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker.Products

set_option doc.verso true in
/-!
# Equalizers of decision problems

An equalizer restricts a source checker to inputs on which two admissible functions
return the same value. Its inclusion is represented by identity, and a map that
equalizes the two functions factors through it using the same admissible endomorphism.
Thus the additional requirement concerns decision checkers, not output encodings.

Agreement is tested at the given input. Neither equality of functions on all inputs
nor an encoding of equality proofs is required. Acceptance and commutativity proofs
remain propositions in the metalanguage.

## Main definitions

* {lit}`EqualizerCheckers` supplies checkers for a source fiber intersected with the
  agreement set of two admissible functions.
* {lit}`EqualizerCheckers.equalizer` descends those checkers to quotient morphisms.
* {lit}`EqualizerCheckers.ι` and {lit}`EqualizerCheckers.lift` supply the inclusion
  and factorization maps.
* {lit}`EqualizerCheckers.ofProducts` reduces the condition to a checker for equality
  of encoded components when product coding is available.

## Main statements

* {lit}`EqualizerCheckers.equalizer_pass_iff` characterizes acceptance using the
  actions of the quotient morphisms on the source fiber.
* {lit}`EqualizerCheckers.condition`, {lit}`EqualizerCheckers.lift_ι`, and
  {lit}`EqualizerCheckers.hom_ext` prove the equalizer universal property.

## Complexity classes

All total logspace functions on bitstrings satisfy the condition: check source
acceptance and compare the two output streams symbol by symbol, rejecting a symbol
or length mismatch. Keeping the two simulations uses logarithmic workspace; their
outputs need not be stored. This uses the read-only input, write-only output model
of \[CenzerDowneyRemmelUddin2008\], Section 2. It is an algorithmic application,
not a formal machine-class instance.

The condition does not require pairing or any increase in output length. For a
logspace-sound algebra complete for logspace decision problems, it therefore
follows semantically even if the algebra is incomplete for general logspace
functions, provided its decision outputs use the designated truth values.

## References

* \[CenzerDowneyRemmelUddin2008\]

## Tags

decision problem, equalizer, output equality, quotient, logspace
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

/-- Decision checkers are closed under restriction to agreement of admissible outputs. -/
@[ext]
structure EqualizerCheckers (S : Submonoid (Function.End B)) (t f : B) : Type u where
  /-- Restrict a source checker to inputs on which the two functions agree. -/
  filter : DecisionProblem S t f → S → S → DecisionProblem S t f
  /-- Filtering accepts exactly the source inputs where the outputs are equal. -/
  filter_pass_iff : ∀ X r s x, (filter X r s).checker.val x = t ↔
    X.checker.val x = t ∧ r.val x = s.val x

namespace EqualizerCheckers

variable (d : EqualizerCheckers S t f)

/-- Changing the functions outside the source fiber does not change the filtered checker. -/
theorem filter_congr (X : DecisionProblem S t f) {r r' s s' : S}
    (hr : ∀ x, X.checker.val x = t → r.val x = r'.val x)
    (hs : ∀ x, X.checker.val x = t → s.val x = s'.val x) :
    d.filter X r s = d.filter X r' s' := by
  apply acceptedFiber_injective
  apply Set.ext
  intro x
  change (d.filter X r s).checker.val x = t ↔ (d.filter X r' s').checker.val x = t
  rw [d.filter_pass_iff, d.filter_pass_iff]
  exact and_congr_right fun hx ↦ by rw [hr x hx, hs x hx]

/-- The filtered checker depends only on the quotient morphisms, without choosing
representatives. Its behavior outside the source fiber is always rejection. -/
def equalizer {X Y : DecisionProblem S t f} : (X ⟶ Y) → (X ⟶ Y) → DecisionProblem S t f :=
  Quotient.lift₂ (fun r s ↦ d.filter X r.val s.val) (fun r s r' s' hr hs ↦
    d.filter_congr X ((homSetoid_iff r r').mp hr) ((homSetoid_iff s s').mp hs))

/-- Acceptance means source acceptance and equality of the two actions on that input. -/
theorem equalizer_pass_iff {X Y : DecisionProblem S t f} (r s : X ⟶ Y) (x : B) :
    (d.equalizer r s).checker.val x = t ↔
      ∃ hx : X.checker.val x = t, (r.restrict ⟨x, hx⟩).val = (s.restrict ⟨x, hx⟩).val := by
  refine Quotient.inductionOn₂ r s fun r s ↦ ?_
  change (d.filter X r.val s.val).checker.val x = t ↔ _
  rw [d.filter_pass_iff]
  exact ⟨fun ⟨hx, h⟩ ↦ ⟨hx, h⟩, fun ⟨hx, h⟩ ↦ ⟨hx, h⟩⟩

/-- Equalizing a morphism with itself leaves the source checker unchanged. -/
@[simp]
theorem equalizer_self {X Y : DecisionProblem S t f} (r : X ⟶ Y) : d.equalizer r r = X := by
  apply acceptedFiber_injective
  apply Set.ext
  intro x
  change (d.equalizer r r).checker.val x = t ↔ X.checker.val x = t
  rw [d.equalizer_pass_iff]
  exact ⟨fun ⟨hx, _⟩ ↦ hx, fun hx ↦ ⟨hx, rfl⟩⟩

/-- Identity on the base includes the filtered fiber in the source fiber. -/
def ιRep {X Y : DecisionProblem S t f} (r s : X ⟶ Y) :
    Representative (d.equalizer r s) X :=
  ⟨1, fun x hx ↦ ((d.equalizer_pass_iff r s x).mp hx).elim fun hx _ ↦ hx⟩

/-- The equalizer inclusion as a quotient morphism. -/
def ι {X Y : DecisionProblem S t f} (r s : X ⟶ Y) : d.equalizer r s ⟶ X :=
  (d.ιRep r s).toHom

/-- The inclusion equalizes the given parallel morphisms. -/
theorem condition {X Y : DecisionProblem S t f} (r s : X ⟶ Y) :
    d.ι r s ≫ r = d.ι r s ≫ s :=
  Quotient.inductionOn₂ r s fun r s ↦
    (Representative.toHom_eq_iff _ _).mpr fun x hx ↦
      ((d.filter_pass_iff X r.val s.val x).mp hx).2

/-- The inclusion detects equality of maps into the filtered fiber. -/
theorem hom_ext {X Y Z : DecisionProblem S t f} {r s : X ⟶ Y}
    {k l : Z ⟶ d.equalizer r s} (h : k ≫ d.ι r s = l ≫ d.ι r s) : k = l := by
  refine Quotient.inductionOn₂ k l (fun k l h ↦ ?_) h
  exact (Representative.toHom_eq_iff _ _).mpr
    ((Representative.toHom_eq_iff (k.comp (d.ιRep r s)) (l.comp (d.ιRep r s))).mp h)

/-- A representative equalizing the two maps already lands in the filtered fiber. -/
def liftRep {X Y Z : DecisionProblem S t f} (r s : X ⟶ Y) (k : Representative Z X)
    (h : k.toHom ≫ r = k.toHom ≫ s) : Representative Z (d.equalizer r s) :=
  ⟨k.val, fun x hx ↦ by
    revert h
    refine Quotient.inductionOn₂ r s fun r s h ↦ ?_
    exact (d.filter_pass_iff X r.val s.val _).mpr
      ⟨k.property x hx, (Representative.toHom_eq_iff _ _).mp h x hx⟩⟩

/-- Factorization together with its inclusion equation. Uniqueness lets the construction
descend through the quotient without selecting a representative. -/
def liftWithProof {X Y Z : DecisionProblem S t f} (r s : X ⟶ Y) (k : Z ⟶ X)
    (h : k ≫ r = k ≫ s) : { m : Z ⟶ d.equalizer r s // m ≫ d.ι r s = k } :=
  Quotient.recOnSubsingleton
    (h := fun _ ↦ ⟨fun a b ↦ funext fun h ↦
      Subtype.ext (d.hom_ext ((a h).property.trans (b h).property.symm))⟩) k
    (fun k h ↦ ⟨(d.liftRep r s k h).toHom, rfl⟩) h

/-- Factor through the equalizer using the same underlying admissible function. -/
def lift {X Y Z : DecisionProblem S t f} (r s : X ⟶ Y) (k : Z ⟶ X)
    (h : k ≫ r = k ≫ s) : Z ⟶ d.equalizer r s :=
  (d.liftWithProof r s k h).val

/-- The factorization recovers the original map after inclusion. -/
@[simp]
theorem lift_ι {X Y Z : DecisionProblem S t f} (r s : X ⟶ Y) (k : Z ⟶ X)
    (h : k ≫ r = k ≫ s) : d.lift r s k h ≫ d.ι r s = k :=
  (d.liftWithProof r s k h).property

/-- Pairing and conjunction reduce agreement filtering to an admissible decision procedure
for equality of encoded components. No condition is imposed on its other inputs. -/
def ofProducts (p : ProductCoding S t f) (D : DecisionProblem S t f)
    (hD : ∀ x y, D.checker.val (p.encode x y) = t ↔ x = y) : EqualizerCheckers S t f where
  filter X r s := p.conjunction X
    ⟨D.checker * ⟨fun x ↦ p.encode (r.val x) (s.val x), p.pair_mem r s⟩,
      D.twoValued.comp_right (fun x ↦ p.encode (r.val x) (s.val x))⟩
  filter_pass_iff X r s x := by
    rw [p.conjunction_pass_iff]
    exact and_congr_right' (hD (r.val x) (s.val x))

end EqualizerCheckers

end GebProto.EndomorphismCategory.DecisionProblem
