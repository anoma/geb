/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker.Initial
public import Geb.Prototypes.Typechecker.Products

set_option doc.verso true in
/-!
# Binary coproducts of decision problems

A coproduct accepts tagged inputs from either summand. Its universal map examines
the tag and applies the corresponding morphism to the payload. Admissible case
distinction is therefore a separate closure condition from pairing outputs.

The direct criterion needs only two admissible tags, closure of decision problems
under their tagged union, and admissible elimination of the tags. General pair
coding is one way to supply it, together with conditionals, both tag constants,
and singleton tests for both tags. The latter tests reject tags other than the
two distinguished values; the pair-code test rejects malformed codes.

## Main definitions

* {lit}`DecisionConditionals` expresses closure under branching on a decision procedure.
* {lit}`CoproductCoding` records admissible injections, tagged unions of decision
  problems, and elimination of tags by admissible functions.
* {lit}`CoproductCoding.ofProducts` constructs these data from product coding and
  the additional decision operations.

## Main statements

* {lit}`CoproductCoding.inl_desc` and {lit}`CoproductCoding.inr_desc` are the injection laws.
* {lit}`CoproductCoding.hom_ext` proves uniqueness of the map out of a coproduct.
* {lit}`exists_injective_not_surjective_of_copairing` gives a necessary condition
  when an everywhere-accepting object has a coproduct with itself.

## Complexity classes

For bitstrings, all total logspace transducers satisfy these sufficient conditions:
they can prepend and remove a tag, test it, and then run the selected computation.
The workspace excludes the output tape, as in \[CenzerDowneyRemmelUddin2008\],
Section 2. Fixed tags cost only a constant increase in length.

Even total regular string functions suffice for products and coproducts. The regular
combinators of \[AlurFreilichRaghothaman2014\], Sections II and III, include choice
and pointwise output concatenation. A regular decision function has regular accepted
and rejected languages; restricting each branch to the corresponding language and
using choice supplies the conditional. These are informal applications of the
published closure results, not formal machine-class instances or a minimality claim.

Containment of a standard function class alone does not establish closure under
conditionals on additional admissible functions. Also, even constant-size tagging
can be unavailable under an eventual non-size-increase bound: the necessary
injection condition here gives an obstruction independent of the chosen coding.

## References

* \[AlurFreilichRaghothaman2014\]
* \[CenzerDowneyRemmelUddin2008\]

## Tags

decision problem, binary coproduct, tagged union, conditional, closure
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

/-- Admissible functions can branch on any admissible decision procedure. Both branches
receive the original input, and their outputs need not be truth values. -/
@[ext]
structure DecisionConditionals (S : Submonoid (Function.End B)) (t f : B) : Type u where
  /-- Select between two admissible functions using a decision procedure. -/
  choose : DecisionProblem S t f → S → S → S
  /-- A successful test selects the first function. -/
  choose_true : ∀ p r s x, p.checker.val x = t → (choose p r s).val x = r.val x
  /-- A failed test selects the second function. -/
  choose_false : ∀ p r s x, p.checker.val x = f → (choose p r s).val x = s.val x

namespace DecisionConditionals

variable (c : DecisionConditionals S t f)

/-- Branching between decision checkers again gives a decision checker. -/
def chooseDecision (p X Y : DecisionProblem S t f) : DecisionProblem S t f :=
  ⟨c.choose p X.checker Y.checker, p.twoValued.1, fun x ↦ by
    rcases p.twoValued.2 x with hx | hx
    · rw [c.choose_true p X.checker Y.checker x hx]
      exact X.twoValued.2 x
    · rw [c.choose_false p X.checker Y.checker x hx]
      exact Y.twoValued.2 x⟩

/-- A conditional decision accepts exactly when its selected branch accepts. -/
theorem chooseDecision_pass_iff (p X Y : DecisionProblem S t f) (x : B) :
    (c.chooseDecision p X Y).checker.val x = t ↔
      (p.checker.val x = t ∧ X.checker.val x = t) ∨
        (p.checker.val x = f ∧ Y.checker.val x = t) := by
  rcases p.twoValued.2 x with hx | hx
  · change (c.choose p X.checker Y.checker).val x = t ↔ _
    rw [c.choose_true p X.checker Y.checker x hx]
    simp only [hx, p.twoValued.1, true_and, false_and, or_false]
  · change (c.choose p X.checker Y.checker).val x = t ↔ _
    rw [c.choose_false p X.checker Y.checker x hx]
    simp only [hx, p.twoValued.1.symm, true_and, false_and, false_or]

end DecisionConditionals

/-- Sufficient closure data for coproducts: admissible injections, decision procedures for
their tagged unions, and an admissible case operation on arbitrary admissible functions. -/
@[ext]
structure CoproductCoding (S : Submonoid (Function.End B)) (t f : B) : Type u where
  /-- Tag an input for the left summand. -/
  left : S
  /-- Tag an input for the right summand. -/
  right : S
  /-- A chosen decision procedure for the tagged union of two accepted fibers. -/
  coproduct : DecisionProblem S t f → DecisionProblem S t f → DecisionProblem S t f
  /-- Accepted inputs are exactly tagged accepted inputs from one of the summands. -/
  coproduct_pass_iff : ∀ X Y z, (coproduct X Y).checker.val z = t ↔
    (∃ x, X.checker.val x = t ∧ left.val x = z) ∨
      (∃ y, Y.checker.val y = t ∧ right.val y = z)
  /-- Apply the chosen branch to the payload of a tagged input. -/
  merge : S → S → S
  /-- A left-tagged input selects the first branch. -/
  merge_left : ∀ r s x, (merge r s).val (left.val x) = r.val x
  /-- A right-tagged input selects the second branch. -/
  merge_right : ∀ r s x, (merge r s).val (right.val x) = s.val x

namespace CoproductCoding

variable (d : CoproductCoding S t f)

/-- The admissible left injection into the tagged union. -/
def inlRep (X Y : DecisionProblem S t f) : Representative X (d.coproduct X Y) :=
  ⟨d.left, fun x hx ↦ (d.coproduct_pass_iff X Y _).mpr (Or.inl ⟨x, hx, rfl⟩)⟩

/-- The admissible right injection into the tagged union. -/
def inrRep (X Y : DecisionProblem S t f) : Representative Y (d.coproduct X Y) :=
  ⟨d.right, fun y hy ↦ (d.coproduct_pass_iff X Y _).mpr (Or.inr ⟨y, hy, rfl⟩)⟩

/-- The left coproduct injection as a quotient morphism. -/
def inl (X Y : DecisionProblem S t f) : X ⟶ d.coproduct X Y := (d.inlRep X Y).toHom

/-- The right coproduct injection as a quotient morphism. -/
def inr (X Y : DecisionProblem S t f) : Y ⟶ d.coproduct X Y := (d.inrRep X Y).toHom

/-- Merge representatives with the same target by applying the branch selected by the tag. -/
def descRep {X Y Z : DecisionProblem S t f} (r : Representative X Z) (s : Representative Y Z) :
    Representative (d.coproduct X Y) Z :=
  ⟨d.merge r.val s.val, fun z hz ↦ by
    rcases (d.coproduct_pass_iff X Y z).mp hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · rw [d.merge_left]
      exact r.property x hx
    · rw [d.merge_right]
      exact s.property y hy⟩

/-- Case distinction respects agreement on accepted inputs and descends to quotient maps. -/
def desc {X Y Z : DecisionProblem S t f} : (X ⟶ Z) → (Y ⟶ Z) → (d.coproduct X Y ⟶ Z) :=
  Quotient.map₂ d.descRep (fun r r' hr s s' hs ↦ (homSetoid_iff _ _).mpr fun z hz ↦ by
    rcases (d.coproduct_pass_iff X Y z).mp hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · change (d.merge r.val s.val).val _ = (d.merge r'.val s'.val).val _
      rw [d.merge_left, d.merge_left]
      exact (homSetoid_iff r r').mp hr x hx
    · change (d.merge r.val s.val).val _ = (d.merge r'.val s'.val).val _
      rw [d.merge_right, d.merge_right]
      exact (homSetoid_iff s s').mp hs y hy)

/-- Left injection followed by the universal map is the first given morphism. -/
@[simp]
theorem inl_desc {X Y Z : DecisionProblem S t f} (r : X ⟶ Z) (s : Y ⟶ Z) :
    d.inl X Y ≫ d.desc r s = r :=
  Quotient.inductionOn₂ r s fun r s ↦
    (Representative.toHom_eq_iff _ _).mpr fun x _ ↦ d.merge_left r.val s.val x

/-- Right injection followed by the universal map is the second given morphism. -/
@[simp]
theorem inr_desc {X Y Z : DecisionProblem S t f} (r : X ⟶ Z) (s : Y ⟶ Z) :
    d.inr X Y ≫ d.desc r s = s :=
  Quotient.inductionOn₂ r s fun r s ↦
    (Representative.toHom_eq_iff _ _).mpr fun y _ ↦ d.merge_right r.val s.val y

/-- Two maps out of the coproduct are equal when they agree on both injections. -/
theorem hom_ext {X Y Z : DecisionProblem S t f} {r s : d.coproduct X Y ⟶ Z}
    (hl : d.inl X Y ≫ r = d.inl X Y ≫ s) (hr : d.inr X Y ≫ r = d.inr X Y ≫ s) :
    r = s := by
  refine Quotient.inductionOn₂ r s (fun r s hl hr ↦ ?_) hl hr
  apply (Representative.toHom_eq_iff _ _).mpr
  intro z hz
  rcases (d.coproduct_pass_iff X Y z).mp hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · exact (Representative.toHom_eq_iff _ _).mp hl x hx
  · exact (Representative.toHom_eq_iff _ _).mp hr y hy

end CoproductCoding

namespace ProductCoding

variable (d : ProductCoding S t f) (c : DecisionConditionals S t f)
  (T F : DecisionProblem S t f) (hf : (fun _ : B ↦ f) ∈ S)

/-- Check a pair code, use the first component as a tag, and check the second component
against the selected summand. Tags passing neither tag test are rejected. -/
def taggedUnion (X Y : DecisionProblem S t f) : DecisionProblem S t f :=
  d.conjunction d.codes (c.chooseDecision
    ⟨T.checker * d.left, T.twoValued.comp_right d.left.val⟩
    ⟨X.checker * d.right, X.twoValued.comp_right d.right.val⟩
    (c.chooseDecision
      ⟨F.checker * d.left, F.twoValued.comp_right d.left.val⟩
      ⟨Y.checker * d.right, Y.twoValued.comp_right d.right.val⟩
      (rejectAll ⟨d.codes.twoValued.1, hf⟩)))

/-- Singleton tests for the two tags make the accepted inputs exactly tagged accepted
payloads from the respective summands. Invalid pair codes and other tags are rejected. -/
theorem taggedUnion_pass_iff
    (hT : ∀ x, T.checker.val x = t ↔ x = t) (hF : ∀ x, F.checker.val x = t ↔ x = f)
    (X Y : DecisionProblem S t f) (z : B) :
    (d.taggedUnion c T F hf X Y).checker.val z = t ↔
      (∃ x, X.checker.val x = t ∧ d.encode t x = z) ∨
        (∃ y, Y.checker.val y = t ∧ d.encode f y = z) := by
  have hTf : T.checker.val f = f := by
    rcases T.twoValued.2 f with h | h
    · exact False.elim (T.twoValued.1 ((hT f).mp h).symm)
    · exact h
  rw [taggedUnion, d.conjunction_pass_iff, d.codes_pass_iff,
    c.chooseDecision_pass_iff, c.chooseDecision_pass_iff]
  change (d.encode (d.left.val z) (d.right.val z) = z ∧
    ((T.checker.val (d.left.val z) = t ∧ X.checker.val (d.right.val z) = t) ∨
      (T.checker.val (d.left.val z) = f ∧
        ((F.checker.val (d.left.val z) = t ∧ Y.checker.val (d.right.val z) = t) ∨
          (F.checker.val (d.left.val z) = f ∧ f = t))))) ↔ _
  constructor
  · rintro ⟨hz, h⟩
    rcases h with ⟨ht, hx⟩ | ⟨_, ⟨hf, hy⟩ | ⟨_, hft⟩⟩
    · refine Or.inl ⟨d.right.val z, hx, ?_⟩
      simpa only [(hT _).mp ht] using hz
    · refine Or.inr ⟨d.right.val z, hy, ?_⟩
      simpa only [(hF _).mp hf] using hz
    · exact False.elim (T.twoValued.1 hft.symm)
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · simp only [d.left_encode, d.right_encode]
      exact ⟨True.intro, Or.inl ⟨(hT t).mpr rfl, hx⟩⟩
    · simp only [d.left_encode, d.right_encode]
      exact ⟨True.intro, Or.inr ⟨hTf, Or.inl ⟨(hF f).mpr rfl, hy⟩⟩⟩

end ProductCoding

/-- Product coding gives coproduct coding when admissible functions include the two tag
constants, singleton tests for both tags, and conditionals on decision procedures. -/
def CoproductCoding.ofProducts (d : ProductCoding S t f) (c : DecisionConditionals S t f)
    (T F : DecisionProblem S t f)
    (hT : ∀ x, T.checker.val x = t ↔ x = t) (hF : ∀ x, F.checker.val x = t ↔ x = f)
    (ht : (fun _ : B ↦ t) ∈ S) (hf : (fun _ : B ↦ f) ∈ S) : CoproductCoding S t f := by
  have hTf : T.checker.val f = f := by
    rcases T.twoValued.2 f with h | h
    · exact False.elim (T.twoValued.1 ((hT f).mp h).symm)
    · exact h
  exact {
    left := ⟨fun x ↦ d.encode t x, d.pair_mem ⟨_, ht⟩ 1⟩
    right := ⟨fun x ↦ d.encode f x, d.pair_mem ⟨_, hf⟩ 1⟩
    coproduct := d.taggedUnion c T F hf
    coproduct_pass_iff := d.taggedUnion_pass_iff c T F hf hT hF
    merge := fun r s ↦ c.choose
      ⟨T.checker * d.left, T.twoValued.comp_right d.left.val⟩
      (r * d.right) (s * d.right)
    merge_left := fun r s x ↦ by
      rw [c.choose_true]
      · exact congrArg r.val (d.right_encode t x)
      · change T.checker.val (d.left.val (d.encode t x)) = t
        rw [d.left_encode]
        exact (hT t).mpr rfl
    merge_right := fun r s x ↦ by
      rw [c.choose_false]
      · exact congrArg s.val (d.right_encode f x)
      · change T.checker.val (d.left.val (d.encode f x)) = f
        rw [d.left_encode]
        exact hTf }

/-- Copairing maps out of an everywhere-accepting object requires an admissible injection
that is not surjective. Only existence of copairing maps is used. Copairing two identities
gives a left inverse to the first injection; copairing identity with constant true
separates the two injections at false. -/
theorem exists_injective_not_surjective_of_copairing (U P : DecisionProblem S t f)
    (hU : ∀ x, U.checker.val x = t) (i j : U ⟶ P)
    (hdesc : ∀ r s : U ⟶ U, ∃ m : P ⟶ U, i ≫ m = r ∧ j ≫ m = s) :
    ∃ r : S, Function.Injective r.val ∧ ¬Function.Surjective r.val := by
  refine Quotient.inductionOn₂ i j (fun i j hdesc ↦ ?_) hdesc
  let c : Representative U U := ⟨U.checker, fun x _ ↦ hU (U.checker.val x)⟩
  obtain ⟨r, hir, hjr⟩ := hdesc (𝟙 U) (𝟙 U)
  obtain ⟨s, his, hjs⟩ := hdesc (𝟙 U) c.toHom
  refine Quotient.inductionOn₂ r s (fun r s hir hjr his hjs ↦ ?_) hir hjr his hjs
  have hr (x : B) : r.val.val (i.val.val x) = x :=
    (Representative.toHom_eq_iff _ _).mp hir x (hU x)
  have hs (x : B) : s.val.val (i.val.val x) = x :=
    (Representative.toHom_eq_iff _ _).mp his x (hU x)
  have hrf : r.val.val (j.val.val f) = f :=
    (Representative.toHom_eq_iff _ _).mp hjr f (hU f)
  have hsf : s.val.val (j.val.val f) = t :=
    ((Representative.toHom_eq_iff _ _).mp hjs f (hU f)).trans (hU f)
  refine ⟨i.val, fun x y h ↦ (hr x).symm.trans ((congrArg r.val.val h).trans (hr y)), ?_⟩
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (j.val.val f)
  have hxt : x = t := (hs x).symm.trans ((congrArg s.val.val hx).trans hsf)
  have hxf : x = f := (hr x).symm.trans ((congrArg r.val.val hx).trans hrf)
  exact U.twoValued.1 (hxt.symm.trans hxf)

end GebProto.EndomorphismCategory.DecisionProblem
