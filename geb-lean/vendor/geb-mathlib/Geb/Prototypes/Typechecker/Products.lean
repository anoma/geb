/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker

set_option doc.verso true in
/-!
# Binary products of decision problems

A product is the language of encoded pairs of accepted inputs. Its projections
decode the components, and its universal map pairs the results of the two given
maps. Quotienting identifies maps exactly where the source accepts, so these
operations and their equations descend to morphisms.

The sufficient conditions separate decision procedures from output-producing
functions: admissible projections, closure under pairing two admissible outputs,
a decision checker recognizing pair codes, and closure of decision checkers under
conjunction. Composition supplies the checks of the decoded components.

The code check is necessary for this construction when the encoding is not
surjective: an accepted product input must be reconstructible from its projections.
No assumption that every base value is a pair code is imposed.

## Main definitions

* {lit}`ProductCoding` carries the encoding operations and closure conditions.
* {lit}`ProductCoding.product` checks a pair code and both decoded components.
* {lit}`ProductCoding.fst`, {lit}`ProductCoding.snd`, and {lit}`ProductCoding.lift`
  give the projections and pairing of quotient morphisms.

## Main statements

* {lit}`ProductCoding.product_pass_iff` characterizes the accepted product inputs.
* {lit}`ProductCoding.lift_fst` and {lit}`ProductCoding.lift_snd` are the projection laws.
* {lit}`ProductCoding.hom_ext` proves uniqueness from equality of both projections.
* {lit}`exists_injective_not_surjective` gives a necessary condition when an
  everywhere-accepting object has a product with itself.

## Complexity classes

Even total regular string functions, realized by deterministic two-way finite-state
transducers, suffice. Encode a pair as {lit}`escape(x) ++ 11 ++ escape(y)`, where
{lit}`escape` replaces bits zero and one by {lit}`00` and {lit}`01`. Decoding and
validity are finite-state operations. Closure under pointwise output concatenation
and composition supplies tupling; a test for the encoded pair of true values
supplies conjunction. These closure results are proved in
\[AlurFreilichRaghothaman2014\], Section III. This is an application of those
results to the criterion here, not a formal transducer instance.

For bitstrings, all total logspace transducers, with output space excluded from
the workspace bound, provide a sufficient standard benchmark. Composition closure
and a pairing with logspace decoding appear in \[CenzerDowneyRemmelUddin2008\],
Section 2 and page 12. From these algorithms, the conditions here follow by
combining output computations and checking code validity and conjunction.
This application is informal; no machine-class instance is constructed here.

Completeness for decision problems alone does not supply closure under pairing
outputs. Also, mere containment of logspace functions in a larger submonoid does
not establish that closure for its additional functions. No minimal complexity
class is claimed.

## References

* \[AlurFreilichRaghothaman2014\]
* \[CenzerDowneyRemmelUddin2008\]

## Tags

decision problem, binary product, pairing, quotient, closure
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

/-- Pair encoding, admissible decoding and tupling, and the decision operations needed to
recognize products. The checker for codes permits encodings with a proper subset as range. -/
@[ext]
structure ProductCoding (S : Submonoid (Function.End B)) (t f : B) : Type u where
  /-- Encode two base values as one. -/
  encode : B → B → B
  /-- Admissible first-component decoding, defined on the entire base. -/
  left : AdmissibleEndomorphism S
  /-- Admissible second-component decoding, defined on the entire base. -/
  right : AdmissibleEndomorphism S
  /-- Decode the first component of an encoded pair. -/
  left_encode : ∀ x y, left.val (encode x y) = x
  /-- Decode the second component of an encoded pair. -/
  right_encode : ∀ x y, right.val (encode x y) = y
  /-- Pairing the outputs of any two admissible endomorphisms is admissible. -/
  pair_mem : ∀ r s : S, (fun x ↦ encode (r.val x) (s.val x)) ∈ S
  /-- A decision procedure for valid pair codes. -/
  codes : DecisionProblem S t f
  /-- Valid codes are exactly the values reconstructed from their projections. -/
  codes_pass_iff : ∀ x, codes.checker.val x = t ↔ encode (left.val x) (right.val x) = x
  /-- A chosen admissible conjunction of two decision checkers. -/
  conjunction : DecisionProblem S t f → DecisionProblem S t f → DecisionProblem S t f
  /-- Conjunction accepts exactly the inputs accepted by both checkers. -/
  conjunction_pass_iff : ∀ X Y x,
    (conjunction X Y).checker.val x = t ↔ X.checker.val x = t ∧ Y.checker.val x = t

namespace ProductCoding

variable (d : ProductCoding S t f)

/-- A checker for valid pair codes whose decoded components pass the given checkers. -/
def product (X Y : DecisionProblem S t f) : DecisionProblem S t f :=
  d.conjunction d.codes (d.conjunction
    ⟨X.checker * d.left, X.twoValued.comp_right d.left.val⟩
    ⟨Y.checker * d.right, Y.twoValued.comp_right d.right.val⟩)

/-- Product membership requires a canonical pair code and acceptance of both components. -/
theorem product_pass_iff (X Y : DecisionProblem S t f) (x : B) :
    (d.product X Y).checker.val x = t ↔
      d.encode (d.left.val x) (d.right.val x) = x ∧
        X.checker.val (d.left.val x) = t ∧ Y.checker.val (d.right.val x) = t := by
  rw [product, d.conjunction_pass_iff, d.codes_pass_iff, d.conjunction_pass_iff]
  rfl

/-- An encoded pair is accepted exactly when its two components are accepted. -/
theorem encode_pass_iff (X Y : DecisionProblem S t f) (x y : B) :
    (d.product X Y).checker.val (d.encode x y) = t ↔
      X.checker.val x = t ∧ Y.checker.val y = t := by
  rw [d.product_pass_iff]
  simp only [d.left_encode, d.right_encode, true_and]

/-- The admissible first projection from the product language. -/
def fstRep (X Y : DecisionProblem S t f) : Representative (d.product X Y) X :=
  ⟨d.left, fun x hx ↦ ((d.product_pass_iff X Y x).mp hx).2.1⟩

/-- The admissible second projection from the product language. -/
def sndRep (X Y : DecisionProblem S t f) : Representative (d.product X Y) Y :=
  ⟨d.right, fun x hx ↦ ((d.product_pass_iff X Y x).mp hx).2.2⟩

/-- The first product projection as a quotient morphism. -/
def fst (X Y : DecisionProblem S t f) : d.product X Y ⟶ X := (d.fstRep X Y).toHom

/-- The second product projection as a quotient morphism. -/
def snd (X Y : DecisionProblem S t f) : d.product X Y ⟶ Y := (d.sndRep X Y).toHom

/-- Pair the outputs of two representatives on their common source. -/
def liftRep {Z X Y : DecisionProblem S t f} (r : Representative Z X) (s : Representative Z Y) :
    Representative Z (d.product X Y) :=
  ⟨⟨fun x ↦ d.encode (r.val.val x) (s.val.val x), d.pair_mem r.val s.val⟩, fun x hx ↦ by
    apply (d.product_pass_iff X Y _).mpr
    simp only [d.left_encode, d.right_encode]
    exact ⟨True.intro, r.property x hx, s.property x hx⟩⟩

/-- Pairing descends to the quotient because it respects agreement on accepted inputs. -/
def lift {Z X Y : DecisionProblem S t f} : (Z ⟶ X) → (Z ⟶ Y) → (Z ⟶ d.product X Y) :=
  Quotient.map₂ d.liftRep (fun r r' hr s s' hs ↦
    (homSetoid_iff _ _).mpr fun x hx ↦ congrArg₂ d.encode
      ((homSetoid_iff r r').mp hr x hx) ((homSetoid_iff s s').mp hs x hx))

/-- Pairing followed by first projection is the first given morphism. -/
@[simp]
theorem lift_fst {Z X Y : DecisionProblem S t f} (r : Z ⟶ X) (s : Z ⟶ Y) :
    d.lift r s ≫ d.fst X Y = r :=
  Quotient.inductionOn₂ r s fun r s ↦
    (Representative.toHom_eq_iff _ _).mpr fun x _ ↦ d.left_encode (r.val.val x) (s.val.val x)

/-- Pairing followed by second projection is the second given morphism. -/
@[simp]
theorem lift_snd {Z X Y : DecisionProblem S t f} (r : Z ⟶ X) (s : Z ⟶ Y) :
    d.lift r s ≫ d.snd X Y = s :=
  Quotient.inductionOn₂ r s fun r s ↦
    (Representative.toHom_eq_iff _ _).mpr fun x _ ↦ d.right_encode (r.val.val x) (s.val.val x)

/-- Two maps into the product are equal when both projections agree. -/
theorem hom_ext {Z X Y : DecisionProblem S t f} {r s : Z ⟶ d.product X Y}
    (hl : r ≫ d.fst X Y = s ≫ d.fst X Y) (hr : r ≫ d.snd X Y = s ≫ d.snd X Y) :
    r = s := by
  refine Quotient.inductionOn₂ r s (fun r s hl hr ↦ ?_) hl hr
  apply (Representative.toHom_eq_iff _ _).mpr
  intro x hx
  have hleft := (Representative.toHom_eq_iff _ _).mp hl x hx
  have hright := (Representative.toHom_eq_iff _ _).mp hr x hx
  exact ((d.product_pass_iff X Y _).mp (r.property x hx)).1.symm.trans
    ((congrArg₂ d.encode hleft hright).trans
      ((d.product_pass_iff X Y _).mp (s.property x hx)).1)

end ProductCoding

/-- Pairing maps into an everywhere-accepting object requires an admissible injection that
is not surjective. Only existence of pairing maps is used, not their uniqueness.
Pairing identity with constant true gives the injection; pairing identity with itself
produces a point outside its range by evaluating at false. -/
theorem exists_injective_not_surjective (U P : DecisionProblem S t f)
    (hU : ∀ x, U.checker.val x = t) (p q : P ⟶ U)
    (hlift : ∀ r s : U ⟶ U, ∃ m : U ⟶ P, m ≫ p = r ∧ m ≫ q = s) :
    ∃ r : S, Function.Injective r.val ∧ ¬Function.Surjective r.val := by
  refine Quotient.inductionOn₂ p q (fun p q hlift ↦ ?_) hlift
  let c : Representative U U := ⟨U.checker, fun x _ ↦ hU (U.checker.val x)⟩
  obtain ⟨r, hrp, hrq⟩ := hlift (𝟙 U) c.toHom
  obtain ⟨s, _, hsq⟩ := hlift (𝟙 U) (𝟙 U)
  refine Quotient.inductionOn₂ r s (fun r s hrp hrq hsq ↦ ?_) hrp hrq hsq
  have hp (x : B) : p.val.val (r.val.val x) = x :=
    (Representative.toHom_eq_iff _ _).mp hrp x (hU x)
  have hq (x : B) : q.val.val (r.val.val x) = t :=
    ((Representative.toHom_eq_iff _ _).mp hrq x (hU x)).trans (hU x)
  have hsq' : q.val.val (s.val.val f) = f :=
    (Representative.toHom_eq_iff _ _).mp hsq f (hU f)
  refine ⟨r.val, fun x y h ↦ (hp x).symm.trans ((congrArg p.val.val h).trans (hp y)), ?_⟩
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (s.val.val f)
  exact U.twoValued.1 ((hq x).symm.trans ((congrArg q.val.val hx).trans hsq'))

end GebProto.EndomorphismCategory.DecisionProblem
