/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker.Products


set_option doc.verso true in
/-!
# Exponentials from extensional function codes

Accepted codes describe functions on an accepted argument fiber. Evaluation must
be admissible, as must the production of a code when parameters of an admissible
function are fixed. Codes are extensional: codes with the same values on every
accepted argument are equal as base values. This last condition supplies
uniqueness of currying and its independence from morphism representatives.

## Main definitions

* {lit}`ExponentialCoding` gives evaluation, admissible parameter abstraction,
  and extensionality for a proposed exponential.
* {lit}`ExponentialCoding.homEquiv` is the currying equivalence.
* {lit}`singletonExponentialCoding` codes functions from a singleton by their values.

## Main statements

* {lit}`ExponentialCoding.uncurry_curry` and {lit}`ExponentialCoding.curry_uncurry`
  prove the exponential universal property.
* {lit}`ExponentialCoding.curry_natural` supplies the naturality used to construct
  the right adjoint in the instance wrapper.
* {lit}`exists_fixed_point_of_evaluation` is the diagonal obstruction to an
  admissible universal evaluator for the admissible endomorphisms themselves.
* {lit}`exists_fixed_point_of_exponential` derives the same obstruction from
  any exponential of an everywhere-accepting object into itself.

## Implementation notes

The structure is a sufficient condition for each pair of objects separately.
It asks for equality of codes only when their evaluations agree on the accepted
argument fiber. It does not ask for equality of the underlying total functions
outside that fiber. Quotienting morphisms alone cannot identify distinct codes
as elements of the exponential object. With all constants admissible, the
uniqueness part of the exponential property forces this extensionality of codes.

Representing functions with an external interpretation is weaker than admitting
that interpretation as a morphism. If {lit}`eval(encode(x, c))` enumerates every
admissible endomorphism, then for any admissible {lit}`a` the diagonal function
{lit}`x ↦ a(eval(encode(x, x)))` is admissible. Applying its code to itself gives
a fixed point of {lit}`a`. This is the restricted-function form of the diagonal
argument of \[Lawvere1969\], Section 1. The proof only needs existence of
codes, not their uniqueness or a decision procedure recognizing them.

An exponential of an everywhere-accepting object {lit}`U` into itself would give
such an evaluator: transpose an admissible function ignoring its parameter and
evaluate the transpose at a fixed accepted parameter. Every admissible function
would consequently have a fixed point. In particular, an admissible function
without fixed points prevents this exponential and hence cartesian closure.

## Complexity classes

For bitstrings, prepending a bit has no fixed point and is a total regular
function, hence also logspace. Together with the product coding and constant-true
checker, its admissibility triggers the formal obstruction above. Full logspace
functions, all total computable functions, and even all set-theoretic
endomorphisms therefore fail to provide all exponentials in this fixed-base
category. Enlarging the complexity bound does not repair this obstruction.

Restricted exponents can still satisfy the criterion. For a fixed finite argument
fiber, a code can list one output for each argument, in a fixed order. Checking
the table and evaluating it use finitely many equality and checker tests;
abstraction runs the given function at each of these finitely many arguments.
With standard string encodings, full logspace functions suffice for these
operations. This finite-table complexity claim is informal; the singleton case
and the abstract criterion are formalized here.

## References

* \[Lawvere1969\]

## Tags

decision problem, exponential, function code, evaluation, currying
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

/-- An admissible language of extensional codes, with evaluation and closure under
parameter abstraction. The first component of a pair is the function argument. -/
@[ext]
structure ExponentialCoding (p : ProductCoding S t f) (X Y : DecisionProblem S t f) :
    Type u where
  /-- The decision problem recognizing function codes. -/
  codes : DecisionProblem S t f
  /-- Admissible evaluation on accepted arguments and accepted codes. -/
  eval : Representative (p.product X codes) Y
  /-- Fixing the second argument produces an admissible map into function codes. -/
  curryRep : ∀ {Z : DecisionProblem S t f}, Representative (p.product X Z) Y →
    Representative Z codes
  /-- Evaluating an abstracted function recovers its action on accepted pairs. -/
  eval_curry : ∀ {Z} (h : Representative (p.product X Z) Y) x z,
    X.checker.val x = t → Z.checker.val z = t →
      eval.val.val (p.encode x ((curryRep h).val.val z)) = h.val.val (p.encode x z)
  /-- Accepted codes agreeing on all accepted arguments are the same base value. -/
  codes_ext : ∀ c c', codes.checker.val c = t → codes.checker.val c' = t →
    (∀ x, X.checker.val x = t → eval.val.val (p.encode x c) =
      eval.val.val (p.encode x c')) → c = c'

namespace ExponentialCoding

variable {p : ProductCoding S t f} {X Y Z : DecisionProblem S t f}
  (d : ExponentialCoding p X Y)

/-- Extensionally equal maps produce equal codes on every accepted parameter. -/
theorem curryRep_congr (h k : Representative (p.product X Z) Y)
    (hk : (homSetoid _ _) h k) : (homSetoid _ _) (d.curryRep h) (d.curryRep k) := by
  apply (homSetoid_iff _ _).mpr
  intro z hz
  apply d.codes_ext _ _ ((d.curryRep h).property z hz) ((d.curryRep k).property z hz)
  intro x hx
  rw [d.eval_curry h x z hx hz, d.eval_curry k x z hx hz]
  exact (homSetoid_iff _ _).mp hk _ ((p.encode_pass_iff X Z x z).mpr ⟨hx, hz⟩)

/-- Parameter abstraction descends to quotient morphisms. -/
def curry : (p.product X Z ⟶ Y) → (Z ⟶ d.codes) :=
  Quotient.map d.curryRep d.curryRep_congr

/-- Apply a code-producing representative to the second component, then evaluate. -/
def uncurryRep (k : Representative Z d.codes) : Representative (p.product X Z) Y :=
  ((p.liftRep (p.fstRep X Z) ((p.sndRep X Z).comp k)).comp d.eval)

/-- Uncurrying is product substitution followed by evaluation. -/
def uncurry (k : Z ⟶ d.codes) : p.product X Z ⟶ Y :=
  p.lift (p.fst X Z) (p.snd X Z ≫ k) ≫ d.eval.toHom

/-- Evaluating a curried map recovers the original morphism. -/
@[simp]
theorem uncurry_curry (h : p.product X Z ⟶ Y) : d.uncurry (d.curry h) = h := by
  refine Quotient.inductionOn h fun h ↦ ?_
  apply (Representative.toHom_eq_iff _ _).mpr
  intro z hz
  obtain ⟨hcode, hx, hz⟩ := (p.product_pass_iff X Z z).mp hz
  change d.eval.val.val (p.encode (p.left.val z)
    ((d.curryRep h).val.val (p.right.val z))) = h.val.val z
  rw [d.eval_curry h _ _ hx hz, hcode]

/-- Extensionality of codes makes currying inverse to evaluation. -/
@[simp]
theorem curry_uncurry (k : Z ⟶ d.codes) : d.curry (d.uncurry k) = k := by
  refine Quotient.inductionOn k fun k ↦ ?_
  change (d.curryRep (d.uncurryRep k)).toHom = k.toHom
  apply (Representative.toHom_eq_iff _ _).mpr
  intro z hz
  apply d.codes_ext _ _ ((d.curryRep (d.uncurryRep k)).property z hz) (k.property z hz)
  intro x hx
  rw [d.eval_curry _ x z hx hz]
  change d.eval.val.val (p.encode (p.left.val (p.encode x z))
    (k.val.val (p.right.val (p.encode x z)))) = _
  rw [p.left_encode, p.right_encode]

/-- The hom-set equivalence expressing the exponential universal property. -/
def homEquiv : (p.product X Z ⟶ Y) ≃ (Z ⟶ d.codes) where
  toFun := d.curry
  invFun := d.uncurry
  left_inv := d.uncurry_curry
  right_inv := d.curry_uncurry

/-- Evaluation commutes with substitution in the parameter. -/
theorem uncurry_natural {Z' : DecisionProblem S t f} (g : Z' ⟶ Z) (k : Z ⟶ d.codes) :
    d.uncurry (g ≫ k) = p.lift (p.fst X Z') (p.snd X Z' ≫ g) ≫ d.uncurry k := by
  refine Quotient.inductionOn₂ g k fun g k ↦ ?_
  apply (Representative.toHom_eq_iff _ _).mpr
  intro z _
  change d.eval.val.val (p.encode (p.left.val z) (k.val.val (g.val.val (p.right.val z)))) =
    d.eval.val.val (p.encode (p.left.val (p.encode (p.left.val z)
      (g.val.val (p.right.val z)))) (k.val.val (p.right.val
        (p.encode (p.left.val z) (g.val.val (p.right.val z))))))
  rw [p.left_encode, p.right_encode]

/-- Currying is natural in the parameter object, as required by the adjunction constructor. -/
theorem curry_natural {Z' : DecisionProblem S t f} (g : Z' ⟶ Z)
    (h : p.product X Z ⟶ Y) :
    d.curry (p.lift (p.fst X Z') (p.snd X Z' ≫ g) ≫ h) = g ≫ d.curry h := by
  apply d.homEquiv.symm.injective
  change d.uncurry (d.curry _) = d.uncurry (g ≫ d.curry h)
  rw [d.uncurry_curry, d.uncurry_natural, d.uncurry_curry]

end ExponentialCoding

/-- A singleton argument fiber has the codomain itself as its function-code language,
provided the singleton value is an admissible constant. -/
def singletonExponentialCoding (p : ProductCoding S t f) (X Y : DecisionProblem S t f)
    (a : B) (hX : ∀ x, X.checker.val x = t ↔ x = a) (ha : (fun _ : B ↦ a) ∈ S) :
    ExponentialCoding p X Y where
  codes := Y
  eval := p.sndRep X Y
  curryRep h :=
    ⟨h.val * ⟨fun z ↦ p.encode a z, p.pair_mem ⟨_, ha⟩ 1⟩, fun z hz ↦
      h.property _ ((p.encode_pass_iff X _ a z).mpr ⟨(hX a).mpr rfl, hz⟩)⟩
  eval_curry h x z hx _ := by
    change p.right.val (p.encode x (h.val.val (p.encode a z))) = h.val.val (p.encode x z)
    rw [p.right_encode, (hX x).mp hx]
  codes_ext c c' _ _ he := by
    have h := he a ((hX a).mpr rfl)
    change p.right.val (p.encode a c) = p.right.val (p.encode a c') at h
    simpa only [p.right_encode] using h

/-- A universal admissible evaluator, together with admissible diagonal pairing,
forces every admissible endomorphism to have a fixed point. -/
theorem exists_fixed_point_of_evaluation (encode : B → B → B)
    (hdiag : (fun x ↦ encode x x) ∈ S) (eval : S)
    (complete : ∀ r : S, ∃ c : B, ∀ x, eval.val (encode x c) = r.val x) (a : S) :
    ∃ y, a.val y = y := by
  obtain ⟨c, hc⟩ := complete (a * eval * ⟨_, hdiag⟩)
  exact ⟨eval.val (encode c c), (hc c).symm⟩

/-- An exponential of the everywhere-accepting object into itself supplies a universal
evaluator. Only existence of transposes is used, without uniqueness or canonical codes. -/
theorem exists_fixed_point_of_exponential (p : ProductCoding S t f)
    (U E : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t)
    (eval : p.product U E ⟶ U)
    (transpose : ∀ h : p.product U U ⟶ U, ∃ k : U ⟶ E,
      p.lift (p.fst U U) (p.snd U U ≫ k) ≫ eval = h) (a : S) : ∃ y, a.val y = y := by
  refine Quotient.inductionOn eval (fun eval transpose ↦ ?_) transpose
  apply exists_fixed_point_of_evaluation p.encode (p.pair_mem 1 1) eval.val _ a
  intro r
  let h : Representative (p.product U U) U := ⟨r * p.left, fun x _ ↦ hU _⟩
  obtain ⟨k, hk⟩ := transpose h.toHom
  refine Quotient.inductionOn k (fun k hk ↦ ?_) hk
  refine ⟨k.val.val t, fun x ↦ ?_⟩
  have he := (Representative.toHom_eq_iff _ _).mp hk (p.encode x t)
    ((p.encode_pass_iff U U x t).mpr ⟨hU x, hU t⟩)
  change eval.val.val (p.encode (p.left.val (p.encode x t))
    (k.val.val (p.right.val (p.encode x t)))) = r.val (p.left.val (p.encode x t)) at he
  simpa only [p.left_encode, p.right_encode] using he

/-- A fixed-point-free admissible function rules out extensional coding of all
endomorphisms of the everywhere-accepting object. -/
theorem not_nonempty_exponentialCoding_self (p : ProductCoding S t f)
    (U : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t)
    (a : S) (ha : ∀ y, a.val y ≠ y) : ¬Nonempty (ExponentialCoding p U U) := by
  rintro ⟨d⟩
  obtain ⟨y, hy⟩ := exists_fixed_point_of_exponential p U d.codes hU d.eval.toHom
    (fun h ↦ ⟨d.curry h, d.uncurry_curry h⟩) a
  exact ha y hy

end GebProto.EndomorphismCategory.DecisionProblem
