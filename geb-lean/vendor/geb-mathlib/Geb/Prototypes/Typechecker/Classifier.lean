/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker
public import Mathlib.CategoryTheory.EpiMono

set_option doc.verso true in
/-!
# Subobject classification by admissible image tests

A characteristic map decides membership in the image of a monomorphism. To make
its square a pullback in the decision-problem category, an accepted image value
must also have an admissibly recoverable preimage. These are separate conditions:
an image test supplies the characteristic map, and an admissible inverse on the
image supplies pullback lifts.

## Main definitions

* {lit}`HasConstants` makes every accepted value available as a constant morphism.
* {lit}`MonoImage` records an image checker and an admissible inverse on that image.
* {lit}`ClassifierData` supplies the truth-value objects and images of monomorphisms.

## Main statements

* {lit}`mono_iff_injective` identifies monomorphisms with injections on accepted fibers
  when all constants are admissible.
* {lit}`ClassifierData.liftWithProof` factors maps through a mono using its image inverse.
* {lit}`ClassifierData.chi_unique` determines a characteristic map from its true fiber.
* {lit}`ClassifierData.exists_fixed_point_free` derives an endomorphism without fixed
  points from the image checker of the false singleton.

## Necessity and complexity

The instance wrapper proves {lit}`exists_image_test_of_classifier`: with all constants
admissible and an inhabited accepted fiber, every monomorphism's image, on accepted
target inputs, is the equality fiber of an admissible endomorphism at a fixed base value.
This holds for any classifier, with no restriction to two truth values. For computable
string functions, such an equality test is computable.

Consider the language of canonical complete halting histories of a fixed deterministic
universal machine. Require the initial configuration to contain the input, unique
configuration encodings, and termination at the first halting configuration. Checking
a supplied history and extracting its input are logspace operations on the supplied
string. The extraction is injective on accepted histories, since a halting input has
exactly one such history. Its image is the undecidable halting language.

Consequently, the full logspace function class and the class of all total computable
string functions have no subobject classifier here. More generally this excludes any
computable submonoid containing the history checker, input extraction, and all constants.
This is an informal application of the formal image-test theorem; the machine encoding
and its space analysis are not formalized in this module. Certificate validation alone
does not decide whether a certificate exists, even when certificates are unique.

The sufficient condition is stronger than image recognition alone: the image inverse
must also extend to an admissible total endomorphism. Arbitrary set-theoretic functions
on a base with two distinct values satisfy this condition classically: use image
indicators and the unique inverse of an injection on its image, extended by a default
value elsewhere. This observation is separate from the obstruction to exponentials.

## Tags

decision problem, subobject classifier, image, inverse, pullback
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}
  {X Y Z : DecisionProblem S t f}

/-- Every constant endomorphism is admissible. -/
def HasConstants (S : Submonoid (Function.End B)) : Prop := ∀ b : B, (fun _ ↦ b) ∈ S

/-- An accepted value defines a constant representative from any source. -/
def constantRep (h : HasConstants S) (X : DecisionProblem S t f) (y : Fiber Y) :
    Representative X Y := ⟨⟨fun _ ↦ y.val, h y.val⟩, fun _ _ ↦ y.property⟩

/-- Injectivity on the accepted fiber suffices for a categorical monomorphism. -/
theorem mono_of_injective (m : X ⟶ Y) (hm : Function.Injective m.restrict) : Mono m := by
  constructor
  intro Z k l h
  apply Hom.ext
  funext z
  apply hm
  have he := congrArg (fun r : Z ⟶ Y ↦ r.restrict z) h
  simpa only [Hom.restrict_comp, Function.comp_apply] using he

/-- With all constants admissible, monomorphisms are precisely injections on accepted fibers. -/
theorem mono_iff_injective (h : HasConstants S) (m : X ⟶ Y) :
    Mono m ↔ Function.Injective m.restrict := by
  constructor
  · intro hm
    let := hm
    intro x x' he
    have hw : (constantRep h X x).toHom ≫ m = (constantRep h X x').toHom ≫ m := by
      apply Hom.ext
      funext z
      simp only [Hom.restrict_comp, Function.comp_apply]
      exact he
    have hc := (cancel_mono m).mp hw
    exact congrArg (fun r : X ⟶ X ↦ r.restrict x) hc
  · exact mono_of_injective m

/-- An admissible image checker and an admissible inverse defined on its accepted fiber.
The inverse's total representative may act arbitrarily outside the image. -/
@[ext]
structure MonoImage (m : X ⟶ Y) : Type u where
  /-- A decision problem accepting exactly the image of the source fiber. -/
  image : DecisionProblem S t f
  /-- Acceptance is existence of an accepted preimage. -/
  pass_iff : ∀ y : B, image.checker.val y = t ↔ ∃ x : Fiber X, (m.restrict x).val = y
  /-- An admissible map recovering a preimage of every accepted image value. -/
  inverse : Representative image X
  /-- The recovered preimage maps back to the given image value. -/
  inverse_spec : ∀ y : Fiber image, (m.restrict (inverse.restrict y)).val = y.val

/-- Sufficient computational data for a two-valued subobject classifier. -/
@[ext]
structure ClassifierData (S : Submonoid (Function.End B)) (t f : B) : Type u where
  /-- All accepted points are accessible by admissible constants. -/
  constants : HasConstants S
  /-- The singleton decision problem used as the terminal object. -/
  terminal : DecisionProblem S t f
  /-- The terminal checker accepts exactly true. -/
  terminal_pass_iff : ∀ x, terminal.checker.val x = t ↔ x = t
  /-- The decision problem whose elements are the two truth values. -/
  omega : DecisionProblem S t f
  /-- Both truth values, and only those values, are accepted by the classifier object. -/
  omega_pass_iff : ∀ x, omega.checker.val x = t ↔ x = t ∨ x = f
  /-- Every categorical monomorphism has an admissible image test and inverse on its image. -/
  monoImage : ∀ {X Y : DecisionProblem S t f} (m : X ⟶ Y) [Mono m], MonoImage m

namespace ClassifierData

variable (d : ClassifierData S t f)

/-- The source checker maps every accepted input to the terminal true value. -/
def toTerminal (X : DecisionProblem S t f) : X ⟶ d.terminal :=
  Representative.toHom ⟨X.checker, fun _ hx ↦ (d.terminal_pass_iff _).mpr hx⟩

/-- Inclusion of true into the two truth values. -/
def truth : d.terminal ⟶ d.omega :=
  Representative.toHom ⟨1, fun x hx ↦ (d.omega_pass_iff x).mpr
    (Or.inl ((d.terminal_pass_iff x).mp hx))⟩

/-- An admissible image checker, regarded as a map to the truth-value object. -/
def chi (m : X ⟶ Y) [Mono m] : Y ⟶ d.omega :=
  Representative.toHom ⟨(d.monoImage m).image.checker, fun y _ ↦
    (d.omega_pass_iff _).mpr ((d.monoImage m).image.twoValued.2 y)⟩

/-- The image checker is true on the monomorphism's image. -/
theorem condition (m : X ⟶ Y) [Mono m] : m ≫ d.chi m = d.toTerminal X ≫ d.truth := by
  apply Hom.ext
  funext x
  simp only [Hom.restrict_comp, Function.comp_apply]
  apply Subtype.ext
  exact ((d.monoImage m).pass_iff _).mpr ⟨x, rfl⟩ |>.trans x.property.symm

/-- A map whose accepted outputs belong to the image factors through its admissible inverse. -/
def liftRep (m : X ⟶ Y) [Mono m] (k : Representative Z Y)
    (h : ∀ z : Fiber Z, (d.monoImage m).image.checker.val (k.restrict z).val = t) :
    Representative Z X :=
  ⟨(d.monoImage m).inverse.val * k.val, fun z hz ↦
    (d.monoImage m).inverse.property _ (h ⟨z, hz⟩)⟩

/-- The image inverse recovers the original map after the monomorphism. -/
theorem liftRep_comp (m : X ⟶ Y) [Mono m] (k : Representative Z Y)
    (h : ∀ z : Fiber Z, (d.monoImage m).image.checker.val (k.restrict z).val = t) :
    (d.liftRep m k h).toHom ≫ m = k.toHom := by
  apply Hom.ext
  funext z
  simp only [Hom.restrict_comp, Function.comp_apply]
  exact Subtype.ext ((d.monoImage m).inverse_spec ⟨(k.restrict z).val, h z⟩)

/-- Unique factorization descends through the morphism quotient without choosing representatives. -/
def liftWithProof (m : X ⟶ Y) [Mono m] (k : Z ⟶ Y)
    (h : ∀ z : Fiber Z, (d.monoImage m).image.checker.val (k.restrict z).val = t) :
    { l : Z ⟶ X // l ≫ m = k } :=
  Quotient.recOnSubsingleton
    (h := fun _ ↦ ⟨fun a b ↦ funext fun h ↦
      Subtype.ext ((cancel_mono m).mp ((a h).property.trans (b h).property.symm))⟩) k
    (fun k h ↦ ⟨(d.liftRep m k h).toHom, d.liftRep_comp m k h⟩) h

/-- A commuting square with truth forces the first leg to land in the image. -/
theorem lands_in_image (m : X ⟶ Y) [Mono m] (k : Z ⟶ Y) (l : Z ⟶ d.terminal)
    (h : k ≫ d.chi m = l ≫ d.truth) (z : Fiber Z) :
    (d.monoImage m).image.checker.val (k.restrict z).val = t := by
  have he := congrArg (fun r : Z ⟶ d.omega ↦ (r.restrict z).val) h
  simp only [Hom.restrict_comp, Function.comp_apply] at he
  exact he.trans ((d.terminal_pass_iff _).mp (l.restrict z).property)

/-- A truth-valued map with the prescribed true fiber is the characteristic map. -/
theorem chi_unique (m : X ⟶ Y) [Mono m] (k : Y ⟶ d.omega)
    (h : ∀ y : Fiber Y, (k.restrict y).val = t ↔
      ∃ x : Fiber X, (m.restrict x).val = y.val) : k = d.chi m := by
  apply Hom.ext
  funext y
  apply Subtype.ext
  change (k.restrict y).val = (d.monoImage m).image.checker.val y.val
  have he := (h y).trans ((d.monoImage m).pass_iff y.val).symm
  rcases (d.omega_pass_iff _).mp (k.restrict y).property with ht | hf
  · exact ht.trans (he.mp ht).symm
  · rcases (d.monoImage m).image.twoValued.2 y.val with ht' | hf'
    · exact (d.omega.twoValued.1 ((he.mpr ht').symm.trans hf)).elim
    · exact hf.trans hf'.symm

/-- The image checker of the false singleton has no fixed point: it swaps the two truth
values and sends every other value to false. -/
theorem exists_fixed_point_free (d : ClassifierData S t f) : ∃ r : S, ∀ x, r.val x ≠ x := by
  let m := constantRep d.constants d.terminal
    (⟨f, (d.omega_pass_iff f).mpr (Or.inr rfl)⟩ : Fiber d.omega)
  have hm : Mono m.toHom := mono_of_injective m.toHom (by
    intro x y _
    exact Subtype.ext (((d.terminal_pass_iff x.val).mp x.property).trans
      ((d.terminal_pass_iff y.val).mp y.property).symm))
  let i := d.monoImage m.toHom
  have hi (x : B) : i.image.checker.val x = t ↔ f = x := by
    rw [i.pass_iff]
    exact ⟨fun ⟨_, hx⟩ ↦ hx,
      fun hx ↦ ⟨⟨t, (d.terminal_pass_iff t).mpr rfl⟩, hx⟩⟩
  refine ⟨i.image.checker, fun x hx ↦ ?_⟩
  rcases i.image.twoValued.2 x with ht | hf
  · exact d.terminal.twoValued.1 ((hi x).mp ht |>.trans (hx.symm.trans ht)).symm
  · exact d.terminal.twoValued.1 (((hi x).mpr (hf.symm.trans hx)).symm.trans hf)

end ClassifierData

end GebProto.EndomorphismCategory.DecisionProblem
