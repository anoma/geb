/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Setoid.Basic

set_option doc.verso true in
/-!
# Decision problems with quotiented admissible maps

A predicate on endomorphisms containing the identity and closed under composition
defines a submonoid and hence a one-object category. Fix distinct true and false
values in the base type. A decision checker is an admissible endomorphism returning
only those values, and its accepted fiber determines it everywhere.

Decision problems are these checkers. Their morphisms are admissible endomorphisms
preserving acceptance, quotiented by agreement on accepted source inputs.
The reductions may return any base values; only checkers must be two-valued.
Restriction to accepted fibers gives a faithful functor to types.

## Main definitions

* {lit}`ContainsIdentity`, {lit}`ClosedUnderComposition`, and
  {lit}`CompositionallyClosed` express the closure conditions.
* {lit}`CompositionallyClosed.toSubmonoid` bundles the admissible endomorphisms.
* {lit}`OneObject` is their one-object category.
* {lit}`AdmissibleEndomorphism` names an element of the chosen submonoid.
* {lit}`AcceptancePredicate` names a predicate on inputs, represented as a set.
* {lit}`acceptedFiber` assigns the acceptance predicate to an endomorphism.
* {lit}`FiberDeterminesFunction` states that this assignment is injective.
* {lit}`TwoValued` requires distinct truth values and restricts a function's range.
* {lit}`DecisionProblem` is the category of decision checkers and quotiented maps.
* {lit}`DecisionProblem.homSetoid` identifies representatives on the source fiber.
* {lit}`DecisionProblem.interpretation` restricts morphisms to accepted fibers.

## Main statements

* {lit}`TwoValued.nontrivial` witnesses that the base has at least two elements.
* {lit}`fiberDeterminesFunction_of_twoValued` gives a sufficient condition on
  the entire submonoid.
* {lit}`DecisionProblem.acceptedFiber_injective` gives the corresponding property
  on decision checkers without restricting other admissible functions.
* {lit}`DecisionProblem.Representative.toHom_eq_iff` characterizes morphism equality
  as pointwise equality on the source fiber.
* {lit}`DecisionProblem.interpretation_faithful` shows that interpretation detects
  morphism equality.

## Implementation notes

Multiplication in {name}`Function.End` is function composition. In
{name}`CategoryTheory.SingleObj`, categorical composition reverses multiplication,
so composing first {lit}`r` and then {lit}`s` gives {lit}`s ∘ r`.
The truth values are shared parameters. Each object's range proof also carries
their distinctness, so there are no objects when the parameters coincide.
Constant decision procedures are allowed; a checker need not attain both values.
The identity is admissible but need not be a decision checker.
No decidable equality on the base type is required.

## Tags

category, endomorphism, submonoid, decision problem, fiber, quotient, typechecker
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory

open CategoryTheory

variable {B : Type u}

/-- The identity endomorphism satisfies the predicate. -/
def ContainsIdentity (P : (B → B) → Prop) : Prop := P id

/-- Applying two admissible endomorphisms in sequence is admissible. -/
def ClosedUnderComposition (P : (B → B) → Prop) : Prop :=
  ∀ ⦃f g : B → B⦄, P f → P g → P (g ∘ f)

/-- The predicate contains the identity and is closed under composition. -/
def CompositionallyClosed (P : (B → B) → Prop) : Prop :=
  ContainsIdentity P ∧ ClosedUnderComposition P

/-- The submonoid whose elements are precisely the admissible endomorphisms. -/
def CompositionallyClosed.toSubmonoid {P : (B → B) → Prop}
    (h : CompositionallyClosed P) : Submonoid (Function.End B) where
  carrier := P
  one_mem' := h.1
  mul_mem' hf hg := h.2 hg hf

/-- The one-object category with the admissible endomorphisms as morphisms. -/
abbrev OneObject (S : Submonoid (Function.End B)) := SingleObj S

section AcceptedFibers

/-- An endomorphism belonging to the chosen submonoid. -/
abbrev AdmissibleEndomorphism (S : Submonoid (Function.End B)) : Type u := S

/-- A predicate recording which inputs are accepted, represented as a subset of the base type. -/
abbrev AcceptancePredicate (B : Type u) : Type u := Set B

/-- The predicate that an admissible endomorphism returns the selected success value.
This records accepted inputs and forgets which values are returned on rejected inputs. -/
def acceptedFiber {S : Submonoid (Function.End B)} (t : B)
    (f : AdmissibleEndomorphism S) : AcceptancePredicate B :=
  { x : B | f.val x = t }

/-- Admissible endomorphisms with the same accepted inputs are equal everywhere.
Thus agreement about success determines the outputs on rejected inputs as well. -/
def FiberDeterminesFunction (S : Submonoid (Function.End B)) (t : B) : Prop :=
  Function.Injective (acceptedFiber (S := S) t)

end AcceptedFibers

section DecisionCheckers

variable {S : Submonoid (Function.End B)} {t f : B}

/-- A function returning only the specified, distinct true and false values.
It need not attain both values: constant decision procedures are included. -/
def TwoValued (t f : B) (p : B → B) : Prop :=
  t ≠ f ∧ ∀ x : B, p x = t ∨ p x = f

namespace TwoValued

/-- The specified truth values witness that the base type has at least two elements. -/
theorem nontrivial {p : B → B} (hp : TwoValued t f p) : Nontrivial B :=
  nontrivial_of_ne t f hp.1

/-- Precomposing a decision checker with any function preserves its output restriction. -/
theorem comp_right {p : B → B} (hp : TwoValued t f p) (r : B → B) :
    TwoValued t f (p ∘ r) :=
  ⟨hp.1, fun x ↦ hp.2 (r x)⟩

/-- Two functions using the same truth values are equal if they accept the same inputs. -/
theorem eq_of_pass_iff {p q : B → B} (hp : TwoValued t f p) (hq : TwoValued t f q)
    (h : ∀ x : B, p x = t ↔ q x = t) : p = q := by
  funext x
  rcases hp.2 x with hpt | hpf
  · exact hpt.trans ((h x).mp hpt).symm
  · rcases hq.2 x with hqt | hqf
    · exact ((h x).mpr hqt).trans hqt.symm
    · exact hpf.trans hqf.symm

end TwoValued

/-- If every admissible endomorphism uses the same two truth values, its fiber determines it. -/
theorem fiberDeterminesFunction_of_twoValued
    (h : ∀ p : S, TwoValued t f p.val) : FiberDeterminesFunction S t :=
  fun p q hpq ↦ Subtype.ext ((h p).eq_of_pass_iff (h q) (Set.ext_iff.mp hpq))

end DecisionCheckers

/-- An admissible decision checker, interpreted by its accepted fiber. -/
@[ext]
structure DecisionProblem (S : Submonoid (Function.End B)) (t f : B) : Type u where
  /-- The endomorphism deciding acceptance. -/
  checker : AdmissibleEndomorphism S
  /-- The checker returns only the shared, distinct truth values. -/
  twoValued : TwoValued t f checker.val

namespace DecisionProblem

variable {S : Submonoid (Function.End B)} {t f : B}

/-- The accepted fiber determines a decision checker, without restricting other functions in
the admissible submonoid. -/
theorem acceptedFiber_injective :
    Function.Injective (fun X : DecisionProblem S t f ↦ acceptedFiber t X.checker) := by
  intro X Y h
  apply DecisionProblem.ext
  exact Subtype.ext (X.twoValued.eq_of_pass_iff Y.twoValued (Set.ext_iff.mp h))

/-- The elements accepted by a typechecker. -/
def Fiber (X : DecisionProblem S t f) : Type u := { x : B // x ∈ acceptedFiber t X.checker }

/-- An admissible endomorphism taking the source fiber into the target fiber. -/
def Representative (X Y : DecisionProblem S t f) : Type u :=
  { f : S // ∀ x : B, X.checker.val x = t → Y.checker.val (f.val x) = t }

/-- Restriction of a representative to the source fiber. -/
def Representative.restrict {X Y : DecisionProblem S t f} (f : Representative X Y) :
    Fiber X → Fiber Y :=
  fun x ↦ ⟨f.val.val x.val, f.property x.val x.property⟩

/-- The identity endomorphism preserves every fiber. -/
def Representative.id (X : DecisionProblem S t f) : Representative X X :=
  ⟨1, fun _ hx ↦ hx⟩

/-- Composition of endomorphisms preserving fibers. -/
def Representative.comp {X Y Z : DecisionProblem S t f}
    (f : Representative X Y) (g : Representative Y Z) : Representative X Z :=
  ⟨g.val * f.val, fun x hx ↦ g.property (f.val.val x) (f.property x hx)⟩

/-- Restricting a composite is composition of the restrictions. -/
@[simp]
theorem Representative.restrict_comp {X Y Z : DecisionProblem S t f}
    (f : Representative X Y) (g : Representative Y Z) :
    (f.comp g).restrict = g.restrict ∘ f.restrict := rfl

/-- Representatives are equivalent exactly when their restrictions agree. -/
instance homSetoid (X Y : DecisionProblem S t f) : Setoid (Representative X Y) :=
  Setoid.ker Representative.restrict

/-- The equivalence relation observes precisely the source fiber. -/
theorem homSetoid_iff {X Y : DecisionProblem S t f} (f g : Representative X Y) :
    f ≈ g ↔ ∀ x : B, X.checker.val x = t → f.val.val x = g.val.val x := by
  constructor
  · intro h x hx
    exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
  · intro h
    exact funext fun x ↦ Subtype.ext (h x.val x.property)

/-- Morphisms are equivalence classes of admissible fiber-preserving endomorphisms. -/
def Hom (X Y : DecisionProblem S t f) : Type u := _root_.Quotient (homSetoid X Y)

/-- A morphism acts on the source fiber independently of its representative. -/
def Hom.restrict {X Y : DecisionProblem S t f} : Hom X Y → (Fiber X → Fiber Y) :=
  Quotient.lift Representative.restrict (fun _ _ h ↦ h)

/-- Morphisms are determined by their actions on the source fiber. -/
@[ext]
theorem Hom.ext {X Y : DecisionProblem S t f} {f g : Hom X Y}
    (h : f.restrict = g.restrict) : f = g :=
  Quotient.inductionOn₂ f g (fun _ _ h ↦ Quotient.sound h) h

/-- Composition descends to the quotient because restrictions compose. -/
def Hom.comp {X Y Z : DecisionProblem S t f} : Hom X Y → Hom Y Z → Hom X Z :=
  Quotient.map₂ Representative.comp (fun _ _ hf _ _ hg ↦
    congrArg₂ (fun g f ↦ g ∘ f) hg hf)

/-- The category of typecheckers and admissible functions modulo source-fiber agreement. -/
instance category : Category (DecisionProblem S t f) where
  Hom := Hom
  id X := Quotient.mk _ (Representative.id X)
  comp := Hom.comp
  id_comp f := Quotient.inductionOn f fun _ ↦ Quotient.sound rfl
  comp_id f := Quotient.inductionOn f fun _ ↦ Quotient.sound rfl
  assoc f g h := Quotient.inductionOn f fun _ ↦ Quotient.inductionOn g fun _ ↦
    Quotient.inductionOn h fun _ ↦ Quotient.sound rfl

/-- Restriction of quotient morphisms commutes with composition. -/
@[simp]
theorem Hom.restrict_comp {X Y Z : DecisionProblem S t f} (r : X ⟶ Y) (s : Y ⟶ Z) :
    (r ≫ s).restrict = s.restrict ∘ r.restrict :=
  Quotient.inductionOn₂ r s fun _ _ ↦ rfl

/-- The morphism represented by an admissible fiber-preserving endomorphism. -/
def Representative.toHom {X Y : DecisionProblem S t f} (f : Representative X Y) : X ⟶ Y :=
  Quotient.mk _ f

/-- Representatives define the same morphism exactly when they agree on the source fiber. -/
theorem Representative.toHom_eq_iff {X Y : DecisionProblem S t f} (f g : Representative X Y) :
    f.toHom = g.toHom ↔ ∀ x : B, X.checker.val x = t → f.val.val x = g.val.val x :=
  Quotient.eq.trans (homSetoid_iff f g)

/-- Composition of represented morphisms is represented by composition of endomorphisms. -/
@[simp]
theorem Representative.toHom_comp {X Y Z : DecisionProblem S t f}
    (f : Representative X Y) (g : Representative Y Z) :
    f.toHom ≫ g.toHom = (f.comp g).toHom := rfl

/-- Interpret each typechecker as its fiber and each morphism as its restriction. -/
def interpretation (S : Submonoid (Function.End B)) (t f : B) :
    DecisionProblem S t f ⥤ Type u where
  obj := Fiber
  map f := f.restrict
  map_id _ := rfl
  map_comp f g := Quotient.inductionOn₂ f g fun _ _ ↦ rfl

/-- Interpreting a represented morphism evaluates its endomorphism on the fiber. -/
@[simp]
theorem interpretation_map_toHom {X Y : DecisionProblem S t f}
    (r : Representative X Y) (x : Fiber X) :
    (interpretation S t f).map r.toHom x = r.restrict x := rfl

/-- Equality of interpretations is exactly equality in the quotient. -/
instance interpretation_faithful : (interpretation S t f).Faithful where
  map_injective h := Hom.ext h

end DecisionProblem

end GebProto.EndomorphismCategory
