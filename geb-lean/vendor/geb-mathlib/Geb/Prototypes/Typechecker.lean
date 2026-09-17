/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Setoid.Basic

set_option doc.verso true in
/-!
# Categories of typecheckers

A predicate on endomorphisms containing the identity and closed under composition
defines a submonoid and hence a one-object category. Given a selected base element,
each admissible endomorphism also specifies a type: its fiber over that element.

The typechecker category has these endomorphisms as objects. Its morphisms are
admissible endomorphisms preserving the specified fibers, quotiented by agreement
on the source fiber. Restriction to fibers gives a faithful functor to types.

The reflecting typechecker category retains the same objects, with unquotiented
morphisms that preserve and reflect membership in the fibers. Such morphisms
preserve both passing and failing. Sending each to its class defines a functor
to the quotient category.

## Main definitions

* {lit}`ContainsIdentity`, {lit}`ClosedUnderComposition`, and
  {lit}`CompositionallyClosed` express the closure conditions.
* {lit}`CompositionallyClosed.toSubmonoid` bundles the admissible endomorphisms.
* {lit}`OneObject` is their one-object category.
* {lit}`Typechecker` is the category of fiber specifications.
* {lit}`Typechecker.homSetoid` identifies representatives on the source fiber.
* {lit}`Typechecker.interpretation` restricts morphisms to fibers.
* {lit}`ReflectingTypechecker` retains functions that preserve and reflect passing.
* {lit}`ReflectingTypechecker.toQuotient` sends these functions to their quotient classes.

## Main statements

* {lit}`Typechecker.Representative.toHom_eq_iff` characterizes morphism equality
  as pointwise equality on the source fiber.
* {lit}`Typechecker.interpretation_faithful` shows that interpretation detects
  morphism equality.

## Implementation notes

Multiplication in {name}`Function.End` is function composition. In
{name}`CategoryTheory.SingleObj`, categorical composition reverses multiplication,
so composing first {lit}`f` and then {lit}`g` gives {lit}`g ∘ f`.
Objects remain distinct when different typecheckers specify the same fiber.
No decidability of the predicate or of equality on the base is required.

## Tags

category, endomorphism, submonoid, fiber, quotient, typechecker
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

/-- An admissible endomorphism, interpreted by its fiber over the selected element. -/
@[ext]
structure Typechecker (S : Submonoid (Function.End B)) (b : B) : Type u where
  /-- The endomorphism specifying the fiber. -/
  checker : S

namespace Typechecker

variable {S : Submonoid (Function.End B)} {b : B}

/-- The identity endomorphism supplies a typechecker for every selected element. -/
instance : Inhabited (Typechecker S b) := ⟨⟨1⟩⟩

/-- The elements accepted by a typechecker. -/
def Fiber (X : Typechecker S b) : Type u := { x : B // X.checker.val x = b }

/-- An admissible endomorphism taking the source fiber into the target fiber. -/
def Representative (X Y : Typechecker S b) : Type u :=
  { f : S // ∀ x : B, X.checker.val x = b → Y.checker.val (f.val x) = b }

/-- Restriction of a representative to the source fiber. -/
def Representative.restrict {X Y : Typechecker S b} (f : Representative X Y) :
    Fiber X → Fiber Y :=
  fun x ↦ ⟨f.val.val x.val, f.property x.val x.property⟩

/-- The identity endomorphism preserves every fiber. -/
def Representative.id (X : Typechecker S b) : Representative X X :=
  ⟨1, fun _ hx ↦ hx⟩

/-- Composition of endomorphisms preserving fibers. -/
def Representative.comp {X Y Z : Typechecker S b}
    (f : Representative X Y) (g : Representative Y Z) : Representative X Z :=
  ⟨g.val * f.val, fun x hx ↦ g.property (f.val.val x) (f.property x hx)⟩

/-- Restricting a composite is composition of the restrictions. -/
@[simp]
theorem Representative.restrict_comp {X Y Z : Typechecker S b}
    (f : Representative X Y) (g : Representative Y Z) :
    (f.comp g).restrict = g.restrict ∘ f.restrict := rfl

/-- Representatives are equivalent exactly when their restrictions agree. -/
instance homSetoid (X Y : Typechecker S b) : Setoid (Representative X Y) :=
  Setoid.ker Representative.restrict

/-- The equivalence relation observes precisely the source fiber. -/
theorem homSetoid_iff {X Y : Typechecker S b} (f g : Representative X Y) :
    f ≈ g ↔ ∀ x : B, X.checker.val x = b → f.val.val x = g.val.val x := by
  constructor
  · intro h x hx
    exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
  · intro h
    exact funext fun x ↦ Subtype.ext (h x.val x.property)

/-- Morphisms are equivalence classes of admissible fiber-preserving endomorphisms. -/
def Hom (X Y : Typechecker S b) : Type u := _root_.Quotient (homSetoid X Y)

/-- A morphism acts on the source fiber independently of its representative. -/
def Hom.restrict {X Y : Typechecker S b} : Hom X Y → (Fiber X → Fiber Y) :=
  Quotient.lift Representative.restrict (fun _ _ h ↦ h)

/-- Morphisms are determined by their actions on the source fiber. -/
@[ext]
theorem Hom.ext {X Y : Typechecker S b} {f g : Hom X Y}
    (h : f.restrict = g.restrict) : f = g :=
  Quotient.inductionOn₂ f g (fun _ _ h ↦ Quotient.sound h) h

/-- Composition descends to the quotient because restrictions compose. -/
def Hom.comp {X Y Z : Typechecker S b} : Hom X Y → Hom Y Z → Hom X Z :=
  Quotient.map₂ Representative.comp (fun _ _ hf _ _ hg ↦
    congrArg₂ (fun g f ↦ g ∘ f) hg hf)

/-- The category of typecheckers and admissible functions modulo source-fiber agreement. -/
instance category : Category (Typechecker S b) where
  Hom := Hom
  id X := Quotient.mk _ (Representative.id X)
  comp := Hom.comp
  id_comp f := Quotient.inductionOn f fun _ ↦ Quotient.sound rfl
  comp_id f := Quotient.inductionOn f fun _ ↦ Quotient.sound rfl
  assoc f g h := Quotient.inductionOn f fun _ ↦ Quotient.inductionOn g fun _ ↦
    Quotient.inductionOn h fun _ ↦ Quotient.sound rfl

/-- The morphism represented by an admissible fiber-preserving endomorphism. -/
def Representative.toHom {X Y : Typechecker S b} (f : Representative X Y) : X ⟶ Y :=
  Quotient.mk _ f

/-- Representatives define the same morphism exactly when they agree on the source fiber. -/
theorem Representative.toHom_eq_iff {X Y : Typechecker S b} (f g : Representative X Y) :
    f.toHom = g.toHom ↔ ∀ x : B, X.checker.val x = b → f.val.val x = g.val.val x :=
  Quotient.eq.trans (homSetoid_iff f g)

/-- Composition of represented morphisms is represented by composition of endomorphisms. -/
@[simp]
theorem Representative.toHom_comp {X Y Z : Typechecker S b}
    (f : Representative X Y) (g : Representative Y Z) :
    f.toHom ≫ g.toHom = (f.comp g).toHom := rfl

/-- Interpret each typechecker as its fiber and each morphism as its restriction. -/
def interpretation (S : Submonoid (Function.End B)) (b : B) : Typechecker S b ⥤ Type u where
  obj := Fiber
  map f := f.restrict
  map_id _ := rfl
  map_comp f g := Quotient.inductionOn₂ f g fun _ _ ↦ rfl

/-- Interpreting a represented morphism evaluates its endomorphism on the fiber. -/
@[simp]
theorem interpretation_map_toHom {X Y : Typechecker S b}
    (f : Representative X Y) (x : Fiber X) :
    (interpretation S b).map f.toHom x = f.restrict x := rfl

/-- Equality of interpretations is exactly equality in the quotient. -/
instance interpretation_faithful : (interpretation S b).Faithful where
  map_injective h := Hom.ext h

end Typechecker

/-- Typecheckers with unquotiented morphisms that preserve and reflect passing. -/
@[ext]
structure ReflectingTypechecker (S : Submonoid (Function.End B)) (b : B) : Type u where
  /-- The same fiber specification as in the quotient category. -/
  toTypechecker : Typechecker S b
  deriving Inhabited

namespace ReflectingTypechecker

variable {S : Submonoid (Function.End B)} {b : B}

/-- A fiber-preserving representative that also reflects membership in the fiber.
Equality is equality of functions on the whole base type. -/
def Hom (X Y : ReflectingTypechecker S b) : Type u :=
  { f : Typechecker.Representative X.toTypechecker Y.toTypechecker //
    ∀ x : B, Y.toTypechecker.checker.val (f.val.val x) = b → X.toTypechecker.checker.val x = b }

/-- Identity preserves and reflects passing. -/
def Hom.id (X : ReflectingTypechecker S b) : Hom X X :=
  ⟨Typechecker.Representative.id _, fun _ hx ↦ hx⟩

/-- Composition preserves and reflects passing. -/
def Hom.comp {X Y Z : ReflectingTypechecker S b} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.val.comp g.val, fun x hx ↦ f.property x (g.property (f.val.val.val x) hx)⟩

/-- The category of typecheckers with functions that preserve and reflect passing. -/
instance category : Category (ReflectingTypechecker S b) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- An input passes exactly when its image passes. -/
theorem map_pass_iff {X Y : ReflectingTypechecker S b} (f : X ⟶ Y) (x : B) :
    Y.toTypechecker.checker.val (f.val.val.val x) = b ↔ X.toTypechecker.checker.val x = b :=
  ⟨f.property x, f.val.property x⟩

/-- An input fails exactly when its image fails. -/
theorem map_fail_iff {X Y : ReflectingTypechecker S b} (f : X ⟶ Y) (x : B) :
    Y.toTypechecker.checker.val (f.val.val.val x) ≠ b ↔ X.toTypechecker.checker.val x ≠ b :=
  not_congr (map_pass_iff f x)

/-- Keep each typechecker and send each function to its class modulo source-fiber agreement. -/
def toQuotient (S : Submonoid (Function.End B)) (b : B) :
    ReflectingTypechecker S b ⥤ Typechecker S b where
  obj := toTypechecker
  map f := f.val.toHom
  map_id _ := rfl
  map_comp _ _ := rfl

end ReflectingTypechecker

end GebProto.EndomorphismCategory
