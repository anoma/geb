import GebLean.Utilities.Elements
import GebLean.Utilities.Profunctors
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Grothendieck

/-!
# Twisted arrow categories

This module defines twisted arrow categories and their variants.

The twisted arrow category of a category C is the category of elements of
the hom functor `hom : Cᵒᵖ × C ⥤ Type`. Objects are triples (X, Y, f) where
f : X ⟶ Y, and morphisms consist of pairs of morphisms going in opposite
directions (backwards on domain, forwards on codomain) making the resulting
square (with three morphisms composing parallel to one) commute.

We define four variants:
- `Tw(C)` = `Elements(hom)` - twisted arrow category
- `Tw(Cᵒᵖ')` = `Elements(homOp')` - twisted arrow of opposite
- `Tw^op'(C)` = `ElementsContra'(hom')` - opposite of twisted arrow
- `Tw^co` = `Tw^op'(Cᵒᵖ')` - opposite of twisted arrow of opposite
-                            (which we shall call "co-twisted")
-/

universe v u w

namespace GebLean

open CategoryTheory

section TwistedArrowCategories

/--
The twisted arrow category of `C`, defined as the category of elements of
the hom functor.
-/
@[simp]
def TwistedArrow (C : Type u) [Category.{v} C] :=
  (Functor.hom C).Elements

instance (C : Type u) [Category.{v} C] : Category (TwistedArrow C) := by
  unfold TwistedArrow
  infer_instance

@[simp]
def TwistedArrow' (C : Type u) [Category.{v} C] :=
  (hom' (C := C)).Elements

instance (C : Type u) [Category.{v} C] : Category (TwistedArrow' C) := by
  unfold TwistedArrow'
  infer_instance

abbrev Tw := TwistedArrow

abbrev Tw' := TwistedArrow'

variable {C : Type u} [Category.{v} C]

section TwistedArrow'Helpers

/--
Construct an object of `TwistedArrow' C` from domain, codomain, and arrow.
-/
def twObjMk' {dom cod : C} (arr : dom ⟶ cod) : TwistedArrow' C :=
  ⟨(dom, cod), arr⟩

/--
Extract the domain from an object of `TwistedArrow' C`.
-/
def twDom' (x : TwistedArrow' C) : C := x.fst.1

/--
Extract the codomain from an object of `TwistedArrow' C`.
-/
def twCod' (x : TwistedArrow' C) : C := x.fst.2

/--
Extract the arrow from an object of `TwistedArrow' C`.
-/
def twArr' (x : TwistedArrow' C) : twDom' x ⟶ twCod' x := x.snd

lemma twObjMk'_dom {dom cod : C} (arr : dom ⟶ cod) :
    twDom' (twObjMk' arr) = dom := rfl

lemma twObjMk'_cod {dom cod : C} (arr : dom ⟶ cod) :
    twCod' (twObjMk' arr) = cod := rfl

lemma twObjMk'_arr {dom cod : C} (arr : dom ⟶ cod) :
    twArr' (twObjMk' arr) = arr := rfl

/--
Construct a morphism in `TwistedArrow' C` from morphisms on domains and
codomains.

A morphism from `(X, Y, f)` to `(X', Y', f')` consists of:
- `domArr : X' ⟶ X` (morphism between domains, going backwards)
- `codArr : Y ⟶ Y'` (morphism between codomains, going forwards)
such that the square commutes: `domArr ≫ f ≫ codArr = f'`.

Note: The domain arrow goes backwards because the first component of the
product is in `Cᵒᵖ'`.
-/
def twHomMk' {x y : TwistedArrow' C}
    (domArr : twDom' y ⟶ twDom' x)
    (codArr : twCod' x ⟶ twCod' y)
    (comm : domArr ≫ twArr' x ≫ codArr = twArr' y) : x ⟶ y :=
  CategoryOfElements.homMk x y (domArr, codArr) comm

def twHomMkChain' {w x y z : C}
    (domArr : x ⟶ w) (domObjArr : w ⟶ y) (codArr : y ⟶ z) :
    twObjMk' (dom := w) (cod := y) domObjArr ⟶
    twObjMk' (dom := x) (cod := z) (domArr ≫ domObjArr ≫ codArr) :=
  twHomMk'
    (x := twObjMk' (dom := w) (cod := y) domObjArr)
    (y := twObjMk' (dom := x) (cod := z) (domArr ≫ domObjArr ≫ codArr))
    (by simp [twObjMk'_dom] ; exact domArr)
    (by simp [twObjMk'_cod] ; exact codArr)
    rfl

/--
Extract the domain arrow from a morphism in `TwistedArrow' C`.
Note: This goes backwards (from codomain to domain) because the first component
is in `Cᵒᵖ'`.
-/
def twDomArr' {x y : TwistedArrow' C} (f : x ⟶ y) : twDom' y ⟶ twDom' x :=
  f.val.1

/--
Extract the codomain arrow from a morphism in `TwistedArrow' C`.
-/
def twCodArr' {x y : TwistedArrow' C} (f : x ⟶ y) : twCod' x ⟶ twCod' y :=
  f.val.2

lemma twHomMk'_domArr {x y : TwistedArrow' C}
    (domArr : twDom' y ⟶ twDom' x)
    (codArr : twCod' x ⟶ twCod' y)
    (comm : domArr ≫ twArr' x ≫ codArr = twArr' y) :
    twDomArr' (twHomMk' domArr codArr comm) = domArr := rfl

lemma twHomMk'_codArr {x y : TwistedArrow' C}
    (domArr : twDom' y ⟶ twDom' x)
    (codArr : twCod' x ⟶ twCod' y)
    (comm : domArr ≫ twArr' x ≫ codArr = twArr' y) :
    twCodArr' (twHomMk' domArr codArr comm) = codArr := rfl

/--
Extract the commutativity condition from a morphism in `TwistedArrow' C`.
-/
lemma twHomComm' {x y : TwistedArrow' C} (f : x ⟶ y) :
    twDomArr' f ≫ twArr' x ≫ twCodArr' f = twArr' y :=
  f.property

@[ext]
lemma twHom'_ext {x y : TwistedArrow' C} (f g : x ⟶ y)
    (hdom : twDomArr' f = twDomArr' g)
    (hcod : twCodArr' f = twCodArr' g) : f = g := by
  cases f; cases g
  congr
  exact Prod.ext hdom hcod

@[simp]
lemma twHomMk'_eta {x y : TwistedArrow' C} (f : x ⟶ y) :
    twHomMk' (twDomArr' f) (twCodArr' f) (twHomComm' f) = f := by
  apply twHom'_ext <;> simp only [twHomMk'_domArr, twHomMk'_codArr]

@[simp]
lemma twDomArr'_id (tw : TwistedArrow' C) : twDomArr' (𝟙 tw) = 𝟙 (twDom' tw) := rfl

@[simp]
lemma twCodArr'_id (tw : TwistedArrow' C) : twCodArr' (𝟙 tw) = 𝟙 (twCod' tw) := rfl

@[simp]
lemma twDomArr'_comp {x y z : TwistedArrow' C} (f : x ⟶ y) (g : y ⟶ z) :
    twDomArr' (f ≫ g) = twDomArr' g ≫ twDomArr' f := rfl

@[simp]
lemma twCodArr'_comp {x y z : TwistedArrow' C} (f : x ⟶ y) (g : y ⟶ z) :
    twCodArr' (f ≫ g) = twCodArr' f ≫ twCodArr' g := rfl

end TwistedArrow'Helpers

/--
The twisted arrow category of `Cᵒᵖ'`, defined as the category of elements
of `homOp'`.
-/
@[simp]
def TwistedArrowOp' (C : Type u) [Category.{v} C] :=
  (homOp' (C := C)).Elements

instance (C : Type u) [Category.{v} C] : Category (TwistedArrowOp' C) := by
  unfold TwistedArrowOp'
  infer_instance

section TwistedArrowOp'Helpers

/--
Construct an object of `TwistedArrowOp' C` from domain, codomain, and arrow.
Note: The arrow goes from `cod` to `dom` because this is the twisted arrow
category of `Cᵒᵖ'`.
-/
def twOpObjMk' {dom cod : C} (arr : cod ⟶ dom) : TwistedArrowOp' C :=
  ⟨(dom, cod), arr⟩

/--
Extract the domain from an object of `TwistedArrowOp' C`.
-/
def twOpDom' (x : TwistedArrowOp' C) : C := x.fst.1

/--
Extract the codomain from an object of `TwistedArrowOp' C`.
-/
def twOpCod' (x : TwistedArrowOp' C) : C := x.fst.2

/--
Extract the arrow from an object of `TwistedArrowOp' C`.
-/
def twOpArr' (x : TwistedArrowOp' C) : twOpCod' x ⟶ twOpDom' x := x.snd

lemma twOpObjMk'_dom {dom cod : C} (arr : cod ⟶ dom) :
    twOpDom' (twOpObjMk' arr) = dom := rfl

lemma twOpObjMk'_cod {dom cod : C} (arr : cod ⟶ dom) :
    twOpCod' (twOpObjMk' arr) = cod := rfl

lemma twOpObjMk'_arr {dom cod : C} (arr : cod ⟶ dom) :
    twOpArr' (twOpObjMk' arr) = arr := rfl

/--
Construct a morphism in `TwistedArrowOp' C` from morphisms on domains and
codomains.

A morphism from `(X, Y, f)` to `(X', Y', f')` consists of:
- `domArr : X ⟶ X'` (morphism between domains, going forwards)
- `codArr : Y' ⟶ Y` (morphism between codomains, going backwards)
such that the square commutes: `codArr ≫ f ≫ domArr = f'`.
-/
def twOpHomMk' {x y : TwistedArrowOp' C}
    (domArr : twOpDom' x ⟶ twOpDom' y)
    (codArr : twOpCod' y ⟶ twOpCod' x)
    (comm : codArr ≫ twOpArr' x ≫ domArr = twOpArr' y) : x ⟶ y :=
  CategoryOfElements.homMk x y (domArr, codArr) comm

def twOpHomMkChain' {w x y z : C}
    (codArr : z ⟶ y) (domObjArr : y ⟶ w) (domArr : w ⟶ x) :
    twOpObjMk' (dom := w) (cod := y) domObjArr ⟶
    twOpObjMk' (dom := x) (cod := z) (codArr ≫ domObjArr ≫ domArr) :=
  twOpHomMk'
    (x := twOpObjMk' (dom := w) (cod := y) domObjArr)
    (y := twOpObjMk' (dom := x) (cod := z) (codArr ≫ domObjArr ≫ domArr))
    (by simp [twOpObjMk'_dom] ; exact domArr)
    (by simp [twOpObjMk'_cod] ; exact codArr)
    rfl

/--
Extract the domain arrow from a morphism in `TwistedArrowOp' C`.
-/
def twOpDomArr' {x y : TwistedArrowOp' C} (f : x ⟶ y) :
    twOpDom' x ⟶ twOpDom' y :=
  f.val.1

/--
Extract the codomain arrow from a morphism in `TwistedArrowOp' C`.
Note: This goes backwards (from `y`'s codomain to `x`'s codomain).
-/
def twOpCodArr' {x y : TwistedArrowOp' C} (f : x ⟶ y) :
    twOpCod' y ⟶ twOpCod' x :=
  f.val.2

lemma twOpHomMk'_domArr {x y : TwistedArrowOp' C}
    (domArr : twOpDom' x ⟶ twOpDom' y)
    (codArr : twOpCod' y ⟶ twOpCod' x)
    (comm : codArr ≫ twOpArr' x ≫ domArr = twOpArr' y) :
    twOpDomArr' (twOpHomMk' domArr codArr comm) = domArr := rfl

lemma twOpHomMk'_codArr {x y : TwistedArrowOp' C}
    (domArr : twOpDom' x ⟶ twOpDom' y)
    (codArr : twOpCod' y ⟶ twOpCod' x)
    (comm : codArr ≫ twOpArr' x ≫ domArr = twOpArr' y) :
    twOpCodArr' (twOpHomMk' domArr codArr comm) = codArr := rfl

/--
Extract the commutativity condition from a morphism in `TwistedArrowOp' C`.
-/
lemma twOpHomComm' {x y : TwistedArrowOp' C} (f : x ⟶ y) :
    twOpCodArr' f ≫ twOpArr' x ≫ twOpDomArr' f = twOpArr' y :=
  f.property

@[ext]
lemma twOpHom'_ext {x y : TwistedArrowOp' C} (f g : x ⟶ y)
    (hdom : twOpDomArr' f = twOpDomArr' g)
    (hcod : twOpCodArr' f = twOpCodArr' g) : f = g := by
  cases f; cases g
  congr
  exact Prod.ext hdom hcod

end TwistedArrowOp'Helpers

/--
The opposite of the twisted arrow category, defined as a contravariant
category of elements.
-/
@[simp]
def OpTwistedArrow' (C : Type u) [Category.{v} C] :=
  (homPre' (C := C)).ElementsContra'

instance (C : Type u) [Category.{v} C] : Category (OpTwistedArrow' C) := by
  unfold OpTwistedArrow'
  infer_instance

section OpTwistedArrow'Helpers

/--
Construct an object of `OpTwistedArrow' C` from domain, codomain, and arrow.
Note: This is the opposite of `TwistedArrow' C`, so objects have the same
structure.
-/
def opTwObjMk' {dom cod : C} (arr : dom ⟶ cod) : OpTwistedArrow' C :=
  ⟨(cod, dom), arr⟩

/--
Extract the domain from an object of `OpTwistedArrow' C`.
-/
def opTwDom' (x : OpTwistedArrow' C) : C := x.fst.2

/--
Extract the codomain from an object of `OpTwistedArrow' C`.
-/
def opTwCod' (x : OpTwistedArrow' C) : C := x.fst.1

/--
Extract the arrow from an object of `OpTwistedArrow' C`.
-/
def opTwArr' (x : OpTwistedArrow' C) : opTwDom' x ⟶ opTwCod' x := x.snd

lemma opTwObjMk'_dom {dom cod : C} (arr : dom ⟶ cod) :
    opTwDom' (opTwObjMk' arr) = dom := rfl

lemma opTwObjMk'_cod {dom cod : C} (arr : dom ⟶ cod) :
    opTwCod' (opTwObjMk' arr) = cod := rfl

lemma opTwObjMk'_arr {dom cod : C} (arr : dom ⟶ cod) :
    opTwArr' (opTwObjMk' arr) = arr := rfl

/--
Construct a morphism in `OpTwistedArrow' C` from morphisms on domains and
codomains.

A morphism from `(X, Y, f)` to `(X', Y', f')` consists of:
- `domArr : X ⟶ X'` (morphism between domains, going forwards)
- `codArr : Y' ⟶ Y` (morphism between codomains, going backwards)
such that the square commutes: `f ≫ codArr = domArr ≫ f'`.

Note: This is the opposite of `TwistedArrow' C`, so morphisms go in opposite
directions compared to `TwistedArrow' C`.
-/
def opTwHomMk' {x y : OpTwistedArrow' C}
    (domArr : opTwDom' x ⟶ opTwDom' y)
    (codArr : opTwCod' y ⟶ opTwCod' x)
    (comm : domArr ≫ opTwArr' y ≫ codArr = opTwArr' x) : x ⟶ y :=
  CategoryOfElements.homMk y x (codArr, domArr) comm

def opTwHomMkChain' {w x y z : C}
    (domArr : w ⟶ x) (codObjArr : x ⟶ y) (codArr : y ⟶ z) :
    opTwObjMk' (dom := w) (cod := z) (domArr ≫ codObjArr ≫ codArr) ⟶
    opTwObjMk' (dom := x) (cod := y) codObjArr :=
  opTwHomMk'
    (x := opTwObjMk' (dom := w) (cod := z) (domArr ≫ codObjArr ≫ codArr))
    (y := opTwObjMk' (dom := x) (cod := y) codObjArr)
    (by simp [opTwObjMk'_dom] ; exact domArr)
    (by simp [opTwObjMk'_cod] ; exact codArr)
    rfl

/--
Extract the domain arrow from a morphism in `OpTwistedArrow' C`.
-/
def opTwDomArr' {x y : OpTwistedArrow' C} (f : x ⟶ y) :
    opTwDom' x ⟶ opTwDom' y :=
  f.val.2

/--
Extract the codomain arrow from a morphism in `OpTwistedArrow' C`.
Note: This goes backwards (from `y`'s codomain to `x`'s codomain).
-/
def opTwCodArr' {x y : OpTwistedArrow' C} (f : x ⟶ y) :
    opTwCod' y ⟶ opTwCod' x :=
  f.val.1

lemma opTwHomMk'_domArr {x y : OpTwistedArrow' C}
    (domArr : opTwDom' x ⟶ opTwDom' y)
    (codArr : opTwCod' y ⟶ opTwCod' x)
    (comm : domArr ≫ opTwArr' y ≫ codArr = opTwArr' x) :
    opTwDomArr' (opTwHomMk' domArr codArr comm) = domArr := rfl

lemma opTwHomMk'_codArr {x y : OpTwistedArrow' C}
    (domArr : opTwDom' x ⟶ opTwDom' y)
    (codArr : opTwCod' y ⟶ opTwCod' x)
    (comm : domArr ≫ opTwArr' y ≫ codArr = opTwArr' x) :
    opTwCodArr' (opTwHomMk' domArr codArr comm) = codArr := rfl

/--
Extract the commutativity condition from a morphism in `OpTwistedArrow' C`.
-/
lemma opTwHomComm' {x y : OpTwistedArrow' C} (f : x ⟶ y) :
    opTwDomArr' f ≫ opTwArr' y ≫ opTwCodArr' f = opTwArr' x :=
  f.property

@[ext]
lemma opTwHom'_ext {x y : OpTwistedArrow' C} (f g : x ⟶ y)
    (hdom : opTwDomArr' f = opTwDomArr' g)
    (hcod : opTwCodArr' f = opTwCodArr' g) : f = g := by
  cases f; cases g
  congr
  exact Prod.ext hcod hdom

end OpTwistedArrow'Helpers

/--
The opposite of the twisted arrow category of `Cᵒᵖ'`, which we
are calling the co-twisted arrow category of `C`.
-/
@[simp]
def CoTwistedArrow (C : Type u) [Category.{v} C] :=
  (homPreOp' (C := C)).ElementsContra'

instance (C : Type u) [Category.{v} C] : Category (CoTwistedArrow C) := by
  unfold CoTwistedArrow
  infer_instance

section CoTwistedArrowHelpers

/--
Construct an object of `CoTwistedArrow C` from domain, codomain, and arrow.
Note: The arrow goes from `cod` to `dom`, and this is the opposite of
`TwistedArrowOp' C`.
-/
def coTwObjMk' {dom cod : C} (arr : cod ⟶ dom) : CoTwistedArrow C :=
  ⟨(cod, dom), arr⟩

/--
Extract the domain from an object of `CoTwistedArrow C`.
-/
def coTwDom' (x : CoTwistedArrow C) : C := x.fst.2

/--
Extract the codomain from an object of `CoTwistedArrow C`.
-/
def coTwCod' (x : CoTwistedArrow C) : C := x.fst.1

/--
Extract the arrow from an object of `CoTwistedArrow C`.
-/
def coTwArr' (x : CoTwistedArrow C) : coTwCod' x ⟶ coTwDom' x := x.snd

lemma coTwObjMk'_dom {dom cod : C} (arr : cod ⟶ dom) :
    coTwDom' (coTwObjMk' arr) = dom := rfl

lemma coTwObjMk'_cod {dom cod : C} (arr : cod ⟶ dom) :
    coTwCod' (coTwObjMk' arr) = cod := rfl

lemma coTwObjMk'_arr {dom cod : C} (arr : cod ⟶ dom) :
    coTwArr' (coTwObjMk' arr) = arr := rfl

/--
Construct a morphism in `CoTwistedArrow C` from morphisms on domains and
codomains.

A morphism from `(X, Y, f)` to `(X', Y', f')` consists of:
- `domArr : X' ⟶ X` (morphism between domains, going backwards)
- `codArr : Y ⟶ Y'` (morphism between codomains, going forwards)
such that the square commutes: `codArr ≫ f' ≫ domArr = f`.

Note: This is the opposite of `TwistedArrowOp' C`.
-/
def coTwHomMk' {x y : CoTwistedArrow C}
    (domArr : coTwDom' y ⟶ coTwDom' x)
    (codArr : coTwCod' x ⟶ coTwCod' y)
    (comm : codArr ≫ coTwArr' y ≫ domArr = coTwArr' x) : x ⟶ y :=
  CategoryOfElements.homMk y x (codArr, domArr)
    (by simp [homPreOp', profunctorToOp', hom']  ;exact comm)

def coTwHomMkChain' {w x y z : C}
    (codArr : y ⟶ z) (codObjArr : z ⟶ x) (domArr : x ⟶ w) :
    coTwObjMk' (dom := w) (cod := y) (codArr ≫ codObjArr ≫ domArr) ⟶
    coTwObjMk' (dom := x) (cod := z) codObjArr :=
  coTwHomMk'
    (x := coTwObjMk' (dom := w) (cod := y) (codArr ≫ codObjArr ≫ domArr))
    (y := coTwObjMk' (dom := x) (cod := z) codObjArr)
    (by simp [coTwObjMk'_dom] ; exact domArr)
    (by simp [coTwObjMk'_cod] ; exact codArr)
    rfl

/--
Extract the domain arrow from a morphism in `CoTwistedArrow C`.
Note: This goes backwards (from `y`'s domain to `x`'s domain).
-/
def coTwDomArr' {x y : CoTwistedArrow C} (f : x ⟶ y) :
    coTwDom' y ⟶ coTwDom' x :=
  f.val.2

/--
Extract the codomain arrow from a morphism in `CoTwistedArrow C`.
-/
def coTwCodArr' {x y : CoTwistedArrow C} (f : x ⟶ y) :
    coTwCod' x ⟶ coTwCod' y :=
  f.val.1

lemma coTwHomMk'_domArr {x y : CoTwistedArrow C}
    (domArr : coTwDom' y ⟶ coTwDom' x)
    (codArr : coTwCod' x ⟶ coTwCod' y)
    (comm : codArr ≫ coTwArr' y ≫ domArr = coTwArr' x) :
    coTwDomArr' (coTwHomMk' domArr codArr comm) = domArr := rfl

lemma coTwHomMk'_codArr {x y : CoTwistedArrow C}
    (domArr : coTwDom' y ⟶ coTwDom' x)
    (codArr : coTwCod' x ⟶ coTwCod' y)
    (comm : codArr ≫ coTwArr' y ≫ domArr = coTwArr' x) :
    coTwCodArr' (coTwHomMk' domArr codArr comm) = codArr := rfl

/--
Extract the commutativity condition from a morphism in `CoTwistedArrow C`.
-/
lemma coTwHomComm' {x y : CoTwistedArrow C} (f : x ⟶ y) :
    coTwCodArr' f ≫ coTwArr' y ≫ coTwDomArr' f = coTwArr' x := by
  unfold coTwCodArr' coTwDomArr' coTwArr'
  change f.val.1 ≫ y.snd ≫ f.val.2 = x.snd
  have h := f.property
  simp only [homPreOp', hom', profunctorToOp',
    opProdEquiv, Equivalence.prod_inverse, Equivalence.refl_inverse,
    Cat.equivOfIso, opEquivOp', opIsoOp', catOfOp'ToOp] at h
  exact h

@[ext]
lemma coTwHom'_ext {x y : CoTwistedArrow C} (f g : x ⟶ y)
    (hdom : coTwDomArr' f = coTwDomArr' g)
    (hcod : coTwCodArr' f = coTwCodArr' g) : f = g := by
  cases f; cases g
  congr
  exact Prod.ext hcod hdom

end CoTwistedArrowHelpers

section TwistedArrowIsomorphisms

/--
Functor from `OpTwistedArrow' C` to `(TwistedArrow' C)ᵒᵖ'`.
-/
def opTwistedArrowToTwistedArrowOp' :
    OpTwistedArrow' C ⥤ (TwistedArrow' C)ᵒᵖ' where
  obj := fun x => twObjMk' (opTwArr' x)
  map := fun {x y} f =>
    twHomMk'
      (x := twObjMk' (opTwArr' y))
      (y := twObjMk' (opTwArr' x))
      (by simp only [twObjMk'_dom, opTwDom']; exact opTwDomArr' f)
      (by simp only [twObjMk'_cod, opTwCod']; exact opTwCodArr' f)
      (opTwHomComm' f)
  map_id := fun x => by
    apply twHom'_ext
    · rfl
    · rfl
  map_comp := fun {x y z} f g => by
    apply twHom'_ext
    · rfl
    · rfl

/--
Functor from `(TwistedArrow' C)ᵒᵖ'` to `OpTwistedArrow' C`.
-/
def twistedArrowOp'ToOpTwistedArrow :
    (TwistedArrow' C)ᵒᵖ' ⥤ OpTwistedArrow' C where
  obj := fun x => opTwObjMk' (twArr' x)
  map := fun {x y} f =>
    opTwHomMk'
      (x := opTwObjMk' (twArr' x))
      (y := opTwObjMk' (twArr' y))
      (by simp only [opTwObjMk'_dom, twDom']; exact twDomArr' (C := C) f)
      (by simp only [opTwObjMk'_cod, twCod']; exact twCodArr' (C := C) f)
      (twHomComm' (C := C) f)
  map_id := fun x => by
    apply opTwHom'_ext
    · rfl
    · rfl
  map_comp := fun {x y z} f g => by
    apply opTwHom'_ext
    · rfl
    · rfl

/--
`OpTwistedArrow' C` is isomorphic to `(TwistedArrow' C)ᵒᵖ'`.
-/
def opTwistedArrowIsoTwistedArrowOp' :
    OpTwistedArrow' C ≅Cat (TwistedArrow' C)ᵒᵖ' where
  hom := opTwistedArrowToTwistedArrowOp'
  inv := twistedArrowOp'ToOpTwistedArrow
  hom_inv_id := rfl
  inv_hom_id := rfl

/--
Functor from `CoTwistedArrow C` to `(TwistedArrowOp' C)ᵒᵖ'`.

Objects of `CoTwistedArrow C` are stored as `((cod, dom), arr : cod ⟶ dom)`.
Objects of `TwistedArrowOp' C` are stored as `((dom, cod), arr : cod ⟶ dom)`.
So we swap the pair components.
-/
def coTwistedArrowToTwistedArrowOpOp' :
    CoTwistedArrow C ⥤ (TwistedArrowOp' C)ᵒᵖ' where
  obj x :=
    let dom := coTwDom' x ; let cod := coTwCod' x ; let arr := coTwArr' x
    ⟨(dom, cod), arr⟩
  map {x y} f :=
    let xDom := coTwDom' x ; let xCod := coTwCod' x ; let xArr := coTwArr' x
    let yDom := coTwDom' y ; let yCod := coTwCod' y ; let yArr := coTwArr' y
    let domArr := coTwDomArr' f ; let codArr := coTwCodArr' f
    twOpHomMk'
      (x := ⟨(yDom, yCod), yArr⟩)
      (y := ⟨(xDom, xCod), xArr⟩)
      domArr codArr (coTwHomComm' f)
  map_id x := by apply twOpHom'_ext <;> rfl
  map_comp {x y z} f g := by apply twOpHom'_ext <;> rfl

/--
Functor from `(TwistedArrowOp' C)ᵒᵖ'` to `CoTwistedArrow C`.
-/
def twistedArrowOpOp'ToCoTwistedArrow :
    (TwistedArrowOp' C)ᵒᵖ' ⥤ CoTwistedArrow C where
  obj x :=
    let dom := twOpDom' x ; let cod := twOpCod' x ; let arr := twOpArr' x
    ⟨(cod, dom), arr⟩
  map {x y} f :=
    let xDom := twOpDom' x ; let xCod := twOpCod' x ; let xArr := twOpArr' x
    let yDom := twOpDom' y ; let yCod := twOpCod' y ; let yArr := twOpArr' y
    let domArr := twOpDomArr' (C := C) f ; let codArr := twOpCodArr' (C := C) f
    coTwHomMk'
      (x := ⟨(xCod, xDom), xArr⟩)
      (y := ⟨(yCod, yDom), yArr⟩)
      domArr codArr (twOpHomComm' (C := C) f)
  map_id x := by apply coTwHom'_ext <;> rfl
  map_comp {x y z} f g := by apply coTwHom'_ext <;> rfl

/--
`CoTwistedArrow C` is isomorphic to `(TwistedArrowOp' C)ᵒᵖ'`.
-/
def coTwistedArrowIsoTwistedArrowOpOp' :
    CoTwistedArrow C ≅Cat (TwistedArrowOp' C)ᵒᵖ' where
  hom := coTwistedArrowToTwistedArrowOpOp'
  inv := twistedArrowOpOp'ToCoTwistedArrow
  hom_inv_id := rfl
  inv_hom_id := rfl

/--
`TwistedArrowOp' C` is definitionally equal to `TwistedArrow' (Cᵒᵖ')`.

Both are defined as the category of elements of `homOp'`, but Lean needs explicit
coercion. We provide this as an equality rather than an isomorphism.
-/
theorem twistedArrowOpEqTwistedArrowOfOp' :
    TwistedArrowOp' C = TwistedArrow' (Cᵒᵖ') := rfl

/--
`OpTwistedArrow' (Cᵒᵖ')` is definitionally equal to `CoTwistedArrow C`.

Both are defined as `ElementsContra'` of `homPreOp'`.
-/
theorem opTwistedArrowOfOpEqCoTwistedArrow :
    OpTwistedArrow' (Cᵒᵖ') = CoTwistedArrow C := rfl

end TwistedArrowIsomorphisms

section TwistedArrowAsGrothendieck

/-!
## Twisted Arrow Categories as Grothendieck Constructions

This section establishes that twisted arrow categories can be expressed as
Grothendieck constructions over Under/Over categories.

The equivalences are:
- `TwistedArrow' C ≅ Grothendieck (Under.mapFunctor C)`

where `Under.mapFunctor : Cᵒᵖ ⥤ Cat` maps `op x` to `Under x`.

This formulation enables cleaner functor constructions by leveraging the
existing `FunctorFromData` infrastructure.
-/

variable {C : Type u} [Category.{v} C]

/--
Object map for the functor from `TwistedArrow' C` to
`Grothendieck (Under.mapFunctor C)`.

A twisted arrow `(x, y, f : x ⟶ y)` maps to `(op x, (y, f) ∈ Under x)`.
-/
def twArrToGrothendieckUnderObj (tw : TwistedArrow' C) :
    Grothendieck (Under.mapFunctor C) :=
  ⟨Opposite.op (twDom' tw), Under.mk (twArr' tw)⟩

/--
Commutativity proof for the morphism map to Grothendieck.
The form matches what `Under.homMk` expects: `(domArr ≫ f) ≫ codArr = f'`.
-/
lemma twArrToGrothendieckUnder_comm {tw tw' : TwistedArrow' C} (m : tw ⟶ tw') :
    (twDomArr' m ≫ twArr' tw) ≫ twCodArr' m = twArr' tw' := by
  rw [Category.assoc]
  exact twHomComm' m

/--
The fiber morphism for the Grothendieck construction, as an Under morphism.
-/
def twArrToGrothendieckUnderFiber {tw tw' : TwistedArrow' C} (m : tw ⟶ tw') :
    (Under.map (twDomArr' m)).obj (Under.mk (twArr' tw)) ⟶ Under.mk (twArr' tw') :=
  Under.homMk (twCodArr' m) (by
    simp only [Under.map_obj_hom, Under.mk_hom]
    exact twArrToGrothendieckUnder_comm m)

/--
Morphism map for the functor from `TwistedArrow' C` to
`Grothendieck (Under.mapFunctor C)`.
-/
def twArrToGrothendieckUnderMap {tw tw' : TwistedArrow' C} (m : tw ⟶ tw') :
    twArrToGrothendieckUnderObj tw ⟶ twArrToGrothendieckUnderObj tw' :=
  ⟨(twDomArr' m).op, twArrToGrothendieckUnderFiber m⟩

/--
Functor from `TwistedArrow' C` to `Grothendieck (Under.mapFunctor C)`.
-/
def twArrToGrothendieckUnder : TwistedArrow' C ⥤ Grothendieck (Under.mapFunctor C) where
  obj := twArrToGrothendieckUnderObj
  map := twArrToGrothendieckUnderMap
  map_id tw := by
    simp only [twArrToGrothendieckUnderMap, twArrToGrothendieckUnderFiber, twDomArr'_id,
      twCodArr'_id]
    fapply Grothendieck.ext
    · rfl
    · simp only [eqToHom_refl, Category.id_comp, Grothendieck.id_fiber]
      apply CommaMorphism.ext
      · rfl
      · simp only [Under.homMk_right]
        rw [Under.eqToHom_right, eqToHom_refl]
        rfl
  map_comp {tw tw' tw''} m m' := by
    simp only [twArrToGrothendieckUnderMap, twArrToGrothendieckUnderFiber, twDomArr'_comp,
      twCodArr'_comp]
    fapply Grothendieck.ext
    · simp only [Grothendieck.comp_base, op_comp]
    · simp only [Grothendieck.comp_fiber, Under.mapFunctor_map]
      apply CommaMorphism.ext
      · rfl
      · rw [Comma.comp_right, Comma.comp_right, Comma.comp_right]
        rw [Under.eqToHom_right, Under.eqToHom_right]
        simp only [Under.homMk_right, eqToHom_refl, Category.id_comp]
        congr 1

/--
Object map for the functor from `Grothendieck (Under.mapFunctor C)` to
`TwistedArrow' C`.
-/
def grothendieckUnderToTwArrObj (g : Grothendieck (Under.mapFunctor C)) :
    TwistedArrow' C :=
  twObjMk' g.fiber.hom

/--
Morphism map for the functor from `Grothendieck (Under.mapFunctor C)` to
`TwistedArrow' C`.
-/
def grothendieckUnderToTwArrMap {g g' : Grothendieck (Under.mapFunctor C)}
    (m : g ⟶ g') : grothendieckUnderToTwArrObj g ⟶ grothendieckUnderToTwArrObj g' := by
  refine twHomMk' m.base.unop m.fiber.right ?_
  simp only [grothendieckUnderToTwArrObj, twObjMk'_arr]
  have h := Under.w m.fiber
  simp only [Under.mapFunctor_map, Under.map_obj_hom] at h
  rw [← Category.assoc]
  exact h

/--
Functor from `Grothendieck (Under.mapFunctor C)` to `TwistedArrow' C`.
-/
def grothendieckUnderToTwArr : Grothendieck (Under.mapFunctor C) ⥤ TwistedArrow' C where
  obj := grothendieckUnderToTwArrObj
  map := grothendieckUnderToTwArrMap
  map_id g := by
    apply twHom'_ext
    · simp only [grothendieckUnderToTwArrMap, twHomMk'_domArr, Grothendieck.id_base]
      rfl
    · simp only [grothendieckUnderToTwArrMap, twHomMk'_codArr, Grothendieck.id_fiber,
        twCodArr'_id]
      rw [Under.eqToHom_right]
      rfl
  map_comp {g g' g''} m m' := by
    apply twHom'_ext
    · simp only [grothendieckUnderToTwArrMap, twHomMk'_domArr, Grothendieck.comp_base,
        unop_comp, twDomArr'_comp]
    · simp only [grothendieckUnderToTwArrMap, twHomMk'_codArr, Grothendieck.comp_fiber,
        Under.mapFunctor_map, twCodArr'_comp]
      rw [Comma.comp_right, Comma.comp_right]
      rw [Under.eqToHom_right]
      simp only [eqToHom_refl, Category.id_comp]
      congr 1

/--
The equivalence between `TwistedArrow' C` and `Grothendieck (Under.mapFunctor C)`.

This establishes that twisted arrow categories ARE Grothendieck constructions
over the Under functor, enabling the use of `FunctorFromData` infrastructure.
-/
def twArrEquivGrothendieckUnder : TwistedArrow' C ≌ Grothendieck (Under.mapFunctor C) where
  functor := twArrToGrothendieckUnder
  inverse := grothendieckUnderToTwArr
  unitIso := NatIso.ofComponents
    (fun tw => Iso.refl tw)
    (fun {tw tw'} m => by simp [grothendieckUnderToTwArr, grothendieckUnderToTwArrObj,
          grothendieckUnderToTwArrMap, twArrToGrothendieckUnder, twArrToGrothendieckUnderObj,
          twArrToGrothendieckUnderMap, twArrToGrothendieckUnderFiber])
  counitIso := NatIso.ofComponents
    (fun g => Iso.refl g)
    (fun {g g'} m => by
      fapply Grothendieck.ext
      · simp only [Functor.comp_map, Functor.id_map, Grothendieck.comp_base, Grothendieck.id_base,
          Iso.refl_hom, twArrToGrothendieckUnder, grothendieckUnderToTwArr,
          twArrToGrothendieckUnderMap, grothendieckUnderToTwArrMap, twHomMk'_domArr,
          Quiver.Hom.op_unop]
        rw [@Category.comp_id _ _ _ _ m.base, @Category.id_comp _ _ _ _ m.base]
      · simp only [Functor.comp_map, Functor.id_map, Grothendieck.comp_fiber, Grothendieck.id_fiber,
          Iso.refl_hom, Under.mapFunctor_map]
        simp only [twArrToGrothendieckUnder, grothendieckUnderToTwArr, twArrToGrothendieckUnderMap,
          twArrToGrothendieckUnderFiber, grothendieckUnderToTwArrMap, twHomMk'_codArr]
        apply CommaMorphism.ext
        · simp only [eq_iff_true_of_subsingleton]
        · simp_all)

end TwistedArrowAsGrothendieck

end TwistedArrowCategories

end GebLean
