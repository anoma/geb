import GebLean.Utilities.Elements
import GebLean.Utilities.Profunctors
import GebLean.Utilities.Grothendieck
import GebLean.Utilities.Slice
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Arrow
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

variable {C : Type u} [Category.{v} C]

section TwistedArrowHelpers

/--
Construct an object of `TwistedArrow C` from domain, codomain, and arrow.
-/
def twObjMk {dom cod : C} (arr : dom ⟶ cod) : TwistedArrow C :=
  ⟨(Opposite.op dom, cod), arr⟩

/--
Extract the domain from an object of `TwistedArrow C`.
-/
def twDom (x : TwistedArrow C) : C := x.fst.1.unop

/--
Extract the codomain from an object of `TwistedArrow C`.
-/
def twCod (x : TwistedArrow C) : C := x.fst.2

/--
Extract the arrow from an object of `TwistedArrow C`.
-/
def twArr (x : TwistedArrow C) : twDom x ⟶ twCod x := x.snd

lemma twObjMk_dom {dom cod : C} (arr : dom ⟶ cod) :
    twDom (twObjMk arr) = dom := rfl

lemma twObjMk_cod {dom cod : C} (arr : dom ⟶ cod) :
    twCod (twObjMk arr) = cod := rfl

lemma twObjMk_arr {dom cod : C} (arr : dom ⟶ cod) :
    twArr (twObjMk arr) = arr := rfl

/--
Reconstructing a twisted arrow object from its components gives the original.
-/
@[simp]
lemma twObjMk_twArr (x : TwistedArrow C) : twObjMk (twArr x) = x := rfl

/--
Construct a morphism in `TwistedArrow C` from morphisms on domains and
codomains.

A morphism from `(X, Y, f)` to `(X', Y', f')` consists of:
- `domArr : X' ⟶ X` (morphism between domains, going backwards)
- `codArr : Y ⟶ Y'` (morphism between codomains, going forwards)
such that the square commutes: `domArr ≫ f ≫ codArr = f'`.
-/
def twHomMk {x y : TwistedArrow C}
    (domArr : twDom y ⟶ twDom x)
    (codArr : twCod x ⟶ twCod y)
    (comm : domArr ≫ twArr x ≫ codArr = twArr y) : x ⟶ y :=
  CategoryOfElements.homMk x y (domArr.op, codArr) comm

/--
Extract the domain arrow from a morphism in `TwistedArrow C`.
-/
def twDomArr {x y : TwistedArrow C} (f : x ⟶ y) : twDom y ⟶ twDom x :=
  f.val.1.unop

/--
Extract the codomain arrow from a morphism in `TwistedArrow C`.
-/
def twCodArr {x y : TwistedArrow C} (f : x ⟶ y) : twCod x ⟶ twCod y :=
  f.val.2

lemma twHomMk_domArr {x y : TwistedArrow C}
    (domArr : twDom y ⟶ twDom x)
    (codArr : twCod x ⟶ twCod y)
    (comm : domArr ≫ twArr x ≫ codArr = twArr y) :
    twDomArr (twHomMk domArr codArr comm) = domArr := rfl

lemma twHomMk_codArr {x y : TwistedArrow C}
    (domArr : twDom y ⟶ twDom x)
    (codArr : twCod x ⟶ twCod y)
    (comm : domArr ≫ twArr x ≫ codArr = twArr y) :
    twCodArr (twHomMk domArr codArr comm) = codArr := rfl

/--
Extract the commutativity condition from a morphism in `TwistedArrow C`.
-/
lemma twHomComm {x y : TwistedArrow C} (f : x ⟶ y) :
    twDomArr f ≫ twArr x ≫ twCodArr f = twArr y :=
  f.property

@[ext]
lemma twHom_ext {x y : TwistedArrow C} (f g : x ⟶ y)
    (hdom : twDomArr f = twDomArr g)
    (hcod : twCodArr f = twCodArr g) : f = g := by
  cases f; cases g
  congr
  exact Prod.ext (Opposite.unop_injective hdom) hcod

@[simp]
lemma twHomMk_eta {x y : TwistedArrow C} (f : x ⟶ y) :
    twHomMk (twDomArr f) (twCodArr f) (twHomComm f) = f := by
  apply twHom_ext <;> simp only [twHomMk_domArr, twHomMk_codArr]

@[simp]
lemma twDomArr_id (tw : TwistedArrow C) : twDomArr (𝟙 tw) = 𝟙 (twDom tw) := rfl

@[simp]
lemma twCodArr_id (tw : TwistedArrow C) : twCodArr (𝟙 tw) = 𝟙 (twCod tw) := rfl

@[simp]
lemma twDomArr_comp {x y z : TwistedArrow C} (f : x ⟶ y) (g : y ⟶ z) :
    twDomArr (f ≫ g) = twDomArr g ≫ twDomArr f := rfl

@[simp]
lemma twCodArr_comp {x y z : TwistedArrow C} (f : x ⟶ y) (g : y ⟶ z) :
    twCodArr (f ≫ g) = twCodArr f ≫ twCodArr g := rfl

@[simp]
lemma twDomArr_eqToHom {x y : TwistedArrow C} (h : x = y) :
    twDomArr (eqToHom h) = eqToHom (congrArg twDom h).symm := by
  cases h; rfl

@[simp]
lemma twCodArr_eqToHom {x y : TwistedArrow C} (h : x = y) :
    twCodArr (eqToHom h) = eqToHom (congrArg twCod h) := by
  cases h; rfl

end TwistedArrowHelpers

/--
The co-twisted arrow category of `C`, defined as the presheaf category of
elements of `homPreOp`.

Objects are triples `(dom, cod, arr : cod ⟶ dom)` where the arrow points
from codomain to domain (opposite direction from `TwistedArrow`).

Since `homPreOp : (Cᵒᵖᵒᵖ × Cᵒᵖ)ᵒᵖ ⥤ Type v`, its `ElementsPre` has objects
`Opposite.op ⟨p, x⟩` where `p : Cᵒᵖᵒᵖ × Cᵒᵖ` and `x : homPreOp.obj (op p)`.
-/
abbrev CoTwistedArrow (C : Type u) [Category.{v} C] :=
  (homPreOp (C := C)).ElementsPre

instance (C : Type u) [Category.{v} C] : Category (CoTwistedArrow C) :=
  inferInstanceAs (Category (homPreOp (C := C)).ElementsPre)

section CoTwistedArrowHelpers

variable {C : Type u} [Category.{v} C]

/--
Extract the domain from an object of `CoTwistedArrow C`.

For `tw : CoTwistedArrow C = (homPreOp C).ElementsPre`, the underlying
element structure is:
- `tw.unop : (homPreOp C).Elements` is `⟨p, x⟩`
- `tw.unop.fst : (Cᵒᵖᵒᵖ × Cᵒᵖ)ᵒᵖ`
- `tw.unop.fst.unop : Cᵒᵖᵒᵖ × Cᵒᵖ`
- With encoding `(op (op cod), op dom)`:
  - `.1.unop.unop` gives `cod`
  - `.2.unop` gives `dom`
-/
def coTwDom (tw : CoTwistedArrow C) : C := tw.unop.fst.unop.2.unop

/--
Extract the codomain from an object of `CoTwistedArrow C`.
-/
def coTwCod (tw : CoTwistedArrow C) : C := tw.unop.fst.unop.1.unop.unop

/--
Construct an object of `CoTwistedArrow C` from domain, codomain, and arrow.
The arrow goes from `cod` to `dom`.

The structure is `Opposite.op ⟨p, x⟩` where:
- `p : (Cᵒᵖᵒᵖ × Cᵒᵖ)ᵒᵖ` encodes `(op (op cod), op dom)`
- `x : homPreOp.obj p = cod ⟶ dom` is the arrow
-/
def coTwObjMk {dom cod : C} (arr : cod ⟶ dom) : CoTwistedArrow C :=
  Opposite.op ⟨Opposite.op (Opposite.op (Opposite.op cod), Opposite.op dom),
    homPreOpObjIn arr⟩

/--
Extract the arrow from an object of `CoTwistedArrow C`.
The arrow goes from `coTwCod tw` to `coTwDom tw`.
-/
def coTwArr (tw : CoTwistedArrow C) : coTwCod tw ⟶ coTwDom tw :=
  homPreOpObjOut tw.unop.snd

/--
Extract the domain arrow from a morphism in `CoTwistedArrow C`.

Since `CoTwistedArrow C = (homPreOp C).Elementsᵒᵖ`, morphisms are reversed:
a morphism `f : x ⟶ y` in `CoTwistedArrow C` corresponds to
`f.unop : y.unop ⟶ x.unop` in `(homPreOp C).Elements`.

The `.val` of such a morphism is a morphism in `(Cᵒᵖᵒᵖ × Cᵒᵖ)ᵒᵖ`.
The domain goes backwards (from `y` to `x`), matching `CoTwistedArrow'`.
-/
def coTwDomArr {x y : CoTwistedArrow C} (f : x ⟶ y) :
    coTwDom y ⟶ coTwDom x :=
  f.unop.val.unop.2.unop

/--
Extract the codomain arrow from a morphism in `CoTwistedArrow C`.
The codomain goes forwards (from `x` to `y`), matching `CoTwistedArrow'`.
-/
def coTwCodArr {x y : CoTwistedArrow C} (f : x ⟶ y) :
    coTwCod x ⟶ coTwCod y :=
  f.unop.val.unop.1.unop.unop

@[simp]
lemma coTwObjMk_dom {dom cod : C} (arr : cod ⟶ dom) :
    coTwDom (coTwObjMk arr) = dom := rfl

@[simp]
lemma coTwObjMk_cod {dom cod : C} (arr : cod ⟶ dom) :
    coTwCod (coTwObjMk arr) = cod := rfl

@[simp]
lemma coTwObjMk_arr {dom cod : C} (arr : cod ⟶ dom) :
    coTwArr (coTwObjMk arr) = arr := by
  unfold coTwArr coTwObjMk
  simp only [homPreOpObjOut, homPreOpObjIn]

/--
A co-twisted arrow equals its reconstruction from components.
This provides a canonical form for any co-twisted arrow.
-/
@[simp]
lemma coTw_eq_coTwObjMk (tw : CoTwistedArrow C) :
    tw = coTwObjMk (coTwArr tw) := by
  unfold coTwObjMk coTwArr coTwCod coTwDom homPreOpObjIn homPreOpObjOut
  rw [← Opposite.unop_inj_iff]
  apply Sigma.ext
  · simp only [Opposite.op_unop]
  · simp only [heq_eq_eq]

/--
The diagonal co-twisted arrow for an object `A : C`, which is the identity
morphism `𝟙 A` viewed as a co-twisted arrow from `A` to `A`.
-/
abbrev diagCoTwArr (A : C) : CoTwistedArrow C := coTwObjMk (𝟙 A)

@[simp]
lemma diagCoTwArr_dom (A : C) : coTwDom (diagCoTwArr A) = A := rfl

@[simp]
lemma diagCoTwArr_cod (A : C) : coTwCod (diagCoTwArr A) = A := rfl

@[simp]
lemma diagCoTwArr_arr (A : C) : coTwArr (diagCoTwArr A) = 𝟙 A := coTwObjMk_arr (𝟙 A)

/--
Construct a morphism in `CoTwistedArrow C` from morphisms on domains and
codomains.

A morphism from `x` to `y` consists of:
- `domArr : coTwDom y ⟶ coTwDom x` (morphism between domains, going backwards)
- `codArr : coTwCod x ⟶ coTwCod y` (morphism between codomains, going forwards)
such that the square commutes: `codArr ≫ coTwArr y ≫ domArr = coTwArr x`.
-/
def coTwHomMk {x y : CoTwistedArrow C}
    (domArr : coTwDom y ⟶ coTwDom x)
    (codArr : coTwCod x ⟶ coTwCod y)
    (comm : codArr ≫ coTwArr y ≫ domArr = coTwArr x) : x ⟶ y :=
  Quiver.Hom.op (CategoryOfElements.homMk y.unop x.unop
    (Quiver.Hom.op (codArr.op.op, domArr.op))
    (by
      unfold coTwArr coTwCod coTwDom at comm
      simp only [homPreOp, profunctorPreOp, profunctorPre, profunctorOp,
        Functor.comp_map, Functor.hom_map]
      exact comm))

@[simp]
lemma coTwHomMk_domArr {x y : CoTwistedArrow C}
    (domArr : coTwDom y ⟶ coTwDom x)
    (codArr : coTwCod x ⟶ coTwCod y)
    (comm : codArr ≫ coTwArr y ≫ domArr = coTwArr x) :
    coTwDomArr (coTwHomMk domArr codArr comm) = domArr := rfl

@[simp]
lemma coTwCodArr_coTwHomMk {x y : CoTwistedArrow C}
    (domArr : coTwDom y ⟶ coTwDom x)
    (codArr : coTwCod x ⟶ coTwCod y)
    (comm : codArr ≫ coTwArr y ≫ domArr = coTwArr x) :
    coTwCodArr (coTwHomMk domArr codArr comm) = codArr := rfl

@[simp]
lemma coTwDomArr_coTwHomMk {x y : CoTwistedArrow C}
    (domArr : coTwDom y ⟶ coTwDom x)
    (codArr : coTwCod x ⟶ coTwCod y)
    (comm : codArr ≫ coTwArr y ≫ domArr = coTwArr x) :
    coTwDomArr (coTwHomMk domArr codArr comm) = domArr := rfl

/--
Extract the commutativity condition from a morphism in `CoTwistedArrow C`.
-/
lemma coTwHomComm {x y : CoTwistedArrow C} (f : x ⟶ y) :
    coTwCodArr f ≫ coTwArr y ≫ coTwDomArr f = coTwArr x := by
  unfold coTwCodArr coTwDomArr coTwArr coTwCod coTwDom homPreOpObjOut
  have h := f.unop.property
  simp only [homPreOp, profunctorPreOp, profunctorPre, profunctorOp,
    Functor.comp_map, Functor.hom_map] at h
  exact h

@[ext]
lemma coTwHom_ext {x y : CoTwistedArrow C} (f g : x ⟶ y)
    (hdom : coTwDomArr f = coTwDomArr g)
    (hcod : coTwCodArr f = coTwCodArr g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  unfold coTwCodArr at hcod
  unfold coTwDomArr at hdom
  apply Prod.ext
  · exact congr_arg (fun x => x.op.op) hcod
  · exact congr_arg Quiver.Hom.op hdom

@[simp]
lemma coTwDomArr_id (tw : CoTwistedArrow C) :
    coTwDomArr (𝟙 tw) = 𝟙 (coTwDom tw) := rfl

@[simp]
lemma coTwCodArr_id (tw : CoTwistedArrow C) :
    coTwCodArr (𝟙 tw) = 𝟙 (coTwCod tw) := rfl

@[simp]
lemma coTwDomArr_comp {x y z : CoTwistedArrow C} (f : x ⟶ y) (g : y ⟶ z) :
    coTwDomArr (f ≫ g) = coTwDomArr g ≫ coTwDomArr f := rfl

@[simp]
lemma coTwCodArr_comp {x y z : CoTwistedArrow C} (f : x ⟶ y) (g : y ⟶ z) :
    coTwCodArr (f ≫ g) = coTwCodArr f ≫ coTwCodArr g := rfl

end CoTwistedArrowHelpers

section TwistedArrowSelfDualityUnprimed

/-!
## Self-Duality for Unprimed Twisted Arrow Categories

The twisted arrow category is self-dual: `TwistedArrow C ≌ TwistedArrow (Cᵒᵖ)`.

This equivalence swaps domain and codomain while taking the opposite of the
arrow. Combined with the op functor, this gives the equivalence
`(TwistedArrow C)ᵒᵖ ≌ CoTwistedArrow C`.
-/

variable {C : Type u} [Category.{v} C]

/--
Functor from `TwistedArrow C` to `TwistedArrow (Cᵒᵖ)`.

Sends `(dom, cod, f : dom ⟶ cod)` to `(op cod, op dom, f.op : op cod ⟶ op dom)`.
-/
def twistedArrowToTwistedArrowOp : TwistedArrow C ⥤ TwistedArrow (Cᵒᵖ) where
  obj := fun tw => twObjMk (twArr tw).op
  map := fun {x y} m =>
    twHomMk (twCodArr m).op (twDomArr m).op (by
      simp only [twObjMk_arr, ← op_comp, Category.assoc, twHomComm])
  map_id := fun tw => by apply twHom_ext <;> rfl
  map_comp := fun {x y z} f g => by apply twHom_ext <;> rfl

/--
Functor from `TwistedArrow (Cᵒᵖ)` to `TwistedArrow C`.

Sends `(dom', cod', f' : dom' ⟶ cod')` where `dom', cod' : Cᵒᵖ`
to `(cod'.unop, dom'.unop, f'.unop)`.
-/
def twistedArrowOpToTwistedArrow : TwistedArrow (Cᵒᵖ) ⥤ TwistedArrow C where
  obj := fun tw => twObjMk (twArr tw).unop
  map := fun {x y} m =>
    twHomMk (twCodArr m).unop (twDomArr m).unop (by
      simp only [twObjMk_arr, ← unop_comp, Category.assoc, twHomComm])
  map_id := fun tw => by apply twHom_ext <;> rfl
  map_comp := fun {x y z} f g => by apply twHom_ext <;> rfl

/--
Round-trip from `TwistedArrow C` through `TwistedArrow (Cᵒᵖ)` and back
gives the identity on objects.
-/
theorem twistedArrowRoundTrip_obj (tw : TwistedArrow C) :
    twistedArrowOpToTwistedArrow.obj (twistedArrowToTwistedArrowOp.obj tw) = tw := by
  simp only [twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow, twObjMk]
  rfl

/--
Round-trip from `TwistedArrow (Cᵒᵖ)` through `TwistedArrow C` and back
gives the identity on objects.
-/
theorem twistedArrowOpRoundTrip_obj (tw : TwistedArrow (Cᵒᵖ)) :
    twistedArrowToTwistedArrowOp.obj (twistedArrowOpToTwistedArrow.obj tw) = tw := by
  simp only [twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow, twObjMk]
  rfl

/--
Round-trip preserves morphisms on domain component.
-/
@[simp]
theorem twistedArrowRoundTrip_map_domArr {x y : TwistedArrow C} (f : x ⟶ y) :
    twDomArr ((twistedArrowToTwistedArrowOp ⋙ twistedArrowOpToTwistedArrow).map f) =
    twDomArr f := by
  simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
    twHomMk_domArr, twHomMk_codArr, Quiver.Hom.unop_op]

/--
Round-trip preserves morphisms on codomain component.
-/
@[simp]
theorem twistedArrowRoundTrip_map_codArr {x y : TwistedArrow C} (f : x ⟶ y) :
    twCodArr ((twistedArrowToTwistedArrowOp ⋙ twistedArrowOpToTwistedArrow).map f) =
    twCodArr f := by
  simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
    twHomMk_domArr, twHomMk_codArr, Quiver.Hom.unop_op]

/--
Round-trip preserves morphisms on domain component (opposite direction).
-/
@[simp]
theorem twistedArrowOpRoundTrip_map_domArr {x y : TwistedArrow (Cᵒᵖ)} (f : x ⟶ y) :
    twDomArr ((twistedArrowOpToTwistedArrow ⋙ twistedArrowToTwistedArrowOp).map f) =
    twDomArr f := by
  simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
    twHomMk_domArr, twHomMk_codArr, Quiver.Hom.op_unop]

/--
Round-trip preserves morphisms on codomain component (opposite direction).
-/
@[simp]
theorem twistedArrowOpRoundTrip_map_codArr {x y : TwistedArrow (Cᵒᵖ)} (f : x ⟶ y) :
    twCodArr ((twistedArrowOpToTwistedArrow ⋙ twistedArrowToTwistedArrowOp).map f) =
    twCodArr f := by
  simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
    twHomMk_domArr, twHomMk_codArr, Quiver.Hom.op_unop]

/--
The round-trip `inverse ⋙ functor` is definitionally the identity functor.
-/
theorem twistedArrowRoundTrip_map {x y : TwistedArrow C} (f : x ⟶ y) :
    (twistedArrowToTwistedArrowOp ⋙ twistedArrowOpToTwistedArrow).map f = f := by
  apply twHom_ext
  · simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
      twHomMk_domArr, twHomMk_codArr, Quiver.Hom.unop_op]
  · simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
      twHomMk_domArr, twHomMk_codArr, Quiver.Hom.unop_op]

/--
The round-trip `functor ⋙ inverse` is definitionally the identity functor.
-/
theorem twistedArrowOpRoundTrip_map {x y : TwistedArrow (Cᵒᵖ)} (f : x ⟶ y) :
    (twistedArrowOpToTwistedArrow ⋙ twistedArrowToTwistedArrowOp).map f = f := by
  apply twHom_ext
  · simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
      twHomMk_domArr, twHomMk_codArr, Quiver.Hom.op_unop]
  · simp only [Functor.comp_map, twistedArrowToTwistedArrowOp, twistedArrowOpToTwistedArrow,
      twHomMk_domArr, twHomMk_codArr, Quiver.Hom.op_unop]

/--
The twisted arrow category is self-dual: `TwistedArrow C ≌ TwistedArrow (Cᵒᵖ)`.
-/
def twistedArrowEquivTwistedArrowOp : TwistedArrow C ≌ TwistedArrow (Cᵒᵖ) where
  functor := twistedArrowToTwistedArrowOp
  inverse := twistedArrowOpToTwistedArrow
  unitIso := NatIso.ofComponents
    (fun tw => eqToIso (twistedArrowRoundTrip_obj tw).symm)
    (fun {x y} f => by
      simp only [eqToIso.hom, Functor.id_obj, Functor.comp_obj, Functor.id_map]
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact (twistedArrowRoundTrip_map f).symm)
  counitIso := NatIso.ofComponents
    (fun tw => eqToIso (twistedArrowOpRoundTrip_obj tw))
    (fun {x y} f => by
      simp only [eqToIso.hom, Functor.comp_obj, Functor.id_obj, Functor.id_map]
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact twistedArrowOpRoundTrip_map f)

/--
The categorical isomorphism `Cat.of (TwistedArrow C) ≅ Cat.of (TwistedArrow (Cᵒᵖ))`.
This is stronger than the equivalence, showing that the two categories are
isomorphic as objects in `Cat`. The round-trip functors are definitionally
the identity on objects.
-/
def twistedArrowIsoTwistedArrowOp :
    TwistedArrow C ≅Cat TwistedArrow (Cᵒᵖ) :=
  Cat.isoOfEquiv
    twistedArrowEquivTwistedArrowOp
    twistedArrowRoundTrip_obj
    twistedArrowOpRoundTrip_obj

/--
The categorical isomorphism `(TwistedArrow C)ᵒᵖ ≅ (TwistedArrow (Cᵒᵖ))ᵒᵖ` in Cat,
obtained by applying `Cat.opFunctor` to `twistedArrowIsoTwistedArrowOp`.

This uses the fact that `Cat.opFunctor.mapIso` preserves isomorphisms:
applying `op` to `TwistedArrow C ≅ TwistedArrow (Cᵒᵖ)` yields
`(TwistedArrow C)ᵒᵖ ≅ (TwistedArrow (Cᵒᵖ))ᵒᵖ`.
-/
def twistedArrowOpIsoTwistedArrowOpOp :
    (TwistedArrow C)ᵒᵖ ≅Cat (TwistedArrow (Cᵒᵖ))ᵒᵖ :=
  Cat.opFunctor.mapIso twistedArrowIsoTwistedArrowOp

/--
The equivalence `(TwistedArrow C)ᵒᵖ ≌ (TwistedArrow (Cᵒᵖ))ᵒᵖ` derived from the
categorical isomorphism via `Cat.equivOfIso`.
-/
def twistedArrowOpEquivTwistedArrowOpOp :
    (TwistedArrow C)ᵒᵖ ≌ (TwistedArrow (Cᵒᵖ))ᵒᵖ :=
  Cat.equivOfIso twistedArrowOpIsoTwistedArrowOpOp

/-!
### Isomorphism between `(TwistedArrow (Cᵒᵖ))ᵒᵖ` and `CoTwistedArrow C`

Objects of `TwistedArrow (Cᵒᵖ)` are triples `(dom, cod, arr)` where:
- `dom : Cᵒᵖ` (domain in opposite category)
- `cod : Cᵒᵖ` (codomain in opposite category)
- `arr : dom ⟶ cod` in `Cᵒᵖ`, which corresponds to `cod.unop ⟶ dom.unop` in `C`

Objects of `CoTwistedArrow C` are triples `(dom, cod, arr)` where:
- `dom : C` (domain)
- `cod : C` (codomain)
- `arr : cod ⟶ dom` in `C`

The correspondence maps `TwistedArrow (Cᵒᵖ)` object `(dom_op, cod_op, arr)` to
`CoTwistedArrow C` object `(dom_op.unop, cod_op.unop, arr')` where `arr'` is the
corresponding morphism in `C`.
-/

/--
Functor from `(TwistedArrow (Cᵒᵖ))ᵒᵖ` to `CoTwistedArrow C`.

Maps `op tw` where `tw : TwistedArrow (Cᵒᵖ)` to the corresponding co-twisted
arrow with domain `(twDom tw).unop` and codomain `(twCod tw).unop`.
-/
def twistedArrowOpOpToCoTwistedArrow : (TwistedArrow (Cᵒᵖ))ᵒᵖ ⥤ CoTwistedArrow C where
  obj tw :=
    let t := tw.unop
    coTwObjMk (twArr t).unop
  map {x y} f :=
    let g := f.unop
    coTwHomMk
      (domArr := (twDomArr g).unop)
      (codArr := (twCodArr g).unop)
      (by
        simp only [coTwObjMk_arr, coTwObjMk_cod, coTwObjMk_dom]
        have h := twHomComm g
        calc (twCodArr g).unop ≫ (twArr y.unop).unop ≫ (twDomArr g).unop
            = ((twCodArr g).unop ≫ (twArr y.unop).unop) ≫ (twDomArr g).unop :=
                (Category.assoc _ _ _).symm
          _ = ((twDomArr g) ≫ (twArr y.unop) ≫ (twCodArr g)).unop := by
                simp only [unop_comp]
          _ = (twArr x.unop).unop := by rw [h])
  map_id tw := by
    apply coTwHom_ext
    · simp only [twDomArr, unop_id, coTwDomArr]; rfl
    · simp only [twCodArr, unop_id, coTwCodArr]; rfl
  map_comp {x y z} f g := by
    apply coTwHom_ext
    · simp only [coTwHomMk_domArr, twDomArr, unop_comp]; rfl
    · simp only [coTwCodArr_coTwHomMk, twCodArr, unop_comp]; rfl

/--
Functor from `CoTwistedArrow C` to `(TwistedArrow (Cᵒᵖ))ᵒᵖ`.

Maps a co-twisted arrow `(dom, cod, arr : cod ⟶ dom)` to `op tw` where
`tw : TwistedArrow (Cᵒᵖ)` has domain `op dom`, codomain `op cod`, and the
corresponding arrow.
-/
def coTwistedArrowToTwistedArrowOpOp : CoTwistedArrow C ⥤ (TwistedArrow (Cᵒᵖ))ᵒᵖ where
  obj tw := Opposite.op (twObjMk (coTwArr tw).op)
  map {x y} f :=
    Quiver.Hom.op (twHomMk
      (domArr := (coTwDomArr f).op)
      (codArr := (coTwCodArr f).op)
      (by
        simp only [twObjMk_arr]
        have h := coTwHomComm f
        calc (coTwDomArr f).op ≫ (coTwArr y).op ≫ (coTwCodArr f).op
            = ((coTwDomArr f).op ≫ (coTwArr y).op) ≫ (coTwCodArr f).op :=
                (Category.assoc _ _ _).symm
          _ = ((coTwCodArr f) ≫ (coTwArr y) ≫ (coTwDomArr f)).op := by
                simp only [op_comp]
          _ = (coTwArr x).op := by rw [h]))
  map_id tw := by
    apply Quiver.Hom.unop_inj
    apply twHom_ext
    · simp only [coTwDomArr, unop_id, twDomArr]; rfl
    · simp only [coTwCodArr, unop_id, twCodArr]; rfl
  map_comp {x y z} f g := by
    apply Quiver.Hom.unop_inj
    apply twHom_ext
    · simp only [coTwDomArr, twDomArr]; rfl
    · simp only [coTwCodArr, twCodArr]; rfl

/--
Round-trip on objects: `(TwistedArrow (Cᵒᵖ))ᵒᵖ → CoTwistedArrow C → (TwistedArrow (Cᵒᵖ))ᵒᵖ`
returns the same object.
-/
theorem twistedArrowOpOpCoTwRoundTrip_obj (tw : (TwistedArrow (Cᵒᵖ))ᵒᵖ) :
    coTwistedArrowToTwistedArrowOpOp.obj (twistedArrowOpOpToCoTwistedArrow.obj tw) = tw := by
  simp only [twistedArrowOpOpToCoTwistedArrow, coTwistedArrowToTwistedArrowOpOp,
    coTwObjMk_arr, Quiver.Hom.op_unop]
  rfl

/--
Round-trip on objects: `CoTwistedArrow C → (TwistedArrow (Cᵒᵖ))ᵒᵖ → CoTwistedArrow C`
returns the same object.
-/
theorem coTwTwistedArrowOpOpRoundTrip_obj (tw : CoTwistedArrow C) :
    twistedArrowOpOpToCoTwistedArrow.obj (coTwistedArrowToTwistedArrowOpOp.obj tw) = tw := by
  simp only [twistedArrowOpOpToCoTwistedArrow, coTwistedArrowToTwistedArrowOpOp,
    twObjMk_arr, Quiver.Hom.unop_op]
  rfl

/--
The equivalence `(TwistedArrow (Cᵒᵖ))ᵒᵖ ≌ CoTwistedArrow C`.
-/
def twistedArrowOpOpEquivCoTwistedArrow :
    (TwistedArrow (Cᵒᵖ))ᵒᵖ ≌ CoTwistedArrow C where
  functor := twistedArrowOpOpToCoTwistedArrow
  inverse := coTwistedArrowToTwistedArrowOpOp
  unitIso := NatIso.ofComponents
    (fun tw => eqToIso (twistedArrowOpOpCoTwRoundTrip_obj tw).symm)
    (fun {x y} f => by
      simp only [eqToIso.hom, Functor.id_obj, Functor.comp_obj, Functor.id_map]
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      apply Quiver.Hom.unop_inj
      apply twHom_ext <;> rfl)
  counitIso := NatIso.ofComponents
    (fun tw => eqToIso (coTwTwistedArrowOpOpRoundTrip_obj tw))
    (fun {x y} f => by
      simp only [eqToIso.hom, Functor.comp_obj, Functor.id_obj, Functor.id_map]
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      apply coTwHom_ext <;> rfl)

/--
The categorical isomorphism `(TwistedArrow (Cᵒᵖ))ᵒᵖ ≅ CoTwistedArrow C` in `Cat`.
-/
def twistedArrowOpOpIsoCoTwistedArrow :
    (TwistedArrow (Cᵒᵖ))ᵒᵖ ≅Cat CoTwistedArrow C :=
  Cat.isoOfEquiv
    twistedArrowOpOpEquivCoTwistedArrow
    twistedArrowOpOpCoTwRoundTrip_obj
    coTwTwistedArrowOpOpRoundTrip_obj

/-!
### Composed isomorphism: `(TwistedArrow C)ᵒᵖ ≅ CoTwistedArrow C`

Composing the isomorphisms:
- `(TwistedArrow C)ᵒᵖ ≅ (TwistedArrow (Cᵒᵖ))ᵒᵖ`
- `(TwistedArrow (Cᵒᵖ))ᵒᵖ ≅ CoTwistedArrow C`

gives the isomorphism `(TwistedArrow C)ᵒᵖ ≅ CoTwistedArrow C`.
-/

/--
The categorical isomorphism `(TwistedArrow C)ᵒᵖ ≅ CoTwistedArrow C` in `Cat`,
obtained by composing the self-duality isomorphism with the
`(TwistedArrow (Cᵒᵖ))ᵒᵖ ≅ CoTwistedArrow C` isomorphism.
-/
def twistedArrowOpIsoCoTwistedArrow :
    (TwistedArrow C)ᵒᵖ ≅Cat CoTwistedArrow C :=
  twistedArrowOpIsoTwistedArrowOpOp ≪≫ twistedArrowOpOpIsoCoTwistedArrow

/--
The equivalence `(TwistedArrow C)ᵒᵖ ≌ CoTwistedArrow C` derived from the
categorical isomorphism.
-/
def twistedArrowOpEquivCoTwistedArrow : (TwistedArrow C)ᵒᵖ ≌ CoTwistedArrow C :=
  Cat.equivOfIso twistedArrowOpIsoCoTwistedArrow

/-!
### Isomorphism: `(CoTwistedArrow C)ᵒᵖ ≅ TwistedArrow (Cᵒᵖ)`

This isomorphism is obtained by composing:
1. `Cat.opFunctor.mapIso twistedArrowOpOpIsoCoTwistedArrow.symm` to get
   `(CoTwistedArrow C)ᵒᵖ ≅ ((TwistedArrow (Cᵒᵖ))ᵒᵖ)ᵒᵖ`
2. `Cat.opFunctorInvolutive.app` to get
   `((TwistedArrow (Cᵒᵖ))ᵒᵖ)ᵒᵖ ≅ TwistedArrow (Cᵒᵖ)`
-/

/--
The categorical isomorphism `(CoTwistedArrow C)ᵒᵖ ≅ TwistedArrow (Cᵒᵖ)` in `Cat`.
-/
def coTwistedArrowOpIsoTwistedArrowOp :
    (CoTwistedArrow C)ᵒᵖ ≅Cat TwistedArrow (Cᵒᵖ) :=
  Cat.opFunctor.mapIso twistedArrowOpOpIsoCoTwistedArrow.symm ≪≫
    Cat.opFunctorInvolutive.app (Cat.of (TwistedArrow (Cᵒᵖ)))

/--
The equivalence `(CoTwistedArrow C)ᵒᵖ ≌ TwistedArrow (Cᵒᵖ)` derived from the
categorical isomorphism.
-/
def coTwistedArrowOpEquivTwistedArrowOp :
    (CoTwistedArrow C)ᵒᵖ ≌ TwistedArrow (Cᵒᵖ) :=
  Cat.equivOfIso coTwistedArrowOpIsoTwistedArrowOp

/-!
### Composed isomorphism: `(CoTwistedArrow C)ᵒᵖ ≅ TwistedArrow C`

Composing the isomorphisms:
- `(CoTwistedArrow C)ᵒᵖ ≅ TwistedArrow (Cᵒᵖ)`
- `TwistedArrow (Cᵒᵖ) ≅ TwistedArrow C` (via `twistedArrowIsoTwistedArrowOp.symm`)

gives the isomorphism `(CoTwistedArrow C)ᵒᵖ ≅ TwistedArrow C`.
-/

/--
The categorical isomorphism `(CoTwistedArrow C)ᵒᵖ ≅ TwistedArrow C` in `Cat`,
obtained by composing `coTwistedArrowOpIsoTwistedArrowOp` with
`twistedArrowIsoTwistedArrowOp.symm`.
-/
def coTwistedArrowOpIsoTwistedArrow :
    (CoTwistedArrow C)ᵒᵖ ≅Cat TwistedArrow C :=
  coTwistedArrowOpIsoTwistedArrowOp ≪≫ twistedArrowIsoTwistedArrowOp.symm

/--
The equivalence `(CoTwistedArrow C)ᵒᵖ ≌ TwistedArrow C` derived from the
categorical isomorphism.
-/
def coTwistedArrowOpEquivTwistedArrow : (CoTwistedArrow C)ᵒᵖ ≌ TwistedArrow C :=
  Cat.equivOfIso coTwistedArrowOpIsoTwistedArrow

/-!
### Object component lemmas for the equivalence

These lemmas relate `twDom`/`twCod` on the twisted arrow side to
`coTwDom`/`coTwCod` on the co-twisted arrow side through the
`coTwistedArrowOpEquivTwistedArrow` equivalence.
-/

/-- The domain of the twisted arrow corresponding to a co-twisted arrow
is the codomain of the co-twisted arrow. -/
theorem coTwistedArrowOpEquiv_obj_dom (tw : CoTwistedArrow C) :
    twDom (coTwistedArrowOpEquivTwistedArrow.functor.obj (Opposite.op tw)) =
    coTwCod tw := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow, Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [twDom, twObjMk, coTwCod]
  rfl

/-- The codomain of the twisted arrow corresponding to a co-twisted arrow
is the domain of the co-twisted arrow. -/
theorem coTwistedArrowOpEquiv_obj_cod (tw : CoTwistedArrow C) :
    twCod (coTwistedArrowOpEquivTwistedArrow.functor.obj (Opposite.op tw)) =
    coTwDom tw := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow, Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [twCod, twObjMk, coTwDom]
  rfl

/-!
### Morphism component lemmas for the equivalence

These lemmas relate `twDomArr`/`twCodArr` on the twisted arrow side to
`coTwDomArr`/`coTwCodArr` on the co-twisted arrow side through the
`coTwistedArrowOpEquivTwistedArrow` equivalence.

For a morphism `f : tw ⟶ tw'` in CoTwistedArrow C:
- After the equivalence, this becomes
  `equiv.map f.op : equiv.obj (op tw') ⟶ equiv.obj (op tw)`
- The `twDomArr` component has type
  `twDom (equiv.obj (op tw)) ⟶ twDom (equiv.obj (op tw'))`,
  which equals `coTwCod tw ⟶ coTwCod tw'` (matching `coTwCodArr f`)
- The `twCodArr` component has type
  `twCod (equiv.obj (op tw')) ⟶ twCod (equiv.obj (op tw))`,
  which equals `coTwDom tw' ⟶ coTwDom tw` (matching `coTwDomArr f`)
-/

/-- The `twDomArr` component of a morphism under the equivalence equals
the `coTwCodArr` of the original morphism (modulo the object correspondence).
The equality holds because `twDom ∘ equiv = coTwCod`. -/
theorem coTwistedArrowOpEquiv_map_twDomArr {tw tw' : CoTwistedArrow C}
    (f : tw ⟶ tw') :
    twDomArr (coTwistedArrowOpEquivTwistedArrow.functor.map f.op) =
    eqToHom (coTwistedArrowOpEquiv_obj_dom tw).symm ≫
    coTwCodArr f ≫ eqToHom (coTwistedArrowOpEquiv_obj_dom tw') := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow, Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.mapIso_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [twDomArr, coTwCodArr]
  rfl

/-- The `twCodArr` component of a morphism under the equivalence equals
the `coTwDomArr` of the original morphism (modulo the object correspondence).
The equality holds because `twCod ∘ equiv = coTwDom`. -/
theorem coTwistedArrowOpEquiv_map_twCodArr {tw tw' : CoTwistedArrow C}
    (f : tw ⟶ tw') :
    twCodArr (coTwistedArrowOpEquivTwistedArrow.functor.map f.op) =
    eqToHom (coTwistedArrowOpEquiv_obj_cod tw').symm ≫
    coTwDomArr f ≫ eqToHom (coTwistedArrowOpEquiv_obj_cod tw) := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow, Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.mapIso_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [twCodArr, coTwDomArr]
  rfl

end TwistedArrowSelfDualityUnprimed

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
Reconstructing a twisted arrow object from its components gives the original.
-/
@[simp]
lemma twObjMk'_twArr' (x : TwistedArrow' C) : twObjMk' (twArr' x) = x := rfl

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
    (by simp only [twObjMk'_dom] ; exact domArr)
    (by simp only [twObjMk'_cod] ; exact codArr)
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
lemma twDomArr'_eqToHom {x y : TwistedArrow' C} (h : x = y) :
    twDomArr' (eqToHom h) = eqToHom (congrArg twDom' h).symm := by
  cases h; rfl

@[simp]
lemma twCodArr'_eqToHom {x y : TwistedArrow' C} (h : x = y) :
    twCodArr' (eqToHom h) = eqToHom (congrArg twCod' h) := by
  cases h; rfl

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
    (by simp only [twOpObjMk'_dom] ; exact domArr)
    (by simp only [twOpObjMk'_cod] ; exact codArr)
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
    (by simp only [opTwObjMk'_dom] ; exact domArr)
    (by simp only [opTwObjMk'_cod] ; exact codArr)
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
def CoTwistedArrow' (C : Type u) [Category.{v} C] :=
  (homPreOp' (C := C)).ElementsContra'

instance (C : Type u) [Category.{v} C] : Category (CoTwistedArrow' C) := by
  unfold CoTwistedArrow'
  infer_instance

section CoTwistedArrow'Helpers

/--
Construct an object of `CoTwistedArrow' C` from domain, codomain, and arrow.
Note: The arrow goes from `cod` to `dom`, and this is the opposite of
`TwistedArrowOp' C`.
-/
def coTwObjMk' {dom cod : C} (arr : cod ⟶ dom) : CoTwistedArrow' C :=
  ⟨(cod, dom), arr⟩

/--
Extract the domain from an object of `CoTwistedArrow' C`.
-/
def coTwDom' (x : CoTwistedArrow' C) : C := x.fst.2

/--
Extract the codomain from an object of `CoTwistedArrow' C`.
-/
def coTwCod' (x : CoTwistedArrow' C) : C := x.fst.1

/--
Extract the arrow from an object of `CoTwistedArrow' C`.
-/
def coTwArr' (x : CoTwistedArrow' C) : coTwCod' x ⟶ coTwDom' x := x.snd

lemma coTwObjMk'_dom {dom cod : C} (arr : cod ⟶ dom) :
    coTwDom' (coTwObjMk' arr) = dom := rfl

lemma coTwObjMk'_cod {dom cod : C} (arr : cod ⟶ dom) :
    coTwCod' (coTwObjMk' arr) = cod := rfl

lemma coTwObjMk'_arr {dom cod : C} (arr : cod ⟶ dom) :
    coTwArr' (coTwObjMk' arr) = arr := rfl

/--
Construct a morphism in `CoTwistedArrow' C` from morphisms on domains and
codomains.

A morphism from `(X, Y, f)` to `(X', Y', f')` consists of:
- `domArr : X' ⟶ X` (morphism between domains, going backwards)
- `codArr : Y ⟶ Y'` (morphism between codomains, going forwards)
such that the square commutes: `codArr ≫ f' ≫ domArr = f`.

Note: This is the opposite of `TwistedArrowOp' C`.
-/
def coTwHomMk' {x y : CoTwistedArrow' C}
    (domArr : coTwDom' y ⟶ coTwDom' x)
    (codArr : coTwCod' x ⟶ coTwCod' y)
    (comm : codArr ≫ coTwArr' y ≫ domArr = coTwArr' x) : x ⟶ y :=
  CategoryOfElements.homMk y x (codArr, domArr)
    (by simp only [homPreOp', profunctorToOp', hom'] ; exact comm)

def coTwHomMkChain' {w x y z : C}
    (codArr : y ⟶ z) (codObjArr : z ⟶ x) (domArr : x ⟶ w) :
    coTwObjMk' (dom := w) (cod := y) (codArr ≫ codObjArr ≫ domArr) ⟶
    coTwObjMk' (dom := x) (cod := z) codObjArr :=
  coTwHomMk'
    (x := coTwObjMk' (dom := w) (cod := y) (codArr ≫ codObjArr ≫ domArr))
    (y := coTwObjMk' (dom := x) (cod := z) codObjArr)
    (by simp only [coTwObjMk'_dom] ; exact domArr)
    (by simp only [coTwObjMk'_cod] ; exact codArr)
    rfl

/--
Extract the domain arrow from a morphism in `CoTwistedArrow' C`.
Note: This goes backwards (from `y`'s domain to `x`'s domain).
-/
def coTwDomArr' {x y : CoTwistedArrow' C} (f : x ⟶ y) :
    coTwDom' y ⟶ coTwDom' x :=
  f.val.2

/--
Extract the codomain arrow from a morphism in `CoTwistedArrow' C`.
-/
def coTwCodArr' {x y : CoTwistedArrow' C} (f : x ⟶ y) :
    coTwCod' x ⟶ coTwCod' y :=
  f.val.1

lemma coTwHomMk'_domArr {x y : CoTwistedArrow' C}
    (domArr : coTwDom' y ⟶ coTwDom' x)
    (codArr : coTwCod' x ⟶ coTwCod' y)
    (comm : codArr ≫ coTwArr' y ≫ domArr = coTwArr' x) :
    coTwDomArr' (coTwHomMk' domArr codArr comm) = domArr := rfl

lemma coTwHomMk'_codArr {x y : CoTwistedArrow' C}
    (domArr : coTwDom' y ⟶ coTwDom' x)
    (codArr : coTwCod' x ⟶ coTwCod' y)
    (comm : codArr ≫ coTwArr' y ≫ domArr = coTwArr' x) :
    coTwCodArr' (coTwHomMk' domArr codArr comm) = codArr := rfl

/--
Extract the commutativity condition from a morphism in `CoTwistedArrow' C`.
-/
lemma coTwHomComm' {x y : CoTwistedArrow' C} (f : x ⟶ y) :
    coTwCodArr' f ≫ coTwArr' y ≫ coTwDomArr' f = coTwArr' x := by
  unfold coTwCodArr' coTwDomArr' coTwArr'
  change f.val.1 ≫ y.snd ≫ f.val.2 = x.snd
  have h := f.property
  simp only [homPreOp', hom', profunctorToOp',
    opProdEquiv, Equivalence.prod_inverse, Equivalence.refl_inverse,
    Cat.equivOfIso, opEquivOp', opIsoOp', catOfOp'ToOp] at h
  exact h

@[ext]
lemma coTwHom'_ext {x y : CoTwistedArrow' C} (f g : x ⟶ y)
    (hdom : coTwDomArr' f = coTwDomArr' g)
    (hcod : coTwCodArr' f = coTwCodArr' g) : f = g := by
  cases f; cases g
  congr
  exact Prod.ext hcod hdom

end CoTwistedArrow'Helpers

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
  hom := opTwistedArrowToTwistedArrowOp'.toCatHom
  inv := twistedArrowOp'ToOpTwistedArrow.toCatHom
  hom_inv_id := Cat.Hom.ext rfl
  inv_hom_id := Cat.Hom.ext rfl

/--
Functor from `CoTwistedArrow' C` to `(TwistedArrowOp' C)ᵒᵖ'`.

Objects of `CoTwistedArrow' C` are stored as `((cod, dom), arr : cod ⟶ dom)`.
Objects of `TwistedArrowOp' C` are stored as `((dom, cod), arr : cod ⟶ dom)`.
So we swap the pair components.
-/
def coTwistedArrowToTwistedArrowOpOp' :
    CoTwistedArrow' C ⥤ (TwistedArrowOp' C)ᵒᵖ' where
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
Functor from `(TwistedArrowOp' C)ᵒᵖ'` to `CoTwistedArrow' C`.
-/
def twistedArrowOpOp'ToCoTwistedArrow' :
    (TwistedArrowOp' C)ᵒᵖ' ⥤ CoTwistedArrow' C where
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
`CoTwistedArrow' C` is isomorphic to `(TwistedArrowOp' C)ᵒᵖ'`.
-/
def coTwistedArrowIsoTwistedArrowOpOp' :
    CoTwistedArrow' C ≅Cat (TwistedArrowOp' C)ᵒᵖ' where
  hom := coTwistedArrowToTwistedArrowOpOp'.toCatHom
  inv := twistedArrowOpOp'ToCoTwistedArrow'.toCatHom
  hom_inv_id := Cat.Hom.ext rfl
  inv_hom_id := Cat.Hom.ext rfl

/--
`TwistedArrowOp' C` is definitionally equal to `TwistedArrow' (Cᵒᵖ')`.

Both are defined as the category of elements of `homOp'`, but Lean needs explicit
coercion. We provide this as an equality rather than an isomorphism.
-/
theorem twistedArrowOpEqTwistedArrowOfOp' :
    TwistedArrowOp' C = TwistedArrow' (Cᵒᵖ') := rfl

/--
`OpTwistedArrow' (Cᵒᵖ')` is definitionally equal to `CoTwistedArrow' C`.

Both are defined as `ElementsContra'` of `homPreOp'`.
-/
theorem opTwistedArrowOfOpEqCoTwistedArrow' :
    OpTwistedArrow' (Cᵒᵖ') = CoTwistedArrow' C := rfl

section TwistedArrowSelfDuality

/-!
### Self-Duality of Twisted Arrow Categories

The twisted arrow category satisfies a self-duality property:
`TwistedArrow' C ≅ TwistedArrowOp' C` (equivalently, `Tw(C) ≅ Tw(C^op')`).

The isomorphism works by viewing an arrow `f : a → b` in `C` as the same
arrow `f : b → a` in `C^op'`:
- Objects: `(dom, cod, arr : dom → cod)` ↦ `(cod, dom, arr)` where `arr` is
  viewed as going from `cod` to `dom` in the opposite category
- Morphisms: `(α : c → a, β : b → d)` ↦ `(β, α)` (swap components)

The commutativity condition `α ≫ f ≫ β = g` transforms correctly under this
swap.

This self-duality reduces the four twisted arrow variants to two fundamental
categories (up to isomorphism):
- `TwistedArrow' C ≅ TwistedArrowOp' C`
- `OpTwistedArrow' C ≅ CoTwistedArrow' C`
-/

/--
Functor from `TwistedArrow' C` to `TwistedArrowOp' C`.

Objects `(dom, cod, arr : dom → cod)` map to `(cod, dom, arr)` where `arr` is
now viewed as going from `cod` to `dom` (the opposite direction).
Morphisms `(domArr, codArr)` map to `(codArr, domArr)` (swapped components).
-/
def twistedArrowToTwistedArrowOp' : TwistedArrow' C ⥤ TwistedArrowOp' C where
  obj tw := twOpObjMk' (twArr' tw)
  map {x y} f :=
    twOpHomMk'
      (x := twOpObjMk' (twArr' x))
      (y := twOpObjMk' (twArr' y))
      (by simp only [twOpObjMk'_dom, twCod']; exact twCodArr' f)
      (by simp only [twOpObjMk'_cod, twDom']; exact twDomArr' f)
      (twHomComm' f)
  map_id tw := by apply twOpHom'_ext <;> rfl
  map_comp {x y z} f g := by apply twOpHom'_ext <;> rfl

/--
Functor from `TwistedArrowOp' C` to `TwistedArrow' C`.

Objects `(dom, cod, arr : cod → dom)` map to `(cod, dom, arr)` where `arr` is
now viewed as going from `cod` to `dom` (the original direction).
Morphisms `(domArr, codArr)` map to `(codArr, domArr)` (swapped components).
-/
def twistedArrowOp'ToTwistedArrow : TwistedArrowOp' C ⥤ TwistedArrow' C where
  obj tw := twObjMk' (twOpArr' tw)
  map {x y} f :=
    twHomMk'
      (x := twObjMk' (twOpArr' x))
      (y := twObjMk' (twOpArr' y))
      (by simp only [twObjMk'_dom, twOpCod']; exact twOpCodArr' f)
      (by simp only [twObjMk'_cod, twOpDom']; exact twOpDomArr' f)
      (twOpHomComm' f)
  map_id tw := by apply twHom'_ext <;> rfl
  map_comp {x y z} f g := by apply twHom'_ext <;> rfl

/--
Round-trip on objects: `TwistedArrow' → TwistedArrowOp' → TwistedArrow'`
returns the same object.
-/
theorem twistedArrow'RoundTrip_obj (tw : TwistedArrow' C) :
    twistedArrowOp'ToTwistedArrow.obj (twistedArrowToTwistedArrowOp'.obj tw) = tw := by
  simp only [twistedArrowToTwistedArrowOp', twistedArrowOp'ToTwistedArrow,
    twObjMk', twOpObjMk', twArr', twOpArr', twOpCod', twOpDom', twCod', twDom']
  rfl

/--
Round-trip on objects: `TwistedArrowOp' → TwistedArrow' → TwistedArrowOp'`
returns the same object.
-/
theorem twistedArrowOp'RoundTrip_obj (tw : TwistedArrowOp' C) :
    twistedArrowToTwistedArrowOp'.obj (twistedArrowOp'ToTwistedArrow.obj tw) = tw := by
  simp only [twistedArrowToTwistedArrowOp', twistedArrowOp'ToTwistedArrow,
    twObjMk', twOpObjMk', twArr', twOpArr', twOpCod', twOpDom', twCod', twDom']
  rfl

/--
`TwistedArrow' C` is isomorphic to `TwistedArrowOp' C`.

This is the self-duality property: the twisted arrow category of `C` is
isomorphic to the twisted arrow category of `C^op'`.
-/
def twistedArrowIsoTwistedArrowOp' : TwistedArrow' C ≅Cat TwistedArrowOp' C where
  hom := twistedArrowToTwistedArrowOp'.toCatHom
  inv := twistedArrowOp'ToTwistedArrow.toCatHom
  hom_inv_id := Cat.Hom.ext <| by
    fapply Functor.ext
    · exact twistedArrow'RoundTrip_obj
    · intros tw tw' f
      apply twHom'_ext
      · unfold twistedArrowToTwistedArrowOp' twistedArrowOp'ToTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      · unfold twistedArrowToTwistedArrowOp' twistedArrowOp'ToTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
  inv_hom_id := Cat.Hom.ext <| by
    fapply Functor.ext
    · exact twistedArrowOp'RoundTrip_obj
    · intros tw tw' f
      apply twOpHom'_ext
      · unfold twistedArrowToTwistedArrowOp' twistedArrowOp'ToTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      · unfold twistedArrowToTwistedArrowOp' twistedArrowOp'ToTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl

/--
Functor from `OpTwistedArrow' C` to `CoTwistedArrow' C`.

This combines the isomorphisms:
- `OpTwistedArrow' C ≅ (TwistedArrow' C)^op'`
- `TwistedArrow' C ≅ TwistedArrowOp' C`
- `(TwistedArrowOp' C)^op' ≅ CoTwistedArrow' C`

Objects are preserved as the same underlying arrow in `C`.
Morphisms swap components.
-/
def opTwistedArrowToCoTwistedArrow' : OpTwistedArrow' C ⥤ CoTwistedArrow' C where
  obj tw := coTwObjMk' (opTwArr' tw)
  map {x y} f :=
    coTwHomMk'
      (x := coTwObjMk' (opTwArr' x))
      (y := coTwObjMk' (opTwArr' y))
      (by simp only [coTwObjMk'_dom, opTwCod']; exact opTwCodArr' f)
      (by simp only [coTwObjMk'_cod, opTwDom']; exact opTwDomArr' f)
      (opTwHomComm' f)
  map_id tw := by apply coTwHom'_ext <;> rfl
  map_comp {x y z} f g := by apply coTwHom'_ext <;> rfl

/--
Functor from `CoTwistedArrow' C` to `OpTwistedArrow' C`.
-/
def coTwistedArrowToOpTwistedArrow : CoTwistedArrow' C ⥤ OpTwistedArrow' C where
  obj tw := opTwObjMk' (coTwArr' tw)
  map {x y} f :=
    opTwHomMk'
      (x := opTwObjMk' (coTwArr' x))
      (y := opTwObjMk' (coTwArr' y))
      (by simp only [opTwObjMk'_dom, coTwCod']; exact coTwCodArr' f)
      (by simp only [opTwObjMk'_cod, coTwDom']; exact coTwDomArr' f)
      (coTwHomComm' f)
  map_id tw := by apply opTwHom'_ext <;> rfl
  map_comp {x y z} f g := by apply opTwHom'_ext <;> rfl

/--
Round-trip on objects: `OpTwistedArrow' → CoTwistedArrow' → OpTwistedArrow'`
returns the same object.
-/
theorem opTwistedArrowRoundTrip_obj (tw : OpTwistedArrow' C) :
    coTwistedArrowToOpTwistedArrow.obj (opTwistedArrowToCoTwistedArrow'.obj tw) = tw := by
  simp only [opTwistedArrowToCoTwistedArrow', coTwistedArrowToOpTwistedArrow,
    opTwObjMk', coTwObjMk', opTwArr', coTwArr', opTwDom', opTwCod', coTwDom', coTwCod']
  rfl

/--
Round-trip on objects: `CoTwistedArrow' → OpTwistedArrow' → CoTwistedArrow'`
returns the same object.
-/
theorem coTwistedArrowRoundTrip_obj (tw : CoTwistedArrow' C) :
    opTwistedArrowToCoTwistedArrow'.obj (coTwistedArrowToOpTwistedArrow.obj tw) = tw := by
  simp only [opTwistedArrowToCoTwistedArrow', coTwistedArrowToOpTwistedArrow,
    opTwObjMk', coTwObjMk', opTwArr', coTwArr', opTwDom', opTwCod', coTwDom', coTwCod']
  rfl

/--
`OpTwistedArrow' C` is isomorphic to `CoTwistedArrow' C`.

This shows that the opposite of the twisted arrow category is isomorphic to
the co-twisted arrow category (opposite of twisted arrow of opposite).
-/
def opTwistedArrowIsoCoTwistedArrow' : OpTwistedArrow' C ≅Cat CoTwistedArrow' C where
  hom := opTwistedArrowToCoTwistedArrow'.toCatHom
  inv := coTwistedArrowToOpTwistedArrow.toCatHom
  hom_inv_id := Cat.Hom.ext <| by
    fapply Functor.ext
    · exact opTwistedArrowRoundTrip_obj
    · intros tw tw' f
      apply opTwHom'_ext
      · unfold opTwistedArrowToCoTwistedArrow' coTwistedArrowToOpTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      · unfold opTwistedArrowToCoTwistedArrow' coTwistedArrowToOpTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
  inv_hom_id := Cat.Hom.ext <| by
    fapply Functor.ext
    · exact coTwistedArrowRoundTrip_obj
    · intros tw tw' f
      apply coTwHom'_ext
      · unfold opTwistedArrowToCoTwistedArrow' coTwistedArrowToOpTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      · unfold opTwistedArrowToCoTwistedArrow' coTwistedArrowToOpTwistedArrow
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl

end TwistedArrowSelfDuality

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
  simp only [Under.mapFunctor_map] at h
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

/-!
### Alternative Grothendieck Characterizations

There are 16 possible Grothendieck constructions formed by varying:
1. Grothendieck variance: covariant (`Grothendieck`) vs contravariant
   (`GrothendieckContra'`)
2. Map functor: `Under.mapFunctor` vs `Over.mapFunctor`
3. Domain category: `C` vs `Cᵒᵖ'`
4. Fiber oppositization: plain vs post-composed with oppositization functor

These 16 constructions produce 8 distinct categories with 2:1 redundancy.
Four are twisted arrow categories (where domArr and codArr go in opposite
directions) and four are arrow categories (where they go in the same direction).

#### The Eight Target Categories

Categories formed from arrows in C with commutative square morphisms are
classified by three binary choices: object arrow direction, domArr direction,
and codArr direction.

Twisted categories (domArr and codArr go in opposite directions):
- `TwistedArrow' C`: objects dom→cod, domArr backward, codArr forward
- `OpTwistedArrow' C`: objects dom→cod, domArr forward, codArr backward
- `TwistedArrowOp' C`: objects cod→dom, domArr forward, codArr backward
- `CoTwistedArrow' C`: objects cod→dom, domArr backward, codArr forward

Arrow categories (domArr and codArr go in the same direction):
- `Arr(C)`: objects dom→cod, both forward
- `Arr(C)ᵒᵖ`: objects dom→cod, both backward
- `Arr(Cᵒᵖ)`: objects cod→dom, both forward
- `Arr(Cᵒᵖ)ᵒᵖ`: objects cod→dom, both backward

#### Redundancy via Self-Duality

The eight categories above reduce to four fundamental categories (up to
isomorphism) via self-duality isomorphisms.

Twisted arrow self-duality (reduces 4 twisted to 2):
- `TwistedArrow' C ≅ TwistedArrowOp' C` (proven as
  `twistedArrowIsoTwistedArrowOp'`)
- `OpTwistedArrow' C ≅ CoTwistedArrow' C` (proven as
  `opTwistedArrowIsoCoTwistedArrow'`)

Arrow self-duality (reduces 4 arrow to 2):
- `Arrow C ≅ (ArrowOp' C)ᵒᵖ'` (proven as `arrowIsoArrowOpOp'`)

These isomorphisms swap domain and codomain while reinterpreting the arrow
as going in the opposite direction, and swap the morphism components
`(domArr, codArr) ↦ (codArr, domArr)`.

The resulting four fundamental categories are:
- Two twisted variants: `TwistedArrow' C` and `OpTwistedArrow' C`
- Two arrow variants: `Arrow C` and `(Arrow C)ᵒᵖ'`

#### The Sixteen Grothendieck Constructions

Using abbreviations: Gr = covariant Grothendieck, GrC' = GrothendieckContra',
U = Under.mapFunctor, O = Over.mapFunctor, op = fiber oppositization.

Group 1 — Covariant Grothendieck with Under:
- Gr(U(C)): `TwistedArrow' C` (proven as `twArrEquivGrothendieckUnder`)
- Gr(U(C) ⋙ op): `OpTwistedArrow' C`
- Gr(U(Cᵒᵖ')): `Arr(Cᵒᵖ)`
- Gr(U(Cᵒᵖ') ⋙ op): `TwistedArrowOp' C`

Group 2 — Covariant Grothendieck with Over:
- Gr(O(C)): `Arr(C)`
- Gr(O(C) ⋙ op): related to `TwistedArrow'(Cᵒᵖ')ᵒᵖ`
- Gr(O(Cᵒᵖ')): `Arr(C)ᵒᵖ`
- Gr(O(Cᵒᵖ') ⋙ op): `CoTwistedArrow' C`

Group 3 — Contravariant Grothendieck with Under:
- GrC'(U(C)): `Arr(C)`
- GrC'(U(C) ⋙ op): related to `TwistedArrow' C`
- GrC'(U(Cᵒᵖ')): `CoTwistedArrow' C`
- GrC'(U(Cᵒᵖ') ⋙ op): `Arr(C)ᵒᵖ`

Group 4 — Contravariant Grothendieck with Over:
- GrC'(O(C)): `TwistedArrow' C`
- GrC'(O(C) ⋙ op): `OpTwistedArrow' C`
- GrC'(O(Cᵒᵖ')): `TwistedArrowOp' C`
- GrC'(O(Cᵒᵖ') ⋙ op): `Arr(Cᵒᵖ)`

#### Patterns

Under vs Over with covariant Grothendieck:
- `Gr(Under.mapFunctor -)`: Base morphisms go backward (via Cᵒᵖ indexing),
  producing twisted categories
- `Gr(Over.mapFunctor -)`: Base morphisms go forward, producing arrow categories

GrothendieckContra' reverses this pattern:
- `GrC'(Under.mapFunctor -)`: Base morphisms go forward, producing arrow
  categories
- `GrC'(Over.mapFunctor -)`: Base morphisms go backward (via type adaptation),
  producing twisted categories

Fiber oppositization swaps twisted ↔ arrow within each group by reversing
codArr direction.

Applying mapFunctor to Cᵒᵖ' instead of C swaps the object arrow direction.

#### Proven Equivalences

The Under-based equivalence `TwistedArrow' C ≌ Grothendieck (Under.mapFunctor C)`
is proven above as `twArrEquivGrothendieckUnder`. This works because:
- `Under.mapFunctor : Cᵒᵖ ⥤ Cat` indexes by domain (contravariantly)
- The contravariant indexing makes base morphisms go backwards in C
- Combined with forwards fiber morphisms, this gives the twisted pattern

The remaining twisted arrow variants follow from existing isomorphisms:
- `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`
  (proven as `opTwistedArrowIsoTwistedArrowOp'`)
- `TwistedArrowOp' C = TwistedArrow' Cᵒᵖ'`
  (definitional via `twistedArrowOpEqTwistedArrowOfOp'`)
- `CoTwistedArrow' C ≅ (TwistedArrowOp' C)ᵒᵖ'`
  (proven as `coTwistedArrowIsoTwistedArrowOpOp'`)

These combine to give:
- `OpTwistedArrow' C ≌ (Grothendieck (Under.mapFunctor C))ᵒᵖ'`
- `TwistedArrowOp' C ≌ Grothendieck (Under.mapFunctor Cᵒᵖ')`
- `CoTwistedArrow' C ≌ (Grothendieck (Under.mapFunctor Cᵒᵖ'))ᵒᵖ'`
-/

/--
Equivalence between `OpTwistedArrow' C` and the opposite of the Grothendieck
construction of `Under.mapFunctor`.

This combines:
- `opTwistedArrowIsoTwistedArrowOp' : OpTwistedArrow' C ≅Cat (TwistedArrow' C)ᵒᵖ'`
- `Equivalence.op' twArrEquivGrothendieckUnder`
-/
def opTwArrEquivGrothendieckUnderOp' :
    OpTwistedArrow' C ≌ (Grothendieck (Under.mapFunctor C))ᵒᵖ' :=
  (Cat.equivOfIso opTwistedArrowIsoTwistedArrowOp').trans
    (Equivalence.op' twArrEquivGrothendieckUnder)

/-!
### Remaining Twisted Arrow Variants

The equivalences for `TwistedArrowOp' C` and `CoTwistedArrow' C` follow from:

- `TwistedArrowOp' C = TwistedArrow' Cᵒᵖ'` (definitional equality, but different
  category instances in Lean's typeclass system)
- `CoTwistedArrow' C ≅Cat (TwistedArrowOp' C)ᵒᵖ'`

Combined with `twArrEquivGrothendieckUnder`, these give:
- `TwistedArrowOp' C ≌ Grothendieck (Under.mapFunctor Cᵒᵖ')`
- `CoTwistedArrow' C ≌ (Grothendieck (Under.mapFunctor Cᵒᵖ'))ᵒᵖ'`

Direct Lean implementations would require working around typeclass instance
differences between `TwistedArrowOp' C` and `TwistedArrow' Cᵒᵖ'`.
-/

/--
The fiber inclusion functor from `(Over b)^op` to `TwistedArrow' C`.

On objects: `(f : a → b) ↦ f` (viewed as a twisted arrow `a → b`)
On morphisms: `α : f → g` in `(Over b)^op` (i.e., `α : c → a` with `f ∘ α = g`)
  maps to `(α, 𝟙 b) : f → g` in `Tw(C)`
-/
def overOpToTwistedArrow (C : Type u) [Category C] (b : C) :
    (Over b)ᵒᵖ' ⥤ TwistedArrow' C where
  obj ov := twObjMk' ov.hom
  map {ov ov'} α :=
    twHomMk'
      (x := twObjMk' ov.hom)
      (y := twObjMk' ov'.hom)
      (by simp only [twObjMk'_dom]; exact α.left)
      (by simp only [twObjMk'_cod]; exact 𝟙 b)
      (by
        simp only [twObjMk'_arr]
        change id α.left ≫ ov.hom ≫ id (𝟙 b) = ov'.hom
        simp only [id]
        have h : ov.hom ≫ 𝟙 b = ov.hom := Category.comp_id ov.hom
        rw [h]
        exact Over.w α)
  map_id ov := by
    apply twHom'_ext <;> rfl
  map_comp {ov ov' ov''} α β := by
    apply twHom'_ext
    · rfl
    · simp only [twHomMk'_codArr, twCodArr'_comp]
      exact (Category.id_comp (𝟙 b)).symm

/--
The twisted arrow morphism from `twObjMk' ov.hom` to `twObjMk' (ov.hom ≫ β)`,
used to transport fiber elements along a base morphism `β : b ⟶ d`.
-/
def fiberTransportTwMorph (C : Type u) [Category C] {b d : C}
    (β : b ⟶ d) (ov : Over b) :
    twObjMk' ov.hom ⟶ twObjMk' (ov.hom ≫ β) :=
  twHomMk'
    (x := twObjMk' ov.hom)
    (y := twObjMk' (ov.hom ≫ β))
    (by simp only [twObjMk'_dom]; exact 𝟙 ov.left)
    (by simp only [twObjMk'_cod]; exact β)
    (by
      simp only [twObjMk'_arr]
      change id (𝟙 ov.left) ≫ ov.hom ≫ id β = ov.hom ≫ β
      simp only [id, Category.id_comp])

/--
Coherence lemma: the twisted arrow morphism corresponding to `fiberTransport`
composed with the image of a base morphism under `overOpToTwistedArrow d`
equals the image of the base morphism under `overOpToTwistedArrow b`
composed with `fiberTransportTwMorph`.

In the opposite category `(Over b)ᵒᵖ'`, a morphism `α : ov ⟶ ov'` corresponds
to a morphism `ov' ⟶ ov` in `Over b`, so the functors map it in reverse.
-/
theorem fiberTransport_naturality (C : Type u) [Category C] {b d : C}
    (β : b ⟶ d)
    {ov ov' : (Over b)ᵒᵖ'} (α : ov ⟶ ov') :
    (overOpToTwistedArrow C b).map α ≫ fiberTransportTwMorph C β ov' =
    fiberTransportTwMorph C β ov ≫ (overOpToTwistedArrow C d).map ((Over.map β).map α) := by
  apply twHom'_ext
  · simp only [twDomArr'_comp, twHomMk'_domArr, overOpToTwistedArrow,
               fiberTransportTwMorph, twHomMk'_domArr, id, Over.map_map_left]
    trans α.left
    · exact Category.id_comp α.left
    · exact (Category.comp_id α.left).symm
  · simp only [twCodArr'_comp, twHomMk'_codArr, overOpToTwistedArrow,
               fiberTransportTwMorph, twHomMk'_codArr, id]
    trans β
    · exact Category.id_comp β
    · exact (Category.comp_id β).symm

section OverOpToTwistedArrowLax

/-!
### Lax Natural Transformation Structure

The family of functors `overOpToTwistedArrow C b` indexed by `b : C`, together
with the transport morphisms `fiberTransportTwMorph`, forms a lax natural
transformation from `overOpMapFunctor C` to the constant functor at
`TwistedArrow' C`.

The components are:
- Component functors: `overOpToTwistedArrow C b : (Over b)ᵒᵖ' ⥤ TwistedArrow' C`
- Laxity morphisms: `fiberTransportTwMorph C β ov` for `β : b ⟶ d`
- Naturality: `fiberTransport_naturality`
- Identity coherence: `fiberTransportTwMorph_id`
- Composition coherence: `fiberTransportTwMorph_comp`

The `LaxNatTransData` structure in `Grothendieck.lean` has flexible universe
parameters allowing `Cat.{vF, uF}` for arbitrary fiber category universes.
-/

variable (C : Type u) [Category.{v} C]

/--
The constant functor sending every object to `TwistedArrow' C` and every
morphism to the identity functor.
-/
def constTwistedArrowFunctor : C ⥤ Cat.{v, max u v} where
  obj _ := Cat.of (TwistedArrow' C)
  map _ := 𝟙 (Cat.of (TwistedArrow' C))
  map_id _ := rfl
  map_comp _ _ := (Category.comp_id _).symm

/--
Identity coherence for `fiberTransportTwMorph`: when `β = 𝟙 b`, the transport
morphism is the identity (up to the equality `ov.hom = ov.hom ≫ 𝟙 b`).
-/
lemma fiberTransportTwMorph_id (b : C) (ov : Over b) :
    fiberTransportTwMorph C (𝟙 b) ov =
    eqToHom (congrArg (twObjMk' (C := C)) (Category.comp_id ov.hom).symm) := by
  apply twHom'_ext
  · simp only [fiberTransportTwMorph, twHomMk'_domArr, id, twDomArr'_eqToHom,
      twObjMk'_dom]
    rfl
  · simp only [fiberTransportTwMorph, twHomMk'_codArr, id, twCodArr'_eqToHom,
      twObjMk'_cod]
    rfl

/--
Composition coherence for `fiberTransportTwMorph`: the transport along `β ≫ γ`
decomposes into transport along `β` followed by transport along `γ`.

The target functor is constant so `(F.map γ).map` acts as identity.
-/
lemma fiberTransportTwMorph_comp {b d e : C} (β : b ⟶ d) (γ : d ⟶ e)
    (ov : Over b) :
    fiberTransportTwMorph C (β ≫ γ) ov =
    fiberTransportTwMorph C β ov ≫
      fiberTransportTwMorph C γ ((Over.map β).obj ov) ≫
      eqToHom (congrArg (twObjMk' (C := C)) (Category.assoc ov.hom β γ)) := by
  apply twHom'_ext
  · simp only [twDomArr'_comp, fiberTransportTwMorph, twHomMk'_domArr, id,
      twDomArr'_eqToHom, Over.map_obj_left, twObjMk'_dom, eqToHom_refl',
      Functor.id_obj, Category.id_comp]
  · simp only [twCodArr'_comp, fiberTransportTwMorph, twHomMk'_codArr, id,
      twCodArr'_eqToHom, Over.map_obj_hom, twObjMk'_cod, eqToHom_refl',
      Category.comp_id]

/--
The lax natural transformation from `overOpMapFunctor C` to `constTwistedArrowFunctor C`.

This uses the standard `LaxNatTransData` structure from `Grothendieck.lean`,
demonstrating that `overOpToTwistedArrow` forms a proper lax natural transformation.
-/
def overOpToTwistedArrowLax :
    LaxNatTransData (overOpMapFunctor C) (constTwistedArrowFunctor C) where
  app := overOpToTwistedArrow C
  laxApp := fiberTransportTwMorph C
  laxNat := fiberTransport_naturality C
  laxId := fiberTransportTwMorph_id C
  laxComp := fun {b d e} β γ ov => by
    simp only [constTwistedArrowFunctor, Cat.id_eq_id, Functor.id_map, Functor.id_obj]
    conv_rhs =>
      arg 1
      simp only [eqToHom_refl']
    simp only [Category.id_comp]
    change fiberTransportTwMorph C (β ≫ γ) ov =
      fiberTransportTwMorph C β ov ≫
        fiberTransportTwMorph C γ ((Over.map β).obj ov) ≫ eqToHom _
    rw [fiberTransportTwMorph_comp]

end OverOpToTwistedArrowLax

end TwistedArrowAsGrothendieck

/-!
## Arrow Categories

Arrow categories are similar to twisted arrow categories, but morphisms go in
the same direction on both domain and codomain (rather than opposite directions).

For a category C:
- Objects: morphisms `f : a → b` in C
- Morphisms from `(a, b, f)` to `(c, d, g)`: pairs `(α : a → c, β : b → d)` with
  `α ≫ g = f ≫ β` (a commutative square)

We use mathlib's `Arrow C = Comma (𝟭 C) (𝟭 C)` and define:
- `ArrowOp' C`: the arrow category of `Cᵒᵖ'`, i.e., `Arrow Cᵒᵖ'`

A duality result is that `Arrow C ≅ (ArrowOp' C)ᵒᵖ'`, which reduces the four
arrow category variants to two fundamental categories.
-/

section ArrowCategories

/-!
### Arrow Categories using Mathlib's Arrow

This section establishes the self-duality of arrow categories using mathlib's
`Arrow` type. We show that `Arrow C ≅ (Arrow Cᵒᵖ')ᵒᵖ'`.

Mathlib defines `Arrow C = Comma (𝟭 C) (𝟭 C)`, where objects are morphisms in
C and morphisms are commutative squares.
-/

variable (C : Type u) [Category.{v} C]

/--
The arrow category of `Cᵒᵖ'`. This is mathlib's Arrow applied to our
alternative opposite category construction.
-/
abbrev ArrowOp' : Type (max u v) := Arrow Cᵒᵖ'

instance instCategoryArrowOp' : Category (ArrowOp' C) := inferInstance

section ArrowCategorySelfDuality

/-!
### Self-Duality of Arrow Categories

Arrow categories satisfy a duality: `Arrow C ≅ (ArrowOp' C)ᵒᵖ'`.

The isomorphism swaps domain and codomain labels while keeping the same
underlying arrow, and swaps the morphism components.

This reduces the four arrow category variants to two fundamental categories.
Combined with the twisted arrow self-duality, this shows that of the eight
categories formed from arrows with commutative square morphisms, only four
are fundamentally distinct.
-/

variable {C}

/--
Functor from `Arrow C` to `(ArrowOp' C)ᵒᵖ'`.

Objects `f : X ⟶ Y` map to `f` viewed as `Y ⟶ X` in `Cᵒᵖ'`.
Morphisms with components `(left, right)` swap to `(right, left)`.
-/
def arrowToArrowOpOp' : Arrow C ⥤ (ArrowOp' C)ᵒᵖ' where
  obj arr := Arrow.mk arr.hom
  map {x y} f :=
    Arrow.homMk f.right f.left (f.w.symm)
  map_id _ := by
    apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by
    apply Arrow.hom_ext <;> rfl

/--
Functor from `(ArrowOp' C)ᵒᵖ'` to `Arrow C`.

Objects `f : Y ⟶ X` in `Cᵒᵖ'` (i.e., `X ⟶ Y` in C) map to `f` as `X ⟶ Y`.
Morphisms swap components back.
-/
def arrowOpOp'ToArrow : (ArrowOp' C)ᵒᵖ' ⥤ Arrow C where
  obj arr := Arrow.mk arr.hom
  map {x y} f :=
    Arrow.homMk f.right f.left (f.w.symm)
  map_id _ := by
    apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by
    apply Arrow.hom_ext <;> rfl

/--
Round-trip on objects: `Arrow → (ArrowOp')ᵒᵖ' → Arrow` returns the same object.
-/
theorem arrowRoundTrip_obj (arr : Arrow C) :
    arrowOpOp'ToArrow.obj (arrowToArrowOpOp'.obj arr) = arr := by
  simp only [arrowToArrowOpOp', arrowOpOp'ToArrow]
  cases arr
  rfl

/--
Round-trip on objects: `(ArrowOp')ᵒᵖ' → Arrow → (ArrowOp')ᵒᵖ'` returns the
same object.
-/
theorem arrowOpOp'RoundTrip_obj (arr : ArrowOp' C) :
    arrowToArrowOpOp'.obj (arrowOpOp'ToArrow.obj arr) = arr := by
  simp only [arrowToArrowOpOp', arrowOpOp'ToArrow]
  cases arr
  rfl

/--
Category isomorphism between `Arrow C` and `(ArrowOp' C)ᵒᵖ'`.

This establishes that the arrow category is self-dual up to taking the
opposite of the arrow category on the opposite category.
-/
def arrowIsoArrowOpOp' : Arrow C ≅Cat (ArrowOp' C)ᵒᵖ' where
  hom := arrowToArrowOpOp'.toCatHom
  inv := arrowOpOp'ToArrow.toCatHom
  hom_inv_id := Cat.Hom.ext <| by
    fapply Functor.ext
    · exact arrowRoundTrip_obj
    · intros x y f
      apply Arrow.hom_ext <;>
        dsimp [arrowToArrowOpOp', arrowOpOp'ToArrow] <;>
        simp only [Category.id_comp, Category.comp_id]
  inv_hom_id := Cat.Hom.ext <| by
    fapply Functor.ext
    · exact arrowOpOp'RoundTrip_obj
    · intros x y f
      change (arrowOpOp'ToArrow ⋙ arrowToArrowOpOp').map f = _
      rw [Functor.comp_map]
      dsimp only [arrowToArrowOpOp', arrowOpOp'ToArrow]
      simp only [Arrow.homMk_left, Arrow.homMk_right]
      unfold ArrowOp' CategoryOp'
      simp only [CategoryOp'Inst.eq_1, CategoryOp'.eq_1, CategoryOpQuivInst.eq_1,
        Functor.id_obj, Functor.comp_obj, Arrow.mk_right, Arrow.mk_left, Arrow.mk_hom,
        Cat.of_α, Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor,
        Cat.Hom.id_toFunctor, eqToHom_refl, Functor.id_map]
      cases x
      cases y
      unfold Arrow.mk
      apply CommaMorphism.ext
      · simp only [Arrow.homMk_left]
        change f.left = (𝟙 _ ≫ f ≫ 𝟙 _).left
        simp only [Category.id_comp, Category.comp_id]
      · simp only [Arrow.homMk_right]
        change f.right = (𝟙 _ ≫ f ≫ 𝟙 _).right
        simp only [Category.id_comp, Category.comp_id]

end ArrowCategorySelfDuality

end ArrowCategories

end TwistedArrowCategories

section ForgetfulFunctors

/-!
## Forgetful functors from twisted arrow categories

The twisted arrow categories forget to product categories via projection
from the category of elements.
-/

variable (C : Type u) [Category.{v} C]

/--
The forgetful functor from `TwistedArrow C` to `Cᵒᵖ × C`.

This is `CategoryOfElements.π` applied to the hom functor.
-/
abbrev twistedArrowForget : TwistedArrow C ⥤ Cᵒᵖ × C :=
  CategoryOfElements.π (Functor.hom C)

/--
The forgetful functor from `CoTwistedArrow C` to `Cᵒᵖᵒᵖ × Cᵒᵖ`.

This projects from the co-twisted arrow category to the base product category.
The encoding stores `(op (op coTwCod), op coTwDom)` in the pair.
-/
def coTwistedArrowForget : CoTwistedArrow C ⥤ Cᵒᵖᵒᵖ × Cᵒᵖ where
  obj tw := (Opposite.op (Opposite.op (coTwCod tw)), Opposite.op (coTwDom tw))
  map f := ⟨(coTwCodArr f).op.op, (coTwDomArr f).op⟩
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

end ForgetfulFunctors

end GebLean
