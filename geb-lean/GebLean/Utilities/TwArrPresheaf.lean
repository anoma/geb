import GebLean.Utilities.Elements
import GebLean.Utilities.Slice
import GebLean.Utilities.TwistedArrow

/-!
# Functor categories on twisted arrow categories

This module defines functor categories from the four twisted arrow category
variants to `Type v`:

- `TwArrCopresheaf C` = `TwistedArrow' C ⥤ Type v` (copresheaves on Tw)
- `TwArrPresheaf C` = `OpTwistedArrow' C ⥤ Type v` (presheaves on Tw)
- `TwArrOpCopresheaf C` = `TwistedArrowOp' C ⥤ Type v` (copresheaves on TwOp)
- `TwArrOpPresheaf C` = `CoTwistedArrow C ⥤ Type v` (presheaves on TwOp)

Since `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`, functors from `OpTwistedArrow'`
are presheaves on `TwistedArrow'`. Similarly, since
`CoTwistedArrow C ≅ (TwistedArrowOp' C)ᵒᵖ'`, functors from `CoTwistedArrow`
are presheaves on `TwistedArrowOp'`.

Two of these have direct slice equivalences via `sliceEquivCopresheaf`:
- `Over hom' ≌ TwArrCopresheaf C`
- `Over homOp' ≌ TwArrOpCopresheaf C`
-/

universe v u

namespace GebLean

open CategoryTheory

variable (C : Type u) [Category.{v} C]

section TwArrCopresheaf

/--
Copresheaves on the twisted arrow category: covariant functors from
`TwistedArrow' C` to `Type v`.
-/
def TwArrCopresheaf := TwistedArrow' C ⥤ Type v

instance : Category (TwArrCopresheaf C) := by
  unfold TwArrCopresheaf
  infer_instance

/--
The slice category over `hom'` is equivalent to the category of copresheaves
on the twisted arrow category.
-/
def sliceEquivTwArrCopresheaf : Over (hom' (C := C)) ≌ TwArrCopresheaf C :=
  sliceEquivCopresheaf (hom' (C := C))

/--
Curried object map for `TwArrCopresheaf`.

Given `F : TwArrCopresheaf C`, the object map takes a twisted arrow `(x, y, f)`
to a type. In curried form: `y` first (covariant), then `x` (contravariant),
then `f : x ⟶ y`. This lets us view `f` as a slice over `y`.

- `y : C` (covariant in the functor category)
- `x : C` (contravariant in the functor category)
- `f : x ⟶ y`
- Returns: `F.obj (twObjMk' f) : Type v`
-/
def TwArrCopresheaf.curriedObj (F : TwArrCopresheaf C) (y : C) (x : C)
    (f : x ⟶ y) : Type v :=
  F.obj (twObjMk' f)

/--
Given a morphism in `Over y` from `(f : x ⟶ y)` to `(f' : x' ⟶ y)`, i.e.,
`g : x ⟶ x'` with `g ≫ f' = f`, we get a twisted-arrow morphism from
`twObjMk' f'` to `twObjMk' f` (note the reversal) with `domArr = g` and
`codArr = 𝟙 y`.

This induces a map `F.obj (twObjMk' f') → F.obj (twObjMk' f)` via `F.map`.
-/
def TwArrCopresheaf.sliceMap (F : TwArrCopresheaf C) {y : C} {x x' : C}
    {f : x ⟶ y} {f' : x' ⟶ y} (g : x ⟶ x') (comm : g ≫ f' = f) :
    F.obj (twObjMk' f') → F.obj (twObjMk' f) :=
  F.map (twHomMk' g (𝟙 y) (by
    simp only [twObjMk'_arr]
    rw [show f' ≫ 𝟙 y = f' from Category.comp_id f', comm]))

end TwArrCopresheaf

section TwArrPresheaf

/--
Presheaves on the twisted arrow category: covariant functors from
`OpTwistedArrow' C` to `Type v`.

Since `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrow' C`, i.e., presheaves.
-/
def TwArrPresheaf := OpTwistedArrow' C ⥤ Type v

instance : Category (TwArrPresheaf C) := by
  unfold TwArrPresheaf
  infer_instance

/--
Curried object map for `TwArrPresheaf`.

Given `F : TwArrPresheaf C`, the object map takes an opposite-twisted arrow
`(x, y, f)` to a type. In curried form: `y` first (covariant), then `x`
(contravariant), then `f : x ⟶ y`. This lets us view `f` as a slice over `y`.

- `y : C` (contravariant in the functor category)
- `x : C` (covariant in the functor category)
- `f : x ⟶ y`
- Returns: `F.obj (opTwObjMk' f) : Type v`
-/
def TwArrPresheaf.curriedObj (F : TwArrPresheaf C) (y : C) (x : C)
    (f : x ⟶ y) : Type v :=
  F.obj (opTwObjMk' f)

/--
Given a morphism in `Over y` from `(f : x ⟶ y)` to `(f' : x' ⟶ y)`, i.e.,
`g : x ⟶ x'` with `g ≫ f' = f`, we get an opposite-twisted-arrow morphism from
`opTwObjMk' f` to `opTwObjMk' f'` with `domArr = g` and `codArr = 𝟙 y`.

This induces a map `F.obj (opTwObjMk' f) → F.obj (opTwObjMk' f')` via `F.map`.
-/
def TwArrPresheaf.sliceMap (F : TwArrPresheaf C) {y : C} {x x' : C}
    {f : x ⟶ y} {f' : x' ⟶ y} (g : x ⟶ x') (comm : g ≫ f' = f) :
    F.obj (opTwObjMk' f) → F.obj (opTwObjMk' f') :=
  F.map (opTwHomMk' g (𝟙 y) (by
    simp only [opTwObjMk'_arr]
    rw [show f' ≫ 𝟙 y = f' from Category.comp_id f', comm]))

end TwArrPresheaf

section TwArrOpCopresheaf

/--
Copresheaves on the opposite-variant twisted arrow category: covariant functors
from `TwistedArrowOp' C` to `Type v`.
-/
def TwArrOpCopresheaf := TwistedArrowOp' C ⥤ Type v

instance : Category (TwArrOpCopresheaf C) := by
  unfold TwArrOpCopresheaf
  infer_instance

/--
The slice category over `homOp'` is equivalent to the category of copresheaves
on the opposite-variant twisted arrow category.
-/
def sliceEquivTwArrOpCopresheaf : Over (homOp' (C := C)) ≌ TwArrOpCopresheaf C :=
  sliceEquivCopresheaf (homOp' (C := C))

/--
Curried object map for `TwArrOpCopresheaf`.

Given `F : TwArrOpCopresheaf C`, the object map takes a twisted arrow of `Cᵒᵖ'`,
i.e., `(x, y, f : y ⟶ x)`, to a type. In curried form: `x` first (covariant),
then `y` (contravariant), then `f : y ⟶ x`. This lets us view `f` as a slice
over `x`.

- `x : C` (covariant in the functor category)
- `y : C` (contravariant in the functor category)
- `f : y ⟶ x`
- Returns: `F.obj (twOpObjMk' f) : Type v`
-/
def TwArrOpCopresheaf.curriedObj (F : TwArrOpCopresheaf C) (x : C) (y : C)
    (f : y ⟶ x) : Type v :=
  F.obj (twOpObjMk' f)

/--
Given a morphism in `Over x` from `(f : y ⟶ x)` to `(f' : y' ⟶ x)`, i.e.,
`g : y ⟶ y'` with `g ≫ f' = f`, we get a twisted-arrow-op morphism from
`twOpObjMk' f'` to `twOpObjMk' f` (note the reversal) with `domArr = 𝟙 x`
and `codArr = g`.

This induces a map `F.obj (twOpObjMk' f') → F.obj (twOpObjMk' f)` via `F.map`.
-/
def TwArrOpCopresheaf.sliceMap (F : TwArrOpCopresheaf C) {x : C} {y y' : C}
    {f : y ⟶ x} {f' : y' ⟶ x} (g : y ⟶ y') (comm : g ≫ f' = f) :
    F.obj (twOpObjMk' f') → F.obj (twOpObjMk' f) :=
  F.map (twOpHomMk' (𝟙 x) g (by
    simp only [twOpObjMk'_arr]
    rw [show f' ≫ 𝟙 x = f' from Category.comp_id f', comm]))

end TwArrOpCopresheaf

section TwArrOpPresheaf

/--
Presheaves on the opposite-variant twisted arrow category: covariant functors
from `CoTwistedArrow C` to `Type v`.

Since `CoTwistedArrow C ≅ (TwistedArrowOp' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrowOp' C`, i.e., presheaves.
-/
def TwArrOpPresheaf := CoTwistedArrow C ⥤ Type v

instance : Category (TwArrOpPresheaf C) := by
  unfold TwArrOpPresheaf
  infer_instance

/--
Curried object map for `TwArrOpPresheaf`.

Given `F : TwArrOpPresheaf C`, the object map takes a co-twisted arrow, i.e.,
`(x, y, f : y ⟶ x)`, to a type. In curried form: `x` first (contravariant),
then `y` (covariant), then `f : y ⟶ x`. This lets us view `f` as a slice
over `x`.

- `x : C` (contravariant in the functor category)
- `y : C` (covariant in the functor category)
- `f : y ⟶ x`
- Returns: `F.obj (coTwObjMk' f) : Type v`
-/
def TwArrOpPresheaf.curriedObj (F : TwArrOpPresheaf C) (x : C) (y : C)
    (f : y ⟶ x) : Type v :=
  F.obj (coTwObjMk' f)

/--
Given a morphism in `Over x` from `(f : y ⟶ x)` to `(f' : y' ⟶ x)`, i.e.,
`g : y ⟶ y'` with `g ≫ f' = f`, we get a co-twisted-arrow morphism from
`coTwObjMk' f` to `coTwObjMk' f'` with `domArr = 𝟙 x` and `codArr = g`.

This induces a map `F.obj (coTwObjMk' f) → F.obj (coTwObjMk' f')` via `F.map`.
-/
def TwArrOpPresheaf.sliceMap (F : TwArrOpPresheaf C) {x : C} {y y' : C}
    {f : y ⟶ x} {f' : y' ⟶ x} (g : y ⟶ y') (comm : g ≫ f' = f) :
    F.obj (coTwObjMk' f) → F.obj (coTwObjMk' f') :=
  F.map (coTwHomMk' (𝟙 x) g (by
    simp only [coTwObjMk'_arr]
    rw [show f' ≫ 𝟙 x = f' from Category.comp_id f', comm]))

end TwArrOpPresheaf

end GebLean
