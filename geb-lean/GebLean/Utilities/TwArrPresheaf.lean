import GebLean.Utilities.Elements
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
Presheaves on the opposite-variant twisted arrow category: covariant functors
from `CoTwistedArrow C` to `Type v`.

Since `CoTwistedArrow C ≅ (TwistedArrowOp' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrowOp' C`, i.e., presheaves.
-/
def TwArrOpPresheaf := CoTwistedArrow C ⥤ Type v

instance : Category (TwArrOpPresheaf C) := by
  unfold TwArrOpPresheaf
  infer_instance

end GebLean
