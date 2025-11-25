import GebLean.Utilities.TwistedArrow

/-!
# Presheaf and copresheaf categories on twisted arrow categories

This module defines functor categories from the four twisted arrow category
variants to `Type`:

- `TwArrCopresheaf C` = `TwistedArrow' C ⥤ Type` (covariant functors)
- `TwArrPresheaf C` = `OpTwistedArrow' C ⥤ Type` (contravariant functors)
- `TwArrOpCopresheaf C` = `TwistedArrowOp' C ⥤ Type` (covariant functors)
- `TwArrOpPresheaf C` = `CoTwistedArrow C ⥤ Type` (contravariant functors)
-/

universe v u

namespace GebLean

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
Copresheaves on the twisted arrow category: covariant functors from
`TwistedArrow' C` to `Type`.
-/
def TwArrCopresheaf := TwistedArrow' C ⥤ Type (max u v)

instance : Category (TwArrCopresheaf C) := by
  unfold TwArrCopresheaf
  infer_instance

/--
Presheaves on the twisted arrow category: contravariant functors from
`TwistedArrow' C` to `Type`, i.e., covariant functors from `OpTwistedArrow' C`.
-/
def TwArrPresheaf := OpTwistedArrow' C ⥤ Type (max u v)

instance : Category (TwArrPresheaf C) := by
  unfold TwArrPresheaf
  infer_instance

/--
Copresheaves on the opposite twisted arrow category: covariant functors from
`TwistedArrowOp' C` to `Type`.
-/
def TwArrOpCopresheaf := TwistedArrowOp' C ⥤ Type (max u v)

instance : Category (TwArrOpCopresheaf C) := by
  unfold TwArrOpCopresheaf
  infer_instance

/--
Presheaves on the opposite twisted arrow category: contravariant functors from
`TwistedArrowOp' C` to `Type`, i.e., covariant functors from `CoTwistedArrow C`.
-/
def TwArrOpPresheaf := CoTwistedArrow C ⥤ Type (max u v)

instance : Category (TwArrOpPresheaf C) := by
  unfold TwArrOpPresheaf
  infer_instance

end GebLean
