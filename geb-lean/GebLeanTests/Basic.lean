import GebLean
import Mathlib.CategoryTheory.Category.Cat
import Counterexamples.Girard

/-!
# Basic Tests

This file contains basic sanity tests for the GebLean library using Lean's
built-in `#guard` command.

The `#guard` command checks that an expression evaluates to `true` at
compile time. If it fails, the build will fail.
-/

-- Test that we can import the library
#guard true

namespace InstanceIllustrations

open CategoryTheory

private def ofSmall.{u} (C : Type u) {CI : SmallCategory.{u} C} :
  Cat.{u, u} :=
    Cat.of C

private instance toSmall.{u} (C : Cat.{u, u}) :
  SmallCategory C.α :=
    C.str

private def ofLarge.{u} (C : Type (u + 1)) {CI : LargeCategory.{u} C} :
  Cat.{u, u + 1} :=
    Cat.of C

private instance toLarge.{u} (C : Cat.{u, u + 1}) :
  LargeCategory C.α :=
    C.str

private def propCat : Cat.{0, 0} := Cat.of Prop

private def typeCat.{u} : Cat.{u, u + 1} := Cat.of (Type u)

private def overTypeCat.{u} (X : Type u) : Cat.{u, u + 1} := Cat.of (Over X)

private def psubtypeExample.{u} (α : Sort u) : (α → Prop) → Sort (max 1 u) :=
  Subtype.{u} (α := α)

end InstanceIllustrations

namespace UniverseIllustrations

open CategoryTheory

abbrev ovr.{u, v} (C : Type u) [Category.{v, u} C] (X : C) :
  Type (max u v) :=
    Over X

instance ovrc.{u, v} (C : Type u) [Category.{v, u} C] (X : C) :
  Category.{v, max u v} (ovr.{u, v} C X) :=
    inferInstance

abbrev fctr.{u, v, u', v'} (C : Type u) (D : Type u')
    [Category.{v, u} C] [Category.{v', u'} D] :
  Type (max u v u' v') :=
    C ⥤ D

instance fctrc.{u, v, u', v'} (C : Type u) (D : Type u')
    [Category.{v, u} C] [Category.{v', u'} D] :
  Category.{max u v', max u u' v v'} (fctr.{u, v, u', v'} C D) :=
    inferInstance

abbrev copr.{u, v, w} (C : Type u) [Category.{v, u} C] :
  Type (max u v (w + 1)) :=
    C ⥤ Type w

lemma copr_is_f.{u, v, w} (C : Type u) [Category.{v, u} C] :
  copr.{u, v, w} C = fctr.{u, v, w + 1, w} C (Type w) :=
    rfl

instance coprc.{u, v, w} (C : Type u) [Category.{v, u} C] :
  Category.{max u w, max u v (w + 1)} (copr.{u, v, w} C) :=
    inferInstance

instance coprc_is_f.{u, v, w} (C : Type u) [Category.{v, u} C] :
  coprc.{u, v, w} C = fctrc.{u, v, w + 1, w} C (Type w) :=
    rfl

instance overf.{u, v, w} (C : Type u) [Category.{v, u} C] (F : C ⥤ Type w) :
  Category.{max u w, max u v (w + 1)} (Over (T := C ⥤ Type w) F) :=
    inferInstance

instance elc.{u, v, w} (C : Type u) [Category.{v, u} C] (F : C ⥤ Type w) :
  Category.{v, max u w} F.Elements :=
    inferInstance

instance coprel.{u, v, w, w'} (C : Type u) [Category.{v, u} C] (F : C ⥤ Type w) :
  Category.{max u w w', max u v w (w' + 1)} (F.Elements ⥤ Type w') :=
    inferInstance

abbrev Pi.{u, v} : (Type u → Type v) → Type (max (u + 1) v) :=
  fun A ↦ ∀ (α : Type u), A α

abbrev Sigma.{u, v} : (Type u → Type v) → Type (max (u + 1) v) :=
  fun A ↦ Σ (α : Type u), A α

abbrev girard.{u} :=
  Counterexample.girard.{u}

end UniverseIllustrations
