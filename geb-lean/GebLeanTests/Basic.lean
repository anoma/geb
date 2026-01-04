import GebLean
import Mathlib.CategoryTheory.Category.Cat

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

end InstanceIllustrations
