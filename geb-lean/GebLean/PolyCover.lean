import GebLean.Polynomial
import GebLean.Utilities.Presheaf
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Regular Projective Cover by Coproducts of Representables

For `C : Type u` with `Category.{v} C` and an auxiliary
universe `w`, the presheaf category `Cᵒᵖ ⥤ Type (max w v)`
and the copresheaf category `C ⥤ Type (max w v)` each have
enough projectives: coproducts of (universe-lifted)
representables are projective, and every (co)presheaf
admits an epimorphism from such a coproduct.

For presheaves, the projective objects are coproducts of
contravariant representables `yoneda.obj c`, corresponding
to objects of `FreeCoprodCompletionCat C`.  For
copresheaves, the projective objects are coproducts of
covariant representables `coyoneda.obj (op c)`,
corresponding to objects of `CoprodCovarRepCat C`.

The density theorem (`colimitOfRepresentable`) exhibits
every presheaf `P : Cᵒᵖ ⥤ Type (max w v)` as a colimit
of representables via its category of elements.  The
copresheaf case follows by applying the density theorem
to `Cᵒᵖ` in place of `C`.
-/

namespace GebLean

open CategoryTheory

universe w v u

end GebLean
