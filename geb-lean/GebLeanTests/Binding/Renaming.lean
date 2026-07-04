import GebLean.Binding.Renaming
import GebLeanTests.Binding.Term

/-!
# Tests for renaming

Reduction-equation checks for `GebLean.Binding.ren`, the renaming instance of
the generic traversal, and its functor laws `ren_id` / `ren_comp`. The
single-sorted one-operation signature `sigK` is reused from the term tests.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- renaming by the identity thinning is the identity, on a variable
example (x : Var [()] ()) :
    ren (S := sigK) Thinning.id (Tm.var x) = Tm.var x := ren_id _

-- weakening a variable term shifts its index (via ren/renEnv/traverse_var)
example (x : Var [()] ()) :
    ren (S := sigK) (Thinning.weak (s := ())) (Tm.var x)
      = Tm.var ((Thinning.weak (s := ())).app x) := by
  simp [ren, renEnv, traverse_var, varKit]

end GebLean.Binding.Test
