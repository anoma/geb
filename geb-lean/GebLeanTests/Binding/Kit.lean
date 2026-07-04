import GebLean.Binding.Kit

/-!
# Tests for the generic binder-aware traversal

Reduction-equation checks for `GebLean.Binding.traverse` against the renaming
kit `varKit`.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- `traverse` of the identity environment over a variable reduces by
-- `traverse_var` to that variable, wrapped by the kit's `toTm`.
example (S : BinderSig Unit) (x : Var [()] ()) :
    traverse (varKit S) (fun _ y => y) (Tm.var x)
      = (varKit S).toTm x := by simp [traverse_var]

end GebLean.Binding.Test
