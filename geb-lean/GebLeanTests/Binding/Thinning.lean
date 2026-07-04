import GebLean.Binding.Thinning

/-!
# Tests for context thinnings

Compilation tests for `GebLean.Binding.Thinning`: weakening shifts a
variable's position past a new head, and the identity thinning acts as the
identity on variables.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- weakening shifts the sole variable of `[()]` past a new head
example : (Thinning.weak.app (⟨0, rfl⟩ : Var [()] ())).1
    = (⟨1, rfl⟩ : Var [(), ()] ()).1 := by decide

-- `app` of the identity thinning is the identity
example (x : Var [()] ()) : Thinning.id.app x = x := Thinning.app_id x

end GebLean.Binding.Test
