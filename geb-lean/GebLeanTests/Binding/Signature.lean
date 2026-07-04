import GebLean.Binding.Signature

/-!
# Tests for binding signatures

Compilation tests for `GebLean.Binding.Var`: the anti-collapse property that
two positions of the same sort in a context are distinct data, and that a
variable's sort is read off its position.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- two positions of the same sort in a context are distinct data
-- (the anti-collapse property: Var is Type-valued, not Prop)
example : (⟨0, rfl⟩ : Var [true, true] true).1
    ≠ (⟨1, rfl⟩ : Var [true, true] true).1 := by decide

-- a variable's sort is read off its position
example : ((⟨1, rfl⟩ : Var [false, true] true)).1 = 1 := by decide

end GebLean.Binding.Test
