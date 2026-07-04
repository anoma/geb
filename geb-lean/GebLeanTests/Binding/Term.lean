import GebLean.Binding.Term

/-!
# Tests for the binder-substitution term type

Compilation tests for `GebLean.Binding.Tm`: a constant (an operation with no
arguments) is a closed term, and a variable is a term.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- a one-operation signature: a constant `k` of sort `()` (no args)
def sigK : BinderSig Unit where
  Op := Unit
  result := fun _ => ()
  args := fun _ => []

-- the constant is a closed term; a variable is a term
example : Tm sigK [] () := Tm.op () (fun j => j.elim0)
example : Tm sigK [()] () := Tm.var ⟨0, rfl⟩

end GebLean.Binding.Test
