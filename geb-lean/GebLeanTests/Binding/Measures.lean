import GebLean.Binding.Measures
import GebLean.Binding.Examples.Stlc

/-!
# Tests for the term measures

Worked `example`s over `GebLean.Binding.stlcBody`, `GebLean.Binding.stlcId`,
and a two-argument application node, exercising `Tm.size` and `Tm.height` on a
variable, an abstraction, and an application. The application distinguishes the
two measures: its size (node count) exceeds its height (`1 + max` over
children).
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- An application node `f x` in the context `[a ⇒ a, a]`, with the function and
-- argument read off from the two variables of the context. The two arguments
-- are non-binding, so the extended contexts coincide with the ambient one; the
-- sort ascriptions supply the ambient context concretely, before the argument
-- list's positional lookup is reduced.
def stlcApp (a : StlcTy) : Tm stlcSig [StlcTy.arrow a a, a] a :=
  Tm.op (S := stlcSig) (o := StlcOp.app a a) (fun j => by
    cases j using Fin.cases with
    | zero => exact (Tm.var ⟨0, rfl⟩ : Tm stlcSig [StlcTy.arrow a a, a] (StlcTy.arrow a a))
    | succ i =>
      cases i using Fin.cases with
      | zero => exact (Tm.var ⟨1, rfl⟩ : Tm stlcSig [StlcTy.arrow a a, a] a)
      | succ k => exact k.elim0)

-- `size`/`height` of a variable: both `1`.
example : (stlcBody StlcTy.base).size = 1 := by simp [stlcBody]

example : (stlcBody StlcTy.base).height = 1 := by simp [stlcBody]

-- `size`/`height` of the identity abstraction `λx. x`: both `2` (the `lam`
-- node over the single bound variable). The argument tuple is read off by
-- `Fin.cases` on a numeral literal, which resolves only by definitional
-- reduction, not by a structural `simp` lemma; hence `rfl` (as in the
-- `instantiate₁` acceptance test).
example : (stlcId StlcTy.base).size = 2 := by rfl

example : (stlcId StlcTy.base).height = 2 := by rfl

-- `size`/`height` of the application `f x`: size `3` (the `app` node and its
-- two variable arguments), height `2` (`1 + max 1 1`); size and height diverge
-- at a branching node.
example : (stlcApp StlcTy.base).size = 3 := by rfl

example : (stlcApp StlcTy.base).height = 2 := by rfl

end GebLean.Binding.Test
