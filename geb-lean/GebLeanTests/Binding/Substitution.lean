import GebLean.Binding.Substitution
import GebLeanTests.Binding.Term

/-!
# Tests for substitution

Reduction-equation checks for `GebLean.Binding.sub` and the environment
helpers: substituting a variable by the identity environment is the identity,
and `instantiate₁` replaces the sole bound variable of the append-at-end
singleton by the substituted term. The single-sorted one-operation signature
`sigK` is reused from the term tests.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- substituting by the identity environment is the identity, on a variable
example (x : Var [()] ()) :
    sub (S := sigK) idEnv (Tm.var x) = Tm.var x := by
  simp [sub, idEnv, subKit, traverse_var]

-- instantiate₁ replaces the single bound variable of [()] ++ [()]
example (u : Tm sigK [()] ()) :
    instantiate₁ (Γ := [()]) (a := ()) u (Tm.var (⟨1, rfl⟩ : Var [(), ()] ())) = u := by
  simp only [instantiate₁, instantiate, sub, extendEnv, idEnv, subKit, splitVar,
    traverse_var]
  -- the sole bound variable is a `Fin` numeral literal that `splitVar` resolves
  -- only by definitional reduction, not by a structural `simp` lemma
  rfl

end GebLean.Binding.Test
