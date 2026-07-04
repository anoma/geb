import GebLean.Binding.Laws
import GebLeanTests.Binding.Term

/-!
# Tests for the substitution-lemma suite

Reduction-equation checks for the substitution monoid law
`GebLean.Binding.sub_var`: substituting a variable reads the environment (left
unit). The single-sorted one-operation signature `sigK` is reused from the term
tests.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- the left-unit law on a concrete variable
example (σ : Env (Tm sigK) [()] [()]) (x : Var [()] ()) :
    sub σ (Tm.var x) = σ () x := sub_var σ x

end GebLean.Binding.Test
