import GebLean.Binding.Laws
import GebLeanTests.Binding.Term

/-!
# Tests for the substitution-lemma suite

Reduction-equation checks for the substitution monoid laws
`GebLean.Binding.sub_var` and `GebLean.Binding.sub_id`: substituting a variable
reads the environment (left unit), and substituting by the identity environment
is the identity (right unit). The single-sorted one-operation signature `sigK`
is reused from the term tests.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- the left-unit law on a concrete variable
example (σ : Env (Tm sigK) [()] [()]) (x : Var [()] ()) :
    sub σ (Tm.var x) = σ () x := sub_var σ x

-- the right-unit law
example (t : Tm sigK [()] ()) : sub idEnv t = t := sub_id t

end GebLean.Binding.Test
