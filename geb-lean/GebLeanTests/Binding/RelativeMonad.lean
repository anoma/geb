import GebLean.Binding.RelativeMonad
import GebLeanTests.Binding.Term

/-!
# Tests for the substitution relative monad

A compilation and reduction check for `GebLean.Binding.Tm.relativeMonad`: its
Kleisli extension at the identity environment is the identity, matching
`GebLean.Binding.sub_id`. The single-sorted one-operation signature `sigK` is
reused from the term tests.
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- the relative monad exists and its `ext` is `sub` on a concrete term
example (t : Tm sigK [()] ()) :
    (Tm.relativeMonad sigK).ext (fun _ x => Tm.var x) () t = t := by
  simpa using sub_id t

end GebLean.Binding.Test
