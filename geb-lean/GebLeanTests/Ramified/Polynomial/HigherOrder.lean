import GebLean
import GebLean.Ramified.Polynomial.HigherOrder
import GebLeanTests.Ramified.Polynomial.Ident

/-!
# Tests for the primed higher-order presentation and schema identifiers

Executable checks over the `1 + X` word algebra `natAlgSig`
(`GebLeanTests.Ramified.Polynomial.IdentTest.A`). `appChain_curryInterp'` is
checked at a two-sort context, reading off the first argument through the
currying-then-application round trip. `identHom_eval'` is checked at the
constant-zero identifier `idZero'`
(`GebLeanTests/Ramified/Polynomial/Ident.lean`), the explicit definition of
context `[]` and result `RType'.o`.
-/

namespace GebLeanTests.Ramified.Polynomial.HigherOrderTest

open GebLean.Ramified GebLean.Ramified.Polynomial
open GebLeanTests.Ramified.Polynomial.IdentTest (A idZero')

-- `appChain_curryInterp'` at a two-sort context `[o, o]`: currying the
-- first-projection function and applying it back along the environment via
-- `appChain'` recovers the first-projection value.
example (ρ : ∀ i : Fin ([RType'.o, RType'.o] : List RType').length,
      RType'.interp (FreeAlg' A) (([RType'.o, RType'.o] : List RType').get i)) :
    appChain' A [RType'.o, RType'.o] RType'.o
        (curryInterp' A [RType'.o, RType'.o] RType'.o (fun ρ' => ρ' 0)) ρ
      = ρ 0 :=
  appChain_curryInterp' A [RType'.o, RType'.o] RType'.o (fun ρ' => ρ' 0) ρ

-- `identHom_eval'` at the constant-zero identifier `idZero'`: the
-- standard-model evaluation of `identHom' idZero'` reads off `idZero'.interp`.
example (ρ : (standardModel (higherOrder' A)).Env ([] : List RType')) :
    (identHom' idZero').eval ρ 0 = idZero'.interp ρ :=
  identHom_eval' idZero' ρ

end GebLeanTests.Ramified.Polynomial.HigherOrderTest
