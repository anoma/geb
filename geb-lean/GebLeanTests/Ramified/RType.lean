import GebLean
import GebLean.Ramified.RType

/-!
# Tests for the ramified types and object sorts

Executable checks that `GebLean.Ramified.RType.IsObj` decides object
sorts through the derived `DecidablePred` instance, that equality of
r-types is decidable, that `RType.tower` iterates `omega`, and that
`RType.interp` sends object sorts to the carrier and arrows to function
spaces.
-/

namespace GebLeanTests.Ramified.RTypeTest

open GebLean.Ramified

/-- The base type. -/
def o : RType := RType.o

/-- `o → o`. -/
def arrowOO : RType := RType.arrow o o

/-- `Omega o`. -/
def omegaO : RType := RType.omega o

/-- `Omega (o → o)`. -/
def omegaArrowOO : RType := RType.omega arrowOO

-- Object-sort decisions (via the `DecidablePred RType.IsObj` instance).
#guard o.IsObj
#guard omegaO.IsObj
#guard omegaArrowOO.IsObj
#guard ¬ arrowOO.IsObj

-- The tower sorts iterate `omega` on `o`.
example : RType.tower 2 = RType.omega (RType.omega RType.o) := rfl

-- Every object sort denotes a copy of the carrier; `Omega` adds no
-- structure to the denotation, and arrows denote function spaces.
example : RType.interp Nat omegaArrowOO = Nat := rfl
example : RType.interp Nat o = Nat := rfl
example : RType.interp Nat arrowOO = (Nat → Nat) := rfl

-- Equality of r-types is decidable.
#guard omegaO ≠ arrowOO
#guard RType.arrow o omegaO = RType.arrow o omegaO

end GebLeanTests.Ramified.RTypeTest
