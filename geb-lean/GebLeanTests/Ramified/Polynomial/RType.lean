import GebLean.Ramified.Polynomial.RType

/-!
# Tests for `RType'` on the vendored slice stack

Executable checks that the bridge equivalence `rTypeSliceEquiv` carries a
native constructor tree to its legacy counterpart, and that the native
order measure `RType'.ord` agrees with the legacy `RType.ord` across the
bridge. Each check goes through a proven compatibility lemma rather than
kernel reduction of the underlying slice `W`-tree.
-/

namespace GebLeanTests.Ramified.Polynomial.RType

open GebLean.Ramified GebLean.Ramified.Polynomial

example :
    rTypeSliceEquiv (RType'.arrow RType'.o RType'.o) = RType.arrow RType.o RType.o := by
  simp [rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]

example :
    RType'.ord (RType'.arrow RType'.o RType'.o)
      = RType.ord (RType.arrow RType.o RType.o) := by
  simp [rTypeSliceEquiv_ord, rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]

end GebLeanTests.Ramified.Polynomial.RType
