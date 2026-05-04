import GebLean.Utilities.ERPackedBound

/-!
# Tests for `ERMor1.tuplePackedBound`,
# `ERMor1.PolyBound.ofTuplePackedBound`.

ER-side packed-state value bound for the ER ↔ K^sim_2
categorical equivalence.  See
`GebLean.Utilities.ERPackedBound` and master design §3.2.

Per the test discipline from
`GebLeanTests/Utilities/ERTupling.lean` (Gödel-numbering
kernel-reduction is impractical), this file restricts
runtime checks to PolyBound shape verification (struct
field access only).
-/

open GebLean

-- PolyBound shape at k = 0 with a trivial componentBound
-- (`ERMor1.PolyBound.ofZeroN 0`: degree = 0,
-- coefficient = 0, constant = 0).
-- Result: degree = 0 * 2^0 = 0.
example :
    (ERMor1.PolyBound.ofTuplePackedBound 0
       (ERMor1.PolyBound.ofZeroN 0)).degree = 0 := rfl

-- PolyBound shape at k = 1.  Result: degree = 0 * 2^1 = 0.
example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).degree = 0 := rfl

-- coefficient = tuplePackCoef 1 * (0 + 0 + 1)^(2^1)
--             = tuplePackCoef 1 * 1
example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).coefficient
      = Nat.tuplePackCoef 1 * 1 ^ (2 ^ 1) := rfl

example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).constant = 0 := rfl
