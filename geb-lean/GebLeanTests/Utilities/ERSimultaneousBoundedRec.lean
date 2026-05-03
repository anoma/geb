import GebLean.Utilities.ERSimultaneousBoundedRec

/-!
# Tests for `ERMor1.simultaneousBoundedRec`,
# `ERMor1.PolyBound.ofSimultaneousBoundedRec`.

Per the test discipline from
`GebLeanTests/Utilities/ERTupling.lean` (Gödel-numbering
kernel-reduction is impractical), this file restricts
runtime checks to PolyBound shape verification (struct
field access only).  Higher-arity correctness rests on
`simultaneousBoundedRec_interp_correct`.
-/

open GebLean

-- PolyBound shape at small k with trivial componentBound
-- (`ERMor1.PolyBound.ofZeroN 1` at arity (a + 1) = 1 for
-- a = 0).  Struct field access only — no .interp
-- evaluation.
example :
    (ERMor1.PolyBound.ofSimultaneousBoundedRec
       (h := fun _ => ERMor1.zeroN 0)
       (g := fun _ => ERMor1.zeroN 3)
       1 0
       (ERMor1.PolyBound.ofZeroN 1)
       ⟨0, by decide⟩).degree = 0 := rfl
