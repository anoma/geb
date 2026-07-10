import GebLean.Utilities.ERCourseOfValues

/-!
# Tests for `GebLean.Utilities.ERCourseOfValues`.
-/

open GebLean

/-- `cvRec` at `k = 0` with the node `proj 0` (which reads no β-positions,
so the reference table is the identity `f = id`) and value bound `proj 0`
extracts the input code itself, by `interp_cvRec_of_bounded`. -/
example (c : ℕ) :
    (ERMor1.cvRec (k := 0) (ERMor1.proj 0)
        (ERMor1.proj 0)).interp ![c] = c :=
  ERMor1.interp_cvRec_of_bounded
    (ERMor1.proj 0) (ERMor1.proj 0) c ![] id
    (fun j _ => le_refl j)
    (fun _ hj => hj)
    (fun _ _ _ _ => rfl)

/-- The `cvRec` output at the identity instantiation is dominated by its
value bound, by `interp_cvRec_le_bound`. -/
example (c : ℕ) :
    (ERMor1.cvRec (k := 0) (ERMor1.proj 0)
        (ERMor1.proj 0)).interp ![c] ≤ c :=
  ERMor1.interp_cvRec_le_bound
    (ERMor1.proj 0) (ERMor1.proj 0) ![c]
