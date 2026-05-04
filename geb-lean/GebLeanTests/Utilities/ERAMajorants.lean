import GebLean.Utilities.ERAMajorants

/-!
# Tests for `GebLean.Utilities.ERAMajorants`

Per the project's ER-side `.interp` test discipline:
`#guard`s are restricted to bprod-free composites at small
inputs.  `A_one` and `A_one_iter` use `bsum` via `mulN`
inside `addN`, but `bsum` size scales linearly with input
so small-input `#guard`s terminate quickly.  `A_two_iter`
at `r ≥ 1` aliases `towerER` (which uses `expER`'s `bprod`)
and is excluded except at `r = 0` (definitionally
`proj 0`).

Closed-form correctness for all `r` is captured by the
`@[simp]` interp lemmas
(`ERMor1.interp_A_one`, `ERMor1.interp_A_one_iter`,
`ERMor1.interp_A_two_iter`); these `#guard`s are sanity
backstops, not the primary correctness witness.
-/

namespace GebLean

-- A_one: shallow, with bsum reductions only at small bounds
-- via mulN (= boolAnd = bsum ...).  No bprod, no boundedRec;
-- bsum-via-mulN size scales linearly with input, so
-- small-input #guards terminate fast.
#guard ERMor1.A_one.interp ![0] = 2
#guard ERMor1.A_one.interp ![3] = 8
#guard ERMor1.A_one.interp ![5] = 12

-- A_one_iter at small r: bsum sizes <= 9 at r = 2, x = 3.
#guard (ERMor1.A_one_iter 0).interp ![3] = 3
#guard (ERMor1.A_one_iter 1).interp ![3] = 8
#guard (ERMor1.A_one_iter 2).interp ![0] = 6
#guard (ERMor1.A_one_iter 2).interp ![3] = 18

-- A_two_iter at r = 0 reduces definitionally to proj 0;
-- safe to #guard.
#guard (ERMor1.A_two_iter 0).interp ![5] = 5

-- No #guard on A_two_iter at r ≥ 1: kernel reduction
-- explodes through expER's bprod.  Closed-form correctness
-- is captured by interp_A_two_iter + the existing
-- interp_towerER lemma.

end GebLean
