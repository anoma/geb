import GebLean.LawvereERArith
import GebLean.LawvereERInterp
import GebLean.LawvereERPrimrec

/-!
# Tests for LawvereERPrimrec

Sanity tests: confirm `ERMor1.toPrimrec'` instances type-check for each
generator, and confirm `erInterpFunctor_not_full` type-checks.
-/

open GebLean

example : Nat.Primrec'
    (fun v : List.Vector ℕ 0 =>
      ERMor1.zero.interp v.get) :=
  ERMor1.zero.toPrimrec'

example : Nat.Primrec'
    (fun v : List.Vector ℕ 1 =>
      ERMor1.succ.interp v.get) :=
  ERMor1.succ.toPrimrec'

example : Nat.Primrec'
    (fun v : List.Vector ℕ 3 =>
      (ERMor1.proj (k := 3) 1).interp v.get) :=
  (ERMor1.proj 1).toPrimrec'

example : Nat.Primrec'
    (fun v : List.Vector ℕ 2 =>
      ERMor1.sub.interp v.get) :=
  ERMor1.sub.toPrimrec'

example : Nat.Primrec'
    (fun v : List.Vector ℕ 2 =>
      ERMor1.expER.interp v.get) :=
  ERMor1.expER.toPrimrec'

example : ¬ erInterpFunctor.Full :=
  erInterpFunctor_not_full
