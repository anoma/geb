import GebLean.LawvereGodelTERCatEquiv
import Mathlib.Data.Fin.VecNotation

/-!
# Round-trip tests for the
`LawvereGodelTCat ≌ LawvereERCat` equivalence

`#guard` sanity tests verifying that `toER` /
`toGodelT` and their round-trips preserve interpretation
on concrete primitive terms.
-/

open GebLean

private def equiv_ctx0 : Fin 0 → ℕ := Fin.elim0
private def equiv_ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x
private def equiv_ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]
private def equiv_ctx3 (x y z : ℕ) : Fin 3 → ℕ := ![x, y, z]

/-! ### `GodelTMor1.toER` on primitives -/

#guard (GodelTMor1.zero.toER).interp equiv_ctx0 = 0
#guard (GodelTMor1.succ.toER).interp (equiv_ctx1 5) = 6
#guard (GodelTMor1.pred.toER).interp (equiv_ctx1 5) = 4
#guard (GodelTMor1.sub.toER).interp (equiv_ctx2 7 3) = 4
#guard (GodelTMor1.disc.toER).interp (equiv_ctx3 0 7 3) = 7
#guard (GodelTMor1.disc.toER).interp (equiv_ctx3 5 7 3) = 3

/-! ### `ERMor1.toGodelT` on primitives -/

#guard (ERMor1.zero.toGodelT).interp equiv_ctx0 = 0
#guard (ERMor1.succ.toGodelT).interp (equiv_ctx1 5) = 6
#guard (ERMor1.sub.toGodelT).interp (equiv_ctx2 7 3) = 4
#guard (ERMor1.sub.toGodelT).interp (equiv_ctx2 3 7) = 0

/-! ### Round-trip identities on concrete terms -/

#guard (GodelTMor1.succ.toER.toGodelT).interp (equiv_ctx1 7) =
  GodelTMor1.succ.interp (equiv_ctx1 7)
#guard (GodelTMor1.pred.toER.toGodelT).interp (equiv_ctx1 7) =
  GodelTMor1.pred.interp (equiv_ctx1 7)
#guard (GodelTMor1.disc.toER.toGodelT).interp
    (equiv_ctx3 0 5 9) = GodelTMor1.disc.interp
  (equiv_ctx3 0 5 9)

#guard (ERMor1.sub.toGodelT.toER).interp (equiv_ctx2 8 3) =
  ERMor1.sub.interp (equiv_ctx2 8 3)
#guard (ERMor1.succ.toGodelT.toER).interp (equiv_ctx1 4) =
  ERMor1.succ.interp (equiv_ctx1 4)
