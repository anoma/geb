import GebLean.LawvereGodelT
import GebLean.LawvereGodelTQuot
import GebLean.LawvereGodelTInterp
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for `LawvereGodelT`

`#guard` sanity tests covering `GodelTType.arrow0`,
`GodelTTerm.interp` at each constructor, and the
`GodelTMor1` categorical layer: per-constructor interp
lemmas, tuple composition, and the quotient-level
identity / composition.
-/

open GebLean

/-! ### `GodelTType` -/

#guard GodelTType.arrow0 0 == .base
#guard GodelTType.arrow0 1 == .arrow .base .base
#guard GodelTType.arrow0 2 == .arrow .base (.arrow .base .base)

/-! ### `GodelTTerm` combinator-logic interp -/

#guard GodelTTerm.zero.interp = 0
#guard GodelTTerm.succ.interp 0 = 1
#guard GodelTTerm.succ.interp 3 = 4
#guard GodelTTerm.pred.interp 0 = 0
#guard GodelTTerm.pred.interp 5 = 4
#guard (GodelTTerm.K .base .base).interp 7 3 = 7
#guard (GodelTTerm.S .base .base .base).interp
  (fun _ _ => 42) (fun _ => 99) 0 = 42
#guard (GodelTTerm.disc .base).interp 0 7 3 = 7
#guard (GodelTTerm.disc .base).interp 5 7 3 = 3
#guard GodelTTerm.iter.interp 0 Nat.succ 10 = 10
#guard GodelTTerm.iter.interp 3 Nat.succ 10 = 13
#guard GodelTTerm.iter.interp 4 (· * 2) 1 = 16

/-! ### `GodelTMor1` categorical layer -/

private def gt_ctx0 : Fin 0 → ℕ := Fin.elim0
private def gt_ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x
private def gt_ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]
private def gt_ctx3 (x y z : ℕ) : Fin 3 → ℕ := ![x, y, z]

#guard GodelTMor1.zero.interp gt_ctx0 = 0
#guard GodelTMor1.succ.interp (gt_ctx1 5) = 6
#guard GodelTMor1.pred.interp (gt_ctx1 5) = 4
#guard GodelTMor1.pred.interp (gt_ctx1 0) = 0
#guard (GodelTMor1.proj (k := 3) ⟨1, by omega⟩).interp
  (gt_ctx3 10 20 30) = 20
#guard GodelTMor1.sub.interp (gt_ctx2 7 3) = 4
#guard GodelTMor1.sub.interp (gt_ctx2 3 7) = 0
#guard GodelTMor1.disc.interp (gt_ctx3 0 7 3) = 7
#guard GodelTMor1.disc.interp (gt_ctx3 5 7 3) = 3

-- `bsum (proj 1)` at (3, x) computes Σ_{i<3} x = 3 * x.
#guard (GodelTMor1.bsum
    (GodelTMor1.proj (k := 2) ⟨1, by omega⟩)).interp
  (gt_ctx2 3 5) = 15

-- `bprod (proj 1)` at (3, x) computes Π_{i<3} x = x^3.
#guard (GodelTMor1.bprod
    (GodelTMor1.proj (k := 2) ⟨1, by omega⟩)).interp
  (gt_ctx2 3 5) = 125

/-! ### Tuple interp, identity, composition -/

#guard (GodelTMorN.id 2).interp (gt_ctx2 7 9) 0 = 7
#guard (GodelTMorN.id 2).interp (gt_ctx2 7 9) 1 = 9
