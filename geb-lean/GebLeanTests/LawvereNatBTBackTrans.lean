import GebLean.LawvereNatBTBackTrans
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for `LawvereNatBTBackTrans`

Sanity tests covering `isFoldFree`, `toER`, and `toER_bt` on
small fold-free terms.
-/

open GebLean

private def ctxN0 : Fin 0 → ℕ := Fin.elim0

private def ctxN1 (x : ℕ) : Fin 1 → ℕ := fun _ => x

/-- A zero term at arity `(0, 0)` is fold-free. -/
example : NatBTMor1.isFoldFree
    (NatBTMor1.zero (nm := (0, 0))) :=
  trivial

/-- `toER` of `zero` interprets to `0`. -/
#guard
  (NatBTMor1.zero (nm := (0, 0))).toER.interp ctxN0 == 0

/-- `toER` of `succ zero` interprets to `1`. -/
#guard
  (NatBTMor1.succ
      (NatBTMor1.zero (nm := (0, 0)))).toER.interp ctxN0 == 1

/-- `toER` of `natProj 0` at arity `(1, 0)` interprets as a
context lookup. -/
#guard
  (NatBTMor1.natProj (nm := (1, 0)) (0 : Fin 1)).toER.interp
      (ctxN1 7) == 7

/-- `toER` of `sub` at `(7, 3)` interprets to cut-off
subtraction result `4`. -/
#guard
  (NatBTMor1.sub
      (NatBTMor1.natProj (nm := (2, 0)) (0 : Fin 2))
      (NatBTMor1.natProj (nm := (2, 0)) (1 : Fin 2)))
    .toER.interp ![7, 3] == 4

/-- `toER_bt` of `leafBT zero` interprets to
`BTL.encode (BTL.leaf 0) = 0`. -/
#guard
  (NatBTMor1.leafBT
      (NatBTMor1.zero (nm := (0, 0)))).toER_bt.interp
      ctxN0 == 0

/-- `toER_bt` of `leafBT (succ zero)` interprets to
`BTL.encode (BTL.leaf 1) = 2`. -/
#guard
  (NatBTMor1.leafBT
      (NatBTMor1.succ
        (NatBTMor1.zero (nm := (0, 0))))).toER_bt.interp
      ctxN0 == 2

/-- `toER_bt` of a nested `nodeBT` matches the corresponding
`BTL.encode` of the constructed tree. -/
#guard
  (NatBTMor1.nodeBT
      (NatBTMor1.leafBT (NatBTMor1.zero (nm := (0, 0))))
      (NatBTMor1.leafBT
        (NatBTMor1.succ
          (NatBTMor1.zero (nm := (0, 0)))))).toER_bt.interp
      ctxN0 ==
    BTL.encode (BTL.node (BTL.leaf 0) (BTL.leaf 1))

/-- `toER` of `encodeBT (leafBT zero)` agrees with
`BTL.encode (BTL.leaf 0)`. -/
#guard
  (NatBTMor1.encodeBT
      (NatBTMor1.leafBT
        (NatBTMor1.zero (nm := (0, 0))))).toER.interp
      ctxN0 == BTL.encode (BTL.leaf 0)
