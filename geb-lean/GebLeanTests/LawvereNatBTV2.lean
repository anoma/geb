import GebLean.LawvereNatBTV2
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for `LawvereNatBTV2`

`#guard` sanity tests covering the bottom-up two-sort theory's
foundational and BT structural constructors at small numerical
inputs.  The recursive constructors (`foldBTNat`, `foldBTBT`,
`boundedNatRec`) are exercised by the equivalence's round-trip
identity proofs in `GebLean/LawvereERNatBTV2Equiv.lean` rather
than by direct `#guard`s — their interpretation goes through
ER's witness search, which is slow even at small inputs.
-/

open GebLean

private def ctxN0 : Fin 0 → ℕ := Fin.elim0

private def ctxB0 : Fin 0 → BTL := Fin.elim0

private def ctxN1 (x : ℕ) : Fin 1 → ℕ :=
  fun _ => x

private def ctxN2 (x y : ℕ) : Fin 2 → ℕ :=
  ![x, y]

private def ctxB1 (t : BTL) : Fin 1 → BTL :=
  fun _ => t

private def interpNatV2 {nm : ℕ × ℕ}
    (t : NatBTMor1V2 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) : ℕ :=
  t.interp ctxN ctxB

private def interpBTV2 {nm : ℕ × ℕ}
    (t : NatBTMor1V2 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) : BTL :=
  t.interp ctxN ctxB

#guard
  interpNatV2 (NatBTMor1V2.zero (nm := (0, 0))) ctxN0 ctxB0 == 0

#guard
  interpNatV2
    (NatBTMor1V2.succ (NatBTMor1V2.zero (nm := (0, 0))))
    ctxN0 ctxB0 == 1

#guard
  interpNatV2
    (NatBTMor1V2.succ
      (NatBTMor1V2.succ
        (NatBTMor1V2.succ (NatBTMor1V2.zero (nm := (0, 0))))))
    ctxN0 ctxB0 == 3

#guard
  interpNatV2 (NatBTMor1V2.natProj (nm := (1, 0)) (0 : Fin 1))
    (ctxN1 5) ctxB0 == 5

#guard
  interpNatV2 (NatBTMor1V2.natProj (nm := (2, 0)) (1 : Fin 2))
    (ctxN2 7 3) ctxB0 == 3

example :
    interpNatV2
      (NatBTMor1V2.sub
        (NatBTMor1V2.natProj (nm := (2, 0)) (0 : Fin 2))
        (NatBTMor1V2.natProj (nm := (2, 0)) (1 : Fin 2)))
      (ctxN2 7 3) ctxB0 = 4 := by
  simp [interpNatV2, NatBTMor1V2.interp_sub,
    NatBTMor1V2.interp_natProj, ctxN2]

example :
    interpNatV2
      (NatBTMor1V2.sub
        (NatBTMor1V2.natProj (nm := (2, 0)) (0 : Fin 2))
        (NatBTMor1V2.natProj (nm := (2, 0)) (1 : Fin 2)))
      (ctxN2 3 7) ctxB0 = 0 := by
  simp [interpNatV2, NatBTMor1V2.interp_sub,
    NatBTMor1V2.interp_natProj, ctxN2]

example :
    interpBTV2
      (NatBTMor1V2.leafBT (NatBTMor1V2.zero (nm := (0, 0))))
      ctxN0 ctxB0 = BTL.leaf 0 := by
  simp [interpBTV2, NatBTMor1V2.interp_leafBT,
    NatBTMor1V2.interp_zero]

example :
    interpBTV2
      (NatBTMor1V2.leafBT
        (NatBTMor1V2.succ (NatBTMor1V2.zero (nm := (0, 0)))))
      ctxN0 ctxB0 = BTL.leaf 1 := by
  simp [interpBTV2, NatBTMor1V2.interp_leafBT,
    NatBTMor1V2.interp_succ, NatBTMor1V2.interp_zero]

example :
    interpBTV2
      (NatBTMor1V2.nodeBT
        (NatBTMor1V2.leafBT (NatBTMor1V2.zero (nm := (0, 0))))
        (NatBTMor1V2.leafBT
          (NatBTMor1V2.succ (NatBTMor1V2.zero (nm := (0, 0))))))
      ctxN0 ctxB0 =
    BTL.node (BTL.leaf 0) (BTL.leaf 1) := by
  simp [interpBTV2, NatBTMor1V2.interp_nodeBT,
    NatBTMor1V2.interp_leafBT, NatBTMor1V2.interp_succ,
    NatBTMor1V2.interp_zero]

example :
    interpBTV2 (NatBTMor1V2.btProj (nm := (0, 1)) (0 : Fin 1))
      ctxN0 (ctxB1 (BTL.leaf 5)) = BTL.leaf 5 := by
  simp [interpBTV2, NatBTMor1V2.interp_btProj, ctxB1]

example :
    interpBTV2 (NatBTMor1V2.btProj (nm := (0, 1)) (0 : Fin 1))
      ctxN0
      (ctxB1 (BTL.node (BTL.leaf 2) (BTL.leaf 3))) =
    BTL.node (BTL.leaf 2) (BTL.leaf 3) := by
  simp [interpBTV2, NatBTMor1V2.interp_btProj, ctxB1]

example :
    interpNatV2
      (NatBTMor1V2.encodeBT
        (NatBTMor1V2.leafBT (NatBTMor1V2.zero (nm := (0, 0)))))
      ctxN0 ctxB0 = (BTL.leaf 0).encode := by
  simp [interpNatV2, NatBTMor1V2.interp_encodeBT,
    NatBTMor1V2.interp_leafBT, NatBTMor1V2.interp_zero]

example :
    interpBTV2
      (NatBTMor1V2.decodeBT
        (NatBTMor1V2.encodeBT
          (NatBTMor1V2.leafBT
            (NatBTMor1V2.succ
              (NatBTMor1V2.zero (nm := (0, 0)))))))
      ctxN0 ctxB0 = BTL.leaf 1 := by
  simp [interpBTV2, NatBTMor1V2.interp_decodeBT,
    NatBTMor1V2.interp_encodeBT, NatBTMor1V2.interp_leafBT,
    NatBTMor1V2.interp_succ, NatBTMor1V2.interp_zero,
    BTL.decode_encode]

example :
    interpBTV2
      (NatBTMor1V2.decodeBT
        (NatBTMor1V2.encodeBT
          (NatBTMor1V2.nodeBT
            (NatBTMor1V2.leafBT
              (NatBTMor1V2.zero (nm := (0, 0))))
            (NatBTMor1V2.leafBT
              (NatBTMor1V2.succ
                (NatBTMor1V2.zero (nm := (0, 0))))))))
      ctxN0 ctxB0 =
    BTL.node (BTL.leaf 0) (BTL.leaf 1) := by
  simp [interpBTV2, NatBTMor1V2.interp_decodeBT,
    NatBTMor1V2.interp_encodeBT, NatBTMor1V2.interp_nodeBT,
    NatBTMor1V2.interp_leafBT, NatBTMor1V2.interp_succ,
    NatBTMor1V2.interp_zero, BTL.decode_encode]

example :
    interpNatV2
      (NatBTMor1V2.compNat
        (nm := (1, 0)) (nm' := (1, 0))
        (NatBTMor1V2.succ
          (NatBTMor1V2.natProj (nm := (1, 0)) (0 : Fin 1)))
        (fun _ : Fin 1 =>
          NatBTMor1V2.succ
            (NatBTMor1V2.natProj (nm := (1, 0)) (0 : Fin 1)))
        (Fin.elim0))
      (ctxN1 4) ctxB0 = 6 := by
  simp [interpNatV2, NatBTMor1V2.interp_compNat,
    NatBTMor1V2.interp_succ, NatBTMor1V2.interp_natProj,
    ctxN1]

example :
    interpNatV2
      (NatBTMor1V2.compNat
        (nm := (2, 0)) (nm' := (2, 0))
        (NatBTMor1V2.sub
          (NatBTMor1V2.natProj (nm := (2, 0)) (0 : Fin 2))
          (NatBTMor1V2.natProj (nm := (2, 0)) (1 : Fin 2)))
        (fun i : Fin 2 =>
          NatBTMor1V2.natProj (nm := (2, 0))
            (⟨1 - i.val, by omega⟩ : Fin 2))
        (Fin.elim0))
      (ctxN2 7 3) ctxB0 = 0 := by
  simp [interpNatV2, NatBTMor1V2.interp_compNat,
    NatBTMor1V2.interp_sub, NatBTMor1V2.interp_natProj,
    ctxN2]
