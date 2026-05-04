import GebLean.LawvereNatBT
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereNatBT

`#guard` sanity tests covering `BTL` round-tripping and the
standard interpretation of `NatBTMor1` generators.
-/

open GebLean

-- BTL round-trip on specific leaves and internal nodes.
#guard BTL.decode (BTL.leaf 0).encode == BTL.leaf 0
#guard BTL.decode (BTL.leaf 7).encode == BTL.leaf 7
#guard BTL.decode
    (BTL.node (BTL.leaf 2) (BTL.leaf 3)).encode ==
  BTL.node (BTL.leaf 2) (BTL.leaf 3)

-- Empty ℕ-context for arity `(0, 0)` terms.
private def ctxN0 : Fin 0 → ℕ := Fin.elim0

-- Empty BT-context for arity `(0, 0)` terms.
private def ctxB0 : Fin 0 → BTL := Fin.elim0

-- A unary ℕ-context.
private def ctxN1 (x : ℕ) : Fin 1 → ℕ :=
  fun _ => x

-- A binary ℕ-context.
private def ctxN2 (x y : ℕ) : Fin 2 → ℕ :=
  ![x, y]

-- Wrapper specializing `interp` at the `.nat` sort so the
-- return type reduces syntactically to `ℕ`.
private def interpNat {nm : ℕ × ℕ}
    (t : NatBTMor1 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) : ℕ :=
  t.interp ctxN ctxB

-- Wrapper specializing `interp` at the `.bt` sort so the
-- return type reduces syntactically to `BTL`.
private def interpBT {nm : ℕ × ℕ}
    (t : NatBTMor1 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) : BTL :=
  t.interp ctxN ctxB

-- zero returns 0 regardless of context.
#guard
  interpNat (NatBTMor1.zero (nm := (0, 0))) ctxN0 ctxB0 == 0

-- succ adds one to its argument's interpretation.
#guard
  interpNat
    (NatBTMor1.succ (NatBTMor1.zero (nm := (0, 0))))
    ctxN0 ctxB0 == 1

-- natProj 0 out of (5) is 5.
#guard
  interpNat (NatBTMor1.natProj (nm := (1, 0)) (0 : Fin 1))
    (ctxN1 5) ctxB0 == 5

-- natProj 1 out of (7, 3) is 3.
#guard
  interpNat (NatBTMor1.natProj (nm := (2, 0)) (1 : Fin 2))
    (ctxN2 7 3) ctxB0 == 3

-- sub at (7, 3) computes cut-off subtraction 7 - 3 = 4.
#guard
  interpNat
    (NatBTMor1.sub
      (NatBTMor1.natProj (nm := (2, 0)) (0 : Fin 2))
      (NatBTMor1.natProj (nm := (2, 0)) (1 : Fin 2)))
    (ctxN2 7 3) ctxB0 == 4

-- sub is cut-off: at (3, 7) it is 0.
#guard
  interpNat
    (NatBTMor1.sub
      (NatBTMor1.natProj (nm := (2, 0)) (0 : Fin 2))
      (NatBTMor1.natProj (nm := (2, 0)) (1 : Fin 2)))
    (ctxN2 3 7) ctxB0 == 0

-- nodeBT of two leaf trees builds the node tree.
#guard
  interpBT
    (NatBTMor1.nodeBT
      (NatBTMor1.leafBT (NatBTMor1.zero (nm := (0, 0))))
      (NatBTMor1.leafBT
        (NatBTMor1.succ (NatBTMor1.zero (nm := (0, 0))))))
    ctxN0 ctxB0 ==
  BTL.node (BTL.leaf 0) (BTL.leaf 1)

-- encodeBT of leaf 0 is 0.
#guard
  interpNat
    (NatBTMor1.encodeBT
      (NatBTMor1.leafBT (NatBTMor1.zero (nm := (0, 0)))))
    ctxN0 ctxB0 == 0

-- decodeBT ∘ encodeBT recovers the original tree.
#guard
  interpBT
    (NatBTMor1.decodeBT
      (NatBTMor1.encodeBT
        (NatBTMor1.leafBT
          (NatBTMor1.succ (NatBTMor1.zero (nm := (0, 0)))))))
    ctxN0 ctxB0 == BTL.leaf 1
