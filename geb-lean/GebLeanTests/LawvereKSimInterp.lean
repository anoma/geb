import GebLean.LawvereKSimInterp
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereKSimInterp

`#guard` sanity tests covering the interpretation of each
`KMor1` generator and `KMorN` operation.
-/

open GebLean

private def ctx0 : Fin 0 → ℕ := Fin.elim0
private def ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x
private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]
private def ctx3 (x y z : ℕ) : Fin 3 → ℕ := ![x, y, z]

-- zero at the empty context.
#guard (KMor1.zero (n := 0)).interp ctx0 == 0

-- zero at higher arity (P-rule: KMor1.zero is at any arity).
#guard (KMor1.zero (n := 2)).interp (ctx2 5 7) == 0

-- succ of 5.
#guard KMor1.succ.interp (ctx1 5) == 6

-- proj 0 out of (7, 3).
#guard (KMor1.proj (0 : Fin 2)).interp (ctx2 7 3) == 7

-- proj 1 out of (7, 3).
#guard (KMor1.proj (1 : Fin 2)).interp (ctx2 7 3) == 3

-- raise is the same as the underlying term.
#guard (KMor1.raise KMor1.succ).interp (ctx1 5) == 6

-- comp (succ ∘ proj 0) on (7, 3) yields succ 7 = 8.
#guard
  (KMor1.comp KMor1.succ
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 2))).interp
    (ctx2 7 3) == 8
