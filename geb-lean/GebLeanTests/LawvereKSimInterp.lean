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

/-- Addition `λ x y. x + y` as a level-1 K^sim
composite: simrec on the first argument (x) with
base = proj 0 of the one-parameter slot (returns y
at x = 0) and step = succ applied to the previous
value (occupying slot 2 of the step context). -/
private def addK : KMor1 2 :=
  KMor1.simrec (k := 0) (a := 1)
    (0 : Fin 1)
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 1))
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.succ
        (fun _ : Fin 1 => KMor1.proj (2 : Fin 3)))

#guard addK.interp (ctx2 3 5) == 8
#guard addK.interp (ctx2 0 0) == 0
#guard addK.interp (ctx2 7 1) == 8
#guard addK.level == 1

-- rec1 zero (proj 0) at recvar 0 returns 0 (predecessor base).
#guard (KMor1.rec1 (h := (KMor1.zero : KMor1 0))
    (g := (KMor1.proj ⟨0, by decide⟩ : KMor1 2))).interp
    ![0] == 0

-- rec1 zero (proj 0) at recvar 5 returns 4 (predecessor step).
#guard (KMor1.rec1 (h := (KMor1.zero : KMor1 0))
    (g := (KMor1.proj ⟨0, by decide⟩ : KMor1 2))).interp
    ![5] == 4
