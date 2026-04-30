import GebLean.LawvereKSimQuot
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereKSimQuot

Sanity tests verifying that the quotient-category
machinery operates correctly on small inputs.
-/

open GebLean

private def ctx0 : Fin 0 → ℕ := Fin.elim0
private def ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x
private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]

-- Two different syntactic forms of "constantly 5" at
-- arity 1 have the same interpretation (one uses
-- `raise` for level padding; both should evaluate to
-- 5 at every input).
private def five₁ : KMor1 1 :=
  KMor1.comp KMor1.succ (fun _ =>
    KMor1.comp KMor1.succ (fun _ =>
      KMor1.comp KMor1.succ (fun _ =>
        KMor1.comp KMor1.succ (fun _ =>
          KMor1.comp KMor1.succ (fun _ =>
            KMor1.zero (n := 1))))))

private def five₂ : KMor1 1 :=
  KMor1.comp KMor1.succ (fun _ =>
    KMor1.comp KMor1.succ (fun _ =>
      KMor1.comp KMor1.succ (fun _ =>
        KMor1.comp KMor1.succ (fun _ =>
          KMor1.comp KMor1.succ (fun _ =>
            KMor1.raise (KMor1.zero (n := 1)))))))

-- Both interpret to 5.
#guard five₁.interp (ctx1 0) == 5
#guard five₂.interp (ctx1 0) == 5
#guard five₁.interp (ctx1 0) == five₂.interp (ctx1 0)

-- The KMorN identity wrapper: id at arity 2 produces
-- (proj 0, proj 1), which interp returns the input.
#guard
  let idHom : KMorN 2 2 := KMorN.id 2
  idHom.interp (ctx2 5 7) 0 == 5

#guard
  let idHom : KMorN 2 2 := KMorN.id 2
  idHom.interp (ctx2 5 7) 1 == 7
