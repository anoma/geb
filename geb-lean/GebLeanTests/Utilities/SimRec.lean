import GebLean.Utilities.SimRec

/-!
# Tests for `Nat.simRecVec`, `Nat.simRec`,
# `Nat.simRecVec_le_of_dominates`.

Nat-level simultaneous primitive-recursion semantic
function for the ER ↔ K^sim_2 categorical equivalence.
See `GebLean.Utilities.SimRec` and master design §3.2
in `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

open Nat

-- Identity-case smoke (k = 0, a = 0): 1-component
-- "simrec" reduces to ordinary recursion.  Step input
-- arity = a + 1 + (k + 1) = 0 + 1 + 1 = 2: slot 0 =
-- counter, slot 1 = previous singleton component (no
-- params at a = 0).

-- Constant base, constant step: f(0) = 5, f(n+1) = 7.
#guard simRecVec 0 0 (fun _ _ => 5) (fun _ _ => 7) 0
         (fun _ => 0) ⟨0, by decide⟩ = 5

-- Successor step on the previous value: f(0) = 5,
-- f(n+1) = prev + 1.  Step `fun _ ctx => ctx 1 + 1`
-- consumes slot 1 (the previous value).
#guard simRecVec 0 0 (fun _ _ => 5)
         (fun _ ctx => ctx 1 + 1) 1
         (fun _ => 0) ⟨0, by decide⟩ = 6

-- Non-trivial 2-component swap: f_0(0) = 1, f_1(0) = 2,
-- step swaps the components.  At odd n, component 0 = 2.
-- Iteration trace (k = 1, a = 0, step input arity = 3):
--   iteration 0: (1, 2)
--   iteration 1: swap → (2, 1)
--   iteration 5: swap → (2, 1)  -- component 0 = 2.
example :
    simRecVec 1 0
      (fun j _ => match j with
        | ⟨0, _⟩ => 1
        | ⟨1, _⟩ => 2)
      (fun j ctx => match j with
        | ⟨0, _⟩ => ctx ⟨2, by decide⟩
        | ⟨1, _⟩ => ctx ⟨1, by decide⟩)
      5 (fun _ => 0) ⟨0, by decide⟩ = 2 := by decide
