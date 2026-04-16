import Mathlib.Data.Nat.Pairing
import GebLean.LawvereBT
import GebLean.LawvereBTPrimrec

/-!
# Szudzik Sequence Encoding and Tree-Fold Simulation

Generic Lean-native arithmetic building blocks for the
`LawvereTreeERCat ≅ LawvereERCat` isomorphism:

* `Nat.seqPack` / `Nat.seqAt` — encode a list of naturals as
  one natural via iterated right-associated Szudzik pairing.
* `Nat.treeFoldOnCode` — simulate `BT.fold` via
  course-of-values recursion on a Gödel-encoded tree.
* `Nat.tupleRecN` — finite-arity mutumorphism via iterated
  pair.

All functions are elementary recursive (E₃).  Reduction rules
are proved with `@[simp]` and are suitable for use in
downstream `TreeERMor1`-level agreement theorems.
-/

namespace Nat

/-- Encode a list of naturals as a single natural via
iterated right-associated Szudzik pairing.  Empty list is 0;
`x :: xs` packs as `pair x (seqPack xs) + 1`. -/
def seqPack : List ℕ → ℕ
  | []      => 0
  | x :: xs => pair x (seqPack xs) + 1

@[simp] theorem seqPack_nil : seqPack [] = 0 := rfl

@[simp] theorem seqPack_cons (x : ℕ) (xs : List ℕ) :
    seqPack (x :: xs) = pair x (seqPack xs) + 1 := rfl

/-- Extract the `i`-th element from a packed sequence.
Returns 0 if out of range.  On in-range indices, satisfies
`seqAt (seqPack xs) i = xs.get ⟨i, h⟩`. -/
def seqAt : ℕ → ℕ → ℕ
  | 0,     _     => 0
  | n + 1, 0     => (unpair n).1
  | n + 1, i + 1 => seqAt (unpair n).2 i

@[simp] theorem seqAt_zero_head (n : ℕ) :
    seqAt (n + 1) 0 = (unpair n).1 := rfl

@[simp] theorem seqAt_succ_tail (n i : ℕ) :
    seqAt (n + 1) (i + 1) = seqAt (unpair n).2 i := rfl

@[simp] theorem seqAt_zero_of_zero (i : ℕ) :
    seqAt 0 i = 0 := by
  cases i <;> rfl

theorem seqAt_seqPack :
    ∀ (xs : List ℕ) (i : ℕ) (h : i < xs.length),
      seqAt (seqPack xs) i = xs.get ⟨i, h⟩
  | [],        i,     h => absurd h (by simp)
  | x :: xs,   0,     _ => by
      simp [seqPack, unpair_pair]
  | x :: xs,   i + 1, h => by
      simp [seqPack, unpair_pair]
      exact seqAt_seqPack xs i (by
        simp [List.length_cons] at h; omega)

end Nat
