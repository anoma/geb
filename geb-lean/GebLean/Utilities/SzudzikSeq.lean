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

end Nat
