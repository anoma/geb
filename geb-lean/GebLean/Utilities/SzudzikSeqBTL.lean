import GebLean.Utilities.SzudzikSeq
import GebLean.LawvereNatBT

/-!
# Course-of-values fold on BTL Gödel codes: correctness

Establishes that `Nat.foldBTLOnCode` agrees with `BTL.fold`
when applied to a `BTL.encode` Gödel code.  Separated from
`Utilities/SzudzikSeq.lean` so that the Nat-level definition
of `Nat.foldBTLOnCode` is available within `LawvereNatBT.lean`
without inducing an import cycle.
-/

namespace GebLean

/-- Correctness of `Nat.foldBTLOnCode` against `BTL.fold`:
running the labeled course-of-values recursion on the Gödel
code of a labeled tree agrees with the structural fold of
that tree. -/
theorem foldBTLOnCode_encode {α : Type*}
    (baseLeaf : ℕ → α) (stepNode : α → α → α) (t : BTL) :
    Nat.foldBTLOnCode baseLeaf stepNode (BTL.encode t) =
      BTL.fold baseLeaf stepNode t := by
  induction t with
  | leaf k =>
      change Nat.foldBTLOnCode baseLeaf stepNode (2 * k) =
        baseLeaf k
      match h2k : 2 * k with
      | 0 =>
          have hk : k = 0 := by omega
          subst hk
          simp
      | m + 1 =>
          have heven : (m + 1) % 2 = 0 := by omega
          have hdiv : (m + 1) / 2 = k := by omega
          rw [Nat.foldBTLOnCode_even baseLeaf stepNode
            (m + 1) (Nat.succ_pos m) heven, hdiv]
  | node l r ihl ihr =>
      change Nat.foldBTLOnCode baseLeaf stepNode
        (2 * Nat.pair l.encode r.encode + 1) =
        stepNode (BTL.fold baseLeaf stepNode l)
          (BTL.fold baseLeaf stepNode r)
      set p := Nat.pair l.encode r.encode with hp
      change Nat.foldBTLOnCode baseLeaf stepNode
        (2 * p + 1) = _
      have hodd : (2 * p + 1) % 2 ≠ 0 := by omega
      have hdiv : (2 * p + 1) / 2 = p := by omega
      rw [Nat.foldBTLOnCode_odd baseLeaf stepNode
        (2 * p + 1) hodd, hdiv]
      rw [show Nat.unpair p = (l.encode, r.encode) from
        by rw [hp]; exact Nat.unpair_pair _ _]
      rw [ihl, ihr]

end GebLean
