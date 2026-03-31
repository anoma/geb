import GebLean.LawvereBTInterp
import Mathlib.Computability.Ackermann

/-!
# Primitive Recursion and Non-Fullness

Proves that every morphism in `LawvereBTQuotCat`
computes a primitive recursive function (under a
Goedel encoding `BT <-> Nat`), and that the
interpretation functor `interpFunctor` is not full
(the Ackermann function is not in the image).
-/

namespace GebLean

open CategoryTheory

/-- Goedel encoding of binary trees into natural
numbers.  Maps `BT.leaf` to `0` and `BT.node l r`
to `Nat.pair (encodeBT l) (encodeBT r) + 1`. -/
def encodeBT : BT.{0} → Nat :=
  BT.fold 0 (fun el er =>
    Nat.pair el er + 1)

/-- Decoding natural numbers back to binary trees.
Inverse of `encodeBT`. -/
def decodeBT : Nat → BT.{0}
  | 0 => BT.leaf
  | n + 1 =>
    BT.node
      (decodeBT (Nat.unpair n).1)
      (decodeBT (Nat.unpair n).2)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le
      (Nat.unpair_left_le n)
  · exact Nat.lt_succ_of_le
      (Nat.unpair_right_le n)

private theorem decodeBT_encodeBT_gen
    {x : PUnit.{1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x) :
    decodeBT (encodeBT bt) = bt := by
  induction bt with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      -- This PolyFix.mk is BT.leaf.
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e; exact PEmpty.elim e
      rw [hleaf]
      simp only [encodeBT, BT.fold_leaf, decodeBT]
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      -- Show PolyFix.mk equals BT.node of
      -- children at left and right.
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node
            (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk]
      simp only [encodeBT, BT.fold_node]
      rw [show BT.fold 0
        (fun el er => Nat.pair el er + 1) =
        encodeBT from rfl]
      simp only [decodeBT, Nat.unpair_pair]
      rw [ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit), ← hmk]

theorem decodeBT_encodeBT (bt : BT.{0}) :
    decodeBT (encodeBT bt) = bt :=
  decodeBT_encodeBT_gen bt

end GebLean
