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

theorem encodeBT_injective :
    Function.Injective encodeBT := by
  intro a b h
  rw [← decodeBT_encodeBT a,
    ← decodeBT_encodeBT b, h]

instance : Encodable BT.{0} where
  encode := encodeBT
  decode n := some (decodeBT n)
  encodek bt := by simp [decodeBT_encodeBT]

private theorem encodeDecode_primrec :
    Primrec (fun (n : Nat) =>
      encodeBT (decodeBT n)) := by
  apply @Primrec.nat_omega_rec' Nat Nat _ _
    (fun n => encodeBT (decodeBT n))
    (m := id)
    (l := fun n => match n with
      | 0 => []
      | n + 1 =>
        [(Nat.unpair n).1,
          (Nat.unpair n).2])
    (g := fun n rs =>
      @Nat.casesOn
        (fun _ => Option Nat) n
        (some 0)
        (fun _ => some
          (Nat.pair (rs.getD 0 0)
            (rs.getD 1 0) + 1)))
  · exact Primrec.id
  · have heq : (fun (n : Nat) =>
        match n with
        | 0 => ([] : List Nat)
        | n + 1 =>
          [(Nat.unpair n).1,
            (Nat.unpair n).2]) =
      (fun (n : Nat) =>
        @Nat.casesOn
          (fun _ => List Nat) n
          ([] : List Nat)
          (fun k =>
            [(Nat.unpair k).1,
              (Nat.unpair k).2])) := by
      funext n; cases n <;> rfl
    rw [heq]
    exact Primrec.nat_casesOn
      Primrec.id
      (Primrec.const [])
      (Primrec₂.comp
        Primrec.list_cons
        (Primrec.fst.comp
          (Primrec.unpair.comp
            Primrec.snd))
        (Primrec₂.comp
          Primrec.list_cons
          (Primrec.snd.comp
            (Primrec.unpair.comp
              Primrec.snd))
          (Primrec.const [])))
  · unfold Primrec₂
    apply Primrec.nat_casesOn
      Primrec.fst
      (Primrec.const (some 0))
    unfold Primrec₂
    exact Primrec.option_some.comp
      (Primrec.succ.comp
        (Primrec₂.natPair.comp
          (Primrec₂.comp
            (f := fun (l : List Nat)
              (n : Nat) => l.getD n 0)
            (Primrec.list_getD 0)
            (Primrec.snd.comp
              Primrec.fst)
            (Primrec.const 0))
          (Primrec₂.comp
            (f := fun (l : List Nat)
              (n : Nat) => l.getD n 0)
            (Primrec.list_getD 0)
            (Primrec.snd.comp
              Primrec.fst)
            (Primrec.const 1))))
  · intro b b' hmem
    match b with
    | 0 =>
      simp only [List.not_mem_nil] at hmem
    | n + 1 =>
      simp only [id_eq]
      simp only [List.mem_cons,
        List.mem_nil_iff,
        or_false] at hmem
      rcases hmem with h | h
      · rw [h]
        exact Nat.lt_succ_of_le
          (Nat.unpair_left_le n)
      · rw [h]
        exact Nat.lt_succ_of_le
          (Nat.unpair_right_le n)
  · intro b
    match b with
    | 0 =>
      simp [decodeBT, encodeBT,
        BT.fold_leaf]
    | n + 1 =>
      simp [decodeBT, encodeBT,
        BT.fold_node, List.getD]

instance : Primcodable BT.{0} where
  prim := by
    have heq : (fun n =>
        @Encodable.encode (Option BT.{0}) _
          (@Encodable.decode BT.{0} _ n)) =
      (fun n =>
        encodeBT (decodeBT n) + 1) := by
      funext n
      simp [Encodable.decode,
        Encodable.encode]
    rw [heq]
    exact Nat.Primrec.comp
      Nat.Primrec.succ
      (Primrec.nat_iff.mp
        encodeDecode_primrec)

end GebLean
