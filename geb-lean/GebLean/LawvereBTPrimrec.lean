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

theorem encodeBT_decodeBT (n : Nat) :
    encodeBT (decodeBT n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [decodeBT, encodeBT,
        BT.fold_leaf]
    | n + 1 =>
      simp only [decodeBT, encodeBT,
        BT.fold_node]
      rw [show BT.fold 0
        (fun el er => Nat.pair el er + 1) =
        encodeBT from rfl]
      rw [ih _ (Nat.lt_succ_of_le
        (Nat.unpair_left_le n))]
      rw [ih _ (Nat.lt_succ_of_le
        (Nat.unpair_right_le n))]
      rw [Nat.pair_unpair n]

theorem decodeBT_primrec :
    Primrec (decodeBT : Nat → BT.{0}) := by
  change Nat.Primrec (fun n =>
    @Encodable.encode (Option BT.{0}) _
      (Option.map decodeBT
        (@Encodable.decode Nat _ n)))
  have heq : (fun n =>
    @Encodable.encode (Option BT.{0}) _
      (Option.map decodeBT
        (@Encodable.decode Nat _ n))) =
    (fun n =>
      @Encodable.encode (Option BT.{0}) _
        (@Encodable.decode BT.{0} _ n)) := by
    funext n
    simp [Encodable.decode,
      Encodable.encode]
  rw [heq]
  exact @Primcodable.prim BT.{0} _

private def btFoldChildren (bt : BT.{0}) :
    List BT.{0} :=
  @Nat.casesOn (fun _ => List BT.{0})
    (encodeBT bt)
    []
    (fun n =>
      [decodeBT (Nat.unpair n).1,
       decodeBT (Nat.unpair n).2])

private theorem btFoldChildren_primrec :
    Primrec btFoldChildren := by
  unfold btFoldChildren
  apply Primrec.nat_casesOn
  · exact Primrec.encode
  · exact Primrec.const []
  · unfold Primrec₂
    have hfst :
        Primrec (fun (p : BT.{0} × Nat) =>
          decodeBT (Nat.unpair p.2).1) :=
      decodeBT_primrec.comp
        (Primrec.fst.comp
          (Primrec.unpair.comp Primrec.snd))
    have hsnd :
        Primrec (fun (p : BT.{0} × Nat) =>
          decodeBT (Nat.unpair p.2).2) :=
      decodeBT_primrec.comp
        (Primrec.snd.comp
          (Primrec.unpair.comp Primrec.snd))
    exact Primrec₂.comp Primrec.list_cons
      hfst
      (Primrec₂.comp Primrec.list_cons
        hsnd (Primrec.const []))

private def btFoldRecombine
    (b : BT.{0}) (s : BT.{0} → BT.{0} → BT.{0})
    (bt : BT.{0}) (results : List BT.{0}) :
    Option BT.{0} :=
  @Nat.casesOn (fun _ => Option BT.{0})
    (encodeBT bt)
    (some b)
    (fun _ => some (s
      (results.getD 0 BT.leaf)
      (results.getD 1 BT.leaf)))

private theorem btFoldRecombine_primrec₂
    {b : BT.{0}}
    {s : BT.{0} → BT.{0} → BT.{0}}
    (hs : Primrec₂ s) :
    Primrec₂ (btFoldRecombine b s) := by
  unfold Primrec₂ btFoldRecombine
  apply Primrec.nat_casesOn
  · exact Primrec.encode.comp Primrec.fst
  · exact Primrec.const (some b)
  · unfold Primrec₂
    exact Primrec.option_some.comp
      (hs.comp
        ((Primrec.list_getD BT.leaf).comp
          (Primrec.snd.comp Primrec.fst)
          (Primrec.const 0))
        ((Primrec.list_getD BT.leaf).comp
          (Primrec.snd.comp Primrec.fst)
          (Primrec.const 1)))

private theorem btFoldChildren_lt
    (bt bt' : BT.{0})
    (hmem : bt' ∈ btFoldChildren bt) :
    encodeBT bt' < encodeBT bt := by
  unfold btFoldChildren at hmem
  generalize h : encodeBT bt = k at hmem
  match k with
  | 0 =>
    change bt' ∈ ([] : List BT.{0}) at hmem
    exact absurd hmem List.not_mem_nil
  | n + 1 =>
    change bt' ∈
      [decodeBT (Nat.unpair n).1,
       decodeBT (Nat.unpair n).2] at hmem
    simp only [List.mem_cons,
      List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl <;>
      rw [encodeBT_decodeBT]
    · exact Nat.lt_succ_of_le
        (Nat.unpair_left_le n)
    · exact Nat.lt_succ_of_le
        (Nat.unpair_right_le n)

private theorem btFoldChildren_leaf :
    btFoldChildren BT.leaf = [] := by
  unfold btFoldChildren
  simp only [encodeBT, BT.fold_leaf]
  rfl

private theorem btFoldChildren_node
    (l r : BT.{0}) :
    btFoldChildren (BT.node l r) = [l, r] := by
  unfold btFoldChildren
  simp only [encodeBT, BT.fold_node,
    Nat.unpair_pair]
  change [decodeBT (encodeBT l),
    decodeBT (encodeBT r)] = [l, r]
  rw [decodeBT_encodeBT, decodeBT_encodeBT]

private theorem btFoldRecombine_leaf
    (b : BT.{0})
    (s : BT.{0} → BT.{0} → BT.{0})
    (results : List BT.{0}) :
    btFoldRecombine b s BT.leaf results =
    some b := by
  unfold btFoldRecombine
  simp only [encodeBT, BT.fold_leaf]
  rfl

private theorem btFoldRecombine_node
    (b : BT.{0})
    (s : BT.{0} → BT.{0} → BT.{0})
    (l r : BT.{0}) (results : List BT.{0}) :
    btFoldRecombine b s (BT.node l r) results =
    some (s (results.getD 0 BT.leaf)
            (results.getD 1 BT.leaf)) := by
  unfold btFoldRecombine
  simp only [encodeBT, BT.fold_node]

private theorem btFoldFuncEq
    (b : BT.{0})
    (s : BT.{0} → BT.{0} → BT.{0})
    (bt : BT.{0}) :
    btFoldRecombine b s bt
      (List.map (BT.fold b s)
        (btFoldChildren bt)) =
      some (BT.fold b s bt) := by
  match h : encodeBT bt with
  | 0 =>
    have hbt : bt = BT.leaf :=
      encodeBT_injective (by
        rw [h]
        simp only [encodeBT, BT.fold_leaf])
    subst hbt
    rw [btFoldChildren_leaf,
      btFoldRecombine_leaf]
    simp only [BT.fold_leaf]
  | n + 1 =>
    have hbt : bt = BT.node
        (decodeBT (Nat.unpair n).1)
        (decodeBT (Nat.unpair n).2) := by
      rw [← decodeBT_encodeBT bt, h]
      simp only [decodeBT]
    subst hbt
    rw [btFoldChildren_node,
      btFoldRecombine_node]
    simp only [BT.fold_node, List.map,
      List.getD_cons_zero,
      List.getD_cons_succ]

theorem bt_fold_primrec
    {b : BT.{0}}
    {s : BT.{0} → BT.{0} → BT.{0}}
    (hs : Primrec₂ s) :
    Primrec (BT.fold b s) :=
  Primrec.nat_omega_rec'
    (BT.fold b s)
    (m := Encodable.encode)
    (l := btFoldChildren)
    (g := btFoldRecombine b s)
    Primrec.encode
    btFoldChildren_primrec
    (btFoldRecombine_primrec₂ hs)
    (fun bt bt' hmem =>
      btFoldChildren_lt bt bt' hmem)
    (fun bt => btFoldFuncEq b s bt)

end GebLean
