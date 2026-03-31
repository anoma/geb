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

private theorem list_ofFn_getD {σ : Type}
    {n : ℕ} (f : Fin n → σ)
    (i : Fin n) (d : σ) :
    (List.ofFn f).getD i.val d = f i := by
  unfold List.getD
  rw [List.getElem?_ofFn]
  simp

theorem primrec_finArrow_ofComponents
    {γ σ : Type} [Primcodable γ]
    [Primcodable σ] [Inhabited σ]
    {n : ℕ} {f : Fin n → γ → σ}
    (hf : ∀ i, Primrec (f i)) :
    Primrec
      (fun a =>
        (fun i : Fin n => f i a)) := by
  rw [Primrec.fin_curry]
  unfold Primrec₂
  have heq :
      (fun p : γ × Fin n =>
        (fun a i => f i a) p.1 p.2) =
      (fun p : γ × Fin n =>
        (List.ofFn
          (fun i => f i p.1)).getD
          p.2.val default) := by
    funext ⟨a, i⟩
    exact (list_ofFn_getD
      (fun j => f j a) i default).symm
  rw [heq]
  exact (Primrec.list_getD default).comp
    ((Primrec.list_ofFn hf).comp
      Primrec.fst)
    (Primrec.encode.comp Primrec.snd)

theorem btNode_primrec₂ :
    Primrec₂
      (BT.node : BT.{0} → BT.{0} → BT.{0}) := by
  unfold Primrec₂
  have heq :
      (fun p : BT.{0} × BT.{0} =>
        BT.node p.1 p.2) =
      (fun p : BT.{0} × BT.{0} =>
        decodeBT (Nat.pair
          (encodeBT p.1)
          (encodeBT p.2) + 1)) := by
    funext ⟨l, r⟩
    simp [decodeBT, Nat.unpair_pair,
      decodeBT_encodeBT]
  rw [heq]
  exact decodeBT_primrec.comp
    (Primrec.succ.comp
      (Primrec₂.natPair.comp
        (Primrec.encode.comp Primrec.fst)
        (Primrec.encode.comp Primrec.snd)))

/-- Generalization of `bt_fold_primrec` that
allows the base to depend on an additional
parameter, and the tree to be computed from
that parameter.  Given `base : α → σ`,
`step : σ → σ → σ`, and `tree : α → BT`,
shows that `fun a => BT.fold (base a)
step (tree a)` is primitive recursive when all
components are. -/
private def btFoldParamChildren
    {α : Type} [Primcodable α]
    (p : α × BT.{0}) : List (α × BT.{0}) :=
  (btFoldChildren p.2).map (fun c => (p.1, c))

private def btFoldParamRecombine
    {α σ : Type} [Primcodable α] [Primcodable σ]
    [Inhabited σ]
    (base : α → σ)
    (step : σ → σ → σ)
    (p : α × BT.{0})
    (results : List σ) : Option σ :=
  @Nat.casesOn (fun _ => Option σ)
    (encodeBT p.2)
    (some (base p.1))
    (fun _ => some (step
      (results.getD 0 default)
      (results.getD 1 default)))

private theorem btFoldParamChildren_primrec
    {α : Type} [Primcodable α] :
    Primrec
      (btFoldParamChildren :
        α × BT.{0} → List (α × BT.{0})) := by
  unfold btFoldParamChildren
  exact Primrec.list_map
    (btFoldChildren_primrec.comp Primrec.snd)
    (Primrec₂.comp Primrec₂.pair
      (Primrec.fst.comp Primrec.fst)
      Primrec.snd)

private theorem btFoldParamRecombine_primrec₂
    {α σ : Type} [Primcodable α] [Primcodable σ]
    [Inhabited σ]
    {base : α → σ}
    {step : σ → σ → σ}
    (hbase : Primrec base)
    (hstep : Primrec₂ step) :
    Primrec₂
      (btFoldParamRecombine base step :
        α × BT.{0} → List σ → Option σ) := by
  unfold Primrec₂ btFoldParamRecombine
  apply Primrec.nat_casesOn
  · exact Primrec.encode.comp
      (Primrec.snd.comp Primrec.fst)
  · exact Primrec.option_some.comp
      (hbase.comp
        (Primrec.fst.comp Primrec.fst))
  · unfold Primrec₂
    exact Primrec.option_some.comp
      (hstep.comp
        ((Primrec.list_getD default).comp
          (Primrec.snd.comp Primrec.fst)
          (Primrec.const 0))
        ((Primrec.list_getD default).comp
          (Primrec.snd.comp Primrec.fst)
          (Primrec.const 1)))

private theorem btFoldParamChildren_lt
    {α : Type} [Primcodable α]
    (p p' : α × BT.{0})
    (hmem : p' ∈ btFoldParamChildren p) :
    encodeBT p'.2 < encodeBT p.2 := by
  unfold btFoldParamChildren at hmem
  rw [List.mem_map] at hmem
  obtain ⟨c, hc_mem, hc_eq⟩ := hmem
  rw [← hc_eq]
  exact btFoldChildren_lt p.2 c hc_mem

private theorem btFoldParamFuncEq
    {α σ : Type} [Primcodable α] [Primcodable σ]
    [Inhabited σ]
    (base : α → σ)
    (step : σ → σ → σ)
    (p : α × BT.{0}) :
    btFoldParamRecombine base step p
      (List.map
        (fun q : α × BT.{0} =>
          BT.fold (base q.1) step q.2)
        (btFoldParamChildren p)) =
      some (BT.fold (base p.1) step p.2) := by
  unfold btFoldParamRecombine btFoldParamChildren
  generalize hk : encodeBT p.2 = k
  match k with
  | 0 =>
    have hbt : p.2 = BT.leaf :=
      encodeBT_injective (by
        rw [hk]
        simp only [encodeBT, BT.fold_leaf])
    rw [hbt, btFoldChildren_leaf]
    simp only [BT.fold_leaf, List.map]
    rfl
  | n + 1 =>
    have hbt : p.2 = BT.node
        (decodeBT (Nat.unpair n).1)
        (decodeBT (Nat.unpair n).2) := by
      rw [← decodeBT_encodeBT p.2, hk]
      simp only [decodeBT]
    rw [hbt, btFoldChildren_node]
    simp only [BT.fold_node, List.map,
      List.getD_cons_zero,
      List.getD_cons_succ]

theorem bt_fold_primrec_param
    {α σ : Type} [Primcodable α] [Primcodable σ]
    [Inhabited σ]
    {base : α → σ}
    {step : σ → σ → σ}
    {tree : α → BT.{0}}
    (hbase : Primrec base)
    (hstep : Primrec₂ step)
    (htree : Primrec tree) :
    Primrec (fun a =>
      BT.fold (base a) step (tree a)) := by
  have hpair :
      Primrec (fun (p : α × BT.{0}) =>
        BT.fold (base p.1) step p.2) :=
    Primrec.nat_omega_rec'
      (fun (p : α × BT.{0}) =>
        BT.fold (base p.1) step p.2)
      (m := fun p => encodeBT p.2)
      (l := btFoldParamChildren)
      (g := btFoldParamRecombine base step)
      (Primrec.encode.comp Primrec.snd)
      btFoldParamChildren_primrec
      (btFoldParamRecombine_primrec₂
        hbase hstep)
      (fun p p' hmem =>
        btFoldParamChildren_lt p p' hmem)
      (fun p =>
        btFoldParamFuncEq base step p)
  exact hpair.comp
    (Primrec₂.pair.comp Primrec.id htree)

/-- Every `BTMor1 n` term computes a primitive
recursive function when the context is built
from a single input of any Primcodable type
by a family of primitive recursive functions. -/
theorem interpU_primrec_of_ctx
    {α : Type} [Primcodable α]
    {n : ℕ} (t : BTMor1 n)
    (mkCtx : α → Fin n → BT.{0})
    (hCtx : ∀ i : Fin n,
      Primrec (fun a => mkCtx a i)) :
    Primrec (fun a : α =>
      t.interpU (mkCtx a)) :=
  BTMor1.ind
    (motive := fun {k} (t : BTMor1 k) =>
      ∀ {α : Type} [Primcodable α]
        (mkCtx : α → Fin k → BT.{0}),
        (∀ i : Fin k,
          Primrec (fun a => mkCtx a i)) →
        Primrec (fun a : α =>
          t.interpU (mkCtx a)))
    (step := fun i => match i with
      | ⟨0, _⟩ =>
        fun p _ _ {α} [_] mkCtx hCtx => by
          rw [polyFixMk_eq_proj]
          simp only [BTMor1.interpU_proj]
          exact hCtx _
      | ⟨1, _⟩ =>
        fun p _ _ {α} [_] mkCtx hCtx => by
          rw [polyFixMk_eq_leaf]
          simp only [BTMor1.interpU_leaf]
          exact Primrec.const _
      | ⟨2, _⟩ =>
        fun p children ih
            {α} [_] mkCtx hCtx => by
          rw [polyFixMk_eq_branch]
          simp only [BTMor1.interpU_branch]
          exact btNode_primrec₂.comp
            (ih (Sum.inl PUnit.unit)
              mkCtx hCtx)
            (ih (Sum.inr PUnit.unit)
              mkCtx hCtx)
      | ⟨3, isLt3⟩ =>
        fun p children ih
            {α} [_] mkCtx hCtx => by
          rename_i ni _inst
          rw [polyFixMk_eq_fold]
          simp only [BTMor1.interpU_fold]
          let m := p.1
          have hlb (i : Fin m) :
              i.val < m + m + 1 :=
            Nat.lt_of_lt_of_le i.isLt
              (Nat.le_add_right m (m + 1))
          have hls (i : Fin m) :
              m + i.val < m + m + 1 :=
            by omega
          have hlt :
              m + m < m + m + 1 :=
            Nat.lt_succ_self _
          have hbf (i : Fin m) :
              (polyBetweenFamily ℕ ℕ
                (btMorComponents
                  ⟨3, by omega⟩)
                ni p).hom
                ⟨i.val, hlb i⟩ = ni := by
            unfold btMorComponents
              btMorFoldPoly
              polyBetweenFamily
              polyToOverFamily ccrObjMk
              ccrFamily; dsimp
            split_ifs <;> omega
          have hsf (i : Fin m) :
              (polyBetweenFamily ℕ ℕ
                (btMorComponents
                  ⟨3, by omega⟩)
                ni p).hom
                ⟨m + i.val, hls i⟩ =
                  m + m := by
            unfold btMorComponents
              btMorFoldPoly
              polyBetweenFamily
              polyToOverFamily ccrObjMk
              ccrFamily; dsimp
            split_ifs <;> omega
          have htf :
              (polyBetweenFamily ℕ ℕ
                (btMorComponents
                  ⟨3, by omega⟩)
                ni p).hom
                ⟨m + m, hlt⟩ = ni := by
            unfold btMorComponents
              btMorFoldPoly
              polyBetweenFamily
              polyToOverFamily ccrObjMk
              ccrFamily; dsimp
            split_ifs <;> omega
          -- IH on base children
          have ih_base (i : Fin m) :
              Primrec (fun a : α =>
                (foldBaseChild isLt3 p
                  children i).interpU
                  (mkCtx a)) := by
            have := ih ⟨i.val, hlb i⟩
              (fun a v =>
                mkCtx a (hbf i ▸ v))
              (fun v => hCtx (hbf i ▸ v))
            have heq :
                (fun a : α =>
                  (foldBaseChild isLt3 p
                    children i).interpU
                    (mkCtx a)) =
                (fun a => (children
                  ⟨i.val, hlb i⟩).interpU
                  (fun v =>
                    mkCtx a
                      (hbf i ▸ v))) := by
              funext a
              unfold foldBaseChild
              exact BTMor1.interpU_cast
                (hbf i) _ _
            rw [heq]; exact this
          -- IH on tree child
          have ih_tree :
              Primrec (fun a : α =>
                (foldTreeChild isLt3 p
                  children).interpU
                  (mkCtx a)) := by
            have := ih ⟨m + m, hlt⟩
              (fun a v =>
                mkCtx a (htf ▸ v))
              (fun v => hCtx (htf ▸ v))
            have heq :
                (fun a : α =>
                  (foldTreeChild isLt3 p
                    children).interpU
                    (mkCtx a)) =
                (fun a => (children
                  ⟨m + m, hlt⟩).interpU
                  (fun v =>
                    mkCtx a
                      (htf ▸ v))) := by
              funext a
              unfold foldTreeChild
              exact BTMor1.interpU_cast
                htf _ _
            rw [heq]; exact this
          -- IH on step children
          have ih_step (j' : Fin m)
              {β : Type} [Primcodable β]
              (mkCtx' : β →
                Fin (m + m) → BT.{0})
              (hCtx' : ∀ idx,
                Primrec
                  (fun b => mkCtx' b idx))
              : Primrec (fun b : β =>
                (foldStepChild isLt3 p
                  children j').interpU
                  (mkCtx' b)) := by
            have := ih
              ⟨m + j'.val, hls j'⟩
              (fun b v =>
                mkCtx' b (hsf j' ▸ v))
              (fun v =>
                hCtx' (hsf j' ▸ v))
            have heq :
                (fun b : β =>
                  (foldStepChild isLt3 p
                    children j').interpU
                    (mkCtx' b)) =
                (fun b => (children
                  ⟨m + j'.val,
                    hls j'⟩).interpU
                  (fun v =>
                    mkCtx' b
                      (hsf j' ▸ v))) := by
              funext b
              unfold foldStepChild
              exact BTMor1.interpU_cast
                (hsf j') _ _
            rw [heq]; exact this
          -- Assemble base
          have : Inhabited BT.{0} :=
            ⟨BT.leaf⟩
          have hbase :
              Primrec (fun a : α =>
                (fun i : Fin m =>
                  (foldBaseChild isLt3 p
                    children i).interpU
                    (mkCtx a))) :=
            primrec_finArrow_ofComponents
              ih_base
          -- Assemble step as Primrec₂
          have hstep_pr :
              Primrec (fun pair :
                (Fin m → BT.{0}) ×
                (Fin m → BT.{0}) =>
                (fun j' : Fin m =>
                  (foldStepChild isLt3 p
                    children j').interpU
                    (finAppend
                      pair.1 pair.2))) :=
            primrec_finArrow_ofComponents
              (fun j' => ih_step j'
                (fun (pair :
                  (Fin m → BT.{0}) ×
                  (Fin m → BT.{0}))
                  idx =>
                  finAppend pair.1
                    pair.2 idx)
                (fun idx => by
                  simp only [finAppend]
                  split
                  · exact Primrec₂.comp
                      (f := @id
                        (Fin m → BT.{0}))
                      Primrec.fin_app
                      (Primrec.fst
                        (β :=
                          Fin m → BT.{0}))
                      (Primrec.const _)
                  · exact Primrec₂.comp
                      (f := @id
                        (Fin m → BT.{0}))
                      Primrec.fin_app
                      (Primrec.snd
                        (α :=
                          Fin m → BT.{0}))
                      (Primrec.const _)))
          have hstep₂ : Primrec₂
              (fun (l r :
                Fin m → BT.{0})
                (j' : Fin m) =>
                (foldStepChild isLt3 p
                  children j').interpU
                  (finAppend l r)) := by
            change Primrec
              (fun (pair :
                (Fin m → BT.{0}) ×
                (Fin m → BT.{0})) =>
                (fun (j' : Fin m) =>
                  (foldStepChild isLt3 p
                    children j').interpU
                    (finAppend
                      pair.1 pair.2)))
            exact hstep_pr
          -- Apply bt_fold_primrec_param
          have hfold :
              Primrec (fun a : α =>
                BT.fold
                  (fun i =>
                    (foldBaseChild isLt3 p
                      children i).interpU
                      (mkCtx a))
                  (fun l r j' =>
                    (foldStepChild isLt3 p
                      children j').interpU
                      (finAppend l r))
                  ((foldTreeChild isLt3 p
                    children).interpU
                    (mkCtx a))) :=
            bt_fold_primrec_param
              hbase hstep₂ ih_tree
          -- Project at p.snd
          exact Primrec₂.comp
            Primrec.fin_app hfold
            (Primrec.const p.snd))
    t mkCtx hCtx

/-- Every `BTMor1 1` term computes a primitive
recursive function `BT → BT`. -/
theorem interpU_unary_primrec
    (t : BTMor1 1) :
    Primrec (fun bt : BT.{0} =>
      t.interpU (fun _ => bt)) :=
  interpU_primrec_of_ctx t
    (fun bt _ => bt)
    (fun _ => Primrec.id)

/-- The Ackermann function transported to
binary trees via the Goedel encoding. -/
def ackOnBT : BT.{0} → BT.{0} :=
  fun bt => decodeBT
    (ack (encodeBT bt) (encodeBT bt))

theorem ackOnBT_not_primrec :
    ¬ Primrec ackOnBT := by
  intro h
  have heq : (fun n : Nat => ack n n) =
      (fun n => encodeBT
        (ackOnBT (decodeBT n))) := by
    funext n
    simp only [ackOnBT, encodeBT_decodeBT]
  have : Primrec (fun n : Nat =>
      ack n n) := by
    rw [heq]
    exact Primrec.encode.comp
      (h.comp decodeBT_primrec)
  exact not_nat_primrec_ack_self
    (Primrec.nat_iff.mp this)

/-- The interpretation functor from the Lawvere
theory of parameterized binary tree objects into
`Type` is not full.  The Ackermann function
(transported to binary trees) is a computable
function `BT -> BT` that is not in the image of
any morphism in the Lawvere theory, since
all such morphisms compute primitive recursive
functions. -/
theorem interpFunctor_not_full :
    ¬ interpFunctor.{0}.Full := by
  intro hfull
  have hsurj := Functor.map_surjective
    (F := interpFunctor.{0}) (X := (1 : ℕ))
    (Y := (1 : ℕ))
  have hmor := hsurj
    (fun (ctx : Fin 1 → BT.{0}) =>
      (fun (_ : Fin 1) =>
        ackOnBT (ctx 0)))
  obtain ⟨f, hf⟩ := hmor
  have hprim : Primrec ackOnBT := by
    obtain ⟨f_raw, hfr⟩ :=
      Quotient.exists_rep
        (s := btMorNSetoid 1 1) f
    have hinterp : ∀ (ctx : Fin 1 → BT.{0}),
        BTMorN.interpU f_raw ctx =
        (fun (_ : Fin 1) =>
          ackOnBT (ctx 0)) := by
      intro ctx
      have hmap : interpFunctor.{0}.map f =
          BTMorNQuo.interpU f := rfl
      rw [hmap] at hf
      rw [← hfr] at hf
      have := congrFun hf ctx
      simp only [BTMorNQuo.interpU,
        Quotient.lift_mk] at this
      exact this
    have hcomp :
        (fun bt : BT.{0} =>
          (f_raw ⟨0, by omega⟩).interpU
            (fun _ => bt)) =
        ackOnBT := by
      funext bt
      have h0 := congrFun
        (hinterp (fun _ => bt))
        ⟨0, by omega⟩
      simp only [BTMorN.interpU] at h0
      exact h0
    rw [← hcomp]
    exact interpU_unary_primrec
      (f_raw ⟨0, by omega⟩)
  exact ackOnBT_not_primrec hprim

end GebLean
