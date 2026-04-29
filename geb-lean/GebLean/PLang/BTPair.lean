import GebLean.PLang.Syntax
import GebLean.LawvereBT
import GebLean.LawvereBTInterp
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Encodable.Basic

/-!
# Bijection between Finite-Alphabet Binary Trees and ℕ

For each `n : ℕ`, a bijection `BTα (Fin (n+1)) ≃ ℕ` via the
"tree of finite alphabet" pairing function (Wikipedia,
"Restriction to natural numbers"); composition through ℕ gives
alphabet-shift bijections; specializing at `m = 0` plus
`Fin 1 ≃ PUnit` gives `BTα (Fin (n+1)) ≃ BT.{0}`.  Includes the
perfect-tree generator and the depth-ordering biconditional.

Relocates `encodeBT`/`decodeBT`/`Encodable BT.{0}` from
`LawvereBTPrimrec.lean` and recovers them as `n = 0` aliases.
-/

namespace GebLean

open CategoryTheory

universe u

/-- The `Over PUnit` carrier for `BTα α`: the constant fibration
`α → PUnit`. -/
def BTα.carrier (α : Type u) : Over PUnit.{u + 1} :=
  Over.mk (fun _ : α => PUnit.unit)

@[simp] theorem BTα.carrier_hom {α : Type u} (a : α) :
    (BTα.carrier α).hom a = PUnit.unit := rfl

/-- Labeled binary trees with leaf labels in `α`, as the free
monad of `polyProdType` at the `α`-fibered carrier.

`BTα PUnit` and the existing `BT` (defined in
`GebLean.LawvereBT`) share the same host `PolyFreeM
… polyProdType PUnit.unit` but differ in their `Over PUnit`
carriers: `Over.mk (fun _ : PUnit => PUnit.unit)` versus
`Over.mk (@id PUnit)`.  These carriers are propositionally
but not definitionally equal; an equivalence
`equivBTαPUnitBT : BTα PUnit ≃ BT.{0}` is constructed in a
later section. -/
abbrev BTα (α : Type u) : Type u :=
  PolyFreeM (BTα.carrier α) polyProdType PUnit.unit

/-- Leaf with label `a : α` (the unit of the free monad,
generalized from the unit-labeled `BT.leaf` to a labeled
alphabet).  Constructed via `polyFreeMPure`. -/
def BTα.leaf {α : Type u} (a : α) : BTα α :=
  polyFreeMPure (BTα.carrier α) polyProdType ⟨a, rfl⟩

/-- Branching node from two subtrees (the binary operation of
the BTO at the `α`-fibered carrier, parametric analogue of
`BT.node`).  Constructed via `polyProdFreeMNode`. -/
def BTα.node {α : Type u} (l r : BTα α) : BTα α :=
  polyProdFreeMNode (BTα.carrier α) l r

/-- Catamorphism: fold a `BTα α` to `β` given a leaf and node
action.  Built on `polyProdFreeMFoldAt`. -/
def BTα.fold {α β : Type u}
    (onLeaf : α → β) (onNode : β → β → β) (t : BTα α) : β :=
  polyProdFreeMFoldAt (BTα.carrier α)
    (onLeaf := fun {_ : PUnit.{u + 1}} v => onLeaf v.val)
    (onNode := onNode) t

/-- `BTα.fold` at a leaf returns the leaf action applied to the
label. -/
@[simp] theorem BTα.fold_leaf {α β : Type u}
    (onLeaf : α → β) (onNode : β → β → β) (a : α) :
    BTα.fold onLeaf onNode (BTα.leaf a) = onLeaf a := by
  unfold BTα.fold BTα.leaf
    polyProdFreeMFoldAt
    polyFreeMapAt
  simp only [polyFreeM_pure_bind]
  unfold polyFreeMPure polyFreeCounitFoldAt
  rfl

/-- `BTα.fold` at a node applies the node action to the two
recursive fold results. -/
@[simp] theorem BTα.fold_node {α β : Type u}
    (onLeaf : α → β) (onNode : β → β → β) (l r : BTα α) :
    BTα.fold onLeaf onNode (BTα.node l r) =
      onNode (BTα.fold onLeaf onNode l)
        (BTα.fold onLeaf onNode r) := by
  rfl

/-- Every `BTα α` tree is either a leaf or a node. -/
theorem BTα.leaf_or_node {α : Type u} (t : BTα α) :
    (∃ a : α, t = BTα.leaf a) ∨
    (∃ l r : BTα α, t = BTα.node l r) := by
  match t with
  | PolyFix.mk y idx children =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      left
      refine ⟨leafIdx.val, ?_⟩
      unfold BTα.leaf polyFreeMPure
      congr 1
      funext e
      exact PEmpty.elim e
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      right
      exact ⟨children (Sum.inl PUnit.unit),
        children (Sum.inr PUnit.unit), by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        ext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl⟩

/-- Encode a `BTα (Fin (n+1))` tree as a natural number.

Leaves with label `i : Fin (n+1)` use codes `0, …, n`; nodes
shift by `n+1` and `Nat.pair` the recursive encodings. -/
def encodeBTn (n : ℕ) (t : BTα.{0} (Fin (n + 1))) : ℕ :=
  BTα.fold (fun i : Fin (n + 1) => i.val)
    (fun el er => (n + 1) + Nat.pair el er) t

@[simp] theorem encodeBTn_leaf (n : ℕ) (i : Fin (n + 1)) :
    encodeBTn n (BTα.leaf i) = i.val := by
  simp [encodeBTn]

@[simp] theorem encodeBTn_node (n : ℕ)
    (l r : BTα.{0} (Fin (n + 1))) :
    encodeBTn n (BTα.node l r) =
      (n + 1) + Nat.pair (encodeBTn n l) (encodeBTn n r) := by
  simp [encodeBTn]

/-- Decode a natural number to a `BTα (Fin (n+1))` tree.
Numbers `< n+1` decode to leaves; the rest decode by
`Nat.unpair`-ing the residue after subtracting `n+1`. -/
def decodeBTn (n : ℕ) : ℕ → BTα.{0} (Fin (n + 1))
  | k =>
    if h : k < n + 1 then
      BTα.leaf ⟨k, h⟩
    else
      let r := k - (n + 1)
      BTα.node
        (decodeBTn n (Nat.unpair r).1)
        (decodeBTn n (Nat.unpair r).2)
  termination_by k => k
  decreasing_by
    all_goals
      have hlt : k - (n + 1) < k := by omega
      first
        | exact Nat.lt_of_le_of_lt
            (Nat.unpair_left_le _) hlt
        | exact Nat.lt_of_le_of_lt
            (Nat.unpair_right_le _) hlt

@[simp] theorem decodeBTn_lt (n k : ℕ) (h : k < n + 1) :
    decodeBTn n k = BTα.leaf ⟨k, h⟩ := by
  unfold decodeBTn
  simp [h]

@[simp] theorem decodeBTn_ge (n k : ℕ) (h : ¬ k < n + 1) :
    decodeBTn n k =
      BTα.node
        (decodeBTn n (Nat.unpair (k - (n + 1))).1)
        (decodeBTn n (Nat.unpair (k - (n + 1))).2) := by
  conv_lhs => rw [decodeBTn]
  simp [h]

private theorem decodeBTn_encodeBTn_gen
    (n : ℕ) {x : PUnit.{1}}
    (t : PolyFreeM (BTα.carrier (Fin (n + 1)))
      polyProdType x) :
    decodeBTn n (encodeBTn n t) = t := by
  induction t with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (BTα.carrier (Fin (n + 1)))
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf leafIdx.val := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hleaf]
      change decodeBTn n (encodeBTn n
          (BTα.leaf (leafIdx.val : Fin (n + 1)))) =
        BTα.leaf (leafIdx.val : Fin (n + 1))
      rw [encodeBTn_leaf,
        decodeBTn_lt _ _ leafIdx.val.isLt]
      congr 1
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (BTα.carrier (Fin (n + 1)))
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BTα.node
            (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode, encodeBTn_node]
      have hge :
          ¬ ((n + 1) +
            Nat.pair
              (encodeBTn n
                (children (Sum.inl PUnit.unit)))
              (encodeBTn n
                (children (Sum.inr PUnit.unit)))) <
          n + 1 := by omega
      rw [decodeBTn_ge _ _ hge]
      have hsub :
          (n + 1) +
            Nat.pair
              (encodeBTn n
                (children (Sum.inl PUnit.unit)))
              (encodeBTn n
                (children (Sum.inr PUnit.unit))) -
          (n + 1) =
          Nat.pair
            (encodeBTn n
              (children (Sum.inl PUnit.unit)))
            (encodeBTn n
              (children (Sum.inr PUnit.unit))) := by
        omega
      rw [hsub, Nat.unpair_pair]
      rw [ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]

/-- Decoding inverts encoding on every `BTα (Fin (n+1))` tree. -/
theorem decodeBTn_encodeBTn (n : ℕ)
    (t : BTα.{0} (Fin (n + 1))) :
    decodeBTn n (encodeBTn n t) = t :=
  decodeBTn_encodeBTn_gen n t

/-- Encoding inverts decoding on every natural number. -/
theorem encodeBTn_decodeBTn (n : ℕ) (k : ℕ) :
    encodeBTn n (decodeBTn n k) = k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
      by_cases h : k < n + 1
      · rw [decodeBTn_lt n k h]
        rw [encodeBTn_leaf]
      · rw [decodeBTn_ge n k h]
        rw [encodeBTn_node]
        set r := k - (n + 1) with hr
        have hlt : r < k := by omega
        have ihl := ih (Nat.unpair r).1
          (Nat.lt_of_le_of_lt
            (Nat.unpair_left_le _) hlt)
        have ihr := ih (Nat.unpair r).2
          (Nat.lt_of_le_of_lt
            (Nat.unpair_right_le _) hlt)
        rw [ihl, ihr]
        rw [Nat.pair_unpair]
        omega

/-- The bijection `BTα (Fin (n+1)) ≃ ℕ`.  For `n = 0` this is the
existing `encodeBT`/`decodeBT` bijection; for general `n` it
encodes labeled binary trees over a finite alphabet. -/
def equivBTnNat (n : ℕ) : BTα.{0} (Fin (n + 1)) ≃ ℕ where
  toFun     := encodeBTn n
  invFun    := decodeBTn n
  left_inv  := decodeBTn_encodeBTn n
  right_inv := encodeBTn_decodeBTn n

/-- Bijection between trees over two finite alphabets, factored
through `ℕ`. -/
def equivBTnBTm (n m : ℕ) :
    BTα.{0} (Fin (n + 1)) ≃ BTα.{0} (Fin (m + 1)) :=
  (equivBTnNat n).trans (equivBTnNat m).symm

/-- Specialization at `m = 0`: trees over `Fin (n+1)` are in
bijection with trees over `Fin 1`. -/
def equivBTnBT1 (n : ℕ) :
    BTα.{0} (Fin (n + 1)) ≃ BTα.{0} (Fin 1) :=
  equivBTnBTm n 0

private theorem BTα.equivOfEquiv_left_inv_gen
    {α β : Type u} (e : α ≃ β) {x : PUnit.{u + 1}}
    (t : PolyFreeM (BTα.carrier α) polyProdType x) :
    BTα.fold (fun b => BTα.leaf (e.symm b)) BTα.node
      (BTα.fold (fun a => BTα.leaf (e a)) BTα.node t) =
    t := by
  induction t with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      let a : α := leafIdx.val
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier α)
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf a := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hleaf, BTα.fold_leaf, BTα.fold_leaf,
        Equiv.symm_apply_apply]
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier α)
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BTα.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode]
      simp only [BTα.fold_node,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]

private theorem BTα.equivOfEquiv_right_inv_gen
    {α β : Type u} (e : α ≃ β) {x : PUnit.{u + 1}}
    (t : PolyFreeM (BTα.carrier β) polyProdType x) :
    BTα.fold (fun a => BTα.leaf (e a)) BTα.node
      (BTα.fold (fun b => BTα.leaf (e.symm b)) BTα.node t) =
    t := by
  induction t with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      let b : β := leafIdx.val
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier β)
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf b := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hleaf, BTα.fold_leaf, BTα.fold_leaf,
        Equiv.apply_symm_apply]
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier β)
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BTα.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode]
      simp [BTα.fold_node,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]

/-- Functorial action of `BTα` on type equivalences: any
equivalence between alphabets `α ≃ β` lifts to an equivalence
`BTα α ≃ BTα β` by relabeling leaves. -/
def BTα.equivOfEquiv {α β : Type u} (e : α ≃ β) :
    BTα α ≃ BTα β where
  toFun :=
    BTα.fold (fun a => BTα.leaf (e a)) BTα.node
  invFun :=
    BTα.fold (fun b => BTα.leaf (e.symm b)) BTα.node
  left_inv := fun t =>
    BTα.equivOfEquiv_left_inv_gen e t
  right_inv := fun t =>
    BTα.equivOfEquiv_right_inv_gen e t

private theorem equivBTαPUnitBT_left_inv_gen
    {x : PUnit.{1}}
    (t : PolyFreeM (BTα.carrier PUnit)
      polyProdType x) :
    BT.fold (BTα.leaf PUnit.unit) BTα.node
      (BTα.fold (fun _ => BT.leaf) BT.node t) =
    t := by
  induction t with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      let a : PUnit := PUnit.unit
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier PUnit)
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf a := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hleaf, BTα.fold_leaf, BT.fold_leaf]
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier PUnit)
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BTα.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode]
      simp [BTα.fold_node, BT.fold_node,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]

private theorem equivBTαPUnitBT_right_inv_gen
    {x : PUnit.{1}}
    (t : PolyFreeM (overTerminal PUnit.{1})
      polyProdType x) :
    BTα.fold (fun _ => BT.leaf) BT.node
      (BT.fold (BTα.leaf PUnit.unit) BTα.node t) =
    t := by
  induction t with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hleaf]
      simp [BT.fold_leaf, BTα.fold_leaf]
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode]
      simp [BT.fold_node, BTα.fold_node,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]

/-- The bridge `BTα PUnit ≃ BT.{0}`.  Both sides are free monads
of `polyProdType` at `PUnit.unit`, but `BTα.carrier PUnit` and
`overTerminal PUnit` differ propositionally (PUnit η).  We fold
through `BT.leaf`/`BT.node` and `BTα.leaf PUnit.unit`/`BTα.node`
in either direction. -/
def equivBTαPUnitBT : BTα.{0} PUnit ≃ BT.{0} where
  toFun  := BTα.fold (fun _ => BT.leaf) BT.node
  invFun := BT.fold (BTα.leaf PUnit.unit) BTα.node
  left_inv := fun t =>
    equivBTαPUnitBT_left_inv_gen t
  right_inv := fun t =>
    equivBTαPUnitBT_right_inv_gen t

/-- Bijection between `BTα (Fin (n+1))` and the unlabeled `BT.{0}`.
Composes the alphabet shift `Fin (n+1) → Fin 1`, the relabeling
`Fin 1 ≃ PUnit`, and the carrier bridge. -/
def equivBTnBT (n : ℕ) : BTα.{0} (Fin (n + 1)) ≃ BT.{0} :=
  ((equivBTnBT1 n).trans
    (BTα.equivOfEquiv (Equiv.equivPUnit (Fin 1)))).trans
      equivBTαPUnitBT

/-! ## Recovery of the existing unlabeled-tree API

These names were originally in `LawvereBTPrimrec.lean`; they are
relocated here as the `n = 0` case of the labeled API.
Definitions and proofs are textually unchanged. -/

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

/-! ## Connecting lemmas: unlabeled `encodeBT`/`decodeBT` agree
with `encodeBTn 0` / `decodeBTn 0` modulo the bridge `equivBTnBT 0`. -/

private theorem encodeBT_equivBTαPUnitBT_gen
    {x : PUnit.{1}}
    (u : PolyFreeM (BTα.carrier PUnit)
      polyProdType x) :
    encodeBT (BTα.fold (fun _ : PUnit => BT.leaf)
        BT.node u) =
      BTα.fold (fun _ : PUnit => 0)
        (fun el er => Nat.pair el er + 1) u := by
  induction u with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier PUnit)
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf leafIdx.val := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hleaf]
      change encodeBT BT.leaf = (0 : ℕ)
      rfl
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier PUnit)
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BTα.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode]
      have ihL := ih (Sum.inl PUnit.unit)
      have ihR := ih (Sum.inr PUnit.unit)
      change encodeBT (BT.node
          (BTα.fold (fun _ : PUnit => BT.leaf) BT.node
            (children (Sum.inl PUnit.unit)))
          (BTα.fold (fun _ : PUnit => BT.leaf) BT.node
            (children (Sum.inr PUnit.unit)))) =
        Nat.pair
          (BTα.fold (fun _ : PUnit => 0)
            (fun el er => Nat.pair el er + 1)
            (children (Sum.inl PUnit.unit)))
          (BTα.fold (fun _ : PUnit => 0)
            (fun el er => Nat.pair el er + 1)
            (children (Sum.inr PUnit.unit))) + 1
      change Nat.pair
          (encodeBT (BTα.fold (fun _ : PUnit => BT.leaf)
            BT.node (children (Sum.inl PUnit.unit))))
          (encodeBT (BTα.fold (fun _ : PUnit => BT.leaf)
            BT.node (children (Sum.inr PUnit.unit)))) +
          1 = _
      rw [ihL, ihR]

private theorem encodeBT_equivOfEquiv_gen
    {α : Type} (e : α ≃ PUnit) {x : PUnit.{1}}
    (u : PolyFreeM (BTα.carrier α) polyProdType x) :
    BTα.fold (fun _ : PUnit => 0)
        (fun el er => Nat.pair el er + 1)
        (BTα.fold
          (fun a => BTα.leaf (e a)) BTα.node u) =
      BTα.fold (fun _ : α => 0)
        (fun el er => Nat.pair el er + 1) u := by
  induction u with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier α)
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf leafIdx.val := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e'
        exact PEmpty.elim e'
      rw [hleaf]
      rfl
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier α)
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BTα.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e'
        match e' with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode]
      change Nat.pair
          (BTα.fold (fun _ : PUnit => 0)
            (fun el er => Nat.pair el er + 1)
            (BTα.fold (fun a => BTα.leaf (e a)) BTα.node
              (children (Sum.inl PUnit.unit))))
          (BTα.fold (fun _ : PUnit => 0)
            (fun el er => Nat.pair el er + 1)
            (BTα.fold (fun a => BTα.leaf (e a)) BTα.node
              (children (Sum.inr PUnit.unit)))) + 1 =
        Nat.pair
          (BTα.fold (fun _ : α => 0)
            (fun el er => Nat.pair el er + 1)
            (children (Sum.inl PUnit.unit)))
          (BTα.fold (fun _ : α => 0)
            (fun el er => Nat.pair el er + 1)
            (children (Sum.inr PUnit.unit))) + 1
      rw [ih (Sum.inl PUnit.unit), ih (Sum.inr PUnit.unit)]

/-- The fold computation appearing in `encodeBT ∘ equivBTαPUnitBT
∘ BTα.equivOfEquiv` over `BTα (Fin 1)` matches `encodeBTn 0`. -/
private theorem fold_eq_encodeBTn_zero
    {x : PUnit.{1}}
    (u : PolyFreeM (BTα.carrier (Fin 1))
      polyProdType x) :
    BTα.fold (fun _ : Fin 1 => 0)
        (fun el er => Nat.pair el er + 1) u =
      encodeBTn 0 u := by
  induction u with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier (Fin 1))
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf leafIdx.val := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e'
        exact PEmpty.elim e'
      rw [hleaf]
      change BTα.fold (fun _ : Fin 1 => 0)
          (fun el er => Nat.pair el er + 1)
          (BTα.leaf (leafIdx.val : Fin 1)) =
        encodeBTn 0 (BTα.leaf (leafIdx.val : Fin 1))
      rw [BTα.fold_leaf, encodeBTn_leaf]
      have hi : (leafIdx.val : Fin 1) = ⟨0, by omega⟩ := by
        apply Fin.eq_of_val_eq
        have := (leafIdx.val : Fin 1).isLt
        simp
      rw [hi]
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hnode :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier (Fin 1))
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BTα.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BTα.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e'
        match e' with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hnode]
      change Nat.pair (BTα.fold (fun _ : Fin 1 => 0)
          (fun el er => Nat.pair el er + 1)
          (children (Sum.inl PUnit.unit)))
        (BTα.fold (fun _ : Fin 1 => 0)
          (fun el er => Nat.pair el er + 1)
          (children (Sum.inr PUnit.unit))) + 1 =
        encodeBTn 0 (BTα.node
          (children (Sum.inl PUnit.unit))
          (children (Sum.inr PUnit.unit)))
      rw [encodeBTn_node]
      rw [ih (Sum.inl PUnit.unit), ih (Sum.inr PUnit.unit)]
      omega

/-- The forward direction `equivBTnBT n` sends a labeled tree to its
unlabeled image: at any `n`, encoding the unlabeled image equals the
generic encoding `encodeBTn n`. -/
private lemma encodeBT_equivBTnBT (n : ℕ)
    (s : BTα.{0} (Fin (n + 1))) :
    encodeBT (equivBTnBT n s) = encodeBTn n s := by
  unfold equivBTnBT
  change encodeBT
      (BTα.fold (fun _ : PUnit => BT.leaf) BT.node
        (BTα.fold
          (fun a : Fin 1 =>
            BTα.leaf (Equiv.equivPUnit (Fin 1) a))
          BTα.node
          (equivBTnBT1 n s))) = encodeBTn n s
  rw [encodeBT_equivBTαPUnitBT_gen]
  rw [encodeBT_equivOfEquiv_gen]
  rw [fold_eq_encodeBTn_zero (equivBTnBT1 n s)]
  unfold equivBTnBT1 equivBTnBTm
  change (equivBTnNat 0)
      ((equivBTnNat 0).symm ((equivBTnNat n) s)) =
        encodeBTn n s
  rw [Equiv.apply_symm_apply]
  rfl

/-- The unlabeled `encodeBT` agrees with `encodeBTn 0` after the
bridge `BTα (Fin 1) ↔ BT.{0}`. -/
theorem encodeBT_eq_encodeBTn_zero (t : BT.{0}) :
    encodeBT t = encodeBTn 0 ((equivBTnBT 0).symm t) := by
  have := encodeBT_equivBTnBT 0 ((equivBTnBT 0).symm t)
  rw [Equiv.apply_symm_apply] at this
  exact this

/-- The unlabeled `decodeBT` agrees with `decodeBTn 0` after the
bridge in the opposite direction. -/
theorem decodeBT_eq_decodeBTn_zero (k : ℕ) :
    decodeBT k = (equivBTnBT 0) (decodeBTn 0 k) := by
  have h1 :
      encodeBT (equivBTnBT 0 (decodeBTn 0 k)) = k := by
    rw [encodeBT_equivBTnBT 0 (decodeBTn 0 k)]
    exact encodeBTn_decodeBTn 0 k
  have h2 :
      decodeBT (encodeBT
        (equivBTnBT 0 (decodeBTn 0 k))) =
        equivBTnBT 0 (decodeBTn 0 k) :=
    decodeBT_encodeBT _
  rw [h1] at h2
  exact h2

end GebLean
