import GebLean.PLang.Syntax
import GebLean.LawvereBT
import Mathlib.Data.Nat.Pairing

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

end GebLean
