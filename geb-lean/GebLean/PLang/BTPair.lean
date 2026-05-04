import GebLean.PLang.Syntax
import GebLean.LawvereBT
import GebLean.LawvereBTInterp
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.Ring

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

/-! ## Decidable equality on `BTα α`

A structurally-recursive instance lifting `DecidableEq α` to
`DecidableEq (BTα α)`.  The recursion is over the `PolyFix` carrier
of `BTα`; constructor injectivity and disjointness are established
by examining the underlying `PolyFix.mk` representation. -/

/-- Decompose a `BTα α` tree as either a leaf or a node, returning
the corresponding label or pair of subtrees.  This is a one-step
destructor that does not recurse into subtrees. -/
private def BTα.dest {α : Type u} (t : BTα α) :
    α ⊕ (BTα α × BTα α) :=
  match t with
  | PolyFix.mk _ (Sum.inl leafIdx) _ => Sum.inl leafIdx.val
  | PolyFix.mk _ (Sum.inr _) children =>
      Sum.inr ⟨children (Sum.inl PUnit.unit),
        children (Sum.inr PUnit.unit)⟩

@[simp] private theorem BTα.dest_leaf {α : Type u} (a : α) :
    BTα.dest (BTα.leaf a) = Sum.inl a := by
  unfold BTα.dest BTα.leaf polyFreeMPure
  rfl

@[simp] private theorem BTα.dest_node {α : Type u}
    (l r : BTα α) :
    BTα.dest (BTα.node l r) = Sum.inr ⟨l, r⟩ := by
  unfold BTα.dest BTα.node polyProdFreeMNode
    polyFreeMStrFamily
  rfl

private theorem BTα.leaf_injective {α : Type u}
    {a₁ a₂ : α} (h : BTα.leaf a₁ = BTα.leaf a₂) :
    a₁ = a₂ := by
  have comm : BTα.dest (BTα.leaf a₁) = BTα.dest (BTα.leaf a₂) := by
    rw [h]
  rw [BTα.dest_leaf, BTα.dest_leaf] at comm
  exact Sum.inl.inj comm

private theorem BTα.leaf_ne_node {α : Type u}
    (a : α) (l r : BTα α) :
    BTα.leaf a ≠ BTα.node l r := by
  intro h
  have comm : BTα.dest (BTα.leaf a) = BTα.dest (BTα.node l r) := by
    rw [h]
  rw [BTα.dest_leaf, BTα.dest_node] at comm
  exact (Sum.inl_ne_inr comm).elim

private theorem BTα.node_injective {α : Type u}
    {l₁ r₁ l₂ r₂ : BTα α}
    (h : BTα.node l₁ r₁ = BTα.node l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have comm :
      BTα.dest (BTα.node l₁ r₁) = BTα.dest (BTα.node l₂ r₂) := by
    rw [h]
  rw [BTα.dest_node, BTα.dest_node] at comm
  exact ⟨congrArg (·.1) (Sum.inr.inj comm),
    congrArg (·.2) (Sum.inr.inj comm)⟩

/-- Reconstruct `t` from its `dest`-image: every `BTα α` tree
equals `BTα.leaf a` or `BTα.node l r` according to `dest t`. -/
private theorem BTα.eq_of_dest_leaf {α : Type u}
    (t : BTα α) (a : α) (h : BTα.dest t = Sum.inl a) :
    t = BTα.leaf a := by
  match t with
  | PolyFix.mk y idx children =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have h' : (Sum.inl leafIdx.val : α ⊕ (BTα α × BTα α)) =
          Sum.inl a := h
      have hval : leafIdx.val = a := Sum.inl.inj h'
      unfold BTα.leaf polyFreeMPure
      congr 1
      · subst hval; rfl
      · funext e; exact PEmpty.elim e
    | Sum.inr nodeIdx =>
      have h' :
          (Sum.inr (children (Sum.inl PUnit.unit),
            children (Sum.inr PUnit.unit)) :
            α ⊕ (BTα α × BTα α)) = Sum.inl a := h
      exact (Sum.inr_ne_inl h').elim

private theorem BTα.eq_of_dest_node {α : Type u}
    (t : BTα α) (l r : BTα α)
    (h : BTα.dest t = Sum.inr ⟨l, r⟩) :
    t = BTα.node l r := by
  match t with
  | PolyFix.mk y idx children =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have h' : (Sum.inl leafIdx.val : α ⊕ (BTα α × BTα α)) =
          Sum.inr (l, r) := h
      exact (Sum.inl_ne_inr h').elim
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have h' :
          (Sum.inr (children (Sum.inl PUnit.unit),
            children (Sum.inr PUnit.unit)) :
            α ⊕ (BTα α × BTα α)) = Sum.inr (l, r) := h
      have hpair :
          (children (Sum.inl PUnit.unit),
            children (Sum.inr PUnit.unit)) = (l, r) :=
        Sum.inr.inj h'
      have hl : children (Sum.inl PUnit.unit) = l :=
        congrArg Prod.fst hpair
      have hr : children (Sum.inr PUnit.unit) = r :=
        congrArg Prod.snd hpair
      unfold BTα.node polyProdFreeMNode polyFreeMStrFamily
      congr 1
      funext e
      match e with
      | Sum.inl _ =>
        change children (Sum.inl PUnit.unit) = l
        exact hl
      | Sum.inr _ =>
        change children (Sum.inr PUnit.unit) = r
        exact hr

/-- Structural induction principle for `BTα α`, factored over
the underlying `PolyFix` carrier and packaged as a leaf/node
case-dispatch.  The `_gen` form keeps the `PolyFix` index
`{x : PUnit}` free so it can be applied at any `PolyFix.mk`
node during a deeper induction. -/
private theorem BTα.induction_gen {α : Type u}
    {motive : ∀ {x : PUnit.{u + 1}},
      PolyFreeM (BTα.carrier α) polyProdType x → Prop}
    (hleaf : ∀ a : α, motive (BTα.leaf a))
    (hnode : ∀ l r : BTα α,
      motive l → motive r → motive (BTα.node l r))
    {x : PUnit.{u + 1}}
    (t : PolyFreeM (BTα.carrier α) polyProdType x) :
    motive t := by
  induction t with
  | mk y idx children ih =>
    have hy := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hself :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate (BTα.carrier α)
                polyProdType) PUnit.unit from
              Sum.inl leafIdx)
            children =
          BTα.leaf leafIdx.val := by
        unfold BTα.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hself]
      exact hleaf leafIdx.val
    | Sum.inr nodeIdx =>
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      have hself :
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
      rw [hself]
      exact hnode _ _
        (ih (Sum.inl PUnit.unit))
        (ih (Sum.inr PUnit.unit))

/-- Structural induction principle for `BTα α`: to prove a
predicate on every tree, prove it for leaves and prove it
preserved by node-formation given the inductive hypotheses on
the two subtrees. -/
theorem BTα.induction {α : Type u}
    {motive : BTα α → Prop}
    (hleaf : ∀ a : α, motive (BTα.leaf a))
    (hnode : ∀ l r : BTα α,
      motive l → motive r → motive (BTα.node l r))
    (t : BTα α) : motive t :=
  BTα.induction_gen (motive := fun {_} t => motive t)
    hleaf hnode t

private def BTα.decEqAux {α : Type u} [DecidableEq α] :
    ∀ (t₁ t₂ : BTα α), Decidable (t₁ = t₂) := by
  intro t₁
  refine PolyFix.ind
    (motive := fun {x} (t : PolyFreeM (BTα.carrier α)
      polyProdType x) =>
      ∀ (t₂ : PolyFreeM (BTα.carrier α) polyProdType x),
        Decidable (t = t₂)) ?step t₁
  intro x i children ih t₂
  have hx := PUnit.eq_punit x
  subst hx
  match i with
  | Sum.inl leafIdx =>
    have hself :
        PolyFix.mk PUnit.unit
          (show polyBetweenIndex PUnit PUnit
            (polyTranslate (BTα.carrier α) polyProdType)
            PUnit.unit from Sum.inl leafIdx) children =
          BTα.leaf leafIdx.val := by
      unfold BTα.leaf polyFreeMPure
      congr 1
      funext e; exact PEmpty.elim e
    rw [hself]
    set b : α := leafIdx.val with hb
    cases hd : BTα.dest t₂ with
    | inl a =>
      have ht₂ := BTα.eq_of_dest_leaf t₂ a hd
      subst ht₂
      exact
        if heq : b = a then
          isTrue (by subst heq; rfl)
        else
          isFalse (fun h => heq (BTα.leaf_injective h))
    | inr p =>
      obtain ⟨l, r⟩ := p
      have ht₂ := BTα.eq_of_dest_node t₂ l r hd
      subst ht₂
      exact isFalse (BTα.leaf_ne_node b l r)
  | Sum.inr nodeIdx =>
    have hni := PUnit.eq_punit nodeIdx
    subst hni
    have hself :
        PolyFix.mk PUnit.unit
          (show polyBetweenIndex PUnit PUnit
            (polyTranslate (BTα.carrier α) polyProdType)
            PUnit.unit from Sum.inr PUnit.unit) children =
          BTα.node (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
      unfold BTα.node polyProdFreeMNode polyFreeMStrFamily
      congr 1
      funext e
      match e with
      | Sum.inl _ => rfl
      | Sum.inr _ => rfl
    rw [hself]
    cases hd : BTα.dest t₂ with
    | inl a =>
      have ht₂ := BTα.eq_of_dest_leaf t₂ a hd
      subst ht₂
      exact isFalse (fun h =>
        BTα.leaf_ne_node a _ _ h.symm)
    | inr p =>
      obtain ⟨l, r⟩ := p
      have ht₂ := BTα.eq_of_dest_node t₂ l r hd
      subst ht₂
      have hl := ih (Sum.inl PUnit.unit) l
      have hr := ih (Sum.inr PUnit.unit) r
      exact
        if heql : children (Sum.inl PUnit.unit) = l then
          if heqr : children (Sum.inr PUnit.unit) = r then
            isTrue (by rw [heql, heqr])
          else
            isFalse (fun h =>
              heqr (BTα.node_injective h).2)
        else
          isFalse (fun h =>
            heql (BTα.node_injective h).1)

instance BTα.decidableEq {α : Type u} [DecidableEq α] :
    DecidableEq (BTα α) :=
  fun t₁ t₂ => BTα.decEqAux t₁ t₂

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

/-- Decoding inverts encoding on every `BTα (Fin (n+1))` tree. -/
theorem decodeBTn_encodeBTn (n : ℕ)
    (t : BTα.{0} (Fin (n + 1))) :
    decodeBTn n (encodeBTn n t) = t := by
  induction t using BTα.induction with
  | hleaf i =>
    rw [encodeBTn_leaf, decodeBTn_lt _ _ i.isLt]
  | hnode l r ihl ihr =>
    rw [encodeBTn_node]
    have hge :
        ¬ ((n + 1) +
          Nat.pair (encodeBTn n l) (encodeBTn n r)) <
            n + 1 := by omega
    rw [decodeBTn_ge _ _ hge]
    have hsub :
        (n + 1) +
          Nat.pair (encodeBTn n l) (encodeBTn n r) -
            (n + 1) =
          Nat.pair (encodeBTn n l) (encodeBTn n r) := by
      omega
    rw [hsub, Nat.unpair_pair, ihl, ihr]

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

private theorem BTα.equivOfEquiv_left_inv
    {α β : Type u} (e : α ≃ β) (t : BTα α) :
    BTα.fold (fun b => BTα.leaf (e.symm b)) BTα.node
      (BTα.fold (fun a => BTα.leaf (e a)) BTα.node t) =
    t := by
  induction t using BTα.induction with
  | hleaf a =>
    rw [BTα.fold_leaf, BTα.fold_leaf,
      Equiv.symm_apply_apply]
  | hnode l r ihl ihr =>
    simp only [BTα.fold_node, ihl, ihr]

private theorem BTα.equivOfEquiv_right_inv
    {α β : Type u} (e : α ≃ β) (t : BTα β) :
    BTα.fold (fun a => BTα.leaf (e a)) BTα.node
      (BTα.fold (fun b => BTα.leaf (e.symm b)) BTα.node t) =
    t := by
  induction t using BTα.induction with
  | hleaf b =>
    rw [BTα.fold_leaf, BTα.fold_leaf,
      Equiv.apply_symm_apply]
  | hnode l r ihl ihr =>
    simp only [BTα.fold_node, ihl, ihr]

/-- Functorial action of `BTα` on type equivalences: any
equivalence between alphabets `α ≃ β` lifts to an equivalence
`BTα α ≃ BTα β` by relabeling leaves. -/
def BTα.equivOfEquiv {α β : Type u} (e : α ≃ β) :
    BTα α ≃ BTα β where
  toFun :=
    BTα.fold (fun a => BTα.leaf (e a)) BTα.node
  invFun :=
    BTα.fold (fun b => BTα.leaf (e.symm b)) BTα.node
  left_inv := BTα.equivOfEquiv_left_inv e
  right_inv := BTα.equivOfEquiv_right_inv e

private theorem equivBTαPUnitBT_left_inv
    (t : BTα.{0} PUnit) :
    BT.fold (BTα.leaf PUnit.unit) BTα.node
      (BTα.fold (fun _ => BT.leaf) BT.node t) =
    t := by
  induction t using BTα.induction with
  | hleaf _ =>
    rw [BTα.fold_leaf, BT.fold_leaf]
  | hnode l r ihl ihr =>
    simp [BTα.fold_node, BT.fold_node, ihl, ihr]

private theorem equivBTαPUnitBT_right_inv
    (t : BT.{0}) :
    BTα.fold (fun _ => BT.leaf) BT.node
      (BT.fold (BTα.leaf PUnit.unit) BTα.node t) =
    t := by
  induction t using BT.induction with
  | hleaf =>
    simp [BT.fold_leaf, BTα.fold_leaf]
  | hnode l r ihl ihr =>
    simp [BT.fold_node, BTα.fold_node, ihl, ihr]

/-- The bridge `BTα PUnit ≃ BT.{0}`.  Both sides are free monads
of `polyProdType` at `PUnit.unit`, but `BTα.carrier PUnit` and
`overTerminal PUnit` differ propositionally (PUnit η).  We fold
through `BT.leaf`/`BT.node` and `BTα.leaf PUnit.unit`/`BTα.node`
in either direction. -/
def equivBTαPUnitBT : BTα.{0} PUnit ≃ BT.{0} where
  toFun  := BTα.fold (fun _ => BT.leaf) BT.node
  invFun := BT.fold (BTα.leaf PUnit.unit) BTα.node
  left_inv := equivBTαPUnitBT_left_inv
  right_inv := equivBTαPUnitBT_right_inv

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

theorem decodeBT_encodeBT (bt : BT.{0}) :
    decodeBT (encodeBT bt) = bt := by
  induction bt using BT.induction with
  | hleaf =>
    simp only [encodeBT, BT.fold_leaf, decodeBT]
  | hnode l r ihl ihr =>
    simp only [encodeBT, BT.fold_node]
    rw [show BT.fold 0
      (fun el er => Nat.pair el er + 1) =
      encodeBT from rfl]
    simp only [decodeBT, Nat.unpair_pair]
    rw [ihl, ihr]

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

private theorem encodeBT_equivBTαPUnitBT
    (u : BTα.{0} PUnit) :
    encodeBT (BTα.fold (fun _ : PUnit => BT.leaf)
        BT.node u) =
      BTα.fold (fun _ : PUnit => 0)
        (fun el er => Nat.pair el er + 1) u := by
  induction u using BTα.induction with
  | hleaf _ =>
    rw [BTα.fold_leaf, BTα.fold_leaf]
    rfl
  | hnode l r ihl ihr =>
    rw [BTα.fold_node, BTα.fold_node]
    change Nat.pair
        (encodeBT (BTα.fold (fun _ : PUnit => BT.leaf)
          BT.node l))
        (encodeBT (BTα.fold (fun _ : PUnit => BT.leaf)
          BT.node r)) + 1 = _
    rw [ihl, ihr]

private theorem encodeBT_equivOfEquiv
    {α : Type} (e : α ≃ PUnit) (u : BTα.{0} α) :
    BTα.fold (fun _ : PUnit => 0)
        (fun el er => Nat.pair el er + 1)
        (BTα.fold
          (fun a => BTα.leaf (e a)) BTα.node u) =
      BTα.fold (fun _ : α => 0)
        (fun el er => Nat.pair el er + 1) u := by
  induction u using BTα.induction with
  | hleaf _ =>
    rw [BTα.fold_leaf, BTα.fold_leaf, BTα.fold_leaf]
  | hnode l r ihl ihr =>
    rw [BTα.fold_node, BTα.fold_node, BTα.fold_node, ihl, ihr]

/-- The fold computation appearing in `encodeBT ∘ equivBTαPUnitBT
∘ BTα.equivOfEquiv` over `BTα (Fin 1)` matches `encodeBTn 0`. -/
private theorem fold_eq_encodeBTn_zero
    (u : BTα.{0} (Fin 1)) :
    BTα.fold (fun _ : Fin 1 => 0)
        (fun el er => Nat.pair el er + 1) u =
      encodeBTn 0 u := by
  induction u using BTα.induction with
  | hleaf i =>
    rw [BTα.fold_leaf, encodeBTn_leaf]
    have hi : i = ⟨0, by omega⟩ := by
      apply Fin.eq_of_val_eq
      have := i.isLt
      simp
    rw [hi]
  | hnode l r ihl ihr =>
    rw [BTα.fold_node, encodeBTn_node, ihl, ihr]
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
  rw [encodeBT_equivBTαPUnitBT]
  rw [encodeBT_equivOfEquiv]
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

/-! ## Perfect tree, depth, and depth-ordering theorem -/

/-- Depth of a `BTα` tree.  Leaf has depth 0; node has depth
1 plus the maximum of its children's depths.

The return type `ℕ` lives in `Type 0`; `BTα.fold` requires both
`α` and `β` in the same universe, so the universe is fixed to 0
here. -/
def BTα.depth {α : Type} : BTα.{0} α → ℕ :=
  BTα.fold (fun _ => 0) (fun dl dr => 1 + max dl dr)

@[simp] theorem BTα.depth_leaf {α : Type} (a : α) :
    BTα.depth (BTα.leaf a) = 0 := by
  simp [BTα.depth]

@[simp] theorem BTα.depth_node {α : Type} (l r : BTα.{0} α) :
    BTα.depth (BTα.node l r) =
      1 + max (BTα.depth l) (BTα.depth r) := by
  simp [BTα.depth]

/-- Perfect labeled binary tree of depth `d` over `Fin (n+1)`,
with all leaves labeled `n` (the maximum-code leaf). -/
def fullBTn (n : ℕ) : ℕ → BTα.{0} (Fin (n + 1))
  | 0     => BTα.leaf ⟨n, Nat.lt_succ_self n⟩
  | d + 1 => BTα.node (fullBTn n d) (fullBTn n d)

@[simp] theorem fullBTn_zero (n : ℕ) :
    fullBTn n 0 = BTα.leaf ⟨n, Nat.lt_succ_self n⟩ := rfl

@[simp] theorem fullBTn_succ (n d : ℕ) :
    fullBTn n (d + 1) =
      BTα.node (fullBTn n d) (fullBTn n d) := rfl

/-- Perfect unlabeled binary tree of depth `d`. -/
def fullBT : ℕ → BT.{0}
  | 0     => BT.leaf
  | d + 1 => BT.node (fullBT d) (fullBT d)

@[simp] theorem fullBT_zero : fullBT 0 = BT.leaf := rfl

@[simp] theorem fullBT_succ (d : ℕ) :
    fullBT (d + 1) = BT.node (fullBT d) (fullBT d) := rfl

private lemma Nat.pair_self_of_self (x : ℕ) :
    Nat.pair x x = x * x + 2 * x := by
  unfold Nat.pair
  split_ifs with h
  · omega
  · ring

/-- The encoding of `fullBTn` satisfies the recurrence
`encode (fullBTn (d+1)) = (encode (fullBTn d) + 1)^2 + n`. -/
theorem encodeBTn_fullBTn_succ (n d : ℕ) :
    encodeBTn n (fullBTn n (d + 1)) =
      (encodeBTn n (fullBTn n d) + 1) ^ 2 + n := by
  rw [fullBTn_succ, encodeBTn_node, Nat.pair_self_of_self]
  ring

/-- Unlabeled specialization: `encode (fullBT (d+1)) =
(encode (fullBT d) + 1)^2`. -/
@[simp] theorem encodeBT_fullBT_succ (d : ℕ) :
    encodeBT (fullBT (d + 1)) = (encodeBT (fullBT d) + 1) ^ 2 := by
  rw [fullBT_succ]
  simp only [encodeBT, BT.fold_node]
  rw [show BT.fold 0 (fun el er => Nat.pair el er + 1) =
    encodeBT from rfl]
  rw [Nat.pair_self_of_self]
  ring

private lemma n_le_encodeBTn_fullBTn (n d : ℕ) :
    n ≤ encodeBTn n (fullBTn n d) := by
  induction d with
  | zero => simp [fullBTn_zero, encodeBTn_leaf]
  | succ d _ =>
      rw [encodeBTn_fullBTn_succ]
      have hsq : 1 ≤ (encodeBTn n (fullBTn n d) + 1) ^ 2 := by
        have h1 : 1 ≤ encodeBTn n (fullBTn n d) + 1 :=
          Nat.le_add_left 1 _
        have := Nat.pow_le_pow_left h1 2
        simpa using this
      omega

private lemma natPair_le_pair {a b a' b' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' := by
  by_cases h1 : a = a'
  · subst h1
    rcases lt_or_eq_of_le hb with hb | rfl
    · exact le_of_lt (Nat.pair_lt_pair_right a hb)
    · rfl
  · have ha' : a < a' := lt_of_le_of_ne ha h1
    by_cases h2 : b = b'
    · subst h2
      exact le_of_lt (Nat.pair_lt_pair_left b ha')
    · have hb' : b < b' := lt_of_le_of_ne hb h2
      exact le_of_lt (lt_trans
        (Nat.pair_lt_pair_left b ha')
        (Nat.pair_lt_pair_right a' hb'))

private lemma pair_le_pair_self_iff {a b M : ℕ} :
    Nat.pair a b ≤ Nat.pair M M ↔ a ≤ M ∧ b ≤ M := by
  constructor
  · intro h
    have hMM : Nat.pair M M = M * M + 2 * M :=
      Nat.pair_self_of_self M
    have hlb : max a b ^ 2 + min a b ≤ Nat.pair a b :=
      Nat.max_sq_add_min_le_pair a b
    have hbound : max a b ^ 2 + min a b ≤ M * M + 2 * M := by
      rw [← hMM]; exact le_trans hlb h
    have hmax : max a b ≤ M := by
      by_contra hgt
      push_neg at hgt
      have hge : max a b ≥ M + 1 := hgt
      have hsq : (M + 1) ^ 2 ≤ max a b ^ 2 :=
        Nat.pow_le_pow_left hge 2
      have hexp : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
      have : M * M + 2 * M + 1 ≤ M * M + 2 * M := by
        calc M * M + 2 * M + 1
            = (M + 1) ^ 2 := hexp.symm
          _ ≤ max a b ^ 2 := hsq
          _ ≤ max a b ^ 2 + min a b := Nat.le_add_right _ _
          _ ≤ M * M + 2 * M := hbound
      omega
    exact ⟨le_trans (le_max_left a b) hmax,
           le_trans (le_max_right a b) hmax⟩
  · intro ⟨ha, hb⟩
    exact natPair_le_pair ha hb

/-- Trees of depth ≤ d are exactly those with encoding ≤ that of
the perfect depth-d tree.  This is the precise statement that
the encoding orders trees by depth. -/
theorem encodeBTn_le_fullBTn_iff_depth_le {n : ℕ}
    (t : BTα.{0} (Fin (n + 1))) (d : ℕ) :
    encodeBTn n t ≤ encodeBTn n (fullBTn n d) ↔
      BTα.depth t ≤ d := by
  induction d generalizing t with
  | zero =>
      rcases BTα.leaf_or_node t with ⟨i, rfl⟩ | ⟨l, r, rfl⟩
      · simp only [encodeBTn_leaf, fullBTn_zero,
          BTα.depth_leaf, Nat.le_zero, iff_true]
        exact Nat.le_of_lt_succ i.isLt
      · simp only [encodeBTn_node, fullBTn_zero,
          encodeBTn_leaf, BTα.depth_node]
        constructor
        · intro h
          have hpos : 0 < n + 1 + Nat.pair
              (encodeBTn n l) (encodeBTn n r) := by omega
          have hni : n < n + 1 + Nat.pair
              (encodeBTn n l) (encodeBTn n r) := by omega
          omega
        · intro h; omega
  | succ d ih =>
      rcases BTα.leaf_or_node t with ⟨i, rfl⟩ | ⟨l, r, rfl⟩
      · constructor
        · intro _; simp [BTα.depth_leaf]
        · intro _
          rw [encodeBTn_leaf]
          have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
          have hbase : n ≤ encodeBTn n (fullBTn n (d + 1)) :=
            n_le_encodeBTn_fullBTn n (d + 1)
          exact le_trans hi hbase
      · rw [encodeBTn_node, encodeBTn_fullBTn_succ,
          BTα.depth_node]
        constructor
        · intro h
          set M := encodeBTn n (fullBTn n d) with hM
          have hMpair : (M + 1) ^ 2 + n =
              n + 1 + Nat.pair M M := by
            rw [Nat.pair_self_of_self]; ring
          rw [hMpair] at h
          have hpair :
              Nat.pair (encodeBTn n l) (encodeBTn n r) ≤
              Nat.pair M M := by omega
          rw [pair_le_pair_self_iff] at hpair
          obtain ⟨hl, hr⟩ := hpair
          have ihl := (ih l).mp hl
          have ihr := (ih r).mp hr
          have : max (BTα.depth l) (BTα.depth r) ≤ d :=
            max_le ihl ihr
          omega
        · intro h
          have hmax : max (BTα.depth l) (BTα.depth r) ≤ d := by
            omega
          have hl : BTα.depth l ≤ d :=
            le_trans (le_max_left _ _) hmax
          have hr : BTα.depth r ≤ d :=
            le_trans (le_max_right _ _) hmax
          have hle_l := (ih l).mpr hl
          have hle_r := (ih r).mpr hr
          set M := encodeBTn n (fullBTn n d) with hM
          have hpair :
              Nat.pair (encodeBTn n l) (encodeBTn n r) ≤
              Nat.pair M M :=
            natPair_le_pair hle_l hle_r
          have hexp : Nat.pair M M = M * M + 2 * M :=
            Nat.pair_self_of_self M
          have hsq : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
          omega

/-- Strict-monotonicity corollary of the depth-ordering
biconditional: depth-strict-less implies encoding-strict-less. -/
theorem encodeBTn_lt_of_depth_lt {n : ℕ}
    (t₁ t₂ : BTα.{0} (Fin (n + 1)))
    (h : BTα.depth t₁ < BTα.depth t₂) :
    encodeBTn n t₁ < encodeBTn n t₂ := by
  set d := BTα.depth t₂ - 1 with hd
  have hd2 : BTα.depth t₂ = d + 1 := by omega
  have h1 : BTα.depth t₁ ≤ d := by omega
  have h2 : ¬ BTα.depth t₂ ≤ d := by omega
  have hu :
      encodeBTn n t₁ ≤ encodeBTn n (fullBTn n d) :=
    (encodeBTn_le_fullBTn_iff_depth_le t₁ d).mpr h1
  have hv :
      ¬ encodeBTn n t₂ ≤ encodeBTn n (fullBTn n d) :=
    fun he =>
      h2 ((encodeBTn_le_fullBTn_iff_depth_le t₂ d).mp he)
  have : encodeBTn n (fullBTn n d) < encodeBTn n t₂ :=
    Nat.lt_of_not_le hv
  exact lt_of_le_of_lt hu this

/-! ## Unlabeled depth specializations -/

/-- Depth of an unlabeled `BT.{0}` tree.  Leaf has depth 0; node
has depth 1 plus the maximum of its children's depths. -/
def BT.depth (t : BT.{0}) : ℕ :=
  BT.fold 0 (fun dl dr => 1 + max dl dr) t

@[simp] theorem BT.depth_leaf : BT.depth BT.leaf = 0 := by
  simp [BT.depth, BT.fold_leaf]

@[simp] theorem BT.depth_node (l r : BT.{0}) :
    BT.depth (BT.node l r) =
      1 + max (BT.depth l) (BT.depth r) := by
  simp [BT.depth, BT.fold_node]

private lemma equivBTnBT1_zero_symm_id
    (s : BTα.{0} (Fin 1)) :
    (equivBTnBT1 0).symm s = s := by
  unfold equivBTnBT1 equivBTnBTm
  change (equivBTnNat 0).symm
      ((equivBTnNat 0) s) = s
  exact Equiv.symm_apply_apply _ s

private lemma equivBTαPUnitBT_symm_leaf :
    equivBTαPUnitBT.symm BT.leaf = BTα.leaf PUnit.unit := by
  change BT.fold (BTα.leaf PUnit.unit) BTα.node BT.leaf =
    BTα.leaf PUnit.unit
  exact BT.fold_leaf _ _

private lemma equivBTαPUnitBT_symm_node (l r : BT.{0}) :
    equivBTαPUnitBT.symm (BT.node l r) =
      BTα.node (equivBTαPUnitBT.symm l)
        (equivBTαPUnitBT.symm r) := by
  change BT.fold (BTα.leaf PUnit.unit) BTα.node
      (BT.node l r) = _
  rw [BT.fold_node]
  rfl

private lemma equivOfEquivFinPUnit_symm_leaf
    (b : PUnit) :
    (BTα.equivOfEquiv (Equiv.equivPUnit (Fin 1))).symm
        (BTα.leaf b) =
      BTα.leaf ((Equiv.equivPUnit (Fin 1)).symm b) := by
  change BTα.fold
      (fun b' => BTα.leaf
        ((Equiv.equivPUnit (Fin 1)).symm b'))
      BTα.node (BTα.leaf b) = _
  exact BTα.fold_leaf _ _ _

private lemma equivOfEquivFinPUnit_symm_node
    (u v : BTα.{0} PUnit) :
    (BTα.equivOfEquiv (Equiv.equivPUnit (Fin 1))).symm
        (BTα.node u v) =
      BTα.node
        ((BTα.equivOfEquiv
          (Equiv.equivPUnit (Fin 1))).symm u)
        ((BTα.equivOfEquiv
          (Equiv.equivPUnit (Fin 1))).symm v) := by
  change BTα.fold
      (fun b => BTα.leaf
        ((Equiv.equivPUnit (Fin 1)).symm b))
      BTα.node (BTα.node u v) = _
  rw [BTα.fold_node]
  rfl

private lemma equivBTnBT_zero_symm_leaf :
    (equivBTnBT 0).symm BT.leaf =
      BTα.leaf (⟨0, Nat.zero_lt_one⟩ : Fin 1) := by
  unfold equivBTnBT
  change (equivBTnBT1 0).symm
      ((BTα.equivOfEquiv (Equiv.equivPUnit (Fin 1))).symm
        (equivBTαPUnitBT.symm BT.leaf)) = _
  rw [equivBTαPUnitBT_symm_leaf,
    equivOfEquivFinPUnit_symm_leaf,
    equivBTnBT1_zero_symm_id]
  rfl

private lemma equivBTnBT_zero_symm_node (l r : BT.{0}) :
    (equivBTnBT 0).symm (BT.node l r) =
      BTα.node ((equivBTnBT 0).symm l)
        ((equivBTnBT 0).symm r) := by
  unfold equivBTnBT
  change (equivBTnBT1 0).symm
      ((BTα.equivOfEquiv (Equiv.equivPUnit (Fin 1))).symm
        (equivBTαPUnitBT.symm (BT.node l r))) =
    BTα.node _ _
  rw [equivBTαPUnitBT_symm_node,
    equivOfEquivFinPUnit_symm_node,
    equivBTnBT1_zero_symm_id]
  change BTα.node _ _ = BTα.node _ _
  congr 1
  · change _ =
      (equivBTnBT1 0).symm
        ((BTα.equivOfEquiv (Equiv.equivPUnit (Fin 1))).symm
          (equivBTαPUnitBT.symm l))
    rw [equivBTnBT1_zero_symm_id]
  · change _ =
      (equivBTnBT1 0).symm
        ((BTα.equivOfEquiv (Equiv.equivPUnit (Fin 1))).symm
          (equivBTαPUnitBT.symm r))
    rw [equivBTnBT1_zero_symm_id]

private lemma encodeBT_fullBT_eq_encodeBTn_fullBTn (d : ℕ) :
    encodeBT (fullBT d) = encodeBTn 0 (fullBTn 0 d) := by
  induction d with
  | zero =>
      simp [fullBT, encodeBT, BT.fold_leaf, fullBTn_zero,
        encodeBTn_leaf]
  | succ d ih =>
      rw [encodeBT_fullBT_succ, encodeBTn_fullBTn_succ, ih]
      omega

private theorem BT_depth_eq_BTα_depth (t : BT.{0}) :
    BT.depth t = BTα.depth ((equivBTnBT 0).symm t) := by
  induction t using BT.induction with
  | hleaf =>
    rw [BT.depth_leaf, equivBTnBT_zero_symm_leaf,
      BTα.depth_leaf]
  | hnode l r ihl ihr =>
    rw [BT.depth_node, equivBTnBT_zero_symm_node,
      BTα.depth_node, ihl, ihr]

/-- Unlabeled trees of depth ≤ d are exactly those with encoding ≤
that of the perfect depth-d tree. -/
theorem encodeBT_le_fullBT_iff_depth_le (t : BT.{0}) (d : ℕ) :
    encodeBT t ≤ encodeBT (fullBT d) ↔ BT.depth t ≤ d := by
  rw [encodeBT_eq_encodeBTn_zero t,
    encodeBT_fullBT_eq_encodeBTn_fullBTn d,
    encodeBTn_le_fullBTn_iff_depth_le, BT_depth_eq_BTα_depth]

/-- Strict-monotonicity corollary for unlabeled trees:
depth-strict-less implies encoding-strict-less. -/
theorem encodeBT_lt_of_depth_lt (t₁ t₂ : BT.{0})
    (h : BT.depth t₁ < BT.depth t₂) :
    encodeBT t₁ < encodeBT t₂ := by
  set d := BT.depth t₂ - 1 with hd
  have hd2 : BT.depth t₂ = d + 1 := by omega
  have h1 : BT.depth t₁ ≤ d := by omega
  have h2 : ¬ BT.depth t₂ ≤ d := by omega
  have hu : encodeBT t₁ ≤ encodeBT (fullBT d) :=
    (encodeBT_le_fullBT_iff_depth_le t₁ d).mpr h1
  have hv : ¬ encodeBT t₂ ≤ encodeBT (fullBT d) :=
    fun he =>
      h2 ((encodeBT_le_fullBT_iff_depth_le t₂ d).mp he)
  have : encodeBT (fullBT d) < encodeBT t₂ :=
    Nat.lt_of_not_le hv
  exact lt_of_le_of_lt hu this

end GebLean
