import GebLean.LawvereBTInterp
import GebLean.TreeLogic
import GebLean.TreePER
import Mathlib.CategoryTheory.Types.Basic

/-!
# `Type` as a PBTO Category

Provides instances exhibiting `Type u` as a category with
chosen finite products, a parameterized binary tree object
(`BT`), Boolean dichotomy, and decidable structural tree
equality.  These witness that the abstract typeclass
interfaces `HasChosenFiniteProducts`, `HasPBTO`,
`HasBoolDichotomy`, and `HasTreeEq` are inhabited in a
model distinct from `LawvereBTQuotCat`.
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## Chosen finite products on `Type u` -/

instance : HasChosenFiniteProducts (Type u) where
  terminal :=
    { obj := PUnit
      from_ := fun _ _ => PUnit.unit
      uniq := by
        intro A f
        funext a
        exact (PUnit.eq_punit (f a)).symm }
  product A B :=
    { obj := A × B
      fst := Prod.fst
      snd := Prod.snd
      lift := fun f g d => (f d, g d)
      lift_fst := by intros; rfl
      lift_snd := by intros; rfl
      lift_uniq := by
        intro D f g h hfst hsnd
        funext d
        have hf : (h d).1 = f d := congrFun hfst d
        have hs : (h d).2 = g d := congrFun hsnd d
        exact Prod.ext hf hs }

/-! ## Parameterized binary tree object on `Type u` -/

/-- The `elim` operator for `Type u`: parameterized
catamorphism on `BT` via `BT.fold`. -/
def typeElim {A X : Type u} (f : A → X)
    (g : X × X → X) : A × BT.{u} → X :=
  fun p => BT.fold (f p.1)
    (fun x y => g (x, y)) p.2

private theorem typeElim_uniq_gen
    {A X : Type u} (f : A → X) (g : X × X → X)
    (φ : A × BT.{u} → X)
    (hℓ : ∀ a, φ (a, BT.leaf) = f a)
    (hβ : ∀ a l r,
      φ (a, BT.node l r) = g (φ (a, l), φ (a, r)))
    (a : A)
    {y : PUnit.{u + 1}}
    (t : PolyFreeM (overTerminal PUnit.{u + 1})
      polyProdType y) :
    φ (a, t) = typeElim f g (a, t) := by
  induction t with
  | mk y idx children ih =>
    have hy : y = PUnit.unit := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hmk, hℓ a]
      exact (BT.fold_leaf (f a)
        (fun x y => g (x, y))).symm
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      set l : BT.{u} :=
        children (Sum.inl PUnit.unit)
      set r : BT.{u} :=
        children (Sum.inr PUnit.unit)
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node l r := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, hβ a l r,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]
      rfl

instance : HasPBTO (Type u) where
  T := BT.{u}
  ℓ := fun _ => BT.leaf
  β := fun p => BT.node p.1 p.2
  elim := @typeElim
  elim_ℓ := by
    intro A X f g
    funext a
    exact BT.fold_leaf (f a) (fun x y => g (x, y))
  elim_β := by
    intro A X f g
    funext p
    rfl
  elim_uniq := by
    intro A X f g φ hℓ hβ
    funext p
    obtain ⟨a, t⟩ := p
    apply typeElim_uniq_gen f g φ
      (fun a' => congrFun hℓ a')
      (fun a' l r => congrFun hβ (a', (l, r)))
      a t

/-! ## Boolean dichotomy on `Type u` -/

/-- `isLeafEndo` applied to `BT.leaf` in `Type`
reduces to `BT.leaf`. -/
private theorem type_isLeafEndo_leaf :
    (isLeafEndo (C := Type u)) BT.leaf = BT.leaf := by
  unfold isLeafEndo isLeaf
  change BT.fold BT.leaf
    (fun _ _ => BT.node BT.leaf BT.leaf) BT.leaf =
    BT.leaf
  exact BT.fold_leaf _ _

/-- `isLeafEndo` applied to `BT.node l r` in `Type`
reduces to `treeFalse`. -/
private theorem type_isLeafEndo_node
    (l r : BT.{u}) :
    (isLeafEndo (C := Type u)) (BT.node l r) =
      BT.node BT.leaf BT.leaf := by
  unfold isLeafEndo isLeaf
  change BT.fold BT.leaf
    (fun _ _ => BT.node BT.leaf BT.leaf)
    (BT.node l r) =
    BT.node BT.leaf BT.leaf
  rw [BT.fold_node]

/-- Tree `false`: `BT.node BT.leaf BT.leaf`. -/
def treeFalseBT : BT.{u} := BT.node BT.leaf BT.leaf

/-- "Is leaf" check on `BT`: `BT.leaf` if the tree is
leaf, `treeFalseBT` otherwise. -/
def isLeafBT (t : BT.{u}) : BT.{u} :=
  BT.fold BT.leaf (fun _ _ => treeFalseBT) t

/-- Boolean conjunction on `BT`: result is `BT.leaf`
when both arguments are `BT.leaf`, otherwise
`treeFalseBT`. -/
def boolAndBT (a b : BT.{u}) : BT.{u} :=
  BT.fold (isLeafBT b)
    (fun _ _ => treeFalseBT) a

/-- Single-level case analysis on a `BT`: applies
`onLeaf` when the tree is a leaf, and `onNode`
applied to the two children when the tree is a
branch.  This is a non-recursive match on the
underlying `PolyFix` constructor. -/
def BT.caseOn {α : Type u} (t : BT.{u})
    (onLeaf : α)
    (onNode : BT.{u} → BT.{u} → α) : α :=
  match t with
  | PolyFix.mk _ (Sum.inl _) _ => onLeaf
  | PolyFix.mk _ (Sum.inr _) cs =>
    onNode (cs (Sum.inl PUnit.unit))
      (cs (Sum.inr PUnit.unit))

/-- Structural tree equality via fold on the first
argument (producing a `BT → BT` function) with
`BT.caseOn` on the second argument inside the step.
Returns `BT.leaf` when the two trees are
structurally equal, and `treeFalseBT` otherwise. -/
def treeEqBT (s t : BT.{u}) : BT.{u} :=
  BT.fold
    (α := BT.{u} → BT.{u})
    (fun t' => isLeafBT t')
    (fun rA rB => fun t' =>
      BT.caseOn t' treeFalseBT
        (fun c d => boolAndBT (rA c) (rB d)))
    s t

/-! ### Computation rules for `isLeafBT` -/

theorem isLeafBT_leaf :
    isLeafBT (BT.leaf : BT.{u}) = BT.leaf :=
  BT.fold_leaf _ _

theorem isLeafBT_node (l r : BT.{u}) :
    isLeafBT (BT.node l r) = treeFalseBT := by
  unfold isLeafBT
  rw [BT.fold_node]

/-! ### Computation rules for `BT.caseOn` -/

theorem BT.caseOn_leaf {α : Type u}
    (onLeaf : α)
    (onNode : BT.{u} → BT.{u} → α) :
    BT.caseOn (BT.leaf : BT.{u}) onLeaf onNode =
      onLeaf := by
  unfold BT.caseOn BT.leaf polyFreeMPure
  rfl

theorem BT.caseOn_node {α : Type u}
    (l r : BT.{u}) (onLeaf : α)
    (onNode : BT.{u} → BT.{u} → α) :
    BT.caseOn (BT.node l r) onLeaf onNode =
      onNode l r := by
  unfold BT.caseOn BT.node polyProdFreeMNode
    polyFreeMStrFamily
  rfl

/-! ### Computation rules for `boolAndBT` -/

theorem boolAndBT_leaf_leaf :
    boolAndBT (BT.leaf : BT.{u}) BT.leaf =
      BT.leaf := by
  unfold boolAndBT
  rw [BT.fold_leaf, isLeafBT_leaf]

theorem boolAndBT_leaf_node (l r : BT.{u}) :
    boolAndBT BT.leaf (BT.node l r) =
      treeFalseBT := by
  unfold boolAndBT
  rw [BT.fold_leaf, isLeafBT_node]

theorem boolAndBT_node_any (l r t : BT.{u}) :
    boolAndBT (BT.node l r) t = treeFalseBT := by
  unfold boolAndBT
  rw [BT.fold_node]

/-! ### Computation rules for `treeEqBT` -/

theorem treeEqBT_leaf (t : BT.{u}) :
    treeEqBT BT.leaf t = isLeafBT t := by
  unfold treeEqBT
  rw [BT.fold_leaf]

theorem treeEqBT_node_leaf (a b : BT.{u}) :
    treeEqBT (BT.node a b) BT.leaf =
      treeFalseBT := by
  unfold treeEqBT
  rw [BT.fold_node]
  exact BT.caseOn_leaf _ _

theorem treeEqBT_node_node (a b c d : BT.{u}) :
    treeEqBT (BT.node a b) (BT.node c d) =
      boolAndBT (treeEqBT a c) (treeEqBT b d) := by
  unfold treeEqBT
  rw [BT.fold_node]
  exact BT.caseOn_node c d _ _

/-! ### Booleanness of `treeEqBT` -/

/-- `boolAndBT` always returns `BT.leaf` or
`treeFalseBT`. -/
theorem boolAndBT_is_bool (a b : BT.{u}) :
    boolAndBT a b = BT.leaf ∨
    boolAndBT a b = treeFalseBT := by
  rcases BT.leaf_or_node a with ha | ⟨l, r, ha⟩
  · rcases BT.leaf_or_node b with hb | ⟨l', r', hb⟩
    · subst ha; subst hb
      left; exact boolAndBT_leaf_leaf
    · subst ha; subst hb
      right; exact boolAndBT_leaf_node l' r'
  · subst ha
    right
    exact boolAndBT_node_any l r b

/-- `isLeafBT` always returns `BT.leaf` or
`treeFalseBT`. -/
theorem isLeafBT_is_bool (t : BT.{u}) :
    isLeafBT t = BT.leaf ∨
    isLeafBT t = treeFalseBT := by
  rcases BT.leaf_or_node t with ht | ⟨l, r, ht⟩
  · subst ht; left; exact isLeafBT_leaf
  · subst ht; right; exact isLeafBT_node l r

/-- `treeEqBT` always returns `BT.leaf` or
`treeFalseBT`.  Generalized over the fiber index for
induction on the underlying `PolyFix`. -/
private theorem treeEqBT_is_bool_gen
    {y : PUnit.{u + 1}}
    (s : PolyFreeM (overTerminal PUnit.{u + 1})
      polyProdType y)
    (t : BT.{u}) :
    treeEqBT s t = BT.leaf ∨
    treeEqBT s t = treeFalseBT := by
  induction s with
  | mk y idx children ih =>
    have hy : y = PUnit.unit := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hmk, treeEqBT_leaf]
      exact isLeafBT_is_bool t
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      set l : BT.{u} :=
        children (Sum.inl PUnit.unit)
      set r : BT.{u} :=
        children (Sum.inr PUnit.unit)
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node l r := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk]
      rcases BT.leaf_or_node t with ht | ⟨c, d, ht⟩
      · subst ht
        rw [treeEqBT_node_leaf]
        right; rfl
      · subst ht
        rw [treeEqBT_node_node]
        exact boolAndBT_is_bool _ _

theorem treeEqBT_is_bool (s t : BT.{u}) :
    treeEqBT s t = BT.leaf ∨
    treeEqBT s t = treeFalseBT :=
  treeEqBT_is_bool_gen s t

/-! ### Reflexivity, symmetry, transitivity -/

/-- `treeEqBT t t = BT.leaf` for all `t`. -/
private theorem treeEqBT_refl_gen
    {y : PUnit.{u + 1}}
    (t : PolyFreeM (overTerminal PUnit.{u + 1})
      polyProdType y) :
    treeEqBT t t = BT.leaf := by
  induction t with
  | mk y idx children ih =>
    have hy : y = PUnit.unit := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hmk, treeEqBT_leaf, isLeafBT_leaf]
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      set l : BT.{u} :=
        children (Sum.inl PUnit.unit)
      set r : BT.{u} :=
        children (Sum.inr PUnit.unit)
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node l r := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, treeEqBT_node_node,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit),
        boolAndBT_leaf_leaf]

theorem treeEqBT_refl (t : BT.{u}) :
    treeEqBT t t = BT.leaf :=
  treeEqBT_refl_gen t

/-- `treeEqBT` is symmetric. -/
private theorem treeEqBT_symm_gen
    {y : PUnit.{u + 1}}
    (s : PolyFreeM (overTerminal PUnit.{u + 1})
      polyProdType y) :
    ∀ (t : BT.{u}),
    treeEqBT s t = treeEqBT t s := by
  induction s with
  | mk y idx children ih =>
    intro t
    have hy : y = PUnit.unit := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hmk, treeEqBT_leaf]
      rcases BT.leaf_or_node t with ht | ⟨c, d, ht⟩
      · subst ht
        rw [isLeafBT_leaf, treeEqBT_leaf,
          isLeafBT_leaf]
      · subst ht
        rw [isLeafBT_node, treeEqBT_node_leaf]
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      set l : BT.{u} :=
        children (Sum.inl PUnit.unit)
      set r : BT.{u} :=
        children (Sum.inr PUnit.unit)
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node l r := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk]
      rcases BT.leaf_or_node t with ht | ⟨c, d, ht⟩
      · subst ht
        rw [treeEqBT_leaf, treeEqBT_node_leaf,
          isLeafBT_node]
      · subst ht
        rw [treeEqBT_node_node, treeEqBT_node_node,
          ih (Sum.inl PUnit.unit) c,
          ih (Sum.inr PUnit.unit) d]

theorem treeEqBT_symm (s t : BT.{u}) :
    treeEqBT s t = treeEqBT t s :=
  treeEqBT_symm_gen s t

/-- If `boolAndBT a b = BT.leaf` then both `a` and
`b` are `BT.leaf`. -/
theorem boolAndBT_eq_leaf_iff (a b : BT.{u}) :
    boolAndBT a b = BT.leaf ↔
    a = BT.leaf ∧ b = BT.leaf := by
  constructor
  · intro h
    rcases BT.leaf_or_node a with ha | ⟨l, r, ha⟩
    · subst ha
      rcases BT.leaf_or_node b with hb | ⟨l', r', hb⟩
      · exact ⟨rfl, hb⟩
      · subst hb
        rw [boolAndBT_leaf_node] at h
        exact absurd h BT.leaf_ne_node.symm
    · subst ha
      rw [boolAndBT_node_any] at h
      exact absurd h BT.leaf_ne_node.symm
  · intro ⟨ha, hb⟩
    subst ha; subst hb
    exact boolAndBT_leaf_leaf

/-- If `treeEqBT s t = BT.leaf` and
`treeEqBT t u = BT.leaf`, then
`treeEqBT s u = BT.leaf`.  This is Boolean
transitivity of `treeEqBT`. -/
private theorem treeEqBT_trans_gen
    {y : PUnit.{u + 1}}
    (s : PolyFreeM (overTerminal PUnit.{u + 1})
      polyProdType y) :
    ∀ (t u : BT.{u}),
    treeEqBT s t = BT.leaf →
    treeEqBT t u = BT.leaf →
    treeEqBT s u = BT.leaf := by
  induction s with
  | mk y idx children ih =>
    intro t u hst htu
    have hy : y = PUnit.unit := PUnit.eq_punit y
    subst hy
    match idx with
    | Sum.inl leafIdx =>
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e
        exact PEmpty.elim e
      rw [hmk] at hst
      rw [hmk, treeEqBT_leaf]
      rw [treeEqBT_leaf] at hst
      rcases BT.leaf_or_node t with ht | ⟨c, d, ht⟩
      · subst ht
        rcases BT.leaf_or_node u with
          hu | ⟨c', d', hu⟩
        · subst hu; exact isLeafBT_leaf
        · subst hu
          rw [treeEqBT_leaf, isLeafBT_node]
            at htu
          exact absurd htu BT.leaf_ne_node.symm
      · subst ht
        rw [isLeafBT_node] at hst
        exact absurd hst BT.leaf_ne_node.symm
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      set l : BT.{u} :=
        children (Sum.inl PUnit.unit)
      set r : BT.{u} :=
        children (Sum.inr PUnit.unit)
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node l r := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk] at hst
      rw [hmk]
      rcases BT.leaf_or_node t with ht | ⟨c, d, ht⟩
      · subst ht
        rw [treeEqBT_node_leaf] at hst
        exact absurd hst BT.leaf_ne_node.symm
      · subst ht
        rw [treeEqBT_node_node] at hst
        obtain ⟨hac, hbd⟩ :=
          (boolAndBT_eq_leaf_iff _ _).mp hst
        rcases BT.leaf_or_node u with
          hu | ⟨c', d', hu⟩
        · subst hu
          rw [treeEqBT_node_leaf] at htu
          exact absurd htu BT.leaf_ne_node.symm
        · subst hu
          rw [treeEqBT_node_node] at htu
          obtain ⟨hcc, hdd⟩ :=
            (boolAndBT_eq_leaf_iff _ _).mp htu
          rw [treeEqBT_node_node]
          rw [ih (Sum.inl PUnit.unit) c c' hac hcc,
            ih (Sum.inr PUnit.unit) d d' hbd hdd]
          exact boolAndBT_leaf_leaf

theorem treeEqBT_trans (s t u : BT.{u})
    (hst : treeEqBT s t = BT.leaf)
    (htu : treeEqBT t u = BT.leaf) :
    treeEqBT s u = BT.leaf :=
  treeEqBT_trans_gen s t u hst htu

theorem hasBoolDichotomy_type :
    HasBoolDichotomy (Type u) := by
  intro e he
  have heval :
      (isLeafEndo (C := Type u)) (e PUnit.unit) =
      e PUnit.unit := congrFun he PUnit.unit
  rcases BT.leaf_or_node (e PUnit.unit) with
    hleaf | ⟨l, r, hnode⟩
  · left
    funext x
    have hx : e x = e PUnit.unit := by
      congr 1
    rw [hx, hleaf]
    rfl
  · right
    funext x
    have hx : e x = e PUnit.unit := by
      congr 1
    rw [hnode, type_isLeafEndo_node l r] at heval
    rw [hx, hnode, ← heval]
    rfl

end GebLean
