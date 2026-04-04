import GebLean.LawvereBTInterp
import GebLean.TreeLogic
import GebLean.TreePER
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Generator.Type

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

/-! ## `HasTreeEq` instance for `Type u` -/

/-- `cfpTerminal` in `Type u` is `PUnit.{u+1}` and
is a separator. -/
theorem type_cfpTerminal_isSeparator :
    IsSeparator (cfpTerminal (C := Type u)) :=
  CategoryTheory.Types.isSeparator_punit

/-- The categorical tree equality morphism in
`Type u`: applies `treeEqBT` pointwise. -/
def typeTreeEq : cfpProd (C := Type u) BT.{u} BT.{u} ⟶
    BT.{u} :=
  fun p => treeEqBT p.1 p.2

theorem typeTreeEq_bool :
    (typeTreeEq ≫ isLeafEndo :
      cfpProd BT.{u} BT.{u} ⟶ BT.{u}) =
      typeTreeEq := by
  funext p
  change (isLeafEndo (C := Type u))
    (treeEqBT p.1 p.2) = treeEqBT p.1 p.2
  rcases treeEqBT_is_bool p.1 p.2 with hL | hR
  · rw [hL]; exact type_isLeafEndo_leaf
  · rw [hR]
    exact type_isLeafEndo_node BT.leaf BT.leaf

theorem typeTreeEq_refl :
    cfpLift (𝟙 (BT.{u})) (𝟙 BT.{u}) ≫ typeTreeEq =
    cfpTerminalFrom BT.{u} ≫
      (HasPBTO.ℓ : cfpTerminal ⟶ BT.{u}) := by
  funext t
  change treeEqBT t t = BT.leaf
  exact treeEqBT_refl t

theorem typeTreeEq_symm :
    cfpSwap BT.{u} BT.{u} ≫ typeTreeEq = typeTreeEq := by
  funext p
  change treeEqBT p.2 p.1 = treeEqBT p.1 p.2
  exact (treeEqBT_symm p.1 p.2).symm

private theorem typeTreeEq_quantTransitive :
    QuantTransitive typeTreeEq := by
  intro D e h1 h2
  unfold IsLeafConst at h1 h2 ⊢
  funext d
  have h1d := congrFun h1 d
  have h2d := congrFun h2 d
  change treeEqBT (e d).1 (e d).2.2 = BT.leaf at h1d
  change treeEqBT (e d).2.2 (e d).2.1 = BT.leaf at h2d
  change treeEqBT (e d).1 (e d).2.1 = BT.leaf
  exact treeEqBT_trans _ _ _ h1d h2d

theorem typeTreeEq_trans : EqTransitive typeTreeEq :=
  quantTransitive_implies_eq
    type_cfpTerminal_isSeparator
    hasBoolDichotomy_type
    typeTreeEq_bool
    typeTreeEq_quantTransitive

theorem typeTreeEq_ℓℓ :
    cfpLift
      (HasPBTO.ℓ : cfpTerminal ⟶ BT.{u})
      HasPBTO.ℓ ≫
      typeTreeEq =
    HasPBTO.ℓ := by
  funext _
  change treeEqBT BT.leaf BT.leaf = BT.leaf
  rw [treeEqBT_leaf]
  exact isLeafBT_leaf

theorem typeTreeEq_ℓβ :
    cfpMap
      (HasPBTO.ℓ : cfpTerminal ⟶ BT.{u})
      (HasPBTO.β : cfpProd BT BT ⟶ BT) ≫
      typeTreeEq =
    cfpTerminalFrom _ ≫ treeFalse := by
  funext p
  change treeEqBT BT.leaf (BT.node p.2.1 p.2.2) =
    BT.node BT.leaf BT.leaf
  rw [treeEqBT_leaf]
  exact isLeafBT_node p.2.1 p.2.2

theorem typeTreeEq_βℓ :
    cfpMap
      (HasPBTO.β : cfpProd BT BT ⟶ BT)
      (HasPBTO.ℓ : cfpTerminal ⟶ BT.{u}) ≫
      typeTreeEq =
    cfpTerminalFrom _ ≫ treeFalse := by
  funext p
  change treeEqBT (BT.node p.1.1 p.1.2) BT.leaf =
    BT.node BT.leaf BT.leaf
  exact treeEqBT_node_leaf p.1.1 p.1.2

/-- Applying the categorical `boolAnd` in `Type u`
to a Boolean-valued pair where both components are
`BT.leaf` returns `BT.leaf`. -/
private theorem boolAnd_leaf_leaf_eval :
    ((boolAnd (C := Type u)) : BT × BT → BT)
      (BT.leaf, BT.leaf) = BT.leaf := by
  have h := boolAnd_ℓ_ℓ (C := Type u)
  have := congrFun h PUnit.unit
  exact this

/-- `cfpMap HasPBTO.ℓ (𝟙 HasPBTO.T)` in `Type u`
acts by sending `(_, y)` to `(BT.leaf, y)`. -/
private theorem cfpMap_ℓ_id_eval (y : BT.{u}) :
    ((cfpMap HasPBTO.ℓ (𝟙 HasPBTO.T) :
      cfpProd cfpTerminal HasPBTO.T ⟶
        cfpProd BT.{u} BT.{u}) :
      cfpTerminal × BT.{u} → BT × BT)
      (PUnit.unit, y) = (BT.leaf, y) := by
  unfold cfpMap cfpLift cfpFst cfpSnd
  rfl

/-- The categorical composition `A ≫ B` in `Type u`
is function composition. -/
private theorem type_comp_apply
    {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) : (f ≫ g) x = g (f x) := rfl

/-- Applying the categorical `boolAnd` in `Type u`
to `(leaf, treeFalseBT)` returns `treeFalseBT`. -/
private theorem boolAnd_leaf_treeFalseBT_eval :
    ((boolAnd (C := Type u)) : BT × BT → BT)
      (BT.leaf, treeFalseBT) = treeFalseBT := by
  have h := boolAnd_leaf_left (C := Type u)
  have heval := congrFun h
    ((PUnit.unit, treeFalseBT) :
      cfpTerminal × BT.{u})
  rw [type_comp_apply, type_comp_apply] at heval
  rw [cfpMap_ℓ_id_eval treeFalseBT] at heval
  change ((boolAnd (C := Type u)) : BT × BT → BT)
    (BT.leaf, treeFalseBT) =
    (isLeafEndo (C := Type u)) treeFalseBT at heval
  rw [heval]
  exact type_isLeafEndo_node BT.leaf BT.leaf

/-- `cfpLift (cfpTerminalFrom _ ≫ treeFalse)
(cfpSnd _ _)` in `Type u` sends `(x, y)` to
`(treeFalseBT, y)`. -/
private theorem cfpLift_tf_snd_eval
    (x y : BT.{u}) :
    ((cfpLift (cfpTerminalFrom (cfpProd BT BT) ≫
        treeFalse)
      (cfpSnd BT.{u} BT.{u}) :
      cfpProd BT.{u} BT.{u} ⟶
        cfpProd BT.{u} BT.{u}) :
      BT × BT → BT × BT)
      (x, y) = (treeFalseBT, y) := by
  unfold cfpLift
  rfl

/-- `cfpTerminalFrom _ ≫ treeFalse` in `Type u`
sends any input to `treeFalseBT`. -/
private theorem cfpTerminalFrom_treeFalse_eval
    (x : BT.{u} × BT.{u}) :
    ((cfpTerminalFrom (cfpProd BT.{u} BT.{u}) ≫
      treeFalse :
      cfpProd BT BT ⟶ BT) :
      BT × BT → BT)
      x = treeFalseBT := by
  unfold cfpTerminalFrom treeFalse cfpLift
  rfl

/-- Applying the categorical `boolAnd` in `Type u`
to `(treeFalseBT, y)` for any `y` returns
`treeFalseBT`. -/
private theorem boolAnd_treeFalseBT_any_eval
    (y : BT.{u}) :
    ((boolAnd (C := Type u)) : BT × BT → BT)
      (treeFalseBT, y) = treeFalseBT := by
  have h := boolAnd_treeFalse_left
    (C := Type u) (cfpSnd BT.{u} BT.{u})
  have heval := congrFun h
    ((treeFalseBT, y) : BT.{u} × BT.{u})
  rw [type_comp_apply] at heval
  rw [cfpLift_tf_snd_eval treeFalseBT y] at heval
  rw [cfpTerminalFrom_treeFalse_eval
    ((treeFalseBT, y) : BT.{u} × BT.{u})] at heval
  exact heval

theorem boolAndBT_leaf_treeFalseBT :
    boolAndBT (BT.leaf : BT.{u}) treeFalseBT =
      treeFalseBT := by
  unfold treeFalseBT
  exact boolAndBT_leaf_node BT.leaf BT.leaf

theorem boolAndBT_treeFalseBT_any (y : BT.{u}) :
    boolAndBT treeFalseBT y = treeFalseBT := by
  unfold treeFalseBT
  exact boolAndBT_node_any BT.leaf BT.leaf y

/-- The categorical `boolAnd` on `Type u`, applied to
a pair of Boolean-valued (i.e., `BT.leaf` or
`treeFalseBT`) inputs, produces the same result as
`boolAndBT`. -/
private theorem boolAnd_on_bool_values
    (a b : BT.{u})
    (ha : a = BT.leaf ∨ a = treeFalseBT)
    (hb : b = BT.leaf ∨ b = treeFalseBT) :
    ((boolAnd (C := Type u)) : BT × BT → BT)
      (a, b) = boolAndBT a b := by
  rcases ha with ha | ha <;>
  rcases hb with hb | hb <;>
  subst ha <;> subst hb
  · rw [boolAndBT_leaf_leaf, boolAnd_leaf_leaf_eval]
  · rw [boolAndBT_leaf_treeFalseBT,
      boolAnd_leaf_treeFalseBT_eval]
  · rw [boolAndBT_treeFalseBT_any,
      boolAnd_treeFalseBT_any_eval]
  · rw [boolAndBT_treeFalseBT_any,
      boolAnd_treeFalseBT_any_eval]

theorem typeTreeEq_ββ :
    cfpMap
      (HasPBTO.β : cfpProd BT.{u} BT.{u} ⟶ BT.{u})
      (HasPBTO.β : cfpProd BT.{u} BT.{u} ⟶ BT.{u}) ≫
      typeTreeEq =
    cfpLift
      (cfpLift
        (cfpFst (cfpProd BT.{u} BT.{u})
          (cfpProd BT.{u} BT.{u}) ≫
          cfpFst BT.{u} BT.{u})
        (cfpSnd (cfpProd BT.{u} BT.{u})
          (cfpProd BT.{u} BT.{u}) ≫
          cfpFst BT.{u} BT.{u}) ≫ typeTreeEq)
      (cfpLift
        (cfpFst (cfpProd BT.{u} BT.{u})
          (cfpProd BT.{u} BT.{u}) ≫
          cfpSnd BT.{u} BT.{u})
        (cfpSnd (cfpProd BT.{u} BT.{u})
          (cfpProd BT.{u} BT.{u}) ≫
          cfpSnd BT.{u} BT.{u}) ≫ typeTreeEq)
    ≫ boolAnd := by
  funext ⟨⟨a, b⟩, c, d⟩
  change treeEqBT (BT.node a b) (BT.node c d) =
    ((boolAnd (C := Type u)) : BT × BT → BT)
      (treeEqBT a c, treeEqBT b d)
  rw [treeEqBT_node_node]
  rw [boolAnd_on_bool_values _ _
    (treeEqBT_is_bool a c)
    (treeEqBT_is_bool b d)]

/-- `Type u` has structural tree equality. -/
def hasTreeEq_type : HasTreeEq (Type u) where
  treeEq := typeTreeEq
  treeEq_bool := typeTreeEq_bool
  treeEq_refl := typeTreeEq_refl
  treeEq_symm := typeTreeEq_symm
  treeEq_trans := typeTreeEq_trans
  treeEq_ℓℓ := typeTreeEq_ℓℓ
  treeEq_ℓβ := typeTreeEq_ℓβ
  treeEq_βℓ := typeTreeEq_βℓ
  treeEq_ββ := typeTreeEq_ββ

end GebLean
