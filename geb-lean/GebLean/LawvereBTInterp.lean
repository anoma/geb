import GebLean.LawvereBTQuot
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Interpretation of the Lawvere Theory into Type

Defines a functor from `LawvereBTQuotCat` (the
Lawvere theory of parameterized binary tree objects)
into `Type u` for an arbitrary universe `u`.

The interpretation `BTMor1.interpU` and its
computation lemmas for proj, leaf, and branch are
in `LawvereBT.lean`.  The fold computation lemma
(`interpU_fold`) is deferred pending resolution
of a transport issue in `polyFixChildAt`.

This file will contain:
- Soundness (btMorRel implies equal interpU)
- The functor LawvereBTQuotCat ⥤ Type u
- Faithfulness of the functor

These all depend on `interpU_fold`.
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## BT.fold computation lemmas -/

/-- `BT.fold` on `BT.leaf` returns the base
value. -/
theorem BT.fold_leaf {α : Type u}
    (b : α) (s : α → α → α) :
    BT.fold b s BT.leaf = b := by
  unfold BT.fold BT.leaf
    polyProdFreeMFoldAt
    polyFreeMapAt
  simp only [polyFreeM_pure_bind]
  unfold polyFreeMPure polyFreeCounitFoldAt
  rfl

/-- `BT.fold` on `BT.node` applies the step
function to the recursive results. -/
theorem BT.fold_node {α : Type u}
    (b : α) (s : α → α → α)
    (l r : BT.{u}) :
    BT.fold b s (BT.node l r) =
      s (BT.fold b s l)
        (BT.fold b s r) := by
  rfl

/-! ## BT structural lemmas -/

/-- `BT.leaf` and `BT.node` produce different
`PolyFix` shapes and are therefore distinct. -/
private theorem bt_leaf_index_eq :
    (BT.leaf : BT.{u}).index =
    Sum.inl ⟨PUnit.unit, rfl⟩ := by
  unfold BT.leaf polyFreeMPure
  rfl

private theorem bt_node_index_eq
    (l r : BT.{u}) :
    (BT.node l r).index =
    Sum.inr PUnit.unit := by
  unfold BT.node polyProdFreeMNode
    polyFreeMStrFamily
  rfl

theorem BT.leaf_ne_node
    {l r : BT.{u}} :
    BT.leaf ≠ BT.node l r := by
  intro h
  have hi := congrArg PolyFix.index h
  rw [bt_leaf_index_eq,
    bt_node_index_eq] at hi
  exact absurd hi (fun h => nomatch h)

/-! ## Fold eta lemma

The fold with the identity base/step is the
identity on BT. -/

/-- Folding with the identity algebra
(base = leaf, step = node) recovers the
original tree. -/
private theorem fold_eta_gen
    {x : PUnit.{u + 1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{u + 1})
      polyProdType x) :
    BT.fold BT.leaf BT.node bt = bt := by
  induction bt with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      unfold BT.fold polyProdFreeMFoldAt
        polyFreeMapAt
      simp only [polyFreeMBind, polyFreeMPure,
        polyFreeCounitFoldAt]
      -- LHS reduces to BT.leaf.
      change BT.leaf =
        PolyFix.mk y
          (show polyBetweenIndex PUnit PUnit
            (polyTranslate
              (overTerminal PUnit.{u + 1})
              polyProdType) y from
            Sum.inl leafIdx)
          children
      unfold BT.leaf polyFreeMPure
      -- Both sides are PolyFix.mk; use congr.
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      congr 1
      funext e; exact PEmpty.elim e
    | Sum.inr nodeIdx =>
      -- Node case.
      -- The fold on a Sum.inr node recurses into
      -- children and applies the step (BT.node).
      -- By IH, folding each child is the identity.
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      -- Now show PolyFix.mk equals BT.node of
      -- children at left and right.
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
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
      rw [hmk, BT.fold_node,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit),
        ← hmk]

private theorem fold_eta_aux
    (bt : BT.{u}) :
    BT.fold BT.leaf BT.node bt = bt :=
  fold_eta_gen bt

/-- A fold homomorphism lemma: if `h` preserves
base and step, then `h ∘ fold b s = fold (h b)
(fun l r => h (s (... l) (... r)))`. We prove
the special case needed for fold eta. -/
private theorem fold_eval_at_zero_gen
    {x : PUnit.{u + 1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{u + 1})
      polyProdType x) :
    BT.fold
      (fun (_ : Fin 1) => BT.leaf)
      (fun l r (_ : Fin 1) =>
        BT.node (l ⟨0, by omega⟩)
          (r ⟨0, by omega⟩))
      bt ⟨0, by omega⟩ =
    BT.fold BT.leaf BT.node bt := by
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
        funext e; exact PEmpty.elim e
      rw [hmk, BT.fold_leaf, BT.fold_leaf]
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
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
      rw [hmk, BT.fold_node, BT.fold_node]
      congr 1
      · exact ih (Sum.inl PUnit.unit)
      · exact ih (Sum.inr PUnit.unit)

private theorem fold_eta_fin1
    (bt : BT.{u}) :
    BT.fold
      (fun (_ : Fin 1) => BT.leaf)
      (fun l r (_ : Fin 1) =>
        BT.node (l ⟨0, by omega⟩)
          (r ⟨0, by omega⟩))
      bt ⟨0, by omega⟩ = bt := by
  rw [fold_eval_at_zero_gen, fold_eta_aux]

/-! ## BT structural lemmas (continued) -/

/-- `BT.node` is injective: equal nodes have
equal left and right children. -/
private theorem bt_node_eq_mk
    (l r : BT.{u}) :
    BT.node l r =
    PolyFix.mk PUnit.unit
      (show polyBetweenIndex PUnit PUnit
        (polyTranslate
          (overTerminal PUnit.{u + 1})
          polyProdType) PUnit.unit from
        Sum.inr PUnit.unit)
      (fun e => match e with
        | Sum.inl _ => l
        | Sum.inr _ => r) := by
  unfold BT.node polyProdFreeMNode
    polyFreeMStrFamily
  simp only
  congr 1
  funext e
  match e with
  | Sum.inl _ => rfl
  | Sum.inr _ => rfl

theorem BT.node_inj
    {l1 r1 l2 r2 : BT.{u}}
    (h : BT.node l1 r1 = BT.node l2 r2) :
    l1 = l2 ∧ r1 = r2 := by
  rw [bt_node_eq_mk, bt_node_eq_mk] at h
  have hc := eq_of_heq (PolyFix.mk.inj h).2
  constructor
  · exact congrFun hc (Sum.inl PUnit.unit)
  · exact congrFun hc (Sum.inr PUnit.unit)

/-- Case analysis on BT: every tree is either
`BT.leaf` or `BT.node l r`. -/
theorem BT.cases {P : BT.{u} → Prop}
    (hleaf : P BT.leaf)
    (hnode : ∀ (l r : BT.{u}),
      P (BT.node l r))
    (bt : BT.{u}) : P bt := by
  match bt with
  | PolyFix.mk y idx children =>
    have hy : y = PUnit.unit :=
      PUnit.eq_punit y
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
        funext e; exact PEmpty.elim e
      rw [hmk]; exact hleaf
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node
            (children (Sum.inl PUnit.unit))
            (children
              (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk]; exact hnode _ _

private theorem BT.ind_gen
    {motive : BT.{u} → Prop}
    (leaf : motive BT.leaf)
    (node : ∀ (l r : BT.{u}),
      motive l → motive r → motive (BT.node l r))
    {x : PUnit.{u + 1}}
    (t : PolyFreeM
      (overTerminal PUnit.{u + 1})
      polyProdType x) : motive t := by
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
        funext e; exact PEmpty.elim e
      rw [hmk]; exact leaf
    | Sum.inr nodeIdx =>
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
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
      exact node _ _
        (ih (Sum.inl PUnit.unit))
        (ih (Sum.inr PUnit.unit))

/-- Structural induction on BT: a predicate holding
at `BT.leaf` and preserved by `BT.node` given
inductive hypotheses on both children holds on every
tree. -/
theorem BT.ind {motive : BT.{u} → Prop}
    (leaf : motive BT.leaf)
    (node : ∀ (l r : BT.{u}),
      motive l → motive r → motive (BT.node l r))
    (t : BT.{u}) : motive t :=
  BT.ind_gen leaf node t

/-- Quotation: embed a ground `BT` tree as a
`BTMor1 n` term (leaf → `BTMor1.leaf`,
node → `BTMor1.branch`). -/
def quoteBT {n : ℕ} :
    BT.{0} → BTMor1 n :=
  BT.fold BTMor1.leaf BTMor1.branch

/-- Interpreting a quoted BT tree recovers the
original tree. -/
private theorem quoteBT_interpU_gen {n : ℕ}
    {x : PUnit.{1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x)
    (ctx : Fin n → BT.{0}) :
    (BT.fold BTMor1.leaf BTMor1.branch
      bt).interpU ctx = bt := by
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
      have hmk :
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
      rw [hmk, BT.fold_leaf,
        BTMor1.interpU_leaf]
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
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
            (children
              (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, BT.fold_node,
        BTMor1.interpU_branch,
        ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit),
        ← hmk]

theorem quoteBT_interpU {n : ℕ}
    (bt : BT.{0})
    (ctx : Fin n → BT.{0}) :
    (quoteBT bt).interpU ctx = bt :=
  quoteBT_interpU_gen bt ctx

/-! ## Fold uniqueness at the interpretation level

The fold uniqueness constructor `btMorRel.foldUniq`
states that any morphism tuple satisfying the leaf
and branch computation rules equals the fold. At
the interpretation level, this becomes a statement
about `BT.fold` being the unique catamorphism. -/

private theorem fold_uniq_interp_gen
    {n_inner m k : ℕ}
    (φ : Fin m → BTMor1 (n_inner + 1))
    (f : Fin m → BTMor1 n_inner)
    (g : Fin m → BTMor1 (m + m))
    (σ : Fin n_inner → BTMor1 k)
    (ctx : Fin k → BT.{u})
    (hℓ_ih :
      ∀ (j : Fin m) (ctx' : Fin k → BT.{u}),
        ((φ j).subst
          (btSubstSnoc σ BTMor1.leaf)).interpU
            ctx' =
          ((f j).subst σ).interpU ctx')
    (hβ_ih :
      ∀ (j : Fin m)
        (ctx' : Fin (k + 2) → BT.{u}),
        ((φ j).subst
          (btSubstSnoc (btSubstEmbed 2 σ)
            (BTMor1.branch
              (BTMor1.proj ⟨k, by omega⟩)
              (BTMor1.proj
                ⟨k + 1, by omega⟩)))).interpU
            ctx' =
          ((g j).subst
            (btFoldBranchSubstPhi φ σ)).interpU
              ctx')
    {x : PUnit.{u + 1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{u + 1})
      polyProdType x)
    (j : Fin m) :
    (φ j).interpU
      (Fin.lastCases bt
        (fun v => (σ v).interpU ctx)) =
    BT.fold
      (fun i => ((f i).subst σ).interpU ctx)
      (fun leftAll rightAll j' =>
        (g j').interpU
          (finAppend leftAll rightAll))
      bt j := by
  -- Generalize over j before inducting on bt,
  -- so the IH holds for all j.
  revert j
  induction bt with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      intro j
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
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
        funext e; exact PEmpty.elim e
      rw [hmk, BT.fold_leaf]
      rw [← hℓ_ih j ctx,
        BTMor1.interpU_subst]
      congr 1; funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [btSubstSnoc_last,
          BTMor1.interpU_leaf]
      · intro v
        simp [btSubstSnoc_castSucc]
    | Sum.inr nodeIdx =>
      intro j
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{u + 1})
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
      rw [hmk, BT.fold_node]
      set lc := children (Sum.inl PUnit.unit)
      set rc := children (Sum.inr PUnit.unit)
      set σ_ctx := fun v => (σ v).interpU ctx
      set base := fun i =>
        ((f i).subst σ).interpU ctx
      set step := fun leftAll rightAll
        (j' : Fin m) =>
        (g j').interpU
          (finAppend leftAll rightAll)
      -- Use hβ_ih with ctx' extending ctx by
      -- lc and rc.
      set ctx' : Fin (k + 2) → BT.{u} :=
        fun i =>
          if h : i.val < k
          then ctx ⟨i.val, h⟩
          else if i.val = k then lc else rc
      -- Step 1: LHS equals LHS of hβ_ih.
      trans ((φ j).subst
        (btSubstSnoc (btSubstEmbed 2 σ)
          (BTMor1.branch
            (BTMor1.proj ⟨k, by omega⟩)
            (BTMor1.proj
              ⟨k + 1,
                by omega⟩)))).interpU ctx'
      · rw [BTMor1.interpU_subst]
        congr 1; funext i
        refine Fin.lastCases ?_ ?_ i
        · -- i = last: branch
          simp only [Fin.lastCases_last,
            btSubstSnoc_last,
            BTMor1.interpU_branch,
            BTMor1.interpU_proj]
          simp only [ctx']
          congr 1
          · simp
          · simp [show ¬ (k + 1 < k) by omega]
        · -- i = castSucc v: embedded σ
          intro v
          simp only [Fin.lastCases_castSucc,
            btSubstSnoc_castSucc,
            btSubstEmbed,
            BTMor1.interpU_subst,
            BTMor1.interpU_proj]
          simp only [σ_ctx]
          congr 1; funext u
          simp only [ctx']
          simp [show u.val < k from u.isLt]
      -- Step 2: Apply hβ_ih.
      · rw [hβ_ih j ctx']
        -- Step 3: RHS of hβ_ih equals RHS.
        rw [BTMor1.interpU_subst]
        congr 1; funext i
        unfold btFoldBranchSubstPhi
        split
        · -- i.val < m: fold on lc
          rename_i hlt
          rw [BTMor1.interpU_subst]
          -- RHS: finAppend unfolds to the left
          -- fold since i.val < m.
          have hfa : finAppend
              (BT.fold base step lc)
              (BT.fold base step rc) i =
            BT.fold base step lc
              ⟨i.val, hlt⟩ := by
            simp [finAppend, hlt]
          rw [hfa, ← ih (Sum.inl PUnit.unit)
            ⟨i.val, hlt⟩]
          -- Show the contexts match.
          congr 1; funext v'
          refine Fin.lastCases ?_ ?_ v'
          · simp only [Fin.lastCases_last,
              btSubstSnoc_last,
              BTMor1.interpU_proj, ctx',
              lc]
            simp
          · intro w
            simp only [Fin.lastCases_castSucc,
              btSubstSnoc_castSucc,
              btSubstEmbed,
              BTMor1.interpU_subst,
              BTMor1.interpU_proj,
              σ_ctx, ctx']
            congr 1; funext u
            simp [show u.val < k from u.isLt]
        · -- i.val >= m: fold on rc
          rename_i hge
          rw [BTMor1.interpU_subst]
          have hfa : finAppend
              (BT.fold base step lc)
              (BT.fold base step rc) i =
            BT.fold base step rc
              ⟨i.val - m, by omega⟩ := by
            simp [finAppend, hge]
          rw [hfa, ← ih (Sum.inr PUnit.unit)
            ⟨i.val - m, by omega⟩]
          congr 1; funext v'
          refine Fin.lastCases ?_ ?_ v'
          · simp only [Fin.lastCases_last,
              btSubstSnoc_last,
              BTMor1.interpU_proj, ctx',
              rc]
            simp [show ¬ (k + 1 < k) by omega]
          · intro w
            simp only [Fin.lastCases_castSucc,
              btSubstSnoc_castSucc,
              btSubstEmbed,
              BTMor1.interpU_subst,
              BTMor1.interpU_proj,
              σ_ctx, ctx']
            congr 1; funext u
            simp [show u.val < k from u.isLt]

/-! ## Universe-polymorphic surjectivity -/

/-- Every `BT.{u}` value is the interpretation
of some closed `BTMor1 0` term. -/
private theorem interpU_surjective
    {x : PUnit.{u + 1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{u + 1})
      polyProdType x) :
    ∃ t : BTMor1 0,
    t.interpU (Fin.elim0 (α := BT.{u})) =
      bt := by
  induction bt with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      have hy := PUnit.eq_punit y; subst hy
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      exact ⟨BTMor1.leaf, by
        rw [BTMor1.interpU_leaf]
        unfold BT.leaf polyFreeMPure
        congr 1; funext e
        exact PEmpty.elim e⟩
    | Sum.inr nodeIdx =>
      have hy := PUnit.eq_punit y; subst hy
      have hni := PUnit.eq_punit nodeIdx
      subst hni
      obtain ⟨tl, hl⟩ :=
        ih (Sum.inl PUnit.unit)
      obtain ⟨tr, hr⟩ :=
        ih (Sum.inr PUnit.unit)
      exact ⟨BTMor1.branch tl tr, by
        rw [BTMor1.interpU_branch, hl, hr]
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only; congr 1; ext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl⟩

/-- Constructive finite choice: from pointwise
existence over `Fin n`, extract a function. -/
private theorem fin_choice {n : ℕ}
    {α : Type} {P : Fin n → α → Prop}
    (h : ∀ i, ∃ a, P i a) :
    ∃ f : Fin n → α, ∀ i, P i (f i) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨a_last, h_last⟩ :=
      h (Fin.last k)
    obtain ⟨f_rest, h_rest⟩ := ih
      (fun i => h (Fin.castSucc i))
    refine ⟨Fin.lastCases a_last f_rest,
      fun i => ?_⟩
    refine Fin.lastCases ?_ ?_ i
    · simp only [Fin.lastCases_last]
      exact h_last
    · intro j
      simp only [Fin.lastCases_castSucc]
      exact h_rest j

/-! ## Soundness -/

/-- `btMorRel`-equivalent terms have equal
interpretations: the standard model `BT` satisfies
all fold equations. -/
theorem interpU_sound {n : ℕ}
    {t1 t2 : BTMor1 n}
    (h : btMorRel n t1 t2)
    (ctx : Fin n → BT.{u}) :
    t1.interpU ctx = t2.interpU ctx := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih ctx).symm
  | trans _ _ ih1 ih2 =>
    exact (ih1 ctx).trans (ih2 ctx)
  | congBranch _ _ ihl ihr =>
    simp only [BTMor1.interpU_branch]
    exact congrArg₂ BT.node (ihl ctx)
      (ihr ctx)
  | @congFold _ m _ f f' g g' tree tree'
      _ _ _ ihf ihg iht =>
    rw [BTMor1.interpU_fold, BTMor1.interpU_fold]
    apply congr_fun; congr 1
    · funext i; exact ihf i ctx
    · funext l r j'; exact ihg j' _
    · exact iht ctx
  | foldLeaf =>
    rw [BTMor1.interpU_fold, BTMor1.interpU_leaf]
    exact congrFun (BT.fold_leaf _ _) _
  | @foldBranch _ m j f g t1' t2' =>
    rw [BTMor1.interpU_fold,
      BTMor1.interpU_branch,
      BT.fold_node,
      BTMor1.interpU_subst]
    congr 1; funext i
    simp only [finAppend]
    split
    · rw [BTMor1.interpU_fold]
    · rw [BTMor1.interpU_fold]
  | foldEta =>
    rw [BTMor1.interpU_fold]
    -- After interpU_fold, the LHS is a BT.fold
    -- at type (Fin 1 → BT) evaluated at ⟨0, _⟩.
    -- The base and step match the identity algebra
    -- at the BT level.
    -- First, show the step matches the expected
    -- form for fold_eta_fin1.
    change BT.fold
      (fun (_ : Fin 1) => BT.leaf)
      (fun l r (_ : Fin 1) =>
        BT.node (l ⟨0, by omega⟩)
          (r ⟨0, by omega⟩))
      _ ⟨0, by omega⟩ = _
    exact fold_eta_fin1 _
  | substReflect hground ih_ground =>
    -- The IH gives: for each ground σ,
    -- (t1.subst σ).interpU ctx' =
    -- (t2.subst σ).interpU ctx'.
    -- By interpU_surjective (constructive),
    -- each ctx i is the interpU of some
    -- closed term.
    -- By interpU_surjective + fin_choice:
    -- extract σ with (σ i).interpU = ctx i.
    obtain ⟨σ, hσ⟩ := fin_choice
      (fun i => interpU_surjective (ctx i))
    rw [show ctx = (fun i =>
        (σ i).interpU Fin.elim0) from
        (funext hσ).symm,
      ← BTMor1.interpU_subst,
      ← BTMor1.interpU_subst]
    exact ih_ground σ
      (Fin.elim0 (α := BT.{u}))
  | @foldUniq n_inner m j φ f g k σ tree
      hℓ hβ hℓ_ih hβ_ih =>
    rw [BTMor1.interpU_subst,
      BTMor1.interpU_fold]
    -- The LHS context uses btSubstSnoc σ tree;
    -- convert to Fin.lastCases.
    conv_lhs =>
      arg 2; ext i
      rw [show (btSubstSnoc σ tree i).interpU
        ctx = Fin.lastCases (tree.interpU ctx)
          (fun v => (σ v).interpU ctx) i from by
        refine Fin.lastCases ?_ ?_ i
        · simp [btSubstSnoc_last]
        · intro v
          simp [btSubstSnoc_castSucc]]
    exact fold_uniq_interp_gen φ f g σ ctx
      hℓ_ih hβ_ih (tree.interpU ctx) j

/-! ## Lifting interpU through the quotient -/

/-- The interpretation of a quotient morphism:
lifts `BTMorN.interpU` through the quotient. -/
def BTMorNQuo.interpU {n m : ℕ}
    (f : BTMorNQuo n m)
    (ctx : Fin n → BT.{u}) :
    Fin m → BT.{u} :=
  Quotient.lift
    (s := btMorNSetoid n m)
    (fun f_raw => BTMorN.interpU f_raw ctx)
    (fun _ _ h =>
      funext fun j => interpU_sound (h j) ctx)
    f

/-- `interpU` on the identity quotient morphism
is the identity function on contexts. -/
theorem BTMorNQuo.interpU_id (n : ℕ)
    (ctx : Fin n → BT.{u}) :
    BTMorNQuo.interpU (BTMorNQuo.id n) ctx =
    ctx := by
  funext j
  exact BTMor1.interpU_proj j ctx

/-- `interpU` on a composition of quotient
morphisms equals composition of the
interpretations. -/
theorem BTMorNQuo.interpU_comp {n m k : ℕ}
    (f : BTMorNQuo n m) (g : BTMorNQuo m k)
    (ctx : Fin n → BT.{u}) :
    BTMorNQuo.interpU
      (BTMorNQuo.comp f g) ctx =
    BTMorNQuo.interpU g
      (BTMorNQuo.interpU f ctx) := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  funext j
  exact BTMor1.interpU_subst (g_raw j)
    f_raw ctx

/-! ## The interpretation functor -/

/-- The interpretation functor from the Lawvere
theory of parameterized binary tree objects
into `Type u`. Maps object `n` to the type
`Fin n → BT.{u}` and each morphism class to the
corresponding function on contexts. -/
def interpFunctor : LawvereBTQuotCat ⥤
    Type u where
  obj n := Fin n → BT.{u}
  map f := BTMorNQuo.interpU f
  map_id n := by
    funext ctx j
    exact congrFun
      (BTMorNQuo.interpU_id n ctx) j
  map_comp f g := by
    funext ctx j
    exact congrFun
      (BTMorNQuo.interpU_comp f g ctx) j

/-! ## Faithfulness

The interpretation functor is faithful: distinct
morphism classes in `LawvereBTQuotCat` produce
distinct functions on contexts. Equivalently,
the standard model `BT` is complete for the
equational theory `btMorRel`. -/

/-! ### Completeness: helper lemmas -/

/-- Distinguishing context for `Fin` indices:
maps `i` to a node and everything else to leaf.
Used to discriminate between projections. -/
private def distinguishCtx {n : ℕ}
    (i : Fin n) : Fin n → BT.{0} :=
  fun j =>
    if j = i then BT.node BT.leaf BT.leaf
    else BT.leaf

private theorem distinguishCtx_self
    {n : ℕ} (i : Fin n) :
    distinguishCtx i i =
      BT.node BT.leaf BT.leaf := by
  simp [distinguishCtx]

private theorem distinguishCtx_ne
    {n : ℕ} (i j : Fin n) (h : j ≠ i) :
    distinguishCtx i j = BT.leaf := by
  simp [distinguishCtx, h]

/-- `BT.node l r ≠ BT.leaf`. -/
private theorem BT.node_ne_leaf
    {l r : BT.{u}} :
    BT.node l r ≠ BT.leaf :=
  fun h => BT.leaf_ne_node h.symm

/-- If `∀ ctx, ctx i = ctx j`, then `i = j`. -/
private theorem fin_eq_of_ctx_eq {n : ℕ}
    (i j : Fin n)
    (h : ∀ ctx : Fin n → BT.{0},
      ctx i = ctx j) :
    i = j := by
  by_contra hne
  have hd := h (distinguishCtx i)
  simp only [distinguishCtx] at hd
  simp only [if_true] at hd
  simp only [show ¬(j = i) from
    Ne.symm hne, if_false] at hd
  exact absurd hd BT.node_ne_leaf

/-- A projection cannot be constantly leaf. -/
private theorem proj_ne_const_leaf
    {n : ℕ}
    (i : Fin n)
    (h : ∀ ctx : Fin n → BT.{0},
      ctx i = BT.leaf) : False := by
  have hd := h (distinguishCtx i)
  simp only [distinguishCtx, if_true] at hd
  exact absurd hd BT.node_ne_leaf

/-- A projection cannot be constantly a node. -/
private theorem proj_ne_const_node
    {n : ℕ}
    (i : Fin n)
    {l r : BT.{0}}
    (h : ∀ ctx : Fin n → BT.{0},
      ctx i = BT.node l r) :
    False := by
  have hd := h (fun _ => BT.leaf)
  exact absurd hd BT.leaf_ne_node

/-- If a node interpretation equals `BT.leaf`,
this is a contradiction. -/
private theorem node_interp_ne_leaf
    {n : ℕ} (l r : BTMor1 n)
    (ctx : Fin n → BT.{0})
    (h : BT.node (l.interpU ctx)
      (r.interpU ctx) = BT.leaf) :
    False :=
  absurd h BT.node_ne_leaf

/-- If `BT.leaf` equals a node interpretation,
this is a contradiction. -/
private theorem leaf_ne_node_interp
    {n : ℕ} (l r : BTMor1 n)
    (ctx : Fin n → BT.{0})
    (h : BT.leaf = BT.node (l.interpU ctx)
      (r.interpU ctx)) :
    False :=
  absurd h BT.leaf_ne_node

/-- `quoteBT` on `BT.leaf` returns
`BTMor1.leaf`. -/
private theorem quoteBT_leaf {n : ℕ} :
    (quoteBT (n := n) BT.leaf) =
      BTMor1.leaf := by
  unfold quoteBT
  exact BT.fold_leaf BTMor1.leaf BTMor1.branch

/-- `quoteBT` on `BT.node` returns a branch of
the quoted children. -/
private theorem quoteBT_node {n : ℕ}
    (l r : BT.{0}) :
    (quoteBT (n := n) (BT.node l r)) =
      BTMor1.branch (quoteBT l)
        (quoteBT r) := by
  unfold quoteBT
  exact BT.fold_node BTMor1.leaf
    BTMor1.branch l r

/-- Substitution commutes with fiber transport:
`(h ▸ t).subst σ = t.subst (fun v => σ (h ▸ v))`.
-/
private theorem subst_cast {a b m : ℕ}
    (h : a = b) (t : BTMor1 a)
    (σ : Fin b → BTMor1 m) :
    (h ▸ t).subst σ =
      t.subst (fun v => σ (h ▸ v)) := by
  cases h; rfl

/-- Fold-quoteBT commutation: applying a
syntactic fold to quoted arguments and then
comparing with the quotation of the semantic
fold.  Uses BT structural induction on the
tree argument.

The proof has two cases:
- Leaf: `foldLeaf` + `BT.fold_leaf`.
- Node: `foldBranch` + `BT.fold_node` +
  `subst_cong_left` + BT-IH on sub-trees. -/
private theorem norm0_fold_commute_gen
    {x : PUnit.{1}}
    (m : ℕ)
    (base : Fin m → BT.{0})
    (g : Fin m → BTMor1 (m + m))
    (ih_g : ∀ (j : Fin m)
      (σ : Fin (m + m) → BTMor1 0),
      (∀ i, btMorRel 0 (σ i)
        (quoteBT ((σ i).interpU
          Fin.elim0))) →
      btMorRel 0 ((g j).subst σ)
        (quoteBT (((g j).subst σ).interpU
          Fin.elim0)))
    (bt : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x)
    (j : Fin m) :
    btMorRel 0
      (BTMor1.fold m
        (fun i => quoteBT (base i))
        g (quoteBT bt) j)
      (quoteBT
        (BT.fold
          base
          (fun leftAll rightAll j' =>
            (g j').interpU
              (finAppend leftAll rightAll))
          bt j)) := by
  revert j
  induction bt with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      intro j
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType)
              PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e; exact PEmpty.elim e
      rw [hmk, BT.fold_leaf, quoteBT_leaf]
      exact btMorRel.foldLeaf m j
        (fun i => quoteBT (base i)) g
    | Sum.inr nodeIdx =>
      intro j
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType)
              PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node
            (children (Sum.inl PUnit.unit))
            (children
              (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, BT.fold_node,
        quoteBT_node]
      set lc :=
        children (Sum.inl PUnit.unit)
      set rc :=
        children (Sum.inr PUnit.unit)
      set stepFn :=
        fun leftAll rightAll
          (j' : Fin m) =>
          (g j').interpU
            (finAppend leftAll rightAll)
      apply btMorRel.trans
      · exact btMorRel.foldBranch m j
          (fun i => quoteBT (base i))
          g (quoteBT lc) (quoteBT rc)
      · set σ_fold :=
          fun (i : Fin (m + m)) =>
            if h : i.val < m
            then BTMor1.fold m
              (fun k => quoteBT (base k))
              g (quoteBT lc) ⟨i.val, h⟩
            else BTMor1.fold m
              (fun k => quoteBT (base k))
              g (quoteBT rc)
              ⟨i.val - m, by omega⟩
        set σ_quote :=
          fun (i : Fin (m + m)) =>
            quoteBT
              (finAppend
                (BT.fold base stepFn lc)
                (BT.fold base stepFn rc) i)
        have hσ_eq :
            ∀ i, btMorRel 0
              (σ_fold i) (σ_quote i) := by
          intro i
          simp only [σ_fold, σ_quote,
            finAppend]
          split
          · rename_i hlt
            exact ih (Sum.inl PUnit.unit)
              ⟨i.val, hlt⟩
          · rename_i hge
            exact ih (Sum.inr PUnit.unit)
              ⟨i.val - m, by omega⟩
        have hσ_quote_norm :
            ∀ i, btMorRel 0
              (σ_quote i)
              (quoteBT ((σ_quote i).interpU
                Fin.elim0)) := by
          intro i
          simp only [σ_quote]
          rw [quoteBT_interpU]
          exact btMorRel.refl _
        apply btMorRel.trans
        · exact subst_cong_left (g j) hσ_eq
        · have h_g :=
            ih_g j σ_quote hσ_quote_norm
          have hrw :
              ((g j).subst σ_quote).interpU
                Fin.elim0 =
              (g j).interpU
                (finAppend
                  (BT.fold base stepFn lc)
                  (BT.fold base
                    stepFn rc)) := by
            rw [BTMor1.interpU_subst]
            congr 1; funext i
            simp only [σ_quote]
            exact quoteBT_interpU _ _
          rw [hrw] at h_g
          exact h_g

private theorem norm0_fold_commute
    (m : ℕ)
    (base : Fin m → BT.{0})
    (g : Fin m → BTMor1 (m + m))
    (ih_g : ∀ (j : Fin m)
      (σ : Fin (m + m) → BTMor1 0),
      (∀ i, btMorRel 0 (σ i)
        (quoteBT ((σ i).interpU
          Fin.elim0))) →
      btMorRel 0 ((g j).subst σ)
        (quoteBT (((g j).subst σ).interpU
          Fin.elim0)))
    (bt : BT.{0})
    (j : Fin m) :
    btMorRel 0
      (BTMor1.fold m
        (fun i => quoteBT (base i))
        g (quoteBT bt) j)
      (quoteBT
        (BT.fold
          base
          (fun leftAll rightAll j' =>
            (g j').interpU
              (finAppend leftAll rightAll))
          bt j)) :=
  norm0_fold_commute_gen m base g ih_g bt j

set_option backward.isDefEq.respectTransparency false in
/-- Ground normalization: every `BTMor1 k` term,
when substituted with ground values satisfying
the normalization property, is `btMorRel 0`
to the quotation of its ground interpretation.

The motive for `BTMor1.ind` carries the
hypothesis on σ through all fibers, giving
interpU_complete for ALL fibers in one pass. -/
private theorem norm0_gen :
    ∀ {k : ℕ} (t : BTMor1 k)
      (σ : Fin k → BTMor1 0),
      (∀ i, btMorRel 0 (σ i)
        (quoteBT ((σ i).interpU
          (Fin.elim0 (α := BT.{0}))))) →
      btMorRel 0 (t.subst σ)
        (quoteBT ((t.subst σ).interpU
          (Fin.elim0 (α := BT.{0})))) :=
  fun t => BTMor1.ind
    (motive := fun {k} (t : BTMor1 k) =>
      ∀ (σ : Fin k → BTMor1 0),
        (∀ i, btMorRel 0 (σ i)
          (quoteBT ((σ i).interpU
            Fin.elim0))) →
        btMorRel 0 (t.subst σ)
          (quoteBT ((t.subst σ).interpU
            Fin.elim0)))
    (step := fun i => match i with
      | ⟨0, _⟩ =>
        -- proj case: result is σ i, use hσ
        fun p _ _ σ hσ =>
          hσ (p.property ▸ p.val.2)
      | ⟨1, _⟩ =>
        -- leaf case: leaf.subst σ = leaf,
        -- quoteBT BT.leaf = leaf, so refl
        fun _ _ _ _ _ =>
          btMorRel.refl _
      | ⟨2, _⟩ =>
        -- branch case: congBranch + IH
        fun _ children ih σ hσ => by
          rename_i ni _
          set lhs := BTMor1.subst _ σ
            with hlhs
          unfold BTMor1.subst BTMor1.ind
            PolyFixCoprod.ind PolyFix.ind
            at hlhs
          dsimp only at hlhs
          set rhs_interpU :=
            BTMor1.interpU lhs Fin.elim0
            with hrhs
          rw [hlhs] at hrhs
          simp only [BTMor1.interpU_branch]
            at hrhs
          rw [hlhs, hrhs, quoteBT_node]
          exact btMorRel.congBranch
            (ih (Sum.inl PUnit.unit) σ hσ)
            (ih (Sum.inr PUnit.unit) σ hσ)
      | ⟨3, _⟩ =>
        -- fold case
        fun pos children ih σ hσ => by
          rename_i ni _
          let pm := pos.1
          let pj := pos.2
          have hlb (i : Fin pm) :
              i.val < pm + pm + 1 :=
            Nat.lt_of_lt_of_le i.isLt
              (Nat.le_add_right
                pm (pm + 1))
          have hls (i : Fin pm) :
              pm + i.val < pm + pm + 1 :=
            by omega
          have hlt :
              pm + pm < pm + pm + 1 :=
            Nat.lt_succ_self _
          have hbf (i : Fin pm) :
              (polyBetweenFamily ℕ ℕ
                (btMorComponents
                  ⟨3, by omega⟩)
                ni pos).hom
                ⟨i.val, hlb i⟩ = ni := by
            unfold btMorComponents
              btMorFoldPoly
              polyBetweenFamily
              polyToOverFamily ccrObjMk
              ccrFamily; dsimp
            split_ifs <;> omega
          have hsf (i : Fin pm) :
              (polyBetweenFamily ℕ ℕ
                (btMorComponents
                  ⟨3, by omega⟩)
                ni pos).hom
                ⟨pm + i.val, hls i⟩ =
                  pm + pm := by
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
                ni pos).hom
                ⟨pm + pm, hlt⟩ = ni := by
            unfold btMorComponents
              btMorFoldPoly
              polyBetweenFamily
              polyToOverFamily ccrObjMk
              ccrFamily; dsimp
            split_ifs <;> omega
          -- Unfold subst to expose the fold.
          set lhs := BTMor1.subst _ σ
            with hlhs
          unfold BTMor1.subst BTMor1.ind
            PolyFixCoprod.ind PolyFix.ind
            at hlhs
          dsimp only at hlhs
          -- Unfold interpU to expose BT.fold.
          set rhs_interpU :=
            BTMor1.interpU lhs Fin.elim0
            with hrhs
          rw [hlhs] at hrhs
          rw [BTMor1.interpU_fold] at hrhs
          -- Now lhs is a fold and rhs_interpU
          -- is a BT.fold.
          rw [hlhs, hrhs]
          -- Goal: btMorRel 0 (fold pm f' g' tree' pj)
          --   (quoteBT (BT.fold base step bt pj))
          -- where f' i = (children ⟨i,_⟩).subst σ_i
          -- Use congFold to reduce to norm on
          -- base/tree children, then
          -- norm0_fold_commute.
          set f' := fun (i : Fin pm) =>
            (children ⟨i.val, hlb i⟩).subst
              (fun v => σ (hbf i ▸ v))
          set g' := fun (i : Fin pm) =>
            (hsf i ▸ children
              ⟨pm + i.val, hls i⟩ :
              BTMor1 (pm + pm))
          set tree' :=
            (children ⟨pm + pm, hlt⟩).subst
              (fun v => σ (htf ▸ v))
          set base' := fun (i : Fin pm) =>
            (f' i).interpU Fin.elim0
          set stepFn :=
            fun leftAll rightAll
              (j' : Fin pm) =>
              (g' j').interpU
                (finAppend leftAll rightAll)
          set bt' := tree'.interpU Fin.elim0
          -- IH on base children:
          have ih_base (i : Fin pm) :
              btMorRel 0 (f' i)
                (quoteBT (base' i)) :=
            ih ⟨i.val, hlb i⟩
              (fun v => σ (hbf i ▸ v))
              (fun v => hσ (hbf i ▸ v))
          -- IH on tree child:
          have ih_tree :
              btMorRel 0 tree'
                (quoteBT bt') :=
            ih ⟨pm + pm, hlt⟩
              (fun v => σ (htf ▸ v))
              (fun v => hσ (htf ▸ v))
          -- IH on step children:
          have ih_step (j' : Fin pm)
              (σ_g : Fin (pm + pm) →
                BTMor1 0)
              (hσ_g : ∀ i, btMorRel 0
                (σ_g i)
                (quoteBT ((σ_g i).interpU
                  Fin.elim0))) :
              btMorRel 0
                ((g' j').subst σ_g)
                (quoteBT
                  (((g' j').subst
                    σ_g).interpU
                    Fin.elim0)) := by
            simp only [g']
            rw [subst_cast (hsf j')]
            exact ih ⟨pm + j'.val, hls j'⟩
              (fun v => σ_g (hsf j' ▸ v))
              (fun v => hσ_g (hsf j' ▸ v))
          apply btMorRel.trans
          · exact btMorRel.congFold
              ih_base
              (fun i => btMorRel.refl _)
              ih_tree
          · exact norm0_fold_commute
              pm base' g' ih_step bt' pj)
    t

/-- At arity 0, every term normalizes to the
quotation of its interpretation.  Follows from
`norm0_gen` applied with the empty substitution.
-/
private theorem norm0
    (t : BTMor1 0) :
    btMorRel 0 t
      (quoteBT (t.interpU
        (Fin.elim0 (α := BT.{0})))) := by
  have comm := norm0_gen t
    (Fin.elim0 (α := BTMor1 0))
    (fun i => Fin.elim0 i)
  rw [show t.subst Fin.elim0 = t from by
    conv_rhs => rw [← BTMor1.subst_id t]
    congr 1; funext i; exact Fin.elim0 i]
    at comm
  exact comm

/-- Completeness at arity 0: if two closed terms
have the same interpretation, they are
`btMorRel`-equivalent. -/
private theorem interpU_complete_zero
    (t1 t2 : BTMor1 0)
    (h : t1.interpU (Fin.elim0 (α := BT.{0}))
      = t2.interpU (Fin.elim0 (α := BT.{0}))) :
    btMorRel 0 t1 t2 :=
  btMorRel.trans (norm0 t1)
    (h ▸ btMorRel.symm (norm0 t2))

/-- Substituting a closed term (at arity 0) into
arity n via the empty substitution produces a
term at arity n structurally identical to the
original but at the new arity.  For quoteBT
values, this yields `quoteBT` at the target
arity. -/
private theorem quoteBT_subst_elim0_gen
    {n : ℕ} {x : PUnit.{1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x) :
    (BT.fold BTMor1.leaf BTMor1.branch
      bt).subst
      (Fin.elim0 (α := BTMor1 n)) =
    BT.fold BTMor1.leaf BTMor1.branch bt := by
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
      have hmk :
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
      rw [hmk, BT.fold_leaf, BT.fold_leaf]
      rfl
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
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
            (children
              (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, BT.fold_node, BT.fold_node]
      change BTMor1.branch
        ((BT.fold BTMor1.leaf BTMor1.branch
          (children
            (Sum.inl PUnit.unit))).subst
          Fin.elim0)
        ((BT.fold BTMor1.leaf BTMor1.branch
          (children
            (Sum.inr PUnit.unit))).subst
          Fin.elim0) =
        BTMor1.branch
          (BT.fold BTMor1.leaf BTMor1.branch
            (children (Sum.inl PUnit.unit)))
          (BT.fold BTMor1.leaf BTMor1.branch
            (children (Sum.inr PUnit.unit)))
      rw [ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]

private theorem quoteBT_subst_elim0
    {n : ℕ} (bt : BT.{0}) :
    (quoteBT (n := 0) bt).subst
      (Fin.elim0 (α := BTMor1 n)) =
    quoteBT (n := n) bt :=
  quoteBT_subst_elim0_gen bt

/-- Substituting any σ into a quoteBT value
produces the same quoteBT at the target arity,
because quoteBT terms contain no variables. -/
private theorem quoteBT_subst_any_gen
    {k m : ℕ} {x : PUnit.{1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x)
    (σ : Fin k → BTMor1 m) :
    (BT.fold BTMor1.leaf BTMor1.branch
      bt).subst σ =
    BT.fold BTMor1.leaf BTMor1.branch bt := by
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
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit
              from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e; exact PEmpty.elim e
      rw [hmk, BT.fold_leaf, BT.fold_leaf]
      rfl
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit
              from
              Sum.inr PUnit.unit)
            children =
          BT.node
            (children (Sum.inl PUnit.unit))
            (children
              (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        simp only
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, BT.fold_node, BT.fold_node]
      change BTMor1.branch
        ((BT.fold BTMor1.leaf
          BTMor1.branch
          (children
            (Sum.inl PUnit.unit))).subst
          σ)
        ((BT.fold BTMor1.leaf
          BTMor1.branch
          (children
            (Sum.inr PUnit.unit))).subst
          σ) =
        BTMor1.branch
          (BT.fold BTMor1.leaf
            BTMor1.branch
            (children
              (Sum.inl PUnit.unit)))
          (BT.fold BTMor1.leaf
            BTMor1.branch
            (children
              (Sum.inr PUnit.unit)))
      rw [ih (Sum.inl PUnit.unit),
        ih (Sum.inr PUnit.unit)]

private theorem quoteBT_subst_any
    {k m : ℕ} (bt : BT.{0})
    (σ : Fin k → BTMor1 m) :
    (quoteBT (n := k) bt).subst σ =
    quoteBT (n := m) bt :=
  quoteBT_subst_any_gen bt σ

/-- Ground completeness lifted to arity n:
if two terms agree semantically at all contexts,
then for any ground substitution the resulting
closed terms are `btMorRel n`-equivalent. -/
private theorem ground_rel_at_n {n : ℕ}
    (t1 t2 : BTMor1 n)
    (h : ∀ (ctx : Fin n → BT.{0}),
      t1.interpU ctx = t2.interpU ctx)
    (ctx : Fin n → BT.{0}) :
    btMorRel n
      (t1.subst
        (fun i => quoteBT (n := n) (ctx i)))
      (t2.subst
        (fun i => quoteBT (n := n) (ctx i))) := by
  -- Ground normalization at arity 0.
  set σ0 : Fin n → BTMor1 0 :=
    fun i => quoteBT (n := 0) (ctx i)
  have hσ0 : ∀ i, btMorRel 0 (σ0 i)
      (quoteBT ((σ0 i).interpU
        (Fin.elim0 (α := BT.{0})))) := by
    intro i; simp only [σ0]
    rw [quoteBT_interpU]
    exact btMorRel.refl _
  have h1 := norm0_gen t1 σ0 hσ0
  have h2 := norm0_gen t2 σ0 hσ0
  -- Rewrite interpU using interpU_subst and
  -- quoteBT_interpU.
  have hrw1 :
      (t1.subst σ0).interpU
        (Fin.elim0 (α := BT.{0})) =
      t1.interpU ctx := by
    rw [BTMor1.interpU_subst]; congr 1
    funext i; exact quoteBT_interpU (ctx i) _
  have hrw2 :
      (t2.subst σ0).interpU
        (Fin.elim0 (α := BT.{0})) =
      t2.interpU ctx := by
    rw [BTMor1.interpU_subst]; congr 1
    funext i; exact quoteBT_interpU (ctx i) _
  rw [hrw1] at h1; rw [hrw2] at h2
  rw [h ctx] at h1
  -- h1 : btMorRel 0 (t1.subst σ0)
  --   (quoteBT (t2.interpU ctx))
  -- h2 : btMorRel 0 (t2.subst σ0)
  --   (quoteBT (t2.interpU ctx))
  have rel0 : btMorRel 0 (t1.subst σ0)
      (t2.subst σ0) :=
    btMorRel.trans h1 (btMorRel.symm h2)
  -- Lift from btMorRel 0 to btMorRel n via
  -- subst_cong_right with Fin.elim0.
  have lifted :=
    subst_cong_right
      (Fin.elim0 (α := BTMor1 n)) rel0
  -- Rewrite using subst_comp and
  -- quoteBT_subst_elim0.
  rw [BTMor1.subst_comp,
    BTMor1.subst_comp] at lifted
  have hσeq : (fun i =>
      (σ0 i).subst
        (Fin.elim0 (α := BTMor1 n))) =
      (fun i =>
        quoteBT (n := n) (ctx i)) := by
    funext i; exact quoteBT_subst_elim0
      (ctx i)
  rw [hσeq] at lifted
  exact lifted

/-- Given `btMorRel 0` at the ground level,
lift to `btMorRel n` via `subst_cong_right`
with the empty substitution. -/
private theorem btMorRel_lift_zero
    {n : ℕ} {s1 s2 : BTMor1 0}
    (h : btMorRel 0 s1 s2) :
    btMorRel n (s1.subst Fin.elim0)
      (s2.subst Fin.elim0) :=
  subst_cong_right
    (Fin.elim0 (α := BTMor1 n)) h

/-- If two terms have the same interpretation
at every context, their ground substitutions
are `btMorRel 0`-equivalent. -/
private theorem interpU_ground_rel
    {n : ℕ}
    (t1 t2 : BTMor1 n)
    (h : ∀ (ctx : Fin n → BT.{0}),
      t1.interpU ctx = t2.interpU ctx)
    (σ : Fin n → BTMor1 0) :
    btMorRel 0 (t1.subst σ)
      (t2.subst σ) := by
  set ctx : Fin n → BT.{0} :=
    fun i => (σ i).interpU
      (Fin.elim0 (α := BT.{0}))
  have hσ : ∀ i, btMorRel 0 (σ i)
      (quoteBT ((σ i).interpU
        (Fin.elim0 (α := BT.{0})))) :=
    fun i => norm0 (σ i)
  have h1 := norm0_gen t1 σ hσ
  have h2 := norm0_gen t2 σ hσ
  have hrw1 :
      (t1.subst σ).interpU
        (Fin.elim0 (α := BT.{0})) =
      t1.interpU ctx := by
    rw [BTMor1.interpU_subst]
  have hrw2 :
      (t2.subst σ).interpU
        (Fin.elim0 (α := BT.{0})) =
      t2.interpU ctx := by
    rw [BTMor1.interpU_subst]
  rw [hrw1] at h1; rw [hrw2] at h2
  rw [h ctx] at h1
  exact btMorRel.trans h1
    (btMorRel.symm h2)

/-- If a branch's interpU matches a projection
at all contexts, that is a contradiction. -/
private theorem branch_ne_proj
    {n : ℕ} (l r : BTMor1 n) (j : Fin n)
    (h : ∀ ctx : Fin n → BT.{0},
      BT.node (l.interpU ctx)
        (r.interpU ctx) = ctx j) :
    False :=
  BT.leaf_ne_node
    ((h (fun _ => BT.leaf)).symm)

/-- If a branch's interpU matches `BT.leaf` at
all contexts, that is a contradiction. -/
private theorem branch_ne_leaf
    {n : ℕ} (l r : BTMor1 n)
    (h : ∀ ctx : Fin n → BT.{0},
      BT.node (l.interpU ctx)
        (r.interpU ctx) = BT.leaf) :
    False :=
  BT.node_ne_leaf (h (fun _ => BT.leaf))

/-- Completeness: if two terms have equal
interpretations at all contexts, they are
`btMorRel`-equivalent.  This is the converse of
`interpU_sound`.

The proof uses `btMorRel.substReflect`
(ground completeness implies open completeness)
together with `interpU_ground_rel` (ground
normalization via `norm0_gen`). -/
theorem interpU_complete {n : ℕ}
    (t1 t2 : BTMor1 n)
    (h : ∀ (ctx : Fin n → BT.{0}),
      t1.interpU ctx = t2.interpU ctx) :
    btMorRel n t1 t2 :=
  btMorRel.substReflect
    (interpU_ground_rel t1 t2 h)

/-- If `t : BTMor1 n` interprets to `BT.leaf`
at every context, then `t` is
`btMorRel`-equivalent to `BTMor1.leaf`. -/
private theorem interpU_always_leaf
    {n : ℕ} (t : BTMor1 n)
    (h : ∀ ctx : Fin n → BT.{0},
      t.interpU ctx = BT.leaf) :
    btMorRel n t BTMor1.leaf :=
  interpU_complete t BTMor1.leaf
    (fun ctx => by
      rw [h ctx, BTMor1.interpU_leaf])

/-- If `t : BTMor1 n` interprets to `BT.node`
at every context (with decomposable left and
right interpretations), then `t` is
`btMorRel`-equivalent to a `BTMor1.branch`. -/
private theorem interpU_always_node
    {n : ℕ} (t : BTMor1 n)
    (hl hr : BTMor1 n)
    (h : ∀ ctx : Fin n → BT.{0},
      t.interpU ctx =
      BT.node (hl.interpU ctx)
        (hr.interpU ctx)) :
    btMorRel n t (BTMor1.branch hl hr) :=
  interpU_complete t (BTMor1.branch hl hr)
    (fun ctx => by
      rw [h ctx, BTMor1.interpU_branch])

/-- The interpretation functor is faithful. -/
instance : interpFunctor.{0}.Faithful where
  map_injective {n m} {f g} h := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw heq
    apply Quotient.sound
      (s := btMorNSetoid n m)
    intro j
    apply interpU_complete
    intro ctx
    exact congrFun
      (congrFun heq ctx) j

/-! ## Separator

The terminal object `0` is a separator in
`LawvereBTQuotCat`: morphisms are determined by
their values on global elements (morphisms from
the terminal object).  This follows from the
completeness theorem (`interpU_complete`), which
states that agreement of interpretations at all
ground contexts implies equivalence under
`btMorRel`. -/

/-- The terminal object `0` is a separator in
`LawvereBTQuotCat`.  For any two morphisms
`f g : n ⟶ m`, if `h ≫ f = h ≫ g` for every
global element `h : 0 ⟶ n`, then `f = g`. -/
theorem lawvereBTQuotCat_isSeparator :
    IsSeparator (0 : LawvereBTQuotCat) := by
  rw [isSeparator_def]
  intro n m f g hyp
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw hyp'
  apply Quotient.sound
    (s := btMorNSetoid n m)
  intro j
  apply interpU_complete
  intro ctx
  let h_raw : BTMorN 0 n :=
    fun i => quoteBT (ctx i)
  let h : (0 : LawvereBTQuotCat) ⟶ n :=
    Quotient.mk (btMorNSetoid 0 n) h_raw
  have heq := hyp' h
  have heq_interp :
      BTMorNQuo.interpU
        (BTMorNQuo.comp h ⟦f_raw⟧)
        (Fin.elim0 (α := BT.{0})) =
      BTMorNQuo.interpU
        (BTMorNQuo.comp h ⟦g_raw⟧)
        (Fin.elim0 (α := BT.{0})) :=
    congrArg (BTMorNQuo.interpU ·
      (Fin.elim0 (α := BT.{0}))) heq
  rw [BTMorNQuo.interpU_comp,
      BTMorNQuo.interpU_comp] at heq_interp
  have h_interp_eq :
      BTMorNQuo.interpU h
        (Fin.elim0 (α := BT.{0})) = ctx := by
    funext i
    exact quoteBT_interpU (ctx i) Fin.elim0
  rw [h_interp_eq] at heq_interp
  exact congrFun heq_interp j

end GebLean
