import GebLean.LawvereBTQuot

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

/-- Completeness: if two terms have equal
interpretations at all contexts, they are
`btMorRel`-equivalent.  This is the converse of
`interpU_sound`. -/
theorem interpU_complete {n : ℕ}
    (t1 t2 : BTMor1 n)
    (h : ∀ (ctx : Fin n → BT.{0}),
      t1.interpU ctx = t2.interpU ctx) :
    btMorRel n t1 t2 := by
  sorry

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

end GebLean
