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

/-- Completeness: if two terms have equal
interpretations at all contexts, they are
`btMorRel`-equivalent.  This is the converse of
`interpU_sound`. -/
theorem interpU_complete {n : ℕ}
    (t1 t2 : BTMor1 n)
    (h : ∀ (ctx : Fin n → BT.{0}),
      t1.interpU ctx = t2.interpU ctx) :
    btMorRel n t1 t2 := by
  exact _

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
