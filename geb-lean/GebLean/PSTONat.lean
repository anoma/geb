import GebLean.PSO

/-!
# NNO Recursion from PSTO

Derives a natural number object (NNO) recursion
interface from the parameterized snoclist-of-trees
object (PSTO).  The tree type `T` contains
right-spine naturals (snoclists where all elements
are nil).  The NNO interface wraps the PSO fold to
operate with this natural number structure, using
`pstoToRSpineNat` to normalize trees before folding.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  {T : C} [s : IsPSTO C T]

/-- Successor on the right-spine encoding:
`n ↦ snoc(n, nil)`. -/
def pstoNatSucc : T ⟶ T :=
  cfpLift (𝟙 T)
    (cfpTerminalFrom T ≫ s.nil) ≫
    s.snoc

/-- Normalize a tree to its right-spine natural
(= top-level snoclist length).  Uses the PSO fold
to replace every element with nil:
`pstoToRSpineNat(nil) = nil`,
`pstoToRSpineNat(snoc(rest, elem)) =
  pstoNatSucc(pstoToRSpineNat(rest))`. -/
def pstoToRSpineNat : T ⟶ T :=
  cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
    @IsPSO.elim C _ h T T s cfpTerminal T
      s.nil
      (cfpFst T T ≫ pstoNatSucc)

/-- Nil computation rule for `pstoToRSpineNat`:
`pstoToRSpineNat(nil) = nil`. -/
theorem pstoToRSpineNat_nil :
    s.nil ≫ pstoToRSpineNat =
    (s.nil : cfpTerminal (C := C) ⟶ T) := by
  unfold pstoToRSpineNat
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have h1 : s.nil ≫ cfpTerminalFrom T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h1]
  have h2 :
      cfpLift
        (cfpTerminalFrom
          (cfpTerminal (C := C)))
        s.nil =
      cfpInsertSnd s.nil cfpTerminal := by
    unfold cfpInsertSnd
    have term_id :
        cfpTerminalFrom
          (cfpTerminal (C := C)) =
          𝟙 cfpTerminal :=
      (h.terminal.uniq (𝟙 cfpTerminal)).symm
    apply cfpLift_uniq
    · rw [cfpLift_fst, term_id]
    · rw [cfpLift_snd, term_id,
        Category.id_comp]
  rw [h2, s.elim_nil]

/-- Snoc computation rule for `pstoToRSpineNat`:
`pstoToRSpineNat(snoc(rest, elem)) =
  pstoNatSucc(pstoToRSpineNat(rest))`. -/
theorem pstoToRSpineNat_snoc :
    s.snoc ≫ pstoToRSpineNat =
    cfpMap pstoToRSpineNat (𝟙 T) ≫
      cfpFst T T ≫ pstoNatSucc := by
  unfold pstoToRSpineNat
  set embed := cfpLift (cfpTerminalFrom T)
    (𝟙 T) with embed_def
  set helper :=
    @IsPSO.elim C _ h T T s cfpTerminal T
      s.nil (cfpFst T T ≫ pstoNatSucc)
    with helper_def
  -- LHS: snoc ≫ embed ≫ helper
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq :
      s.snoc ≫ cfpTerminalFrom T =
      cfpTerminalFrom (cfpProd T T) :=
    h.terminal.uniq _
  rw [term_eq]
  -- LHS: cfpLift (term (T×T)) snoc ≫ helper
  -- Factor through embed' and cfpMap
  have factor :
      cfpLift
        (cfpTerminalFrom (cfpProd T T))
        s.snoc =
      cfpLift (cfpTerminalFrom (cfpProd T T))
        (𝟙 (cfpProd T T)) ≫
        cfpMap (𝟙 cfpTerminal) s.snoc := by
    rw [cfpLift_cfpMap, Category.id_comp,
      Category.comp_id]
  rw [factor, Category.assoc,
    s.elim_snoc s.nil
      (cfpFst T T ≫ pstoNatSucc)]
  set embed' :=
    cfpLift
      (cfpTerminalFrom (cfpProd T T))
      (𝟙 (cfpProd T T))
  -- Goal: embed' ≫ cfpLiftRecElem helper ≫
  --   cfpFst T T ≫ pstoNatSucc
  -- = cfpMap (embed ≫ helper) (𝟙 T) ≫
  --   cfpFst T T ≫ pstoNatSucc
  -- Show embed' ≫ cfpLiftRecElem helper ≫ fst
  --   = fst ≫ embed ≫ helper
  have lhs_fst :
      embed' ≫ cfpLiftRecElem helper ≫
        cfpFst T T =
      cfpFst T T ≫ embed ≫ helper := by
    rw [← Category.assoc]
    unfold cfpLiftRecElem
    rw [cfpLift_precomp, cfpLift_fst,
      ← Category.assoc]
    unfold cfpAssocFst
    rw [cfpLift_precomp]
    -- Now have nested embed' ≫ fst and
    -- embed' ≫ snd ≫ fst.
    -- Reassociate to apply embed'_fst/snd.
    conv_lhs =>
      rw [show embed' ≫
        cfpSnd cfpTerminal (cfpProd T T) ≫
        cfpFst T T =
        (embed' ≫
          cfpSnd cfpTerminal (cfpProd T T)) ≫
        cfpFst T T from
        (Category.assoc _ _ _).symm]
    rw [show embed' ≫
        cfpFst cfpTerminal (cfpProd T T) =
        cfpTerminalFrom (cfpProd T T) from
        cfpLift_fst _ _,
      show embed' ≫
        cfpSnd cfpTerminal (cfpProd T T) =
        𝟙 (cfpProd T T) from
        cfpLift_snd _ _,
      Category.id_comp]
    -- cfpLift (term (T×T)) (fst T T) ≫ helper
    -- = fst T T ≫ embed ≫ helper
    -- Show the morphisms before helper are equal.
    have lift_eq :
        cfpLift
          (cfpTerminalFrom (cfpProd T T))
          (cfpFst T T) =
        cfpFst T T ≫ embed := by
      rw [embed_def, cfpLift_precomp,
        Category.comp_id]
      congr 1
      exact (h.terminal.uniq _).symm
    rw [lift_eq, Category.assoc]
  have rhs_fst :
      cfpMap (embed ≫ helper) (𝟙 T) ≫
        cfpFst T T =
      cfpFst T T ≫ embed ≫ helper :=
    cfpMap_fst _ _
  -- The goal has cfpLiftRecElem (IsPSO.elim ...)
  -- which is the same as cfpLiftRecElem helper.
  change embed' ≫ cfpLiftRecElem helper ≫
    cfpFst T T ≫ pstoNatSucc =
    cfpMap (embed ≫ helper) (𝟙 T) ≫
      cfpFst T T ≫ pstoNatSucc
  -- lhs_fst:
  --   embed' ≫ cfpLiftRecElem helper ≫ fst
  --   = fst ≫ embed ≫ helper
  -- The goal's LHS (right-associated) is:
  --   embed' ≫ (cfpLiftRecElem helper ≫
  --     (cfpFst T T ≫ pstoNatSucc))
  -- Rewrite using the associativity lemma to
  -- extract the fst.
  have lhs_eq :
      embed' ≫ cfpLiftRecElem helper ≫
        cfpFst T T ≫ pstoNatSucc =
      (embed' ≫ cfpLiftRecElem helper ≫
        cfpFst T T) ≫ pstoNatSucc := by
    simp only [Category.assoc]
  have rhs_eq :
      cfpMap (embed ≫ helper) (𝟙 T) ≫
        cfpFst T T ≫ pstoNatSucc =
      (cfpMap (embed ≫ helper) (𝟙 T) ≫
        cfpFst T T) ≫ pstoNatSucc := by
    simp only [Category.assoc]
  rw [lhs_eq, rhs_eq, lhs_fst, rhs_fst]

/-- `pstoNatSucc` commutes with `pstoToRSpineNat`:
normalizing before or after successor gives the
same result. -/
theorem pstoNatSucc_pstoToRSpineNat_comm :
    pstoNatSucc ≫ pstoToRSpineNat =
    pstoToRSpineNat ≫
      (pstoNatSucc : T ⟶ T) := by
  -- pstoNatSucc = cfpLift (𝟙 T) (term ≫ nil) ≫ snoc
  -- So pstoNatSucc ≫ pstoToRSpineNat =
  --   cfpLift (𝟙 T) (term ≫ nil) ≫ snoc ≫
  --     pstoToRSpineNat
  -- By pstoToRSpineNat_snoc:
  --   snoc ≫ pstoToRSpineNat =
  --   cfpMap pstoToRSpineNat (𝟙 T) ≫
  --     fst ≫ pstoNatSucc
  unfold pstoNatSucc
  rw [Category.assoc, pstoToRSpineNat_snoc]
  -- Goal: cfpLift (𝟙 T) (term ≫ nil) ≫
  --   cfpMap pstoToRSpineNat (𝟙 T) ≫
  --   fst ≫ pstoNatSucc
  -- = pstoToRSpineNat ≫
  --   cfpLift (𝟙 T) (term ≫ nil) ≫ snoc
  rw [← Category.assoc
    (cfpLift (𝟙 T) (cfpTerminalFrom T ≫ s.nil))
    (cfpMap pstoToRSpineNat (𝟙 T)),
    cfpLift_cfpMap, Category.id_comp,
    Category.comp_id]
  -- Goal: cfpLift pstoToRSpineNat (term ≫ nil) ≫
  --   fst ≫ pstoNatSucc
  -- = pstoToRSpineNat ≫
  --   cfpLift (𝟙 T) (term ≫ nil) ≫ snoc
  rw [← Category.assoc, cfpLift_fst]
  -- Goal: pstoToRSpineNat ≫ pstoNatSucc
  -- = pstoToRSpineNat ≫
  --   cfpLift (𝟙 T) (term ≫ nil) ≫ snoc
  -- The RHS is pstoToRSpineNat ≫ pstoNatSucc.
  rfl

/-- For any `φ : T ⟶ T` satisfying the nil and
snoc computation rules of `pstoToRSpineNat`,
the embedding `cfpSnd cfpTerminal T ≫ φ` equals
the PSO fold `helper`. -/
private theorem snd_elim_helper
    (φ : T ⟶ T)
    (hnil : s.nil ≫ φ = s.nil)
    (hsnoc :
      s.snoc ≫ φ =
      cfpMap φ (𝟙 T) ≫
        cfpFst T T ≫ pstoNatSucc) :
    cfpSnd cfpTerminal T ≫ φ =
    @IsPSO.elim C _ h T T s cfpTerminal T
      s.nil
      (cfpFst T T ≫ pstoNatSucc) := by
  apply s.elim_uniq
  · -- Base: cfpInsertSnd nil 1 ≫ snd ≫ φ = nil
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc]
    have : cfpTerminalFrom cfpTerminal ≫
        s.nil = s.nil := by
      rw [show cfpTerminalFrom
        (cfpTerminal (C := C)) =
        𝟙 cfpTerminal from
        (h.terminal.uniq _).symm,
        Category.id_comp]
    rw [hnil, this]
  · -- Step: cfpMap (𝟙 1) snoc ≫ snd ≫ φ
    --   = cfpLiftRecElem (snd ≫ φ) ≫
    --     fst ≫ pstoNatSucc
    rw [← Category.assoc,
      show cfpMap (𝟙 cfpTerminal) s.snoc ≫
        cfpSnd cfpTerminal T =
        cfpSnd cfpTerminal (cfpProd T T) ≫
          s.snoc from
        cfpMap_snd _ _,
      Category.assoc, hsnoc]
    -- Goal:
    -- snd 1 (T×T) ≫ cfpMap φ (𝟙 T) ≫
    --   fst ≫ pstoNatSucc
    -- = cfpLiftRecElem (snd ≫ φ) ≫
    --   fst ≫ pstoNatSucc
    -- Both sides reduce to
    -- snd ≫ fst ≫ φ ≫ pstoNatSucc.
    -- Rewrite LHS using cfpMap_fst.
    calc cfpSnd cfpTerminal (cfpProd T T) ≫
          cfpMap φ (𝟙 T) ≫
          cfpFst T T ≫ pstoNatSucc
        = cfpSnd cfpTerminal (cfpProd T T) ≫
          (cfpMap φ (𝟙 T) ≫ cfpFst T T) ≫
          pstoNatSucc := by
          simp only [Category.assoc]
      _ = cfpSnd cfpTerminal (cfpProd T T) ≫
          (cfpFst T T ≫ φ) ≫
          pstoNatSucc := by
          rw [cfpMap_fst]
      _ = (cfpAssocFst cfpTerminal T T ≫
            cfpSnd cfpTerminal T ≫ φ) ≫
          pstoNatSucc := by
          have assocFst_snd :
              cfpAssocFst cfpTerminal T T ≫
                cfpSnd cfpTerminal T =
              cfpSnd cfpTerminal (cfpProd T T) ≫
                cfpFst T T := by
            unfold cfpAssocFst
            exact cfpLift_snd _ _
          rw [show cfpSnd cfpTerminal
              (cfpProd T T) ≫
              (cfpFst T T ≫ φ) ≫
              pstoNatSucc =
            (cfpSnd cfpTerminal
              (cfpProd T T) ≫
              cfpFst T T) ≫ φ ≫
              pstoNatSucc from by
              simp only [Category.assoc],
            ← assocFst_snd]
          simp only [Category.assoc]
      _ = (cfpLiftRecElem
            (cfpSnd cfpTerminal T ≫ φ) ≫
            cfpFst T T) ≫ pstoNatSucc := by
          congr 1
          unfold cfpLiftRecElem
          exact (cfpLift_fst _ _).symm
      _ = cfpLiftRecElem
            (cfpSnd cfpTerminal T ≫ φ) ≫
          cfpFst T T ≫ pstoNatSucc := by
          simp only [Category.assoc]

/-- `pstoToRSpineNat` is idempotent. -/
theorem pstoToRSpineNat_idem :
    pstoToRSpineNat ≫ pstoToRSpineNat =
    (pstoToRSpineNat : T ⟶ T) := by
  set embed :=
    cfpLift (cfpTerminalFrom T)
      (𝟙 T) with embed_def
  set helper :=
    @IsPSO.elim C _ h T T s cfpTerminal T
      s.nil (cfpFst T T ≫ pstoNatSucc)
    with helper_def
  have embed_snd :
      embed ≫ cfpSnd cfpTerminal T =
        𝟙 T :=
    cfpLift_snd _ _
  -- Both snd ≫ pstoToRSpineNat and
  -- snd ≫ (pstoToRSpineNat ≫ pstoToRSpineNat)
  -- equal helper by snd_elim_helper.
  have snd_rsn :=
    @snd_elim_helper C _ h T s
      pstoToRSpineNat
      pstoToRSpineNat_nil
      pstoToRSpineNat_snoc
  have snd_rsn2 :=
    @snd_elim_helper C _ h T s
      (pstoToRSpineNat ≫ pstoToRSpineNat)
      (by rw [← Category.assoc,
          pstoToRSpineNat_nil,
          pstoToRSpineNat_nil])
      (by
        -- Goal: snoc ≫ rsn ≫ rsn =
        --   cfpMap (rsn ≫ rsn) (𝟙 T) ≫
        --   fst ≫ natSucc
        -- Both sides equal
        -- fst ≫ rsn ≫ rsn ≫ natSucc.
        rw [← Category.assoc
          (s.snoc) pstoToRSpineNat,
          pstoToRSpineNat_snoc]
        simp only [Category.assoc]
        rw [pstoNatSucc_pstoToRSpineNat_comm]
        -- Now fst-reduce both sides.
        -- LHS: cfpMap rsn (𝟙 T) ≫
        --   fst ≫ rsn ≫ natSucc
        -- RHS: cfpMap (rsn ≫ rsn) (𝟙 T) ≫
        --   fst ≫ natSucc
        -- Show both equal fst ≫ rsn ≫ rsn
        --   ≫ natSucc.
        rw [show cfpMap pstoToRSpineNat
              (𝟙 T) ≫
            cfpFst T T ≫
            pstoToRSpineNat ≫
            pstoNatSucc =
          (cfpMap pstoToRSpineNat (𝟙 T) ≫
            cfpFst T T) ≫
            pstoToRSpineNat ≫
            pstoNatSucc from by
            simp only [Category.assoc],
          cfpMap_fst,
          show cfpMap
            (pstoToRSpineNat ≫
              pstoToRSpineNat)
            (𝟙 T) ≫
            cfpFst T T ≫ pstoNatSucc =
          (cfpMap
            (pstoToRSpineNat ≫
              pstoToRSpineNat)
            (𝟙 T) ≫ cfpFst T T) ≫
            pstoNatSucc from by
            simp only [Category.assoc],
          cfpMap_fst]
        simp only [Category.assoc])
  calc pstoToRSpineNat ≫ pstoToRSpineNat
      = embed ≫ cfpSnd cfpTerminal T ≫
        pstoToRSpineNat ≫
        pstoToRSpineNat := by
        rw [← Category.assoc embed
          (cfpSnd cfpTerminal T),
          embed_snd, Category.id_comp]
    _ = embed ≫ cfpSnd cfpTerminal T ≫
        pstoToRSpineNat := by
        congr 1
        exact snd_rsn2.trans snd_rsn.symm
    _ = pstoToRSpineNat := by
        rw [← Category.assoc, embed_snd,
          Category.id_comp]

/-- The NNO fold: normalize via `pstoToRSpineNat`,
then fold with unary step.  Given `f : A ⟶ X`
(base case) and `g : X ⟶ X` (step), produces a
morphism `A × T ⟶ X` that recursively folds a
right-spine natural. -/
def pstoNnoElim {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpProd A T ⟶ X :=
  cfpMap (𝟙 A) pstoToRSpineNat ≫
    @IsPSO.elim C _ h T T s A X f
      (cfpFst X T ≫ g)

/-- Base case: `pstoNnoElim(a, nil) = f(a)`. -/
theorem pstoNnoElim_nil {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpInsertSnd s.nil A ≫
      pstoNnoElim f g = f := by
  unfold pstoNnoElim
  rw [← Category.assoc]
  have insert_rsn :
      cfpInsertSnd s.nil A ≫
        cfpMap (𝟙 A) pstoToRSpineNat =
      cfpInsertSnd s.nil A := by
    unfold cfpInsertSnd
    rw [cfpLift_cfpMap, Category.id_comp,
      Category.assoc, pstoToRSpineNat_nil]
  rw [insert_rsn, s.elim_nil]

/-- Composing `cfpMap (𝟙 A) pstoNatSucc` with the
PSO fold `elim f (cfpFst X T ≫ g)` yields
`elim f (cfpFst X T ≫ g) ≫ g`. -/
private theorem pstoNatSucc_elim_step
    {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpMap (𝟙 A) pstoNatSucc ≫
      @IsPSO.elim C _ h T T s A X f
        (cfpFst X T ≫ g) =
    @IsPSO.elim C _ h T T s A X f
      (cfpFst X T ≫ g) ≫ g := by
  set φ := @IsPSO.elim C _ h T T s A X f
    (cfpFst X T ≫ g)
  -- pstoNatSucc = cfpLift (𝟙 T)
  --   (term ≫ nil) ≫ snoc
  have step_def :
      cfpMap (𝟙 A) pstoNatSucc =
      cfpMap (𝟙 A)
        (cfpLift (𝟙 T)
          (cfpTerminalFrom T ≫ s.nil)) ≫
        cfpMap (𝟙 A) s.snoc := by
    show cfpMap (𝟙 A) pstoNatSucc = _
    unfold pstoNatSucc
    conv_lhs =>
      rw [show (𝟙 A : A ⟶ A) =
        𝟙 A ≫ 𝟙 A from
        (Category.id_comp (𝟙 A)).symm]
    rw [← cfpMap_comp]
  rw [step_def, Category.assoc,
    s.elim_snoc f (cfpFst X T ≫ g)]
  -- Goal (with cfpLiftRecElem expanded):
  -- cfpMap (𝟙 A) (cfpLift (𝟙 T) (term ≫ nil))
  --   ≫ cfpLift (cfpAssocFst A T T ≫ φ)
  --       (snd A (T×T) ≫ snd T T)
  --   ≫ cfpFst X T ≫ g
  -- = φ ≫ g
  -- Show the fst component extracts to φ.
  have cancel :
      cfpMap (𝟙 A)
        (cfpLift (𝟙 T)
          (cfpTerminalFrom T ≫ s.nil)) ≫
        cfpAssocFst A T T =
      𝟙 (cfpProd A T) := by
    rw [← cfpMap_id A T]
    unfold cfpAssocFst
    apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst,
        cfpMap_fst, Category.comp_id]
    · rw [Category.assoc, cfpLift_snd,
        ← Category.assoc, cfpMap_snd,
        Category.assoc, cfpLift_fst,
        Category.comp_id]
  have fst_extract :
      cfpMap (𝟙 A)
        (cfpLift (𝟙 T)
          (cfpTerminalFrom T ≫ s.nil)) ≫
        cfpLift (cfpAssocFst A T T ≫ φ)
          (cfpSnd A (cfpProd T T) ≫
            cfpSnd T T) ≫
        cfpFst X T = φ := by
    rw [← Category.assoc, cfpLift_precomp,
      cfpLift_fst, ← Category.assoc,
      cancel, Category.id_comp]
  unfold cfpLiftRecElem
  rw [show cfpMap (𝟙 A)
      (cfpLift (𝟙 T)
        (cfpTerminalFrom T ≫ s.nil)) ≫
      cfpLift (cfpAssocFst A T T ≫ φ)
        (cfpSnd A (cfpProd T T) ≫
          cfpSnd T T) ≫
      cfpFst X T ≫ g =
    (cfpMap (𝟙 A)
      (cfpLift (𝟙 T)
        (cfpTerminalFrom T ≫ s.nil)) ≫
      cfpLift (cfpAssocFst A T T ≫ φ)
        (cfpSnd A (cfpProd T T) ≫
          cfpSnd T T) ≫
      cfpFst X T) ≫ g from by
      simp only [Category.assoc],
    fst_extract]

/-- Step case:
`pstoNnoElim(a, pstoNatSucc(n)) =
  g(pstoNnoElim(a, n))`. -/
theorem pstoNnoElim_s {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpMap (𝟙 A)
      (pstoNatSucc : T ⟶ T) ≫
      pstoNnoElim f g =
    pstoNnoElim f g ≫ g := by
  unfold pstoNnoElim
  rw [← Category.assoc]
  -- Factor cfpMap pstoNatSucc through rsn.
  have comm :
      cfpMap (𝟙 A)
        (pstoNatSucc : T ⟶ T) ≫
        cfpMap (𝟙 A)
          (pstoToRSpineNat : T ⟶ T) =
      cfpMap (𝟙 A)
        (pstoToRSpineNat : T ⟶ T) ≫
        cfpMap (𝟙 A)
          (pstoNatSucc : T ⟶ T) := by
    rw [cfpMap_comp, Category.id_comp,
      cfpMap_comp, Category.id_comp,
      pstoNatSucc_pstoToRSpineNat_comm]
  rw [comm, Category.assoc,
    pstoNatSucc_elim_step f g,
    ← Category.assoc]

/-- The snoc-step equation for `φ` derived from
the normalization and natSucc step conditions. -/
private theorem φ_snoc_step
    {A X : C}
    (φ : cfpProd A T ⟶ X)
    (g : X ⟶ X)
    (hs :
      cfpMap (𝟙 A)
        (pstoNatSucc : T ⟶ T) ≫ φ = φ ≫ g)
    (hnorm :
      cfpMap (𝟙 A)
        (pstoToRSpineNat : T ⟶ T) ≫ φ =
        φ) :
    cfpMap (𝟙 A) s.snoc ≫ φ =
    cfpLiftRecElem φ ≫
      (cfpFst X T ≫ g) := by
  have step1 :
      cfpMap (𝟙 A) s.snoc ≫ φ =
      cfpMap (𝟙 A)
        (s.snoc ≫ pstoToRSpineNat) ≫ φ := by
    rw [show cfpMap (𝟙 A)
        (s.snoc ≫ pstoToRSpineNat) =
      cfpMap (𝟙 A) s.snoc ≫
        cfpMap (𝟙 A)
          (pstoToRSpineNat : T ⟶ T) from by
        conv_lhs =>
          rw [show (𝟙 A : A ⟶ A) =
            𝟙 A ≫ 𝟙 A from
            (Category.id_comp (𝟙 A)).symm]
        rw [← cfpMap_comp],
      Category.assoc, hnorm]
  rw [step1, pstoToRSpineNat_snoc]
  have rhs_simp :
      cfpLiftRecElem φ ≫ cfpFst X T ≫ g =
      cfpAssocFst A T T ≫ φ ≫ g := by
    rw [← Category.assoc]
    unfold cfpLiftRecElem
    rw [cfpLift_fst, Category.assoc]
  rw [rhs_simp]
  have factor1 :
      cfpMap (𝟙 A)
        (cfpMap pstoToRSpineNat (𝟙 T) ≫
          cfpFst T T ≫ pstoNatSucc) =
      cfpMap (𝟙 A)
        (cfpMap pstoToRSpineNat (𝟙 T)) ≫
        cfpMap (𝟙 A)
          (cfpFst T T ≫ pstoNatSucc) := by
    conv_lhs =>
      rw [show (𝟙 A : A ⟶ A) =
        𝟙 A ≫ 𝟙 A from
        (Category.id_comp (𝟙 A)).symm]
    rw [← cfpMap_comp]
  -- cfpMap (𝟙 A) (fst ≫ natS)
  --   = cfpAssocFst ≫ cfpMap (𝟙 A) natS
  have factor2 :
      cfpMap (𝟙 A)
        (cfpFst T T ≫ pstoNatSucc) =
      cfpAssocFst A T T ≫
        cfpMap (𝟙 A)
          (pstoNatSucc : T ⟶ T) := by
    symm
    apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        ← Category.assoc]
      unfold cfpAssocFst
      rw [cfpLift_fst]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc]
      unfold cfpAssocFst
      rw [cfpLift_snd, Category.assoc]
  -- cfpMap (𝟙 A) (cfpMap rsn (𝟙 T)) ≫
  --   cfpAssocFst
  --   = cfpAssocFst ≫ cfpMap (𝟙 A) rsn
  have factor3 :
      cfpMap (𝟙 A)
        (cfpMap pstoToRSpineNat (𝟙 T)) ≫
        cfpAssocFst A T T =
      cfpAssocFst A T T ≫
        cfpMap (𝟙 A)
          (pstoToRSpineNat : T ⟶ T) := by
    -- Both sides: A×(T×T) → A×T
    -- Fst: both give fst A (T×T) (= proj to A)
    -- Snd: both give snd A (T×T) ≫ fst T T ≫ rsn
    -- Both sides: A×(T×T) → A×T.
    -- Use cfpProd_ext (from PSO.lean).
    have cfpProd_ext' :
        ∀ {D : C}
        (m₁ m₂ : D ⟶ cfpProd A T),
        m₁ ≫ cfpFst A T = m₂ ≫ cfpFst A T →
        m₁ ≫ cfpSnd A T = m₂ ≫ cfpSnd A T →
        m₁ = m₂ := by
      intro D m₁ m₂ hfst hsnd
      have h2 := cfpLift_uniq
        (m₂ ≫ cfpFst A T) (m₂ ≫ cfpSnd A T)
        m₂ rfl rfl
      rw [h2]
      exact cfpLift_uniq _ _ m₁ hfst hsnd
    apply cfpProd_ext'
    · -- Fst: both = fst A (T×T).
      -- LHS fst: cfpMap (cfpMap rsn (𝟙 T)) ≫
      --   cfpAssocFst ≫ fst A T
      -- = cfpMap (cfpMap rsn (𝟙 T)) ≫
      --   fst A (T×T) (by cfpAssocFst_fst)
      -- = fst A (T×T) ≫ 𝟙 A (by cfpMap_fst)
      -- = fst A (T×T) (by comp_id).
      -- RHS fst: cfpAssocFst ≫ cfpMap rsn ≫
      --   fst A T
      -- = cfpAssocFst ≫ fst A T ≫ 𝟙 A (cfpMap_fst)
      -- = cfpAssocFst ≫ fst A T (comp_id)
      -- = fst A (T×T) (cfpAssocFst_fst).
      have af : cfpAssocFst A T T ≫
          cfpFst A T =
          cfpFst A (cfpProd T T) := by
        unfold cfpAssocFst; exact cfpLift_fst _ _
      simp only [Category.assoc]
      rw [cfpMap_fst, Category.comp_id, af]
      rw [cfpMap_fst, Category.comp_id]
    · -- Snd: both = snd A (T×T) ≫ fst ≫ rsn.
      simp only [Category.assoc]
      rw [cfpMap_snd,
        show cfpAssocFst A T T ≫
          cfpSnd A T =
          cfpSnd A (cfpProd T T) ≫
            cfpFst T T from by
          unfold cfpAssocFst
          exact cfpLift_snd _ _,
        ← Category.assoc
          (cfpAssocFst A T T)
          (cfpSnd A T),
        show cfpAssocFst A T T ≫
          cfpSnd A T =
          cfpSnd A (cfpProd T T) ≫
            cfpFst T T from by
          unfold cfpAssocFst
          exact cfpLift_snd _ _,
        ← Category.assoc
          (cfpMap (𝟙 A)
            (cfpMap pstoToRSpineNat (𝟙 T)))
          (cfpSnd A (cfpProd T T)),
        cfpMap_snd,
        Category.assoc, cfpMap_fst,
        Category.assoc]
  rw [factor1, factor2]
  simp only [Category.assoc]
  rw [← Category.assoc
    (cfpMap (𝟙 A)
      (cfpMap pstoToRSpineNat (𝟙 T)))
    (cfpAssocFst A T T),
    factor3]
  simp only [Category.assoc]
  -- Goal: cfpAssocFst ≫ cfpMap rsn ≫
  --   cfpMap natS ≫ φ =
  --   cfpAssocFst ≫ φ ≫ g
  rw [hs,
    ← Category.assoc
      (cfpMap (𝟙 A)
        (pstoToRSpineNat : T ⟶ T))
      φ g,
    hnorm]

/-- Any `pstoToRSpineNat`-invariant morphism
satisfying the base and step conditions equals
`pstoNnoElim`. -/
theorem pstoNnoElim_uniq {A X : C}
    (f : A ⟶ X) (g : X ⟶ X)
    (φ : cfpProd A T ⟶ X)
    (hnil : cfpInsertSnd s.nil A ≫ φ = f)
    (hs :
      cfpMap (𝟙 A)
        (pstoNatSucc : T ⟶ T) ≫ φ = φ ≫ g)
    (hnorm :
      cfpMap (𝟙 A)
        (pstoToRSpineNat : T ⟶ T) ≫ φ =
        φ) :
    φ = pstoNnoElim f g := by
  unfold pstoNnoElim
  conv_lhs => rw [hnorm.symm]
  congr 1
  exact s.elim_uniq f (cfpFst X T ≫ g) φ
    hnil (φ_snoc_step φ g hs hnorm)

end GebLean
