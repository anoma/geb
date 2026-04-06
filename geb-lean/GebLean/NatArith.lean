import GebLean.TreeLogic

/-!
# Internal Natural Number Arithmetic

Defines predecessor, truncated subtraction, and
equality on right-spine natural numbers encoded as
trees, as morphisms in any category with chosen finite
products and a parameterized binary tree object.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-- Predecessor on right-spine naturals:
`pred(leaf) = leaf`, `pred(branch(_, n)) = n`. -/
def natPred : p.T ⟶ p.T := treeRightEndo

/-- Leaf computation rule for `natPred`:
`pred(leaf) = leaf`. -/
theorem natPred_ℓ :
    p.ℓ ≫ natPred =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold natPred
  exact ℓ_treeRightEndo

/-- `natPred` is a left inverse of `natSucc`:
`natSucc ≫ natPred = 𝟙 p.T`. -/
theorem natPred_natSucc :
    natSucc ≫ natPred = (𝟙 p.T : p.T ⟶ p.T) := by
  unfold natPred natSucc
  rw [Category.assoc, β_treeRightEndo,
    cfpLift_snd]

/-- Truncated subtraction `n - m` on right-spine
naturals.  Fold on the second argument `m`, applying
`natPred` at each successor step.  At `m = leaf`
(zero), return `n`.  At `m = branch(_, m')`, return
`natPred(natTruncSub(n, m'))`. -/
def natTruncSub : cfpProd p.T p.T ⟶ p.T :=
  p.elim (𝟙 p.T) (cfpSnd p.T p.T ≫ natPred)

/-- Leaf computation rule for `natTruncSub`:
`natTruncSub(n, leaf) = n`. -/
theorem natTruncSub_ℓ :
    cfpInsertSnd p.ℓ p.T ≫ natTruncSub =
    𝟙 p.T := by
  unfold natTruncSub
  exact p.elim_ℓ (𝟙 p.T) _

/-- Branch computation rule for `natTruncSub`:
`natTruncSub(n, branch(l, r)) =
  natPred(natTruncSub(n, r))` under the unary encoding
(where `l = leaf`). -/
theorem natTruncSub_β :
    cfpMap (𝟙 p.T) p.β ≫ natTruncSub =
    cfpLiftAssoc natTruncSub natTruncSub ≫
      (cfpSnd p.T p.T ≫ natPred) := by
  unfold natTruncSub
  exact p.elim_β (𝟙 p.T) _

/-- The step morphism of `natTruncSub` commutes
with `natPred` in the sense required by
`elim_algebra_morphism`. -/
private theorem natPred_step_comm :
    cfpMap natPred natPred ≫
      (cfpSnd p.T p.T ≫ natPred) =
    (cfpSnd p.T p.T ≫ natPred) ≫
      (natPred : p.T ⟶ p.T) := by
  rw [← Category.assoc
    (cfpMap natPred natPred),
    cfpMap_snd, Category.assoc]

/-- Post-composing `natTruncSub` with `natPred`
yields the catamorphism with predecessor as base:
`natTruncSub ≫ natPred =
  p.elim natPred (cfpSnd T T ≫ natPred)`. -/
theorem natTruncSub_natPred :
    natTruncSub ≫ natPred =
    p.elim (natPred : p.T ⟶ p.T)
      (cfpSnd p.T p.T ≫ natPred) := by
  unfold natTruncSub
  rw [elim_algebra_morphism
    (𝟙 p.T) (cfpSnd p.T p.T ≫ natPred)
    natPred (cfpSnd p.T p.T ≫ natPred)
    natPred_step_comm, Category.id_comp]

/-- Pre-composing `natTruncSub` with `natSucc` in
the first argument and post-composing with
`natPred` yields `natTruncSub`:
`cfpMap natSucc (𝟙 T) ≫ natTruncSub ≫ natPred
  = natTruncSub`.  This is the categorical
analogue of the peeling lemma
`natPred(natTruncSub(succ(n), m))
  = natTruncSub(n, m)`. -/
theorem natSucc_natTruncSub_natPred :
    cfpMap natSucc (𝟙 p.T) ≫
      (natTruncSub ≫ natPred) =
    (natTruncSub : cfpProd p.T p.T ⟶ p.T) := by
  rw [natTruncSub_natPred,
    elim_naturality natSucc natPred
      (cfpSnd p.T p.T ≫ natPred),
    natPred_natSucc]
  rfl

/-- The diagonal applied to `natTruncSub`, lifted
to a parameterized morphism on
`cfpProd cfpTerminal T`. -/
private def diagTruncSub :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  cfpLift (cfpSnd cfpTerminal p.T)
    (cfpSnd cfpTerminal p.T) ≫ natTruncSub

/-- Base case for the diagonal truncated
subtraction: `diagTruncSub(*, leaf) = leaf`. -/
private theorem diagTruncSub_base :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      diagTruncSub = p.ℓ := by
  unfold diagTruncSub
  rw [← Category.assoc, cfpLift_precomp]
  have hsnd :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        cfpSnd cfpTerminal p.T = p.ℓ := by
    unfold cfpInsertSnd
    rw [cfpLift_snd,
      cfpTerminalFrom_terminal,
      Category.id_comp]
  rw [hsnd]
  have factor :
      cfpLift p.ℓ p.ℓ =
      p.ℓ ≫ cfpInsertSnd p.ℓ p.T := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    have hterm :
        p.ℓ ≫ cfpTerminalFrom p.T =
        cfpTerminalFrom cfpTerminal :=
      h.terminal.uniq _
    rw [hterm, cfpTerminalFrom_terminal,
      Category.id_comp]
  rw [factor, Category.assoc,
    natTruncSub_ℓ, Category.comp_id]

/-- `natPred` applied to `p.β`:
`β ≫ natPred = cfpSnd T T`. -/
theorem β_natPred :
    p.β ≫ natPred = cfpSnd p.T p.T := by
  unfold natPred
  exact β_treeRightEndo

theorem β_natTruncSub_natPred :
    cfpMap p.β (𝟙 p.T) ≫
      (natTruncSub ≫ natPred) =
    cfpMap (cfpSnd p.T p.T) (𝟙 p.T) ≫
      (natTruncSub : cfpProd p.T p.T ⟶ p.T)
      := by
  rw [natTruncSub_natPred,
    elim_naturality p.β natPred
      (cfpSnd p.T p.T ≫ natPred),
    β_natPred]
  conv_rhs =>
    rw [show natTruncSub =
      p.elim (𝟙 p.T)
        (cfpSnd p.T p.T ≫ natPred) from
      rfl]
  rw [elim_naturality (cfpSnd p.T p.T)
    (𝟙 p.T) (cfpSnd p.T p.T ≫ natPred),
    Category.comp_id]

/-- `natTruncSub(β(l,r), β(l,r))
  = natTruncSub(r, r)`:  the self-subtraction of
a branch equals the self-subtraction of its right
child. -/
private theorem diag_β_natTruncSub :
    cfpLift p.β p.β ≫ natTruncSub =
    cfpLift (cfpSnd p.T p.T)
      (cfpSnd p.T p.T) ≫
      (natTruncSub :
        cfpProd p.T p.T ⟶ p.T) := by
  -- Step 1: show cfpLift β β ≫ natTruncSub =
  --   cfpLift β (snd) ≫ natTruncSub ≫ natPred.
  have step1 :
      cfpLift p.β p.β ≫ natTruncSub =
      cfpLift p.β (cfpSnd p.T p.T) ≫
        natTruncSub ≫ natPred := by
    -- Factor cfpLift β β = cfpLift β (𝟙 _)
    --   ≫ cfpMap (𝟙 T) β.
    have hββ :
        cfpLift p.β p.β =
        cfpLift p.β (𝟙 (cfpProd p.T p.T)) ≫
          cfpMap (𝟙 p.T) p.β := by
      symm
      apply cfpLift_uniq
      · rw [Category.assoc, cfpMap_fst,
          ← Category.assoc, cfpLift_fst,
          Category.comp_id]
      · rw [Category.assoc, cfpMap_snd,
          ← Category.assoc, cfpLift_snd,
          Category.id_comp]
    -- Intermediate: cfpLift β (𝟙 _) ≫
    -- cfpLiftAssoc ≫ snd = cfpLift β (snd)
    -- ≫ natTruncSub.
    have hLA :
        cfpLift p.β (𝟙 (cfpProd p.T p.T)) ≫
          cfpLiftAssoc natTruncSub
            natTruncSub ≫
            cfpSnd p.T p.T =
        cfpLift p.β (cfpSnd p.T p.T) ≫
          natTruncSub := by
      unfold cfpLiftAssoc
      rw [← Category.assoc, cfpLift_precomp,
        cfpLift_snd]
      -- Goal: cfpLift β (𝟙 _) ≫ cfpAssocSnd
      --   ≫ natTruncSub = cfpLift β (snd)
      --   ≫ natTruncSub
      rw [← Category.assoc]
      congr 1
      unfold cfpAssocSnd
      rw [cfpLift_precomp]
      apply cfpLift_uniq
      · rw [cfpLift_fst, cfpLift_fst]
      · rw [cfpLift_snd, ← Category.assoc,
          cfpLift_snd, Category.id_comp]
    rw [hββ, Category.assoc, natTruncSub_β]
    -- Goal: cfpLift β (𝟙 _) ≫ cfpLiftAssoc ≫
    --   (snd ≫ natPred) = cfpLift β (snd) ≫
    --   natTruncSub ≫ natPred
    -- Reassociate LHS to isolate (cfpLift β
    -- (𝟙 _) ≫ cfpLiftAssoc ≫ snd) ≫ natPred.
    have lhs_reassoc :
        cfpLift p.β (𝟙 (cfpProd p.T p.T)) ≫
          cfpLiftAssoc natTruncSub
            natTruncSub ≫
          (cfpSnd p.T p.T ≫ natPred) =
        (cfpLift p.β (𝟙 (cfpProd p.T p.T)) ≫
          cfpLiftAssoc natTruncSub
            natTruncSub ≫
          cfpSnd p.T p.T) ≫ natPred := by
      simp only [Category.assoc]
    rw [lhs_reassoc, hLA, Category.assoc]
  -- Step 2: show cfpLift β (snd) ≫ natTruncSub
  --   ≫ natPred = cfpLift (snd) (snd)
  --   ≫ natTruncSub via the peeling lemma.
  have step2 :
      cfpLift p.β (cfpSnd p.T p.T) ≫
        (natTruncSub ≫ natPred) =
      cfpLift (cfpSnd p.T p.T)
        (cfpSnd p.T p.T) ≫
        natTruncSub := by
    -- Factor cfpLift β (snd) = cfpLift (𝟙 _)
    --   (snd) ≫ cfpMap β (𝟙 T).
    have hβs :
        cfpLift p.β (cfpSnd p.T p.T) =
        cfpLift (𝟙 (cfpProd p.T p.T))
          (cfpSnd p.T p.T) ≫
          cfpMap p.β (𝟙 p.T) := by
      symm
      apply cfpLift_uniq
      · rw [Category.assoc, cfpMap_fst,
          ← Category.assoc, cfpLift_fst,
          Category.id_comp]
      · rw [Category.assoc, cfpMap_snd,
          ← Category.assoc, cfpLift_snd,
          Category.comp_id]
    rw [hβs, Category.assoc,
      β_natTruncSub_natPred, ← Category.assoc]
    -- Collapse cfpLift (𝟙 _) (snd) ≫
    --   cfpMap (snd) (𝟙 T).
    congr 1
    apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        ← Category.assoc, cfpLift_fst,
        Category.id_comp]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc, cfpLift_snd,
        Category.comp_id]
  rw [step1]
  exact step2

/-- Step case for the diagonal truncated
subtraction with `g = cfpSnd T T`. -/
private theorem diagTruncSub_step :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      diagTruncSub =
    cfpLiftAssoc diagTruncSub diagTruncSub ≫
      cfpSnd p.T p.T := by
  -- Both sides equal cfpLift (snd 1 (T×T) ≫
  --   snd T T) (snd 1 (T×T) ≫ snd T T) ≫
  --   natTruncSub.
  -- LHS via diag_β_natTruncSub; RHS via
  -- cfpLift_snd on cfpLiftAssoc.
  unfold diagTruncSub cfpLiftAssoc
  -- LHS: cfpMap (𝟙 1) β ≫ cfpLift (snd 1 T)
  --   (snd 1 T) ≫ natTruncSub.
  -- RHS: cfpLift (cfpAssocFst ≫ cfpLift (snd
  --   1 T) (snd 1 T) ≫ natTruncSub)
  --   (cfpAssocSnd ≫ cfpLift (snd 1 T) (snd
  --   1 T) ≫ natTruncSub) ≫ cfpSnd T T.
  rw [cfpLift_snd]
  -- RHS is now cfpAssocSnd ≫ cfpLift (snd 1 T)
  --   (snd 1 T) ≫ natTruncSub.
  -- LHS: rewrite cfpMap ≫ cfpLift via
  --   cfpLift_precomp, then use diag_β.
  rw [← Category.assoc, cfpLift_precomp,
    cfpMap_snd (𝟙 cfpTerminal) p.β,
    ← cfpLift_precomp, Category.assoc,
    diag_β_natTruncSub,
    ← Category.assoc]
  -- LHS: snd 1 (T×T) ≫ cfpLift (snd T T)
  --   (snd T T) ≫ natTruncSub.
  -- RHS: cfpAssocSnd ≫ cfpLift (snd 1 T)
  --   (snd 1 T) ≫ natTruncSub.
  -- Pre-compose parts are equal.
  -- snd 1 (T×T) ≫ cfpLift (snd T T) (snd T T)
  -- = cfpAssocSnd ≫ cfpLift (snd 1 T) (snd 1 T)
  -- Both map (*, (l, r)) to (r, r).
  have lhs_form :
      cfpSnd cfpTerminal
        (cfpProd p.T p.T) ≫
        cfpLift (cfpSnd p.T p.T)
          (cfpSnd p.T p.T) =
      cfpLift
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T)
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) :=
    cfpLift_precomp _ _ _
  have rhs_form :
      cfpAssocSnd cfpTerminal p.T p.T ≫
        cfpLift (cfpSnd cfpTerminal p.T)
          (cfpSnd cfpTerminal p.T) =
      cfpLift
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T)
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) := by
    rw [cfpLift_precomp]
    unfold cfpAssocSnd
    congr 1 <;>
      rw [cfpLift_snd]
  rw [lhs_form, ← rhs_form, Category.assoc]

/-- The constant-leaf morphism on
`cfpProd cfpTerminal T` satisfies the step
equation for `g = cfpSnd T T`. -/
private theorem constLeaf_step :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      (cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ) =
    cfpLiftAssoc
      (cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ)
      (cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ) ≫
      cfpSnd p.T p.T := by
  rw [← Category.assoc]
  have hterm :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        cfpTerminalFrom
          (cfpProd cfpTerminal p.T) =
      cfpTerminalFrom
        (cfpProd cfpTerminal
          (cfpProd p.T p.T)) :=
    h.terminal.uniq _
  rw [hterm]
  unfold cfpLiftAssoc
  rw [cfpLift_snd, ← Category.assoc]
  have hterm2 :
      cfpAssocSnd cfpTerminal p.T p.T ≫
        cfpTerminalFrom
          (cfpProd cfpTerminal p.T) =
      cfpTerminalFrom
        (cfpProd cfpTerminal
          (cfpProd p.T p.T)) :=
    h.terminal.uniq _
  rw [hterm2]

/-- The constant-leaf morphism on
`cfpProd cfpTerminal T` satisfies the base
equation for `f = p.ℓ`. -/
private theorem constLeaf_base :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      (cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ) =
    p.ℓ := by
  rw [← Category.assoc]
  have hterm :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        cfpTerminalFrom
          (cfpProd cfpTerminal p.T) =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [hterm, cfpTerminalFrom_terminal,
    Category.id_comp]

/-- Self-subtraction is zero:
`cfpLift (𝟙 T) (𝟙 T) ≫ natTruncSub
  = cfpTerminalFrom T ≫ p.ℓ`. -/
theorem natTruncSub_self :
    cfpLift (𝟙 p.T) (𝟙 p.T) ≫ natTruncSub =
    cfpTerminalFrom p.T ≫ p.ℓ := by
  -- Factor through cfpProd cfpTerminal T.
  have hfactor :
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        natTruncSub =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        diagTruncSub := by
    unfold diagTruncSub
    rw [← Category.assoc, cfpLift_precomp]
    simp only [cfpLift_snd]
  -- By elim_uniq, diagTruncSub =
  --   p.elim ℓ (cfpSnd T T).
  have h1 : diagTruncSub =
      p.elim p.ℓ (cfpSnd p.T p.T) :=
    p.elim_uniq p.ℓ (cfpSnd p.T p.T)
      diagTruncSub
      diagTruncSub_base
      diagTruncSub_step
  -- By elim_uniq, cfpTerminalFrom _ ≫ ℓ =
  --   p.elim ℓ (cfpSnd T T).
  have h2 :
      cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ =
      p.elim p.ℓ (cfpSnd p.T p.T) :=
    p.elim_uniq p.ℓ (cfpSnd p.T p.T)
      (cfpTerminalFrom _ ≫ p.ℓ)
      constLeaf_base
      constLeaf_step
  rw [hfactor, h1, ← h2]
  rw [← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- Equality on right-spine naturals via
truncated subtraction.
`natEq(m, n) = isLeafEndo(natPlus(m - n, n - m))`
where `m - n` and `n - m` are truncated
subtractions.  Returns `p.ℓ` iff `m = n` (as
right-spine nats), `treeFalse` otherwise. -/
def natEq : cfpProd p.T p.T ⟶ p.T :=
  cfpLift natTruncSub
    (cfpSwap p.T p.T ≫ natTruncSub) ≫
    natPlus ≫ isLeafEndo

/-- Reflexivity of `natEq`:
`cfpLift (𝟙 T) (𝟙 T) ≫ natEq
  = cfpTerminalFrom T ≫ p.ℓ`. -/
theorem natEq_refl :
    cfpLift (𝟙 p.T) (𝟙 p.T) ≫ natEq =
    cfpTerminalFrom p.T ≫
      (p.ℓ : cfpTerminal (C := C) ⟶ p.T)
      := by
  unfold natEq
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp]
  -- The two components both become
  -- cfpTerminalFrom T ≫ ℓ.
  have h1 :
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        natTruncSub =
      cfpTerminalFrom p.T ≫ p.ℓ :=
    natTruncSub_self
  have h2 :
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        cfpSwap p.T p.T ≫ natTruncSub =
      cfpTerminalFrom p.T ≫ p.ℓ := by
    rw [← Category.assoc]
    have hswap :
        cfpLift (𝟙 p.T) (𝟙 p.T) ≫
          cfpSwap p.T p.T =
        cfpLift (𝟙 p.T) (𝟙 p.T) := by
      unfold cfpSwap
      rw [cfpLift_precomp, cfpLift_fst,
        cfpLift_snd]
    rw [hswap, natTruncSub_self]
  rw [h1, h2, ← cfpLift_precomp]
  -- cfpTerminalFrom T ≫ cfpLift ℓ ℓ
  --   ≫ natPlus ≫ isLeafEndo
  --   = cfpTerminalFrom T ≫ ℓ
  have inner :
      cfpLift p.ℓ p.ℓ ≫ natPlus ≫
        isLeafEndo =
      (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
    rw [← Category.assoc, natPlus_ℓℓ,
      isLeafEndo_ℓ]
  simp only [Category.assoc]
  rw [inner]

/-- `natEq` is idempotent under `isLeafEndo`:
`natEq ≫ isLeafEndo = natEq`. -/
theorem natEq_bool :
    natEq ≫ isLeafEndo =
      (natEq : cfpProd p.T p.T ⟶ p.T) := by
  unfold natEq
  rw [Category.assoc, Category.assoc,
    isLeafEndo_idem]

end GebLean
