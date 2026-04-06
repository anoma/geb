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

/-- Step morphism for the triangular-number
catamorphism.  From the pair of recursive results
`((iL, sL), (iR, sR))`, extracts the right child's
result `(iR, sR)`, increments the index to
`natSucc(iR)`, and adds the new index to the running
sum to produce `(natSucc(iR), natPlus(natSucc(iR),
sR))`. -/
def natTriStep :
    cfpProd (cfpProd p.T p.T)
      (cfpProd p.T p.T) ⟶
      cfpProd p.T p.T :=
  cfpLift
    (cfpSnd (cfpProd p.T p.T)
      (cfpProd p.T p.T) ≫
      cfpFst p.T p.T ≫ natSucc)
    (cfpLift
      (cfpSnd (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpFst p.T p.T ≫ natSucc)
      (cfpSnd (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T) ≫
      natPlus)

/-- Parameterized catamorphism computing the pair
`(currentIndex, runningSum)` for the triangular
number.  At `n = leaf` (zero), the pair is
`(leaf, leaf) = (0, 0)`.  At each successor step,
the index is incremented and added to the running
sum. -/
def natTriHelper :
    cfpProd cfpTerminal p.T ⟶
      cfpProd p.T p.T :=
  p.elim (cfpLift p.ℓ p.ℓ) natTriStep

/-- Triangular number `tri(n) = n*(n+1)/2` on
right-spine naturals.  Computed by pairing the
terminal morphism with the identity (to form the
parameter), applying `natTriHelper`, and projecting
the second component (the running sum). -/
def natTri : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    natTriHelper ≫ cfpSnd p.T p.T

/-- Base case for `natTriHelper`:
`natTriHelper(*, leaf) = (leaf, leaf)`. -/
theorem natTriHelper_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      natTriHelper =
    cfpLift p.ℓ p.ℓ := by
  unfold natTriHelper
  exact p.elim_ℓ (cfpLift p.ℓ p.ℓ) _

/-- Step case for `natTriHelper`:
`natTriHelper(*, branch(l, r)) =
  natTriStep(natTriHelper(*, l),
    natTriHelper(*, r))`. -/
theorem natTriHelper_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      natTriHelper =
    cfpLiftAssoc natTriHelper natTriHelper ≫
      natTriStep := by
  unfold natTriHelper
  exact p.elim_β (cfpLift p.ℓ p.ℓ) _

/-- Leaf computation rule for `natTri`:
`tri(0) = 0`, i.e. `p.ℓ ≫ natTri = p.ℓ`. -/
theorem natTri_ℓ :
    p.ℓ ≫ natTri =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold natTri
  rw [← Category.assoc, ← Category.assoc]
  have factor :
      p.ℓ ≫ cfpLift (cfpTerminalFrom p.T)
        (𝟙 p.T) =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    have hterm :
        p.ℓ ≫ cfpTerminalFrom p.T =
        cfpTerminalFrom cfpTerminal :=
      h.terminal.uniq _
    rw [hterm, cfpTerminalFrom_terminal,
      Category.id_comp]
  rw [factor, natTriHelper_ℓ, cfpLift_snd]

/-- Cantor pairing on right-spine naturals:
`cantorPair(m, n) = natPlus(natTri(natPlus(m, n)),
m)`. -/
def cantorPair : cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (natPlus ≫ natTri)
    (cfpFst p.T p.T) ≫
    natPlus

/-- Truncated subtraction cancels successor on both
arguments:
`natTruncSub(succ(m), succ(n)) = natTruncSub(m, n)`.
Proof: applying `natTruncSub` to `(succ(m), succ(n))`
peels off one successor from the second argument (by
the step rule), producing
`natPred(natTruncSub(succ(m), n))`, then the peeling
lemma (`natSucc_natTruncSub_natPred`) cancels the
`natSucc`/`natPred` pair. -/
theorem natTruncSub_succ_succ {D : C}
    (a b : D ⟶ p.T) :
    cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
      natTruncSub =
    cfpLift a b ≫
      (natTruncSub : cfpProd p.T p.T ⟶ p.T)
    := by
  -- Step 1: peel one succ from the second arg.
  have step1 :
      cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
        natTruncSub =
      (cfpLift (a ≫ natSucc) b ≫
        natTruncSub) ≫ natPred := by
    unfold natTruncSub
    exact iterNat_cfpLift_succ natPred
      (a ≫ natSucc) b
  -- Step 2: factor the first argument.
  have factor :
      cfpLift (a ≫ natSucc) b =
      cfpLift a b ≫
        cfpMap natSucc (𝟙 p.T) := by
    symm
    apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        ← Category.assoc, cfpLift_fst]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc, cfpLift_snd,
        Category.comp_id]
  rw [step1, factor, Category.assoc,
    Category.assoc,
    natSucc_natTruncSub_natPred]

/-- Successor cancellation for `natEq`:
`natEq(succ(m), succ(n)) = natEq(m, n)`. -/
theorem natEq_succ_cancel {D : C}
    (a b : D ⟶ p.T) :
    cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
      natEq =
    cfpLift a b ≫
      (natEq : cfpProd p.T p.T ⟶ p.T)
    := by
  unfold natEq
  -- Both sides have the form
  -- cfpLift X (cfpSwap ≫ X) ≫ natPlus ≫ isLeafEndo
  -- where X = natTruncSub precomposed differently.
  -- Reduce the truncated subtraction components.
  have h1 :
      cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
        natTruncSub =
      cfpLift a b ≫ natTruncSub :=
    natTruncSub_succ_succ a b
  have hswap :
      cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
        cfpSwap p.T p.T =
      cfpLift (b ≫ natSucc) (a ≫ natSucc) := by
    unfold cfpSwap
    rw [cfpLift_precomp, cfpLift_fst,
      cfpLift_snd]
  have hswap2 :
      cfpLift a b ≫ cfpSwap p.T p.T =
      cfpLift b a := by
    unfold cfpSwap
    rw [cfpLift_precomp, cfpLift_fst,
      cfpLift_snd]
  have h2 :
      cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
        cfpSwap p.T p.T ≫ natTruncSub =
      cfpLift a b ≫
        cfpSwap p.T p.T ≫ natTruncSub := by
    rw [← Category.assoc, hswap,
      natTruncSub_succ_succ,
      ← Category.assoc, ← hswap2,
      Category.assoc]
  -- Rewrite both sides to:
  -- cfpLift (cfpLift a b ≫ natTruncSub)
  --   (cfpLift a b ≫ cfpSwap ≫ natTruncSub) ≫
  --   natPlus ≫ isLeafEndo.
  -- LHS: unfold natEq and distribute the outer lift.
  have lhs :
      cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
        cfpLift natTruncSub
          (cfpSwap p.T p.T ≫ natTruncSub) ≫
          natPlus ≫ isLeafEndo =
      (cfpLift
        (cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
          natTruncSub)
        (cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
          cfpSwap p.T p.T ≫ natTruncSub) ≫
        natPlus) ≫ isLeafEndo := by
    rw [← Category.assoc
      (cfpLift (a ≫ natSucc) (b ≫ natSucc))
      (cfpLift natTruncSub
        (cfpSwap p.T p.T ≫ natTruncSub))
      (natPlus ≫ isLeafEndo),
      cfpLift_precomp,
      Category.assoc]
  have rhs :
      cfpLift a b ≫
        cfpLift natTruncSub
          (cfpSwap p.T p.T ≫ natTruncSub) ≫
          natPlus ≫ isLeafEndo =
      (cfpLift
        (cfpLift a b ≫ natTruncSub)
        (cfpLift a b ≫
          cfpSwap p.T p.T ≫ natTruncSub) ≫
        natPlus) ≫ isLeafEndo := by
    rw [← Category.assoc
      (cfpLift a b)
      (cfpLift natTruncSub
        (cfpSwap p.T p.T ≫ natTruncSub))
      (natPlus ≫ isLeafEndo),
      cfpLift_precomp,
      Category.assoc]
  rw [lhs, rhs, h1, h2]

/-- Adding a successor in the second argument:
`natPlus(m, succ(n)) = succ(natPlus(m, n))`. -/
theorem natPlus_succ {D : C}
    (a b : D ⟶ p.T) :
    cfpLift a (b ≫ natSucc) ≫ natPlus =
    (cfpLift a b ≫ natPlus) ≫
      (natSucc : p.T ⟶ p.T) := by
  unfold natPlus
  exact iterNat_cfpLift_succ natSucc a b

/-- Adding zero in the second argument:
`natPlus(m, 0) = m`. -/
theorem natPlus_zero {D : C}
    (a : D ⟶ p.T) :
    cfpLift a (cfpTerminalFrom D ≫ p.ℓ) ≫
      natPlus = a := by
  unfold natPlus
  exact iterNat_cfpLift_ℓ natSucc a

/-- The `natSucc` step morphism commutes with
itself in the sense required by
`elim_algebra_morphism`. -/
private theorem natSucc_step_comm :
    cfpMap natSucc natSucc ≫
      (cfpSnd p.T p.T ≫ natSucc) =
    (cfpSnd p.T p.T ≫ natSucc) ≫
      (natSucc : p.T ⟶ p.T) := by
  rw [← Category.assoc
    (cfpMap natSucc natSucc),
    cfpMap_snd, Category.assoc]

/-- Post-composing `natPlus` with `natSucc` yields
the catamorphism with `natSucc` as base:
`natPlus ≫ natSucc =
  p.elim natSucc (cfpSnd T T ≫ natSucc)`. -/
theorem natPlus_natSucc :
    natPlus ≫ natSucc =
    p.elim (natSucc : p.T ⟶ p.T)
      (cfpSnd p.T p.T ≫ natSucc) := by
  unfold natPlus
  rw [elim_algebra_morphism
    (𝟙 p.T) (cfpSnd p.T p.T ≫ natSucc)
    natSucc (cfpSnd p.T p.T ≫ natSucc)
    natSucc_step_comm, Category.id_comp]

/-- Adding a successor in the first argument:
`natPlus(succ(m), n) = succ(natPlus(m, n))`. -/
theorem natPlus_succ_left {D : C}
    (a b : D ⟶ p.T) :
    cfpLift (a ≫ natSucc) b ≫ natPlus =
    (cfpLift a b ≫ natPlus) ≫
      (natSucc : p.T ⟶ p.T) := by
  have factor :
      cfpLift (a ≫ natSucc) b =
      cfpLift a b ≫
        cfpMap natSucc (𝟙 p.T) := by
    symm
    apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        ← Category.assoc, cfpLift_fst]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc, cfpLift_snd,
        Category.comp_id]
  rw [factor, Category.assoc]
  -- cfpMap natSucc (𝟙 T) ≫ natPlus =
  -- natPlus ≫ natSucc
  -- by elim_naturality + natPlus_natSucc.
  unfold natPlus
  rw [elim_naturality natSucc (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natSucc),
    Category.comp_id,
    ← natPlus_natSucc]
  unfold natPlus
  rw [Category.assoc]

/-- The morphism `(T × T) × T ⟶ T` computing
`natEq(natPlus(fst(fst), snd),
  natPlus(snd(fst), snd))`.
From the triple `((a, b), c)`, computes
`natEq(a + c, b + c)`. -/
private def natEqPlusCommon :
    cfpProd (cfpProd p.T p.T) p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (cfpFst (cfpProd p.T p.T) p.T ≫
        cfpFst p.T p.T)
      (cfpSnd (cfpProd p.T p.T) p.T) ≫
      natPlus)
    (cfpLift
      (cfpFst (cfpProd p.T p.T) p.T ≫
        cfpSnd p.T p.T)
      (cfpSnd (cfpProd p.T p.T) p.T) ≫
      natPlus) ≫
    natEq

/-- Base case for `natEqPlusCommon`:
`natEqPlusCommon((a, b), leaf) = natEq(a, b)`. -/
private theorem natEqPlusCommon_base :
    cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
      natEqPlusCommon =
    natEq := by
  unfold natEqPlusCommon
  rw [← Category.assoc, cfpLift_precomp]
  -- Each component simplifies via natPlus_zero.
  have h_fst :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpLift
          (cfpFst (cfpProd p.T p.T) p.T ≫
            cfpFst p.T p.T)
          (cfpSnd (cfpProd p.T p.T) p.T) ≫
        natPlus =
      cfpFst p.T p.T := by
    rw [← Category.assoc, cfpLift_precomp]
    unfold cfpInsertSnd
    rw [← Category.assoc
      (cfpLift (𝟙 _) _)
      (cfpFst _ _) (cfpFst _ _),
      cfpLift_fst, Category.id_comp,
      cfpLift_snd]
    exact natPlus_zero (cfpFst p.T p.T)
  have h_snd :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpLift
          (cfpFst (cfpProd p.T p.T) p.T ≫
            cfpSnd p.T p.T)
          (cfpSnd (cfpProd p.T p.T) p.T) ≫
        natPlus =
      cfpSnd p.T p.T := by
    rw [← Category.assoc, cfpLift_precomp]
    unfold cfpInsertSnd
    rw [← Category.assoc
      (cfpLift (𝟙 _) _)
      (cfpFst _ _) (cfpSnd _ _),
      cfpLift_fst, Category.id_comp,
      cfpLift_snd]
    exact natPlus_zero (cfpSnd p.T p.T)
  rw [h_fst, h_snd]
  have eta :
      𝟙 (cfpProd p.T p.T) =
      cfpLift (cfpFst p.T p.T)
        (cfpSnd p.T p.T) :=
    cfpLift_uniq _ _
      (𝟙 _)
      (Category.id_comp _)
      (Category.id_comp _)
  rw [← eta, Category.id_comp]

/-- Step case for `natEqPlusCommon`:
`natEqPlusCommon((a,b), β(l,r)) =
  natEqPlusCommon((a,b), r)`.
In `p.elim` form, the step algebra is
`cfpSnd T T` (project the right child's result). -/
private theorem natEqPlusCommon_step :
    cfpMap (𝟙 (cfpProd p.T p.T)) p.β ≫
      natEqPlusCommon =
    cfpLiftAssoc natEqPlusCommon
      natEqPlusCommon ≫ cfpSnd p.T p.T := by
  -- Both sides equal cfpLift (cfpLift (fst≫fst)
  -- (snd≫snd) ≫ natPlus) (cfpLift (fst≫snd)
  -- (snd≫snd) ≫ natPlus) ≫ natEq, where fst/snd
  -- project from (T×T)×(T×T).
  -- We prove both sides equal this common form.
  -- Abbreviate P = cfpProd T T.
  -- Common target.
  set P := cfpProd p.T p.T
  -- The common form (from P×P):
  let target :
      cfpProd P P ⟶ p.T :=
    cfpLift
      (cfpLift (cfpFst P P ≫ cfpFst p.T p.T)
        (cfpSnd P P ≫ cfpSnd p.T p.T) ≫
        natPlus)
      (cfpLift (cfpFst P P ≫ cfpSnd p.T p.T)
        (cfpSnd P P ≫ cfpSnd p.T p.T) ≫
        natPlus) ≫ natEq
  -- LHS = target.
  -- Helper: cfpAssocSnd pushes through natPlus
  -- components.
  have assocSnd_comp (proj : P ⟶ p.T) :
      cfpAssocSnd P p.T p.T ≫
        cfpLift (cfpFst P p.T ≫ proj)
          (cfpSnd P p.T) ≫ natPlus =
      cfpLift (cfpFst P P ≫ proj)
        (cfpSnd P P ≫ cfpSnd p.T p.T) ≫
        natPlus := by
    rw [← Category.assoc, cfpLift_precomp]
    unfold cfpAssocSnd
    rw [← Category.assoc, cfpLift_fst,
      cfpLift_snd]
  -- Prove RHS = target.
  have rhs_eq :
      cfpLiftAssoc natEqPlusCommon
        natEqPlusCommon ≫ cfpSnd p.T p.T =
      target := by
    unfold cfpLiftAssoc
    rw [cfpLift_snd]
    unfold natEqPlusCommon
    rw [← Category.assoc, cfpLift_precomp,
      assocSnd_comp (cfpFst p.T p.T),
      assocSnd_comp (cfpSnd p.T p.T)]
  -- Prove LHS = target.
  suffices lhs_eq :
      cfpMap (𝟙 P) p.β ≫ natEqPlusCommon =
      target from
    lhs_eq.trans rhs_eq.symm
  -- Prove LHS = target.
  unfold natEqPlusCommon
  rw [← Category.assoc, cfpLift_precomp]
  -- Each natPlus component: cfpMap ≫ cfpLift ≫
  -- natPlus = ... ≫ natPlus ≫ natSucc.
  have cfpMap_comp_natPlus (proj : P ⟶ p.T) :
      cfpMap (𝟙 P) p.β ≫
        (cfpLift (cfpFst P p.T ≫ proj)
          (cfpSnd P p.T) ≫ natPlus) =
      (cfpLift (cfpFst P P ≫ proj)
        (cfpSnd P P ≫ cfpSnd p.T p.T) ≫
        natPlus) ≫ natSucc := by
    rw [← Category.assoc, cfpLift_precomp,
      ← Category.assoc, cfpMap_fst,
      Category.assoc, Category.id_comp,
      cfpMap_snd]
    -- cfpLift (fst(P,P) ≫ proj) (snd(P,P) ≫ β)
    -- ≫ natPlus = (...) ≫ natPlus ≫ natSucc.
    -- Factor snd(P,P) ≫ β through cfpMap (𝟙 T) β.
    have factor :
        cfpLift (cfpFst P P ≫ proj)
          (cfpSnd P P ≫ p.β) =
        cfpLift (cfpFst P P ≫ proj)
          (cfpSnd P P) ≫
          cfpMap (𝟙 p.T) p.β := by
      symm; apply cfpLift_uniq
      · rw [Category.assoc, cfpMap_fst,
          ← Category.assoc, cfpLift_fst,
          Category.comp_id]
      · rw [Category.assoc, cfpMap_snd,
          ← Category.assoc, cfpLift_snd]
    rw [factor, Category.assoc, natPlus_β]
    -- cfpLiftAssoc ≫ cfpSnd ≫ natSucc projects
    -- the right child's natPlus result.
    unfold cfpLiftAssoc
    rw [← Category.assoc, ← Category.assoc,
      cfpLift_precomp, cfpLift_snd,
      Category.assoc, ← Category.assoc,
      ← Category.assoc]
    congr 1; congr 1
    unfold cfpAssocSnd
    rw [cfpLift_precomp, cfpLift_fst,
      ← Category.assoc, cfpLift_snd]
  rw [cfpMap_comp_natPlus (cfpFst p.T p.T),
    cfpMap_comp_natPlus (cfpSnd p.T p.T),
    natEq_succ_cancel]

/-- The constant-natEq morphism on
`cfpProd (cfpProd T T) T` satisfies the base
equation. -/
private theorem constNatEq_base :
    cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
      (cfpFst (cfpProd p.T p.T) p.T ≫ natEq) =
    natEq := by
  rw [← Category.assoc]
  unfold cfpInsertSnd
  rw [cfpLift_fst, Category.id_comp]

/-- The constant-natEq morphism on
`cfpProd (cfpProd T T) T` satisfies the step
equation with step `cfpSnd T T`. -/
private theorem constNatEq_step :
    cfpMap (𝟙 (cfpProd p.T p.T)) p.β ≫
      (cfpFst (cfpProd p.T p.T) p.T ≫ natEq) =
    cfpLiftAssoc
      (cfpFst (cfpProd p.T p.T) p.T ≫ natEq)
      (cfpFst (cfpProd p.T p.T) p.T ≫ natEq) ≫
      cfpSnd p.T p.T := by
  rw [← Category.assoc, cfpMap_fst,
    Category.comp_id]
  unfold cfpLiftAssoc
  rw [cfpLift_snd]
  unfold cfpAssocSnd
  rw [← Category.assoc, cfpLift_fst]

/-- Right cancellation for `natPlus` under `natEq`:
`natEq(a + c, b + c) = natEq(a, b)` for all
`a, b, c`.  Both `natEqPlusCommon` and the constant
morphism `cfpFst ≫ natEq` satisfy the same
`p.elim` equations (base = `natEq`, step =
`cfpSnd T T`), hence they are equal by
`p.elim_uniq`. -/
theorem natPlus_cancel_right {D : C}
    (a b c : D ⟶ p.T) :
    cfpLift (cfpLift a c ≫ natPlus)
      (cfpLift b c ≫ natPlus) ≫ natEq =
    cfpLift a b ≫
      (natEq : cfpProd p.T p.T ⟶ p.T) := by
  -- Factor through cfpProd (cfpProd T T) T.
  -- Helper: projections simplify.
  have proj_helper (proj : cfpProd p.T p.T ⟶ p.T) :
      cfpLift (cfpLift a b) c ≫
        cfpLift
          (cfpFst (cfpProd p.T p.T) p.T ≫
            proj)
          (cfpSnd (cfpProd p.T p.T) p.T) =
      cfpLift (cfpLift a b ≫ proj) c := by
    rw [cfpLift_precomp, ← Category.assoc,
      cfpLift_fst, cfpLift_snd]
  have factor :
      cfpLift (cfpLift a c ≫ natPlus)
        (cfpLift b c ≫ natPlus) ≫ natEq =
      cfpLift (cfpLift a b) c ≫
        natEqPlusCommon := by
    unfold natEqPlusCommon
    rw [← Category.assoc, cfpLift_precomp]
    -- Simplify each component.
    have h1 :
        cfpLift (cfpLift a b) c ≫
          cfpLift
            (cfpFst (cfpProd p.T p.T) p.T ≫
              cfpFst p.T p.T)
            (cfpSnd (cfpProd p.T p.T) p.T) ≫
          natPlus =
        cfpLift a c ≫ natPlus := by
      rw [← Category.assoc,
        proj_helper (cfpFst p.T p.T),
        cfpLift_fst]
    have h2 :
        cfpLift (cfpLift a b) c ≫
          cfpLift
            (cfpFst (cfpProd p.T p.T) p.T ≫
              cfpSnd p.T p.T)
            (cfpSnd (cfpProd p.T p.T) p.T) ≫
          natPlus =
        cfpLift b c ≫ natPlus := by
      rw [← Category.assoc,
        proj_helper (cfpSnd p.T p.T),
        cfpLift_snd]
    rw [h1, h2]
  have factor2 :
      cfpLift a b ≫ natEq =
      cfpLift (cfpLift a b) c ≫
        (cfpFst (cfpProd p.T p.T) p.T ≫
          natEq) := by
    rw [← Category.assoc, cfpLift_fst]
  rw [factor, factor2]
  -- By p.elim_uniq, natEqPlusCommon = cfpFst ≫ natEq.
  congr 1
  exact (p.elim_uniq natEq (cfpSnd p.T p.T)
    natEqPlusCommon
    natEqPlusCommon_base
    natEqPlusCommon_step).trans
    (p.elim_uniq natEq (cfpSnd p.T p.T)
      (cfpFst (cfpProd p.T p.T) p.T ≫ natEq)
      constNatEq_base
      constNatEq_step).symm

/-- The parameterized morphism computing
`natPlus(natPlus(a, b), c)` from
`((a, b), c) : cfpProd (cfpProd T T) T`. -/
private def natPlusAssocLeft :
    cfpProd (cfpProd p.T p.T) p.T ⟶ p.T :=
  cfpLift
    (cfpFst (cfpProd p.T p.T) p.T ≫ natPlus)
    (cfpSnd (cfpProd p.T p.T) p.T) ≫ natPlus

/-- The parameterized morphism computing
`natPlus(a, natPlus(b, c))` from
`((a, b), c) : cfpProd (cfpProd T T) T`. -/
private def natPlusAssocRight :
    cfpProd (cfpProd p.T p.T) p.T ⟶ p.T :=
  cfpLift
    (cfpFst (cfpProd p.T p.T) p.T ≫
      cfpFst p.T p.T)
    (cfpLift
      (cfpFst (cfpProd p.T p.T) p.T ≫
        cfpSnd p.T p.T)
      (cfpSnd (cfpProd p.T p.T) p.T) ≫
      natPlus) ≫ natPlus

/-- Base case for `natPlusAssocLeft`:
`natPlusAssocLeft((a,b), leaf) = natPlus(a,b)`.
-/
private theorem natPlusAssocLeft_base :
    cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
      natPlusAssocLeft =
    natPlus := by
  unfold natPlusAssocLeft
  rw [← Category.assoc, cfpLift_precomp]
  have hfst :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpFst (cfpProd p.T p.T) p.T ≫
        natPlus =
      natPlus := by
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_fst,
      Category.id_comp]
  have hsnd :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpSnd (cfpProd p.T p.T) p.T =
      cfpTerminalFrom (cfpProd p.T p.T) ≫
        p.ℓ := by
    unfold cfpInsertSnd; rw [cfpLift_snd]
  rw [hfst, hsnd]
  exact natPlus_zero natPlus

end GebLean
