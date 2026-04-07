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
  have step1 :
      cfpLift p.β p.β ≫ natTruncSub =
      cfpLift p.β (cfpSnd p.T p.T) ≫
        natTruncSub ≫ natPred := by
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
      rw [← Category.assoc]
      congr 1
      unfold cfpAssocSnd
      rw [cfpLift_precomp]
      apply cfpLift_uniq
      · rw [cfpLift_fst, cfpLift_fst]
      · rw [cfpLift_snd, ← Category.assoc,
          cfpLift_snd, Category.id_comp]
    rw [hββ, Category.assoc, natTruncSub_β]
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
  have step2 :
      cfpLift p.β (cfpSnd p.T p.T) ≫
        (natTruncSub ≫ natPred) =
      cfpLift (cfpSnd p.T p.T)
        (cfpSnd p.T p.T) ≫
        natTruncSub := by
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
  unfold diagTruncSub cfpLiftAssoc
  rw [cfpLift_snd]
  rw [← Category.assoc, cfpLift_precomp,
    cfpMap_snd (𝟙 cfpTerminal) p.β,
    ← cfpLift_precomp, Category.assoc,
    diag_β_natTruncSub,
    ← Category.assoc]
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
  have hfactor :
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        natTruncSub =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        diagTruncSub := by
    unfold diagTruncSub
    rw [← Category.assoc, cfpLift_precomp]
    simp only [cfpLift_snd]
  have h1 : diagTruncSub =
      p.elim p.ℓ (cfpSnd p.T p.T) :=
    p.elim_uniq p.ℓ (cfpSnd p.T p.T)
      diagTruncSub
      diagTruncSub_base
      diagTruncSub_step
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
  have step1 :
      cfpLift (a ≫ natSucc) (b ≫ natSucc) ≫
        natTruncSub =
      (cfpLift (a ≫ natSucc) b ≫
        natTruncSub) ≫ natPred := by
    unfold natTruncSub
    exact iterNat_cfpLift_succ natPred
      (a ≫ natSucc) b
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
  suffices lhs_eq :
      cfpMap (𝟙 P) p.β ≫ natEqPlusCommon =
      target from
    lhs_eq.trans rhs_eq.symm
  unfold natEqPlusCommon
  rw [← Category.assoc, cfpLift_precomp]
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

/-- `natPlusAssocLeft` equals `cfpMap natPlus (𝟙 T)
≫ natPlus`.  This factors it as a composition of
`natPlus` applied to the parameter projection,
followed by `natPlus` on the result paired with the
third component. -/
private theorem natPlusAssocLeft_cfpMap :
    natPlusAssocLeft =
    cfpMap (natPlus : cfpProd p.T p.T ⟶ p.T)
      (𝟙 p.T) ≫ natPlus := by
  unfold natPlusAssocLeft
  congr 1
  symm
  unfold cfpMap
  apply cfpLift_uniq
  · rw [cfpLift_fst]
  · rw [cfpLift_snd, Category.comp_id]

/-- `natPlusAssocLeft` equals the parameterized
catamorphism `p.elim natPlus (cfpSnd ≫ natSucc)`. -/
private theorem natPlusAssocLeft_elim :
    natPlusAssocLeft =
    p.elim (natPlus : cfpProd p.T p.T ⟶ p.T)
      (cfpSnd p.T p.T ≫ natSucc) := by
  rw [natPlusAssocLeft_cfpMap]
  unfold natPlus
  rw [elim_naturality
    (p.elim (𝟙 p.T)
      (cfpSnd p.T p.T ≫ natSucc))
    (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natSucc),
    Category.comp_id]

/-- Base case for `natPlusAssocRight`:
`natPlusAssocRight((a,b), leaf) = natPlus(a,b)`. -/
private theorem natPlusAssocRight_base :
    cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
      natPlusAssocRight =
    natPlus := by
  unfold natPlusAssocRight
  rw [← Category.assoc, cfpLift_precomp]
  have hsnd :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpSnd (cfpProd p.T p.T) p.T =
      cfpTerminalFrom (cfpProd p.T p.T) ≫
        p.ℓ := by
    unfold cfpInsertSnd; rw [cfpLift_snd]
  have hfst_fst :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpFst (cfpProd p.T p.T) p.T ≫
        cfpFst p.T p.T =
      cfpFst p.T p.T := by
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_fst,
      Category.id_comp]
  have hfst_snd :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpFst (cfpProd p.T p.T) p.T ≫
        cfpSnd p.T p.T =
      cfpSnd p.T p.T := by
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_fst,
      Category.id_comp]
  have hinner :
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
        cfpLift
          (cfpFst (cfpProd p.T p.T) p.T ≫
            cfpSnd p.T p.T)
          (cfpSnd (cfpProd p.T p.T) p.T) ≫
        natPlus =
      cfpSnd p.T p.T := by
    rw [← Category.assoc, cfpLift_precomp,
      hfst_snd, hsnd]
    exact natPlus_zero (cfpSnd p.T p.T)
  rw [hfst_fst, hinner]
  have eta :
      cfpLift (cfpFst p.T p.T) (cfpSnd p.T p.T) =
      𝟙 (cfpProd p.T p.T) :=
    (cfpLift_uniq _ _
      (𝟙 _) (Category.id_comp _)
      (Category.id_comp _)).symm
  rw [eta, Category.id_comp]

/-- Associativity of `natPlus`:
`natPlus(natPlus(a, b), c) =
  natPlus(a, natPlus(b, c))`. -/
theorem natPlus_assoc {D : C}
    (a b c : D ⟶ p.T) :
    cfpLift (cfpLift a b ≫ natPlus) c ≫
      natPlus =
    cfpLift a (cfpLift b c ≫ natPlus) ≫
      natPlus := by
  have lhs_factor :
      cfpLift (cfpLift a b ≫ natPlus) c =
      cfpLift (𝟙 D) c ≫
        cfpMap (cfpLift a b ≫ natPlus)
          (𝟙 p.T) := by
    symm; apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        ← Category.assoc, cfpLift_fst,
        Category.id_comp]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc, cfpLift_snd,
        Category.comp_id]
  have lhs_elim :
      cfpMap (cfpLift a b ≫ natPlus) (𝟙 p.T) ≫
        natPlus =
      p.elim (cfpLift a b ≫ natPlus)
        (cfpSnd p.T p.T ≫ natSucc) := by
    unfold natPlus
    rw [elim_naturality
      (cfpLift a b ≫
        p.elim (𝟙 p.T)
          (cfpSnd p.T p.T ≫ natSucc))
      (𝟙 p.T)
      (cfpSnd p.T p.T ≫ natSucc),
      Category.comp_id]
  rw [lhs_factor, Category.assoc, lhs_elim]
  have inner_factor :
      cfpLift b c =
      cfpLift (𝟙 D) c ≫
        cfpMap b (𝟙 p.T) := by
    symm; apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        ← Category.assoc, cfpLift_fst,
        Category.id_comp]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc, cfpLift_snd,
        Category.comp_id]
  have inner_elim :
      cfpMap b (𝟙 p.T) ≫ natPlus =
      p.elim b
        (cfpSnd p.T p.T ≫ natSucc) := by
    unfold natPlus
    rw [elim_naturality b (𝟙 p.T)
      (cfpSnd p.T p.T ≫ natSucc),
      Category.comp_id]
  rw [inner_factor, Category.assoc, inner_elim]
  set eb := p.elim b
    (cfpSnd p.T p.T ≫ natSucc)
  have rhs_factor :
      cfpLift a (cfpLift (𝟙 D) c ≫ eb) =
      cfpLift (𝟙 D) c ≫
        cfpLift (cfpFst D p.T ≫ a) eb := by
    rw [cfpLift_precomp,
      ← Category.assoc
        (cfpLift (𝟙 D) c) (cfpFst D p.T) a,
      cfpLift_fst,
      Category.id_comp]
  rw [rhs_factor, Category.assoc]
  congr 1
  apply (p.elim_uniq
    (cfpLift a b ≫ natPlus)
    (cfpSnd p.T p.T ≫ natSucc)
    (cfpLift (cfpFst D p.T ≫ a) eb ≫ natPlus)
    _ _).symm
  -- Base case.
  · rw [← Category.assoc, cfpLift_precomp]
    have hfst :
        cfpInsertSnd p.ℓ D ≫
          (cfpFst D p.T ≫ a) =
        a := by
      unfold cfpInsertSnd
      rw [← Category.assoc, cfpLift_fst,
        Category.id_comp]
    have hsnd :
        cfpInsertSnd p.ℓ D ≫ eb = b := by
      simp only [eb]
      exact p.elim_ℓ b
        (cfpSnd p.T p.T ≫ natSucc)
    rw [hfst, hsnd]
  -- Step case.
  · rw [← Category.assoc, cfpLift_precomp]
    have hfst :
        cfpMap (𝟙 D) p.β ≫
          (cfpFst D p.T ≫ a) =
        cfpFst D (cfpProd p.T p.T) ≫ a := by
      rw [← Category.assoc,
        cfpMap_fst, Category.comp_id]
    have heb :
        cfpMap (𝟙 D) p.β ≫ eb =
        cfpLiftAssoc eb eb ≫
          (cfpSnd p.T p.T ≫ natSucc) := by
      simp only [eb]
      exact p.elim_β b
        (cfpSnd p.T p.T ≫ natSucc)
    rw [hfst, heb]
    rw [← Category.assoc
      (cfpLiftAssoc eb eb)
      (cfpSnd p.T p.T) natSucc]
    unfold cfpLiftAssoc
    rw [cfpLift_snd]
    rw [natPlus_succ]
    rw [← Category.assoc (cfpLift _ _)
      (cfpSnd p.T p.T),
      cfpLift_snd]
    congr 1
    rw [← Category.assoc
      (cfpAssocSnd D p.T p.T)
      (cfpLift (cfpFst D p.T ≫ a) eb),
      cfpLift_precomp,
      ← Category.assoc
        (cfpAssocSnd D p.T p.T)
        (cfpFst D p.T) a]
    unfold cfpAssocSnd
    rw [cfpLift_fst]

/-- The single-pair version of `natTriStep`: given
`(i, s)`, produces
`(natSucc(i), natPlus(natSucc(i), s))`. -/
private def natTriStepSingle :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift
    (cfpFst p.T p.T ≫ natSucc)
    (cfpLift
      (cfpFst p.T p.T ≫ natSucc)
      (cfpSnd p.T p.T) ≫
      natPlus)

/-- `natTriStep` factors through `cfpSnd` and
`natTriStepSingle`:
`natTriStep = cfpSnd ≫ natTriStepSingle`. -/
private theorem natTriStep_factor :
    natTriStep =
    cfpSnd (cfpProd p.T p.T)
      (cfpProd p.T p.T) ≫
      (natTriStepSingle :
        cfpProd p.T p.T ⟶ cfpProd p.T p.T) := by
  unfold natTriStep natTriStepSingle
  conv_rhs =>
    rw [cfpLift_precomp]
  congr 1
  conv_rhs =>
    rw [← Category.assoc, cfpLift_precomp]

/-- The step case of `natTriHelper` factors through
the right child only:
`cfpMap (𝟙) p.β ≫ natTriHelper =
  cfpAssocSnd ≫ natTriHelper ≫ natTriStepSingle`.
-/
private theorem natTriHelper_β_factor :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      natTriHelper =
    cfpAssocSnd cfpTerminal p.T p.T ≫
      natTriHelper ≫
      (natTriStepSingle :
        cfpProd p.T p.T ⟶ cfpProd p.T p.T) := by
  rw [natTriHelper_β, natTriStep_factor,
    ← Category.assoc, ← Category.assoc]
  unfold cfpLiftAssoc
  rw [cfpLift_snd, Category.assoc]

/-- Single-input step for the combined state
`((index, tri), natPlus(index, tri))`.  From
`((i, s), v)`, produces
`(natTriStepSingle(i, s),
  natSucc(natSucc(natPlus(i, v))))`. -/
private def natTriPlusStepSingle :
    cfpProd (cfpProd p.T p.T) p.T ⟶
      cfpProd (cfpProd p.T p.T) p.T :=
  cfpLift
    (cfpFst (cfpProd p.T p.T) p.T ≫
      natTriStepSingle)
    (cfpLift
      (cfpFst (cfpProd p.T p.T) p.T ≫
        cfpFst p.T p.T)
      (cfpSnd (cfpProd p.T p.T) p.T) ≫
      natPlus ≫ natSucc ≫ natSucc)

/-- Combined step for the `p.elim` that produces
the triple `(natTriHelper, extra)`, where the step
only depends on the right child. -/
private def natTriPlusCombinedStep :
    cfpProd (cfpProd (cfpProd p.T p.T) p.T)
      (cfpProd (cfpProd p.T p.T) p.T) ⟶
      cfpProd (cfpProd p.T p.T) p.T :=
  cfpSnd (cfpProd (cfpProd p.T p.T) p.T)
    (cfpProd (cfpProd p.T p.T) p.T) ≫
    natTriPlusStepSingle

/-- Base case: `Ψ₁(*, leaf) =
((leaf, leaf), leaf)`. -/
private theorem natTriPlus1_base :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      cfpLift natTriHelper
        (natTriHelper ≫ natPlus) =
    cfpLift (cfpLift p.ℓ p.ℓ) p.ℓ := by
  rw [cfpLift_precomp, natTriHelper_ℓ]
  congr 1
  rw [← Category.assoc, natTriHelper_ℓ,
    natPlus_ℓℓ]

/-- Composing `natTriStepSingle` with `natPlus`
yields `cfpLift cfpFst natPlus ≫ natPlus ≫
natSucc ≫ natSucc`. -/
private theorem natTriStepSingle_natPlus :
    natTriStepSingle ≫ natPlus =
    cfpLift (cfpFst p.T p.T)
      (natPlus : cfpProd p.T p.T ⟶ p.T) ≫
      natPlus ≫ natSucc ≫ natSucc := by
  unfold natTriStepSingle
  rw [natPlus_succ_left
    (cfpFst p.T p.T)
    (cfpLift (cfpFst p.T p.T ≫ natSucc)
      (cfpSnd p.T p.T) ≫ natPlus)]
  have inner :
      cfpLift (cfpFst p.T p.T ≫ natSucc)
        (cfpSnd p.T p.T) ≫ natPlus =
      natPlus ≫ natSucc := by
    rw [natPlus_succ_left
      (cfpFst p.T p.T)
      (cfpSnd p.T p.T)]
    have eta :
        cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T) =
        𝟙 (cfpProd p.T p.T) :=
      (cfpLift_uniq _ _ (𝟙 _)
        (Category.id_comp _)
        (Category.id_comp _)).symm
    rw [eta, Category.id_comp]
  rw [inner]
  rw [natPlus_succ
    (cfpFst p.T p.T)
    (natPlus : cfpProd p.T p.T ⟶ p.T)]
  simp only [Category.assoc]

/-- `cfpLift natTriHelper (natTriHelper ≫ natPlus)`
satisfies the `p.elim` equations with base
`cfpLift (cfpLift p.ℓ p.ℓ) p.ℓ` and step
`natTriPlusCombinedStep`. -/
private theorem natTriPlus1_elim :
    cfpLift natTriHelper
      (natTriHelper ≫ natPlus) =
    p.elim
      (cfpLift (cfpLift p.ℓ p.ℓ) p.ℓ)
      (natTriPlusCombinedStep :
        cfpProd
          (cfpProd (cfpProd p.T p.T) p.T)
          (cfpProd (cfpProd p.T p.T) p.T) ⟶
          cfpProd (cfpProd p.T p.T) p.T) := by
  apply p.elim_uniq
  · exact natTriPlus1_base
  · set Ψ := cfpLift natTriHelper
      (natTriHelper ≫
        (natPlus : cfpProd p.T p.T ⟶ p.T))
    have lhs_form :
        cfpMap (𝟙 cfpTerminal) p.β ≫ Ψ =
        cfpLift
          (cfpAssocSnd cfpTerminal p.T p.T ≫
            natTriHelper ≫ natTriStepSingle)
          (cfpLift
            (cfpAssocSnd cfpTerminal p.T p.T ≫
              natTriHelper ≫ cfpFst p.T p.T)
            (cfpAssocSnd cfpTerminal p.T p.T ≫
              natTriHelper ≫ natPlus) ≫
            natPlus ≫ natSucc ≫ natSucc) := by
      simp only [Ψ]
      apply cfpLift_uniq
      · rw [Category.assoc, cfpLift_fst,
          natTriHelper_β_factor]
      · rw [Category.assoc, cfpLift_snd,
          ← Category.assoc,
          natTriHelper_β_factor,
          Category.assoc, Category.assoc,
          natTriStepSingle_natPlus,
          ← Category.assoc, ← Category.assoc,
          cfpLift_precomp]
        simp only [Category.assoc]
    have rhs_form :
        cfpLiftAssoc Ψ Ψ ≫
          natTriPlusCombinedStep =
        cfpLift
          (cfpAssocSnd cfpTerminal p.T p.T ≫
            natTriHelper ≫ natTriStepSingle)
          (cfpLift
            (cfpAssocSnd cfpTerminal p.T p.T ≫
              natTriHelper ≫ cfpFst p.T p.T)
            (cfpAssocSnd cfpTerminal p.T p.T ≫
              natTriHelper ≫ natPlus) ≫
            natPlus ≫ natSucc ≫ natSucc) := by
      simp only [Ψ]
      unfold natTriPlusCombinedStep
        natTriPlusStepSingle
      apply cfpLift_uniq
      · -- fst component.
        simp only [cfpLift_fst,
          cfpLift_precomp, cfpLiftAssoc]
        rw [← Category.assoc, ← Category.assoc,
          cfpLift_snd,
          ← Category.assoc, cfpLift_fst,
          Category.assoc]
      · -- snd component.
        simp only [cfpLift_snd,
          cfpLift_precomp, cfpLiftAssoc]
        rw [← Category.assoc, ← Category.assoc,
          ← Category.assoc, ← Category.assoc,
          cfpLift_snd]
        simp only [cfpLift_precomp,
          cfpLift_snd, Category.assoc]
        rw [← cfpLift_precomp
          (cfpAssocSnd cfpTerminal p.T p.T)]
        simp only [Category.assoc]
        congr 1; congr 1; congr 1
        rw [← Category.assoc, cfpLift_fst]
    rw [lhs_form, rhs_form]

/-- Base case for the second combined morphism
`cfpLift natTriHelper
  (cfpLift (natTriHelper ≫ cfpSnd) cfpSnd ≫
    natPlus)`. -/
private theorem natTriPlus2_base :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      cfpLift natTriHelper
        (cfpLift (natTriHelper ≫ cfpSnd p.T p.T)
          (cfpSnd cfpTerminal p.T) ≫ natPlus) =
    cfpLift (cfpLift p.ℓ p.ℓ) p.ℓ := by
  rw [cfpLift_precomp, natTriHelper_ℓ]
  congr 1
  rw [← Category.assoc, cfpLift_precomp]
  have hfst :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        natTriHelper ≫ cfpSnd p.T p.T =
      p.ℓ := by
    rw [← Category.assoc, natTriHelper_ℓ,
      cfpLift_snd]
  have hsnd :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        cfpSnd cfpTerminal p.T = p.ℓ := by
    unfold cfpInsertSnd
    rw [cfpLift_snd]
    rw [show cfpTerminalFrom cfpTerminal =
      𝟙 cfpTerminal from
      (h.terminal.uniq (𝟙 cfpTerminal)).symm,
      Category.id_comp]
  rw [hfst, hsnd, natPlus_ℓℓ]

/-- The step morphism `natTriStep` composed with
`cfpFst` extracts the right child's first component
and applies `natSucc`. -/
private theorem natTriStep_cfpFst :
    natTriStep ≫ cfpFst p.T p.T =
    cfpSnd (cfpProd p.T p.T)
      (cfpProd p.T p.T) ≫
      cfpFst p.T p.T ≫ natSucc := by
  unfold natTriStep
  rw [cfpLift_fst]

/-- The commutativity condition for projecting the
first component of `natTriHelper` via
`elim_algebra_morphism`. -/
private theorem natTriStep_cfpFst_comm :
    cfpMap (cfpFst p.T p.T)
        (cfpFst p.T p.T) ≫
      (cfpSnd p.T p.T ≫ natSucc) =
    natTriStep ≫ cfpFst p.T p.T := by
  rw [natTriStep_cfpFst,
    ← Category.assoc, cfpMap_snd,
    Category.assoc]

/-- The first projection of `natTriHelper` is the
parameterized identity catamorphism:
`natTriHelper ≫ cfpFst =
  p.elim p.ℓ (cfpSnd ≫ natSucc)`. -/
private theorem natTriHelper_cfpFst :
    natTriHelper ≫ cfpFst p.T p.T =
    p.elim p.ℓ
      (cfpSnd p.T p.T ≫ natSucc) := by
  unfold natTriHelper
  rw [elim_algebra_morphism
    (cfpLift p.ℓ p.ℓ)
    natTriStep
    (cfpFst p.T p.T)
    (cfpSnd p.T p.T ≫ natSucc)
    natTriStep_cfpFst_comm,
    cfpLift_fst]

/-- The second projection of `natTriStepSingle`
yields `natPlus(natSucc(fst), snd)`:
`natTriStepSingle ≫ cfpSnd =
  cfpLift (cfpFst ≫ natSucc) cfpSnd ≫ natPlus`.
-/
private theorem natTriStepSingle_cfpSnd :
    natTriStepSingle ≫ cfpSnd p.T p.T =
    cfpLift
      (cfpFst p.T p.T ≫ natSucc)
      (cfpSnd p.T p.T) ≫
      natPlus := by
  unfold natTriStepSingle
  rw [cfpLift_snd]

/-- Evaluating `natTriHelper` at a successor
input:
`cfpLift (cfpTerminalFrom T) natSucc ≫
  natTriHelper =
  cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
  natTriHelper ≫ natTriStepSingle`. -/
private theorem natTriHelper_natSucc :
    cfpLift (cfpTerminalFrom p.T)
      (natSucc : p.T ⟶ p.T) ≫
      natTriHelper =
    cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
      natTriHelper ≫
      (natTriStepSingle :
        cfpProd p.T p.T ⟶
          cfpProd p.T p.T) := by
  -- Factor through cfpMap (𝟙) p.β then use
  -- natTriHelper_β_factor.
  have factor1 :
      cfpLift (cfpTerminalFrom p.T)
        (natSucc : p.T ⟶ p.T) =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal) natSucc := by
    symm
    apply cfpLift_uniq
    · rw [Category.assoc, cfpMap_fst,
        Category.comp_id, cfpLift_fst]
    · rw [Category.assoc, cfpMap_snd,
        ← Category.assoc, cfpLift_snd,
        Category.id_comp]
  set rhs2 :=
    cfpMap (𝟙 cfpTerminal)
      (cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T)) ≫
      cfpMap (𝟙 cfpTerminal) p.β
  have factor2_fst :
      cfpMap (𝟙 cfpTerminal)
        (natSucc : p.T ⟶ p.T) ≫
        cfpFst cfpTerminal p.T =
      rhs2 ≫ cfpFst cfpTerminal p.T := by
    simp only [rhs2]
    rw [cfpMap_fst, Category.comp_id,
      Category.assoc, cfpMap_fst,
      Category.comp_id, cfpMap_fst,
      Category.comp_id]
  have factor2_snd :
      cfpMap (𝟙 cfpTerminal)
        (natSucc : p.T ⟶ p.T) ≫
        cfpSnd cfpTerminal p.T =
      rhs2 ≫ cfpSnd cfpTerminal p.T := by
    simp only [rhs2]
    rw [cfpMap_snd,
      Category.assoc, cfpMap_snd,
      ← Category.assoc, cfpMap_snd]
    unfold natSucc
    simp only [Category.assoc]
  have factor2 :
      cfpMap (𝟙 cfpTerminal)
        (natSucc : p.T ⟶ p.T) = rhs2 :=
    (cfpLift_uniq _ _ _
      factor2_fst factor2_snd).trans
      (cfpLift_uniq _ _ _
        (by rfl) (by rfl)).symm
  have factor3 :
      cfpMap (𝟙 cfpTerminal)
        (cfpLift
          (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpAssocSnd cfpTerminal p.T p.T =
      𝟙 (cfpProd cfpTerminal p.T) := by
    set m3 :=
      cfpMap (𝟙 cfpTerminal)
        (cfpLift
          (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
        cfpAssocSnd cfpTerminal p.T p.T
    have hfst :
        m3 ≫ cfpFst cfpTerminal p.T =
        cfpFst cfpTerminal p.T := by
      simp only [m3]
      unfold cfpAssocSnd
      simp only [Category.assoc]
      rw [cfpLift_fst, cfpMap_fst,
        Category.comp_id]
    have hsnd :
        m3 ≫ cfpSnd cfpTerminal p.T =
        cfpSnd cfpTerminal p.T := by
      simp only [m3]
      unfold cfpAssocSnd
      simp only [Category.assoc]
      rw [cfpLift_snd, ← Category.assoc,
        cfpMap_snd, Category.assoc,
        cfpLift_snd, Category.comp_id]
    exact (cfpLift_uniq _ _ _ hfst hsnd).trans
      (cfpLift_uniq _ _ (𝟙 _)
        (Category.id_comp _)
        (Category.id_comp _)).symm
  rw [factor1, Category.assoc, factor2]
  simp only [rhs2, Category.assoc]
  rw [natTriHelper_β_factor]
  -- Goal: ... ≫ cfpMap ≫ cfpAssocSnd ≫
  --   natTriHelper ≫ natTriStepSingle = ...
  congr 1
  rw [← Category.assoc, ← Category.assoc,
    factor3, Category.id_comp]

/-- Triangular number recurrence:
`tri(succ(n)) =
  natPlus(natSucc(natTriHelper_fst(n)), tri(n))`.
Expressed via the full `natTriHelper` state:
`natSucc ≫ natTri =
  cfpLift
    (cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
      natTriHelper ≫ cfpFst ≫ natSucc)
    natTri ≫ natPlus`. -/
theorem natTri_natSucc :
    natSucc ≫ natTri =
    cfpLift
      (cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        natTriHelper ≫
        cfpFst p.T p.T ≫ natSucc)
      (natTri : p.T ⟶ p.T) ≫
      natPlus := by
  have step1 :
      natSucc ≫
        cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) =
      cfpLift (cfpTerminalFrom p.T)
        natSucc := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    exact h.terminal.uniq _
  unfold natTri
  rw [← Category.assoc, ← Category.assoc,
    step1, natTriHelper_natSucc]
  simp only [Category.assoc]
  rw [natTriStepSingle_cfpSnd]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [cfpLift_precomp, cfpLift_precomp]

/-- Normalization to right-spine form: replaces all
left children with leaf, keeping only the right
spine.
`toRSpineNat(leaf) = leaf`,
`toRSpineNat(branch(l, r)) =
  branch(leaf, toRSpineNat(r))`. -/
def toRSpineNat : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    p.elim p.ℓ
      (cfpLift (cfpTerminalFrom (cfpProd p.T p.T) ≫
          p.ℓ)
        (cfpSnd p.T p.T) ≫ p.β)

/-- Leaf computation rule for `toRSpineNat`:
`toRSpineNat(leaf) = leaf`. -/
theorem toRSpineNat_ℓ :
    p.ℓ ≫ toRSpineNat =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold toRSpineNat
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have h1 : p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h1]
  have h2 :
      cfpLift (cfpTerminalFrom cfpTerminal) p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact cfpTerminalFrom_terminal
    · rw [cfpTerminalFrom_terminal,
        Category.id_comp]
  rw [h2, p.elim_ℓ]

/-- `p.β ≫ cfpLift (cfpTerminalFrom T) (𝟙 T)`
factors through `cfpMap (𝟙 cfpTerminal) p.β`. -/
private theorem β_embed_factor :
    p.β ≫
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) =
    cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        (𝟙 (cfpProd p.T p.T)) ≫
      cfpMap (𝟙 cfpTerminal) p.β := by
  rw [cfpLift_precomp, Category.comp_id]
  unfold cfpMap
  rw [cfpLift_precomp]
  congr 1
  · rw [← Category.assoc, cfpLift_fst,
      Category.comp_id]
    exact h.terminal.uniq _
  · rw [← Category.assoc, cfpLift_snd,
      Category.id_comp]

/-- Branch computation rule for `toRSpineNat`:
`toRSpineNat(branch(l, r)) =
  branch(leaf, toRSpineNat(r))`. -/
theorem toRSpineNat_β :
    p.β ≫ toRSpineNat =
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ)
      (cfpSnd p.T p.T ≫ toRSpineNat) ≫
      p.β := by
  unfold toRSpineNat
  rw [← Category.assoc, β_embed_factor]
  simp only [Category.assoc]
  rw [p.elim_β]
  -- Both sides end with ≫ β; suffices to show the
  -- pairs agree.
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply cfpLift_uniq
  · -- First component: ≫ cfpFst = cfpTerminalFrom ≫ ℓ.
    rw [Category.assoc, cfpLift_fst,
      ← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  · -- Second component.
    rw [Category.assoc, cfpLift_snd,
      Category.assoc]
    unfold cfpLiftAssoc
    rw [cfpLift_snd]
    unfold cfpAssocSnd
    -- Goal: L ≫ cfpLift (cfpFst) (cfpSnd ≫ cfpSnd)
    --   ≫ E = cfpSnd ≫ embed ≫ E.
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    -- Prove both sides equal
    -- cfpLift (cfpTerminalFrom _) (cfpSnd T T).
    have lhs_eq :
        cfpLift
            (cfpTerminalFrom (cfpProd p.T p.T))
            (𝟙 (cfpProd p.T p.T)) ≫
          cfpLift
            (cfpFst cfpTerminal
              (cfpProd p.T p.T))
            (cfpSnd cfpTerminal
                (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) =
        cfpLift
          (cfpTerminalFrom (cfpProd p.T p.T))
          (cfpSnd p.T p.T) := by
      rw [cfpLift_precomp]
      apply cfpLift_uniq
      · simp only [cfpLift_fst,
          ← Category.assoc, cfpLift_snd,
          Category.id_comp]
      · rw [← Category.assoc]
        simp only [cfpLift_snd]
        rw [Category.id_comp]
    have rhs_eq :
        cfpSnd p.T p.T ≫
          cfpLift (cfpTerminalFrom p.T)
            (𝟙 p.T) =
        cfpLift
          (cfpTerminalFrom (cfpProd p.T p.T))
          (cfpSnd p.T p.T) := by
      rw [cfpLift_precomp, Category.comp_id]
      congr 1
      exact h.terminal.uniq _
    rw [lhs_eq, rhs_eq]

/-- The step function for the `isRSpineNat`
paramorphism.  Given `(*, ((l, r), (res_l, res_r)))`,
returns `boolAnd(isLeafEndo(l), res_r)`. -/
private def isRSpineNatStep :
    cfpProd cfpTerminal
      (cfpProd (cfpProd p.T p.T)
        (cfpProd p.T p.T)) ⟶ p.T :=
  cfpLift
    (cfpSnd cfpTerminal _ ≫
      cfpFst (cfpProd p.T p.T) (cfpProd p.T p.T) ≫
      cfpFst p.T p.T ≫ isLeafEndo)
    (cfpSnd cfpTerminal _ ≫
      cfpSnd (cfpProd p.T p.T) (cfpProd p.T p.T) ≫
      cfpSnd p.T p.T) ≫
    boolAnd

/-- Boolean predicate: returns `p.ℓ` (leaf = true)
when the input is a right-spine natural number,
`treeFalse` otherwise.  Defined as a paramorphism
so the step can inspect the left subtree directly. -/
def isRSpineNat : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    paraElim p.ℓ isRSpineNatStep

/-- Leaf computation rule for `isRSpineNat`:
`isRSpineNat(leaf) = leaf`. -/
theorem isRSpineNat_ℓ :
    p.ℓ ≫ isRSpineNat =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold isRSpineNat
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have h1 : p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h1]
  have h2 :
      cfpLift (cfpTerminalFrom cfpTerminal) p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact cfpTerminalFrom_terminal
    · rw [cfpTerminalFrom_terminal,
        Category.id_comp]
  rw [h2, paraElim_ℓ]

def IsRSpineNatValued {D : C} (m : D ⟶ p.T) :
    Prop :=
  m ≫ isRSpineNat = cfpTerminalFrom D ≫ p.ℓ

def IsRSpineNatNorm {D : C} (m : D ⟶ p.T) :
    Prop :=
  m ≫ toRSpineNat = m

/-- Leaf is right-spine-nat-valued. -/
theorem ℓ_isRSpineNatValued :
    IsRSpineNatValued
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold IsRSpineNatValued
  rw [isRSpineNat_ℓ, cfpTerminalFrom_terminal,
    Category.id_comp]

/-- Leaf is right-spine-nat-normalized. -/
theorem ℓ_isRSpineNatNorm :
    IsRSpineNatNorm
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold IsRSpineNatNorm
  exact toRSpineNat_ℓ

/-- `natSucc` preserves right-spine normalization. -/
theorem natSucc_isRSpineNatNorm {D : C}
    (m : D ⟶ p.T) (hm : IsRSpineNatNorm m) :
    IsRSpineNatNorm (m ≫ natSucc) := by
  unfold IsRSpineNatNorm
  unfold natSucc
  rw [Category.assoc, Category.assoc,
    toRSpineNat_β]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  have inner :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) ≫
      cfpLift
        (cfpTerminalFrom
          (cfpProd p.T p.T) ≫ p.ℓ)
        (cfpSnd p.T p.T ≫ toRSpineNat) =
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        toRSpineNat := by
    rw [cfpLift_precomp]
    congr 1
    · rw [← Category.assoc]; congr 1
      exact h.terminal.uniq _
    · rw [← Category.assoc, cfpLift_snd,
        Category.id_comp]
  rw [inner, cfpLift_precomp, hm,
    cfpLift_precomp, Category.comp_id]

/-- The step morphism of `toRSpineNat`
equals the step morphism of `natPlus` composed
with `natSucc`. -/
private theorem toRSpineNat_step_eq_natSucc :
    cfpLift
      (cfpTerminalFrom
        (cfpProd p.T p.T) ≫ p.ℓ)
      (cfpSnd p.T p.T) ≫ p.β =
    cfpSnd p.T p.T ≫
      (natSucc : p.T ⟶ p.T) := by
  have expand :
      cfpSnd p.T p.T ≫ natSucc =
      cfpSnd p.T p.T ≫
        cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T) ≫ p.β := rfl
  rw [expand, ← Category.assoc,
    cfpLift_precomp]
  congr 2
  · rw [← Category.assoc]; congr 1
    exact (h.terminal.uniq
      (cfpSnd p.T p.T ≫
        cfpTerminalFrom p.T)).symm
  · exact (Category.comp_id _).symm

/-- `natSucc` commutes with `toRSpineNat`. -/
theorem natSucc_toRSpineNat_comm :
    natSucc ≫ toRSpineNat =
    toRSpineNat ≫
      (natSucc : p.T ⟶ p.T) := by
  unfold natSucc
  rw [Category.assoc, toRSpineNat_β,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [cfpLift_precomp]
  have hfst :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) ≫
        cfpTerminalFrom (cfpProd p.T p.T) ≫
        p.ℓ =
      cfpTerminalFrom p.T ≫ p.ℓ := by
    rw [← Category.assoc]; congr 1
    exact h.terminal.uniq _
  have hsnd :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) ≫
        cfpSnd p.T p.T ≫ toRSpineNat =
      toRSpineNat := by
    rw [← Category.assoc, cfpLift_snd,
      Category.id_comp]
  rw [hfst, hsnd]
  rw [cfpLift_precomp, Category.comp_id]
  congr 1
  rw [← Category.assoc]; congr 1
  exact (h.terminal.uniq
    (toRSpineNat ≫
      cfpTerminalFrom p.T)).symm


/-- Adding zero on the left under right-spine
encoding equals `toRSpineNat`. -/
theorem natPlus_ℓ_left_eq_toRSpineNat :
    cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
      (𝟙 p.T) ≫ natPlus =
    (toRSpineNat : p.T ⟶ p.T) := by
  have factor :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpMap p.ℓ (𝟙 p.T) := by
    rw [cfpLift_cfpMap, Category.comp_id]
  rw [factor, Category.assoc]
  unfold natPlus
  rw [elim_naturality p.ℓ (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natSucc),
    Category.comp_id]
  change cfpLift (cfpTerminalFrom p.T)
    (𝟙 p.T) ≫
    p.elim p.ℓ (cfpSnd p.T p.T ≫ natSucc) =
    toRSpineNat
  congr 1
  exact congrArg (p.elim p.ℓ)
    toRSpineNat_step_eq_natSucc.symm

/-- Adding zero on the left for right-spine
normalized inputs. -/
theorem natPlus_ℓ_left_rsn {D : C}
    (m : D ⟶ p.T)
    (hm : IsRSpineNatNorm m) :
    cfpLift
      (cfpTerminalFrom D ≫ p.ℓ) m ≫
      natPlus = m := by
  have factor :
      cfpLift (cfpTerminalFrom D ≫ p.ℓ) m =
      m ≫ cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T) := by
    rw [cfpLift_precomp, Category.comp_id]
    rw [← Category.assoc,
      show cfpTerminalFrom D =
        m ≫ cfpTerminalFrom p.T from
        (h.terminal.uniq
          (m ≫ cfpTerminalFrom p.T)).symm]
  rw [factor, Category.assoc,
    natPlus_ℓ_left_eq_toRSpineNat, hm]

/-- `toRSpineNat` is idempotent. -/
theorem toRSpineNat_idem :
    toRSpineNat ≫ toRSpineNat =
    (toRSpineNat : p.T ⟶ p.T) := by
  have embed_snd :
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T = 𝟙 p.T :=
    cfpLift_snd _ _
  -- Auxiliary: cfpSnd ≫ toRSN and
  -- cfpSnd ≫ toRSN ≫ toRSN both equal
  -- p.elim ℓ step.
  -- Shared step lemma: for any φ : T ⟶ T with
  -- ℓ ≫ φ = ℓ and β ≫ φ = cfpLift ... (cfpSnd ≫ φ) ≫ β,
  -- show cfpSnd ≫ φ = p.elim ℓ step.
  have snd_elim :
      ∀ (φ : p.T ⟶ p.T),
      p.ℓ ≫ φ = p.ℓ →
      (p.β ≫ φ =
        cfpLift
          (cfpTerminalFrom
            (cfpProd p.T p.T) ≫ p.ℓ)
          (cfpSnd p.T p.T ≫ φ) ≫ p.β) →
      cfpSnd cfpTerminal p.T ≫ φ =
        p.elim p.ℓ
          (cfpLift
            (cfpTerminalFrom
              (cfpProd p.T p.T) ≫ p.ℓ)
            (cfpSnd p.T p.T) ≫ p.β) := by
    intro φ hℓ hβ
    apply p.elim_uniq
    · unfold cfpInsertSnd
      rw [← Category.assoc, cfpLift_snd,
        Category.assoc,
        @cfpTerminalFrom_terminal C _ h,
        Category.id_comp, hℓ]
    · rw [← Category.assoc, cfpMap_snd,
        Category.assoc, hβ,
        ← Category.assoc, ← Category.assoc]
      congr 1
      -- Both sides : cfpProd 1 (T×T) ⟶ T×T.
      -- Show projections agree.
      -- LHS = cfpSnd ≫ cfpLift F (cfpSnd ≫ φ)
      --   = cfpLift (cfpSnd ≫ F) (cfpSnd ≫ cfpSnd ≫ φ)
      -- RHS = cfpLiftAssoc (cfpSnd ≫ φ)
      --   (cfpSnd ≫ φ) ≫ cfpLift F (cfpSnd)
      -- After expanding cfpLiftAssoc, both have fst =
      -- cfpTerminalFrom ≫ ℓ and snd = cfpSnd ≫ cfpSnd ≫ φ.
      -- Prove by showing projections agree.
      rw [cfpLift_precomp]
      symm
      apply cfpLift_uniq
      · rw [Category.assoc, cfpLift_fst,
          ← Category.assoc, ← Category.assoc]
        have hlhs : cfpLiftAssoc
            (cfpSnd cfpTerminal p.T ≫ φ)
            (cfpSnd cfpTerminal p.T ≫ φ) ≫
            cfpTerminalFrom
              (cfpProd p.T p.T) =
          cfpTerminalFrom _ :=
          h.terminal.uniq _
        have hrhs : cfpSnd cfpTerminal
            (cfpProd p.T p.T) ≫
            cfpTerminalFrom
              (cfpProd p.T p.T) =
          cfpTerminalFrom _ :=
          h.terminal.uniq _
        rw [hlhs, hrhs]
      · rw [Category.assoc, cfpLift_snd]
        unfold cfpLiftAssoc
        rw [← Category.assoc, cfpLift_snd]
        unfold cfpAssocSnd
        rw [← Category.assoc, cfpLift_snd,
          Category.assoc]
  have snd_toRSN :=
    snd_elim toRSpineNat toRSpineNat_ℓ
      toRSpineNat_β
  have snd_toRSN2 :=
    snd_elim (toRSpineNat ≫ toRSpineNat)
      (by rw [← Category.assoc,
          toRSpineNat_ℓ, toRSpineNat_ℓ])
      (by
        rw [← Category.assoc, toRSpineNat_β,
          Category.assoc, toRSpineNat_β,
          ← Category.assoc]
        congr 1
        rw [cfpLift_precomp]
        apply cfpLift_uniq
        · rw [cfpLift_fst, ← Category.assoc]
          congr 1
          exact h.terminal.uniq _
        · rw [cfpLift_snd,
            ← Category.assoc, cfpLift_snd,
            Category.assoc])
  calc toRSpineNat ≫ toRSpineNat
      = cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T ≫
        toRSpineNat ≫ toRSpineNat := by
        rw [← Category.assoc
          (cfpLift _ _) (cfpSnd _ _),
          embed_snd, Category.id_comp]
    _ = cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T ≫
        toRSpineNat := by
        congr 1
        exact snd_toRSN2.trans snd_toRSN.symm
    _ = toRSpineNat := by
        rw [← Category.assoc, embed_snd,
          Category.id_comp]

theorem natPlus_toRSpineNat_first :
    cfpMap (toRSpineNat : p.T ⟶ p.T) (𝟙 p.T) ≫
      natPlus =
    natPlus ≫ toRSpineNat := by
  have rhs :
      natPlus ≫ toRSpineNat =
      p.elim (toRSpineNat : p.T ⟶ p.T)
        (cfpSnd p.T p.T ≫ natSucc) := by
    have comm :
        cfpMap toRSpineNat toRSpineNat ≫
          (cfpSnd p.T p.T ≫ natSucc) =
        (cfpSnd p.T p.T ≫ natSucc) ≫
          toRSpineNat := by
      simp only [← Category.assoc]
      rw [cfpMap_snd]
      simp only [Category.assoc]
      rw [← natSucc_toRSpineNat_comm]
    change p.elim (𝟙 p.T)
        (cfpSnd p.T p.T ≫ natSucc) ≫
      toRSpineNat = _
    rw [elim_algebra_morphism
      (𝟙 p.T) (cfpSnd p.T p.T ≫ natSucc)
      toRSpineNat
      (cfpSnd p.T p.T ≫ natSucc)
      comm, Category.id_comp]
  have lhs :
      cfpMap toRSpineNat (𝟙 p.T) ≫ natPlus =
      p.elim (toRSpineNat : p.T ⟶ p.T)
        (cfpSnd p.T p.T ≫ natSucc) := by
    unfold natPlus
    rw [elim_naturality toRSpineNat (𝟙 p.T)
      (cfpSnd p.T p.T ≫ natSucc),
      Category.comp_id]
  rw [lhs, rhs]

private theorem natPlus_rsn_comm_aux
    {D : C} (a : D ⟶ p.T)
    (ha : IsRSpineNatNorm a) :
    cfpLift
      (cfpSnd D p.T ≫ toRSpineNat)
      (cfpFst D p.T ≫ a) ≫ natPlus =
    cfpMap a (𝟙 p.T) ≫
      (natPlus : cfpProd p.T p.T ⟶ p.T) := by
  have lhs_eq :
      cfpMap a (𝟙 p.T) ≫ natPlus =
      p.elim a
        (cfpSnd p.T p.T ≫ natSucc) := by
    unfold natPlus
    rw [elim_naturality a (𝟙 p.T)
      (cfpSnd p.T p.T ≫ natSucc),
      Category.comp_id]
  rw [lhs_eq, show
    p.elim a (cfpSnd p.T p.T ≫ natSucc) =
    cfpLift (cfpSnd D p.T ≫ toRSpineNat)
      (cfpFst D p.T ≫ a) ≫ natPlus from
    (p.elim_uniq a
      (cfpSnd p.T p.T ≫ natSucc)
      (cfpLift (cfpSnd D p.T ≫ toRSpineNat)
        (cfpFst D p.T ≫ a) ≫ natPlus)
      _ _).symm]
  · -- Base: cfpInsertSnd ℓ D ≫ Ψ = a.
    rw [← Category.assoc, cfpLift_precomp]
    have hsnd :
        cfpInsertSnd p.ℓ D ≫
          (cfpSnd D p.T ≫ toRSpineNat) =
        cfpTerminalFrom D ≫
          (p.ℓ ≫ toRSpineNat) := by
      rw [← Category.assoc]
      unfold cfpInsertSnd
      rw [cfpLift_snd]
      simp only [Category.assoc]
    have hfst :
        cfpInsertSnd p.ℓ D ≫
          (cfpFst D p.T ≫ a) = a := by
      rw [← Category.assoc]
      unfold cfpInsertSnd
      rw [cfpLift_fst, Category.id_comp]
    rw [hsnd, toRSpineNat_ℓ, hfst]
    exact natPlus_ℓ_left_rsn a ha
  · -- Step.
    set P := cfpProd p.T p.T
    set Ψ :=
      cfpLift (cfpSnd D p.T ≫ toRSpineNat)
        (cfpFst D p.T ≫ a) ≫ natPlus
    -- LHS: factor through cfpLift_precomp.
    have β_toRSN_eq :
        p.β ≫ toRSpineNat =
        cfpSnd p.T p.T ≫ toRSpineNat ≫
          (natSucc : p.T ⟶ p.T) := by
      rw [toRSpineNat_β]
      -- Goal: cfpLift (F ≫ ℓ)
      -- (cfpSnd ≫ toRSN) ≫ β
      -- = cfpSnd ≫ toRSN ≫ natSucc.
      -- Rewrite RHS: natSucc =
      -- cfpLift (cfpTerminalFrom ≫ ℓ) (𝟙) ≫ β.
      -- cfpSnd ≫ toRSN ≫ cfpLift F' (𝟙) ≫ β
      -- = (cfpSnd ≫ cfpLift F' toRSN) ≫ β
      -- = cfpLift (cfpSnd ≫ F') (cfpSnd ≫ toRSN)
      --   ≫ β.
      -- cfpSnd ≫ F' = cfpTerminalFrom ≫ ℓ
      -- (terminal uniqueness), and the second
      -- components match.
      -- LHS: cfpLift (F ≫ ℓ) (cfpSnd ≫ toRSN)
      --   ≫ β.
      -- RHS: cfpSnd ≫ toRSN ≫ natSucc
      -- = cfpSnd ≫ toRSN ≫
      --   cfpLift (F' ≫ ℓ) (𝟙) ≫ β.
      -- Factor cfpSnd ≫ toRSN through cfpLift.
      unfold natSucc
      simp only [← Category.assoc]
      congr 1
      rw [cfpLift_precomp, Category.comp_id]
      have htermℓ :
          cfpTerminalFrom
            (cfpProd p.T p.T) ≫ p.ℓ =
          (cfpSnd p.T p.T ≫ toRSpineNat) ≫
            cfpTerminalFrom p.T ≫ p.ℓ := by
        rw [← Category.assoc]; congr 1
        exact (h.terminal.uniq _).symm
      rw [htermℓ]
    have lhs_eq :
        cfpMap (𝟙 D) p.β ≫ Ψ =
        cfpLift
          (cfpSnd D P ≫ cfpSnd p.T p.T ≫
            toRSpineNat ≫ natSucc)
          (cfpFst D P ≫ a) ≫ natPlus := by
      simp only [Ψ]
      rw [← Category.assoc, cfpLift_precomp,
        show cfpMap (𝟙 D) p.β ≫
            cfpSnd D p.T ≫ toRSpineNat =
          cfpSnd D P ≫ cfpSnd p.T p.T ≫
            toRSpineNat ≫ natSucc from by
          rw [← Category.assoc, cfpMap_snd,
            Category.assoc, β_toRSN_eq],
        show cfpMap (𝟙 D) p.β ≫
            cfpFst D p.T ≫ a =
          cfpFst D P ≫ a from by
          rw [← Category.assoc, cfpMap_fst,
            Category.comp_id]]
    -- natPlus_succ_left.
    have lhs_succ :
        cfpLift
          (cfpSnd D P ≫ cfpSnd p.T p.T ≫
            toRSpineNat ≫ natSucc)
          (cfpFst D P ≫ a) ≫ natPlus =
        (cfpLift
          (cfpSnd D P ≫ cfpSnd p.T p.T ≫
            toRSpineNat)
          (cfpFst D P ≫ a) ≫ natPlus) ≫
          natSucc := by
      rw [← natPlus_succ_left
        (cfpSnd D P ≫ cfpSnd p.T p.T ≫
          toRSpineNat)
        (cfpFst D P ≫ a)]
      simp only [Category.assoc]
    -- RHS: reduce cfpLiftAssoc ≫ cfpSnd.
    have rhs_eq :
        cfpLiftAssoc Ψ Ψ ≫
          cfpSnd p.T p.T ≫ natSucc =
        (cfpAssocSnd D p.T p.T ≫ Ψ) ≫
          natSucc := by
      rw [← Category.assoc (cfpLiftAssoc _ _)]
      unfold cfpLiftAssoc
      rw [cfpLift_snd]
    -- cfpAssocSnd ≫ Ψ reduces to the same
    -- inner form.
    have assocSnd_Ψ :
        cfpAssocSnd D p.T p.T ≫ Ψ =
        cfpLift
          (cfpSnd D P ≫ cfpSnd p.T p.T ≫
            toRSpineNat)
          (cfpFst D P ≫ a) ≫ natPlus := by
      simp only [Ψ]
      rw [← Category.assoc, cfpLift_precomp]
      have h1 :
          cfpAssocSnd D p.T p.T ≫
            (cfpSnd D p.T ≫ toRSpineNat) =
          cfpSnd D P ≫ cfpSnd p.T p.T ≫
            toRSpineNat := by
        unfold cfpAssocSnd
        rw [← Category.assoc, cfpLift_snd,
          Category.assoc]
      have h2 :
          cfpAssocSnd D p.T p.T ≫
            (cfpFst D p.T ≫ a) =
          cfpFst D P ≫ a := by
        unfold cfpAssocSnd
        rw [← Category.assoc, cfpLift_fst]
      rw [h1, h2]
    rw [lhs_eq, lhs_succ, rhs_eq, assocSnd_Ψ]

theorem natPlus_comm_rsn {D : C}
    (a c : D ⟶ p.T)
    (ha : IsRSpineNatNorm a)
    (hc : IsRSpineNatNorm c) :
    cfpLift c a ≫ natPlus =
    cfpLift a c ≫ natPlus := by
  -- cfpLift c a ≫ natPlus
  -- = cfpLift (𝟙 D) c ≫
  --   cfpLift (cfpSnd ≫ toRSN) (cfpFst ≫ a)
  --   ≫ natPlus
  -- (for rsn c: toRSN(c) = c).
  -- By natPlus_rsn_comm_aux, the inner morphism
  -- equals cfpMap a (𝟙 T) ≫ natPlus.
  -- cfpLift (𝟙 D) c ≫ cfpMap a (𝟙 T) ≫ natPlus
  -- = cfpLift a c ≫ natPlus.
  have step1 :
      cfpLift c a ≫ natPlus =
      cfpLift (𝟙 D) c ≫
        cfpLift
          (cfpSnd D p.T ≫ toRSpineNat)
          (cfpFst D p.T ≫ a) ≫
        natPlus := by
    rw [← Category.assoc, cfpLift_precomp]
    have h1 :
        cfpLift (𝟙 D) c ≫
          (cfpSnd D p.T ≫ toRSpineNat) =
        c ≫ toRSpineNat := by
      rw [← Category.assoc, cfpLift_snd]
    have h2 :
        cfpLift (𝟙 D) c ≫
          (cfpFst D p.T ≫ a) =
        a := by
      rw [← Category.assoc, cfpLift_fst,
        Category.id_comp]
    rw [h1, hc, h2]
  have step2 :
      cfpLift (𝟙 D) c ≫
        cfpLift
          (cfpSnd D p.T ≫ toRSpineNat)
          (cfpFst D p.T ≫ a) ≫
        natPlus =
      cfpLift (𝟙 D) c ≫
        cfpMap a (𝟙 p.T) ≫ natPlus := by
    congr 1
    exact natPlus_rsn_comm_aux a ha
  have step3 :
      cfpLift (𝟙 D) c ≫
        cfpMap a (𝟙 p.T) ≫ natPlus =
      cfpLift a c ≫ natPlus := by
    rw [← Category.assoc,
      cfpLift_cfpMap, Category.id_comp,
      Category.comp_id]
  rw [step1, step2, step3]

theorem natPlus_cancel_left_rsn {D : C}
    (a b c : D ⟶ p.T)
    (ha : IsRSpineNatNorm a)
    (hb : IsRSpineNatNorm b)
    (hc : IsRSpineNatNorm c) :
    cfpLift (cfpLift c a ≫ natPlus)
        (cfpLift c b ≫ natPlus) ≫ natEq =
    cfpLift a b ≫ natEq := by
  rw [natPlus_comm_rsn a c ha hc,
    natPlus_comm_rsn b c hb hc,
    natPlus_cancel_right a b c]

/-- `natPlus` preserves right-spine normalization
in its first argument: if `a` is rsn, then
`cfpLift a b ≫ natPlus` is rsn (for any `b`). -/
theorem natPlus_isRSpineNatNorm {D : C}
    (a b : D ⟶ p.T)
    (ha : IsRSpineNatNorm a) :
    IsRSpineNatNorm
      (cfpLift a b ≫ natPlus) := by
  unfold IsRSpineNatNorm
  rw [Category.assoc,
    ← natPlus_toRSpineNat_first,
    ← Category.assoc,
    cfpLift_cfpMap, Category.comp_id, ha]

private theorem β_toRSpineNat_eq :
    p.β ≫ toRSpineNat =
    cfpSnd p.T p.T ≫ toRSpineNat ≫
      (natSucc : p.T ⟶ p.T) := by
  rw [toRSpineNat_β]
  unfold natSucc
  simp only [← Category.assoc]
  congr 1
  rw [cfpLift_precomp, Category.comp_id]
  congr 1
  rw [← Category.assoc]; congr 1
  exact (h.terminal.uniq _).symm

/-- `natPlus` is insensitive to normalization of
its second argument: the fold walks only the
right spine.
`cfpMap (𝟙 T) toRSpineNat ≫ natPlus = natPlus`.
-/
theorem natPlus_toRSpineNat_second :
    cfpMap (𝟙 p.T) toRSpineNat ≫ natPlus =
    (natPlus : cfpProd p.T p.T ⟶ p.T) := by
  change _ = p.elim (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natSucc)
  apply p.elim_uniq (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natSucc)
  · rw [← Category.assoc]
    have : cfpInsertSnd p.ℓ p.T ≫
        cfpMap (𝟙 p.T) toRSpineNat =
      cfpInsertSnd p.ℓ p.T := by
      unfold cfpInsertSnd
      rw [cfpLift_cfpMap, Category.id_comp,
        Category.assoc, toRSpineNat_ℓ]
    rw [this, natPlus_ℓ]
  · rw [← Category.assoc
      (cfpMap (𝟙 p.T) p.β),
      cfpMap_comp, Category.id_comp,
      β_toRSpineNat_eq]
    unfold cfpMap
    rw [show cfpSnd p.T
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T ≫
        toRSpineNat ≫ natSucc =
      (cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T ≫
        toRSpineNat) ≫ natSucc from
      by simp only [Category.assoc]]
    rw [natPlus_succ,
      ← Category.assoc (cfpLiftAssoc _ _)]
    congr 1
    have lhs_eq :
        cfpLift
          (cfpFst p.T
            (cfpProd p.T p.T))
          (cfpSnd p.T
            (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T ≫
            toRSpineNat) ≫ natPlus =
        cfpAssocSnd p.T p.T p.T ≫
          cfpMap (𝟙 p.T) toRSpineNat ≫
          natPlus := by
      symm
      unfold cfpAssocSnd
      rw [← Category.assoc,
        cfpLift_cfpMap,
        Category.comp_id]
      simp only [Category.assoc]
    have rhs_eq :
        cfpLiftAssoc
          (cfpMap (𝟙 p.T) toRSpineNat ≫
            natPlus)
          (cfpMap (𝟙 p.T) toRSpineNat ≫
            natPlus) ≫
          cfpSnd p.T p.T =
        cfpAssocSnd p.T p.T p.T ≫
          cfpMap (𝟙 p.T) toRSpineNat ≫
          natPlus := by
      unfold cfpLiftAssoc
      rw [cfpLift_snd]
    simp only [Category.comp_id]
    rw [lhs_eq]
    unfold cfpLiftAssoc cfpMap
    simp only [Category.comp_id]
    unfold cfpAssocSnd
    rw [cfpLift_snd]

/-- `natTriStepSingle` commutes with
`cfpMap toRSpineNat toRSpineNat`. -/
private theorem
    natTriStepSingle_toRSpineNat_comm :
    cfpMap (toRSpineNat : p.T ⟶ p.T)
        toRSpineNat ≫ natTriStepSingle =
    natTriStepSingle ≫
      cfpMap (toRSpineNat : p.T ⟶ p.T)
        toRSpineNat := by
  set S := natTriStepSingle (C := C) (p := p)
  set N := cfpMap (toRSpineNat : p.T ⟶ p.T)
    toRSpineNat
  -- cfpFst projection.
  have S_fst : S ≫ cfpFst p.T p.T =
      cfpFst p.T p.T ≫ natSucc := by
    simp only [S]; unfold natTriStepSingle
    exact cfpLift_fst _ _
  have S_snd : S ≫ cfpSnd p.T p.T =
      cfpLift (cfpFst p.T p.T ≫ natSucc)
        (cfpSnd p.T p.T) ≫ natPlus := by
    simp only [S]; unfold natTriStepSingle
    exact cfpLift_snd _ _
  have hfst :
      (N ≫ S) ≫ cfpFst p.T p.T =
      (S ≫ N) ≫ cfpFst p.T p.T := by
    -- LHS: N ≫ S ≫ cfpFst = N ≫ cfpFst ≫
    -- natSucc.
    rw [Category.assoc, S_fst]
    -- RHS: S ≫ N ≫ cfpFst.
    rw [Category.assoc]; simp only [N]
    rw [cfpMap_fst, ← Category.assoc (S),
      S_fst]
    rw [← Category.assoc
      (cfpMap toRSpineNat toRSpineNat),
      cfpMap_fst, Category.assoc,
      ← natSucc_toRSpineNat_comm]
    simp only [Category.assoc]
  -- cfpSnd projection.
  have hsnd :
      (N ≫ S) ≫ cfpSnd p.T p.T =
      (S ≫ N) ≫ cfpSnd p.T p.T := by
    -- LHS: N ≫ S ≫ cfpSnd = N ≫ (cfpLift ≫
    -- natPlus).
    rw [Category.assoc, S_snd]
    -- RHS: S ≫ N ≫ cfpSnd = S ≫ cfpSnd ≫
    -- toRSN = (cfpLift ≫ natPlus) ≫ toRSN.
    rw [Category.assoc]; simp only [N]
    rw [cfpMap_snd]
    rw [← Category.assoc (S), S_snd,
      Category.assoc]
    -- LHS: cfpMap toRSN toRSN ≫ cfpLift
    --   (cfpFst ≫ natSucc) cfpSnd ≫ natPlus.
    -- RHS: cfpLift (cfpFst ≫ natSucc) cfpSnd
    --   ≫ natPlus ≫ toRSN.
    -- RHS = cfpLift ≫ cfpMap toRSN (𝟙)
    --   ≫ natPlus.
    rw [← natPlus_toRSpineNat_first]
    -- LHS: cfpMap toRSN toRSN ≫ cfpLift ≫
    -- natPlus.
    -- RHS: cfpLift ≫ cfpMap toRSN (𝟙) ≫
    -- natPlus.
    -- Both sides suffice to show the cfpLift
    -- parts agree after absorbing toRSN on
    -- second component.
    -- Reduce both sides via natPlus_
    -- toRSpineNat_second on second arg.
    -- LHS: push cfpMap through cfpLift.
    rw [← Category.assoc
      (cfpMap toRSpineNat toRSpineNat),
      cfpLift_precomp]
    simp only [← Category.assoc]
    rw [cfpMap_fst, cfpMap_snd]
    simp only [Category.assoc]
    -- LHS: cfpLift (cfpFst ≫ toRSN ≫ natSucc)
    -- (cfpSnd ≫ toRSN) ≫ natPlus.
    -- RHS: factor cfpLift ≫ cfpMap.
    rw [← Category.assoc
      (cfpLift _ _) (cfpMap _ _),
      cfpLift_cfpMap, Category.comp_id]
    -- LHS first comp: cfpFst ≫ toRSN ≫ natSucc.
    -- RHS first comp: (cfpFst ≫ natSucc) ≫ toRSN.
    -- LHS second comp: cfpSnd ≫ toRSN.
    -- RHS second comp: cfpSnd.
    -- Rewrite RHS first comp.
    conv_rhs =>
      rw [Category.assoc,
        natSucc_toRSpineNat_comm]
    -- Absorb toRSN on LHS second comp.
    conv_lhs =>
      rw [show cfpLift
          (cfpFst p.T p.T ≫ toRSpineNat ≫
            natSucc)
          (cfpSnd p.T p.T ≫ toRSpineNat) =
        cfpLift
          (cfpFst p.T p.T ≫ toRSpineNat ≫
            natSucc)
          (cfpSnd p.T p.T) ≫
          cfpMap (𝟙 p.T) toRSpineNat from by
        rw [cfpLift_cfpMap, Category.comp_id]]
      rw [Category.assoc,
        natPlus_toRSpineNat_second]
  -- Combine projections.
  have lhs_eta : N ≫ S =
      cfpLift ((N ≫ S) ≫ cfpFst p.T p.T)
        ((N ≫ S) ≫ cfpSnd p.T p.T) :=
    cfpLift_uniq _ _ (N ≫ S) rfl rfl
  have rhs_eta : S ≫ N =
      cfpLift ((S ≫ N) ≫ cfpFst p.T p.T)
        ((S ≫ N) ≫ cfpSnd p.T p.T) :=
    cfpLift_uniq _ _ (S ≫ N) rfl rfl
  rw [lhs_eta, rhs_eta]
  exact congrArg₂ cfpLift hfst hsnd

/-- `natTriStep` commutes with
`cfpMap (cfpMap toRSpineNat toRSpineNat)
  (cfpMap toRSpineNat toRSpineNat)`. -/
private theorem natTriStep_toRSpineNat_comm :
    cfpMap
      (cfpMap (toRSpineNat : p.T ⟶ p.T)
        toRSpineNat)
      (cfpMap toRSpineNat toRSpineNat) ≫
      natTriStep =
    natTriStep ≫
      cfpMap (toRSpineNat : p.T ⟶ p.T)
        toRSpineNat := by
  rw [natTriStep_factor]
  simp only [← Category.assoc]
  rw [cfpMap_snd]
  simp only [Category.assoc]
  congr 1
  exact natTriStepSingle_toRSpineNat_comm

/-- Both components of `natTriHelper` are
right-spine normalized:
`natTriHelper ≫ cfpMap toRSpineNat toRSpineNat
  = natTriHelper`. -/
theorem natTriHelper_isRSpineNatNorm :
    natTriHelper ≫
      cfpMap (toRSpineNat : p.T ⟶ p.T)
        toRSpineNat =
    (natTriHelper :
      cfpProd cfpTerminal p.T ⟶
        cfpProd p.T p.T) := by
  change p.elim (cfpLift p.ℓ p.ℓ) natTriStep ≫
    cfpMap toRSpineNat toRSpineNat =
    p.elim (cfpLift p.ℓ p.ℓ) natTriStep
  rw [elim_algebra_morphism
    (cfpLift p.ℓ p.ℓ) natTriStep
    (cfpMap toRSpineNat toRSpineNat)
    natTriStep
    natTriStep_toRSpineNat_comm,
    cfpLift_cfpMap,
    toRSpineNat_ℓ]

/-- `natTri` is right-spine normalized:
`natTri ≫ toRSpineNat = natTri`. -/
theorem natTri_isRSpineNatNorm :
    IsRSpineNatNorm
      (natTri : p.T ⟶ p.T) := by
  unfold IsRSpineNatNorm
  unfold natTri
  rw [Category.assoc, Category.assoc,
    show cfpSnd p.T p.T ≫ toRSpineNat =
      cfpMap toRSpineNat toRSpineNat ≫
        cfpSnd p.T p.T from
      (cfpMap_snd toRSpineNat
        toRSpineNat).symm,
    ← Category.assoc
      (natTriHelper)
      (cfpMap _ _),
    natTriHelper_isRSpineNatNorm]

omit p in
/-- `cfpMap` with identity first component
distributes over composition in the second
component. -/
theorem cfpMap_id_comp'
    {A B B' B'' : C}
    (f : B ⟶ B') (g : B' ⟶ B'') :
    cfpMap (𝟙 A) (f ≫ g) =
    cfpMap (𝟙 A) f ≫
      cfpMap (𝟙 A) g := by
  conv_lhs =>
    rw [show (𝟙 A : A ⟶ A) =
      𝟙 A ≫ 𝟙 A from
      (Category.id_comp (𝟙 A)).symm]
  rw [← cfpMap_comp]

omit p in
/-- `cfpMap (𝟙 A) (cfpSnd B D)` equals
`cfpAssocSnd A B D`. -/
private theorem
    cfpMap_id_cfpSnd_eq_cfpAssocSnd
    {A B D : C} :
    cfpMap (𝟙 A) (cfpSnd B D) =
    cfpAssocSnd A B D := by
  unfold cfpMap cfpAssocSnd
  congr 1
  exact Category.comp_id _

omit p in
/-- `cfpMap (𝟙 A) (cfpLift f (𝟙 D)) ≫
cfpAssocSnd A B D = 𝟙`. -/
private theorem
    cfpMap_id_cfpLift_cfpAssocSnd
    {A B D : C} (f : D ⟶ B) :
    cfpMap (𝟙 A) (cfpLift f (𝟙 D)) ≫
      cfpAssocSnd A B D =
    𝟙 (cfpProd A D) := by
  have hfst :
      (cfpMap (𝟙 A)
        (cfpLift f (𝟙 D)) ≫
        cfpAssocSnd A B D) ≫
        cfpFst A D =
      cfpFst A D := by
    unfold cfpAssocSnd
    rw [Category.assoc, cfpLift_fst,
      cfpMap_fst, Category.comp_id]
  have hsnd :
      (cfpMap (𝟙 A)
        (cfpLift f (𝟙 D)) ≫
        cfpAssocSnd A B D) ≫
        cfpSnd A D =
      cfpSnd A D := by
    unfold cfpAssocSnd
    rw [Category.assoc, cfpLift_snd,
      ← Category.assoc, cfpMap_snd,
      Category.assoc, cfpLift_snd,
      Category.comp_id]
  exact (cfpLift_uniq _ _
    (cfpMap (𝟙 A)
      (cfpLift f (𝟙 D)) ≫
      cfpAssocSnd A B D)
    hfst hsnd).trans
    (cfpLift_uniq _ _ _
      (Category.id_comp _)
      (Category.id_comp _)).symm

/-- Applying `natSucc` to the tree input of
`natTriHelper` equals post-composing with
`natTriStepSingle`. -/
private theorem natSucc_natTriHelper :
    cfpMap (𝟙 cfpTerminal) natSucc ≫
      natTriHelper =
    natTriHelper ≫
      (natTriStepSingle :
        cfpProd p.T p.T ⟶
          cfpProd p.T p.T) := by
  unfold natSucc
  rw [cfpMap_id_comp', Category.assoc,
    natTriHelper_β_factor]
  have comm :
      cfpMap (𝟙 cfpTerminal)
        (cfpLift
          (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T)) ≫
      cfpAssocSnd cfpTerminal p.T p.T =
    𝟙 (cfpProd cfpTerminal p.T) :=
    cfpMap_id_cfpLift_cfpAssocSnd _
  simp only [← Category.assoc]
  rw [comm, Category.id_comp]

/-- Normalizing the tree input of `natTriHelper`
does not change the result:
`cfpMap (𝟙 cfpTerminal) toRSpineNat ≫
  natTriHelper = natTriHelper`. -/
private theorem toRSpineNat_natTriHelper :
    cfpMap (𝟙 cfpTerminal) toRSpineNat ≫
      natTriHelper =
    (natTriHelper :
      cfpProd cfpTerminal p.T ⟶
        cfpProd p.T p.T) := by
  apply p.elim_uniq (cfpLift p.ℓ p.ℓ)
    natTriStep
    (cfpMap (𝟙 cfpTerminal) toRSpineNat ≫
      natTriHelper)
  · -- Base case.
    rw [← Category.assoc]
    have : cfpInsertSnd p.ℓ cfpTerminal ≫
        cfpMap (𝟙 cfpTerminal) toRSpineNat =
      cfpInsertSnd p.ℓ cfpTerminal := by
      unfold cfpInsertSnd
      rw [cfpLift_cfpMap, Category.comp_id,
        Category.assoc, toRSpineNat_ℓ]
    rw [this, natTriHelper_ℓ]
  · -- Step case.
    rw [← Category.assoc
      (cfpMap (𝟙 cfpTerminal) p.β),
      show cfpMap (𝟙 cfpTerminal) p.β ≫
        cfpMap (𝟙 cfpTerminal)
          toRSpineNat =
        cfpMap (𝟙 cfpTerminal)
          (p.β ≫ toRSpineNat) from
        (cfpMap_id_comp' p.β
          toRSpineNat).symm,
      β_toRSpineNat_eq,
      cfpMap_id_comp',
      cfpMap_id_cfpSnd_eq_cfpAssocSnd,
      cfpMap_id_comp',
      Category.assoc, Category.assoc,
      natSucc_natTriHelper,
      natTriStep_factor]
    simp only [← Category.assoc]
    congr 1
    unfold cfpLiftAssoc
    rw [cfpLift_snd]
    exact Category.assoc _ _ _

/-- Pre-normalizing `natTri`'s input does not
change its output. -/
theorem toRSpineNat_natTri :
    toRSpineNat ≫ natTri =
    (natTri : p.T ⟶ p.T) := by
  unfold natTri
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp, Category.comp_id]
  have hterm :
      toRSpineNat ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom p.T :=
    h.terminal.uniq _
  rw [hterm]
  have embed_factor :
      cfpLift (cfpTerminalFrom p.T)
        toRSpineNat =
      cfpLift (cfpTerminalFrom p.T)
        (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal)
          toRSpineNat := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [embed_factor]
  simp only [Category.assoc]
  rw [← Category.assoc
    (cfpMap (𝟙 cfpTerminal) toRSpineNat),
    toRSpineNat_natTriHelper]

/-- `cantorPair` commutes with `toRSpineNat`:
normalizing both inputs then pairing equals
pairing then normalizing. -/
private theorem natPlus_toRSpineNat_both :
    cfpMap toRSpineNat toRSpineNat ≫
      (natPlus : cfpProd p.T p.T ⟶ p.T) =
    natPlus ≫ toRSpineNat := by
  have split :
      cfpMap toRSpineNat toRSpineNat =
      cfpMap (𝟙 p.T) toRSpineNat ≫
        cfpMap toRSpineNat
          (𝟙 p.T) := by
    symm; rw [cfpMap_comp,
      Category.id_comp,
      Category.comp_id]
  rw [split, Category.assoc,
    natPlus_toRSpineNat_first,
    ← Category.assoc,
    natPlus_toRSpineNat_second]

/-- `cantorPair` commutes with `toRSpineNat`:
normalizing both inputs then pairing equals
pairing then normalizing. -/
theorem cantorPair_toRSpineNat_comm :
    cfpMap toRSpineNat toRSpineNat ≫
      cantorPair =
    cantorPair ≫
      (toRSpineNat : p.T ⟶ p.T) := by
  have lhs :
      cfpMap toRSpineNat toRSpineNat ≫
        cantorPair =
      (cantorPair :
        cfpProd p.T p.T ⟶ p.T) := by
    unfold cantorPair
    rw [← Category.assoc, cfpLift_precomp,
      show cfpMap toRSpineNat
          toRSpineNat ≫
        natPlus ≫ natTri =
        natPlus ≫ natTri from by
        rw [← Category.assoc,
          natPlus_toRSpineNat_both,
          Category.assoc,
          toRSpineNat_natTri],
      cfpMap_fst toRSpineNat
        toRSpineNat,
      show cfpLift (natPlus ≫ natTri)
          (cfpFst p.T p.T ≫
            toRSpineNat) =
        cfpLift (natPlus ≫ natTri)
          (cfpFst p.T p.T) ≫
          cfpMap (𝟙 p.T)
            toRSpineNat from by
        rw [cfpLift_cfpMap,
          Category.comp_id],
      Category.assoc,
      natPlus_toRSpineNat_second]
  have rhs :
      cantorPair ≫ toRSpineNat =
      (cantorPair :
        cfpProd p.T p.T ⟶ p.T) := by
    unfold cantorPair
    rw [Category.assoc,
      ← natPlus_toRSpineNat_first,
      ← Category.assoc,
      cfpLift_cfpMap,
      Category.comp_id,
      Category.assoc,
      show natTri ≫ toRSpineNat =
        natTri from
        natTri_isRSpineNatNorm]
  rw [lhs, rhs]

/-- `natTruncSub(β(l,r), β(l',r')) =
natTruncSub(r, r')`:  the left children are
irrelevant to `natTruncSub` because the fold
only walks right spines. -/
theorem natTruncSub_β_β :
    cfpMap p.β p.β ≫ natTruncSub =
    cfpMap (cfpSnd p.T p.T)
      (cfpSnd p.T p.T) ≫
      (natTruncSub :
        cfpProd p.T p.T ⟶ p.T) := by
  have factor :
      cfpMap p.β p.β =
      cfpMap p.β
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpMap (𝟙 p.T) p.β := by
    rw [cfpMap_comp, Category.comp_id,
      Category.id_comp]
  rw [factor, Category.assoc, natTruncSub_β]
  have liftAssoc_snd :
      cfpLiftAssoc natTruncSub natTruncSub ≫
        cfpSnd p.T p.T =
      cfpAssocSnd p.T p.T p.T ≫
        natTruncSub := by
    unfold cfpLiftAssoc
    exact cfpLift_snd _ _
  rw [← Category.assoc
    (cfpLiftAssoc natTruncSub natTruncSub),
    liftAssoc_snd, Category.assoc]
  have assocSnd_eq :
      cfpMap p.β
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpAssocSnd p.T p.T p.T =
      cfpMap p.β (cfpSnd p.T p.T) := by
    set LHS :=
      cfpMap p.β
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpAssocSnd p.T p.T p.T
    set RHS :=
      cfpMap p.β (cfpSnd p.T p.T)
    have fst_eq :
        LHS ≫ cfpFst p.T p.T =
        cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫ p.β := by
      simp only [LHS]
      unfold cfpAssocSnd
      rw [Category.assoc, cfpLift_fst,
        cfpMap_fst]
    have snd_eq :
        LHS ≫ cfpSnd p.T p.T =
        cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T := by
      simp only [LHS]
      unfold cfpAssocSnd
      rw [Category.assoc, cfpLift_snd,
        ← Category.assoc,
        cfpMap_snd, Category.comp_id]
    have fst_eq' :
        RHS ≫ cfpFst p.T p.T =
        cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫ p.β := by
      simp only [RHS]; exact cfpMap_fst _ _
    have snd_eq' :
        RHS ≫ cfpSnd p.T p.T =
        cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T := by
      simp only [RHS]; exact cfpMap_snd _ _
    exact (cfpLift_uniq _ _ LHS
      fst_eq snd_eq).trans
      (cfpLift_uniq _ _ RHS
        fst_eq' snd_eq').symm
  have cfpMap_β_snd :
      cfpMap p.β (cfpSnd p.T p.T) =
      cfpMap (𝟙 (cfpProd p.T p.T))
        (cfpSnd p.T p.T) ≫
        cfpMap p.β (𝟙 p.T) := by
    rw [cfpMap_comp,
      Category.id_comp,
      Category.comp_id]
  rw [← Category.assoc
    (cfpMap p.β
      (𝟙 (cfpProd p.T p.T))),
    assocSnd_eq, cfpMap_β_snd,
    Category.assoc,
    β_natTruncSub_natPred,
    ← Category.assoc, cfpMap_comp,
    Category.id_comp, Category.comp_id]

/-- `natEq(β(l,r), β(l',r')) = natEq(r, r')`:
the left children are irrelevant to `natEq`
because `natTruncSub` only walks right spines. -/
theorem natEq_β_β :
    cfpMap p.β p.β ≫ natEq =
    cfpMap (cfpSnd p.T p.T)
      (cfpSnd p.T p.T) ≫
      (natEq : cfpProd p.T p.T ⟶ p.T) := by
  unfold natEq
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp]
  have h_sub :
      cfpMap p.β p.β ≫ natTruncSub =
      cfpMap (cfpSnd p.T p.T)
        (cfpSnd p.T p.T) ≫
        natTruncSub :=
    natTruncSub_β_β
  have h_swap_sub :
      cfpMap p.β p.β ≫
        cfpSwap p.T p.T ≫ natTruncSub =
      cfpMap (cfpSnd p.T p.T)
        (cfpSnd p.T p.T) ≫
        cfpSwap p.T p.T ≫ natTruncSub := by
    have step1 :
        cfpMap p.β p.β ≫
          cfpSwap p.T p.T ≫ natTruncSub =
        cfpSwap (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpMap p.β p.β ≫ natTruncSub := by
      rw [← Category.assoc,
        ← cfpSwap_cfpMap_diag p.β,
        Category.assoc]
    rw [step1, natTruncSub_β_β,
      ← Category.assoc,
      cfpSwap_cfpMap_diag
        (cfpSnd p.T p.T),
      Category.assoc]
  rw [h_sub, h_swap_sub,
    ← cfpLift_precomp]
  simp only [Category.assoc]

/-- The step of the Cantor unpairing catamorphism.
Given a pair `(a, b) : cfpProd T T`, produces the
next pair in the Cantor enumeration order:
  - if `b = 0` (leaf): return `(0, succ(a))`
  - if `b > 0` (branch): return `(succ(a), pred(b))`
-/
def cantorNextPair :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift
    (iteBranches
      (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ)
      (cfpFst p.T p.T ≫ natSucc)
      (cfpSnd p.T p.T ≫ isLeafEndo))
    (iteBranches
      (cfpFst p.T p.T ≫ natSucc)
      (cfpSnd p.T p.T ≫ natPred)
      (cfpSnd p.T p.T ≫ isLeafEndo))

/-- The step morphism for the Cantor unpairing
catamorphism.  From the pair of recursive results
`(result_l, result_r)`, extracts the right child's
result and applies `cantorNextPair`. -/
def cantorUnpairStep :
    cfpProd (cfpProd p.T p.T)
      (cfpProd p.T p.T) ⟶
      cfpProd p.T p.T :=
  cfpSnd (cfpProd p.T p.T)
    (cfpProd p.T p.T) ≫ cantorNextPair

/-- Parameterized catamorphism computing the Cantor
unpairing.  At `n = 0`, the pair is `(0, 0)`.  At
each successor step, `cantorNextPair` advances the
pair. -/
def cantorUnpairHelper :
    cfpProd cfpTerminal p.T ⟶
      cfpProd p.T p.T :=
  p.elim (cfpLift p.ℓ p.ℓ) cantorUnpairStep

/-- First component of the Cantor unpairing. -/
def cantorUnpairFst : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    cantorUnpairHelper ≫ cfpFst p.T p.T

/-- Second component of the Cantor unpairing. -/
def cantorUnpairSnd : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    cantorUnpairHelper ≫ cfpSnd p.T p.T

/-- Base case for `cantorUnpairHelper`:
`cantorUnpairHelper(*, 0) = (0, 0)`. -/
theorem cantorUnpairHelper_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      cantorUnpairHelper =
    cfpLift p.ℓ p.ℓ := by
  unfold cantorUnpairHelper
  exact p.elim_ℓ (cfpLift p.ℓ p.ℓ) _

/-- Step case for `cantorUnpairHelper`:
`cantorUnpairHelper(*, β(l, r)) =
  cantorNextPair(cantorUnpairHelper(*, r))`. -/
theorem cantorUnpairHelper_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      cantorUnpairHelper =
    cfpLiftAssoc cantorUnpairHelper
      cantorUnpairHelper ≫
      cantorUnpairStep := by
  unfold cantorUnpairHelper
  exact p.elim_β (cfpLift p.ℓ p.ℓ) _

/-- Successor rule for the Cantor pairing:
`cantorPair(succ(a), b) =
  succ(cantorPair(a, succ(b)))`. -/
theorem cantorPair_succ_fst {D : C}
    (a b : D ⟶ p.T) :
    cfpLift (a ≫ natSucc) b ≫ cantorPair =
    (cfpLift a (b ≫ natSucc) ≫ cantorPair) ≫
      natSucc := by
  unfold cantorPair
  have sum_l :
      cfpLift (a ≫ natSucc) b ≫ natPlus =
      (cfpLift a b ≫ natPlus) ≫ natSucc :=
    natPlus_succ_left a b
  have sum_r :
      cfpLift a (b ≫ natSucc) ≫ natPlus =
      (cfpLift a b ≫ natPlus) ≫ natSucc :=
    natPlus_succ a b
  have lhs_step :
      cfpLift (a ≫ natSucc) b ≫
        cfpLift (natPlus ≫ natTri)
          (cfpFst p.T p.T) =
      cfpLift
        (cfpLift a b ≫ natPlus ≫
          natSucc ≫ natTri)
        (a ≫ natSucc) := by
    rw [cfpLift_precomp, cfpLift_fst]
    congr 1
    rw [← Category.assoc, sum_l]
    simp only [Category.assoc]
  have rhs_step :
      cfpLift a (b ≫ natSucc) ≫
        cfpLift (natPlus ≫ natTri)
          (cfpFst p.T p.T) =
      cfpLift
        (cfpLift a b ≫ natPlus ≫
          natSucc ≫ natTri)
        a := by
    rw [cfpLift_precomp, cfpLift_fst]
    congr 1
    rw [← Category.assoc, sum_r]
    simp only [Category.assoc]
  have lhs_eq :
      cfpLift (a ≫ natSucc) b ≫
        cfpLift (natPlus ≫ natTri)
          (cfpFst p.T p.T) ≫ natPlus =
      cfpLift
        (cfpLift a b ≫ natPlus ≫
          natSucc ≫ natTri)
        (a ≫ natSucc) ≫ natPlus := by
    rw [← Category.assoc, lhs_step]
  have rhs_eq :
      (cfpLift a (b ≫ natSucc) ≫
        cfpLift (natPlus ≫ natTri)
          (cfpFst p.T p.T) ≫ natPlus) ≫
        natSucc =
      (cfpLift
        (cfpLift a b ≫ natPlus ≫
          natSucc ≫ natTri)
        a ≫ natPlus) ≫ natSucc := by
    congr 1
    rw [← Category.assoc, rhs_step]
  rw [lhs_eq, rhs_eq]
  exact natPlus_succ _ a

/-- Cantor pairing at `(0, 0)`:
`cantorPair(ℓ, ℓ) = ℓ`. -/
theorem cantorPair_ℓℓ :
    cfpLift p.ℓ p.ℓ ≫ cantorPair =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold cantorPair
  rw [← Category.assoc, cfpLift_precomp,
    cfpLift_fst]
  have hsum :
      cfpLift p.ℓ p.ℓ ≫ natPlus =
      (p.ℓ : cfpTerminal (C := C) ⟶ p.T) :=
    natPlus_ℓℓ
  rw [← Category.assoc, hsum,
    natTri_ℓ, hsum]

/-- When `b = ℓ`:
`cantorNextPair(a, ℓ) = (ℓ, succ(a))`. -/
theorem cantorNextPair_ℓ :
    cfpInsertSnd p.ℓ p.T ≫ cantorNextPair =
    cfpLift
      (cfpTerminalFrom p.T ≫ p.ℓ)
      (natSucc : p.T ⟶ p.T) := by
  unfold cantorNextPair
  rw [cfpLift_precomp]
  have cond :
      cfpInsertSnd p.ℓ p.T ≫
        cfpSnd p.T p.T ≫ isLeafEndo =
      cfpTerminalFrom p.T ≫ p.ℓ := by
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc, isLeafEndo_ℓ]
  congr 1
  · rw [iteBranches_precomp, cond]
    rw [show cfpInsertSnd p.ℓ p.T ≫
        cfpTerminalFrom (cfpProd p.T p.T) ≫
          p.ℓ =
      cfpTerminalFrom p.T ≫ p.ℓ from by
        rw [← Category.assoc]; congr 1
        exact h.terminal.uniq _]
    exact iteBranches_ℓ _ _
  · rw [iteBranches_precomp, cond]
    rw [show cfpInsertSnd p.ℓ p.T ≫
        cfpFst p.T p.T ≫ natSucc =
      natSucc from by
        unfold cfpInsertSnd
        rw [← Category.assoc, cfpLift_fst,
          Category.id_comp]]
    exact iteBranches_ℓ _ _

/-- When `b = β(l, r)`:
`cantorNextPair(a, β(l,r)) = (succ(a), r)`. -/
theorem cantorNextPair_β :
    cfpMap (𝟙 p.T) p.β ≫ cantorNextPair =
    cfpLift
      (cfpFst p.T (cfpProd p.T p.T) ≫ natSucc)
      (cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T) := by
  unfold cantorNextPair
  rw [cfpLift_precomp]
  have cond :
      cfpMap (𝟙 p.T) p.β ≫
        cfpSnd p.T p.T ≫ isLeafEndo =
      cfpSnd p.T (cfpProd p.T p.T) ≫
        p.β ≫ isLeafEndo := by
    rw [← Category.assoc, cfpMap_snd,
      Category.assoc]
  have cond' :
      cfpSnd p.T (cfpProd p.T p.T) ≫
        p.β ≫ isLeafEndo =
      cfpSnd p.T (cfpProd p.T p.T) ≫
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse) := by
    rw [isLeafEndo_β]
  set D := cfpProd p.T (cfpProd p.T p.T)
  have fst_simp :
      cfpMap (𝟙 p.T) p.β ≫
        cfpFst p.T p.T ≫ natSucc =
      cfpFst p.T (cfpProd p.T p.T) ≫
        natSucc := by
    rw [← Category.assoc, cfpMap_fst,
      Category.assoc, Category.id_comp]
  have snd_pred :
      cfpMap (𝟙 p.T) p.β ≫
        cfpSnd p.T p.T ≫ natPred =
      cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T := by
    rw [← Category.assoc, cfpMap_snd,
      Category.assoc, β_natPred]
  have term_simp :
      cfpMap (𝟙 p.T) p.β ≫
        cfpTerminalFrom (cfpProd p.T p.T) ≫
          p.ℓ =
      cfpTerminalFrom D ≫ p.ℓ := by
    rw [← Category.assoc]; congr 1
    exact h.terminal.uniq _
  have cond_β :
      cfpSnd p.T (cfpProd p.T p.T) ≫
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse) =
      (cfpTerminalFrom D ≫
        cfpLift p.ℓ p.ℓ) ≫ p.β := by
    unfold treeFalse
    rw [← Category.assoc
      (cfpSnd p.T (cfpProd p.T p.T))
      (cfpTerminalFrom _)]
    rw [show cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom D from
        h.terminal.uniq _]
    simp only [Category.assoc]
  congr 1
  · rw [iteBranches_precomp, cond, cond',
      cond_β, term_simp, fst_simp]
    exact iteBranches_β _ _
      (cfpTerminalFrom D ≫ cfpLift p.ℓ p.ℓ)
  · rw [iteBranches_precomp, cond, cond',
      cond_β, fst_simp, snd_pred]
    exact iteBranches_β _ _
      (cfpTerminalFrom D ≫ cfpLift p.ℓ p.ℓ)

/-- `cantorPair(a, natSucc(b)) =
cantorPair(a, β(l, b))`: the left child of the
second argument is irrelevant to cantorPair,
so natSucc in the second argument agrees with
any β in the second argument. -/
private theorem cantorPair_natSucc_eq_β
    {D : C}
    (a l r : D ⟶ p.T) :
    cfpLift a (r ≫ natSucc) ≫ cantorPair =
    cfpLift a (cfpLift l r ≫ p.β) ≫
      cantorPair := by
  have sum_succ :
      cfpLift a (r ≫ natSucc) ≫ natPlus =
      (cfpLift a r ≫ natPlus) ≫ natSucc :=
    natPlus_succ a r
  have sum_β :
      cfpLift a (cfpLift l r ≫ p.β) ≫
        natPlus =
      (cfpLift a r ≫ natPlus) ≫ natSucc := by
    have factor :
        cfpLift a (cfpLift l r ≫ p.β) =
        cfpLift a (cfpLift l r) ≫
          cfpMap (𝟙 p.T) p.β := by
      rw [cfpLift_cfpMap, Category.comp_id]
    rw [factor, Category.assoc, natPlus_β]
    simp only [← Category.assoc]
    have step :
        cfpLift a (cfpLift l r) ≫
          cfpLiftAssoc natPlus natPlus ≫
          cfpSnd p.T p.T =
        cfpLift a r ≫ natPlus := by
      have h1 :
          cfpLiftAssoc natPlus natPlus ≫
            cfpSnd p.T p.T =
          cfpAssocSnd p.T p.T p.T ≫
            natPlus := by
        unfold cfpLiftAssoc
        exact cfpLift_snd _ _
      rw [h1]
      unfold cfpAssocSnd
      rw [← Category.assoc, cfpLift_precomp,
        cfpLift_fst,
        ← Category.assoc, cfpLift_snd,
        cfpLift_snd]
    congr 1
    rw [Category.assoc]; exact step
  have sum_eq :
      cfpLift a (r ≫ natSucc) ≫ natPlus =
      cfpLift a (cfpLift l r ≫ p.β) ≫
        natPlus := by
    rw [sum_succ, sum_β]
  unfold cantorPair
  rw [← Category.assoc
    (cfpLift a (r ≫ natSucc)),
    cfpLift_precomp,
    ← Category.assoc
      (cfpLift a (cfpLift l r ≫ p.β)),
    cfpLift_precomp,
    cfpLift_fst, cfpLift_fst]
  congr 1; congr 1
  rw [← Category.assoc, ← Category.assoc,
    sum_eq]

/-- β case of the key lemma:
`cantorNextPair ≫ cantorPair =
  cantorPair ≫ natSucc`
precomposed with `cfpMap (𝟙 T) p.β`. -/
private theorem
    cantorPair_cantorNextPair_β :
    cfpMap (𝟙 p.T) p.β ≫
      cantorNextPair ≫ cantorPair =
    cfpMap (𝟙 p.T) p.β ≫
      cantorPair ≫ natSucc := by
  rw [← Category.assoc
    (cfpMap (𝟙 p.T) p.β) cantorNextPair,
    cantorNextPair_β]
  -- LHS: cfpLift (cfpFst ≫ natSucc) (cfpSnd ≫
  --   cfpSnd) ≫ cantorPair
  -- RHS: cfpMap (𝟙 T) β ≫ cantorPair ≫ natSucc
  have snd_eta :
      cfpLift
        (cfpSnd p.T (cfpProd p.T p.T) ≫
          cfpFst p.T p.T)
        (cfpSnd p.T (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) =
      cfpSnd p.T (cfpProd p.T p.T) :=
    (cfpLift_uniq _ _ _ rfl rfl).symm
  have cfpMap_eq :
      cfpLift
        (cfpFst p.T (cfpProd p.T p.T))
        (cfpSnd p.T (cfpProd p.T p.T) ≫
          p.β) =
      cfpMap (𝟙 p.T) p.β := by
    unfold cfpMap; congr 1
    exact (Category.comp_id
      (cfpFst p.T (cfpProd p.T p.T))).symm
  rw [cantorPair_succ_fst
    (cfpFst p.T (cfpProd p.T p.T))
    (cfpSnd p.T (cfpProd p.T p.T) ≫
      cfpSnd p.T p.T),
    cantorPair_natSucc_eq_β
      (cfpFst p.T (cfpProd p.T p.T))
      (cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpFst p.T p.T)
      (cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T),
    snd_eta, cfpMap_eq]
  simp only [Category.assoc]

/-- The first component of `natTriHelper`,
applied at the terminal section, equals
`toRSpineNat`:
`cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
  natTriHelper ≫ cfpFst =
  toRSpineNat`. -/
private theorem embed_natTriHelper_cfpFst :
    cfpLift (cfpTerminalFrom p.T)
      (𝟙 p.T) ≫
      natTriHelper ≫ cfpFst p.T p.T =
    (toRSpineNat : p.T ⟶ p.T) := by
  rw [natTriHelper_cfpFst,
    congrArg (p.elim p.ℓ)
      toRSpineNat_step_eq_natSucc.symm]
  rfl

/-- ℓ case of the main lemma:
`cantorNextPair ≫ cantorPair =
  cantorPair ≫ natSucc`
precomposed with `cfpInsertSnd p.ℓ p.T`. -/
private theorem
    cantorPair_cantorNextPair_ℓ :
    cfpInsertSnd p.ℓ p.T ≫
      cantorNextPair ≫ cantorPair =
    cfpInsertSnd p.ℓ p.T ≫
      cantorPair ≫ natSucc := by
  -- Reduce LHS via cantorNextPair_ℓ.
  rw [← Category.assoc
    (cfpInsertSnd p.ℓ p.T) cantorNextPair,
    cantorNextPair_ℓ]
  -- LHS = cfpLift (cfpTerminalFrom T ≫ ℓ)
  --   natSucc ≫ cantorPair
  -- RHS = cfpInsertSnd ℓ T ≫ cantorPair
  --   ≫ natSucc
  -- Reduce both sides to natSucc ≫ natTri
  -- and succ(natPlus(natTri(a), a)).
  -- Step A: LHS = natSucc ≫ natTri.
  have sum_eq :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (natSucc : p.T ⟶ p.T) ≫ natPlus =
      natSucc ≫ toRSpineNat := by
    have precomp :
        cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (natSucc : p.T ⟶ p.T) ≫
          natPlus =
        (cfpLift
          (cfpTerminalFrom p.T ≫ p.ℓ)
          (𝟙 p.T) ≫ natPlus) ≫
          natSucc := by
      rw [← natPlus_succ
        (cfpTerminalFrom p.T ≫ p.ℓ)
        (𝟙 p.T)]
      congr 1; congr 1
      exact (Category.id_comp natSucc).symm
    rw [precomp,
      natPlus_ℓ_left_eq_toRSpineNat]
    exact natSucc_toRSpineNat_comm.symm
  have lhs_eq :
      cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
        (natSucc : p.T ⟶ p.T) ≫
        cantorPair =
      natSucc ≫ natTri := by
    unfold cantorPair
    have outer :
        cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
          (natSucc : p.T ⟶ p.T) ≫
          cfpLift (natPlus ≫ natTri)
            (cfpFst p.T p.T) =
        cfpLift (natSucc ≫ natTri)
          (cfpTerminalFrom p.T ≫ p.ℓ) := by
      rw [cfpLift_precomp, cfpLift_fst]
      congr 1
      rw [← Category.assoc, sum_eq,
        Category.assoc, toRSpineNat_natTri]
    rw [← Category.assoc, outer,
      natPlus_zero]
  -- Step B: RHS base =
  --   natPlus(natTri(a), a).
  have rhs_eq :
      cfpInsertSnd p.ℓ p.T ≫ cantorPair =
      cfpLift natTri (𝟙 p.T) ≫
        natPlus := by
    unfold cantorPair cfpInsertSnd
    have outer :
        cfpLift (𝟙 p.T)
          (cfpTerminalFrom p.T ≫ p.ℓ) ≫
          cfpLift (natPlus ≫ natTri)
            (cfpFst p.T p.T) =
        cfpLift natTri (𝟙 p.T) := by
      rw [cfpLift_precomp, cfpLift_fst,
        ← Category.assoc,
        natPlus_zero, Category.id_comp]
    rw [← Category.assoc, outer]
  rw [lhs_eq, ← Category.assoc, rhs_eq,
    Category.assoc]
  -- Goal: natSucc ≫ natTri =
  --   cfpLift natTri (𝟙 T) ≫ natPlus
  --   ≫ natSucc
  rw [natTri_natSucc]
  -- The first argument of cfpLift contains
  -- `... ≫ natTriHelper ≫ cfpFst ≫ natSucc`,
  -- which equals `toRSpineNat ≫ natSucc`.
  have reassoc :
      cfpLift (cfpTerminalFrom p.T)
        (𝟙 p.T) ≫
        natTriHelper ≫
        cfpFst p.T p.T ≫ natSucc =
      toRSpineNat ≫ natSucc := by
    have h :
        cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
          natTriHelper ≫ cfpFst p.T p.T =
        (toRSpineNat : p.T ⟶ p.T) :=
      embed_natTriHelper_cfpFst
    rw [show cfpLift (cfpTerminalFrom p.T)
        (𝟙 p.T) ≫ natTriHelper ≫
        cfpFst p.T p.T ≫ natSucc =
      (cfpLift (cfpTerminalFrom p.T)
        (𝟙 p.T) ≫ natTriHelper ≫
        cfpFst p.T p.T) ≫ natSucc from by
        simp only [Category.assoc],
      h]
  rw [reassoc,
    natPlus_succ_left toRSpineNat natTri]
  -- Goal:
  -- (cfpLift toRSpineNat natTri ≫ natPlus)
  --   ≫ natSucc =
  -- cfpLift natTri (𝟙 T) ≫ natPlus
  --   ≫ natSucc
  simp only [Category.assoc]
  -- Now both sides are right-associated.
  -- Peel off the common natSucc suffix.
  have inner :
      cfpLift toRSpineNat natTri ≫ natPlus =
      cfpLift natTri (𝟙 p.T) ≫
        natPlus := by
    rw [(natPlus_comm_rsn toRSpineNat natTri
      toRSpineNat_idem
      natTri_isRSpineNatNorm).symm]
    -- Goal: cfpLift natTri toRSpineNat ≫
    --   natPlus = cfpLift natTri (𝟙 T) ≫
    --   natPlus
    have factor :
        cfpLift natTri
          (toRSpineNat : p.T ⟶ p.T) =
        cfpLift natTri (𝟙 p.T) ≫
          cfpMap (𝟙 p.T) toRSpineNat := by
      rw [cfpLift_cfpMap, Category.id_comp,
        Category.comp_id]
    rw [factor, Category.assoc,
      natPlus_toRSpineNat_second]
  simp only [← Category.assoc]
  rw [inner]

/-- `cantorPair` absorbs `toRSpineNat` on its
second argument:
`cfpMap (𝟙 T) toRSpineNat ≫ cantorPair =
  cantorPair`. -/
private theorem cantorPair_toRSN_second :
    cfpMap (𝟙 p.T) toRSpineNat ≫
      cantorPair =
    (cantorPair :
      cfpProd p.T p.T ⟶ p.T) := by
  unfold cantorPair
  rw [← Category.assoc, cfpLift_precomp]
  have h_fst :
      cfpMap (𝟙 p.T) toRSpineNat ≫
        natPlus ≫ natTri =
      natPlus ≫ natTri := by
    rw [← Category.assoc,
      natPlus_toRSpineNat_second]
  have h_snd :
      cfpMap (𝟙 p.T) toRSpineNat ≫
        cfpFst p.T p.T =
      cfpFst p.T p.T := by
    rw [cfpMap_fst, Category.comp_id]
  rw [h_fst, h_snd]

/-- The paramorphism step for `cantorPair_cantorNextPair`:
given `(a, ((l,r), (res_l, res_r)))`, returns
`cantorPair(succ(a), r)`.  The sub-results are
ignored. -/
private def cantorPairParaStep :
    cfpProd p.T
      (cfpProd (cfpProd p.T p.T)
        (cfpProd p.T p.T)) ⟶ p.T :=
  cfpLift
    (cfpFst p.T
      (cfpProd (cfpProd p.T p.T)
        (cfpProd p.T p.T)) ≫
      natSucc)
    (cfpSnd p.T
      (cfpProd (cfpProd p.T p.T)
        (cfpProd p.T p.T)) ≫
      cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
      cfpSnd p.T p.T) ≫
  cantorPair

/-- The paramorphism pre-composition map composed
with `cantorPairParaStep` simplifies: the sub-results
are discarded. -/
private theorem cantorPairParaStep_precomp
    (φ : cfpProd p.T p.T ⟶ p.T) :
    cfpLift
      (cfpFst p.T (cfpProd p.T p.T))
      (cfpLift
        (cfpSnd p.T (cfpProd p.T p.T))
        (cfpLiftAssoc φ φ)) ≫
      cantorPairParaStep =
    cfpLift
      (cfpFst p.T (cfpProd p.T p.T) ≫
        natSucc)
      (cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T) ≫
    cantorPair := by
  unfold cantorPairParaStep
  rw [← Category.assoc, cfpLift_precomp]
  congr 1
  set P :=
    cfpLift
      (cfpFst p.T (cfpProd p.T p.T))
      (cfpLift
        (cfpSnd p.T (cfpProd p.T p.T))
        (cfpLiftAssoc φ φ))
  have h_fst :
      P ≫
        cfpFst p.T
          (cfpProd (cfpProd p.T p.T)
            (cfpProd p.T p.T)) ≫
        natSucc =
      cfpFst p.T (cfpProd p.T p.T) ≫
        natSucc := by
    rw [← Category.assoc, cfpLift_fst]
  have h_snd :
      P ≫
        cfpSnd p.T
          (cfpProd (cfpProd p.T p.T)
            (cfpProd p.T p.T)) ≫
        cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T =
      cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T := by
    rw [← Category.assoc P
      (cfpSnd _ _),
      cfpLift_snd,
      ← Category.assoc, cfpLift_fst]
  rw [h_fst, h_snd]

/-- Both `cantorNextPair ≫ cantorPair` and
`cantorPair ≫ natSucc` satisfy the same paramorphism
β-step equation: at `(a, β(l, r))`, both produce
`cantorPair(succ(a), r)`. -/
private theorem
    cantorPair_cantorNextPair_β_form :
    cfpMap (𝟙 p.T) p.β ≫
      cantorNextPair ≫ cantorPair =
    cfpLift
      (cfpFst p.T (cfpProd p.T p.T) ≫
        natSucc)
      (cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T) ≫
    cantorPair := by
  rw [← Category.assoc
    (cfpMap (𝟙 p.T) p.β) cantorNextPair,
    cantorNextPair_β]

/-- `cantorNextPair ≫ cantorPair =
cantorPair ≫ natSucc`. -/
theorem cantorPair_cantorNextPair :
    cantorNextPair ≫ cantorPair =
    cantorPair ≫
      (natSucc : p.T ⟶ p.T) := by
  set base :=
    cfpInsertSnd p.ℓ p.T ≫
      cantorPair ≫ natSucc
  set g :=
    (cantorPairParaStep :
      cfpProd p.T
        (cfpProd (cfpProd p.T p.T)
          (cfpProd p.T p.T)) ⟶ p.T)
  have lhs_eq :
      cantorNextPair ≫ cantorPair =
      paraElim base g := by
    apply paraElim_uniq (C := C)
    · exact cantorPair_cantorNextPair_ℓ
    · rw [cantorPairParaStep_precomp,
        cantorPair_cantorNextPair_β_form]
  have rhs_eq :
      cantorPair ≫ natSucc =
      paraElim base g := by
    apply paraElim_uniq
    · rfl
    · rw [cantorPairParaStep_precomp]
      exact
        cantorPair_cantorNextPair_β.symm.trans
          cantorPair_cantorNextPair_β_form
  rw [lhs_eq, rhs_eq]

/-- The right-inverse for Cantor pairing:
`cantorUnpairHelper ≫ cantorPair` equals the
terminal-parameterized fold that counts
right-spine depth (a form of `toRSpineNat`). -/
theorem cantorUnpairHelper_cantorPair :
    cantorUnpairHelper ≫ cantorPair =
    p.elim p.ℓ
      (cfpSnd p.T p.T ≫ natSucc) := by
  have hw :
      cfpMap cantorPair cantorPair ≫
        cfpSnd p.T p.T ≫ natSucc =
      cantorUnpairStep ≫ cantorPair := by
    unfold cantorUnpairStep
    rw [← Category.assoc
      (cfpMap cantorPair cantorPair),
      cfpMap_snd]
    simp only [Category.assoc]
    congr 1
    exact cantorPair_cantorNextPair.symm
  rw [show cantorUnpairHelper =
      p.elim (cfpLift p.ℓ p.ℓ)
        cantorUnpairStep from rfl,
    elim_algebra_morphism
      (cfpLift p.ℓ p.ℓ) cantorUnpairStep
      cantorPair
      (cfpSnd p.T p.T ≫ natSucc)
      hw,
    cantorPair_ℓℓ]

/-- `toRSpineNat ≫ isLeafEndo = isLeafEndo`:
right-spine normalization preserves
leaf/branch classification. -/
theorem toRSpineNat_isLeafEndo :
    toRSpineNat ≫ isLeafEndo =
    (isLeafEndo : p.T ⟶ p.T) := by
  set F :=
    cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse
  set base :=
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T)
  have lhs_embed :
      cfpSnd cfpTerminal p.T ≫
        toRSpineNat ≫ isLeafEndo =
      p.elim base F := by
    set φ := cfpSnd cfpTerminal p.T ≫
      toRSpineNat ≫ isLeafEndo
    apply p.elim_uniq base F φ
    · change cfpInsertSnd p.ℓ cfpTerminal ≫
        (cfpSnd cfpTerminal p.T ≫
          toRSpineNat ≫ isLeafEndo) = p.ℓ
      unfold cfpInsertSnd
      simp only [← Category.assoc]
      rw [cfpLift_snd, Category.assoc,
        Category.assoc,
        ← Category.assoc p.ℓ toRSpineNat,
        toRSpineNat_ℓ, isLeafEndo_ℓ,
        cfpTerminalFrom_terminal,
        Category.id_comp]
    · simp only [φ]
      have β_toRSN_isLeaf :
          p.β ≫ toRSpineNat ≫ isLeafEndo =
          cfpTerminalFrom
            (cfpProd p.T p.T) ≫
            treeFalse := by
        rw [← Category.assoc, toRSpineNat_β,
          Category.assoc, isLeafEndo_β,
          ← Category.assoc]; congr 1
        exact h.terminal.uniq _
      have lhs_eq :
          cfpMap (𝟙 cfpTerminal) p.β ≫
            (cfpSnd cfpTerminal p.T ≫
              toRSpineNat ≫ isLeafEndo) =
          cfpTerminalFrom _ ≫ treeFalse := by
        have h1 :
            cfpMap (𝟙 cfpTerminal) p.β ≫
              cfpSnd cfpTerminal p.T =
            cfpSnd cfpTerminal
              (cfpProd p.T p.T) ≫ p.β :=
          cfpMap_snd _ _
        rw [← Category.assoc, ← Category.assoc,
          h1, Category.assoc,
          Category.assoc,
          β_toRSN_isLeaf, ← Category.assoc]
        congr 1; exact h.terminal.uniq _
      have rhs_eq :
          cfpLiftAssoc
            (cfpSnd cfpTerminal p.T ≫
              toRSpineNat ≫ isLeafEndo)
            (cfpSnd cfpTerminal p.T ≫
              toRSpineNat ≫ isLeafEndo) ≫
            F =
          cfpTerminalFrom _ ≫ treeFalse := by
        rw [← Category.assoc]; congr 1
        exact h.terminal.uniq _
      rw [lhs_eq, rhs_eq]
  have rhs_embed :
      cfpSnd cfpTerminal p.T ≫ isLeafEndo =
      p.elim base F := by
    set ψ := cfpSnd cfpTerminal p.T ≫
      isLeafEndo
    apply p.elim_uniq base F ψ
    · simp only [ψ, base]
      rw [show cfpInsertSnd p.ℓ cfpTerminal ≫
          (cfpSnd cfpTerminal p.T ≫
            isLeafEndo) =
        p.ℓ ≫ isLeafEndo from by
          rw [← Category.assoc]; congr 1
          unfold cfpInsertSnd
          rw [cfpLift_snd,
            cfpTerminalFrom_terminal,
            Category.id_comp],
        isLeafEndo_ℓ]
    · simp only [ψ]
      have lhs_eq :
          cfpMap (𝟙 cfpTerminal) p.β ≫
            (cfpSnd cfpTerminal p.T ≫
              isLeafEndo) =
          cfpTerminalFrom _ ≫ treeFalse := by
        have h1 :
            cfpMap (𝟙 cfpTerminal) p.β ≫
              cfpSnd cfpTerminal p.T =
            cfpSnd cfpTerminal
              (cfpProd p.T p.T) ≫ p.β :=
          cfpMap_snd _ _
        rw [← Category.assoc, h1,
          Category.assoc, isLeafEndo_β,
          ← Category.assoc]
        congr 1; exact h.terminal.uniq _
      have rhs_eq :
          cfpLiftAssoc
            (cfpSnd cfpTerminal p.T ≫
              isLeafEndo)
            (cfpSnd cfpTerminal p.T ≫
              isLeafEndo) ≫
            F =
          cfpTerminalFrom _ ≫ treeFalse := by
        rw [← Category.assoc]; congr 1
        exact h.terminal.uniq _
      rw [lhs_eq, rhs_eq]
  have h_embed :
      cfpSnd cfpTerminal p.T ≫
        toRSpineNat ≫ isLeafEndo =
      cfpSnd cfpTerminal p.T ≫ isLeafEndo :=
    lhs_embed.trans rhs_embed.symm
  calc toRSpineNat ≫ isLeafEndo
      = cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T ≫
        toRSpineNat ≫ isLeafEndo := by
        rw [← Category.assoc
          (cfpLift _ _) (cfpSnd _ _),
          cfpLift_snd, Category.id_comp]
    _ = cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T ≫
        isLeafEndo := by
        rw [h_embed]
    _ = isLeafEndo := by
        rw [← Category.assoc, cfpLift_snd,
          Category.id_comp]

/-- `toRSpineNat` commutes with `natPred`:
`toRSpineNat ≫ natPred = natPred ≫ toRSpineNat`.
Both sides map `ℓ` to `ℓ` and `β(l, r)` to
`toRSpineNat(r)`. The proof uses `paraElim_uniq`
to show both embedded morphisms satisfy the same
paramorphism equations. -/
theorem natPred_toRSpineNat_comm :
    toRSpineNat ≫ natPred =
    natPred ≫ (toRSpineNat : p.T ⟶ p.T) := by
  set g : cfpProd cfpTerminal
      (cfpProd (cfpProd p.T p.T)
        (cfpProd p.T p.T)) ⟶ p.T :=
    cfpSnd cfpTerminal _ ≫
      cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
      cfpSnd p.T p.T ≫ toRSpineNat
  have both_base (φ : p.T ⟶ p.T)
      (hℓ : p.ℓ ≫ φ = p.ℓ)
      (_hβ : p.β ≫ φ =
        cfpSnd p.T p.T ≫ toRSpineNat) :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        (cfpSnd cfpTerminal p.T ≫ φ) =
      p.ℓ := by
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc,
      @cfpTerminalFrom_terminal C _ h,
      Category.id_comp, hℓ]
  have both_step (φ : p.T ⟶ p.T)
      (hβ : p.β ≫ φ =
        cfpSnd p.T p.T ≫ toRSpineNat) :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (cfpSnd cfpTerminal p.T ≫ φ) =
      cfpLift
          (cfpFst cfpTerminal
            (cfpProd p.T p.T))
          (cfpLift
            (cfpSnd cfpTerminal
              (cfpProd p.T p.T))
            (cfpLiftAssoc
              (cfpSnd cfpTerminal p.T ≫ φ)
              (cfpSnd cfpTerminal p.T ≫
                φ))) ≫ g := by
    have lhs_eq :
        cfpMap (𝟙 cfpTerminal) p.β ≫
          (cfpSnd cfpTerminal p.T ≫ φ) =
        cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T ≫
          toRSpineNat := by
      rw [← Category.assoc, cfpMap_snd,
        Category.assoc, hβ]
    have rhs_eq :
        cfpLift
          (cfpFst cfpTerminal
            (cfpProd p.T p.T))
          (cfpLift
            (cfpSnd cfpTerminal
              (cfpProd p.T p.T))
            (cfpLiftAssoc
              (cfpSnd cfpTerminal p.T ≫ φ)
              (cfpSnd cfpTerminal p.T ≫
                φ))) ≫ g =
        cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T ≫
          toRSpineNat := by
      simp only [g]
      simp only [← Category.assoc]
      rw [cfpLift_snd, cfpLift_fst]
    rw [lhs_eq, rhs_eq]
  have toRSN_natPred_β :
      p.β ≫ toRSpineNat ≫ natPred =
      cfpSnd p.T p.T ≫ toRSpineNat := by
    rw [← Category.assoc, toRSpineNat_β,
      Category.assoc, β_natPred,
      cfpLift_snd]
  have natPred_toRSN_β :
      p.β ≫ natPred ≫ toRSpineNat =
      cfpSnd p.T p.T ≫ toRSpineNat := by
    rw [← Category.assoc, β_natPred]
  have lhs_para :
      cfpSnd cfpTerminal p.T ≫
        toRSpineNat ≫ natPred =
      paraElim p.ℓ g := by
    exact paraElim_uniq p.ℓ g
      (cfpSnd cfpTerminal p.T ≫
        toRSpineNat ≫ natPred)
      (both_base (toRSpineNat ≫ natPred)
        (by rw [← Category.assoc,
            toRSpineNat_ℓ, natPred_ℓ])
        toRSN_natPred_β)
      (both_step (toRSpineNat ≫ natPred)
        toRSN_natPred_β)
  have rhs_para :
      cfpSnd cfpTerminal p.T ≫
        natPred ≫ toRSpineNat =
      paraElim p.ℓ g := by
    exact paraElim_uniq p.ℓ g
      (cfpSnd cfpTerminal p.T ≫
        natPred ≫ toRSpineNat)
      (both_base (natPred ≫ toRSpineNat)
        (by rw [← Category.assoc,
            natPred_ℓ, toRSpineNat_ℓ])
        natPred_toRSN_β)
      (both_step (natPred ≫ toRSpineNat)
        natPred_toRSN_β)
  calc toRSpineNat ≫ natPred
      = cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T ≫
        toRSpineNat ≫ natPred := by
        rw [← Category.assoc
          (cfpLift _ _) (cfpSnd _ _),
          cfpLift_snd, Category.id_comp]
    _ = cfpLift (cfpTerminalFrom p.T)
          (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T ≫
        natPred ≫ toRSpineNat := by
        congr 1
        exact lhs_para.trans rhs_para.symm
    _ = natPred ≫ toRSpineNat := by
        rw [← Category.assoc
          (cfpLift _ _) (cfpSnd _ _),
          cfpLift_snd, Category.id_comp]

/-- Normalizing the first argument of `natTruncSub`
via `toRSpineNat` is absorbed into the output:
`cfpMap toRSpineNat (𝟙 T) ≫ natTruncSub
  = natTruncSub ≫ toRSpineNat`. -/
theorem natTruncSub_toRSpineNat_first :
    cfpMap (toRSpineNat : p.T ⟶ p.T)
      (𝟙 p.T) ≫ natTruncSub =
    natTruncSub ≫ toRSpineNat := by
  have comm :
      cfpMap toRSpineNat toRSpineNat ≫
        (cfpSnd p.T p.T ≫ natPred) =
      (cfpSnd p.T p.T ≫ natPred) ≫
        (toRSpineNat : p.T ⟶ p.T) := by
    simp only [← Category.assoc]
    rw [cfpMap_snd]
    simp only [Category.assoc]
    rw [natPred_toRSpineNat_comm]
  have rhs :
      natTruncSub ≫ toRSpineNat =
      p.elim (toRSpineNat : p.T ⟶ p.T)
        (cfpSnd p.T p.T ≫ natPred) := by
    change p.elim (𝟙 p.T)
        (cfpSnd p.T p.T ≫ natPred) ≫
      toRSpineNat = _
    rw [elim_algebra_morphism
      (𝟙 p.T) (cfpSnd p.T p.T ≫ natPred)
      toRSpineNat
      (cfpSnd p.T p.T ≫ natPred)
      comm, Category.id_comp]
  have lhs :
      cfpMap toRSpineNat (𝟙 p.T) ≫
        natTruncSub =
      p.elim (toRSpineNat : p.T ⟶ p.T)
        (cfpSnd p.T p.T ≫ natPred) := by
    unfold natTruncSub
    rw [elim_naturality toRSpineNat (𝟙 p.T)
      (cfpSnd p.T p.T ≫ natPred),
      Category.comp_id]
  rw [lhs, rhs]

/-- `natTruncSub` is insensitive to normalization
of its second argument:
`cfpMap (𝟙 T) toRSpineNat ≫ natTruncSub
  = natTruncSub`. -/
theorem natTruncSub_toRSpineNat_second :
    cfpMap (𝟙 p.T) toRSpineNat ≫ natTruncSub =
    (natTruncSub : cfpProd p.T p.T ⟶ p.T) := by
  change _ = p.elim (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natPred)
  apply p.elim_uniq (𝟙 p.T)
    (cfpSnd p.T p.T ≫ natPred)
  · rw [← Category.assoc]
    have : cfpInsertSnd p.ℓ p.T ≫
        cfpMap (𝟙 p.T) toRSpineNat =
      cfpInsertSnd p.ℓ p.T := by
      unfold cfpInsertSnd
      rw [cfpLift_cfpMap, Category.id_comp,
        Category.assoc, toRSpineNat_ℓ]
    rw [this, natTruncSub_ℓ]
  · rw [← Category.assoc
      (cfpMap (𝟙 p.T) p.β),
      cfpMap_comp, Category.id_comp,
      toRSpineNat_β,
      cfpMap_id_comp'
        (cfpLift
          (cfpTerminalFrom
            (cfpProd p.T p.T) ≫ p.ℓ)
          (cfpSnd p.T p.T ≫ toRSpineNat))
        p.β,
      Category.assoc,
      show cfpMap (𝟙 p.T) p.β ≫
        natTruncSub =
      cfpLiftAssoc natTruncSub
        natTruncSub ≫
        cfpSnd p.T p.T ≫ natPred from
        p.elim_β (𝟙 p.T)
          (cfpSnd p.T p.T ≫ natPred)]
    simp only [← Category.assoc
      (cfpLiftAssoc _ _)]
    rw [show cfpLiftAssoc natTruncSub
        natTruncSub ≫ cfpSnd p.T p.T =
      cfpAssocSnd p.T p.T p.T ≫
        natTruncSub from by
      unfold cfpLiftAssoc; rw [cfpLift_snd]]
    rw [show cfpLiftAssoc
        (cfpMap (𝟙 p.T) toRSpineNat ≫
          natTruncSub)
        (cfpMap (𝟙 p.T) toRSpineNat ≫
          natTruncSub) ≫
        cfpSnd p.T p.T =
      cfpAssocSnd p.T p.T p.T ≫
        cfpMap (𝟙 p.T) toRSpineNat ≫
          natTruncSub from by
      unfold cfpLiftAssoc; rw [cfpLift_snd]]
    simp only [← Category.assoc
      (cfpAssocSnd _ _ _)]
    have key :
        cfpMap (𝟙 p.T)
          (cfpLift
            (cfpTerminalFrom
              (cfpProd p.T p.T) ≫ p.ℓ)
            (cfpSnd p.T p.T ≫
              toRSpineNat)) ≫
          cfpAssocSnd p.T p.T p.T =
        cfpAssocSnd p.T p.T p.T ≫
          cfpMap (𝟙 p.T) toRSpineNat := by
      unfold cfpAssocSnd
      rw [cfpLift_precomp,
        cfpLift_cfpMap]
      congr 1
      · rw [cfpMap_fst]
      · rw [← Category.assoc, cfpMap_snd,
          Category.assoc, cfpLift_snd,
          Category.assoc]
    rw [show cfpMap (𝟙 p.T)
        (cfpLift
          (cfpTerminalFrom
            (cfpProd p.T p.T) ≫ p.ℓ)
          (cfpSnd p.T p.T ≫
            toRSpineNat)) ≫
        (cfpAssocSnd p.T p.T p.T ≫
          natTruncSub) ≫ natPred =
      (cfpMap (𝟙 p.T)
          (cfpLift
            (cfpTerminalFrom
              (cfpProd p.T p.T) ≫ p.ℓ)
            (cfpSnd p.T p.T ≫
              toRSpineNat)) ≫
        cfpAssocSnd p.T p.T p.T) ≫
          natTruncSub ≫ natPred from by
      simp only [Category.assoc]]
    rw [key]
    simp only [Category.assoc]

/-- Normalizing both arguments of `natEq` via
`toRSpineNat` doesn't change the result:
`cfpMap toRSpineNat toRSpineNat ≫ natEq = natEq`.
-/
theorem natEq_toRSpineNat :
    cfpMap toRSpineNat toRSpineNat ≫ natEq =
    (natEq : cfpProd p.T p.T ⟶ p.T) := by
  unfold natEq
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp]
  have factor :
      cfpMap toRSpineNat toRSpineNat =
      cfpMap (𝟙 p.T) toRSpineNat ≫
        cfpMap toRSpineNat (𝟙 p.T) := by
    rw [cfpMap_comp, Category.comp_id,
      Category.id_comp]
  have sub_both :
      cfpMap toRSpineNat toRSpineNat ≫
        natTruncSub =
      natTruncSub ≫
        (toRSpineNat : p.T ⟶ p.T) := by
    rw [factor, Category.assoc,
      natTruncSub_toRSpineNat_first
        (C := C) (p := p),
      ← Category.assoc,
      natTruncSub_toRSpineNat_second
        (C := C) (p := p)]
  have swap_sub_both :
      cfpMap toRSpineNat toRSpineNat ≫
        cfpSwap p.T p.T ≫ natTruncSub =
      cfpSwap p.T p.T ≫
        natTruncSub ≫ toRSpineNat := by
    rw [← Category.assoc,
      ← cfpSwap_cfpMap_diag toRSpineNat,
      Category.assoc, sub_both]
  rw [sub_both, swap_sub_both]
  have inner :
      cfpLift (natTruncSub ≫ toRSpineNat)
        (cfpSwap p.T p.T ≫
          natTruncSub ≫ toRSpineNat) ≫
        natPlus ≫ isLeafEndo =
      cfpLift natTruncSub
        (cfpSwap p.T p.T ≫
          natTruncSub) ≫
        natPlus ≫ isLeafEndo := by
    have rsn_factor :
        cfpLift (natTruncSub ≫ toRSpineNat)
          (cfpSwap p.T p.T ≫
            natTruncSub ≫ toRSpineNat) =
        cfpLift natTruncSub
          (cfpSwap p.T p.T ≫
            natTruncSub) ≫
          cfpMap toRSpineNat toRSpineNat := by
      rw [cfpLift_cfpMap]
      simp only [Category.assoc]
    have plus_rsn :
        cfpMap (toRSpineNat : p.T ⟶ p.T)
          toRSpineNat ≫ natPlus =
        natPlus ≫ toRSpineNat := by
      rw [factor, Category.assoc,
        natPlus_toRSpineNat_first
          (C := C) (p := p),
        ← Category.assoc,
        natPlus_toRSpineNat_second
          (C := C) (p := p)]
    rw [rsn_factor]
    simp only [Category.assoc]
    simp only [← Category.assoc
      (cfpMap _ _) natPlus]
    rw [plus_rsn, Category.assoc,
      toRSpineNat_isLeafEndo
        (C := C) (p := p)]
  rw [Category.assoc, inner]

/-- The successor of any right-spine natural is
not a leaf. -/
private theorem natSucc_isLeafEndo' :
    natSucc ≫ isLeafEndo =
    cfpTerminalFrom p.T ≫
      (treeFalse :
        cfpTerminal (C := C) ⟶ p.T) := by
  unfold natSucc
  rw [Category.assoc, isLeafEndo_β,
    ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- `natTri` preserves leaf/branch classification:
`natTri ≫ isLeafEndo = isLeafEndo`. -/
theorem natTri_isLeafEndo :
    natTri ≫ isLeafEndo =
    (isLeafEndo : p.T ⟶ p.T) := by
  -- Prove the parameterized version:
  -- natTriHelper ≫ cfpSnd ≫ isLeafEndo
  --   = cfpSnd 1 T ≫ isLeafEndo
  -- via p.elim_uniq.
  set g :=
    cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse
  have base_lhs :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        (natTriHelper ≫ cfpSnd p.T p.T ≫
          isLeafEndo) =
      p.ℓ := by
    rw [← Category.assoc, ← Category.assoc,
      natTriHelper_ℓ, cfpLift_snd,
      isLeafEndo_ℓ]
  have base_rhs :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        (cfpSnd cfpTerminal p.T ≫
          isLeafEndo) =
      p.ℓ := by
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_snd,
      cfpTerminalFrom_terminal,
      Category.id_comp, isLeafEndo_ℓ]
  have natTriStep_cfpSnd' :
      (natTriStep :
        cfpProd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ⟶
          cfpProd p.T p.T) ≫
        cfpSnd p.T p.T =
      cfpLift
        ((cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpFst p.T p.T) ≫ natSucc)
        (cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) ≫
        natPlus := by
    unfold natTriStep
    rw [cfpLift_snd]
    congr 1
    exact cfpLift_uniq _ _ _
      (by rw [cfpLift_fst]; simp [Category.assoc])
      (by rw [cfpLift_snd])
  have triStep_snd_isLeaf :
      natTriStep ≫ cfpSnd p.T p.T ≫
        isLeafEndo =
      cfpTerminalFrom
        (cfpProd (cfpProd p.T p.T)
          (cfpProd p.T p.T)) ≫
        treeFalse := by
    rw [← Category.assoc, natTriStep_cfpSnd',
      Category.assoc, ← Category.assoc
        (cfpLift _ _),
      natPlus_succ_left _ _]
    simp only [Category.assoc]
    rw [natSucc_isLeafEndo']
    simp only [← Category.assoc]
    congr 1; exact h.terminal.uniq _
  have step_lhs :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (natTriHelper ≫ cfpSnd p.T p.T ≫
          isLeafEndo) =
      cfpLiftAssoc
        (natTriHelper ≫ cfpSnd p.T p.T ≫
          isLeafEndo)
        (natTriHelper ≫ cfpSnd p.T p.T ≫
          isLeafEndo) ≫ g := by
    rw [← Category.assoc, ← Category.assoc,
      natTriHelper_β]
    simp only [Category.assoc]
    rw [triStep_snd_isLeaf]
    rw [show cfpLiftAssoc
        (natTriHelper ≫ cfpSnd p.T p.T ≫
          isLeafEndo)
        (natTriHelper ≫ cfpSnd p.T p.T ≫
          isLeafEndo) ≫ g =
      cfpTerminalFrom _ ≫ treeFalse from by
      rw [← Category.assoc]; congr 1
      exact h.terminal.uniq _]
    rw [← Category.assoc]; congr 1
    exact h.terminal.uniq _
  have step_rhs :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (cfpSnd cfpTerminal p.T ≫
          isLeafEndo) =
      cfpLiftAssoc
        (cfpSnd cfpTerminal p.T ≫ isLeafEndo)
        (cfpSnd cfpTerminal p.T ≫ isLeafEndo)
          ≫ g := by
    rw [← Category.assoc, cfpMap_snd,
      Category.assoc, isLeafEndo_β]
    rw [show cfpLiftAssoc
        (cfpSnd cfpTerminal p.T ≫ isLeafEndo)
        (cfpSnd cfpTerminal p.T ≫ isLeafEndo)
          ≫ g =
      cfpTerminalFrom _ ≫ treeFalse from by
      rw [← Category.assoc]; congr 1
      exact h.terminal.uniq _]
    rw [← Category.assoc]; congr 1
    exact h.terminal.uniq _
  have param_eq :
      natTriHelper ≫ cfpSnd p.T p.T ≫
        isLeafEndo =
      cfpSnd cfpTerminal p.T ≫ isLeafEndo :=
    (p.elim_uniq p.ℓ g
      (natTriHelper ≫ cfpSnd p.T p.T ≫
        isLeafEndo)
      base_lhs step_lhs).trans
    (p.elim_uniq p.ℓ g
      (cfpSnd cfpTerminal p.T ≫ isLeafEndo)
      base_rhs step_rhs).symm
  unfold natTri
  simp only [Category.assoc]
  change cfpLift (cfpTerminalFrom p.T)
    (𝟙 p.T) ≫
    natTriHelper ≫ cfpSnd p.T p.T ≫
    isLeafEndo = isLeafEndo
  rw [param_eq, ← Category.assoc,
    cfpLift_snd, Category.id_comp]

/-- Left cancellation for `natPlus` under `natEq`
(unrestricted):
`natEq(c + a, c + b) = natEq(a, b)` for all
`a, b, c` without normalization hypotheses. -/
theorem natPlus_cancel_left {A : C}
    (a b c : A ⟶ p.T) :
    cfpLift (cfpLift c a ≫ natPlus)
        (cfpLift c b ≫ natPlus) ≫ natEq =
    cfpLift a b ≫
      (natEq : cfpProd p.T p.T ⟶ p.T) := by
  -- Normalize all arguments via toRSpineNat.
  -- Step 1: natEq absorbs toRSN on both sides.
  have rsn_absorb :
      ∀ (f g : A ⟶ p.T),
        cfpLift f g ≫ natEq =
        cfpLift (f ≫ toRSpineNat)
          (g ≫ toRSpineNat) ≫
          (natEq :
            cfpProd p.T p.T ⟶ p.T) := by
    intro f g
    rw [show cfpLift (f ≫ toRSpineNat)
        (g ≫ toRSpineNat) =
      cfpLift f g ≫
        cfpMap toRSpineNat toRSpineNat from
      (cfpLift_cfpMap f g
        toRSpineNat toRSpineNat).symm,
      Category.assoc, natEq_toRSpineNat]
  -- Step 2: toRSN(natPlus(c, a))
  --   = natPlus(toRSN(c), a).
  have plus_rsn_first (x y : A ⟶ p.T) :
      cfpLift x y ≫ natPlus ≫ toRSpineNat =
      cfpLift (x ≫ toRSpineNat) y ≫
        (natPlus :
          cfpProd p.T p.T ⟶ p.T) := by
    rw [← natPlus_toRSpineNat_first,
      ← Category.assoc,
      cfpLift_cfpMap, Category.comp_id]
  -- Step 3: natPlus(toRSN(c), a)
  --   = natPlus(toRSN(c), toRSN(a)).
  have plus_rsn_second (x y : A ⟶ p.T) :
      cfpLift x y ≫ natPlus =
      cfpLift x (y ≫ toRSpineNat) ≫
        (natPlus :
          cfpProd p.T p.T ⟶ p.T) := by
    rw [show cfpLift x (y ≫ toRSpineNat) =
      cfpLift x y ≫
        cfpMap (𝟙 p.T) toRSpineNat from by
        rw [cfpLift_cfpMap, Category.comp_id]
      , Category.assoc,
      natPlus_toRSpineNat_second]
  -- Combine: LHS uses rsn_absorb + plus_rsn.
  rw [rsn_absorb]
  simp only [Category.assoc]
  rw [plus_rsn_first c a, plus_rsn_first c b,
    plus_rsn_second (c ≫ toRSpineNat) a,
    plus_rsn_second (c ≫ toRSpineNat) b]
  -- Now all three arguments are rsn.
  have hc : IsRSpineNatNorm
      (c ≫ toRSpineNat) := by
    unfold IsRSpineNatNorm
    rw [Category.assoc, toRSpineNat_idem]
  have ha : IsRSpineNatNorm
      (a ≫ toRSpineNat) := by
    unfold IsRSpineNatNorm
    rw [Category.assoc, toRSpineNat_idem]
  have hb : IsRSpineNatNorm
      (b ≫ toRSpineNat) := by
    unfold IsRSpineNatNorm
    rw [Category.assoc, toRSpineNat_idem]
  rw [natPlus_cancel_left_rsn
    (a ≫ toRSpineNat) (b ≫ toRSpineNat)
    (c ≫ toRSpineNat) ha hb hc,
    ← rsn_absorb]

end GebLean

namespace GebLean

open CategoryTheory

universe v' u'

variable {C' : Type u'} [Category.{v'} C']
  [h' : HasChosenFiniteProducts C']

/-- `cfpMap` with identity first component distributes
over composition in the second component. -/
theorem cfpMap_id_comp
    {A B B' B'' : C'}
    (f : B ⟶ B') (g : B' ⟶ B'') :
    cfpMap (𝟙 A) (f ≫ g) =
    cfpMap (𝟙 A) f ≫
      cfpMap (𝟙 A) g := by
  conv_lhs =>
    rw [show (𝟙 A : A ⟶ A) = 𝟙 A ≫ 𝟙 A from
      (Category.id_comp (𝟙 A)).symm]
  rw [← cfpMap_comp]

end GebLean
