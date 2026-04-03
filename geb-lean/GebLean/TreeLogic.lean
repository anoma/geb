import GebLean.EqualizerCompletionPBTO

/-!
# Boolean Logic on Binary Trees

Defines Boolean logic operations on the binary tree
type T within a Lawvere BT theory (any category with
chosen finite products and a parameterized binary tree
object).

The encoding uses leaf as true and branch(leaf, leaf)
as false.  Operations are defined as morphisms in the
ambient category using the `elim` catamorphism.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-- The "false" element of T: `branch(leaf, leaf)`,
as a morphism from the terminal object. -/
def treeFalse :
    cfpTerminal (C := C) ⟶ p.T :=
  cfpLift p.ℓ p.ℓ ≫ p.β

/-- Leaf detection: `isLeaf(*, leaf) = leaf` (true),
`isLeaf(*, branch(a,b)) = branch(leaf,leaf)` (false).
Defined as `elim ℓ g` where the step `g` returns
the constant `branch(leaf,leaf)` regardless of
the recursive results. -/
def isLeaf :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  p.elim p.ℓ
    (cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse)

/-- Leaf computation rule for `isLeaf`:
`cfpInsertSnd ℓ cfpTerminal ≫ isLeaf = ℓ`. -/
theorem isLeaf_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      isLeaf = p.ℓ := by
  unfold isLeaf
  exact p.elim_ℓ p.ℓ _

/-- Branch computation rule for `isLeaf`:
`cfpMap (𝟙 cfpTerminal) β ≫ isLeaf =
  cfpLiftAssoc isLeaf isLeaf ≫
    (cfpTerminalFrom _ ≫ treeFalse)`. -/
theorem isLeaf_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      isLeaf =
    cfpLiftAssoc isLeaf isLeaf ≫
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse) := by
  unfold isLeaf
  exact p.elim_β p.ℓ _

/-- Boolean negation on trees:
`treeNot(*, leaf) = branch(leaf,leaf)` (false),
`treeNot(*, branch(a,b)) = leaf` (true).
Defined as `elim treeFalse (cfpTerminalFrom _ ≫ ℓ)`
where the base returns false and the step returns
leaf regardless of the recursive results. -/
def treeNot :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  p.elim treeFalse
    (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ)

/-- Leaf computation rule for `treeNot`:
`cfpInsertSnd ℓ cfpTerminal ≫ treeNot =
  treeFalse`. -/
theorem treeNot_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      treeNot = treeFalse := by
  unfold treeNot
  exact p.elim_ℓ treeFalse _

/-- Branch computation rule for `treeNot`. -/
theorem treeNot_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      treeNot =
    cfpLiftAssoc treeNot treeNot ≫
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        p.ℓ) := by
  unfold treeNot
  exact p.elim_β treeFalse _

/-- Tree conjunction (grafting):
`treeAnd(a, leaf) = a`,
`treeAnd(a, branch(t₁,t₂)) =
  branch(treeAnd(a,t₁), treeAnd(a,t₂))`.
Leaf is the right identity for this operation. -/
def treeAnd :
    cfpProd p.T p.T ⟶ p.T :=
  p.elim (𝟙 p.T) p.β

/-- Right identity for `treeAnd`:
`cfpInsertSnd ℓ T ≫ treeAnd = 𝟙 T`. -/
theorem treeAnd_leaf_right :
    cfpInsertSnd p.ℓ p.T ≫ treeAnd =
      𝟙 p.T := by
  unfold treeAnd
  exact p.elim_ℓ (𝟙 p.T) p.β

/-- Branch computation rule for `treeAnd`:
`cfpMap (𝟙 T) β ≫ treeAnd =
  cfpLiftAssoc treeAnd treeAnd ≫ β`. -/
theorem treeAnd_β :
    cfpMap (𝟙 p.T) p.β ≫ treeAnd =
    cfpLiftAssoc treeAnd treeAnd ≫ p.β := by
  unfold treeAnd
  exact p.elim_β (𝟙 p.T) p.β

omit p in
/-- The terminal morphism from the terminal
object is the identity. -/
theorem cfpTerminalFrom_terminal :
    cfpTerminalFrom (cfpTerminal (C := C)) =
      𝟙 cfpTerminal :=
  (h.terminal.uniq (𝟙 cfpTerminal)).symm

/-- `cfpSnd` is the catamorphism
`elim ℓ β : cfpProd cfpTerminal T ⟶ T`.
This follows from uniqueness: the second
projection satisfies both the leaf and branch
computation rules. -/
theorem cfpSnd_eq_elim_ℓ_β :
    cfpSnd cfpTerminal p.T =
    p.elim p.ℓ p.β := by
  exact p.elim_uniq p.ℓ p.β
    (cfpSnd cfpTerminal p.T)
    (by
      unfold cfpInsertSnd
      rw [cfpLift_snd,
        cfpTerminalFrom_terminal,
        Category.id_comp])
    (by
      rw [cfpMap_snd]
      congr 1
      unfold cfpLiftAssoc
      apply cfpLift_uniq
      · unfold cfpAssocFst
        exact (cfpLift_snd _ _).symm
      · unfold cfpAssocSnd
        exact (cfpLift_snd _ _).symm)

/-- Tree negation as an endomorphism on T,
obtained by inserting the terminal component
into `treeNot`. -/
def treeNotEndo : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    treeNot

/-- Left identity for `treeAnd`:
`cfpMap ℓ (𝟙 T) ≫ treeAnd = cfpSnd`,
meaning `treeAnd(leaf, b) = b`. -/
theorem treeAnd_leaf_left :
    cfpMap p.ℓ (𝟙 p.T) ≫ treeAnd =
      cfpSnd cfpTerminal p.T := by
  unfold treeAnd
  rw [elim_naturality, Category.comp_id,
    ← cfpSnd_eq_elim_ℓ_β]

/-- Tree disjunction (De Morgan):
`treeOr(a, b) = treeNot(treeAnd(treeNot(a),
  treeNot(b)))`.
Defined by negating both inputs, combining via
`treeAnd`, and negating the result. -/
def treeOr : cfpProd p.T p.T ⟶ p.T :=
  cfpMap treeNotEndo treeNotEndo ≫
    treeAnd ≫ treeNotEndo

/-- Tree implication:
`treeImplies(a, b) = treeOr(treeNot(a), b)`.
Defined by negating the first input and applying
`treeOr`. -/
def treeImplies : cfpProd p.T p.T ⟶ p.T :=
  cfpMap treeNotEndo (𝟙 p.T) ≫ treeOr

/-- Intermediate fold for if-then-else.
Folds the condition tree into a pair, where the
step function extracts and duplicates the second
component of the first recursive result:
`g((x₁,y₁), (x₂,y₂)) = (y₁, y₁)`.

For leaf (true): returns the parameter pair as-is.
For branch (false): returns `(else, else)`. -/
def iteFold :
    cfpProd (cfpProd p.T p.T) p.T ⟶
      cfpProd p.T p.T :=
  p.elim (𝟙 (cfpProd p.T p.T))
    (cfpLift
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T)
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T))

/-- If-then-else on trees:
`treeIte((then, else), cond)`:
  - if `cond = leaf`: returns `then`
  - if `cond = branch(_, _)`: returns `else`
Defined as `iteFold ≫ cfpFst`. -/
def treeIte :
    cfpProd (cfpProd p.T p.T) p.T ⟶ p.T :=
  iteFold ≫ cfpFst p.T p.T

/-- Leaf computation rule for `iteFold`:
returns the parameter pair unchanged. -/
theorem iteFold_ℓ :
    cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
      iteFold = 𝟙 (cfpProd p.T p.T) := by
  unfold iteFold
  exact p.elim_ℓ (𝟙 (cfpProd p.T p.T)) _

/-- Leaf computation rule for `treeIte`:
returns the first (then) branch. -/
theorem treeIte_ℓ :
    cfpInsertSnd p.ℓ (cfpProd p.T p.T) ≫
      treeIte = cfpFst p.T p.T := by
  unfold treeIte
  rw [← Category.assoc, iteFold_ℓ,
    Category.id_comp]

/-- Abbreviation for the first-component
projection from a pair of pairs, extracting the
first element of the first pair. -/
def cfpFstFst (A B D E : C) :
    cfpProd (cfpProd A B)
      (cfpProd D E) ⟶ A :=
  cfpFst (cfpProd A B) (cfpProd D E) ≫
    cfpFst A B

/-- Abbreviation for the first-component
projection from a pair of pairs, extracting the
first element of the second pair. -/
def cfpSndFst (A B D E : C) :
    cfpProd (cfpProd A B)
      (cfpProd D E) ⟶ D :=
  cfpSnd (cfpProd A B) (cfpProd D E) ≫
    cfpFst D E

/-- Destructuring fold: given `* × T`, produces
`T × T` where the first component reconstructs the
tree and the second component gives the left child
(or leaf for a leaf input).

Base: `(leaf, leaf)`.
Step: `g((selfL, _), (selfR, _)) =
  (branch(selfL, selfR), selfL)`. -/
def destructFold :
    cfpProd cfpTerminal p.T ⟶
      cfpProd p.T p.T :=
  p.elim
    (cfpLift p.ℓ p.ℓ)
    (cfpLift
      (cfpLift
        (cfpFstFst p.T p.T p.T p.T)
        (cfpSndFst p.T p.T p.T p.T) ≫
        p.β)
      (cfpFstFst p.T p.T p.T p.T))

/-- Left destructor:
`treeLeft(*, leaf) = leaf`,
`treeLeft(*, branch(l, r)) = l`.
Defined as the second projection of
`destructFold`. -/
def treeLeft :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  destructFold ≫ cfpSnd p.T p.T

/-- Destructuring fold for the right child:
the step function `g((selfL, _), (selfR, _)) =
  (branch(selfL, selfR), selfR)` tracks the
right child instead of the left. -/
def destructFoldR :
    cfpProd cfpTerminal p.T ⟶
      cfpProd p.T p.T :=
  p.elim
    (cfpLift p.ℓ p.ℓ)
    (cfpLift
      (cfpLift
        (cfpFstFst p.T p.T p.T p.T)
        (cfpSndFst p.T p.T p.T p.T) ≫
        p.β)
      (cfpSndFst p.T p.T p.T p.T))

/-- Right destructor:
`treeRight(*, leaf) = leaf`,
`treeRight(*, branch(l, r)) = r`.
Defined as the second projection of
`destructFoldR`. -/
def treeRight :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  destructFoldR ≫ cfpSnd p.T p.T

/-- Leaf computation rule for `destructFold`. -/
theorem destructFold_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      destructFold =
    cfpLift p.ℓ p.ℓ := by
  unfold destructFold
  exact p.elim_ℓ (cfpLift p.ℓ p.ℓ) _

/-- Leaf computation rule for `treeLeft`. -/
theorem treeLeft_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      treeLeft = p.ℓ := by
  unfold treeLeft
  rw [← Category.assoc, destructFold_ℓ,
    cfpLift_snd]

/-- Leaf computation rule for `destructFoldR`. -/
theorem destructFoldR_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      destructFoldR =
    cfpLift p.ℓ p.ℓ := by
  unfold destructFoldR
  exact p.elim_ℓ (cfpLift p.ℓ p.ℓ) _

/-- Leaf computation rule for `treeRight`. -/
theorem treeRight_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      treeRight = p.ℓ := by
  unfold treeRight
  rw [← Category.assoc, destructFoldR_ℓ,
    cfpLift_snd]

/-- Branch computation rule for `iteFold`. -/
theorem iteFold_β :
    cfpMap (𝟙 (cfpProd p.T p.T)) p.β ≫
      iteFold =
    cfpLiftAssoc iteFold iteFold ≫
      cfpLift
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T)
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) := by
  unfold iteFold
  exact p.elim_β (𝟙 (cfpProd p.T p.T)) _

/-- Branch computation rule for `destructFold`. -/
theorem destructFold_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      destructFold =
    cfpLiftAssoc destructFold destructFold ≫
      cfpLift
        (cfpLift
          (cfpFstFst p.T p.T p.T p.T)
          (cfpSndFst p.T p.T p.T p.T) ≫
          p.β)
        (cfpFstFst p.T p.T p.T p.T) := by
  unfold destructFold
  exact p.elim_β (cfpLift p.ℓ p.ℓ) _

/-- Branch computation rule for `destructFoldR`. -/
theorem destructFoldR_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      destructFoldR =
    cfpLiftAssoc destructFoldR destructFoldR ≫
      cfpLift
        (cfpLift
          (cfpFstFst p.T p.T p.T p.T)
          (cfpSndFst p.T p.T p.T p.T) ≫
          p.β)
        (cfpSndFst p.T p.T p.T p.T) := by
  unfold destructFoldR
  exact p.elim_β (cfpLift p.ℓ p.ℓ) _

/-- Branch computation rule for `treeIte`:
after folding both subtrees, extracts the second
component of the first recursive result. -/
theorem treeIte_β :
    cfpMap (𝟙 (cfpProd p.T p.T)) p.β ≫
      treeIte =
    cfpLiftAssoc iteFold iteFold ≫
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T) := by
  unfold treeIte
  rw [← Category.assoc, iteFold_β,
    Category.assoc, cfpLift_fst]

/-- Branch computation rule for `treeLeft`:
after folding both subtrees, extracts the first
component of the first recursive result. -/
theorem treeLeft_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      treeLeft =
    cfpLiftAssoc destructFold destructFold ≫
      cfpFstFst p.T p.T p.T p.T := by
  unfold treeLeft
  rw [← Category.assoc, destructFold_β,
    Category.assoc, cfpLift_snd]

/-- Branch computation rule for `treeRight`:
after folding both subtrees, extracts the first
component of the second recursive result. -/
theorem treeRight_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      treeRight =
    cfpLiftAssoc destructFoldR destructFoldR ≫
      cfpSndFst p.T p.T p.T p.T := by
  unfold treeRight
  rw [← Category.assoc, destructFoldR_β,
    Category.assoc, cfpLift_snd]

/-- Leaf computation rule for `treeNotEndo`:
`ℓ ≫ treeNotEndo = treeFalse`. -/
theorem treeNotEndo_ℓ :
    p.ℓ ≫ treeNotEndo = treeFalse := by
  unfold treeNotEndo
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have h1 : p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h1]
  have h2 : cfpLift
      (cfpTerminalFrom cfpTerminal) p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact cfpTerminalFrom_terminal
    · rw [cfpTerminalFrom_terminal,
        Category.id_comp]
  rw [h2]
  exact treeNot_ℓ

/-- `treeFalse ≫ treeNotEndo = ℓ`. -/
theorem treeNotEndo_treeFalse :
    treeFalse ≫ treeNotEndo = p.ℓ := by
  unfold treeNotEndo treeFalse
  -- Goal: (cfpLift ℓ ℓ ≫ β) ≫
  --   cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
  --   treeNot = ℓ
  rw [Category.assoc]
  -- Goal: cfpLift ℓ ℓ ≫ β ≫
  --   cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
  --   treeNot = ℓ
  have step1 : p.β ≫
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) =
      cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        p.β := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    exact h.terminal.uniq _
  rw [← Category.assoc p.β _ treeNot, step1]
  -- Goal: cfpLift ℓ ℓ ≫
  --   cfpLift (cfpTerminalFrom (T×T)) β ≫
  --   treeNot = ℓ
  rw [← Category.assoc, cfpLift_precomp]
  have h2 : cfpLift p.ℓ p.ℓ ≫
      cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h2]
  change
    cfpLift (cfpTerminalFrom cfpTerminal)
      treeFalse ≫ treeNot = p.ℓ
  -- Factor treeFalse through β
  have step2 :
      cfpLift (cfpTerminalFrom cfpTerminal)
        treeFalse =
      cfpLift (cfpTerminalFrom cfpTerminal)
        (cfpLift p.ℓ p.ℓ) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    unfold treeFalse cfpMap
    rw [cfpLift_precomp]
    congr 1
    · rw [← Category.assoc, cfpLift_fst,
        Category.comp_id]
    · rw [← Category.assoc, cfpLift_snd]
  rw [step2, Category.assoc, treeNot_β]
  -- Goal: cfpLift ... (cfpLift ℓ ℓ) ≫
  --   cfpLiftAssoc treeNot treeNot ≫
  --   cfpTerminalFrom _ ≫ ℓ = ℓ
  -- The composition ...≫ cfpTerminalFrom _ is
  -- a morphism to cfpTerminal, hence equal to
  -- cfpTerminalFrom cfpTerminal by uniqueness.
  have step3 :
      (cfpLift (cfpTerminalFrom cfpTerminal)
        (cfpLift p.ℓ p.ℓ) ≫
        cfpLiftAssoc treeNot treeNot) ≫
        cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [← Category.assoc, ← Category.assoc,
    step3, cfpTerminalFrom_terminal,
    Category.id_comp]

/-- Branch computation rule for `treeNotEndo`:
`β ≫ treeNotEndo = cfpTerminalFrom _ ≫ ℓ`.
Any branch node is sent to leaf. -/
theorem treeNotEndo_β :
    p.β ≫ treeNotEndo =
      cfpTerminalFrom (cfpProd p.T p.T) ≫
        p.ℓ := by
  unfold treeNotEndo
  have step1 : p.β ≫
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) =
      cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        p.β := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    exact h.terminal.uniq _
  rw [← Category.assoc, step1]
  -- Goal: cfpLift (cfpTerminalFrom (T×T)) β ≫
  --   treeNot = cfpTerminalFrom (T×T) ≫ ℓ
  -- Factor through cfpMap (𝟙 cfpTerminal) β
  have step2 :
      cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        p.β =
      cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    unfold cfpMap
    rw [cfpLift_precomp]
    congr 1
    · rw [← Category.assoc, cfpLift_fst,
        Category.comp_id]
    · rw [← Category.assoc, cfpLift_snd,
        Category.id_comp]
  rw [step2, Category.assoc, treeNot_β,
    ← Category.assoc, ← Category.assoc]
  have step3 :
      (cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpLiftAssoc treeNot treeNot) ≫
        cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom (cfpProd p.T p.T) :=
    h.terminal.uniq _
  rw [step3]

/-- Post-composing `treeAnd` with `treeNotEndo`:
`treeAnd ≫ treeNotEndo = elim treeNotEndo
  (cfpTerminalFrom _ ≫ ℓ)`.
The algebra morphism condition holds because
`β ≫ treeNotEndo = cfpTerminalFrom _ ≫ ℓ`. -/
theorem treeAnd_treeNotEndo :
    treeAnd ≫ treeNotEndo =
      p.elim treeNotEndo
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          p.ℓ) := by
  unfold treeAnd
  have step := elim_algebra_morphism
    (𝟙 p.T) p.β treeNotEndo
    (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ)
    (by
      rw [treeNotEndo_β, ← Category.assoc]
      congr 1
      exact h.terminal.uniq _)
  rw [Category.id_comp] at step
  exact step

/-- For a catamorphism with constant step function,
substituting `treeFalse` as the tree always returns
the constant. -/
theorem elim_const_step_treeFalse
    {A X : C} (f : A ⟶ X)
    (c : cfpTerminal ⟶ X) :
    cfpInsertSnd treeFalse A ≫
      p.elim f
        (cfpTerminalFrom (cfpProd X X) ≫ c) =
      cfpTerminalFrom A ≫ c := by
  have factor :
      cfpInsertSnd treeFalse A =
      cfpInsertSnd (cfpLift p.ℓ p.ℓ) A ≫
        cfpMap (𝟙 A) p.β := by
    unfold cfpInsertSnd
    rw [cfpLift_cfpMap, Category.id_comp]
    unfold treeFalse
    rw [Category.assoc]
  rw [factor, Category.assoc,
    p.elim_β,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- `treeOr(leaf, b) = leaf` for all `b`.
Leaf is the left absorbing element of `treeOr`. -/
theorem treeOr_leaf_left :
    cfpMap p.ℓ (𝟙 p.T) ≫ treeOr =
      cfpTerminalFrom (cfpProd cfpTerminal p.T) ≫
        p.ℓ := by
  unfold treeOr
  -- Step 1: Merge the cfpMap compositions.
  rw [← Category.assoc, cfpMap_comp,
    Category.id_comp, treeNotEndo_ℓ]
  -- Goal: cfpMap treeFalse treeNotEndo ≫
  --   treeAnd ≫ treeNotEndo =
  --   cfpTerminalFrom _ ≫ ℓ
  -- Step 2: Use treeAnd_treeNotEndo.
  rw [treeAnd_treeNotEndo]
  -- Goal: cfpMap treeFalse treeNotEndo ≫
  --   elim treeNotEndo (cfpTerminalFrom _ ≫ ℓ)
  --   = cfpTerminalFrom _ ≫ ℓ
  -- Both sides are the catamorphism
  -- elim ℓ (cfpTerminalFrom _ ≫ ℓ).
  -- First show the RHS equals this catamorphism:
  -- Step 3: Decompose cfpMap treeFalse treeNotEndo
  -- as cfpMap (𝟙) treeNotEndo ≫ cfpMap treeFalse (𝟙).
  have decomp :
      cfpMap treeFalse treeNotEndo =
      cfpMap (𝟙 cfpTerminal)
        treeNotEndo ≫
        cfpMap treeFalse (𝟙 p.T) := by
    rw [cfpMap_comp, Category.id_comp,
      Category.comp_id]
  rw [decomp, Category.assoc,
    elim_naturality, treeNotEndo_treeFalse]
  -- Goal: cfpMap (𝟙 cfpTerminal) treeNotEndo ≫
  --   elim ℓ (cfpTerminalFrom _ ≫ ℓ) =
  --   cfpTerminalFrom _ ≫ ℓ
  -- elim ℓ (cfpTerminalFrom _ ≫ ℓ) is constant ℓ,
  -- so precomposing doesn't change the result.
  -- Show elim ℓ g = cfpTerminalFrom _ ≫ ℓ first.
  have const_elim :
      p.elim p.ℓ
        (cfpTerminalFrom (cfpProd p.T p.T) ≫
          p.ℓ) =
      cfpTerminalFrom (cfpProd cfpTerminal p.T) ≫
        p.ℓ := by
    symm
    exact p.elim_uniq p.ℓ
      (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ)
      (cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ)
      (by
        have : cfpInsertSnd p.ℓ cfpTerminal ≫
            cfpTerminalFrom
              (cfpProd cfpTerminal p.T) =
            cfpTerminalFrom cfpTerminal :=
          h.terminal.uniq _
        rw [← Category.assoc, this,
          cfpTerminalFrom_terminal,
          Category.id_comp])
      (by
        have h1 :
            cfpMap (𝟙 cfpTerminal) p.β ≫
              cfpTerminalFrom
                (cfpProd cfpTerminal p.T) =
            cfpTerminalFrom
              (cfpProd cfpTerminal
                (cfpProd p.T p.T)) :=
          h.terminal.uniq _
        have h2 :
            cfpLiftAssoc
              (cfpTerminalFrom
                (cfpProd cfpTerminal p.T) ≫ p.ℓ)
              (cfpTerminalFrom
                (cfpProd cfpTerminal p.T) ≫
                p.ℓ) ≫
              cfpTerminalFrom
                (cfpProd p.T p.T) =
            cfpTerminalFrom
              (cfpProd cfpTerminal
                (cfpProd p.T p.T)) :=
          h.terminal.uniq _
        rw [← Category.assoc, ← Category.assoc,
          h2, h1])
  rw [const_elim, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- `treeOr(a, leaf) = leaf` for all `a`.
Leaf is the right absorbing element of `treeOr`. -/
theorem treeOr_leaf_right :
    cfpMap (𝟙 p.T) p.ℓ ≫ treeOr =
      cfpTerminalFrom (cfpProd p.T cfpTerminal) ≫
        p.ℓ := by
  unfold treeOr
  rw [← Category.assoc, cfpMap_comp,
    Category.id_comp, treeNotEndo_ℓ,
    treeAnd_treeNotEndo]
  -- Goal: cfpMap treeNotEndo treeFalse ≫
  --   elim treeNotEndo (cfpTerminalFrom _ ≫ ℓ)
  --   = cfpTerminalFrom _ ≫ ℓ
  -- Decompose and use elim_naturality.
  have decomp :
      cfpMap treeNotEndo treeFalse =
      cfpMap (𝟙 p.T) treeFalse ≫
        cfpMap treeNotEndo (𝟙 p.T) := by
    rw [cfpMap_comp, Category.id_comp,
      Category.comp_id]
  rw [decomp, Category.assoc,
    elim_naturality]
  -- Goal: cfpMap (𝟙 T) treeFalse ≫
  --   elim (treeNotEndo ≫ treeNotEndo)
  --     (cfpTerminalFrom _ ≫ ℓ)
  --   = cfpTerminalFrom _ ≫ ℓ
  -- cfpMap (𝟙 T) treeFalse substitutes treeFalse
  -- as the tree argument.
  -- Factor cfpMap (𝟙 T) treeFalse through
  -- cfpInsertSnd treeFalse T.
  have mapFactor :
      cfpMap (𝟙 p.T) treeFalse =
      cfpFst p.T cfpTerminal ≫
        cfpInsertSnd treeFalse p.T := by
    unfold cfpMap cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    congr 1
    have h1 : cfpFst p.T cfpTerminal ≫
        cfpTerminalFrom p.T =
        cfpTerminalFrom
          (cfpProd p.T cfpTerminal) :=
      h.terminal.uniq _
    have h2 : cfpSnd p.T cfpTerminal =
        cfpTerminalFrom
          (cfpProd p.T cfpTerminal) :=
      h.terminal.uniq _
    rw [h1, ← h2]
  rw [mapFactor, Category.assoc,
    elim_const_step_treeFalse,
    ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- Leaf computation rule for `treeImplies`:
`treeImplies(leaf, b) = treeNotEndo(treeNotEndo(b))`.
For Boolean-valued trees (leaf or treeFalse),
this reduces to the identity since `treeNotEndo`
is an involution on that subset. -/
theorem treeImplies_leaf_left :
    cfpMap p.ℓ (𝟙 p.T) ≫ treeImplies =
      cfpSnd cfpTerminal p.T ≫
        treeNotEndo ≫ treeNotEndo := by
  unfold treeImplies treeOr
  -- Merge the first two cfpMap compositions.
  rw [← Category.assoc
    (cfpMap p.ℓ (𝟙 p.T))
    (cfpMap treeNotEndo (𝟙 p.T)) _,
    cfpMap_comp, treeNotEndo_ℓ,
    Category.id_comp,
    ← Category.assoc, cfpMap_comp,
    Category.id_comp, treeNotEndo_treeFalse]
  -- Goal: cfpMap ℓ treeNotEndo ≫
  --   treeAnd ≫ treeNotEndo =
  --   cfpSnd ≫ treeNotEndo ≫ treeNotEndo
  -- Decompose cfpMap ℓ treeNotEndo.
  have decomp :
      cfpMap p.ℓ treeNotEndo =
      cfpMap (𝟙 cfpTerminal) treeNotEndo ≫
        cfpMap p.ℓ (𝟙 p.T) := by
    rw [cfpMap_comp, Category.id_comp,
      Category.comp_id]
  rw [decomp,
    Category.assoc
      (cfpMap (𝟙 cfpTerminal) treeNotEndo)
      (cfpMap p.ℓ (𝟙 p.T))
      (treeAnd ≫ treeNotEndo),
    ← Category.assoc
      (cfpMap p.ℓ (𝟙 p.T))
      treeAnd treeNotEndo,
    treeAnd_leaf_left,
    ← Category.assoc, cfpMap_snd,
    Category.assoc]

/-- Boolean biconditional on trees:
`treeIff(a, b) = treeAnd(treeImplies(a, b),
  treeImplies(b, a))`.
Correct when both inputs are Boolean-valued
(either leaf or `branch(leaf, leaf)`). -/
def treeIff : cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (treeImplies)
    (cfpLift (cfpSnd p.T p.T)
      (cfpFst p.T p.T) ≫
      treeImplies) ≫
    treeAnd

end GebLean
