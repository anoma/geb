import GebLean.EqualizerCompletionPBTO
import Mathlib.CategoryTheory.Generator.Basic

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
  rw [Category.assoc]
  have step1 : p.β ≫
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) =
      cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        p.β := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    exact h.terminal.uniq _
  rw [← Category.assoc p.β _ treeNot, step1]
  rw [← Category.assoc, cfpLift_precomp]
  have h2 : cfpLift p.ℓ p.ℓ ≫
      cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h2]
  change
    cfpLift (cfpTerminalFrom cfpTerminal)
      treeFalse ≫ treeNot = p.ℓ
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
  rw [← Category.assoc, cfpMap_comp,
    Category.id_comp, treeNotEndo_ℓ]
  rw [treeAnd_treeNotEndo]
  have decomp :
      cfpMap treeFalse treeNotEndo =
      cfpMap (𝟙 cfpTerminal)
        treeNotEndo ≫
        cfpMap treeFalse (𝟙 p.T) := by
    rw [cfpMap_comp, Category.id_comp,
      Category.comp_id]
  rw [decomp, Category.assoc,
    elim_naturality, treeNotEndo_treeFalse]
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
  have decomp :
      cfpMap treeNotEndo treeFalse =
      cfpMap (𝟙 p.T) treeFalse ≫
        cfpMap treeNotEndo (𝟙 p.T) := by
    rw [cfpMap_comp, Category.id_comp,
      Category.comp_id]
  rw [decomp, Category.assoc,
    elim_naturality]
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
  rw [← Category.assoc
    (cfpMap p.ℓ (𝟙 p.T))
    (cfpMap treeNotEndo (𝟙 p.T)) _,
    cfpMap_comp, treeNotEndo_ℓ,
    Category.id_comp,
    ← Category.assoc, cfpMap_comp,
    Category.id_comp, treeNotEndo_treeFalse]
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

/-- Associativity of `treeAnd` (grafting),
stated pointwise: for any `A B C : D ⟶ T`,
`treeAnd(treeAnd(A, B), C) =
  treeAnd(A, treeAnd(B, C))`.

Proof: the right side
`cfpLift A (cfpLift B C ≫ treeAnd) ≫ treeAnd`
equals `elim_naturality` applied to the inner
`treeAnd`, giving `cfpLift A ... ≫ elim A' β`.
The left side is shown to satisfy the same
computation rules via `elim_uniq`. -/
theorem treeAnd_assoc
    {D : C}
    (A B E : D ⟶ p.T) :
    cfpLift (cfpLift A B ≫ treeAnd) E ≫
      treeAnd =
    cfpLift A (cfpLift B E ≫ treeAnd) ≫
      treeAnd := by
  have cfpLift_treeAnd :
      ∀ (f g : D ⟶ p.T),
      cfpLift f g ≫ treeAnd =
      cfpLift (𝟙 D) g ≫ p.elim f p.β := by
    intro f g
    have h1 : cfpLift f g =
        cfpLift (𝟙 D) g ≫
          cfpMap f (𝟙 p.T) := by
      rw [cfpLift_cfpMap, Category.id_comp,
        Category.comp_id]
    rw [h1, Category.assoc]
    unfold treeAnd
    rw [elim_naturality, Category.comp_id]
  rw [cfpLift_treeAnd]
  have rhs_factor :
      cfpLift A (cfpLift B E ≫ treeAnd) ≫
        treeAnd =
      cfpLift (𝟙 D) E ≫
        (cfpLift (cfpFst D p.T ≫ A)
          (p.elim B p.β) ≫ treeAnd) := by
    rw [cfpLift_treeAnd B E]
    have h2 :
        cfpLift A
          (cfpLift (𝟙 D) E ≫
            p.elim B p.β) =
        cfpLift (𝟙 D) E ≫
          cfpLift (cfpFst D p.T ≫ A)
            (p.elim B p.β) := by
      rw [cfpLift_precomp]
      congr 1
      rw [← Category.assoc, cfpLift_fst,
        Category.id_comp]
    rw [h2, Category.assoc]
  rw [rhs_factor]
  congr 1
  symm
  exact p.elim_uniq
    (cfpLift A B ≫ treeAnd) p.β
    (cfpLift (cfpFst D p.T ≫ A)
      (p.elim B p.β) ≫ treeAnd)
    (by
      rw [← Category.assoc, cfpLift_precomp]
      have h1 : cfpInsertSnd p.ℓ D ≫
          cfpFst D p.T = 𝟙 D :=
        cfpLift_fst _ _
      rw [← Category.assoc, h1,
        Category.id_comp, p.elim_ℓ B p.β])
    (by
      rw [← Category.assoc, cfpLift_precomp]
      rw [← Category.assoc
        (cfpMap (𝟙 D) p.β)
        (cfpFst D p.T) A,
        cfpMap_fst (𝟙 D) p.β,
        Category.comp_id]
      rw [p.elim_β B p.β]
      have hfactor :
          cfpLift
            (cfpFst D (cfpProd p.T p.T) ≫ A)
            (cfpLiftAssoc (p.elim B p.β)
              (p.elim B p.β) ≫ p.β) =
          cfpLift
            (cfpFst D (cfpProd p.T p.T) ≫ A)
            (cfpLiftAssoc (p.elim B p.β)
              (p.elim B p.β)) ≫
            cfpMap (𝟙 p.T) p.β := by
        rw [cfpLift_cfpMap, Category.comp_id]
      rw [hfactor, Category.assoc, treeAnd_β,
        ← Category.assoc]
      congr 1
      rw [← cfpLiftAssoc_postcomp]
      have lhs_step :
          cfpLift
            (cfpFst D (cfpProd p.T p.T) ≫ A)
            (cfpLiftAssoc (p.elim B p.β)
              (p.elim B p.β)) ≫
            cfpLiftAssoc treeAnd treeAnd =
          cfpLift
            (cfpLift
              (cfpFst D (cfpProd p.T p.T) ≫ A)
              (cfpAssocFst D p.T p.T ≫
                p.elim B p.β) ≫ treeAnd)
            (cfpLift
              (cfpFst D (cfpProd p.T p.T) ≫ A)
              (cfpAssocSnd D p.T p.T ≫
                p.elim B p.β) ≫
              treeAnd) := by
        unfold cfpLiftAssoc
        rw [cfpLift_precomp]
        congr 1 <;>
          rw [← Category.assoc] <;>
          congr 1
        · apply cfpLift_uniq
          · rw [Category.assoc]
            unfold cfpAssocFst
            rw [← Category.assoc,
              cfpLift_precomp, cfpLift_fst]
            exact cfpLift_fst _ _
          · have : cfpAssocFst p.T p.T p.T ≫
                cfpSnd p.T p.T =
              cfpSnd p.T (cfpProd p.T p.T) ≫
                cfpFst p.T p.T := by
              unfold cfpAssocFst
              exact cfpLift_snd _ _
            rw [Category.assoc, this,
              ← Category.assoc, cfpLift_snd,
              cfpLift_fst]
        · have aFst : cfpAssocSnd p.T p.T p.T ≫
                cfpFst p.T p.T =
              cfpFst p.T (cfpProd p.T p.T) := by
              unfold cfpAssocSnd
              exact cfpLift_fst _ _
          have aSnd : cfpAssocSnd p.T p.T p.T ≫
                cfpSnd p.T p.T =
              cfpSnd p.T (cfpProd p.T p.T) ≫
                cfpSnd p.T p.T := by
              unfold cfpAssocSnd
              exact cfpLift_snd _ _
          apply cfpLift_uniq
          · rw [Category.assoc, aFst,
              cfpLift_fst]
          · rw [Category.assoc, aSnd,
              ← Category.assoc, cfpLift_snd,
              cfpLift_snd]
      have rhs_step :
          cfpLiftAssoc
            (cfpLift (cfpFst D p.T ≫ A)
              (p.elim B p.β))
            (cfpLift (cfpFst D p.T ≫ A)
              (p.elim B p.β)) ≫
            cfpMap treeAnd treeAnd =
          cfpLift
            (cfpLift
              (cfpFst D (cfpProd p.T p.T) ≫ A)
              (cfpAssocFst D p.T p.T ≫
                p.elim B p.β) ≫ treeAnd)
            (cfpLift
              (cfpFst D (cfpProd p.T p.T) ≫ A)
              (cfpAssocSnd D p.T p.T ≫
                p.elim B p.β) ≫
              treeAnd) := by
        unfold cfpLiftAssoc
        rw [cfpLift_cfpMap]
        congr 1 <;>
          rw [cfpLift_precomp] <;>
          congr 1
        · unfold cfpAssocFst
          rw [← Category.assoc, cfpLift_fst]
        · unfold cfpAssocSnd
          rw [← Category.assoc, cfpLift_fst]
      rw [lhs_step, rhs_step])

/-- Transitivity of `treeAnd`-implication:
if `treeAnd(A, B) = A` and
`treeAnd(B, C) = B`, then
`treeAnd(A, C) = A`.

This is the chain rule for the encoding of
implication as `treeAnd(a, b) = a`. -/
theorem treeAnd_implies_trans
    {D : C}
    {A B E : D ⟶ p.T}
    (hAB : cfpLift A B ≫ treeAnd = A)
    (hBE : cfpLift B E ≫ treeAnd = B) :
    cfpLift A E ≫ treeAnd = A := by
  calc cfpLift A E ≫ treeAnd
      = cfpLift (cfpLift A B ≫ treeAnd) E ≫
          treeAnd := by
        rw [hAB]
    _ = cfpLift A (cfpLift B E ≫ treeAnd) ≫
          treeAnd := treeAnd_assoc A B E
    _ = cfpLift A B ≫ treeAnd := by
        rw [hBE]
    _ = A := hAB

/-- Propositional conjunction on trees using
`treeIte`.  `propAnd(a, b)` returns `b` when
`a = leaf` (true) and returns `a` when
`a = branch(_, _)` (false).

The definition maps `(a, b)` to
`treeIte((b, a), a)`: the condition is `a`
(the first component), the "then" value
(returned when condition is leaf) is `b`
(the second component), and the "else" value
(returned when condition is non-leaf) is `a`
(the first component). -/
def propAnd :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (cfpLift (cfpSnd p.T p.T)
      (cfpFst p.T p.T))
    (cfpFst p.T p.T) ≫
    treeIte

/-- `propAnd(leaf, b) = b`.
When the first argument is leaf (true), propositional
conjunction returns the second argument. -/
theorem propAnd_leaf_left :
    cfpMap p.ℓ (𝟙 p.T) ≫ propAnd =
      cfpSnd cfpTerminal p.T := by
  unfold propAnd
  rw [← Category.assoc, cfpLift_precomp]
  have h1 :
      cfpMap p.ℓ (𝟙 p.T) ≫
        cfpLift (cfpSnd p.T p.T)
          (cfpFst p.T p.T) =
      cfpLift (cfpSnd cfpTerminal p.T)
        (cfpFst cfpTerminal p.T ≫ p.ℓ) := by
    rw [cfpLift_precomp, cfpMap_snd,
      Category.comp_id, cfpMap_fst]
  have h2 :
      cfpMap p.ℓ (𝟙 p.T) ≫
        cfpFst p.T p.T =
      cfpFst cfpTerminal p.T ≫ p.ℓ := by
    rw [cfpMap_fst]
  rw [h1, h2]
  have hterm :
      cfpFst cfpTerminal p.T =
      cfpTerminalFrom
        (cfpProd cfpTerminal p.T) :=
    h.terminal.uniq _
  rw [hterm]
  set P := cfpLift (cfpSnd cfpTerminal p.T)
    (cfpTerminalFrom
      (cfpProd cfpTerminal p.T) ≫ p.ℓ)
    with hP
  set c := cfpTerminalFrom
    (cfpProd cfpTerminal p.T) ≫ p.ℓ
    with hc
  have factor : cfpLift P c =
      P ≫ cfpInsertSnd p.ℓ
        (cfpProd p.T p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    have hPterm :
        P ≫ cfpTerminalFrom
          (cfpProd p.T p.T) =
        cfpTerminalFrom
          (cfpProd cfpTerminal p.T) :=
      h.terminal.uniq _
    rw [← Category.assoc, hPterm]
  rw [factor, Category.assoc, treeIte_ℓ,
    cfpLift_fst]

/-- When both branches of `treeIte` are equal,
the result is that common value regardless of
the condition.

`treeIte((f, f), g) = f` for any
`f g : D ⟶ T`. -/
theorem treeIte_equal_branches
    {D : C}
    (f g : D ⟶ p.T) :
    cfpLift (cfpLift f f) g ≫ treeIte = f := by
  unfold treeIte
  have factor :
      cfpLift (cfpLift f f) g =
      cfpLift (𝟙 D) g ≫
        cfpMap (cfpLift f f) (𝟙 p.T) := by
    rw [cfpLift_cfpMap, Category.id_comp,
      Category.comp_id]
  rw [factor, Category.assoc, ← Category.assoc
    (cfpMap (cfpLift f f) (𝟙 p.T))
    iteFold (cfpFst p.T p.T)]
  unfold iteFold
  rw [elim_naturality, Category.comp_id]
  set step :=
    cfpLift
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T)
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T)
    with hstep
  have elim_eq :
      p.elim (cfpLift f f) step =
      cfpLift (cfpFst D p.T ≫ f)
        (cfpFst D p.T ≫ f) := by
    symm
    exact p.elim_uniq (cfpLift f f) step
      (cfpLift (cfpFst D p.T ≫ f)
        (cfpFst D p.T ≫ f))
      (by
        have hbase :
            cfpInsertSnd p.ℓ D ≫
              cfpFst D p.T = 𝟙 D := by
          unfold cfpInsertSnd
          exact cfpLift_fst _ _
        rw [cfpLift_precomp
          (cfpInsertSnd p.ℓ D)
          (cfpFst D p.T ≫ f)
          (cfpFst D p.T ≫ f)]
        rw [← Category.assoc, hbase,
          Category.id_comp])
      (by
        have hq :
            cfpLift (cfpFst D p.T ≫ f)
              (cfpFst D p.T ≫ f) =
            cfpFst D p.T ≫ cfpLift f f := by
          rw [cfpLift_precomp]
        have lhs :
            cfpMap (𝟙 D) p.β ≫
              cfpLift (cfpFst D p.T ≫ f)
                (cfpFst D p.T ≫ f) =
            cfpFst D (cfpProd p.T p.T) ≫
              cfpLift f f := by
          rw [hq, ← Category.assoc,
            cfpMap_fst, Category.comp_id]
        have rhs :
            cfpLiftAssoc
              (cfpLift (cfpFst D p.T ≫ f)
                (cfpFst D p.T ≫ f))
              (cfpLift (cfpFst D p.T ≫ f)
                (cfpFst D p.T ≫ f)) ≫
              step =
            cfpFst D (cfpProd p.T p.T) ≫
              cfpLift f f := by
          rw [hstep, cfpLift_precomp]
          have comp1 :
              cfpLiftAssoc
                (cfpLift (cfpFst D p.T ≫ f)
                  (cfpFst D p.T ≫ f))
                (cfpLift (cfpFst D p.T ≫ f)
                  (cfpFst D p.T ≫ f)) ≫
              cfpFst (cfpProd p.T p.T)
                (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T =
            cfpFst D (cfpProd p.T p.T) ≫
              f := by
            unfold cfpLiftAssoc
            rw [← Category.assoc,
              cfpLift_fst, hq]
            rw [Category.assoc, Category.assoc,
              cfpLift_snd]
            unfold cfpAssocFst
            rw [← Category.assoc,
              cfpLift_fst]
          rw [comp1, cfpLift_precomp]
        rw [lhs, rhs])
  rw [elim_eq, cfpLift_fst,
    ← Category.assoc, cfpLift_fst,
    Category.id_comp]

/-- `propAnd(a, a) = a`.
Propositional conjunction is idempotent. -/
theorem propAnd_idem :
    cfpLift (𝟙 p.T) (𝟙 p.T) ≫ propAnd =
      𝟙 p.T := by
  unfold propAnd
  rw [← Category.assoc, cfpLift_precomp]
  have h1 :
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        cfpLift (cfpSnd p.T p.T)
          (cfpFst p.T p.T) =
      cfpLift (𝟙 p.T) (𝟙 p.T) := by
    rw [cfpLift_precomp, cfpLift_snd,
      cfpLift_fst]
  have h2 :
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        cfpFst p.T p.T = 𝟙 p.T :=
    cfpLift_fst _ _
  rw [h1, h2]
  exact treeIte_equal_branches (𝟙 p.T) (𝟙 p.T)

/-- Pre-composition distributes into `propAnd`:
`e ≫ cfpLift f g ≫ propAnd =
  cfpLift (e ≫ f) (e ≫ g) ≫ propAnd`.
This follows directly from `cfpLift_precomp`. -/
theorem propAnd_precomp
    {D E : C}
    (e : E ⟶ D)
    (f g : D ⟶ p.T) :
    e ≫ cfpLift f g ≫ propAnd =
      cfpLift (e ≫ f) (e ≫ g) ≫ propAnd := by
  rw [← Category.assoc, cfpLift_precomp]

/-- A morphism `f : D ⟶ T` is "leaf-constant"
when it equals the constant leaf morphism.
This encodes "for all inputs, the result is
leaf (true)." -/
def IsLeafConst
    {D : C} (f : D ⟶ p.T) : Prop :=
  f = cfpTerminalFrom D ≫ p.ℓ

/-- Conversion from `propAnd`-implication
(equational) to `IsLeafConst`-implication
(Prop-valued): if `propAnd(A, B) = A` then
for any `e : E ⟶ D`, `A(e) = leaf` implies
`B(e) = leaf`. -/
theorem propAnd_implies_IsLeafConst
    {D : C}
    {A B : D ⟶ p.T}
    (h : cfpLift A B ≫ propAnd = A)
    {E : C}
    (e : E ⟶ D)
    (hA : IsLeafConst (e ≫ A)) :
    IsLeafConst (e ≫ B) := by
  unfold IsLeafConst at hA ⊢
  have h1 : cfpLift (e ≫ A) (e ≫ B) ≫
      propAnd = e ≫ A := by
    rw [← propAnd_precomp, h]
  rw [hA] at h1
  have factor :
      cfpLift (cfpTerminalFrom E ≫ p.ℓ)
        (e ≫ B) =
      cfpLift (cfpTerminalFrom E) (e ≫ B) ≫
        cfpMap p.ℓ (𝟙 p.T) := by
    rw [cfpLift_cfpMap, Category.comp_id]
  rw [factor, Category.assoc,
    propAnd_leaf_left] at h1
  rw [cfpLift_snd] at h1
  exact h1

/-- Leaf detection as an endomorphism on T:
returns `leaf` when the input is leaf, `treeFalse`
when the input is non-leaf. -/
def isLeafEndo : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    isLeaf

/-- `ℓ ≫ isLeafEndo = ℓ`:
leaf is a fixed point of `isLeafEndo`. -/
theorem isLeafEndo_ℓ :
    p.ℓ ≫ isLeafEndo = p.ℓ := by
  unfold isLeafEndo
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
  exact isLeaf_ℓ

/-- `treeFalse ≫ isLeafEndo = treeFalse`:
`treeFalse` is a fixed point of `isLeafEndo`. -/
theorem isLeafEndo_treeFalse :
    treeFalse ≫ isLeafEndo =
      (treeFalse : cfpTerminal (C := C) ⟶ _) := by
  unfold isLeafEndo treeFalse
  rw [Category.assoc]
  have step1 : p.β ≫
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) =
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        p.β := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    exact h.terminal.uniq _
  rw [← Category.assoc p.β _ isLeaf, step1]
  rw [← Category.assoc, cfpLift_precomp]
  have h2 : cfpLift p.ℓ p.ℓ ≫
      cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h2]
  change
    cfpLift (cfpTerminalFrom cfpTerminal)
      treeFalse ≫ isLeaf =
    treeFalse
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
  rw [step2, Category.assoc, isLeaf_β]
  have step3 :
      (cfpLift (cfpTerminalFrom cfpTerminal)
        (cfpLift p.ℓ p.ℓ) ≫
        cfpLiftAssoc isLeaf isLeaf) ≫
        cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [← Category.assoc, ← Category.assoc,
    step3, cfpTerminalFrom_terminal,
    Category.id_comp]

/-- Branch computation rule for `isLeafEndo`:
any branch node maps to `treeFalse`. -/
theorem isLeafEndo_β :
    p.β ≫ isLeafEndo =
      cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse := by
  unfold isLeafEndo
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have h1 : p.β ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom (cfpProd p.T p.T) :=
    h.terminal.uniq _
  rw [h1]
  have factor :
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        p.β =
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    unfold cfpMap
    rw [cfpLift_precomp]
    congr 1
    · rw [← Category.assoc, cfpLift_fst,
        Category.comp_id]
    · rw [← Category.assoc, cfpLift_snd,
        Category.id_comp]
  rw [factor, Category.assoc, isLeaf_β,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- Applying `isLeaf` after `isLeafEndo` equals
`isLeaf`: the output of `isLeaf` is always either
leaf or treeFalse, both of which are fixed points
of `isLeafEndo`. -/
theorem isLeaf_isLeafEndo :
    isLeaf ≫ isLeafEndo =
      (isLeaf :
        cfpProd cfpTerminal p.T ⟶ p.T) := by
  set step :=
    cfpTerminalFrom (cfpProd p.T p.T) ≫ treeFalse
    with hstep
  have alg : cfpMap isLeafEndo isLeafEndo ≫
      step = step ≫ isLeafEndo := by
    have h1 :
        cfpMap isLeafEndo isLeafEndo ≫ step =
        cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse := by
      rw [← Category.assoc]
      congr 1
      exact h.terminal.uniq _
    have h2 : step ≫ isLeafEndo =
        cfpTerminalFrom (cfpProd p.T p.T) ≫
          treeFalse := by
      rw [hstep, Category.assoc,
        isLeafEndo_treeFalse]
    rw [h1, h2]
  have main :=
    elim_algebra_morphism p.ℓ step isLeafEndo
      step alg
  rw [isLeafEndo_ℓ] at main
  unfold isLeaf
  exact main

/-- `isLeafEndo` is idempotent:
`isLeafEndo ≫ isLeafEndo = isLeafEndo`. -/
theorem isLeafEndo_idem :
    isLeafEndo ≫ isLeafEndo =
      (isLeafEndo : p.T ⟶ p.T) := by
  have : isLeafEndo ≫ isLeafEndo =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        (isLeaf ≫ isLeafEndo) := by
    unfold isLeafEndo
    simp only [Category.assoc]
  rw [this, isLeaf_isLeafEndo]; rfl

/-- Boolean conjunction: returns `leaf` when both
inputs are leaf, and `treeFalse` otherwise.
Defined as `boolAnd(a, b) =
  treeIte((isLeafEndo(b), treeFalse), a)`:
a case split on whether `a` is leaf (returning
`isLeafEndo(b)`) or non-leaf (returning
`treeFalse`). -/
def boolAnd :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (cfpSnd p.T p.T ≫ isLeafEndo)
      (cfpFst p.T p.T ≫
        cfpTerminalFrom p.T ≫ treeFalse))
    (cfpFst p.T p.T) ≫
    treeIte

/-- Boolean disjunction:
`boolOr(a, b) = treeIte((leaf_const,
  isLeafEndo(b)), a)`.
Returns `leaf` when either input is leaf, and
`treeFalse` otherwise. -/
def boolOr :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (cfpFst p.T p.T ≫
        cfpTerminalFrom p.T ≫ p.ℓ)
      (cfpSnd p.T p.T ≫ isLeafEndo))
    (cfpFst p.T p.T) ≫
    treeIte

/-- Boolean implication:
`boolImplies(a, b) = treeIte((isLeafEndo(b),
  leaf_const), a)`.
Returns `treeFalse` only when the first input is
leaf and the second is non-leaf; returns `leaf`
otherwise. -/
def boolImplies :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (cfpSnd p.T p.T ≫ isLeafEndo)
      (cfpFst p.T p.T ≫
        cfpTerminalFrom p.T ≫ p.ℓ))
    (cfpFst p.T p.T) ≫
    treeIte

/-- `boolAnd(leaf, b) = isLeafEndo(b)`:
when the first argument is leaf, the result
is the Boolean normalization of the second. -/
theorem boolAnd_leaf_left :
    cfpMap p.ℓ (𝟙 p.T) ≫ boolAnd =
      cfpSnd cfpTerminal p.T ≫
        isLeafEndo := by
  unfold boolAnd
  rw [← Category.assoc, cfpLift_precomp]
  have h1 :
      cfpMap p.ℓ (𝟙 p.T) ≫
        cfpLift
          (cfpSnd p.T p.T ≫ isLeafEndo)
          (cfpFst p.T p.T ≫
            cfpTerminalFrom p.T ≫ treeFalse) =
      cfpLift
        (cfpSnd cfpTerminal p.T ≫ isLeafEndo)
        (cfpTerminalFrom
          (cfpProd cfpTerminal p.T) ≫
          treeFalse) := by
    rw [cfpLift_precomp]
    congr 1
    · rw [← Category.assoc, cfpMap_snd,
        Category.comp_id]
    · have :
          (cfpFst cfpTerminal p.T ≫ p.ℓ) ≫
            cfpTerminalFrom p.T ≫ treeFalse =
          cfpTerminalFrom
            (cfpProd cfpTerminal p.T) ≫
            treeFalse := by
        rw [← Category.assoc]
        congr 1
        exact h.terminal.uniq _
      rw [← Category.assoc, cfpMap_fst]
      exact this
  have h2 :
      cfpMap p.ℓ (𝟙 p.T) ≫
        cfpFst p.T p.T =
      cfpFst cfpTerminal p.T ≫ p.ℓ := by
    rw [cfpMap_fst]
  rw [h1, h2]
  have hterm :
      cfpFst cfpTerminal p.T =
      cfpTerminalFrom
        (cfpProd cfpTerminal p.T) :=
    h.terminal.uniq _
  rw [hterm]
  set P := cfpLift
    (cfpSnd cfpTerminal p.T ≫ isLeafEndo)
    (cfpTerminalFrom (cfpProd cfpTerminal p.T)
      ≫ treeFalse)
    with hP
  set c := cfpTerminalFrom
    (cfpProd cfpTerminal p.T) ≫ p.ℓ
    with hc
  have factor : cfpLift P c =
      P ≫ cfpInsertSnd p.ℓ
        (cfpProd p.T p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    have hPterm :
        P ≫ cfpTerminalFrom
          (cfpProd p.T p.T) =
        cfpTerminalFrom
          (cfpProd cfpTerminal p.T) :=
      h.terminal.uniq _
    rw [← Category.assoc, hPterm]
  rw [factor, Category.assoc, treeIte_ℓ,
    cfpLift_fst]

/-- Evaluating `treeIte` at `treeFalse` (a branch
node) as the condition returns the second ("else")
component of the parameter pair. -/
theorem treeIte_treeFalse :
    cfpInsertSnd treeFalse (cfpProd p.T p.T) ≫
      treeIte = cfpSnd p.T p.T := by
  have factor :
      cfpInsertSnd treeFalse
        (cfpProd p.T p.T) =
      cfpInsertSnd (cfpLift p.ℓ p.ℓ)
        (cfpProd p.T p.T) ≫
        cfpMap (𝟙 (cfpProd p.T p.T)) p.β := by
    unfold cfpInsertSnd
    rw [cfpLift_cfpMap, Category.id_comp]
    unfold treeFalse
    rw [Category.assoc]
  rw [factor, Category.assoc, treeIte_β,
    ← Category.assoc, ← Category.assoc]
  have h1 :
      cfpInsertSnd (cfpLift p.ℓ p.ℓ)
        (cfpProd p.T p.T) ≫
        cfpLiftAssoc iteFold iteFold =
      cfpLift
        (cfpInsertSnd (cfpLift p.ℓ p.ℓ)
          (cfpProd p.T p.T) ≫
          cfpAssocFst (cfpProd p.T p.T)
            p.T p.T ≫
          iteFold)
        (cfpInsertSnd (cfpLift p.ℓ p.ℓ)
          (cfpProd p.T p.T) ≫
          cfpAssocSnd (cfpProd p.T p.T)
            p.T p.T ≫
          iteFold) := by
    unfold cfpLiftAssoc
    rw [cfpLift_precomp]
  have assocFst_eq :
      cfpInsertSnd (cfpLift p.ℓ p.ℓ)
        (cfpProd p.T p.T) ≫
        cfpAssocFst (cfpProd p.T p.T)
          p.T p.T =
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) := by
    unfold cfpAssocFst
    unfold cfpInsertSnd
    rw [cfpLift_precomp, cfpLift_fst]
    congr 1
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc, cfpLift_fst]
  have assocSnd_eq :
      cfpInsertSnd (cfpLift p.ℓ p.ℓ)
        (cfpProd p.T p.T) ≫
        cfpAssocSnd (cfpProd p.T p.T)
          p.T p.T =
      cfpInsertSnd p.ℓ (cfpProd p.T p.T) := by
    unfold cfpAssocSnd
    unfold cfpInsertSnd
    rw [cfpLift_precomp, cfpLift_fst]
    congr 1
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc, cfpLift_snd]
  have fst_simp :
      cfpInsertSnd (cfpLift p.ℓ p.ℓ)
        (cfpProd p.T p.T) ≫
        cfpAssocFst (cfpProd p.T p.T)
          p.T p.T ≫
        iteFold =
      𝟙 (cfpProd p.T p.T) := by
    rw [← Category.assoc, assocFst_eq,
      iteFold_ℓ]
  have snd_simp :
      cfpInsertSnd (cfpLift p.ℓ p.ℓ)
        (cfpProd p.T p.T) ≫
        cfpAssocSnd (cfpProd p.T p.T)
          p.T p.T ≫
        iteFold =
      𝟙 (cfpProd p.T p.T) := by
    rw [← Category.assoc, assocSnd_eq,
      iteFold_ℓ]
  rw [h1, fst_simp, snd_simp,
    cfpLift_fst, Category.id_comp]

/-- When both branches of a `treeIte` are fixed
points of `isLeafEndo`, the output of `treeIte`
is also a fixed point, so post-composing with
`isLeafEndo` has no effect. -/
theorem treeIte_isLeafEndo_stable
    {D : C}
    (f g : D ⟶ p.T)
    (c : D ⟶ p.T)
    (hf : f ≫ isLeafEndo = f)
    (hg : g ≫ isLeafEndo = g) :
    cfpLift (cfpLift f g) c ≫
      treeIte ≫ isLeafEndo =
    cfpLift (cfpLift f g) c ≫ treeIte := by
  -- Factor the pre-composition through cfpMap.
  have factor :
      cfpLift (cfpLift f g) c =
      cfpLift (𝟙 D) c ≫
        cfpMap (cfpLift f g) (𝟙 p.T) := by
    rw [cfpLift_cfpMap, Category.id_comp,
      Category.comp_id]
  -- Reduce to showing the fold output
  -- is isLeafEndo-stable.
  rw [factor]
  unfold treeIte iteFold
  simp only [Category.assoc]
  set step :=
    cfpLift
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T)
      (cfpFst (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T)
    with hstep
  -- Absorb cfpMap into the fold base case
  -- on both sides using elim_naturality.
  have nat :
      cfpMap (cfpLift f g) (𝟙 p.T) ≫
        p.elim (𝟙 (cfpProd p.T p.T)) step =
      p.elim (cfpLift f g) step := by
    rw [elim_naturality, Category.comp_id]
  rw [← Category.assoc
    (cfpMap (cfpLift f g) (𝟙 p.T))
    (p.elim (𝟙 (cfpProd p.T p.T)) step)
    (cfpFst p.T p.T ≫ isLeafEndo),
    nat,
    ← Category.assoc
    (cfpMap (cfpLift f g) (𝟙 p.T))
    (p.elim (𝟙 (cfpProd p.T p.T)) step)
    (cfpFst p.T p.T),
    nat]
  -- Rewrite cfpFst ≫ isLeafEndo to
  -- cfpMap isLeafEndo isLeafEndo ≫ cfpFst.
  rw [← cfpMap_fst
    (isLeafEndo : p.T ⟶ p.T)
    (isLeafEndo : p.T ⟶ p.T)]
  -- The algebra morphism condition.
  have alg :
      cfpMap (cfpMap isLeafEndo isLeafEndo)
        (cfpMap isLeafEndo isLeafEndo) ≫
        step = step ≫
        cfpMap isLeafEndo isLeafEndo := by
    rw [hstep]
    rw [cfpLift_precomp, cfpLift_cfpMap]
    congr 1 <;> (
      rw [← Category.assoc,
        cfpMap_fst, Category.assoc,
        cfpMap_snd]
      simp only [Category.assoc])
  rw [← Category.assoc
    (p.elim (cfpLift f g) step)
    (cfpMap isLeafEndo isLeafEndo)
    (cfpFst p.T p.T),
    elim_algebra_morphism (cfpLift f g)
      step (cfpMap isLeafEndo isLeafEndo)
      step alg,
    cfpLift_cfpMap, hf, hg]

/-- `boolAnd(leaf, leaf) = leaf`. -/
theorem boolAnd_ℓ_ℓ :
    cfpLift p.ℓ p.ℓ ≫ boolAnd = p.ℓ := by
  have factor :
      cfpLift p.ℓ p.ℓ =
      cfpLift (cfpTerminalFrom cfpTerminal) p.ℓ
        ≫ cfpMap p.ℓ (𝟙 p.T) := by
    rw [cfpLift_cfpMap, Category.comp_id,
      cfpTerminalFrom_terminal,
      Category.id_comp]
  rw [factor, Category.assoc,
    boolAnd_leaf_left, ← Category.assoc,
    cfpLift_snd, isLeafEndo_ℓ]

/-- The output of `boolAnd` is always Boolean:
`boolAnd ≫ isLeafEndo = boolAnd`. -/
theorem boolAnd_output_boolean :
    boolAnd ≫ isLeafEndo =
      (boolAnd : cfpProd p.T p.T ⟶ p.T) := by
  unfold boolAnd
  rw [Category.assoc, treeIte_isLeafEndo_stable]
  · rw [Category.assoc,
      @isLeafEndo_idem C _ h p]
  · rw [Category.assoc, Category.assoc,
      isLeafEndo_treeFalse]

/-- From `boolAnd(A, B) = A`, derive that `A`
is Boolean: `A ≫ isLeafEndo = A`. -/
theorem boolAnd_hyp_boolean
    {D : C}
    {A B : D ⟶ p.T}
    (hAB : cfpLift A B ≫ boolAnd = A) :
    A ≫ isLeafEndo = A := by
  calc A ≫ isLeafEndo
      = cfpLift A B ≫ boolAnd ≫ isLeafEndo := by
        rw [← Category.assoc, hAB]
    _ = cfpLift A B ≫ boolAnd := by
        rw [boolAnd_output_boolean]
    _ = A := hAB

/-- Rewrite of `boolAnd` applied to specific
morphisms in terms of `treeIte`: the condition
is the first argument, the "then" branch is
`isLeafEndo` of the second, and the "else" branch
is the constant `treeFalse`. -/
theorem boolAnd_treeIte_form
    {D : C}
    (A B : D ⟶ p.T) :
    cfpLift A B ≫ boolAnd =
    cfpLift
      (cfpLift (B ≫ isLeafEndo)
        (cfpTerminalFrom D ≫ treeFalse))
      A ≫ treeIte := by
  unfold boolAnd
  rw [← Category.assoc, cfpLift_precomp]
  have inner :
      cfpLift A B ≫
        cfpLift
          (cfpSnd p.T p.T ≫ isLeafEndo)
          (cfpFst p.T p.T ≫
            cfpTerminalFrom p.T ≫
            treeFalse) =
      cfpLift (B ≫ isLeafEndo)
        (A ≫ cfpTerminalFrom p.T ≫
          treeFalse) := by
    rw [cfpLift_precomp]
    congr 1
    · rw [← Category.assoc, cfpLift_snd]
    · rw [← Category.assoc, cfpLift_fst]
  have hfst :
      cfpLift A B ≫ cfpFst p.T p.T = A :=
    cfpLift_fst A B
  have hterm :
      A ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom D :=
    h.terminal.uniq _
  rw [inner, hfst]
  congr 2
  rw [← Category.assoc, hterm]

/-- Evaluating `treeIte` with `treeFalse` as the
condition and specific morphisms as branches:
`treeIte((X, Y), treeFalse) = Y`. -/
theorem treeIte_treeFalse_applied
    {D : C}
    (X Y : D ⟶ p.T) :
    cfpLift (cfpLift X Y)
      (cfpTerminalFrom D ≫ treeFalse) ≫
      treeIte = Y := by
  have factor :
      cfpLift (cfpLift X Y)
        (cfpTerminalFrom D ≫ treeFalse) =
      cfpLift X Y ≫
        cfpInsertSnd treeFalse
          (cfpProd p.T p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm
  rw [factor, Category.assoc,
    treeIte_treeFalse, cfpLift_snd]

/-- `iteFold ≫ cfpSnd T T` equals the constant
"else" projection: folding any tree returns the
second component (the "else" branch) as its own
second component. -/
theorem iteFold_snd :
    (iteFold :
      cfpProd (cfpProd p.T p.T) p.T ⟶
        cfpProd p.T p.T) ≫
      cfpSnd p.T p.T =
    cfpFst (cfpProd p.T p.T) p.T ≫
      cfpSnd p.T p.T := by
  have lhs :
      iteFold ≫ cfpSnd p.T p.T =
      p.elim (cfpSnd p.T p.T)
        (cfpFst p.T p.T) :=
    p.elim_uniq (cfpSnd p.T p.T)
      (cfpFst p.T p.T)
      (iteFold ≫ cfpSnd p.T p.T)
      (by
        rw [← Category.assoc, iteFold_ℓ,
          Category.id_comp])
      (by
        rw [← Category.assoc, iteFold_β,
          Category.assoc, cfpLift_snd]
        rw [← cfpMap_fst
          (cfpSnd p.T p.T)
          (cfpSnd p.T p.T)]
        rw [← Category.assoc,
          ← cfpLiftAssoc_postcomp])
  have rhs :
      cfpFst (cfpProd p.T p.T) p.T ≫
        cfpSnd p.T p.T =
      p.elim (cfpSnd p.T p.T)
        (cfpFst p.T p.T) :=
    p.elim_uniq (cfpSnd p.T p.T)
      (cfpFst p.T p.T)
      (cfpFst (cfpProd p.T p.T) p.T ≫
        cfpSnd p.T p.T)
      (by
        rw [← Category.assoc]
        unfold cfpInsertSnd
        rw [cfpLift_fst, Category.id_comp])
      (by
        rw [← Category.assoc,
          cfpMap_fst (𝟙 _) p.β,
          Category.comp_id]
        symm
        unfold cfpLiftAssoc
        rw [cfpLift_fst,
          ← Category.assoc]
        unfold cfpAssocFst
        rw [cfpLift_fst])
  rw [lhs, ← rhs]

/-- At `treeFalse`, `iteFold` returns the pair
`(cfpSnd, cfpSnd)`, duplicating the "else" value.
-/
theorem iteFold_treeFalse :
    cfpInsertSnd treeFalse (cfpProd p.T p.T) ≫
      iteFold =
    cfpLift (cfpSnd p.T p.T)
      (cfpSnd p.T p.T) := by
  apply cfpLift_uniq
  · -- cfpFst projection: treeIte at treeFalse
    have h1 := @treeIte_treeFalse C _ h p
    unfold treeIte at h1
    simp only [Category.assoc] at h1 ⊢
    exact h1
  · -- cfpSnd projection: by iteFold_snd
    rw [Category.assoc, iteFold_snd,
      ← Category.assoc]
    unfold cfpInsertSnd
    rw [cfpLift_fst, Category.id_comp]

/-- Pre-composing the condition of `iteFold`
with `isLeafEndo` has no effect:
`cfpMap (𝟙 (T×T)) isLeafEndo ≫ iteFold
  = iteFold`. -/
theorem iteFold_isLeafEndo :
    cfpMap (𝟙 (cfpProd p.T p.T)) isLeafEndo ≫
      iteFold =
    (iteFold :
      cfpProd (cfpProd p.T p.T) p.T ⟶
        cfpProd p.T p.T) := by
  set A := cfpProd p.T p.T with hA
  set step :=
    cfpLift
      (cfpFst A A ≫ cfpSnd p.T p.T)
      (cfpFst A A ≫ cfpSnd p.T p.T)
    with hstep
  exact p.elim_uniq (𝟙 A) step
    (cfpMap (𝟙 A) isLeafEndo ≫ iteFold)
    (by
      rw [← Category.assoc]
      have : cfpInsertSnd p.ℓ A ≫
          cfpMap (𝟙 A) isLeafEndo =
          cfpInsertSnd (p.ℓ ≫ isLeafEndo) A := by
        unfold cfpInsertSnd
        rw [cfpLift_cfpMap, Category.id_comp,
          Category.assoc]
      rw [this, isLeafEndo_ℓ, iteFold_ℓ])
    (by
      -- LHS: cfpMap (𝟙 A) β ≫
      --   cfpMap (𝟙 A) isLeafEndo ≫ iteFold
      -- = cfpMap (𝟙 A)
      --     (β ≫ isLeafEndo) ≫ iteFold
      -- = cfpMap (𝟙 A)
      --     (cfpTerminalFrom (T×T) ≫ treeFalse)
      --   ≫ iteFold
      rw [← Category.assoc, cfpMap_comp,
        Category.id_comp,
        @isLeafEndo_β C _ h p]
      -- Show cfpMap (𝟙 A)
      --   (cfpTerminalFrom (T×T) ≫ treeFalse)
      --   ≫ iteFold
      -- = cfpLiftAssoc (...) (...) ≫ step
      -- Both sides equal cfpLift
      --   (cfpFst A (T×T) ≫ cfpSnd T T)
      --   (cfpFst A (T×T) ≫ cfpSnd T T)
      -- LHS: factor through cfpFst ≫ iteFold_treeFalse
      have lhs_eq :
          cfpMap (𝟙 A)
            (cfpTerminalFrom (cfpProd p.T p.T)
              ≫ treeFalse) ≫
            iteFold =
          cfpLift (cfpFst A (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T)
            (cfpFst A (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) := by
        have factor :
            cfpMap (𝟙 A)
              (cfpTerminalFrom
                (cfpProd p.T p.T) ≫
                treeFalse) =
            cfpFst A (cfpProd p.T p.T) ≫
              cfpInsertSnd treeFalse A := by
          unfold cfpMap cfpInsertSnd
          rw [cfpLift_precomp,
            Category.comp_id]
          congr 1
          rw [← Category.assoc,
            ← Category.assoc]
          congr 1
          have h1 : cfpSnd A
              (cfpProd p.T p.T) ≫
              cfpTerminalFrom
                (cfpProd p.T p.T) =
            cfpTerminalFrom
              (cfpProd A
                (cfpProd p.T p.T)) :=
            h.terminal.uniq _
          have h2 : cfpFst A
              (cfpProd p.T p.T) ≫
              cfpTerminalFrom A =
            cfpTerminalFrom
              (cfpProd A
                (cfpProd p.T p.T)) :=
            h.terminal.uniq _
          rw [h1, h2]
        rw [factor, Category.assoc,
          iteFold_treeFalse, cfpLift_precomp]
      -- RHS: unfold cfpLiftAssoc and step
      have rhs_eq :
          cfpLiftAssoc
            (cfpMap (𝟙 A) isLeafEndo ≫
              iteFold)
            (cfpMap (𝟙 A) isLeafEndo ≫
              iteFold) ≫ step =
          cfpLift (cfpFst A (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T)
            (cfpFst A (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T) := by
        rw [hstep, cfpLift_precomp]
        unfold cfpLiftAssoc
        have simplify :
            cfpAssocFst A p.T p.T ≫
              cfpMap (𝟙 A) isLeafEndo ≫
              cfpFst A p.T ≫
              cfpSnd p.T p.T =
            cfpFst A (cfpProd p.T p.T) ≫
              cfpSnd p.T p.T := by
          calc cfpAssocFst A p.T p.T ≫
                cfpMap (𝟙 A) isLeafEndo ≫
                cfpFst A p.T ≫
                cfpSnd p.T p.T
              = cfpAssocFst A p.T p.T ≫
                  (cfpMap (𝟙 A) isLeafEndo ≫
                    cfpFst A p.T) ≫
                  cfpSnd p.T p.T := by
                simp only [Category.assoc]
            _ = cfpAssocFst A p.T p.T ≫
                  cfpFst A p.T ≫
                  cfpSnd p.T p.T := by
                rw [cfpMap_fst,
                  Category.comp_id]
            _ = (cfpAssocFst A p.T p.T ≫
                  cfpFst A p.T) ≫
                  cfpSnd p.T p.T := by
                rw [Category.assoc]
            _ = cfpFst A (cfpProd p.T p.T) ≫
                  cfpSnd p.T p.T := by
                unfold cfpAssocFst
                rw [cfpLift_fst]
        congr 1 <;> (
          rw [← Category.assoc, cfpLift_fst,
            Category.assoc, Category.assoc,
            iteFold_snd]
          exact simplify)
      rw [lhs_eq, rhs_eq])

/-- Pre-composing the condition of `treeIte`
with `isLeafEndo` has no effect:
`treeIte((X, Y), isLeafEndo(c))
  = treeIte((X, Y), c)`. -/
theorem treeIte_condition_isLeafEndo
    {D : C}
    (X Y c : D ⟶ p.T) :
    cfpLift (cfpLift X Y) (c ≫ isLeafEndo) ≫
      treeIte =
    cfpLift (cfpLift X Y) c ≫ treeIte := by
  -- Factor cfpLift through cfpMap
  have factor : ∀ (z : D ⟶ p.T),
      cfpLift (cfpLift X Y) z ≫ treeIte =
      cfpLift (𝟙 D) z ≫
        (cfpMap (cfpLift X Y) (𝟙 p.T) ≫
          treeIte) := by
    intro z
    rw [← Category.assoc,
      cfpLift_cfpMap, Category.id_comp,
      Category.comp_id]
  rw [factor, factor]
  -- Factor cfpLift (𝟙 D) (c ≫ isLeafEndo)
  -- through cfpMap (𝟙 D) isLeafEndo
  have h1 :
      cfpLift (𝟙 D) (c ≫ isLeafEndo) =
      cfpLift (𝟙 D) c ≫
        cfpMap (𝟙 D) isLeafEndo := by
    rw [cfpLift_cfpMap, Category.id_comp]
  rw [h1, Category.assoc]
  -- Absorb cfpMap isLeafEndo into treeIte
  congr 1
  unfold treeIte
  rw [← Category.assoc, ← Category.assoc,
    cfpMap_comp, Category.id_comp,
    Category.comp_id]
  have split :
      cfpMap (cfpLift X Y) isLeafEndo =
      cfpMap (cfpLift X Y) (𝟙 p.T) ≫
        cfpMap (𝟙 (cfpProd p.T p.T))
          isLeafEndo := by
    rw [cfpMap_comp, Category.comp_id,
      Category.id_comp]
  rw [split, Category.assoc,
    Category.assoc,
    ← Category.assoc
      (cfpMap (𝟙 (cfpProd p.T p.T))
        isLeafEndo)
      iteFold
      (cfpFst p.T p.T),
    iteFold_isLeafEndo]

/-- At a branch condition, `treeIte` returns
the "else" branch: for any `f g r : D ⟶ T`,
`treeIte((f, g), β ∘ r) = g`. -/
theorem treeIte_β_applied
    {D : C}
    (f g : D ⟶ p.T)
    (r : D ⟶ cfpProd p.T p.T) :
    cfpLift (cfpLift f g) (r ≫ p.β) ≫
      treeIte = g := by
  have factor :
      cfpLift (cfpLift f g) (r ≫ p.β) =
      cfpLift (cfpLift f g) r ≫
        cfpMap (𝟙 (cfpProd p.T p.T)) p.β := by
    symm
    rw [cfpLift_cfpMap, Category.comp_id]
  rw [factor, Category.assoc, treeIte_β,
    ← Category.assoc, ← Category.assoc]
  unfold cfpLiftAssoc
  rw [cfpLift_precomp, cfpLift_fst,
    Category.assoc, Category.assoc,
    iteFold_snd]
  unfold cfpAssocFst
  rw [← Category.assoc (cfpLift _ _)
    (cfpFst _ _) (cfpSnd _ _),
    cfpLift_fst, ← Category.assoc,
    cfpLift_fst, cfpLift_snd]

/-- At `cfpMap k β ≫ treeIte` with `k = cfpLift A B`,
the branch condition β gives the "else" value B. -/
theorem cfpMap_β_treeIte
    {D : C}
    (A B : D ⟶ p.T) :
    cfpMap (cfpLift A B) p.β ≫ treeIte =
    cfpFst D (cfpProd p.T p.T) ≫ B := by
  have expand :
      cfpMap (cfpLift A B) p.β =
      cfpLift
        (cfpLift
          (cfpFst D (cfpProd p.T p.T) ≫ A)
          (cfpFst D (cfpProd p.T p.T) ≫ B))
        (cfpSnd D (cfpProd p.T p.T) ≫ p.β) := by
    unfold cfpMap
    congr 1
    rw [cfpLift_precomp]
  rw [expand, treeIte_β_applied]

/-- At `cfpInsertSnd ℓ ≫ cfpMap k (𝟙 T) ≫ treeIte`
with `k = cfpLift A B`, the leaf condition gives
the "then" value A. -/
theorem cfpInsertSnd_cfpMap_treeIte
    {D : C}
    (A B : D ⟶ p.T) :
    cfpInsertSnd p.ℓ D ≫
      cfpMap (cfpLift A B) (𝟙 p.T) ≫ treeIte =
    A := by
  rw [← Category.assoc]
  unfold cfpInsertSnd
  rw [cfpLift_cfpMap, Category.comp_id,
    Category.id_comp]
  have : cfpLift (cfpLift A B)
      (cfpTerminalFrom D ≫ p.ℓ) =
      cfpLift A B ≫ cfpInsertSnd p.ℓ
        (cfpProd p.T p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm
  rw [this, Category.assoc, treeIte_ℓ,
    cfpLift_fst]

/-- At a branch condition, the inner treeIte
gives the "else" value, composed with the
parameter projection. -/
theorem cfpMap_β_inner_treeIte
    {D : C}
    (A B : D ⟶ p.T) :
    cfpMap (𝟙 D) p.β ≫
      cfpMap (cfpLift A B) (𝟙 p.T) ≫ treeIte =
    cfpFst D (cfpProd p.T p.T) ≫ B := by
  rw [← Category.assoc, cfpMap_comp,
    Category.id_comp, Category.comp_id,
    cfpMap_β_treeIte]

/-- Composition of `treeIte`: nesting an inner
`treeIte` as the condition of an outer `treeIte`
distributes the outer branches into the inner
branches.

`treeIte((X, Y), treeIte((A, B), c))
  = treeIte((treeIte((X,Y), A),
             treeIte((X,Y), B)), c)` -/
theorem treeIte_compose
    {D : C}
    (X Y A B c : D ⟶ p.T) :
    cfpLift (cfpLift X Y)
      (cfpLift (cfpLift A B) c ≫ treeIte) ≫
      treeIte =
    cfpLift
      (cfpLift
        (cfpLift (cfpLift X Y) A ≫ treeIte)
        (cfpLift (cfpLift X Y) B ≫ treeIte))
      c ≫ treeIte := by
  -- Factor cfpLift (cfpLift A B) c.
  have factor (z : D ⟶ p.T) :
      cfpLift (cfpLift A B) z =
      cfpLift (𝟙 D) z ≫
        cfpMap (cfpLift A B) (𝟙 p.T) := by
    symm; rw [cfpLift_cfpMap,
      Category.id_comp, Category.comp_id]
  -- Factor both sides through cfpLift (𝟙 D) c.
  have lhs_eq :
      cfpLift (cfpLift X Y)
        (cfpLift (cfpLift A B) c ≫
          treeIte) ≫ treeIte =
      cfpLift (𝟙 D) c ≫
        (cfpLift (cfpFst D p.T ≫ cfpLift X Y)
          (cfpMap (cfpLift A B) (𝟙 p.T) ≫
            treeIte) ≫
          treeIte) := by
    have h1 :
        cfpLift (cfpLift A B) c ≫ treeIte =
        cfpLift (𝟙 D) c ≫
          (cfpMap (cfpLift A B) (𝟙 p.T) ≫
            treeIte) := by
      rw [← Category.assoc, factor c]
    rw [← Category.assoc, h1,
      ← Category.assoc
        (cfpLift (𝟙 D) c) _ treeIte,
      cfpLift_precomp, ← Category.assoc,
      cfpLift_fst, Category.id_comp,
      Category.assoc]
  have rhs_eq :
      cfpLift
        (cfpLift
          (cfpLift (cfpLift X Y) A ≫ treeIte)
          (cfpLift (cfpLift X Y) B ≫
            treeIte))
        c ≫ treeIte =
      cfpLift (𝟙 D) c ≫
        (cfpMap
          (cfpLift
            (cfpLift (cfpLift X Y) A ≫
              treeIte)
            (cfpLift (cfpLift X Y) B ≫
              treeIte))
          (𝟙 p.T) ≫
          treeIte) := by
    rw [← Category.assoc]
    congr 1; symm
    rw [cfpLift_cfpMap, Category.id_comp,
      Category.comp_id]
  rw [lhs_eq, rhs_eq]
  congr 1
  -- Reduce to elim_uniq.
  have rhs_elim :
      cfpMap
        (cfpLift
          (cfpLift (cfpLift X Y) A ≫ treeIte)
          (cfpLift (cfpLift X Y) B ≫
            treeIte))
        (𝟙 p.T) ≫ treeIte =
      p.elim
        (cfpLift
          (cfpLift (cfpLift X Y) A ≫ treeIte)
          (cfpLift (cfpLift X Y) B ≫
            treeIte))
        (cfpLift
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T)
          (cfpFst (cfpProd p.T p.T)
            (cfpProd p.T p.T) ≫
            cfpSnd p.T p.T)) ≫
        cfpFst p.T p.T := by
    unfold treeIte iteFold
    rw [← Category.assoc, elim_naturality,
      Category.comp_id]
  rw [rhs_elim]
  -- Witness for elim_uniq.
  have w :=
    p.elim_uniq
      (cfpLift
        (cfpLift (cfpLift X Y) A ≫ treeIte)
        (cfpLift (cfpLift X Y) B ≫ treeIte))
      (cfpLift
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T)
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T))
      (cfpLift
        (cfpLift
          (cfpFst D p.T ≫ cfpLift X Y)
          (cfpMap (cfpLift A B)
            (𝟙 p.T) ≫ treeIte) ≫
          treeIte)
        (cfpFst D p.T ≫
          cfpLift (cfpLift X Y) B ≫
          treeIte))
      -- Base
      (by
        unfold cfpInsertSnd
        rw [cfpLift_precomp]
        congr 1
        · rw [← Category.assoc, cfpLift_precomp,
            ← Category.assoc _ (cfpFst _ _)
              (cfpLift X Y),
            cfpLift_fst, Category.id_comp]
          change cfpLift (cfpLift X Y)
            (cfpInsertSnd p.ℓ D ≫
              cfpMap (cfpLift A B)
                (𝟙 p.T) ≫ treeIte) ≫
            treeIte = _
          rw [cfpInsertSnd_cfpMap_treeIte]
        · rw [← Category.assoc, cfpLift_fst,
            Category.id_comp])
      -- Branch
      (by
        rw [cfpLift_precomp]
        -- LHS fst
        have h1 :
            cfpMap (𝟙 D) p.β ≫
              (cfpLift
                (cfpFst D p.T ≫ cfpLift X Y)
                (cfpMap (cfpLift A B)
                  (𝟙 p.T) ≫ treeIte) ≫
                treeIte) =
            cfpFst D (cfpProd p.T p.T) ≫
              cfpLift (cfpLift X Y) B ≫
              treeIte := by
          rw [← Category.assoc, cfpLift_precomp]
          have : cfpMap (𝟙 D) p.β ≫
              cfpFst D p.T ≫ cfpLift X Y =
              cfpFst D (cfpProd p.T p.T) ≫
                cfpLift X Y := by
            rw [← Category.assoc,
              cfpMap_fst, Category.comp_id]
          rw [this, cfpMap_β_inner_treeIte,
            ← cfpLift_precomp, Category.assoc]
        -- LHS snd
        have h2 :
            cfpMap (𝟙 D) p.β ≫
              (cfpFst D p.T ≫
                cfpLift (cfpLift X Y) B ≫
                treeIte) =
            cfpFst D (cfpProd p.T p.T) ≫
              cfpLift (cfpLift X Y) B ≫
              treeIte := by
          rw [← Category.assoc (cfpMap _ _)
            (cfpFst _ _), cfpMap_fst,
            Category.comp_id]
        rw [h1, h2]
        -- Show cfpLiftAssoc Ψ' Ψ' ≫ step
        -- = cfpLift (cfpFst ≫ EL) (cfpFst ≫ EL).
        have rhs_proj (proj :
            cfpProd p.T p.T ⟶ p.T)
            (hp : (cfpLift
              (cfpFst (cfpProd p.T p.T)
                (cfpProd p.T p.T) ≫
                cfpSnd p.T p.T)
              (cfpFst (cfpProd p.T p.T)
                (cfpProd p.T p.T) ≫
                cfpSnd p.T p.T)) ≫ proj =
              cfpFst (cfpProd p.T p.T)
                (cfpProd p.T p.T) ≫
                cfpSnd p.T p.T) :
            cfpLiftAssoc
              (cfpLift
                (cfpLift
                  (cfpFst D p.T ≫
                    cfpLift X Y)
                  (cfpMap (cfpLift A B)
                    (𝟙 p.T) ≫ treeIte) ≫
                  treeIte)
                (cfpFst D p.T ≫
                  cfpLift (cfpLift X Y) B ≫
                  treeIte))
              (cfpLift
                (cfpLift
                  (cfpFst D p.T ≫
                    cfpLift X Y)
                  (cfpMap (cfpLift A B)
                    (𝟙 p.T) ≫ treeIte) ≫
                  treeIte)
                (cfpFst D p.T ≫
                  cfpLift (cfpLift X Y) B ≫
                  treeIte)) ≫
              (cfpLift
                (cfpFst (cfpProd p.T p.T)
                  (cfpProd p.T p.T) ≫
                  cfpSnd p.T p.T)
                (cfpFst (cfpProd p.T p.T)
                  (cfpProd p.T p.T) ≫
                  cfpSnd p.T p.T)) ≫ proj =
            cfpFst D (cfpProd p.T p.T) ≫
              cfpLift (cfpLift X Y) B ≫
              treeIte := by
          rw [hp]
          unfold cfpLiftAssoc
          rw [← Category.assoc,
            cfpLift_fst, Category.assoc,
            cfpLift_snd]
          unfold cfpAssocFst
          rw [← Category.assoc, cfpLift_fst]
        symm
        apply cfpLift_uniq
        · rw [Category.assoc,
            rhs_proj _ (cfpLift_fst _ _)]
        · rw [Category.assoc,
            rhs_proj _ (cfpLift_snd _ _)])
  rw [← w, cfpLift_fst]

/-- Associativity of `boolAnd`. -/
theorem boolAnd_assoc
    {D : C}
    (A B E : D ⟶ p.T) :
    cfpLift (cfpLift A B ≫ boolAnd) E ≫
      boolAnd =
    cfpLift A (cfpLift B E ≫ boolAnd) ≫
      boolAnd := by
  -- Expand via boolAnd_treeIte_form.
  rw [boolAnd_treeIte_form]
  rw [boolAnd_treeIte_form]
  rw [boolAnd_treeIte_form]
  rw [boolAnd_treeIte_form]
  -- LHS: nested treeIte. Apply treeIte_compose.
  rw [treeIte_compose]
  -- Simplify the inner treeIte applications.
  congr 1
  apply cfpLift_uniq
  · -- cfpFst: treeIte_condition_isLeafEndo +
    -- treeIte_isLeafEndo_stable.
    rw [cfpLift_fst]
    congr 1
    · rw [treeIte_condition_isLeafEndo]
      symm
      rw [Category.assoc]
      exact treeIte_isLeafEndo_stable
        (E ≫ isLeafEndo)
        (cfpTerminalFrom D ≫ treeFalse) B
        (by rw [Category.assoc,
          @isLeafEndo_idem C _ h p])
        (by rw [Category.assoc,
          isLeafEndo_treeFalse])
    · rw [treeIte_treeFalse_applied]
  · rw [cfpLift_snd]

/-- Transitivity of `boolAnd`-implication:
if `boolAnd(A, B) = A` and `boolAnd(B, E) = B`,
then `boolAnd(A, E) = A`. -/
theorem boolAnd_implies_trans
    {D : C}
    {A B E : D ⟶ p.T}
    (hAB : cfpLift A B ≫ boolAnd = A)
    (hBE : cfpLift B E ≫ boolAnd = B) :
    cfpLift A E ≫ boolAnd = A := by
  calc cfpLift A E ≫ boolAnd
      = cfpLift (cfpLift A B ≫ boolAnd) E ≫
          boolAnd := by
        rw [hAB]
    _ = cfpLift A (cfpLift B E ≫ boolAnd) ≫
          boolAnd := boolAnd_assoc A B E
    _ = cfpLift A B ≫ boolAnd := by
        rw [hBE]
    _ = A := hAB


/-- Bridge from `boolAnd`-implication to
`IsLeafConst`: if `boolAnd(A, B) = A` and
`B` is Boolean-valued (`B ≫ isLeafEndo = B`),
then for any `e` with `e ≫ A = leaf`,
also `e ≫ B = leaf`. -/
theorem boolAnd_implies_IsLeafConst
    {D : C}
    {A B : D ⟶ p.T}
    (h : cfpLift A B ≫ boolAnd = A)
    (hB : B ≫ isLeafEndo = B)
    {E : C}
    (e : E ⟶ D)
    (hA : IsLeafConst (e ≫ A)) :
    IsLeafConst (e ≫ B) := by
  unfold IsLeafConst at hA ⊢
  have h1 : cfpLift (e ≫ A) (e ≫ B) ≫
      boolAnd = e ≫ A := by
    rw [← cfpLift_precomp, Category.assoc, h]
  rw [hA] at h1
  have factor :
      cfpLift (cfpTerminalFrom E ≫ p.ℓ)
        (e ≫ B) =
      cfpLift (cfpTerminalFrom E)
        (e ≫ B) ≫
        cfpMap p.ℓ (𝟙 p.T) := by
    rw [cfpLift_cfpMap, Category.comp_id]
  rw [factor, Category.assoc,
    boolAnd_leaf_left] at h1
  -- h1 : cfpLift (cfpTerminalFrom E) (e ≫ B)
  --   ≫ cfpSnd ≫ isLeafEndo = leaf
  rw [← Category.assoc, cfpLift_snd] at h1
  -- h1 : (e ≫ B) ≫ isLeafEndo = leaf
  rw [Category.assoc, hB] at h1
  exact h1

/-- Idempotence of `boolAnd` along the diagonal:
`boolAnd(a, a) = isLeafEndo(a)`. -/
theorem boolAnd_idem :
    cfpLift (𝟙 p.T) (𝟙 p.T) ≫ boolAnd =
      (isLeafEndo : p.T ⟶ p.T) := by
  -- Lift to cfpProd cfpTerminal T → T, show
  -- both sides equal isLeaf, then project back.
  -- Abbreviations.
  let snd : cfpProd cfpTerminal p.T ⟶ p.T :=
    cfpSnd cfpTerminal p.T
  let step : cfpProd p.T p.T ⟶ p.T :=
    cfpTerminalFrom (cfpProd p.T p.T) ≫ treeFalse
  let D' : C :=
    cfpProd cfpTerminal (cfpProd p.T p.T)
  let snd' : D' ⟶ p.T :=
    cfpSnd cfpTerminal (cfpProd p.T p.T) ≫ p.β
  -- ℓ equation for cfpLift snd snd ≫ boolAnd.
  have snd_ℓ :
      cfpInsertSnd p.ℓ cfpTerminal ≫ snd =
      p.ℓ := by
    change cfpInsertSnd p.ℓ cfpTerminal ≫
      cfpSnd cfpTerminal p.T = p.ℓ
    unfold cfpInsertSnd
    rw [cfpLift_snd, cfpTerminalFrom_terminal,
      Category.id_comp]
  have ℓ_eq :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        (cfpLift snd snd ≫ boolAnd) = p.ℓ := by
    rw [← Category.assoc, cfpLift_precomp,
      snd_ℓ, boolAnd_ℓ_ℓ]
  -- β equation for cfpLift snd snd ≫ boolAnd.
  have snd_β :
      cfpMap (𝟙 cfpTerminal) p.β ≫ snd =
      cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
        p.β := by
    change cfpMap (𝟙 cfpTerminal) p.β ≫
      cfpSnd cfpTerminal p.T =
      cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
        p.β
    exact cfpMap_snd (𝟙 cfpTerminal) p.β
  have β_lhs :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (cfpLift snd snd ≫ boolAnd) =
      cfpLift snd' snd' ≫ boolAnd := by
    change cfpMap (𝟙 cfpTerminal) p.β ≫
      (cfpLift snd snd ≫ boolAnd) =
      cfpLift
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫ p.β)
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫ p.β) ≫
        boolAnd
    rw [← Category.assoc, cfpLift_precomp, snd_β]
  have snd'_isLeafEndo :
      snd' ≫ isLeafEndo =
      cfpTerminalFrom D' ≫ treeFalse := by
    change (cfpSnd cfpTerminal
      (cfpProd p.T p.T) ≫ p.β) ≫
      isLeafEndo =
      cfpTerminalFrom D' ≫ treeFalse
    rw [Category.assoc, isLeafEndo_β,
      ← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  have β_boolAnd :
      cfpLift snd' snd' ≫ boolAnd =
      cfpTerminalFrom D' ≫ treeFalse := by
    change cfpLift
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫ p.β)
        (cfpSnd cfpTerminal
          (cfpProd p.T p.T) ≫ p.β) ≫
        boolAnd =
      cfpTerminalFrom D' ≫ treeFalse
    rw [boolAnd_treeIte_form,
      snd'_isLeafEndo, treeIte_equal_branches]
  have β_rhs :
      cfpLiftAssoc
        (cfpLift snd snd ≫ boolAnd)
        (cfpLift snd snd ≫ boolAnd) ≫ step =
      cfpTerminalFrom D' ≫ treeFalse := by
    change cfpLiftAssoc
        (cfpLift snd snd ≫ boolAnd)
        (cfpLift snd snd ≫ boolAnd) ≫
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse) =
      cfpTerminalFrom D' ≫ treeFalse
    rw [← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  have β_eq :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (cfpLift snd snd ≫ boolAnd) =
      cfpLiftAssoc
        (cfpLift snd snd ≫ boolAnd)
        (cfpLift snd snd ≫ boolAnd) ≫ step := by
    rw [β_lhs, β_boolAnd, β_rhs]
  -- By p.elim_uniq.
  have is_isLeaf :
      cfpLift snd snd ≫ boolAnd =
      p.elim p.ℓ step := by
    exact p.elim_uniq p.ℓ step _ ℓ_eq β_eq
  -- isLeaf = p.elim ℓ step.
  have isLeaf_def :
      (isLeaf :
        cfpProd cfpTerminal p.T ⟶ p.T) =
      p.elim p.ℓ step := by
    change isLeaf = p.elim p.ℓ
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse)
    rfl
  -- Project back via sect.
  let sect : p.T ⟶ cfpProd cfpTerminal p.T :=
    cfpLift (cfpTerminalFrom p.T) (𝟙 p.T)
  have sect_snd :
      sect ≫ snd = 𝟙 p.T := by
    change
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpSnd cfpTerminal p.T = 𝟙 p.T
    exact cfpLift_snd _ _
  have sect_lift_snd :
      sect ≫ cfpLift snd snd =
      cfpLift (𝟙 p.T) (𝟙 p.T) := by
    change
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpLift (cfpSnd cfpTerminal p.T)
          (cfpSnd cfpTerminal p.T) =
      cfpLift (𝟙 p.T) (𝟙 p.T)
    rw [cfpLift_precomp,
      cfpLift_snd (cfpTerminalFrom p.T) (𝟙 p.T)]
  -- isLeafEndo = sect ≫ isLeaf.
  have isLeafEndo_eq :
      (isLeafEndo : p.T ⟶ p.T) =
      sect ≫ isLeaf := by
    change isLeafEndo =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        isLeaf
    rfl
  -- Conclude.
  calc cfpLift (𝟙 p.T) (𝟙 p.T) ≫ boolAnd
      = (sect ≫ cfpLift snd snd) ≫ boolAnd := by
        rw [sect_lift_snd]
    _ = sect ≫ (cfpLift snd snd ≫ boolAnd) :=
        Category.assoc _ _ _
    _ = sect ≫ p.elim p.ℓ step := by
        rw [is_isLeaf]
    _ = sect ≫ isLeaf := by rw [isLeaf_def]
    _ = isLeafEndo := isLeafEndo_eq.symm

/-- Right-identity for `boolAnd` with constant
leaf second argument, on `cfpProd cfpTerminal T`:
`boolAnd(snd, const_ℓ) = isLeaf`.

The proof parallels `boolAnd_idem`: both sides
satisfy the same ℓ and β computation rules
(yielding `ℓ` at leaf and `treeFalse` at branch),
so they are equal by `elim_uniq`. -/
theorem boolAnd_snd_const_ℓ :
    cfpLift
      (cfpSnd cfpTerminal p.T)
      (cfpTerminalFrom (cfpProd cfpTerminal p.T) ≫
        p.ℓ) ≫
      boolAnd =
    (isLeaf :
      cfpProd cfpTerminal p.T ⟶ p.T) := by
  set snd := cfpSnd cfpTerminal p.T
  set c := cfpTerminalFrom
    (cfpProd cfpTerminal p.T) ≫ p.ℓ
  set step : cfpProd p.T p.T ⟶ p.T :=
    cfpTerminalFrom (cfpProd p.T p.T) ≫ treeFalse
  set D' := cfpProd cfpTerminal (cfpProd p.T p.T)
  -- ℓ computation rule.
  have snd_ℓ :
      cfpInsertSnd p.ℓ cfpTerminal ≫ snd =
      p.ℓ := by
    change cfpInsertSnd p.ℓ cfpTerminal ≫
      cfpSnd cfpTerminal p.T = p.ℓ
    unfold cfpInsertSnd
    rw [cfpLift_snd, cfpTerminalFrom_terminal,
      Category.id_comp]
  have c_at_ℓ :
      cfpInsertSnd p.ℓ cfpTerminal ≫ c = p.ℓ := by
    change cfpInsertSnd p.ℓ cfpTerminal ≫
      cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ = p.ℓ
    rw [← Category.assoc,
      show cfpInsertSnd p.ℓ cfpTerminal ≫
        cfpTerminalFrom
          (cfpProd cfpTerminal p.T) =
        cfpTerminalFrom cfpTerminal from
        h.terminal.uniq _,
      cfpTerminalFrom_terminal,
      Category.id_comp]
  have ℓ_eq :
      cfpInsertSnd p.ℓ cfpTerminal ≫
        (cfpLift snd c ≫ boolAnd) = p.ℓ := by
    rw [← Category.assoc, cfpLift_precomp,
      snd_ℓ, c_at_ℓ, boolAnd_ℓ_ℓ]
  -- β computation rule.
  have snd_β :
      cfpMap (𝟙 cfpTerminal) p.β ≫ snd =
      cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
        p.β :=
    cfpMap_snd (𝟙 cfpTerminal) p.β
  have c_at_β :
      cfpMap (𝟙 cfpTerminal) p.β ≫ c =
      cfpTerminalFrom D' ≫ p.ℓ := by
    change cfpMap (𝟙 cfpTerminal) p.β ≫
      cfpTerminalFrom
        (cfpProd cfpTerminal p.T) ≫ p.ℓ =
      cfpTerminalFrom D' ≫ p.ℓ
    rw [← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  have β_lhs :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (cfpLift snd c ≫ boolAnd) =
      cfpLift
        (cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
          p.β)
        (cfpTerminalFrom D' ≫ p.ℓ) ≫
        boolAnd := by
    rw [← Category.assoc, cfpLift_precomp,
      snd_β, c_at_β]
  -- β is non-leaf, so boolAnd(β, const_ℓ) =
  -- treeFalse.
  have snd'_isLeafEndo :
      (cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
        p.β) ≫ isLeafEndo =
      cfpTerminalFrom D' ≫ treeFalse := by
    rw [Category.assoc, isLeafEndo_β,
      ← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  have β_boolAnd_val :
      cfpLift
        (cfpSnd cfpTerminal (cfpProd p.T p.T) ≫
          p.β)
        (cfpTerminalFrom D' ≫ p.ℓ) ≫ boolAnd =
      cfpTerminalFrom D' ≫ treeFalse := by
    rw [boolAnd_treeIte_form]
    have h1 : (cfpTerminalFrom D' ≫ p.ℓ) ≫
        isLeafEndo =
        cfpTerminalFrom D' ≫ p.ℓ := by
      rw [Category.assoc, isLeafEndo_ℓ]
    rw [h1]
    -- Goal: treeIte((const_ℓ, const_treeFalse),
    --   snd ≫ β) = const_treeFalse.
    -- snd ≫ β is a branch node, so treeIte
    -- returns the else branch.
    exact treeIte_β_applied
      (cfpTerminalFrom D' ≫ p.ℓ)
      (cfpTerminalFrom D' ≫ treeFalse)
      (cfpSnd cfpTerminal (cfpProd p.T p.T))
  have β_rhs :
      cfpLiftAssoc
        (cfpLift snd c ≫ boolAnd)
        (cfpLift snd c ≫ boolAnd) ≫ step =
      cfpTerminalFrom D' ≫ treeFalse := by
    change cfpLiftAssoc
        (cfpLift snd c ≫ boolAnd)
        (cfpLift snd c ≫ boolAnd) ≫
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse) =
      cfpTerminalFrom D' ≫ treeFalse
    rw [← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  have β_eq :
      cfpMap (𝟙 cfpTerminal) p.β ≫
        (cfpLift snd c ≫ boolAnd) =
      cfpLiftAssoc
        (cfpLift snd c ≫ boolAnd)
        (cfpLift snd c ≫ boolAnd) ≫ step := by
    rw [β_lhs, β_boolAnd_val, β_rhs]
  -- By elim_uniq.
  have is_isLeaf :
      cfpLift snd c ≫ boolAnd =
      p.elim p.ℓ step :=
    p.elim_uniq p.ℓ step _ ℓ_eq β_eq
  have isLeaf_def :
      (isLeaf :
        cfpProd cfpTerminal p.T ⟶ p.T) =
      p.elim p.ℓ step := rfl
  rw [is_isLeaf, ← isLeaf_def]

/-- `boolAnd(A, const_leaf) = A` for Boolean
`A` (satisfying `A ≫ isLeafEndo = A`).
The constant leaf acts as a right identity for
`boolAnd` on Boolean-valued morphisms.

Proof: Factor through `boolAnd_snd_const_ℓ`
which establishes the identity on
`cfpProd cfpTerminal T`, then project via the
section `cfpLift (cfpTerminalFrom T) (𝟙 T)`. -/
theorem boolAnd_const_leaf_right
    {D : C}
    {A : D ⟶ p.T}
    (hA : A ≫ isLeafEndo = A) :
    cfpLift A (cfpTerminalFrom D ≫ p.ℓ) ≫
      boolAnd = A := by
  have factor :
      cfpLift A (cfpTerminalFrom D ≫ p.ℓ) =
      A ≫ cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ) := by
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm
  rw [factor, Category.assoc]
  suffices hsuff :
      cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ) ≫
        boolAnd = isLeafEndo by
    rw [hsuff, hA]
  -- isLeafEndo = sect ≫ isLeaf where
  -- sect = cfpLift (cfpTerminalFrom T) (𝟙 T).
  let sect : p.T ⟶ cfpProd cfpTerminal p.T :=
    cfpLift (cfpTerminalFrom p.T) (𝟙 p.T)
  -- sect ≫ cfpLift snd (const_ℓ) =
  --   cfpLift (𝟙 T) (const_ℓ).
  have sect_comp :
      sect ≫ cfpLift
        (cfpSnd cfpTerminal p.T)
        (cfpTerminalFrom
          (cfpProd cfpTerminal p.T) ≫ p.ℓ) =
      cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ) := by
    change cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
      cfpLift
        (cfpSnd cfpTerminal p.T)
        (cfpTerminalFrom
          (cfpProd cfpTerminal p.T) ≫ p.ℓ) =
      cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ)
    rw [cfpLift_precomp,
      cfpLift_snd (cfpTerminalFrom p.T) (𝟙 p.T)]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  calc cfpLift (𝟙 p.T)
        (cfpTerminalFrom p.T ≫ p.ℓ) ≫ boolAnd
      = (sect ≫ cfpLift
          (cfpSnd cfpTerminal p.T)
          (cfpTerminalFrom
            (cfpProd cfpTerminal p.T) ≫
            p.ℓ)) ≫ boolAnd := by
        rw [sect_comp]
    _ = sect ≫ (cfpLift
          (cfpSnd cfpTerminal p.T)
          (cfpTerminalFrom
            (cfpProd cfpTerminal p.T) ≫
            p.ℓ) ≫ boolAnd) :=
        Category.assoc _ _ _
    _ = sect ≫ isLeaf :=
        by rw [boolAnd_snd_const_ℓ]
    _ = isLeafEndo := rfl

/-- `boolAnd(treeFalse, B) = treeFalse` for any
`B : D ⟶ T`.  The first argument is non-leaf, so
`treeIte` returns the "else" branch
(`treeFalse`). -/
theorem boolAnd_treeFalse_left
    {D : C}
    (B : D ⟶ p.T) :
    cfpLift (cfpTerminalFrom D ≫ treeFalse) B ≫
      boolAnd =
    cfpTerminalFrom D ≫ treeFalse := by
  rw [boolAnd_treeIte_form]
  exact treeIte_treeFalse_applied _ _

/-- From `IsLeafConst(e ≫ cfpLift A B ≫ boolAnd)`
and `A ≫ isLeafEndo = A`, derive
`IsLeafConst(e ≫ A)`.

The proof is purely equational.  Starting from
`boolAnd_const_leaf_right` applied to `e ≫ A`
(which is Boolean by `hA`), substituting the
hypothesis, and applying `boolAnd_assoc` together
with `boolAnd_idem` yields `e ≫ A` equal to the
hypothesis. -/
theorem boolAnd_fst_IsLeafConst
    {D : C}
    {A B : D ⟶ p.T}
    (hA : A ≫ isLeafEndo = A)
    {E : C} (e : E ⟶ D)
    (hAB : IsLeafConst
      (e ≫ cfpLift A B ≫ boolAnd)) :
    IsLeafConst (e ≫ A) := by
  unfold IsLeafConst at hAB ⊢
  -- hAB : e ≫ cfpLift A B ≫ boolAnd =
  --   cfpTerminalFrom E ≫ p.ℓ
  set a := e ≫ A
  set b := e ≫ B
  -- a is Boolean.
  have ha : a ≫ isLeafEndo = a := by
    change (e ≫ A) ≫ isLeafEndo = e ≫ A
    rw [Category.assoc, hA]
  -- boolAnd(a, ℓ) = a (by boolAnd_const_leaf_right).
  have step1 :
      cfpLift a (cfpTerminalFrom E ≫ p.ℓ) ≫
        boolAnd = a :=
    boolAnd_const_leaf_right ha
  -- Substitute hypothesis backwards:
  -- boolAnd(a, ℓ) = boolAnd(a, boolAnd(a, b)).
  have hab_eq :
      e ≫ cfpLift A B ≫ boolAnd =
      cfpLift a b ≫ boolAnd := by
    rw [← Category.assoc, cfpLift_precomp]
  -- boolAnd(a, boolAnd(a, b)) =
  --   boolAnd(boolAnd(a, a), b)
  --   by boolAnd_assoc.
  have step2 :
      cfpLift a (cfpLift a b ≫ boolAnd) ≫
        boolAnd =
      cfpLift (cfpLift a a ≫ boolAnd) b ≫
        boolAnd :=
    (boolAnd_assoc a a b).symm
  -- boolAnd(a, a) = isLeafEndo(a) = a.
  have step3 :
      cfpLift a a ≫ boolAnd = a := by
    have : cfpLift a a =
        a ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [this, Category.assoc, boolAnd_idem, ha]
  -- Chain: a = boolAnd(a, ℓ)
  --          = boolAnd(a, boolAnd(a, b))
  --          = boolAnd(boolAnd(a, a), b)
  --          = boolAnd(a, b)
  --          = ℓ.
  calc a
      = cfpLift a (cfpTerminalFrom E ≫ p.ℓ) ≫
          boolAnd := step1.symm
    _ = cfpLift a
          (e ≫ cfpLift A B ≫ boolAnd) ≫
          boolAnd := by
        rw [hAB]
    _ = cfpLift a
          (cfpLift a b ≫ boolAnd) ≫
          boolAnd := by
        rw [hab_eq]
    _ = cfpLift (cfpLift a a ≫ boolAnd) b ≫
          boolAnd := step2
    _ = cfpLift a b ≫ boolAnd := by
        rw [step3]
    _ = e ≫ cfpLift A B ≫ boolAnd := by
        rw [← hab_eq]
    _ = cfpTerminalFrom E ≫ p.ℓ := hAB

/-- From `IsLeafConst(e ≫ cfpLift A B ≫ boolAnd)`
and `B ≫ isLeafEndo = B`, derive
`IsLeafConst(e ≫ B)`.

The proof is purely equational.  Starting from
`boolAnd_leaf_left` applied to `e ≫ B`, substituting
the hypothesis, and applying `boolAnd_assoc` together
with `boolAnd_idem` yields `e ≫ B` equal to the
hypothesis. -/
theorem boolAnd_snd_IsLeafConst
    {D : C}
    {A B : D ⟶ p.T}
    (hB : B ≫ isLeafEndo = B)
    {E : C} (e : E ⟶ D)
    (hAB : IsLeafConst
      (e ≫ cfpLift A B ≫ boolAnd)) :
    IsLeafConst (e ≫ B) := by
  unfold IsLeafConst at hAB ⊢
  set a := e ≫ A
  set b := e ≫ B
  -- b is Boolean.
  have hb : b ≫ isLeafEndo = b := by
    change (e ≫ B) ≫ isLeafEndo = e ≫ B
    rw [Category.assoc, hB]
  -- boolAnd(ℓ, b) = isLeafEndo(b) = b.
  have step1 :
      cfpLift (cfpTerminalFrom E ≫ p.ℓ) b ≫
        boolAnd = b := by
    have factor :
        cfpLift (cfpTerminalFrom E ≫ p.ℓ) b =
        cfpLift (cfpTerminalFrom E) b ≫
          cfpMap p.ℓ (𝟙 p.T) := by
      rw [cfpLift_cfpMap, Category.comp_id]
    rw [factor, Category.assoc,
      boolAnd_leaf_left, ← Category.assoc,
      cfpLift_snd, hb]
  have hab_eq :
      e ≫ cfpLift A B ≫ boolAnd =
      cfpLift a b ≫ boolAnd := by
    rw [← Category.assoc, cfpLift_precomp]
  -- boolAnd(boolAnd(a, b), b) =
  --   boolAnd(a, boolAnd(b, b))
  --   by boolAnd_assoc.
  have step2 :
      cfpLift (cfpLift a b ≫ boolAnd) b ≫
        boolAnd =
      cfpLift a (cfpLift b b ≫ boolAnd) ≫
        boolAnd :=
    boolAnd_assoc a b b
  -- boolAnd(b, b) = isLeafEndo(b) = b.
  have step3 :
      cfpLift b b ≫ boolAnd = b := by
    have : cfpLift b b =
        b ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [this, Category.assoc, boolAnd_idem, hb]
  -- Chain: b = boolAnd(ℓ, b)
  --          = boolAnd(boolAnd(a, b), b)
  --          = boolAnd(a, boolAnd(b, b))
  --          = boolAnd(a, b)
  --          = ℓ.
  calc b
      = cfpLift (cfpTerminalFrom E ≫ p.ℓ) b ≫
          boolAnd := step1.symm
    _ = cfpLift
          (e ≫ cfpLift A B ≫ boolAnd) b ≫
          boolAnd := by
        rw [hAB]
    _ = cfpLift
          (cfpLift a b ≫ boolAnd) b ≫
          boolAnd := by
        rw [hab_eq]
    _ = cfpLift a (cfpLift b b ≫ boolAnd) ≫
          boolAnd := step2
    _ = cfpLift a b ≫ boolAnd := by
        rw [step3]
    _ = e ≫ cfpLift A B ≫ boolAnd := by
        rw [← hab_eq]
    _ = cfpTerminalFrom E ≫ p.ℓ := hAB

/-- A PBTO has Boolean dichotomy when every
Boolean-valued global element of T (fixed by
`isLeafEndo`) is either `ℓ` or `treeFalse`. -/
def HasBoolDichotomy
    (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C]
    [p : HasPBTO C] : Prop :=
  ∀ (e : cfpTerminal (C := C) ⟶ p.T),
    e ≫ isLeafEndo = e →
    e = p.ℓ ∨ e = treeFalse

/-- `boolAnd(ℓ, treeFalse) = treeFalse`: the
conjunction of leaf (true) and treeFalse (false)
is treeFalse. -/
theorem boolAnd_ℓ_treeFalse :
    cfpLift p.ℓ
      (treeFalse (C := C)) ≫
      boolAnd = treeFalse := by
  rw [boolAnd_treeIte_form,
    @isLeafEndo_treeFalse C _ h p]
  have : cfpTerminalFrom
      (cfpTerminal (C := C)) ≫
      treeFalse = treeFalse := by
    rw [cfpTerminalFrom_terminal,
      Category.id_comp]
  rw [this]
  exact treeIte_equal_branches
    treeFalse p.ℓ

/-- First projection absorption for `boolAnd`:
`boolAnd(boolAnd(A, B), A) = boolAnd(A, B)`
when `A` and `B` are Boolean-valued.

The proof applies `IsSeparator` to reduce to
global elements and performs a case split via
`HasBoolDichotomy`. -/
theorem boolAnd_fst_proj
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hDich : HasBoolDichotomy C)
    {D : C} (A B : D ⟶ p.T)
    (hA : A ≫ isLeafEndo = A)
    (hB : B ≫ isLeafEndo = B) :
    cfpLift (cfpLift A B ≫ boolAnd) A ≫
      boolAnd =
    cfpLift A B ≫ boolAnd := by
  apply hSep.def
  intro e
  -- Push e through cfpLift on both sides.
  simp only [← Category.assoc]
  rw [cfpLift_precomp e, cfpLift_precomp e]
  set a := e ≫ A
  set b := e ≫ B
  have ha : a ≫ isLeafEndo = a := by
    change (e ≫ A) ≫ isLeafEndo = e ≫ A
    rw [Category.assoc, hA]
  have hb : b ≫ isLeafEndo = b := by
    change (e ≫ B) ≫ isLeafEndo = e ≫ B
    rw [Category.assoc, hB]
  -- Push e through the inner boolAnd.
  have inner_eq :
      e ≫ cfpLift A B ≫ boolAnd =
      cfpLift a b ≫ boolAnd := by
    rw [← Category.assoc, cfpLift_precomp e]
  rw [inner_eq]
  -- Auxiliary: rewrite treeFalse at cfpTerminal
  -- to the form required by boolAnd_treeFalse_left.
  have tf_eq :
      treeFalse (C := C) =
      cfpTerminalFrom cfpTerminal ≫
        treeFalse := by
    rw [cfpTerminalFrom_terminal,
      Category.id_comp]
  -- Case split on a and b.
  rcases hDich a ha with ha_val | ha_val <;>
    rcases hDich b hb with hb_val | hb_val <;>
    rw [ha_val, hb_val]
  · -- a = ℓ, b = ℓ
    rw [boolAnd_ℓ_ℓ, boolAnd_ℓ_ℓ]
  · -- a = ℓ, b = treeFalse
    rw [boolAnd_ℓ_treeFalse, tf_eq,
      boolAnd_treeFalse_left]
  · -- a = treeFalse, b = ℓ
    rw [tf_eq, boolAnd_treeFalse_left,
      boolAnd_treeFalse_left]
  · -- a = treeFalse, b = treeFalse
    rw [tf_eq, boolAnd_treeFalse_left,
      boolAnd_treeFalse_left]

/-- Second projection absorption for `boolAnd`:
`boolAnd(boolAnd(A, B), B) = boolAnd(A, B)`
when `A` and `B` are Boolean-valued.

The proof applies `IsSeparator` to reduce to
global elements and performs a case split via
`HasBoolDichotomy`. -/
theorem boolAnd_snd_proj
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hDich : HasBoolDichotomy C)
    {D : C} (A B : D ⟶ p.T)
    (hA : A ≫ isLeafEndo = A)
    (hB : B ≫ isLeafEndo = B) :
    cfpLift (cfpLift A B ≫ boolAnd) B ≫
      boolAnd =
    cfpLift A B ≫ boolAnd := by
  apply hSep.def
  intro e
  simp only [← Category.assoc]
  rw [cfpLift_precomp e, cfpLift_precomp e]
  set a := e ≫ A
  set b := e ≫ B
  have ha : a ≫ isLeafEndo = a := by
    change (e ≫ A) ≫ isLeafEndo = e ≫ A
    rw [Category.assoc, hA]
  have hb : b ≫ isLeafEndo = b := by
    change (e ≫ B) ≫ isLeafEndo = e ≫ B
    rw [Category.assoc, hB]
  have inner_eq :
      e ≫ cfpLift A B ≫ boolAnd =
      cfpLift a b ≫ boolAnd := by
    rw [← Category.assoc, cfpLift_precomp e]
  rw [inner_eq]
  have tf_eq :
      treeFalse (C := C) =
      cfpTerminalFrom cfpTerminal ≫
        treeFalse := by
    rw [cfpTerminalFrom_terminal,
      Category.id_comp]
  rcases hDich a ha with ha_val | ha_val <;>
    rcases hDich b hb with hb_val | hb_val <;>
    rw [ha_val, hb_val]
  · -- a = ℓ, b = ℓ
    rw [boolAnd_ℓ_ℓ, boolAnd_ℓ_ℓ]
  · -- a = ℓ, b = treeFalse
    rw [boolAnd_ℓ_treeFalse, tf_eq,
      boolAnd_treeFalse_left]
  · -- a = treeFalse, b = ℓ
    rw [tf_eq, boolAnd_treeFalse_left,
      boolAnd_treeFalse_left]
  · -- a = treeFalse, b = treeFalse
    rw [tf_eq, boolAnd_treeFalse_left,
      boolAnd_treeFalse_left]

end GebLean
