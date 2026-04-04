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

omit h p in
/-- Swapping commutes with diagonal `cfpMap`:
`cfpSwap ≫ cfpMap f f = cfpMap f f ≫ cfpSwap`. -/
theorem cfpSwap_cfpMap_diag
    [hh : HasChosenFiniteProducts C]
    {A B : C}
    (f : A ⟶ B) :
    cfpSwap A A ≫ cfpMap f f =
      cfpMap f f ≫ cfpSwap B B := by
  unfold cfpSwap
  rw [cfpLift_precomp]
  unfold cfpMap
  rw [cfpLift_precomp]
  congr 1 <;> (
    simp only [← Category.assoc,
      cfpLift_fst, cfpLift_snd]
  )

omit h p in
/-- Precomposing `cfpMap` with a composition
factors through an intermediate `cfpMap`. -/
theorem cfpMap_comp_comp
    [hh : HasChosenFiniteProducts C]
    {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ D)
    (f' : A ⟶ E) (g' : E ⟶ D) :
    cfpMap (f ≫ g) (f' ≫ g') =
    cfpMap f f' ≫ cfpMap g g' := by
  unfold cfpMap
  rw [cfpLift_precomp]
  apply cfpLift_uniq
  · simp only [← Category.assoc]
    rw [cfpLift_fst, cfpLift_fst]
  · simp only [← Category.assoc]
    rw [cfpLift_snd, cfpLift_snd]

/-! ## Tree destructors as endomorphisms -/

/-- Left destructor as endomorphism on T:
`treeLeftEndo(leaf) = leaf`,
`treeLeftEndo(branch(l, r)) = l`. -/
def treeLeftEndo : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    treeLeft

/-- Right destructor as endomorphism on T:
`treeRightEndo(leaf) = leaf`,
`treeRightEndo(branch(l, r)) = r`. -/
def treeRightEndo : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    treeRight

/-- Commutativity of `boolAnd` for Boolean-valued
arguments: if `A` and `B` are Boolean-valued
(i.e., `A ≫ isLeafEndo = A` and similarly for
`B`), then `cfpLift A B ≫ boolAnd =
cfpLift B A ≫ boolAnd`. -/
theorem boolAnd_comm_bool
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {D : C}
    (A B : D ⟶ p.T)
    (hA : A ≫ isLeafEndo = A)
    (hB : B ≫ isLeafEndo = B) :
    cfpLift A B ≫ boolAnd =
      cfpLift B A ≫
        (boolAnd :
          cfpProd p.T p.T ⟶ p.T) := by
  apply hSep.def
  intro e
  have eA_bool :
      (e ≫ A) ≫ isLeafEndo = e ≫ A := by
    rw [Category.assoc, hA]
  have eB_bool :
      (e ≫ B) ≫ isLeafEndo = e ≫ B := by
    rw [Category.assoc, hB]
  simp only [← Category.assoc,
    cfpLift_precomp e]
  rcases hBD (e ≫ A) eA_bool with ha | ha <;>
    rcases hBD (e ≫ B) eB_bool with hb | hb
  · rw [ha, hb]
  · rw [ha, hb, boolAnd_ℓ_treeFalse]
    have :
        cfpLift
          (cfpTerminalFrom cfpTerminal ≫
            treeFalse) p.ℓ ≫ boolAnd =
        cfpTerminalFrom cfpTerminal ≫
          treeFalse :=
      boolAnd_treeFalse_left _
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at this
    exact this.symm
  · rw [ha, hb]
    have h1 :
        cfpLift (treeFalse (C := C)) p.ℓ ≫
          boolAnd =
        treeFalse := by
      have :
          cfpLift
            (cfpTerminalFrom cfpTerminal ≫
              treeFalse) p.ℓ ≫ boolAnd =
          cfpTerminalFrom cfpTerminal ≫
            treeFalse :=
        boolAnd_treeFalse_left _
      rw [cfpTerminalFrom_terminal,
        Category.id_comp] at this
      exact this
    have h2 :
        cfpLift p.ℓ
          (treeFalse (C := C)) ≫
          boolAnd =
        treeFalse := boolAnd_ℓ_treeFalse
    rw [h1, h2]
  · rw [ha, hb]

/-- The first projection of `destructFold` is the
identity: `destructFold ≫ cfpFst T T = cfpSnd`. -/
theorem destructFold_cfpFst :
    destructFold ≫ cfpFst p.T p.T =
    cfpSnd cfpTerminal p.T := by
  rw [cfpSnd_eq_elim_ℓ_β]
  exact (p.elim_uniq p.ℓ p.β
    (destructFold ≫ cfpFst p.T p.T)
    (by rw [← Category.assoc, destructFold_ℓ,
          cfpLift_fst])
    (by
      rw [← Category.assoc
        (cfpMap (𝟙 cfpTerminal) p.β)
        destructFold (cfpFst p.T p.T),
        destructFold_β, Category.assoc
        (cfpLiftAssoc destructFold destructFold),
        cfpLift_fst]
      have hpre :
          cfpLiftAssoc destructFold
            destructFold ≫
            cfpLift
              (cfpFstFst p.T p.T p.T p.T)
              (cfpSndFst p.T p.T p.T p.T) =
          cfpLiftAssoc
            (destructFold ≫ cfpFst p.T p.T)
            (destructFold ≫
              cfpFst p.T p.T) := by
        unfold cfpLiftAssoc
        rw [cfpLift_precomp]
        congr 1
        · unfold cfpFstFst
          simp only [← Category.assoc,
            cfpLift_fst]
        · unfold cfpSndFst
          simp only [← Category.assoc,
            cfpLift_snd]
      simp only [← Category.assoc] at hpre ⊢
      rw [hpre]
    ))

/-- Beta-reduction for the left destructor:
`β ≫ treeLeftEndo = cfpFst T T`. -/
theorem β_treeLeftEndo :
    p.β ≫ treeLeftEndo =
    cfpFst p.T p.T := by
  unfold treeLeftEndo
  rw [← Category.assoc, cfpLift_precomp]
  have h1 : p.β ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom (cfpProd p.T p.T) :=
    h.terminal.uniq _
  rw [h1, Category.comp_id]
  have h2 :
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        p.β =
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    rw [cfpLift_cfpMap]
    simp only [Category.comp_id,
      Category.id_comp]
  rw [h2, Category.assoc, treeLeft_β]
  set sect :=
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (𝟙 (cfpProd p.T p.T))
  unfold cfpFstFst
  simp only [← Category.assoc]
  unfold cfpLiftAssoc
  rw [Category.assoc sect, cfpLift_fst]
  have sect_assocFst :
      sect ≫ cfpAssocFst cfpTerminal p.T p.T =
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        (cfpFst p.T p.T) := by
    unfold cfpAssocFst
    rw [cfpLift_precomp]
    congr 1
    · exact cfpLift_fst _ _
    · rw [← Category.assoc, cfpLift_snd,
        Category.id_comp]
  simp only [← Category.assoc]
    at sect_assocFst ⊢
  rw [sect_assocFst]
  simp only [Category.assoc]
  rw [destructFold_cfpFst, cfpLift_snd]

/-- The first projection of `destructFoldR` is the
identity:
`destructFoldR ≫ cfpFst T T = cfpSnd`. -/
theorem destructFoldR_cfpFst :
    destructFoldR ≫ cfpFst p.T p.T =
    cfpSnd cfpTerminal p.T := by
  rw [cfpSnd_eq_elim_ℓ_β]
  exact (p.elim_uniq p.ℓ p.β
    (destructFoldR ≫ cfpFst p.T p.T)
    (by rw [← Category.assoc,
          destructFoldR_ℓ, cfpLift_fst])
    (by
      rw [← Category.assoc
        (cfpMap (𝟙 cfpTerminal) p.β)
        destructFoldR (cfpFst p.T p.T),
        destructFoldR_β, Category.assoc
        (cfpLiftAssoc destructFoldR
          destructFoldR),
        cfpLift_fst]
      have hpre :
          cfpLiftAssoc destructFoldR
            destructFoldR ≫
            cfpLift
              (cfpFstFst p.T p.T p.T p.T)
              (cfpSndFst p.T p.T p.T p.T) =
          cfpLiftAssoc
            (destructFoldR ≫ cfpFst p.T p.T)
            (destructFoldR ≫
              cfpFst p.T p.T) := by
        unfold cfpLiftAssoc
        rw [cfpLift_precomp]
        congr 1
        · unfold cfpFstFst
          simp only [← Category.assoc,
            cfpLift_fst]
        · unfold cfpSndFst
          simp only [← Category.assoc,
            cfpLift_snd]
      simp only [← Category.assoc] at hpre ⊢
      rw [hpre]
    ))

/-- Beta-reduction for the right destructor:
`β ≫ treeRightEndo = cfpSnd T T`. -/
theorem β_treeRightEndo :
    p.β ≫ treeRightEndo =
    cfpSnd p.T p.T := by
  unfold treeRightEndo
  rw [← Category.assoc, cfpLift_precomp]
  have h1 : p.β ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom (cfpProd p.T p.T) :=
    h.terminal.uniq _
  rw [h1, Category.comp_id]
  have h2 :
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        p.β =
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    rw [cfpLift_cfpMap]
    simp only [Category.comp_id,
      Category.id_comp]
  rw [h2, Category.assoc, treeRight_β]
  set sect :=
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (𝟙 (cfpProd p.T p.T))
  unfold cfpSndFst
  simp only [← Category.assoc]
  unfold cfpLiftAssoc
  rw [Category.assoc sect, cfpLift_snd]
  have sect_assocSnd :
      sect ≫
        cfpAssocSnd cfpTerminal p.T p.T =
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        (cfpSnd p.T p.T) := by
    unfold cfpAssocSnd
    rw [cfpLift_precomp]
    congr 1
    · exact cfpLift_fst _ _
    · rw [← Category.assoc, cfpLift_snd,
        Category.id_comp]
  rw [← Category.assoc sect, sect_assocSnd,
    Category.assoc, destructFoldR_cfpFst,
    cfpLift_snd]

/-- Unary zero as a morphism: the leaf.  A unary
natural number `n` is represented as the tree
`branch(leaf, branch(leaf, ... branch(leaf, leaf)))`
with `n` outer branches; the number `0` is just
`leaf`. -/
def natZero :
    cfpTerminal (C := C) ⟶ p.T := p.ℓ

/-- Unary successor as an endomorphism: sends a
tree `n` to `branch(leaf, n)`.  Composed with the
unary-nat encoding, this maps the representation of
`n` to the representation of `n + 1`. -/
def natSucc : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T ≫ p.ℓ) (𝟙 p.T) ≫
    p.β

/-- Unary addition on the tree type.  The second
component is folded as a unary natural number; the
first component serves as the accumulator.  The
recursion is:
`natPlus(m, leaf) = m` and
`natPlus(m, branch(_, n')) = natSucc(natPlus(m, n'))`
-- correct under the unary encoding because then the
step ignores the recursive result corresponding to
the always-leaf left subtree. -/
def natPlus : cfpProd p.T p.T ⟶ p.T :=
  p.elim (𝟙 p.T) (cfpSnd p.T p.T ≫ natSucc)

/-- Leaf computation rule for `natPlus`:
`natPlus(m, leaf) = m`. -/
theorem natPlus_ℓ :
    cfpInsertSnd p.ℓ p.T ≫ natPlus = 𝟙 p.T := by
  unfold natPlus
  exact p.elim_ℓ (𝟙 p.T) _

/-- Branch computation rule for `natPlus`:
`natPlus(m, branch(l, r)) = natSucc(natPlus(m, r))`
under the unary encoding (where `l = leaf`). -/
theorem natPlus_β :
    cfpMap (𝟙 p.T) p.β ≫ natPlus =
    cfpLiftAssoc natPlus natPlus ≫
      (cfpSnd p.T p.T ≫ natSucc) := by
  unfold natPlus
  exact p.elim_β (𝟙 p.T) _

/-- Parameterized tree-size morphism.  Folds a tree
into its size (as a unary natural number): leaves
become `natZero`, and a branch with recursive sizes
`(sl, sr)` becomes `natSucc(natPlus(sl, sr))`. -/
def treeSizeParam :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  p.elim p.ℓ (natPlus ≫ natSucc)

/-- Tree size as an endomorphism on `T`.  Computes
the number of branches in the tree, represented as a
unary natural number (also a tree). -/
def treeSize : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    treeSizeParam

/-- Leaf computation rule for `treeSizeParam`:
`treeSizeParam(*, leaf) = natZero`. -/
theorem treeSizeParam_ℓ :
    cfpInsertSnd p.ℓ cfpTerminal ≫
      treeSizeParam = p.ℓ := by
  unfold treeSizeParam
  exact p.elim_ℓ p.ℓ _

/-- Branch computation rule for `treeSizeParam`:
`treeSizeParam(*, branch(l, r)) =
 natSucc(natPlus(treeSizeParam(*, l),
                 treeSizeParam(*, r)))`. -/
theorem treeSizeParam_β :
    cfpMap (𝟙 cfpTerminal) p.β ≫
      treeSizeParam =
    cfpLiftAssoc treeSizeParam treeSizeParam ≫
      (natPlus ≫ natSucc) := by
  unfold treeSizeParam
  exact p.elim_β p.ℓ _

/-- Iterate a morphism `f : T ⟶ T` a unary-nat
number of times.  `iterNat f` takes the pair
`(init, n)` and returns `f^n(init)`, where the
second component `n` is interpreted as a unary
natural number.  The recursion is:
`iterNat f (init, leaf) = init` (zero iterations)
and `iterNat f (init, branch(_, n')) =
  f (iterNat f (init, n'))` (one more iteration). -/
def iterNat (f : p.T ⟶ p.T) :
    cfpProd p.T p.T ⟶ p.T :=
  p.elim (𝟙 p.T) (cfpSnd p.T p.T ≫ f)

/-- Zero-iteration rule for `iterNat`:
`iterNat f (init, leaf) = init`. -/
theorem iterNat_ℓ (f : p.T ⟶ p.T) :
    cfpInsertSnd p.ℓ p.T ≫ iterNat f = 𝟙 p.T := by
  unfold iterNat
  exact p.elim_ℓ (𝟙 p.T) _

/-- Successor-iteration rule for `iterNat`:
`iterNat f (init, branch(l, r)) =
  f (iterNat f (init, r))` under the unary encoding
(where `l = leaf`). -/
theorem iterNat_β (f : p.T ⟶ p.T) :
    cfpMap (𝟙 p.T) p.β ≫ iterNat f =
    cfpLiftAssoc (iterNat f) (iterNat f) ≫
      (cfpSnd p.T p.T ≫ f) := by
  unfold iterNat
  exact p.elim_β (𝟙 p.T) _

/-- If-then-else helper combining three morphisms
with a common domain into a single conditional
morphism.  `iteBranches thn els cnd` returns `thn`
when `cnd` evaluates to leaf and `els` when `cnd`
evaluates to a branch. -/
def iteBranches {D : C}
    (thn els cnd : D ⟶ p.T) : D ⟶ p.T :=
  cfpLift (cfpLift thn els) cnd ≫ treeIte

/-- Branch-case computation rule for `iteBranches`:
if the condition factors through `p.β`, the result
is the else branch. -/
theorem iteBranches_β {D : C}
    (thn els : D ⟶ p.T)
    (r : D ⟶ cfpProd p.T p.T) :
    iteBranches thn els (r ≫ p.β) = els := by
  unfold iteBranches
  exact treeIte_β_applied thn els r

/-- Leaf-case computation rule for `iteBranches`:
if the condition factors through `p.ℓ` via the
terminal morphism, the result is the then branch. -/
theorem iteBranches_ℓ {D : C}
    (thn els : D ⟶ p.T) :
    iteBranches thn els
      (cfpTerminalFrom D ≫ p.ℓ) = thn := by
  unfold iteBranches
  have factor :
      cfpLift (cfpLift thn els)
        (cfpTerminalFrom D ≫ p.ℓ) =
      cfpLift thn els ≫
        cfpInsertSnd p.ℓ (cfpProd p.T p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm
  rw [factor, Category.assoc, treeIte_ℓ,
    cfpLift_fst]

/-- Pre-composition distributes through
`iteBranches`. -/
theorem iteBranches_precomp {D E : C}
    (s : E ⟶ D)
    (thn els cnd : D ⟶ p.T) :
    s ≫ iteBranches thn els cnd =
    iteBranches (s ≫ thn) (s ≫ els)
      (s ≫ cnd) := by
  unfold iteBranches
  rw [← Category.assoc, cfpLift_precomp,
    cfpLift_precomp]

/-- Constructor helper: given two morphisms into
`p.T`, produces the branch pair as a single
morphism into `p.T`.  Encodes `branch(f, g)`. -/
def mkBranch {D : C} (f g : D ⟶ p.T) : D ⟶ p.T :=
  cfpLift f g ≫ p.β

/-- The leaf constant as a morphism from any
object, obtained by composing with the unique
morphism to the terminal object. -/
def leafConst (D : C) : D ⟶ p.T :=
  cfpTerminalFrom D ≫ p.ℓ

/-- The `treeFalse` constant as a morphism from
any object. -/
def treeFalseConst (D : C) : D ⟶ p.T :=
  cfpTerminalFrom D ≫ treeFalse

/-- One step of the tree-equality comparison
procedure.  The input is an encoded state of the
form `branch(result, worklist)`, where `result` is
either `leaf` (still equal so far) or `treeFalse`
(mismatch detected), and `worklist` is a
right-spine list of pairs yet to compare.  The
output is the next state.

The step:
- If the worklist is empty (leaf), the state is
  unchanged.
- Otherwise, the head pair is `(a, b)` and the
  rest of the worklist follows.  If either of
  `a`, `b` is a leaf and the other is a branch,
  a mismatch is recorded and the worklist is
  cleared.  If both are leaves, the pair is
  consumed without changing `result`.  If both
  are branches, the pair is expanded into two
  child-pair comparisons that are prepended to
  the worklist. -/
def compareStep : p.T ⟶ p.T :=
  let state : p.T ⟶ p.T := 𝟙 p.T
  let result := treeLeftEndo
  let worklist := treeRightEndo
  let head := worklist ≫ treeLeftEndo
  let rest := worklist ≫ treeRightEndo
  let a := head ≫ treeLeftEndo
  let b := head ≫ treeRightEndo
  let al := a ≫ treeLeftEndo
  let ar := a ≫ treeRightEndo
  let bl := b ≫ treeLeftEndo
  let br := b ≫ treeRightEndo
  let matchOut := mkBranch result rest
  let mismatchOut :=
    mkBranch (treeFalseConst p.T)
      (leafConst p.T)
  let expandOut :=
    mkBranch result
      (mkBranch
        (mkBranch al bl)
        (mkBranch
          (mkBranch ar br)
          rest))
  let aIsLeafCase := iteBranches matchOut mismatchOut b
  let aIsBranchCase :=
    iteBranches mismatchOut expandOut b
  let workNonEmpty :=
    iteBranches aIsLeafCase aIsBranchCase a
  iteBranches state workNonEmpty worklist

/-- `β ≫ treeLeftEndo = cfpFst p.T p.T`:
left destructor applied to a branch pair. -/
theorem mkBranch_treeLeftEndo {D : C}
    (f g : D ⟶ p.T) :
    mkBranch f g ≫ treeLeftEndo = f := by
  unfold mkBranch
  rw [Category.assoc, β_treeLeftEndo,
    cfpLift_fst]

/-- `β ≫ treeRightEndo = cfpSnd p.T p.T`:
right destructor applied to a branch pair. -/
theorem mkBranch_treeRightEndo {D : C}
    (f g : D ⟶ p.T) :
    mkBranch f g ≫ treeRightEndo = g := by
  unfold mkBranch
  rw [Category.assoc, β_treeRightEndo,
    cfpLift_snd]

/-- Worklist-empty computation rule for
`compareStep`: if the state is encoded with an
empty worklist, the step acts as the identity. -/
theorem compareStep_leaf_wl {D : C}
    (r : D ⟶ p.T) :
    mkBranch r (leafConst D) ≫ compareStep =
    mkBranch r (leafConst D) := by
  unfold compareStep
  simp only
  rw [iteBranches_precomp]
  have h_wl :
      mkBranch r (leafConst D) ≫
        treeRightEndo = leafConst D := by
    rw [mkBranch_treeRightEndo]
  rw [h_wl]
  rw [Category.comp_id]
  exact iteBranches_ℓ _ _

/-- Precomposition of `leafConst`: for any
`s : E ⟶ D`, we have `s ≫ leafConst D =
leafConst E`. -/
theorem leafConst_precomp {D E : C}
    (s : E ⟶ D) :
    s ≫ leafConst D = leafConst E := by
  unfold leafConst
  rw [← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- Precomposition of `treeFalseConst`: for any
`s : E ⟶ D`, we have `s ≫ treeFalseConst D =
treeFalseConst E`. -/
theorem treeFalseConst_precomp {D E : C}
    (s : E ⟶ D) :
    s ≫ treeFalseConst D = treeFalseConst E := by
  unfold treeFalseConst
  rw [← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- Precomposition of `mkBranch`: for any
`s : E ⟶ D`, `s ≫ mkBranch f g =
mkBranch (s ≫ f) (s ≫ g)`. -/
theorem mkBranch_precomp {D E : C}
    (s : E ⟶ D) (f g : D ⟶ p.T) :
    s ≫ mkBranch f g =
    mkBranch (s ≫ f) (s ≫ g) := by
  unfold mkBranch
  rw [← Category.assoc, cfpLift_precomp]

/-- `ℓ ≫ treeLeftEndo = ℓ`: leaf is a fixed
point of `treeLeftEndo`. -/
theorem ℓ_treeLeftEndo :
    p.ℓ ≫ treeLeftEndo =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold treeLeftEndo
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
  exact treeLeft_ℓ

/-- `ℓ ≫ treeRightEndo = ℓ`: leaf is a fixed
point of `treeRightEndo`. -/
theorem ℓ_treeRightEndo :
    p.ℓ ≫ treeRightEndo =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
  unfold treeRightEndo
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
  exact treeRight_ℓ

/-- `leafConst D ≫ treeLeftEndo = leafConst D`:
the left destructor of a leaf is a leaf. -/
theorem leafConst_treeLeftEndo (D : C) :
    leafConst D ≫ treeLeftEndo = leafConst D := by
  unfold leafConst
  rw [Category.assoc, ℓ_treeLeftEndo]

/-- `leafConst D ≫ treeRightEndo = leafConst D`:
the right destructor of a leaf is a leaf. -/
theorem leafConst_treeRightEndo (D : C) :
    leafConst D ≫ treeRightEndo = leafConst D
    := by
  unfold leafConst
  rw [Category.assoc, ℓ_treeRightEndo]

/-- Match computation rule for `compareStep`:
if the head pair is `(leaf, leaf)`, the result
component is unchanged and the worklist becomes
the rest of the worklist. -/
theorem compareStep_match {D : C}
    (r rest : D ⟶ p.T) :
    mkBranch r
        (mkBranch
          (mkBranch (leafConst D) (leafConst D))
          rest)
      ≫ compareStep =
    mkBranch r rest := by
  unfold compareStep
  simp only
  rw [iteBranches_precomp]
  -- First reduce: state ≫ treeRightEndo = head::rest
  have h_wl :
      mkBranch r
          (mkBranch
            (mkBranch (leafConst D) (leafConst D))
            rest) ≫
        treeRightEndo =
      mkBranch
        (mkBranch (leafConst D) (leafConst D))
        rest := mkBranch_treeRightEndo _ _
  rw [h_wl]
  -- The worklist is a branch: apply the β rule.
  change iteBranches _ _
      (mkBranch
        (mkBranch (leafConst D) (leafConst D))
        rest) = _
  unfold mkBranch at *
  rw [iteBranches_β]
  simp only [iteBranches_precomp]
  -- Now compute each projection composed with
  -- the state morphism.
  set state := cfpLift r
    (cfpLift
      (cfpLift (leafConst D) (leafConst D) ≫
        p.β) rest ≫ p.β) ≫ p.β with hstate
  have h_wlR :
      state ≫ treeRightEndo =
      cfpLift
        (cfpLift (leafConst D) (leafConst D) ≫
          p.β) rest ≫ p.β := by
    rw [hstate, Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  have h_head :
      state ≫ treeRightEndo ≫ treeLeftEndo =
      cfpLift (leafConst D) (leafConst D) ≫
        p.β := by
    rw [← Category.assoc, h_wlR,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_a :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeLeftEndo = leafConst D := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_b :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeRightEndo = leafConst D := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  rw [h_a, h_b]
  unfold leafConst
  rw [iteBranches_ℓ, iteBranches_ℓ]
  -- Now the goal uses the then-branch: matchOut.
  -- Simplify state ≫ cfpLift treeLeftEndo
  -- (treeRightEndo ≫ treeRightEndo) ≫ p.β.
  rw [← Category.assoc, cfpLift_precomp]
  have h_l :
      state ≫ treeLeftEndo = r := by
    rw [hstate, Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_rr :
      state ≫ treeRightEndo ≫ treeRightEndo =
      rest := by
    rw [← Category.assoc, h_wlR,
      Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  rw [h_l, h_rr]

/-- Mismatch-left computation rule for
`compareStep`: if the head pair is
`(leaf, branch(l, r))`, the result becomes
`treeFalse` and the worklist is cleared. -/
theorem compareStep_mismatch_left {D : C}
    (r : D ⟶ p.T) (bl br rest : D ⟶ p.T) :
    mkBranch r
        (mkBranch
          (mkBranch (leafConst D) (mkBranch bl br))
          rest)
      ≫ compareStep =
    mkBranch (treeFalseConst D) (leafConst D)
    := by
  unfold compareStep
  simp only
  rw [iteBranches_precomp]
  have h_wl :
      mkBranch r
          (mkBranch
            (mkBranch (leafConst D)
              (mkBranch bl br))
            rest) ≫
        treeRightEndo =
      mkBranch
        (mkBranch (leafConst D) (mkBranch bl br))
        rest := mkBranch_treeRightEndo _ _
  rw [h_wl]
  change iteBranches _ _
      (mkBranch
        (mkBranch (leafConst D) (mkBranch bl br))
        rest) = _
  unfold mkBranch at *
  rw [iteBranches_β]
  simp only [iteBranches_precomp]
  set state := cfpLift r
    (cfpLift
      (cfpLift (leafConst D)
        (cfpLift bl br ≫ p.β) ≫ p.β) rest ≫ p.β)
    ≫ p.β with hstate
  have h_wlR :
      state ≫ treeRightEndo =
      cfpLift
        (cfpLift (leafConst D)
          (cfpLift bl br ≫ p.β) ≫ p.β) rest ≫
        p.β := by
    rw [hstate, Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  have h_head :
      state ≫ treeRightEndo ≫ treeLeftEndo =
      cfpLift (leafConst D)
        (cfpLift bl br ≫ p.β) ≫ p.β := by
    rw [← Category.assoc, h_wlR,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_a :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeLeftEndo = leafConst D := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_b :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeRightEndo =
      cfpLift bl br ≫ p.β := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  rw [h_a, h_b]
  unfold leafConst
  rw [iteBranches_ℓ]
  rw [iteBranches_β]
  rw [← Category.assoc, cfpLift_precomp,
    treeFalseConst_precomp,
    ← Category.assoc]
  have hstate_term :
      state ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom D :=
    h.terminal.uniq _
  rw [hstate_term]

/-- Mismatch-right computation rule for
`compareStep`: if the head pair is
`(branch(l, r), leaf)`, the result becomes
`treeFalse` and the worklist is cleared. -/
theorem compareStep_mismatch_right {D : C}
    (r : D ⟶ p.T) (al ar rest : D ⟶ p.T) :
    mkBranch r
        (mkBranch
          (mkBranch (mkBranch al ar)
            (leafConst D))
          rest)
      ≫ compareStep =
    mkBranch (treeFalseConst D) (leafConst D)
    := by
  unfold compareStep
  simp only
  rw [iteBranches_precomp]
  have h_wl :
      mkBranch r
          (mkBranch
            (mkBranch (mkBranch al ar)
              (leafConst D))
            rest) ≫
        treeRightEndo =
      mkBranch
        (mkBranch (mkBranch al ar)
          (leafConst D))
        rest := mkBranch_treeRightEndo _ _
  rw [h_wl]
  change iteBranches _ _
      (mkBranch
        (mkBranch (mkBranch al ar)
          (leafConst D))
        rest) = _
  unfold mkBranch at *
  rw [iteBranches_β]
  simp only [iteBranches_precomp]
  set state := cfpLift r
    (cfpLift
      (cfpLift (cfpLift al ar ≫ p.β)
        (leafConst D) ≫ p.β) rest ≫ p.β)
    ≫ p.β with hstate
  have h_wlR :
      state ≫ treeRightEndo =
      cfpLift
        (cfpLift (cfpLift al ar ≫ p.β)
          (leafConst D) ≫ p.β) rest ≫
        p.β := by
    rw [hstate, Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  have h_head :
      state ≫ treeRightEndo ≫ treeLeftEndo =
      cfpLift (cfpLift al ar ≫ p.β)
        (leafConst D) ≫ p.β := by
    rw [← Category.assoc, h_wlR,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_a :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeLeftEndo = cfpLift al ar ≫ p.β := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_b :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeRightEndo = leafConst D := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  rw [h_a, h_b]
  unfold leafConst
  rw [iteBranches_β]
  rw [iteBranches_ℓ]
  rw [← Category.assoc, cfpLift_precomp,
    treeFalseConst_precomp,
    ← Category.assoc]
  have hstate_term :
      state ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom D :=
    h.terminal.uniq _
  rw [hstate_term]

/-- Expand computation rule for `compareStep`:
if the head pair is
`(branch(al, ar), branch(bl, br))`, the result
component is unchanged and the worklist has the
two child pairs `(al, bl)` and `(ar, br)`
prepended. -/
theorem compareStep_expand {D : C}
    (r al ar bl br rest : D ⟶ p.T) :
    mkBranch r
        (mkBranch
          (mkBranch (mkBranch al ar)
            (mkBranch bl br))
          rest)
      ≫ compareStep =
    mkBranch r
      (mkBranch
        (mkBranch al bl)
        (mkBranch
          (mkBranch ar br)
          rest)) := by
  unfold compareStep
  simp only
  rw [iteBranches_precomp]
  have h_wl :
      mkBranch r
          (mkBranch
            (mkBranch (mkBranch al ar)
              (mkBranch bl br))
            rest) ≫
        treeRightEndo =
      mkBranch
        (mkBranch (mkBranch al ar)
          (mkBranch bl br))
        rest := mkBranch_treeRightEndo _ _
  rw [h_wl]
  change iteBranches _ _
      (mkBranch
        (mkBranch (mkBranch al ar)
          (mkBranch bl br))
        rest) = _
  unfold mkBranch at *
  rw [iteBranches_β]
  simp only [iteBranches_precomp]
  set state := cfpLift r
    (cfpLift
      (cfpLift (cfpLift al ar ≫ p.β)
        (cfpLift bl br ≫ p.β) ≫ p.β) rest ≫ p.β)
    ≫ p.β with hstate
  have h_wlR :
      state ≫ treeRightEndo =
      cfpLift
        (cfpLift (cfpLift al ar ≫ p.β)
          (cfpLift bl br ≫ p.β) ≫ p.β) rest ≫
        p.β := by
    rw [hstate, Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  have h_head :
      state ≫ treeRightEndo ≫ treeLeftEndo =
      cfpLift (cfpLift al ar ≫ p.β)
        (cfpLift bl br ≫ p.β) ≫ p.β := by
    rw [← Category.assoc, h_wlR,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_a :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeLeftEndo =
      cfpLift al ar ≫ p.β := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_b :
      state ≫ (treeRightEndo ≫ treeLeftEndo) ≫
        treeRightEndo =
      cfpLift bl br ≫ p.β := by
    rw [← Category.assoc, h_head,
      Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  rw [h_a, h_b]
  rw [iteBranches_β, iteBranches_β]
  -- Now compute all state-precomposed values in
  -- right-associated form (matching simp output).
  simp only [Category.assoc] at h_a h_b
  have h_l :
      state ≫ treeLeftEndo = r := by
    rw [hstate, Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_rr :
      state ≫ treeRightEndo ≫ treeRightEndo =
      rest := by
    rw [← Category.assoc, h_wlR,
      Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  have h_al :
      state ≫ treeRightEndo ≫ treeLeftEndo ≫
        treeLeftEndo ≫ treeLeftEndo = al := by
    rw [show state ≫ treeRightEndo ≫
      treeLeftEndo ≫ treeLeftEndo ≫ treeLeftEndo
      = (state ≫ treeRightEndo ≫ treeLeftEndo ≫
        treeLeftEndo) ≫ treeLeftEndo by
        simp only [Category.assoc],
      h_a, Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_ar :
      state ≫ treeRightEndo ≫ treeLeftEndo ≫
        treeLeftEndo ≫ treeRightEndo = ar := by
    rw [show state ≫ treeRightEndo ≫
      treeLeftEndo ≫ treeLeftEndo ≫
      treeRightEndo = (state ≫ treeRightEndo ≫
      treeLeftEndo ≫ treeLeftEndo) ≫
      treeRightEndo by
        simp only [Category.assoc],
      h_a, Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  have h_bl :
      state ≫ treeRightEndo ≫ treeLeftEndo ≫
        treeRightEndo ≫ treeLeftEndo = bl := by
    rw [show state ≫ treeRightEndo ≫
      treeLeftEndo ≫ treeRightEndo ≫
      treeLeftEndo = (state ≫ treeRightEndo ≫
      treeLeftEndo ≫ treeRightEndo) ≫
      treeLeftEndo by
        simp only [Category.assoc],
      h_b, Category.assoc, β_treeLeftEndo,
      cfpLift_fst]
  have h_br :
      state ≫ treeRightEndo ≫ treeLeftEndo ≫
        treeRightEndo ≫ treeRightEndo = br := by
    rw [show state ≫ treeRightEndo ≫
      treeLeftEndo ≫ treeRightEndo ≫
      treeRightEndo = (state ≫ treeRightEndo ≫
      treeLeftEndo ≫ treeRightEndo) ≫
      treeRightEndo by
        simp only [Category.assoc],
      h_b, Category.assoc, β_treeRightEndo,
      cfpLift_snd]
  -- The expandOut expression precomposed with
  -- state reduces to the desired output.
  simp only [← Category.assoc, cfpLift_precomp]
  simp only [Category.assoc]
  rw [h_l, h_al, h_ar, h_bl, h_br, h_rr]

/-- Tree equality as a morphism on pairs of
trees.  The construction:
- Forms the initial comparison state
  `branch(leaf, branch(branch(x, y), leaf))`
  encoding `result = leaf` (still-equal) and a
  singleton worklist containing the pair `(x, y)`.
- Uses the size of `branch(x, y)` as an iteration
  bound sufficient to exhaust the worklist.
- Applies `compareStep` repeatedly via
  `iterNat compareStep`.
- Extracts the result component of the final
  state and normalizes via `isLeafEndo` to yield
  a Boolean-valued tree (`leaf` for equal,
  `treeFalse` for unequal). -/
def treeEq : cfpProd p.T p.T ⟶ p.T :=
  let initState :
      cfpProd p.T p.T ⟶ p.T :=
    mkBranch
      (leafConst (cfpProd p.T p.T))
      (mkBranch p.β
        (leafConst (cfpProd p.T p.T)))
  let iterCount :
      cfpProd p.T p.T ⟶ p.T :=
    p.β ≫ treeSize
  cfpLift initState iterCount ≫
    iterNat compareStep ≫
    treeLeftEndo ≫
    isLeafEndo

/-- `natPlus(leaf, leaf) = leaf`: adding the unary
zero to itself gives zero. -/
theorem natPlus_ℓℓ :
    cfpLift p.ℓ p.ℓ ≫ natPlus =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
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
  rw [factor, Category.assoc, natPlus_ℓ,
    Category.comp_id]

/-- `natSucc(leaf) = treeFalse`: applying the
unary successor to zero gives the unary one,
which in the tree encoding is `branch(leaf, leaf)
= treeFalse`. -/
theorem natSucc_ℓ :
    p.ℓ ≫ natSucc =
    (treeFalse : cfpTerminal (C := C) ⟶ p.T)
    := by
  unfold natSucc treeFalse
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  rw [← Category.assoc p.ℓ
    (cfpTerminalFrom p.T) p.ℓ]
  have h1 : p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h1]
  rw [cfpTerminalFrom_terminal,
    Category.id_comp]

/-- `treeSizeParam(*, leaf)` with the unique
constant map, composed appropriately, equals
`p.ℓ`.  This is a specialization of
`treeSizeParam_ℓ` to a pair built via `cfpLift`
from the terminal morphism. -/
theorem treeSizeParam_cfpLift_ℓ :
    cfpLift
        (cfpTerminalFrom (cfpTerminal (C := C)))
        p.ℓ ≫ treeSizeParam = p.ℓ := by
  have rewrite_insertSnd :
      cfpLift
          (cfpTerminalFrom (cfpTerminal (C := C)))
          p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact cfpTerminalFrom_terminal
    · rw [cfpTerminalFrom_terminal,
        Category.id_comp]
  rw [rewrite_insertSnd]
  exact treeSizeParam_ℓ

/-- `treeSize(branch(ℓ, ℓ)) = treeFalse`: the
size of a two-leaf tree is the unary one,
represented in the tree encoding as
`branch(leaf, leaf)`. -/
theorem treeSize_treeFalse :
    treeFalse ≫ treeSize =
    (treeFalse : cfpTerminal (C := C) ⟶ p.T)
    := by
  unfold treeSize
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have h_term :
      treeFalse ≫
        cfpTerminalFrom (p.T : C) =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [h_term]
  -- The goal is now
  -- cfpLift (cfpTerminalFrom cfpTerminal)
  --   treeFalse ≫ treeSizeParam = treeFalse.
  unfold treeFalse
  have factor :
      cfpLift (cfpTerminalFrom cfpTerminal)
        (cfpLift p.ℓ p.ℓ ≫ p.β) =
      cfpLift (cfpTerminalFrom cfpTerminal)
        (cfpLift p.ℓ p.ℓ) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    unfold cfpMap
    rw [cfpLift_precomp]
    congr 1
    · rw [← Category.assoc, cfpLift_fst,
        Category.comp_id]
    · rw [← Category.assoc, cfpLift_snd]
  rw [factor, Category.assoc, treeSizeParam_β]
  unfold cfpLiftAssoc
  rw [← Category.assoc, cfpLift_precomp]
  -- Compute the two branches; both should give
  -- p.ℓ via treeSizeParam_cfpLift_ℓ.
  have h_fst :
      cfpLift (cfpTerminalFrom cfpTerminal)
        (cfpLift p.ℓ p.ℓ) ≫
        (cfpAssocFst cfpTerminal p.T p.T ≫
          treeSizeParam) = p.ℓ := by
    rw [← Category.assoc]
    unfold cfpAssocFst
    rw [cfpLift_precomp]
    rw [cfpLift_fst, ← Category.assoc,
      cfpLift_snd, cfpLift_fst]
    exact treeSizeParam_cfpLift_ℓ
  have h_snd :
      cfpLift (cfpTerminalFrom cfpTerminal)
        (cfpLift p.ℓ p.ℓ) ≫
        (cfpAssocSnd cfpTerminal p.T p.T ≫
          treeSizeParam) = p.ℓ := by
    rw [← Category.assoc]
    unfold cfpAssocSnd
    rw [cfpLift_precomp]
    rw [cfpLift_fst, ← Category.assoc,
      cfpLift_snd, cfpLift_snd]
    exact treeSizeParam_cfpLift_ℓ
  rw [h_fst, h_snd, ← Category.assoc,
    natPlus_ℓℓ, natSucc_ℓ]
  rfl

/-- Zero-iteration rule applied: for any
`init : D ⟶ p.T`, precomposing `init` with the
zero-count version of `iterNat` gives back
`init`. -/
theorem iterNat_cfpLift_ℓ {D : C}
    (f : p.T ⟶ p.T) (init : D ⟶ p.T) :
    cfpLift init (cfpTerminalFrom D ≫ p.ℓ)
      ≫ iterNat f = init := by
  have factor :
      cfpLift init
          (cfpTerminalFrom D ≫ p.ℓ) =
      init ≫ cfpInsertSnd p.ℓ p.T := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    have : init ≫ cfpTerminalFrom p.T =
        cfpTerminalFrom D :=
      h.terminal.uniq _
    rw [this]
  rw [factor, Category.assoc, iterNat_ℓ,
    Category.comp_id]

/-- One-iteration rule for `iterNat` with the
count `treeFalse = branch(leaf, leaf)`: applying
`iterNat f` once gives `init ≫ f`. -/
theorem iterNat_cfpLift_treeFalse {D : C}
    (f : p.T ⟶ p.T)
    (init : D ⟶ p.T) :
    cfpLift init (cfpTerminalFrom D ≫ treeFalse)
      ≫ iterNat f = init ≫ f := by
  unfold treeFalse
  have factor :
      cfpLift init
          (cfpTerminalFrom D ≫
            cfpLift p.ℓ p.ℓ ≫ p.β) =
      cfpLift init
          (cfpTerminalFrom D ≫
            cfpLift p.ℓ p.ℓ) ≫
        cfpMap (𝟙 p.T) p.β := by
    unfold cfpMap
    rw [cfpLift_precomp]
    simp only [← Category.assoc,
      cfpLift_fst, cfpLift_snd,
      Category.comp_id]
  rw [factor, Category.assoc, iterNat_β]
  unfold cfpLiftAssoc
  rw [← Category.assoc, cfpLift_precomp]
  have h_pair :
      cfpLift init
        (cfpTerminalFrom D ≫ cfpLift p.ℓ p.ℓ) =
      cfpLift init
        (cfpLift
          (cfpTerminalFrom D ≫ p.ℓ)
          (cfpTerminalFrom D ≫ p.ℓ)) := by
    congr 1
    rw [cfpLift_precomp]
  rw [h_pair]
  -- Compute both components via
  -- iterNat_cfpLift_ℓ.
  have h_fst_step :
      cfpLift init
          (cfpLift
            (cfpTerminalFrom D ≫ p.ℓ)
            (cfpTerminalFrom D ≫ p.ℓ)) ≫
        (cfpAssocFst p.T p.T p.T ≫ iterNat f) =
      init := by
    rw [← Category.assoc]
    unfold cfpAssocFst
    rw [cfpLift_precomp]
    rw [cfpLift_fst, ← Category.assoc,
      cfpLift_snd, cfpLift_fst]
    exact iterNat_cfpLift_ℓ f init
  have h_snd_step :
      cfpLift init
          (cfpLift
            (cfpTerminalFrom D ≫ p.ℓ)
            (cfpTerminalFrom D ≫ p.ℓ)) ≫
        (cfpAssocSnd p.T p.T p.T ≫ iterNat f) =
      init := by
    rw [← Category.assoc]
    unfold cfpAssocSnd
    rw [cfpLift_precomp]
    rw [cfpLift_fst, ← Category.assoc,
      cfpLift_snd, cfpLift_snd]
    exact iterNat_cfpLift_ℓ f init
  rw [h_fst_step, h_snd_step, ← Category.assoc,
    cfpLift_snd]

/-- Sanity-check computation rule for `treeEq`:
comparing two leaves yields `p.ℓ` (interpreted as
"true"). -/
theorem treeEq_ℓℓ :
    cfpLift p.ℓ p.ℓ ≫ treeEq = p.ℓ := by
  unfold treeEq
  simp only
  -- Distribute cfpLift p.ℓ p.ℓ through the
  -- initial cfpLift to build init state and
  -- iteration count.
  rw [← Category.assoc, cfpLift_precomp]
  -- First: compute initState applied to
  -- cfpLift p.ℓ p.ℓ.
  have h_init :
      cfpLift p.ℓ p.ℓ ≫
        mkBranch
          (leafConst (cfpProd p.T p.T))
          (mkBranch p.β
            (leafConst (cfpProd p.T p.T))) =
      mkBranch (leafConst cfpTerminal)
        (mkBranch treeFalse
          (leafConst cfpTerminal)) := by
    rw [mkBranch_precomp, leafConst_precomp,
      mkBranch_precomp, leafConst_precomp]
    rfl
  -- Second: compute iterCount.
  have h_count :
      cfpLift p.ℓ p.ℓ ≫ (p.β ≫ treeSize) =
      (treeFalse : cfpTerminal (C := C) ⟶ p.T)
      ≫ treeSize := by
    rw [← Category.assoc]
    rfl
  rw [h_init, h_count, treeSize_treeFalse]
  -- Apply the one-iteration rule specialized
  -- to D = cfpTerminal.
  have apply_iter :
      ∀ (init :
          cfpTerminal (C := C) ⟶ p.T),
      cfpLift init
          (treeFalse :
            cfpTerminal (C := C) ⟶ p.T)
        ≫ iterNat compareStep =
      init ≫ compareStep := by
    intro init
    have h_tf :
        (treeFalse :
          cfpTerminal (C := C) ⟶ p.T) =
        cfpTerminalFrom
          (cfpTerminal (C := C)) ≫
          treeFalse := by
      rw [cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [h_tf]
    exact iterNat_cfpLift_treeFalse
      (D := cfpTerminal (C := C))
      compareStep init
  rw [← Category.assoc (cfpLift _ _) _
    (treeLeftEndo ≫ isLeafEndo),
    apply_iter]
  -- Rewrite treeFalse (which appears as the
  -- worklist head) to mkBranch of leaf consts.
  have h_tf_mkBranch :
      (treeFalse : cfpTerminal (C := C) ⟶ p.T) =
      mkBranch (leafConst cfpTerminal)
        (leafConst cfpTerminal) := by
    unfold mkBranch leafConst treeFalse
    rw [cfpTerminalFrom_terminal,
      Category.id_comp]
  rw [h_tf_mkBranch]
  -- Now apply compareStep_match with
  -- r = leafConst, rest = leafConst.
  rw [compareStep_match]
  -- Now compute treeLeftEndo and isLeafEndo.
  rw [← Category.assoc, mkBranch_treeLeftEndo]
  unfold leafConst
  rw [Category.assoc, isLeafEndo_ℓ,
    cfpTerminalFrom_terminal, Category.id_comp]

/-- `treeEq` is Boolean-valued: postcomposing with
`isLeafEndo` leaves it unchanged.  The final stage
of `treeEq` is already `isLeafEndo`, so this
follows from the idempotence of `isLeafEndo`. -/
theorem treeEq_bool :
    treeEq ≫ isLeafEndo =
    (treeEq : cfpProd p.T p.T ⟶ p.T) := by
  unfold treeEq
  simp only [Category.assoc, isLeafEndo_idem]

/-- One additional iteration rule for `iterNat`:
applying `iterNat f` to `(init, count ≫ natSucc)`
equals applying `iterNat f` to `(init, count)` and
then post-composing with `f`. -/
theorem iterNat_cfpLift_succ {D : C}
    (f : p.T ⟶ p.T)
    (init count : D ⟶ p.T) :
    cfpLift init (count ≫ natSucc) ≫ iterNat f =
    (cfpLift init count ≫ iterNat f) ≫ f := by
  unfold natSucc
  -- Unfold natSucc and push through cfpLift.
  have rewrite_lift :
      cfpLift init
          (count ≫
            cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
              (𝟙 p.T) ≫ p.β) =
      cfpLift init
          (count ≫
            cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
              (𝟙 p.T)) ≫
        cfpMap (𝟙 p.T) p.β := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.assoc]
  rw [rewrite_lift, Category.assoc, iterNat_β]
  -- Normalize associativity rightward.
  simp only [Category.assoc]
  -- Simplify cfpLiftAssoc ≫ cfpSnd.
  have h1 :
      cfpLiftAssoc (iterNat f) (iterNat f) ≫
        (cfpSnd p.T p.T ≫ f) =
      cfpAssocSnd p.T p.T p.T ≫ iterNat f ≫ f := by
    unfold cfpLiftAssoc
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc]
  rw [h1]
  -- Simplify cfpLift init (count ≫ cfpLift _ _) ≫
  -- cfpAssocSnd T T T.
  have h2 :
      cfpLift init
          (count ≫
            cfpLift (cfpTerminalFrom p.T ≫ p.ℓ)
              (𝟙 p.T)) ≫
        cfpAssocSnd p.T p.T p.T =
      cfpLift init count := by
    unfold cfpAssocSnd
    rw [cfpLift_precomp]
    congr 1
    · rw [cfpLift_fst]
    · rw [← Category.assoc, cfpLift_snd,
        Category.assoc, cfpLift_snd,
        Category.comp_id]
  rw [← Category.assoc, h2]

/-- Iteration additivity for `iterNat`.  Viewing
`cfpProd (cfpProd p.T p.T) p.T` as holding
`((init, n), m)`, iterating `f` a total of
`natPlus(n, m)` steps starting at `init` equals
iterating `f` for `m` steps starting from the
result of iterating `f` for `n` steps starting at
`init`. -/
theorem iterNat_plus (f : p.T ⟶ p.T) :
    cfpLift
        (cfpFst (cfpProd p.T p.T) p.T ≫
          cfpFst p.T p.T)
        (cfpLift
          (cfpFst (cfpProd p.T p.T) p.T ≫
            cfpSnd p.T p.T)
          (cfpSnd (cfpProd p.T p.T) p.T) ≫
          natPlus) ≫
      iterNat f =
    cfpLift
        (cfpFst (cfpProd p.T p.T) p.T ≫ iterNat f)
        (cfpSnd (cfpProd p.T p.T) p.T) ≫
      iterNat f := by
  set A := cfpProd p.T p.T with hA_def
  -- Both sides will be shown equal to
  -- `p.elim (iterNat f) (cfpSnd p.T p.T ≫ f)`.
  set base : A ⟶ p.T := iterNat f with hbase
  set step : cfpProd p.T p.T ⟶ p.T :=
    cfpSnd p.T p.T ≫ f with hstep
  -- The RHS is `cfpMap (iterNat f) (𝟙 p.T) ≫
  -- iterNat f`, which by `elim_naturality` equals
  -- `p.elim (iterNat f) step`.
  have hRHS :
      cfpLift
          (cfpFst A p.T ≫ iterNat f)
          (cfpSnd A p.T) ≫
        iterNat f =
      p.elim base step := by
    have rewrite_cfpMap :
        cfpLift
            (cfpFst A p.T ≫ iterNat f)
            (cfpSnd A p.T) =
        cfpMap (iterNat f) (𝟙 p.T) := by
      unfold cfpMap
      rw [Category.comp_id]
    rw [rewrite_cfpMap]
    rw [hbase, hstep]
    unfold iterNat
    rw [elim_naturality, Category.comp_id]
  -- The LHS also equals `p.elim base step`, which
  -- we show by `elim_uniq`.
  suffices hLHS :
      cfpLift
          (cfpFst A p.T ≫ cfpFst p.T p.T)
          (cfpLift
            (cfpFst A p.T ≫ cfpSnd p.T p.T)
            (cfpSnd A p.T) ≫
            natPlus) ≫
        iterNat f =
      p.elim base step by
    rw [hLHS, ← hRHS]
  -- Introduce a name for the LHS morphism.
  set φ : cfpProd A p.T ⟶ p.T :=
    cfpLift
        (cfpFst A p.T ≫ cfpFst p.T p.T)
        (cfpLift
          (cfpFst A p.T ≫ cfpSnd p.T p.T)
          (cfpSnd A p.T) ≫
          natPlus) ≫
      iterNat f with hφ
  -- Base case equation for φ.
  have φ_base :
      cfpInsertSnd p.ℓ A ≫ φ = base := by
    rw [hφ, ← Category.assoc, cfpLift_precomp]
    have h_fst :
        cfpInsertSnd p.ℓ A ≫
          (cfpFst A p.T ≫ cfpFst p.T p.T) =
        cfpFst p.T p.T := by
      unfold cfpInsertSnd
      rw [← Category.assoc, cfpLift_fst,
        Category.id_comp]
    have h_snd :
        cfpInsertSnd p.ℓ A ≫
          (cfpLift
            (cfpFst A p.T ≫ cfpSnd p.T p.T)
            (cfpSnd A p.T) ≫
            natPlus) =
        cfpSnd p.T p.T := by
      rw [← Category.assoc, cfpLift_precomp]
      have h1 :
          cfpInsertSnd p.ℓ A ≫
            (cfpFst A p.T ≫ cfpSnd p.T p.T) =
          cfpSnd p.T p.T := by
        unfold cfpInsertSnd
        rw [← Category.assoc, cfpLift_fst,
          Category.id_comp]
      have h2 :
          cfpInsertSnd p.ℓ A ≫ cfpSnd A p.T =
          cfpTerminalFrom A ≫ p.ℓ := by
        unfold cfpInsertSnd
        rw [cfpLift_snd]
      rw [h1, h2]
      -- Goal:
      -- cfpLift (cfpSnd T T)
      --   (cfpTerminalFrom A ≫ p.ℓ) ≫ natPlus
      -- = cfpSnd T T.
      -- Rewrite as cfpSnd T T ≫ cfpInsertSnd p.ℓ p.T.
      have rew :
          cfpLift (cfpSnd p.T p.T)
              (cfpTerminalFrom A ≫ p.ℓ) =
          cfpSnd p.T p.T ≫
            cfpInsertSnd p.ℓ p.T := by
        unfold cfpInsertSnd
        rw [cfpLift_precomp, Category.comp_id]
        congr 1
        rw [← Category.assoc]
        congr 1
        exact (h.terminal.uniq _).symm
      rw [rew, Category.assoc, natPlus_ℓ,
        Category.comp_id]
    rw [h_fst, h_snd]
    -- Goal:
    -- cfpLift (cfpFst T T) (cfpSnd T T) ≫
    --   iterNat f = base.
    have h_id :
        cfpLift (cfpFst p.T p.T) (cfpSnd p.T p.T) =
        𝟙 (cfpProd p.T p.T) :=
      (cfpLift_uniq _ _ _
        (Category.id_comp _)
        (Category.id_comp _)).symm
    rw [h_id, Category.id_comp]
  -- Step case equation for φ.
  have φ_step :
      cfpMap (𝟙 A) p.β ≫ φ =
      cfpLiftAssoc φ φ ≫ step := by
    -- Name the "init projection" and the "count"
    -- morphism capturing natPlus(n, r).
    set init_part : cfpProd A (cfpProd p.T p.T) ⟶
        p.T :=
      cfpFst A (cfpProd p.T p.T) ≫ cfpFst p.T p.T
      with hinit_part
    set count : cfpProd A (cfpProd p.T p.T) ⟶
        p.T :=
      cfpLift
        (cfpFst A (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T)
        (cfpSnd A (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) ≫ natPlus
      with hcount
    -- Reshape LHS to apply iterNat_cfpLift_succ.
    have φ_reshape :
        cfpMap (𝟙 A) p.β ≫ φ =
        cfpLift init_part (count ≫ natSucc) ≫
          iterNat f := by
      rw [hφ, ← Category.assoc, cfpLift_precomp]
      -- Goal shape:
      -- cfpLift (cfpMap ≫ init_piece)
      --         (cfpMap ≫ snd_piece) ≫ iterNat f =
      -- cfpLift init_part (count ≫ natSucc) ≫
      --   iterNat f.
      -- Show the two inner cfpLifts are equal.
      have inner_eq :
          cfpLift
              (cfpMap (𝟙 A) p.β ≫
                (cfpFst A p.T ≫ cfpFst p.T p.T))
              (cfpMap (𝟙 A) p.β ≫
                (cfpLift
                  (cfpFst A p.T ≫ cfpSnd p.T p.T)
                  (cfpSnd A p.T) ≫ natPlus)) =
          cfpLift init_part (count ≫ natSucc) := by
        apply cfpLift_uniq
        · unfold cfpMap
          rw [cfpLift_fst, ← Category.assoc,
            cfpLift_fst, Category.assoc,
            Category.id_comp, hinit_part]
        · rw [cfpLift_snd, hcount, Category.assoc]
          have h_inner :
              cfpMap (𝟙 A) p.β ≫
                cfpLift
                  (cfpFst A p.T ≫ cfpSnd p.T p.T)
                  (cfpSnd A p.T) =
              cfpLift
                  (cfpFst A (cfpProd p.T p.T) ≫
                    cfpSnd p.T p.T)
                  (cfpSnd A (cfpProd p.T p.T)) ≫
                cfpMap (𝟙 p.T) p.β := by
            unfold cfpMap
            rw [cfpLift_precomp, cfpLift_precomp]
            apply cfpLift_uniq
            · rw [cfpLift_fst, ← Category.assoc,
                cfpLift_fst, Category.assoc,
                Category.id_comp, ← Category.assoc,
                cfpLift_fst, Category.assoc,
                Category.comp_id]
            · rw [cfpLift_snd, cfpLift_snd,
                ← Category.assoc, cfpLift_snd]
          rw [← Category.assoc, h_inner,
            Category.assoc, natPlus_β]
          -- Goal:
          --   cfpLift Y1 Y2 ≫ cfpLiftAssoc natPlus
          --     natPlus ≫ cfpSnd T T ≫ natSucc
          -- = cfpLift Z1 Z2 ≫ natPlus ≫ natSucc
          -- Re-associate to group cfpLiftAssoc with
          -- cfpSnd T T.
          rw [show
            cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T ≫ natSucc =
            (cfpLiftAssoc natPlus natPlus ≫
              cfpSnd p.T p.T) ≫ natSucc from
            (Category.assoc _ _ _).symm]
          -- Reduce cfpLiftAssoc ≫ cfpSnd.
          have hLA_snd :
              cfpLiftAssoc natPlus natPlus ≫
                cfpSnd p.T p.T =
              cfpAssocSnd p.T p.T p.T ≫ natPlus := by
            unfold cfpLiftAssoc
            rw [cfpLift_snd]
          rw [hLA_snd]
          -- Goal: cfpLift Y1 Y2 ≫
          --   (cfpAssocSnd T T T ≫ natPlus) ≫ natSucc
          -- = cfpLift Z1 Z2 ≫ natPlus ≫ natSucc.
          rw [show
            (cfpAssocSnd p.T p.T p.T ≫ natPlus) ≫
              natSucc =
            cfpAssocSnd p.T p.T p.T ≫
              natPlus ≫ natSucc from
            Category.assoc _ _ _]
          rw [show
            cfpLift
                (cfpFst A (cfpProd p.T p.T) ≫
                  cfpSnd p.T p.T)
                (cfpSnd A (cfpProd p.T p.T)) ≫
              cfpAssocSnd p.T p.T p.T ≫
                natPlus ≫ natSucc =
            (cfpLift
                (cfpFst A (cfpProd p.T p.T) ≫
                  cfpSnd p.T p.T)
                (cfpSnd A (cfpProd p.T p.T)) ≫
              cfpAssocSnd p.T p.T p.T) ≫
                natPlus ≫ natSucc from
            (Category.assoc _ _ _).symm]
          -- Now reduce cfpLift Y1 Y2 ≫ cfpAssocSnd.
          have hLY_assoc :
              cfpLift
                  (cfpFst A (cfpProd p.T p.T) ≫
                    cfpSnd p.T p.T)
                  (cfpSnd A (cfpProd p.T p.T)) ≫
                cfpAssocSnd p.T p.T p.T =
              cfpLift
                  (cfpFst A (cfpProd p.T p.T) ≫
                    cfpSnd p.T p.T)
                  (cfpSnd A (cfpProd p.T p.T) ≫
                    cfpSnd p.T p.T) := by
            unfold cfpAssocSnd
            rw [cfpLift_precomp]
            apply cfpLift_uniq
            · rw [cfpLift_fst, cfpLift_fst]
            · rw [cfpLift_snd, ← Category.assoc,
                cfpLift_snd]
          rw [hLY_assoc]
      rw [inner_eq]
    rw [φ_reshape, iterNat_cfpLift_succ]
    -- Show cfpLift init_part count ≫ iterNat f =
    -- cfpAssocSnd A T T ≫ φ.
    have h_assoc :
        cfpLift init_part count ≫ iterNat f =
        cfpAssocSnd A p.T p.T ≫ φ := by
      rw [hφ, ← Category.assoc]
      congr 1
      rw [cfpLift_precomp]
      apply cfpLift_uniq
      · rw [cfpLift_fst, hinit_part]
        unfold cfpAssocSnd
        rw [← Category.assoc, cfpLift_fst]
      · rw [cfpLift_snd, hcount,
          ← Category.assoc]
        congr 1
        unfold cfpAssocSnd
        rw [cfpLift_precomp]
        apply cfpLift_uniq
        · rw [cfpLift_fst, ← Category.assoc,
            cfpLift_fst]
        · rw [cfpLift_snd, cfpLift_snd]
    rw [h_assoc, Category.assoc]
    -- Goal: cfpAssocSnd A T T ≫ φ ≫ f =
    --       cfpLiftAssoc φ φ ≫ step
    rw [hstep]
    -- Reshape RHS: cfpLiftAssoc φ φ ≫ (cfpSnd ≫ f) =
    -- (cfpLiftAssoc φ φ ≫ cfpSnd) ≫ f.
    rw [show
      cfpLiftAssoc φ φ ≫ cfpSnd p.T p.T ≫ f =
      (cfpLiftAssoc φ φ ≫ cfpSnd p.T p.T) ≫ f from
      (Category.assoc _ _ _).symm]
    have hLA_snd_φ :
        cfpLiftAssoc φ φ ≫ cfpSnd p.T p.T =
        cfpAssocSnd A p.T p.T ≫ φ := by
      unfold cfpLiftAssoc
      rw [cfpLift_snd]
    rw [hLA_snd_φ, hφ]
    simp only [Category.assoc]
  exact p.elim_uniq base step φ φ_base φ_step

end GebLean
