import GebLean.TreePER
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Finite Limits for the PER Category

Constructs finite limits in the category of partial
equivalence relations (PERs) on the binary tree type T.

The terminal PER has the constantly-leaf relation,
making all elements related.  Products of PERs encode
pairs via the `branch` constructor, with the product
relation checking that both components are related.
Equalizers restrict the domain of the source PER to
elements on which two morphisms agree.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-! ## Terminal PER -/

/-- The relation for the terminal PER: constantly
leaf.  Every pair of elements is related. -/
def terminalPERRel :
    cfpProd p.T p.T ⟶ p.T :=
  cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ

/-- The terminal PER relation is Boolean-valued. -/
theorem terminalPERRel_bool :
    terminalPERRel ≫ isLeafEndo =
      (terminalPERRel :
        cfpProd p.T p.T ⟶ p.T) := by
  unfold terminalPERRel
  rw [Category.assoc, isLeafEndo_ℓ]

/-- The terminal PER relation is symmetric. -/
theorem terminalPERRel_symm :
    cfpSwap p.T p.T ≫ terminalPERRel =
      (terminalPERRel :
        cfpProd p.T p.T ⟶ p.T) := by
  unfold terminalPERRel
  rw [← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- Composing any morphism into the terminal PER
relation yields the constant leaf morphism. -/
theorem terminalPERRel_const
    {D : C}
    (f : D ⟶ cfpProd p.T p.T) :
    f ≫ terminalPERRel =
      cfpTerminalFrom D ≫ p.ℓ := by
  unfold terminalPERRel
  rw [← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- The terminal PER relation is transitive. -/
theorem terminalPERRel_trans :
    EqTransitive
      (terminalPERRel :
        cfpProd p.T p.T ⟶ p.T) := by
  unfold EqTransitive
  set T3 := cfpProd p.T (cfpProd p.T p.T)
  set c := cfpTerminalFrom T3 ≫ p.ℓ
  have h1 : cfpLift t3x t3z ≫ terminalPERRel =
      c := terminalPERRel_const _
  have h2 : cfpLift t3z t3y ≫ terminalPERRel =
      c := terminalPERRel_const _
  have h3 : cfpLift t3x t3y ≫ terminalPERRel =
      c := terminalPERRel_const _
  have boolAnd_cc :
      cfpLift c c ≫ boolAnd = c := by
    rw [← cfpLift_precomp (cfpTerminalFrom T3),
      Category.assoc, boolAnd_ℓ_ℓ]
  simp only [h1, h2, h3, boolAnd_cc]

/-- The terminal PER: all elements of T form a
single equivalence class.  The relation is
constantly leaf (true). -/
def terminalPERObj :
    @TreePERObj C _ h p where
  rel := terminalPERRel
  rel_bool := terminalPERRel_bool
  rel_symm := terminalPERRel_symm
  rel_trans := terminalPERRel_trans

/-! ## Terminal morphism -/

/-- The pre-morphism from any PER to the terminal
PER, using the identity as the underlying map. -/
def terminalPERPreMor
    (X : @TreePERObj C _ h p) :
    TreePERPreMor X terminalPERObj where
  map := 𝟙 p.T
  map_rel := by
    change cfpLift X.rel
      (cfpMap (𝟙 p.T) (𝟙 p.T) ≫
        terminalPERRel) ≫ boolAnd = X.rel
    rw [cfpMap_id, Category.id_comp]
    change cfpLift X.rel
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        p.ℓ) ≫ boolAnd = X.rel
    exact boolAnd_const_leaf_right X.rel_bool

/-- Any two pre-morphisms to the terminal PER
are equivalent: for any `e : D ⟶ T` in the
domain of X, `terminalPERRel(f(e), g(e)) = leaf`
since `terminalPERRel` is constantly leaf. -/
theorem terminalPERPreMor_unique
    {X : @TreePERObj C _ h p}
    (f g : TreePERPreMor X terminalPERObj) :
    treePERMorEqv f g := by
  intro D e _
  -- The target relation of terminalPERObj is
  -- terminalPERRel, which is constantly leaf.
  -- Any composition into it yields const_ℓ.
  unfold IsLeafConst
  -- terminalPERObj.rel = terminalPERRel
  -- by definition.
  change e ≫ cfpLift f.map g.map ≫
    terminalPERRel = cfpTerminalFrom D ≫ p.ℓ
  rw [← Category.assoc, terminalPERRel_const]

/-- The morphism from any PER to the terminal PER
in the PER category. -/
def terminalPERMor
    (X : @TreePERObj C _ h p) :
    TreePERMor X terminalPERObj :=
  Quotient.mk (treePERSetoid X terminalPERObj)
    (terminalPERPreMor X)

/-- The terminal morphism is unique: any morphism
`X ⟶ terminalPERObj` equals `terminalPERMor X`. -/
theorem terminalPERMor_unique
    {X : @TreePERObj C _ h p}
    (f : TreePERMor X terminalPERObj) :
    f = terminalPERMor X :=
  Quotient.ind
    (motive := fun f =>
      f = terminalPERMor X)
    (fun f' => by
      apply Quotient.sound
        (s := treePERSetoid X terminalPERObj)
      exact treePERMorEqv_symm
        (terminalPERPreMor_unique
          (terminalPERPreMor X) f'))
    f

/-- The terminal PER object is terminal in the
PER category. -/
def terminalPERObj_isTerminal :
    Limits.IsTerminal
      (terminalPERObj :
        @TreePERObj C _ h p) :=
  Limits.IsTerminal.ofUniqueHom
    terminalPERMor
    (fun _ m => terminalPERMor_unique m)

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

/-! ## Product PER -/

/-- The left-component relation check on a pair:
`leftRelCheck(X)(t₁, t₂) =
  X.rel(treeLeft(t₁), treeLeft(t₂))`. -/
def leftRelCheck
    (X : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  cfpMap treeLeftEndo treeLeftEndo ≫ X.rel

/-- The right-component relation check on a pair:
`rightRelCheck(Y)(t₁, t₂) =
  Y.rel(treeRight(t₁), treeRight(t₂))`. -/
def rightRelCheck
    (Y : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  cfpMap treeRightEndo treeRightEndo ≫ Y.rel

/-- The relation for the product PER of X and Y:
`prodPERRel(X,Y)(t₁, t₂) =
  boolAnd(X.rel(left(t₁), left(t₂)),
    Y.rel(right(t₁), right(t₂)))`.

The domain of the product consists of trees `t`
such that `left(t) ∈ dom(X)` and
`right(t) ∈ dom(Y)`. -/
def prodPERRel
    (X Y : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift (leftRelCheck X)
    (rightRelCheck Y) ≫ boolAnd

/-- The product PER relation is Boolean-valued. -/
theorem prodPERRel_bool
    (X Y : @TreePERObj C _ h p) :
    prodPERRel X Y ≫ isLeafEndo =
      prodPERRel X Y := by
  unfold prodPERRel
  rw [Category.assoc, boolAnd_output_boolean]

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

/-- Swap commutes with the left relation check:
`cfpSwap ≫ leftRelCheck X = leftRelCheck X`. -/
theorem cfpSwap_leftRelCheck
    (X : @TreePERObj C _ h p) :
    cfpSwap p.T p.T ≫ leftRelCheck X =
      leftRelCheck X := by
  unfold leftRelCheck
  rw [← Category.assoc,
    cfpSwap_cfpMap_diag treeLeftEndo,
    Category.assoc, X.rel_symm]

/-- Swap commutes with the right relation check:
`cfpSwap ≫ rightRelCheck Y = rightRelCheck Y`. -/
theorem cfpSwap_rightRelCheck
    (Y : @TreePERObj C _ h p) :
    cfpSwap p.T p.T ≫ rightRelCheck Y =
      rightRelCheck Y := by
  unfold rightRelCheck
  rw [← Category.assoc,
    cfpSwap_cfpMap_diag treeRightEndo,
    Category.assoc, Y.rel_symm]

/-- The product PER relation is symmetric. -/
theorem prodPERRel_symm
    (X Y : @TreePERObj C _ h p) :
    cfpSwap p.T p.T ≫ prodPERRel X Y =
      prodPERRel X Y := by
  unfold prodPERRel
  rw [← Category.assoc, cfpLift_precomp,
    cfpSwap_leftRelCheck, cfpSwap_rightRelCheck]

/-- `leftRelCheck X` is Boolean-valued. -/
theorem leftRelCheck_bool
    (X : @TreePERObj C _ h p) :
    leftRelCheck X ≫ isLeafEndo =
      leftRelCheck X := by
  unfold leftRelCheck
  rw [Category.assoc, X.rel_bool]

/-- `rightRelCheck Y` is Boolean-valued. -/
theorem rightRelCheck_bool
    (Y : @TreePERObj C _ h p) :
    rightRelCheck Y ≫ isLeafEndo =
      rightRelCheck Y := by
  unfold rightRelCheck
  rw [Category.assoc, Y.rel_bool]

/-- Applying a pair of morphisms to
`leftRelCheck X` yields X.rel on the
left-destructed components. -/
theorem leftRelCheck_proj
    (X : @TreePERObj C _ h p)
    {D : C}
    (a b : D ⟶ p.T) :
    cfpLift a b ≫ leftRelCheck X =
    cfpLift (a ≫ treeLeftEndo)
      (b ≫ treeLeftEndo) ≫ X.rel := by
  unfold leftRelCheck
  rw [← Category.assoc, ← cfpLift_cfpMap]

/-- Applying a pair of morphisms to
`rightRelCheck Y` yields Y.rel on the
right-destructed components. -/
theorem rightRelCheck_proj
    (Y : @TreePERObj C _ h p)
    {D : C}
    (a b : D ⟶ p.T) :
    cfpLift a b ≫ rightRelCheck Y =
    cfpLift (a ≫ treeRightEndo)
      (b ≫ treeRightEndo) ≫ Y.rel := by
  unfold rightRelCheck
  rw [← Category.assoc, ← cfpLift_cfpMap]

/-- Construct a triple `(left(x), left(y),
left(z))` from a triple `(x, y, z)` by applying
`treeLeftEndo` to each component. -/
def t3Left :
    cfpProd p.T (cfpProd p.T p.T) ⟶
    cfpProd p.T (cfpProd p.T p.T) :=
  cfpLift (t3x ≫ treeLeftEndo)
    (cfpLift (t3y ≫ treeLeftEndo)
      (t3z ≫ treeLeftEndo))

/-- Construct a triple `(right(x), right(y),
right(z))` from a triple `(x, y, z)` by applying
`treeRightEndo` to each component. -/
def t3Right :
    cfpProd p.T (cfpProd p.T p.T) ⟶
    cfpProd p.T (cfpProd p.T p.T) :=
  cfpLift (t3x ≫ treeRightEndo)
    (cfpLift (t3y ≫ treeRightEndo)
      (t3z ≫ treeRightEndo))

/-- Factoring `e ≫ cfpLift a b ≫ leftRelCheck X`
through `t3Left` and X.rel. -/
theorem leftRelCheck_factor
    (X : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T (cfpProd p.T p.T))
    (a b :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) :
    e ≫ cfpLift a b ≫ leftRelCheck X =
    e ≫ cfpLift (a ≫ treeLeftEndo)
      (b ≫ treeLeftEndo) ≫ X.rel := by
  rw [leftRelCheck_proj]

/-- Factoring `e ≫ cfpLift a b ≫ rightRelCheck Y`
through `t3Right` and Y.rel. -/
theorem rightRelCheck_factor
    (Y : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T (cfpProd p.T p.T))
    (a b :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) :
    e ≫ cfpLift a b ≫ rightRelCheck Y =
    e ≫ cfpLift (a ≫ treeRightEndo)
      (b ≫ treeRightEndo) ≫ Y.rel := by
  rw [rightRelCheck_proj]

/-- Precomposing `prodPERRel` with a cfpLift
yields the boolAnd of the component relation
checks. -/
theorem prodPERRel_precomp
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (X Y : @TreePERObj C _ h p) :
    e ≫ prodPERRel X Y =
    cfpLift (e ≫ leftRelCheck X)
      (e ≫ rightRelCheck Y) ≫ boolAnd := by
  unfold prodPERRel
  simp only [← Category.assoc]
  congr 1
  exact cfpLift_precomp e _ _

/-- Quantified transitivity for the product PER
relation: from `IsLeafConst` of the (x,z) and
(z,y) product relations, derive `IsLeafConst` of
the (x,y) product relation, using the component
PER transitivity. -/
theorem prodPERRel_quantTransitive
    (X Y : @TreePERObj C _ h p) :
    QuantTransitive (prodPERRel X Y) := by
  intro D e hxz hzy
  -- Step 1: Extract component IsLeafConst
  -- from the hypotheses.
  -- First, we need the hypotheses in terms of
  -- boolAnd of component checks (not prodPERRel).
  -- hxz : IsLeafConst
  --   (e ≫ cfpLift t3x t3z ≫ prodPERRel X Y)
  -- We rewrite to get
  --   IsLeafConst(boolAnd(lrc_xz, rrc_xz)).
  -- From boolAnd_fst_IsLeafConst:
  --   extract IsLeafConst(lrc_xz).
  -- From boolAnd_snd_IsLeafConst:
  --   extract IsLeafConst(rrc_xz).
  --
  -- The relation check after a cfpLift is Boolean:
  have lrc_bool_lift
      (a b : cfpProd p.T (cfpProd p.T p.T) ⟶
        p.T) :
      (cfpLift a b ≫ leftRelCheck X) ≫
        isLeafEndo =
      cfpLift a b ≫ leftRelCheck X := by
    rw [Category.assoc, leftRelCheck_bool]
  have rrc_bool_lift
      (a b : cfpProd p.T (cfpProd p.T p.T) ⟶
        p.T) :
      (cfpLift a b ≫ rightRelCheck Y) ≫
        isLeafEndo =
      cfpLift a b ≫ rightRelCheck Y := by
    rw [Category.assoc, rightRelCheck_bool]
  -- Expand the xz hypothesis.
  have prod_xz :
      cfpLift t3x t3z ≫ prodPERRel X Y =
      cfpLift
        (cfpLift t3x t3z ≫ leftRelCheck X)
        (cfpLift t3x t3z ≫ rightRelCheck Y) ≫
        boolAnd := by
    unfold prodPERRel
    rw [← Category.assoc,
      cfpLift_precomp (cfpLift t3x t3z)]
  have hxz' : IsLeafConst
      (e ≫ cfpLift
        (cfpLift t3x t3z ≫ leftRelCheck X)
        (cfpLift t3x t3z ≫ rightRelCheck Y) ≫
        boolAnd) := by
    unfold IsLeafConst at hxz ⊢
    rw [← Category.assoc, Category.assoc e,
      ← prod_xz]
    exact hxz
  have h_lxz : IsLeafConst
      (e ≫ cfpLift t3x t3z ≫
        leftRelCheck X) :=
    boolAnd_fst_IsLeafConst
      (lrc_bool_lift t3x t3z) e hxz'
  have h_rxz : IsLeafConst
      (e ≫ cfpLift t3x t3z ≫
        rightRelCheck Y) :=
    boolAnd_snd_IsLeafConst
      (rrc_bool_lift t3x t3z) e hxz'
  -- Expand the zy hypothesis.
  have prod_zy :
      cfpLift t3z t3y ≫ prodPERRel X Y =
      cfpLift
        (cfpLift t3z t3y ≫ leftRelCheck X)
        (cfpLift t3z t3y ≫ rightRelCheck Y) ≫
        boolAnd := by
    unfold prodPERRel
    rw [← Category.assoc,
      cfpLift_precomp (cfpLift t3z t3y)]
  have hzy' : IsLeafConst
      (e ≫ cfpLift
        (cfpLift t3z t3y ≫ leftRelCheck X)
        (cfpLift t3z t3y ≫ rightRelCheck Y) ≫
        boolAnd) := by
    unfold IsLeafConst at hzy ⊢
    rw [← Category.assoc, Category.assoc e,
      ← prod_zy]
    exact hzy
  have h_lzy : IsLeafConst
      (e ≫ cfpLift t3z t3y ≫
        leftRelCheck X) :=
    boolAnd_fst_IsLeafConst
      (lrc_bool_lift t3z t3y) e hzy'
  have h_rzy : IsLeafConst
      (e ≫ cfpLift t3z t3y ≫
        rightRelCheck Y) :=
    boolAnd_snd_IsLeafConst
      (rrc_bool_lift t3z t3y) e hzy'
  -- Step 2: Relate component checks to X.rel
  -- and Y.rel via t3Left/t3Right.
  -- t3Left ≫ cfpLift a b = cfpLift a b ≫
  --   cfpMap treeLeftEndo treeLeftEndo.
  -- factor_l: e ≫ cfpLift a b ≫ leftRelCheck X
  --   = (e ≫ t3Left) ≫ cfpLift a b ≫ X.rel.
  -- Proved for specific pairs using
  -- leftRelCheck_proj and projection lemmas.
  have factor_l
      (a b :
        cfpProd p.T (cfpProd p.T p.T) ⟶ p.T)
      (ha : t3Left ≫ a = a ≫ treeLeftEndo)
      (hb : t3Left ≫ b = b ≫ treeLeftEndo) :
      e ≫ cfpLift a b ≫ leftRelCheck X =
      (e ≫ t3Left) ≫ cfpLift a b ≫
        X.rel := by
    rw [leftRelCheck_proj]
    simp only [← Category.assoc]
    congr 1
    rw [← ha, ← hb, cfpLift_precomp]
    simp only [← Category.assoc]
    exact (cfpLift_precomp
      (e ≫ t3Left) a b).symm
  have factor_r
      (a b :
        cfpProd p.T (cfpProd p.T p.T) ⟶ p.T)
      (ha : t3Right ≫ a = a ≫ treeRightEndo)
      (hb : t3Right ≫ b = b ≫ treeRightEndo) :
      e ≫ cfpLift a b ≫ rightRelCheck Y =
      (e ≫ t3Right) ≫ cfpLift a b ≫
        Y.rel := by
    rw [rightRelCheck_proj]
    simp only [← Category.assoc]
    congr 1
    rw [← ha, ← hb, cfpLift_precomp]
    simp only [← Category.assoc]
    exact (cfpLift_precomp
      (e ≫ t3Right) a b).symm
  -- Projection lemmas for t3Left.
  have tL_x :
      (t3Left :
        cfpProd p.T (cfpProd p.T p.T) ⟶ _) ≫
        t3x = t3x ≫ treeLeftEndo := by
    unfold t3Left t3x; exact cfpLift_fst _ _
  have tL_y :
      (t3Left :
        cfpProd p.T (cfpProd p.T p.T) ⟶ _) ≫
        t3y = t3y ≫ treeLeftEndo := by
    unfold t3Left t3y
    rw [← Category.assoc, cfpLift_snd]
    exact cfpLift_fst _ _
  have tL_z :
      (t3Left :
        cfpProd p.T (cfpProd p.T p.T) ⟶ _) ≫
        t3z = t3z ≫ treeLeftEndo := by
    unfold t3Left t3z
    rw [← Category.assoc, cfpLift_snd]
    exact cfpLift_snd _ _
  -- Projection lemmas for t3Right.
  have tR_x :
      (t3Right :
        cfpProd p.T (cfpProd p.T p.T) ⟶ _) ≫
        t3x = t3x ≫ treeRightEndo := by
    unfold t3Right t3x; exact cfpLift_fst _ _
  have tR_y :
      (t3Right :
        cfpProd p.T (cfpProd p.T p.T) ⟶ _) ≫
        t3y = t3y ≫ treeRightEndo := by
    unfold t3Right t3y
    rw [← Category.assoc, cfpLift_snd]
    exact cfpLift_fst _ _
  have tR_z :
      (t3Right :
        cfpProd p.T (cfpProd p.T p.T) ⟶ _) ≫
        t3z = t3z ≫ treeRightEndo := by
    unfold t3Right t3z
    rw [← Category.assoc, cfpLift_snd]
    exact cfpLift_snd _ _
  -- Build hypotheses for rel_trans_prop.
  have h_lxz' : IsLeafConst
      ((e ≫ t3Left) ≫ cfpLift t3x t3z ≫
        X.rel) := by
    unfold IsLeafConst at h_lxz ⊢
    simp only [Category.assoc] at h_lxz ⊢
    rw [factor_l t3x t3z tL_x tL_z] at h_lxz
    simp only [Category.assoc] at h_lxz
    exact h_lxz
  have h_lzy' : IsLeafConst
      ((e ≫ t3Left) ≫ cfpLift t3z t3y ≫
        X.rel) := by
    unfold IsLeafConst at h_lzy ⊢
    simp only [Category.assoc] at h_lzy ⊢
    rw [factor_l t3z t3y tL_z tL_y] at h_lzy
    simp only [Category.assoc] at h_lzy
    exact h_lzy
  have h_rxz' : IsLeafConst
      ((e ≫ t3Right) ≫ cfpLift t3x t3z ≫
        Y.rel) := by
    unfold IsLeafConst at h_rxz ⊢
    simp only [Category.assoc] at h_rxz ⊢
    rw [factor_r t3x t3z tR_x tR_z] at h_rxz
    simp only [Category.assoc] at h_rxz
    exact h_rxz
  have h_rzy' : IsLeafConst
      ((e ≫ t3Right) ≫ cfpLift t3z t3y ≫
        Y.rel) := by
    unfold IsLeafConst at h_rzy ⊢
    simp only [Category.assoc] at h_rzy ⊢
    rw [factor_r t3z t3y tR_z tR_y] at h_rzy
    simp only [Category.assoc] at h_rzy
    exact h_rzy
  -- Step 3: Apply component transitivity.
  have h_lxy := X.rel_trans_prop
    (e ≫ t3Left) h_lxz' h_lzy'
  have h_rxy := Y.rel_trans_prop
    (e ≫ t3Right) h_rxz' h_rzy'
  -- Step 4: Convert back and recombine.
  have h_lxy' : IsLeafConst
      (e ≫ cfpLift t3x t3y ≫
        leftRelCheck X) := by
    unfold IsLeafConst at h_lxy ⊢
    simp only [Category.assoc] at h_lxy ⊢
    rw [factor_l t3x t3y tL_x tL_y]
    simp only [Category.assoc] at h_lxy ⊢
    exact h_lxy
  have h_rxy' : IsLeafConst
      (e ≫ cfpLift t3x t3y ≫
        rightRelCheck Y) := by
    unfold IsLeafConst at h_rxy ⊢
    simp only [Category.assoc] at h_rxy ⊢
    rw [factor_r t3x t3y tR_x tR_y]
    simp only [Category.assoc] at h_rxy ⊢
    exact h_rxy
  -- Recombine: boolAnd(ℓ, ℓ) = ℓ.
  unfold IsLeafConst at h_lxy' h_rxy' ⊢
  rw [← Category.assoc,
    prodPERRel_precomp
      (e ≫ cfpLift t3x t3y) X Y]
  simp only [Category.assoc]
  rw [h_lxy', h_rxy',
    ← cfpLift_precomp
      (cfpTerminalFrom D) p.ℓ p.ℓ,
    Category.assoc, boolAnd_ℓ_ℓ]

/-! ## Product PER (continued)

The remaining product PER constructions require
the terminal object to be a separator and the
PBTO to satisfy Boolean dichotomy, in order to
convert quantified transitivity to equational
transitivity. -/

/-- Equational transitivity for the product PER
relation, obtained from `quantTransitive_implies_eq`
applied to the quantified transitivity of the
product relation. -/
theorem prodPERRel_eqTransitive
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    (X Y : @TreePERObj C _ h p) :
    EqTransitive (prodPERRel X Y) :=
  quantTransitive_implies_eq hSep hBD
    (prodPERRel_bool X Y)
    (prodPERRel_quantTransitive X Y)

/-- The product PER of X and Y: trees `t` with
`left(t) ∈ dom(X)` and `right(t) ∈ dom(Y)`,
related componentwise. -/
def prodPERObj
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    (X Y : @TreePERObj C _ h p) :
    @TreePERObj C _ h p where
  rel := prodPERRel X Y
  rel_bool := prodPERRel_bool X Y
  rel_symm := prodPERRel_symm X Y
  rel_trans := prodPERRel_eqTransitive hSep hBD X Y

/-! ## Product projections -/

/-- The left projection pre-morphism from the product
PER to X: the underlying map is `treeLeftEndo`. -/
def prodPERFstPreMor
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    (X Y : @TreePERObj C _ h p) :
    TreePERPreMor (prodPERObj hSep hBD X Y) X where
  map := treeLeftEndo
  map_rel := by
    -- Goal: cfpLift (prodPERRel X Y)
    --   (cfpMap treeLeftEndo treeLeftEndo ≫ X.rel)
    --   ≫ boolAnd = prodPERRel X Y
    -- Since cfpMap treeLeftEndo treeLeftEndo ≫ X.rel
    --   = leftRelCheck X (by definition),
    -- and prodPERRel X Y
    --   = cfpLift (leftRelCheck X)
    --       (rightRelCheck Y) ≫ boolAnd,
    -- this is boolAnd_fst_proj.
    change cfpLift (prodPERRel X Y)
      (leftRelCheck X) ≫ boolAnd =
      prodPERRel X Y
    unfold prodPERRel
    exact boolAnd_fst_proj hSep hBD
      (leftRelCheck X) (rightRelCheck Y)
      (leftRelCheck_bool X) (rightRelCheck_bool Y)

/-- The right projection pre-morphism from the
product PER to Y: the underlying map is
`treeRightEndo`. -/
def prodPERSndPreMor
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    (X Y : @TreePERObj C _ h p) :
    TreePERPreMor (prodPERObj hSep hBD X Y) Y where
  map := treeRightEndo
  map_rel := by
    change cfpLift (prodPERRel X Y)
      (rightRelCheck Y) ≫ boolAnd =
      prodPERRel X Y
    unfold prodPERRel
    exact boolAnd_snd_proj hSep hBD
      (leftRelCheck X) (rightRelCheck Y)
      (leftRelCheck_bool X) (rightRelCheck_bool Y)

/-- The left projection morphism in the PER
category. -/
def prodPERFst
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    (X Y : @TreePERObj C _ h p) :
    TreePERMor (prodPERObj hSep hBD X Y) X :=
  Quotient.mk
    (treePERSetoid
      (prodPERObj hSep hBD X Y) X)
    (prodPERFstPreMor hSep hBD X Y)

/-- The right projection morphism in the PER
category. -/
def prodPERSnd
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    (X Y : @TreePERObj C _ h p) :
    TreePERMor (prodPERObj hSep hBD X Y) Y :=
  Quotient.mk
    (treePERSetoid
      (prodPERObj hSep hBD X Y) Y)
    (prodPERSndPreMor hSep hBD X Y)

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
      -- Goal:
      -- cfpLiftAssoc destructFold destructFold ≫
      --   cfpLift cfpFstFst cfpSndFst ≫ β
      -- = cfpLiftAssoc (destructFold ≫ cfpFst)
      --   (destructFold ≫ cfpFst) ≫ β
      -- Suffices to show the prefixes match.
      have hpre :
          cfpLiftAssoc destructFold destructFold ≫
            cfpLift
              (cfpFstFst p.T p.T p.T p.T)
              (cfpSndFst p.T p.T p.T p.T) =
          cfpLiftAssoc
            (destructFold ≫ cfpFst p.T p.T)
            (destructFold ≫ cfpFst p.T p.T) := by
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
  -- Goal: cfpLift (cfpTerminalFrom (T×T)) β ≫
  --   treeLeft = cfpFst T T
  -- Factor through cfpMap (𝟙 cfpTerminal) β.
  have h2 :
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        p.β =
      cfpLift
        (cfpTerminalFrom (cfpProd p.T p.T))
        (𝟙 (cfpProd p.T p.T)) ≫
        cfpMap (𝟙 cfpTerminal) p.β := by
    rw [cfpLift_cfpMap]
    simp only [Category.comp_id, Category.id_comp]
  rw [h2, Category.assoc, treeLeft_β]
  -- Goal: sect ≫ cfpLiftAssoc dF dF ≫
  --   cfpFstFst T T T T = cfpFst T T
  -- where sect = cfpLift (cfpTerminalFrom _)
  --   (𝟙 _).
  -- Reassociate and factor.
  set sect :=
    cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T))
      (𝟙 (cfpProd p.T p.T))
  unfold cfpFstFst
  simp only [← Category.assoc]
  -- Now fully left-associated.
  -- cfpLiftAssoc ≫ cfpFst (T×T) (T×T) =
  -- cfpAssocFst ≫ destructFold (by cfpLift_fst).
  unfold cfpLiftAssoc
  -- Left-associated at this point.
  -- Re-associate to apply cfpLift_fst.
  rw [Category.assoc sect, cfpLift_fst]
  -- Goal: sect ≫ cfpAssocFst ≫ destructFold ≫
  --   cfpFst T T = cfpFst T T
  have sect_assocFst :
      sect ≫ cfpAssocFst cfpTerminal p.T p.T =
      cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
        (cfpFst p.T p.T) := by
    unfold cfpAssocFst
    rw [cfpLift_precomp]
    congr 1
    · exact cfpLift_fst _ _
    · rw [← Category.assoc, cfpLift_snd,
        Category.id_comp]
  simp only [← Category.assoc] at sect_assocFst ⊢
  rw [sect_assocFst]
  simp only [Category.assoc]
  rw [destructFold_cfpFst, cfpLift_snd]

/-- The first projection of `destructFoldR` is the
identity: `destructFoldR ≫ cfpFst T T = cfpSnd`. -/
theorem destructFoldR_cfpFst :
    destructFoldR ≫ cfpFst p.T p.T =
    cfpSnd cfpTerminal p.T := by
  rw [cfpSnd_eq_elim_ℓ_β]
  exact (p.elim_uniq p.ℓ p.β
    (destructFoldR ≫ cfpFst p.T p.T)
    (by rw [← Category.assoc, destructFoldR_ℓ,
          cfpLift_fst])
    (by
      rw [← Category.assoc
        (cfpMap (𝟙 cfpTerminal) p.β)
        destructFoldR (cfpFst p.T p.T),
        destructFoldR_β, Category.assoc
        (cfpLiftAssoc destructFoldR destructFoldR),
        cfpLift_fst]
      have hpre :
          cfpLiftAssoc destructFoldR
            destructFoldR ≫
            cfpLift
              (cfpFstFst p.T p.T p.T p.T)
              (cfpSndFst p.T p.T p.T p.T) =
          cfpLiftAssoc
            (destructFoldR ≫ cfpFst p.T p.T)
            (destructFoldR ≫ cfpFst p.T p.T) := by
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
    simp only [Category.comp_id, Category.id_comp]
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
      sect ≫ cfpAssocSnd cfpTerminal p.T p.T =
      cfpLift (cfpTerminalFrom (cfpProd p.T p.T))
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

/-! ## Product pairing -/

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

/-- The pairing pre-morphism from Z to the product
PER of X and Y, given morphisms `f : Z → X` and
`g : Z → Y`.  The underlying map is
`cfpLift f.map g.map ≫ β`. -/
def prodPERPairPreMor
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (f : TreePERPreMor Z X)
    (g : TreePERPreMor Z Y) :
    TreePERPreMor Z
      (prodPERObj hSep hBD X Y) where
  map := cfpLift f.map g.map ≫ p.β
  map_rel := by
    -- Reduce cfpMap (pair) (pair) ≫ prodPERRel
    -- to boolAnd(cfpMap f f ≫ X.rel,
    --            cfpMap g g ≫ Y.rel).
    change cfpLift Z.rel
      (cfpMap (cfpLift f.map g.map ≫ p.β)
        (cfpLift f.map g.map ≫ p.β) ≫
        prodPERRel X Y) ≫ boolAnd = Z.rel
    -- Expand prodPERRel and push cfpMap through.
    unfold prodPERRel
    -- cfpMap pair pair ≫ cfpLift lrc rrc ≫
    --   boolAnd.
    -- Push cfpMap through cfpLift using
    -- cfpLift_precomp.
    set pair := cfpLift f.map g.map ≫ p.β
    rw [← Category.assoc (cfpMap pair pair),
      cfpLift_precomp (cfpMap pair pair)]
    -- Simplify left component.
    unfold leftRelCheck
    rw [← Category.assoc (cfpMap pair pair)
      (cfpMap treeLeftEndo treeLeftEndo),
      ← cfpMap_comp_comp]
    rw [show pair ≫ treeLeftEndo = f.map from
      by rw [Category.assoc, β_treeLeftEndo,
        cfpLift_fst]]
    -- Simplify right component.
    unfold rightRelCheck
    rw [← Category.assoc (cfpMap pair pair)
      (cfpMap treeRightEndo treeRightEndo),
      ← cfpMap_comp_comp]
    rw [show pair ≫ treeRightEndo = g.map from
      by rw [Category.assoc, β_treeRightEndo,
        cfpLift_snd]]
    -- Goal: cfpLift Z.rel
    --   (cfpLift (cfpMap f.map f.map ≫ X.rel)
    --     (cfpMap g.map g.map ≫ Y.rel) ≫
    --     boolAnd) ≫ boolAnd = Z.rel
    rw [← boolAnd_assoc, f.map_rel, g.map_rel]

/-- The pairing morphism in the PER category. -/
def prodPERPair
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (f : TreePERMor Z X)
    (g : TreePERMor Z Y) :
    TreePERMor Z (prodPERObj hSep hBD X Y) :=
  Quotient.lift₂
    (s₁ := treePERSetoid Z X)
    (s₂ := treePERSetoid Z Y)
    (fun f' g' =>
      Quotient.mk
        (treePERSetoid Z
          (prodPERObj hSep hBD X Y))
        (prodPERPairPreMor hSep hBD f' g'))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply Quotient.sound
        (s := treePERSetoid Z
          (prodPERObj hSep hBD X Y))
      intro D e hdom
      -- hdom : IsLeafConst(e ≫ Z.rel(e, e)).
      -- From hf: f₁ ~ f₂, so
      --   IsLeafConst(e ≫ X.rel(f₁(e), f₂(e))).
      -- From hg: g₁ ~ g₂, so
      --   IsLeafConst(e ≫ Y.rel(g₁(e), g₂(e))).
      -- Need: IsLeafConst(e ≫
      --   prodPERRel(pair₁(e), pair₂(e))).
      -- pair_i(e) = β(f_i(e), g_i(e)).
      -- prodPERRel(β(f₁(e), g₁(e)), β(f₂(e), g₂(e)))
      -- = boolAnd(
      --     X.rel(left(β(f₁(e),g₁(e))),
      --           left(β(f₂(e),g₂(e)))),
      --     Y.rel(right(β(f₁(e),g₁(e))),
      --           right(β(f₂(e),g₂(e)))))
      -- = boolAnd(X.rel(f₁(e), f₂(e)),
      --           Y.rel(g₁(e), g₂(e))).
      -- This is IsLeafConst by hf, hg.
      -- Reduce prodPERRel to boolAnd of
      -- component relation checks.
      have map1 :
          (prodPERPairPreMor hSep hBD f₁ f₂).map =
          cfpLift f₁.map f₂.map ≫ p.β := rfl
      have map2 :
          (prodPERPairPreMor hSep hBD g₁ g₂).map =
          cfpLift g₁.map g₂.map ≫ p.β := rfl
      rw [map1, map2]
      change IsLeafConst
        (e ≫ cfpLift
          (cfpLift f₁.map f₂.map ≫ p.β)
          (cfpLift g₁.map g₂.map ≫ p.β) ≫
          prodPERRel X Y)
      unfold prodPERRel
      rw [← Category.assoc
        (cfpLift
          (cfpLift f₁.map f₂.map ≫ p.β)
          (cfpLift g₁.map g₂.map ≫ p.β)),
        cfpLift_precomp
          (cfpLift
            (cfpLift f₁.map f₂.map ≫ p.β)
            (cfpLift g₁.map g₂.map ≫ p.β))]
      -- Simplify left component.
      set pair1 :=
        cfpLift f₁.map f₂.map ≫ p.β
      set pair2 :=
        cfpLift g₁.map g₂.map ≫ p.β
      have lrc_simp :
          cfpLift pair1 pair2 ≫
            leftRelCheck X =
          cfpLift f₁.map g₁.map ≫ X.rel := by
        rw [leftRelCheck_proj]
        have h1 : pair1 ≫ treeLeftEndo =
            f₁.map := by
          rw [Category.assoc, β_treeLeftEndo,
            cfpLift_fst]
        have h2 : pair2 ≫ treeLeftEndo =
            g₁.map := by
          rw [Category.assoc, β_treeLeftEndo,
            cfpLift_fst]
        rw [h1, h2]
      -- Simplify right component.
      have rrc_simp :
          cfpLift pair1 pair2 ≫
            rightRelCheck Y =
          cfpLift f₂.map g₂.map ≫ Y.rel := by
        rw [rightRelCheck_proj]
        have h1 : pair1 ≫ treeRightEndo =
            f₂.map := by
          rw [Category.assoc, β_treeRightEndo,
            cfpLift_snd]
        have h2 : pair2 ≫ treeRightEndo =
            g₂.map := by
          rw [Category.assoc, β_treeRightEndo,
            cfpLift_snd]
        rw [h1, h2]
      rw [lrc_simp, rrc_simp]
      -- Goal: IsLeafConst(e ≫
      --   cfpLift (cfpLift f₁ g₁ ≫ X.rel)
      --     (cfpLift f₂ g₂ ≫ Y.rel) ≫ boolAnd)
      have h1 := hf e hdom
      have h2 := hg e hdom
      unfold IsLeafConst at h1 h2 ⊢
      rw [← Category.assoc, cfpLift_precomp,
        h1, h2,
        ← cfpLift_precomp
          (cfpTerminalFrom D) p.ℓ p.ℓ,
        Category.assoc, boolAnd_ℓ_ℓ]
    )
    f g

/-! ## Product beta laws -/

/-- The map of `pair(f, g) ≫ fst` equals `f.map`:
`(cfpLift f.map g.map ≫ β) ≫ treeLeftEndo
  = f.map`. -/
theorem prodPERPairFst_map
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (f : TreePERPreMor Z X)
    (g : TreePERPreMor Z Y) :
    (treePERPreMorComp
      (prodPERPairPreMor hSep hBD f g)
      (prodPERFstPreMor hSep hBD X Y)).map =
    f.map := by
  change (cfpLift f.map g.map ≫ p.β) ≫
    treeLeftEndo = f.map
  rw [Category.assoc, β_treeLeftEndo,
    cfpLift_fst]

/-- The map of `pair(f, g) ≫ snd` equals `g.map`:
`(cfpLift f.map g.map ≫ β) ≫ treeRightEndo
  = g.map`. -/
theorem prodPERPairSnd_map
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (f : TreePERPreMor Z X)
    (g : TreePERPreMor Z Y) :
    (treePERPreMorComp
      (prodPERPairPreMor hSep hBD f g)
      (prodPERSndPreMor hSep hBD X Y)).map =
    g.map := by
  change (cfpLift f.map g.map ≫ p.β) ≫
    treeRightEndo = g.map
  rw [Category.assoc, β_treeRightEndo,
    cfpLift_snd]

/-- Pre-morphism equality: if `f.map = g.map` then
`f = g` (since `map_rel` is proof-irrelevant). -/
theorem treePERPreMor_ext
    {X Y : @TreePERObj C _ h p}
    {f g : TreePERPreMor X Y}
    (h_map : f.map = g.map) :
    f = g := by
  cases f; cases g
  simp only [TreePERPreMor.mk.injEq]
  exact h_map

/-- First beta law in the PER category:
`pair(f, g) ≫ fst = f`. -/
theorem prodPERFst_comp_pair
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (f : TreePERMor Z X)
    (g : TreePERMor Z Y) :
    treePERMorComp
      (prodPERPair hSep hBD f g)
      (prodPERFst hSep hBD X Y) = f := by
  revert f g
  apply Quotient.ind
  intro f'
  apply Quotient.ind
  intro g'
  apply congr_arg
    (Quotient.mk (treePERSetoid Z X))
  exact treePERPreMor_ext
    (prodPERPairFst_map hSep hBD f' g')

/-- Second beta law in the PER category:
`pair(f, g) ≫ snd = g`. -/
theorem prodPERSnd_comp_pair
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (f : TreePERMor Z X)
    (g : TreePERMor Z Y) :
    treePERMorComp
      (prodPERPair hSep hBD f g)
      (prodPERSnd hSep hBD X Y) = g := by
  revert f g
  apply Quotient.ind
  intro f'
  apply Quotient.ind
  intro g'
  apply congr_arg
    (Quotient.mk (treePERSetoid Z Y))
  exact treePERPreMor_ext
    (prodPERPairSnd_map hSep hBD f' g')

/-! ## Product eta / uniqueness law -/

/-- The pairing map `cfpLift (m ≫ treeLeftEndo)
(m ≫ treeRightEndo) ≫ β` composed with
`treeLeftEndo` yields `m ≫ treeLeftEndo`. -/
theorem pairReconstruct_left
    (m : p.T ⟶ p.T) :
    (cfpLift (m ≫ treeLeftEndo)
      (m ≫ treeRightEndo) ≫ p.β) ≫
      treeLeftEndo = m ≫ treeLeftEndo := by
  rw [Category.assoc, β_treeLeftEndo,
    cfpLift_fst]

/-- The pairing map `cfpLift (m ≫ treeLeftEndo)
(m ≫ treeRightEndo) ≫ β` composed with
`treeRightEndo` yields `m ≫ treeRightEndo`. -/
theorem pairReconstruct_right
    (m : p.T ⟶ p.T) :
    (cfpLift (m ≫ treeLeftEndo)
      (m ≫ treeRightEndo) ≫ p.β) ≫
      treeRightEndo = m ≫ treeRightEndo := by
  rw [Category.assoc, β_treeRightEndo,
    cfpLift_snd]

/-- The reconstruct map applied to `leftRelCheck`
yields the same as the original map. -/
theorem reconstruct_leftRelCheck
    (X : @TreePERObj C _ h p)
    (m : p.T ⟶ p.T) :
    cfpLift
      (cfpLift (m ≫ treeLeftEndo)
        (m ≫ treeRightEndo) ≫ p.β) m ≫
      leftRelCheck X =
    cfpLift m m ≫ leftRelCheck X := by
  rw [leftRelCheck_proj, leftRelCheck_proj,
    pairReconstruct_left]

/-- The reconstruct map applied to `rightRelCheck`
yields the same as the original map. -/
theorem reconstruct_rightRelCheck
    (Y : @TreePERObj C _ h p)
    (m : p.T ⟶ p.T) :
    cfpLift
      (cfpLift (m ≫ treeLeftEndo)
        (m ≫ treeRightEndo) ≫ p.β) m ≫
      rightRelCheck Y =
    cfpLift m m ≫ rightRelCheck Y := by
  rw [rightRelCheck_proj, rightRelCheck_proj,
    pairReconstruct_right]

/-- The prodPERRel of a pair `(reconstruct, m)`
reduces to `prodPERRel(m, m)` when reconstruct
is built from left/right destructors of `m`. -/
theorem prodPERRel_reconstruct_eq
    (X Y : @TreePERObj C _ h p)
    (m : p.T ⟶ p.T) :
    cfpLift
      (cfpLift (m ≫ treeLeftEndo)
        (m ≫ treeRightEndo) ≫ p.β) m ≫
      prodPERRel X Y =
    cfpLift m m ≫ prodPERRel X Y := by
  unfold prodPERRel
  rw [← Category.assoc, cfpLift_precomp,
    ← Category.assoc, cfpLift_precomp,
    reconstruct_leftRelCheck X m,
    reconstruct_rightRelCheck Y m]

/-- The pair-reconstruct pre-morphism is equivalent
to the original: for any `m : Z → prodPER(X, Y)`,
`pair(fst ∘ m, snd ∘ m) ≈ m`. -/
theorem prodPER_pair_reconstruct_eqv
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (m : TreePERPreMor Z
      (prodPERObj hSep hBD X Y)) :
    treePERMorEqv
      (prodPERPairPreMor hSep hBD
        (treePERPreMorComp m
          (prodPERFstPreMor hSep hBD X Y))
        (treePERPreMorComp m
          (prodPERSndPreMor hSep hBD X Y)))
      m := by
  intro D e hdom
  -- The reconstruct map is:
  -- cfpLift (m ≫ treeLeftEndo)
  --   (m ≫ treeRightEndo) ≫ β
  -- We must show:
  -- IsLeafConst(e ≫ cfpLift reconstruct m.map ≫
  --   prodPERRel X Y)
  -- By prodPERRel_reconstruct_eq, this equals:
  -- IsLeafConst(e ≫ cfpLift m.map m.map ≫
  --   prodPERRel X Y)
  -- which is treePERMorEqv_refl m e hdom.
  change IsLeafConst
    (e ≫ cfpLift
      (cfpLift (m.map ≫ treeLeftEndo)
        (m.map ≫ treeRightEndo) ≫ p.β)
      m.map ≫
      prodPERRel X Y)
  unfold IsLeafConst
  have hrw :
      cfpLift
        (cfpLift (m.map ≫ treeLeftEndo)
          (m.map ≫ treeRightEndo) ≫ p.β)
        m.map ≫
        prodPERRel X Y =
      cfpLift m.map m.map ≫
        prodPERRel X Y :=
    prodPERRel_reconstruct_eq X Y m.map
  rw [hrw]
  have := treePERMorEqv_refl m e hdom
  unfold IsLeafConst at this
  exact this

/-- Uniqueness of pairing in the PER category:
if `treePERMorComp m (prodPERFst ...) = f` and
`treePERMorComp m (prodPERSnd ...) = g`, then
`m = prodPERPair ... f g`. -/
theorem prodPER_pair_unique
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {Z X Y : @TreePERObj C _ h p}
    (f : TreePERMor Z X)
    (g : TreePERMor Z Y)
    (m : TreePERMor Z
      (prodPERObj hSep hBD X Y))
    (hf : treePERMorComp m
      (prodPERFst hSep hBD X Y) = f)
    (hg : treePERMorComp m
      (prodPERSnd hSep hBD X Y) = g) :
    m = prodPERPair hSep hBD f g := by
  subst hf; subst hg
  revert m
  apply Quotient.ind
  intro m'
  apply Quotient.sound
    (s := treePERSetoid Z
      (prodPERObj hSep hBD X Y))
  exact treePERMorEqv_symm
    (prodPER_pair_reconstruct_eqv
      hSep hBD m')

/-! ## HasTerminal instance -/

/-- The PER category has a terminal object. -/
instance treePER_hasTerminal :
    Limits.HasTerminal
      (@TreePERObj C _ h p) :=
  terminalPERObj_isTerminal.hasTerminal

/-! ## HasBinaryProducts instance -/

section BinaryProducts

variable
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)

/-- The binary fan for the product PER. -/
def prodPERFan
    (X Y : @TreePERObj C _ h p) :
    Limits.BinaryFan X Y :=
  Limits.BinaryFan.mk
    (prodPERFst hSep hBD X Y)
    (prodPERSnd hSep hBD X Y)

/-- The binary fan for the product PER is a
limit cone. -/
def prodPERFan_isLimit
    (X Y : @TreePERObj C _ h p) :
    Limits.IsLimit (prodPERFan hSep hBD X Y) :=
  Limits.BinaryFan.isLimitMk
    (fun s =>
      prodPERPair hSep hBD s.fst s.snd)
    (fun s =>
      prodPERFst_comp_pair hSep hBD
        s.fst s.snd)
    (fun s =>
      prodPERSnd_comp_pair hSep hBD
        s.fst s.snd)
    (fun s m hf hg =>
      prodPER_pair_unique hSep hBD
        s.fst s.snd m hf hg)

/-- Each pair of PER objects has a product. -/
@[reducible]
def treePER_hasLimitPair
    (X Y : @TreePERObj C _ h p) :
    Limits.HasLimit (Limits.pair X Y) :=
  Limits.HasLimit.mk
    ⟨prodPERFan hSep hBD X Y,
      prodPERFan_isLimit hSep hBD X Y⟩

/-- The PER category has binary products (given
separator and Boolean dichotomy hypotheses). -/
@[reducible]
def treePER_hasBinaryProducts :
    Limits.HasBinaryProducts
      (@TreePERObj C _ h p) :=
  { has_limit := fun F => by
      have := treePER_hasLimitPair hSep hBD
        (F.obj ⟨Limits.WalkingPair.left⟩)
        (F.obj ⟨Limits.WalkingPair.right⟩)
      exact Limits.hasLimit_of_iso
        (Limits.diagramIsoPair F).symm }

end BinaryProducts

/-! ## Equalizer PER -/

section Equalizers

variable
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)

/-- The equalizer check: `eqCheck f g` applied to
`x` yields `Y.rel(f(x), g(x))`.  Defined as the
diagonal followed by `cfpMap f.map g.map ≫
Y.rel`. -/
def eqCheck
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    p.T ⟶ p.T :=
  cfpLift (𝟙 p.T) (𝟙 p.T) ≫
    cfpMap f.map g.map ≫ Y.rel

/-- The equalizer PER relation for pre-morphisms
`f, g : X → Y`.  The relation is
`boolAnd(X.rel(x, y), boolAnd(eqCheck(x),
  eqCheck(y)))`.
The domain consists of elements `x` in dom(X)
such that `Y.rel(f(x), g(x)) = leaf`. -/
def eqPERRel
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift X.rel
    (cfpLift
      (cfpFst p.T p.T ≫ eqCheck f g)
      (cfpSnd p.T p.T ≫ eqCheck f g) ≫
      boolAnd) ≫ boolAnd

/-- The equalizer PER relation is
Boolean-valued. -/
theorem eqPERRel_bool
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    eqPERRel f g ≫ isLeafEndo =
      eqPERRel f g := by
  unfold eqPERRel
  rw [Category.assoc, boolAnd_output_boolean]

include hSep hBD in
/-- Commutativity of `boolAnd` for Boolean-valued
arguments: if `A` and `B` are Boolean-valued
(i.e., `A ≫ isLeafEndo = A` and similarly for
`B`), then `cfpLift A B ≫ boolAnd =
cfpLift B A ≫ boolAnd`. -/
theorem boolAnd_comm_bool
    {D : C}
    (A B : D ⟶ p.T)
    (hA : A ≫ isLeafEndo = A)
    (hB : B ≫ isLeafEndo = B) :
    cfpLift A B ≫ boolAnd =
      cfpLift B A ≫
        (boolAnd : cfpProd p.T p.T ⟶ p.T) := by
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
          treeFalse := boolAnd_treeFalse_left _
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
            treeFalse := boolAnd_treeFalse_left _
      rw [cfpTerminalFrom_terminal,
        Category.id_comp] at this
      exact this
    have h2 :
        cfpLift p.ℓ (treeFalse (C := C)) ≫
          boolAnd =
        treeFalse := boolAnd_ℓ_treeFalse
    rw [h1, h2]
  · rw [ha, hb]

/-- `eqCheck f g` is Boolean-valued. -/
theorem eqCheck_bool
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    eqCheck f g ≫ isLeafEndo =
      eqCheck f g := by
  unfold eqCheck
  simp only [Category.assoc]
  rw [Y.rel_bool]

include hSep hBD in
/-- The equalizer PER relation is symmetric:
`cfpSwap ≫ eqPERRel f g = eqPERRel f g`.
This follows from X.rel's symmetry and
commutativity of boolAnd on Boolean-valued
arguments. -/
theorem eqPERRel_symm
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    cfpSwap p.T p.T ≫ eqPERRel f g =
      eqPERRel f g := by
  unfold eqPERRel
  rw [← Category.assoc, cfpLift_precomp]
  -- After swap, the first component becomes
  -- cfpSwap ≫ X.rel = X.rel (by symmetry).
  have h1 :
      cfpSwap p.T p.T ≫ X.rel = X.rel :=
    X.rel_symm
  -- The second component: swap permutes the
  -- cfpFst/cfpSnd, so
  -- eqCheck(snd) and eqCheck(fst) get swapped.
  -- For the second component, swap exchanges
  -- fst and snd, then boolAnd_comm_bool applies.
  set ec := eqCheck f g
  have swap_lift :
      cfpSwap p.T p.T ≫
        cfpLift
          (cfpFst p.T p.T ≫ ec)
          (cfpSnd p.T p.T ≫ ec) =
      cfpLift
        (cfpSnd p.T p.T ≫ ec)
        (cfpFst p.T p.T ≫ ec) := by
    unfold cfpSwap
    rw [cfpLift_precomp, ← Category.assoc,
      cfpLift_fst, ← Category.assoc,
      cfpLift_snd]
  -- The goal after cfpLift_precomp is:
  -- cfpLift (cfpSwap ≫ X.rel)
  --   (cfpSwap ≫ (...) ≫ boolAnd) ≫ boolAnd
  -- = cfpLift X.rel ((...) ≫ boolAnd) ≫ boolAnd.
  -- The outer boolAnd is the same, so it
  -- suffices to show the cfpLift arguments match.
  have h2 :
      cfpSwap p.T p.T ≫
        (cfpLift
          (cfpFst p.T p.T ≫ ec)
          (cfpSnd p.T p.T ≫ ec) ≫
        boolAnd) =
      cfpLift
        (cfpFst p.T p.T ≫ ec)
        (cfpSnd p.T p.T ≫ ec) ≫
        boolAnd := by
    rw [← Category.assoc, swap_lift]
    have snd_ec_bool :
        (cfpSnd p.T p.T ≫ ec) ≫ isLeafEndo =
        cfpSnd p.T p.T ≫ ec := by
      rw [Category.assoc, eqCheck_bool]
    have fst_ec_bool :
        (cfpFst p.T p.T ≫ ec) ≫ isLeafEndo =
        cfpFst p.T p.T ≫ ec := by
      rw [Category.assoc, eqCheck_bool]
    exact boolAnd_comm_bool hSep hBD _ _
      snd_ec_bool fst_ec_bool
  rw [h1, h2]

/-- Quantified transitivity for the equalizer PER
relation. If `eqPERRel(x,z)` and `eqPERRel(z,y)`
hold, then `eqPERRel(x,y)` holds.

The proof decomposes each hypothesis into its
`X.rel` and `eqCheck` components, applies X's
transitivity for `X.rel(x,y)`, and uses
`eqCheck(x)` from the first hypothesis and
`eqCheck(y)` from the second. -/
theorem eqPERRel_quantTransitive
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    QuantTransitive (eqPERRel f g) := by
  intro D e hxz hzy
  -- Expand eqPERRel in both hypotheses
  -- and the goal.
  -- eqPERRel = boolAnd(X.rel,
  --   boolAnd(fst ≫ eqCheck, snd ≫ eqCheck)).
  -- After cfpLift t3x t3z ≫ eqPERRel:
  -- boolAnd(cfpLift t3x t3z ≫ X.rel,
  --   boolAnd(t3x ≫ eqCheck, t3z ≫ eqCheck)).
  --
  -- From hxz, extract:
  --   IsLeafConst(e ≫ cfpLift t3x t3z ≫ X.rel)
  --   IsLeafConst(e ≫ t3x ≫ eqCheck f g)
  --   IsLeafConst(e ≫ t3z ≫ eqCheck f g)
  -- From hzy, extract:
  --   IsLeafConst(e ≫ cfpLift t3z t3y ≫ X.rel)
  --   IsLeafConst(e ≫ t3z ≫ eqCheck f g)
  --   IsLeafConst(e ≫ t3y ≫ eqCheck f g)
  -- The goal needs:
  --   IsLeafConst(e ≫ cfpLift t3x t3y ≫ X.rel)
  --   IsLeafConst(e ≫ t3x ≫ eqCheck f g)
  --   IsLeafConst(e ≫ t3y ≫ eqCheck f g)
  -- The first follows from X's transitivity.
  -- The second comes from hxz.
  -- The third comes from hzy.
  set ec := eqCheck f g
  -- Rewrite the eqPERRel applications.
  have eqPER_expand
      (a b :
        cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) :
      e ≫ cfpLift a b ≫ eqPERRel f g =
      e ≫ cfpLift
        (cfpLift a b ≫ X.rel)
        (cfpLift (a ≫ ec) (b ≫ ec) ≫
          boolAnd) ≫
        boolAnd := by
    unfold eqPERRel
    rw [← Category.assoc (cfpLift a b),
      cfpLift_precomp (cfpLift a b)]
    rw [← Category.assoc (cfpLift a b),
      cfpLift_precomp (cfpLift a b)]
    simp only [← Category.assoc]
    rw [cfpLift_fst, cfpLift_snd]
  -- Extract components from hxz.
  have hxz_rw : IsLeafConst
      (e ≫ cfpLift
        (cfpLift t3x t3z ≫ X.rel)
        (cfpLift (t3x ≫ ec) (t3z ≫ ec) ≫
          boolAnd) ≫ boolAnd) := by
    unfold IsLeafConst at hxz ⊢
    rw [← eqPER_expand]; exact hxz
  have xrel_bool
      (a b :
        cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) :
      (cfpLift a b ≫ X.rel) ≫ isLeafEndo =
      cfpLift a b ≫ X.rel := by
    rw [Category.assoc, X.rel_bool]
  have hxz_Xrel : IsLeafConst
      (e ≫ cfpLift t3x t3z ≫ X.rel) :=
    boolAnd_fst_IsLeafConst
      (xrel_bool t3x t3z) e hxz_rw
  have checks_bool
      (a b :
        cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) :
      (cfpLift (a ≫ ec) (b ≫ ec) ≫
        boolAnd) ≫ isLeafEndo =
      cfpLift (a ≫ ec) (b ≫ ec) ≫
        boolAnd := by
    rw [Category.assoc, boolAnd_output_boolean]
  have hxz_checks : IsLeafConst
      (e ≫ cfpLift (t3x ≫ ec) (t3z ≫ ec) ≫
        boolAnd) := by
    exact boolAnd_snd_IsLeafConst
      (checks_bool t3x t3z) e hxz_rw
  have hxz_ecx : IsLeafConst
      (e ≫ t3x ≫ ec) := by
    have hA :
        (t3x ≫ ec) ≫ isLeafEndo =
        t3x ≫ ec := by
      rw [Category.assoc, eqCheck_bool]
    exact boolAnd_fst_IsLeafConst hA e
      hxz_checks
  -- Extract from hzy.
  have hzy_rw : IsLeafConst
      (e ≫ cfpLift
        (cfpLift t3z t3y ≫ X.rel)
        (cfpLift (t3z ≫ ec) (t3y ≫ ec) ≫
          boolAnd) ≫ boolAnd) := by
    unfold IsLeafConst at hzy ⊢
    rw [← eqPER_expand]; exact hzy
  have hzy_Xrel : IsLeafConst
      (e ≫ cfpLift t3z t3y ≫ X.rel) :=
    boolAnd_fst_IsLeafConst
      (xrel_bool t3z t3y) e hzy_rw
  have hzy_checks : IsLeafConst
      (e ≫ cfpLift (t3z ≫ ec) (t3y ≫ ec) ≫
        boolAnd) :=
    boolAnd_snd_IsLeafConst
      (checks_bool t3z t3y) e hzy_rw
  have hzy_ecy : IsLeafConst
      (e ≫ t3y ≫ ec) := by
    have hB' :
        (t3y ≫ ec) ≫ isLeafEndo =
        t3y ≫ ec := by
      rw [Category.assoc, eqCheck_bool]
    exact boolAnd_snd_IsLeafConst hB' e
      hzy_checks
  -- Build the goal.
  have goal_Xrel : IsLeafConst
      (e ≫ cfpLift t3x t3y ≫ X.rel) :=
    X.rel_trans_prop e hxz_Xrel hzy_Xrel
  -- Combine: eqCheck(x) from hxz, eqCheck(y)
  -- from hzy, X.rel(x,y) from transitivity.
  have goal_checks : IsLeafConst
      (e ≫ cfpLift (t3x ≫ ec) (t3y ≫ ec) ≫
        boolAnd) := by
    unfold IsLeafConst at hxz_ecx hzy_ecy ⊢
    rw [← Category.assoc, cfpLift_precomp,
      hxz_ecx, hzy_ecy,
      ← cfpLift_precomp
        (cfpTerminalFrom D) p.ℓ p.ℓ,
      Category.assoc, boolAnd_ℓ_ℓ]
  -- Final assembly.
  unfold IsLeafConst at goal_Xrel goal_checks ⊢
  rw [eqPER_expand]
  rw [← Category.assoc, cfpLift_precomp,
    goal_Xrel, goal_checks,
    ← cfpLift_precomp
      (cfpTerminalFrom D) p.ℓ p.ℓ,
    Category.assoc, boolAnd_ℓ_ℓ]

include hSep hBD in
/-- Equational transitivity for the equalizer PER
relation. -/
theorem eqPERRel_eqTransitive
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    EqTransitive (eqPERRel f g) :=
  quantTransitive_implies_eq hSep hBD
    (eqPERRel_bool f g)
    (eqPERRel_quantTransitive f g)

/-- The equalizer PER object. -/
def eqPERObj
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    @TreePERObj C _ h p where
  rel := eqPERRel f g
  rel_bool := eqPERRel_bool f g
  rel_symm := eqPERRel_symm hSep hBD f g
  rel_trans :=
    eqPERRel_eqTransitive hSep hBD f g

/-- The inclusion pre-morphism from the equalizer
PER to X: the underlying map is `𝟙 T`.
The relation-preservation condition
`boolAnd(eqPERRel, cfpMap (𝟙 T) (𝟙 T) ≫ X.rel)
  = eqPERRel`
holds because `eqPERRel` implies `X.rel` (via its
first boolAnd component). -/
def eqPERInclPreMor
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    TreePERPreMor
      (eqPERObj hSep hBD f g) X where
  map := 𝟙 p.T
  map_rel := by
    rw [cfpMap_id, Category.id_comp]
    -- Goal: cfpLift (eqPERRel f g) X.rel ≫
    --   boolAnd = eqPERRel f g.
    -- eqPERRel = boolAnd(X.rel, ...).
    -- cfpLift (boolAnd(X.rel, B)) X.rel ≫ boolAnd
    -- = boolAnd(X.rel, B) by boolAnd_fst_proj.
    exact boolAnd_fst_proj hSep hBD
      X.rel
      (cfpLift
        (cfpFst p.T p.T ≫ eqCheck f g)
        (cfpSnd p.T p.T ≫ eqCheck f g) ≫
        boolAnd)
      X.rel_bool
      (by rw [Category.assoc,
        boolAnd_output_boolean])

/-- The inclusion morphism in the PER category. -/
def eqPERIncl
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    TreePERMor
      (eqPERObj hSep hBD f g) X :=
  Quotient.mk
    (treePERSetoid
      (eqPERObj hSep hBD f g) X)
    (eqPERInclPreMor hSep hBD f g)

/-- `eqCheck f g` equals
`cfpLift f.map g.map ≫ Y.rel`. -/
theorem eqCheck_expand
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    eqCheck f g =
      cfpLift f.map g.map ≫ Y.rel := by
  unfold eqCheck
  rw [← Category.assoc, cfpLift_cfpMap]
  simp only [Category.id_comp]

/-- The equalizing condition: `incl ≫ f ≈ incl ≫ g`
as pre-morphisms from `eqPERObj` to `Y`.
For `e` in dom(eqPERObj), the `eqCheck` component
of the domain condition gives
`Y.rel(f(e), g(e)) = leaf`. -/
theorem eqPER_equalizes
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    treePERMorEqv
      (treePERPreMorComp
        (eqPERInclPreMor hSep hBD f g) f)
      (treePERPreMorComp
        (eqPERInclPreMor hSep hBD f g) g) := by
  intro D e hdom
  change IsLeafConst
    (e ≫ cfpLift (𝟙 p.T ≫ f.map)
      (𝟙 p.T ≫ g.map) ≫ Y.rel)
  simp only [Category.id_comp]
  -- The goal is now
  -- IsLeafConst(e ≫ cfpLift f.map g.map ≫ Y.rel).
  -- Rewrite via eqCheck_expand.
  rw [← eqCheck_expand f g]
  -- Goal: IsLeafConst(e ≫ eqCheck f g).
  -- Extract from the domain condition.
  -- hdom says e is in dom(eqPERObj), i.e.,
  -- eqPERRel(e, e) = leaf.
  -- eqPERRel = boolAnd(X.rel,
  --   boolAnd(fst ≫ ec, snd ≫ ec)).
  -- On the diagonal (via cfpLift (𝟙)(𝟙)):
  -- boolAnd(X.rel(e,e),
  --   boolAnd(ec(e), ec(e))) = leaf.
  -- Extract boolAnd(ec(e), ec(e)) = leaf,
  -- then ec(e) = leaf.
  change IsLeafConst
    (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T) ≫
      eqPERRel f g) at hdom
  -- Extract the checks component.
  have checks_bool :
      (cfpLift
        (cfpFst p.T p.T ≫ eqCheck f g)
        (cfpSnd p.T p.T ≫ eqCheck f g) ≫
        boolAnd) ≫ isLeafEndo =
      cfpLift
        (cfpFst p.T p.T ≫ eqCheck f g)
        (cfpSnd p.T p.T ≫ eqCheck f g) ≫
        boolAnd := by
    rw [Category.assoc, boolAnd_output_boolean]
  -- hdom after unfolding eqPERRel:
  -- IsLeafConst(e ≫ cfpLift (𝟙)(𝟙) ≫
  --   cfpLift X.rel (...) ≫ boolAnd).
  -- The `e` for boolAnd_snd_IsLeafConst
  -- is `e ≫ cfpLift (𝟙)(𝟙)`.
  have hdom' : IsLeafConst
      ((e ≫ cfpLift (𝟙 p.T) (𝟙 p.T)) ≫
        cfpLift X.rel
          (cfpLift
            (cfpFst p.T p.T ≫ eqCheck f g)
            (cfpSnd p.T p.T ≫ eqCheck f g) ≫
            boolAnd) ≫ boolAnd) := by
    unfold IsLeafConst at hdom ⊢
    rw [Category.assoc]; exact hdom
  have h_checks : IsLeafConst
      ((e ≫ cfpLift (𝟙 p.T) (𝟙 p.T)) ≫
        cfpLift
          (cfpFst p.T p.T ≫ eqCheck f g)
          (cfpSnd p.T p.T ≫ eqCheck f g) ≫
        boolAnd) :=
    boolAnd_snd_IsLeafConst
      checks_bool _ hdom'
  -- Simplify the diagonal.
  have diag :
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        cfpLift
          (cfpFst p.T p.T ≫ eqCheck f g)
          (cfpSnd p.T p.T ≫ eqCheck f g) =
      cfpLift (eqCheck f g)
        (eqCheck f g) := by
    rw [cfpLift_precomp]
    simp only [← Category.assoc,
      cfpLift_fst, cfpLift_snd,
      Category.id_comp]
  -- Rewrite h_checks using diag.
  -- h_checks has type:
  -- IsLeafConst((e ≫ cfpLift (𝟙)(𝟙)) ≫
  --   cfpLift (fst ≫ ec)(snd ≫ ec) ≫ boolAnd)
  -- We need:
  -- IsLeafConst(e ≫ cfpLift ec ec ≫ boolAnd)
  have h_checks' : IsLeafConst
      (e ≫ cfpLift (eqCheck f g)
        (eqCheck f g) ≫ boolAnd) := by
    unfold IsLeafConst at h_checks ⊢
    have step :
        (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T)) ≫
          cfpLift
            (cfpFst p.T p.T ≫ eqCheck f g)
            (cfpSnd p.T p.T ≫ eqCheck f g) ≫
          boolAnd =
        e ≫ cfpLift (eqCheck f g)
          (eqCheck f g) ≫ boolAnd := by
      rw [Category.assoc,
        ← Category.assoc
          (cfpLift (𝟙 p.T) (𝟙 p.T)),
        diag]
    rw [step] at h_checks; exact h_checks
  exact boolAnd_fst_IsLeafConst
    (eqCheck_bool f g) e h_checks'

/-- The equalizing condition lifted to the quotient
category: `eqPERIncl ≫ f = eqPERIncl ≫ g`. -/
theorem eqPER_equalizes_quot
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    treePERMorComp
      (eqPERIncl hSep hBD f g)
      (Quotient.mk (treePERSetoid X Y) f) =
    treePERMorComp
      (eqPERIncl hSep hBD f g)
      (Quotient.mk (treePERSetoid X Y) g) := by
  apply Quotient.sound
    (s := treePERSetoid
      (eqPERObj hSep hBD f g) Y)
  exact eqPER_equalizes hSep hBD f g

/-- Domain membership in a PER is implied by
relatedness: if `Z.rel(x, y) = leaf` (as a
global element), then `Z.rel(x, x) = leaf`.
Proved via symmetry and transitivity. -/
theorem treePER_domain_from_rel
    (Z : @TreePERObj C _ h p)
    (e : cfpTerminal (C := C) ⟶
      cfpProd p.T p.T)
    (hrel : IsLeafConst (e ≫ Z.rel)) :
    IsLeafConst
      ((e ≫ cfpFst p.T p.T) ≫
        cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        Z.rel) := by
  have hrel_yx : IsLeafConst
      (e ≫ cfpSwap p.T p.T ≫ Z.rel) := by
    unfold IsLeafConst at hrel ⊢
    rw [Z.rel_symm]; exact hrel
  -- Triple: (fst(e), fst(e), snd(e)).
  -- (x,z) = e, (z,y) = swap(e),
  -- (x,y) = diag(fst(e)).
  set tr := cfpLift (e ≫ cfpFst p.T p.T)
    (cfpLift (e ≫ cfpFst p.T p.T)
      (e ≫ cfpSnd p.T p.T))
  have tr_fst : tr ≫
      cfpFst p.T (cfpProd p.T p.T) =
      e ≫ cfpFst p.T p.T := cfpLift_fst _ _
  have tr_snd_fst : tr ≫
      cfpSnd p.T (cfpProd p.T p.T) ≫
      cfpFst p.T p.T =
      e ≫ cfpFst p.T p.T := by
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_fst]
  have tr_snd_snd : tr ≫
      cfpSnd p.T (cfpProd p.T p.T) ≫
      cfpSnd p.T p.T =
      e ≫ cfpSnd p.T p.T := by
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_snd]
  have ht3_xz : tr ≫ cfpLift t3x t3z =
      e := by
    have h1 := cfpLift_uniq
      (e ≫ cfpFst p.T p.T)
      (e ≫ cfpSnd p.T p.T)
      (tr ≫ cfpLift t3x t3z)
      (by rw [Category.assoc,
            cfpLift_fst]; exact tr_fst)
      (by rw [Category.assoc,
            cfpLift_snd]; exact tr_snd_snd)
    have h2 := cfpLift_uniq
      (e ≫ cfpFst p.T p.T)
      (e ≫ cfpSnd p.T p.T) e rfl rfl
    exact h1.trans h2.symm
  have ht3_zy : tr ≫ cfpLift t3z t3y =
      e ≫ cfpSwap p.T p.T := by
    unfold cfpSwap
    have h1 := cfpLift_uniq
      (e ≫ cfpSnd p.T p.T)
      (e ≫ cfpFst p.T p.T)
      (tr ≫ cfpLift t3z t3y)
      (by rw [Category.assoc, cfpLift_fst]
          unfold t3z
          exact tr_snd_snd)
      (by rw [Category.assoc, cfpLift_snd]
          unfold t3y
          exact tr_snd_fst)
    have h2 := cfpLift_uniq
      (e ≫ cfpSnd p.T p.T)
      (e ≫ cfpFst p.T p.T)
      (e ≫ cfpLift (cfpSnd p.T p.T)
        (cfpFst p.T p.T))
      (by rw [Category.assoc,
            cfpLift_fst])
      (by rw [Category.assoc,
            cfpLift_snd])
    exact h1.trans h2.symm
  have ht3_xy : tr ≫ cfpLift t3x t3y =
      (e ≫ cfpFst p.T p.T) ≫
        cfpLift (𝟙 p.T) (𝟙 p.T) := by
    have h1 := cfpLift_uniq
      (e ≫ cfpFst p.T p.T)
      (e ≫ cfpFst p.T p.T)
      (tr ≫ cfpLift t3x t3y)
      (by rw [Category.assoc,
            cfpLift_fst]; exact tr_fst)
      (by rw [Category.assoc,
            cfpLift_snd]; exact tr_snd_fst)
    have h2 := cfpLift_uniq
      (e ≫ cfpFst p.T p.T)
      (e ≫ cfpFst p.T p.T)
      ((e ≫ cfpFst p.T p.T) ≫
        cfpLift (𝟙 p.T) (𝟙 p.T))
      (by rw [Category.assoc,
            cfpLift_fst, Category.comp_id])
      (by rw [Category.assoc,
            cfpLift_snd, Category.comp_id])
    exact h1.trans h2.symm
  set triple :=
    cfpLift (e ≫ cfpFst p.T p.T)
      (cfpLift (e ≫ cfpFst p.T p.T)
        (e ≫ cfpSnd p.T p.T))
  have hxz : IsLeafConst
      (triple ≫ cfpLift t3x t3z ≫
        Z.rel) := by
    unfold IsLeafConst at hrel ⊢
    rw [← Category.assoc, ht3_xz]
    exact hrel
  have hzy : IsLeafConst
      (triple ≫ cfpLift t3z t3y ≫
        Z.rel) := by
    unfold IsLeafConst at hrel_yx ⊢
    rw [← Category.assoc, ht3_zy,
      Category.assoc]
    exact hrel_yx
  have hxy :=
    Z.rel_trans_prop triple hxz hzy
  unfold IsLeafConst at hxy ⊢
  rw [← Category.assoc, ht3_xy] at hxy
  simp only [Category.assoc] at hxy ⊢
  exact hxy

include hSep hBD in
/-- The relation `Z.rel` implies `eqCheck(t(_))`
on the first component: given the equalizing
condition `treePERMorEqv (comp t f) (comp t g)`,
`boolAnd(Z.rel, cfpFst ≫ t.map ≫ eqCheck f g)
  = Z.rel`. -/
theorem eqPER_rel_implies_eqCheck_fst
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t : TreePERPreMor Z X)
    (heq : treePERMorEqv
      (treePERPreMorComp t f)
      (treePERPreMorComp t g)) :
    cfpLift Z.rel
      (cfpFst p.T p.T ≫
        t.map ≫ eqCheck f g) ≫
      boolAnd = Z.rel := by
  apply hSep.def
  intro e
  rw [← Category.assoc, cfpLift_precomp]
  set eZ := e ≫ Z.rel
  set eA := e ≫ cfpFst p.T p.T ≫
    t.map ≫ eqCheck f g
  have eZ_bool :
      eZ ≫ isLeafEndo = eZ := by
    change (e ≫ Z.rel) ≫ isLeafEndo = _
    rw [Category.assoc, Z.rel_bool]
  have eA_bool :
      eA ≫ isLeafEndo = eA := by
    change (e ≫ cfpFst p.T p.T ≫ t.map ≫
      eqCheck f g) ≫ isLeafEndo = _
    simp only [Category.assoc]
    rw [eqCheck_bool]
  have tf_eq : treeFalse (C := C) =
      cfpTerminalFrom cfpTerminal ≫
        treeFalse := by
    rw [cfpTerminalFrom_terminal,
      Category.id_comp]
  rcases hBD eZ eZ_bool with hZ | hZ
  · -- eZ = ℓ: derive eA = ℓ from equalizing.
    have e_fst_dom :=
      treePER_domain_from_rel Z e
        (isLeafConst_terminal_eq_ℓ.mpr hZ)
    have ec_leaf := heq
      (e ≫ cfpFst p.T p.T) e_fst_dom
    unfold IsLeafConst at ec_leaf
    have map_tf :
        (treePERPreMorComp t f).map =
        t.map ≫ f.map := rfl
    have map_tg :
        (treePERPreMorComp t g).map =
        t.map ≫ g.map := rfl
    rw [map_tf, map_tg] at ec_leaf
    have ec_simp :
        (e ≫ cfpFst p.T p.T) ≫
          cfpLift (t.map ≫ f.map)
            (t.map ≫ g.map) ≫
          Y.rel = eA := by
      simp only [Category.assoc]
      congr 2
      rw [eqCheck_expand,
        ← Category.assoc,
        cfpLift_precomp]
    rw [ec_simp] at ec_leaf
    -- ec_leaf : eA = cfpTerminalFrom ≫ ℓ.
    -- With cfpTerminalFrom = 𝟙, eA = ℓ.
    have hA_ℓ : eA = p.ℓ := by
      rw [cfpTerminalFrom_terminal,
        Category.id_comp] at ec_leaf
      exact ec_leaf
    rw [hZ, hA_ℓ, boolAnd_ℓ_ℓ]
  · rw [hZ, tf_eq, boolAnd_treeFalse_left]

include hSep hBD in
/-- The relation `Z.rel` implies `eqCheck(t(_))`
on the second component. -/
theorem eqPER_rel_implies_eqCheck_snd
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t : TreePERPreMor Z X)
    (heq : treePERMorEqv
      (treePERPreMorComp t f)
      (treePERPreMorComp t g)) :
    cfpLift Z.rel
      (cfpSnd p.T p.T ≫
        t.map ≫ eqCheck f g) ≫
      boolAnd = Z.rel := by
  -- Rewrite via symmetry of Z.rel.
  -- Z.rel = cfpSwap ≫ Z.rel (by rel_symm).
  -- cfpSwap ≫ cfpFst = cfpSnd and vice versa.
  have h1 :
      cfpLift Z.rel
        (cfpSnd p.T p.T ≫
          t.map ≫ eqCheck f g) =
      cfpLift (cfpSwap p.T p.T ≫ Z.rel)
        (cfpSwap p.T p.T ≫ cfpFst p.T p.T ≫
          t.map ≫ eqCheck f g) := by
    congr 1
    · exact Z.rel_symm.symm
    · unfold cfpSwap
      simp only [← Category.assoc]
      rw [cfpLift_fst]
  rw [h1]
  -- Factor out cfpSwap.
  have h2 :
      cfpLift (cfpSwap p.T p.T ≫ Z.rel)
        (cfpSwap p.T p.T ≫ cfpFst p.T p.T ≫
          t.map ≫ eqCheck f g) =
      cfpSwap p.T p.T ≫
        cfpLift Z.rel
          (cfpFst p.T p.T ≫
            t.map ≫ eqCheck f g) := by
    rw [cfpLift_precomp]
  rw [h2, Category.assoc,
    eqPER_rel_implies_eqCheck_fst
      hSep hBD f g t heq,
    Z.rel_symm]

include hSep hBD in
/-- The lift pre-morphism for the equalizer: given
`t : Z → X` with `t ≫ f ≈ t ≫ g`, the lift is
`t.map` itself, viewed as a morphism `Z → eqPER`.
The `map_rel` condition follows by
`boolAnd_implies_trans` using `t.map_rel` and the
equalizing condition. -/
def eqPERLiftPreMor
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t : TreePERPreMor Z X)
    (heq : treePERMorEqv
      (treePERPreMorComp t f)
      (treePERPreMorComp t g)) :
    TreePERPreMor Z
      (eqPERObj hSep hBD f g) where
  map := t.map
  map_rel := by
    -- Goal: boolAnd(Z.rel,
    --   cfpMap t t ≫ eqPERRel f g)
    --   = Z.rel.
    -- Expand eqPERRel and push cfpMap through.
    change cfpLift Z.rel
      (cfpMap t.map t.map ≫
        eqPERRel f g) ≫ boolAnd = Z.rel
    unfold eqPERRel
    rw [← Category.assoc
      (cfpMap t.map t.map),
      cfpLift_precomp (cfpMap t.map t.map)]
    -- boolAnd_assoc to extract X.rel part.
    rw [← boolAnd_assoc]
    rw [t.map_rel]
    -- Remaining: boolAnd(Z.rel,
    --   cfpMap t t ≫ cfpLift (fst≫ec)(snd≫ec)
    --   ≫ boolAnd) = Z.rel.
    -- Simplify cfpMap t t ≫ cfpLift (fst≫ec)
    --   (snd≫ec).
    have cfpMap_ec :
        cfpMap t.map t.map ≫
          cfpLift
            (cfpFst p.T p.T ≫ eqCheck f g)
            (cfpSnd p.T p.T ≫ eqCheck f g) =
        cfpLift (cfpFst p.T p.T ≫
            t.map ≫ eqCheck f g)
          (cfpSnd p.T p.T ≫
            t.map ≫ eqCheck f g) := by
      rw [cfpLift_precomp
        (cfpMap t.map t.map)]
      unfold cfpMap
      simp only [← Category.assoc]
      rw [cfpLift_fst, cfpLift_snd]
    rw [← Category.assoc
      (cfpMap t.map t.map), cfpMap_ec]
    -- boolAnd_assoc to separate fst and snd.
    rw [← boolAnd_assoc]
    rw [eqPER_rel_implies_eqCheck_fst
      hSep hBD f g t heq]
    exact eqPER_rel_implies_eqCheck_snd
      hSep hBD f g t heq

include hSep hBD in
/-- The lift morphism in the PER quotient
category. -/
def eqPERLift
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t : TreePERPreMor Z X)
    (heq : treePERMorEqv
      (treePERPreMorComp t f)
      (treePERPreMorComp t g)) :
    TreePERMor Z
      (eqPERObj hSep hBD f g) :=
  Quotient.mk
    (treePERSetoid Z
      (eqPERObj hSep hBD f g))
    (eqPERLiftPreMor hSep hBD f g t heq)

include hSep hBD in
/-- Factorization: `lift ≫ incl = t`. -/
theorem eqPERLift_fac
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t : TreePERPreMor Z X)
    (heq : treePERMorEqv
      (treePERPreMorComp t f)
      (treePERPreMorComp t g)) :
    treePERMorComp
      (eqPERLift hSep hBD f g t heq)
      (eqPERIncl hSep hBD f g) =
    Quotient.mk (treePERSetoid Z X) t := by
  apply congr_arg
    (Quotient.mk (treePERSetoid Z X))
  exact treePERPreMor_ext
    (show t.map ≫ 𝟙 p.T = t.map from
      Category.comp_id _)

include hSep hBD in
/-- Uniqueness of the equalizer lift: if
`m ≫ incl = t`, then `m = lift`. -/
theorem eqPERLift_uniq
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t : TreePERPreMor Z X)
    (heq : treePERMorEqv
      (treePERPreMorComp t f)
      (treePERPreMorComp t g))
    (m : TreePERMor Z
      (eqPERObj hSep hBD f g))
    (hm : treePERMorComp m
      (eqPERIncl hSep hBD f g) =
      Quotient.mk (treePERSetoid Z X) t) :
    m = eqPERLift hSep hBD f g t heq := by
  revert hm
  apply Quotient.inductionOn
    (motive := fun (q :
      TreePERMor Z
        (eqPERObj hSep hBD f g)) =>
      treePERMorComp q
        (eqPERIncl hSep hBD f g) =
        Quotient.mk _ t →
      q = eqPERLift hSep hBD f g t heq)
    m
  intro m' hm'
  apply Quotient.sound
    (s := treePERSetoid Z
      (eqPERObj hSep hBD f g))
  have hm_eqv : treePERMorEqv
      (treePERPreMorComp m'
        (eqPERInclPreMor hSep hBD f g)) t :=
    Quotient.exact
      (s := treePERSetoid Z X) hm'
  intro D e hdom
  -- (1) X.rel(m'(e), t(e)) = ℓ.
  have hX := hm_eqv e hdom
  -- (comp m' incl).map = m'.map ≫ 𝟙 = m'.map.
  change IsLeafConst (e ≫ cfpLift m'.map
    ((eqPERLiftPreMor hSep hBD f g t heq).map)
    ≫ (eqPERObj hSep hBD f g).rel)
  -- Reduce (eqPERLiftPreMor ...).map = t.map
  -- and (eqPERObj ...).rel = eqPERRel f g.
  change IsLeafConst (e ≫ cfpLift m'.map
    t.map ≫ eqPERRel f g)
  -- (comp m' incl).map = m'.map.
  have hmap_eq :
      (treePERPreMorComp m'
        (eqPERInclPreMor hSep hBD f g)).map =
      m'.map := Category.comp_id _
  rw [hmap_eq] at hX
  -- (2) ec(m'(e)) = ℓ.
  have h_ec_m : IsLeafConst
      (e ≫ m'.map ≫ eqCheck f g) := by
    have h_m_dom :=
      treePERMorEqv_refl m' e hdom
    change IsLeafConst
      (e ≫ cfpLift m'.map m'.map ≫
        eqPERRel f g) at h_m_dom
    have diag_rw :
        m'.map ≫
          cfpLift (𝟙 p.T) (𝟙 p.T) =
        cfpLift m'.map m'.map := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    have hdom_eq : IsLeafConst
        ((e ≫ m'.map) ≫
          cfpLift (𝟙 p.T) (𝟙 p.T) ≫
          eqPERRel f g) := by
      unfold IsLeafConst at h_m_dom ⊢
      have rw1 :
          e ≫ m'.map ≫
            cfpLift (𝟙 p.T) (𝟙 p.T) ≫
            eqPERRel f g =
          e ≫ cfpLift m'.map m'.map ≫
            eqPERRel f g := by
        rw [← Category.assoc m'.map,
          diag_rw]
      rw [Category.assoc, rw1]
      exact h_m_dom
    have h := eqPER_equalizes hSep hBD f g
      (e ≫ m'.map) hdom_eq
    -- h : IsLeafConst((e ≫ m') ≫
    --   cfpLift (𝟙≫f.map)(𝟙≫g.map) ≫ Y.rel)
    -- which equals e ≫ m' ≫ eqCheck f g.
    have comp_map_f :
        (treePERPreMorComp
          (eqPERInclPreMor hSep hBD f g)
          f).map = 𝟙 p.T ≫ f.map := rfl
    have comp_map_g :
        (treePERPreMorComp
          (eqPERInclPreMor hSep hBD f g)
          g).map = 𝟙 p.T ≫ g.map := rfl
    rw [comp_map_f, comp_map_g,
      Category.id_comp, Category.id_comp]
      at h
    -- h : IsLeafConst((e ≫ m') ≫
    --   cfpLift f.map g.map ≫ Y.rel)
    unfold IsLeafConst at h ⊢
    rw [eqCheck_expand]
    simp only [Category.assoc] at h ⊢
    exact h
  -- (3) ec(t(e)) = ℓ.
  have h_ec_t : IsLeafConst
      (e ≫ t.map ≫ eqCheck f g) := by
    have h := heq e hdom
    change IsLeafConst
      (e ≫ cfpLift (t.map ≫ f.map)
        (t.map ≫ g.map) ≫ Y.rel) at h
    unfold IsLeafConst at h ⊢
    rw [eqCheck_expand]
    -- Goal: e ≫ t ≫ cfpLift f g ≫ Y.rel = ...
    -- h: e ≫ cfpLift (t≫f) (t≫g) ≫ Y.rel = ...
    -- Use cfpLift_precomp in h.
    rw [← cfpLift_precomp t.map f.map
      g.map] at h
    simp only [Category.assoc] at h ⊢
    exact h
  -- Assembly: eqPERRel = boolAnd(X.rel,
  --   boolAnd(ec_fst, ec_snd)).
  change IsLeafConst (e ≫ cfpLift m'.map
    t.map ≫ eqPERRel f g)
  -- Inline the eqPERRel expansion.
  have expand :
      e ≫ cfpLift m'.map t.map ≫
        eqPERRel f g =
      e ≫ cfpLift
        (cfpLift m'.map t.map ≫ X.rel)
        (cfpLift (m'.map ≫ eqCheck f g)
          (t.map ≫ eqCheck f g) ≫
          boolAnd) ≫
        boolAnd := by
    unfold eqPERRel
    have inner :
        cfpLift (m'.map ≫ eqCheck f g)
          (t.map ≫ eqCheck f g) =
        cfpLift m'.map t.map ≫
          cfpLift
            (cfpFst p.T p.T ≫ eqCheck f g)
            (cfpSnd p.T p.T ≫
              eqCheck f g) := by
      rw [cfpLift_precomp]
      simp only [← Category.assoc]
      rw [cfpLift_fst, cfpLift_snd]
    have outer :
        cfpLift
          (cfpLift m'.map t.map ≫ X.rel)
          (cfpLift (m'.map ≫ eqCheck f g)
            (t.map ≫ eqCheck f g) ≫
            boolAnd) =
        cfpLift m'.map t.map ≫
          cfpLift X.rel
            (cfpLift
              (cfpFst p.T p.T ≫
                eqCheck f g)
              (cfpSnd p.T p.T ≫
                eqCheck f g) ≫
              boolAnd) := by
      rw [inner]
      conv_lhs =>
        rw [show
          (cfpLift m'.map t.map ≫
            cfpLift
              (cfpFst p.T p.T ≫ eqCheck f g)
              (cfpSnd p.T p.T ≫
                eqCheck f g)) ≫
            boolAnd =
          cfpLift m'.map t.map ≫
            (cfpLift
              (cfpFst p.T p.T ≫ eqCheck f g)
              (cfpSnd p.T p.T ≫
                eqCheck f g) ≫
              boolAnd)
          from Category.assoc _ _ _]
      rw [← cfpLift_precomp]
    rw [outer]; simp only [Category.assoc]
  unfold IsLeafConst at hX h_ec_m h_ec_t ⊢
  rw [expand, ← Category.assoc,
    cfpLift_precomp e, hX,
    ← Category.assoc,
    cfpLift_precomp e,
    h_ec_m, h_ec_t,
    ← cfpLift_precomp
      (cfpTerminalFrom D) p.ℓ p.ℓ,
    Category.assoc, boolAnd_ℓ_ℓ,
    ← cfpLift_precomp
      (cfpTerminalFrom D) p.ℓ p.ℓ,
    Category.assoc, boolAnd_ℓ_ℓ]

include hSep hBD in
/-- The equalizer fork for pre-morphism
representatives `f` and `g`. -/
def eqPERFork
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    Limits.Fork
      (show X ⟶ Y from
        Quotient.mk (treePERSetoid X Y) f)
      (show X ⟶ Y from
        Quotient.mk (treePERSetoid X Y) g) :=
  Limits.Fork.ofι
    (eqPERIncl hSep hBD f g)
    (eqPER_equalizes_quot hSep hBD f g)

include hSep hBD in
/-- The lift from the equalizer is well-defined
on equivalence classes: if `t₁ ≈ t₂` as
pre-morphisms `Z → X`, and both equalize `f, g`,
then the lifts to the equalizer PER are equal
as quotient morphisms. -/
theorem eqPERLift_resp
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t₁ t₂ : TreePERPreMor Z X)
    (heq₁ : treePERMorEqv
      (treePERPreMorComp t₁ f)
      (treePERPreMorComp t₁ g))
    (heq₂ : treePERMorEqv
      (treePERPreMorComp t₂ f)
      (treePERPreMorComp t₂ g))
    (hrel : treePERMorEqv t₁ t₂) :
    eqPERLift hSep hBD f g t₁ heq₁ =
    eqPERLift hSep hBD f g t₂ heq₂ := by
  apply Quotient.sound
    (s := treePERSetoid Z
      (eqPERObj hSep hBD f g))
  intro D e hdom
  change IsLeafConst
    (e ≫ cfpLift t₁.map t₂.map ≫
      eqPERRel f g)
  -- The proof of eqPERLiftPreMor.map_rel shows
  -- boolAnd(Z.rel, cfpMap t t ≫ eqPERRel) = Z.rel.
  -- We adapt the same technique for the mixed
  -- pair (t₁, t₂).
  -- Use the map_rel proof for t₁.
  have h₁ := (eqPERLiftPreMor
    hSep hBD f g t₁ heq₁).map_rel
  -- h₁: cfpLift Z.rel
  --   (cfpMap t₁ t₁ ≫ eqPERRel) ≫ boolAnd
  --   = Z.rel.
  -- At domain element e:
  -- boolAnd(Z.rel(e), eqPERRel(t₁(e),t₁(e)))=ℓ.
  have h_dom_lift :=
    treePERMorEqv_refl
      (eqPERLiftPreMor hSep hBD f g t₁ heq₁)
      e hdom
  -- h_dom_lift: eqPERRel(t₁(e), t₁(e)) = ℓ.
  -- From hrel: X.rel(t₁(e), t₂(e)) = ℓ.
  have hX := hrel e hdom
  -- Extract eqCheck values from the domain
  -- condition.
  -- eqPERRel(t₁,t₁)=ℓ implies X.rel(t₁,t₁)=ℓ,
  -- eqCheck(t₁)=ℓ.
  -- eqPERRel = boolAnd(X.rel, boolAnd(ec∘fst,
  --   ec∘snd)).
  -- So eqPERRel(t₁,t₁)=ℓ implies ec(t₁)=ℓ.
  -- ec(t₁(e)) = ℓ.
  have h_ec_t1 : IsLeafConst
      (e ≫ t₁.map ≫ eqCheck f g) := by
    have hfst := eqPER_rel_implies_eqCheck_fst
      hSep hBD f g t₁ heq₁
    have hBool :
        (cfpFst p.T p.T ≫ t₁.map ≫
          eqCheck f g) ≫ isLeafEndo =
        cfpFst p.T p.T ≫ t₁.map ≫
          eqCheck f g := by
      simp only [Category.assoc]
      rw [eqCheck_bool]
    have hdom_assoc : IsLeafConst
        ((e ≫ cfpLift (𝟙 p.T) (𝟙 p.T)) ≫
          Z.rel) := by
      rw [Category.assoc]; exact hdom
    have hdom' := boolAnd_implies_IsLeafConst
      hfst hBool
      (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T))
      hdom_assoc
    -- hdom': IsLeafConst ((e ≫ cfpLift ...)
    --   ≫ cfpFst ≫ t₁ ≫ ec).
    rw [Category.assoc,
      show cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        cfpFst p.T p.T ≫ t₁.map ≫
        eqCheck f g =
        (cfpLift (𝟙 p.T) (𝟙 p.T) ≫
          cfpFst p.T p.T) ≫ t₁.map ≫
          eqCheck f g
        from by simp only [Category.assoc],
      cfpLift_fst, Category.id_comp]
      at hdom'
    exact hdom'
  -- ec(t₂(e)) = ℓ.
  have h_ec_t2 : IsLeafConst
      (e ≫ t₂.map ≫ eqCheck f g) := by
    have hfst := eqPER_rel_implies_eqCheck_fst
      hSep hBD f g t₂ heq₂
    have hBool :
        (cfpFst p.T p.T ≫ t₂.map ≫
          eqCheck f g) ≫ isLeafEndo =
        cfpFst p.T p.T ≫ t₂.map ≫
          eqCheck f g := by
      simp only [Category.assoc]
      rw [eqCheck_bool]
    have hdom_assoc : IsLeafConst
        ((e ≫ cfpLift (𝟙 p.T) (𝟙 p.T)) ≫
          Z.rel) := by
      rw [Category.assoc]; exact hdom
    have hdom' := boolAnd_implies_IsLeafConst
      hfst hBool
      (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T))
      hdom_assoc
    rw [Category.assoc,
      show cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        cfpFst p.T p.T ≫ t₂.map ≫
        eqCheck f g =
        (cfpLift (𝟙 p.T) (𝟙 p.T) ≫
          cfpFst p.T p.T) ≫ t₂.map ≫
          eqCheck f g
        from by simp only [Category.assoc],
      cfpLift_fst, Category.id_comp]
      at hdom'
    exact hdom'
  unfold eqPERRel
  rw [← Category.assoc
    (cfpLift t₁.map t₂.map),
    cfpLift_precomp (cfpLift t₁.map t₂.map)]
  -- boolAnd(cfpLift t₁ t₂ ≫ X.rel,
  --   cfpLift t₁ t₂ ≫ cfpLift(fst≫ec)(snd≫ec)
  --   ≫ boolAnd).
  -- Simplify the eqCheck part.
  have cfpMap_ec :
      cfpLift t₁.map t₂.map ≫
        cfpLift
          (cfpFst p.T p.T ≫ eqCheck f g)
          (cfpSnd p.T p.T ≫
            eqCheck f g) =
      cfpLift (t₁.map ≫ eqCheck f g)
        (t₂.map ≫ eqCheck f g) := by
    rw [cfpLift_precomp
      (cfpLift t₁.map t₂.map)]
    simp only [← Category.assoc]
    rw [cfpLift_fst, cfpLift_snd]
  rw [show cfpLift t₁.map t₂.map ≫
      (cfpLift (cfpFst p.T p.T ≫ eqCheck f g)
        (cfpSnd p.T p.T ≫ eqCheck f g) ≫
          boolAnd) =
      (cfpLift t₁.map t₂.map ≫
        cfpLift (cfpFst p.T p.T ≫ eqCheck f g)
          (cfpSnd p.T p.T ≫ eqCheck f g)) ≫
        boolAnd
      from (Category.assoc _ _ _).symm,
    cfpMap_ec]
  -- Goal: IsLeafConst (e ≫
  --   cfpLift (cfpLift t₁ t₂ ≫ X.rel)
  --     (cfpLift(t₁≫ec)(t₂≫ec) ≫ boolAnd)
  --   ≫ boolAnd).
  -- Use hSep to reduce to global elements.
  -- At element e: we need
  -- boolAnd(X.rel(t₁(e),t₂(e)),
  --   boolAnd(ec(t₁(e)), ec(t₂(e)))) = ℓ.
  -- All three are ℓ by hX, h_ec_t1, h_ec_t2.
  -- Use cfpLift_precomp to push e in.
  unfold IsLeafConst at hX h_ec_t1 h_ec_t2 ⊢
  have step1 :
      e ≫ cfpLift
        (cfpLift t₁.map t₂.map ≫ X.rel)
        (cfpLift (t₁.map ≫ eqCheck f g)
          (t₂.map ≫ eqCheck f g) ≫
          boolAnd) =
      cfpLift
        (e ≫ cfpLift t₁.map t₂.map ≫ X.rel)
        (e ≫ cfpLift (t₁.map ≫ eqCheck f g)
          (t₂.map ≫ eqCheck f g) ≫
          boolAnd) := by
    rw [← cfpLift_precomp]
  rw [show e ≫
      cfpLift
        (cfpLift t₁.map t₂.map ≫ X.rel)
        (cfpLift (t₁.map ≫ eqCheck f g)
          (t₂.map ≫ eqCheck f g) ≫
          boolAnd) ≫ boolAnd =
      (e ≫ cfpLift
        (cfpLift t₁.map t₂.map ≫ X.rel)
        (cfpLift (t₁.map ≫ eqCheck f g)
          (t₂.map ≫ eqCheck f g) ≫
          boolAnd)) ≫ boolAnd
      from (Category.assoc _ _ _).symm,
    step1]
  -- Inner boolAnd.
  -- After step1 the goal has the form:
  -- cfpLift (e ≫ ... ≫ X.rel)
  --   (e ≫ cfpLift(t₁≫ec)(t₂≫ec) ≫ boolAnd)
  -- ≫ boolAnd = ℓ.
  -- Push e into the inner boolAnd.
  conv_lhs =>
    rw [show
      e ≫ cfpLift (t₁.map ≫ eqCheck f g)
        (t₂.map ≫ eqCheck f g) ≫ boolAnd =
      (e ≫ cfpLift (t₁.map ≫ eqCheck f g)
        (t₂.map ≫ eqCheck f g)) ≫ boolAnd
      from (Category.assoc _ _ _).symm]
    rw [cfpLift_precomp]
  rw [h_ec_t1, h_ec_t2, hX,
    ← cfpLift_precomp
      (cfpTerminalFrom D) p.ℓ p.ℓ,
    Category.assoc, boolAnd_ℓ_ℓ,
    ← cfpLift_precomp
      (cfpTerminalFrom D) p.ℓ p.ℓ,
    Category.assoc, boolAnd_ℓ_ℓ]

include hSep hBD in
/-- The quotient-level lift for the equalizer:
given `t_q : Z ⟶ X` with `t_q ≫ ⟦f⟧ = t_q ≫ ⟦g⟧`,
produce the factorization `Z ⟶ eqPERObj`. -/
def eqPERLiftQuot
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t_q : TreePERMor Z X)
    (heq : treePERMorComp t_q
      (Quotient.mk (treePERSetoid X Y) f) =
      treePERMorComp t_q
      (Quotient.mk (treePERSetoid X Y) g)) :
    TreePERMor Z
      (eqPERObj hSep hBD f g) :=
  let fq := Quotient.mk (treePERSetoid X Y) f
  let gq := Quotient.mk (treePERSetoid X Y) g
  (Quot.hrecOn
    (motive :=
      fun (q : TreePERMor Z X) =>
        treePERMorComp q fq =
          treePERMorComp q gq →
        TreePERMor Z
          (eqPERObj hSep hBD f g))
    t_q
    (fun t heq_raw =>
      eqPERLift hSep hBD f g t
        (Quotient.exact
          (s := treePERSetoid Z Y)
          heq_raw))
    (fun t₁ t₂ hrel => by
      apply Function.hfunext
      · exact congrArg
          (fun q => treePERMorComp q fq =
            treePERMorComp q gq)
          (Quotient.sound
            (s := treePERSetoid Z X) hrel)
      · intro h₁ h₂ _
        exact heq_of_eq
          (eqPERLift_resp hSep hBD f g
            t₁ t₂ _ _ hrel)))
  heq

include hSep hBD in
/-- Factorization: `eqPERLiftQuot ≫ incl = t_q`. -/
theorem eqPERLiftQuot_fac
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t_q : TreePERMor Z X)
    (heq : treePERMorComp t_q
      (Quotient.mk (treePERSetoid X Y) f) =
      treePERMorComp t_q
      (Quotient.mk (treePERSetoid X Y) g)) :
    treePERMorComp
      (eqPERLiftQuot hSep hBD f g t_q heq)
      (eqPERIncl hSep hBD f g) = t_q := by
  revert heq
  apply Quotient.inductionOn
    (motive := fun (q : TreePERMor Z X) =>
      (heq : treePERMorComp q _ = _) →
      treePERMorComp
        (eqPERLiftQuot hSep hBD f g q heq)
        (eqPERIncl hSep hBD f g) = q)
    t_q
  intro t heq_raw
  -- Quot.hrecOn at ⟦t⟧ reduces to the function.
  change treePERMorComp
    (eqPERLift hSep hBD f g t
      (Quotient.exact
        (s := treePERSetoid Z Y) heq_raw))
    (eqPERIncl hSep hBD f g) = ⟦t⟧
  exact eqPERLift_fac hSep hBD f g t _

include hSep hBD in
/-- Uniqueness of the quotient-level lift. -/
theorem eqPERLiftQuot_uniq
    {X Y Z : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y)
    (t_q : TreePERMor Z X)
    (heq : treePERMorComp t_q
      (Quotient.mk (treePERSetoid X Y) f) =
      treePERMorComp t_q
      (Quotient.mk (treePERSetoid X Y) g))
    (m : TreePERMor Z
      (eqPERObj hSep hBD f g))
    (hm : treePERMorComp m
      (eqPERIncl hSep hBD f g) = t_q) :
    m = eqPERLiftQuot hSep hBD f g
      t_q heq := by
  revert heq hm
  apply Quotient.inductionOn
    (motive := fun (q : TreePERMor Z X) =>
      (heq : treePERMorComp q _ = _) →
      treePERMorComp m
        (eqPERIncl hSep hBD f g) = q →
      m = eqPERLiftQuot hSep hBD f g
        q heq)
    t_q
  intro t heq_raw hm_raw
  change m = eqPERLift hSep hBD f g t
    (Quotient.exact
      (s := treePERSetoid Z Y) heq_raw)
  exact eqPERLift_uniq hSep hBD f g t _ m
    hm_raw

include hSep hBD in
/-- The IsLimit witness for the equalizer fork. -/
def eqPERFork_isLimit
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    Limits.IsLimit
      (eqPERFork hSep hBD f g) :=
  Limits.Fork.IsLimit.mk _
    (fun s =>
      eqPERLiftQuot hSep hBD f g
        s.ι s.condition)
    (fun s =>
      eqPERLiftQuot_fac hSep hBD f g
        s.ι s.condition)
    (fun s m hm =>
      eqPERLiftQuot_uniq hSep hBD f g
        s.ι s.condition m hm)

include hSep hBD in
/-- HasEqualizer for a pair of pre-morphism
representatives. -/
theorem treePER_hasEqualizer_of_reps
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) :
    Limits.HasEqualizer
      (show X ⟶ Y from
        Quotient.mk (treePERSetoid X Y) f)
      (show X ⟶ Y from
        Quotient.mk (treePERSetoid X Y) g) :=
  Limits.HasLimit.mk
    ⟨eqPERFork hSep hBD f g,
      eqPERFork_isLimit hSep hBD f g⟩

end Equalizers

/-- Every parallel pair in the PER category has an
equalizer (given separator and Boolean dichotomy). -/
theorem treePER_hasEqualizer
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)
    {X Y : @TreePERObj C _ h p}
    (f_q g_q : X ⟶ Y) :
    Limits.HasLimit
      (Limits.parallelPair f_q g_q) := by
  revert f_q g_q
  apply Quotient.ind₂
  intro f g
  exact treePER_hasEqualizer_of_reps
    hSep hBD f g

/-- The PER category has all equalizers (given
separator and Boolean dichotomy). -/
theorem treePER_hasEqualizers
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C) :
    Limits.HasEqualizers
      (@TreePERObj C _ h p) :=
  haveI : ∀ {X Y : @TreePERObj C _ h p}
      (f g : X ⟶ Y),
      Limits.HasLimit
        (Limits.parallelPair f g) :=
    fun f g =>
      treePER_hasEqualizer hSep hBD f g
  Limits.hasEqualizers_of_hasLimit_parallelPair
    (@TreePERObj C _ h p)

/-- The PER category has all finite limits (given
separator and Boolean dichotomy). -/
theorem treePER_hasFiniteLimits
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C) :
    Limits.HasFiniteLimits
      (@TreePERObj C _ h p) :=
  haveI : Limits.HasBinaryProducts
      (@TreePERObj C _ h p) :=
    treePER_hasBinaryProducts hSep hBD
  haveI : Limits.HasFiniteProducts
      (@TreePERObj C _ h p) :=
    hasFiniteProducts_of_has_binary_and_terminal
  haveI : Limits.HasEqualizers
      (@TreePERObj C _ h p) :=
    treePER_hasEqualizers hSep hBD
  Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products

end GebLean
