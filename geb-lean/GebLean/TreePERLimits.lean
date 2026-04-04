import GebLean.TreePER

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

end GebLean
