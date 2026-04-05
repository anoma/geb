import GebLean.TreePER
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Finite Colimits for the PER Category

Constructs finite colimits in the category of partial
equivalence relations (PERs) on the binary tree type T.

The initial PER has the constantly-treeFalse relation,
making its domain empty.  Coproducts of PERs encode
tagged values via the `branch` constructor, with the
coproduct relation dispatching on the tag to check the
corresponding component relation.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-! ## Initial PER -/

/-- The relation for the initial PER: constantly
treeFalse.  No pair of elements is related; the
domain is empty. -/
def initialPERRel :
    cfpProd p.T p.T ⟶ p.T :=
  cfpTerminalFrom (cfpProd p.T p.T) ≫ treeFalse

/-- The initial PER relation is Boolean-valued. -/
theorem initialPERRel_bool :
    initialPERRel ≫ isLeafEndo =
      (initialPERRel :
        cfpProd p.T p.T ⟶ p.T) := by
  unfold initialPERRel
  rw [Category.assoc, isLeafEndo_treeFalse]

/-- The initial PER relation is symmetric. -/
theorem initialPERRel_symm :
    cfpSwap p.T p.T ≫ initialPERRel =
      (initialPERRel :
        cfpProd p.T p.T ⟶ p.T) := by
  unfold initialPERRel
  rw [← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- Composing any morphism into the initial PER
relation yields the constant treeFalse morphism. -/
theorem initialPERRel_const
    {D : C}
    (f : D ⟶ cfpProd p.T p.T) :
    f ≫ initialPERRel =
      cfpTerminalFrom D ≫ treeFalse := by
  unfold initialPERRel
  rw [← Category.assoc]
  congr 1
  exact h.terminal.uniq _

/-- The initial PER relation is transitive. -/
theorem initialPERRel_trans :
    EqTransitive
      (initialPERRel :
        cfpProd p.T p.T ⟶ p.T) := by
  unfold EqTransitive
  set T3 := cfpProd p.T (cfpProd p.T p.T)
  set c : T3 ⟶ p.T :=
    cfpTerminalFrom T3 ≫ treeFalse
  have h1 : cfpLift t3x t3z ≫ initialPERRel =
      c := initialPERRel_const _
  have h2 : cfpLift t3z t3y ≫ initialPERRel =
      c := initialPERRel_const _
  have h3 : cfpLift t3x t3y ≫ initialPERRel =
      c := initialPERRel_const _
  have boolAnd_cc :
      cfpLift c c ≫ boolAnd = c := by
    change cfpLift (cfpTerminalFrom T3 ≫ treeFalse)
      (cfpTerminalFrom T3 ≫ treeFalse) ≫ boolAnd =
      cfpTerminalFrom T3 ≫ treeFalse
    exact boolAnd_treeFalse_left _
  simp only [h1, h2, h3, boolAnd_cc]

/-- The initial PER: no two elements are related.
The relation is constantly treeFalse. -/
def initialPERObj :
    @TreePERObj C _ h p where
  rel := initialPERRel
  rel_bool := initialPERRel_bool
  rel_symm := initialPERRel_symm
  rel_trans := initialPERRel_trans

/-! ## Initial morphism -/

/-- The pre-morphism from the initial PER to any PER.
The underlying map is the identity; the
relation-preservation equation
`boolAnd(initialPERRel, (𝟙 × 𝟙) ≫ X.rel)
  = initialPERRel` holds because
`boolAnd(treeFalse, _) = treeFalse`. -/
def initialPERPreMor
    (X : @TreePERObj C _ h p) :
    TreePERPreMor initialPERObj X where
  map := 𝟙 p.T
  map_rel := by
    change cfpLift initialPERRel
      (cfpMap (𝟙 p.T) (𝟙 p.T) ≫ X.rel) ≫
      boolAnd = initialPERRel
    rw [cfpMap_id, Category.id_comp]
    change cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse) X.rel ≫ boolAnd =
      cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse
    exact boolAnd_treeFalse_left _

/-- Any two pre-morphisms from the initial PER are
equivalent.  The proof uses
`boolAnd_implies_IsLeafConst` with the equation
`boolAnd(cfpTerminalFrom ≫ treeFalse,
  cfpLift f.map g.map ≫ X.rel) =
  cfpTerminalFrom ≫ treeFalse`,
which holds by `boolAnd_treeFalse_left` since the
first argument is constantly treeFalse. -/
theorem initialPERPreMor_unique
    {X : @TreePERObj C _ h p}
    (f g : TreePERPreMor initialPERObj X) :
    treePERMorEqv f g := by
  intro D e hdom
  -- hdom: IsLeafConst(e ≫ cfpLift (𝟙)(𝟙) ≫
  --         initialPERRel).
  have hA :
      cfpLift
        (cfpTerminalFrom p.T ≫ treeFalse)
        (cfpLift f.map g.map ≫ X.rel) ≫
        boolAnd =
      cfpTerminalFrom p.T ≫ treeFalse :=
    boolAnd_treeFalse_left _
  have hB :
      (cfpLift f.map g.map ≫ X.rel) ≫
        isLeafEndo =
      cfpLift f.map g.map ≫ X.rel := by
    rw [Category.assoc, X.rel_bool]
  -- From hdom, derive IsLeafConst
  --   (e ≫ cfpTerminalFrom p.T ≫ treeFalse).
  have hpre : IsLeafConst
      (e ≫ cfpTerminalFrom p.T ≫ treeFalse) := by
    unfold IsLeafConst at hdom ⊢
    -- cfpLift (𝟙) (𝟙) ≫ initialPERRel =
    -- cfpTerminalFrom p.T ≫ treeFalse.
    have step :
        cfpLift (𝟙 p.T) (𝟙 p.T) ≫ initialPERRel =
        cfpTerminalFrom p.T ≫ treeFalse :=
      initialPERRel_const _
    rw [← step]
    exact hdom
  have hconcl :=
    boolAnd_implies_IsLeafConst hA hB e hpre
  exact hconcl

/-- The morphism from the initial PER to any PER in
the PER category. -/
def initialPERMor
    (X : @TreePERObj C _ h p) :
    TreePERMor initialPERObj X :=
  Quotient.mk (treePERSetoid initialPERObj X)
    (initialPERPreMor X)

/-- The initial morphism is unique: any morphism
`initialPERObj ⟶ X` equals `initialPERMor X`. -/
theorem initialPERMor_unique
    {X : @TreePERObj C _ h p}
    (f : TreePERMor initialPERObj X) :
    f = initialPERMor X :=
  Quotient.ind
    (motive := fun f => f = initialPERMor X)
    (fun f' => by
      apply Quotient.sound
        (s := treePERSetoid initialPERObj X)
      exact initialPERPreMor_unique f'
        (initialPERPreMor X))
    f

/-- The initial PER object is initial in the PER
category. -/
def initialPERObj_isInitial :
    Limits.IsInitial
      (initialPERObj : @TreePERObj C _ h p) :=
  Limits.IsInitial.ofUniqueHom
    initialPERMor
    (fun _ m => initialPERMor_unique m)

/-- The PER category has an initial object. -/
instance treePER_hasInitial :
    Limits.HasInitial
      (@TreePERObj C _ h p) :=
  initialPERObj_isInitial.hasInitial

/-! ## Coproduct PER

The coproduct PER of `X` and `Y` encodes tagged
values.  The injections use `branch`: the left
injection sends `x` to `branch(ℓ, x)`, and the right
injection sends `y` to `branch(treeFalse, y)`.
The "tag" of a value is the left component of the
branch, and the "payload" is the right component.
A value belongs to `X` if its tag is leaf, and to
`Y` if its tag is non-leaf.  Two values are
coproduct-related when they have matching tags and
their payloads are component-related in the
corresponding PER.
-/

/-- The left injection as a morphism `T ⟶ T`:
`x ↦ branch(ℓ, x)`. -/
def coprodPERInlMap : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T ≫ p.ℓ) (𝟙 p.T) ≫
    p.β

/-- The right injection as a morphism `T ⟶ T`:
`y ↦ branch(treeFalse, y)`. -/
def coprodPERInrMap : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T ≫ treeFalse)
    (𝟙 p.T) ≫ p.β

/-- The tag of a coproduct-tagged value:
`treeLeftEndo`.  The tag is `ℓ` for left-tagged
values and `treeFalse` for right-tagged values. -/
def coprodPERTag : p.T ⟶ p.T := treeLeftEndo

/-- The payload of a coproduct-tagged value:
`treeRightEndo`. -/
def coprodPERPayload : p.T ⟶ p.T := treeRightEndo

/-- The tag check as a morphism on pairs: extracts
the leaf-ness of the first tree's tag.  Returns `ℓ`
when the first tree is left-tagged and `treeFalse`
when it is right-tagged. -/
def coprodPERFstTagCheck :
    cfpProd p.T p.T ⟶ p.T :=
  cfpFst p.T p.T ≫ coprodPERTag ≫ isLeafEndo

/-- The tag check for the second tree. -/
def coprodPERSndTagCheck :
    cfpProd p.T p.T ⟶ p.T :=
  cfpSnd p.T p.T ≫ coprodPERTag ≫ isLeafEndo

/-- The payload pair of a coproduct pair:
`(payload(t1), payload(t2))`. -/
def coprodPERPayloadPair :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpMap coprodPERPayload coprodPERPayload

/-- The X-relation applied to payloads. -/
def coprodPERXRelCheck
    (X : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  coprodPERPayloadPair ≫ X.rel

/-- The Y-relation applied to payloads. -/
def coprodPERYRelCheck
    (Y : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  coprodPERPayloadPair ≫ Y.rel

/-- The "then branch" of the outer `treeIte`:
when the first tag is leaf (i.e., first tree is
left-tagged), check that the second tag is also
leaf and the payloads are X-related.  Realized as
`treeIte((xRel, treeFalse), sndTag)`. -/
def coprodPERThenBranch
    (X : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (cfpLift (coprodPERXRelCheck X)
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse))
    coprodPERSndTagCheck ≫
    treeIte

/-- The "else branch" of the outer `treeIte`:
when the first tag is non-leaf (i.e., first tree
is right-tagged), check that the second tag is
also non-leaf and the payloads are Y-related.
Realized as `treeIte((treeFalse, yRel), sndTag)`. -/
def coprodPERElseBranch
    (Y : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse)
      (coprodPERYRelCheck Y))
    coprodPERSndTagCheck ≫
    treeIte

/-- The relation for the coproduct PER of `X` and
`Y`:
`coprodPERRel(t1, t2) =
  treeIte((thenBranch, elseBranch), fstTag)`. -/
def coprodPERRel
    (X Y : @TreePERObj C _ h p) :
    cfpProd p.T p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (coprodPERThenBranch X)
      (coprodPERElseBranch Y))
    coprodPERFstTagCheck ≫
    treeIte

/-! ## Coproduct relation properties -/

/-- The X-relation check is Boolean-valued. -/
theorem coprodPERXRelCheck_bool
    (X : @TreePERObj C _ h p) :
    coprodPERXRelCheck X ≫ isLeafEndo =
      coprodPERXRelCheck X := by
  unfold coprodPERXRelCheck
  rw [Category.assoc, X.rel_bool]

/-- The Y-relation check is Boolean-valued. -/
theorem coprodPERYRelCheck_bool
    (Y : @TreePERObj C _ h p) :
    coprodPERYRelCheck Y ≫ isLeafEndo =
      coprodPERYRelCheck Y := by
  unfold coprodPERYRelCheck
  rw [Category.assoc, Y.rel_bool]

/-- The second-tag check is Boolean-valued. -/
theorem coprodPERSndTagCheck_bool :
    (coprodPERSndTagCheck :
      cfpProd p.T p.T ⟶ p.T) ≫
      isLeafEndo =
      coprodPERSndTagCheck := by
  unfold coprodPERSndTagCheck
  rw [Category.assoc, Category.assoc,
    @isLeafEndo_idem C _ h p]

/-- The first-tag check is Boolean-valued. -/
theorem coprodPERFstTagCheck_bool :
    (coprodPERFstTagCheck :
      cfpProd p.T p.T ⟶ p.T) ≫
      isLeafEndo =
      coprodPERFstTagCheck := by
  unfold coprodPERFstTagCheck
  rw [Category.assoc, Category.assoc,
    @isLeafEndo_idem C _ h p]

/-- The "then branch" is Boolean-valued. -/
theorem coprodPERThenBranch_bool
    (X : @TreePERObj C _ h p) :
    coprodPERThenBranch X ≫ isLeafEndo =
      coprodPERThenBranch X := by
  unfold coprodPERThenBranch
  rw [Category.assoc]
  exact treeIte_isLeafEndo_stable
    (coprodPERXRelCheck X)
    (cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse)
    coprodPERSndTagCheck
    (coprodPERXRelCheck_bool X)
    (by rw [Category.assoc,
      isLeafEndo_treeFalse])

/-- The "else branch" is Boolean-valued. -/
theorem coprodPERElseBranch_bool
    (Y : @TreePERObj C _ h p) :
    coprodPERElseBranch Y ≫ isLeafEndo =
      coprodPERElseBranch Y := by
  unfold coprodPERElseBranch
  rw [Category.assoc]
  exact treeIte_isLeafEndo_stable
    (cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse)
    (coprodPERYRelCheck Y)
    coprodPERSndTagCheck
    (by rw [Category.assoc,
      isLeafEndo_treeFalse])
    (coprodPERYRelCheck_bool Y)

/-- The coproduct PER relation is Boolean-valued. -/
theorem coprodPERRel_bool
    (X Y : @TreePERObj C _ h p) :
    coprodPERRel X Y ≫ isLeafEndo =
      coprodPERRel X Y := by
  unfold coprodPERRel
  rw [Category.assoc]
  exact treeIte_isLeafEndo_stable
    (coprodPERThenBranch X)
    (coprodPERElseBranch Y)
    coprodPERFstTagCheck
    (coprodPERThenBranch_bool X)
    (coprodPERElseBranch_bool Y)

/-! ## Quantified coproduct relation

We characterize the coproduct relation via its value
on generalized elements.  For any
`e : D ⟶ cfpProd p.T p.T`, the composition
`e ≫ coprodPERRel X Y` evaluates to one of four
case-defined expressions based on the tag values.
To reason about this we work in the
separator + Boolean dichotomy setting, where global
elements suffice to distinguish morphisms and each
Boolean-valued morphism factors through `ℓ` or
`treeFalse`.
-/

section CoprodProperties

variable
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C)

/-- Expansion of `coprodPERRel X Y` composed with a
generalized element `e`.  Push the `e` through the
nested `cfpLift`/`treeIte` structure. -/
theorem coprodPERRel_precomp
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (X Y : @TreePERObj C _ h p) :
    e ≫ coprodPERRel X Y =
    cfpLift
      (cfpLift
        (e ≫ coprodPERThenBranch X)
        (e ≫ coprodPERElseBranch Y))
      (e ≫ coprodPERFstTagCheck) ≫
    treeIte := by
  unfold coprodPERRel
  rw [← Category.assoc, cfpLift_precomp]
  congr 1
  rw [cfpLift_precomp]

/-- Expansion of `coprodPERThenBranch X` composed
with a generalized element `e`. -/
theorem coprodPERThenBranch_precomp
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (X : @TreePERObj C _ h p) :
    e ≫ coprodPERThenBranch X =
    cfpLift
      (cfpLift
        (e ≫ coprodPERXRelCheck X)
        (cfpTerminalFrom D ≫ treeFalse))
      (e ≫ coprodPERSndTagCheck) ≫
    treeIte := by
  unfold coprodPERThenBranch
  rw [← Category.assoc, cfpLift_precomp]
  have hterm :
      e ≫ cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse =
      cfpTerminalFrom D ≫ treeFalse := by
    rw [← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  rw [cfpLift_precomp, hterm]

/-- Expansion of `coprodPERElseBranch Y` composed
with a generalized element `e`. -/
theorem coprodPERElseBranch_precomp
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (Y : @TreePERObj C _ h p) :
    e ≫ coprodPERElseBranch Y =
    cfpLift
      (cfpLift
        (cfpTerminalFrom D ≫ treeFalse)
        (e ≫ coprodPERYRelCheck Y))
      (e ≫ coprodPERSndTagCheck) ≫
    treeIte := by
  unfold coprodPERElseBranch
  rw [← Category.assoc, cfpLift_precomp]
  have hterm :
      e ≫ cfpTerminalFrom (cfpProd p.T p.T) ≫
        treeFalse =
      cfpTerminalFrom D ≫ treeFalse := by
    rw [← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  rw [cfpLift_precomp, hterm]

/-! ## Global-element evaluation of the coproduct
relation

At a global element (with source `cfpTerminal`),
the tag checks factor through `ℓ` or `treeFalse`.
Using `HasBoolDichotomy`, we case-split and evaluate
`coprodPERRel X Y` explicitly in each of the four
cases for the tag pair. -/

/-- Evaluation of a `treeIte` with a constant leaf
condition at a generalized element: returns the
"then" branch. -/
theorem treeIte_ℓ_applied
    {D : C}
    (X Y : D ⟶ p.T) :
    cfpLift (cfpLift X Y)
      (cfpTerminalFrom D ≫ p.ℓ) ≫
      treeIte = X := by
  have factor :
      cfpLift (cfpLift X Y)
        (cfpTerminalFrom D ≫ p.ℓ) =
      cfpLift X Y ≫
        cfpInsertSnd p.ℓ (cfpProd p.T p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_precomp, Category.comp_id]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact (h.terminal.uniq _).symm
  rw [factor, Category.assoc, treeIte_ℓ,
    cfpLift_fst]

/-- Evaluation of a `treeIte` with a constant
treeFalse condition at a generalized element:
returns the "else" branch.  This is an alias for
`treeIte_treeFalse_applied`. -/
theorem treeIte_tf_applied
    {D : C}
    (X Y : D ⟶ p.T) :
    cfpLift (cfpLift X Y)
      (cfpTerminalFrom D ≫ treeFalse) ≫
      treeIte = Y :=
  treeIte_treeFalse_applied X Y

/-- The coproduct relation at `e`, when
`e ≫ fstTag = ℓ` and `e ≫ sndTag = ℓ`
(both left-tagged), evaluates to
`e ≫ coprodPERXRelCheck X`. -/
theorem coprodPERRel_eval_ℓℓ
    (X Y : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (hfst : e ≫ coprodPERFstTagCheck =
      cfpTerminalFrom D ≫ p.ℓ)
    (hsnd : e ≫ coprodPERSndTagCheck =
      cfpTerminalFrom D ≫ p.ℓ) :
    e ≫ coprodPERRel X Y =
    e ≫ coprodPERXRelCheck X := by
  rw [coprodPERRel_precomp, hfst]
  rw [coprodPERThenBranch_precomp e X, hsnd]
  rw [treeIte_ℓ_applied, treeIte_ℓ_applied]

/-- The coproduct relation at `e`, when
`e ≫ fstTag = ℓ` and `e ≫ sndTag = treeFalse`
(left, right-tagged: mismatch), evaluates to
`cfpTerminalFrom D ≫ treeFalse`. -/
theorem coprodPERRel_eval_ℓtf
    (X Y : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (hfst : e ≫ coprodPERFstTagCheck =
      cfpTerminalFrom D ≫ p.ℓ)
    (hsnd : e ≫ coprodPERSndTagCheck =
      cfpTerminalFrom D ≫ treeFalse) :
    e ≫ coprodPERRel X Y =
    cfpTerminalFrom D ≫ treeFalse := by
  rw [coprodPERRel_precomp, hfst]
  rw [coprodPERThenBranch_precomp e X, hsnd]
  rw [treeIte_tf_applied, treeIte_ℓ_applied]

/-- The coproduct relation at `e`, when
`e ≫ fstTag = treeFalse` and `e ≫ sndTag = ℓ`
(right, left-tagged: mismatch), evaluates to
`cfpTerminalFrom D ≫ treeFalse`. -/
theorem coprodPERRel_eval_tfℓ
    (X Y : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (hfst : e ≫ coprodPERFstTagCheck =
      cfpTerminalFrom D ≫ treeFalse)
    (hsnd : e ≫ coprodPERSndTagCheck =
      cfpTerminalFrom D ≫ p.ℓ) :
    e ≫ coprodPERRel X Y =
    cfpTerminalFrom D ≫ treeFalse := by
  rw [coprodPERRel_precomp, hfst]
  rw [coprodPERElseBranch_precomp e Y, hsnd]
  rw [treeIte_ℓ_applied, treeIte_tf_applied]

/-- The coproduct relation at `e`, when
`e ≫ fstTag = treeFalse` and
`e ≫ sndTag = treeFalse` (both right-tagged),
evaluates to `e ≫ coprodPERYRelCheck Y`. -/
theorem coprodPERRel_eval_tftf
    (X Y : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T p.T)
    (hfst : e ≫ coprodPERFstTagCheck =
      cfpTerminalFrom D ≫ treeFalse)
    (hsnd : e ≫ coprodPERSndTagCheck =
      cfpTerminalFrom D ≫ treeFalse) :
    e ≫ coprodPERRel X Y =
    e ≫ coprodPERYRelCheck Y := by
  rw [coprodPERRel_precomp, hfst]
  rw [coprodPERElseBranch_precomp e Y, hsnd]
  rw [treeIte_tf_applied, treeIte_tf_applied]

/-- Precomposing `coprodPERFstTagCheck` with `cfpSwap`
gives `coprodPERSndTagCheck`. -/
theorem cfpSwap_coprodPERFstTagCheck :
    cfpSwap p.T p.T ≫
      (coprodPERFstTagCheck :
        cfpProd p.T p.T ⟶ p.T) =
    coprodPERSndTagCheck := by
  unfold coprodPERFstTagCheck coprodPERSndTagCheck
    cfpSwap
  rw [← Category.assoc, cfpLift_fst]

/-- Precomposing `coprodPERSndTagCheck` with `cfpSwap`
gives `coprodPERFstTagCheck`. -/
theorem cfpSwap_coprodPERSndTagCheck :
    cfpSwap p.T p.T ≫
      (coprodPERSndTagCheck :
        cfpProd p.T p.T ⟶ p.T) =
    coprodPERFstTagCheck := by
  unfold coprodPERFstTagCheck coprodPERSndTagCheck
    cfpSwap
  rw [← Category.assoc, cfpLift_snd]

/-- Precomposing `coprodPERXRelCheck` with `cfpSwap`
yields itself (by symmetry of `X.rel`). -/
theorem cfpSwap_coprodPERXRelCheck
    (X : @TreePERObj C _ h p) :
    cfpSwap p.T p.T ≫
      coprodPERXRelCheck X =
    coprodPERXRelCheck X := by
  unfold coprodPERXRelCheck coprodPERPayloadPair
  rw [← Category.assoc,
    cfpSwap_cfpMap_diag coprodPERPayload,
    Category.assoc, X.rel_symm]

/-- Precomposing `coprodPERYRelCheck` with `cfpSwap`
yields itself. -/
theorem cfpSwap_coprodPERYRelCheck
    (Y : @TreePERObj C _ h p) :
    cfpSwap p.T p.T ≫
      coprodPERYRelCheck Y =
    coprodPERYRelCheck Y := by
  unfold coprodPERYRelCheck coprodPERPayloadPair
  rw [← Category.assoc,
    cfpSwap_cfpMap_diag coprodPERPayload,
    Category.assoc, Y.rel_symm]

include hSep hBD in
/-- The coproduct PER relation is symmetric. -/
theorem coprodPERRel_symm
    (X Y : @TreePERObj C _ h p) :
    cfpSwap p.T p.T ≫ coprodPERRel X Y =
      coprodPERRel X Y := by
  apply hSep.def
  intro e
  have hf_bool :
      (e ≫ coprodPERFstTagCheck) ≫ isLeafEndo =
      e ≫ coprodPERFstTagCheck := by
    rw [Category.assoc, coprodPERFstTagCheck_bool]
  have hs_bool :
      (e ≫ coprodPERSndTagCheck) ≫ isLeafEndo =
      e ≫ coprodPERSndTagCheck := by
    rw [Category.assoc, coprodPERSndTagCheck_bool]
  have tf_eq :
      cfpTerminalFrom (cfpTerminal (C := C)) ≫
        treeFalse =
      (treeFalse : cfpTerminal (C := C) ⟶ p.T) := by
    rw [cfpTerminalFrom_terminal, Category.id_comp]
  have ℓ_eq :
      cfpTerminalFrom (cfpTerminal (C := C)) ≫
        p.ℓ =
      (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
    rw [cfpTerminalFrom_terminal, Category.id_comp]
  -- Reassociated swap tag checks.
  have swap_fst :
      (e ≫ cfpSwap p.T p.T) ≫
        coprodPERFstTagCheck =
      e ≫ coprodPERSndTagCheck := by
    rw [Category.assoc,
      cfpSwap_coprodPERFstTagCheck]
  have swap_snd :
      (e ≫ cfpSwap p.T p.T) ≫
        coprodPERSndTagCheck =
      e ≫ coprodPERFstTagCheck := by
    rw [Category.assoc,
      cfpSwap_coprodPERSndTagCheck]
  rcases hBD (e ≫ coprodPERFstTagCheck)
    hf_bool with hf | hf <;>
  rcases hBD (e ≫ coprodPERSndTagCheck)
    hs_bool with hs | hs
  · rw [← Category.assoc]
    rw [coprodPERRel_eval_ℓℓ X Y
      (e ≫ cfpSwap p.T p.T)
      (by rw [swap_fst, hs]; exact ℓ_eq.symm)
      (by rw [swap_snd, hf]; exact ℓ_eq.symm)]
    rw [coprodPERRel_eval_ℓℓ X Y e
      (by rw [hf]; exact ℓ_eq.symm)
      (by rw [hs]; exact ℓ_eq.symm)]
    rw [Category.assoc,
      cfpSwap_coprodPERXRelCheck]
  · rw [← Category.assoc]
    rw [coprodPERRel_eval_tfℓ X Y
      (e ≫ cfpSwap p.T p.T)
      (by rw [swap_fst, hs]; exact tf_eq.symm)
      (by rw [swap_snd, hf]; exact ℓ_eq.symm)]
    rw [coprodPERRel_eval_ℓtf X Y e
      (by rw [hf]; exact ℓ_eq.symm)
      (by rw [hs]; exact tf_eq.symm)]
  · rw [← Category.assoc]
    rw [coprodPERRel_eval_ℓtf X Y
      (e ≫ cfpSwap p.T p.T)
      (by rw [swap_fst, hs]; exact ℓ_eq.symm)
      (by rw [swap_snd, hf]; exact tf_eq.symm)]
    rw [coprodPERRel_eval_tfℓ X Y e
      (by rw [hf]; exact tf_eq.symm)
      (by rw [hs]; exact ℓ_eq.symm)]
  · rw [← Category.assoc]
    rw [coprodPERRel_eval_tftf X Y
      (e ≫ cfpSwap p.T p.T)
      (by rw [swap_fst, hs]; exact tf_eq.symm)
      (by rw [swap_snd, hf]; exact tf_eq.symm)]
    rw [coprodPERRel_eval_tftf X Y e
      (by rw [hf]; exact tf_eq.symm)
      (by rw [hs]; exact tf_eq.symm)]
    rw [Category.assoc,
      cfpSwap_coprodPERYRelCheck]

/-! ## Tag check properties on triples -/

/-- Tag projection commutes with `cfpLift t3x t3y`
from `T×(T×T)` to `T×T`: composing with
`coprodPERFstTagCheck` extracts the check on `t3x`. -/
theorem t3xy_coprodPERFstTagCheck :
    (cfpLift t3x t3y ≫
      coprodPERFstTagCheck :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) =
    t3x ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERFstTagCheck
  rw [← Category.assoc, cfpLift_fst]

theorem t3xy_coprodPERSndTagCheck :
    (cfpLift t3x t3y ≫
      coprodPERSndTagCheck :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) =
    t3y ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERSndTagCheck
  rw [← Category.assoc, cfpLift_snd]

theorem t3xz_coprodPERFstTagCheck :
    (cfpLift t3x t3z ≫
      coprodPERFstTagCheck :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) =
    t3x ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERFstTagCheck
  rw [← Category.assoc, cfpLift_fst]

theorem t3xz_coprodPERSndTagCheck :
    (cfpLift t3x t3z ≫
      coprodPERSndTagCheck :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) =
    t3z ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERSndTagCheck
  rw [← Category.assoc, cfpLift_snd]

theorem t3zy_coprodPERFstTagCheck :
    (cfpLift t3z t3y ≫
      coprodPERFstTagCheck :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) =
    t3z ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERFstTagCheck
  rw [← Category.assoc, cfpLift_fst]

theorem t3zy_coprodPERSndTagCheck :
    (cfpLift t3z t3y ≫
      coprodPERSndTagCheck :
      cfpProd p.T (cfpProd p.T p.T) ⟶ p.T) =
    t3y ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERSndTagCheck
  rw [← Category.assoc, cfpLift_snd]

/-- `coprodPERXRelCheck` precomposed with
`cfpLift a b` equals `cfpMap payload payload`
followed by `X.rel`, applied to `a` and `b`. -/
theorem cfpLift_coprodPERXRelCheck
    (X : @TreePERObj C _ h p)
    {D : C}
    (a b : D ⟶ p.T) :
    cfpLift a b ≫ coprodPERXRelCheck X =
    cfpLift (a ≫ coprodPERPayload)
      (b ≫ coprodPERPayload) ≫ X.rel := by
  unfold coprodPERXRelCheck coprodPERPayloadPair
  rw [← Category.assoc, ← cfpLift_cfpMap]

/-- `coprodPERYRelCheck` precomposed with
`cfpLift a b` equals `cfpMap payload payload`
followed by `Y.rel`. -/
theorem cfpLift_coprodPERYRelCheck
    (Y : @TreePERObj C _ h p)
    {D : C}
    (a b : D ⟶ p.T) :
    cfpLift a b ≫ coprodPERYRelCheck Y =
    cfpLift (a ≫ coprodPERPayload)
      (b ≫ coprodPERPayload) ≫ Y.rel := by
  unfold coprodPERYRelCheck coprodPERPayloadPair
  rw [← Category.assoc, ← cfpLift_cfpMap]

/-! ## Transitivity via case analysis -/

/-- The tag value at a coproduct element equals
the element's left component composed with
`isLeafEndo`.  Reformulation: `e ≫ coprodPERTag ≫
isLeafEndo = e ≫ treeLeftEndo ≫ isLeafEndo`. -/
theorem coprodPERTag_eq_treeLeftEndo :
    (coprodPERTag : p.T ⟶ p.T) = treeLeftEndo :=
  rfl

/-- The triple tag morphism on `T×(T×T)`:
extracts the tag of each component.  This maps
a triple of coproduct values to a triple of tags
(each in `{ℓ, treeFalse}`). -/
def t3TagCheck :
    cfpProd p.T (cfpProd p.T p.T) ⟶
    cfpProd p.T (cfpProd p.T p.T) :=
  cfpLift (t3x ≫ coprodPERTag ≫ isLeafEndo)
    (cfpLift (t3y ≫ coprodPERTag ≫ isLeafEndo)
      (t3z ≫ coprodPERTag ≫ isLeafEndo))

/-- The payload triple on `T×(T×T)`:
extracts the payload of each component. -/
def t3PayloadCheck :
    cfpProd p.T (cfpProd p.T p.T) ⟶
    cfpProd p.T (cfpProd p.T p.T) :=
  cfpLift (t3x ≫ coprodPERPayload)
    (cfpLift (t3y ≫ coprodPERPayload)
      (t3z ≫ coprodPERPayload))

/-- Precomposing `coprodPERFstTagCheck` with
`cfpLift a b` extracts the tag check on `a`. -/
theorem cfpLift_coprodPERFstTagCheck
    {D : C}
    (a b : D ⟶ p.T) :
    cfpLift a b ≫ coprodPERFstTagCheck =
    a ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERFstTagCheck
  rw [← Category.assoc, cfpLift_fst]

/-- Precomposing `coprodPERSndTagCheck` with
`cfpLift a b` extracts the tag check on `b`. -/
theorem cfpLift_coprodPERSndTagCheck
    {D : C}
    (a b : D ⟶ p.T) :
    cfpLift a b ≫ coprodPERSndTagCheck =
    b ≫ coprodPERTag ≫ isLeafEndo := by
  unfold coprodPERSndTagCheck
  rw [← Category.assoc, cfpLift_snd]

/-- The tag check `a ≫ coprodPERTag ≫ isLeafEndo`
is Boolean-valued for any `a : D ⟶ p.T`. -/
theorem tagCheck_bool
    {D : C}
    (a : D ⟶ p.T) :
    (a ≫ coprodPERTag ≫ isLeafEndo) ≫
      isLeafEndo =
    a ≫ coprodPERTag ≫ isLeafEndo := by
  rw [Category.assoc, Category.assoc,
    @isLeafEndo_idem C _ h p]

/-- The equation `treeFalse = cfpTerminalFrom
cfpTerminal ≫ treeFalse` on the terminal object. -/
theorem treeFalse_eq_terminal :
    (treeFalse : cfpTerminal (C := C) ⟶ p.T) =
    cfpTerminalFrom cfpTerminal ≫ treeFalse := by
  rw [cfpTerminalFrom_terminal, Category.id_comp]

/-- The equation `p.ℓ = cfpTerminalFrom cfpTerminal ≫
p.ℓ` on the terminal object. -/
theorem ℓ_eq_terminal :
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) =
    cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
  rw [cfpTerminalFrom_terminal, Category.id_comp]

include hBD in
/-- In a degenerate case where `treeFalse = p.ℓ` at
the terminal object, every Boolean-valued morphism
from `cfpTerminal` into `p.T` equals `p.ℓ`.  This
resolves contradictory tag cases in the coproduct
transitivity proof. -/
theorem bool_eq_ℓ_of_treeFalse_eq_ℓ
    (h0 : (treeFalse : cfpTerminal (C := C) ⟶ p.T)
      = p.ℓ)
    (f : cfpTerminal (C := C) ⟶ p.T)
    (hf : f ≫ isLeafEndo = f) :
    f = p.ℓ := by
  rcases hBD f hf with hℓ | htf
  · exact hℓ
  · rw [htf, h0]

include hSep hBD in
/-- Convert an `IsLeafConst` implication (at every
generalized element) into a `boolAnd`-absorption
equation on the underlying Boolean-valued morphisms.
Given that `A` and `B` are Boolean-valued on
`cfpProd A' B'` and that `A(e)` leaf implies `B(e)`
leaf for every global element `e`, the equation
`cfpLift A B ≫ boolAnd = A` holds.  The proof
reduces both sides to global elements via `hSep`
and case-splits on the Boolean values of `A(e)` and
`B(e)` via `hBD`. -/
theorem boolAnd_eq_fst_of_IsLeafConst_impl
    {D : C}
    (A B : D ⟶ p.T)
    (hA_bool : A ≫ isLeafEndo = A)
    (hB_bool : B ≫ isLeafEndo = B)
    (himpl : ∀ e : cfpTerminal (C := C) ⟶ D,
      IsLeafConst (e ≫ A) →
      IsLeafConst (e ≫ B)) :
    cfpLift A B ≫ boolAnd = A := by
  apply hSep.def
  intro e
  rw [← Category.assoc, cfpLift_precomp]
  have eA_bool : (e ≫ A) ≫ isLeafEndo = e ≫ A := by
    rw [Category.assoc, hA_bool]
  have eB_bool : (e ≫ B) ≫ isLeafEndo = e ≫ B := by
    rw [Category.assoc, hB_bool]
  rcases hBD (e ≫ A) eA_bool with hA | hA
  · -- e ≫ A = ℓ; use himpl to get e ≫ B = ℓ.
    have hAlc : IsLeafConst (e ≫ A) := by
      unfold IsLeafConst
      rw [hA, cfpTerminalFrom_terminal,
        Category.id_comp]
    have hBlc := himpl e hAlc
    unfold IsLeafConst at hBlc
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at hBlc
    rw [hA, hBlc, boolAnd_ℓ_ℓ]
  · -- e ≫ A = treeFalse; boolAnd(treeFalse, _) =
    -- treeFalse = e ≫ A.
    rw [hA]
    have tf_eq :
        (treeFalse : cfpTerminal (C := C) ⟶ p.T)
        = cfpTerminalFrom cfpTerminal ≫
          treeFalse := by
      rw [cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [tf_eq, boolAnd_treeFalse_left]

/-- A payload-transitivity helper for the coproduct
transitivity proof.  Given payloads `px, py, pz :
cfpTerminal ⟶ p.T` and equations saying
`X.rel(px, pz) = p.ℓ` and `X.rel(pz, py) = p.ℓ`,
conclude `X.rel(px, py) = p.ℓ`.  This packages the
application of `X.rel_trans_prop` to a concrete
triple element at the terminal object. -/
theorem payload_rel_trans
    (X : @TreePERObj C _ h p)
    {px py pz : cfpTerminal (C := C) ⟶ p.T}
    (hxz : cfpLift px pz ≫ X.rel = p.ℓ)
    (hzy : cfpLift pz py ≫ X.rel = p.ℓ) :
    cfpLift px py ≫ X.rel = p.ℓ := by
  let triple : cfpTerminal (C := C) ⟶
      cfpProd p.T (cfpProd p.T p.T) :=
    cfpLift px (cfpLift py pz)
  have tr_x :
      triple ≫ t3x = px := by
    change cfpLift px (cfpLift py pz) ≫ t3x = px
    unfold t3x
    rw [cfpLift_fst]
  have tr_y :
      triple ≫ t3y = py := by
    change cfpLift px (cfpLift py pz) ≫ t3y = py
    unfold t3y
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_fst]
  have tr_z :
      triple ≫ t3z = pz := by
    change cfpLift px (cfpLift py pz) ≫ t3z = pz
    unfold t3z
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_snd]
  have tr_xz :
      triple ≫ cfpLift t3x t3z ≫ X.rel =
      cfpLift px pz ≫ X.rel := by
    rw [← Category.assoc, cfpLift_precomp, tr_x,
      tr_z]
  have tr_zy :
      triple ≫ cfpLift t3z t3y ≫ X.rel =
      cfpLift pz py ≫ X.rel := by
    rw [← Category.assoc, cfpLift_precomp, tr_z,
      tr_y]
  have tr_xy :
      triple ≫ cfpLift t3x t3y ≫ X.rel =
      cfpLift px py ≫ X.rel := by
    rw [← Category.assoc, cfpLift_precomp, tr_x,
      tr_y]
  have h1 : IsLeafConst
      (triple ≫ cfpLift t3x t3z ≫ X.rel) := by
    unfold IsLeafConst
    rw [tr_xz, hxz, cfpTerminalFrom_terminal,
      Category.id_comp]
  have h2 : IsLeafConst
      (triple ≫ cfpLift t3z t3y ≫ X.rel) := by
    unfold IsLeafConst
    rw [tr_zy, hzy, cfpTerminalFrom_terminal,
      Category.id_comp]
  have h3 := X.rel_trans_prop triple h1 h2
  unfold IsLeafConst at h3
  rw [tr_xy, cfpTerminalFrom_terminal,
    Category.id_comp] at h3
  exact h3

include hSep hBD in
/-- Quantified transitivity for the coproduct PER
relation.  Under the separator and Boolean
dichotomy hypotheses, we reduce transitivity to a
check at global elements and case-split on the
tag values of the three tree components.  When
all three tags agree (all leaf or all branch),
the relation reduces to the appropriate component
PER's relation and transitivity follows.  When
tags disagree, the hypothesis forces an equation
`treeFalse = p.ℓ`, which collapses the goal. -/
theorem coprodPERRel_quantTransitive
    (X Y : @TreePERObj C _ h p) :
    QuantTransitive (coprodPERRel X Y) := by
  intro D e hxz hzy
  unfold IsLeafConst
  apply hSep.def
  intro d
  have d_term :
      d ≫ cfpTerminalFrom D =
      cfpTerminalFrom (cfpTerminal (C := C)) :=
    h.terminal.uniq _
  have rhs_simp :
      d ≫ cfpTerminalFrom D ≫ p.ℓ =
      (p.ℓ : cfpTerminal (C := C) ⟶ p.T) := by
    rw [← Category.assoc, d_term,
      cfpTerminalFrom_terminal, Category.id_comp]
  rw [rhs_simp]
  have hxz' :
      (d ≫ e) ≫ cfpLift t3x t3z ≫
        coprodPERRel X Y = p.ℓ := by
    unfold IsLeafConst at hxz
    rw [Category.assoc, hxz, ← Category.assoc,
      d_term, cfpTerminalFrom_terminal,
      Category.id_comp]
  have hzy' :
      (d ≫ e) ≫ cfpLift t3z t3y ≫
        coprodPERRel X Y = p.ℓ := by
    unfold IsLeafConst at hzy
    rw [Category.assoc, hzy, ← Category.assoc,
      d_term, cfpTerminalFrom_terminal,
      Category.id_comp]
  -- Set up tag values at the global element d ≫ e.
  set tx : cfpTerminal (C := C) ⟶ p.T :=
    (d ≫ e) ≫ t3x with tx_def
  set ty : cfpTerminal (C := C) ⟶ p.T :=
    (d ≫ e) ≫ t3y with ty_def
  set tz : cfpTerminal (C := C) ⟶ p.T :=
    (d ≫ e) ≫ t3z with tz_def
  have e_xz :
      (d ≫ e) ≫ cfpLift t3x t3z =
      cfpLift tx tz := by
    rw [cfpLift_precomp]
  have e_zy :
      (d ≫ e) ≫ cfpLift t3z t3y =
      cfpLift tz ty := by
    rw [cfpLift_precomp]
  have e_xy :
      (d ≫ e) ≫ cfpLift t3x t3y =
      cfpLift tx ty := by
    rw [cfpLift_precomp]
  rw [← Category.assoc, e_xz] at hxz'
  rw [← Category.assoc, e_zy] at hzy'
  rw [show d ≫ e ≫ cfpLift t3x t3y ≫
    coprodPERRel X Y =
    cfpLift tx ty ≫ coprodPERRel X Y by
    rw [← Category.assoc, ← Category.assoc,
      e_xy]]
  -- Tag boolean checks.
  have txTag_bool :
      (tx ≫ coprodPERTag ≫ isLeafEndo) ≫
        isLeafEndo =
      tx ≫ coprodPERTag ≫ isLeafEndo :=
    tagCheck_bool tx
  have tyTag_bool :
      (ty ≫ coprodPERTag ≫ isLeafEndo) ≫
        isLeafEndo =
      ty ≫ coprodPERTag ≫ isLeafEndo :=
    tagCheck_bool ty
  have tzTag_bool :
      (tz ≫ coprodPERTag ≫ isLeafEndo) ≫
        isLeafEndo =
      tz ≫ coprodPERTag ≫ isLeafEndo :=
    tagCheck_bool tz
  -- Fst/Snd tag checks on cfpLift decompositions.
  have fst_xz :
      cfpLift tx tz ≫ coprodPERFstTagCheck =
      cfpTerminalFrom cfpTerminal ≫
        (tx ≫ coprodPERTag ≫ isLeafEndo) := by
    rw [cfpLift_coprodPERFstTagCheck,
      cfpTerminalFrom_terminal, Category.id_comp]
  have snd_xz :
      cfpLift tx tz ≫ coprodPERSndTagCheck =
      cfpTerminalFrom cfpTerminal ≫
        (tz ≫ coprodPERTag ≫ isLeafEndo) := by
    rw [cfpLift_coprodPERSndTagCheck,
      cfpTerminalFrom_terminal, Category.id_comp]
  have fst_zy :
      cfpLift tz ty ≫ coprodPERFstTagCheck =
      cfpTerminalFrom cfpTerminal ≫
        (tz ≫ coprodPERTag ≫ isLeafEndo) := by
    rw [cfpLift_coprodPERFstTagCheck,
      cfpTerminalFrom_terminal, Category.id_comp]
  have snd_zy :
      cfpLift tz ty ≫ coprodPERSndTagCheck =
      cfpTerminalFrom cfpTerminal ≫
        (ty ≫ coprodPERTag ≫ isLeafEndo) := by
    rw [cfpLift_coprodPERSndTagCheck,
      cfpTerminalFrom_terminal, Category.id_comp]
  have fst_xy :
      cfpLift tx ty ≫ coprodPERFstTagCheck =
      cfpTerminalFrom cfpTerminal ≫
        (tx ≫ coprodPERTag ≫ isLeafEndo) := by
    rw [cfpLift_coprodPERFstTagCheck,
      cfpTerminalFrom_terminal, Category.id_comp]
  have snd_xy :
      cfpLift tx ty ≫ coprodPERSndTagCheck =
      cfpTerminalFrom cfpTerminal ≫
        (ty ≫ coprodPERTag ≫ isLeafEndo) := by
    rw [cfpLift_coprodPERSndTagCheck,
      cfpTerminalFrom_terminal, Category.id_comp]
  -- Case-split on tags via dichotomy.
  rcases hBD (tx ≫ coprodPERTag ≫ isLeafEndo)
    txTag_bool with htx | htx <;>
  rcases hBD (ty ≫ coprodPERTag ≫ isLeafEndo)
    tyTag_bool with hty | hty <;>
  rcases hBD (tz ≫ coprodPERTag ≫ isLeafEndo)
    tzTag_bool with htz | htz
  -- Case ℓℓℓ: all three tags are leaf.
  · rw [coprodPERRel_eval_ℓℓ X Y (cfpLift tx tz)
      (by rw [fst_xz, htx]) (by rw [snd_xz, htz])]
      at hxz'
    rw [coprodPERRel_eval_ℓℓ X Y (cfpLift tz ty)
      (by rw [fst_zy, htz]) (by rw [snd_zy, hty])]
      at hzy'
    rw [coprodPERRel_eval_ℓℓ X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    -- Now the goal is about X.rel on payloads.
    -- Build the triple element for X.rel_trans_prop.
    rw [cfpLift_coprodPERXRelCheck X] at hxz' hzy'
    rw [cfpLift_coprodPERXRelCheck X]
    exact payload_rel_trans X hxz' hzy'
  -- Case ℓℓtf: (tx=ℓ, ty=ℓ, tz=tf).  XZ mismatch:
  -- cfpLift tx tz ≫ rel reduces via eval_ℓtf to
  -- treeFalse, giving hxz' : treeFalse = ℓ.
  · rw [coprodPERRel_eval_ℓtf X Y (cfpLift tx tz)
      (by rw [fst_xz, htx]) (by rw [snd_xz, htz])]
      at hxz'
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at hxz'
    rw [coprodPERRel_eval_ℓℓ X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    exact bool_eq_ℓ_of_treeFalse_eq_ℓ hBD hxz'
      (cfpLift tx ty ≫ coprodPERXRelCheck X)
      (by rw [Category.assoc,
        coprodPERXRelCheck_bool X])
  -- Case ℓtfℓ: (tx=ℓ, ty=tf, tz=ℓ).  ZY mismatch.
  · rw [coprodPERRel_eval_ℓtf X Y (cfpLift tz ty)
      (by rw [fst_zy, htz]) (by rw [snd_zy, hty])]
      at hzy'
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at hzy'
    rw [coprodPERRel_eval_ℓtf X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    rw [cfpTerminalFrom_terminal, Category.id_comp]
    exact hzy'
  -- Case ℓtftf: (tx=ℓ, ty=tf, tz=tf).  XZ mismatch.
  · rw [coprodPERRel_eval_ℓtf X Y (cfpLift tx tz)
      (by rw [fst_xz, htx]) (by rw [snd_xz, htz])]
      at hxz'
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at hxz'
    rw [coprodPERRel_eval_ℓtf X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    rw [cfpTerminalFrom_terminal, Category.id_comp]
    exact hxz'
  -- Case tfℓℓ: (tx=tf, ty=ℓ, tz=ℓ).  XZ mismatch.
  · rw [coprodPERRel_eval_tfℓ X Y (cfpLift tx tz)
      (by rw [fst_xz, htx]) (by rw [snd_xz, htz])]
      at hxz'
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at hxz'
    rw [coprodPERRel_eval_tfℓ X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    rw [cfpTerminalFrom_terminal, Category.id_comp]
    exact hxz'
  -- Case tfℓtf: (tx=tf, ty=ℓ, tz=tf).  ZY mismatch.
  · rw [coprodPERRel_eval_tfℓ X Y (cfpLift tz ty)
      (by rw [fst_zy, htz]) (by rw [snd_zy, hty])]
      at hzy'
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at hzy'
    rw [coprodPERRel_eval_tfℓ X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    rw [cfpTerminalFrom_terminal, Category.id_comp]
    exact hzy'
  -- Case tftfℓ: (tx=tf, ty=tf, tz=ℓ).  XZ mismatch:
  -- XZ reduces via eval_tfℓ to treeFalse.
  · rw [coprodPERRel_eval_tfℓ X Y (cfpLift tx tz)
      (by rw [fst_xz, htx]) (by rw [snd_xz, htz])]
      at hxz'
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at hxz'
    rw [coprodPERRel_eval_tftf X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    exact bool_eq_ℓ_of_treeFalse_eq_ℓ hBD hxz'
      (cfpLift tx ty ≫ coprodPERYRelCheck Y)
      (by rw [Category.assoc,
        coprodPERYRelCheck_bool Y])
  -- Case tftftf: all three tags are treeFalse.
  · rw [coprodPERRel_eval_tftf X Y (cfpLift tx tz)
      (by rw [fst_xz, htx]) (by rw [snd_xz, htz])]
      at hxz'
    rw [coprodPERRel_eval_tftf X Y (cfpLift tz ty)
      (by rw [fst_zy, htz]) (by rw [snd_zy, hty])]
      at hzy'
    rw [coprodPERRel_eval_tftf X Y (cfpLift tx ty)
      (by rw [fst_xy, htx]) (by rw [snd_xy, hty])]
    rw [cfpLift_coprodPERYRelCheck Y] at hxz' hzy'
    rw [cfpLift_coprodPERYRelCheck Y]
    exact payload_rel_trans Y hxz' hzy'

include hSep hBD in
/-- Equational transitivity for the coproduct PER
relation, obtained by converting quantified
transitivity via `quantTransitive_implies_eq`. -/
theorem coprodPERRel_eqTransitive
    (X Y : @TreePERObj C _ h p) :
    EqTransitive (coprodPERRel X Y) :=
  quantTransitive_implies_eq hSep hBD
    (coprodPERRel_bool X Y)
    (coprodPERRel_quantTransitive hSep hBD X Y)

/-! ### Injection helper lemmas -/

/-- The tag of `coprodPERInlMap` is `ℓ`:
`coprodPERInlMap ≫ coprodPERTag = cfpTerminalFrom
≫ p.ℓ`. -/
theorem coprodPERInlMap_tag :
    coprodPERInlMap ≫ coprodPERTag =
    cfpTerminalFrom p.T ≫ p.ℓ := by
  unfold coprodPERInlMap coprodPERTag
  rw [Category.assoc, β_treeLeftEndo, cfpLift_fst]

/-- The tag of `coprodPERInrMap` is `treeFalse`:
`coprodPERInrMap ≫ coprodPERTag = cfpTerminalFrom
≫ treeFalse`. -/
theorem coprodPERInrMap_tag :
    coprodPERInrMap ≫ coprodPERTag =
    cfpTerminalFrom p.T ≫ treeFalse := by
  unfold coprodPERInrMap coprodPERTag
  rw [Category.assoc, β_treeLeftEndo, cfpLift_fst]

/-- The payload of `coprodPERInlMap` is the
identity: `coprodPERInlMap ≫ coprodPERPayload =
𝟙 p.T`. -/
theorem coprodPERInlMap_payload :
    coprodPERInlMap ≫ coprodPERPayload =
    𝟙 p.T := by
  unfold coprodPERInlMap coprodPERPayload
  rw [Category.assoc, β_treeRightEndo, cfpLift_snd]

/-- The payload of `coprodPERInrMap` is the
identity: `coprodPERInrMap ≫ coprodPERPayload =
𝟙 p.T`. -/
theorem coprodPERInrMap_payload :
    coprodPERInrMap ≫ coprodPERPayload =
    𝟙 p.T := by
  unfold coprodPERInrMap coprodPERPayload
  rw [Category.assoc, β_treeRightEndo, cfpLift_snd]

/-- `coprodPERInlMap ≫ coprodPERTag ≫ isLeafEndo =
cfpTerminalFrom p.T ≫ p.ℓ`: the tag check of the
left injection is leaf. -/
theorem coprodPERInlMap_tagCheck :
    coprodPERInlMap ≫ coprodPERTag ≫ isLeafEndo =
    cfpTerminalFrom p.T ≫ p.ℓ := by
  rw [← Category.assoc, coprodPERInlMap_tag,
    Category.assoc, isLeafEndo_ℓ]

/-- `coprodPERInrMap ≫ coprodPERTag ≫ isLeafEndo =
cfpTerminalFrom p.T ≫ treeFalse`: the tag check of
the right injection is treeFalse. -/
theorem coprodPERInrMap_tagCheck :
    coprodPERInrMap ≫ coprodPERTag ≫ isLeafEndo =
    cfpTerminalFrom p.T ≫ treeFalse := by
  rw [← Category.assoc, coprodPERInrMap_tag,
    Category.assoc,
    @isLeafEndo_treeFalse C _ h p]

theorem cfpMap_inl_coprodPERFstTagCheck :
    cfpMap coprodPERInlMap coprodPERInlMap ≫
      (coprodPERFstTagCheck :
        cfpProd p.T p.T ⟶ p.T) =
    cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ := by
  unfold coprodPERFstTagCheck cfpMap
  rw [← Category.assoc, cfpLift_fst, Category.assoc,
    coprodPERInlMap_tagCheck, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

theorem cfpMap_inl_coprodPERSndTagCheck :
    cfpMap coprodPERInlMap coprodPERInlMap ≫
      (coprodPERSndTagCheck :
        cfpProd p.T p.T ⟶ p.T) =
    cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ := by
  unfold coprodPERSndTagCheck cfpMap
  rw [← Category.assoc, cfpLift_snd, Category.assoc,
    coprodPERInlMap_tagCheck, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

theorem cfpMap_inr_coprodPERFstTagCheck :
    cfpMap coprodPERInrMap coprodPERInrMap ≫
      (coprodPERFstTagCheck :
        cfpProd p.T p.T ⟶ p.T) =
    cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse := by
  unfold coprodPERFstTagCheck cfpMap
  rw [← Category.assoc, cfpLift_fst, Category.assoc,
    coprodPERInrMap_tagCheck, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

theorem cfpMap_inr_coprodPERSndTagCheck :
    cfpMap coprodPERInrMap coprodPERInrMap ≫
      (coprodPERSndTagCheck :
        cfpProd p.T p.T ⟶ p.T) =
    cfpTerminalFrom (cfpProd p.T p.T) ≫
      treeFalse := by
  unfold coprodPERSndTagCheck cfpMap
  rw [← Category.assoc, cfpLift_snd, Category.assoc,
    coprodPERInrMap_tagCheck, ← Category.assoc]
  congr 1
  exact h.terminal.uniq _

include hSep in
/-- The coproduct relation applied to the pair
`(inl(a), inl(b))` equals `X.rel(a, b)`: the left
injection preserves the left component's relation.
Equationally: `cfpMap inlMap inlMap ≫
coprodPERRel X Y = X.rel`. -/
theorem cfpMap_inl_inl_coprodPERRel
    (X Y : @TreePERObj C _ h p) :
    cfpMap coprodPERInlMap coprodPERInlMap ≫
      coprodPERRel X Y = X.rel := by
  apply hSep.def
  intro e
  -- Use hBD to case split on the tag of the
  -- first component of e.  But both inl-tags are
  -- ℓ, so the case is always ℓℓ and reduces to
  -- X.rel on payloads.
  rw [← Category.assoc]
  set e' : cfpTerminal (C := C) ⟶
    cfpProd p.T p.T := e ≫ cfpMap coprodPERInlMap
      coprodPERInlMap
  have e_fst :
      e' ≫ coprodPERFstTagCheck =
      cfpTerminalFrom (cfpTerminal (C := C)) ≫
        p.ℓ := by
    change (e ≫ cfpMap coprodPERInlMap
      coprodPERInlMap) ≫ coprodPERFstTagCheck = _
    rw [Category.assoc,
      cfpMap_inl_coprodPERFstTagCheck,
      ← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  have e_snd :
      e' ≫ coprodPERSndTagCheck =
      cfpTerminalFrom (cfpTerminal (C := C)) ≫
        p.ℓ := by
    change (e ≫ cfpMap coprodPERInlMap
      coprodPERInlMap) ≫ coprodPERSndTagCheck = _
    rw [Category.assoc,
      cfpMap_inl_coprodPERSndTagCheck,
      ← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  rw [coprodPERRel_eval_ℓℓ X Y e' e_fst e_snd]
  unfold coprodPERXRelCheck coprodPERPayloadPair
  change (e ≫ cfpMap coprodPERInlMap
    coprodPERInlMap) ≫ cfpMap coprodPERPayload
    coprodPERPayload ≫ X.rel = _
  rw [show (e ≫ cfpMap coprodPERInlMap
    coprodPERInlMap) ≫ cfpMap coprodPERPayload
    coprodPERPayload ≫ X.rel =
    e ≫ (cfpMap coprodPERInlMap coprodPERInlMap ≫
      cfpMap coprodPERPayload coprodPERPayload) ≫
      X.rel by
    simp only [Category.assoc]]
  rw [← cfpMap_comp_comp, coprodPERInlMap_payload,
    cfpMap_id, Category.id_comp]

include hSep in
/-- The coproduct relation applied to the pair
`(inr(a), inr(b))` equals `Y.rel(a, b)`.
Equationally: `cfpMap inrMap inrMap ≫
coprodPERRel X Y = Y.rel`. -/
theorem cfpMap_inr_inr_coprodPERRel
    (X Y : @TreePERObj C _ h p) :
    cfpMap coprodPERInrMap coprodPERInrMap ≫
      coprodPERRel X Y = Y.rel := by
  apply hSep.def
  intro e
  rw [← Category.assoc]
  set e' : cfpTerminal (C := C) ⟶
    cfpProd p.T p.T := e ≫ cfpMap coprodPERInrMap
      coprodPERInrMap
  have e_fst :
      e' ≫ coprodPERFstTagCheck =
      cfpTerminalFrom (cfpTerminal (C := C)) ≫
        treeFalse := by
    change (e ≫ cfpMap coprodPERInrMap
      coprodPERInrMap) ≫ coprodPERFstTagCheck = _
    rw [Category.assoc,
      cfpMap_inr_coprodPERFstTagCheck,
      ← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  have e_snd :
      e' ≫ coprodPERSndTagCheck =
      cfpTerminalFrom (cfpTerminal (C := C)) ≫
        treeFalse := by
    change (e ≫ cfpMap coprodPERInrMap
      coprodPERInrMap) ≫ coprodPERSndTagCheck = _
    rw [Category.assoc,
      cfpMap_inr_coprodPERSndTagCheck,
      ← Category.assoc]
    congr 1
    exact h.terminal.uniq _
  rw [coprodPERRel_eval_tftf X Y e' e_fst e_snd]
  unfold coprodPERYRelCheck coprodPERPayloadPair
  change (e ≫ cfpMap coprodPERInrMap
    coprodPERInrMap) ≫ cfpMap coprodPERPayload
    coprodPERPayload ≫ Y.rel = _
  rw [show (e ≫ cfpMap coprodPERInrMap
    coprodPERInrMap) ≫ cfpMap coprodPERPayload
    coprodPERPayload ≫ Y.rel =
    e ≫ (cfpMap coprodPERInrMap coprodPERInrMap ≫
      cfpMap coprodPERPayload coprodPERPayload) ≫
      Y.rel by
    simp only [Category.assoc]]
  rw [← cfpMap_comp_comp, coprodPERInrMap_payload,
    cfpMap_id, Category.id_comp]

/-- The coproduct PER of `X` and `Y`: trees `t`
whose tag determines which component PER the
payload must belong to, with the appropriate
component relation on payloads. -/
def coprodPERObj
    (X Y : @TreePERObj C _ h p) :
    @TreePERObj C _ h p where
  rel := coprodPERRel X Y
  rel_bool := coprodPERRel_bool X Y
  rel_symm := coprodPERRel_symm hSep hBD X Y
  rel_trans := coprodPERRel_eqTransitive hSep hBD X Y

/-! ## Coproduct injections -/

include hSep in
/-- The left injection pre-morphism from `X` to the
coproduct PER: the underlying map is
`coprodPERInlMap`. -/
def coprodPERInlPreMor
    (X Y : @TreePERObj C _ h p) :
    TreePERPreMor X (coprodPERObj hSep hBD X Y) where
  map := coprodPERInlMap
  map_rel := by
    change cfpLift X.rel
      (cfpMap coprodPERInlMap coprodPERInlMap ≫
        coprodPERRel X Y) ≫ boolAnd = X.rel
    rw [cfpMap_inl_inl_coprodPERRel hSep X Y]
    have lift_eq :
        cfpLift X.rel X.rel =
        X.rel ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [lift_eq, Category.assoc, boolAnd_idem,
      X.rel_bool]

include hSep in
/-- The right injection pre-morphism from `Y` to
the coproduct PER: the underlying map is
`coprodPERInrMap`. -/
def coprodPERInrPreMor
    (X Y : @TreePERObj C _ h p) :
    TreePERPreMor Y (coprodPERObj hSep hBD X Y) where
  map := coprodPERInrMap
  map_rel := by
    change cfpLift Y.rel
      (cfpMap coprodPERInrMap coprodPERInrMap ≫
        coprodPERRel X Y) ≫ boolAnd = Y.rel
    rw [cfpMap_inr_inr_coprodPERRel hSep X Y]
    have lift_eq :
        cfpLift Y.rel Y.rel =
        Y.rel ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [lift_eq, Category.assoc, boolAnd_idem,
      Y.rel_bool]

/-- The left injection morphism in the PER
category. -/
def coprodPERInl
    (X Y : @TreePERObj C _ h p) :
    TreePERMor X (coprodPERObj hSep hBD X Y) :=
  Quotient.mk
    (treePERSetoid X (coprodPERObj hSep hBD X Y))
    (coprodPERInlPreMor hSep hBD X Y)

/-- The right injection morphism in the PER
category. -/
def coprodPERInr
    (X Y : @TreePERObj C _ h p) :
    TreePERMor Y (coprodPERObj hSep hBD X Y) :=
  Quotient.mk
    (treePERSetoid Y (coprodPERObj hSep hBD X Y))
    (coprodPERInrPreMor hSep hBD X Y)

/-! ## Copairing -/

/-- The copair map underlying `coprodPERCopair`:
given `fMap gMap : p.T ⟶ p.T` playing the role of
the underlying maps of `f : X → Z` and `g : Y → Z`,
the copair dispatches on the tag of its input and
applies the corresponding map to the payload.
`copairMap(t) = if tag(t) = ℓ then f(payload(t))
  else g(payload(t))`. -/
def coprodPERCopairMap
    (fMap gMap : p.T ⟶ p.T) : p.T ⟶ p.T :=
  cfpLift
    (cfpLift (coprodPERPayload ≫ fMap)
      (coprodPERPayload ≫ gMap))
    (coprodPERTag ≫ isLeafEndo) ≫
    treeIte

/-- Value of `coprodPERCopairMap f g` at a
generalized element: expanded via `treeIte`. -/
theorem coprodPERCopairMap_precomp
    (fMap gMap : p.T ⟶ p.T)
    {D : C} (e : D ⟶ p.T) :
    e ≫ coprodPERCopairMap fMap gMap =
    cfpLift
      (cfpLift (e ≫ coprodPERPayload ≫ fMap)
        (e ≫ coprodPERPayload ≫ gMap))
      (e ≫ coprodPERTag ≫ isLeafEndo) ≫
    treeIte := by
  unfold coprodPERCopairMap
  rw [← Category.assoc, cfpLift_precomp]
  congr 1
  rw [cfpLift_precomp]

/-- Value of `coprodPERCopairMap` at a tagged-left
global element: reduces to `fMap` applied to the
payload. -/
theorem coprodPERCopairMap_ℓ
    (fMap gMap : p.T ⟶ p.T)
    {D : C} (e : D ⟶ p.T)
    (htag : e ≫ coprodPERTag ≫ isLeafEndo =
      cfpTerminalFrom D ≫ p.ℓ) :
    e ≫ coprodPERCopairMap fMap gMap =
    e ≫ coprodPERPayload ≫ fMap := by
  rw [coprodPERCopairMap_precomp, htag,
    treeIte_ℓ_applied]

/-- Value of `coprodPERCopairMap` at a
tagged-treeFalse global element: reduces to `gMap`
applied to the payload. -/
theorem coprodPERCopairMap_tf
    (fMap gMap : p.T ⟶ p.T)
    {D : C} (e : D ⟶ p.T)
    (htag : e ≫ coprodPERTag ≫ isLeafEndo =
      cfpTerminalFrom D ≫ treeFalse) :
    e ≫ coprodPERCopairMap fMap gMap =
    e ≫ coprodPERPayload ≫ gMap := by
  rw [coprodPERCopairMap_precomp, htag,
    treeIte_tf_applied]

/-- The copair map commutes through `treeLeftEndo`
for the left injection: `coprodPERInlMap ≫
coprodPERCopairMap fMap gMap = fMap`. -/
theorem coprodPERInlMap_copair
    (fMap gMap : p.T ⟶ p.T) :
    coprodPERInlMap ≫
      coprodPERCopairMap fMap gMap = fMap := by
  rw [coprodPERCopairMap_ℓ fMap gMap
    coprodPERInlMap]
  · rw [← Category.assoc, coprodPERInlMap_payload,
      Category.id_comp]
  · rw [← Category.assoc, coprodPERInlMap_tag,
      Category.assoc, isLeafEndo_ℓ]

/-- The copair map commutes through `treeLeftEndo`
for the right injection: `coprodPERInrMap ≫
coprodPERCopairMap fMap gMap = gMap`. -/
theorem coprodPERInrMap_copair
    (fMap gMap : p.T ⟶ p.T) :
    coprodPERInrMap ≫
      coprodPERCopairMap fMap gMap = gMap := by
  rw [coprodPERCopairMap_tf fMap gMap
    coprodPERInrMap]
  · rw [← Category.assoc, coprodPERInrMap_payload,
      Category.id_comp]
  · rw [← Category.assoc, coprodPERInrMap_tag,
      Category.assoc,
      @isLeafEndo_treeFalse C _ h p]

include hSep hBD in
/-- The `map_rel` condition for the copair
pre-morphism.  Given `f : X → Z` and `g : Y → Z`,
the equation
`boolAnd(coprodPERRel X Y, (copair × copair) ≫
  Z.rel) = coprodPERRel X Y` holds.  The proof
uses `boolAnd_eq_fst_of_IsLeafConst_impl` to
reduce to an implication on leaf-constant elements,
then case-analyses tags of both components to
either use `f.map_rel` (left), `g.map_rel` (right),
or observe that the hypothesis already contradicts
the mismatched tag case. -/
theorem coprodPERCopairPreMor_map_rel
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERPreMor X Z)
    (g : TreePERPreMor Y Z) :
    cfpLift (coprodPERRel X Y)
      (cfpMap (coprodPERCopairMap f.map g.map)
        (coprodPERCopairMap f.map g.map) ≫
        Z.rel) ≫ boolAnd =
    coprodPERRel X Y := by
  have A_bool := coprodPERRel_bool X Y
  have B_bool :
      (cfpMap (coprodPERCopairMap f.map g.map)
        (coprodPERCopairMap f.map g.map) ≫
        Z.rel) ≫ isLeafEndo =
      cfpMap (coprodPERCopairMap f.map g.map)
        (coprodPERCopairMap f.map g.map) ≫ Z.rel := by
    rw [Category.assoc, Z.rel_bool]
  apply boolAnd_eq_fst_of_IsLeafConst_impl hSep hBD
    _ _ A_bool B_bool
  intro e hlc
  -- hlc : IsLeafConst(e ≫ coprodPERRel X Y)
  -- i.e., e ≫ coprodPERRel X Y = ℓ (since source
  -- is cfpTerminal).
  unfold IsLeafConst at hlc
  rw [cfpTerminalFrom_terminal, Category.id_comp]
    at hlc
  unfold IsLeafConst
  rw [cfpTerminalFrom_terminal, Category.id_comp]
  -- Case-split on tags of e's components.
  set tx : cfpTerminal (C := C) ⟶ p.T :=
    e ≫ cfpFst p.T p.T ≫ coprodPERTag ≫ isLeafEndo
    with tx_def
  set ty : cfpTerminal (C := C) ⟶ p.T :=
    e ≫ cfpSnd p.T p.T ≫ coprodPERTag ≫ isLeafEndo
    with ty_def
  have tx_bool : tx ≫ isLeafEndo = tx := by
    rw [tx_def]
    simp only [Category.assoc]
    rw [@isLeafEndo_idem C _ h p]
  have ty_bool : ty ≫ isLeafEndo = ty := by
    rw [ty_def]
    simp only [Category.assoc]
    rw [@isLeafEndo_idem C _ h p]
  have efst :
      e ≫ coprodPERFstTagCheck =
      cfpTerminalFrom cfpTerminal ≫ tx := by
    unfold coprodPERFstTagCheck
    rw [tx_def, cfpTerminalFrom_terminal,
      Category.id_comp]
  have esnd :
      e ≫ coprodPERSndTagCheck =
      cfpTerminalFrom cfpTerminal ≫ ty := by
    unfold coprodPERSndTagCheck
    rw [ty_def, cfpTerminalFrom_terminal,
      Category.id_comp]
  -- Reduce `e ≫ cfpMap copair copair ≫ Z.rel` to
  -- `cfpLift (fst ≫ copair) (snd ≫ copair) ≫ Z.rel`.
  rw [show e ≫ cfpMap
      (coprodPERCopairMap f.map g.map)
      (coprodPERCopairMap f.map g.map) ≫ Z.rel =
      cfpLift
        ((e ≫ cfpFst p.T p.T) ≫
          coprodPERCopairMap f.map g.map)
        ((e ≫ cfpSnd p.T p.T) ≫
          coprodPERCopairMap f.map g.map) ≫
      Z.rel by
    rw [← Category.assoc]
    congr 1
    unfold cfpMap
    rw [cfpLift_precomp]
    congr 1 <;> simp only [Category.assoc]]
  rcases hBD tx tx_bool with hx | hx <;>
  rcases hBD ty ty_bool with hy | hy
  -- Case ℓℓ: tags both leaf.  copair ≫ fst = ... ≫
  -- f.map; rel reduces to X.rel on payloads; use
  -- hlc (which is X.rel on payloads = ℓ by
  -- eval_ℓℓ) and f.map_rel to get Z.rel = ℓ.
  · have hx_full : (e ≫ cfpFst p.T p.T) ≫
        coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
      rw [← hx, tx_def, cfpTerminalFrom_terminal,
        Category.id_comp]
      simp only [Category.assoc]
    have hy_full : (e ≫ cfpSnd p.T p.T) ≫
        coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
      rw [← hy, ty_def, cfpTerminalFrom_terminal,
        Category.id_comp]
      simp only [Category.assoc]
    have copair_fst :
        (e ≫ cfpFst p.T p.T) ≫
          coprodPERCopairMap f.map g.map =
        (e ≫ cfpFst p.T p.T) ≫
          coprodPERPayload ≫ f.map :=
      coprodPERCopairMap_ℓ _ _ _ hx_full
    have copair_snd :
        (e ≫ cfpSnd p.T p.T) ≫
          coprodPERCopairMap f.map g.map =
        (e ≫ cfpSnd p.T p.T) ≫
          coprodPERPayload ≫ f.map :=
      coprodPERCopairMap_ℓ _ _ _ hy_full
    rw [copair_fst, copair_snd]
    -- cfpLift (a ≫ payload ≫ f) (b ≫ payload ≫ f) ≫
    --   Z.rel = cfpLift (a ≫ payload) (b ≫ payload)
    --     ≫ cfpMap f f ≫ Z.rel.
    simp only [Category.assoc]
    set ea : cfpTerminal (C := C) ⟶ p.T :=
      e ≫ cfpFst p.T p.T ≫ coprodPERPayload
      with ea_def
    set eb : cfpTerminal (C := C) ⟶ p.T :=
      e ≫ cfpSnd p.T p.T ≫ coprodPERPayload
      with eb_def
    rw [show e ≫ cfpFst p.T p.T ≫
      coprodPERPayload ≫ f.map = ea ≫ f.map from by
      rw [ea_def]; simp only [Category.assoc]]
    rw [show e ≫ cfpSnd p.T p.T ≫
      coprodPERPayload ≫ f.map = eb ≫ f.map from by
      rw [eb_def]; simp only [Category.assoc]]
    rw [show cfpLift (ea ≫ f.map) (eb ≫ f.map) ≫
      Z.rel = cfpLift ea eb ≫
        cfpMap f.map f.map ≫ Z.rel from by
      rw [← Category.assoc, cfpLift_cfpMap]]
    have hℓℓ :
        e ≫ coprodPERRel X Y =
        e ≫ coprodPERXRelCheck X :=
      coprodPERRel_eval_ℓℓ X Y e
        (by rw [efst, hx])
        (by rw [esnd, hy])
    rw [hℓℓ] at hlc
    have hlc' :
        cfpLift ea eb ≫ X.rel = p.ℓ := by
      rw [ea_def, eb_def]
      unfold coprodPERXRelCheck coprodPERPayloadPair
        at hlc
      rw [show cfpLift
        (e ≫ cfpFst p.T p.T ≫ coprodPERPayload)
        (e ≫ cfpSnd p.T p.T ≫ coprodPERPayload)
        = e ≫ cfpMap coprodPERPayload
          coprodPERPayload from by
        unfold cfpMap
        rw [cfpLift_precomp]]
      rw [Category.assoc]
      exact hlc
    -- Apply f.map_rel: boolAnd(X.rel, cfpMap f f ≫
    -- Z.rel) = X.rel, so if X.rel is ℓ then cfpMap
    -- f f ≫ Z.rel is ℓ.
    have hB_bool_local :
        (cfpMap f.map f.map ≫ Z.rel) ≫
          isLeafEndo =
        cfpMap f.map f.map ≫ Z.rel := by
      rw [Category.assoc, Z.rel_bool]
    have step :=
      boolAnd_implies_IsLeafConst f.map_rel
        hB_bool_local
        (cfpLift ea eb)
        (by
          unfold IsLeafConst
          rw [hlc', cfpTerminalFrom_terminal,
            Category.id_comp])
    unfold IsLeafConst at step
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at step
    exact step
  -- Case ℓtf: mismatched tags.  hlc reduces to
  -- treeFalse = ℓ; every Boolean-valued f equals ℓ.
  · have h_mismatch :
        e ≫ coprodPERRel X Y =
        cfpTerminalFrom cfpTerminal ≫ treeFalse :=
      coprodPERRel_eval_ℓtf X Y e
        (by rw [efst, hx]) (by rw [esnd, hy])
    rw [h_mismatch, cfpTerminalFrom_terminal,
      Category.id_comp] at hlc
    -- hlc : treeFalse = ℓ, i.e. degenerate.
    apply bool_eq_ℓ_of_treeFalse_eq_ℓ hBD hlc
    rw [Category.assoc, Z.rel_bool]
  · have h_mismatch :
        e ≫ coprodPERRel X Y =
        cfpTerminalFrom cfpTerminal ≫ treeFalse :=
      coprodPERRel_eval_tfℓ X Y e
        (by rw [efst, hx]) (by rw [esnd, hy])
    rw [h_mismatch, cfpTerminalFrom_terminal,
      Category.id_comp] at hlc
    apply bool_eq_ℓ_of_treeFalse_eq_ℓ hBD hlc
    rw [Category.assoc, Z.rel_bool]
  -- Case tftf: both tags treeFalse.  Use g.map_rel
  -- symmetrically.
  · have hx_full : (e ≫ cfpFst p.T p.T) ≫
        coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ treeFalse := by
      rw [← hx, tx_def, cfpTerminalFrom_terminal,
        Category.id_comp]
      simp only [Category.assoc]
    have hy_full : (e ≫ cfpSnd p.T p.T) ≫
        coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ treeFalse := by
      rw [← hy, ty_def, cfpTerminalFrom_terminal,
        Category.id_comp]
      simp only [Category.assoc]
    have copair_fst :
        (e ≫ cfpFst p.T p.T) ≫
          coprodPERCopairMap f.map g.map =
        (e ≫ cfpFst p.T p.T) ≫
          coprodPERPayload ≫ g.map :=
      coprodPERCopairMap_tf _ _ _ hx_full
    have copair_snd :
        (e ≫ cfpSnd p.T p.T) ≫
          coprodPERCopairMap f.map g.map =
        (e ≫ cfpSnd p.T p.T) ≫
          coprodPERPayload ≫ g.map :=
      coprodPERCopairMap_tf _ _ _ hy_full
    rw [copair_fst, copair_snd]
    simp only [Category.assoc]
    set ea : cfpTerminal (C := C) ⟶ p.T :=
      e ≫ cfpFst p.T p.T ≫ coprodPERPayload
      with ea_def
    set eb : cfpTerminal (C := C) ⟶ p.T :=
      e ≫ cfpSnd p.T p.T ≫ coprodPERPayload
      with eb_def
    rw [show e ≫ cfpFst p.T p.T ≫
      coprodPERPayload ≫ g.map = ea ≫ g.map from by
      rw [ea_def]; simp only [Category.assoc]]
    rw [show e ≫ cfpSnd p.T p.T ≫
      coprodPERPayload ≫ g.map = eb ≫ g.map from by
      rw [eb_def]; simp only [Category.assoc]]
    rw [show cfpLift (ea ≫ g.map) (eb ≫ g.map) ≫
      Z.rel = cfpLift ea eb ≫
        cfpMap g.map g.map ≫ Z.rel from by
      rw [← Category.assoc, cfpLift_cfpMap]]
    have htftf :
        e ≫ coprodPERRel X Y =
        e ≫ coprodPERYRelCheck Y :=
      coprodPERRel_eval_tftf X Y e
        (by rw [efst, hx])
        (by rw [esnd, hy])
    rw [htftf] at hlc
    have hlc' :
        cfpLift ea eb ≫ Y.rel = p.ℓ := by
      rw [ea_def, eb_def]
      unfold coprodPERYRelCheck coprodPERPayloadPair
        at hlc
      rw [show cfpLift
        (e ≫ cfpFst p.T p.T ≫ coprodPERPayload)
        (e ≫ cfpSnd p.T p.T ≫ coprodPERPayload)
        = e ≫ cfpMap coprodPERPayload
          coprodPERPayload from by
        unfold cfpMap
        rw [cfpLift_precomp]]
      rw [Category.assoc]
      exact hlc
    have hB_bool_local :
        (cfpMap g.map g.map ≫ Z.rel) ≫
          isLeafEndo =
        cfpMap g.map g.map ≫ Z.rel := by
      rw [Category.assoc, Z.rel_bool]
    have step :=
      boolAnd_implies_IsLeafConst g.map_rel
        hB_bool_local
        (cfpLift ea eb)
        (by
          unfold IsLeafConst
          rw [hlc', cfpTerminalFrom_terminal,
            Category.id_comp])
    unfold IsLeafConst at step
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at step
    exact step

include hSep hBD in
/-- The copair pre-morphism from the coproduct PER
to `Z`, built from pre-morphisms `f : X → Z` and
`g : Y → Z`.  The underlying map is
`coprodPERCopairMap f.map g.map`. -/
def coprodPERCopairPreMor
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERPreMor X Z)
    (g : TreePERPreMor Y Z) :
    TreePERPreMor (coprodPERObj hSep hBD X Y) Z where
  map := coprodPERCopairMap f.map g.map
  map_rel :=
    coprodPERCopairPreMor_map_rel hSep hBD f g

include hSep hBD in
/-- Copair respects morphism equivalence.  Given
`f₁ ~ f₂ : X → Z` and `g₁ ~ g₂ : Y → Z`, the copair
pre-morphisms built from them are equivalent at the
level of the coproduct PER. -/
theorem coprodPERCopair_resp
    {X Y Z : @TreePERObj C _ h p}
    {f₁ f₂ : TreePERPreMor X Z}
    {g₁ g₂ : TreePERPreMor Y Z}
    (hf : treePERMorEqv f₁ f₂)
    (hg : treePERMorEqv g₁ g₂) :
    treePERMorEqv
      (coprodPERCopairPreMor hSep hBD f₁ g₁)
      (coprodPERCopairPreMor hSep hBD f₂ g₂) := by
  intro D e hdom
  change IsLeafConst (e ≫ cfpLift
    (coprodPERCopairMap f₁.map g₁.map)
    (coprodPERCopairMap f₂.map g₂.map) ≫ Z.rel)
  unfold IsLeafConst
  apply hSep.def
  intro d
  change d ≫ e ≫ cfpLift
    (coprodPERCopairMap f₁.map g₁.map)
    (coprodPERCopairMap f₂.map g₂.map) ≫ Z.rel =
    d ≫ cfpTerminalFrom D ≫ p.ℓ
  -- Reduce RHS.
  have d_term : d ≫ cfpTerminalFrom D =
      cfpTerminalFrom (cfpTerminal (C := C)) :=
    h.terminal.uniq _
  rw [show d ≫ cfpTerminalFrom D ≫ p.ℓ =
    p.ℓ from by
    rw [← Category.assoc, d_term,
      cfpTerminalFrom_terminal, Category.id_comp]]
  -- hdom gives IsLeafConst of e ≫ cfpLift (𝟙) (𝟙) ≫
  -- coprodPERRel X Y.  Extract d ≫ e as a global
  -- element and reason by tag cases.
  unfold IsLeafConst at hdom
  have hdom' :
      d ≫ e ≫ cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        coprodPERRel X Y = p.ℓ := by
    change _ = _
    rw [show e ≫ cfpLift (𝟙 p.T) (𝟙 p.T) ≫
      coprodPERRel X Y =
      cfpTerminalFrom D ≫ p.ℓ from hdom,
      ← Category.assoc, d_term,
      cfpTerminalFrom_terminal, Category.id_comp]
  -- e ≫ cfpLift (𝟙) (𝟙) = cfpLift e e.
  set e0 : cfpTerminal (C := C) ⟶ p.T := d ≫ e
    with e0_def
  have lift_id :
      cfpLift (d ≫ e) (d ≫ e) =
      cfpLift e0 e0 := rfl
  rw [show d ≫ e ≫ cfpLift (𝟙 p.T) (𝟙 p.T) ≫
    coprodPERRel X Y =
    cfpLift e0 e0 ≫ coprodPERRel X Y from by
    rw [← Category.assoc, ← Category.assoc,
      cfpLift_precomp]
    simp only [Category.comp_id]
    rw [lift_id]] at hdom'
  -- Goal: d ≫ e ≫ cfpLift (copair f₁ g₁)
  --   (copair f₂ g₂) ≫ Z.rel = ℓ
  rw [show d ≫ e ≫ cfpLift
    (coprodPERCopairMap f₁.map g₁.map)
    (coprodPERCopairMap f₂.map g₂.map) ≫ Z.rel =
    cfpLift
      (e0 ≫ coprodPERCopairMap f₁.map g₁.map)
      (e0 ≫ coprodPERCopairMap f₂.map g₂.map) ≫
      Z.rel from by
    rw [← Category.assoc, ← Category.assoc,
      cfpLift_precomp, e0_def]]
  -- Case-split on the tag of e0.
  set τ : cfpTerminal (C := C) ⟶ p.T :=
    e0 ≫ coprodPERTag ≫ isLeafEndo with τ_def
  have τ_bool : τ ≫ isLeafEndo = τ := by
    rw [τ_def]
    simp only [Category.assoc]
    rw [@isLeafEndo_idem C _ h p]
  -- Relate hdom' to the tag: coprodPERRel of
  -- (e0, e0) evaluates based on the tag of e0.
  have efst : cfpLift e0 e0 ≫
      coprodPERFstTagCheck = τ := by
    rw [cfpLift_coprodPERFstTagCheck, τ_def]
  have esnd : cfpLift e0 e0 ≫
      coprodPERSndTagCheck = τ := by
    rw [cfpLift_coprodPERSndTagCheck, τ_def]
  rcases hBD τ τ_bool with hτ | hτ
  -- Case τ = ℓ: e0 is left-tagged, copair reduces
  -- to f, and hf applies.
  · have efst_full :
        cfpLift e0 e0 ≫ coprodPERFstTagCheck =
        cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
      rw [efst, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    have esnd_full :
        cfpLift e0 e0 ≫ coprodPERSndTagCheck =
        cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
      rw [esnd, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    have hℓℓ :
        cfpLift e0 e0 ≫ coprodPERRel X Y =
        cfpLift e0 e0 ≫ coprodPERXRelCheck X :=
      coprodPERRel_eval_ℓℓ X Y (cfpLift e0 e0)
        efst_full esnd_full
    rw [hℓℓ, cfpLift_coprodPERXRelCheck X] at hdom'
    -- hdom' : cfpLift (e0 ≫ payload) (e0 ≫ payload)
    --   ≫ X.rel = ℓ
    -- We need: cfpLift (e0 ≫ copair f₁ g₁) (e0 ≫
    --   copair f₂ g₂) ≫ Z.rel = ℓ
    -- Using hτ_full : e0 ≫ tag ≫ isLeafEndo = ℓ,
    -- copair reduces to f_i on the payload.
    have hτ_full : e0 ≫ coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
      rw [← τ_def, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [coprodPERCopairMap_ℓ f₁.map g₁.map e0
      hτ_full]
    rw [coprodPERCopairMap_ℓ f₂.map g₂.map e0
      hτ_full]
    -- Goal: cfpLift (e0 ≫ payload ≫ f₁)
    --   (e0 ≫ payload ≫ f₂) ≫ Z.rel = ℓ
    -- Apply hf : treePERMorEqv f₁ f₂, which gives
    -- cfpLift (e' ≫ f₁) (e' ≫ f₂) ≫ Z.rel is
    -- leaf-constant when e' is in dom(X).
    have hx_dom : IsLeafConst
        ((e0 ≫ coprodPERPayload) ≫
          cfpLift (𝟙 p.T) (𝟙 p.T) ≫ X.rel) := by
      unfold IsLeafConst
      rw [cfpTerminalFrom_terminal, Category.id_comp]
      rw [show (e0 ≫ coprodPERPayload) ≫
        cfpLift (𝟙 p.T) (𝟙 p.T) ≫ X.rel =
        cfpLift (e0 ≫ coprodPERPayload)
          (e0 ≫ coprodPERPayload) ≫ X.rel from by
        rw [← Category.assoc, cfpLift_precomp]
        simp only [Category.comp_id]]
      exact hdom'
    have step := hf (e0 ≫ coprodPERPayload) hx_dom
    unfold IsLeafConst at step
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at step
    rw [show cfpLift (e0 ≫ coprodPERPayload ≫ f₁.map)
      (e0 ≫ coprodPERPayload ≫ f₂.map) ≫ Z.rel =
      cfpLift ((e0 ≫ coprodPERPayload) ≫ f₁.map)
        ((e0 ≫ coprodPERPayload) ≫ f₂.map) ≫
        Z.rel from by
      simp only [Category.assoc]]
    rw [show cfpLift
      ((e0 ≫ coprodPERPayload) ≫ f₁.map)
      ((e0 ≫ coprodPERPayload) ≫ f₂.map) =
      (e0 ≫ coprodPERPayload) ≫
        cfpLift f₁.map f₂.map from by
      rw [cfpLift_precomp]]
    rw [Category.assoc]
    exact step
  -- Case τ = treeFalse: e0 is right-tagged,
  -- copair reduces to g, and hg applies.
  · have efst_full :
        cfpLift e0 e0 ≫ coprodPERFstTagCheck =
        cfpTerminalFrom cfpTerminal ≫ treeFalse := by
      rw [efst, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    have esnd_full :
        cfpLift e0 e0 ≫ coprodPERSndTagCheck =
        cfpTerminalFrom cfpTerminal ≫ treeFalse := by
      rw [esnd, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    have htftf :
        cfpLift e0 e0 ≫ coprodPERRel X Y =
        cfpLift e0 e0 ≫ coprodPERYRelCheck Y :=
      coprodPERRel_eval_tftf X Y (cfpLift e0 e0)
        efst_full esnd_full
    rw [htftf, cfpLift_coprodPERYRelCheck Y] at hdom'
    have hτ_full : e0 ≫ coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ treeFalse := by
      rw [← τ_def, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [coprodPERCopairMap_tf f₁.map g₁.map e0
      hτ_full]
    rw [coprodPERCopairMap_tf f₂.map g₂.map e0
      hτ_full]
    have hy_dom : IsLeafConst
        ((e0 ≫ coprodPERPayload) ≫
          cfpLift (𝟙 p.T) (𝟙 p.T) ≫ Y.rel) := by
      unfold IsLeafConst
      rw [cfpTerminalFrom_terminal, Category.id_comp]
      rw [show (e0 ≫ coprodPERPayload) ≫
        cfpLift (𝟙 p.T) (𝟙 p.T) ≫ Y.rel =
        cfpLift (e0 ≫ coprodPERPayload)
          (e0 ≫ coprodPERPayload) ≫ Y.rel from by
        rw [← Category.assoc, cfpLift_precomp]
        simp only [Category.comp_id]]
      exact hdom'
    have step := hg (e0 ≫ coprodPERPayload) hy_dom
    unfold IsLeafConst at step
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at step
    rw [show cfpLift (e0 ≫ coprodPERPayload ≫ g₁.map)
      (e0 ≫ coprodPERPayload ≫ g₂.map) ≫ Z.rel =
      cfpLift ((e0 ≫ coprodPERPayload) ≫ g₁.map)
        ((e0 ≫ coprodPERPayload) ≫ g₂.map) ≫
        Z.rel from by
      simp only [Category.assoc]]
    rw [show cfpLift
      ((e0 ≫ coprodPERPayload) ≫ g₁.map)
      ((e0 ≫ coprodPERPayload) ≫ g₂.map) =
      (e0 ≫ coprodPERPayload) ≫
        cfpLift g₁.map g₂.map from by
      rw [cfpLift_precomp]]
    rw [Category.assoc]
    exact step

include hSep hBD in
/-- The eta reconstruction: the pre-morphism
`coprodPERCopairPreMor (inl ≫ m) (inr ≫ m)` is
equivalent to `m` for any `m :
coprodPERObj X Y → Z`.  This witnesses the
uniqueness of the copair. -/
theorem coprodPER_copair_reconstruct_eqv
    {X Y Z : @TreePERObj C _ h p}
    (m : TreePERPreMor
      (coprodPERObj hSep hBD X Y) Z) :
    treePERMorEqv
      (coprodPERCopairPreMor hSep hBD
        (treePERPreMorComp
          (coprodPERInlPreMor hSep hBD X Y) m)
        (treePERPreMorComp
          (coprodPERInrPreMor hSep hBD X Y) m))
      m := by
  intro D e hdom
  change IsLeafConst (e ≫ cfpLift
    (coprodPERCopairMap (coprodPERInlMap ≫ m.map)
      (coprodPERInrMap ≫ m.map))
    m.map ≫ Z.rel)
  unfold IsLeafConst
  apply hSep.def
  intro d
  have d_term : d ≫ cfpTerminalFrom D =
      cfpTerminalFrom (cfpTerminal (C := C)) :=
    h.terminal.uniq _
  rw [show d ≫ cfpTerminalFrom D ≫ p.ℓ =
    (p.ℓ : cfpTerminal (C := C) ⟶ p.T) from by
    rw [← Category.assoc, d_term,
      cfpTerminalFrom_terminal, Category.id_comp]]
  unfold IsLeafConst at hdom
  have hdom' :
      cfpLift (d ≫ e) (d ≫ e) ≫
        coprodPERRel X Y = p.ℓ := by
    rw [show cfpLift (d ≫ e) (d ≫ e) ≫
        coprodPERRel X Y =
        d ≫ e ≫ cfpLift (𝟙 p.T) (𝟙 p.T) ≫
          coprodPERRel X Y from by
      rw [← Category.assoc, ← Category.assoc,
        cfpLift_precomp]
      simp only [Category.comp_id]]
    rw [show e ≫ cfpLift (𝟙 p.T) (𝟙 p.T) ≫
      coprodPERRel X Y =
      cfpTerminalFrom D ≫ p.ℓ from hdom,
      ← Category.assoc, d_term,
      cfpTerminalFrom_terminal, Category.id_comp]
  set e0 : cfpTerminal (C := C) ⟶ p.T := d ≫ e
    with e0_def
  set τ : cfpTerminal (C := C) ⟶ p.T :=
    e0 ≫ coprodPERTag ≫ isLeafEndo with τ_def
  have τ_bool : τ ≫ isLeafEndo = τ := by
    rw [τ_def]
    simp only [Category.assoc]
    rw [@isLeafEndo_idem C _ h p]
  have efst : cfpLift e0 e0 ≫
      coprodPERFstTagCheck = τ := by
    rw [cfpLift_coprodPERFstTagCheck, τ_def]
  have esnd : cfpLift e0 e0 ≫
      coprodPERSndTagCheck = τ := by
    rw [cfpLift_coprodPERSndTagCheck, τ_def]
  -- Goal: d ≫ e ≫ cfpLift (copair ...) m.map ≫
  --   Z.rel = ℓ
  rw [show d ≫ e ≫ cfpLift
    (coprodPERCopairMap (coprodPERInlMap ≫ m.map)
      (coprodPERInrMap ≫ m.map))
    m.map ≫ Z.rel =
    cfpLift
      (e0 ≫ coprodPERCopairMap
        (coprodPERInlMap ≫ m.map)
        (coprodPERInrMap ≫ m.map))
      (e0 ≫ m.map) ≫ Z.rel from by
    rw [← Category.assoc, ← Category.assoc,
      cfpLift_precomp, e0_def]]
  -- In both tag cases, we apply `m.map_rel` via
  -- `boolAnd_implies_IsLeafConst`.  Set up the
  -- Boolean-valuedness of `cfpMap m.map m.map ≫
  -- Z.rel` once for both cases.
  have hB_bool :
      (cfpMap m.map m.map ≫ Z.rel) ≫ isLeafEndo =
      cfpMap m.map m.map ≫ Z.rel := by
    rw [Category.assoc, Z.rel_bool]
  rcases hBD τ τ_bool with hτ | hτ
  -- Case τ = ℓ: tag(e0) = ℓ.  The copair applied to
  -- e0 reduces to (inl ≫ m)(payload(e0)).  Since
  -- inl(payload(e0)) ≈ e0 in the coproduct PER
  -- (both have tag ℓ and the same payload), m
  -- sends them to Z-equivalent values.
  · have hτ_full : e0 ≫ coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
      rw [← τ_def, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [coprodPERCopairMap_ℓ _ _ e0 hτ_full]
    set p0 : cfpTerminal (C := C) ⟶ p.T :=
      e0 ≫ coprodPERPayload with p0_def
    -- Goal: cfpLift (p0 ≫ inl ≫ m) (e0 ≫ m) ≫
    --   Z.rel = ℓ
    rw [show e0 ≫ coprodPERPayload ≫
      coprodPERInlMap ≫ m.map =
      (p0 ≫ coprodPERInlMap) ≫ m.map from by
      rw [p0_def]; simp only [Category.assoc]]
    -- We need: Z.rel(m(inl(p0)), m(e0)) = ℓ.
    -- Use m.map_rel with the element cfpLift
    -- (inl(p0)) (e0).  For that element we need
    -- coprodPERRel(inl(p0), e0) = ℓ.
    have hxx_ℓ :
        cfpLift (p0 ≫ coprodPERInlMap) e0 ≫
          coprodPERRel X Y = p.ℓ := by
      -- tag(inl(p0)) = ℓ, tag(e0) = ℓ.
      have fst_tag :
          cfpLift (p0 ≫ coprodPERInlMap) e0 ≫
            coprodPERFstTagCheck =
          cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
        rw [cfpLift_coprodPERFstTagCheck,
          Category.assoc, coprodPERInlMap_tagCheck,
          ← Category.assoc]
        congr 1
        exact h.terminal.uniq _
      have snd_tag :
          cfpLift (p0 ≫ coprodPERInlMap) e0 ≫
            coprodPERSndTagCheck =
          cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
        rw [cfpLift_coprodPERSndTagCheck]
        exact hτ_full
      rw [coprodPERRel_eval_ℓℓ X Y
        (cfpLift (p0 ≫ coprodPERInlMap) e0)
        fst_tag snd_tag,
        cfpLift_coprodPERXRelCheck X]
      -- cfpLift (p0 ≫ inl ≫ payload) (e0 ≫ payload)
      --   ≫ X.rel = ℓ
      -- payload(inl(p0)) = p0.
      rw [show (p0 ≫ coprodPERInlMap) ≫
        coprodPERPayload = p0 from by
        rw [Category.assoc, coprodPERInlMap_payload,
          Category.comp_id]]
      -- Goal: cfpLift p0 (e0 ≫ payload) ≫ X.rel = ℓ
      rw [← p0_def]
      -- Goal: cfpLift p0 p0 ≫ X.rel = ℓ
      -- From hdom': coprodPERRel(e0, e0) = ℓ.
      -- At tag ℓ, this reduces to X.rel(p0, p0) = ℓ.
      have ht_fst :
          cfpLift e0 e0 ≫ coprodPERFstTagCheck =
          cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
        rw [cfpLift_coprodPERFstTagCheck]
        exact hτ_full
      have ht_snd :
          cfpLift e0 e0 ≫ coprodPERSndTagCheck =
          cfpTerminalFrom cfpTerminal ≫ p.ℓ := by
        rw [cfpLift_coprodPERSndTagCheck]
        exact hτ_full
      rw [coprodPERRel_eval_ℓℓ X Y (cfpLift e0 e0)
        ht_fst ht_snd, cfpLift_coprodPERXRelCheck X]
        at hdom'
      rw [← p0_def] at hdom'
      exact hdom'
    have step :=
      boolAnd_implies_IsLeafConst m.map_rel
        hB_bool
        (cfpLift (p0 ≫ coprodPERInlMap) e0)
        (by
          unfold IsLeafConst
          change cfpLift (p0 ≫ coprodPERInlMap)
            e0 ≫ coprodPERRel X Y = _
          rw [hxx_ℓ, cfpTerminalFrom_terminal,
            Category.id_comp])
    unfold IsLeafConst at step
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at step
    rw [show cfpLift
      ((p0 ≫ coprodPERInlMap) ≫ m.map)
      (e0 ≫ m.map) =
      cfpLift (p0 ≫ coprodPERInlMap) e0 ≫
        cfpMap m.map m.map from by
      rw [cfpLift_cfpMap]]
    rw [Category.assoc]
    exact step
  -- Case τ = treeFalse: symmetric.
  · have hτ_full : e0 ≫ coprodPERTag ≫ isLeafEndo =
        cfpTerminalFrom cfpTerminal ≫ treeFalse := by
      rw [← τ_def, hτ, cfpTerminalFrom_terminal,
        Category.id_comp]
    rw [coprodPERCopairMap_tf _ _ e0 hτ_full]
    set p0 : cfpTerminal (C := C) ⟶ p.T :=
      e0 ≫ coprodPERPayload with p0_def
    rw [show e0 ≫ coprodPERPayload ≫
      coprodPERInrMap ≫ m.map =
      (p0 ≫ coprodPERInrMap) ≫ m.map from by
      rw [p0_def]; simp only [Category.assoc]]
    have hxx_ℓ :
        cfpLift (p0 ≫ coprodPERInrMap) e0 ≫
          coprodPERRel X Y = p.ℓ := by
      have fst_tag :
          cfpLift (p0 ≫ coprodPERInrMap) e0 ≫
            coprodPERFstTagCheck =
          cfpTerminalFrom cfpTerminal ≫
            treeFalse := by
        rw [cfpLift_coprodPERFstTagCheck,
          Category.assoc, coprodPERInrMap_tagCheck,
          ← Category.assoc]
        congr 1
        exact h.terminal.uniq _
      have snd_tag :
          cfpLift (p0 ≫ coprodPERInrMap) e0 ≫
            coprodPERSndTagCheck =
          cfpTerminalFrom cfpTerminal ≫
            treeFalse := by
        rw [cfpLift_coprodPERSndTagCheck]
        exact hτ_full
      rw [coprodPERRel_eval_tftf X Y
        (cfpLift (p0 ≫ coprodPERInrMap) e0)
        fst_tag snd_tag,
        cfpLift_coprodPERYRelCheck Y]
      rw [show (p0 ≫ coprodPERInrMap) ≫
        coprodPERPayload = p0 from by
        rw [Category.assoc, coprodPERInrMap_payload,
          Category.comp_id]]
      rw [← p0_def]
      have ht_fst :
          cfpLift e0 e0 ≫ coprodPERFstTagCheck =
          cfpTerminalFrom cfpTerminal ≫
            treeFalse := by
        rw [cfpLift_coprodPERFstTagCheck]
        exact hτ_full
      have ht_snd :
          cfpLift e0 e0 ≫ coprodPERSndTagCheck =
          cfpTerminalFrom cfpTerminal ≫
            treeFalse := by
        rw [cfpLift_coprodPERSndTagCheck]
        exact hτ_full
      rw [coprodPERRel_eval_tftf X Y
        (cfpLift e0 e0) ht_fst ht_snd,
        cfpLift_coprodPERYRelCheck Y] at hdom'
      rw [← p0_def] at hdom'
      exact hdom'
    have step :=
      boolAnd_implies_IsLeafConst m.map_rel
        hB_bool
        (cfpLift (p0 ≫ coprodPERInrMap) e0)
        (by
          unfold IsLeafConst
          change cfpLift (p0 ≫ coprodPERInrMap)
            e0 ≫ coprodPERRel X Y = _
          rw [hxx_ℓ, cfpTerminalFrom_terminal,
            Category.id_comp])
    unfold IsLeafConst at step
    rw [cfpTerminalFrom_terminal,
      Category.id_comp] at step
    rw [show cfpLift
      ((p0 ≫ coprodPERInrMap) ≫ m.map)
      (e0 ≫ m.map) =
      cfpLift (p0 ≫ coprodPERInrMap) e0 ≫
        cfpMap m.map m.map from by
      rw [cfpLift_cfpMap]]
    rw [Category.assoc]
    exact step

/-- The copair morphism in the PER category, lifted
to the quotient by showing that the underlying
`coprodPERCopairPreMor` respects equivalence on
both arguments. -/
def coprodPERCopair
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERMor X Z)
    (g : TreePERMor Y Z) :
    TreePERMor (coprodPERObj hSep hBD X Y) Z :=
  Quotient.lift₂
    (s₁ := treePERSetoid X Z)
    (s₂ := treePERSetoid Y Z)
    (fun f' g' =>
      Quotient.mk
        (treePERSetoid (coprodPERObj hSep hBD X Y) Z)
        (coprodPERCopairPreMor hSep hBD f' g'))
    (fun f₁ g₁ f₂ g₂ hf hg => by
      apply Quotient.sound
        (s := treePERSetoid
          (coprodPERObj hSep hBD X Y) Z)
      exact coprodPERCopair_resp hSep hBD hf hg)
    f g

/-! ## Coproduct beta laws -/

include hSep hBD in
/-- First beta law for the coproduct at the
pre-morphism level: `inl ≫ copair(f, g) = f`. -/
theorem coprodPERInlPreMor_copair_map
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERPreMor X Z)
    (g : TreePERPreMor Y Z) :
    (treePERPreMorComp
      (coprodPERInlPreMor hSep hBD X Y)
      (coprodPERCopairPreMor hSep hBD f g)).map =
    f.map := by
  change coprodPERInlMap ≫
    coprodPERCopairMap f.map g.map = f.map
  exact coprodPERInlMap_copair f.map g.map

include hSep hBD in
/-- Second beta law for the coproduct at the
pre-morphism level: `inr ≫ copair(f, g) = g`. -/
theorem coprodPERInrPreMor_copair_map
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERPreMor X Z)
    (g : TreePERPreMor Y Z) :
    (treePERPreMorComp
      (coprodPERInrPreMor hSep hBD X Y)
      (coprodPERCopairPreMor hSep hBD f g)).map =
    g.map := by
  change coprodPERInrMap ≫
    coprodPERCopairMap f.map g.map = g.map
  exact coprodPERInrMap_copair f.map g.map

/-- Pre-morphism extensionality: two pre-morphisms
with the same underlying map are equal. -/
theorem treePERPreMor_ext_cp
    {X Y : @TreePERObj C _ h p}
    {f g : TreePERPreMor X Y}
    (h_map : f.map = g.map) :
    f = g := by
  cases f; cases g
  simp only [TreePERPreMor.mk.injEq]
  exact h_map

include hSep hBD in
/-- First beta law for the coproduct:
`coprodPERInl ≫ coprodPERCopair f g = f`. -/
theorem coprodPERInl_comp_copair
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERMor X Z)
    (g : TreePERMor Y Z) :
    treePERMorComp
      (coprodPERInl hSep hBD X Y)
      (coprodPERCopair hSep hBD f g) = f := by
  revert f g
  apply Quotient.ind
  intro f'
  apply Quotient.ind
  intro g'
  apply congr_arg
    (Quotient.mk (treePERSetoid X Z))
  exact treePERPreMor_ext_cp
    (coprodPERInlPreMor_copair_map hSep hBD f' g')

include hSep hBD in
/-- Second beta law for the coproduct:
`coprodPERInr ≫ coprodPERCopair f g = g`. -/
theorem coprodPERInr_comp_copair
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERMor X Z)
    (g : TreePERMor Y Z) :
    treePERMorComp
      (coprodPERInr hSep hBD X Y)
      (coprodPERCopair hSep hBD f g) = g := by
  revert f g
  apply Quotient.ind
  intro f'
  apply Quotient.ind
  intro g'
  apply congr_arg
    (Quotient.mk (treePERSetoid Y Z))
  exact treePERPreMor_ext_cp
    (coprodPERInrPreMor_copair_map hSep hBD f' g')

/-! ## Coproduct eta / uniqueness law -/

include hSep hBD in
/-- Uniqueness of the copair: any morphism `m`
with `inl ≫ m = f` and `inr ≫ m = g` equals
`coprodPERCopair f g`.  This is the coproduct
universal property in the PER category. -/
theorem coprodPER_copair_unique
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERMor X Z)
    (g : TreePERMor Y Z)
    (m : TreePERMor (coprodPERObj hSep hBD X Y) Z)
    (hf : treePERMorComp
      (coprodPERInl hSep hBD X Y) m = f)
    (hg : treePERMorComp
      (coprodPERInr hSep hBD X Y) m = g) :
    m = coprodPERCopair hSep hBD f g := by
  subst hf; subst hg
  revert m
  apply Quotient.ind
  intro m'
  apply Quotient.sound
    (s := treePERSetoid
      (coprodPERObj hSep hBD X Y) Z)
  exact treePERMorEqv_symm
    (coprodPER_copair_reconstruct_eqv
      hSep hBD m')

/-! ## HasBinaryCoproducts instance -/

/-- The binary cofan for the coproduct PER. -/
def coprodPERCofan
    (X Y : @TreePERObj C _ h p) :
    Limits.BinaryCofan X Y :=
  Limits.BinaryCofan.mk
    (coprodPERInl hSep hBD X Y)
    (coprodPERInr hSep hBD X Y)

/-- The binary cofan for the coproduct PER is a
colimit cocone. -/
def coprodPERCofan_isColimit
    (X Y : @TreePERObj C _ h p) :
    Limits.IsColimit (coprodPERCofan hSep hBD X Y) :=
  Limits.BinaryCofan.isColimitMk
    (fun s => coprodPERCopair hSep hBD s.inl s.inr)
    (fun s =>
      coprodPERInl_comp_copair hSep hBD s.inl s.inr)
    (fun s =>
      coprodPERInr_comp_copair hSep hBD s.inl s.inr)
    (fun s m hinl hinr =>
      coprodPER_copair_unique hSep hBD
        s.inl s.inr m hinl hinr)

/-- Each pair of PER objects has a coproduct. -/
@[reducible]
def treePER_hasColimitPair
    (X Y : @TreePERObj C _ h p) :
    Limits.HasColimit (Limits.pair X Y) :=
  Limits.HasColimit.mk
    ⟨coprodPERCofan hSep hBD X Y,
      coprodPERCofan_isColimit hSep hBD X Y⟩

/-- The PER category has binary coproducts (given
separator and Boolean dichotomy hypotheses). -/
@[reducible]
def treePER_hasBinaryCoproducts :
    Limits.HasBinaryCoproducts
      (@TreePERObj C _ h p) :=
  { has_colimit := fun F => by
      have := treePER_hasColimitPair hSep hBD
        (F.obj ⟨Limits.WalkingPair.left⟩)
        (F.obj ⟨Limits.WalkingPair.right⟩)
      exact Limits.hasColimit_of_iso
        (Limits.diagramIsoPair F) }

end CoprodProperties

/-- The PER category has all finite coproducts
(given separator and Boolean dichotomy hypotheses).
The construction combines the initial PER and the
binary coproducts via the standard mathlib lemma
`hasFiniteCoproducts_of_has_binary_and_initial`. -/
theorem treePER_hasFiniteCoproducts
    (hSep :
      IsSeparator (cfpTerminal (C := C)))
    (hBD : HasBoolDichotomy C) :
    Limits.HasFiniteCoproducts
      (@TreePERObj C _ h p) :=
  haveI : Limits.HasBinaryCoproducts
      (@TreePERObj C _ h p) :=
    treePER_hasBinaryCoproducts hSep hBD
  hasFiniteCoproducts_of_has_binary_and_initial

end GebLean
