import GebLean.TreeLogic

/-!
# Predicate Objects and Category on Binary Trees

Defines predicate-valued objects on the binary tree
type T within a Lawvere BT theory, preservation-respecting
morphisms, and the category instance.

A predicate on T is a morphism `pred : T → T` that is
Boolean-valued (`pred ≫ isLeafEndo = pred`), interpreted
as the characteristic map of a subset of T (leaf means
"in the subset").

Morphisms between predicate objects are raw endomorphisms
`map : T → T` satisfying a forward preservation condition
expressed as a `boolAnd` equation: the restriction of the
source predicate by the pulled-back target predicate
recovers the source predicate.  No quotient on morphisms
is taken, since the ambient equality is decidable.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-! ## Predicate objects -/

/--
A predicate object on the binary tree type T.

Consists of a Boolean-valued endomorphism `pred : T → T`
whose image lies in `{ℓ, treeFalse}`, interpreted as the
characteristic map of a subset of T: `pred(t) = ℓ` means
`t` is in the subset, and `pred(t) = treeFalse` means
`t` is not.
-/
@[ext]
structure TreePredObj where
  /-- The predicate endomorphism `T → T`. -/
  pred : p.T ⟶ p.T
  /-- Boolean-valued output. -/
  pred_bool : pred ≫ isLeafEndo = pred

/-! ## Morphisms -/

/--
A morphism between predicate objects: a raw endomorphism
`map : T → T` satisfying the equational forward
preservation condition
`boolAnd(X.pred, map ≫ Y.pred) = X.pred`
on `T`.

Informally, wherever `X.pred` holds, `Y.pred` also
holds after applying `map`: the set of inputs where
`X.pred` is leaf is contained in the preimage under
`map` of the set where `Y.pred` is leaf.
-/
@[ext]
structure TreePredMor (X Y : @TreePredObj C _ h p) where
  /-- The underlying endomorphism `T → T`. -/
  map : p.T ⟶ p.T
  /-- Equational forward predicate preservation:
  `boolAnd(X.pred, map ≫ Y.pred) = X.pred`. -/
  map_pred :
    cfpLift X.pred (map ≫ Y.pred) ≫ boolAnd =
    X.pred

/-- The identity predicate morphism. -/
def treePredMorId
    (X : @TreePredObj C _ h p) :
    TreePredMor X X where
  map := 𝟙 p.T
  map_pred := by
    rw [Category.id_comp]
    have : cfpLift X.pred X.pred =
        X.pred ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [this, Category.assoc, boolAnd_idem,
      X.pred_bool]

/-- Composition of predicate morphisms. -/
def treePredMorComp
    {X Y Z : @TreePredObj C _ h p}
    (f : TreePredMor X Y)
    (g : TreePredMor Y Z) :
    TreePredMor X Z where
  map := f.map ≫ g.map
  map_pred := by
    have step2 :
        cfpLift (f.map ≫ Y.pred)
          ((f.map ≫ g.map) ≫ Z.pred) ≫
          boolAnd =
        f.map ≫ Y.pred := by
      rw [Category.assoc f.map g.map Z.pred,
        ← cfpLift_precomp f.map Y.pred
          (g.map ≫ Z.pred),
        Category.assoc, g.map_pred]
    exact boolAnd_implies_trans f.map_pred step2

/-! ## Category laws -/

@[simp]
theorem treePredMorId_comp
    {X Y : @TreePredObj C _ h p}
    (f : TreePredMor X Y) :
    treePredMorComp (treePredMorId X) f = f := by
  cases f
  simp only [treePredMorComp, treePredMorId,
    Category.id_comp]

@[simp]
theorem treePredMorComp_id
    {X Y : @TreePredObj C _ h p}
    (f : TreePredMor X Y) :
    treePredMorComp f (treePredMorId Y) = f := by
  cases f
  simp only [treePredMorComp, treePredMorId,
    Category.comp_id]

@[simp]
theorem treePredMorComp_assoc
    {X Y Z W : @TreePredObj C _ h p}
    (f : TreePredMor X Y)
    (g : TreePredMor Y Z)
    (k : TreePredMor Z W) :
    treePredMorComp (treePredMorComp f g) k =
    treePredMorComp f (treePredMorComp g k) := by
  cases f; cases g; cases k
  simp only [treePredMorComp, Category.assoc]

/-! ## Category instance -/

/-- The predicate category: objects are predicate
objects on T, morphisms are preservation-respecting
endomorphisms on T. -/
instance treePredCategory :
    Category (@TreePredObj C _ h p) where
  Hom := TreePredMor
  id := treePredMorId
  comp := treePredMorComp
  id_comp := treePredMorId_comp
  comp_id := treePredMorComp_id
  assoc := treePredMorComp_assoc

/-! ## Binary coproducts (partial construction)

The coproduct of `X Y : TreePredObj` uses tagged
trees: a left-tagged tree is `branch(ℓ, x)` with
payload `x`, and a right-tagged tree is
`branch(treeFalse, y)` with payload `y`.  The tag
is extracted by `treeLeftEndo` and the payload by
`treeRightEndo`.  The coproduct predicate case-splits
on whether the tag is leaf (payload in `X.pred`) or
not (payload in `Y.pred`).

The development below provides:

* the coproduct predicate object `coprodPredObj`
  together with the Boolean-valuedness of its
  underlying endomorphism;
* the underlying endomorphisms of the injections
  `coprodInlMap`, `coprodInrMap` together with the
  exact equations expressing that they compose with
  the coproduct predicate to recover the component
  predicates;
* the injection morphisms `coprodInl`, `coprodInr`
  with their preservation equations;
* the case map's underlying endomorphism
  `coprodCaseMap` and the beta laws
  `coprodInlMap_coprodCaseMap`,
  `coprodInrMap_coprodCaseMap` as exact equations at
  the level of raw endomorphisms.

The case map's preservation condition at the level
of the `TreePredMor` structure and the universal
(eta) law are not provided here.  Both require
extra coupling between the outer coproduct predicate
condition and the inner case map condition that the
purely algebraic treatment via `boolAnd_treeIte_form`
and `treeIte_compose` does not supply: after that
rewriting, the sub-goals ask for
`boolAnd(treeRightEndo ≫ X.pred, caseMap ≫ Z.pred)
= treeRightEndo ≫ X.pred`, which decouples the tag
check from the case map's tag check and is
genuinely not derivable from `f.map_pred` and
`g.map_pred` alone.  Without a morphism quotient
(or a structural induction principle on `T`), the
eta law also fails for the same reason: two
morphisms agreeing on the tagged subset can differ
as raw endomorphisms on arbitrary non-tagged
trees. -/

/-- The underlying endomorphism of the coproduct
predicate.  It returns `X.pred(payload)` on
left-tagged trees and `Y.pred(payload)` on
non-left-tagged trees. -/
def coprodPredEndo (X Y : @TreePredObj C _ h p) :
    p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (treeRightEndo ≫ X.pred)
      (treeRightEndo ≫ Y.pred))
    (treeLeftEndo ≫ isLeafEndo) ≫ treeIte

/-- The coproduct predicate is Boolean-valued. -/
theorem coprodPredEndo_bool
    (X Y : @TreePredObj C _ h p) :
    coprodPredEndo X Y ≫ isLeafEndo =
    coprodPredEndo X Y := by
  unfold coprodPredEndo
  rw [Category.assoc]
  exact treeIte_isLeafEndo_stable _ _ _
    (by rw [Category.assoc, X.pred_bool])
    (by rw [Category.assoc, Y.pred_bool])

/-- The coproduct predicate object. -/
def coprodPredObj (X Y : @TreePredObj C _ h p) :
    @TreePredObj C _ h p where
  pred := coprodPredEndo X Y
  pred_bool := coprodPredEndo_bool X Y

/-- The underlying endomorphism of the left
injection: `x ↦ branch(ℓ, x)`. -/
def coprodInlMap : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T ≫ p.ℓ) (𝟙 p.T) ≫ p.β

/-- The underlying endomorphism of the right
injection: `y ↦ branch(treeFalse, y)`. -/
def coprodInrMap : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T ≫ treeFalse) (𝟙 p.T)
    ≫ p.β

/-- Composition of the left injection with the
coproduct predicate equals `X.pred`: for any tree
`x`, `coprodPredEndo(branch(ℓ, x)) = X.pred(x)`. -/
theorem coprodInlMap_pred
    (X Y : @TreePredObj C _ h p) :
    coprodInlMap ≫ coprodPredEndo X Y = X.pred := by
  set s :=
    cfpLift (cfpTerminalFrom p.T ≫ p.ℓ) (𝟙 p.T)
    with hs
  unfold coprodInlMap coprodPredEndo
  rw [← hs]
  rw [Category.assoc, ← Category.assoc p.β]
  rw [cfpLift_precomp p.β _ _]
  rw [cfpLift_precomp p.β _ _]
  rw [← Category.assoc p.β treeRightEndo X.pred,
    β_treeRightEndo,
    ← Category.assoc p.β treeRightEndo Y.pred,
    β_treeRightEndo,
    ← Category.assoc p.β treeLeftEndo isLeafEndo,
    β_treeLeftEndo]
  rw [← Category.assoc s _ treeIte]
  rw [cfpLift_precomp s _ _]
  rw [cfpLift_precomp s _ _]
  rw [← Category.assoc s (cfpSnd p.T p.T) X.pred]
  rw [← Category.assoc s (cfpSnd p.T p.T) Y.pred]
  rw [← Category.assoc s (cfpFst p.T p.T) isLeafEndo]
  rw [hs]
  simp only [cfpLift_snd, cfpLift_fst,
    Category.id_comp]
  rw [Category.assoc (cfpTerminalFrom p.T) p.ℓ
    isLeafEndo, isLeafEndo_ℓ]
  have rewrite_form :
      cfpLift (cfpLift X.pred Y.pred)
        (cfpTerminalFrom p.T ≫ p.ℓ) =
      cfpInsertSnd p.ℓ p.T ≫
        cfpMap (cfpLift X.pred Y.pred) (𝟙 p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [rewrite_form, Category.assoc,
    cfpInsertSnd_cfpMap_treeIte]

/-- Composition of the right injection with the
coproduct predicate equals `Y.pred`: for any tree
`y`, `coprodPredEndo(branch(treeFalse, y)) =
Y.pred(y)`. -/
theorem coprodInrMap_pred
    (X Y : @TreePredObj C _ h p) :
    coprodInrMap ≫ coprodPredEndo X Y = Y.pred := by
  set s :=
    cfpLift (cfpTerminalFrom p.T ≫ treeFalse)
      (𝟙 p.T)
    with hs
  unfold coprodInrMap coprodPredEndo
  rw [← hs]
  rw [Category.assoc, ← Category.assoc p.β]
  rw [cfpLift_precomp p.β _ _]
  rw [cfpLift_precomp p.β _ _]
  rw [← Category.assoc p.β treeRightEndo X.pred,
    β_treeRightEndo,
    ← Category.assoc p.β treeRightEndo Y.pred,
    β_treeRightEndo,
    ← Category.assoc p.β treeLeftEndo isLeafEndo,
    β_treeLeftEndo]
  rw [← Category.assoc s _ treeIte]
  rw [cfpLift_precomp s _ _]
  rw [cfpLift_precomp s _ _]
  rw [← Category.assoc s (cfpSnd p.T p.T) X.pred]
  rw [← Category.assoc s (cfpSnd p.T p.T) Y.pred]
  rw [← Category.assoc s (cfpFst p.T p.T) isLeafEndo]
  rw [hs]
  simp only [cfpLift_snd, cfpLift_fst,
    Category.id_comp]
  rw [Category.assoc (cfpTerminalFrom p.T) treeFalse
    isLeafEndo, isLeafEndo_treeFalse]
  exact treeIte_treeFalse_applied X.pred Y.pred

/-- The left injection morphism. -/
def coprodInl (X Y : @TreePredObj C _ h p) :
    TreePredMor X (coprodPredObj X Y) where
  map := coprodInlMap
  map_pred := by
    change cfpLift X.pred
      (coprodInlMap ≫ coprodPredEndo X Y) ≫
      boolAnd = X.pred
    rw [coprodInlMap_pred]
    have factor : cfpLift X.pred X.pred =
        X.pred ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [factor, Category.assoc, boolAnd_idem,
      X.pred_bool]

/-- The right injection morphism. -/
def coprodInr (X Y : @TreePredObj C _ h p) :
    TreePredMor Y (coprodPredObj X Y) where
  map := coprodInrMap
  map_pred := by
    change cfpLift Y.pred
      (coprodInrMap ≫ coprodPredEndo X Y) ≫
      boolAnd = Y.pred
    rw [coprodInrMap_pred]
    have factor : cfpLift Y.pred Y.pred =
        Y.pred ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [factor, Category.assoc, boolAnd_idem,
      Y.pred_bool]

/-- The underlying endomorphism of the case
(copairing) map for a pair of morphisms
`f : X ⟶ Z` and `g : Y ⟶ Z`.  Dispatches on the
left destructor: on a left-tagged tree
`branch(ℓ, x)`, returns `f.map(x)`; otherwise
returns `g.map` applied to the right destructor. -/
def coprodCaseMap
    {X Y Z : @TreePredObj C _ h p}
    (f : TreePredMor X Z)
    (g : TreePredMor Y Z) : p.T ⟶ p.T :=
  cfpLift
    (cfpLift
      (treeRightEndo ≫ f.map)
      (treeRightEndo ≫ g.map))
    (treeLeftEndo ≫ isLeafEndo) ≫ treeIte

/-! ### Beta laws for the case map

The left (resp. right) injection followed by the
case map agrees with the left (resp. right) input
morphism at the level of the underlying
endomorphism on `T`.  These are exact equations
between raw `T ⟶ T` maps; no quotient is involved.
-/

/-- Left beta law for the case map on raw
endomorphisms: `coprodInlMap ≫ coprodCaseMap f g =
f.map`. -/
theorem coprodInlMap_coprodCaseMap
    {X Y Z : @TreePredObj C _ h p}
    (f : TreePredMor X Z)
    (g : TreePredMor Y Z) :
    coprodInlMap ≫ coprodCaseMap f g = f.map := by
  set s :=
    cfpLift (cfpTerminalFrom p.T ≫ p.ℓ) (𝟙 p.T)
    with hs
  unfold coprodInlMap coprodCaseMap
  rw [← hs]
  rw [Category.assoc, ← Category.assoc p.β]
  rw [cfpLift_precomp p.β _ _]
  rw [cfpLift_precomp p.β _ _]
  rw [← Category.assoc p.β treeRightEndo f.map,
    β_treeRightEndo,
    ← Category.assoc p.β treeRightEndo g.map,
    β_treeRightEndo,
    ← Category.assoc p.β treeLeftEndo isLeafEndo,
    β_treeLeftEndo]
  rw [← Category.assoc s _ treeIte]
  rw [cfpLift_precomp s _ _]
  rw [cfpLift_precomp s _ _]
  rw [← Category.assoc s (cfpSnd p.T p.T) f.map]
  rw [← Category.assoc s (cfpSnd p.T p.T) g.map]
  rw [← Category.assoc s (cfpFst p.T p.T) isLeafEndo]
  rw [hs]
  simp only [cfpLift_snd, cfpLift_fst,
    Category.id_comp]
  rw [Category.assoc (cfpTerminalFrom p.T) p.ℓ
    isLeafEndo, isLeafEndo_ℓ]
  have rewrite_form :
      cfpLift (cfpLift f.map g.map)
        (cfpTerminalFrom p.T ≫ p.ℓ) =
      cfpInsertSnd p.ℓ p.T ≫
        cfpMap (cfpLift f.map g.map) (𝟙 p.T) := by
    unfold cfpInsertSnd
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [rewrite_form, Category.assoc,
    cfpInsertSnd_cfpMap_treeIte]

/-- Right beta law for the case map on raw
endomorphisms: `coprodInrMap ≫ coprodCaseMap f g =
g.map`. -/
theorem coprodInrMap_coprodCaseMap
    {X Y Z : @TreePredObj C _ h p}
    (f : TreePredMor X Z)
    (g : TreePredMor Y Z) :
    coprodInrMap ≫ coprodCaseMap f g = g.map := by
  set s :=
    cfpLift (cfpTerminalFrom p.T ≫ treeFalse)
      (𝟙 p.T)
    with hs
  unfold coprodInrMap coprodCaseMap
  rw [← hs]
  rw [Category.assoc, ← Category.assoc p.β]
  rw [cfpLift_precomp p.β _ _]
  rw [cfpLift_precomp p.β _ _]
  rw [← Category.assoc p.β treeRightEndo f.map,
    β_treeRightEndo,
    ← Category.assoc p.β treeRightEndo g.map,
    β_treeRightEndo,
    ← Category.assoc p.β treeLeftEndo isLeafEndo,
    β_treeLeftEndo]
  rw [← Category.assoc s _ treeIte]
  rw [cfpLift_precomp s _ _]
  rw [cfpLift_precomp s _ _]
  rw [← Category.assoc s (cfpSnd p.T p.T) f.map]
  rw [← Category.assoc s (cfpSnd p.T p.T) g.map]
  rw [← Category.assoc s (cfpFst p.T p.T) isLeafEndo]
  rw [hs]
  simp only [cfpLift_snd, cfpLift_fst,
    Category.id_comp]
  rw [Category.assoc (cfpTerminalFrom p.T) treeFalse
    isLeafEndo, isLeafEndo_treeFalse]
  exact treeIte_treeFalse_applied f.map g.map

end GebLean
