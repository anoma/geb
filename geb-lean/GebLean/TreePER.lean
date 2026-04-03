import GebLean.TreeLogic
import Mathlib.CategoryTheory.Generator.Basic

/-!
# PER Objects and Category on Binary Trees

Defines partial equivalence relations (PERs) on
the binary tree type T within a Lawvere BT theory,
relation-preserving morphisms, morphism equivalence,
and the category instance.

A PER on T is a morphism `rel : T × T → T` satisfying
symmetry and transitivity, where leaf encodes true and
non-leaf encodes false.  The relation is required to
output Boolean values (`rel ≫ isLeafEndo = rel`).

Morphisms between PERs are equivalence classes of
relation-preserving maps, where two maps are equivalent
when they agree on the domain of the source PER modulo
the target PER.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-! ## Product utilities -/

/-- Swap the two components of a binary product. -/
def cfpSwap (A B : C) :
    cfpProd A B ⟶ cfpProd B A :=
  cfpLift (cfpSnd A B) (cfpFst A B)

/-! ## Triple-product projections -/

/-- We represent `T³` as `T × (T × T)`.
Projection to the first component (x). -/
def t3x :
    cfpProd p.T (cfpProd p.T p.T) ⟶ p.T :=
  cfpFst p.T (cfpProd p.T p.T)

/-- Projection to the second component (y). -/
def t3y :
    cfpProd p.T (cfpProd p.T p.T) ⟶ p.T :=
  cfpSnd p.T (cfpProd p.T p.T) ≫
    cfpFst p.T p.T

/-- Projection to the third component (z). -/
def t3z :
    cfpProd p.T (cfpProd p.T p.T) ⟶ p.T :=
  cfpSnd p.T (cfpProd p.T p.T) ≫
    cfpSnd p.T p.T

/-! ## Transitivity predicates -/

/-- Equational transitivity of a relation
`rel : T × T → T` using `boolAnd`: the equation
`boolAnd(boolAnd(rel(x,z), rel(z,y)), rel(x,y))
  = boolAnd(rel(x,z), rel(z,y))`
holds on `T × (T × T)`.  This encodes
"rel(x,z) ∧ rel(z,y) implies rel(x,y)" as a
single morphism equation. -/
def EqTransitive
    (rel : cfpProd p.T p.T ⟶ p.T) : Prop :=
  cfpLift
    (cfpLift
      (cfpLift t3x t3z ≫ rel)
      (cfpLift t3z t3y ≫ rel) ≫
      boolAnd)
    (cfpLift t3x t3y ≫ rel) ≫
    boolAnd =
  cfpLift
    (cfpLift t3x t3z ≫ rel)
    (cfpLift t3z t3y ≫ rel) ≫
    boolAnd

/-- Quantified transitivity of a relation
`rel : T × T → T`: for any generalized element
`e : D ⟶ T × (T × T)`, if `e ≫ rel(x,z)` and
`e ≫ rel(z,y)` are leaf-constant, then
`e ≫ rel(x,y)` is also leaf-constant. -/
def QuantTransitive
    (rel : cfpProd p.T p.T ⟶ p.T) : Prop :=
  {D : C} →
  (e : D ⟶ cfpProd p.T (cfpProd p.T p.T)) →
  IsLeafConst
    (e ≫ cfpLift t3x t3z ≫ rel) →
  IsLeafConst
    (e ≫ cfpLift t3z t3y ≫ rel) →
  IsLeafConst
    (e ≫ cfpLift t3x t3y ≫ rel)

/-- `EqTransitive` implies `QuantTransitive`:
the equational form of transitivity implies the
quantified form.  The proof uses
`boolAnd_implies_IsLeafConst`, which bridges from
the `boolAnd`-implication equation to the
`IsLeafConst` chain. -/
theorem eqTransitive_implies_quant
    {rel : cfpProd p.T p.T ⟶ p.T}
    (rel_bool : rel ≫ isLeafEndo = rel)
    (ht : EqTransitive rel) :
    QuantTransitive rel := by
  intro D e h1 h2
  unfold EqTransitive at ht
  -- The hypothesis ht says
  -- boolAnd(boolAnd(rel(x,z), rel(z,y)),
  --   rel(x,y)) =
  -- boolAnd(rel(x,z), rel(z,y)).
  -- Set A := boolAnd(rel(x,z), rel(z,y)),
  --      B := rel(x,y).
  -- Then boolAnd(A, B) = A.
  -- By boolAnd_implies_IsLeafConst (with
  -- B ≫ isLeafEndo = B from rel_bool):
  -- for any e, IsLeafConst(e ≫ A) implies
  -- IsLeafConst(e ≫ B).
  -- We have IsLeafConst(e ≫ rel(x,z)) and
  -- IsLeafConst(e ≫ rel(z,y)), so
  -- IsLeafConst(e ≫ boolAnd(rel(x,z), rel(z,y)))
  -- follows from boolAnd_ℓ_ℓ.
  -- Then IsLeafConst(e ≫ B) =
  -- IsLeafConst(e ≫ rel(x,y)).
  set A := cfpLift
    (cfpLift t3x t3z ≫ rel)
    (cfpLift t3z t3y ≫ rel) ≫ boolAnd
  set B := cfpLift t3x t3y ≫ rel
  -- B is Boolean-valued.
  have hB : B ≫ isLeafEndo = B := by
    change (cfpLift t3x t3y ≫ rel) ≫
      isLeafEndo = cfpLift t3x t3y ≫ rel
    rw [Category.assoc, rel_bool]
  -- IsLeafConst(e ≫ A) from h1 and h2.
  have h1' : IsLeafConst
      (e ≫ (cfpLift t3x t3z ≫ rel)) := by
    unfold IsLeafConst at h1 ⊢
    exact h1
  have h2' : IsLeafConst
      (e ≫ (cfpLift t3z t3y ≫ rel)) := by
    unfold IsLeafConst at h2 ⊢
    exact h2
  have hA : IsLeafConst (e ≫ A) := by
    change IsLeafConst (e ≫
      (cfpLift
        (cfpLift t3x t3z ≫ rel)
        (cfpLift t3z t3y ≫ rel) ≫ boolAnd))
    unfold IsLeafConst
    rw [← Category.assoc, cfpLift_precomp,
      h1', h2',
      ← cfpLift_precomp (cfpTerminalFrom D)
        p.ℓ p.ℓ,
      Category.assoc, boolAnd_ℓ_ℓ]
  exact boolAnd_implies_IsLeafConst ht hB e hA

/-! ## PER objects -/

/--
A partial equivalence relation (PER) on the binary
tree type T.

A PER consists of a morphism `rel : T × T → T`
(encoding a T-valued relation where leaf = true)
satisfying:
- Boolean-valued output: `rel ≫ isLeafEndo = rel`
- Symmetry: `rel(x, y) = rel(y, x)`
- Transitivity (equational): the `boolAnd`-based
  implication equation on `T × (T × T)`
-/
structure TreePERObj where
  /-- The relation morphism `T × T → T`. -/
  rel : cfpProd p.T p.T ⟶ p.T
  /-- Boolean-valued output. -/
  rel_bool : rel ≫ isLeafEndo = rel
  /-- Symmetry: swapping inputs preserves the
  relation. -/
  rel_symm :
    cfpSwap p.T p.T ≫ rel = rel
  /-- Equational transitivity. -/
  rel_trans : EqTransitive rel

/-- Derive `QuantTransitive` from `TreePERObj`. -/
theorem TreePERObj.rel_trans_prop
    (X : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T (cfpProd p.T p.T))
    (h1 : IsLeafConst
      (e ≫ cfpLift t3x t3z ≫ X.rel))
    (h2 : IsLeafConst
      (e ≫ cfpLift t3z t3y ≫ X.rel)) :
    IsLeafConst
      (e ≫ cfpLift t3x t3y ≫ X.rel) :=
  eqTransitive_implies_quant
    X.rel_bool X.rel_trans e h1 h2

/-! ## Pre-morphisms -/

/--
A pre-morphism between PER objects: a morphism
`map : T → T` satisfying the equational
relation-preservation condition
`boolAnd(X.rel, Y.rel(map × map)) = X.rel`
on `T × T`.
-/
structure TreePERPreMor
    (X Y : @TreePERObj C _ h p) where
  /-- The underlying morphism `T → T`. -/
  map : p.T ⟶ p.T
  /-- Equational forward relation preservation:
  `boolAnd(X.rel, (map × map) ≫ Y.rel)
    = X.rel`. -/
  map_rel :
    cfpLift X.rel
      (cfpMap map map ≫ Y.rel) ≫ boolAnd =
    X.rel

/-- The identity pre-morphism. -/
def treePERPreMorId
    (X : @TreePERObj C _ h p) :
    TreePERPreMor X X where
  map := 𝟙 p.T
  map_rel := by
    rw [cfpMap_id, Category.id_comp]
    -- Goal: cfpLift X.rel X.rel ≫ boolAnd = X.rel
    have : cfpLift X.rel X.rel =
        X.rel ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
      rw [cfpLift_precomp]
      simp only [Category.comp_id]
    rw [this, Category.assoc, boolAnd_idem,
      X.rel_bool]

/-- Composition of pre-morphisms. -/
def treePERPreMorComp
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERPreMor X Y)
    (g : TreePERPreMor Y Z) :
    TreePERPreMor X Z where
  map := f.map ≫ g.map
  map_rel := by
    -- Goal: boolAnd(X.rel, ((f≫g)×(f≫g)) ≫ Z.rel)
    --   = X.rel.
    -- Set B := (f×f) ≫ Y.rel,
    --      A := ((f≫g)×(f≫g)) ≫ Z.rel.
    -- From f.map_rel: boolAnd(X.rel, B) = X.rel.
    -- From g.map_rel precomposed with (f×f):
    --   boolAnd(B, A) = B.
    -- By boolAnd_implies_trans: done.
    rw [← cfpMap_comp f.map f.map g.map g.map]
    -- Goal: cfpLift X.rel
    --   (cfpMap f.map f.map ≫ cfpMap g.map g.map
    --     ≫ Z.rel) ≫ boolAnd = X.rel
    -- Rewrite (cfpMap f.map f.map ≫
    --   cfpMap g.map g.map ≫ Z.rel) using
    --   associativity.
    have step2 :
        cfpLift
          (cfpMap f.map f.map ≫ Y.rel)
          ((cfpMap f.map f.map ≫
            cfpMap g.map g.map) ≫ Z.rel) ≫
          boolAnd =
        cfpMap f.map f.map ≫ Y.rel := by
      rw [Category.assoc
        (cfpMap f.map f.map)
        (cfpMap g.map g.map) Z.rel]
      rw [← cfpLift_precomp
        (cfpMap f.map f.map)]
      rw [Category.assoc]
      rw [g.map_rel]
    exact boolAnd_implies_trans f.map_rel step2

/-! ## Morphism equivalence -/

/-- Two pre-morphisms `f, g : X → Y` are
equivalent when they agree on the domain of X
modulo Y: for all `e : D ⟶ T`, if `e` is in the
domain of X (i.e., `rel_X(e, e) = leaf`), then
`f(e)` and `g(e)` are Y-related
(i.e., `rel_Y(f(e), g(e)) = leaf`). -/
def treePERMorEqv
    {X Y : @TreePERObj C _ h p}
    (f g : TreePERPreMor X Y) : Prop :=
  {D : C} →
  (e : D ⟶ p.T) →
  IsLeafConst
    (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T) ≫
      X.rel) →
  IsLeafConst
    (e ≫ cfpLift f.map g.map ≫ Y.rel)

/-- Morphism equivalence is reflexive. -/
theorem treePERMorEqv_refl
    {X Y : @TreePERObj C _ h p}
    (f : TreePERPreMor X Y) :
    treePERMorEqv f f := by
  intro D e hdom
  unfold IsLeafConst at hdom ⊢
  have lift_eq :
      cfpLift f.map f.map =
      cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        cfpMap f.map f.map := by
    rw [cfpLift_cfpMap]
    simp only [Category.id_comp]
  rw [lift_eq]
  simp only [Category.assoc]
  have hdom' :
      (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T)) ≫
        X.rel = cfpTerminalFrom D ≫ p.ℓ := by
    rw [Category.assoc]; exact hdom
  have hBool :
      (cfpMap f.map f.map ≫ Y.rel) ≫
        isLeafEndo =
      cfpMap f.map f.map ≫ Y.rel := by
    rw [Category.assoc, Y.rel_bool]
  have step :=
    boolAnd_implies_IsLeafConst f.map_rel
      hBool (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T))
      hdom'
  unfold IsLeafConst at step
  rw [Category.assoc] at step
  exact step

/-- Morphism equivalence is symmetric. -/
theorem treePERMorEqv_symm
    {X Y : @TreePERObj C _ h p}
    {f g : TreePERPreMor X Y}
    (hfg : treePERMorEqv f g) :
    treePERMorEqv g f := by
  intro D e hdom
  have h1 := hfg e hdom
  unfold IsLeafConst at h1 ⊢
  have swap_eq :
      cfpLift g.map f.map =
      cfpLift f.map g.map ≫
        cfpSwap p.T p.T := by
    unfold cfpSwap
    rw [cfpLift_precomp, cfpLift_snd,
      cfpLift_fst]
  rw [swap_eq]
  simp only [Category.assoc]
  rw [Y.rel_symm]
  exact h1

/-- Morphism equivalence is transitive. -/
theorem treePERMorEqv_trans
    {X Y : @TreePERObj C _ h p}
    {f g k : TreePERPreMor X Y}
    (hfg : treePERMorEqv f g)
    (hgk : treePERMorEqv g k) :
    treePERMorEqv f k := by
  intro D e hdom
  let test : D ⟶ cfpProd p.T (cfpProd p.T p.T) :=
    e ≫ cfpLift f.map
      (cfpLift k.map g.map)
  have test_fst :
      test ≫ cfpFst p.T (cfpProd p.T p.T) =
      e ≫ f.map := by
    change (e ≫ cfpLift f.map
        (cfpLift k.map g.map)) ≫
      cfpFst p.T (cfpProd p.T p.T) =
      e ≫ f.map
    rw [Category.assoc, cfpLift_fst]
  have test_snd :
      test ≫ cfpSnd p.T (cfpProd p.T p.T) =
      e ≫ cfpLift k.map g.map := by
    change (e ≫ cfpLift f.map
        (cfpLift k.map g.map)) ≫
      cfpSnd p.T (cfpProd p.T p.T) =
      e ≫ cfpLift k.map g.map
    rw [Category.assoc, cfpLift_snd]
  have test_snd_fst :
      test ≫ cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpFst p.T p.T =
      e ≫ k.map := by
    rw [← Category.assoc, test_snd,
      Category.assoc, cfpLift_fst]
  have test_snd_snd :
      test ≫ cfpSnd p.T (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T =
      e ≫ g.map := by
    rw [← Category.assoc, test_snd,
      Category.assoc, cfpLift_snd]
  have proj_xz :
      test ≫ cfpLift t3x t3z =
      e ≫ cfpLift f.map g.map := by
    rw [cfpLift_precomp e, cfpLift_precomp test]
    unfold t3x t3z
    rw [test_fst, test_snd_snd]
  have proj_zy :
      test ≫ cfpLift t3z t3y =
      e ≫ cfpLift g.map k.map := by
    rw [cfpLift_precomp e, cfpLift_precomp test]
    unfold t3z t3y
    rw [test_snd_snd, test_snd_fst]
  have proj_xy :
      test ≫ cfpLift t3x t3y =
      e ≫ cfpLift f.map k.map := by
    rw [cfpLift_precomp e, cfpLift_precomp test]
    unfold t3x t3y
    rw [test_fst, test_snd_fst]
  have hyp1 : IsLeafConst
      (test ≫ cfpLift t3x t3z ≫ Y.rel) := by
    unfold IsLeafConst
    rw [← Category.assoc, proj_xz,
      Category.assoc]
    have := hfg e hdom
    unfold IsLeafConst at this
    exact this
  have hyp2 : IsLeafConst
      (test ≫ cfpLift t3z t3y ≫ Y.rel) := by
    unfold IsLeafConst
    rw [← Category.assoc, proj_zy,
      Category.assoc]
    have := hgk e hdom
    unfold IsLeafConst at this
    exact this
  have concl := Y.rel_trans_prop test hyp1 hyp2
  unfold IsLeafConst at concl ⊢
  rw [← Category.assoc, proj_xy,
    Category.assoc] at concl
  exact concl

/-! ## Setoid and quotient -/

/-- The setoid on pre-morphisms given by
`treePERMorEqv`. -/
def treePERSetoid
    (X Y : @TreePERObj C _ h p) :
    Setoid (TreePERPreMor X Y) where
  r := treePERMorEqv
  iseqv :=
    ⟨treePERMorEqv_refl,
     fun h => treePERMorEqv_symm h,
     fun h1 h2 => treePERMorEqv_trans h1 h2⟩

/-- Morphisms in the PER category: equivalence
classes of relation-preserving maps. -/
def TreePERMor
    (X Y : @TreePERObj C _ h p) :=
  Quotient (treePERSetoid X Y)

/-! ## Category laws on pre-morphisms -/

@[simp]
theorem treePERPreMorId_comp
    {X Y : @TreePERObj C _ h p}
    (f : TreePERPreMor X Y) :
    treePERPreMorComp (treePERPreMorId X) f =
      f := by
  cases f
  simp only [treePERPreMorComp,
    treePERPreMorId, Category.id_comp]

@[simp]
theorem treePERPreMorComp_id
    {X Y : @TreePERObj C _ h p}
    (f : TreePERPreMor X Y) :
    treePERPreMorComp f (treePERPreMorId Y) =
      f := by
  cases f
  simp only [treePERPreMorComp,
    treePERPreMorId, Category.comp_id]

@[simp]
theorem treePERPreMorComp_assoc
    {X Y Z W : @TreePERObj C _ h p}
    (f : TreePERPreMor X Y)
    (g : TreePERPreMor Y Z)
    (k : TreePERPreMor Z W) :
    treePERPreMorComp
      (treePERPreMorComp f g) k =
    treePERPreMorComp f
      (treePERPreMorComp g k) := by
  cases f; cases g; cases k
  simp only [treePERPreMorComp,
    Category.assoc]

/-! ## Composition on the quotient -/

/-- Composition respects equivalence on the
left: if `f₁ ~ f₂` then `f₁ ∘ g ~ f₂ ∘ g`. -/
theorem treePERComp_left_resp
    {X Y Z : @TreePERObj C _ h p}
    {f₁ f₂ : TreePERPreMor X Y}
    (g : TreePERPreMor Y Z)
    (hf : treePERMorEqv f₁ f₂) :
    treePERMorEqv
      (treePERPreMorComp f₁ g)
      (treePERPreMorComp f₂ g) := by
  intro D e hdom
  change IsLeafConst
    (e ≫ cfpLift (f₁.map ≫ g.map)
      (f₂.map ≫ g.map) ≫ Z.rel)
  -- Factor: cfpLift (f₁≫g) (f₂≫g) =
  --   cfpLift f₁ f₂ ≫ cfpMap g g.
  have h1 := hf e hdom
  unfold IsLeafConst at h1 ⊢
  rw [← cfpLift_cfpMap]
  simp only [Category.assoc]
  -- Need: IsLeafConst of
  --   (e ≫ cfpLift f₁ f₂ ≫ cfpMap g g ≫ Z.rel).
  -- From g.map_rel:
  --   boolAnd(Y.rel, (g×g) ≫ Z.rel) = Y.rel.
  -- By boolAnd_implies_IsLeafConst:
  --   IsLeafConst(e' ≫ Y.rel) →
  --   IsLeafConst(e' ≫ (g×g) ≫ Z.rel).
  have hBool :
      (cfpMap g.map g.map ≫ Z.rel) ≫
        isLeafEndo =
      cfpMap g.map g.map ≫ Z.rel := by
    rw [Category.assoc, Z.rel_bool]
  have h1' :
      (e ≫ cfpLift f₁.map f₂.map) ≫
        Y.rel =
      cfpTerminalFrom D ≫ p.ℓ := by
    rw [Category.assoc]; exact h1
  have step :=
    boolAnd_implies_IsLeafConst g.map_rel
      hBool (e ≫ cfpLift f₁.map f₂.map) h1'
  unfold IsLeafConst at step
  rw [Category.assoc] at step
  exact step

/-- Composition respects equivalence on the
right: if `g₁ ~ g₂` then `f ∘ g₁ ~ f ∘ g₂`. -/
theorem treePERComp_right_resp
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERPreMor X Y)
    {g₁ g₂ : TreePERPreMor Y Z}
    (hg : treePERMorEqv g₁ g₂) :
    treePERMorEqv
      (treePERPreMorComp f g₁)
      (treePERPreMorComp f g₂) := by
  intro D e hdom
  change IsLeafConst
    (e ≫ cfpLift (f.map ≫ g₁.map)
      (f.map ≫ g₂.map) ≫ Z.rel)
  unfold IsLeafConst
  rw [← cfpLift_precomp
    f.map g₁.map g₂.map, Category.assoc]
  have diag_f :
      f.map ≫ cfpLift (𝟙 p.T) (𝟙 p.T) =
      cfpLift f.map f.map := by
    rw [cfpLift_precomp]
    simp only [Category.comp_id]
  have f_self : IsLeafConst
      (e ≫ cfpLift f.map f.map ≫
        Y.rel) :=
    treePERMorEqv_refl f e hdom
  have f_dom : IsLeafConst
      ((e ≫ f.map) ≫
        cfpLift (𝟙 p.T) (𝟙 p.T) ≫
        Y.rel) := by
    unfold IsLeafConst at f_self ⊢
    rw [Category.assoc,
      ← Category.assoc f.map,
      ← Category.assoc e]
    rw [diag_f]
    rw [Category.assoc]
    exact f_self
  have := hg (e ≫ f.map) f_dom
  unfold IsLeafConst at this
  rw [Category.assoc] at this
  exact this

/-- Lift composition to the quotient. -/
def treePERMorComp
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERMor X Y)
    (g : TreePERMor Y Z) :
    TreePERMor X Z :=
  Quotient.lift₂
    (s₁ := treePERSetoid X Y)
    (s₂ := treePERSetoid Y Z)
    (fun f' g' =>
      Quotient.mk (treePERSetoid X Z)
        (treePERPreMorComp f' g'))
    (fun (f₁ : TreePERPreMor X Y)
      (g₁ : TreePERPreMor Y Z)
      (f₂ : TreePERPreMor X Y)
      (g₂ : TreePERPreMor Y Z)
      (hf : treePERMorEqv f₁ f₂)
      (hg : treePERMorEqv g₁ g₂) => by
      apply Quotient.sound
        (s := treePERSetoid X Z)
      exact treePERMorEqv_trans
        (treePERComp_left_resp g₁ hf)
        (treePERComp_right_resp f₂ hg))
    f g

/-- Identity morphism in the quotient. -/
def treePERMorId
    (X : @TreePERObj C _ h p) :
    TreePERMor X X :=
  Quotient.mk (treePERSetoid X X)
    (treePERPreMorId X)

/-! ## Category laws on the quotient -/

theorem treePERMorId_comp
    {X Y : @TreePERObj C _ h p}
    (f : TreePERMor X Y) :
    treePERMorComp (treePERMorId X) f = f :=
  Quotient.ind
    (motive := fun f =>
      treePERMorComp (treePERMorId X) f = f)
    (fun f' => by
      apply congr_arg
        (Quotient.mk (treePERSetoid X Y))
      exact treePERPreMorId_comp f')
    f

theorem treePERMorComp_id
    {X Y : @TreePERObj C _ h p}
    (f : TreePERMor X Y) :
    treePERMorComp f (treePERMorId Y) = f :=
  Quotient.ind
    (motive := fun f =>
      treePERMorComp f (treePERMorId Y) = f)
    (fun f' => by
      apply congr_arg
        (Quotient.mk (treePERSetoid X Y))
      exact treePERPreMorComp_id f')
    f

theorem treePERMorComp_assoc
    {X Y Z W : @TreePERObj C _ h p}
    (f : TreePERMor X Y)
    (g : TreePERMor Y Z)
    (k : TreePERMor Z W) :
    treePERMorComp (treePERMorComp f g) k =
      treePERMorComp f
        (treePERMorComp g k) :=
  Quotient.ind
    (motive := fun f =>
      treePERMorComp (treePERMorComp f g) k =
        treePERMorComp f
          (treePERMorComp g k))
    (fun f' =>
      Quotient.ind
        (motive := fun g =>
          treePERMorComp
            (treePERMorComp
              (Quotient.mk _ f') g) k =
          treePERMorComp
            (Quotient.mk _ f')
            (treePERMorComp g k))
        (fun g' =>
          Quotient.ind
            (motive := fun k =>
              treePERMorComp
                (treePERMorComp
                  (Quotient.mk _ f')
                  (Quotient.mk _ g')) k =
              treePERMorComp
                (Quotient.mk _ f')
                (treePERMorComp
                  (Quotient.mk _ g') k))
            (fun k' => by
              apply congr_arg
                (Quotient.mk
                  (treePERSetoid X W))
              exact
                treePERPreMorComp_assoc
                  f' g' k')
            k)
        g)
    f

/-! ## Category instance -/

/-- The PER category: objects are PER objects on T,
morphisms are equivalence classes of
relation-preserving maps. -/
instance treePERCategory :
    Category (@TreePERObj C _ h p) where
  Hom := TreePERMor
  id := treePERMorId
  comp := treePERMorComp
  id_comp := treePERMorId_comp
  comp_id := treePERMorComp_id
  assoc := treePERMorComp_assoc

end GebLean
