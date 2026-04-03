import GebLean.TreeLogic

/-!
# PER Objects and Category on Binary Trees

Defines partial equivalence relations (PERs) on
the binary tree type T within a Lawvere BT theory,
relation-preserving morphisms, morphism equivalence,
and the category instance.

A PER on T is a morphism `rel : T × T → T` satisfying
symmetry and transitivity, where leaf encodes true and
non-leaf encodes false.

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

/-! ## Leaf-constantness predicate -/

/-! ## PER objects -/

/--
A partial equivalence relation (PER) on the binary
tree type T.

A PER consists of a morphism `rel : T × T → T`
(encoding a T-valued relation where leaf = true)
satisfying:
- Symmetry: `rel(x, y) = rel(y, x)`
- Transitivity: `propAnd(rel(x,z), rel(z,y))`
  implies `rel(x,y)`, encoded as a morphism
  equation on `T × (T × T)`
-/
structure TreePERObj where
  /-- The relation morphism `T × T → T`. -/
  rel : cfpProd p.T p.T ⟶ p.T
  /-- Symmetry: swapping inputs preserves the
  relation. -/
  rel_symm :
    cfpSwap p.T p.T ≫ rel = rel
  /-- Transitivity: `propAnd(rel(x,z), rel(z,y))`
  implies `rel(x,y)`, i.e.,
  `propAnd(propAnd(rel(x,z), rel(z,y)), rel(x,y))
   = propAnd(rel(x,z), rel(z,y))`. -/
  rel_trans :
    cfpLift
      (cfpLift
        (cfpLift t3x t3z ≫ rel)
        (cfpLift t3z t3y ≫ rel) ≫
        propAnd)
      (cfpLift t3x t3y ≫ rel) ≫
      propAnd =
    cfpLift
      (cfpLift t3x t3z ≫ rel)
      (cfpLift t3z t3y ≫ rel) ≫
      propAnd

/-- Derive the Prop-valued transitivity from the
equational form: for any `e : D ⟶ T × (T × T)`,
if `rel(x,z)` and `rel(z,y)` are leaf-constant,
then `rel(x,y)` is leaf-constant.

The proof pre-composes the equational `rel_trans`
with `e`, substitutes the leaf-constant hypotheses
into both sides, then uses `propAnd_leaf_left` to
extract the conclusion. -/
theorem TreePERObj.rel_trans_prop
    (X : @TreePERObj C _ h p)
    {D : C}
    (e : D ⟶ cfpProd p.T (cfpProd p.T p.T))
    (h1 : IsLeafConst
      (e ≫ cfpLift t3x t3z ≫ X.rel))
    (h2 : IsLeafConst
      (e ≫ cfpLift t3z t3y ≫ X.rel)) :
    IsLeafConst
      (e ≫ cfpLift t3x t3y ≫ X.rel) := by
  unfold IsLeafConst at h1 h2 ⊢
  -- Auxiliary: cfpLift leaf leaf ≫ propAnd = leaf
  have lift_ℓℓ_eq :
      cfpLift p.ℓ p.ℓ =
      p.ℓ ≫ cfpLift (𝟙 p.T) (𝟙 p.T) := by
    rw [cfpLift_precomp]
    simp only [Category.comp_id]
  have leaf_leaf_propAnd :
      cfpLift p.ℓ p.ℓ ≫ propAnd = p.ℓ := by
    rw [lift_ℓℓ_eq, Category.assoc,
      propAnd_idem, Category.comp_id]
  have leaf_idem :
      cfpLift (cfpTerminalFrom D ≫ p.ℓ)
        (cfpTerminalFrom D ≫ p.ℓ) ≫
        propAnd =
      cfpTerminalFrom D ≫ p.ℓ := by
    rw [← cfpLift_precomp
      (cfpTerminalFrom D) p.ℓ p.ℓ,
      Category.assoc, leaf_leaf_propAnd]
  -- Auxiliary: propAnd(leaf, X) = X
  have leaf_elim :
      ∀ (B : D ⟶ p.T),
      cfpLift (cfpTerminalFrom D ≫ p.ℓ) B ≫
        propAnd = B := by
    intro B
    have : cfpLift (cfpTerminalFrom D ≫ p.ℓ)
        B = cfpLift (cfpTerminalFrom D) B ≫
          cfpMap p.ℓ (𝟙 p.T) := by
      rw [cfpLift_cfpMap, Category.comp_id]
    rw [this, Category.assoc,
      propAnd_leaf_left, cfpLift_snd]
  -- Pre-compose rel_trans with e.
  have eq : e ≫ (cfpLift
      (cfpLift
        (cfpLift t3x t3z ≫ X.rel)
        (cfpLift t3z t3y ≫ X.rel) ≫
        propAnd)
      (cfpLift t3x t3y ≫ X.rel) ≫
      propAnd) = e ≫ (cfpLift
      (cfpLift t3x t3z ≫ X.rel)
      (cfpLift t3z t3y ≫ X.rel) ≫
      propAnd) :=
    congr_arg (e ≫ ·) X.rel_trans
  -- Distribute e into cfpLift via
  -- propAnd_precomp (outer, then inner).
  rw [propAnd_precomp e,
    propAnd_precomp e] at eq
  -- Substitute h1, h2 to simplify.
  rw [h1, h2, leaf_idem] at eq
  rw [leaf_elim] at eq
  exact eq

/-! ## Pre-morphisms -/

/--
A pre-morphism between PER objects: a morphism
`map : T → T` that preserves the relation in the
forward direction.

The preservation condition is Prop-valued over
generalized elements: for any `e : D ⟶ T × T`,
if `X.rel` is leaf-constant on `e`, then `Y.rel`
is leaf-constant on `(map × map) ∘ e`.
-/
structure TreePERPreMor
    (X Y : @TreePERObj C _ h p) where
  /-- The underlying morphism `T → T`. -/
  map : p.T ⟶ p.T
  /-- Forward relation preservation: if the
  source PER holds, the target PER holds on the
  mapped inputs. -/
  map_rel :
    {D : C} →
    (e : D ⟶ cfpProd p.T p.T) →
    IsLeafConst (e ≫ X.rel) →
    IsLeafConst (e ≫ cfpMap map map ≫ Y.rel)

/-- The identity pre-morphism. -/
def treePERPreMorId
    (X : @TreePERObj C _ h p) :
    TreePERPreMor X X where
  map := 𝟙 p.T
  map_rel := by
    intro D e hX
    rwa [cfpMap_id, Category.id_comp]

/-- Composition of pre-morphisms. -/
def treePERPreMorComp
    {X Y Z : @TreePERObj C _ h p}
    (f : TreePERPreMor X Y)
    (g : TreePERPreMor Y Z) :
    TreePERPreMor X Z where
  map := f.map ≫ g.map
  map_rel := by
    intro D e hX
    have step1 := f.map_rel e hX
    unfold IsLeafConst at step1 ⊢
    have step1a :
        (e ≫ cfpMap f.map f.map) ≫ Y.rel =
          cfpTerminalFrom D ≫ p.ℓ := by
      rw [Category.assoc]; exact step1
    have step2 :=
      g.map_rel
        (e ≫ cfpMap f.map f.map) step1a
    unfold IsLeafConst at step2
    rw [Category.assoc] at step2
    rw [← cfpMap_comp
      f.map f.map g.map g.map,
      Category.assoc]
    exact step2

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
  have := f.map_rel
    (e ≫ cfpLift (𝟙 p.T) (𝟙 p.T)) hdom'
  unfold IsLeafConst at this
  rw [Category.assoc] at this
  exact this

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
  have h1 := hf e hdom
  unfold IsLeafConst at h1 ⊢
  rw [← cfpLift_cfpMap]
  simp only [Category.assoc]
  have h1' :
      (e ≫ cfpLift f₁.map f₂.map) ≫
        Y.rel =
      cfpTerminalFrom D ≫ p.ℓ := by
    rw [Category.assoc]; exact h1
  have step :=
    g.map_rel
      (e ≫ cfpLift f₁.map f₂.map) h1'
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
