import GebLean.EqualizerCompletionLimits
import GebLean.EqualizerCompletionPBTO
import GebLean.LawvereBT

/-!
# Parameterized Snoclist Objects

Defines the parameterized snoclist object (PSO) for an
arbitrary element type `B`, the parameterized
snoclist-of-trees object (PSTO) as a PSO with `B = L`,
and constructions relating PSOs, PNNOs, and PBTOs.

The PSO is the parameterized initial algebra of the
functor `X |-> 1 + X x B`.  Its elimination rule
gives, for `f : A -> X` and `g : X x B -> X`, a
unique `phi : A x L -> X` satisfying
`phi(a, nil) = f(a)` and
`phi(a, snoc(l, b)) = g(phi(a, l), b)`.

The correspondence with binary trees uses
left-associative structure: `branch(l, b) = snoc(l, b)`,
making PSTO the natural intermediary for PBTO
conversions.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]

/-- From `A × (L × B)`, produce `(φ(a, l), b)` as
an element of `X × B`.  Given `φ : A × L ⟶ X`,
extracts `(a, l)` via `cfpAssocFst` and applies `φ`
for the first component, and extracts `b` via the
second projections for the second component. -/
def cfpLiftRecElem {A L B X : C}
    (φ : cfpProd A L ⟶ X) :
    cfpProd A (cfpProd L B) ⟶ cfpProd X B :=
  cfpLift
    (cfpAssocFst A L B ≫ φ)
    (cfpSnd A (cfpProd L B) ≫ cfpSnd L B)

/-- A parameterized snoclist object for element type
`B` in a category with chosen finite products.  The
PSO is the parameterized initial algebra of the
functor `X ↦ 1 + X × B`.  The step morphism
`g : X × B ⟶ X` takes the accumulated result paired
with the next element, corresponding to a left fold
(snoclist). -/
class IsPSO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C]
    (B : C) (L : C) where
  /-- The empty snoclist. -/
  nil : cfpTerminal ⟶ L
  /-- Append an element to a snoclist. -/
  snoc : cfpProd L B ⟶ L
  /-- The unique morphism given by the universal
  property: for `f : A ⟶ X` and `g : X × B ⟶ X`,
  the parameterized fold `φ : A × L ⟶ X`. -/
  elim : ∀ {A X : C},
    (A ⟶ X) → (cfpProd X B ⟶ X) →
    (cfpProd A L ⟶ X)
  /-- Base case: `φ(a, nil) = f(a)`. -/
  elim_nil : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd X B ⟶ X),
    cfpInsertSnd nil A ≫ elim f g = f
  /-- Step case:
  `φ(a, snoc(l, b)) = g(φ(a, l), b)`.
  From `A × (L × B)`, the pair `(a, l)` is
  extracted and `φ` applied for the first
  component, while `b` is extracted for the second,
  producing `(φ(a, l), b)` which is then passed
  to `g`. -/
  elim_snoc : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd X B ⟶ X),
    cfpMap (𝟙 A) snoc ≫ elim f g =
      cfpLiftRecElem (elim f g) ≫ g
  /-- Uniqueness. -/
  elim_uniq : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd X B ⟶ X)
    (φ : cfpProd A L ⟶ X),
    cfpInsertSnd nil A ≫ φ = f →
    cfpMap (𝟙 A) snoc ≫ φ =
      cfpLiftRecElem φ ≫ g →
    φ = elim f g

/-- Existential wrapper: a category has a PSO for
element type `B` if there exists an object `L`
carrying the `IsPSO` structure. -/
class HasPSO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (B : C) where
  /-- The snoclist object. -/
  L : C
  /-- The PSO structure on `L`. -/
  [isPSO : IsPSO C B L]

attribute [reducible, instance] HasPSO.isPSO

/-- A parameterized snoclist-of-trees object: a PSO
whose element type coincides with the snoclist object
itself (`B = L = T`). -/
abbrev IsPSTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (T : C) :=
  IsPSO C T T

/-- Existential wrapper for the PSTO: a category has a
PSTO if there exists an object `T` carrying the
`IsPSTO` structure. -/
class HasPSTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] where
  /-- The snoclist-of-trees object. -/
  T : C
  /-- The PSTO structure on `T`. -/
  [isPSTO : IsPSTO C T]

attribute [reducible, instance] HasPSTO.isPSTO

section PSO_Terminal_NNO

variable [nno : HasNNO C]

omit nno in
private theorem cfpMap_id_fst_eq_assocFst
    (A B D : C) :
    cfpMap (𝟙 A) (cfpFst B D) =
      cfpAssocFst A B D := by
  unfold cfpMap cfpAssocFst
  congr 1
  exact Category.comp_id
    (cfpFst A (cfpProd B D))

omit nno in
private theorem cfpMap_id_fst_comp
    {A B D B' : C} (f : B ⟶ B') :
    cfpMap (𝟙 A) (cfpFst B D ≫ f) =
      cfpAssocFst A B D ≫
        cfpMap (𝟙 A) f := by
  symm
  apply cfpLift_uniq
  · rw [Category.assoc, cfpMap_fst,
      ← Category.assoc,
      show cfpAssocFst A B D ≫
          cfpFst A B =
        cfpFst A (cfpProd B D) from
        cfpLift_fst _ _]
  · rw [Category.assoc, cfpMap_snd,
      ← Category.assoc,
      show cfpAssocFst A B D ≫
          cfpSnd A B =
        cfpSnd A (cfpProd B D) ≫
          cfpFst B D from
        cfpLift_snd _ _,
      Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem nnoToIsPSO_elim_uniq_step
    {A X : C} (φ : cfpProd A nno.N ⟶ X)
    (g : cfpProd X cfpTerminal ⟶ X)
    (hsnoc :
      cfpMap (𝟙 A)
        (cfpFst nno.N cfpTerminal ≫ nno.s) ≫
        φ =
      cfpLiftRecElem φ ≫ g) :
    cfpMap (𝟙 A) nno.s ≫ φ =
      φ ≫ (cfpLift (𝟙 X)
        (cfpTerminalFrom X) ≫ g) := by
  set ι := cfpMap (𝟙 A)
    (cfpInsertSnd (𝟙 cfpTerminal) nno.N)
  -- Step 1: ι ≫ LHS of hsnoc = cfpMap (𝟙 A) s ≫ φ
  have hlhs : ι ≫
      cfpMap (𝟙 A)
        (cfpFst nno.N cfpTerminal ≫ nno.s) ≫
        φ =
      cfpMap (𝟙 A) nno.s ≫ φ := by
    rw [← Category.assoc]
    congr 1
    -- Goal: ι ≫ cfpMap (𝟙 A) (fst ≫ s)
    --   = cfpMap (𝟙 A) s
    simp only [ι]
    rw [cfpMap_comp, Category.id_comp]
    congr 1
    unfold cfpInsertSnd
    rw [← Category.assoc, cfpLift_fst,
      Category.id_comp]
  -- Step 2: ι ≫ RHS of hsnoc
  --   = φ ≫ cfpLift (𝟙 X) (cfpTerminalFrom X) ≫ g
  have hrhs : ι ≫ cfpLiftRecElem φ ≫ g =
      φ ≫ (cfpLift (𝟙 X)
        (cfpTerminalFrom X) ≫ g) := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    -- Goal: ι ≫ cfpLiftRecElem φ
    --   = φ ≫ cfpLift (𝟙 X) (cfpTerminalFrom X)
    -- Rewrite RHS using cfpLift_precomp
    rw [cfpLift_precomp, Category.comp_id]
    -- RHS is now cfpLift φ (φ ≫ cfpTerminalFrom X)
    -- Rewrite LHS
    unfold cfpLiftRecElem
    rw [cfpLift_precomp]
    -- Now both sides are cfpLift
    congr 1
    · -- fst component:
      --   ι ≫ cfpAssocFst A N 1 ≫ φ = φ
      rw [← Category.assoc,
        ← cfpMap_id_fst_eq_assocFst]
      simp only [ι]
      rw [cfpMap_comp, Category.id_comp]
      unfold cfpInsertSnd
      rw [cfpLift_fst, cfpMap_id,
        Category.id_comp]
    · -- snd component: both to cfpTerminal
      rw [h.terminal.uniq
        (ι ≫ (cfpSnd A (cfpProd nno.N
          cfpTerminal) ≫
          cfpSnd nno.N cfpTerminal)),
        h.terminal.uniq
          (φ ≫ cfpTerminalFrom X)]
  rw [← hlhs, hsnoc, hrhs]

set_option backward.isDefEq.respectTransparency false in
instance nnoToIsPSO :
    IsPSO C (cfpTerminal (h := h)) nno.N where
  nil := nno.z
  snoc := cfpFst nno.N cfpTerminal ≫ nno.s
  elim := fun {A X} f g =>
    nno.elim f
      (cfpLift (𝟙 X) (cfpTerminalFrom X) ≫ g)
  elim_nil := fun f g => nno.elim_z f _
  elim_snoc := fun {A X} f g => by
    set g' := cfpLift (𝟙 X)
      (cfpTerminalFrom X) ≫ g
    set φ := nno.elim f g'
    -- Rewrite cfpMap (𝟙 A) (fst ≫ s) using
    -- cfpMap_id_fst_comp
    rw [cfpMap_id_fst_comp nno.s,
      Category.assoc,
      nno.elim_s f g']
    -- Goal: cfpAssocFst ≫ φ ≫ g'
    --   = cfpLiftRecElem φ ≫ g
    -- where g' = cfpLift (𝟙 X) (term X) ≫ g
    simp only [g']
    rw [← Category.assoc φ
      (cfpLift (𝟙 X) (cfpTerminalFrom X)) g,
      ← Category.assoc
      (cfpAssocFst A nno.N cfpTerminal)
      (φ ≫ cfpLift (𝟙 X)
        (cfpTerminalFrom X)) g]
    congr 1
    -- Goal: cfpAssocFst ≫ φ ≫
    --   cfpLift (𝟙 X) (cfpTerminalFrom X)
    --   = cfpLiftRecElem φ
    rw [cfpLift_precomp, cfpLift_precomp]
    unfold cfpLiftRecElem
    congr 1
    · rw [Category.comp_id]
    · rw [h.terminal.uniq
        (cfpAssocFst A nno.N cfpTerminal ≫
          φ ≫ cfpTerminalFrom X),
        h.terminal.uniq
        (cfpSnd A (cfpProd nno.N cfpTerminal)
          ≫ cfpSnd nno.N cfpTerminal)]
  elim_uniq := fun {A X} f g φ hnil hsnoc => by
    set g' := cfpLift (𝟙 X)
      (cfpTerminalFrom X) ≫ g
    -- Use nno.elim_uniq, proving both conditions.
    apply nno.elim_uniq f g' φ hnil
    -- Goal: cfpMap (𝟙 A) s ≫ φ = φ ≫ g'
    exact nnoToIsPSO_elim_uniq_step φ g hsnoc

end PSO_Terminal_NNO

/-- A PSTO is in particular a PSO with `B = T`. -/
instance (priority := 100) pstoToHasPSO
    {C : Type u} [Category.{v} C]
    [HasChosenFiniteProducts C]
    [p : HasPSTO C] : HasPSO C p.T where
  L := p.T

section PBTO_to_PSTO

variable [p : HasPBTO C]

/-- Base morphism for the PBTO-to-PSTO enriched
catamorphism: `a ↦ (ℓ, f(a))`. -/
private def pstoBase {A X : C} (f : A ⟶ X) :
    A ⟶ cfpProd p.T X :=
  cfpLift (cfpTerminalFrom A ≫ p.ℓ) f

/-- Step morphism for the PBTO-to-PSTO enriched
catamorphism: `((t₁, x₁), (t₂, x₂)) ↦
(β(t₁, t₂), g(x₁, t₂))`.  The left pair
provides the recursive result `x₁` on the
accumulated snoclist, and the right pair provides
the element `t₂` as data. -/
private def pstoStep {X : C}
    (g : cfpProd X p.T ⟶ X) :
    cfpProd (cfpProd p.T X) (cfpProd p.T X) ⟶
      cfpProd p.T X :=
  let TX := cfpProd p.T X
  let t1 : cfpProd TX TX ⟶ p.T :=
    cfpFst TX TX ≫ cfpFst p.T X
  let x1 : cfpProd TX TX ⟶ X :=
    cfpFst TX TX ≫ cfpSnd p.T X
  let t2 : cfpProd TX TX ⟶ p.T :=
    cfpSnd TX TX ≫ cfpFst p.T X
  cfpLift
    (cfpLift t1 t2 ≫ p.β)
    (cfpLift x1 t2 ≫ g)

/-- PSO elimination derived from the PBTO
catamorphism on the enriched carrier `T × X`:
the second projection of
`p.elim (pstoBase f) (pstoStep g)`. -/
private def pstoElim {A X : C}
    (f : A ⟶ X) (g : cfpProd X p.T ⟶ X) :
    cfpProd A p.T ⟶ X :=
  p.elim (pstoBase f) (pstoStep g) ≫
    cfpSnd p.T X

private theorem pstoBase_fst {A X : C}
    (f : A ⟶ X) :
    pstoBase f ≫ cfpFst p.T X =
      cfpTerminalFrom A ≫ p.ℓ :=
  cfpLift_fst _ _

private theorem pstoBase_snd {A X : C}
    (f : A ⟶ X) :
    pstoBase f ≫ cfpSnd p.T X = f :=
  cfpLift_snd _ _

private theorem pstoStep_fst {X : C}
    (g : cfpProd X p.T ⟶ X) :
    pstoStep g ≫ cfpFst p.T X =
      cfpLift
        (cfpFst (cfpProd p.T X)
          (cfpProd p.T X) ≫ cfpFst p.T X)
        (cfpSnd (cfpProd p.T X)
          (cfpProd p.T X) ≫ cfpFst p.T X) ≫
      p.β :=
  cfpLift_fst _ _

private theorem pstoStep_snd {X : C}
    (g : cfpProd X p.T ⟶ X) :
    pstoStep g ≫ cfpSnd p.T X =
      cfpLift
        (cfpFst (cfpProd p.T X)
          (cfpProd p.T X) ≫ cfpSnd p.T X)
        (cfpSnd (cfpProd p.T X)
          (cfpProd p.T X) ≫ cfpFst p.T X) ≫
      g :=
  cfpLift_snd _ _

private theorem pstoStep_fst_eq {X : C}
    (g : cfpProd X p.T ⟶ X) :
    cfpMap (cfpFst p.T X) (cfpFst p.T X) ≫
      p.β =
    pstoStep g ≫ cfpFst p.T X := by
  rw [pstoStep_fst]
  unfold cfpMap
  rfl

/-- The first projection of the enriched
catamorphism `p.elim (pstoBase f) (pstoStep g)`
equals the tree projection `cfpSnd A p.T`. -/
private theorem pstoElim_fst {A X : C}
    (f : A ⟶ X) (g : cfpProd X p.T ⟶ X) :
    p.elim (pstoBase f) (pstoStep g) ≫
      cfpFst p.T X =
    cfpSnd A p.T := by
  rw [elim_algebra_morphism
    (pstoBase f) (pstoStep g)
    (cfpFst p.T X) p.β
    (pstoStep_fst_eq g),
    pstoBase_fst]
  symm
  apply p.elim_uniq
  · -- base: cfpInsertSnd ℓ A ≫ cfpSnd A T
    --   = cfpTerminalFrom A ≫ ℓ
    unfold cfpInsertSnd
    exact cfpLift_snd _ _
  · -- step: cfpMap (𝟙 A) β ≫ cfpSnd A T
    --   = cfpLiftAssoc (cfpSnd A T)
    --     (cfpSnd A T) ≫ β
    rw [cfpMap_snd]
    congr 1
    unfold cfpLiftAssoc
    apply cfpLift_uniq
    · unfold cfpAssocFst
      exact (cfpLift_snd _ _).symm
    · unfold cfpAssocSnd
      exact (cfpLift_snd _ _).symm

private theorem pstoElim_nil {A X : C}
    (f : A ⟶ X) (g : cfpProd X p.T ⟶ X) :
    cfpInsertSnd p.ℓ A ≫ pstoElim f g = f := by
  unfold pstoElim
  rw [← Category.assoc, p.elim_ℓ,
    pstoBase_snd]

/-- The second projection of `cfpLiftAssoc θ θ`
followed by the tree projection agrees with
`cfpAssocSnd` followed by the tree
projection. -/
private theorem pstoElim_snoc_t2 {A X : C}
    (f : A ⟶ X) (g : cfpProd X p.T ⟶ X) :
    let TX := cfpProd p.T X
    let θ := p.elim (pstoBase f) (pstoStep g)
    cfpLiftAssoc θ θ ≫
      (cfpSnd TX TX ≫ cfpFst p.T X) =
    cfpSnd A (cfpProd p.T p.T) ≫
      cfpSnd p.T p.T := by
  intro TX θ
  rw [← Category.assoc,
    show cfpLiftAssoc θ θ ≫ cfpSnd TX TX =
      cfpAssocSnd A p.T p.T ≫ θ from
      cfpLift_snd _ _,
    Category.assoc,
    pstoElim_fst f g]
  unfold cfpAssocSnd
  exact cfpLift_snd _ _

private theorem pstoElim_snoc {A X : C}
    (f : A ⟶ X) (g : cfpProd X p.T ⟶ X) :
    cfpMap (𝟙 A) p.β ≫ pstoElim f g =
      cfpLiftRecElem (pstoElim f g) ≫ g := by
  set TX := cfpProd p.T X
  set θ := p.elim (pstoBase f) (pstoStep g)
  unfold pstoElim
  -- LHS: rewrite using elim_β
  rw [← Category.assoc, p.elim_β,
    Category.assoc, pstoStep_snd,
    ← Category.assoc]
  -- Goal: cfpLiftAssoc θ θ ≫ cfpLift x1 t2 ≫ g
  --   = cfpLiftRecElem (θ ≫ cfpSnd) ≫ g
  congr 1
  -- Show the morphisms before g agree.
  rw [cfpLift_precomp]
  unfold cfpLiftRecElem
  congr 1
  · -- fst component:
    -- cfpLiftAssoc θ θ ≫ fst TX TX ≫ snd T X
    -- = cfpAssocFst A T T ≫ θ ≫ snd T X
    rw [← Category.assoc,
      show cfpLiftAssoc θ θ ≫ cfpFst TX TX =
        cfpAssocFst A p.T p.T ≫ θ from
        cfpLift_fst _ _,
      Category.assoc]
  · -- snd component:
    exact pstoElim_snoc_t2 f g

private theorem pstoElim_uniq_base {A X : C}
    (f : A ⟶ X)
    (ψ : cfpProd A p.T ⟶ X)
    (hnil : cfpInsertSnd p.ℓ A ≫ ψ = f) :
    cfpInsertSnd p.ℓ A ≫
      cfpLift (cfpSnd A p.T) ψ =
    pstoBase f := by
  rw [cfpLift_precomp]
  unfold pstoBase
  congr 1
  · unfold cfpInsertSnd
    exact cfpLift_snd _ _

omit p in
private theorem cfpProd_ext {A B D : C}
    (m₁ m₂ : D ⟶ cfpProd A B)
    (hf : m₁ ≫ cfpFst A B = m₂ ≫ cfpFst A B)
    (hs : m₁ ≫ cfpSnd A B = m₂ ≫ cfpSnd A B) :
    m₁ = m₂ := by
  have h2 := cfpLift_uniq
    (m₂ ≫ cfpFst A B) (m₂ ≫ cfpSnd A B)
    m₂ rfl rfl
  rw [h2]
  exact cfpLift_uniq _ _ m₁ hf hs

/-- The first-projection component of the enriched
step case for uniqueness. -/
private theorem pstoElim_uniq_step_fst {A X : C}
    (g : cfpProd X p.T ⟶ X)
    (ψ : cfpProd A p.T ⟶ X) :
    let θ' := cfpLift (cfpSnd A p.T) ψ
    (cfpMap (𝟙 A) p.β ≫ θ') ≫
      cfpFst p.T X =
    (cfpLiftAssoc θ' θ' ≫
      pstoStep g) ≫ cfpFst p.T X := by
  intro θ'
  -- LHS = cfpSnd A (T×T) ≫ β
  have lhs_eq :
      (cfpMap (𝟙 A) p.β ≫ θ') ≫
        cfpFst p.T X =
      cfpSnd A (cfpProd p.T p.T) ≫ p.β := by
    rw [Category.assoc,
      show θ' ≫ cfpFst p.T X =
        cfpSnd A p.T from cfpLift_fst _ _,
      cfpMap_snd]
  -- RHS = cfpSnd A (T×T) ≫ β
  have rhs_eq :
      (cfpLiftAssoc θ' θ' ≫
        pstoStep g) ≫ cfpFst p.T X =
      cfpSnd A (cfpProd p.T p.T) ≫ p.β := by
    rw [Category.assoc, pstoStep_fst,
      ← Category.assoc]
    congr 1
    have θ'_fst : θ' ≫ cfpFst p.T X =
        cfpSnd A p.T := cfpLift_fst _ _
    have la_fst :
        cfpLiftAssoc θ' θ' ≫
          cfpFst (cfpProd p.T X)
            (cfpProd p.T X) =
        cfpAssocFst A p.T p.T ≫ θ' :=
      cfpLift_fst _ _
    have la_snd :
        cfpLiftAssoc θ' θ' ≫
          cfpSnd (cfpProd p.T X)
            (cfpProd p.T X) =
        cfpAssocSnd A p.T p.T ≫ θ' :=
      cfpLift_snd _ _
    have hfst :
        cfpLiftAssoc θ' θ' ≫
          (cfpFst (cfpProd p.T X)
            (cfpProd p.T X) ≫
          cfpFst p.T X) =
        cfpAssocFst A p.T p.T ≫
          cfpSnd A p.T := by
      rw [← Category.assoc, la_fst,
        Category.assoc, θ'_fst]
    have hsnd :
        cfpLiftAssoc θ' θ' ≫
          (cfpSnd (cfpProd p.T X)
            (cfpProd p.T X) ≫
          cfpFst p.T X) =
        cfpAssocSnd A p.T p.T ≫
          cfpSnd A p.T := by
      rw [← Category.assoc, la_snd,
        Category.assoc, θ'_fst]
    rw [cfpLift_precomp, hfst, hsnd]
    symm
    apply cfpLift_uniq
    · unfold cfpAssocFst
      exact (cfpLift_snd _ _).symm
    · unfold cfpAssocSnd
      exact (cfpLift_snd _ _).symm
  rw [lhs_eq, rhs_eq]

/-- The second-projection component of the enriched
step case for uniqueness. -/
private theorem pstoElim_uniq_step_snd {A X : C}
    (g : cfpProd X p.T ⟶ X)
    (ψ : cfpProd A p.T ⟶ X)
    (hsnoc :
      cfpMap (𝟙 A) p.β ≫ ψ =
        cfpLiftRecElem ψ ≫ g) :
    let θ' := cfpLift (cfpSnd A p.T) ψ
    (cfpMap (𝟙 A) p.β ≫ θ') ≫
      cfpSnd p.T X =
    (cfpLiftAssoc θ' θ' ≫
      pstoStep g) ≫ cfpSnd p.T X := by
  intro θ'
  rw [Category.assoc,
    show θ' ≫ cfpSnd p.T X = ψ from
      cfpLift_snd _ _,
    hsnoc,
    Category.assoc, pstoStep_snd,
    ← Category.assoc, cfpLift_precomp]
  -- Goal: cfpLift (...) (...) ≫ g
  --   = cfpLiftRecElem ψ ≫ g
  -- Suffices to show the morphisms before g agree.
  congr 1
  -- Both sides are cfpLift into X × T.
  -- Use cfpLift_uniq.
  unfold cfpLiftRecElem
  apply cfpLift_uniq
  · -- X component:
    -- cfpLiftAssoc θ' θ' ≫ fst TX TX ≫ snd T X
    -- = cfpAssocFst A T T ≫ ψ
    rw [cfpLift_fst,
      ← Category.assoc,
      show cfpLiftAssoc θ' θ' ≫
        cfpFst (cfpProd p.T X)
          (cfpProd p.T X) =
      cfpAssocFst A p.T p.T ≫ θ' from
        cfpLift_fst _ _,
      Category.assoc,
      show θ' ≫ cfpSnd p.T X = ψ from
        cfpLift_snd _ _]
  · rw [cfpLift_snd,
      ← Category.assoc,
      show cfpLiftAssoc θ' θ' ≫
        cfpSnd (cfpProd p.T X)
          (cfpProd p.T X) =
      cfpAssocSnd A p.T p.T ≫ θ' from
        cfpLift_snd _ _,
      Category.assoc,
      show θ' ≫ cfpFst p.T X =
        cfpSnd A p.T from cfpLift_fst _ _]
    exact (cfpLift_snd
      (cfpFst A (cfpProd p.T p.T))
      (cfpSnd A (cfpProd p.T p.T) ≫
        cfpSnd p.T p.T)).symm

/-- The enriched step case for uniqueness: the
candidate `θ' = cfpLift (cfpSnd A T) ψ` satisfies
the PBTO step equation for `pstoStep g`. -/
private theorem pstoElim_uniq_step {A X : C}
    (g : cfpProd X p.T ⟶ X)
    (ψ : cfpProd A p.T ⟶ X)
    (hsnoc :
      cfpMap (𝟙 A) p.β ≫ ψ =
        cfpLiftRecElem ψ ≫ g) :
    cfpMap (𝟙 A) p.β ≫
      cfpLift (cfpSnd A p.T) ψ =
    cfpLiftAssoc
      (cfpLift (cfpSnd A p.T) ψ)
      (cfpLift (cfpSnd A p.T) ψ) ≫
      pstoStep g := by
  exact cfpProd_ext _ _
    (pstoElim_uniq_step_fst g ψ)
    (pstoElim_uniq_step_snd g ψ hsnoc)

private theorem pstoElim_uniq {A X : C}
    (f : A ⟶ X) (g : cfpProd X p.T ⟶ X)
    (ψ : cfpProd A p.T ⟶ X)
    (hnil : cfpInsertSnd p.ℓ A ≫ ψ = f)
    (hsnoc :
      cfpMap (𝟙 A) p.β ≫ ψ =
        cfpLiftRecElem ψ ≫ g) :
    ψ = pstoElim f g := by
  set θ' := cfpLift (cfpSnd A p.T) ψ
  -- θ' satisfies the PBTO equations.
  have hθ' : θ' =
      p.elim (pstoBase f) (pstoStep g) :=
    p.elim_uniq (pstoBase f) (pstoStep g) θ'
      (pstoElim_uniq_base f ψ hnil)
      (pstoElim_uniq_step g ψ hsnoc)
  -- Recover ψ from θ' via snd projection.
  have : ψ = θ' ≫ cfpSnd p.T X :=
    (cfpLift_snd _ _).symm
  rw [this, hθ']
  rfl

instance pbtoToIsPSTO :
    IsPSTO C p.T where
  nil := p.ℓ
  snoc := p.β
  elim := fun f g => pstoElim f g
  elim_nil := fun f g => pstoElim_nil f g
  elim_snoc := fun f g => pstoElim_snoc f g
  elim_uniq := fun f g ψ hnil hsnoc =>
    pstoElim_uniq f g ψ hnil hsnoc

instance pbtoToHasPSTO : HasPSTO C where
  T := p.T

end PBTO_to_PSTO

end GebLean
