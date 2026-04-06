import GebLean.EqualizerCompletionLimits
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

end PBTO_to_PSTO

end GebLean
