import GebLean.PSO

/-!
# Parameterized List Objects

Defines the parameterized (cons-)list object (PLO)
for an arbitrary element type `B`, the parameterized
list-of-trees object (PLTO) as a PLO with `B = L`,
and the equivalence between PSTO and PLTO via
reversal.

The PLO is the parameterized initial algebra of the
functor `X |-> 1 + B x X`.  Its elimination rule
gives, for `f : A -> X` and `g : B x X -> X`, a
unique `phi : A x L -> X` satisfying
`phi(a, nil) = f(a)` and
`phi(a, cons(b, l)) = g(b, phi(a, l))`.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]

/-- From `A × (B × L)`, produce `(b, φ(a, l))` as
an element of `B × X`.  Given `φ : A × L ⟶ X`,
extracts `b` via the second and first projections
for the first component, and extracts `(a, l)` via
`cfpAssocSnd` and applies `φ` for the second
component. -/
def cfpLiftElemRec {A B L X : C}
    (φ : cfpProd A L ⟶ X) :
    cfpProd A (cfpProd B L) ⟶ cfpProd B X :=
  cfpLift
    (cfpSnd A (cfpProd B L) ≫ cfpFst B L)
    (cfpAssocSnd A B L ≫ φ)

/-- A parameterized (cons-)list object for element
type `B` in a category with chosen finite products.
The PLO is the parameterized initial algebra of the
functor `X ↦ 1 + B × X`.  The step morphism
`g : B × X ⟶ X` takes the next element paired with
the accumulated result, corresponding to a right fold
(cons-list).  This is the dual of `IsPSO`, which
uses `X × B` (left fold / snoclist). -/
class IsPLO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C]
    (B : C) (L : C) where
  /-- The empty list. -/
  nil : cfpTerminal ⟶ L
  /-- Prepend an element to a list. -/
  cons : cfpProd B L ⟶ L
  /-- The unique morphism given by the universal
  property: for `f : A ⟶ X` and `g : B × X ⟶ X`,
  the parameterized fold `φ : A × L ⟶ X`. -/
  elim : ∀ {A X : C},
    (A ⟶ X) → (cfpProd B X ⟶ X) →
    (cfpProd A L ⟶ X)
  /-- Base case: `φ(a, nil) = f(a)`. -/
  elim_nil : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd B X ⟶ X),
    cfpInsertSnd nil A ≫ elim f g = f
  /-- Step case:
  `φ(a, cons(b, l)) = g(b, φ(a, l))`.
  From `A × (B × L)`, the element `b` is
  extracted via second and first projections,
  while `(a, l)` is extracted via `cfpAssocSnd`
  and `φ` applied, producing `(b, φ(a, l))`
  which is then passed to `g`. -/
  elim_cons : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd B X ⟶ X),
    cfpMap (𝟙 A) cons ≫ elim f g =
      cfpLiftElemRec (elim f g) ≫ g
  /-- Uniqueness. -/
  elim_uniq : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd B X ⟶ X)
    (φ : cfpProd A L ⟶ X),
    cfpInsertSnd nil A ≫ φ = f →
    cfpMap (𝟙 A) cons ≫ φ =
      cfpLiftElemRec φ ≫ g →
    φ = elim f g

/-- Existential wrapper: a category has a PLO for
element type `B` if there exists an object `L`
carrying the `IsPLO` structure. -/
class HasPLO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (B : C) where
  /-- The list object. -/
  L : C
  /-- The PLO structure on `L`. -/
  [isPLO : IsPLO C B L]

attribute [reducible, instance] HasPLO.isPLO

/-- A parameterized list-of-trees object: a PLO
whose element type coincides with the list object
itself (`B = L = T`). -/
abbrev IsPLTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (T : C) :=
  IsPLO C T T

/-- Existential wrapper for the PLTO: a category has
a PLTO if there exists an object `T` carrying the
`IsPLTO` structure. -/
class HasPLTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] where
  /-- The list-of-trees object. -/
  T : C
  /-- The PLTO structure on `T`. -/
  [isPLTO : IsPLTO C T]

attribute [reducible, instance] HasPLTO.isPLTO

/-- A PLTO is in particular a PLO with `B = T`. -/
instance (priority := 100) pltoToHasPLO
    {C : Type u} [Category.{v} C]
    [HasChosenFiniteProducts C]
    [p : HasPLTO C] : HasPLO C p.T where
  L := p.T

section PLO_Paramorphism

variable {B L : C} [s : IsPLO C B L]

/-- Post-composing `cfpLiftElemRec φ` with
`cfpMap (𝟙 B) q` yields `cfpLiftElemRec (φ ≫ q)`. -/
private theorem cfpLiftElemRec_postcomp
    {A B' L' X X' : C}
    (φ : cfpProd A L' ⟶ X)
    (q : X ⟶ X') :
    cfpLiftElemRec φ ≫ cfpMap (𝟙 B') q =
    cfpLiftElemRec (φ ≫ q) := by
  unfold cfpLiftElemRec
  rw [cfpLift_cfpMap]
  congr 1
  · rw [Category.assoc, Category.comp_id]
  · rw [Category.assoc]

/-- Algebra morphism lemma for PLO: if `q : X ⟶ X'`
intertwines the step algebras via
`cfpMap (𝟙 B) q ≫ w = g ≫ q`, then
`elim f g ≫ q = elim (f ≫ q) w`. -/
private theorem ploElim_algebra_morphism
    {A X X' : C}
    (f : A ⟶ X) (g : cfpProd B X ⟶ X)
    (q : X ⟶ X')
    (w : cfpProd B X' ⟶ X')
    (hw : cfpMap (𝟙 B) q ≫ w = g ≫ q) :
    s.elim f g ≫ q = s.elim (f ≫ q) w := by
  exact s.elim_uniq (f ≫ q) w
    (s.elim f g ≫ q)
    (by rw [← Category.assoc, s.elim_nil])
    (by
      rw [← Category.assoc, s.elim_cons,
        Category.assoc, ← hw,
        ← Category.assoc,
        cfpLiftElemRec_postcomp])

/-- Carrier for the PLO paramorphism: the triple
`(A, (L, X))`. -/
private def ploParaCarrier (A X : C) : C :=
  cfpProd A (cfpProd L X)

/-- Base morphism for `ploParaElim`: sends `a : A` to
`(a, (nil, f(a)))`. -/
private def ploParaBase {A X : C} (f : A ⟶ X) :
    A ⟶ ploParaCarrier (L := L) A X :=
  cfpLift (𝟙 A)
    (cfpLift (cfpTerminalFrom A ≫ s.nil) f)

/-- Step morphism for `ploParaElim`: given
`(b, (a, (l, x)))` from `B × (A × (L × X))`, produces
`(a, (cons(b, l), g(a, b, l, x)))`.  The parameter `a`
is carried through unchanged; the list component is
extended by consing `b` onto the raw tail `l`; the
result component is `g` applied to the parameter,
element, raw tail, and recursive result. -/
private def ploParaStep {A X : C}
    (g : cfpProd A
        (cfpProd B (cfpProd L X)) ⟶ X) :
    cfpProd B (ploParaCarrier (L := L) A X) ⟶
      ploParaCarrier (L := L) A X :=
  let BX' := cfpProd B
    (ploParaCarrier (L := L) A X)
  let b : BX' ⟶ B := cfpFst B _
  let a : BX' ⟶ A :=
    cfpSnd B _ ≫ cfpFst A (cfpProd L X)
  let l : BX' ⟶ L :=
    cfpSnd B _ ≫ cfpSnd A (cfpProd L X) ≫
      cfpFst L X
  let x : BX' ⟶ X :=
    cfpSnd B _ ≫ cfpSnd A (cfpProd L X) ≫
      cfpSnd L X
  let bl : BX' ⟶ cfpProd B L :=
    cfpLift b l
  let gArg : BX' ⟶
      cfpProd A (cfpProd B (cfpProd L X)) :=
    cfpLift a (cfpLift b (cfpLift l x))
  cfpLift a
    (cfpLift (bl ≫ s.cons) (gArg ≫ g))

/-- PLO paramorphism: an enhanced fold whose step
function sees the parameter, the element, the raw
tail, and the recursive result on the tail.
The step `g` has type
`A × (B × (L × X)) ⟶ X`. -/
def ploParaElim {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd B (cfpProd L X)) ⟶ X) :
    cfpProd A L ⟶ X :=
  let base := ploParaBase (s := s) f
  let step := ploParaStep (s := s) g
  @IsPLO.elim C _ h B L s A
    (ploParaCarrier (L := L) A X)
    base step ≫
    cfpSnd A (cfpProd L X) ≫ cfpSnd L X

set_option backward.isDefEq.respectTransparency false in
/-- Base-case equation for `ploParaElim`: at nil,
the result is `f` applied to the parameter. -/
theorem ploParaElim_nil {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd B (cfpProd L X)) ⟶ X) :
    cfpInsertSnd s.nil A ≫
      ploParaElim (s := s) f g = f := by
  unfold ploParaElim
  simp only
  rw [← Category.assoc, ← Category.assoc,
    s.elim_nil]
  unfold ploParaBase
  rw [cfpLift_snd, cfpLift_snd]

set_option backward.isDefEq.respectTransparency false in
/-- Parameter invariant: the `A` component of the
enriched catamorphism carries the input parameter
through unchanged. -/
private theorem ploParaElim_param_inv {A X : C}
    (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd B (cfpProd L X)) ⟶ X) :
    @IsPLO.elim C _ h B L s A
        (cfpProd A (cfpProd L X))
        (ploParaBase (s := s) f)
        (ploParaStep (s := s) g) ≫
      cfpFst A (cfpProd L X) =
    cfpFst A L := by
  have step_q :
      cfpMap (𝟙 B)
          (cfpFst A (cfpProd L X)) ≫
        cfpSnd B A =
      ploParaStep (s := s) g ≫
        cfpFst A (cfpProd L X) := by
    rw [cfpMap_snd]
    unfold ploParaStep ploParaCarrier
    simp only
    rw [cfpLift_fst]
  rw [ploElim_algebra_morphism
      (ploParaBase (s := s) f)
      (ploParaStep (s := s) g)
      (cfpFst A (cfpProd L X))
      (cfpSnd B A) step_q]
  have hbase_proj :
      ploParaBase (s := s) f ≫
        cfpFst A (cfpProd L X) = 𝟙 A := by
    unfold ploParaBase
    rw [cfpLift_fst]
  rw [hbase_proj]
  symm
  apply s.elim_uniq (𝟙 A) (cfpSnd B A)
    (cfpFst A L)
  · unfold cfpInsertSnd
    rw [cfpLift_fst]
  · rw [cfpMap_fst, Category.comp_id]
    unfold cfpLiftElemRec
    rw [cfpLift_snd]
    unfold cfpAssocSnd
    rw [cfpLift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- Tail invariant: the `L` component of the enriched
catamorphism carries the input list through
unchanged. -/
private theorem ploParaElim_tail_inv {A X : C}
    (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd B (cfpProd L X)) ⟶ X) :
    @IsPLO.elim C _ h B L s A
        (cfpProd A (cfpProd L X))
        (ploParaBase (s := s) f)
        (ploParaStep (s := s) g) ≫
      cfpSnd A (cfpProd L X) ≫ cfpFst L X =
    cfpSnd A L := by
  have step_q :
      cfpMap (𝟙 B)
        (cfpSnd A (cfpProd L X) ≫
          cfpFst L X) ≫ s.cons =
      ploParaStep (s := s) g ≫
        cfpSnd A (cfpProd L X) ≫
          cfpFst L X := by
    unfold ploParaStep ploParaCarrier
    simp only
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_fst]
    -- Goal: cfpMap ... ≫ s.cons = cfpLift b l ≫ cons
    -- The LHS cfpMap sends (b, (a, (l, x))) to
    -- (b, l), same as cfpLift b l.
    congr 1
    symm
    apply cfpLift_uniq
    · rw [cfpLift_fst, Category.comp_id]
    · rw [cfpLift_snd]
  rw [ploElim_algebra_morphism
      (ploParaBase (s := s) f)
      (ploParaStep (s := s) g)
      (cfpSnd A (cfpProd L X) ≫ cfpFst L X)
      s.cons step_q]
  have hbase_proj :
      ploParaBase (s := s) f ≫
        cfpSnd A (cfpProd L X) ≫
          cfpFst L X =
      cfpTerminalFrom A ≫ s.nil := by
    unfold ploParaBase
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_fst]
  rw [hbase_proj]
  symm
  apply s.elim_uniq
    (cfpTerminalFrom A ≫ s.nil) s.cons
    (cfpSnd A L)
  · unfold cfpInsertSnd
    rw [cfpLift_snd]
  · rw [cfpMap_snd]
    congr 1
    unfold cfpLiftElemRec
    have h_assocSnd_snd :
        cfpAssocSnd A B L ≫ cfpSnd A L =
        cfpSnd A (cfpProd B L) ≫
          cfpSnd B L := by
      unfold cfpAssocSnd
      rw [cfpLift_snd]
    rw [h_assocSnd_snd]
    exact cfpLift_uniq _ _
      (cfpSnd A (cfpProd B L)) rfl rfl

set_option backward.isDefEq.respectTransparency false in
/-- Step-case equation for `ploParaElim`: at
`cons(b, l)` with parameter `a`, the result is `g`
applied to `(a, (b, (l, ploParaElim(a, l))))`. -/
theorem ploParaElim_cons {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd B (cfpProd L X)) ⟶ X) :
    cfpMap (𝟙 A) s.cons ≫
      ploParaElim (s := s) f g =
    cfpLift
        (cfpFst A (cfpProd B L))
        (cfpLift
          (cfpSnd A (cfpProd B L) ≫ cfpFst B L)
          (cfpLift
            (cfpSnd A (cfpProd B L) ≫ cfpSnd B L)
            (cfpAssocSnd A B L ≫
              ploParaElim (s := s) f g))) ≫
      g := by
  -- Expand ploParaElim and apply elim_cons.
  unfold ploParaElim
  rw [← Category.assoc, ← Category.assoc,
    s.elim_cons]
  -- Goal: cfpLiftElemRec E ≫ step ≫ snd_A ≫ snd_L
  --       = RHS ≫ g
  -- where E = elim base step.
  -- Extract what step ≫ snd_A ≫ snd_L does.
  set E := s.elim (ploParaBase (s := s) f)
      (ploParaStep (s := s) g) with hE
  have hstep_proj :
      ploParaStep (s := s) g ≫
        cfpSnd A (cfpProd L X) ≫ cfpSnd L X =
      cfpLift
        (cfpSnd B (ploParaCarrier (L := L) A X) ≫
          cfpFst A (cfpProd L X))
        (cfpLift
          (cfpFst B
            (ploParaCarrier (L := L) A X))
          (cfpLift
            (cfpSnd B
                (ploParaCarrier (L := L) A X) ≫
              cfpSnd A (cfpProd L X) ≫
              cfpFst L X)
            (cfpSnd B
                (ploParaCarrier (L := L) A X) ≫
              cfpSnd A (cfpProd L X) ≫
              cfpSnd L X))) ≫
        g := by
    unfold ploParaStep ploParaCarrier
    simp only
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_snd]
  rw [Category.assoc, Category.assoc, hstep_proj]
  -- Goal: cfpLiftElemRec E ≫ (big cfpLift) ≫ g =
  --       RHS ≫ g.
  rw [← Category.assoc]
  congr 1
  -- Goal: cfpLiftElemRec E ≫ gArg = RHS.
  -- Distribute over the inner cfpLift.
  rw [cfpLift_precomp]
  apply cfpLift_uniq
  · -- First component (a): via param invariant.
    rw [cfpLift_fst]
    unfold cfpLiftElemRec
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc,
      ploParaElim_param_inv f g]
    unfold cfpAssocSnd
    rw [cfpLift_fst]
  · -- Second component: (b, (l, x)).
    rw [cfpLift_snd, cfpLift_precomp]
    apply cfpLift_uniq
    · -- b component: direct from cfpLift projection.
      unfold cfpLiftElemRec
      rw [cfpLift_fst, cfpLift_fst]
    · -- (l, x) pair.
      rw [cfpLift_snd, cfpLift_precomp]
      apply cfpLift_uniq
      · -- l component: via tail invariant.
        rw [cfpLift_fst]
        unfold cfpLiftElemRec
        rw [← Category.assoc, cfpLift_snd,
          Category.assoc,
          ploParaElim_tail_inv f g]
        unfold cfpAssocSnd
        rw [cfpLift_snd]
      · -- x component: ploParaElim.
        rw [cfpLift_snd]
        unfold cfpLiftElemRec
        rw [← Category.assoc, cfpLift_snd,
          Category.assoc, hE]

set_option backward.isDefEq.respectTransparency false in
/-- Uniqueness for `ploParaElim`: any morphism `ψ`
satisfying the base and step equations of the PLO
paramorphism equals `ploParaElim f g`. -/
theorem ploParaElim_uniq {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd B (cfpProd L X)) ⟶ X)
    (ψ : cfpProd A L ⟶ X)
    (hnil : cfpInsertSnd s.nil A ≫ ψ = f)
    (hcons : cfpMap (𝟙 A) s.cons ≫ ψ =
      cfpLift
          (cfpFst A (cfpProd B L))
          (cfpLift
            (cfpSnd A (cfpProd B L) ≫ cfpFst B L)
            (cfpLift
              (cfpSnd A (cfpProd B L) ≫ cfpSnd B L)
              (cfpAssocSnd A B L ≫ ψ))) ≫
        g) :
    ψ = ploParaElim (s := s) f g := by
  -- Lift ψ to the enriched carrier.
  set ψLift : cfpProd A L ⟶
      ploParaCarrier (L := L) A X :=
    cfpLift (cfpFst A L)
      (cfpLift (cfpSnd A L) ψ)
    with hψLift
  -- Show ψLift satisfies the enriched equations.
  have hlift_eq :
      ψLift =
      s.elim (ploParaBase (s := s) f)
        (ploParaStep (s := s) g) := by
    apply s.elim_uniq
      (ploParaBase (s := s) f)
      (ploParaStep (s := s) g)
      ψLift
    · -- Base: cfpInsertSnd s.nil A ≫ ψLift =
      -- ploParaBase f.
      rw [hψLift]
      unfold ploParaBase
      rw [cfpLift_precomp]
      apply cfpLift_uniq
      · rw [cfpLift_fst]
        unfold cfpInsertSnd
        rw [cfpLift_fst]
      · rw [cfpLift_snd, cfpLift_precomp]
        apply cfpLift_uniq
        · rw [cfpLift_fst]
          unfold cfpInsertSnd
          rw [cfpLift_snd]
        · rw [cfpLift_snd, hnil]
    · -- Step: cfpMap (𝟙 A) s.cons ≫ ψLift =
      -- cfpLiftElemRec ψLift ≫ ploParaStep g.
      rw [hψLift]
      set ψ' := cfpLift (cfpFst A L)
        (cfpLift (cfpSnd A L) ψ)
      -- Helper: projections of ψ'.
      have hψ'_fst : ψ' ≫ cfpFst A
          (cfpProd L X) = cfpFst A L :=
        cfpLift_fst _ _
      have hψ'_snd_fst :
          ψ' ≫ cfpSnd A (cfpProd L X) ≫
            cfpFst L X =
          cfpSnd A L := by
        rw [← Category.assoc, cfpLift_snd,
          cfpLift_fst]
      have hψ'_snd_snd :
          ψ' ≫ cfpSnd A (cfpProd L X) ≫
            cfpSnd L X = ψ := by
        rw [← Category.assoc, cfpLift_snd,
          cfpLift_snd]
      -- Use product ext: show both sides
      -- project the same on fst and snd.
      -- LHS: cfpMap (𝟙 A) cons ≫ ψ'.
      -- RHS: cfpLiftElemRec ψ' ≫ ploParaStep g.
      -- First, compute fst of RHS.
      have hRHS_fst :
          cfpLiftElemRec ψ' ≫
            ploParaStep (s := s) g ≫
              cfpFst A (cfpProd L X) =
          cfpFst A (cfpProd B L) := by
        unfold ploParaStep ploParaCarrier
        simp only
        rw [cfpLift_fst]
        unfold cfpLiftElemRec
        rw [← Category.assoc, cfpLift_snd,
          Category.assoc, hψ'_fst]
        unfold cfpAssocSnd
        rw [cfpLift_fst]
      -- Next, compute fst of LHS.
      have hLHS_fst :
          cfpMap (𝟙 A) s.cons ≫ ψ' ≫
            cfpFst A (cfpProd L X) =
          cfpFst A (cfpProd B L) := by
        rw [hψ'_fst,
          cfpMap_fst, Category.comp_id]
      -- Compute snd ≫ fst of RHS (cons(b,l)).
      -- Compute snd ≫ fst of RHS (cons(b,l)).
      have hRHS_snd_fst :
          cfpLiftElemRec ψ' ≫
            ploParaStep (s := s) g ≫
              cfpSnd A (cfpProd L X) ≫
                cfpFst L X =
          cfpSnd A (cfpProd B L) ≫
            s.cons := by
        -- Reduce ploParaStep ≫ snd ≫ fst to
        -- cfpLift b l ≫ cons (from ploParaStep).
        unfold ploParaStep ploParaCarrier
        simp only
        rw [← Category.assoc
          (cfpLift _ _)
          (cfpSnd A (cfpProd L X))
          (cfpFst L X),
          cfpLift_snd, cfpLift_fst,
          ← Category.assoc]
        -- Goal: cfpLiftElemRec ψ' ≫
        --   cfpLift b l ≫ cons
        --   = cfpSnd A (B×L) ≫ cons
        congr 1
        -- Goal: cfpLiftElemRec ψ' ≫ cfpLift b l
        -- = cfpSnd A (B×L)
        -- where b = cfpFst B _ and
        -- l = cfpSnd B _ ≫ snd A _ ≫ fst L X.
        -- cfpLiftElemRec ψ' (a,(b,l)) =
        -- (b, ψ'(a,l)). Composing with
        -- cfpLift fst_B (snd_B ≫ snd_A ≫ fst_L)
        -- gives (b, l). And cfpSnd A (B×L)
        -- also gives (b, l) from (a,(b,l)).
        unfold cfpLiftElemRec
        rw [cfpLift_precomp]
        symm
        apply cfpLift_uniq
          (cfpLift
            (cfpSnd A (cfpProd B L) ≫
              cfpFst B L)
            (cfpAssocSnd A B L ≫ ψ') ≫
            cfpFst B
              (cfpProd A (cfpProd L X)))
          (cfpLift
            (cfpSnd A (cfpProd B L) ≫
              cfpFst B L)
            (cfpAssocSnd A B L ≫ ψ') ≫
            cfpSnd B
              (cfpProd A (cfpProd L X)) ≫
            cfpSnd A (cfpProd L X) ≫
            cfpFst L X)
        · rw [cfpLift_fst]
        · rw [← Category.assoc
            (cfpLift _ _)
            (cfpSnd B
              (cfpProd A (cfpProd L X)))
            (cfpSnd A (cfpProd L X) ≫
              cfpFst L X),
            cfpLift_snd, Category.assoc,
            hψ'_snd_fst]
          unfold cfpAssocSnd
          rw [cfpLift_snd]
      -- Compute snd ≫ fst of LHS.
      have hLHS_snd_fst :
          cfpMap (𝟙 A) s.cons ≫ ψ' ≫
            cfpSnd A (cfpProd L X) ≫
              cfpFst L X =
          cfpSnd A (cfpProd B L) ≫
            s.cons := by
        rw [hψ'_snd_fst, cfpMap_snd]
      -- Compute snd ≫ snd of RHS.
      have hRHS_snd_snd :
          cfpLiftElemRec ψ' ≫
            ploParaStep (s := s) g ≫
              cfpSnd A (cfpProd L X) ≫
                cfpSnd L X =
          cfpMap (𝟙 A) s.cons ≫ ψ := by
        unfold ploParaStep ploParaCarrier
        simp only
        rw [← Category.assoc
          (cfpLift _ _)
          (cfpSnd A (cfpProd L X))
          (cfpSnd L X),
          cfpLift_snd, cfpLift_snd,
          hcons, ← Category.assoc]
        congr 1
        -- cfpLiftElemRec ψ' ≫ gArg =
        -- cfpLift (fst) (cfpLift (snd ≫ fst)
        --   (cfpLift (snd ≫ snd)
        --     (cfpAssocSnd ≫ ψ)))
        unfold cfpLiftElemRec
        rw [cfpLift_precomp]
        apply cfpLift_uniq
        · rw [cfpLift_fst,
            ← Category.assoc
              (cfpLift _ _)
              (cfpSnd B _)
              (cfpFst A _),
            cfpLift_snd, Category.assoc,
            hψ'_fst]
          unfold cfpAssocSnd
          rw [cfpLift_fst]
        · rw [cfpLift_snd, cfpLift_precomp]
          apply cfpLift_uniq
          · rw [cfpLift_fst, cfpLift_fst]
          · rw [cfpLift_snd, cfpLift_precomp]
            apply cfpLift_uniq
            · rw [cfpLift_fst,
                ← Category.assoc
                  (cfpLift _ _)
                  (cfpSnd B _)
                  (cfpSnd A _ ≫ cfpFst L X),
                cfpLift_snd, Category.assoc,
                hψ'_snd_fst]
              unfold cfpAssocSnd
              rw [cfpLift_snd]
            · rw [cfpLift_snd,
                ← Category.assoc
                  (cfpLift _ _)
                  (cfpSnd B _)
                  (cfpSnd A _ ≫ cfpSnd L X),
                cfpLift_snd, Category.assoc,
                hψ'_snd_snd]
      -- Compute snd ≫ snd of LHS.
      have hLHS_snd_snd :
          cfpMap (𝟙 A) s.cons ≫ ψ' ≫
            cfpSnd A (cfpProd L X) ≫
              cfpSnd L X =
          cfpMap (𝟙 A) s.cons ≫ ψ := by
        rw [hψ'_snd_snd]
      -- Now combine both sides.
      have hLHS_snd :
          cfpMap (𝟙 A) s.cons ≫ ψ' ≫
            cfpSnd A (cfpProd L X) =
          cfpLift
            (cfpSnd A (cfpProd B L) ≫ s.cons)
            (cfpMap (𝟙 A) s.cons ≫ ψ) := by
        apply cfpLift_uniq
        · simp only [Category.assoc]
          exact hLHS_snd_fst
        · simp only [Category.assoc]
          exact hLHS_snd_snd
      have hRHS_snd :
          cfpLiftElemRec ψ' ≫
            ploParaStep (s := s) g ≫
              cfpSnd A (cfpProd L X) =
          cfpLift
            (cfpSnd A (cfpProd B L) ≫ s.cons)
            (cfpMap (𝟙 A) s.cons ≫ ψ) := by
        apply cfpLift_uniq
        · simp only [Category.assoc]
          exact hRHS_snd_fst
        · simp only [Category.assoc]
          exact hRHS_snd_snd
      have h_lhs : cfpMap (𝟙 A) s.cons ≫ ψ' =
          cfpLift
            (cfpFst A (cfpProd B L))
            (cfpLift
              (cfpSnd A (cfpProd B L) ≫ s.cons)
              (cfpMap (𝟙 A) s.cons ≫ ψ)) :=
        cfpLift_uniq _ _ _
          (by rw [Category.assoc]; exact hLHS_fst)
          (by rw [Category.assoc]; exact hLHS_snd)
      have h_rhs : cfpLiftElemRec ψ' ≫
          ploParaStep (s := s) g =
          cfpLift
            (cfpFst A (cfpProd B L))
            (cfpLift
              (cfpSnd A (cfpProd B L) ≫ s.cons)
              (cfpMap (𝟙 A) s.cons ≫ ψ)) :=
        cfpLift_uniq _ _ _
          (by rw [Category.assoc]; exact hRHS_fst)
          (by rw [Category.assoc]; exact hRHS_snd)
      rw [h_lhs, h_rhs]
  -- Project out ψ from ψLift.
  have hproj :
      ψLift ≫ cfpSnd A (cfpProd L X) ≫
        cfpSnd L X = ψ := by
    rw [hψLift, ← Category.assoc, cfpLift_snd,
      cfpLift_snd]
  change ψ = ploParaElim (s := s) f g
  unfold ploParaElim
  simp only
  rw [← hlift_eq, hproj]

end PLO_Paramorphism

section PSO_Paramorphism

variable {B L : C} [s : IsPSO C B L]

/-- Carrier for the PSO paramorphism: the triple
`(A, (L, X))`. -/
private def psoParaCarrier (A X : C) : C :=
  cfpProd A (cfpProd L X)

/-- Base morphism for `psoParaElim`: sends `a : A` to
`(a, (nil, f(a)))`. -/
private def psoParaBase {A X : C} (f : A ⟶ X) :
    A ⟶ psoParaCarrier (L := L) A X :=
  cfpLift (𝟙 A)
    (cfpLift (cfpTerminalFrom A ≫ s.nil) f)

/-- Step morphism for `psoParaElim`: given
`((a, (l, x)), b)` from
`(A × (L × X)) × B`, produces
`(a, (snoc(l, b), g(a, l, b, x)))`.
The parameter `a` is carried through unchanged;
the list component is extended by snocing `b` onto
the raw init `l`; the result component is `g`
applied to the parameter, raw init, element, and
recursive result. -/
private def psoParaStep {A X : C}
    (g : cfpProd A
        (cfpProd L (cfpProd B X)) ⟶ X) :
    cfpProd (psoParaCarrier (L := L) A X) B ⟶
      psoParaCarrier (L := L) A X :=
  let X'B := cfpProd
    (psoParaCarrier (L := L) A X) B
  let a : X'B ⟶ A :=
    cfpFst _ B ≫ cfpFst A (cfpProd L X)
  let l : X'B ⟶ L :=
    cfpFst _ B ≫ cfpSnd A (cfpProd L X) ≫
      cfpFst L X
  let x : X'B ⟶ X :=
    cfpFst _ B ≫ cfpSnd A (cfpProd L X) ≫
      cfpSnd L X
  let b : X'B ⟶ B := cfpSnd _ B
  let lb : X'B ⟶ cfpProd L B :=
    cfpLift l b
  let gArg : X'B ⟶
      cfpProd A (cfpProd L (cfpProd B X)) :=
    cfpLift a (cfpLift l (cfpLift b x))
  cfpLift a
    (cfpLift (lb ≫ s.snoc) (gArg ≫ g))

/-- PSO paramorphism: an enhanced fold whose step
function sees the parameter, the raw init, the
element, and the recursive result on the init.
The step `g` has type
`A × (L × (B × X)) ⟶ X`. -/
def psoParaElim {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd L (cfpProd B X)) ⟶ X) :
    cfpProd A L ⟶ X :=
  let base := psoParaBase (s := s) f
  let step := psoParaStep (s := s) g
  @IsPSO.elim C _ h B L s A
    (psoParaCarrier (L := L) A X)
    base step ≫
    cfpSnd A (cfpProd L X) ≫ cfpSnd L X

set_option backward.isDefEq.respectTransparency false in
/-- Base-case equation for `psoParaElim`: at nil,
the result is `f` applied to the parameter. -/
theorem psoParaElim_nil {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd L (cfpProd B X)) ⟶ X) :
    cfpInsertSnd s.nil A ≫
      psoParaElim (s := s) f g = f := by
  unfold psoParaElim
  simp only
  rw [← Category.assoc, ← Category.assoc,
    s.elim_nil]
  unfold psoParaBase
  rw [cfpLift_snd, cfpLift_snd]

/-- Post-composing `cfpLiftRecElem φ` with
`cfpMap q (𝟙 B)` yields `cfpLiftRecElem (φ ≫ q)`. -/
private theorem cfpLiftRecElem_postcomp
    {A L' B' X X' : C}
    (φ : cfpProd A L' ⟶ X)
    (q : X ⟶ X') :
    cfpLiftRecElem φ ≫ cfpMap q (𝟙 B') =
    cfpLiftRecElem (φ ≫ q) := by
  unfold cfpLiftRecElem
  rw [cfpLift_cfpMap]
  congr 1
  · rw [Category.assoc]
  · rw [Category.comp_id]

/-- Algebra morphism lemma for PSO. -/
private theorem psoElim_algebra_morphism
    {A X X' : C}
    (f : A ⟶ X) (g : cfpProd X B ⟶ X)
    (q : X ⟶ X')
    (w : cfpProd X' B ⟶ X')
    (hw : cfpMap q (𝟙 B) ≫ w = g ≫ q) :
    s.elim f g ≫ q = s.elim (f ≫ q) w := by
  exact s.elim_uniq (f ≫ q) w
    (s.elim f g ≫ q)
    (by rw [← Category.assoc, s.elim_nil])
    (by
      rw [← Category.assoc, s.elim_snoc,
        Category.assoc, ← hw,
        ← Category.assoc,
        cfpLiftRecElem_postcomp])

set_option backward.isDefEq.respectTransparency false in
/-- Parameter invariant for PSO. -/
private theorem psoParaElim_param_inv {A X : C}
    (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd L (cfpProd B X)) ⟶ X) :
    @IsPSO.elim C _ h B L s A
        (cfpProd A (cfpProd L X))
        (psoParaBase (s := s) f)
        (psoParaStep (s := s) g) ≫
      cfpFst A (cfpProd L X) =
    cfpFst A L := by
  have step_q :
      cfpMap
          (cfpFst A (cfpProd L X))
          (𝟙 B) ≫
        cfpFst A B =
      psoParaStep (s := s) g ≫
        cfpFst A (cfpProd L X) := by
    rw [cfpMap_fst]
    unfold psoParaStep psoParaCarrier
    simp only
    rw [cfpLift_fst]
  rw [psoElim_algebra_morphism
      (psoParaBase (s := s) f)
      (psoParaStep (s := s) g)
      (cfpFst A (cfpProd L X))
      (cfpFst A B) step_q]
  have hbase_proj :
      psoParaBase (s := s) f ≫
        cfpFst A (cfpProd L X) = 𝟙 A := by
    unfold psoParaBase
    rw [cfpLift_fst]
  rw [hbase_proj]
  symm
  apply s.elim_uniq (𝟙 A) (cfpFst A B)
    (cfpFst A L)
  · unfold cfpInsertSnd
    rw [cfpLift_fst]
  · rw [cfpMap_fst, Category.comp_id]
    unfold cfpLiftRecElem cfpAssocFst
    rw [cfpLift_fst, cfpLift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- Tail invariant for PSO. -/
private theorem psoParaElim_tail_inv {A X : C}
    (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd L (cfpProd B X)) ⟶ X) :
    @IsPSO.elim C _ h B L s A
        (cfpProd A (cfpProd L X))
        (psoParaBase (s := s) f)
        (psoParaStep (s := s) g) ≫
      cfpSnd A (cfpProd L X) ≫ cfpFst L X =
    cfpSnd A L := by
  have step_q :
      cfpMap
        (cfpSnd A (cfpProd L X) ≫
          cfpFst L X)
        (𝟙 B) ≫ s.snoc =
      psoParaStep (s := s) g ≫
        cfpSnd A (cfpProd L X) ≫
          cfpFst L X := by
    unfold psoParaStep psoParaCarrier
    simp only
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_fst]
    congr 1
    apply cfpLift_uniq <;> simp [cfpMap_fst,
      cfpMap_snd, Category.comp_id]
  rw [psoElim_algebra_morphism
      (psoParaBase (s := s) f)
      (psoParaStep (s := s) g)
      (cfpSnd A (cfpProd L X) ≫ cfpFst L X)
      s.snoc step_q]
  have hbase_proj :
      psoParaBase (s := s) f ≫
        cfpSnd A (cfpProd L X) ≫
          cfpFst L X =
      cfpTerminalFrom A ≫ s.nil := by
    unfold psoParaBase
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_fst]
  rw [hbase_proj]
  symm
  apply s.elim_uniq
    (cfpTerminalFrom A ≫ s.nil) s.snoc
    (cfpSnd A L)
  · unfold cfpInsertSnd
    rw [cfpLift_snd]
  · rw [cfpMap_snd]
    congr 1
    unfold cfpLiftRecElem
    have h_assocFst_fst :
        cfpAssocFst A L B ≫ cfpSnd A L =
        cfpSnd A (cfpProd L B) ≫
          cfpFst L B := by
      unfold cfpAssocFst
      rw [cfpLift_snd]
    rw [h_assocFst_fst]
    exact cfpLift_uniq _ _
      (cfpSnd A (cfpProd L B)) rfl rfl

set_option backward.isDefEq.respectTransparency false in
/-- Step-case equation for `psoParaElim`. -/
theorem psoParaElim_snoc {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd L (cfpProd B X)) ⟶ X) :
    cfpMap (𝟙 A) s.snoc ≫
      psoParaElim (s := s) f g =
    cfpLift
        (cfpFst A (cfpProd L B))
        (cfpLift
          (cfpSnd A (cfpProd L B) ≫ cfpFst L B)
          (cfpLift
            (cfpSnd A (cfpProd L B) ≫ cfpSnd L B)
            (cfpAssocFst A L B ≫
              psoParaElim (s := s) f g))) ≫
      g := by
  -- Expand psoParaElim and apply elim_snoc.
  unfold psoParaElim
  rw [← Category.assoc, ← Category.assoc,
    s.elim_snoc]
  set E := s.elim (psoParaBase (s := s) f)
      (psoParaStep (s := s) g) with hE
  have hstep_proj :
      psoParaStep (s := s) g ≫
        cfpSnd A (cfpProd L X) ≫ cfpSnd L X =
      cfpLift
        (cfpFst
          (psoParaCarrier (L := L) A X) B ≫
          cfpFst A (cfpProd L X))
        (cfpLift
          (cfpFst
            (psoParaCarrier (L := L) A X) B ≫
            cfpSnd A (cfpProd L X) ≫
            cfpFst L X)
          (cfpLift
            (cfpSnd
              (psoParaCarrier (L := L) A X) B)
            (cfpFst
              (psoParaCarrier (L := L) A X) B ≫
              cfpSnd A (cfpProd L X) ≫
              cfpSnd L X))) ≫
        g := by
    unfold psoParaStep psoParaCarrier
    simp only
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_snd]
  rw [Category.assoc, Category.assoc, hstep_proj]
  rw [← Category.assoc]
  congr 1
  -- cfpLiftRecElem E ≫ gArg = RHS.
  rw [cfpLift_precomp]
  apply cfpLift_uniq
  · -- a component: via param invariant.
    rw [cfpLift_fst]
    unfold cfpLiftRecElem
    rw [← Category.assoc, cfpLift_fst,
      Category.assoc,
      psoParaElim_param_inv f g]
    unfold cfpAssocFst
    rw [cfpLift_fst]
  · -- (l, (b, x)) component.
    rw [cfpLift_snd, cfpLift_precomp]
    apply cfpLift_uniq
    · -- l component: via tail invariant.
      rw [cfpLift_fst]
      unfold cfpLiftRecElem
      rw [← Category.assoc, cfpLift_fst,
        Category.assoc,
        psoParaElim_tail_inv f g]
      unfold cfpAssocFst
      rw [cfpLift_snd]
    · -- (b, x) pair.
      rw [cfpLift_snd, cfpLift_precomp]
      apply cfpLift_uniq
      · -- b component.
        rw [cfpLift_fst]
        unfold cfpLiftRecElem
        rw [cfpLift_snd]
      · -- x component: psoParaElim.
        rw [cfpLift_snd]
        unfold cfpLiftRecElem
        rw [← Category.assoc, cfpLift_fst,
          Category.assoc, hE]

set_option backward.isDefEq.respectTransparency false in
/-- Uniqueness for `psoParaElim`. -/
theorem psoParaElim_uniq {A X : C} (f : A ⟶ X)
    (g : cfpProd A
        (cfpProd L (cfpProd B X)) ⟶ X)
    (ψ : cfpProd A L ⟶ X)
    (hnil : cfpInsertSnd s.nil A ≫ ψ = f)
    (hsnoc : cfpMap (𝟙 A) s.snoc ≫ ψ =
      cfpLift
          (cfpFst A (cfpProd L B))
          (cfpLift
            (cfpSnd A (cfpProd L B) ≫ cfpFst L B)
            (cfpLift
              (cfpSnd A (cfpProd L B) ≫ cfpSnd L B)
              (cfpAssocFst A L B ≫ ψ))) ≫
        g) :
    ψ = psoParaElim (s := s) f g := by
  set ψLift : cfpProd A L ⟶
      psoParaCarrier (L := L) A X :=
    cfpLift (cfpFst A L)
      (cfpLift (cfpSnd A L) ψ)
    with hψLift
  have hψ'_fst : ψLift ≫ cfpFst A
      (cfpProd L X) = cfpFst A L :=
    cfpLift_fst _ _
  have hψ'_snd_fst :
      ψLift ≫ cfpSnd A (cfpProd L X) ≫
        cfpFst L X =
      cfpSnd A L := by
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_fst]
  have hψ'_snd_snd :
      ψLift ≫ cfpSnd A (cfpProd L X) ≫
        cfpSnd L X = ψ := by
    rw [← Category.assoc, cfpLift_snd,
      cfpLift_snd]
  have hlift_eq :
      ψLift =
      s.elim (psoParaBase (s := s) f)
        (psoParaStep (s := s) g) := by
    apply s.elim_uniq
      (psoParaBase (s := s) f)
      (psoParaStep (s := s) g)
      ψLift
    · rw [hψLift]
      unfold psoParaBase
      rw [cfpLift_precomp]
      apply cfpLift_uniq
      · rw [cfpLift_fst]
        unfold cfpInsertSnd
        rw [cfpLift_fst]
      · rw [cfpLift_snd, cfpLift_precomp]
        apply cfpLift_uniq
        · rw [cfpLift_fst]
          unfold cfpInsertSnd
          rw [cfpLift_snd]
        · rw [cfpLift_snd, hnil]
    · -- Step condition.
      rw [hψLift]
      set ψ' := cfpLift (cfpFst A L)
        (cfpLift (cfpSnd A L) ψ)
      -- Product ext on A × (L × X).
      have hRHS_fst :
          cfpLiftRecElem ψ' ≫
            psoParaStep (s := s) g ≫
              cfpFst A (cfpProd L X) =
          cfpFst A (cfpProd L B) := by
        unfold psoParaStep psoParaCarrier
        simp only
        rw [cfpLift_fst]
        unfold cfpLiftRecElem
        rw [← Category.assoc, cfpLift_fst,
          Category.assoc, hψ'_fst]
        unfold cfpAssocFst
        rw [cfpLift_fst]
      have hLHS_fst :
          cfpMap (𝟙 A) s.snoc ≫ ψ' ≫
            cfpFst A (cfpProd L X) =
          cfpFst A (cfpProd L B) := by
        rw [hψ'_fst,
          cfpMap_fst, Category.comp_id]
      have hRHS_snd_fst :
          cfpLiftRecElem ψ' ≫
            psoParaStep (s := s) g ≫
              cfpSnd A (cfpProd L X) ≫
                cfpFst L X =
          cfpSnd A (cfpProd L B) ≫
            s.snoc := by
        unfold psoParaStep psoParaCarrier
        simp only
        rw [← Category.assoc
          (cfpLift _ _)
          (cfpSnd A (cfpProd L X))
          (cfpFst L X),
          cfpLift_snd, cfpLift_fst,
          ← Category.assoc]
        congr 1
        unfold cfpLiftRecElem
        rw [cfpLift_precomp]
        symm
        apply cfpLift_uniq
        · rw [← Category.assoc
              (cfpLift _ _)
              (cfpFst _ B)
              (cfpSnd A _ ≫ cfpFst L X),
            cfpLift_fst, Category.assoc,
            hψ'_snd_fst]
          unfold cfpAssocFst
          rw [cfpLift_snd]
        · rw [cfpLift_snd]
      have hLHS_snd_fst :
          cfpMap (𝟙 A) s.snoc ≫ ψ' ≫
            cfpSnd A (cfpProd L X) ≫
              cfpFst L X =
          cfpSnd A (cfpProd L B) ≫
            s.snoc := by
        rw [hψ'_snd_fst, cfpMap_snd]
      have hRHS_snd_snd :
          cfpLiftRecElem ψ' ≫
            psoParaStep (s := s) g ≫
              cfpSnd A (cfpProd L X) ≫
                cfpSnd L X =
          cfpMap (𝟙 A) s.snoc ≫ ψ := by
        unfold psoParaStep psoParaCarrier
        simp only
        rw [← Category.assoc
          (cfpLift _ _)
          (cfpSnd A (cfpProd L X))
          (cfpSnd L X),
          cfpLift_snd, cfpLift_snd,
          hsnoc, ← Category.assoc]
        congr 1
        unfold cfpLiftRecElem
        rw [cfpLift_precomp]
        apply cfpLift_uniq
        · rw [cfpLift_fst,
            ← Category.assoc, cfpLift_fst,
            Category.assoc, hψ'_fst]
          unfold cfpAssocFst
          rw [cfpLift_fst]
        · rw [cfpLift_snd, cfpLift_precomp]
          apply cfpLift_uniq
          · rw [cfpLift_fst,
              ← Category.assoc, cfpLift_fst,
              Category.assoc, hψ'_snd_fst]
            unfold cfpAssocFst
            rw [cfpLift_snd]
          · rw [cfpLift_snd, cfpLift_precomp]
            apply cfpLift_uniq
            · rw [cfpLift_fst, cfpLift_snd]
            · rw [cfpLift_snd,
                ← Category.assoc, cfpLift_fst,
                Category.assoc, hψ'_snd_snd]
      have hLHS_snd_snd :
          cfpMap (𝟙 A) s.snoc ≫ ψ' ≫
            cfpSnd A (cfpProd L X) ≫
              cfpSnd L X =
          cfpMap (𝟙 A) s.snoc ≫ ψ := by
        rw [hψ'_snd_snd]
      have hLHS_snd :
          cfpMap (𝟙 A) s.snoc ≫ ψ' ≫
            cfpSnd A (cfpProd L X) =
          cfpLift
            (cfpSnd A (cfpProd L B) ≫ s.snoc)
            (cfpMap (𝟙 A) s.snoc ≫ ψ) := by
        apply cfpLift_uniq
        · simp only [Category.assoc]
          exact hLHS_snd_fst
        · simp only [Category.assoc]
          exact hLHS_snd_snd
      have hRHS_snd :
          cfpLiftRecElem ψ' ≫
            psoParaStep (s := s) g ≫
              cfpSnd A (cfpProd L X) =
          cfpLift
            (cfpSnd A (cfpProd L B) ≫ s.snoc)
            (cfpMap (𝟙 A) s.snoc ≫ ψ) := by
        apply cfpLift_uniq
        · simp only [Category.assoc]
          exact hRHS_snd_fst
        · simp only [Category.assoc]
          exact hRHS_snd_snd
      have h_lhs : cfpMap (𝟙 A) s.snoc ≫ ψ' =
          cfpLift
            (cfpFst A (cfpProd L B))
            (cfpLift
              (cfpSnd A (cfpProd L B) ≫ s.snoc)
              (cfpMap (𝟙 A) s.snoc ≫ ψ)) :=
        cfpLift_uniq _ _ _
          (by rw [Category.assoc]; exact hLHS_fst)
          (by rw [Category.assoc]; exact hLHS_snd)
      have h_rhs : cfpLiftRecElem ψ' ≫
          psoParaStep (s := s) g =
          cfpLift
            (cfpFst A (cfpProd L B))
            (cfpLift
              (cfpSnd A (cfpProd L B) ≫ s.snoc)
              (cfpMap (𝟙 A) s.snoc ≫ ψ)) :=
        cfpLift_uniq _ _ _
          (by rw [Category.assoc]; exact hRHS_fst)
          (by rw [Category.assoc]; exact hRHS_snd)
      rw [h_lhs, h_rhs]
  have hproj :
      ψLift ≫ cfpSnd A (cfpProd L X) ≫
        cfpSnd L X = ψ := by
    rw [hψLift, ← Category.assoc, cfpLift_snd,
      cfpLift_snd]
  change ψ = psoParaElim (s := s) f g
  unfold psoParaElim
  simp only
  rw [← hlift_eq, hproj]

end PSO_Paramorphism

section PSTO_PLTO

variable {T : C}

/-- `cfpSwap A B ≫ cfpFst B A = cfpSnd A B`. -/
theorem cfpSwap_fst (A B : C) :
    cfpSwap A B ≫ cfpFst B A = cfpSnd A B :=
  cfpLift_fst _ _

/-- `cfpSwap A B ≫ cfpSnd B A = cfpFst A B`. -/
theorem cfpSwap_snd (A B : C) :
    cfpSwap A B ≫ cfpSnd B A = cfpFst A B :=
  cfpLift_snd _ _

/-- `cfpSwap A B ≫ cfpSwap B A = 𝟙 (A × B)`. -/
theorem cfpSwap_inv (A B : C) :
    cfpSwap A B ≫ cfpSwap B A =
      𝟙 (cfpProd A B) := by
  have hfst : (cfpSwap A B ≫ cfpSwap B A) ≫
      cfpFst A B = cfpFst A B := by
    rw [Category.assoc, cfpSwap_fst B A,
      cfpSwap_snd A B]
  have hsnd : (cfpSwap A B ≫ cfpSwap B A) ≫
      cfpSnd A B = cfpSnd A B := by
    rw [Category.assoc, cfpSwap_snd B A,
      cfpSwap_fst A B]
  have h1 := cfpLift_uniq
    (cfpFst A B) (cfpSnd A B)
    (𝟙 (cfpProd A B))
    (Category.id_comp _) (Category.id_comp _)
  have h2 := cfpLift_uniq
    (cfpFst A B) (cfpSnd A B)
    (cfpSwap A B ≫ cfpSwap B A)
    hfst hsnd
  rw [h2, ← h1]

/-- `cfpMap (𝟙 A) (cfpSwap B D) ≫ cfpSwap A
(cfpProd D B)` rearranges `A × (B × D)` to
`(D × B) × A`. -/
theorem cfpMap_id_swap_fst (A B D : C) :
    cfpMap (𝟙 A) (cfpSwap B D) ≫
      cfpFst A (cfpProd D B) =
    cfpFst A (cfpProd B D) := by
  rw [cfpMap_fst, Category.comp_id]

theorem cfpMap_id_swap_snd (A B D : C) :
    cfpMap (𝟙 A) (cfpSwap B D) ≫
      cfpSnd A (cfpProd D B) =
    cfpSnd A (cfpProd B D) ≫ cfpSwap B D := by
  exact cfpMap_snd _ _

/-- The `B`-component of swapping: extracting `B`
from `cfpLiftRecElem φ` after input swap and
output swap. -/
private theorem swap_liftRecElem_swap_fst
    {A B D X : C}
    (φ : cfpProd A D ⟶ X) :
    (cfpMap (𝟙 A) (cfpSwap B D) ≫
      cfpLiftRecElem φ ≫ cfpSwap X B) ≫
      cfpFst B X =
    cfpSnd A (cfpProd B D) ≫ cfpFst B D := by
  rw [Category.assoc, Category.assoc,
    cfpSwap_fst X B]
  -- Goal: cfpMap ≫ cfpLiftRecElem φ ≫ cfpSnd X B
  --   = cfpSnd ≫ cfpFst
  have step1 : cfpLiftRecElem φ ≫
      cfpSnd X B =
      cfpSnd A (cfpProd D B) ≫
        cfpSnd D B := by
    unfold cfpLiftRecElem
    exact cfpLift_snd _ _
  rw [step1]
  -- Goal: cfpMap (𝟙 A) (cfpSwap B D) ≫
  --   cfpSnd A (D×B) ≫ cfpSnd D B
  --   = cfpSnd A (B×D) ≫ cfpFst B D
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap B D))
    (cfpSnd A (cfpProd D B))
    (cfpSnd D B),
    cfpMap_id_swap_snd A B D,
    Category.assoc,
    cfpSwap_snd B D]

/-- The `X`-component of swapping. -/
private theorem swap_liftRecElem_swap_snd
    {A B D X : C}
    (φ : cfpProd A D ⟶ X) :
    (cfpMap (𝟙 A) (cfpSwap B D) ≫
      cfpLiftRecElem φ ≫ cfpSwap X B) ≫
      cfpSnd B X =
    cfpAssocSnd A B D ≫ φ := by
  rw [Category.assoc, Category.assoc,
    cfpSwap_snd X B]
  -- Goal: cfpMap ≫ cfpLiftRecElem φ ≫ cfpFst X B
  --   = cfpAssocSnd ≫ φ
  have step1 : cfpLiftRecElem φ ≫
      cfpFst X B =
      cfpAssocFst A D B ≫ φ := by
    unfold cfpLiftRecElem
    exact cfpLift_fst _ _
  -- Goal: cfpMap ≫ (cfpLiftRecElem φ ≫ cfpFst X B)
  --   = cfpAssocSnd ≫ φ
  rw [step1]
  -- Goal: cfpMap (𝟙 A) (cfpSwap B D) ≫
  --   cfpAssocFst A D B ≫ φ
  --   = cfpAssocSnd A B D ≫ φ
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap B D))
    (cfpAssocFst A D B) φ]
  congr 1
  -- cfpMap swap ≫ cfpAssocFst A D B
  --   = cfpAssocSnd A B D
  unfold cfpAssocFst cfpAssocSnd
  rw [cfpLift_precomp]
  congr 1
  · exact cfpMap_id_swap_fst A B D
  · rw [← Category.assoc,
      cfpMap_id_swap_snd A B D,
      Category.assoc, cfpSwap_fst B D]

/-- Swapping the second component, then extracting
`(φ(a, fst), snd)`, then swapping the result, equals
extracting `(snd, φ(a, fst))` with the original
component order reversed. -/
private theorem swap_liftRecElem_swap
    {A B D X : C}
    (φ : cfpProd A D ⟶ X) :
    cfpMap (𝟙 A) (cfpSwap B D) ≫
      cfpLiftRecElem φ ≫ cfpSwap X B =
    cfpLiftElemRec φ := by
  unfold cfpLiftElemRec
  exact cfpLift_uniq
    (cfpSnd A (cfpProd B D) ≫ cfpFst B D)
    (cfpAssocSnd A B D ≫ φ)
    (cfpMap (𝟙 A) (cfpSwap B D) ≫
      cfpLiftRecElem φ ≫ cfpSwap X B)
    (swap_liftRecElem_swap_fst φ)
    (swap_liftRecElem_swap_snd φ)

/-- The `X`-component of swapping for
cfpLiftElemRec, specialized to the case
where the element type equals the list type
(`B = L`). -/
private theorem swap_liftElemRec_swap_fst
    {A L X : C}
    (φ : cfpProd A L ⟶ X) :
    (cfpMap (𝟙 A) (cfpSwap L L) ≫
      cfpLiftElemRec φ ≫ cfpSwap L X) ≫
      cfpFst X L =
    cfpAssocFst A L L ≫ φ := by
  rw [Category.assoc, Category.assoc,
    cfpSwap_fst L X]
  have step1 : cfpLiftElemRec φ ≫
      cfpSnd L X =
      cfpAssocSnd A L L ≫ φ := by
    unfold cfpLiftElemRec
    exact cfpLift_snd _ _
  rw [step1]
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap L L))
    (cfpAssocSnd A L L) φ]
  congr 1
  unfold cfpAssocSnd cfpAssocFst
  rw [cfpLift_precomp]
  congr 1
  · exact cfpMap_id_swap_fst A L L
  · rw [← Category.assoc,
      cfpMap_id_swap_snd A L L,
      Category.assoc, cfpSwap_snd L L]

/-- The `L`-component of swapping for
cfpLiftElemRec, specialized to `B = L`. -/
private theorem swap_liftElemRec_swap_snd
    {A L X : C}
    (φ : cfpProd A L ⟶ X) :
    (cfpMap (𝟙 A) (cfpSwap L L) ≫
      cfpLiftElemRec φ ≫ cfpSwap L X) ≫
      cfpSnd X L =
    cfpSnd A (cfpProd L L) ≫ cfpSnd L L := by
  rw [Category.assoc, Category.assoc,
    cfpSwap_snd L X]
  have step1 : cfpLiftElemRec φ ≫
      cfpFst L X =
      cfpSnd A (cfpProd L L) ≫
        cfpFst L L := by
    unfold cfpLiftElemRec
    exact cfpLift_fst _ _
  rw [step1]
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap L L))
    (cfpSnd A (cfpProd L L))
    (cfpFst L L),
    cfpMap_id_swap_snd A L L,
    Category.assoc,
    cfpSwap_fst L L]

/-- The dual of `swap_liftRecElem_swap`,
specialized to the case `B = L`.  Swapping the
second component, then extracting
`(fst, φ(a, snd))`, then swapping the result,
yields `cfpLiftRecElem`. -/
private theorem swap_liftElemRec_swap
    {A L X : C}
    (φ : cfpProd A L ⟶ X) :
    cfpMap (𝟙 A) (cfpSwap L L) ≫
      cfpLiftElemRec φ ≫ cfpSwap L X =
    cfpLiftRecElem φ := by
  unfold cfpLiftRecElem
  exact cfpLift_uniq
    (cfpAssocFst A L L ≫ φ)
    (cfpSnd A (cfpProd L L) ≫ cfpSnd L L)
    (cfpMap (𝟙 A) (cfpSwap L L) ≫
      cfpLiftElemRec φ ≫ cfpSwap L X)
    (swap_liftElemRec_swap_fst φ)
    (swap_liftElemRec_swap_snd φ)

/-- `cfpMap (𝟙 A) (f ≫ g) = cfpMap (𝟙 A) f ≫
cfpMap (𝟙 A) g`. -/
private theorem cfpMap_id_comp_eq {A B D E : C}
    (f : B ⟶ D) (g : D ⟶ E) :
    cfpMap (𝟙 A) (f ≫ g) =
      cfpMap (𝟙 A) f ≫ cfpMap (𝟙 A) g := by
  conv_lhs => rw [show 𝟙 A = 𝟙 A ≫ 𝟙 A from
    (Category.id_comp (𝟙 A)).symm]
  exact (cfpMap_comp (𝟙 A) f (𝟙 A) g).symm

private theorem pstoToIsPLTO_elim_cons
    (s : IsPSTO C T) {A X : C}
    (f : A ⟶ X) (g : cfpProd T X ⟶ X) :
    cfpMap (𝟙 A) (cfpSwap T T ≫ s.snoc) ≫
      s.elim f (cfpSwap X T ≫ g) =
    cfpLiftElemRec
      (s.elim f (cfpSwap X T ≫ g)) ≫ g := by
  set φ := s.elim f (cfpSwap X T ≫ g)
  set g' := cfpSwap X T ≫ g
  have comm : cfpMap (𝟙 A) (cfpSwap T T) ≫
      cfpLiftRecElem φ ≫ cfpSwap X T ≫ g =
      cfpLiftElemRec φ ≫ g := by
    rw [← Category.assoc (cfpLiftRecElem φ)
      (cfpSwap X T) g,
      ← Category.assoc
      (cfpMap (𝟙 A) (cfpSwap T T))
      (cfpLiftRecElem φ ≫ cfpSwap X T) g,
      swap_liftRecElem_swap φ]
  rw [cfpMap_id_comp_eq (cfpSwap T T) s.snoc,
    Category.assoc,
    s.elim_snoc f g']
  -- Goal: cfpMap swap ≫ cfpLiftRecElem φ ≫ g'
  --   = cfpLiftElemRec φ ≫ g
  exact comm

/-- `cfpMap (𝟙 A) (cfpSwap B D) ≫
cfpMap (𝟙 A) (cfpSwap D B) = 𝟙 _`. -/
private theorem cfpMap_id_swap_inv
    {A B D : C} :
    cfpMap (𝟙 A) (cfpSwap B D) ≫
      cfpMap (𝟙 A) (cfpSwap D B) =
    𝟙 (cfpProd A (cfpProd B D)) := by
  rw [cfpMap_comp, Category.id_comp,
    cfpSwap_inv, cfpMap_id]

/-- Derives the PSO step equation from the
PLO step equation. -/
private theorem pstoToIsPLTO_step_convert
    (s : IsPSTO C T) {A X : C}
    (g : cfpProd T X ⟶ X)
    (φ : cfpProd A T ⟶ X)
    (hsnoc :
      cfpMap (𝟙 A) (cfpSwap T T ≫ s.snoc) ≫ φ =
        cfpLiftElemRec φ ≫ g) :
    cfpMap (𝟙 A) s.snoc ≫ φ =
      cfpLiftRecElem φ ≫ (cfpSwap X T ≫ g) := by
  -- From hsnoc, extract the PSO step.
  -- hsnoc: cfpMap swap ≫ cfpMap snoc ≫ φ
  --   = cfpLiftElemRec φ ≫ g
  -- Precompose with cfpMap swap to cancel.
  have h1 :
      cfpMap (𝟙 A) (cfpSwap T T) ≫
      cfpMap (𝟙 A) (cfpSwap T T ≫ s.snoc) ≫ φ =
      cfpMap (𝟙 A) (cfpSwap T T) ≫
      cfpLiftElemRec φ ≫ g := by
    rw [hsnoc]
  -- LHS simplification:
  -- cfpMap swap ≫ cfpMap (swap ≫ snoc) ≫ φ
  -- = cfpMap swap ≫ cfpMap swap ≫ cfpMap snoc ≫ φ
  -- = (cfpMap swap ≫ cfpMap swap) ≫ cfpMap snoc ≫ φ
  -- = 𝟙 ≫ cfpMap snoc ≫ φ
  -- = cfpMap snoc ≫ φ
  -- Rewrite the composition in h1.
  -- First expand cfpMap (𝟙 A) (swap ≫ snoc) on
  -- the LHS of h1.
  rw [cfpMap_id_comp_eq (cfpSwap T T) s.snoc]
    at h1
  -- h1: cfpMap swap ≫
  --   (cfpMap swap ≫ cfpMap snoc) ≫ φ = ...
  -- Associate the inner composition.
  rw [Category.assoc
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpMap (𝟙 A) s.snoc) φ] at h1
  -- h1: cfpMap swap ≫ cfpMap swap
  --   ≫ cfpMap snoc ≫ φ = ...
  -- Now group the first two.
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpMap (𝟙 A) s.snoc ≫ φ),
    cfpMap_id_swap_inv,
    Category.id_comp] at h1
  -- h1: cfpMap snoc ≫ φ
  --   = cfpMap swap ≫ cfpLiftElemRec φ ≫ g
  -- Now use swap_liftRecElem_swap to rewrite RHS.
  rw [h1]
  -- Goal: cfpMap swap ≫ cfpLiftElemRec φ ≫ g
  --   = cfpLiftRecElem φ ≫ cfpSwap X T ≫ g
  -- Group on both sides to isolate ≫ g.
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpLiftElemRec φ) g,
    ← Category.assoc
    (cfpLiftRecElem φ)
    (cfpSwap X T) g]
  congr 1
  -- Goal: cfpMap swap ≫ cfpLiftElemRec φ
  --   = cfpLiftRecElem φ ≫ cfpSwap X T
  -- From swap_liftRecElem_swap (B := T):
  -- cfpMap swap ≫ cfpLiftRecElem φ ≫ cfpSwap X T
  --   = cfpLiftElemRec φ
  -- So cfpMap swap ≫ cfpLiftElemRec φ
  --   = cfpMap swap ≫ cfpMap swap
  --     ≫ cfpLiftRecElem φ ≫ cfpSwap X T
  --   = cfpLiftRecElem φ ≫ cfpSwap X T
  rw [← swap_liftRecElem_swap (B := T) φ,
    ← Category.assoc
      (cfpMap (𝟙 A) (cfpSwap T T))
      (cfpMap (𝟙 A) (cfpSwap T T))
      (cfpLiftRecElem φ ≫ cfpSwap X T),
    cfpMap_id_swap_inv,
    Category.id_comp]

private theorem pstoToIsPLTO_elim_uniq
    (s : IsPSTO C T) {A X : C}
    (f : A ⟶ X) (g : cfpProd T X ⟶ X)
    (φ : cfpProd A T ⟶ X)
    (hnil :
      cfpInsertSnd s.nil A ≫ φ = f)
    (hsnoc :
      cfpMap (𝟙 A) (cfpSwap T T ≫ s.snoc) ≫
        φ = cfpLiftElemRec φ ≫ g) :
    φ = s.elim f (cfpSwap X T ≫ g) :=
  s.elim_uniq f (cfpSwap X T ≫ g) φ
    hnil
    (pstoToIsPLTO_step_convert s g φ hsnoc)

/-- Given `IsPSTO C T`, derive `IsPLTO C T` by
swapping the argument order of `snoc`. -/
@[reducible]
def pstoToIsPLTO (s : IsPSTO C T) :
    IsPLTO C T where
  nil := s.nil
  cons := cfpSwap T T ≫ s.snoc
  elim := fun {_A X} f g =>
    s.elim f (cfpSwap X T ≫ g)
  elim_nil := fun f g =>
    s.elim_nil f (cfpSwap _ T ≫ g)
  elim_cons := fun f g =>
    pstoToIsPLTO_elim_cons s f g
  elim_uniq := fun {_A _X} f g φ hnil hsnoc =>
    pstoToIsPLTO_elim_uniq s f g φ hnil hsnoc

private theorem pltoToIsPSTO_elim_snoc
    (c : IsPLTO C T) {A X : C}
    (f : A ⟶ X) (g : cfpProd X T ⟶ X) :
    cfpMap (𝟙 A) (cfpSwap T T ≫ c.cons) ≫
      c.elim f (cfpSwap T X ≫ g) =
    cfpLiftRecElem
      (c.elim f (cfpSwap T X ≫ g)) ≫ g := by
  set φ := c.elim f (cfpSwap T X ≫ g)
  set g' := cfpSwap T X ≫ g
  have comm : cfpMap (𝟙 A) (cfpSwap T T) ≫
      cfpLiftElemRec φ ≫ cfpSwap T X ≫ g =
      cfpLiftRecElem φ ≫ g := by
    rw [← Category.assoc (cfpLiftElemRec φ)
      (cfpSwap T X) g,
      ← Category.assoc
      (cfpMap (𝟙 A) (cfpSwap T T))
      (cfpLiftElemRec φ ≫ cfpSwap T X) g,
      swap_liftElemRec_swap φ]
  rw [cfpMap_id_comp_eq (cfpSwap T T) c.cons,
    Category.assoc,
    c.elim_cons f g']
  exact comm

private theorem pltoToIsPSTO_step_convert
    (c : IsPLTO C T) {A X : C}
    (g : cfpProd X T ⟶ X)
    (φ : cfpProd A T ⟶ X)
    (hsnoc :
      cfpMap (𝟙 A)
        (cfpSwap T T ≫ c.cons) ≫ φ =
        cfpLiftRecElem φ ≫ g) :
    cfpMap (𝟙 A) c.cons ≫ φ =
      cfpLiftElemRec φ ≫
        (cfpSwap T X ≫ g) := by
  have h1 :
      cfpMap (𝟙 A) (cfpSwap T T) ≫
      cfpMap (𝟙 A) (cfpSwap T T ≫ c.cons) ≫ φ =
      cfpMap (𝟙 A) (cfpSwap T T) ≫
      cfpLiftRecElem φ ≫ g := by
    rw [hsnoc]
  rw [cfpMap_id_comp_eq (cfpSwap T T) c.cons]
    at h1
  rw [Category.assoc
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpMap (𝟙 A) c.cons) φ] at h1
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpMap (𝟙 A) c.cons ≫ φ),
    cfpMap_id_swap_inv,
    Category.id_comp] at h1
  rw [h1]
  rw [← Category.assoc
    (cfpMap (𝟙 A) (cfpSwap T T))
    (cfpLiftRecElem φ) g,
    ← Category.assoc
    (cfpLiftElemRec φ)
    (cfpSwap T X) g]
  congr 1
  rw [← swap_liftElemRec_swap φ,
    ← Category.assoc
      (cfpMap (𝟙 A) (cfpSwap T T))
      (cfpMap (𝟙 A) (cfpSwap T T))
      (cfpLiftElemRec φ ≫ cfpSwap T X),
    cfpMap_id_swap_inv,
    Category.id_comp]

private theorem pltoToIsPSTO_elim_uniq
    (c : IsPLTO C T) {A X : C}
    (f : A ⟶ X) (g : cfpProd X T ⟶ X)
    (φ : cfpProd A T ⟶ X)
    (hnil :
      cfpInsertSnd c.nil A ≫ φ = f)
    (hsnoc :
      cfpMap (𝟙 A) (cfpSwap T T ≫ c.cons) ≫
        φ = cfpLiftRecElem φ ≫ g) :
    φ = c.elim f (cfpSwap T X ≫ g) :=
  c.elim_uniq f (cfpSwap T X ≫ g) φ
    hnil
    (pltoToIsPSTO_step_convert c g φ hsnoc)

/-- Given `IsPLTO C T`, derive `IsPSTO C T` by
swapping the argument order of `cons`. -/
@[reducible]
def pltoToIsPSTO (c : IsPLTO C T) :
    IsPSTO C T where
  nil := c.nil
  snoc := cfpSwap T T ≫ c.cons
  elim := fun {_A X} f g =>
    c.elim f (cfpSwap T X ≫ g)
  elim_nil := fun f g =>
    c.elim_nil f (cfpSwap _ _ ≫ g)
  elim_snoc := fun f g =>
    pltoToIsPSTO_elim_snoc c f g
  elim_uniq :=
    fun {_A _X} f g φ hnil hsnoc =>
    pltoToIsPSTO_elim_uniq c f g φ hnil hsnoc

/-- Given `HasPSTO C`, derive `HasPLTO C` using the
same underlying object. -/
@[reducible]
def HasPSTO.toHasPLTO
    {C : Type u} [Category.{v} C]
    [h : HasChosenFiniteProducts C]
    [s : HasPSTO C] :
    HasPLTO C where
  T := s.T
  isPLTO := pstoToIsPLTO s.isPSTO

/-- Given `HasPLTO C`, derive `HasPSTO C` using the
same underlying object. -/
@[reducible]
def HasPLTO.toHasPSTO
    {C : Type u} [Category.{v} C]
    [h : HasChosenFiniteProducts C]
    [c : HasPLTO C] :
    HasPSTO C where
  T := c.T
  isPSTO := pltoToIsPSTO c.isPLTO

end PSTO_PLTO

end GebLean
