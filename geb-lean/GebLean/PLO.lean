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
  have key : cfpMap (𝟙 A) (cfpSwap T T) ≫
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
  exact key

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
  have key : cfpMap (𝟙 A) (cfpSwap T T) ≫
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
  exact key

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
