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

/-- A PSTO is in particular a PSO with `B = T`. -/
instance (priority := 100) pstoToHasPSO
    {C : Type u} [Category.{v} C]
    [HasChosenFiniteProducts C]
    [p : HasPSTO C] : HasPSO C p.T where
  L := p.T

end GebLean
