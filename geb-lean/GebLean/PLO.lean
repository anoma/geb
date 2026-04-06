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

end GebLean
