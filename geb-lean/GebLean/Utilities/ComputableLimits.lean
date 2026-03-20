import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
-- 81 chars (external mathlib path)
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Computable limits and colimits

`Type`-valued analogues of mathlib's `Prop`-valued
`HasLimit`, `HasLimitsOfShape`, and
`HasFiniteProducts`.  These provide chosen limit cones
as data, enabling computable extraction of projections,
pairings, terminal morphisms, etc.
-/

namespace GebLean

open CategoryTheory

universe v u

/-! ## Computable binary products and terminal

A bundled, computable interface for categories with
chosen finite products.  This replaces the
`Prop`-valued `HasFiniteProducts` for situations
where we need to compute with the product
morphisms. -/

/-- Chosen computable binary product data for
objects `A` and `B`. -/
structure ChosenBinaryProduct
    {C : Type u} [Category.{v} C]
    (A B : C) where
  /-- The product object. -/
  obj : C
  /-- First projection. -/
  fst : obj ⟶ A
  /-- Second projection. -/
  snd : obj ⟶ B
  /-- Pairing (universal morphism). -/
  lift : ∀ {D : C}, (D ⟶ A) → (D ⟶ B) →
    (D ⟶ obj)
  /-- First projection absorbs pairing. -/
  lift_fst : ∀ {D : C}
    (f : D ⟶ A) (g : D ⟶ B),
    lift f g ≫ fst = f
  /-- Second projection absorbs pairing. -/
  lift_snd : ∀ {D : C}
    (f : D ⟶ A) (g : D ⟶ B),
    lift f g ≫ snd = g
  /-- Uniqueness of pairing. -/
  lift_uniq : ∀ {D : C}
    (f : D ⟶ A) (g : D ⟶ B)
    (h : D ⟶ obj),
    h ≫ fst = f → h ≫ snd = g →
    h = lift f g

/-- Chosen computable terminal object data. -/
structure ChosenTerminal
    (C : Type u) [Category.{v} C] where
  /-- The terminal object. -/
  obj : C
  /-- The unique morphism from any object. -/
  from_ : ∀ (A : C), A ⟶ obj
  /-- Uniqueness. -/
  uniq : ∀ {A : C} (f : A ⟶ obj),
    f = from_ A

/-- A category with chosen computable finite
products: a terminal object and binary products
for all pairs. -/
class HasChosenFiniteProducts
    (C : Type u) [Category.{v} C] where
  /-- Chosen terminal object. -/
  terminal : ChosenTerminal C
  /-- Chosen binary product for each pair. -/
  product : ∀ (A B : C),
    ChosenBinaryProduct A B

/-! ## Convenience aliases

These extract from `HasChosenFiniteProducts`,
providing a clean interface for use in universal
property definitions. -/

section Aliases

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]

/-- The terminal object. -/
def cfpTerminal : C :=
  h.terminal.obj

/-- The unique morphism to the terminal object. -/
def cfpTerminalFrom (A : C) :
    A ⟶ cfpTerminal :=
  h.terminal.from_ A

/-- The product object. -/
def cfpProd (A B : C) : C :=
  (h.product A B).obj

/-- First projection. -/
def cfpFst (A B : C) :
    cfpProd A B ⟶ A :=
  (h.product A B).fst

/-- Second projection. -/
def cfpSnd (A B : C) :
    cfpProd A B ⟶ B :=
  (h.product A B).snd

/-- Pairing morphism. -/
def cfpLift {A B D : C}
    (f : D ⟶ A) (g : D ⟶ B) :
    D ⟶ cfpProd A B :=
  (h.product A B).lift f g

/-- Product of morphisms. -/
def cfpMap {A B A' B' : C}
    (f : A ⟶ A') (g : B ⟶ B') :
    cfpProd A B ⟶ cfpProd A' B' :=
  cfpLift (cfpFst A B ≫ f)
    (cfpSnd A B ≫ g)

/-- Insert a constant into the second component:
`⟨id_A, c ∘ !_A⟩ : A ⟶ A × B`. -/
def cfpInsertSnd {B : C}
    (c : cfpTerminal ⟶ B) (A : C) :
    A ⟶ cfpProd A B :=
  cfpLift (𝟙 A) (cfpTerminalFrom A ≫ c)

/-- From `A × (B × D)`, extract `(a, b)`. -/
def cfpAssocFst (A B D : C) :
    cfpProd A (cfpProd B D) ⟶
      cfpProd A B :=
  cfpLift (cfpFst A (cfpProd B D))
    (cfpSnd A (cfpProd B D) ≫
      cfpFst B D)

/-- From `A × (B × D)`, extract `(a, d)`. -/
def cfpAssocSnd (A B D : C) :
    cfpProd A (cfpProd B D) ⟶
      cfpProd A D :=
  cfpLift (cfpFst A (cfpProd B D))
    (cfpSnd A (cfpProd B D) ≫
      cfpSnd B D)

/-- From `A × (B × D)`, pair the results of applying
`f` to `(a, b)` and `g` to `(a, d)`.  Commonly used
for the step case of parameterized binary tree
objects, where `f` and `g` process the two
subtrees. -/
def cfpLiftAssoc {A B D E : C}
    (f : cfpProd A B ⟶ E)
    (g : cfpProd A D ⟶ E) :
    cfpProd A (cfpProd B D) ⟶
      cfpProd E E :=
  cfpLift
    (cfpAssocFst A B D ≫ f)
    (cfpAssocSnd A B D ≫ g)

end Aliases

/-! ## Deriving mathlib's `Prop`-valued classes

Each computable class implies its mathlib counterpart,
confirming that our definitions are correctly
structured. -/

section Derivations

variable {C : Type u} [Category.{v} C]

/-- A `ChosenTerminal` gives `IsTerminal`. -/
def chosenTerminalIsTerminal
    [h : HasChosenFiniteProducts C] :
    Limits.IsTerminal h.terminal.obj :=
  Limits.IsTerminal.ofUniqueHom
    (fun A => h.terminal.from_ A)
    (fun _ f => h.terminal.uniq f)

/-- A `ChosenTerminal` gives `HasTerminal`. -/
instance chosenTerminalToHasTerminal
    [h : HasChosenFiniteProducts C] :
    Limits.HasTerminal C :=
  chosenTerminalIsTerminal.hasTerminal

/-- A `ChosenBinaryProduct` gives `HasLimit` for
the binary pair diagram. -/
instance chosenBinaryProductToHasLimit
    [h : HasChosenFiniteProducts C]
    (A B : C) :
    Limits.HasLimit (Limits.pair A B) :=
  let p := h.product A B
  ⟨⟨Limits.BinaryFan.mk p.fst p.snd,
    Limits.BinaryFan.isLimitMk
      (fun s =>
        p.lift (s.fst) (s.snd))
      (fun s => p.lift_fst s.fst s.snd)
      (fun s => p.lift_snd s.fst s.snd)
      (fun s m hf hs =>
        p.lift_uniq s.fst s.snd m hf hs)⟩⟩

/-- `HasChosenFiniteProducts` gives
`HasBinaryProducts`. -/
instance chosenToHasBinaryProducts
    [h : HasChosenFiniteProducts C] :
    Limits.HasBinaryProducts C :=
  Limits.hasBinaryProducts_of_hasLimit_pair C

/-- `HasChosenFiniteProducts` gives
`HasFiniteProducts`. -/
instance chosenToHasFiniteProducts
    [h : HasChosenFiniteProducts C] :
    Limits.HasFiniteProducts C :=
  hasFiniteProducts_of_has_binary_and_terminal

end Derivations

end GebLean
