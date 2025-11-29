import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Grothendieck
import GebLean.Utilities.Opposites

/-!
# The family functor and free coproduct completion

Given a category `C`, the family functor `familyFunctor C : Typeᵒᵖ' ⥤ Cat` sends
a type `X` to the product category `∀ x : X, C`, which is the category of
`X`-indexed families of objects from `C`.

For a function `f : X → Y`, the induced functor `familyFunctor.map f` sends an
`X`-indexed family to a `Y`-indexed family by precomposition with `f`.

The Grothendieck construction of this functor yields the free coproduct
completion of `C`, often denoted `Fam(C)` or `PSh_⨿(C)`. Objects are pairs
`(X, F)` where `X` is a type and `F : X → C` is an `X`-indexed family of
objects. Morphisms `(X, F) → (Y, G)` consist of a function `f : Y → X` and
a family of morphisms `F(f(y)) → G(y)` for each `y : Y`.

## References

* https://ncatlab.org/nlab/show/free+coproduct+completion#AsAGrothendieckConstruction
* https://ncatlab.org/nlab/show/family

-/

namespace GebLean

open CategoryTheory

universe u v w v₂ u₂

/-! ## The family category -/

section FamilyCat

variable (C : Type u) [Category.{v} C]

/--
For an index type `X`, the product category of `C` indexed by `X`. Objects are
functions `X → C`, and morphisms are families of morphisms indexed by `X`.
-/
@[simp]
def FamilyCat (X : Type u) : Cat.{max u v, u} :=
  Cat.of (∀ _ : X, C)

end FamilyCat

/-! ## Functoriality in the indexing type -/

section FunctorialityInIndex

variable (C : Type u) [Category.{v} C]

/--
For a function `f : X → Y`, the induced functor between family categories
sends a `Y`-indexed family to an `X`-indexed family by precomposition.
-/
@[simp]
def familyMap {X Y : Type u} (f : X → Y) : FamilyCat C Y ⥤ FamilyCat C X where
  obj F x := F (f x)
  map φ x := φ (f x)

@[simp]
theorem familyMap_id (X : Type u) : familyMap C (𝟙 X) = 𝟙 (FamilyCat C X) := rfl

@[simp]
theorem familyMap_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) :
    familyMap C (g ∘ f) = familyMap C g ⋙ familyMap C f := rfl

/--
The family functor `familyFunctor C : Typeᵒᵖ' ⥤ Cat` sends a type `X` to the
product category of `C` indexed by `X`. This is the functor whose Grothendieck
construction yields the free coproduct completion of `C`.

For a function `f : X → Y` (viewed as a morphism `Y → X` in `Typeᵒᵖ'`), the
induced functor is given by precomposition: an `X`-indexed family is sent to
a `Y`-indexed family by `(F : X → C) ↦ (F ∘ f : Y → C)`.
-/
@[simp]
def familyFunctor : Type uᵒᵖ' ⥤ Cat.{max u v, u} where
  obj X := FamilyCat C X
  map f := familyMap C f
  map_id X := familyMap_id C X
  map_comp _ _ := rfl

end FunctorialityInIndex

/-! ## Functoriality in the category -/

section FunctorialityInCategory

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v₂} D]

/--
A functor `F : C ⥤ D` induces a functor `FamilyCat C X ⥤ FamilyCat D X` by
postcomposition: an `X`-indexed family of objects in `C` is sent to an
`X`-indexed family of objects in `D`.
-/
@[simp]
def familyPostcomp (F : C ⥤ D) (X : Type u) : (∀ _ : X, C) ⥤ (∀ _ : X, D) where
  obj G x := F.obj (G x)
  map φ x := F.map (φ x)
  map_id G := by funext x; simp
  map_comp φ ψ := by funext x; simp

/--
`familyPostcomp` respects the identity functor.
-/
@[simp]
theorem familyPostcomp_id (X : Type u) :
    familyPostcomp (𝟭 C) X = 𝟭 (∀ _ : X, C) := rfl

/--
`familyPostcomp` respects functor composition.
-/
@[simp]
theorem familyPostcomp_comp {E : Type u} [Category E] (F : C ⥤ D) (G : D ⥤ E)
    (X : Type u) : familyPostcomp (F ⋙ G) X = familyPostcomp F X ⋙ familyPostcomp G X := rfl

/--
`familyPostcomp` is natural in the indexing type: for any function `f : X → Y`,
the following square commutes:
```
  FamilyCat C Y --familyPostcomp F Y--> FamilyCat D Y
       |                                     |
  familyMap C f                         familyMap D f
       |                                     |
       v                                     v
  FamilyCat C X --familyPostcomp F X--> FamilyCat D X
```
-/
@[simp]
theorem familyPostcomp_natural (F : C ⥤ D) {X Y : Type u} (f : X → Y) :
    familyMap C f ⋙ familyPostcomp F X = familyPostcomp F Y ⋙ familyMap D f := rfl

end FunctorialityInCategory

/-! ## The family bifunctor -/

section FamilyBifunctor

/--
A functor `F : C ⥤ D` induces a natural transformation from `familyFunctor C`
to `familyFunctor D`, with components given by `familyPostcomp F X`.
-/
@[simp]
def familyNatTrans {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    familyFunctor C ⟶ familyFunctor D where
  app X := familyPostcomp F X
  naturality _ _ f := (familyPostcomp_natural F f).symm

@[simp]
theorem familyNatTrans_id (C : Type u) [Category.{v} C] :
    familyNatTrans (𝟭 C) = 𝟙 (familyFunctor C) := rfl

@[simp]
theorem familyNatTrans_comp {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (F : C ⥤ D) (G : D ⥤ E) :
    familyNatTrans (F ⋙ G) = familyNatTrans F ≫ familyNatTrans G := rfl

/--
The family bifunctor `familyBifunctor : Cat ⥤ (Type uᵒᵖ' ⥤ Cat)` sends a
category `C` to the family functor `familyFunctor C`, and a functor `F : C ⥤ D`
to the natural transformation `familyNatTrans F`.
-/
@[simp]
def familyBifunctor : Cat.{v, u} ⥤ (Type uᵒᵖ' ⥤ Cat.{max u v, u}) where
  obj C := familyFunctor C
  map F := familyNatTrans F
  map_id C := familyNatTrans_id C
  map_comp F G := familyNatTrans_comp F G

end FamilyBifunctor

end GebLean
