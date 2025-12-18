import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Cat
import GebLean.Utilities.Grothendieck
import GebLean.Utilities.Opposites
import GebLean.Utilities.Families

/-!
# Category Judgments via Layered Grothendieck Construction

This module presents category-judgment copresheaves as a chain of contravariant
Grothendieck constructions using `GrothendieckContra'` and `familyFunctor`.

The layering is:

* Layer 0: `Type u` (object types)
* Layer 1: `familyFunctor Type (X × X)` — quiver structures (morphism families)
* Layer 2: functor sending quivers to identity structures
* Layer 3: functor sending identity-quivers to composition structures

Each layer is the `GrothendieckContra'` of a functor from the opposite of
the previous layer into `Cat`.
-/

namespace GebLean

namespace PLang

namespace Groth

open CategoryTheory

/-! ## Layer 1: Quiver Functor via familyFunctor

For each type `X`, a quiver over `X` consists of:
- For each pair `(x, y) : X × X`, a type `Mor(x, y)` of morphisms from x to y

This is exactly `FamilyCat Type (X × X)` = the category of `(X × X)`-indexed
type families. The functor `familyFunctor Type` composes with the squaring
functor to give us quiver structures.
-/

/-- The squaring functor `X ↦ X × X` on types. -/
def sqFunctor.{u} : Type u ⥤ Type u where
  obj X := X × X
  map f := fun p => (f p.1, f p.2)

@[simp]
theorem sqFunctor_map_id.{u} (X : Type u) :
    sqFunctor.map (𝟙 X) = 𝟙 (X × X) := rfl

@[simp]
theorem sqFunctor_map_comp.{u} {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sqFunctor.map (f ≫ g) = sqFunctor.map f ≫ sqFunctor.map g := rfl

/-- The squaring functor on the opposite category. -/
def sqFunctorOp'.{u} : (Type u)ᵒᵖ' ⥤ (Type u)ᵒᵖ' where
  obj X := X × X
  map f := fun p => (f p.1, f p.2)

@[simp]
theorem sqFunctorOp'_map_id.{u} (X : (Type u)ᵒᵖ') :
    sqFunctorOp'.map (𝟙 X) = 𝟙 (X × X) := rfl

@[simp]
theorem sqFunctorOp'_map_comp.{u} {X Y Z : (Type u)ᵒᵖ'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sqFunctorOp'.map (f ≫ g) = sqFunctorOp'.map f ≫ sqFunctorOp'.map g := rfl

/-- The quiver functor: sends `X` to the category of `(X × X)`-indexed type
    families. This is `familyFunctor Type` composed with squaring.

    Objects of `quiverFunctor.obj X` are functions `X × X → Type`, i.e.,
    for each pair of objects, a type of morphisms between them. -/
def quiverFunctor.{u} : (Type u)ᵒᵖ' ⥤ Cat.{u, u + 1} :=
  sqFunctorOp'.{u} ⋙ familyFunctor.{u + 1, u, u} (Type u)

/-! ## Layer 1 Grothendieck Construction

The Grothendieck construction `∫quiverFunctor` has:
- Objects: pairs `(X, M)` where `X : Type` and `M : X × X → Type`
- Morphisms: pairs of a function `f` on bases and a natural transformation
  making the reindexing diagram commute
-/

/-- The first layer: Grothendieck construction of the quiver functor.
    Objects are types equipped with a morphism-family structure. -/
def QuiverGr.{u} : Type (u + 1) :=
  GrothendieckContra'.{u + 1, u, u + 1, u}
    (C := Type u)
    quiverFunctor.{u}

/-- Category instance on QuiverGr from the Grothendieck construction. -/
instance QuiverGr.categoryInst.{u} : Category.{u, u + 1} QuiverGr.{u} :=
  GrothendieckContra'.GrothendieckContraInst'.{u + 1, u, u + 1, u}
    (F' := quiverFunctor.{u})

/-- Extract the object type from a quiver. -/
def QuiverGr.objType.{u} (Q : QuiverGr.{u}) : Type u := Q.base

/-- Extract the morphism family from a quiver: for each `(x, y) : X × X`,
    gives the type of morphisms from `x` to `y`. -/
def QuiverGr.morFamily.{u} (Q : QuiverGr.{u}) : Q.objType × Q.objType → Type u :=
  Q.fiber

/-- The type of morphisms from `x` to `y` in quiver `Q`. -/
def QuiverGr.Hom.{u} (Q : QuiverGr.{u}) (x y : Q.objType) : Type u :=
  Q.morFamily (x, y)

/-! ## Layer 2: Identity-Quiver Structure

For each quiver `Q = (X, M : X × X → Type)`, an identity structure assigns
to each object `x : X` a morphism in `M(x, x)`.

The type of such sections is `∀ x : X, M(x, x)`. We define `IdGr` directly
as a sigma type over `QuiverGr`, representing the Grothendieck construction
of the "identity structure" functor.
-/

/-- For a quiver Q, the type of identity structures: a choice of identity
    morphism for each object. -/
def IdStruct.{u} (Q : QuiverGr.{u}) : Type u :=
  ∀ x : Q.objType, Q.Hom x x

/-- The second layer: quivers equipped with identity morphisms.
    This corresponds to the Grothendieck construction of the functor sending
    each quiver to its type of identity structures. -/
structure IdGr.{u} where
  /-- The underlying quiver structure -/
  quiver : QuiverGr.{u}
  /-- The identity morphism assignment -/
  idMor : IdStruct quiver

/-- Extract the object type from an identity-quiver. -/
def IdGr.objType.{u} (I : IdGr.{u}) : Type u := I.quiver.objType

/-- Extract the morphism family from an identity-quiver. -/
def IdGr.morFamily.{u} (I : IdGr.{u}) : I.objType × I.objType → Type u :=
  I.quiver.morFamily

/-- The type of morphisms from `x` to `y` in identity-quiver `I`. -/
def IdGr.Hom.{u} (I : IdGr.{u}) (x y : I.objType) : Type u :=
  I.morFamily (x, y)

/-- Get the identity morphism for an object. -/
def IdGr.id.{u} (I : IdGr.{u}) (x : I.objType) : I.Hom x x :=
  I.idMor x

/-! ## Layer 3: Composition Structure

For each identity-quiver `I = (X, M, id)`, a composition structure assigns
to each composable pair `(f : M(x,y), g : M(y,z))` a composite `g ∘ f : M(x,z)`.
-/

/-- For an identity-quiver I, the type of composition structures. -/
def CompStruct.{u} (I : IdGr.{u}) : Type u :=
  ∀ (x y z : I.objType), I.Hom x y → I.Hom y z → I.Hom x z

/-- The third layer: identity-quivers equipped with composition.
    This corresponds to the Grothendieck construction of the functor sending
    each identity-quiver to its type of composition structures. -/
structure CompGr.{u} where
  /-- The underlying identity-quiver structure -/
  idQuiver : IdGr.{u}
  /-- The composition operation -/
  compOp : CompStruct idQuiver

/-- Extract the underlying quiver from a composition structure. -/
def CompGr.quiver.{u} (C : CompGr.{u}) : QuiverGr.{u} := C.idQuiver.quiver

/-- Extract the object type from a composition structure. -/
def CompGr.objType.{u} (C : CompGr.{u}) : Type u := C.idQuiver.objType

/-- Extract the morphism family from a composition structure. -/
def CompGr.morFamily.{u} (C : CompGr.{u}) :
    C.objType × C.objType → Type u :=
  C.idQuiver.morFamily

/-- The type of morphisms from `x` to `y` in composition structure `C`. -/
def CompGr.Hom.{u} (C : CompGr.{u}) (x y : C.objType) : Type u :=
  C.morFamily (x, y)

/-- Extract the identity morphism for an object. -/
def CompGr.idMor.{u} (C : CompGr.{u}) (x : C.objType) : C.Hom x x :=
  C.idQuiver.id x

/-- Compose two morphisms. -/
def CompGr.comp.{u} (C : CompGr.{u}) {x y z : C.objType}
    (f : C.Hom x y) (g : C.Hom y z) : C.Hom x z :=
  C.compOp x y z f g

/-! ## Summary

We have constructed a three-layer structure for category-judgment data:

1. `quiverFunctor : (Type u)ᵒᵖ' ⥤ Cat` — strict functor via familyFunctor
2. `QuiverGr = GrothendieckContra' quiverFunctor` — quiver structures with
   full Grothendieck category structure
3. `IdGr` — quivers with identity morphisms (as a structure over QuiverGr)
4. `CompGr` — identity-quivers with composition (as a structure over IdGr)

The first layer uses the full `GrothendieckContra'` construction with
`familyFunctor`, which has strict functor laws (by `rfl`). Layers 2 and 3
are defined as structures, representing the fiber data over the previous layer.

The `CompGr` type captures full category-judgment copresheaf data: object types,
morphism families, identity morphisms, and composition operations.
-/

end Groth

end PLang

end GebLean
