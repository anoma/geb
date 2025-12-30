import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import GebLean.Utilities.Grothendieck
import GebLean.Utilities.Opposites
import GebLean.Utilities.Families

/-!
# Category Judgments via Layered Grothendieck Construction

This module presents category-judgment copresheaves as a chain of contravariant
Grothendieck constructions using `GrothendieckContra'` and `familyFunctor`.

The layering with independent universe parameters:

* Layer 0: `Type uObj` (object types)
* Layer 1: `GrothendieckContra' quiverFunctor` — quiver structures with morphism
  families in `Type uMor`
* Layer 2: `GrothendieckContra' idFunctor` — identity structures
* Layer 3: `GrothendieckContra' compFunctor` — composition structures

Each layer is the `GrothendieckContra'` of a functor from the opposite of
the previous layer into `Cat`. The universe parameters `uObj` and `uMor` remain
independent throughout, analogous to `Cat.{vMor, uObj}`.
-/

namespace GebLean

namespace PLang

namespace Groth

open CategoryTheory

/-! ## Layer 1: Quiver Functor via familyFunctor

For each type `X : Type uObj`, a quiver over `X` consists of:
- For each pair `(x, y) : X × X`, a type `Mor(x, y) : Type uMor` of morphisms

This is `FamilyCat (Type uMor) (X × X)` = the category of `(X × X)`-indexed
type families. The functor `familyFunctor (Type uMor)` composes with the
squaring functor to give us quiver structures.
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

/-- The quiver functor with independent universes: sends `X : Type uObj` to
    the category of `(X × X)`-indexed type families in `Type uMor`.

    Objects of `quiverFunctor.obj X` are functions `X × X → Type uMor`, i.e.,
    for each pair of objects, a type of morphisms between them. -/
def quiverFunctor.{uObj, uMor} : (Type uObj)ᵒᵖ' ⥤ Cat.{max uObj uMor, max uObj (uMor + 1)} :=
  sqFunctorOp'.{uObj} ⋙ familyFunctor.{uMor + 1, uMor, uObj} (Type uMor)

/-! ## Layer 1 Grothendieck Construction -/

/-- The first layer: Grothendieck construction of the quiver functor.
    Objects are pairs `(X : Type uObj, M : X × X → Type uMor)`. -/
abbrev QuiverGr.{uObj, uMor} :=
  GrothendieckContra'.{uObj + 1, uObj, max uObj (uMor + 1), max uObj uMor}
    (C := Type uObj)
    quiverFunctor.{uObj, uMor}

/-! ### Layer 1 Accessors -/

/-- Extract the object type from a quiver. -/
def QuiverGr.objType.{uObj, uMor} (Q : QuiverGr.{uObj, uMor}) : Type uObj := Q.base

/-- Extract the morphism family from a quiver: for each `(x, y) : X × X`,
    gives the type of morphisms from `x` to `y`. -/
def QuiverGr.morFamily.{uObj, uMor} (Q : QuiverGr.{uObj, uMor}) :
    Q.objType × Q.objType → Type uMor :=
  Q.fiber

/-- The type of morphisms from `x` to `y` in quiver `Q`. -/
def QuiverGr.Hom.{uObj, uMor} (Q : QuiverGr.{uObj, uMor}) (x y : Q.objType) : Type uMor :=
  Q.morFamily (x, y)

/-! ### Layer 1 Constructor -/

/-- Construct a quiver from an object type and morphism family. -/
def QuiverGr.mk.{uObj, uMor} (X : Type uObj) (M : X × X → Type uMor) :
    QuiverGr.{uObj, uMor} :=
  ⟨X, M⟩

@[simp]
theorem QuiverGr.mk_objType.{uObj, uMor} (X : Type uObj) (M : X × X → Type uMor) :
    (QuiverGr.mk X M).objType = X := rfl

@[simp]
theorem QuiverGr.mk_morFamily.{uObj, uMor} (X : Type uObj) (M : X × X → Type uMor) :
    (QuiverGr.mk X M).morFamily = M := rfl

/-- Reconstruction: a quiver equals its components. -/
theorem QuiverGr.eta.{uObj, uMor} (Q : QuiverGr.{uObj, uMor}) :
    QuiverGr.mk Q.objType Q.morFamily = Q := rfl

/-! ## Layer 2: Identity-Quiver Structure via Grothendieck Construction

For layer 2, we bundle quiver structure and identity structure together in the
fiber over each type. Given `X : Type uObj`, the fiber `IdQuiverBundle X` has:
- Objects: pairs `(Hom : X × X → Type uMor, id : ∀ x, Hom(x, x))`
- Morphisms: natural transformations that preserve identity

This allows proper pullback along functions: for `f : X → Y`, a bundle
`(Hom_Y, id_Y)` pulls back to `(f*Hom_Y, f*id_Y)` where:
- `(f*Hom_Y)(x, y) = Hom_Y(f x, f y)`
- `(f*id_Y)(x) = id_Y(f x)`
-/

/-- Bundle of quiver structure with identity: pairs of morphism family and
    identity assignment. -/
structure IdQuiverBundle.{uObj, uMor} (X : Type uObj) where
  /-- The morphism family: for each pair `(x, y)`, a type of morphisms -/
  morFamily : X × X → Type uMor
  /-- The identity assignment: for each `x`, an identity morphism -/
  idMor : ∀ x : X, morFamily (x, x)

/-- Morphisms between identity-quiver bundles over the same base type:
    natural transformations that preserve identity. -/
structure IdQuiverBundle.Hom.{uObj, uMor} {X : Type uObj}
    (B₁ B₂ : IdQuiverBundle.{uObj, uMor} X) where
  /-- The natural transformation on morphism families -/
  transform : ∀ p : X × X, B₁.morFamily p → B₂.morFamily p
  /-- The transformation preserves identity morphisms -/
  preserves_id : ∀ x : X, transform (x, x) (B₁.idMor x) = B₂.idMor x

/-- Identity morphism for IdQuiverBundle. -/
def IdQuiverBundle.Hom.identity.{uObj, uMor} {X : Type uObj}
    (B : IdQuiverBundle.{uObj, uMor} X) : IdQuiverBundle.Hom B B where
  transform := fun _ m => m
  preserves_id := fun _ => rfl

/-- Composition of IdQuiverBundle morphisms. -/
def IdQuiverBundle.Hom.comp.{uObj, uMor} {X : Type uObj}
    {B₁ B₂ B₃ : IdQuiverBundle.{uObj, uMor} X}
    (f : IdQuiverBundle.Hom B₁ B₂) (g : IdQuiverBundle.Hom B₂ B₃) :
    IdQuiverBundle.Hom B₁ B₃ where
  transform := fun p m => g.transform p (f.transform p m)
  preserves_id := fun x => by rw [f.preserves_id, g.preserves_id]

/-- Extensionality for IdQuiverBundle.Hom. -/
@[ext]
theorem IdQuiverBundle.Hom.ext.{uObj, uMor} {X : Type uObj}
    {B₁ B₂ : IdQuiverBundle.{uObj, uMor} X}
    {f g : IdQuiverBundle.Hom B₁ B₂}
    (h : ∀ p m, f.transform p m = g.transform p m) : f = g := by
  cases f; cases g
  congr 1
  funext p m
  exact h p m

/-- Category instance for IdQuiverBundle over a fixed type. -/
instance IdQuiverBundle.instCategory.{uObj, uMor} (X : Type uObj) :
    Category.{max uObj uMor} (IdQuiverBundle.{uObj, uMor} X) where
  Hom := IdQuiverBundle.Hom
  id := IdQuiverBundle.Hom.identity
  comp := IdQuiverBundle.Hom.comp
  id_comp := fun f => by
    ext p m
    rfl
  comp_id := fun f => by
    ext p m
    rfl
  assoc := fun f g h => by
    ext p m
    rfl

/-- Pullback of an IdQuiverBundle along a function. -/
def IdQuiverBundle.pullback.{uObj, uMor} {X Y : Type uObj}
    (f : X → Y) (B : IdQuiverBundle.{uObj, uMor} Y) : IdQuiverBundle.{uObj, uMor} X where
  morFamily := fun p => B.morFamily (f p.1, f p.2)
  idMor := fun x => B.idMor (f x)

/-- Pullback of a morphism of IdQuiverBundles. -/
def IdQuiverBundle.Hom.pullback.{uObj, uMor} {X Y : Type uObj}
    (f : X → Y) {B₁ B₂ : IdQuiverBundle.{uObj, uMor} Y}
    (φ : IdQuiverBundle.Hom B₁ B₂) :
    IdQuiverBundle.Hom (IdQuiverBundle.pullback f B₁)
      (IdQuiverBundle.pullback f B₂) where
  transform := fun p => φ.transform (f p.1, f p.2)
  preserves_id := fun x => φ.preserves_id (f x)

/-- Pullback functor for IdQuiverBundle categories. -/
def IdQuiverBundle.pullbackFunctor.{uObj, uMor} {X Y : Type uObj} (f : X → Y) :
    IdQuiverBundle.{uObj, uMor} Y ⥤ IdQuiverBundle.{uObj, uMor} X where
  obj := IdQuiverBundle.pullback f
  map := IdQuiverBundle.Hom.pullback f
  map_id := fun B => by
    apply IdQuiverBundle.Hom.ext
    intro p m
    rfl
  map_comp := fun φ ψ => by
    apply IdQuiverBundle.Hom.ext
    intro p m
    rfl

/-- Pullback along identity equals identity on objects. -/
@[simp]
theorem IdQuiverBundle.pullback_id.{uObj, uMor} {X : Type uObj}
    (B : IdQuiverBundle.{uObj, uMor} X) :
    IdQuiverBundle.pullback (fun x => x) B = B := rfl

/-- Pullback along identity equals identity on morphisms. -/
@[simp]
theorem IdQuiverBundle.Hom.pullback_id.{uObj, uMor} {X : Type uObj}
    {B₁ B₂ : IdQuiverBundle.{uObj, uMor} X} (φ : IdQuiverBundle.Hom B₁ B₂) :
    IdQuiverBundle.Hom.pullback (fun x => x) φ = φ := rfl

/-- Pullback functor along identity is identity. -/
@[simp]
theorem IdQuiverBundle.pullbackFunctor_id.{uObj, uMor} (X : Type uObj) :
    IdQuiverBundle.pullbackFunctor (𝟙 X) =
      𝟙 (Cat.of (IdQuiverBundle.{uObj, uMor} X)) := rfl

/-- Pullback along composition equals composition of pullbacks on objects. -/
@[simp]
theorem IdQuiverBundle.pullback_comp.{uObj, uMor} {X Y Z : Type uObj}
    (f : X → Y) (g : Y → Z) (B : IdQuiverBundle.{uObj, uMor} Z) :
    IdQuiverBundle.pullback f (IdQuiverBundle.pullback g B) =
      IdQuiverBundle.pullback (fun x => g (f x)) B := rfl

/-- Pullback functor along composition equals composition of pullback functors.
    In `(Type uObj)ᵒᵖ'`, morphisms are reversed: `f : X ⟶ Y` means `f : Y → X`.
    Composition `f ≫ g : X ⟶ Z` means `g ∘ f : Z → X`. -/
@[simp]
theorem IdQuiverBundle.pullbackFunctor_comp.{uObj, uMor}
    {X Y Z : (Type uObj)ᵒᵖ'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IdQuiverBundle.pullbackFunctor.{uObj, uMor} f ⋙
      IdQuiverBundle.pullbackFunctor g =
      IdQuiverBundle.pullbackFunctor (f ≫ g) := rfl

/-- The identity-quiver functor: sends types to categories of identity-quiver
    bundles, with pullback as the functorial action. -/
def idQuiverFunctor.{uObj, uMor} :
    (Type uObj)ᵒᵖ' ⥤ Cat.{max uObj uMor, max uObj (uMor + 1)} where
  obj X := Cat.of (IdQuiverBundle.{uObj, uMor} X)
  map f := IdQuiverBundle.pullbackFunctor f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ## Layer 2 Grothendieck Construction -/

/-- The second layer: Grothendieck construction of the identity-quiver functor.
    Objects are pairs `(X : Type uObj, B : IdQuiverBundle X)`. -/
abbrev IdGr.{uObj, uMor} :=
  GrothendieckContra'.{uObj + 1, uObj, max uObj (uMor + 1), max uObj uMor}
    (C := Type uObj)
    idQuiverFunctor.{uObj, uMor}

/-- For a quiver Q, the type of identity structures. -/
def IdStruct.{uObj, uMor} (Q : QuiverGr.{uObj, uMor}) : Type (max uObj uMor) :=
  ∀ x : Q.objType, Q.Hom x x

/-! ### Layer 2 Accessors -/

/-- Extract the object type from an identity-quiver. -/
def IdGr.objType.{uObj, uMor} (I : IdGr.{uObj, uMor}) : Type uObj := I.base

/-- Extract the morphism family from an identity-quiver. -/
def IdGr.morFamily.{uObj, uMor} (I : IdGr.{uObj, uMor}) :
    I.objType × I.objType → Type uMor :=
  I.fiber.morFamily

/-- The type of morphisms from `x` to `y` in identity-quiver `I`. -/
def IdGr.Hom.{uObj, uMor} (I : IdGr.{uObj, uMor}) (x y : I.objType) : Type uMor :=
  I.morFamily (x, y)

/-- Get the identity morphism for an object. -/
def IdGr.id.{uObj, uMor} (I : IdGr.{uObj, uMor}) (x : I.objType) : I.Hom x x :=
  I.fiber.idMor x

/-! ### Layer 2 Constructors -/

/-- Construct an IdGr from a type and an IdQuiverBundle. -/
def IdGr.mk.{uObj, uMor} (X : Type uObj) (B : IdQuiverBundle.{uObj, uMor} X) :
    IdGr.{uObj, uMor} :=
  ⟨X, B⟩

/-- Construct an IdGr from raw data. -/
def IdGr.ofData.{uObj, uMor}
    (X : Type uObj)
    (M : X × X → Type uMor)
    (idMorFn : ∀ x : X, M (x, x)) :
    IdGr.{uObj, uMor} :=
  ⟨X, ⟨M, idMorFn⟩⟩

@[simp]
theorem IdGr.mk_objType.{uObj, uMor} (X : Type uObj) (B : IdQuiverBundle.{uObj, uMor} X) :
    (IdGr.mk X B).objType = X := rfl

@[simp]
theorem IdGr.mk_fiber.{uObj, uMor} (X : Type uObj) (B : IdQuiverBundle.{uObj, uMor} X) :
    (IdGr.mk X B).fiber = B := rfl

@[simp]
theorem IdGr.ofData_objType.{uObj, uMor}
    (X : Type uObj) (M : X × X → Type uMor) (idMorFn : ∀ x : X, M (x, x)) :
    (IdGr.ofData X M idMorFn).objType = X := rfl

@[simp]
theorem IdGr.ofData_morFamily.{uObj, uMor}
    (X : Type uObj) (M : X × X → Type uMor) (idMorFn : ∀ x : X, M (x, x)) :
    (IdGr.ofData X M idMorFn).morFamily = M := rfl

@[simp]
theorem IdGr.ofData_id.{uObj, uMor}
    (X : Type uObj) (M : X × X → Type uMor) (idMorFn : ∀ x : X, M (x, x))
    (x : X) :
    (IdGr.ofData X M idMorFn).id x = idMorFn x := rfl

/-- Reconstruction: an identity-quiver equals its components. -/
theorem IdGr.eta.{uObj, uMor} (I : IdGr.{uObj, uMor}) :
    IdGr.mk I.objType I.fiber = I := rfl

/-- Extract the underlying QuiverGr from an IdGr. -/
def IdGr.toQuiverGr.{uObj, uMor} (I : IdGr.{uObj, uMor}) : QuiverGr.{uObj, uMor} :=
  QuiverGr.mk I.objType I.morFamily

/-! ## Layer 3: Composition Structure via Grothendieck Construction

For layer 3, we bundle quiver structure, identity structure, and composition
together in the fiber over each type. Given `X : Type uObj`, the fiber
`CompBundle X` has:
- Objects: triples `(Hom, id, comp)` with composition operation
- Morphisms: natural transformations preserving identity and composition

Pullback along `f : X → Y` works for all three components.
-/

/-- Bundle of quiver structure with identity and composition. -/
structure CompBundle.{uObj, uMor} (X : Type uObj) where
  /-- The morphism family: for each pair `(x, y)`, a type of morphisms -/
  morFamily : X × X → Type uMor
  /-- The identity assignment: for each `x`, an identity morphism -/
  idMor : ∀ x : X, morFamily (x, x)
  /-- The composition operation -/
  compOp : ∀ (x y z : X), morFamily (x, y) → morFamily (y, z) → morFamily (x, z)

/-- Morphisms between composition bundles over the same base type:
    natural transformations preserving identity and composition. -/
structure CompBundle.Hom.{uObj, uMor} {X : Type uObj}
    (B₁ B₂ : CompBundle.{uObj, uMor} X) where
  /-- The natural transformation on morphism families -/
  transform : ∀ p : X × X, B₁.morFamily p → B₂.morFamily p
  /-- The transformation preserves identity morphisms -/
  preserves_id : ∀ x : X, transform (x, x) (B₁.idMor x) = B₂.idMor x
  /-- The transformation preserves composition -/
  preserves_comp : ∀ (x y z : X) (f : B₁.morFamily (x, y)) (g : B₁.morFamily (y, z)),
    transform (x, z) (B₁.compOp x y z f g) =
      B₂.compOp x y z (transform (x, y) f) (transform (y, z) g)

/-- Identity morphism for CompBundle. -/
def CompBundle.Hom.identity.{uObj, uMor} {X : Type uObj}
    (B : CompBundle.{uObj, uMor} X) : CompBundle.Hom B B where
  transform := fun _ m => m
  preserves_id := fun _ => rfl
  preserves_comp := fun _ _ _ _ _ => rfl

/-- Composition of CompBundle morphisms. -/
def CompBundle.Hom.comp.{uObj, uMor} {X : Type uObj}
    {B₁ B₂ B₃ : CompBundle.{uObj, uMor} X}
    (f : CompBundle.Hom B₁ B₂) (g : CompBundle.Hom B₂ B₃) :
    CompBundle.Hom B₁ B₃ where
  transform := fun p m => g.transform p (f.transform p m)
  preserves_id := fun x => by rw [f.preserves_id, g.preserves_id]
  preserves_comp := fun x y z fm gm => by rw [f.preserves_comp, g.preserves_comp]

/-- Extensionality for CompBundle.Hom. -/
@[ext]
theorem CompBundle.Hom.ext.{uObj, uMor} {X : Type uObj}
    {B₁ B₂ : CompBundle.{uObj, uMor} X}
    {f g : CompBundle.Hom B₁ B₂}
    (h : ∀ p m, f.transform p m = g.transform p m) : f = g := by
  cases f; cases g
  congr 1
  funext p m
  exact h p m

/-- Category instance for CompBundle over a fixed type. -/
instance CompBundle.instCategory.{uObj, uMor} (X : Type uObj) :
    Category.{max uObj uMor} (CompBundle.{uObj, uMor} X) where
  Hom := CompBundle.Hom
  id := CompBundle.Hom.identity
  comp := CompBundle.Hom.comp
  id_comp := fun f => by
    ext p m
    rfl
  comp_id := fun f => by
    ext p m
    rfl
  assoc := fun f g h => by
    ext p m
    rfl

/-- Pullback of a CompBundle along a function. -/
def CompBundle.pullback.{uObj, uMor} {X Y : Type uObj}
    (f : X → Y) (B : CompBundle.{uObj, uMor} Y) : CompBundle.{uObj, uMor} X where
  morFamily := fun p => B.morFamily (f p.1, f p.2)
  idMor := fun x => B.idMor (f x)
  compOp := fun x y z fm gm => B.compOp (f x) (f y) (f z) fm gm

/-- Pullback of a morphism of CompBundles. -/
def CompBundle.Hom.pullback.{uObj, uMor} {X Y : Type uObj}
    (f : X → Y) {B₁ B₂ : CompBundle.{uObj, uMor} Y}
    (φ : CompBundle.Hom B₁ B₂) :
    CompBundle.Hom (CompBundle.pullback f B₁) (CompBundle.pullback f B₂) where
  transform := fun p => φ.transform (f p.1, f p.2)
  preserves_id := fun x => φ.preserves_id (f x)
  preserves_comp := fun x y z fm gm => φ.preserves_comp (f x) (f y) (f z) fm gm

/-- Pullback functor for CompBundle categories. -/
def CompBundle.pullbackFunctor.{uObj, uMor} {X Y : Type uObj} (f : X → Y) :
    CompBundle.{uObj, uMor} Y ⥤ CompBundle.{uObj, uMor} X where
  obj := CompBundle.pullback f
  map := CompBundle.Hom.pullback f
  map_id := fun B => by
    apply CompBundle.Hom.ext
    intro p m
    rfl
  map_comp := fun φ ψ => by
    apply CompBundle.Hom.ext
    intro p m
    rfl

/-- Pullback along identity equals identity on objects. -/
@[simp]
theorem CompBundle.pullback_id.{uObj, uMor} {X : Type uObj}
    (B : CompBundle.{uObj, uMor} X) :
    CompBundle.pullback (fun x => x) B = B := rfl

/-- Pullback along identity equals identity on morphisms. -/
@[simp]
theorem CompBundle.Hom.pullback_id.{uObj, uMor} {X : Type uObj}
    {B₁ B₂ : CompBundle.{uObj, uMor} X} (φ : CompBundle.Hom B₁ B₂) :
    CompBundle.Hom.pullback (fun x => x) φ = φ := rfl

/-- Pullback functor along identity is identity. -/
@[simp]
theorem CompBundle.pullbackFunctor_id.{uObj, uMor} (X : Type uObj) :
    CompBundle.pullbackFunctor (𝟙 X) =
      𝟙 (Cat.of (CompBundle.{uObj, uMor} X)) := rfl

/-- Pullback along composition equals composition of pullbacks on objects. -/
@[simp]
theorem CompBundle.pullback_comp.{uObj, uMor} {X Y Z : Type uObj}
    (f : X → Y) (g : Y → Z) (B : CompBundle.{uObj, uMor} Z) :
    CompBundle.pullback f (CompBundle.pullback g B) =
      CompBundle.pullback (fun x => g (f x)) B := rfl

/-- Pullback functor along composition equals composition of pullback functors. -/
@[simp]
theorem CompBundle.pullbackFunctor_comp.{uObj, uMor}
    {X Y Z : (Type uObj)ᵒᵖ'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CompBundle.pullbackFunctor.{uObj, uMor} f ⋙
      CompBundle.pullbackFunctor g =
      CompBundle.pullbackFunctor (f ≫ g) := rfl

/-- The composition functor: sends types to categories of composition bundles,
    with pullback as the functorial action. -/
def compFunctor.{uObj, uMor} :
    (Type uObj)ᵒᵖ' ⥤ Cat.{max uObj uMor, max uObj (uMor + 1)} where
  obj X := Cat.of (CompBundle.{uObj, uMor} X)
  map f := CompBundle.pullbackFunctor f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ## Layer 3 Grothendieck Construction -/

/-- The third layer: Grothendieck construction of the composition functor.
    Objects are pairs `(X : Type uObj, B : CompBundle X)`. -/
abbrev CompGr.{uObj, uMor} :=
  GrothendieckContra'.{uObj + 1, uObj, max uObj (uMor + 1), max uObj uMor}
    (C := Type uObj)
    compFunctor.{uObj, uMor}

/-- For an IdGr I, the type of composition structures. -/
def CompStruct.{uObj, uMor} (I : IdGr.{uObj, uMor}) : Type (max uObj uMor) :=
  ∀ (x y z : I.objType), I.Hom x y → I.Hom y z → I.Hom x z

/-! ### Layer 3 Accessors -/

/-- Extract the object type from a composition structure. -/
def CompGr.objType.{uObj, uMor} (C : CompGr.{uObj, uMor}) : Type uObj := C.base

/-- Extract the morphism family from a composition structure. -/
def CompGr.morFamily.{uObj, uMor} (C : CompGr.{uObj, uMor}) :
    C.objType × C.objType → Type uMor :=
  C.fiber.morFamily

/-- The type of morphisms from `x` to `y` in composition structure `C`. -/
def CompGr.Hom.{uObj, uMor} (C : CompGr.{uObj, uMor}) (x y : C.objType) : Type uMor :=
  C.morFamily (x, y)

/-- Extract the identity morphism for an object. -/
def CompGr.idMor.{uObj, uMor} (C : CompGr.{uObj, uMor}) (x : C.objType) : C.Hom x x :=
  C.fiber.idMor x

/-- Compose two morphisms. -/
def CompGr.comp.{uObj, uMor} (C : CompGr.{uObj, uMor}) {x y z : C.objType}
    (f : C.Hom x y) (g : C.Hom y z) : C.Hom x z :=
  C.fiber.compOp x y z f g

/-! ### Layer 3 Constructors -/

/-- Construct a CompGr from a type and a CompBundle. -/
def CompGr.mk.{uObj, uMor} (X : Type uObj) (B : CompBundle.{uObj, uMor} X) :
    CompGr.{uObj, uMor} :=
  ⟨X, B⟩

@[simp]
theorem CompGr.mk_objType.{uObj, uMor} (X : Type uObj) (B : CompBundle.{uObj, uMor} X) :
    (CompGr.mk X B).objType = X := rfl

@[simp]
theorem CompGr.mk_fiber.{uObj, uMor} (X : Type uObj) (B : CompBundle.{uObj, uMor} X) :
    (CompGr.mk X B).fiber = B := rfl

/-- Reconstruction: a composition structure equals its components. -/
theorem CompGr.eta.{uObj, uMor} (C : CompGr.{uObj, uMor}) :
    CompGr.mk C.objType C.fiber = C := rfl

/-- Extract the underlying QuiverGr from a CompGr. -/
def CompGr.toQuiverGr.{uObj, uMor} (C : CompGr.{uObj, uMor}) : QuiverGr.{uObj, uMor} :=
  QuiverGr.mk C.objType C.morFamily

/-- Extract the underlying IdGr from a CompGr. -/
def CompGr.toIdGr.{uObj, uMor} (C : CompGr.{uObj, uMor}) : IdGr.{uObj, uMor} :=
  IdGr.ofData C.objType C.morFamily C.fiber.idMor

/-! ## Complete Constructor

Construct a full `CompGr` from all the raw data at once.
-/

/-- Construct a CompGr from raw data: object type, morphism family,
    identity assignment, and composition operation. -/
def CompGr.ofData.{uObj, uMor}
    (X : Type uObj)
    (M : X × X → Type uMor)
    (idMorFn : ∀ x : X, M (x, x))
    (compOpFn : ∀ (x y z : X), M (x, y) → M (y, z) → M (x, z)) :
    CompGr.{uObj, uMor} :=
  ⟨X, ⟨M, idMorFn, compOpFn⟩⟩

@[simp]
theorem CompGr.ofData_objType.{uObj, uMor}
    (X : Type uObj) (M : X × X → Type uMor)
    (idMorFn : ∀ x : X, M (x, x))
    (compOpFn : ∀ (x y z : X), M (x, y) → M (y, z) → M (x, z)) :
    (CompGr.ofData X M idMorFn compOpFn).objType = X := rfl

@[simp]
theorem CompGr.ofData_morFamily.{uObj, uMor}
    (X : Type uObj) (M : X × X → Type uMor)
    (idMorFn : ∀ x : X, M (x, x))
    (compOpFn : ∀ (x y z : X), M (x, y) → M (y, z) → M (x, z)) :
    (CompGr.ofData X M idMorFn compOpFn).morFamily = M := rfl

@[simp]
theorem CompGr.ofData_idMor.{uObj, uMor}
    (X : Type uObj) (M : X × X → Type uMor)
    (idMorFn : ∀ x : X, M (x, x))
    (compOpFn : ∀ (x y z : X), M (x, y) → M (y, z) → M (x, z))
    (x : X) :
    (CompGr.ofData X M idMorFn compOpFn).idMor x = idMorFn x := rfl

@[simp]
theorem CompGr.ofData_comp.{uObj, uMor}
    (X : Type uObj) (M : X × X → Type uMor)
    (idMorFn : ∀ x : X, M (x, x))
    (compOpFn : ∀ (x y z : X), M (x, y) → M (y, z) → M (x, z))
    {x y z : X} (f : M (x, y)) (g : M (y, z)) :
    (CompGr.ofData X M idMorFn compOpFn).comp f g = compOpFn x y z f g := rfl

/-! ## The Φ Functor: Categories to CompGr

The Φ functor extracts the underlying category judgment data from a category.
Given a category `C : Cat.{v, u}`, we extract:
- Object type: the type of objects (in universe `u`)
- Morphism family: for each pair `(x, y)`, the type of morphisms (in universe `v`)
- Identity: the identity morphisms
- Composition: the composition operation

This is the right adjoint in the reflective adjunction `L ⊣ Φ` where `L`
freely generates a category from judgment data.
-/

/-- Extract the underlying `CompGr` data from a category.
    This is the object mapping of the Φ functor. -/
def CompGr.ofCat.{uObj, uMor} (C : Cat.{uMor, uObj}) : CompGr.{uObj, uMor} :=
  CompGr.ofData
    C
    (fun p => p.1 ⟶ p.2)
    (fun x => 𝟙 x)
    (fun _ _ _ f g => f ≫ g)

@[simp]
theorem CompGr.ofCat_objType.{uObj, uMor} (C : Cat.{uMor, uObj}) :
    (CompGr.ofCat C).objType = C := rfl

@[simp]
theorem CompGr.ofCat_Hom.{uObj, uMor} (C : Cat.{uMor, uObj}) (x y : C) :
    (CompGr.ofCat C).Hom x y = (x ⟶ y) := rfl

@[simp]
theorem CompGr.ofCat_idMor.{uObj, uMor} (C : Cat.{uMor, uObj}) (x : C) :
    (CompGr.ofCat C).idMor x = 𝟙 x := rfl

@[simp]
theorem CompGr.ofCat_comp.{uObj, uMor} (C : Cat.{uMor, uObj})
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (CompGr.ofCat C).comp f g = f ≫ g := rfl

/-! ## Category Laws for CompGr

A `CompGr` represents category judgment data but doesn't enforce category laws.
We define predicates for the laws so we can identify lawful instances.
-/

/-- Left identity law: `id ≫ f = f` for all morphisms `f`. -/
def CompGr.IdLeft.{uObj, uMor} (C : CompGr.{uObj, uMor}) : Prop :=
  ∀ (x y : C.objType) (f : C.Hom x y), C.comp (C.idMor x) f = f

/-- Right identity law: `f ≫ id = f` for all morphisms `f`. -/
def CompGr.IdRight.{uObj, uMor} (C : CompGr.{uObj, uMor}) : Prop :=
  ∀ (x y : C.objType) (f : C.Hom x y), C.comp f (C.idMor y) = f

/-- Associativity law: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`. -/
def CompGr.Assoc.{uObj, uMor} (C : CompGr.{uObj, uMor}) : Prop :=
  ∀ (w x y z : C.objType) (f : C.Hom w x) (g : C.Hom x y) (h : C.Hom y z),
    C.comp (C.comp f g) h = C.comp f (C.comp g h)

/-- A `CompGr` satisfying category laws. -/
structure CompGr.IsLawful.{uObj, uMor} (C : CompGr.{uObj, uMor}) : Prop where
  id_left : C.IdLeft
  id_right : C.IdRight
  assoc : C.Assoc

/-- Categories give lawful CompGr. -/
theorem CompGr.ofCat_isLawful.{uObj, uMor} (C : Cat.{uMor, uObj}) :
    (CompGr.ofCat C).IsLawful where
  id_left := fun _ _ f => Category.id_comp f
  id_right := fun _ _ f => Category.comp_id f
  assoc := fun _ _ _ _ f g h => Category.assoc f g h

/-! ## The L Functor: Lawful CompGr to Cat

For a lawful `CompGr`, we can construct the corresponding category.
This is the left adjoint in the reflective adjunction.
-/

/-- Category instance for a lawful CompGr. -/
def CompGr.toCategoryStruct.{uObj, uMor} (C : CompGr.{uObj, uMor}) :
    CategoryStruct C.objType where
  Hom := C.Hom
  id := C.idMor
  comp := C.comp

/-- A lawful CompGr gives a full Category instance. -/
def CompGr.toCategory.{uObj, uMor} (C : CompGr.{uObj, uMor})
    (h : C.IsLawful) : Category C.objType :=
  { C.toCategoryStruct with
    id_comp := h.id_left _ _
    comp_id := h.id_right _ _
    assoc := h.assoc _ _ _ _ }

/-- The bundled category from a lawful CompGr. -/
def CompGr.toCat.{uObj, uMor} (C : CompGr.{uObj, uMor})
    (h : C.IsLawful) : Cat.{uMor, uObj} :=
  @Cat.of C.objType (C.toCategory h)

/-! ## Round-trip Properties

Properties of the `ofCat`/`toCat` correspondence.
-/

/-- Extracting data from a category and rebuilding gives the same category
    (up to definitional equality of the Category structure). -/
theorem CompGr.ofCat_toCat_eq.{uObj, uMor} (C : Cat.{uMor, uObj}) :
    (CompGr.ofCat C).toCat (CompGr.ofCat_isLawful C) = C := by
  unfold CompGr.toCat CompGr.toCategory CompGr.toCategoryStruct
  unfold CompGr.ofCat CompGr.ofData
  exact Cat.coe_of C

/-- For a lawful CompGr, extracting from toCat gives back the same data. -/
theorem CompGr.toCat_ofCat_eq.{uObj, uMor} (C : CompGr.{uObj, uMor})
    (h : C.IsLawful) :
    CompGr.ofCat (C.toCat h) = C := by
  unfold CompGr.ofCat CompGr.ofData CompGr.toCat
  simp only [Cat.of_α]
  rfl

/-! ## Summary

We have constructed a three-layer structure for category-judgment data, with
all layers as proper contravariant Grothendieck constructions over `Type`:

1. `quiverFunctor : (Type uObj)ᵒᵖ' ⥤ Cat` — sends types to quiver categories
   `QuiverGr = GrothendieckContra' quiverFunctor` — quiver structures

2. `idQuiverFunctor : (Type uObj)ᵒᵖ' ⥤ Cat` — bundles quiver and identity
   `IdGr = GrothendieckContra' idQuiverFunctor` — quivers with identity

3. `compFunctor : (Type uObj)ᵒᵖ' ⥤ Cat` — bundles quiver, identity, composition
   `CompGr = GrothendieckContra' compFunctor` — categories-without-laws

Universe parameters:
- `uObj`: universe for object types
- `uMor`: universe for morphism types (independent of `uObj`)

Each layer has:
- Accessors (`objType`, `morFamily`, `Hom`, `id`, `comp`)
- Constructors (`mk`, `ofData`)
- Inverse proofs (`eta`)

The `CompGr.{uObj, uMor}` type captures full category-judgment copresheaf data
with independent universe parameters, analogous to `Cat.{vMor, uObj}`.

Each layer bundles all accumulated structure in its fiber over `Type`:
- `IdQuiverBundle X` bundles morphism family + identity assignment over `X`
- `CompBundle X` bundles morphism family + identity + composition over `X`

Pullback along functions provides the contravariant functorial action:
for `f : X → Y`, structures pull back via `Hom_X(x,y) := Hom_Y(fx, fy)`.
-/

end Groth

end PLang

end GebLean
