import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import GebLean.Utilities.Grothendieck
import GebLean.Utilities.Opposites
import GebLean.Utilities.Families

/-!
# Category Judgments via Layered Grothendieck Construction

This module presents category-judgment copresheaves as a layered Grothendieck
construction with independent universe parameters.

The layering:

* Layer 1: `QuiverGr = GrothendieckContra' quiverFunctor`
  - Contravariant over `Type uObj`
  - Objects: pairs (X : Type, mor : X × X → Type uMor)
  - Morphisms use pullback along functions

* Layer 2: `IdWitGr = Grothendieck idWitFunctor`
  - Covariant over QuiverGr
  - Objects: pairs (Q : QuiverGr, idWit : IdWitBundle Q)
  - Identity witnesses certify which morphisms are identities
  - Morphisms use pushforward along quiver morphisms

* Layer 3: `CompWitGr = Grothendieck compWitFunctor`
  - Covariant over IdWitGr
  - Objects: pairs (I : IdWitGr, compWit : CompWitBundle I)
  - Composition witnesses certify which morphism triples are compositions
  - Morphisms use pushforward along IdWitGr morphisms

Layers 2 and 3 use the copresheaf/relational approach: identity and composition
are represented as witness types with projections, matching `CatJudgCopr`.
This allows the covariant Grothendieck construction with pushforward functors.
-/

namespace GebLean

namespace PLang

namespace Groth

open CategoryTheory

/-! ## Layer 1: Quiver Functor via familyFunctor'

For each type `X : Type uObj`, a quiver over `X` consists of:
- For each pair `(x, y) : X × X`, a type `Mor(x, y) : Type uMor` of morphisms

This is `FamilyCat (Type uMor) (X × X)` = the category of `(X × X)`-indexed
type families. The functor `familyFunctor' (Type uMor)` composes with the
squaring functor to give us quiver structures.
-/

/-- The squaring functor `X ↦ X × X` on types. -/
def sqFunctor.{u} : Type u ⥤ Type u where
  obj X := X × X
  map f := TypeCat.ofHom fun p => (f p.1, f p.2)

@[simp]
theorem sqFunctor_map_id.{u} (X : Type u) :
    sqFunctor.map (𝟙 X) = 𝟙 (X × X) := by
  apply ConcreteCategory.ext_apply; intro p; rfl

@[simp]
theorem sqFunctor_map_comp.{u} {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sqFunctor.map (f ≫ g) = sqFunctor.map f ≫ sqFunctor.map g := by
  apply ConcreteCategory.ext_apply; intro p; rfl

/-- The squaring functor on the opposite category. -/
def sqFunctorOp'.{u} : (Type u)ᵒᵖ' ⥤ (Type u)ᵒᵖ' :=
  Functor.op' sqFunctor.{u}

@[simp]
theorem sqFunctorOp'_map_id.{u} (X : (Type u)ᵒᵖ') :
    sqFunctorOp'.map (𝟙 X) = 𝟙 (X × X) := by
  change (sqFunctor.map (𝟙 X) : @Quiver.Hom (Type u) _ (X × X) (X × X)) =
    (𝟙 (X × X) : @Quiver.Hom (Type u) _ (X × X) (X × X))
  exact sqFunctor.map_id X

@[simp]
theorem sqFunctorOp'_map_comp.{u} {X Y Z : (Type u)ᵒᵖ'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sqFunctorOp'.map (f ≫ g) = sqFunctorOp'.map f ≫ sqFunctorOp'.map g := by
  change (sqFunctor.map (g ≫ f : @Quiver.Hom (Type u) _ Z X) :
      @Quiver.Hom (Type u) _ (Z × Z) (X × X)) =
    (sqFunctor.map (g : @Quiver.Hom (Type u) _ Z Y) ≫
      sqFunctor.map (f : @Quiver.Hom (Type u) _ Y X) :
      @Quiver.Hom (Type u) _ (Z × Z) (X × X))
  exact sqFunctor.map_comp _ _

/-- The quiver functor with independent universes: sends `X : Type uObj` to
    the category of `(X × X)`-indexed type families in `Type uMor`.

    Objects of `quiverFunctor.obj X` are functions `X × X → Type uMor`, i.e.,
    for each pair of objects, a type of morphisms between them. -/
def quiverFunctor.{uObj, uMor} : (Type uObj)ᵒᵖ' ⥤ Cat.{max uObj uMor, max uObj (uMor + 1)} :=
  sqFunctorOp'.{uObj} ⋙ familyFunctor'.{uMor + 1, uMor, uObj} (Type uMor)

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

/-! ## Copresheaf-Style Identity Witness Bundles

The copresheaf approach represents identity as a *relation* rather than a function.
Instead of assigning an identity morphism to each object (`∀ x, Hom x x`),
we have:
- A type of identity witnesses
- Projections extracting the object and morphism from each witness

This matches `CatJudgCopr` and allows the covariant Grothendieck construction
to work because identity data can be *pushed forward* along quiver morphisms.

Given `h : Q₁ → Q₂`, the pushforward of identity witness data `(W, obj, mor)`:
- Same witness type W
- `obj' w = h.base (obj w)`
- `mor' w = h.fiber (mor w)`
-/

/-- Bundle of identity witness data over a quiver Q.

    This is the copresheaf/relational approach: instead of a function assigning
    an identity morphism to each object, we have a type of witnesses with
    projections. Each witness certifies that a particular morphism is an
    identity at a particular object.

    For a category C, the identity witness type could be C.obj itself,
    with witObj = id and witMor = 𝟙. But this representation is more flexible
    and allows the Grothendieck construction to work via pushforward. -/
structure IdWitBundle.{uObj, uMor, uWit} (Q : QuiverGr.{uObj, uMor}) where
  witType : Type uWit
  witObj : witType → Q.objType
  witMor : (w : witType) → Q.Hom (witObj w) (witObj w)

/-- Morphisms between identity witness bundles over the same quiver:
    functions on witness types that preserve both object and morphism
    projections. The witMor_eq field uses cast since witMor_eq at w relates
    morphisms at B₂.witObj (witMap w) and B₁.witObj w. -/
structure IdWitBundle.Hom.{uObj, uMor, uWit} {Q : QuiverGr.{uObj, uMor}}
    (B₁ B₂ : IdWitBundle.{uObj, uMor, uWit} Q) where
  witMap : B₁.witType → B₂.witType
  witObj_eq : ∀ w, B₂.witObj (witMap w) = B₁.witObj w
  witMor_eq : ∀ w, HEq (B₂.witMor (witMap w)) (B₁.witMor w)

@[ext]
theorem IdWitBundle.Hom.ext.{uObj, uMor, uWit} {Q : QuiverGr.{uObj, uMor}}
    {B₁ B₂ : IdWitBundle.{uObj, uMor, uWit} Q}
    {f g : IdWitBundle.Hom B₁ B₂}
    (h : ∀ w, f.witMap w = g.witMap w) : f = g := by
  cases f; cases g
  congr 1
  funext w
  exact h w

/-- Identity morphism for IdWitBundle. -/
def IdWitBundle.Hom.identity.{uObj, uMor, uWit} {Q : QuiverGr.{uObj, uMor}}
    (B : IdWitBundle.{uObj, uMor, uWit} Q) : IdWitBundle.Hom B B where
  witMap := id
  witObj_eq := fun _ => rfl
  witMor_eq := fun _ => HEq.rfl

/-- Composition of IdWitBundle morphisms. -/
def IdWitBundle.Hom.comp.{uObj, uMor, uWit} {Q : QuiverGr.{uObj, uMor}}
    {B₁ B₂ B₃ : IdWitBundle.{uObj, uMor, uWit} Q}
    (f : IdWitBundle.Hom B₁ B₂) (g : IdWitBundle.Hom B₂ B₃) :
    IdWitBundle.Hom B₁ B₃ where
  witMap := g.witMap ∘ f.witMap
  witObj_eq := fun w => by
    simp only [Function.comp_apply]
    rw [g.witObj_eq, f.witObj_eq]
  witMor_eq := fun w => by
    simp only [Function.comp_apply]
    exact HEq.trans (g.witMor_eq (f.witMap w)) (f.witMor_eq w)

/-- Category instance for IdWitBundle over a fixed quiver. -/
instance IdWitBundle.instCategory.{uObj, uMor, uWit} (Q : QuiverGr.{uObj, uMor}) :
    Category.{uWit} (IdWitBundle.{uObj, uMor, uWit} Q) where
  Hom B₁ B₂ := IdWitBundle.Hom B₁ B₂
  id B := IdWitBundle.Hom.identity B
  comp := fun {B₁ B₂ B₃} (f : IdWitBundle.Hom B₁ B₂) (g : IdWitBundle.Hom B₂ B₃) =>
    IdWitBundle.Hom.comp f g
  id_comp := fun {_ _} _ => IdWitBundle.Hom.ext fun _ => rfl
  comp_id := fun {_ _} _ => IdWitBundle.Hom.ext fun _ => rfl
  assoc := fun {_ _ _ _} _ _ _ => IdWitBundle.Hom.ext fun _ => rfl

/-! ### Pushforward of Identity Witness Bundles

Given a quiver morphism `h : Q₁ ⟶ Q₂`, we can push forward identity witness
data from Q₁ to Q₂. This is the functorial action for the covariant
Grothendieck construction.
-/

/-- Pushforward of an identity witness bundle along a quiver morphism. -/
def IdWitBundle.pushforward.{uObj, uMor, uWit}
    {Q₁ Q₂ : QuiverGr.{uObj, uMor}} (h : Q₁ ⟶ Q₂)
    (B : IdWitBundle.{uObj, uMor, uWit} Q₁) :
    IdWitBundle.{uObj, uMor, uWit} Q₂ where
  witType := B.witType
  witObj := fun w => h.base (B.witObj w)
  witMor := fun w => h.fiber (B.witObj w, B.witObj w) (B.witMor w)

/-- Pushforward of a morphism of identity witness bundles. -/
def IdWitBundle.Hom.pushforward.{uObj, uMor, uWit}
    {Q₁ Q₂ : QuiverGr.{uObj, uMor}} (h : Q₁ ⟶ Q₂)
    {B₁ B₂ : IdWitBundle.{uObj, uMor, uWit} Q₁}
    (φ : IdWitBundle.Hom B₁ B₂) :
    IdWitBundle.Hom (IdWitBundle.pushforward h B₁)
                    (IdWitBundle.pushforward h B₂) where
  witMap := φ.witMap
  witObj_eq := fun w => by
    simp only [IdWitBundle.pushforward]
    rw [φ.witObj_eq]
  witMor_eq := fun w => by
    simp only [IdWitBundle.pushforward]
    have hobj := φ.witObj_eq w
    have hmor := φ.witMor_eq w
    have helper : ∀ {a b : Q₁.objType} (hab : a = b)
        {m : Q₁.morFamily (a, a)} {n : Q₁.morFamily (b, b)} (hmn : HEq m n),
        HEq (h.fiber (a, a) m) (h.fiber (b, b) n) := by
      intro a b hab m n hmn
      subst hab
      exact heq_of_eq (congrArg (h.fiber _) (eq_of_heq hmn))
    exact helper hobj hmor

/-- Pushforward functor for identity witness bundles. -/
def IdWitBundle.pushforwardFunctor.{uObj, uMor, uWit}
    {Q₁ Q₂ : QuiverGr.{uObj, uMor}} (h : Q₁ ⟶ Q₂) :
    IdWitBundle.{uObj, uMor, uWit} Q₁ ⥤ IdWitBundle.{uObj, uMor, uWit} Q₂ where
  obj := IdWitBundle.pushforward h
  map := fun {B₁ B₂} (φ : IdWitBundle.Hom B₁ B₂) =>
    IdWitBundle.Hom.pushforward h φ
  map_id _ := IdWitBundle.Hom.ext fun _ => rfl
  map_comp _ _ := IdWitBundle.Hom.ext fun _ => rfl

@[simp]
theorem IdWitBundle.pushforward_id.{uObj, uMor, uWit}
    {Q : QuiverGr.{uObj, uMor}} (B : IdWitBundle.{uObj, uMor, uWit} Q) :
    IdWitBundle.pushforward (𝟙 Q) B = B := rfl

@[simp]
theorem IdWitBundle.pushforward_comp.{uObj, uMor, uWit}
    {Q₁ Q₂ Q₃ : QuiverGr.{uObj, uMor}} (f : Q₁ ⟶ Q₂) (g : Q₂ ⟶ Q₃)
    (B : IdWitBundle.{uObj, uMor, uWit} Q₁) :
    IdWitBundle.pushforward (f ≫ g) B =
    IdWitBundle.pushforward g (IdWitBundle.pushforward f B) := rfl

/-! ### The Identity Witness Functor

The covariant functor from QuiverGr to Cat sending each quiver to its
category of identity witness bundles.
-/

set_option backward.isDefEq.respectTransparency false in
/-- The identity witness functor: sends quivers to categories of identity
    witness bundles, with pushforward as the functorial action.

    This is a covariant functor QuiverGr → Cat, suitable for mathlib's
    standard Grothendieck construction. -/
def idWitFunctor.{uObj, uMor, uWit} :
    QuiverGr.{uObj, uMor} ⥤
    Cat.{uWit, max uObj uMor (uWit + 1)} where
  obj Q := Cat.of (IdWitBundle.{uObj, uMor, uWit} Q)
  map h := (IdWitBundle.pushforwardFunctor h).toCatHom
  map_id Q := by
    apply Cat.Hom.ext
    apply _root_.CategoryTheory.Functor.ext
    · intro B Y f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply IdWitBundle.Hom.ext
      intro w; rfl
    · intro B; rfl
  map_comp f g := by
    apply Cat.Hom.ext
    apply _root_.CategoryTheory.Functor.ext
    · intro B Y φ
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply IdWitBundle.Hom.ext
      intro w; rfl
    · intro B; rfl

/-! ## Layer 2 via Covariant Grothendieck: Quivers with Identity Witnesses

Using mathlib's standard Grothendieck construction with the identity witness
functor gives us the category of quivers equipped with identity witness data.
-/

/-- The second layer via covariant Grothendieck: quivers with identity witness
    structures. Objects are pairs (Q, B) where Q is a quiver and B is an
    identity witness bundle over Q. -/
abbrev IdWitGr.{uObj, uMor, uWit} :=
  Grothendieck idWitFunctor.{uObj, uMor, uWit}

namespace IdWitGr

/-- Extract the underlying quiver from an IdWitGr. -/
abbrev quiver.{uObj, uMor, uWit} (I : IdWitGr.{uObj, uMor, uWit}) :
    QuiverGr.{uObj, uMor} := I.base

/-- Extract the object type from an IdWitGr. -/
abbrev objType.{uObj, uMor, uWit} (I : IdWitGr.{uObj, uMor, uWit}) :
    Type uObj := I.quiver.objType

/-- The type of morphisms from x to y in an IdWitGr. -/
abbrev Hom'.{uObj, uMor, uWit} (I : IdWitGr.{uObj, uMor, uWit})
    (x y : I.objType) : Type uMor := I.quiver.Hom x y

end IdWitGr

/-! ## Layer 3: Composition Witness Bundles

Composition witness bundles over an `IdWitGr`. Each witness certifies that
a particular triple of morphisms (f, g, h) represents a composition f ≫ g = h.
-/

/-- Bundle of composition witness data over an IdWitGr.
    Each witness provides source/middle/target objects and three morphisms:
    - left: source → middle
    - right: middle → target
    - composite: source → target (= left ≫ right in a category) -/
structure CompWitBundle.{uObj, uMor, uWit, uCWit}
    (I : IdWitGr.{uObj, uMor, uWit}) where
  witType : Type uCWit
  witSrc : witType → I.objType
  witMid : witType → I.objType
  witTgt : witType → I.objType
  witLeft : (w : witType) → I.Hom' (witSrc w) (witMid w)
  witRight : (w : witType) → I.Hom' (witMid w) (witTgt w)
  witComp : (w : witType) → I.Hom' (witSrc w) (witTgt w)

/-- Morphisms between composition witness bundles over the same IdWitGr:
    functions on witness types that preserve all projections. -/
structure CompWitBundle.Hom.{uObj, uMor, uWit, uCWit}
    {I : IdWitGr.{uObj, uMor, uWit}}
    (B₁ B₂ : CompWitBundle.{uObj, uMor, uWit, uCWit} I) where
  witMap : B₁.witType → B₂.witType
  witSrc_eq : ∀ w, B₂.witSrc (witMap w) = B₁.witSrc w
  witMid_eq : ∀ w, B₂.witMid (witMap w) = B₁.witMid w
  witTgt_eq : ∀ w, B₂.witTgt (witMap w) = B₁.witTgt w
  witLeft_eq : ∀ w, HEq (B₂.witLeft (witMap w)) (B₁.witLeft w)
  witRight_eq : ∀ w, HEq (B₂.witRight (witMap w)) (B₁.witRight w)
  witComp_eq : ∀ w, HEq (B₂.witComp (witMap w)) (B₁.witComp w)

@[ext]
theorem CompWitBundle.Hom.ext.{uObj, uMor, uWit, uCWit}
    {I : IdWitGr.{uObj, uMor, uWit}}
    {B₁ B₂ : CompWitBundle.{uObj, uMor, uWit, uCWit} I}
    {f g : CompWitBundle.Hom B₁ B₂}
    (h : ∀ w, f.witMap w = g.witMap w) : f = g := by
  cases f; cases g
  congr 1
  funext w
  exact h w

/-- Identity morphism for CompWitBundle. -/
def CompWitBundle.Hom.identity.{uObj, uMor, uWit, uCWit}
    {I : IdWitGr.{uObj, uMor, uWit}}
    (B : CompWitBundle.{uObj, uMor, uWit, uCWit} I) :
    CompWitBundle.Hom B B where
  witMap := id
  witSrc_eq := fun _ => rfl
  witMid_eq := fun _ => rfl
  witTgt_eq := fun _ => rfl
  witLeft_eq := fun _ => HEq.rfl
  witRight_eq := fun _ => HEq.rfl
  witComp_eq := fun _ => HEq.rfl

/-- Composition of CompWitBundle morphisms. -/
def CompWitBundle.Hom.comp.{uObj, uMor, uWit, uCWit}
    {I : IdWitGr.{uObj, uMor, uWit}}
    {B₁ B₂ B₃ : CompWitBundle.{uObj, uMor, uWit, uCWit} I}
    (f : CompWitBundle.Hom B₁ B₂) (g : CompWitBundle.Hom B₂ B₃) :
    CompWitBundle.Hom B₁ B₃ where
  witMap := g.witMap ∘ f.witMap
  witSrc_eq := fun w => by
    simp only [Function.comp_apply]
    rw [g.witSrc_eq, f.witSrc_eq]
  witMid_eq := fun w => by
    simp only [Function.comp_apply]
    rw [g.witMid_eq, f.witMid_eq]
  witTgt_eq := fun w => by
    simp only [Function.comp_apply]
    rw [g.witTgt_eq, f.witTgt_eq]
  witLeft_eq := fun w => (g.witLeft_eq (f.witMap w)).trans (f.witLeft_eq w)
  witRight_eq := fun w => (g.witRight_eq (f.witMap w)).trans (f.witRight_eq w)
  witComp_eq := fun w => (g.witComp_eq (f.witMap w)).trans (f.witComp_eq w)

/-- The witMap of a composition is function composition of witMaps. -/
@[simp]
theorem CompWitBundle.Hom.comp_witMap.{uObj, uMor, uWit, uCWit}
    {I : IdWitGr.{uObj, uMor, uWit}}
    {B₁ B₂ B₃ : CompWitBundle.{uObj, uMor, uWit, uCWit} I}
    (f : CompWitBundle.Hom B₁ B₂) (g : CompWitBundle.Hom B₂ B₃)
    (w : B₁.witType) :
    (f.comp g).witMap w = g.witMap (f.witMap w) := rfl

/-- Category instance for CompWitBundle over a fixed IdWitGr. -/
instance CompWitBundle.instCategory.{uObj, uMor, uWit, uCWit}
    (I : IdWitGr.{uObj, uMor, uWit}) :
    Category.{uCWit} (CompWitBundle.{uObj, uMor, uWit, uCWit} I) where
  Hom B₁ B₂ := CompWitBundle.Hom B₁ B₂
  id B := CompWitBundle.Hom.identity B
  comp := fun {B₁ B₂ B₃}
    (f : CompWitBundle.Hom B₁ B₂) (g : CompWitBundle.Hom B₂ B₃) =>
    CompWitBundle.Hom.comp f g
  id_comp := fun {_ _} _ => CompWitBundle.Hom.ext fun _ => rfl
  comp_id := fun {_ _} _ => CompWitBundle.Hom.ext fun _ => rfl
  assoc := fun {_ _ _ _} _ _ _ => CompWitBundle.Hom.ext fun _ => rfl

/-- Category composition of CompWitBundle morphisms. -/
@[simp]
theorem CompWitBundle.Hom.category_comp_witMap.{uObj, uMor, uWit, uCWit}
    {I : IdWitGr.{uObj, uMor, uWit}}
    {B₁ B₂ B₃ : CompWitBundle.{uObj, uMor, uWit, uCWit} I}
    (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₃) (w : B₁.witType) :
    (f ≫ g).witMap w = g.witMap (f.witMap w) := rfl

/-! ### Pushforward of Composition Witness Bundles

Given an IdWitGr morphism `h : I₁ ⟶ I₂`, we can push forward composition
witness data from I₁ to I₂.
-/

/-- Pushforward of a composition witness bundle along an IdWitGr morphism. -/
def CompWitBundle.pushforward.{uObj, uMor, uWit, uCWit}
    {I₁ I₂ : IdWitGr.{uObj, uMor, uWit}} (h : I₁ ⟶ I₂)
    (B : CompWitBundle.{uObj, uMor, uWit, uCWit} I₁) :
    CompWitBundle.{uObj, uMor, uWit, uCWit} I₂ where
  witType := B.witType
  witSrc := fun w => h.base.base (B.witSrc w)
  witMid := fun w => h.base.base (B.witMid w)
  witTgt := fun w => h.base.base (B.witTgt w)
  witLeft := fun w => h.base.fiber (B.witSrc w, B.witMid w) (B.witLeft w)
  witRight := fun w => h.base.fiber (B.witMid w, B.witTgt w) (B.witRight w)
  witComp := fun w => h.base.fiber (B.witSrc w, B.witTgt w) (B.witComp w)

/-- HEq transport for fiber maps: if the pairs and morphisms are related by
    equalities/HEq, then the fiber maps are HEq. -/
theorem QuiverGr.Hom.fiber_heq.{uObj, uMor}
    {Q₁ Q₂ : QuiverGr.{uObj, uMor}} (f : Q₁ ⟶ Q₂)
    {a₁ a₂ b₁ b₂ : Q₁.objType} (ha : a₂ = a₁) (hb : b₂ = b₁)
    {m₁ : Q₁.Hom a₁ b₁} {m₂ : Q₁.Hom a₂ b₂} (hm : HEq m₂ m₁) :
    HEq (f.fiber (a₂, b₂) m₂) (f.fiber (a₁, b₁) m₁) := by
  subst ha hb
  exact heq_of_eq (congrArg (f.fiber _) (eq_of_heq hm))

/-- Pushforward of a morphism of composition witness bundles. -/
def CompWitBundle.Hom.pushforward.{uObj, uMor, uWit, uCWit}
    {I₁ I₂ : IdWitGr.{uObj, uMor, uWit}} (h : I₁ ⟶ I₂)
    {B₁ B₂ : CompWitBundle.{uObj, uMor, uWit, uCWit} I₁}
    (φ : CompWitBundle.Hom B₁ B₂) :
    CompWitBundle.Hom (CompWitBundle.pushforward h B₁)
                      (CompWitBundle.pushforward h B₂) where
  witMap := φ.witMap
  witSrc_eq := fun w => by
    simp only [CompWitBundle.pushforward]
    rw [φ.witSrc_eq]
  witMid_eq := fun w => by
    simp only [CompWitBundle.pushforward]
    rw [φ.witMid_eq]
  witTgt_eq := fun w => by
    simp only [CompWitBundle.pushforward]
    rw [φ.witTgt_eq]
  witLeft_eq := fun w => by
    simp only [CompWitBundle.pushforward]
    exact QuiverGr.Hom.fiber_heq h.base (φ.witSrc_eq w) (φ.witMid_eq w) (φ.witLeft_eq w)
  witRight_eq := fun w => by
    simp only [CompWitBundle.pushforward]
    exact QuiverGr.Hom.fiber_heq h.base (φ.witMid_eq w) (φ.witTgt_eq w) (φ.witRight_eq w)
  witComp_eq := fun w => by
    simp only [CompWitBundle.pushforward]
    exact QuiverGr.Hom.fiber_heq h.base (φ.witSrc_eq w) (φ.witTgt_eq w) (φ.witComp_eq w)

/-- Pushforward functor for composition witness bundles. -/
def CompWitBundle.pushforwardFunctor.{uObj, uMor, uWit, uCWit}
    {I₁ I₂ : IdWitGr.{uObj, uMor, uWit}} (h : I₁ ⟶ I₂) :
    CompWitBundle.{uObj, uMor, uWit, uCWit} I₁ ⥤
    CompWitBundle.{uObj, uMor, uWit, uCWit} I₂ where
  obj := CompWitBundle.pushforward h
  map := fun {B₁ B₂} (φ : CompWitBundle.Hom B₁ B₂) =>
    CompWitBundle.Hom.pushforward h φ
  map_id _ := CompWitBundle.Hom.ext fun _ => rfl
  map_comp _ _ := CompWitBundle.Hom.ext fun _ => rfl

@[simp]
theorem CompWitBundle.pushforward_id.{uObj, uMor, uWit, uCWit}
    {I : IdWitGr.{uObj, uMor, uWit}}
    (B : CompWitBundle.{uObj, uMor, uWit, uCWit} I) :
    CompWitBundle.pushforward (𝟙 I) B = B := rfl

@[simp]
theorem CompWitBundle.pushforward_comp.{uObj, uMor, uWit, uCWit}
    {I₁ I₂ I₃ : IdWitGr.{uObj, uMor, uWit}}
    (f : I₁ ⟶ I₂) (g : I₂ ⟶ I₃)
    (B : CompWitBundle.{uObj, uMor, uWit, uCWit} I₁) :
    CompWitBundle.pushforward (f ≫ g) B =
    CompWitBundle.pushforward g (CompWitBundle.pushforward f B) := rfl

/-! ### The Composition Witness Functor -/

set_option backward.isDefEq.respectTransparency false in
/-- The composition witness functor: sends IdWitGr objects to categories of
    composition witness bundles, with pushforward as the functorial action.

    This is a covariant functor IdWitGr → Cat, suitable for mathlib's
    standard Grothendieck construction. -/
def compWitFunctor.{uObj, uMor, uWit, uCWit} :
    IdWitGr.{uObj, uMor, uWit} ⥤
    Cat.{uCWit, max uObj uMor (uCWit + 1)} where
  obj I := Cat.of (CompWitBundle.{uObj, uMor, uWit, uCWit} I)
  map h := (CompWitBundle.pushforwardFunctor h).toCatHom
  map_id I := by
    apply Cat.Hom.ext
    apply _root_.CategoryTheory.Functor.ext
    · intro B Y f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply CompWitBundle.Hom.ext
      intro w; rfl
    · intro B; rfl
  map_comp f g := by
    apply Cat.Hom.ext
    apply _root_.CategoryTheory.Functor.ext
    · intro B Y φ
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply CompWitBundle.Hom.ext
      intro w; rfl
    · intro B; rfl

/-! ## Layer 3 via Covariant Grothendieck: Quivers with Composition Witnesses

Using mathlib's standard Grothendieck construction with the composition
witness functor gives us the category of IdWitGr equipped with composition
witness data.
-/

/-- The third layer via covariant Grothendieck: quivers with identity AND
    composition witness structures. Objects are pairs (I, B) where I is an
    IdWitGr and B is a composition witness bundle over I. -/
abbrev CompWitGr.{uObj, uMor, uWit, uCWit} :=
  Grothendieck compWitFunctor.{uObj, uMor, uWit, uCWit}

namespace CompWitGr

/-- Extract the underlying IdWitGr from a CompWitGr. -/
abbrev idWitGr.{uObj, uMor, uWit, uCWit}
    (C : CompWitGr.{uObj, uMor, uWit, uCWit}) :
    IdWitGr.{uObj, uMor, uWit} := C.base

/-- Extract the underlying quiver from a CompWitGr. -/
abbrev quiver.{uObj, uMor, uWit, uCWit}
    (C : CompWitGr.{uObj, uMor, uWit, uCWit}) :
    QuiverGr.{uObj, uMor} := C.idWitGr.quiver

/-- Extract the object type from a CompWitGr. -/
abbrev objType.{uObj, uMor, uWit, uCWit}
    (C : CompWitGr.{uObj, uMor, uWit, uCWit}) :
    Type uObj := C.quiver.objType

/-- The type of morphisms from x to y in a CompWitGr. -/
abbrev Hom'.{uObj, uMor, uWit, uCWit}
    (C : CompWitGr.{uObj, uMor, uWit, uCWit})
    (x y : C.objType) : Type uMor := C.quiver.Hom x y

/-- Extract the identity witness bundle from a CompWitGr. -/
abbrev idBundle.{uObj, uMor, uWit, uCWit}
    (C : CompWitGr.{uObj, uMor, uWit, uCWit}) :
    IdWitBundle.{uObj, uMor, uWit} C.quiver := C.idWitGr.fiber

/-- Extract the composition witness bundle from a CompWitGr. -/
abbrev bundle.{uObj, uMor, uWit, uCWit}
    (C : CompWitGr.{uObj, uMor, uWit, uCWit}) :
    CompWitBundle.{uObj, uMor, uWit, uCWit} C.idWitGr := C.fiber

end CompWitGr

/-! ## Layered Grothendieck Construction Summary

The complete three-layer construction:

* Layer 1: `QuiverGr = GrothendieckContra' (quiverFunctor : (Type uObj)ᵒᵖ' ⥤ Cat)`
  - Objects: pairs (X : Type, mor : X × X → Type) with a quiver structure
  - Morphisms use pullback along functions

* Layer 2: `IdWitGr = Grothendieck (idWitFunctor : QuiverGr ⥤ Cat)`
  - Objects: pairs (Q : QuiverGr, idWit : IdWitBundle Q)
  - Identity witnesses certify which morphisms are identities
  - Morphisms use pushforward along quiver morphisms

* Layer 3: `CompWitGr = Grothendieck (compWitFunctor : IdWitGr ⥤ Cat)`
  - Objects: pairs (I : IdWitGr, compWit : CompWitBundle I)
  - Composition witnesses certify which morphism triples are compositions
  - Morphisms use pushforward along IdWitGr morphisms

The fiber functors use pushforward for covariant functoriality:
- `idWitFunctor.map h` pushes forward identity witness data along h
- `compWitFunctor.map h` pushes forward composition witness data along h
-/

end Groth

end PLang

end GebLean
