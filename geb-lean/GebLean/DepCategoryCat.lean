import Mathlib.CategoryTheory.Category.Cat
import GebLean.DepCategoryJudgments
import GebLean.Utilities.Category

/-!
# The Category of Categories as a Full Subcategory of DepCategoryData

This file shows that `Cat` (the category of categories) embeds as a full
subcategory into `DepCategoryData`.

## Overview

The category `DepCategoryData` with `DepNatTransData` morphisms is equivalent
to the category of copresheaves on `CategoryJudgments.Obj`. This copresheaf
category contains all "potential" category structures, including ones that
do not satisfy the category axioms.

The category `Cat` of small categories embeds into `DepCategoryData` as
those objects where:
- Identity witnesses exist and are unique for each object
- Composition witnesses exist and are unique for each composable pair
- The identity and associativity laws hold

## Main definitions

* `catToDepCategoryData`: Converts a category to DepCategoryData by encoding
  the category structure as dependent types where identity and composition
  witnesses are propositions (subtypes witnessing equality)

* `functorToDepNatTrans`: Converts a functor between categories to a
  DepNatTransData morphism between the corresponding DepCategoryData

* `catEmbedding`: The functor `Cat ⥤ DepCategoryData` that embeds
  categories into dependent category data

* `catEmbedding.faithful`: Proof that the embedding is faithful (injective
  on morphisms)

* `catEmbedding.full`: Proof that the embedding is full (surjective on
  morphisms between objects in the image)

## Mathematical content

A category `C` is converted to `DepCategoryData` as follows:
- `objT` = the objects of `C`
- `morT a b` = morphisms from `a` to `b` in `C`
- `idT m` = proof that `m` is the identity morphism (i.e., `m = 𝟙 _`)
- `compT f g h` = proof that `h = f ≫ g`

A functor `F : C ⥤ D` induces `DepNatTransData` with:
- `appObj` = the object function of `F`
- `appMor` = the morphism function of `F`
- `appId` = proof preservation (uses that `F` preserves identities)
- `appComp` = proof preservation (uses that `F` preserves composition)

The embedding is full because any `DepNatTransData` between categories
(when viewed as `DepCategoryData`) must preserve the identity and
composition structure, which exactly characterizes functors.

## References

See `DepCategoryJudgments.lean` for the definition of `DepCategoryData` and
its equivalence with copresheaves on `CategoryJudgments.Obj`.
-/

namespace GebLean

namespace CategoryJudgments

open CategoryTheory

section DepCategoryLift

def lift.{u₁, u₂, u₃, u₄}
  (D : DepCategoryData.{u₁, u₂, 0, 0}) :
    DepCategoryData.{u₁, u₂, max 1 u₃, max 1 u₄} :=
  { objT := D.objT
    morT := D.morT
    idT m := PULift.{u₃, 0} (D.idT m)
    compT f g h := PULift.{u₄, 0} (D.compT f g h) }

end DepCategoryLift

section CompletenessConditions

/-- Each object has an identity morphism (with witness). Uses `PSigma` to
    handle the case where `idT` is `Prop`-valued. This is a `Sort` because
    we need to extract witnesses constructively. -/
def DepCategoryData.IdExists.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃) :=
  ∀ (o : D.objT), PSigma (D.idT (o := o))

/-- Each composable pair has a composite (with witness). Uses `PSigma` to
    handle the case where `compT` is `Prop`-valued. This is a `Sort` because
    we need to extract witnesses constructively. -/
def DepCategoryData.CompExists.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₄) :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c),
    PSigma (D.compT f g)

/-- Identity and composition morphisms exist (with witnesses). This is a `Sort`
    because it contains the existence witnesses needed to extract identity
    and composition functions. -/
structure DepCategoryData.Exists.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃ u₄) where
  id : D.IdExists
  comp : D.CompExists

end CompletenessConditions

section CompleteSubcategory

/-- A `DepCategoryData` with existence witnesses for identity and composition.
    This is a `Sort` because it contains extractable witnesses. -/
structure DepCompleteObj.{u₁, u₂, u₃, u₄} : Type (max u₁ u₂ u₃ u₄)
    extends DepCategoryData.{u₁, u₂, u₃, u₄} where
  exists_ : toDepCategoryData.Exists

/-- Morphisms between `DepCompleteObj`s are `DepNatTransData` on the underlying
    `DepCategoryData`. The completeness witnesses need not be preserved
    point-wise; `DepNatTransData` already ensures that identities map to
    identities and compositions map to compositions. -/
abbrev DepCompleteObj.Hom.{u₁, u₂, u₃, u₄, v₁, v₂, v₃, v₄}
  (F : DepCompleteObj.{u₁, u₂, u₃, u₄}) (G : DepCompleteObj.{v₁, v₂, v₃, v₄}) :
  Type (max u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄) :=
    DepNatTransData.{u₁, u₂, u₃, u₄, v₁, v₂, v₃, v₄}
       F.toDepCategoryData
       G.toDepCategoryData

/-- Identity morphism for `DepCompleteObj`. -/
def DepCompleteObj.id (F : DepCompleteObj) : F.Hom F :=
  DepNatTransData.id F.toDepCategoryData

/-- Composition of morphisms for `DepCompleteObj`. -/
def DepCompleteObj.comp {F G H : DepCompleteObj}
    (α : F.Hom G) (β : G.Hom H) : F.Hom H :=
  DepNatTransData.comp α β

/-- Category instance for `DepCompleteObj`. Since morphisms are exactly
    `DepNatTransData` on the underlying `DepCategoryData`, the category laws
    hold by the same proofs as for `DepCategoryData`. -/
instance DepCompleteCat.{u₁, u₂, u₃, u₄} :
    SmallCategory.{max u₁ u₂ u₃ u₄} DepCompleteObj.{u₁, u₂, u₃, u₄} where
  Hom := DepCompleteObj.Hom
  id := DepCompleteObj.id
  comp := DepCompleteObj.comp
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- The forgetful functor from `DepCompleteObj` to `DepCategoryData`. -/
def DepCompleteObj.forget : DepCompleteObj ⥤ DepCategoryData where
  obj := DepCompleteObj.toDepCategoryData
  map := _root_.id
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The forgetful functor is faithful: if two morphisms in `DepCompleteObj`
    have equal underlying `DepNatTransData`, they are equal. This is trivial
    since morphisms are definitionally the same. -/
instance DepCompleteFaithful : DepCompleteObj.forget.Faithful where
  map_injective := _root_.id

/-- The forgetful functor is full: every morphism between the underlying
    `DepCategoryData`s lifts to a morphism between `DepCompleteObj`s.
    This is trivial since morphisms are definitionally the same. -/
instance DepCompleteFull : DepCompleteObj.forget.Full where
  map_surjective := fun f ↦ ⟨f, rfl⟩

/-- The forgetful functor is fully faithful. -/
def DepCompleteObj.forget.fullyFaithful : DepCompleteObj.forget.FullyFaithful :=
  Functor.FullyFaithful.mk (preimage := _root_.id) (map_preimage := fun _ ↦ rfl)

/-- If two `DepCompleteObj`s have isomorphic underlying `DepCategoryData`,
    then they are isomorphic as `DepCompleteObj`s. -/
def DepCompleteObj.isoOfDataIso {F G : DepCompleteObj}
    (i : F.toDepCategoryData ≅ G.toDepCategoryData) : F ≅ G where
  hom := i.hom
  inv := i.inv
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

/-- An isomorphism of `DepCompleteObj`s induces an isomorphism of the
    underlying `DepCategoryData`s. -/
def DepCompleteObj.dataIsoOfIso {F G : DepCompleteObj}
    (i : F ≅ G) : F.toDepCategoryData ≅ G.toDepCategoryData where
  hom := i.hom
  inv := i.inv
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

end CompleteSubcategory

section UniquenessConditions

/-- Each object has at most one identity morphism. -/
def DepCategoryData.IdUnique.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ (o : D.objT) (m₁ m₂ : D.morT o o), D.idT m₁ → D.idT m₂ → m₁ = m₂

/-- Each composable pair has at most one composite. -/
def DepCategoryData.CompUnique.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c) (h₁ h₂ : D.morT a c),
    D.compT f g h₁ → D.compT f g h₂ → h₁ = h₂

/-- Identity and composition morphisms are unique. This is a `Prop`. -/
structure DepCategoryData.Unique.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop where
  id : D.IdUnique
  comp : D.CompUnique

end UniquenessConditions

section CategoryLaws

/-- Left identity law: composing an identity on the left yields the original
    morphism. For any identity `i` on `a` and morphism `f : a → b`, if `h` is
    a composite of `i` and `f`, then `h = f`. -/
def DepCategoryData.LeftIdentity.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ {a b : D.objT} (i : D.morT a a) (f : D.morT a b) (h : D.morT a b),
    D.idT i → D.compT i f h → h = f

/-- Right identity law: composing an identity on the right yields the original
    morphism. For any morphism `f : a → b` and identity `i` on `b`, if `h` is
    a composite of `f` and `i`, then `h = f`. -/
def DepCategoryData.RightIdentity.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ {a b : D.objT} (f : D.morT a b) (i : D.morT b b) (h : D.morT a b),
    D.idT i → D.compT f i h → h = f

/-- Identity law: both left and right identity laws hold. -/
structure DepCategoryData.Identity.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop where
  left : D.LeftIdentity
  right : D.RightIdentity

/-- Associativity law: composition is associative. For morphisms `f : a → b`,
    `g : b → c`, `h : c → d`, if `fg` is `f ≫ g` and `gh` is `g ≫ h`, and
    `fgh₁` is `fg ≫ h` and `fgh₂` is `f ≫ gh`, then `fgh₁ = fgh₂`. -/
def DepCategoryData.Associativity.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ {a b c d : D.objT}
    (f : D.morT a b) (g : D.morT b c) (h : D.morT c d)
    (fg : D.morT a c) (gh : D.morT b d)
    (fgh₁ fgh₂ : D.morT a d),
    D.compT f g fg → D.compT g h gh →
    D.compT fg h fgh₁ → D.compT f gh fgh₂ →
    fgh₁ = fgh₂

/-- Category laws: identity and associativity laws hold. -/
structure DepCategoryData.CategoryLaws.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop where
  identity : D.Identity
  associativity : D.Associativity

end CategoryLaws

section SubsingletonConditions

/-- Each identity witness type is a subsingleton (at most one witness). -/
def DepCategoryData.IdSubsingleton.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ (o : D.objT) (m : D.morT o o), Subsingleton (D.idT m)

/-- Each composition witness type is a subsingleton (at most one witness). -/
def DepCategoryData.CompSubsingleton.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c) (h : D.morT a c),
    Subsingleton (D.compT f g h)

/-- Both identity and composition witness types are subsingletons. -/
structure DepCategoryData.WitnessSubsingleton.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop where
  id : D.IdSubsingleton
  comp : D.CompSubsingleton

end SubsingletonConditions

section IsCategoryLike

/-- The combined property that makes a `DepCategoryData` behave like a category.
    This combines uniqueness of id/comp, subsingleton witnesses, and the
    category laws (identity and associativity). -/
structure DepCategoryData.IsCategoryLike.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop where
  unique : D.Unique
  witnessSubsingleton : D.WitnessSubsingleton
  categoryLaws : D.CategoryLaws

end IsCategoryLike

section IntermediateProperties

/-- The property combining Unique and CategoryLaws (without WitnessSubsingleton).
    This is the intermediate step after applying the WitnessSubsingleton
    reflection. -/
structure DepCategoryData.UniqueAndCategoryLaws.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop where
  unique : D.Unique
  categoryLaws : D.CategoryLaws

/-- Coercion: IsCategoryLike implies UniqueAndCategoryLaws. -/
def DepCategoryData.IsCategoryLike.toUniqueAndCategoryLaws
    {D : DepCategoryData} (h : D.IsCategoryLike) : D.UniqueAndCategoryLaws where
  unique := h.unique
  categoryLaws := h.categoryLaws

/-- The CategoryLaws property alone (without Unique or WitnessSubsingleton).
    This is the intermediate step after applying the Unique reflection. -/
abbrev DepCategoryData.CategoryLawsOnly.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  D.CategoryLaws

/-- Coercion: UniqueAndCategoryLaws implies CategoryLawsOnly. -/
def DepCategoryData.UniqueAndCategoryLaws.toCategoryLawsOnly
    {D : DepCategoryData} (h : D.UniqueAndCategoryLaws) : D.CategoryLawsOnly :=
  h.categoryLaws

end IntermediateProperties

section DepCategoryCatDef

/-! ### Stacked Subcategory Chain

We define subcategories in a stacked manner:
1. `DepCompleteCL` = FullSubcategory of `DepCompleteObj` with `CategoryLaws`
2. `DepCompleteUCL` = FullSubcategory of `DepCompleteCL` with `Unique`
3. `DepCategoryCat` = FullSubcategory of `DepCompleteUCL` with `WitnessSubsingleton`

This gives us the inclusion chain with fully faithful functors automatically
from mathlib's `ObjectProperty.ι`. -/

/-- The property that a `DepCompleteObj` has CategoryLaws. -/
def HasCategoryLaws.{u₁, u₂, u₃, u₄} :
  ObjectProperty.{max u₁ u₂ u₃ u₄, max u₁ u₂ u₃ u₄}
    DepCompleteObj.{u₁, u₂, u₃, u₄} :=
  fun D ↦ D.toDepCategoryData.CategoryLaws

/-- The full subcategory of `DepCompleteObj` with CategoryLaws.
    This is the base of our stacked subcategory chain. -/
abbrev DepCompleteCL.{u₁, u₂, u₃, u₄} :=
  HasCategoryLaws.{u₁, u₂, u₃, u₄}.FullSubcategory

instance DepCompleteCLInstance.{u₁, u₂, u₃, u₄} :
  SmallCategory.{max u₁ u₂ u₃ u₄} DepCompleteCL.{u₁, u₂, u₃, u₄} :=
    ObjectProperty.FullSubcategory.category HasCategoryLaws.{u₁, u₂, u₃, u₄}

/-- The inclusion functor from `DepCompleteCL` to `DepCompleteObj`. -/
abbrev DepCompleteCL.ι.{u₁, u₂, u₃, u₄} :
    DepCompleteCL.{u₁, u₂, u₃, u₄} ⥤ DepCompleteObj.{u₁, u₂, u₃, u₄} :=
  HasCategoryLaws.ι

/-- Extract the underlying `DepCompleteObj` from a `DepCompleteCL`. -/
abbrev DepCompleteCL.toDepCompleteObj (D : DepCompleteCL) : DepCompleteObj := D.obj

/-- Extract the underlying `DepCategoryData` from a `DepCompleteCL`. -/
abbrev DepCompleteCL.toDepCategoryData (D : DepCompleteCL) : DepCategoryData :=
  D.obj.toDepCategoryData

/-- The property that a `DepCompleteCL` has Unique morphisms. -/
def DepCompleteCL.HasUnique.{u₁, u₂, u₃, u₄} :
  ObjectProperty.{max u₁ u₂ u₃ u₄, max u₁ u₂ u₃ u₄}
    DepCompleteCL.{u₁, u₂, u₃, u₄} :=
  fun D ↦ D.toDepCategoryData.Unique

/-- The full subcategory of `DepCompleteCL` with Unique morphisms. -/
abbrev DepCompleteUCL.{u₁, u₂, u₃, u₄} :=
  DepCompleteCL.HasUnique.{u₁, u₂, u₃, u₄}.FullSubcategory

instance DepCompleteUCLInstance.{u₁, u₂, u₃, u₄} :
  SmallCategory.{max u₁ u₂ u₃ u₄} DepCompleteUCL.{u₁, u₂, u₃, u₄} :=
    ObjectProperty.FullSubcategory.category DepCompleteCL.HasUnique.{u₁, u₂, u₃, u₄}

/-- The inclusion functor from `DepCompleteUCL` to `DepCompleteCL`. -/
abbrev DepCompleteUCL.ι.{u₁, u₂, u₃, u₄} :
    DepCompleteUCL.{u₁, u₂, u₃, u₄} ⥤ DepCompleteCL.{u₁, u₂, u₃, u₄} :=
  DepCompleteCL.HasUnique.ι

/-- Extract the underlying `DepCompleteCL` from a `DepCompleteUCL`. -/
abbrev DepCompleteUCL.toDepCompleteCL (D : DepCompleteUCL) : DepCompleteCL := D.obj

/-- Extract the underlying `DepCompleteObj` from a `DepCompleteUCL`. -/
abbrev DepCompleteUCL.toDepCompleteObj (D : DepCompleteUCL) : DepCompleteObj :=
  D.obj.obj

/-- Extract the underlying `DepCategoryData` from a `DepCompleteUCL`. -/
abbrev DepCompleteUCL.toDepCategoryData (D : DepCompleteUCL) : DepCategoryData :=
  D.obj.toDepCategoryData

/-- The property that a `DepCompleteUCL` has subsingleton witnesses. -/
def DepCompleteUCL.HasWitnessSubsingleton.{u₁, u₂, u₃, u₄} :
  ObjectProperty.{max u₁ u₂ u₃ u₄, max u₁ u₂ u₃ u₄}
    DepCompleteUCL.{u₁, u₂, u₃, u₄} :=
  fun D ↦ D.toDepCategoryData.WitnessSubsingleton

/-- The full subcategory of `DepCompleteUCL` with subsingleton witnesses.
    This is equivalent to `Cat`. -/
abbrev DepCategoryCat.{u₁, u₂, u₃, u₄} : Type (max u₁ u₂ u₃ u₄) :=
  DepCompleteUCL.HasWitnessSubsingleton.{u₁, u₂, u₃, u₄}.FullSubcategory

instance DepCategoryCatInstance.{u₁, u₂, u₃, u₄} :
  SmallCategory.{max u₁ u₂ u₃ u₄} DepCategoryCat.{u₁, u₂, u₃, u₄} :=
    ObjectProperty.FullSubcategory.category
      DepCompleteUCL.HasWitnessSubsingleton.{u₁, u₂, u₃, u₄}

/-- The inclusion functor from `DepCategoryCat` to `DepCompleteUCL`. -/
abbrev DepCategoryCat.ι.{u₁, u₂, u₃, u₄} :
    DepCategoryCat.{u₁, u₂, u₃, u₄} ⥤ DepCompleteUCL.{u₁, u₂, u₃, u₄} :=
  DepCompleteUCL.HasWitnessSubsingleton.ι

namespace DepCategoryCat

/-- Extract the underlying `DepCompleteUCL` from a `DepCategoryCat`. -/
abbrev toDepCompleteUCL (D : DepCategoryCat) : DepCompleteUCL := D.obj

/-- Extract the underlying `DepCompleteCL` from a `DepCategoryCat`. -/
abbrev toDepCompleteCL (D : DepCategoryCat) : DepCompleteCL := D.obj.obj

/-- Extract the underlying `DepCompleteObj` from a `DepCategoryCat`. -/
abbrev toDepCompleteObj (D : DepCategoryCat) : DepCompleteObj := D.obj.obj.obj

/-- Extract the underlying `DepCategoryData` from a `DepCategoryCat`. -/
abbrev toDepCategoryData (D : DepCategoryCat) : DepCategoryData :=
  D.obj.toDepCategoryData

/-- The composed inclusion functor from `DepCategoryCat` to `DepCompleteCL`. -/
abbrev ιCL : DepCategoryCat ⥤ DepCompleteCL := DepCategoryCat.ι ⋙ DepCompleteUCL.ι

/-- The composed inclusion functor from `DepCategoryCat` to `DepCompleteObj`. -/
abbrev ιComplete : DepCategoryCat ⥤ DepCompleteObj := ιCL ⋙ DepCompleteCL.ι

/-- The fully faithful inclusion functor from `DepCategoryCat` to
    `DepCategoryData`, obtained by composing with `DepCompleteObj.forget`. -/
def ιData : DepCategoryCat ⥤ DepCategoryData := ιComplete ⋙ DepCompleteObj.forget

/-- Extract the `IsCategoryLike` proof by combining the properties from each
    level of the stacked subcategories. -/
def isCategoryLike (D : DepCategoryCat) : D.toDepCategoryData.IsCategoryLike where
  unique := D.obj.property
  witnessSubsingleton := D.property
  categoryLaws := D.obj.obj.property

/-- The inclusion `DepCategoryCat.ι` is fully faithful. The preimage of a
    morphism is constructed by wrapping in `ObjectProperty.homMk`. -/
def ι_fullyFaithful : DepCategoryCat.ι.FullyFaithful :=
  Functor.FullyFaithful.mk
    (preimage := ObjectProperty.homMk)
    (map_preimage := fun _ ↦ rfl)

/-- The inclusion `DepCompleteUCL.ι` is fully faithful. -/
def DepCompleteUCL.ι_fullyFaithful : DepCompleteUCL.ι.FullyFaithful :=
  Functor.FullyFaithful.mk
    (preimage := ObjectProperty.homMk)
    (map_preimage := fun _ ↦ rfl)

/-- The inclusion `DepCompleteCL.ι` is fully faithful. -/
def DepCompleteCL.ι_fullyFaithful : DepCompleteCL.ι.FullyFaithful :=
  Functor.FullyFaithful.mk
    (preimage := ObjectProperty.homMk)
    (map_preimage := fun _ ↦ rfl)

/-- The composed inclusion `ιCL` is fully faithful. -/
def ιCL_fullyFaithful : ιCL.FullyFaithful :=
  ι_fullyFaithful.comp DepCompleteUCL.ι_fullyFaithful

/-- The composed inclusion `ιComplete` is fully faithful. -/
def ιComplete_fullyFaithful : ιComplete.FullyFaithful :=
  ιCL_fullyFaithful.comp DepCompleteCL.ι_fullyFaithful

/-- The inclusion `ιComplete` is faithful. -/
instance ιComplete_faithful : ιComplete.Faithful :=
  ιComplete_fullyFaithful.faithful

/-- The inclusion `ιComplete` is full. -/
instance ιComplete_full : ιComplete.Full :=
  ιComplete_fullyFaithful.full

/-- The composed inclusion `ιData` is fully faithful. -/
def ιData_fullyFaithful : ιData.FullyFaithful :=
  ιComplete_fullyFaithful.comp DepCompleteObj.forget.fullyFaithful

/-- The composed inclusion `ιData` is faithful. -/
instance ιData_faithful : ιData.Faithful :=
  ιData_fullyFaithful.faithful

/-- The composed inclusion `ιData` is full. -/
instance ιData_full : ιData.Full :=
  ιData_fullyFaithful.full

end DepCategoryCat

end DepCategoryCatDef

section BundledCategoryStructConversions

/-- Convert a `BundledCategoryStruct` to a `DepCategoryData`. -/
def bundledCategoryStructToDepDataProp.{u₁, u₂}
  (C : BundledCategoryStruct.{u₂, u₁}) :
    DepCategoryData.{u₁ + 1, u₂ + 1, 0, 0} :=
  { objT := C.α
    morT := C.str.Hom
    idT := fun {o} m ↦ m = C.str.id o
    compT := fun {_ _ _} f g h ↦ h = C.str.comp f g }

/-- Convert a `BundledCategoryStruct` to a `DepCategoryData` with lifted
    universe levels. -/
def bundledCategoryStructToDepData.{u₁, u₂, u₃, u₄}
  (C : BundledCategoryStruct.{u₂, u₁}) :
    DepCategoryData.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} :=
  lift.{u₁ + 1, u₂ + 1, u₃, u₄} (bundledCategoryStructToDepDataProp.{u₁, u₂} C)

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdExists`. -/
def bundledCategoryStructToDepData_idExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdExists := fun o ↦
  ⟨C.str.id o, PULift.up rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdUnique`. -/
theorem bundledCategoryStructToDepData_idUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdUnique := fun _ _ _ h₁ h₂ ↦
  h₁.down.trans h₂.down.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompExists`. -/
def bundledCategoryStructToDepData_compExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompExists := fun f g ↦
  ⟨C.str.comp f g, PULift.up rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompUnique`. -/
theorem bundledCategoryStructToDepData_compUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompUnique := fun _ _ _ _ p₁ p₂ ↦
  p₁.down.trans p₂.down.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `Exists`. -/
def bundledCategoryStructToDepData_exists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).Exists where
  id := bundledCategoryStructToDepData_idExists C
  comp := bundledCategoryStructToDepData_compExists C

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `Unique`. -/
def bundledCategoryStructToDepData_unique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).Unique where
  id := bundledCategoryStructToDepData_idUnique C
  comp := bundledCategoryStructToDepData_compUnique C

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdSubsingleton`. -/
theorem bundledCategoryStructToDepData_idSubsingleton (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdSubsingleton := fun _ _ ↦
  ⟨fun ⟨_⟩ ⟨_⟩ ↦ rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompSubsingleton`. -/
theorem bundledCategoryStructToDepData_compSubsingleton (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompSubsingleton := fun _ _ _ ↦
  ⟨fun ⟨_⟩ ⟨_⟩ ↦ rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `WitnessSubsingleton`. -/
def bundledCategoryStructToDepData_witnessSubsingleton (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).WitnessSubsingleton where
  id := bundledCategoryStructToDepData_idSubsingleton C
  comp := bundledCategoryStructToDepData_compSubsingleton C

/-- Convert a `BundledCategoryStruct` to a `DepCompleteObj`. -/
def bundledCategoryStructToDepCompleteObj.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
      DepCompleteObj.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} where
  toDepCategoryData := bundledCategoryStructToDepData C
  exists_ := bundledCategoryStructToDepData_exists C

end BundledCategoryStructConversions

section DepCompleteObjToCategoryStruct

/-- Given a `DepCompleteObj`, extract the identity morphism for an object
    using the existence witness. -/
def DepCompleteObj.idMor (D : DepCompleteObj)
    (o : D.toDepCategoryData.objT) : D.toDepCategoryData.morT o o :=
  (D.exists_.id o).fst

/-- The identity morphism satisfies `idT`. -/
def DepCompleteObj.idMor_spec (D : DepCompleteObj)
    (o : D.toDepCategoryData.objT) : D.toDepCategoryData.idT (D.idMor o) :=
  (D.exists_.id o).snd

/-- Given a `DepCompleteObj`, extract the composite morphism for a composable
    pair using the existence witness. -/
def DepCompleteObj.compMor (D : DepCompleteObj)
    {a b c : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b) (g : D.toDepCategoryData.morT b c) :
    D.toDepCategoryData.morT a c :=
  (D.exists_.comp f g).fst

/-- The composite morphism satisfies `compT`. -/
def DepCompleteObj.compMor_spec (D : DepCompleteObj)
    {a b c : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b) (g : D.toDepCategoryData.morT b c) :
    D.toDepCategoryData.compT f g (D.compMor f g) :=
  (D.exists_.comp f g).snd

/-- Convert a `DepCompleteObj` to a `CategoryStruct`. -/
def depCompleteObjToCategoryStruct (D : DepCompleteObj) :
    CategoryStruct D.toDepCategoryData.objT where
  Hom := D.toDepCategoryData.morT
  id := D.idMor
  comp := D.compMor

/-- Convert a `DepCompleteObj` to a `BundledCategoryStruct`. -/
def depCompleteObjToBundledCategoryStruct.{u₁, u₂, u₃, u₄}
    (D : DepCompleteObj.{u₁ + 1, u₂ + 1, u₃, u₄}) :
    BundledCategoryStruct.{u₂, u₁} :=
  @BundledCategoryStruct.of D.toDepCategoryData.objT (depCompleteObjToCategoryStruct D)

/-- Round-trip from `BundledCategoryStruct` to `DepCompleteObj` and back
    is the identity. -/
theorem bundledCategoryStruct_roundtrip.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
    depCompleteObjToBundledCategoryStruct.{u₁, u₂, max 1 u₃, max 1 u₄}
      (bundledCategoryStructToDepCompleteObj.{u₁, u₂, u₃, u₄} C) = C :=
  rfl

end DepCompleteObjToCategoryStruct

section CatEquivalence

/-!
## Universe level analysis for Cat ≃ DepCategoryCat

The equivalence relates:
- `Cat.{v, u}` (objects at `Type u`, morphisms at `Type v`)
- `DepCategoryCat.{u+1, v+1, max 1 w₃, max 1 w₄}` for arbitrary witness universes `w₃, w₄`

The `+1` shift occurs because `bundledCategoryStructToDepDataProp` embeds
`Type u` into `Type (u+1)` via universe cumulativity. This shift is consistent
and doesn't constrain which categories can be represented - any `Cat.{v, u}`
maps to `DepCategoryCat.{u+1, v+1, ...}`.
-/

/-- Convert a `Cat` object to a `BundledCategoryStruct`. -/
def catToBundledCategoryStruct.{u, v} (C : Cat.{v, u}) : BundledCategoryStruct.{v, u} :=
  ⟨C.α, C.str.toCategoryStruct⟩

/-- A `Cat` converted to `DepCategoryData` satisfies `LeftIdentity`. -/
theorem catToDepData_leftIdentity.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    (bundledCategoryStructToDepData.{u, v, w₃, w₄}
      (catToBundledCategoryStruct C)).LeftIdentity :=
  fun {_a _b} i f h hIdI hCompIfH ↦ by
    have heq_h : h = C.str.comp i f := hCompIfH.down
    have heq_i : i = C.str.id _a := hIdI.down
    simp only [heq_h, heq_i, Category.id_comp]

/-- A `Cat` converted to `DepCategoryData` satisfies `RightIdentity`. -/
theorem catToDepData_rightIdentity.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    (bundledCategoryStructToDepData.{u, v, w₃, w₄}
      (catToBundledCategoryStruct C)).RightIdentity :=
  fun {_a _b} f i h hIdI hCompFiH ↦ by
    have heq_h : h = C.str.comp f i := hCompFiH.down
    have heq_i : i = C.str.id _b := hIdI.down
    simp only [heq_h, heq_i, Category.comp_id]

/-- A `Cat` converted to `DepCategoryData` satisfies `Identity`. -/
def catToDepData_identity.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    (bundledCategoryStructToDepData.{u, v, w₃, w₄}
      (catToBundledCategoryStruct C)).Identity where
  left := catToDepData_leftIdentity C
  right := catToDepData_rightIdentity C

/-- A `Cat` converted to `DepCategoryData` satisfies `Associativity`. -/
theorem catToDepData_associativity.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    (bundledCategoryStructToDepData.{u, v, w₃, w₄}
      (catToBundledCategoryStruct C)).Associativity :=
  fun {_a _b _c _d} f g h fg gh fgh₁ fgh₂ hFG hGH hFGH hFGH' ↦ by
    have hfg : fg = C.str.comp f g := hFG.down
    have hgh : gh = C.str.comp g h := hGH.down
    have hfgh1 : fgh₁ = C.str.comp fg h := hFGH.down
    have hfgh2 : fgh₂ = C.str.comp f gh := hFGH'.down
    simp only [hfg, hgh, hfgh1, hfgh2, Category.assoc]

/-- A `Cat` converted to `DepCategoryData` satisfies `CategoryLaws`. -/
def catToDepData_categoryLaws.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    (bundledCategoryStructToDepData.{u, v, w₃, w₄}
      (catToBundledCategoryStruct C)).CategoryLaws where
  identity := catToDepData_identity C
  associativity := catToDepData_associativity C

/-- A `Cat` converted to `DepCategoryData` satisfies `IsCategoryLike`. -/
def catToDepData_isCategoryLike.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    (bundledCategoryStructToDepData.{u, v, w₃, w₄}
      (catToBundledCategoryStruct C)).IsCategoryLike where
  unique := bundledCategoryStructToDepData_unique (catToBundledCategoryStruct C)
  witnessSubsingleton :=
    bundledCategoryStructToDepData_witnessSubsingleton (catToBundledCategoryStruct C)
  categoryLaws := catToDepData_categoryLaws C

/-- Convert a `Cat.{v, u}` to a `DepCompleteObj.{u+1, v+1, max 1 w₃, max 1 w₄}`. -/
def catToDepCompleteObj.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    DepCompleteObj.{u + 1, v + 1, max 1 w₃, max 1 w₄} :=
  bundledCategoryStructToDepCompleteObj (catToBundledCategoryStruct C)

/-- Convert a `Cat.{v, u}` to a `DepCompleteCL.{u+1, v+1, max 1 w₃, max 1 w₄}`. -/
def catToDepCompleteCL.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    DepCompleteCL.{u + 1, v + 1, max 1 w₃, max 1 w₄} where
  obj := catToDepCompleteObj.{u, v, w₃, w₄} C
  property := catToDepData_categoryLaws.{u, v, w₃, w₄} C

/-- Convert a `Cat.{v, u}` to a `DepCompleteUCL.{u+1, v+1, max 1 w₃, max 1 w₄}`. -/
def catToDepCompleteUCL.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    DepCompleteUCL.{u + 1, v + 1, max 1 w₃, max 1 w₄} where
  obj := catToDepCompleteCL.{u, v, w₃, w₄} C
  property := bundledCategoryStructToDepData_unique (catToBundledCategoryStruct C)

/-- Convert a `Cat.{v, u}` to a `DepCategoryCat.{u+1, v+1, max 1 w₃, max 1 w₄}`. -/
def catToDepCategoryCat.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄} where
  obj := catToDepCompleteUCL.{u, v, w₃, w₄} C
  property := bundledCategoryStructToDepData_witnessSubsingleton (catToBundledCategoryStruct C)

/-- Given a `DepCategoryCat`, the extracted `CategoryStruct` satisfies `id_comp`. -/
theorem depCategoryCat_id_comp.{u₁, u₂, u₃, u₄} (D : DepCategoryCat.{u₁, u₂, u₃, u₄})
    {a b : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b) :
    D.toDepCompleteObj.compMor (D.toDepCompleteObj.idMor a) f = f := by
  have hId := D.toDepCompleteObj.idMor_spec a
  have hComp := D.toDepCompleteObj.compMor_spec (D.toDepCompleteObj.idMor a) f
  exact D.isCategoryLike.categoryLaws.identity.left _ f _ hId hComp

/-- Given a `DepCategoryCat`, the extracted `CategoryStruct` satisfies `comp_id`. -/
theorem depCategoryCat_comp_id.{u₁, u₂, u₃, u₄} (D : DepCategoryCat.{u₁, u₂, u₃, u₄})
    {a b : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b) :
    D.toDepCompleteObj.compMor f (D.toDepCompleteObj.idMor b) = f := by
  have hId := D.toDepCompleteObj.idMor_spec b
  have hComp := D.toDepCompleteObj.compMor_spec f (D.toDepCompleteObj.idMor b)
  exact D.isCategoryLike.categoryLaws.identity.right f _ _ hId hComp

/-- Given a `DepCategoryCat`, the extracted `CategoryStruct` satisfies `assoc`. -/
theorem depCategoryCat_assoc.{u₁, u₂, u₃, u₄} (D : DepCategoryCat.{u₁, u₂, u₃, u₄})
    {a b c d : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b)
    (g : D.toDepCategoryData.morT b c)
    (h : D.toDepCategoryData.morT c d) :
    D.toDepCompleteObj.compMor (D.toDepCompleteObj.compMor f g) h =
    D.toDepCompleteObj.compMor f (D.toDepCompleteObj.compMor g h) := by
  have hFG := D.toDepCompleteObj.compMor_spec f g
  have hGH := D.toDepCompleteObj.compMor_spec g h
  have hFGH := D.toDepCompleteObj.compMor_spec (D.toDepCompleteObj.compMor f g) h
  have hFGH' := D.toDepCompleteObj.compMor_spec f (D.toDepCompleteObj.compMor g h)
  exact D.isCategoryLike.categoryLaws.associativity f g h _ _ _ _ hFG hGH hFGH hFGH'

/-- Convert a `DepCategoryCat.{u+1, v+1, w₃, w₄}` to a `Category` instance. -/
def depCategoryCatToCategory.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, w₃, w₄}) :
    Category D.toDepCategoryData.objT where
  Hom := D.toDepCategoryData.morT
  id := D.toDepCompleteObj.idMor
  comp := D.toDepCompleteObj.compMor
  id_comp := depCategoryCat_id_comp D
  comp_id := depCategoryCat_comp_id D
  assoc := depCategoryCat_assoc D

/-- Convert a `DepCategoryCat.{u+1, v+1, w₃, w₄}` to a `Cat.{v, u}`. -/
def depCategoryCatToCat.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, w₃, w₄}) : Cat.{v, u} :=
  @Cat.of D.toDepCategoryData.objT (depCategoryCatToCategory D)

/-- Round-trip from `Cat.{v, u}` to `DepCategoryCat` and back is the identity. -/
theorem cat_roundtrip.{u, v, w₃, w₄} (C : Cat.{v, u}) :
    depCategoryCatToCat.{u, v, max 1 w₃, max 1 w₄}
      (catToDepCategoryCat.{u, v, w₃, w₄} C) = C :=
  rfl

/-- Extract the underlying `DepNatTransData` from a `DepCategoryCat` morphism.
    Morphisms are nested through three layers of `ObjectProperty.FullSubcategory`. -/
def homToNatTrans {D E : DepCategoryCat}
    (f : D ⟶ E) : DepNatTransData D.toDepCategoryData E.toDepCategoryData :=
  f.hom.hom.hom

/-- Convert a `Cat.Hom` morphism to a morphism in `DepCategoryCat`.
    This constructs the nested `ObjectProperty.homMk` structure. -/
def catHomToDepCategoryCatHom.{u, v, w₃, w₄} {C D : Cat.{v, u}}
    (F : C ⟶ D) :
    catToDepCategoryCat.{u, v, w₃, w₄} C ⟶
    catToDepCategoryCat.{u, v, w₃, w₄} D :=
  let natTrans : DepNatTransData
      (catToDepCompleteObj C).toDepCategoryData
      (catToDepCompleteObj D).toDepCategoryData :=
    { appObj := F.toFunctor.obj
      appMor := F.toFunctor.map
      appId := fun {_o _m} ⟨h⟩ ↦ ⟨h ▸ F.toFunctor.map_id _o⟩
      appComp := fun {_a _b _c _f _g _h} ⟨hcomp⟩ ↦ ⟨hcomp ▸ F.toFunctor.map_comp _f _g⟩ }
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk natTrans))

/-- The functor from `Cat` to `DepCategoryCat`. -/
def catToDepCategoryCatFunctor.{u, v, w₃, w₄} :
    Cat.{v, u} ⥤ DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄} where
  obj := catToDepCategoryCat
  map := catHomToDepCategoryCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from `DepCategoryCat` to `Cat`. -/
def depCategoryCatToCatFunctor.{u, v, w₃, w₄} :
    DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄} ⥤ Cat.{v, u} where
  obj := depCategoryCatToCat
  map {D E} f := {
    toFunctor := {
      obj := (homToNatTrans f).appObj
      map := (homToNatTrans f).appMor
      map_id X := by
        have hId := D.toDepCompleteObj.idMor_spec X
        have hApp := (homToNatTrans f).appId hId
        exact E.isCategoryLike.unique.id _ _ _ hApp (E.toDepCompleteObj.idMor_spec _)
      map_comp {_X _Y _Z} g h := by
        have hComp := D.toDepCompleteObj.compMor_spec g h
        have hApp := (homToNatTrans f).appComp hComp
        exact E.isCategoryLike.unique.comp _ _ _ _ hApp
          (E.toDepCompleteObj.compMor_spec _ _)
    }
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The composition `catToDepCategoryCatFunctor ⋙ depCategoryCatToCatFunctor` is
    naturally isomorphic to the identity on `Cat`. -/
def catDepCategoryCatUnit.{u, v, w₃, w₄} :
    𝟭 Cat.{v, u} ≅
    catToDepCategoryCatFunctor.{u, v, w₃, w₄} ⋙
    depCategoryCatToCatFunctor.{u, v, w₃, w₄} :=
  NatIso.ofComponents (fun C ↦ eqToIso (cat_roundtrip C).symm) (by intros; rfl)

/-- The underlying `DepNatTransData` for the counit hom from round-tripped to `D`. -/
def depCategoryCatCounitHomNatTrans.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    DepNatTransData
      (catToDepCategoryCat (depCategoryCatToCat D)).toDepCategoryData
      D.toDepCategoryData :=
  { appObj := _root_.id
    appMor := _root_.id
    appId := fun {_o _m} ⟨hEq⟩ ↦ hEq ▸ D.toDepCompleteObj.idMor_spec _o
    appComp := fun {_a _b _c _f _g _h} ⟨hEq⟩ ↦
      hEq ▸ D.toDepCompleteObj.compMor_spec _f _g }

/-- The counit hom wrapped in nested `ObjectProperty.homMk` for `DepCompleteUCL`. -/
def depCategoryCatCounitHom.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    (catToDepCategoryCat (depCategoryCatToCat D)).obj ⟶ D.obj :=
  ObjectProperty.homMk (ObjectProperty.homMk (depCategoryCatCounitHomNatTrans D))

/-- The underlying `DepNatTransData` for the counit inv from `D` to round-tripped. -/
def depCategoryCatCounitInvNatTrans.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    DepNatTransData
      D.toDepCategoryData
      (catToDepCategoryCat (depCategoryCatToCat D)).toDepCategoryData :=
  { appObj := _root_.id
    appMor := _root_.id
    appId := fun {o m} hId ↦ ⟨D.isCategoryLike.unique.id o m (D.toDepCompleteObj.idMor o)
                                hId (D.toDepCompleteObj.idMor_spec o)⟩
    appComp := fun {_a _b _c f g h} hComp ↦
      ⟨D.isCategoryLike.unique.comp f g h (D.toDepCompleteObj.compMor f g)
         hComp (D.toDepCompleteObj.compMor_spec f g)⟩ }

/-- The counit inv wrapped in nested `ObjectProperty.homMk` for `DepCompleteUCL`. -/
def depCategoryCatCounitInv.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    D.obj ⟶ (catToDepCategoryCat (depCategoryCatToCat D)).obj :=
  ObjectProperty.homMk (ObjectProperty.homMk (depCategoryCatCounitInvNatTrans D))

/-- The composition `inv ≫ hom` is identity for the counit at the `DepNatTransData`
    level. -/
theorem depCategoryCatCounit_inv_hom_natTrans.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    DepNatTransData.comp (depCategoryCatCounitInvNatTrans D)
                         (depCategoryCatCounitHomNatTrans D) =
    DepNatTransData.id D.toDepCategoryData := by
  apply DepNatTransData.ext
  · rfl
  · exact HEq.rfl
  · apply heq_of_eq
    funext o m hId
    simp only [DepNatTransData.comp, DepNatTransData.id,
               depCategoryCatCounitHomNatTrans, depCategoryCatCounitInvNatTrans, id]
    haveI : Subsingleton (D.toDepCategoryData.idT m) :=
      D.property.id o m
    exact Subsingleton.elim _ _
  · apply heq_of_eq
    funext a b c f g h hComp
    simp only [DepNatTransData.comp, DepNatTransData.id,
               depCategoryCatCounitHomNatTrans, depCategoryCatCounitInvNatTrans, id]
    haveI : Subsingleton (D.toDepCategoryData.compT f g h) :=
      D.property.comp f g h
    exact Subsingleton.elim _ _

/-- The composition `inv ≫ hom` is identity for the counit. -/
theorem depCategoryCatCounit_inv_hom.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    depCategoryCatCounitInv D ≫ depCategoryCatCounitHom D = 𝟙 D.obj := by
  simp only [depCategoryCatCounitInv, depCategoryCatCounitHom]
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
             ObjectProperty.homMk_hom]
  exact depCategoryCatCounit_inv_hom_natTrans D

/-- The counit component isomorphism for `D : DepCategoryCat` as an isomorphism
    of `DepCompleteUCL`. -/
def depCategoryCatCounitObjIso.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    (catToDepCategoryCat (depCategoryCatToCat D)).obj ≅ D.obj where
  hom := depCategoryCatCounitHom D
  inv := depCategoryCatCounitInv D
  hom_inv_id := rfl
  inv_hom_id := depCategoryCatCounit_inv_hom D

/-- The counit component isomorphism for `D : DepCategoryCat`. -/
def depCategoryCatCounitIso.{u, v, w₃, w₄}
    (D : DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄}) :
    (depCategoryCatToCatFunctor.{u, v, w₃, w₄} ⋙
     catToDepCategoryCatFunctor.{u, v, w₃, w₄}).obj D ≅ D where
  hom := ObjectProperty.homMk (depCategoryCatCounitObjIso D).hom
  inv := ObjectProperty.homMk (depCategoryCatCounitObjIso D).inv
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
               ObjectProperty.homMk_hom]
    exact (depCategoryCatCounitObjIso D).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
               ObjectProperty.homMk_hom]
    exact (depCategoryCatCounitObjIso D).inv_hom_id

/-- The composition `depCategoryCatToCatFunctor ⋙ catToDepCategoryCatFunctor` is
    naturally isomorphic to the identity on `DepCategoryCat`. -/
def depCategoryCatCounit.{u, v, w₃, w₄} :
    depCategoryCatToCatFunctor.{u, v, w₃, w₄} ⋙
    catToDepCategoryCatFunctor.{u, v, w₃, w₄} ≅
    𝟭 DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄} :=
  NatIso.ofComponents depCategoryCatCounitIso (fun {D E} f ↦ by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
               ObjectProperty.FullSubcategory.comp_hom]
    apply DepNatTransData.ext
    · rfl
    · exact HEq.rfl
    · apply heq_of_eq
      funext o m hId
      exact @Subsingleton.elim (E.toDepCategoryData.idT ((homToNatTrans f).appMor m))
        (E.property.id ((homToNatTrans f).appObj o) ((homToNatTrans f).appMor m)) _ _
    · apply heq_of_eq
      funext a b c mf mg mh hComp
      exact @Subsingleton.elim
        (E.toDepCategoryData.compT ((homToNatTrans f).appMor mf)
          ((homToNatTrans f).appMor mg) ((homToNatTrans f).appMor mh))
        (E.property.comp ((homToNatTrans f).appMor mf)
          ((homToNatTrans f).appMor mg) ((homToNatTrans f).appMor mh)) _ _)

/-- The functor-unitIso-comp triangle identity for the Cat ≌ DepCategoryCat
    equivalence. -/
theorem catDepCategoryCatEquiv_functor_unitIso_comp.{u, v, w₃, w₄} (X : Cat.{v, u}) :
    catToDepCategoryCatFunctor.{u, v, w₃, w₄}.map
      (catDepCategoryCatUnit.{u, v, max 1 w₃, max 1 w₄}.hom.app X) ≫
    depCategoryCatCounit.{u, v, w₃, w₄}.hom.app
      (catToDepCategoryCatFunctor.{u, v, w₃, w₄}.obj X) =
    𝟙 (catToDepCategoryCatFunctor.{u, v, w₃, w₄}.obj X) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  simp only [Functor.comp_obj, catDepCategoryCatUnit, NatIso.ofComponents_hom_app,
             depCategoryCatCounit, Functor.id_obj, depCategoryCatCounitIso,
             catToDepCategoryCatFunctor, catHomToDepCategoryCatHom,
             ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
             ObjectProperty.FullSubcategory.id_hom]
  apply DepNatTransData.ext
  · rfl
  · exact HEq.rfl
  · apply heq_of_eq
    funext o m hId
    exact @Subsingleton.elim
      ((catToDepCategoryCat X).toDepCategoryData.idT m)
      ((catToDepCategoryCat X).property.id o m) _ _
  · apply heq_of_eq
    funext a b c mf mg mh hComp
    exact @Subsingleton.elim
      ((catToDepCategoryCat X).toDepCategoryData.compT mf mg mh)
      ((catToDepCategoryCat X).property.comp mf mg mh) _ _

/-- The equivalence of categories between `Cat` and `DepCategoryCat`. -/
def catDepCategoryCatEquiv.{u, v, w₃, w₄} :
    Cat.{v, u} ≌ DepCategoryCat.{u + 1, v + 1, max 1 w₃, max 1 w₄} where
  functor := catToDepCategoryCatFunctor
  inverse := depCategoryCatToCatFunctor
  unitIso := catDepCategoryCatUnit
  counitIso := depCategoryCatCounit
  functor_unitIso_comp X := catDepCategoryCatEquiv_functor_unitIso_comp X

/-- The functor `catToDepCategoryCatFunctor` is fully faithful, derived from the
    equivalence. -/
def catToDepCategoryCatFunctor.fullyFaithful.{u, v, w₃, w₄} :
    catToDepCategoryCatFunctor.{u, v, max 1 w₃, max 1 w₄}.FullyFaithful :=
  catDepCategoryCatEquiv.fullyFaithfulFunctor

instance catToDepCategoryCatFunctor.faithful.{u, v, w₃, w₄} :
    catToDepCategoryCatFunctor.{u, v, max 1 w₃, max 1 w₄}.Faithful :=
  catDepCategoryCatEquiv.faithful_functor

instance catToDepCategoryCatFunctor.full.{u, v, w₃, w₄} :
    catToDepCategoryCatFunctor.{u, v, max 1 w₃, max 1 w₄}.Full :=
  catDepCategoryCatEquiv.full_functor

/-- The functor `depCategoryCatToCatFunctor` is fully faithful, derived from the
    equivalence. -/
def depCategoryCatToCatFunctor.fullyFaithful.{u, v, w₃, w₄} :
    depCategoryCatToCatFunctor.{u, v, max 1 w₃, max 1 w₄}.FullyFaithful :=
  catDepCategoryCatEquiv.fullyFaithfulInverse

instance depCategoryCatToCatFunctor.faithful.{u, v, w₃, w₄} :
    depCategoryCatToCatFunctor.{u, v, max 1 w₃, max 1 w₄}.Faithful :=
  catDepCategoryCatEquiv.faithful_inverse

instance depCategoryCatToCatFunctor.full.{u, v, w₃, w₄} :
    depCategoryCatToCatFunctor.{u, v, max 1 w₃, max 1 w₄}.Full :=
  catDepCategoryCatEquiv.full_inverse

end CatEquivalence

section DepCategoryCatReflection

def DepCategoryCatAsCatObj.{u₁, u₂, u₃, u₄} :
  Cat.{max u₁ u₂ u₃ u₄, max u₁ u₂ u₃ u₄} :=
    Cat.of.{max u₁ u₂ u₃ u₄, max u₁ u₂ u₃ u₄} DepCategoryCat.{u₁, u₂, u₃, u₄}

def DepCategoryCatAsDepCatObj.{u₁, u₂, u₃, u₄, w₃, w₄} :
  DepCategoryCat.{max u₁ u₂ u₃ u₄ + 1, max u₁ u₂ u₃ u₄ + 1, max 1 w₃, max 1 w₄} :=
    catToDepCategoryCat.{max u₁ u₂ u₃ u₄, max u₁ u₂ u₃ u₄, w₃, w₄}
      DepCategoryCatAsCatObj.{u₁, u₂, u₃, u₄}

end DepCategoryCatReflection

end CategoryJudgments

end GebLean
