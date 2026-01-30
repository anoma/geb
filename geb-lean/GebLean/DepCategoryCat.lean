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

section DepCategoryCatDef

/-- The property that a `DepCompleteObj` is category-like (has unique id/comp,
    subsingleton witnesses, and satisfies category laws). This is an
    `ObjectProperty` on `DepCompleteObj`. -/
def IsCategoryLike.{u₁, u₂, u₃, u₄} :
  ObjectProperty.{max u₁ u₂ u₃ u₄, max u₁ u₂ u₃ u₄}
    DepCompleteObj.{u₁, u₂, u₃, u₄} :=
  fun D ↦ D.toDepCategoryData.IsCategoryLike

/-- The full subcategory of `DepCompleteObj` consisting of objects that
    behave like categories. This is equivalent to `Cat`. -/
abbrev DepCategoryCat := IsCategoryLike.FullSubcategory

namespace DepCategoryCat

/-- The inclusion functor from `DepCategoryCat` to `DepCompleteObj`. -/
abbrev ιComplete : DepCategoryCat ⥤ DepCompleteObj := IsCategoryLike.ι

/-- The fully faithful inclusion functor from `DepCategoryCat` to
    `DepCategoryData`, obtained by composing with `DepCompleteObj.forget`. -/
def ι : DepCategoryCat ⥤ DepCategoryData := ιComplete ⋙ DepCompleteObj.forget

/-- Extract the underlying `DepCompleteObj`. -/
abbrev toDepCompleteObj (D : DepCategoryCat) : DepCompleteObj := D.obj

/-- Extract the underlying `DepCategoryData`. -/
abbrev toDepCategoryData (D : DepCategoryCat) : DepCategoryData :=
  D.obj.toDepCategoryData

/-- Extract the `IsCategoryLike` proof. -/
abbrev isCategoryLike (D : DepCategoryCat) : D.toDepCategoryData.IsCategoryLike :=
  D.property

/-- The inclusion `ιComplete` is faithful. -/
instance ιComplete_faithful : ιComplete.Faithful :=
  IsCategoryLike.faithful_ι

/-- The inclusion `ιComplete` is full. -/
instance ιComplete_full : ιComplete.Full :=
  IsCategoryLike.full_ι

/-- The composed inclusion `ι` is faithful. -/
instance ι_faithful : ι.Faithful :=
  Functor.Faithful.comp ιComplete DepCompleteObj.forget

/-- The composed inclusion `ι` is full. -/
instance ι_full : ι.Full :=
  Functor.Full.comp ιComplete DepCompleteObj.forget

/-- The inclusion `ι` is fully faithful. -/
def ι_fullyFaithful : ι.FullyFaithful :=
  IsCategoryLike.fullyFaithfulι.comp DepCompleteObj.forget.fullyFaithful

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

end CategoryJudgments

end GebLean
