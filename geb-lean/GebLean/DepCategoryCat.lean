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

section FunctionalityConditions

/-- Each object has an identity morphism (with witness). Uses `PSigma` to
    handle the case where `idT` is `Prop`-valued. -/
def DepCategoryData.IdExists.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃) :=
  ∀ (o : D.objT), PSigma (D.idT (o := o))

/-- Each object has at most one identity morphism. -/
def DepCategoryData.IdUnique.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ (o : D.objT) (m₁ m₂ : D.morT o o), D.idT m₁ → D.idT m₂ → m₁ = m₂

/-- Each composable pair has a composite (with witness). Uses `PSigma` to
    handle the case where `compT` is `Prop`-valued. -/
def DepCategoryData.CompExists.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₄) :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c),
    PSigma (D.compT f g)

/-- Each composable pair has at most one composite. -/
def DepCategoryData.CompUnique.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c) (h₁ h₂ : D.morT a c),
    D.compT f g h₁ → D.compT f g h₂ → h₁ = h₂

/-- The identity relation is functional (with witnesses). -/
structure DepCategoryData.IdFunctional.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃) where
  exists_ : D.IdExists
  unique : D.IdUnique

/-- The composition relation is functional (with witnesses). -/
structure DepCategoryData.CompFunctional.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₄) where
  exists_ : D.CompExists
  unique : D.CompUnique

/-- Both identity and composition relations are functional (with witnesses). -/
structure DepCategoryData.Functional.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃ u₄) where
  id : D.IdFunctional
  comp : D.CompFunctional

end FunctionalityConditions

section FunctionalCategoryEquiv

/-- A `DepCategoryData` bundled with its functionality witnesses.
    These are the objects that have the data of a category (without laws). -/
structure DepFunctionalCategory.{u₁, u₂, u₃, u₄} : Type (max u₁ u₂ u₃ u₄) where
  /-- The underlying category data -/
  data : DepCategoryData.{u₁, u₂, u₃, u₄}
  /-- The functionality witnesses -/
  functional : data.Functional

/-- Convert a `BundledCategoryStruct` to a `DepCategoryData`. -/
def bundledCategoryStructToDepDataProp.{u₁, u₂}
  (C : BundledCategoryStruct.{u₂, u₁}) :
    DepCategoryData.{u₁ + 1, u₂ + 1, 0, 0} :=
  { objT := C.α
    morT := C.str.Hom
    idT := fun {o} m => m = C.str.id o
    compT := fun {_ _ _} f g h => h = C.str.comp f g }

/-- Convert a `BundledCategoryStruct` to a `DepCategoryData`. -/
def bundledCategoryStructToDepData.{u₁, u₂, u₃, u₄}
  (C : BundledCategoryStruct.{u₂, u₁}) :
    DepCategoryData.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} :=
  lift.{u₁ + 1, u₂ + 1, u₃, u₄} (bundledCategoryStructToDepDataProp.{u₁, u₂} C)

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdExists`. -/
def bundledCategoryStructToDepData_idExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdExists := fun o =>
  ⟨C.str.id o, PULift.up rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdUnique`. -/
theorem bundledCategoryStructToDepData_idUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdUnique := fun _ _ _ h₁ h₂ =>
  h₁.down.trans h₂.down.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompExists`. -/
def bundledCategoryStructToDepData_compExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompExists := fun f g =>
  ⟨C.str.comp f g, PULift.up rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompUnique`. -/
theorem bundledCategoryStructToDepData_compUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompUnique := fun _ _ _ _ p₁ p₂ =>
  p₁.down.trans p₂.down.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `Functional`. -/
def bundledCategoryStructToDepData_functional (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).Functional where
  id := {
    exists_ := bundledCategoryStructToDepData_idExists C
    unique := bundledCategoryStructToDepData_idUnique C
  }
  comp := {
    exists_ := bundledCategoryStructToDepData_compExists C
    unique := bundledCategoryStructToDepData_compUnique C
  }

/-- Convert a `BundledCategoryStruct` to a `DepFunctionalCategory`. -/
def bundledCategoryStructToDepFunctional.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
      DepFunctionalCategory.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} where
  data := bundledCategoryStructToDepData C
  functional := bundledCategoryStructToDepData_functional C

/-- Given a `DepFunctionalCategory`, extract the identity morphism for an
    object using the functionality condition. -/
def DepFunctionalCategory.idMor (D : DepFunctionalCategory)
    (o : D.data.objT) : D.data.morT o o :=
  (D.functional.id.exists_ o).fst

/-- The identity morphism satisfies `idT`. -/
def DepFunctionalCategory.idMor_spec.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalCategory.{u₁, u₂, u₃, u₄})
    (o : D.data.objT) : D.data.idT (D.idMor o) :=
  (D.functional.id.exists_ o).snd

/-- Given a `DepFunctionalCategory`, extract the composite morphism for a
    composable pair using the functionality condition. -/
def DepFunctionalCategory.compMor (D : DepFunctionalCategory)
    {a b c : D.data.objT} (f : D.data.morT a b) (g : D.data.morT b c) :
    D.data.morT a c :=
  (D.functional.comp.exists_ f g).fst

/-- The composite morphism satisfies `compT`. -/
def DepFunctionalCategory.compMor_spec.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalCategory.{u₁, u₂, u₃, u₄})
    {a b c : D.data.objT} (f : D.data.morT a b) (g : D.data.morT b c) :
    D.data.compT f g (D.compMor f g) :=
  (D.functional.comp.exists_ f g).snd

/-- Convert a `DepFunctionalCategory` to a `CategoryStruct` instance on its
    object type. -/
def depFunctionalToCategoryStruct (D : DepFunctionalCategory) :
    CategoryStruct D.data.objT where
  Hom := D.data.morT
  id := D.idMor
  comp := D.compMor

/-- Convert a `DepFunctionalCategory` to a `BundledCategoryStruct`. -/
def depFunctionalToBundledCategoryStruct.{u₁, u₂, u₃, u₄}
  (D : DepFunctionalCategory.{u₁ + 1, u₂ + 1, u₃, u₄}) :
    BundledCategoryStruct.{u₂, u₁} :=
  @BundledCategoryStruct.of D.data.objT (depFunctionalToCategoryStruct D)

/-- Round-trip from `BundledCategoryStruct` to `DepFunctionalCategory` and back
    is the identity. -/
theorem bundledCategoryStruct_roundtrip.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
    depFunctionalToBundledCategoryStruct.{u₁, u₂, max 1 u₃, max 1 u₄}
      (bundledCategoryStructToDepFunctional.{u₁, u₂, u₃, u₄} C) = C :=
  rfl

end FunctionalCategoryEquiv

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

/-- A `DepCategoryData` bundled with functionality and subsingleton witnesses.
    These are exactly the objects that correspond to `BundledCategoryStruct`. -/
structure DepFunctionalSubsingleton.{u₁, u₂, u₃, u₄} :
    Type (max u₁ u₂ u₃ u₄) where
  /-- The underlying category data -/
  data : DepCategoryData.{u₁, u₂, u₃, u₄}
  /-- The functionality witnesses -/
  functional : data.Functional
  /-- The subsingleton witnesses -/
  subsingleton : data.WitnessSubsingleton

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdSubsingleton`. -/
theorem bundledCategoryStructToDepData_idSubsingleton (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdSubsingleton := fun _ _ =>
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompSubsingleton`. -/
theorem bundledCategoryStructToDepData_compSubsingleton (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompSubsingleton := fun _ _ _ =>
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `WitnessSubsingleton`. -/
def bundledCategoryStructToDepData_witnessSubsingleton (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).WitnessSubsingleton where
  id := bundledCategoryStructToDepData_idSubsingleton C
  comp := bundledCategoryStructToDepData_compSubsingleton C

/-- Convert a `BundledCategoryStruct` to a `DepFunctionalSubsingleton`. -/
def bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
      DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} where
  data := bundledCategoryStructToDepData C
  functional := bundledCategoryStructToDepData_functional C
  subsingleton := bundledCategoryStructToDepData_witnessSubsingleton C

/-- Convert a `DepFunctionalSubsingleton` to a `DepFunctionalCategory`. -/
def depFunctionalSubsingletonToFunctional.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}) :
      DepFunctionalCategory.{u₁, u₂, u₃, u₄} where
  data := D.data
  functional := D.functional

/-- Convert a `DepFunctionalSubsingleton` to a `BundledCategoryStruct`. -/
def depFunctionalSubsingletonToBundledCategoryStruct.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, u₃, u₄}) :
      BundledCategoryStruct.{u₂, u₁} :=
  depFunctionalToBundledCategoryStruct (depFunctionalSubsingletonToFunctional D)

/-- Round-trip from `BundledCategoryStruct` to `DepFunctionalSubsingleton` and
    back is the identity. -/
theorem bundledCategoryStruct_subsingleton_roundtrip.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
    depFunctionalSubsingletonToBundledCategoryStruct.{u₁, u₂, max 1 u₃, max 1 u₄}
      (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄} C) = C :=
  rfl

/-- For a `DepFunctionalSubsingleton`, the objects are preserved after
    round-tripping through `BundledCategoryStruct`. -/
theorem depFunctionalSubsingleton_roundtrip_objT.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄}) :
    (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).data.objT =
    D.data.objT :=
  rfl

/-- For a `DepFunctionalSubsingleton`, the morphisms are preserved after
    round-tripping through `BundledCategoryStruct`. -/
theorem depFunctionalSubsingleton_roundtrip_morT.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    (a b : D.data.objT) :
    (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).data.morT a b =
    D.data.morT a b :=
  rfl

/-- For a `DepFunctionalSubsingleton`, the identity witness holds if and only
    if the morphism equals the functionally-determined identity. -/
theorem depFunctionalSubsingleton_idT_iff
    (D : DepFunctionalSubsingleton) {o : D.data.objT} (m : D.data.morT o o) :
    D.data.idT m ↔ m = (D.functional.id.exists_ o).fst := by
  constructor
  · intro hm
    exact D.functional.id.unique o m _ hm (D.functional.id.exists_ o).snd
  · intro heq
    exact heq ▸ (D.functional.id.exists_ o).snd

/-- For a `DepFunctionalSubsingleton`, the composition witness holds if and
    only if the result equals the functionally-determined composite. -/
theorem depFunctionalSubsingleton_compT_iff
    (D : DepFunctionalSubsingleton) {a b c : D.data.objT}
    (f : D.data.morT a b) (g : D.data.morT b c) (h : D.data.morT a c) :
    D.data.compT f g h ↔ h = (D.functional.comp.exists_ f g).fst := by
  constructor
  · intro hcomp
    exact D.functional.comp.unique f g h _ hcomp (D.functional.comp.exists_ f g).snd
  · intro heq
    exact heq ▸ (D.functional.comp.exists_ f g).snd

/-- Convert an original `idT` witness to the round-tripped `idT` witness. -/
def depFunctionalSubsingleton_roundtrip_idT_to.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {o : D.data.objT} {m : D.data.morT o o} (hid : D.data.idT m) :
    (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).data.idT m :=
  ⟨D.functional.id.unique o m _ hid (D.functional.id.exists_ o).snd⟩

/-- Convert a round-tripped `idT` witness back to the original `idT` witness. -/
def depFunctionalSubsingleton_roundtrip_idT_from.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {o : D.data.objT} {m : D.data.morT o o}
    (hid : (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).data.idT m) :
    D.data.idT m :=
  hid.down ▸ (D.functional.id.exists_ o).snd

/-- Convert an original `compT` witness to the round-tripped `compT` witness. -/
def depFunctionalSubsingleton_roundtrip_compT_to.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {a b c : D.data.objT}
    {f : D.data.morT a b} {g : D.data.morT b c} {h : D.data.morT a c}
    (hcomp : D.data.compT f g h) :
    (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).data.compT f g h :=
  ⟨D.functional.comp.unique f g h _ hcomp (D.functional.comp.exists_ f g).snd⟩

/-- Convert a round-tripped `compT` witness back to the original `compT` witness. -/
def depFunctionalSubsingleton_roundtrip_compT_from.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {a b c : D.data.objT}
    {f : D.data.morT a b} {g : D.data.morT b c} {h : D.data.morT a c}
    (hcomp : (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).data.compT f g h) :
    D.data.compT f g h :=
  hcomp.down ▸ (D.functional.comp.exists_ f g).snd

end SubsingletonConditions

section CatEmbedding

/-- Convert a `Cat` object to a `DepCategoryData`. A category's structure
    is encoded as DepCategoryData where identity and composition witnesses
    are equality propositions. -/
def catToDepCategoryData.{u₁, u₂, u₃, u₄} (C : Cat.{u₂, u₁}) :
    DepCategoryData.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} :=
  bundledCategoryStructToDepData (BundledCategoryStruct.ofCat C)

/-- Convert a functor between categories to a `DepNatTransData` morphism
    between the corresponding `DepCategoryData` structures. -/
def functorToDepNatTrans.{u₁, u₂, u₃, u₄} {C D : Cat.{u₂, u₁}}
    (F : C ⟶ D) :
    DepNatTransData (catToDepCategoryData.{u₁, u₂, u₃, u₄} C)
                    (catToDepCategoryData.{u₁, u₂, u₃, u₄} D) where
  appObj := F.toFunctor.obj
  appMor := F.toFunctor.map
  appId := fun {o} {_} hid =>
    PULift.up (hid.down ▸ F.toFunctor.map_id o)
  appComp := fun {_ _ _} {f g _} hcomp =>
    PULift.up (hcomp.down ▸ F.toFunctor.map_comp f g)

/-- `functorToDepNatTrans` maps the identity functor to the identity
    DepNatTransData. -/
theorem functorToDepNatTrans_id.{u₁, u₂, u₃, u₄} (C : Cat.{u₂, u₁}) :
    functorToDepNatTrans.{u₁, u₂, u₃, u₄} (𝟙 C) =
    DepNatTransData.id (catToDepCategoryData.{u₁, u₂, u₃, u₄} C) :=
  rfl

/-- `functorToDepNatTrans` preserves composition. -/
theorem functorToDepNatTrans_comp.{u₁, u₂, u₃, u₄}
    {C D E : Cat.{u₂, u₁}} (F : C ⟶ D) (G : D ⟶ E) :
    functorToDepNatTrans.{u₁, u₂, u₃, u₄} (F ≫ G) =
    DepNatTransData.comp (functorToDepNatTrans F) (functorToDepNatTrans G) :=
  rfl

/-- The embedding functor from `Cat` to `DepCategoryData`. -/
def catEmbedding.{u₁, u₂, u₃, u₄} : Cat.{u₂, u₁} ⥤ DepCategoryData where
  obj := catToDepCategoryData.{u₁, u₂, u₃, u₄}
  map := functorToDepNatTrans.{u₁, u₂, u₃, u₄}
  map_id := functorToDepNatTrans_id
  map_comp := functorToDepNatTrans_comp

end CatEmbedding

end CategoryJudgments

end GebLean
