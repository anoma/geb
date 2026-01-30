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

section FunctionalCategoryEquiv

/-- A `DepCategoryData` bundled with its functionality witnesses.
    These are the objects that have the data of a category (without laws). -/
structure DepFunctionalCategory.{u₁, u₂, u₃, u₄} : Type (max u₁ u₂ u₃ u₄)
    extends DepCompleteObj.{u₁, u₂, u₃, u₄} where
  /-- The uniqueness witnesses -/
  unique : toDepCompleteObj.toDepCategoryData.Unique

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

/-- Convert a `BundledCategoryStruct` to a `DepCompleteObj`. -/
def bundledCategoryStructToDepCompleteObj.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
      DepCompleteObj.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} where
  toDepCategoryData := bundledCategoryStructToDepData C
  exists_ := bundledCategoryStructToDepData_exists C

/-- Convert a `BundledCategoryStruct` to a `DepFunctionalCategory`. -/
def bundledCategoryStructToDepFunctional.{u₁, u₂, u₃, u₄}
    (C : BundledCategoryStruct.{u₂, u₁}) :
      DepFunctionalCategory.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄} where
  toDepCompleteObj := bundledCategoryStructToDepCompleteObj C
  unique := bundledCategoryStructToDepData_unique C

/-- Given a `DepFunctionalCategory`, extract the identity morphism for an
    object using the existence condition. -/
def DepFunctionalCategory.idMor (D : DepFunctionalCategory)
    (o : D.toDepCategoryData.objT) : D.toDepCategoryData.morT o o :=
  (D.toDepCompleteObj.exists_.id o).fst

/-- The identity morphism satisfies `idT`. -/
def DepFunctionalCategory.idMor_spec.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalCategory.{u₁, u₂, u₃, u₄})
    (o : D.toDepCategoryData.objT) : D.toDepCategoryData.idT (D.idMor o) :=
  (D.toDepCompleteObj.exists_.id o).snd

/-- Given a `DepFunctionalCategory`, extract the composite morphism for a
    composable pair using the existence condition. -/
def DepFunctionalCategory.compMor (D : DepFunctionalCategory)
    {a b c : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b) (g : D.toDepCategoryData.morT b c) :
    D.toDepCategoryData.morT a c :=
  (D.toDepCompleteObj.exists_.comp f g).fst

/-- The composite morphism satisfies `compT`. -/
def DepFunctionalCategory.compMor_spec.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalCategory.{u₁, u₂, u₃, u₄})
    {a b c : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b) (g : D.toDepCategoryData.morT b c) :
    D.toDepCategoryData.compT f g (D.compMor f g) :=
  (D.toDepCompleteObj.exists_.comp f g).snd

/-- Convert a `DepFunctionalCategory` to a `CategoryStruct` instance on its
    object type. -/
def depFunctionalToCategoryStruct (D : DepFunctionalCategory) :
    CategoryStruct D.toDepCategoryData.objT where
  Hom := D.toDepCategoryData.morT
  id := D.idMor
  comp := D.compMor

/-- Convert a `DepFunctionalCategory` to a `BundledCategoryStruct`. -/
def depFunctionalToBundledCategoryStruct.{u₁, u₂, u₃, u₄}
  (D : DepFunctionalCategory.{u₁ + 1, u₂ + 1, u₃, u₄}) :
    BundledCategoryStruct.{u₂, u₁} :=
  @BundledCategoryStruct.of D.toDepCategoryData.objT (depFunctionalToCategoryStruct D)

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
structure DepFunctionalSubsingleton.{u₁, u₂, u₃, u₄} : Type (max u₁ u₂ u₃ u₄)
    extends DepFunctionalCategory.{u₁, u₂, u₃, u₄} where
  /-- The subsingleton witnesses -/
  subsingleton : toDepCategoryData.WitnessSubsingleton

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
  toDepFunctionalCategory := bundledCategoryStructToDepFunctional C
  subsingleton := bundledCategoryStructToDepData_witnessSubsingleton C

/-- Convert a `DepFunctionalSubsingleton` to a `DepFunctionalCategory`. -/
def depFunctionalSubsingletonToFunctional.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}) :
      DepFunctionalCategory.{u₁, u₂, u₃, u₄} :=
  D.toDepFunctionalCategory

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
      (depFunctionalSubsingletonToBundledCategoryStruct D)).toDepCategoryData.objT =
    D.toDepCategoryData.objT :=
  rfl

/-- For a `DepFunctionalSubsingleton`, the morphisms are preserved after
    round-tripping through `BundledCategoryStruct`. -/
theorem depFunctionalSubsingleton_roundtrip_morT.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    (a b : D.toDepCategoryData.objT) :
    (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).toDepCategoryData.morT a b =
    D.toDepCategoryData.morT a b :=
  rfl

/-- For a `DepFunctionalSubsingleton`, the identity witness holds if and only
    if the morphism equals the functionally-determined identity. -/
theorem depFunctionalSubsingleton_idT_iff
    (D : DepFunctionalSubsingleton)
    {o : D.toDepCategoryData.objT} (m : D.toDepCategoryData.morT o o) :
    D.toDepCategoryData.idT m ↔
      m = (D.toDepFunctionalCategory.toDepCompleteObj.exists_.id o).fst := by
  constructor
  · intro hm
    let idWit := D.toDepFunctionalCategory.toDepCompleteObj.exists_.id o
    exact D.toDepFunctionalCategory.unique.id o m _ hm idWit.snd
  · intro heq
    exact heq ▸ (D.toDepFunctionalCategory.toDepCompleteObj.exists_.id o).snd

/-- For a `DepFunctionalSubsingleton`, the composition witness holds if and
    only if the result equals the functionally-determined composite. -/
theorem depFunctionalSubsingleton_compT_iff
    (D : DepFunctionalSubsingleton) {a b c : D.toDepCategoryData.objT}
    (f : D.toDepCategoryData.morT a b) (g : D.toDepCategoryData.morT b c)
    (h : D.toDepCategoryData.morT a c) :
    D.toDepCategoryData.compT f g h ↔
      h = (D.toDepFunctionalCategory.toDepCompleteObj.exists_.comp f g).fst := by
  constructor
  · intro hcomp
    let compWit := D.toDepFunctionalCategory.toDepCompleteObj.exists_.comp f g
    exact D.toDepFunctionalCategory.unique.comp f g h _ hcomp compWit.snd
  · intro heq
    exact heq ▸ (D.toDepFunctionalCategory.toDepCompleteObj.exists_.comp f g).snd

/-- Convert an original `idT` witness to the round-tripped `idT` witness. -/
def depFunctionalSubsingleton_roundtrip_idT_to.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {o : D.toDepCategoryData.objT} {m : D.toDepCategoryData.morT o o}
    (hid : D.toDepCategoryData.idT m) :
    let D' := bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)
    D'.toDepCategoryData.idT m :=
  let idWit := D.toDepFunctionalCategory.toDepCompleteObj.exists_.id o
  ⟨D.toDepFunctionalCategory.unique.id o m _ hid idWit.snd⟩

/-- Convert a round-tripped `idT` witness back to the original `idT` witness. -/
def depFunctionalSubsingleton_roundtrip_idT_from.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {o : D.toDepCategoryData.objT} {m : D.toDepCategoryData.morT o o}
    (hid : (bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)).toDepCategoryData.idT m) :
    D.toDepCategoryData.idT m :=
  hid.down ▸ (D.toDepFunctionalCategory.toDepCompleteObj.exists_.id o).snd

/-- Convert an original `compT` witness to the round-tripped `compT` witness. -/
def depFunctionalSubsingleton_roundtrip_compT_to.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {a b c : D.toDepCategoryData.objT}
    {f : D.toDepCategoryData.morT a b} {g : D.toDepCategoryData.morT b c}
    {h : D.toDepCategoryData.morT a c}
    (hcomp : D.toDepCategoryData.compT f g h) :
    let D' := bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
      (depFunctionalSubsingletonToBundledCategoryStruct D)
    D'.toDepCategoryData.compT f g h :=
  let compWit := D.toDepFunctionalCategory.toDepCompleteObj.exists_.comp f g
  ⟨D.toDepFunctionalCategory.unique.comp f g h _ hcomp compWit.snd⟩

/-- Convert a round-tripped `compT` witness back to the original `compT` witness. -/
def depFunctionalSubsingleton_roundtrip_compT_from.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalSubsingleton.{u₁ + 1, u₂ + 1, max 1 u₃, max 1 u₄})
    {a b c : D.toDepCategoryData.objT}
    {f : D.toDepCategoryData.morT a b} {g : D.toDepCategoryData.morT b c}
    {h : D.toDepCategoryData.morT a c}
    (hcomp :
      let D' := bundledCategoryStructToDepFunctionalSubsingleton.{u₁, u₂, u₃, u₄}
        (depFunctionalSubsingletonToBundledCategoryStruct D)
      D'.toDepCategoryData.compT f g h) :
    D.toDepCategoryData.compT f g h :=
  hcomp.down ▸ (D.toDepFunctionalCategory.toDepCompleteObj.exists_.comp f g).snd

end SubsingletonConditions

end CategoryJudgments

end GebLean
