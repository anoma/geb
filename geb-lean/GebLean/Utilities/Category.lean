import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Category Theory Utilities

Convenience notation and helpers for working with categories.

## Main definitions

### Category structures without typeclasses

* `HomSet`: The data of a quiver (the Hom type family)
* `homSetOfQuiver`: Extract a `HomSet` from a `Quiver` typeclass instance
* `CompositionalStruct`: Composition of morphisms
* `AssociativityLaw`: Associativity law for composition
* `SemicategoryStruct`: Semicategory structure (composition and associativity)
* `IdentityStruct`: Identity morphisms for each object
* `identityStructOfReflQuiver`: Extract an `IdentityStruct` from a `ReflQuiver`
  typeclass instance
* `IdComp`: Law for composition after an identity
* `CompId`: Law for composition before an identity
* `IdentityLaws`: Identity laws for both directions of composition
* `CategoryOps`: Category operations (composition and identity)
* `categoryOpsOfCategoryStruct`: Extract `CategoryOps` from a `CategoryStruct`
  typeclass
* `CategoryLaws`: Category laws (associativity and identity laws)
* `CategoryData`: Category data (operations and laws)
* `CategoryOfData`: Build a `Category` instance from `CategoryData`
* `categoryDataOfCategory`: Extract `CategoryData` from a `Category` typeclass
* `HomSetEquiv`: Equivalence between hom-sets over an equivalence of objects
* `CategoryData.ofEquiv`: Transport `CategoryData` across an equivalence
* `CategoryOpsCompatible`: Compatibility of `CategoryOps` with transported data
* `CategoryLaws.ofCompatible`: Derive laws for compatible operations
* `CategoryData.ofCompatible`: Build `CategoryData` from compatible operations

### Functor structures without typeclasses

* `ObjMap`: Object map of a functor
* `MorphMap`: Morphism map of a functor
* `FunctorOps`: Functor operations (object and morphism maps)
* `PreservesId`: Law that functor preserves identity
* `PreservesComp`: Law that functor preserves composition
* `FunctorLaws`: Functor laws (preserves identity and composition)
* `FunctorData`: Functor data (operations and laws)
* `FunctorOfData`: Build a `CategoryTheory.Functor` from `FunctorData`
* `functorDataOfFunctor`: Extract `FunctorData` from a `Functor`

### Miscellaneous

* `≅Cat`: Notation for isomorphisms between categories without explicit
  `Cat.of`
-/

namespace GebLean

open CategoryTheory

universe v u

/-- The data of a quiver: a family of types indexed by pairs of vertices. -/
abbrev HomSet (U : Type u) := U → U → Sort v

/-- Extract a `Quiver` typeclass instance from a `HomSet`. -/
instance {U : Type u} (hs : HomSet.{v, u} U) : Quiver.{v, u} U where
  Hom := hs

/-- Extract the `HomSet` from a `Quiver` typeclass instance. -/
abbrev homSetOfQuiver (U : Type u) [Quiver.{v, u} U] : HomSet.{v, u} U :=
  Quiver.Hom

/-- Compositional structure: composition of morphisms.

Note: Most presentations of category theory put composition in the opposite
order (e.g., `g ∘ f` for `f : a → b` and `g : b → c`). We follow the
convention of Lean's standard libraries, where composition is written
`f ≫ g` or `comp f g`, with the first morphism applied first. -/
abbrev CompositionalStruct {U : Type u} (hs : HomSet.{v, u} U) :=
  ∀ {a b c : U}, hs a b → hs b c → hs a c

/-- Associativity law for composition. -/
abbrev AssociativityLaw {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) : Prop :=
  ∀ {a b c d : U} (f : hs a b) (g : hs b c) (h : hs c d),
    comp (comp f g) h = comp f (comp g h)

/-- Semicategory structure: composition and associativity. -/
structure SemicategoryStruct (U : Type u) (hs : HomSet.{v, u} U) where
  /-- Composition of morphisms -/
  comp : CompositionalStruct hs
  /-- Associativity of composition -/
  assoc : AssociativityLaw hs comp

/-- Identity structure: identity morphisms for each object. -/
abbrev IdentityStruct {U : Type u} (hs : HomSet.{v, u} U) :=
  ∀ (a : U), hs a a

/-- Extract a `ReflQuiver` typeclass instance from a `HomSet` with identity
    structure. -/
instance {U : Type u} (hs : HomSet.{v, u} U) (ids : IdentityStruct hs) :
    ReflQuiver U where
  Hom := hs
  id := ids

/-- Extract the `IdentityStruct` from a `ReflQuiver` typeclass instance. -/
abbrev identityStructOfReflQuiver (U : Type u) [ReflQuiver U] :
    IdentityStruct (homSetOfQuiver U) :=
  ReflQuiver.id

/-- Composing any morphism after the identity gives the original morphism. -/
abbrev IdComp {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop :=
  ∀ {a b : U} (f : hs a b), comp (id a) f = f

/-- Composing any morphism before the identity gives the original morphism. -/
abbrev CompId {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop :=
  ∀ {a b : U} (f : hs a b), comp f (id b) = f

/-- Identity laws for both pre- and post-composition with identities. -/
structure IdentityLaws {U : Type u} (hs : HomSet.{v, u} U)
    (comp : CompositionalStruct hs) (id : IdentityStruct hs) : Prop where
  id_comp : IdComp hs comp id
  comp_id : CompId hs comp id

/-- Category operations: composition and identity morphisms. -/
structure CategoryOps {U : Type u} (hs : HomSet.{v, u} U) where
  /-- Composition of morphisms -/
  comp : CompositionalStruct hs
  /-- Identity morphisms -/
  id : IdentityStruct hs

/-- Build a `CategoryStruct` typeclass instance from category operations.
    Note: This only works when the HomSet is in Type (not general Sort). -/
instance {U : Type u} (hs : HomSet.{v + 1, u} U)
    (ops : CategoryOps hs) : CategoryStruct.{v, u} U where
  Hom := hs
  id := ops.id
  comp := ops.comp

/-- Extract the `CategoryOps` from a `CategoryStruct` typeclass instance. -/
abbrev categoryOpsOfCategoryStruct (U : Type u) [CategoryStruct.{v, u} U] :
    CategoryOps (homSetOfQuiver U) where
  comp := CategoryStruct.comp
  id := CategoryStruct.id

/-- Category laws: associativity and identity laws. -/
structure CategoryLaws {U : Type u} (hs : HomSet.{v, u} U)
    (ops : CategoryOps hs) : Prop where
  /-- Associativity of composition -/
  assoc : AssociativityLaw hs ops.comp
  /-- Identity laws -/
  id_laws : IdentityLaws hs ops.comp ops.id

/-- Category data: composition, associativity, identities, and
    identity laws. -/
structure CategoryData (U : Type u) (hs : HomSet.{v, u} U)
    extends CategoryOps hs where
  /-- Category laws -/
  laws : CategoryLaws hs toCategoryOps

namespace CategoryData

variable {U : Type u} {hs : HomSet.{v, u} U}

/-- Associativity law from category data. -/
@[reducible] def assoc (cs : CategoryData U hs) :
    AssociativityLaw hs cs.comp :=
  cs.laws.assoc

/-- Identity laws from category data. -/
@[reducible] def id_laws (cs : CategoryData U hs) :
    IdentityLaws hs cs.comp cs.id :=
  cs.laws.id_laws

end CategoryData

/-- Build a `Category` typeclass instance from category data.
    Note: This only works when the HomSet is in Type (not general Sort). -/
instance CategoryOfData {U : Type u} {hs : HomSet.{v + 1, u} U}
    (data : CategoryData U hs) : Category.{v, u} U where
  Hom := hs
  id := data.id
  comp := data.comp
  id_comp := data.laws.id_laws.id_comp
  comp_id := data.laws.id_laws.comp_id
  assoc := data.laws.assoc

/-- Extract the `CategoryData` from a `Category` typeclass instance. -/
abbrev categoryDataOfCategory (U : Type u) [Category.{v, u} U] :
    CategoryData U (homSetOfQuiver U) where
  comp := CategoryStruct.comp
  id := CategoryStruct.id
  laws := {
    assoc := Category.assoc
    id_laws := {
      id_comp := Category.id_comp
      comp_id := Category.comp_id
    }
  }

/-- Round-trip from `CategoryData` to `Category` and back yields the original
    data. -/
theorem categoryDataOfCategory_of_CategoryOfData {U : Type u}
    {hs : HomSet.{v + 1, u} U} (data : CategoryData U hs) :
    @categoryDataOfCategory U (CategoryOfData data) = data := rfl

/-- Round-trip from `Category` to `CategoryData` and back yields the original
    category instance (as `Category` structures). -/
theorem CategoryOfData_of_categoryDataOfCategory (U : Type u)
    [cat : Category.{v, u} U] :
    CategoryOfData (categoryDataOfCategory U) = cat := rfl

/-- Data for an isomorphism between hom-sets over an equivalence of object
    types. Given an equivalence `e : U ≃ V` between object types, this
    structure provides bijections between `hs a b` and `hs' (e a) (e b)` for
    each pair of objects. -/
structure HomSetEquiv {U : Type u} {V : Type u} (e : U ≃ V)
    (hs : HomSet.{v, u} U) (hs' : HomSet.{v, u} V) where
  /-- Forward map on morphisms -/
  toFun : ∀ {a b : U}, hs a b → hs' (e a) (e b)
  /-- Inverse map on morphisms -/
  invFun : ∀ {a b : U}, hs' (e a) (e b) → hs a b
  /-- Left inverse -/
  left_inv : ∀ {a b : U} (f : hs a b), invFun (toFun f) = f
  /-- Right inverse -/
  right_inv : ∀ {a b : U} (f : hs' (e a) (e b)), toFun (invFun f) = f

/-- Transport `CategoryData` across an equivalence of object types and a
    compatible equivalence of hom-sets. -/
def CategoryData.ofEquiv {U : Type u} {V : Type u} (e : U ≃ V)
    {hs : HomSet.{v, u} U} {hs' : HomSet.{v, u} V}
    (he : HomSetEquiv e hs hs') (data : CategoryData V hs') :
    CategoryData U hs where
  comp := fun f g => he.invFun (data.comp (he.toFun f) (he.toFun g))
  id := fun a => he.invFun (data.id (e a))
  laws := {
    assoc := fun f g h => by
      simp only [he.right_inv]
      exact congrArg he.invFun (data.assoc (he.toFun f) (he.toFun g) (he.toFun h))
    id_laws := {
      id_comp := fun f => by
        simp only [he.right_inv]
        have h := data.laws.id_laws.id_comp (he.toFun f)
        simp only [h]
        exact he.left_inv f
      comp_id := fun f => by
        simp only [he.right_inv]
        have h := data.laws.id_laws.comp_id (he.toFun f)
        simp only [h]
        exact he.left_inv f
    }
  }

/-- Compatibility between `CategoryOps` and what `CategoryData.ofEquiv` would
    compute. This asserts that the given operations agree with the transported
    operations. -/
structure CategoryOpsCompatible {U : Type u} {V : Type u} (e : U ≃ V)
    {hs : HomSet.{v, u} U} {hs' : HomSet.{v, u} V}
    (he : HomSetEquiv e hs hs') (data : CategoryData V hs')
    (ops : CategoryOps hs) : Prop where
  /-- Identity agrees with transported identity -/
  id_eq : ∀ (a : U), ops.id a = he.invFun (data.id (e a))
  /-- Composition agrees with transported composition -/
  comp_eq : ∀ {a b c : U} (f : hs a b) (g : hs b c),
    ops.comp f g = he.invFun (data.comp (he.toFun f) (he.toFun g))

/-- Given `CategoryOps` compatible with a transported `CategoryData`, derive the
    `CategoryLaws` for the given ops. -/
def CategoryLaws.ofCompatible {U : Type u} {V : Type u} {e : U ≃ V}
    {hs : HomSet.{v, u} U} {hs' : HomSet.{v, u} V}
    {he : HomSetEquiv e hs hs'} {data : CategoryData V hs'}
    {ops : CategoryOps hs} (compat : CategoryOpsCompatible e he data ops) :
    CategoryLaws hs ops where
  assoc := fun f g h => by
    calc ops.comp (ops.comp f g) h
        = he.invFun (data.comp (he.toFun (ops.comp f g)) (he.toFun h)) :=
          compat.comp_eq _ _
      _ = he.invFun (data.comp (he.toFun (he.invFun (data.comp (he.toFun f)
            (he.toFun g)))) (he.toFun h)) := by rw [compat.comp_eq f g]
      _ = he.invFun (data.comp (data.comp (he.toFun f) (he.toFun g))
            (he.toFun h)) := by rw [he.right_inv]
      _ = he.invFun (data.comp (he.toFun f) (data.comp (he.toFun g)
            (he.toFun h))) :=
          congrArg he.invFun (data.assoc (he.toFun f) (he.toFun g) (he.toFun h))
      _ = he.invFun (data.comp (he.toFun f) (he.toFun (he.invFun
            (data.comp (he.toFun g) (he.toFun h))))) := by rw [he.right_inv]
      _ = he.invFun (data.comp (he.toFun f) (he.toFun (ops.comp g h))) := by
          rw [compat.comp_eq g h]
      _ = ops.comp f (ops.comp g h) := (compat.comp_eq _ _).symm
  id_laws := {
    id_comp := fun f => by
      calc ops.comp (ops.id _) f
          = he.invFun (data.comp (he.toFun (ops.id _)) (he.toFun f)) :=
            compat.comp_eq _ _
        _ = he.invFun (data.comp (he.toFun (he.invFun (data.id (e _))))
              (he.toFun f)) := by rw [compat.id_eq]
        _ = he.invFun (data.comp (data.id (e _)) (he.toFun f)) := by
            rw [he.right_inv]
        _ = he.invFun (he.toFun f) := by
            have h := data.laws.id_laws.id_comp (he.toFun f); simp only [h]
        _ = f := he.left_inv f
    comp_id := fun f => by
      calc ops.comp f (ops.id _)
          = he.invFun (data.comp (he.toFun f) (he.toFun (ops.id _))) :=
            compat.comp_eq _ _
        _ = he.invFun (data.comp (he.toFun f) (he.toFun (he.invFun
              (data.id (e _))))) := by rw [compat.id_eq]
        _ = he.invFun (data.comp (he.toFun f) (data.id (e _))) := by
            rw [he.right_inv]
        _ = he.invFun (he.toFun f) := by
            have h := data.laws.id_laws.comp_id (he.toFun f); simp only [h]
        _ = f := he.left_inv f
  }

/-- Given `CategoryOps` compatible with a transported `CategoryData`, derive a
    `CategoryData` with the given ops. This allows using more convenient forms
    of identity and composition while inheriting the laws from the transported
    category. -/
def CategoryData.ofCompatible {U : Type u} {V : Type u} {e : U ≃ V}
    {hs : HomSet.{v, u} U} {hs' : HomSet.{v, u} V}
    {he : HomSetEquiv e hs hs'} {data : CategoryData V hs'}
    {ops : CategoryOps hs} (compat : CategoryOpsCompatible e he data ops) :
    CategoryData U hs where
  toCategoryOps := ops
  laws := CategoryLaws.ofCompatible compat

/-! ## Functor Data

Structures for representing functors without typeclasses. -/

universe v₁ u₁ v₂' u₂'

/-- The object map of a functor. -/
abbrev ObjMap (C : Type u) (D : Type u₁) := C → D

/-- The morphism map of a functor, given an object map. -/
abbrev MorphMap {C : Type u} {D : Type u₁}
    (hsC : HomSet.{v, u} C) (hsD : HomSet.{v₁, u₁} D)
    (obj : ObjMap C D) :=
  ∀ {a b : C}, hsC a b → hsD (obj a) (obj b)

/-- Functor operations: object map and morphism map. -/
structure FunctorOps {C : Type u} {D : Type u₁}
    (hsC : HomSet.{v, u} C) (hsD : HomSet.{v₁, u₁} D) where
  /-- The object map -/
  obj : ObjMap C D
  /-- The morphism map -/
  map : MorphMap hsC hsD obj

/-- Law that the functor preserves identity morphisms. -/
abbrev PreservesId {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    (opsC : CategoryOps hsC) (opsD : CategoryOps hsD)
    (fops : FunctorOps hsC hsD) : Prop :=
  ∀ (a : C), fops.map (opsC.id a) = opsD.id (fops.obj a)

/-- Law that the functor preserves composition. -/
abbrev PreservesComp {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    (opsC : CategoryOps hsC) (opsD : CategoryOps hsD)
    (fops : FunctorOps hsC hsD) : Prop :=
  ∀ {a b c : C} (f : hsC a b) (g : hsC b c),
    fops.map (opsC.comp f g) = opsD.comp (fops.map f) (fops.map g)

/-- Functor laws: preserves identity and composition. -/
structure FunctorLaws {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    (opsC : CategoryOps hsC) (opsD : CategoryOps hsD)
    (fops : FunctorOps hsC hsD) : Prop where
  /-- Preserves identity morphisms -/
  map_id : PreservesId opsC opsD fops
  /-- Preserves composition -/
  map_comp : PreservesComp opsC opsD fops

/-- Functor data: operations and laws. -/
structure FunctorData {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    (dataC : CategoryData C hsC) (dataD : CategoryData D hsD)
    extends FunctorOps hsC hsD where
  /-- Functor laws -/
  laws : FunctorLaws dataC.toCategoryOps dataD.toCategoryOps toFunctorOps

namespace FunctorData

variable {C : Type u} {D : Type u₁}
variable {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
variable {dataC : CategoryData C hsC} {dataD : CategoryData D hsD}

/-- Preserves identity from functor data. -/
@[reducible] def map_id (fd : FunctorData dataC dataD) :
    PreservesId dataC.toCategoryOps dataD.toCategoryOps fd.toFunctorOps :=
  fd.laws.map_id

/-- Preserves composition from functor data. -/
@[reducible] def map_comp (fd : FunctorData dataC dataD) :
    PreservesComp dataC.toCategoryOps dataD.toCategoryOps fd.toFunctorOps :=
  fd.laws.map_comp

end FunctorData

/-- Build a `CategoryTheory.Functor` from `FunctorData`.
    Note: This only works when the HomSets are in Type (not general Sort). -/
def FunctorOfData {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v + 1, u} C} {hsD : HomSet.{v₁ + 1, u₁} D}
    {dataC : CategoryData C hsC} {dataD : CategoryData D hsD}
    (fd : FunctorData dataC dataD) :
    @CategoryTheory.Functor C (CategoryOfData dataC) D
      (CategoryOfData dataD) :=
  @CategoryTheory.Functor.mk C (CategoryOfData dataC) D
    (CategoryOfData dataD)
    fd.obj fd.map fd.laws.map_id fd.laws.map_comp

/-- Extract `FunctorData` from a `CategoryTheory.Functor`. -/
abbrev functorDataOfFunctor {C : Type u} {D : Type u₁}
    [Category.{v, u} C] [Category.{v₁, u₁} D]
    (F : C ⥤ D) :
    FunctorData (categoryDataOfCategory C) (categoryDataOfCategory D) where
  obj := F.obj
  map := F.map
  laws := {
    map_id := F.map_id
    map_comp := F.map_comp
  }

/-- Round-trip from `FunctorData` to `CategoryTheory.Functor` and back yields
    the original data. -/
theorem functorDataOfFunctor_of_FunctorOfData {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v + 1, u} C} {hsD : HomSet.{v₁ + 1, u₁} D}
    {dataC : CategoryData C hsC} {dataD : CategoryData D hsD}
    (fd : FunctorData dataC dataD) :
    @functorDataOfFunctor C D (CategoryOfData dataC)
      (CategoryOfData dataD) (FunctorOfData fd) = fd := rfl

/-- Round-trip from `CategoryTheory.Functor` to `FunctorData` and back yields
    the original functor instance (as `Functor` structures). -/
theorem FunctorOfData_of_functorDataOfFunctor {C : Type u} {D : Type u₁}
    [Category.{v, u} C] [Category.{v₁, u₁} D] (F : C ⥤ D) :
    FunctorOfData (functorDataOfFunctor F) = F := rfl

/-- Compatibility between `FunctorOps` and the ops of a given `FunctorData`
    when the object maps are the same. The morphism maps are then required
    to agree pointwise. -/
structure FunctorOpsCompatible {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    {dataC : CategoryData C hsC} {dataD : CategoryData D hsD}
    (fd : FunctorData dataC dataD) (ops : FunctorOps hsC hsD) : Prop where
  /-- Object map agrees -/
  obj_eq : ops.obj = fd.obj
  /-- Morphism map agrees (with type cast due to object equality) -/
  map_eq : ∀ {a b : C} (f : hsC a b),
    ops.map f = cast (by rw [obj_eq]) (fd.map f)

/-- Given `FunctorOps` compatible with a `FunctorData`, derive the
    `FunctorLaws` for the given ops using the object map as an explicit
    parameter to enable substitution. -/
def FunctorLaws.ofCompatibleAux {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    {dataC : CategoryData C hsC} {dataD : CategoryData D hsD}
    (fd : FunctorData dataC dataD)
    (objMap : ObjMap C D)
    (morphMap : MorphMap hsC hsD objMap)
    (hobj : objMap = fd.obj)
    (hmap : ∀ {a b : C} (f : hsC a b),
      morphMap f = cast (by rw [hobj]) (fd.map f)) :
    FunctorLaws dataC.toCategoryOps dataD.toCategoryOps ⟨objMap, morphMap⟩ := by
  subst hobj
  exact {
    map_id := fun a => by simp only [hmap, cast_eq, fd.laws.map_id]
    map_comp := fun f g => by simp only [hmap, cast_eq, fd.laws.map_comp]
  }

/-- Given `FunctorOps` compatible with a `FunctorData`, derive the
    `FunctorLaws` for the given ops. -/
def FunctorLaws.ofCompatible {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    {dataC : CategoryData C hsC} {dataD : CategoryData D hsD}
    {fd : FunctorData dataC dataD} {ops : FunctorOps hsC hsD}
    (compat : FunctorOpsCompatible fd ops) :
    FunctorLaws dataC.toCategoryOps dataD.toCategoryOps ops :=
  FunctorLaws.ofCompatibleAux fd ops.obj ops.map compat.obj_eq compat.map_eq

/-- Given `FunctorOps` compatible with a `FunctorData`, derive a new
    `FunctorData` with the given ops. This allows using more convenient forms
    of the object and morphism maps while inheriting the laws from the original
    functor data. -/
def FunctorData.ofCompatible {C : Type u} {D : Type u₁}
    {hsC : HomSet.{v, u} C} {hsD : HomSet.{v₁, u₁} D}
    {dataC : CategoryData C hsC} {dataD : CategoryData D hsD}
    {fd : FunctorData dataC dataD} {ops : FunctorOps hsC hsD}
    (compat : FunctorOpsCompatible fd ops) :
    FunctorData dataC dataD where
  toFunctorOps := ops
  laws := FunctorLaws.ofCompatible compat

section EqToHom

universe v₂ u₂

variable {C : Type u} [Category.{v, u} C]
variable {D : Type u₂} [Category.{v₂, u₂} D]

/--
Composition of `eqToHom` with its symmetric gives identity.
-/
lemma eqToHom_comp_eqToHom_symm {X Y : C} (p : X = Y) :
    eqToHom p ≫ eqToHom p.symm = 𝟙 X := by
  cases p
  simp

/--
Composition of symmetric `eqToHom` with the original gives identity.
-/
lemma eqToHom_symm_comp_eqToHom {X Y : C} (p : X = Y) :
    eqToHom p.symm ≫ eqToHom p = 𝟙 Y := by
  cases p
  simp

/--
Two morphisms composed with `eqToHom` are equal if and only if
the first morphism composed with the combined equality is equal to the second.
-/
lemma comp_eqToHom_eq_comp_eqToHom {X Y Z W : C}
    (f : X ⟶ Y) (g : X ⟶ Z) (p : Y = W) (q : Z = W) :
    f ≫ eqToHom p = g ≫ eqToHom q ↔
    f ≫ eqToHom (p.trans q.symm) = g := by
  constructor
  · intro h
    calc f ≫ eqToHom (p.trans q.symm)
        = f ≫ (eqToHom p ≫ eqToHom q.symm) := by rw [← eqToHom_trans]
      _ = (f ≫ eqToHom p) ≫ eqToHom q.symm := by rw [Category.assoc]
      _ = (g ≫ eqToHom q) ≫ eqToHom q.symm := by rw [h]
      _ = g ≫ (eqToHom q ≫ eqToHom q.symm) := by rw [← Category.assoc]
      _ = g ≫ 𝟙 Z := by rw [eqToHom_comp_eqToHom_symm]
      _ = g := by rw [Category.comp_id]
  · intro h
    calc f ≫ eqToHom p
        = f ≫ (eqToHom (p.trans q.symm) ≫ eqToHom q) := by rw [← eqToHom_trans]
      _ = (f ≫ eqToHom (p.trans q.symm)) ≫ eqToHom q := by rw [Category.assoc]
      _ = g ≫ eqToHom q := by rw [h]

/--
Heterogeneous equality of morphisms is equivalent to equality after postcomposing
with `eqToHom`.
-/
lemma heq_iff_comp_eqToHom {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (p : Y = Z) :
    HEq f g ↔ f ≫ eqToHom p = g := by
  constructor
  · intro h
    cases p
    simp
    exact eq_of_heq h
  · intro h
    cases p
    simp at h
    exact heq_of_eq h

/--
Heterogeneous equality of morphisms is equivalent to equality after precomposing
with `eqToHom`.
-/
lemma heq_iff_eqToHom_comp {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) (p : X = Y) :
    HEq f g ↔ eqToHom p ≫ f = g := by
  constructor
  · intro h
    cases p
    simp
    exact eq_of_heq h
  · intro h
    cases p
    simp at h
    exact heq_of_eq h

/--
Heterogeneous equality of morphisms is equivalent to equality after precomposing
and postcomposing with `eqToHom`.
-/
lemma heq_iff_comp_eqToHom_comp {W X Y Z : C}
    (f : X ⟶ Y) (g : W ⟶ Z) (p : W = X) (q : Y = Z) :
    HEq f g ↔ eqToHom p ≫ f ≫ eqToHom q = g := by
  constructor
  · intro h
    -- f : X ⟶ Y and g : W ⟶ Z with f ≍ g
    -- First use heq_iff_eqToHom_comp to get eqToHom p ≫ f = intermediate
    -- Then use heq_iff_comp_eqToHom to handle the postcomposition
    cases p
    cases q
    simp
    exact eq_of_heq h
  · intro h
    cases p
    cases q
    simp at h
    exact heq_of_eq h

/--
Any `eqToHom` of a reflexive equality is equal to the identity.
By proof irrelevance, all proofs of `X = X` are equal to `rfl`, and
`eqToHom rfl = 𝟙 X`.
-/
lemma eqToHom_refl' {X : C} (p : X = X) : eqToHom p = 𝟙 X := by
  rw [Subsingleton.elim p rfl]
  simp

/--
Any two `eqToHom` terms of reflexive equalities are equal.
-/
lemma eqToHom_refl_eq {X Y : C} (p q : Eq.{u + 1} X Y) :
  Eq (eqToHom.{v, u} p) (eqToHom.{v, u} q) := by
    simp

/--
Proofs of symmetric equalities produce equal `eqToHom` terms.
-/
lemma eqToHom_sym_heq {X Y : C} (p : X = Y) (q : Y = X) :
  eqToHom p ≍ eqToHom q := by
    cases p ; cases q
    simp

lemma eqToHom_sym_eq {X Y : C} (p : X = Y) (q : Y = X) :
  eqToHom p = cast (by rw [p]) (eqToHom q) := by
    cases p ; cases q
    simp

/--
A functor maps `eqToHom` to `eqToHom` of the transported equality.
-/
@[simp]
lemma functor_map_eqToHom (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congrArg F.obj p) := by
  cases p
  simp

/--
A functor maps `eqToHom` of a symmetric equality to `eqToHom` of the symmetric
transported equality.
-/
@[simp]
lemma functor_map_eqToHom_symm (F : C ⥤ D) {X Y : C} (p : Y = X) :
    F.map (eqToHom p.symm) = eqToHom (congrArg F.obj p).symm := by
  cases p
  simp

/--
From HEq of morphisms with the same target, derive an equation with eqToHom.
This is useful for converting HEq hypotheses into equations that tactics like
`cat_disch` can use.
-/
lemma eq_of_heq_eqToHom {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (h : HEq f g)
    (p : X = Y) : f = eqToHom p ≫ g := by
  cases p
  simp [eq_of_heq h]

/--
From HEq of morphisms with the same source, derive an equation with eqToHom.
-/
lemma eq_of_heq_comp_eqToHom {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (h : HEq f g)
    (p : Y = Z) : f ≫ eqToHom p = g := by
  cases p
  simp [eq_of_heq h]

/--
A round-trip through `eqToHom` with an identity in the middle equals the identity.
-/
lemma eqToHom_comp_id_comp_eqToHom {X Y : C} (p : X = Y) (q : Y = X) :
    eqToHom p ≫ 𝟙 Y ≫ eqToHom q = 𝟙 X := by
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl']

/--
When applying F.map to an eqToHom morphism, composed with an eqToHom in the
target type, the result equals the original value if the composed proofs
yield a reflexive equality.
-/
lemma eqToHomMapEqToHomApp {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X) :
    F.map (eqToHom p) (eqToHom q a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant of `eqToHomMapEqToHomApp` where the equality proof for the morphism
uses `.symm`. This handles the case where the morphism `eqToHom p.symm` goes
in the opposite direction.
-/
lemma eqToHomMapEqToHomApp' {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (q : F.obj X = F.obj Y) (a : F.obj X) :
    F.map (eqToHom p.symm) (eqToHom q a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant where the element is from `F.obj Y` and we use the symmetric equality.
For `p : X = Y`, `q : F.obj X = F.obj Y`, and `a : F.obj Y`,
we have `F.map (eqToHom p) (eqToHom q.symm a) = a`.
-/
lemma eqToHomMapEqToHomApp'' {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (q : F.obj X = F.obj Y) (a : F.obj Y) :
    F.map (eqToHom p) (eqToHom q.symm a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
When applying F.map to an eqToHom morphism and an arbitrary eqToHom on
elements, if the element types are equal, the result equals the original.
This handles cases where the equality proofs are complex but the underlying
types are definitionally equal.
-/
lemma eqToHomMapEqToHomAppRefl {E : Type*} [Category E] (F : E ⥤ Type v)
    {X : E} (p : X = X) (q : F.obj X = F.obj X) (a : F.obj X) :
    F.map (eqToHom p) (eqToHom q a) = a := by
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Generalized version that handles arbitrary proof terms by using proof
irrelevance. Given an object `X` of type `T`, a function `f : T → E`,
and proofs that `f X = X'` and `f X = X''`, we can show that
`F.map (eqToHom p) (eqToHom q a) = a` where the proofs `p` and `q` might
be arbitrary (not rfl).

This is needed when `X'` and `X''` are definitionally equal after some
propositional reductions (like `comp_id`) but the proofs inside `eqToHom`
are not definitionally `rfl`.
-/
lemma eqToHomMapEqToHomApp_of_eq {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X)
    (hXY : X = Y) : F.map (eqToHom p) (eqToHom q a) = a := by
  subst hXY
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant that doesn't require `subst` to succeed. Uses proof irrelevance
to handle cases where both sides of the equality are complex expressions.
-/
lemma eqToHomMapEqToHomApp_of_heq {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X)
    (hXY : HEq X Y) : F.map (eqToHom p) (eqToHom q a) = a := by
  cases eq_of_heq hXY
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Most flexible variant: when the eqToHom proofs come from an expression that
can be proven equal by some auxiliary proof `h`, use this lemma.
This uses explicit type casting to make the proof term substitution work.
-/
lemma eqToHomMapEqToHomApp_of_cast {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (q : F.obj X = F.obj Y) (a : F.obj X)
    (h : X = Y) : F.map (eqToHom p) (eqToHom q a) = a := by
  cases h
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Variant where we transport from `F.obj X` through `F.obj Y` back to `F.obj X`.
For `p : X = Y`, `q : F.obj X = F.obj Y`, and `a : F.obj X`,
we have `F.map (eqToHom p.symm) (cast q a) = a`.
The type cast `q` transports from `F.obj X` to `F.obj Y`.
-/
lemma eqToHomMapCastSymm {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (q : F.obj X = F.obj Y) (a : F.obj X) :
    F.map (eqToHom p.symm) (cast q a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply, cast_eq]

/--
General lemma: applying F.map to an eqToHom and eqToHom on elements
gives a round-trip result.
Given `p : Y = X`, we have a morphism `eqToHom p : Y ⟶ X` in E.
Applying F gives `F.map (eqToHom p) : F.obj Y → F.obj X`.
Given `q : F.obj X = F.obj Y`, we have `eqToHom q : F.obj X → F.obj Y`.
So the composition is: a : F.obj X → eqToHom q a : F.obj Y
                            → F.map (eqToHom p) (eqToHom q a) : F.obj X

This equals a when q = (congrArg F.obj p).symm.
-/
lemma eqToHomMapEqToHomAppRoundTrip {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : Y = X) (a : F.obj X) :
    F.map (eqToHom p) (eqToHom (congrArg F.obj p).symm a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

/--
Symmetric version of round-trip lemma.
Given `p : X = Y`, the map `F.map (eqToHom p.symm) : F.obj X → F.obj Y`
applied to `eqToHom (congrArg F.obj p) a` (where `a : F.obj Y`)
gives back `a`.
-/
lemma eqToHomMapEqToHomAppRoundTrip' {E : Type*} [Category E] (F : E ⥤ Type v)
    {X Y : E} (p : X = Y) (a : F.obj Y) :
    F.map (eqToHom p) (eqToHom (congrArg F.obj p.symm) a) = a := by
  cases p
  simp only [eqToHom_refl, Functor.map_id, types_id_apply]

end EqToHom

section Over

/--
For Over morphisms, composition of `.left` equals `.left` of composition.
-/
lemma Over_comp_left {X : Type*} {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).left = g.left ∘ f.left := rfl

/--
For an equality proof in `Over X`, the `.left` component of `eqToHom` equals
the transport function.
-/
lemma eqToHom_Over_left {X : Type*} {A₁ A₂ : Over X} (h : A₁ = A₂)
    (x : A₁.left) :
    (eqToHom h).left x = h ▸ x := by
  subst h
  rfl

/--
For a reflexive equality proof `p : A = A` on objects in `Over X`, the `.left`
component of `eqToHom p` acts as identity. This follows from proof irrelevance:
any proof of `A = A` is propositionally equal to `rfl`, and `eqToHom rfl = 𝟙`.
-/
lemma eqToHom_reflexive_left_eq_id {X : Type*} {A : Over X} (p : A = A) :
    (eqToHom p).left = id := by
  have p_is_rfl : p = rfl := Subsingleton.elim _ _
  subst p_is_rfl
  rfl

end Over

section PiCategory

universe w

variable {I : Type*} {C : I → Type*} [∀ i, Category (C i)]

/--
In the Pi category, `(f ≫ g) a = (f a) ≫ (g a)`.
This is definitional for the Pi category.
-/
lemma pi_comp_apply {f g h : ∀ a, C a} (η : f ⟶ g) (θ : g ⟶ h) (a : I) :
    (η ≫ θ) a = η a ≫ θ a := rfl

/--
In the Pi category, composition at an index is pointwise.
-/
lemma pi_comp_at_idx {x y z : ∀ i, C i} (f : x ⟶ y) (g : y ⟶ z) (i : I) :
    (f ≫ g) i = f i ≫ g i := rfl

/--
`eqToHom` in the Pi category at an index equals `eqToHom` of the component
equality. This is `CategoryTheory.Functor.eqToHom_proj` specialized.
-/
lemma pi_eqToHom_at_idx {x y : ∀ i, C i} (h : x = y) (i : I) :
    (eqToHom h : x ⟶ y) i = eqToHom (congrFun h i) :=
  CategoryTheory.Functor.eqToHom_proj h i

/--
When composing with `eqToHom` in a Pi category, the composition at an index
equals the original morphism at that index followed by `eqToHom` of the
pointwise equality.
-/
lemma pi_fiber_comp_eqToHom_at_idx {x y z : ∀ i, C i}
    (f : x ⟶ y) (h : y = z) (i : I) :
    (f ≫ eqToHom h) i = f i ≫ eqToHom (congrFun h i) := by
  simp only [pi_comp_at_idx, pi_eqToHom_at_idx]

/--
In a pi category, `eqToHom` of a function equality evaluated at an index equals
`eqToHom` of the pointwise equality.
-/
lemma eqToHom_pi_apply {D : Type w} [Category D] {F G : I → D}
    (h : F = G) (i : I) : (eqToHom h) i = eqToHom (congrFun h i) := by
  subst h
  rfl

end PiCategory

end GebLean

namespace CategoryTheory

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

end CategoryTheory
