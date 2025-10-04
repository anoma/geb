import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Category Judgments

This file defines a finite category whose objects represent the components
needed to specify a category, and whose morphisms represent the
relationships between them.

A category can be defined as a copresheaf (covariant functor to Type)
on this category, where:
- The object `Obj` maps to the type of objects
- The object `Mor` maps to the type of morphisms
- The object `Id` maps to the type of identity judgments
- The object `Comp` maps to the type of composition judgments

The morphisms encode the structure:
- `dom, cod : Mor → Obj` give domain and codomain of morphisms
- `idObj : Id → Obj` and `idMor : Id → Mor` specify which morphism is
  identity for which object
- `left, right, composite : Comp → Mor` specify composition triples
  (where left and right compose to give composite)
- `intermediate, compositeDom, compositeCod : Comp → Obj` specify the
  relevant objects

The categorical structure encodes type correctness constraints:
- `idMor ≫ dom = idObj` and `idMor ≫ cod = idObj` ensure identities
  are endomorphisms
- `right ≫ cod = intermediate` and `left ≫ dom = intermediate` ensure
  composable morphisms share an intermediate object
- `right ≫ dom = compositeDom` and `composite ≫ dom = compositeDom`
  ensure domain is preserved
- `left ≫ cod = compositeCod` and `composite ≫ cod = compositeCod`
  ensure codomain is preserved
-/

namespace CategoryJudgments

/-- The objects of the category judgment category -/
inductive Obj : Type where
  | obj  : Obj  -- represents the type of objects
  | mor  : Obj  -- represents the type of morphisms
  | id   : Obj  -- represents identity judgments
  | comp : Obj  -- represents composition judgments
  deriving DecidableEq, Inhabited, Repr

/-- The morphisms of the category judgment category -/
inductive Hom : Obj → Obj → Type where
  -- Identity morphisms
  | identity (X : Obj) : Hom X X

  -- Morphisms from Mor to Obj (domain and codomain)
  | dom : Hom Obj.mor Obj.obj
  | cod : Hom Obj.mor Obj.obj

  -- Morphisms from Id
  | idObj : Hom Obj.id Obj.obj  -- which object this is an identity for
  | idMor : Hom Obj.id Obj.mor  -- which morphism is the identity

  -- Morphisms from Comp to Mor
  | left      : Hom Obj.comp Obj.mor  -- morphism being post-composed
  | right     : Hom Obj.comp Obj.mor  -- morphism being pre-composed
  | composite : Hom Obj.comp Obj.mor  -- resulting composite

  -- Morphisms from Comp to Obj
  | intermediate  : Hom Obj.comp Obj.obj  -- shared intermediate object
  | compositeDom  : Hom Obj.comp Obj.obj  -- domain of composite
  | compositeCod  : Hom Obj.comp Obj.obj  -- codomain of composite
  deriving DecidableEq, Repr

/-- Composition of morphisms in the category judgment category -/
def Hom.comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  -- Identity laws
  | _, _, _, identity _, f => f
  | _, _, _, f, identity _ => f

  -- Compositions from Id to Obj (idMor ≫ dom/cod = idObj)
  | _, _, _, idMor, dom => idObj
  | _, _, _, idMor, cod => idObj

  -- Compositions from Comp to Obj via Mor
  | _, _, _, left, dom => intermediate
  | _, _, _, left, cod => compositeCod
  | _, _, _, right, dom => compositeDom
  | _, _, _, right, cod => intermediate
  | _, _, _, composite, dom => compositeDom
  | _, _, _, composite, cod => compositeCod

@[simp] theorem Hom.comp_idMor_dom : idMor.comp dom = idObj := rfl
@[simp] theorem Hom.comp_idMor_cod : idMor.comp cod = idObj := rfl
@[simp] theorem Hom.comp_left_dom : left.comp dom = intermediate := rfl
@[simp] theorem Hom.comp_left_cod : left.comp cod = compositeCod := rfl
@[simp] theorem Hom.comp_right_dom : right.comp dom = compositeDom := rfl
@[simp] theorem Hom.comp_right_cod : right.comp cod = intermediate := rfl
@[simp] theorem Hom.comp_composite_dom :
    composite.comp dom = compositeDom := rfl
@[simp] theorem Hom.comp_composite_cod :
    composite.comp cod = compositeCod := rfl

/-- Left identity law for composition -/
theorem Hom.id_comp : ∀ {X Y : Obj} (f : Hom X Y),
    (identity X).comp f = f
  | _, _, identity _ => rfl
  | _, _, dom => rfl
  | _, _, cod => rfl
  | _, _, idObj => rfl
  | _, _, idMor => rfl
  | _, _, left => rfl
  | _, _, right => rfl
  | _, _, composite => rfl
  | _, _, intermediate => rfl
  | _, _, compositeDom => rfl
  | _, _, compositeCod => rfl

/-- Right identity law for composition -/
theorem Hom.comp_id : ∀ {X Y : Obj} (f : Hom X Y),
    f.comp (identity Y) = f
  | _, _, identity _ => rfl
  | _, _, dom => rfl
  | _, _, cod => rfl
  | _, _, idObj => rfl
  | _, _, idMor => rfl
  | _, _, left => rfl
  | _, _, right => rfl
  | _, _, composite => rfl
  | _, _, intermediate => rfl
  | _, _, compositeDom => rfl
  | _, _, compositeCod => rfl

/-- Associativity of composition -/
theorem Hom.assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y)
    (h : Hom Y Z), (f.comp g).comp h = f.comp (g.comp h) := by
  intros W X Y Z f g h
  -- All paths have length at most 2, so we check all cases
  cases f <;> cases g <;> (try cases h) <;> rfl

/-- The category structure on CategoryJudgments -/
instance : CategoryTheory.CategoryStruct Obj where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp

instance : CategoryTheory.Category Obj where
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Fintype instance for objects -/
instance : Fintype Obj where
  elems := {Obj.obj, Obj.mor, Obj.id, Obj.comp}
  complete := by intro x; cases x <;> simp

/-- Fintype instance for morphisms -/
instance : ∀ (X Y : Obj), Fintype (Hom X Y)
  | .obj, .obj => ⟨{.identity .obj}, by intro f; cases f; simp⟩
  | .obj, .mor => ⟨∅, by intro f; cases f⟩
  | .obj, .id => ⟨∅, by intro f; cases f⟩
  | .obj, .comp => ⟨∅, by intro f; cases f⟩
  | .mor, .obj => ⟨{.dom, .cod}, by intro f; cases f <;> simp⟩
  | .mor, .mor => ⟨{.identity .mor}, by intro f; cases f; simp⟩
  | .mor, .id => ⟨∅, by intro f; cases f⟩
  | .mor, .comp => ⟨∅, by intro f; cases f⟩
  | .id, .obj => ⟨{.idObj}, by intro f; cases f; simp⟩
  | .id, .mor => ⟨{.idMor}, by intro f; cases f; simp⟩
  | .id, .id => ⟨{.identity .id}, by intro f; cases f; simp⟩
  | .id, .comp => ⟨∅, by intro f; cases f⟩
  | .comp, .obj => ⟨{.intermediate, .compositeDom, .compositeCod},
                    by intro f; cases f <;> simp⟩
  | .comp, .mor => ⟨{.left, .right, .composite},
                    by intro f; cases f <;> simp⟩
  | .comp, .id => ⟨∅, by intro f; cases f⟩
  | .comp, .comp => ⟨{.identity .comp}, by intro f; cases f; simp⟩

/-- Fintype instance for category theory morphisms -/
instance (X Y : Obj) : Fintype (X ⟶ Y) :=
  inferInstanceAs (Fintype (Hom X Y))

/-- The category of category judgments is a finite category -/
instance : CategoryTheory.FinCategory Obj where

/-- The opposite of the category judgment category is also finite
    (automatically via `CategoryTheory.finCategoryOpposite`). -/
instance instJudgmentCatOpFinite :
    CategoryTheory.FinCategory Objᵒᵖ := inferInstance

section Functors

open CategoryTheory

variable {C : Type*} [Category C]

/-- Data required to construct a functor from CategoryJudgments to C. -/
structure FunctorData (C : Type*) [Category C] where
  objC : C
  morC : C
  idC : C
  compC : C
  dom : morC ⟶ objC
  cod : morC ⟶ objC
  idMor : idC ⟶ morC
  left : compC ⟶ morC
  right : compC ⟶ morC
  composite : compC ⟶ morC
  h_id_endo : idMor ≫ dom = idMor ≫ cod
  h_comp_match : right ≫ cod = left ≫ dom
  h_comp_dom : composite ≫ dom = right ≫ dom
  h_comp_cod : composite ≫ cod = left ≫ cod

/-- Construct a functor from CategoryJudgments to C from minimal
    category data. The caller provides only primitive morphisms and
    compatibility conditions; derived morphisms are computed. -/
def mkFunctor (data : FunctorData C) : Obj ⥤ C where
  obj
    | .obj => data.objC
    | .mor => data.morC
    | .id => data.idC
    | .comp => data.compC
  map {X Y} f := match X, Y, f with
    | _, _, .identity _ => 𝟙 _
    | _, _, .dom => data.dom
    | _, _, .cod => data.cod
    | _, _, .idObj => data.idMor ≫ data.dom
    | _, _, .idMor => data.idMor
    | _, _, .left => data.left
    | _, _, .right => data.right
    | _, _, .composite => data.composite
    | _, _, .intermediate => data.right ≫ data.cod
    | _, _, .compositeDom => data.right ≫ data.dom
    | _, _, .compositeCod => data.left ≫ data.cod
  map_id := by intro X; cases X <;> rfl
  map_comp {X Y Z} f g := by
    cases f <;> cases g <;> (try rfl) <;>
      (simp_all only [Category.id_comp, Category.comp_id, data.h_id_endo,
        data.h_comp_match, data.h_comp_dom, data.h_comp_cod]) <;>
      (first | rfl)

/-- Construct a copresheaf (covariant functor into Type) from
    CategoryJudgments from minimal category data. -/
abbrev mkCopresheaf := mkFunctor (C := Type _)

/-- Data required to construct a copresheaf (functor to Type). -/
abbrev CopresheafData.{u} := FunctorData (Type u)

/-- Data for a category structure using dependent types. -/
structure DepCategoryData.{u} where
  objT : Type u
  morT : objT → objT → Type u
  idT : {o : objT} → morT o o → Type u
  compT : {a b c : objT} → morT a b → morT b c → morT a c → Type u

/-- Convert dependent category data to CopresheafData.
    The dependent types enforce the equality conditions automatically. -/
def depToFunctorData.{u} (data : DepCategoryData.{u}) :
    CopresheafData.{u} where
  -- Objects
  objC := data.objT
  -- Morphisms: domain, codomain, and morphism data
  morC := Σ (a b : data.objT), data.morT a b
  -- Identities: morphism that is an identity
  idC := Σ (o : data.objT) (m : data.morT o o), data.idT m
  -- Compositions: witness that h is the composite of f and g
  -- The dependent types ensure f : a→b, g : b→c, h : a→c
  compC := Σ (a b c : data.objT) (f : data.morT a b) (g : data.morT b c)
    (h : data.morT a c), data.compT f g h
  -- dom: extract source
  dom := fun m => m.1
  -- cod: extract target
  cod := fun m => m.2.1
  -- idMor: extract the morphism from an identity witness
  idMor := fun i => ⟨i.1, i.1, i.2.1⟩
  -- left: second morphism in composition (b → c, "post-composed")
  left := fun c => ⟨c.2.1, c.2.2.1, c.2.2.2.2.1⟩
  -- right: first morphism in composition (a → b, "pre-composed")
  right := fun c => ⟨c.1, c.2.1, c.2.2.2.1⟩
  -- composite: result of composition (a → c)
  composite := fun c => ⟨c.1, c.2.2.1, c.2.2.2.2.2.1⟩
  -- h_id_endo: idMor ≫ dom = idMor ≫ cod
  h_id_endo := by funext i; simp
  -- h_comp_match: right ≫ cod = left ≫ dom
  h_comp_match := by funext c; rfl
  -- h_comp_dom: composite ≫ dom = right ≫ dom
  h_comp_dom := by funext c; simp
  -- h_comp_cod: composite ≫ cod = left ≫ cod
  h_comp_cod := by funext c; simp

/-- Convert CopresheafData to dependent category data.
    This extracts the dependent type structure from the copresheaf. -/
def functorDataToDep.{u} (data : CopresheafData.{u}) :
    DepCategoryData.{u} where
  objT := data.objC
  morT := fun a b => {m : data.morC // data.dom m = a ∧ data.cod m = b}
  idT := fun m => {i : data.idC // data.idMor i = m.val}
  compT := fun {a b c} (f : {m : data.morC // data.dom m = a ∧ data.cod m = b})
              (g : {m : data.morC // data.dom m = b ∧ data.cod m = c})
              (h : {m : data.morC // data.dom m = a ∧ data.cod m = c}) =>
    {comp : data.compC // data.right comp = f.val ∧
                          data.left comp = g.val ∧
                          data.composite comp = h.val}

/-- Construct a copresheaf using dependent types to enforce equality
    conditions. Both identities and composition are represented as
    relations. The key insight is that since morphisms already encode
    their domains and codomains in their types, the compatibility
    conditions are enforced by the type structure. -/
def mkCopresheafDep.{u} (data : DepCategoryData.{u}) : Obj ⥤ Type u :=
  mkCopresheaf (depToFunctorData data)

/-- Round-tripping from DepCategoryData to CopresheafData and back
    preserves the object type. -/
theorem functorDataToDep_depToFunctorData_objT.{u} (data : DepCategoryData.{u}) :
    (functorDataToDep (depToFunctorData data)).objT = data.objT := rfl

/-- Round-tripping from CopresheafData to DepCategoryData and back
    preserves the object type. -/
theorem depToFunctorData_functorDataToDep_objC.{u} (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).objC = data.objC := rfl

end Functors

section CategoryCopresheafCorrespondence

open CategoryTheory

variable {C : Type*} [Category C]

/-- The functor category from CategoryJudgments to an arbitrary category C. -/
abbrev JudgmentFunctors (C : Type*) [Category C] := Obj ⥤ C

/-- The category of copresheaves on CategoryJudgments (functors to Type). -/
abbrev JudgmentCopresheaves.{u} := Obj ⥤ Type u

/-- Construct an object in the functor category from FunctorData. -/
abbrev mkJudgmentFunctor (data : FunctorData C) : JudgmentFunctors C :=
  mkFunctor data

/-- Construct an object in the copresheaf category from CopresheafData. -/
abbrev mkJudgmentCopresheaf.{u} (data : CopresheafData.{u}) :
    JudgmentCopresheaves.{u} :=
  mkCopresheaf data

/-- Construct an object in the copresheaf category from DepCategoryData. -/
abbrev mkJudgmentCopresheafDep.{u} (data : DepCategoryData.{u}) :
    JudgmentCopresheaves.{u} :=
  mkCopresheafDep data

end CategoryCopresheafCorrespondence

end CategoryJudgments
