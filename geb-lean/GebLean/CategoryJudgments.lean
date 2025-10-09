import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import GebLean.Utilities

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

section FunctorDataCategory

/-- Data required to construct a functor from CategoryJudgments to C. -/
@[ext]
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

/-- Minimal data needed to specify a natural transformation between two
    FunctorData structures. We only need the components at the 4 objects plus
    naturality conditions for the 6 basic morphisms (dom, cod, idMor, left,
    right, composite); the remaining 4 conditions (intermediate, compositeDom,
    compositeCod, idObj) are derivable. -/
@[ext]
structure NatTransData {C : Type*} [Category C]
    (F G : FunctorData C) where
  appObj : F.objC ⟶ G.objC
  appMor : F.morC ⟶ G.morC
  appId : F.idC ⟶ G.idC
  appComp : F.compC ⟶ G.compC
  naturality_dom : F.dom ≫ appObj = appMor ≫ G.dom
  naturality_cod : F.cod ≫ appObj = appMor ≫ G.cod
  naturality_idMor : F.idMor ≫ appMor = appId ≫ G.idMor
  naturality_left : F.left ≫ appMor = appComp ≫ G.left
  naturality_right : F.right ≫ appMor = appComp ≫ G.right
  naturality_composite : F.composite ≫ appMor = appComp ≫ G.composite

/-- Identity natural transformation for FunctorData. -/
def NatTransData.id (F : FunctorData C) : NatTransData F F where
  appObj := 𝟙 F.objC
  appMor := 𝟙 F.morC
  appId := 𝟙 F.idC
  appComp := 𝟙 F.compC
  naturality_dom := by simp
  naturality_cod := by simp
  naturality_idMor := by simp
  naturality_left := by simp
  naturality_right := by simp
  naturality_composite := by simp

/-- Composition of natural transformations for FunctorData. -/
def NatTransData.comp {F G H : FunctorData C}
    (α : NatTransData F G) (β : NatTransData G H) :
    NatTransData F H where
  appObj := α.appObj ≫ β.appObj
  appMor := α.appMor ≫ β.appMor
  appId := α.appId ≫ β.appId
  appComp := α.appComp ≫ β.appComp
  naturality_dom := by
    rw [← Category.assoc, α.naturality_dom, Category.assoc, β.naturality_dom,
      ← Category.assoc]
  naturality_cod := by
    rw [← Category.assoc, α.naturality_cod, Category.assoc, β.naturality_cod,
      ← Category.assoc]
  naturality_idMor := by
    rw [← Category.assoc, α.naturality_idMor, Category.assoc,
      β.naturality_idMor, ← Category.assoc]
  naturality_left := by
    rw [← Category.assoc, α.naturality_left, Category.assoc,
      β.naturality_left, ← Category.assoc]
  naturality_right := by
    rw [← Category.assoc, α.naturality_right, Category.assoc,
      β.naturality_right, ← Category.assoc]
  naturality_composite := by
    rw [← Category.assoc, α.naturality_composite, Category.assoc,
      β.naturality_composite, ← Category.assoc]

/-- FunctorData with NatTransData forms a category. -/
instance : Category (FunctorData C) where
  Hom := NatTransData
  id := NatTransData.id
  comp := NatTransData.comp
  id_comp := by
    intros
    ext <;> simp [NatTransData.comp, NatTransData.id]
  comp_id := by
    intros
    ext <;> simp [NatTransData.comp, NatTransData.id]
  assoc := by
    intros
    ext <;> simp [NatTransData.comp, Category.assoc]

end FunctorDataCategory

section FunctorDataEquivalence

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

/-- Extract FunctorData from a functor. This is inverse to mkFunctor. -/
def functorToData {C : Type*} [Category C] (F : Obj ⥤ C) :
    FunctorData C where
  objC := F.obj .obj
  morC := F.obj .mor
  idC := F.obj .id
  compC := F.obj .comp
  dom := F.map .dom
  cod := F.map .cod
  idMor := F.map .idMor
  left := F.map .left
  right := F.map .right
  composite := F.map .composite
  h_id_endo := by
    calc F.map .idMor ≫ F.map .dom
      _ = F.map (.idMor ≫ .dom) := (F.map_comp _ _).symm
      _ = F.map .idObj := congrArg F.map Hom.comp_idMor_dom
      _ = F.map (.idMor ≫ .cod) := (congrArg F.map Hom.comp_idMor_cod).symm
      _ = F.map .idMor ≫ F.map .cod := F.map_comp _ _
  h_comp_match := by
    calc F.map .right ≫ F.map .cod
      _ = F.map (.right ≫ .cod) := (F.map_comp _ _).symm
      _ = F.map .intermediate := congrArg F.map Hom.comp_right_cod
      _ = F.map (.left ≫ .dom) := (congrArg F.map Hom.comp_left_dom).symm
      _ = F.map .left ≫ F.map .dom := F.map_comp _ _
  h_comp_dom := by
    calc F.map .composite ≫ F.map .dom
      _ = F.map (.composite ≫ .dom) := (F.map_comp _ _).symm
      _ = F.map .compositeDom := congrArg F.map Hom.comp_composite_dom
      _ = F.map (.right ≫ .dom) := (congrArg F.map Hom.comp_right_dom).symm
      _ = F.map .right ≫ F.map .dom := F.map_comp _ _
  h_comp_cod := by
    calc F.map .composite ≫ F.map .cod
      _ = F.map (.composite ≫ .cod) := (F.map_comp _ _).symm
      _ = F.map .compositeCod := congrArg F.map Hom.comp_composite_cod
      _ = F.map (.left ≫ .cod) := (congrArg F.map Hom.comp_left_cod).symm
      _ = F.map .left ≫ F.map .cod := F.map_comp _ _

/-- Round-tripping a functor through functorToData gives back the
    original functor. -/
theorem mkFunctor_functorToData (F : Obj ⥤ C) :
    mkFunctor (functorToData F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro X; cases X <;> rfl
  case h_map =>
    intro X Y f
    cases X <;> cases Y <;> cases f <;> (
      simp only [mkFunctor, functorToData, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      try rfl
      try exact (F.map_id _).symm
      try (rw [← F.map_comp]; rfl)
    )

theorem functorToData_mkFunctor (data : FunctorData C) :
    functorToData (mkFunctor data) = data := by
  cases data
  rfl

/-- The equivalence between functors from Obj to C and FunctorData C. -/
def functorDataEquiv : FunctorData C ≃ (Obj ⥤ C) where
  toFun := mkFunctor
  invFun := functorToData
  left_inv := functorToData_mkFunctor
  right_inv := mkFunctor_functorToData

/-- Extract CopresheafData from a copresheaf (functor to Type). -/
abbrev copresheafToData := functorToData (C := Type _)

/-- The equivalence between copresheaves and CopresheafData. -/
abbrev copresheafDataEquiv := functorDataEquiv (C := Type _)

/-- Naturality for the composite morphism `intermediate = right ≫ cod` is
    derivable from naturality for `right` and `cod`. -/
theorem NatTransData.naturality_intermediate {C : Type*} [Category C]
    {F G : FunctorData C} (α : NatTransData F G) :
    (F.right ≫ F.cod) ≫ α.appObj = α.appComp ≫ (G.right ≫ G.cod) := by
  rw [Category.assoc, α.naturality_cod, ← Category.assoc, α.naturality_right,
    Category.assoc]

/-- Naturality for the composite morphism `compositeDom = right ≫ dom` is
    derivable from naturality for `right` and `dom`. -/
theorem NatTransData.naturality_compositeDom {C : Type*} [Category C]
    {F G : FunctorData C} (α : NatTransData F G) :
    (F.right ≫ F.dom) ≫ α.appObj = α.appComp ≫ (G.right ≫ G.dom) := by
  rw [Category.assoc, α.naturality_dom, ← Category.assoc, α.naturality_right,
    Category.assoc]

/-- Naturality for the composite morphism `compositeCod = left ≫ cod` is
    derivable from naturality for `left` and `cod`. -/
theorem NatTransData.naturality_compositeCod {C : Type*} [Category C]
    {F G : FunctorData C} (α : NatTransData F G) :
    (F.left ≫ F.cod) ≫ α.appObj = α.appComp ≫ (G.left ≫ G.cod) := by
  rw [Category.assoc, α.naturality_cod, ← Category.assoc, α.naturality_left,
    Category.assoc]

/-- Naturality for the composite morphism `idObj = idMor ≫ dom` is derivable
    from naturality for `idMor` and `dom`. -/
theorem NatTransData.naturality_idObj {C : Type*} [Category C]
    {F G : FunctorData C} (α : NatTransData F G) :
    (F.idMor ≫ F.dom) ≫ α.appObj = α.appId ≫ (G.idMor ≫ G.dom) := by
  rw [Category.assoc, α.naturality_dom, ← Category.assoc, α.naturality_idMor,
    Category.assoc]

/-- Extract NatTransData from a natural transformation. -/
def natTransToData {F G : Obj ⥤ C} (α : F ⟶ G) :
    NatTransData (functorToData F) (functorToData G) where
  appObj := α.app .obj
  appMor := α.app .mor
  appId := α.app .id
  appComp := α.app .comp
  naturality_dom := α.naturality Hom.dom
  naturality_cod := α.naturality Hom.cod
  naturality_idMor := α.naturality Hom.idMor
  naturality_left := α.naturality Hom.left
  naturality_right := α.naturality Hom.right
  naturality_composite := α.naturality Hom.composite

/-- Construct a natural transformation from NatTransData. -/
def mkNatTrans {F G : FunctorData C} (α : NatTransData F G) :
    mkFunctor F ⟶ mkFunctor G where
  app X := match X with
    | .obj => α.appObj
    | .mor => α.appMor
    | .id => α.appId
    | .comp => α.appComp
  naturality X Y f := by
    cases X <;> cases Y <;> cases f
    all_goals simp only [mkFunctor, Category.comp_id, Category.id_comp]
    case mor.obj.dom => exact α.naturality_dom
    case mor.obj.cod => exact α.naturality_cod
    case id.obj.idObj => exact α.naturality_idObj
    case id.mor.idMor => exact α.naturality_idMor
    case comp.obj.intermediate => exact α.naturality_intermediate
    case comp.obj.compositeDom => exact α.naturality_compositeDom
    case comp.obj.compositeCod => exact α.naturality_compositeCod
    case comp.mor.left => exact α.naturality_left
    case comp.mor.right => exact α.naturality_right
    case comp.mor.composite => exact α.naturality_composite

/-- Converting a NatTransData to a natural transformation and extracting
    back gives the original NatTransData. -/
theorem natTransToData_mkNatTrans {F G : FunctorData C}
    (α : NatTransData F G) :
    natTransToData (mkNatTrans α) = α := by
  cases α
  rfl

/-- Extracting NatTransData from a natural transformation and converting
    back gives the original natural transformation (modulo the required
    eqToHom cast along the functor equality mkFunctor ∘ functorToData = id). -/
theorem mkNatTrans_natTransToData {F G : Obj ⥤ C} (α : F ⟶ G) :
    mkNatTrans (natTransToData α) =
    eqToHom (mkFunctor_functorToData F) ≫ α ≫
    eqToHom (mkFunctor_functorToData G).symm := by
  ext X
  cases X <;> simp [mkNatTrans, natTransToData]

/-- The functor from FunctorData to the functor category that sends
    FunctorData to the corresponding functor via mkFunctor. -/
def functorDataToFunctor : FunctorData C ⥤ (Obj ⥤ C) where
  obj := mkFunctor
  map := mkNatTrans
  map_id := by
    intro F
    ext X
    cases X <;> rfl
  map_comp := by
    intros F G H α β
    ext X
    cases X <;> rfl

/-- The functor from the functor category to FunctorData that sends
    functors to their corresponding FunctorData via functorToData. -/
def functorToFunctorData : (Obj ⥤ C) ⥤ FunctorData C where
  obj := functorToData
  map := natTransToData
  map_id := by
    intro F
    rfl
  map_comp := by
    intros F G H α β
    rfl

/-- The composition functorToFunctorData ⋙ functorDataToFunctor is
    equal to the identity functor. -/
theorem functorToFunctorData_comp_functorDataToFunctor :
    functorToFunctorData ⋙ functorDataToFunctor = 𝟭 (Obj ⥤ C) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro F; exact mkFunctor_functorToData F
  case h_map =>
    intro F G α
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
      Functor.id_map, functorToFunctorData, functorDataToFunctor,
      mkNatTrans_natTransToData]

/-- The composition functorDataToFunctor ⋙ functorToFunctorData is
    equal to the identity functor. -/
theorem functorDataToFunctor_comp_functorToFunctorData :
    functorDataToFunctor ⋙ functorToFunctorData = 𝟭 (FunctorData C) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro F; exact functorToData_mkFunctor F
  case h_map =>
    intro F G α
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
      Functor.id_map, functorToFunctorData, functorDataToFunctor,
      natTransToData_mkNatTrans]
    simp

/-- The two functors form an equivalence of categories where the unit and
    counit are identity natural transformations (not just isomorphisms).
    This is stronger than a general equivalence. -/
def functorDataEquivCat : FunctorData C ≌ (Obj ⥤ C) where
  functor := functorDataToFunctor
  inverse := functorToFunctorData
  unitIso := eqToIso functorDataToFunctor_comp_functorToFunctorData
  counitIso := eqToIso functorToFunctorData_comp_functorDataToFunctor
  functor_unitIso_comp := by
    intro F
    simp

/-- Two FunctorData structures are equivalent if their corresponding functors
    are naturally isomorphic. -/
def FunctorData.Equiv (data₁ data₂ : FunctorData C) : Prop :=
  Nonempty (mkFunctor data₁ ≅ mkFunctor data₂)

/-- Natural isomorphism on functors induces an equivalence relation on
    FunctorData via mkFunctor. -/
instance : Setoid (FunctorData C) where
  r := FunctorData.Equiv
  iseqv := {
    refl := fun _ => ⟨Iso.refl _⟩
    symm := fun ⟨iso⟩ => ⟨iso.symm⟩
    trans := fun ⟨iso₁⟩ ⟨iso₂⟩ => ⟨iso₁.trans iso₂⟩
  }

/-- Two `FunctorData` are isomorphic in the category if and only if they are
    equivalent under the Setoid. This follows from the categorical equivalence
    `functorDataEquivCat` and the fact that functors preserve isomorphisms. -/
theorem functorData_iso_iff_setoid_equiv (F G : FunctorData C) :
    Nonempty (F ≅ G) ↔ F ≈ G := by
  change Nonempty (F ≅ G) ↔ Nonempty (mkFunctor F ≅ mkFunctor G)
  constructor
  · intro ⟨e⟩
    exact ⟨functorDataToFunctor.mapIso e⟩
  · intro ⟨e⟩
    exact ⟨functorDataEquivCat.inverse.mapIso e⟩

end FunctorDataEquivalence

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

end CategoryCopresheafCorrespondence

end CategoryJudgments
