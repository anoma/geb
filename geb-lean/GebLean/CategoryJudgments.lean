import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import GebLean.Utilities
import GebLean.AcyclicCat

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

namespace GebLean

namespace CategoryJudgments

/-- The objects of the category judgment category -/
inductive Obj : Type where
  | obj  : Obj  -- represents the type of objects
  | mor  : Obj  -- represents the type of morphisms
  | id   : Obj  -- represents identity judgments
  | comp : Obj  -- represents composition judgments
  deriving DecidableEq, Inhabited, Repr

/-- The non-identity morphisms of the category judgment category.
    These form a semicategory, and identities will be adjoined. -/
inductive SemiHom : Obj → Obj → Type where
  -- Morphisms from Mor to Obj (domain and codomain)
  | dom : SemiHom Obj.mor Obj.obj
  | cod : SemiHom Obj.mor Obj.obj

  -- Morphisms from Id
  | idObj : SemiHom Obj.id Obj.obj  -- which object this is an identity for
  | idMor : SemiHom Obj.id Obj.mor  -- which morphism is the identity

  -- Morphisms from Comp to Mor
  | left      : SemiHom Obj.comp Obj.mor  -- morphism being post-composed
  | right     : SemiHom Obj.comp Obj.mor  -- morphism being pre-composed
  | composite : SemiHom Obj.comp Obj.mor  -- resulting composite

  -- Morphisms from Comp to Obj
  | intermediate  : SemiHom Obj.comp Obj.obj  -- shared intermediate object
  | compositeDom  : SemiHom Obj.comp Obj.obj  -- domain of composite
  | compositeCod  : SemiHom Obj.comp Obj.obj  -- codomain of composite
  deriving DecidableEq, Repr

/-- Composition of non-identity morphisms in the semicategory -/
def SemiHom.comp : ∀ {X Y Z : Obj}, SemiHom X Y → SemiHom Y Z → SemiHom X Z
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

@[simp] theorem SemiHom.comp_idMor_dom : idMor.comp dom = idObj := rfl
@[simp] theorem SemiHom.comp_idMor_cod : idMor.comp cod = idObj := rfl
@[simp] theorem SemiHom.comp_left_dom : left.comp dom = intermediate := rfl
@[simp] theorem SemiHom.comp_left_cod : left.comp cod = compositeCod := rfl
@[simp] theorem SemiHom.comp_right_dom : right.comp dom = compositeDom := rfl
@[simp] theorem SemiHom.comp_right_cod : right.comp cod = intermediate := rfl
@[simp] theorem SemiHom.comp_composite_dom :
    composite.comp dom = compositeDom := rfl
@[simp] theorem SemiHom.comp_composite_cod :
    composite.comp cod = compositeCod := rfl

/-- Associativity of composition in the semicategory -/
theorem SemiHom.assoc : ∀ {W X Y Z : Obj} (f : SemiHom W X) (g : SemiHom X Y)
    (h : SemiHom Y Z), (f.comp g).comp h = f.comp (g.comp h) := by
  intros W X Y Z f g h
  cases f <;> cases g <;> cases h

/-- Quiver instance for CategoryJudgments.Obj -/
instance : Quiver Obj where
  Hom := SemiHom

/-- Semicategory structure on CategoryJudgments.Obj -/
instance instSemicategoryStructObj : SemicategoryStruct Obj where
  comp := SemiHom.comp
  assoc := SemiHom.assoc

/-- TopologicalOrder on CategoryJudgments.Obj.
    Examining the edges:
    - mor → obj (dom, cod)
    - id → obj (idObj)
    - id → mor (idMor)
    - comp → obj (intermediate, compositeDom, compositeCod)
    - comp → mor (left, right, composite)
    Note that comp and id have no edges between them, so they are incomparable.
    The ordering is: {comp, id} < mor < obj -/
instance instPartialOrderObj : PartialOrder Obj where
  le a b := match a, b with
    | Obj.obj, Obj.obj => True
    | Obj.obj, _ => False
    | Obj.mor, Obj.obj => True
    | Obj.mor, Obj.mor => True
    | Obj.mor, _ => False
    | Obj.id, Obj.obj => True
    | Obj.id, Obj.mor => True
    | Obj.id, Obj.id => True
    | Obj.id, Obj.comp => False
    | Obj.comp, Obj.obj => True
    | Obj.comp, Obj.mor => True
    | Obj.comp, Obj.id => False
    | Obj.comp, Obj.comp => True
  le_refl := by intro x; cases x <;> trivial
  le_trans := by
    intros a b c hab hbc
    cases a <;> cases b <;> cases c <;> trivial
  le_antisymm := by
    intros a b hab hba
    cases a <;> cases b <;> trivial
  lt_iff_le_not_ge := by
    intros a b
    cases a <;> cases b <;> decide

/-- AcyclicQuiver instance for CategoryJudgments.Obj -/
instance : AcyclicQuiver Obj where
  toQuiver := inferInstance
  toPartialOrder := instPartialOrderObj
  edgesIncrease := fun {a b} f => by cases a <;> cases b <;> cases f <;> trivial

/-- Semicategory instance for CategoryJudgments.Obj -/
instance instSemicategoryObj : Semicategory Obj where
  toQuiver := inferInstance
  toSemicategoryStruct := instSemicategoryStructObj

/-- AcyclicCategory instance for CategoryJudgments.Obj -/
instance instAcyclicCategoryObj : AcyclicCategory Obj where
  toSemicategoryStruct := instSemicategoryStructObj

/-- The full Hom type with adjoined identities -/
abbrev Hom := Semicategory.AdjoinedIdHom (V := Obj)

/-- The category structure on CategoryJudgments with adjoined identities -/
instance : CategoryTheory.Category Obj :=
  Semicategory.adjoinedIdCategory

/-- DecidableEq on morphisms with adjoined identities, derived from the
    generic utility Semicategory.AdjoinedIdHom.decidableEq applied to the
    DecidableEq on SemiHom (which comes from deriving). -/
instance (X Y : Obj) : DecidableEq (Hom X Y) :=
  Semicategory.AdjoinedIdHom.decidableEq
    (fun A B => fun (f g : SemiHom A B) => decEq f g) X Y

/-- Fintype instance for objects -/
instance : Fintype Obj where
  elems := {Obj.obj, Obj.mor, Obj.id, Obj.comp}
  complete := by intro x; cases x <;> simp

/-- Fintype instance for semicategory morphisms (non-identity morphisms) -/
instance : ∀ (X Y : Obj), Fintype (SemiHom X Y)
  | .obj, .obj => ⟨∅, by intro f; cases f⟩
  | .obj, .mor => ⟨∅, by intro f; cases f⟩
  | .obj, .id => ⟨∅, by intro f; cases f⟩
  | .obj, .comp => ⟨∅, by intro f; cases f⟩
  | .mor, .obj => ⟨{SemiHom.dom, SemiHom.cod}, by intro f; cases f <;> simp⟩
  | .mor, .mor => ⟨∅, by intro f; cases f⟩
  | .mor, .id => ⟨∅, by intro f; cases f⟩
  | .mor, .comp => ⟨∅, by intro f; cases f⟩
  | .id, .obj => ⟨{SemiHom.idObj}, by intro f; cases f; simp⟩
  | .id, .mor => ⟨{SemiHom.idMor}, by intro f; cases f; simp⟩
  | .id, .id => ⟨∅, by intro f; cases f⟩
  | .id, .comp => ⟨∅, by intro f; cases f⟩
  | .comp, .obj => ⟨{SemiHom.intermediate, SemiHom.compositeDom,
                      SemiHom.compositeCod}, by intro f; cases f <;> simp⟩
  | .comp, .mor => ⟨{SemiHom.left, SemiHom.right, SemiHom.composite}, by
      intro f; cases f <;> simp⟩
  | .comp, .id => ⟨∅, by intro f; cases f⟩
  | .comp, .comp => ⟨∅, by intro f; cases f⟩

/-- FinQuiverWitness for the semicategory structure (non-identity
    morphisms only). -/
def semiFinQuiverWitness : @FinQuiverWitness Obj instSemicategoryObj.toQuiver
    where
  fintypeVertex := inferInstance
  fintypeEdge := fun X Y => inferInstanceAs (Fintype (SemiHom X Y))

/-- FinQuiverWitness for the category with adjoined identities, derived from
    the semicategory witness using the generic utility. -/
def finQuiverWitness :
    @FinQuiverWitness Obj Semicategory.adjoinedIdCategory.toQuiver :=
  @Semicategory.AdjoinedIdHom.finQuiverWitness Obj instSemicategoryObj
    inferInstance semiFinQuiverWitness

/-- Fintype instance for morphisms with adjoined identities, derived from
    the FinQuiverWitness. -/
instance (X Y : Obj) : Fintype (Hom X Y) :=
  @FinQuiverWitness.fintypeEdge Obj Semicategory.adjoinedIdCategory.toQuiver
    finQuiverWitness X Y

/-- The category of category judgments is a finite category -/
instance : CategoryTheory.FinCategory Obj where
  fintypeHom := fun X Y => inferInstanceAs (Fintype (Hom X Y))

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

/-- Helper function to map a SemiHom to a morphism in C. -/
def mapSemiHom (data : FunctorData C) : ∀ {X Y : Obj}, SemiHom X Y →
    ((match X with | .obj => data.objC | .mor => data.morC
                   | .id => data.idC | .comp => data.compC) ⟶
     (match Y with | .obj => data.objC | .mor => data.morC
                   | .id => data.idC | .comp => data.compC))
  | .mor, .obj, .dom => data.dom
  | .mor, .obj, .cod => data.cod
  | .id, .obj, .idObj => data.idMor ≫ data.dom
  | .id, .mor, .idMor => data.idMor
  | .comp, .mor, .left => data.left
  | .comp, .mor, .right => data.right
  | .comp, .mor, .composite => data.composite
  | .comp, .obj, .intermediate => data.right ≫ data.cod
  | .comp, .obj, .compositeDom => data.right ≫ data.dom
  | .comp, .obj, .compositeCod => data.left ≫ data.cod

/-- Construct a functor from CategoryJudgments to C from minimal
    category data. The caller provides only primitive morphisms and
    compatibility conditions; derived morphisms are computed. -/
def mkFunctor (data : FunctorData C) : Obj ⥤ C where
  obj
    | .obj => data.objC
    | .mor => data.morC
    | .id => data.idC
    | .comp => data.compC
  map {X Y} f := match f with
    | Semicategory.AdjoinedIdHom.id _ => 𝟙 _
    | Semicategory.AdjoinedIdHom.hom g => mapSemiHom data g
  map_id := by intro X; rfl
  map_comp {X Y Z} f g := by
    cases f with
    | id =>
      cases g with
      | id =>
        change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        simp
      | hom g' =>
        change mapSemiHom data g' = 𝟙 _ ≫ mapSemiHom data g'
        simp
    | hom f' =>
      cases g with
      | id =>
        change mapSemiHom data f' = mapSemiHom data f' ≫ 𝟙 _
        simp
      | hom g' =>
        change mapSemiHom data (SemiHom.comp f' g') =
               mapSemiHom data f' ≫ mapSemiHom data g'
        cases f' <;> cases g' <;> simp [mapSemiHom, SemiHom.comp,
          data.h_id_endo, data.h_comp_match, data.h_comp_dom, data.h_comp_cod]

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
  dom := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.dom)
  cod := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.cod)
  idMor := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.idMor)
  left := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.left)
  right := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.right)
  composite := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.composite)
  h_id_endo := by
    calc F.map (Semicategory.AdjoinedIdHom.hom SemiHom.idMor) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.dom)
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.idMor ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.dom) := (F.map_comp _ _).symm
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.idObj) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.idMor ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.cod) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.idMor) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.cod) := F.map_comp _ _
  h_comp_match := by
    calc F.map (Semicategory.AdjoinedIdHom.hom SemiHom.right) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.cod)
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.right ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.cod) := (F.map_comp _ _).symm
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.intermediate) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.left ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.dom) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.left) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.dom) := F.map_comp _ _
  h_comp_dom := by
    calc F.map (Semicategory.AdjoinedIdHom.hom SemiHom.composite) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.dom)
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.composite ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.dom) := (F.map_comp _ _).symm
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.compositeDom) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.right ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.dom) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.right) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.dom) := F.map_comp _ _
  h_comp_cod := by
    calc F.map (Semicategory.AdjoinedIdHom.hom SemiHom.composite) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.cod)
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.composite ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.cod) := (F.map_comp _ _).symm
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.compositeCod) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.left ≫
                 Semicategory.AdjoinedIdHom.hom SemiHom.cod) :=
          congrArg F.map rfl
      _ = F.map (Semicategory.AdjoinedIdHom.hom SemiHom.left) ≫
           F.map (Semicategory.AdjoinedIdHom.hom SemiHom.cod) := F.map_comp _ _

/-- Round-tripping a functor through functorToData gives back the
    original functor. -/
theorem mkFunctor_functorToData (F : Obj ⥤ C) :
    mkFunctor (functorToData F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro X; cases X <;> rfl
  case h_map =>
    intro X Y f
    cases f with
    | id =>
      cases X <;> (simp [mkFunctor, functorToData]; exact (F.map_id _).symm)
    | hom f' =>
      cases f' <;> simp only [mkFunctor, functorToData, mapSemiHom,
        eqToHom_refl, Category.comp_id, Category.id_comp]
      case idObj =>
        rw [← F.map_comp]
        exact congrArg F.map rfl
      case intermediate =>
        rw [← F.map_comp]
        exact congrArg F.map rfl
      case compositeDom =>
        rw [← F.map_comp]
        exact congrArg F.map rfl
      case compositeCod =>
        rw [← F.map_comp]
        exact congrArg F.map rfl

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
  naturality_dom := α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.dom)
  naturality_cod := α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.cod)
  naturality_idMor :=
    α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.idMor)
  naturality_left := α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.left)
  naturality_right :=
    α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.right)
  naturality_composite :=
    α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.composite)

/-- Construct a natural transformation from NatTransData. -/
def mkNatTrans {F G : FunctorData C} (α : NatTransData F G) :
    mkFunctor F ⟶ mkFunctor G where
  app X := match X with
    | .obj => α.appObj
    | .mor => α.appMor
    | .id => α.appId
    | .comp => α.appComp
  naturality X Y f := by
    cases f with
    | id => simp only [mkFunctor, Category.comp_id, Category.id_comp]
    | hom f' =>
      cases f' <;> simp only [mkFunctor]
      case dom => exact α.naturality_dom
      case cod => exact α.naturality_cod
      case idObj => exact α.naturality_idObj
      case idMor => exact α.naturality_idMor
      case intermediate => exact α.naturality_intermediate
      case compositeDom => exact α.naturality_compositeDom
      case compositeCod => exact α.naturality_compositeCod
      case left => exact α.naturality_left
      case right => exact α.naturality_right
      case composite => exact α.naturality_composite

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

/-- The two functors form a categorical isomorphism: they compose to the
    identity functor in both directions. -/
def functorDataIsoCat : FunctorData C ≅Cat (Obj ⥤ C) where
  hom := functorDataToFunctor
  inv := functorToFunctorData
  hom_inv_id := functorDataToFunctor_comp_functorToFunctorData
  inv_hom_id := functorToFunctorData_comp_functorDataToFunctor

/-- The two functors form an equivalence of categories (derived from the
    isomorphism). -/
def functorDataEquivCat : FunctorData C ≌ (Obj ⥤ C) :=
  Cat.equivOfIso functorDataIsoCat

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

end GebLean
