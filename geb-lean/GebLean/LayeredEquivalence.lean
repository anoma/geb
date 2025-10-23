import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Comma.Over.Basic
import GebLean.Utilities
import GebLean.Semicategory

/-!
# Layered Equivalence between Copresheaves and Dependent Types

This file establishes the categorical equivalence between copresheaf
representations and dependent type representations of categorical structures,
built up in layers.

## Layer 1: Objects and Morphisms

We define a 2-object category (simpler version of CategoryJudgments):
- Object `obj` (representing types of objects)
- Object `mor` (representing types of morphisms)
- Morphisms `dom, cod : mor → obj` (domain and codomain)

This is categorically equivalent to the dependent type representation:
```lean
structure DepData where
  objT : Type
  morT : objT → objT → Type
```

The equivalence `layer1Equivalence : DepData ≌ CopresheafData` demonstrates
that copresheaf structure maps (like `dom` and `cod`) correspond exactly to
type dependencies in dependent types.

## Layer 2: Adding Identity via Grothendieck Construction

Layer 2 extends Layer 1 by adding identity structure. On the dependent type
side, we add `idT : {o : objT} → morT o o → Type`, giving a type of identity
witnesses for each endomorphism. On the copresheaf side, we add an object `id`
with `idMor : id → mor` satisfying `idMor ≫ dom = idMor ≫ cod`, picking out
the endomorphisms.

Layer 2 is constructed via the category of elements of `EndoSigmaFunctor`,
the functor `DepData ⥤ Type` mapping each `DepData` to its endomorphism type
`Σ (o : objT), morT o o`. This gives `DepDataLayer2`, whose objects are pairs
`(D : DepData, e : EndoSigma D)` where `e` is an endomorphism of `D`.
-/

namespace GebLean

namespace Layer1

open CategoryTheory

/-! ## The Layer 1 Category (Copresheaf side) -/

/-- Objects in the layer 1 judgment category. -/
inductive Obj : Type where
  | obj : Obj
  | mor : Obj
  deriving DecidableEq, Inhabited, Repr

/-- Non-identity morphisms. -/
inductive SemiHom : Obj → Obj → Type where
  | dom : SemiHom Obj.mor Obj.obj
  | cod : SemiHom Obj.mor Obj.obj
  deriving DecidableEq, Repr

/-- Composition (there are no composable pairs). -/
def SemiHom.comp : ∀ {X Y Z : Obj}, SemiHom X Y → SemiHom Y Z → SemiHom X Z := by
  intro X Y Z f g
  cases f <;> cases g

/-- Associativity holds trivially. -/
theorem SemiHom.assoc : ∀ {W X Y Z : Obj} (f : SemiHom W X) (g : SemiHom X Y)
    (h : SemiHom Y Z), (f.comp g).comp h = f.comp (g.comp h) := by
  intros W X Y Z f g h
  cases f <;> cases g

instance : Quiver Obj where
  Hom := SemiHom

instance instSemicategoryStructObj : Quiver.SemicategoryStruct Obj where
  comp := SemiHom.comp
  assoc := SemiHom.assoc

instance instSemicategoryObj : Semicategory Obj where
  toQuiver := inferInstance
  toSemicategoryStruct := instSemicategoryStructObj

abbrev Hom := Semicategory.AdjoinedIdHom (V := Obj)

instance : CategoryTheory.Category Obj := Semicategory.adjoinedIdCategory

instance (X Y : Obj) : DecidableEq (Hom X Y) :=
  Semicategory.AdjoinedIdHom.decidableEq
    (fun A B => fun (f g : SemiHom A B) => decEq f g) X Y

/-! ## FunctorData for Layer 1 -/

@[ext]
structure FunctorData (C : Type*) [Category C] where
  objC : C
  morC : C
  dom : morC ⟶ objC
  cod : morC ⟶ objC

def objMap {C : Type*} [Category C] (data : FunctorData C) : Obj → C
  | .obj => data.objC
  | .mor => data.morC

def mapSemiHom {C : Type*} [Category C] (data : FunctorData C) :
    ∀ {X Y : Obj}, SemiHom X Y → (objMap data X ⟶ objMap data Y)
  | .mor, .obj, .dom => data.dom
  | .mor, .obj, .cod => data.cod

def mkFunctor {C : Type*} [Category C] (data : FunctorData C) : Obj ⥤ C where
  obj := objMap data
  map {X Y} f := match f with
    | Semicategory.AdjoinedIdHom.id _ => 𝟙 _
    | Semicategory.AdjoinedIdHom.hom g => mapSemiHom data g
  map_id := by intro X; rfl
  map_comp {X Y Z} f g := by
    cases f with
    | id =>
      cases g with
      | id => change 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
      | hom g' => change mapSemiHom data g' = 𝟙 _ ≫ mapSemiHom data g'; simp
    | hom f' =>
      cases g with
      | id => change mapSemiHom data f' = mapSemiHom data f' ≫ 𝟙 _; simp
      | hom g' => cases f' <;> cases g'

abbrev mkCopresheaf := mkFunctor (C := Type)

abbrev CopresheafData := FunctorData Type

/-- Extract FunctorData from a functor. -/
def functorToData {C : Type*} [Category C] (F : Obj ⥤ C) : FunctorData C where
  objC := F.obj .obj
  morC := F.obj .mor
  dom := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.dom)
  cod := F.map (Semicategory.AdjoinedIdHom.hom SemiHom.cod)

/-- Converting FunctorData to a functor and extracting back gives the
    original FunctorData. -/
theorem functorToData_mkFunctor {C : Type*} [Category C] (data : FunctorData C) :
    functorToData (mkFunctor data) = data := by
  cases data
  rfl

/-- Extracting FunctorData from a functor and converting back gives a
    functor equal to the original. -/
theorem mkFunctor_functorToData {C : Type*} [Category C] (F : Obj ⥤ C) :
    mkFunctor (functorToData F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro X
    cases X <;> rfl
  case h_map =>
    intro X Y f
    cases f with
    | id =>
      cases X
      all_goals
        simp [mkFunctor, functorToData, objMap]
        exact (F.map_id _).symm
    | hom g => cases g <;> simp [mkFunctor, functorToData, mapSemiHom]

@[ext]
structure NatTransData {C : Type*} [Category C] (F G : FunctorData C) where
  appObj : F.objC ⟶ G.objC
  appMor : F.morC ⟶ G.morC
  naturality_dom : F.dom ≫ appObj = appMor ≫ G.dom
  naturality_cod : F.cod ≫ appObj = appMor ≫ G.cod

def NatTransData.id {C : Type*} [Category C] (F : FunctorData C) :
    NatTransData F F where
  appObj := 𝟙 F.objC
  appMor := 𝟙 F.morC
  naturality_dom := by simp
  naturality_cod := by simp

def NatTransData.comp {C : Type*} [Category C] {F G H : FunctorData C}
    (α : NatTransData F G) (β : NatTransData G H) :
    NatTransData F H where
  appObj := α.appObj ≫ β.appObj
  appMor := α.appMor ≫ β.appMor
  naturality_dom := by
    rw [← Category.assoc, α.naturality_dom, Category.assoc, β.naturality_dom,
      ← Category.assoc]
  naturality_cod := by
    rw [← Category.assoc, α.naturality_cod, Category.assoc, β.naturality_cod,
      ← Category.assoc]

instance {C : Type*} [Category C] : Category (FunctorData C) where
  Hom := NatTransData
  id := NatTransData.id
  comp := NatTransData.comp
  id_comp := by intros; ext <;> simp [NatTransData.comp, NatTransData.id]
  comp_id := by intros; ext <;> simp [NatTransData.comp, NatTransData.id]
  assoc := by intros; ext <;> simp [NatTransData.comp, Category.assoc]

/-- Extract NatTransData from a natural transformation. -/
def natTransToData {C : Type*} [Category C] {F G : Obj ⥤ C} (α : F ⟶ G) :
    NatTransData (functorToData F) (functorToData G) where
  appObj := α.app .obj
  appMor := α.app .mor
  naturality_dom := α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.dom)
  naturality_cod := α.naturality (Semicategory.AdjoinedIdHom.hom SemiHom.cod)

/-- Construct a natural transformation from NatTransData. -/
def mkNatTrans {C : Type*} [Category C] {F G : FunctorData C}
    (α : NatTransData F G) : mkFunctor F ⟶ mkFunctor G where
  app X := match X with
    | .obj => α.appObj
    | .mor => α.appMor
  naturality X Y f := by
    cases f with
    | id => simp only [mkFunctor, Category.comp_id, Category.id_comp]
    | hom f' =>
      cases f' <;> simp only [mkFunctor]
      case dom => exact α.naturality_dom
      case cod => exact α.naturality_cod

/-- Converting a NatTransData to a natural transformation and extracting
    back gives the original NatTransData. -/
theorem natTransToData_mkNatTrans {C : Type*} [Category C] {F G : FunctorData C}
    (α : NatTransData F G) :
    natTransToData (mkNatTrans α) = α := by
  cases α
  rfl

/-- Extracting NatTransData from a natural transformation and converting
    back gives the original natural transformation (modulo eqToHom cast). -/
theorem mkNatTrans_natTransToData {C : Type*} [Category C] {F G : Obj ⥤ C}
    (α : F ⟶ G) :
    mkNatTrans (natTransToData α) =
    eqToHom (mkFunctor_functorToData F) ≫ α ≫
    eqToHom (mkFunctor_functorToData G).symm := by
  ext X
  cases X <;> simp [mkNatTrans, natTransToData]

/-- The functor from FunctorData to the functor category. -/
def functorDataToFunctor {C : Type*} [Category C] : FunctorData C ⥤ (Obj ⥤ C) where
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

/-- The functor from the functor category to FunctorData. -/
def functorToFunctorData {C : Type*} [Category C] : (Obj ⥤ C) ⥤ FunctorData C where
  obj := functorToData
  map := natTransToData
  map_id := by
    intro F
    rfl
  map_comp := by
    intros F G H α β
    rfl

/-- The composition functorToFunctorData ⋙ functorDataToFunctor equals
    the identity functor. -/
theorem functorToFunctorData_comp_functorDataToFunctor {C : Type*} [Category C] :
    functorToFunctorData ⋙ functorDataToFunctor = 𝟭 (Obj ⥤ C) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro F; exact mkFunctor_functorToData F
  case h_map =>
    intro F G α
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
      Functor.id_map, functorToFunctorData, functorDataToFunctor,
      mkNatTrans_natTransToData]

/-- The composition functorDataToFunctor ⋙ functorToFunctorData equals
    the identity functor. -/
theorem functorDataToFunctor_comp_functorToFunctorData {C : Type*} [Category C] :
    functorDataToFunctor ⋙ functorToFunctorData = 𝟭 (FunctorData C) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro F; exact functorToData_mkFunctor F
  case h_map =>
    intro F G α
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
      Functor.id_map, functorToFunctorData, functorDataToFunctor,
      natTransToData_mkNatTrans]
    simp

/-- The categorical isomorphism between FunctorData C and Obj ⥤ C. -/
def functorDataIsoCat {C : Type*} [Category C] : FunctorData C ≅Cat (Obj ⥤ C) where
  hom := functorDataToFunctor
  inv := functorToFunctorData
  hom_inv_id := functorDataToFunctor_comp_functorToFunctorData
  inv_hom_id := functorToFunctorData_comp_functorDataToFunctor

/-- The categorical equivalence between FunctorData C and Obj ⥤ C. -/
def functorDataEquivCat {C : Type*} [Category C] : FunctorData C ≌ (Obj ⥤ C) :=
  Cat.equivOfIso functorDataIsoCat

/-! ## Dependent Type Representation -/

@[ext]
structure DepData where
  objT : Type
  morT : objT → objT → Type

structure DepNatTrans (F G : DepData) where
  appObj : F.objT → G.objT
  appMor : {a b : F.objT} → F.morT a b → G.morT (appObj a) (appObj b)

@[ext (iff := false)]
theorem DepNatTrans.ext' {F G : DepData} {α β : DepNatTrans F G}
    (h_obj : α.appObj = β.appObj)
    (h_mor : ∀ a b (m : F.morT a b), h_obj ▸ h_obj ▸ α.appMor m = β.appMor m) :
    α = β := by
  cases α with | mk appObj₁ appMor₁ =>
  cases β with | mk appObj₂ appMor₂ =>
  simp at h_obj
  subst h_obj
  congr
  funext a b m
  exact h_mor a b m

def DepNatTrans.id (F : DepData) : DepNatTrans F F where
  appObj := _root_.id
  appMor := _root_.id

def DepNatTrans.comp {F G H : DepData}
    (α : DepNatTrans F G) (β : DepNatTrans G H) :
    DepNatTrans F H where
  appObj := β.appObj ∘ α.appObj
  appMor := fun m => β.appMor (α.appMor m)

instance : Category DepData where
  Hom := DepNatTrans
  id := DepNatTrans.id
  comp := DepNatTrans.comp
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-! ## The Equivalence -/

def depToCopresheafData (data : DepData) : CopresheafData where
  objC := data.objT
  morC := Σ (a b : data.objT), data.morT a b
  dom := fun m => m.1
  cod := fun m => m.2.1

def copresheafDataToDep (data : CopresheafData) : DepData where
  objT := data.objC
  morT := fun a b => {m : data.morC // data.dom m = a ∧ data.cod m = b}

def depNatTransToNatTransData {F G : DepData} (α : DepNatTrans F G) :
    NatTransData (depToCopresheafData F) (depToCopresheafData G) where
  appObj := α.appObj
  appMor := fun ⟨a, b, m⟩ => ⟨α.appObj a, α.appObj b, α.appMor m⟩
  naturality_dom := by funext ⟨a, b, m⟩; rfl
  naturality_cod := by funext ⟨a, b, m⟩; rfl

def natTransDataToDepNatTrans {F G : CopresheafData} (α : NatTransData F G) :
    DepNatTrans (copresheafDataToDep F) (copresheafDataToDep G) where
  appObj := α.appObj
  appMor := fun m =>
    let hdom := congr_fun α.naturality_dom m.val
    let hcod := congr_fun α.naturality_cod m.val
    ⟨α.appMor m.val,
     hdom.symm.trans (congr_arg α.appObj m.property.1),
     hcod.symm.trans (congr_arg α.appObj m.property.2)⟩

def depToCopr : DepData ⥤ CopresheafData where
  obj := depToCopresheafData
  map := depNatTransToNatTransData
  map_id := by intro F; rfl
  map_comp := by intros; rfl

def coprToDep : CopresheafData ⥤ DepData where
  obj := copresheafDataToDep
  map := natTransDataToDepNatTrans
  map_id := by intro F; rfl
  map_comp := by intros; rfl

/-- Natural isomorphism from the identity on DepData to depToCopr ⋙ coprToDep. -/
def unitIso : 𝟭 DepData ≅ depToCopr ⋙ coprToDep :=
  NatIso.ofComponents
    (fun F => {
      hom := {
        appObj := _root_.id
        appMor := fun {a b} m => ⟨⟨a, b, m⟩, rfl, rfl⟩
      }
      inv := {
        appObj := _root_.id
        appMor := fun {a b} m =>
          match m with
          | ⟨⟨a', b', m'⟩, ha, hb⟩ => ha ▸ hb ▸ m'
      }
      hom_inv_id := rfl
      inv_hom_id := by
        cases F with | mk objT morT =>
        apply DepNatTrans.ext'
        case h_obj => rfl
        case h_mor =>
          intro a b m
          simp only []
          cases m with | mk val prop =>
          cases val with | mk a' val' =>
          cases val' with | mk b' m' =>
          cases prop with | intro ha hb =>
          cases ha
          cases hb
          rfl
    })
    (by
      intro F G α
      apply DepNatTrans.ext'
      case h_obj => rfl
      case h_mor => intro a b m; rfl)

/-- Natural isomorphism from coprToDep ⋙ depToCopr to the identity on CopresheafData. -/
def counitIso : coprToDep ⋙ depToCopr ≅ 𝟭 CopresheafData :=
  NatIso.ofComponents
    (fun F => {
      hom := {
        appObj := _root_.id
        appMor := fun ⟨a, b, m⟩ => m.val
        naturality_dom := by
          funext ⟨a, b, m⟩
          cases m with | mk val prop =>
          simp [depToCopr, coprToDep, depToCopresheafData, copresheafDataToDep]
          exact prop.1.symm
        naturality_cod := by
          funext ⟨a, b, m⟩
          cases m with | mk val prop =>
          simp [depToCopr, coprToDep, depToCopresheafData, copresheafDataToDep]
          exact prop.2.symm
      }
      inv := {
        appObj := _root_.id
        appMor := fun m => ⟨F.dom m, F.cod m, ⟨m, rfl, rfl⟩⟩
        naturality_dom := rfl
        naturality_cod := rfl
      }
      hom_inv_id := by
        cases F with | mk objC morC dom cod =>
        apply NatTransData.ext
        · rfl
        · funext ⟨a, b, m⟩
          cases m with | mk val prop =>
          cases prop with | intro ha hb =>
          -- Need to show: ⟨dom val, cod val, ⟨val, rfl, rfl⟩⟩ = ⟨a, b, ⟨val, ha, hb⟩⟩
          -- Since ha : dom val = a and hb : cod val = b
          cases ha
          cases hb
          rfl
      inv_hom_id := by
        cases F with | mk objC morC dom cod =>
        apply NatTransData.ext
        · rfl
        · funext m
          rfl
    })
    (by
      intro F G α
      cases F; cases G; cases α
      apply NatTransData.ext
      · rfl
      · funext ⟨a, b, m⟩
        rfl)

/-- The categorical equivalence between dependent types and copresheaves
    for Layer 1 (objects and morphisms only). -/
def layer1Equivalence : DepData ≌ CopresheafData where
  functor := depToCopr
  inverse := coprToDep
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := by
    intro F
    apply NatTransData.ext
    · rfl
    · funext m
      rfl

end Layer1

namespace Layer2

open CategoryTheory
open Layer1

/-! ## Dependent Type Structures -/

/-- The type of identity structures on a Layer 1 dependent type.
    For each object `o` and endomorphism `m : morT o o`, we have a type
    of identity witnesses.

    This is the curried form of a slice object over `Σ (o : D.objT), D.morT o o`. -/
def DepDataId (D : DepData) : Type 1 :=
  {o : D.objT} → D.morT o o → Type

/-- The type of endomorphisms for a given DepData structure. -/
def EndoSigma (D : DepData) : Type :=
  Σ (o : D.objT), D.morT o o

/-- Layer 2 dependent data: Layer 1 plus identity types indexed by endomorphisms. -/
structure DepData2 where
  layer1 : DepData
  idT : DepDataId layer1

/-! ## The Endomorphism Functor -/

/-- `EndoSigma` on morphisms: given a natural transformation between DepData
    structures, we get a function between their endomorphism sigma types. -/
def EndoSigma.map {D E : DepData} (α : DepNatTrans D E) :
    EndoSigma D → EndoSigma E :=
  fun ⟨o, m⟩ => ⟨α.appObj o, α.appMor m⟩

/-- The endomorphism functor from DepData to Type.
    Maps each DepData structure to its type of endomorphisms. -/
def EndoSigmaFunctor : DepData ⥤ Type where
  obj := EndoSigma
  map := EndoSigma.map
  map_id := by
    intro D
    funext ⟨o, m⟩
    rfl
  map_comp := by
    intro D E F α β
    funext ⟨o, m⟩
    rfl

/-! ## Slice Categories -/

/-- Objects in the slice category Type / S represented as dependent functions.
    An object is a family of types indexed by S. -/
def TypeSlice (S : Type) : Type 1 := S → Type

/-- Morphisms in TypeSlice S are natural transformations between type families. -/
def TypeSliceMor {S : Type} (F G : TypeSlice S) : Type :=
  (s : S) → F s → G s

/-- Identity morphism in TypeSlice. -/
def TypeSliceMor.id {S : Type} (F : TypeSlice S) : TypeSliceMor F F :=
  fun _s x => x

/-- Composition in TypeSlice. -/
def TypeSliceMor.comp {S : Type} {F G H : TypeSlice S}
    (α : TypeSliceMor F G) (β : TypeSliceMor G H) : TypeSliceMor F H :=
  fun s x => β s (α s x)

/-- TypeSlice S as a category. -/
instance (S : Type) : Category (TypeSlice S) where
  Hom := TypeSliceMor
  id := TypeSliceMor.id
  comp := TypeSliceMor.comp
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-! ## Functor to Categories via Opposite -/

/-- The endomorphism functor in the opposite category. -/
def EndoSigmaFunctorOp : DepDataᵒᵖ ⥤ Typeᵒᵖ :=
  EndoSigmaFunctor.op

open CategoryTheory.Comma

/-- The contravariant slice functor Typeᵒᵖ ⥤ Cat.
    Uses mathlib's `Under.mapFunctor` to map each type to its coslice category. -/
def sliceFunctor : Typeᵒᵖ ⥤ Cat.{0, 1} :=
  Under.mapFunctor Type

/-- The functor from DepDataᵒᵖ to Cat.
    Composition of the endomorphism functor with the slice functor. -/
def depDataOpToCat : DepDataᵒᵖ ⥤ Cat.{0, 1} :=
  EndoSigmaFunctorOp ⋙ sliceFunctor

/-! ## Category of Elements Construction -/

/-- The category of elements of the endomorphism functor.

    Objects are pairs `(D : DepData, e : EndoSigma D)` where:
    - `D` is a Layer 1 structure (objects and morphisms)
    - `e : Σ (o : D.objT), D.morT o o` is an endomorphism of `D`

    Morphisms `(D₁, e₁) → (D₂, e₂)` are Layer 1 morphisms `α : D₁ ⟶ D₂`
    satisfying `EndoSigma.map α e₁ = e₂`. -/
abbrev DepDataLayer2 : Type 1 :=
  EndoSigmaFunctor.Elements

example : Category DepDataLayer2 := inferInstance

/-- Alternative formulation via the general Grothendieck construction.

    Uses the functor `depDataOpToCat : DepDataᵒᵖ ⥤ Cat` which goes through
    opposite categories and coslice categories. Equivalent to `DepDataLayer2`. -/
abbrev DepDataGrothendieck : Type 1 :=
  Grothendieck depDataOpToCat

example : Category DepDataGrothendieck := inferInstance

/-- Construct an element of DepDataLayer2 from DepData and an endomorphism. -/
def layer2OfDepDataEndo (D : DepData) (o : D.objT) (m : D.morT o o) :
    DepDataLayer2 :=
  ⟨D, ⟨o, m⟩⟩

end Layer2

end GebLean
