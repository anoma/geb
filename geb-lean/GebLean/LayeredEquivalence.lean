import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Equivalence
import GebLean.Utilities
import GebLean.Semicategory

/-!
# Layered Equivalence between Copresheaves and Dependent Types

This file demonstrates the categorical equivalence for Layer 1
(objects and morphisms only), as a stepping stone to understanding the
full equivalence in `DepCategoryJudgments.lean`.

## Layer 1: Objects and Morphisms

We define a 2-object category (simpler version of CategoryJudgments):
- Object `obj` (representing types of objects)
- Object `mor` (representing types of morphisms)
- Morphisms `dom, cod : mor → obj` (domain and codomain)

We then show this is categorically equivalent to dependent types:
```lean
structure DepData where
  objT : Type
  morT : objT → objT → Type
```

This demonstrates the key insight: copresheaf structure maps (like `dom` and
`cod`) correspond exactly to type dependencies in dependent types.
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

end GebLean
