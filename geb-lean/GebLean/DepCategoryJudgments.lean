import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import GebLean.CategoryJudgments
import GebLean.Utilities.Sigma

/-!
# Dependent Category Judgments

This file defines dependent type representations of category structures
and their correspondence with the functor-based representations in
CategoryJudgments.

## Main definitions

* `DepCategoryData`: Category structure using dependent types
* `DepNatTransData`: Natural transformations between DepCategoryData
* `depToFunctorData`: Convert DepCategoryData to CopresheafData
* `functorDataToDep`: Convert CopresheafData to DepCategoryData
* Equivalences and round-trip theorems
-/

namespace GebLean

namespace CategoryJudgments

open CategoryTheory

section DepCategoryDataCategory

/-- Data for a category structure using dependent types. -/
@[ext]
structure DepCategoryData.{u₁, u₂, u₃, u₄} : Type (max u₁ u₂ u₃ u₄) where
  objT : Sort u₁
  morT : objT → objT → Sort u₂
  idT : {o : objT} → morT o o → Sort u₃
  compT : {a b c : objT} → morT a b → morT b c → morT a c → Sort u₄

/-- Natural transformation data between two DepCategoryData structures.
    Components are dependent functions respecting the type structure. -/
@[ext]
structure DepNatTransData.{u₁, u₂, u₃, u₄, v₁, v₂, v₃, v₄}
    (F : DepCategoryData.{u₁, u₂, u₃, u₄})
    (G : DepCategoryData.{v₁, v₂, v₃, v₄}) :
    Type (max u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄) where
  appObj : F.objT → G.objT
  appMor : {a b : F.objT} → F.morT a b → G.morT (appObj a) (appObj b)
  appId : {o : F.objT} → {m : F.morT o o} → F.idT m →
    G.idT (appMor m)
  appComp : {a b c : F.objT} → {f : F.morT a b} → {g : F.morT b c} →
    {h : F.morT a c} → F.compT f g h →
    G.compT (appMor f) (appMor g) (appMor h)

/-- Identity natural transformation for DepCategoryData. -/
def DepNatTransData.id (F : DepCategoryData) : DepNatTransData F F where
  appObj := _root_.id
  appMor := _root_.id
  appId := _root_.id
  appComp := _root_.id

/-- Composition of natural transformations for DepCategoryData. -/
def DepNatTransData.comp {F G H : DepCategoryData}
    (α : DepNatTransData F G) (β : DepNatTransData G H) :
    DepNatTransData F H where
  appObj := β.appObj ∘ α.appObj
  appMor := fun m => β.appMor (α.appMor m)
  appId := fun i => β.appId (α.appId i)
  appComp := fun comp => β.appComp (α.appComp comp)

/-- Category instance for DepCategoryData with DepNatTransData as
    morphisms. -/
instance : Category DepCategoryData where
  Hom := DepNatTransData
  id := DepNatTransData.id
  comp := DepNatTransData.comp
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

end DepCategoryDataCategory

section DepCategoryDataCorrespondences

/-- Convert dependent category data to CopresheafData.
    The dependent types enforce the equality conditions automatically. -/
def depToFunctorData.{u} (data : DepCategoryData.{u + 1}) :
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
    DepCategoryData.{u + 1} where
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
    relations. Morphisms encode their domains and codomains in their types,
    so the compatibility conditions are enforced by the type structure. -/
def mkCopresheafDep.{u} (data : DepCategoryData.{u + 1}) : Obj ⥤ Type u :=
  mkCopresheaf (depToFunctorData data)

/-- Extract DepCategoryData from a copresheaf. -/
abbrev functorToDataDep.{u} (F : Obj ⥤ Type u) : DepCategoryData.{u + 1} :=
  functorDataToDep (functorToData F)

/-- Convert a DepNatTransData to a NatTransData by packaging the dependent
    components into sigma types. -/
def depNatTransToNatTrans {F G : DepCategoryData}
    (α : DepNatTransData F G) :
    NatTransData (depToFunctorData F) (depToFunctorData G) where
  appObj := α.appObj
  appMor := fun ⟨a, b, m⟩ => ⟨α.appObj a, α.appObj b, α.appMor m⟩
  appId := fun ⟨o, m, i⟩ => ⟨α.appObj o, α.appMor m, α.appId i⟩
  appComp := fun ⟨a, b, c, f, g, h, comp⟩ =>
    ⟨α.appObj a, α.appObj b, α.appObj c, α.appMor f, α.appMor g,
      α.appMor h, α.appComp comp⟩
  naturality_dom := by funext ⟨a, b, m⟩; rfl
  naturality_cod := by funext ⟨a, b, m⟩; rfl
  naturality_idMor := by funext ⟨o, m, i⟩; rfl
  naturality_left := by funext ⟨a, b, c, f, g, h, comp⟩; rfl
  naturality_right := by funext ⟨a, b, c, f, g, h, comp⟩; rfl
  naturality_composite := by funext ⟨a, b, c, f, g, h, comp⟩; rfl

/-- Convert a NatTransData to a DepNatTransData by extracting from sigma
    types. -/
def natTransToDepNatTrans {F G : CopresheafData}
    (α : NatTransData F G) :
    DepNatTransData (functorDataToDep F) (functorDataToDep G) where
  appObj := α.appObj
  appMor := fun m =>
    let hdom := congr_fun α.naturality_dom m.val
    let hcod := congr_fun α.naturality_cod m.val
    ⟨α.appMor m.val,
     hdom.symm.trans (congr_arg α.appObj m.property.1),
     hcod.symm.trans (congr_arg α.appObj m.property.2)⟩
  appId := fun i =>
    let hidMor := congr_fun α.naturality_idMor i.val
    ⟨α.appId i.val,
     hidMor.symm.trans (congr_arg α.appMor i.property)⟩
  appComp := fun comp =>
    let hr := congr_fun α.naturality_right comp.val
    let hl := congr_fun α.naturality_left comp.val
    let hc := congr_fun α.naturality_composite comp.val
    ⟨α.appComp comp.val,
     hr.symm.trans (congr_arg α.appMor comp.property.1),
     hl.symm.trans (congr_arg α.appMor comp.property.2.1),
      hc.symm.trans (congr_arg α.appMor comp.property.2.2)⟩

/-- Functor from DepCategoryData to CopresheafData using depToFunctorData. -/
def depCatToCopresheaf : DepCategoryData ⥤ CopresheafData where
  obj := depToFunctorData
  map := depNatTransToNatTrans
  map_id := by intro F; rfl
  map_comp := by intros; rfl

/-- Functor from CopresheafData to DepCategoryData using
    functorDataToDep. -/
def copresheafToDepCat : CopresheafData ⥤ DepCategoryData where
  obj := functorDataToDep
  map := natTransToDepNatTrans
  map_id := by intro F; rfl
  map_comp := by intros; rfl

/-- Two DepCategoryData structures are equivalent if their corresponding
    FunctorData structures (via depToFunctorData) are equivalent. -/
def DepCategoryData.Equiv (data₁ data₂ : DepCategoryData) : Prop :=
  FunctorData.Equiv (depToFunctorData data₁) (depToFunctorData data₂)

/-- The equivalence relation on FunctorData induces an equivalence relation
    on DepCategoryData via depToFunctorData. -/
instance : Setoid DepCategoryData where
  r := DepCategoryData.Equiv
  iseqv := {
    refl := fun _ => ⟨Iso.refl _⟩
    symm := fun ⟨iso⟩ => ⟨iso.symm⟩
    trans := fun ⟨iso₁⟩ ⟨iso₂⟩ => ⟨iso₁.trans iso₂⟩
  }

/-- The composition functorToDataDep ∘ mkCopresheafDep simplifies to
    functorDataToDep ∘ depToFunctorData, since functorToData and mkCopresheaf
    are inverses (they compose to the identity). -/
theorem functorToDataDep_mkCopresheafDep.{u} (data : DepCategoryData.{u + 1}) :
    functorToDataDep (mkCopresheafDep data) =
    functorDataToDep (depToFunctorData data) := by
  simp only [functorToDataDep, mkCopresheafDep, mkCopresheaf,
    functorToData_mkFunctor]

/-- Round-tripping from DepCategoryData to CopresheafData and back
    preserves the object type. -/
theorem functorDataToDep_depToFunctorData_objT.{u}
    (data : DepCategoryData.{u + 1}) :
    (functorDataToDep (depToFunctorData data)).objT = data.objT := rfl

/-- Round-tripping from CopresheafData to DepCategoryData and back
    preserves the object type. -/
theorem depToFunctorData_functorDataToDep_objC.{u} (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).objC = data.objC := rfl

/-- Round-tripping from DepCategoryData to CopresheafData and back
    gives an equivalent morphism type. -/
def functorDataToDep_depToFunctorData_morT.{u} (data : DepCategoryData.{u + 1})
    (a b : data.objT) :
    (functorDataToDep (depToFunctorData data)).morT a b ≃
    data.morT a b where
  toFun m := cast
    (congrArg₂ data.morT m.prop.1 m.prop.2) m.val.2.2
  invFun m := ⟨⟨a, b, m⟩, rfl, rfl⟩
  left_inv m := by
    rcases m with ⟨⟨a', b', m⟩, ha : a' = a, hb : b' = b⟩
    subst ha hb
    rfl
  right_inv m := rfl

/-- Round-tripping from CopresheafData to DepCategoryData and back
    gives an equivalent morphism type. -/
def depToFunctorData_functorDataToDep_morC.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).morC ≃
    data.morC where
  toFun m := m.2.2.val
  invFun m := ⟨data.dom m, data.cod m, ⟨m, rfl, rfl⟩⟩
  left_inv m := by
    rcases m with ⟨a, b, ⟨m, ha, hb⟩⟩
    subst ha hb
    rfl
  right_inv m := rfl

def depToFunctorData_functorDataToDep_morCIso.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).morC ≅ data.morC where
  hom := (depToFunctorData_functorDataToDep_morC data).toFun
  inv := (depToFunctorData_functorDataToDep_morC data).invFun
  hom_inv_id := by
    funext m
    exact (depToFunctorData_functorDataToDep_morC data).left_inv m
  inv_hom_id := by
    funext m
    exact (depToFunctorData_functorDataToDep_morC data).right_inv m

/-- Extract the underlying morphism from a round-tripped morphism type.
    When we go DepCategoryData → CopresheafData → DepCategoryData,
    morphisms get wrapped in sigma types and subtypes.
    This extracts the original using the round-trip equivalence. -/
abbrev extractRoundTrippedMor.{u} (data : DepCategoryData.{u + 1})
    (a b : data.objT) :=
  (functorDataToDep_depToFunctorData_morT data a b).toFun

def functorDataToDep_depToFunctorData_morTIso.{u}
    (data : DepCategoryData.{u + 1}) (a b : data.objT) :
    (functorDataToDep (depToFunctorData data)).morT a b ≅
    data.morT a b where
  hom := (functorDataToDep_depToFunctorData_morT data a b).toFun
  inv := (functorDataToDep_depToFunctorData_morT data a b).invFun
  hom_inv_id := by
    funext m
    exact (functorDataToDep_depToFunctorData_morT data a b).left_inv m
  inv_hom_id := by
    funext m
    exact (functorDataToDep_depToFunctorData_morT data a b).right_inv m

/-- Round-tripping from CopresheafData to DepCategoryData and back
    gives an equivalent identity type. -/
def depToFunctorData_functorDataToDep_idC.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).idC ≃
    data.idC where
  toFun i := i.2.2.val
  invFun i :=
    let h_endo := congrFun data.h_id_endo i
    ⟨data.dom (data.idMor i), ⟨data.idMor i, rfl, h_endo.symm⟩, ⟨i, rfl⟩⟩
  left_inv i := by
    rcases i with ⟨o, ⟨m, hdom, hcod⟩, ⟨i, hi⟩⟩
    cases hi
    cases hdom
    rfl
  right_inv i := rfl

def depToFunctorData_functorDataToDep_idCIso.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).idC ≅ data.idC where
  hom := (depToFunctorData_functorDataToDep_idC data).toFun
  inv := (depToFunctorData_functorDataToDep_idC data).invFun
  hom_inv_id := by
    funext i
    exact (depToFunctorData_functorDataToDep_idC data).left_inv i
  inv_hom_id := by
    funext i
    exact (depToFunctorData_functorDataToDep_idC data).right_inv i

/-- Helper lemma: Extract the morphism equality from the identity constraint.
  This proves that the witness morphism equals `extractRoundTrippedMor`. -/
private lemma idT_mor_eq.{u} (data : DepCategoryData.{u + 1}) (o : data.objT)
    (m : (functorDataToDep (depToFunctorData data)).morT o o)
    (wit : (functorDataToDep (depToFunctorData data)).idT m) :
    data.idT wit.1.2.1 = data.idT (extractRoundTrippedMor data o o m) := by
  rcases wit with ⟨⟨o', m', w⟩,
    h : (depToFunctorData data).idMor ⟨o', m', w⟩ = m.val⟩
  rcases m with ⟨⟨a, b, m_val⟩, ha : a = o, hb : b = o⟩
  cases h
  cases ha
  cases hb
  simp [extractRoundTrippedMor, functorDataToDep_depToFunctorData_morT,
    depToFunctorData]

/-- Helper lemma: Prove the idMor constraint for the inverse function. -/
private lemma idT_invFun_constraint.{u} (data : DepCategoryData.{u + 1})
    (o : data.objT)
    (m : (functorDataToDep (depToFunctorData data)).morT o o)
    (wit : data.idT (extractRoundTrippedMor data o o m)) :
    (depToFunctorData data).idMor
      ⟨o, ⟨extractRoundTrippedMor data o o m, wit⟩⟩ = m.val := by
  rcases m with ⟨⟨a, b, mor⟩, ha, hb⟩
  cases ha
  cases hb
  simp [depToFunctorData, functorDataToDep_depToFunctorData_morT]

/-- Round-tripping from DepCategoryData to CopresheafData and back
    gives an equivalent identity type. -/
def functorDataToDep_depToFunctorData_idT.{u}
    (data : DepCategoryData.{u + 1}) (o : data.objT)
    (m : (functorDataToDep (depToFunctorData data)).morT o o) :
    (functorDataToDep (depToFunctorData data)).idT m ≃
    data.idT (extractRoundTrippedMor data o o m) where
  toFun wit :=
    cast (idT_mor_eq data o m wit) wit.1.2.2
  invFun wit :=
    ⟨⟨o, ⟨extractRoundTrippedMor data o o m, wit⟩⟩,
     idT_invFun_constraint data o m wit⟩
  left_inv wit := by
    rcases wit with ⟨⟨o', m', w⟩, h⟩
    rcases m with ⟨⟨a, b, m_val⟩, ha : a = o, hb : b = o⟩
    change (⟨o', ⟨o', m'⟩⟩ : Σ (a b : data.objT), data.morT a b) =
      ⟨a, ⟨b, m_val⟩⟩ at h
    rw [Sigma.mk.injEq] at h
    have ⟨ho', hsig⟩ := h
    subst ha hb ho'
    have hsig_eq := eq_of_heq hsig
    rw [Sigma.mk.injEq] at hsig_eq
    have ⟨_, hm⟩ := hsig_eq
    subst hm
    simp only [cast_eq, depToFunctorData, extractRoundTrippedMor]
    congr 1
  right_inv wit := by
    rcases m with ⟨⟨a, b, mor⟩, ha, hb⟩
    simp only [depToFunctorData] at ha hb
    subst ha hb
    simp only [cast_eq]

def functorDataToDep_depToFunctorData_idIso.{u}
    (data : DepCategoryData.{u + 1}) (o : data.objT)
    (m : (functorDataToDep (depToFunctorData data)).morT o o) :
    (functorDataToDep (depToFunctorData data)).idT m ≅
    data.idT (extractRoundTrippedMor data o o m) where
  hom := (functorDataToDep_depToFunctorData_idT data o m).toFun
  inv := (functorDataToDep_depToFunctorData_idT data o m).invFun
  hom_inv_id := by
    funext i
    exact (functorDataToDep_depToFunctorData_idT data o m).left_inv i
  inv_hom_id := by
    funext i
    exact (functorDataToDep_depToFunctorData_idT data o m).right_inv i

/-- Helper lemma: Extract the composition equality from the witness.
    Proves that the right projection of the reconstructed witness matches
    the original morphism. -/
private lemma compT_invFun_right.{u} (data : DepCategoryData.{u + 1})
    (a b c : data.objT)
    (f : (functorDataToDep (depToFunctorData data)).morT a b)
    (g : (functorDataToDep (depToFunctorData data)).morT b c)
    (h : (functorDataToDep (depToFunctorData data)).morT a c)
    (wit : data.compT (extractRoundTrippedMor data a b f)
      (extractRoundTrippedMor data b c g)
      (extractRoundTrippedMor data a c h)) :
    (depToFunctorData data).right
      ⟨a, b, c, extractRoundTrippedMor data a b f,
       extractRoundTrippedMor data b c g,
       extractRoundTrippedMor data a c h, wit⟩ = f.val := by
    rcases f with ⟨⟨a', b', f'⟩, hfa, hfb⟩
    cases hfa
    cases hfb
    simp [depToFunctorData, functorDataToDep_depToFunctorData_morT, cast_eq]

/-- Helper lemma: Extract the composition equality from the witness.
    Proves that the left projection of the reconstructed witness matches
    the original morphism. -/
private lemma compT_invFun_left.{u} (data : DepCategoryData.{u + 1})
    (a b c : data.objT)
    (f : (functorDataToDep (depToFunctorData data)).morT a b)
    (g : (functorDataToDep (depToFunctorData data)).morT b c)
    (h : (functorDataToDep (depToFunctorData data)).morT a c)
    (wit : data.compT (extractRoundTrippedMor data a b f)
      (extractRoundTrippedMor data b c g)
      (extractRoundTrippedMor data a c h)) :
    (depToFunctorData data).left
      ⟨a, b, c, extractRoundTrippedMor data a b f,
       extractRoundTrippedMor data b c g,
       extractRoundTrippedMor data a c h, wit⟩ = g.val := by
    rcases g with ⟨⟨a', b', g'⟩, hga, hgb⟩
    cases hga
    cases hgb
    simp [depToFunctorData, functorDataToDep_depToFunctorData_morT, cast_eq]

/-- Helper lemma: Extract the composition equality from the witness. -/
private lemma compT_invFun_composite.{u} (data : DepCategoryData.{u + 1})
    (a b c : data.objT)
    (f : (functorDataToDep (depToFunctorData data)).morT a b)
    (g : (functorDataToDep (depToFunctorData data)).morT b c)
    (h : (functorDataToDep (depToFunctorData data)).morT a c)
    (wit : data.compT (extractRoundTrippedMor data a b f)
      (extractRoundTrippedMor data b c g)
      (extractRoundTrippedMor data a c h)) :
    (depToFunctorData data).composite
      ⟨a, b, c, extractRoundTrippedMor data a b f,
       extractRoundTrippedMor data b c g,
       extractRoundTrippedMor data a c h, wit⟩ = h.val := by
    rcases h with ⟨⟨a', b', h'⟩, hha, hhb⟩
    cases hha
    cases hhb
    simp [depToFunctorData, functorDataToDep_depToFunctorData_morT, cast_eq]

/-- Convenience lemma packaging the sigma equality arising from
    `extractRoundTrippedMor`. -/
private lemma extractRoundTrippedMor_sigma_eq.{u}
    (data : DepCategoryData.{u + 1}) {a b a' b' : data.objT}
    {m : data.morT a' b'} (ha : a' = a) (hb : b' = b) :
    (⟨a, ⟨b, extractRoundTrippedMor data a b ⟨⟨a', b', m⟩, ha, hb⟩⟩⟩ :
        Σ (x y : data.objT), data.morT x y) = ⟨a', ⟨b', m⟩⟩ := by
  subst ha hb
  simp [extractRoundTrippedMor, functorDataToDep_depToFunctorData_morT]

private lemma compT_mor_eq.{u} (data : DepCategoryData.{u + 1}) (a b c : data.objT)
    (f : (functorDataToDep (depToFunctorData data)).morT a b)
    (g : (functorDataToDep (depToFunctorData data)).morT b c)
    (h : (functorDataToDep (depToFunctorData data)).morT a c)
    (wit : (functorDataToDep (depToFunctorData data)).compT f g h) :
    data.compT wit.val.2.2.2.1 wit.val.2.2.2.2.1 wit.val.2.2.2.2.2.1 =
    data.compT (extractRoundTrippedMor data a b f)
      (extractRoundTrippedMor data b c g)
      (extractRoundTrippedMor data a c h) := by
  rcases wit with ⟨⟨a_c, b_c, c_c, f_c, g_c, h_c, comp_wit⟩, hr, hl, hcomp⟩
  rcases f with ⟨⟨a_f, b_f, f'⟩, hfa : a_f = a, hfb : b_f = b⟩
  rcases g with ⟨⟨a_g, b_g, g'⟩, hga : a_g = b, hgb : b_g = c⟩
  rcases h with ⟨⟨a_h, b_h, h'⟩, hha : a_h = a, hhb : b_h = c⟩
  simp only [depToFunctorData] at hr hl hcomp
  have hr_extract :=
    extractRoundTrippedMor_sigma_eq (data := data) (a := a) (b := b)
      (a' := a_f) (b' := b_f) (m := f') hfa hfb
  have hl_extract :=
    extractRoundTrippedMor_sigma_eq (data := data) (a := b) (b := c)
      (a' := a_g) (b' := b_g) (m := g') hga hgb
  have hcomp_extract :=
    extractRoundTrippedMor_sigma_eq (data := data) (a := a) (b := c)
      (a' := a_h) (b' := b_h) (m := h') hha hhb
  change (⟨a_c, ⟨b_c, f_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
    ⟨a_f, ⟨b_f, f'⟩⟩ at hr
  change (⟨b_c, ⟨c_c, g_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
    ⟨a_g, ⟨b_g, g'⟩⟩ at hl
  change (⟨a_c, ⟨c_c, h_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
    ⟨a_h, ⟨b_h, h'⟩⟩ at hcomp
  have hr' := hr.trans hr_extract.symm
  have hl' := hl.trans hl_extract.symm
  have hcomp' := hcomp.trans hcomp_extract.symm
  cases hr'
  cases hl'
  cases hcomp'
  simp [extractRoundTrippedMor, functorDataToDep_depToFunctorData_morT]

/-- Proves that the reconstructed composition witness matches the original
    sigma tuple after applying `extractRoundTrippedMor` to its components. -/
private lemma compTSigma_eq.{u} (data : DepCategoryData.{u + 1})
    {a b c a_c b_c c_c : data.objT}
    {f_c : data.morT a_c b_c} {g_c : data.morT b_c c_c}
    {h_c : data.morT a_c c_c}
    {a_f a_g a_h b_f b_g b_h : data.objT}
    {f' : data.morT a_f b_f} {g' : data.morT a_g b_g}
    {h' : data.morT a_h b_h}
    (hfa : a_f = a) (hfb : b_f = b) (hga : a_g = b)
    (hgb : b_g = c) (hha : a_h = a) (hhb : b_h = c)
    (hr : (⟨a_c, ⟨b_c, f_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
      ⟨a_f, ⟨b_f, f'⟩⟩)
    (hl : (⟨b_c, ⟨c_c, g_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
      ⟨a_g, ⟨b_g, g'⟩⟩)
    (hcomp : (⟨a_c, ⟨c_c, h_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
      ⟨a_h, ⟨b_h, h'⟩⟩)
    (comp_wit : data.compT f_c g_c h_c) :
    ((⟨a,
        ⟨b,
          ⟨c,
            ⟨extractRoundTrippedMor data a b ⟨⟨a_f, b_f, f'⟩, hfa, hfb⟩,
              ⟨extractRoundTrippedMor data b c ⟨⟨a_g, b_g, g'⟩, hga, hgb⟩,
                ⟨extractRoundTrippedMor data a c ⟨⟨a_h, b_h, h'⟩, hha, hhb⟩,
                  cast (compT_mor_eq data a b c
                    ⟨⟨a_f, b_f, f'⟩, hfa, hfb⟩
                    ⟨⟨a_g, b_g, g'⟩, hga, hgb⟩
                    ⟨⟨a_h, b_h, h'⟩, hha, hhb⟩
                    ⟨⟨a_c, b_c, c_c, f_c, g_c, h_c, comp_wit⟩, hr, hl, hcomp⟩)
                    comp_wit⟩⟩⟩⟩⟩⟩) :
        Σ (x : data.objT), Σ (y : data.objT), Σ (z : data.objT),
          Σ (f : data.morT x y), Σ (g : data.morT y z),
            Σ (h : data.morT x z), data.compT f g h)
    = ⟨a_c, ⟨b_c, ⟨c_c, ⟨f_c, ⟨g_c, ⟨h_c, comp_wit⟩⟩⟩⟩⟩⟩ := by
  subst hfa hfb hga hgb hha hhb
  simp only [extractRoundTrippedMor]
  cases hr; cases hl; cases hcomp
  simp [functorDataToDep_depToFunctorData_morT, cast_eq]

@[simp] lemma extractRoundTrippedMor_invFun.{u}
  (data : DepCategoryData.{u + 1}) {a b : data.objT}
  (f : data.morT a b) :
  extractRoundTrippedMor data a b
    ((functorDataToDep_depToFunctorData_morT data a b).invFun f) = f := by
  simp [extractRoundTrippedMor]

/-- Round-tripping from CopresheafData to DepCategoryData and back
    gives an equivalent composition type. -/
def depToFunctorData_functorDataToDep_compC.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).compC ≃
    data.compC where
  toFun c := c.2.2.2.2.2.2.1
  invFun c :=
    let h_match := congrFun data.h_comp_match c
    let h_dom := congrFun data.h_comp_dom c
    let h_cod := congrFun data.h_comp_cod c
    ⟨data.dom (data.right c), data.cod (data.right c),
     data.cod (data.left c), ⟨data.right c, rfl, rfl⟩,
     ⟨data.left c, h_match.symm, rfl⟩,
     ⟨data.composite c, h_dom, h_cod⟩,
     ⟨c, rfl, rfl, rfl⟩⟩
  left_inv c := by
    rcases c with ⟨a, b, c_obj, ⟨f, hfa, hfb⟩, ⟨g, hga, hgb⟩,
      ⟨h, hha, hhc⟩, ⟨comp, hr, hl, hcomp⟩⟩
    dsimp only [] at hr hl hcomp hfa hfb hga hgb hha hhc
    subst hfa hfb hr hl hcomp hgb
    rfl
  right_inv c := rfl

def depToFunctorData_functorDataToDep_compCIso.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).compC ≅ data.compC where
  hom := (depToFunctorData_functorDataToDep_compC data).toFun
  inv := (depToFunctorData_functorDataToDep_compC data).invFun
  hom_inv_id := by
    funext c
    exact (depToFunctorData_functorDataToDep_compC data).left_inv c
  inv_hom_id := by
    funext c
    exact (depToFunctorData_functorDataToDep_compC data).right_inv c

def functorDataToDep_depToFunctorData_compT.{u}
    (data : DepCategoryData.{u + 1}) (a b c : data.objT)
    (f : (functorDataToDep (depToFunctorData data)).morT a b)
    (g : (functorDataToDep (depToFunctorData data)).morT b c)
    (h : (functorDataToDep (depToFunctorData data)).morT a c) :
    (functorDataToDep (depToFunctorData data)).compT f g h ≃
    data.compT (extractRoundTrippedMor data a b f)
      (extractRoundTrippedMor data b c g)
      (extractRoundTrippedMor data a c h) where
  toFun wit :=
    cast (compT_mor_eq data a b c f g h wit) wit.val.2.2.2.2.2.2
  invFun wit :=
    ⟨⟨a, b, c,
      extractRoundTrippedMor data a b f,
      extractRoundTrippedMor data b c g,
      extractRoundTrippedMor data a c h,
      wit⟩,
     compT_invFun_right data a b c f g h wit,
     compT_invFun_left data a b c f g h wit,
     compT_invFun_composite data a b c f g h wit⟩
  left_inv :=
    fun ⟨⟨a_c, b_c, c_c, f_c, g_c, h_c, comp_wit⟩, hr, hl, hcomp⟩ => by
    match f, g, h with
    | ⟨⟨a_f, b_f, f'⟩, hfa, hfb⟩, ⟨⟨a_g, b_g, g'⟩, hga, hgb⟩,
      ⟨⟨a_h, b_h, h'⟩, hha, hhb⟩ =>
      simp only [depToFunctorData] at hr hl hcomp hfa hfb hga hgb hha hhb
      have hσ :=
        compTSigma_eq data hfa hfb hga hgb hha hhb hr hl hcomp comp_wit
      cases hσ
      simp [functorDataToDep_depToFunctorData_morT, cast_eq]
  right_inv := fun wit => by
    match f, g, h with
    | ⟨⟨a_f, b_f, f'⟩, hfa, hfb⟩, ⟨⟨a_g, b_g, g'⟩, hga, hgb⟩,
      ⟨⟨a_h, b_h, h'⟩, hha, hhb⟩ =>
      simp only [depToFunctorData] at hfa hfb hga hgb hha hhb
      have hr :=
        extractRoundTrippedMor_sigma_eq (data := data) (m := f') hfa hfb
      have hl := extractRoundTrippedMor_sigma_eq (data := data) (a := b)
        (b := c) (a' := a_g) (b' := b_g) (m := g') hga hgb
      have hcomp_eq := extractRoundTrippedMor_sigma_eq (data := data) (a := a)
        (b := c) (a' := a_h) (b' := b_h) (m := h') hha hhb
      have hσ :=
        compTSigma_eq data hfa hfb hga hgb hha hhb hr hl hcomp_eq wit
      cases hσ
      simp [functorDataToDep_depToFunctorData_morT, cast_eq]

def functorDataToDep_depToFunctorData_compIso.{u}
    (data : DepCategoryData.{u + 1}) (a b c : data.objT)
    (f : (functorDataToDep (depToFunctorData data)).morT a b)
    (g : (functorDataToDep (depToFunctorData data)).morT b c)
    (h : (functorDataToDep (depToFunctorData data)).morT a c) :
    (functorDataToDep (depToFunctorData data)).compT f g h ≅
    data.compT (extractRoundTrippedMor data a b f)
      (extractRoundTrippedMor data b c g)
      (extractRoundTrippedMor data a c h) where
  hom :=
    (functorDataToDep_depToFunctorData_compT data a b c f g h).toFun
  inv :=
    (functorDataToDep_depToFunctorData_compT data a b c f g h).invFun
  hom_inv_id := by
    funext comp_wit
    exact
      (functorDataToDep_depToFunctorData_compT data a b c f g h).left_inv
        comp_wit
  inv_hom_id := by
    funext comp_wit
    exact
      (functorDataToDep_depToFunctorData_compT data a b c f g h).right_inv
        comp_wit

abbrev functorToDataDep_mkCopresheafDep_morEquiv.{u}
    (data : DepCategoryData.{u + 1}) (a b : data.objT) :
    (functorToDataDep (mkCopresheafDep data)).morT a b ≃ data.morT a b := by
  change (functorDataToDep (depToFunctorData data)).morT a b ≃ data.morT a b
  exact functorDataToDep_depToFunctorData_morT data a b

abbrev functorToDataDep_mkCopresheafDep_idEquiv.{u} (data : DepCategoryData.{u + 1})
    {o : data.objT} (m : data.morT o o) :
    (functorToDataDep (mkCopresheafDep data)).idT
      ((sigmaTrivialSubtype o o).invFun m) ≃ data.idT m := by
  change (functorDataToDep (depToFunctorData data)).idT
    ((sigmaTrivialSubtype o o).invFun m) ≃ data.idT m
  exact functorDataToDep_depToFunctorData_idT data o
    ((sigmaTrivialSubtype o o).invFun m)

abbrev functorToDataDep_mkCopresheafDep_compEquiv.{u}
    (data : DepCategoryData.{u + 1}) {a b c : data.objT}
    (f : data.morT a b) (g : data.morT b c) (h : data.morT a c) :
    (functorToDataDep (mkCopresheafDep data)).compT
      ((sigmaTrivialSubtype a b).invFun f)
      ((sigmaTrivialSubtype b c).invFun g)
      ((sigmaTrivialSubtype a c).invFun h) ≃
    data.compT f g h := by
  change (functorDataToDep (depToFunctorData data)).compT
    ((sigmaTrivialSubtype a b).invFun f)
    ((sigmaTrivialSubtype b c).invFun g)
    ((sigmaTrivialSubtype a c).invFun h) ≃ data.compT f g h
  exact functorDataToDep_depToFunctorData_compT data a b c
    ((sigmaTrivialSubtype a b).invFun f)
    ((sigmaTrivialSubtype b c).invFun g)
    ((sigmaTrivialSubtype a c).invFun h)

/-- Round-tripping CopresheafData through DepCategoryData gives a
    naturally isomorphic functor. The component equivalences we proved
    show that the functors are the same on objects, morphisms, identities,
    and composition. -/
def mkCopresheaf_depToFunctorData_functorDataToDep.{u}
    (data : CopresheafData.{u}) :
    mkCopresheaf (depToFunctorData (functorDataToDep data)) ≅
    mkCopresheaf data :=
  NatIso.ofComponents
    (fun X => match X with
      | .obj => eqToIso (depToFunctorData_functorDataToDep_objC data)
      | .mor =>
          { hom := (depToFunctorData_functorDataToDep_morC data).toFun
            inv := (depToFunctorData_functorDataToDep_morC data).invFun
            hom_inv_id := by
              funext x
              exact (depToFunctorData_functorDataToDep_morC data).left_inv x
            inv_hom_id := by
              funext x
              exact (depToFunctorData_functorDataToDep_morC data).right_inv x }
      | .id =>
          { hom := (depToFunctorData_functorDataToDep_idC data).toFun
            inv := (depToFunctorData_functorDataToDep_idC data).invFun
            hom_inv_id := by
              funext x
              exact (depToFunctorData_functorDataToDep_idC data).left_inv x
            inv_hom_id := by
              funext x
              exact (depToFunctorData_functorDataToDep_idC data).right_inv x }
      | .comp =>
          { hom := (depToFunctorData_functorDataToDep_compC data).toFun
            inv := (depToFunctorData_functorDataToDep_compC data).invFun
            hom_inv_id := by
              funext x
              exact
                (depToFunctorData_functorDataToDep_compC data).left_inv x
            inv_hom_id := by
              funext x
              exact
                (depToFunctorData_functorDataToDep_compC data).right_inv x
          })
    (by
      intro X Y f
      cases f with
      | id => cases X <;> rfl
      | hom f' => cases f' <;>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_morC,
                   depToFunctorData_functorDataToDep_idC,
                   depToFunctorData_functorDataToDep_compC, mapSemiHom]
        <;> (first
          | (ext x
             simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
             exact x.snd.snd.property.1.symm)
          | (ext x
             simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
             exact x.snd.snd.property.2.symm)
          | (ext x
             simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
             exact x.snd.snd.property.symm)
          | (ext x
             simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
             exact x.snd.snd.snd.snd.snd.snd.property.1.symm)
          | (ext x
             simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
             exact x.snd.snd.snd.snd.snd.snd.property.2.1.symm)
          | (ext x
             simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
             exact x.snd.snd.snd.snd.snd.snd.property.2.2.symm)
          | (ext x
             simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
             calc x.fst
               _ = data.dom ↑x.snd.fst := x.snd.fst.property.1.symm
               _ = data.dom (data.idMor ↑x.snd.snd) :=
                     congrArg data.dom x.snd.snd.property.symm)
                    | (ext x
                       simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
                       calc x.snd.fst
                         _ = data.cod ↑x.snd.snd.snd.fst := x.snd.snd.snd.fst.property.2.symm
                         _ = data.cod (data.right ↑x.snd.snd.snd.snd.snd.snd) :=
                               congrArg data.cod x.snd.snd.snd.snd.snd.snd.property.1.symm)
                    | (ext x
                       simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
                       calc x.fst
                         _ = data.dom ↑x.snd.snd.snd.fst := x.snd.snd.snd.fst.property.1.symm
                         _ = data.dom (data.right ↑x.snd.snd.snd.snd.snd.snd) :=
                               congrArg data.dom x.snd.snd.snd.snd.snd.snd.property.1.symm)
                    | (ext x
                       simp only [eqToIso_refl, Iso.refl_hom, types_comp_apply, types_id_apply]
                       calc x.snd.snd.fst
                         _ = data.cod ↑x.snd.snd.snd.snd.fst :=
                           x.snd.snd.snd.snd.fst.property.2.symm
                         _ = data.cod (data.left ↑x.snd.snd.snd.snd.snd.snd) :=
                           congrArg data.cod
                             x.snd.snd.snd.snd.snd.snd.property.2.1.symm)))

/-- Round-tripping DepCategoryData through CopresheafData gives a
    naturally isomorphic functor. -/
def mkCopresheafDep_functorDataToDep_depToFunctorData.{u}
    (data : DepCategoryData.{u + 1}) :
    mkCopresheafDep (functorDataToDep (depToFunctorData data)) ≅
    mkCopresheafDep data :=
  NatIso.ofComponents
    (fun X => match X with
      | .obj => eqToIso (functorDataToDep_depToFunctorData_objT data)
      | .mor =>
          { hom := fun m => ⟨m.1, m.2.1,
                     (functorDataToDep_depToFunctorData_morT data m.1
                       m.2.1).toFun m.2.2⟩
            inv := fun m => ⟨m.1, m.2.1,
                     (functorDataToDep_depToFunctorData_morT data m.1
                       m.2.1).invFun m.2.2⟩
            hom_inv_id := by funext m; simp
            inv_hom_id := by funext m; simp }
      | .id =>
          { hom := fun i =>
              let m_equiv :=
                functorDataToDep_depToFunctorData_morT data i.1 i.1
              let m' := m_equiv.toFun i.2.1
              ⟨i.1, m',
                (functorDataToDep_depToFunctorData_idT data i.1
                  i.2.1).toFun i.2.2⟩
            inv := fun i =>
              let m_equiv :=
                functorDataToDep_depToFunctorData_morT data i.1 i.1
              let m_inv := m_equiv.invFun i.2.1
              let id_equiv :=
                functorDataToDep_depToFunctorData_idT data i.1 m_inv
              ⟨i.1, m_inv, id_equiv.invFun (cast (by
                simp [extractRoundTrippedMor]
                rfl) i.2.2)⟩
            hom_inv_id := by
              funext ⟨o, ⟨m, id_wit⟩⟩
              simp only [CategoryStruct.comp, Function.comp_apply, cast_eq]
              congr 1
              have hm :=
                (functorDataToDep_depToFunctorData_morT data o o).left_inv
                  m
              have hid :=
                (functorDataToDep_depToFunctorData_idT data o m).left_inv
                  id_wit
              rw [Sigma.mk.injEq]
              constructor
              · exact hm
              · grind
            inv_hom_id := by
              funext ⟨o, ⟨m, id_wit⟩⟩
              simp only [CategoryStruct.comp, Function.comp_apply, cast_eq]
              congr 1 }
      | .comp =>
          { hom := fun c =>
              let f_equiv :=
                functorDataToDep_depToFunctorData_morT data c.1 c.2.1
              let g_equiv :=
                functorDataToDep_depToFunctorData_morT data c.2.1 c.2.2.1
              let h_equiv :=
                functorDataToDep_depToFunctorData_morT data c.1 c.2.2.1
              ⟨c.1, c.2.1, c.2.2.1,
               f_equiv.toFun c.2.2.2.1,
               g_equiv.toFun c.2.2.2.2.1,
               h_equiv.toFun c.2.2.2.2.2.1,
               (functorDataToDep_depToFunctorData_compT data c.1 c.2.1
                 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1
                 c.2.2.2.2.2.1).toFun c.2.2.2.2.2.2⟩
            inv := fun c =>
              let f_equiv :=
                functorDataToDep_depToFunctorData_morT data c.1 c.2.1
              let g_equiv :=
                functorDataToDep_depToFunctorData_morT data c.2.1 c.2.2.1
              let h_equiv :=
                functorDataToDep_depToFunctorData_morT data c.1 c.2.2.1
              let f_inv := f_equiv.invFun c.2.2.2.1
              let g_inv := g_equiv.invFun c.2.2.2.2.1
              let h_inv := h_equiv.invFun c.2.2.2.2.2.1
              let comp_equiv :=
                functorDataToDep_depToFunctorData_compT data c.1 c.2.1
                  c.2.2.1 f_inv g_inv h_inv
              ⟨c.1, c.2.1, c.2.2.1, f_inv, g_inv, h_inv,
               comp_equiv.invFun (cast (by
                 simp [extractRoundTrippedMor]
                 rfl) c.2.2.2.2.2.2)⟩
            hom_inv_id := by
              funext ⟨a, b, c, f, g, h, comp_wit⟩
              simp only [CategoryStruct.comp, Function.comp_apply, cast_eq]
              rcases f with
                ⟨⟨a_f, b_f, f'⟩, ha_f : a_f = a, hb_f : b_f = b⟩
              rcases g with
                ⟨⟨a_g, b_g, g'⟩, ha_g : a_g = b, hb_g : b_g = c⟩
              rcases h with
                ⟨⟨a_h, b_h, h'⟩, ha_h : a_h = a, hb_h : b_h = c⟩
              have hf :=
                (functorDataToDep_depToFunctorData_morT data a b).left_inv
                  ⟨⟨a_f, b_f, f'⟩, ha_f, hb_f⟩
              have hg :=
                (functorDataToDep_depToFunctorData_morT data b c).left_inv
                  ⟨⟨a_g, b_g, g'⟩, ha_g, hb_g⟩
              have hh :=
                (functorDataToDep_depToFunctorData_morT data a c).left_inv
                  ⟨⟨a_h, b_h, h'⟩, ha_h, hb_h⟩
              have hcomp :=
                (functorDataToDep_depToFunctorData_compT data a b c
                  ⟨⟨a_f, b_f, f'⟩, ha_f, hb_f⟩
                  ⟨⟨a_g, b_g, g'⟩, ha_g, hb_g⟩
                  ⟨⟨a_h, b_h, h'⟩, ha_h, hb_h⟩).left_inv comp_wit
              subst ha_f hb_f ha_g hb_g ha_h hb_h
              congr 1
              grind
            inv_hom_id := by
              funext ⟨a, b, c, f, g, h, comp_wit⟩
              simp only [CategoryStruct.comp, Function.comp_apply, cast_eq]
              have hf :=
                (functorDataToDep_depToFunctorData_morT data a b).right_inv
                  f
              have hg :=
                (functorDataToDep_depToFunctorData_morT data b c).right_inv
                  g
              have hh :=
                (functorDataToDep_depToFunctorData_morT data a c).right_inv
                  h
              let f_inv :=
                (functorDataToDep_depToFunctorData_morT data a b).invFun f
              let g_inv :=
                (functorDataToDep_depToFunctorData_morT data b c).invFun g
              let h_inv :=
                (functorDataToDep_depToFunctorData_morT data a c).invFun h
              have hcomp :=
                (functorDataToDep_depToFunctorData_compT data a b c f_inv
                  g_inv h_inv).right_inv comp_wit
              congr 1 })
    (by
      intro X Y f
      cases f with
      | id => cases X <;> rfl
      | hom f' =>
        cases f' with
        | dom =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | cod =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | idObj =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | idMor =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | left =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | right =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | composite =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | intermediate =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | compositeDom =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp
        | compositeCod =>
          simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                     depToFunctorData, functorDataToDep, mapSemiHom]
          ext x; simp)

end DepCategoryDataCorrespondences

section CategoryCopresheafCorrespondence

/-- Construct an object in the copresheaf category from DepCategoryData. -/
abbrev mkJudgmentCopresheafDep.{u} (data : DepCategoryData.{u + 1}) :
    JudgmentCopresheaves.{u} :=
  mkCopresheafDep data

end CategoryCopresheafCorrespondence

end CategoryJudgments

end GebLean
