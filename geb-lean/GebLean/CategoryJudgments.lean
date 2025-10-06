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

/-- Extract DepCategoryData from a copresheaf. -/
abbrev functorToDataDep.{u} (F : Obj ⥤ Type u) : DepCategoryData.{u} :=
  functorDataToDep (functorToData F)

/-- The composition functorToDataDep ∘ mkCopresheafDep simplifies to
    functorDataToDep ∘ depToFunctorData, since functorToData and mkCopresheaf
    are inverses (they compose to the identity). -/
theorem functorToDataDep_mkCopresheafDep.{u} (data : DepCategoryData.{u}) :
    functorToDataDep (mkCopresheafDep data) =
    functorDataToDep (depToFunctorData data) := by
  simp only [functorToDataDep, mkCopresheafDep, mkCopresheaf,
    functorToData_mkFunctor]

/-- Round-tripping from DepCategoryData to CopresheafData and back
    preserves the object type. -/
theorem functorDataToDep_depToFunctorData_objT.{u}
    (data : DepCategoryData.{u}) :
    (functorDataToDep (depToFunctorData data)).objT = data.objT := rfl

/-- Round-tripping from CopresheafData to DepCategoryData and back
    preserves the object type. -/
theorem depToFunctorData_functorDataToDep_objC.{u} (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).objC = data.objC := rfl

/-- Round-tripping from DepCategoryData to CopresheafData and back
    gives an equivalent morphism type. -/
def functorDataToDep_depToFunctorData_morT.{u} (data : DepCategoryData.{u})
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

/-- Extract the underlying morphism from a round-tripped morphism type.
    When we go DepCategoryData → CopresheafData → DepCategoryData,
    morphisms get wrapped in sigma types and subtypes.
    This extracts the original using the round-trip equivalence. -/
abbrev extractRoundTrippedMor.{u} (data : DepCategoryData.{u})
    (a b : data.objT) :=
  (functorDataToDep_depToFunctorData_morT data a b).toFun

/-- Round-tripping from CopresheafData to DepCategoryData and back
    gives an equivalent identity type. -/
def depToFunctorData_functorDataToDep_idC.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).idC ≃
    data.idC where
  toFun i := i.2.2.val
  invFun i := ⟨data.dom (data.idMor i), ⟨data.idMor i, rfl,
    show data.cod (data.idMor i) =
      data.dom (data.idMor i) by
      have := congrFun data.h_id_endo i
      simp at this
      exact this.symm⟩, ⟨i, rfl⟩⟩
  left_inv i := by
    rcases i with ⟨o, ⟨m, hdom, hcod⟩, ⟨i, hi⟩⟩
    -- Extract: data.idMor i = m
    have him : data.idMor i = (⟨m, hdom, hcod⟩ :
      {m : data.morC // data.dom m = o ∧ data.cod m = o}).val := hi
    simp at him
    subst him hdom
    -- Now goal is: ⟨m, hcod⟩ = ⟨m, proof_from_h_id_endo⟩
    -- Both proofs are of the same Prop,
    -- equal by proof irrelevance
    rfl
  right_inv i := rfl

/-- Round-tripping from DepCategoryData to CopresheafData and back
    gives an equivalent identity type. -/
def functorDataToDep_depToFunctorData_idT.{u}
    (data : DepCategoryData.{u}) (o : data.objT)
    (m : (functorDataToDep (depToFunctorData data)).morT o o) :
    (functorDataToDep (depToFunctorData data)).idT m ≃
    data.idT (extractRoundTrippedMor data o o m) where
  toFun wit := by
    -- wit : {i : Σ (o : objT) (m : morT o o), idT m //
    --        idMor i = m.val}
    rcases wit with ⟨⟨o', m', w⟩,
      h : (depToFunctorData data).idMor ⟨o', m', w⟩ = m.val⟩
    -- m : {m : Σ a b, morT a b // dom m = o ∧ cod m = o}
    rcases m with ⟨⟨a, b, m⟩, ha : a = o, hb : b = o⟩
    -- Unfold depToFunctorData.idMor - it produces ⟨o', ⟨o', m'⟩⟩
    change (⟨o', ⟨o', m'⟩⟩ : Σ (a b : data.objT), data.morT a b) =
      ⟨a, ⟨b, m⟩⟩ at h
    -- Use Sigma.mk.inj to extract equalities
    rw [Sigma.mk.injEq] at h
    have ⟨ho', hsig⟩ := h
    subst ho' ha hb
    -- Now hsig : ⟨o, m'⟩ ≍ ⟨o, m⟩, convert to regular equality
    have hsig_eq := eq_of_heq hsig
    rw [Sigma.mk.injEq] at hsig_eq
    have ⟨_, hm⟩ := hsig_eq
    simp at hm
    subst hm
    simp [extractRoundTrippedMor]
    exact w
  invFun wit := by
    -- wit : idT (extractRoundTrippedMor ...)
    -- m : {m : Σ a b, morT a b // dom m = o ∧ cod m = o}
    refine ⟨⟨o, ⟨extractRoundTrippedMor data o o m, wit⟩⟩, ?_⟩
    -- Need to show:
    -- idMor ⟨o, ⟨extractRoundTrippedMor..., wit⟩⟩ = m.val
    simp only [depToFunctorData, extractRoundTrippedMor]
    rcases m with ⟨⟨a, b, mor⟩, ha, hb⟩
    simp only [depToFunctorData] at ha hb
    subst ha hb
    congr
  left_inv wit := by
    rcases wit with ⟨⟨o', m', w⟩, h⟩
    rcases m with ⟨⟨a, b, m⟩, ha : a = o, hb : b = o⟩
    change (⟨o', ⟨o', m'⟩⟩ : Σ (a b : data.objT), data.morT a b) =
      ⟨a, ⟨b, m⟩⟩ at h
    rw [Sigma.mk.injEq] at h
    have ⟨ho', hsig⟩ := h
    -- Subst a and b first, before ho'
    subst ha hb ho'
    have hsig_eq := eq_of_heq hsig
    rw [Sigma.mk.injEq] at hsig_eq
    have ⟨_, hm⟩ := hsig_eq
    simp at hm
    subst hm
    -- extractRoundTrippedMor evaluates to cast ... m'
    -- which simplifies to m'
    simp
    -- The identity witness just needs the matches to reduce
    congr 2
    (split; split; rfl)
  right_inv wit := by
    -- After round-trip, we should get back the same witness
    rcases m with ⟨⟨a, b, mor⟩, ha, hb⟩
    simp only [depToFunctorData] at ha hb
    subst ha hb
    -- Now mor : morT o o and wit : idT (cast ... mor)
    -- Beta-reduce to expose the match expressions
    dsimp only [id]
    simp only [extractRoundTrippedMor]
    (split; split; rfl)

/-- Round-tripping from CopresheafData to DepCategoryData and back
    gives an equivalent composition type. -/
def depToFunctorData_functorDataToDep_compC.{u}
    (data : CopresheafData.{u}) :
    (depToFunctorData (functorDataToDep data)).compC ≃
    data.compC where
  toFun c := by
    -- c : Σ a b c f g h, {comp : compC //
    --     right comp = f ∧ left comp = g ∧ composite comp = h}
    rcases c with ⟨_, _, _, _, _, _, ⟨comp, _⟩⟩
    exact comp
  invFun c := ⟨data.dom (data.right c), data.cod (data.right c),
    data.cod (data.left c), ⟨data.right c, rfl, rfl⟩,
    ⟨data.left c,
      show data.dom (data.left c) = data.cod (data.right c) by
        have := congrFun data.h_comp_match c
        simp at this
        exact this.symm,
      rfl⟩,
    ⟨data.composite c,
      show data.dom (data.composite c) = data.dom (data.right c) by
        have := congrFun data.h_comp_dom c
        simp at this
        exact this,
      show data.cod (data.composite c) = data.cod (data.left c) by
        have := congrFun data.h_comp_cod c
        simp at this
        exact this⟩,
    ⟨c, rfl, rfl, rfl⟩⟩
  left_inv c := by
    rcases c with ⟨a, b, c_obj, ⟨f, hfa, hfb⟩, ⟨g, hga, hgb⟩,
      ⟨h, hha, hhc⟩, ⟨comp, hr, hl, hcomp⟩⟩
    simp at hr hl hcomp hfa hfb hga hgb hha hhc
    subst hfa hfb hr hl hcomp hgb
    rfl
  right_inv c := rfl

def functorDataToDep_depToFunctorData_compT.{u}
    (data : DepCategoryData.{u}) (a b c : data.objT)
    (f : (functorDataToDep (depToFunctorData data)).morT a b)
    (g : (functorDataToDep (depToFunctorData data)).morT b c)
    (h : (functorDataToDep (depToFunctorData data)).morT a c) :
    (functorDataToDep (depToFunctorData data)).compT f g h ≃
    data.compT (extractRoundTrippedMor data a b f)
      (extractRoundTrippedMor data b c g)
      (extractRoundTrippedMor data a c h) where
  toFun wit := by
    rcases wit with ⟨⟨a_c, b_c, c_c, f_c, g_c, h_c, comp_wit⟩,
      hr, hl, hcomp⟩
    rcases f with ⟨⟨a_f, b_f, f'⟩, hfa : a_f = a, hfb : b_f = b⟩
    rcases g with ⟨⟨a_g, b_g, g'⟩, hga : a_g = b, hgb : b_g = c⟩
    rcases h with ⟨⟨a_h, b_h, h'⟩, hha : a_h = a, hhb : b_h = c⟩
    simp only [depToFunctorData] at hr hl hcomp
    change (⟨a_c, ⟨b_c, f_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
      ⟨a_f, ⟨b_f, f'⟩⟩ at hr
    change (⟨b_c, ⟨c_c, g_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
      ⟨a_g, ⟨b_g, g'⟩⟩ at hl
    change (⟨a_c, ⟨c_c, h_c⟩⟩ : Σ (x y : data.objT), data.morT x y) =
      ⟨a_h, ⟨b_h, h'⟩⟩ at hcomp
    rw [Sigma.mk.injEq] at hr hl hcomp
    have ⟨ha_c, hrf⟩ := hr
    have ⟨hb_c, hlg⟩ := hl
    have ⟨ha_c', hcomph⟩ := hcomp
    subst ha_c ha_c' hb_c
    have hrf_eq := eq_of_heq hrf
    have hlg_eq := eq_of_heq hlg
    have hcomph_eq := eq_of_heq hcomph
    rw [Sigma.mk.injEq] at hrf_eq hlg_eq hcomph_eq
    have ⟨hb_f, hf'⟩ := hrf_eq
    have ⟨hb_g, hg'⟩ := hlg_eq
    have ⟨hb_h, hh'⟩ := hcomph_eq
    subst hb_f hb_g hb_h
    have hf : f_c = f' := eq_of_heq hf'
    have hg : g_c = g' := eq_of_heq hg'
    have hh : h_c = h' := eq_of_heq hh'
    subst hf hg hh
    -- Now hfa : a_c = a, hfb : b_c = b, hga : b_c = b,
    -- hgb : c_c = c, hha : a_c = a, hhb : c_c = c
    have : a = a_c := hfa.symm
    have : b = b_c := hfb.symm
    have : c = c_c := hgb.symm
    subst_vars
    simp only [extractRoundTrippedMor]
    exact comp_wit
  invFun wit := by
    refine ⟨⟨a, b, c,
      extractRoundTrippedMor data a b f,
      extractRoundTrippedMor data b c g,
      extractRoundTrippedMor data a c h,
      wit⟩, ?_, ?_, ?_⟩
    · simp only [depToFunctorData, extractRoundTrippedMor]
      rcases f with ⟨⟨a', b', f'⟩, hfa, hfb⟩
      simp only [depToFunctorData] at hfa hfb
      subst hfa hfb
      rfl
    · simp only [depToFunctorData, extractRoundTrippedMor]
      rcases g with ⟨⟨a', b', g'⟩, hga, hgb⟩
      simp only [depToFunctorData] at hga hgb
      subst hga hgb
      rfl
    · simp only [depToFunctorData, extractRoundTrippedMor]
      rcases h with ⟨⟨a', b', h'⟩, hha, hhb⟩
      simp only [depToFunctorData] at hha hhb
      subst hha hhb
      rfl
  left_inv :=
    fun ⟨⟨a_c, b_c, c_c, f_c, g_c, h_c, comp_wit⟩, hr, hl, hcomp⟩ => by
    match f, g, h with
    | ⟨⟨a_f, b_f, f'⟩, hfa, hfb⟩, ⟨⟨a_g, b_g, g'⟩, hga, hgb⟩,
      ⟨⟨a_h, b_h, h'⟩, hha, hhb⟩ =>
      simp only [depToFunctorData] at hr hl hcomp hfa hfb hga hgb hha hhb
      simp only [extractRoundTrippedMor]
      -- hl : ⟨b_c, ⟨c_c, g_c⟩⟩ = ⟨a_g, ⟨b_g, g'⟩⟩
      -- hcomp : ⟨a_c, ⟨c_c, h_c⟩⟩ = ⟨a_h, ⟨b_h, h'⟩⟩
      rw [Sigma.mk.injEq] at hr hl hcomp
      have ⟨ha_c, hrf⟩ := hr
      have ⟨hb_c, hlg⟩ := hl
      have ⟨ha_c', hcomph⟩ := hcomp
      subst ha_c ha_c' hb_c
      have hrf_eq := eq_of_heq hrf
      have hlg_eq := eq_of_heq hlg
      have hcomph_eq := eq_of_heq hcomph
      rw [Sigma.mk.injEq] at hrf_eq hlg_eq hcomph_eq
      have ⟨hb_f, hf'⟩ := hrf_eq
      have ⟨hb_g, hg'⟩ := hlg_eq
      have ⟨hb_h, hh'⟩ := hcomph_eq
      subst hb_f hb_g hb_h
      have hf : f_c = f' := eq_of_heq hf'
      have hg : g_c = g' := eq_of_heq hg'
      have hh : h_c = h' := eq_of_heq hh'
      subst hf hg hh
      have : a = a_c := hfa.symm
      have : b = b_c := hfb.symm
      have : c = c_c := hgb.symm
      subst_vars
      simp only []
      dsimp only [id]
      split; split; split; split; split; split
      rfl
  right_inv := fun wit => by
    match f, g, h with
    | ⟨⟨a_f, b_f, f'⟩, hfa, hfb⟩, ⟨⟨a_g, b_g, g'⟩, hga, hgb⟩,
      ⟨⟨a_h, b_h, h'⟩, hha, hhb⟩ =>
      simp only [depToFunctorData] at hfa hfb hga hgb hha hhb
      simp only [extractRoundTrippedMor]
      subst hfa hfb hga hgb hha hhb
      dsimp only [id]
      split; split; split; split; split; split
      rfl

abbrev functorToDataDep_mkCopresheafDep_morEquiv.{u} (data : DepCategoryData.{u})
    (a b : data.objT) :
    (functorToDataDep (mkCopresheafDep data)).morT a b ≃ data.morT a b := by
  change (functorDataToDep (depToFunctorData data)).morT a b ≃ data.morT a b
  exact functorDataToDep_depToFunctorData_morT data a b

abbrev functorToDataDep_mkCopresheafDep_idEquiv.{u} (data : DepCategoryData.{u})
    {o : data.objT} (m : data.morT o o) :
    (functorToDataDep (mkCopresheafDep data)).idT
      ((sigmaTrivialSubtype o o).invFun m) ≃ data.idT m := by
  change (functorDataToDep (depToFunctorData data)).idT
    ((sigmaTrivialSubtype o o).invFun m) ≃ data.idT m
  exact functorDataToDep_depToFunctorData_idT data o
    ((sigmaTrivialSubtype o o).invFun m)

abbrev functorToDataDep_mkCopresheafDep_compEquiv.{u} (data : DepCategoryData.{u})
    {a b c : data.objT}
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
      cases f
      case identity => cases X <;> rfl
      case dom =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_morC]
        ext x; simp; exact x.snd.snd.property.1.symm
      case cod =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_morC]
        ext x; simp; exact x.snd.snd.property.2.symm
      case idObj =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_idC]
        ext x; simp
        calc x.fst
          _ = data.dom ↑x.snd.fst := x.snd.fst.property.1.symm
          _ = data.dom (data.idMor ↑x.snd.snd) :=
                congrArg data.dom x.snd.snd.property.symm
      case idMor =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_idC]
        ext x; simp; exact x.snd.snd.property.symm
      case left =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_compC]
        ext x; simp; exact x.snd.snd.snd.snd.snd.snd.property.2.1.symm
      case right =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_compC]
        ext x; simp; exact x.snd.snd.snd.snd.snd.snd.property.1.symm
      case composite =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_compC]
        ext x; simp; exact x.snd.snd.snd.snd.snd.snd.property.2.2.symm
      case intermediate =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_compC]
        ext x; simp
        calc x.snd.fst
          _ = data.cod ↑x.snd.snd.snd.fst := x.snd.snd.snd.fst.property.2.symm
          _ = data.cod (data.right ↑x.snd.snd.snd.snd.snd.snd) :=
                congrArg data.cod x.snd.snd.snd.snd.snd.snd.property.1.symm
      case compositeDom =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_compC]
        ext x; simp
        calc x.fst
          _ = data.dom ↑x.snd.snd.snd.fst := x.snd.snd.snd.fst.property.1.symm
          _ = data.dom (data.right ↑x.snd.snd.snd.snd.snd.snd) :=
                congrArg data.dom x.snd.snd.snd.snd.snd.snd.property.1.symm
      case compositeCod =>
        simp only [mkCopresheaf, mkFunctor, depToFunctorData, functorDataToDep,
                   depToFunctorData_functorDataToDep_compC]
        ext x; simp
        calc x.snd.snd.fst
          _ = data.cod ↑x.snd.snd.snd.snd.fst :=
            x.snd.snd.snd.snd.fst.property.2.symm
          _ = data.cod (data.left ↑x.snd.snd.snd.snd.snd.snd) :=
            congrArg data.cod
              x.snd.snd.snd.snd.snd.snd.property.2.1.symm)

/-- Round-tripping DepCategoryData through CopresheafData gives a
    naturally isomorphic functor. -/
def mkCopresheafDep_functorDataToDep_depToFunctorData.{u}
    (data : DepCategoryData.{u}) :
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
              simp only [CategoryStruct.comp, CategoryStruct.id,
                Function.comp_apply, id_eq, cast_eq]
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
              simp only [CategoryStruct.comp, CategoryStruct.id,
                Function.comp_apply, id_eq, cast_eq]
              congr 1
              have hm :=
                (functorDataToDep_depToFunctorData_morT data o o).right_inv
                  m
              let m_inv :=
                (functorDataToDep_depToFunctorData_morT data o o).invFun m
              have hid :=
                (functorDataToDep_depToFunctorData_idT data o
                  m_inv).right_inv id_wit
              rw [Sigma.mk.injEq]
              constructor
              · exact hm
              · grind }
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
              simp only [CategoryStruct.comp, CategoryStruct.id,
                Function.comp_apply, id_eq, cast_eq]
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
              simp only [CategoryStruct.comp, CategoryStruct.id,
                Function.comp_apply, id_eq, cast_eq]
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
              congr 1
              grind })
    (by
      intro X Y f
      cases f
      case identity => cases X <;> rfl
      case dom =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x; simp
      case cod =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x; simp
      case idObj =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x; simp
      case idMor =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x
        on_goal 1 => simp only [CategoryStruct.comp, Function.comp_apply]
        rcases x with ⟨o, m, i⟩
        congr 1
      case left =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x
        on_goal 1 => simp only [CategoryStruct.comp, Function.comp_apply]
        rcases x with ⟨a, b, c, f, g, h, comp_wit⟩
        congr 1
      case right =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x
        on_goal 1 => simp only [CategoryStruct.comp, Function.comp_apply]
        rcases x with ⟨a, b, c, f, g, h, comp_wit⟩
        congr 1
      case composite =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x
        on_goal 1 => simp only [CategoryStruct.comp, Function.comp_apply]
        rcases x with ⟨a, b, c, f, g, h, comp_wit⟩
        congr 1
      case intermediate =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x; simp
      case compositeDom =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x; simp
      case compositeCod =>
        simp only [mkCopresheafDep, mkCopresheaf, mkFunctor,
                   depToFunctorData, functorDataToDep]
        ext x; simp)

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
