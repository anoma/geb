/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.CategoryTheory.Grothendieck.Basic

/-!
# Functors out of a Grothendieck construction

For `F : C ⥤ Cat`, a functor `Grothendieck F ⥤ E` amounts to a fiber functor
over each object of `C` together with a transition transformation over each
morphism of `C`, subject to identity and composition coherence; a natural
transformation of two such functors amounts to a transformation of fiber
functors coherent with the transitions. This module bundles each family of
data as a structure, gives the data a category structure whose morphisms are
the bundled transformations, and compares that category with the functor
category. The contravariant construction is treated alongside the covariant
one.

## Main definitions

* `CategoryTheory.Grothendieck.FunctorFromData` and
  `Grothendieck.functorFromData`
* `CategoryTheory.Grothendieck.NatTransFromData` and
  `Grothendieck.natTransFrom`
* `CategoryTheory.Functor.leftOpEquiv`
* `CategoryTheory.CoGrothendieck.FunctorFromData`, with the constructor
  `FunctorFromData.mk`, its accessors, and the morphism interface
  `natTransFromMk`/`natTransFromFibNat`

## Main statements

* `Grothendieck.natTransFromEquiv`: the transformation data determines the
  transformation, bijectively
* `Grothendieck.functorFromDataEquivCat` and
  `CoGrothendieck.functorFromDataEquivCat`: the category of data is equivalent
  to the functor category

## Implementation notes

The correspondence is an equivalence rather than an isomorphism: extracting the
fiber functors from `functorFromData data` restricts along `Grothendieck.ι`,
which recovers `data.fib c` up to the canonical isomorphism
`ιCompFunctorFromData` rather than on the nose.

`functorFromData` repeats the construction of mathlib's
`Grothendieck.functorFrom` rather than calling it. The coherence arguments of
mathlib's version carry `eqToHom` proof terms private to that module, and the
module system does not export them, so a definition applying it fails in the
kernel with an unknown private constant.

The contravariant data type is the covariant one for `G ⋙ Cat.opFunctor`,
taken in the opposite category so that its transformations run in the direction
of the codomain, with a constructor and accessors phrased in terms of morphisms
of `C`. `Functor.leftOpEquiv` supplies the transport of the equivalence; the
conversions between the two presentations of the coherence conditions are the
image and preimage of the whole equation under `NatTrans.op`.

`Cat` is a semireducible `def` whose morphisms are a bundled `Cat.Hom`, so
keyed `simp`/`rw` matching fails against generic lemmas on terms routed through
`F.obj`/`F.map` even where the two sides are definitionally equal; see
`Geb/Mathlib/CategoryTheory/Grothendieck/Basic.lean` § Implementation notes.
The `erw` steps below isolate exactly those crossings.

## References

The description of functors out of a Grothendieck construction by fiberwise
data is standard; see [Vistoli2008] and [JohnsonYau2021].

## Tags

Grothendieck construction, contravariant, functor category, universal property
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆

namespace CategoryTheory

open CategoryTheory.Functor

namespace Grothendieck

variable {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{v₂, u₂})

/-! ### Functors out of a covariant Grothendieck construction -/

variable {E : Type u₃} [Category.{v₃} E]

variable (E) in
/-- The fiber-functor component of the data determining a functor out of
`Grothendieck F`: a functor on the fiber over each object of `C`. -/
abbrev FunctorFromFib := ∀ c, F.obj c ⥤ E

/-- The transition component of the data determining a functor out of
`Grothendieck F`: for each `f : c ⟶ c'`, a transformation from the fiber functor
over `c` to the fiber functor over `c'` precomposed with the pushforward. -/
abbrev FunctorFromHom (fib : FunctorFromFib F E) :=
  ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c'

/-- The identity coherence condition on the transition component. -/
abbrev FunctorFromHomId (fib : FunctorFromFib F E) (hom : FunctorFromHom F fib) :=
  ∀ c, hom (𝟙 c) = eqToHom (by simp only [CategoryTheory.Functor.map_id]; rfl)

/-- The composition coherence condition on the transition component. -/
abbrev FunctorFromHomComp (fib : FunctorFromFib F E) (hom : FunctorFromHom F fib) :=
  ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
    hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (hom g) ≫
      eqToHom (by simp only [CategoryTheory.Functor.map_comp]; rfl)

variable (E) in
/-- The data determining a functor `Grothendieck F ⥤ E`: a fiber functor over
each object of `C`, a transition transformation over each morphism of `C`, and
the two coherence conditions. -/
structure FunctorFromData : Type (max u v u₂ v₂ u₃ v₃) where
  /-- The fiber functor over each object of `C`. -/
  fib : FunctorFromFib F E
  /-- The transition transformation over each morphism of `C`. -/
  hom : FunctorFromHom F fib
  /-- Identity coherence. -/
  hom_id : FunctorFromHomId F fib hom
  /-- Composition coherence. -/
  hom_comp : FunctorFromHomComp F fib hom

variable {F}

set_option backward.isDefEq.respectTransparency false in
/-- The functor `Grothendieck F ⥤ E` determined by a `FunctorFromData`. -/
def functorFromData (data : FunctorFromData F E) : Grothendieck F ⥤ E where
  obj X := (data.fib X.base).obj X.fiber
  map f := (data.hom f.base).app _ ≫ (data.fib _).map f.fiber
  map_id X := by simp [data.hom_id, eqToHom_map]
  map_comp f g := by simp [data.hom_comp, eqToHom_map]

set_option backward.isDefEq.respectTransparency false in
/-- The `FunctorFromData` determined by a functor `Grothendieck F ⥤ E`: restrict
along the fiber inclusions, with the transitions induced by `ιNatTrans`. -/
def ofFunctorFrom (H : Grothendieck F ⥤ E) : FunctorFromData F E where
  fib c := Grothendieck.ι F c ⋙ H
  hom f := Functor.whiskerRight (Grothendieck.ιNatTrans f) H
  hom_id c := by
    ext x
    have heq : (⟨c, x⟩ : Grothendieck F) = ⟨c, (F.map (𝟙 c)).toFunctor.obj x⟩ := by
      simp only [CategoryTheory.Functor.map_id]
      rfl
    have h : (Grothendieck.ιNatTrans (F := F) (𝟙 c)).app x = eqToHom heq := by
      refine Grothendieck.ext _ _ (by simp [Grothendieck.ι]) ?_
      simp only [Functor.comp_obj, Grothendieck.ιNatTrans_app_fiber,
        Grothendieck.fiber_eqToHom]
      exact Category.comp_id _
    simp only [Functor.whiskerRight_app, h, eqToHom_app]
    exact eqToHom_map H heq
  hom_comp c₁ c₂ c₃ f g := by
    ext x
    simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, eqToHom_app, Grothendieck.ιNatTrans]
    rw [← Category.assoc, ← H.map_comp]
    have heq : (⟨c₃, (F.map g).toFunctor.obj ((F.map f).toFunctor.obj x)⟩ :
        Grothendieck F) = ⟨c₃, (F.map (f ≫ g)).toFunctor.obj x⟩ := by
      congr 1
      exact (Functor.congr_obj congr($(F.map_comp f g).toFunctor) x).symm
    rw [← eqToHom_map H heq, ← H.map_comp]
    congr 1
    refine Grothendieck.ext _ _ (by simp) ?_
    have hb : (eqToHom heq).base = 𝟙 c₃ := by
      erw [Grothendieck.base_eqToHom]
      simp
    have hF : (F.map (eqToHom heq).base).toFunctor = 𝟭 ↑(F.obj c₃) := by
      rw [hb, F.map_id]
      rfl
    simp only [Grothendieck.comp_fiber, Category.comp_id]
    rw [Functor.congr_hom hF]
    simp

/-- Restricting the functor determined by a `FunctorFromData` along a fiber
inclusion recovers the fiber functor over that object. -/
def ιCompFunctorFromData (data : FunctorFromData F E) (c : C) :
    Grothendieck.ι F c ⋙ functorFromData data ≅ data.fib c :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    simp [functorFromData, Grothendieck.ι, data.hom_id, eqToHom_map])

/-- The isomorphism `ιCompFunctorFromData` acts as the identity on objects. -/
@[simp]
theorem ιCompFunctorFromData_hom_app (data : FunctorFromData F E) (c : C)
    (x : F.obj c) : (ιCompFunctorFromData data c).hom.app x = 𝟙 _ :=
  rfl

/-- The inverse of `ιCompFunctorFromData` acts as the identity on objects. -/
@[simp]
theorem ιCompFunctorFromData_inv_app (data : FunctorFromData F E) (c : C)
    (x : F.obj c) : (ιCompFunctorFromData data c).inv.app x = 𝟙 _ :=
  rfl

/-- Building a functor from the data extracted from it recovers the functor. -/
def functorFromDataOfFunctorFrom (H : Grothendieck F ⥤ E) :
    functorFromData (ofFunctorFrom H) ≅ H :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {X Y} f ↦ by
    simp only [functorFromData, ofFunctorFrom, Functor.comp_obj, Functor.comp_map,
      Functor.whiskerRight_app, Iso.refl_hom]
    have hbase : ((Grothendieck.ιNatTrans (F := F) f.base).app X.fiber ≫
        (Grothendieck.ι F Y.base).map f.fiber).base = f.base := by
      erw [Grothendieck.comp_base]
      exact Category.comp_id _
    have hmor : (Grothendieck.ιNatTrans (F := F) f.base).app X.fiber ≫
        (Grothendieck.ι F Y.base).map f.fiber = f := by
      refine Grothendieck.ext _ _ hbase ?_
      erw [Grothendieck.comp_fiber]
      simp only [Grothendieck.ι, Grothendieck.ιNatTrans]
      erw [CategoryTheory.Functor.map_id (F.map (𝟙 Y.base)).toFunctor
        ((F.map f.base).toFunctor.obj X.fiber)]
      erw [Category.id_comp, eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
    erw [← Functor.map_comp, hmor]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The isomorphism `functorFromDataOfFunctorFrom` acts as the identity on
objects. -/
@[simp]
theorem functorFromDataOfFunctorFrom_hom_app (H : Grothendieck F ⥤ E)
    (X : Grothendieck F) : (functorFromDataOfFunctorFrom H).hom.app X = 𝟙 _ :=
  rfl

/-- The inverse of `functorFromDataOfFunctorFrom` acts as the identity on
objects. -/
@[simp]
theorem functorFromDataOfFunctorFrom_inv_app (H : Grothendieck F ⥤ E)
    (X : Grothendieck F) : (functorFromDataOfFunctorFrom H).inv.app X = 𝟙 _ :=
  rfl

/-! ### Natural transformations of functors out of a covariant Grothendieck
construction -/

variable (F)

/-- The fiber component of the data determining a natural transformation between
functors out of `Grothendieck F`. -/
abbrev NatTransFromFib (dataG dataH : FunctorFromData F E) :=
  ∀ c, dataG.fib c ⟶ dataH.fib c

/-- The coherence condition on the fiber component: the fiber transformations
commute with the transition transformations. -/
abbrev NatTransFromCoherence (dataG dataH : FunctorFromData F E)
    (fibNat : NatTransFromFib F dataG dataH) :=
  ∀ {c c' : C} (f : c ⟶ c'),
    dataG.hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (fibNat c') =
      fibNat c ≫ dataH.hom f

/-- The data determining a natural transformation between functors out of
`Grothendieck F`: a transformation of fiber functors over each object of `C`,
coherent with the transition transformations. -/
@[ext]
structure NatTransFromData (dataG dataH : FunctorFromData F E) :
    Type (max u u₂ v₃) where
  /-- The transformation of fiber functors over each object of `C`. -/
  fibNat : NatTransFromFib F dataG dataH
  /-- Coherence with the transition transformations. -/
  coherence : NatTransFromCoherence F dataG dataH fibNat

variable {F}

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation determined by a `NatTransFromData`. -/
def natTransFrom {dataG dataH : FunctorFromData F E}
    (nat : NatTransFromData F dataG dataH) :
    functorFromData dataG ⟶ functorFromData dataH where
  app X := (nat.fibNat X.base).app X.fiber
  naturality {X Y} f := by
    have h := congrFun (congrArg NatTrans.app (nat.coherence f.base)) X.fiber
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    simp only [functorFromData, Category.assoc, (nat.fibNat Y.base).naturality f.fiber]
    rw [← Category.assoc, ← Category.assoc, h, Category.assoc]

/-- The `NatTransFromData` determined by a natural transformation between
functors out of `Grothendieck F`. -/
def ofNatTransFrom {dataG dataH : FunctorFromData F E}
    (α : functorFromData dataG ⟶ functorFromData dataH) :
    NatTransFromData F dataG dataH where
  fibNat c := (ιCompFunctorFromData dataG c).inv ≫
    Functor.whiskerLeft (Grothendieck.ι F c) α ≫ (ιCompFunctorFromData dataH c).hom
  coherence {c c'} f := by
    ext x
    beta_reduce
    have nat := α.naturality ((Grothendieck.ιNatTrans (F := F) f).app x)
    simp only [functorFromData, Grothendieck.ιNatTrans, Functor.comp_obj] at nat
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at nat
    erw [Category.comp_id, Category.comp_id] at nat
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      ιCompFunctorFromData_hom_app, ιCompFunctorFromData_inv_app]
    erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]
    exact nat

/-- The fiber components of `ofNatTransFrom` are the components of the
transformation at the objects of the fiber. -/
@[simp]
theorem ofNatTransFrom_fibNat_app {dataG dataH : FunctorFromData F E}
    (α : functorFromData dataG ⟶ functorFromData dataH) (c : C) (x : F.obj c) :
    ((ofNatTransFrom α).fibNat c).app x = α.app ⟨c, x⟩ := by
  simp only [ofNatTransFrom, NatTrans.comp_app, Functor.whiskerLeft_app,
    ιCompFunctorFromData_hom_app, ιCompFunctorFromData_inv_app]
  erw [Category.id_comp, Category.comp_id]
  rfl

/-- The components of `natTransFrom` are the fiber components of the data at the
fiber objects. -/
@[simp]
theorem natTransFrom_app {dataG dataH : FunctorFromData F E}
    (nat : NatTransFromData F dataG dataH) (X : Grothendieck F) :
    (natTransFrom nat).app X = (nat.fibNat X.base).app X.fiber :=
  rfl

/-- Building a natural transformation from the data extracted from it recovers
the transformation. -/
theorem natTransFrom_ofNatTransFrom {dataG dataH : FunctorFromData F E}
    (α : functorFromData dataG ⟶ functorFromData dataH) :
    natTransFrom (ofNatTransFrom α) = α := by
  ext X
  simp only [natTransFrom_app, ofNatTransFrom_fibNat_app]

/-- Extracting the data from the natural transformation built on it recovers the
data. -/
theorem ofNatTransFrom_natTransFrom {dataG dataH : FunctorFromData F E}
    (nat : NatTransFromData F dataG dataH) :
    ofNatTransFrom (natTransFrom nat) = nat := by
  ext c x
  simp only [ofNatTransFrom_fibNat_app, natTransFrom_app]

/-- Natural transformations between functors out of `Grothendieck F` correspond
to their determining data. -/
def natTransFromEquiv (dataG dataH : FunctorFromData F E) :
    NatTransFromData F dataG dataH ≃
      (functorFromData dataG ⟶ functorFromData dataH) where
  toFun := natTransFrom
  invFun := ofNatTransFrom
  left_inv := ofNatTransFrom_natTransFrom
  right_inv := natTransFrom_ofNatTransFrom

/-- The identity transformation of a `FunctorFromData`. -/
def NatTransFromData.id (data : FunctorFromData F E) :
    NatTransFromData F data data where
  fibNat c := 𝟙 (data.fib c)
  coherence {c c'} f := by
    ext x
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Composition of transformations of `FunctorFromData`. -/
def NatTransFromData.comp {dataG dataH dataK : FunctorFromData F E}
    (nat₁ : NatTransFromData F dataG dataH)
    (nat₂ : NatTransFromData F dataH dataK) : NatTransFromData F dataG dataK where
  fibNat c := nat₁.fibNat c ≫ nat₂.fibNat c
  coherence {c c'} f := by
    ext x
    have h₁ := congrFun (congrArg NatTrans.app (nat₁.coherence f)) x
    have h₂ := congrFun (congrArg NatTrans.app (nat₂.coherence f)) x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁ h₂ ⊢
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable (F E) in
/-- The category of data determining functors `Grothendieck F ⥤ E`. -/
instance functorFromDataCategory : Category.{max u u₂ v₃} (FunctorFromData F E) where
  Hom := NatTransFromData F
  id := NatTransFromData.id
  comp := NatTransFromData.comp
  id_comp nat := by
    ext c x
    simp [NatTransFromData.comp, NatTransFromData.id]
  comp_id nat := by
    ext c x
    simp [NatTransFromData.comp, NatTransFromData.id]
  assoc nat₁ nat₂ nat₃ := by
    ext c x
    simp [NatTransFromData.comp]

/-- Composition in the category of data acts componentwise. -/
@[simp]
theorem comp_fibNat_app {dataG dataH dataK : FunctorFromData F E}
    (nat₁ : dataG ⟶ dataH) (nat₂ : dataH ⟶ dataK) (c : C) (x : F.obj c) :
    ((nat₁ ≫ nat₂).fibNat c).app x =
      (nat₁.fibNat c).app x ≫ (nat₂.fibNat c).app x :=
  rfl

/-- The identity of the category of data acts componentwise as an identity. -/
@[simp]
theorem id_fibNat_app (data : FunctorFromData F E) (c : C) (x : F.obj c) :
    (NatTransFromData.fibNat (𝟙 data) c).app x = 𝟙 ((data.fib c).obj x) :=
  rfl

/-- The data extracted from the functor determined by a `FunctorFromData`
recovers that data. -/
def ofFunctorFromFunctorFromData (data : FunctorFromData F E) :
    data ≅ ofFunctorFrom (functorFromData data) where
  hom :=
    { fibNat := fun c ↦ (ιCompFunctorFromData data c).inv
      coherence := fun {c c'} f ↦ by
        ext x
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
          ιCompFunctorFromData_inv_app, ofFunctorFrom, Functor.whiskerRight_app,
          functorFromData, Grothendieck.ιNatTrans]
        erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.comp_id,
          Category.id_comp]
        rfl }
  inv :=
    { fibNat := fun c ↦ (ιCompFunctorFromData data c).hom
      coherence := fun {c c'} f ↦ by
        ext x
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
          ιCompFunctorFromData_hom_app, ofFunctorFrom, Functor.whiskerRight_app,
          functorFromData, Grothendieck.ιNatTrans]
        erw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
          Category.comp_id]
        rfl }
  hom_inv_id := by
    apply NatTransFromData.ext
    funext c
    ext x
    simp only [comp_fibNat_app, id_fibNat_app, ιCompFunctorFromData_hom_app,
      ιCompFunctorFromData_inv_app]
    erw [Category.comp_id]
  inv_hom_id := by
    apply NatTransFromData.ext
    funext c
    ext x
    simp only [comp_fibNat_app, id_fibNat_app, ιCompFunctorFromData_hom_app,
      ιCompFunctorFromData_inv_app]
    erw [Category.comp_id]
    rfl

/-- The fiber components of the transformation determined by
`ofFunctorFromFunctorFromData` are identities. -/
@[simp]
theorem ofFunctorFromFunctorFromData_hom_fibNat_app (data : FunctorFromData F E)
    (c : C) (x : F.obj c) :
    (((ofFunctorFromFunctorFromData data).hom).fibNat c).app x = 𝟙 _ :=
  rfl

variable (F E)

/-- The functor from the category of data determining functors
`Grothendieck F ⥤ E` to that functor category. -/
def functorFromDataToFunctorCat : FunctorFromData F E ⥤ (Grothendieck F ⥤ E) where
  obj := functorFromData
  map := natTransFrom
  map_id _ := by
    ext X
    simp only [natTransFrom_app, id_fibNat_app, NatTrans.id_app]
    rfl
  map_comp _ _ := by
    ext X
    simp only [natTransFrom_app, comp_fibNat_app, NatTrans.comp_app]
    rfl

/-- The functor from the functor category `Grothendieck F ⥤ E` to the category
of data determining its objects. -/
def functorCatToFunctorFromData : (Grothendieck F ⥤ E) ⥤ FunctorFromData F E where
  obj := ofFunctorFrom
  map {G H} α := ofNatTransFrom ((functorFromDataOfFunctorFrom G).hom ≫ α ≫
    (functorFromDataOfFunctorFrom H).inv)
  map_id G := by
    apply NatTransFromData.ext
    funext c
    ext x
    simp
    rfl
  map_comp {G H K} α β := by
    apply NatTransFromData.ext
    funext c
    ext x
    simp only [Category.assoc, ofNatTransFrom_fibNat_app, NatTrans.comp_app,
      functorFromDataOfFunctorFrom_hom_app, functorFromDataOfFunctorFrom_inv_app,
      comp_fibNat_app]
    erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id,
      Category.id_comp]
    rfl

/-- The fiber components of the transformation determined by
`functorCatToFunctorFromData` are the components of the transformation. -/
@[simp]
theorem functorCatToFunctorFromData_map_fibNat_app {G H : Grothendieck F ⥤ E}
    (α : G ⟶ H) (c : C) (x : F.obj c) :
    (((functorCatToFunctorFromData F E).map α).fibNat c).app x =
      α.app ⟨c, x⟩ := by
  simp only [functorCatToFunctorFromData, ofNatTransFrom_fibNat_app,
    NatTrans.comp_app, functorFromDataOfFunctorFrom_hom_app,
    functorFromDataOfFunctorFrom_inv_app]
  erw [Category.id_comp, Category.comp_id]

/-- The category of data determining functors `Grothendieck F ⥤ E` is
equivalent to that functor category. -/
def functorFromDataEquivCat : FunctorFromData F E ≌ (Grothendieck F ⥤ E) where
  functor := functorFromDataToFunctorCat F E
  inverse := functorCatToFunctorFromData F E
  unitIso := NatIso.ofComponents (fun data ↦ ofFunctorFromFunctorFromData data)
    (fun {data data'} nat ↦ by
      apply NatTransFromData.ext
      funext c
      ext x
      simp only [Functor.id_map, Functor.comp_map, functorFromDataToFunctorCat,
        comp_fibNat_app, functorCatToFunctorFromData_map_fibNat_app,
        natTransFrom_app, ofFunctorFromFunctorFromData_hom_fibNat_app]
      erw [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun H ↦ functorFromDataOfFunctorFrom H)
    (fun {G H} α ↦ by
      ext X
      simp only [Functor.id_map, Functor.comp_map, functorFromDataToFunctorCat,
        NatTrans.comp_app, functorCatToFunctorFromData_map_fibNat_app,
        natTransFrom_app, functorFromDataOfFunctorFrom_hom_app]
      erw [Category.comp_id, Category.id_comp])
  functor_unitIso_comp data := by
    ext X
    simp only [functorFromDataToFunctorCat, natTransFrom_app, NatTrans.comp_app,
      NatTrans.id_app]
    erw [Category.comp_id]
    rfl

variable {F E}

end Grothendieck

namespace Functor

/-- Functors into an opposite category correspond, contravariantly, to functors
out of the opposite of the domain. -/
def leftOpEquiv (A : Type u₁) [Category.{v₁} A] (B : Type u₃) [Category.{v₃} B] :
    (A ⥤ Bᵒᵖ)ᵒᵖ ≌ (Aᵒᵖ ⥤ B) where
  functor :=
    { obj := fun F ↦ F.unop.leftOp
      map := fun η ↦ NatTrans.leftOp η.unop
      map_id := fun _ ↦ by ext; rfl
      map_comp := fun _ _ ↦ by ext; rfl }
  inverse :=
    { obj := fun F ↦ Opposite.op F.rightOp
      map := fun η ↦ Quiver.Hom.op (NatTrans.rightOp η)
      map_id := fun _ ↦ by
        apply Quiver.Hom.unop_inj
        ext
        rfl
      map_comp := fun _ _ ↦ by
        apply Quiver.Hom.unop_inj
        ext
        rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by
    ext x
    simp
    rfl

end Functor

namespace CoGrothendieck

variable {C : Type u} [Category.{v} C] (G : Cᵒᵖ ⥤ Cat.{v₂, u₂})

variable {T : Type u₃} [Category.{v₃} T]

variable (T) in
/-- The fiber-functor component of the data determining a functor out of
`CoGrothendieck G`: a functor on the fiber over each object of `C`. -/
abbrev FunctorFromFib := ∀ c : C, G.obj (Opposite.op c) ⥤ T

/-- The transition component of the data determining a functor out of
`CoGrothendieck G`: for each `f : c ⟶ c'`, a transformation from the fiber
functor over `c` precomposed with the pullback to the fiber functor over
`c'`. -/
abbrev FunctorFromHom (fib : FunctorFromFib G T) :=
  ∀ {c c' : C} (f : c ⟶ c'), (G.map f.op).toFunctor ⋙ fib c ⟶ fib c'

/-- The identity coherence condition on the transition component. -/
abbrev FunctorFromHomId (fib : FunctorFromFib G T) (hom : FunctorFromHom G fib) :=
  ∀ c, hom (𝟙 c) =
    eqToHom (by simp only [op_id, CategoryTheory.Functor.map_id]; rfl)

/-- The composition coherence condition on the transition component. -/
abbrev FunctorFromHomComp (fib : FunctorFromFib G T)
    (hom : FunctorFromHom G fib) :=
  ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
    eqToHom (by simp only [op_comp, CategoryTheory.Functor.map_comp]; rfl) ≫
      Functor.whiskerLeft (G.map g.op).toFunctor (hom f) ≫ hom g

variable (T) in
/-- The data determining a functor `CoGrothendieck G ⥤ T`: the data determining
the corresponding functor `GrothendieckOp G ⥤ Tᵒᵖ`, taken in the opposite
category so that its transformations run in the direction of `T`. -/
@[implicit_reducible]
def FunctorFromData : Type (max u v u₂ v₂ u₃ v₃) :=
  (Grothendieck.FunctorFromData (G ⋙ Cat.opFunctor) Tᵒᵖ)ᵒᵖ

/-- The category structure on the data determining functors
`CoGrothendieck G ⥤ T`, inherited from the opposite of the covariant one. -/
instance functorFromDataCategory : Category.{max u u₂ v₃} (FunctorFromData G T) :=
  inferInstanceAs
    (Category (Grothendieck.FunctorFromData (G ⋙ Cat.opFunctor) Tᵒᵖ)ᵒᵖ)

variable {G}

/-- Construct the data determining a functor `CoGrothendieck G ⥤ T` from a fiber
functor over each object of `C`, a transition transformation over each morphism
of `C`, and the two coherence conditions. -/
def FunctorFromData.mk (fib : FunctorFromFib G T) (hom : FunctorFromHom G fib)
    (hom_id : FunctorFromHomId G fib hom)
    (hom_comp : FunctorFromHomComp G fib hom) : FunctorFromData G T :=
  Opposite.op
    { fib := fun c ↦ (fib c.unop).op
      hom := fun f ↦ NatTrans.op (hom f.unop)
      hom_id := fun c ↦ by
        ext x
        simp only [NatTrans.op_app, unop_id, hom_id c.unop, eqToHom_app,
          eqToHom_op]
        erw [eqToHom_app]
        rfl
      hom_comp := fun c₁ c₂ c₃ f g ↦ by
        ext x
        erw [NatTrans.comp_app, NatTrans.comp_app]
        simp only [NatTrans.op_app, unop_comp,
          hom_comp c₃.unop c₂.unop c₁.unop g.unop f.unop, op_comp]
        erw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
          op_comp, op_comp, Category.assoc, Functor.whiskerLeft_app,
          NatTrans.op_app, eqToHom_app, eqToHom_op, eqToHom_app]
        rfl }

/-- The fiber functor over each object of `C`. -/
def FunctorFromData.fib (data : FunctorFromData G T) : FunctorFromFib G T :=
  fun c ↦ (data.unop.fib (Opposite.op c)).unop

/-- The transition transformation over each morphism of `C`. -/
def FunctorFromData.hom (data : FunctorFromData G T) :
    FunctorFromHom G data.fib :=
  fun f ↦ NatTrans.unop (data.unop.hom f.op)

/-- The identity coherence satisfied by the transition transformations. -/
theorem FunctorFromData.hom_id (data : FunctorFromData G T) :
    FunctorFromHomId G data.fib data.hom := fun c ↦ by
  ext x
  simp only [FunctorFromData.hom, op_id, data.unop.hom_id]
  erw [NatTrans.unop_app, eqToHom_app, eqToHom_unop, eqToHom_app]
  rfl

/-- The composition coherence satisfied by the transition transformations. -/
theorem FunctorFromData.hom_comp (data : FunctorFromData G T) :
    FunctorFromHomComp G data.fib data.hom := fun c₁ c₂ c₃ f g ↦ by
  ext x
  simp only [FunctorFromData.hom, op_comp, data.unop.hom_comp]
  erw [NatTrans.unop_app, NatTrans.comp_app, NatTrans.comp_app, unop_comp,
    unop_comp, Functor.whiskerLeft_app, eqToHom_app, eqToHom_unop,
    NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    NatTrans.unop_app, NatTrans.unop_app, eqToHom_app, Category.assoc]
  rfl

/-- `FunctorFromData.mk` recovers the fiber functors on the nose. -/
@[simp]
theorem FunctorFromData.fib_mk (fib : FunctorFromFib G T)
    (hom : FunctorFromHom G fib) (hom_id : FunctorFromHomId G fib hom)
    (hom_comp : FunctorFromHomComp G fib hom) (c : C) :
    (FunctorFromData.mk fib hom hom_id hom_comp).fib c = fib c :=
  rfl

/-- `FunctorFromData.mk` recovers the transition transformations on the nose. -/
@[simp]
theorem FunctorFromData.hom_mk (fib : FunctorFromFib G T)
    (hom : FunctorFromHom G fib) (hom_id : FunctorFromHomId G fib hom)
    (hom_comp : FunctorFromHomComp G fib hom) {c c' : C} (f : c ⟶ c') :
    (FunctorFromData.mk fib hom hom_id hom_comp).hom f = hom f :=
  rfl

variable (G) in
/-- The fiber component of the data determining a morphism between data
determining functors out of `CoGrothendieck G`. -/
abbrev NatTransFromFib (dataG dataH : FunctorFromData G T) :=
  ∀ c : C, dataG.fib c ⟶ dataH.fib c

variable (G) in
/-- The coherence condition on the fiber component: the fiber transformations
commute with the transition transformations. -/
abbrev NatTransFromCoherence (dataG dataH : FunctorFromData G T)
    (fibNat : NatTransFromFib G dataG dataH) :=
  ∀ {c c' : C} (f : c ⟶ c'),
    Functor.whiskerLeft (G.map f.op).toFunctor (fibNat c) ≫ dataH.hom f =
      dataG.hom f ≫ fibNat c'

/-- Construct a morphism of the data determining functors out of
`CoGrothendieck G` from a fiber component and its coherence. -/
def natTransFromMk {dataG dataH : FunctorFromData G T}
    (fibNat : NatTransFromFib G dataG dataH)
    (coherence : NatTransFromCoherence G dataG dataH fibNat) : dataG ⟶ dataH :=
  Quiver.Hom.op
    { fibNat := fun c ↦ NatTrans.op (fibNat c.unop)
      coherence := fun {_ _} f ↦ congrArg NatTrans.op (coherence f.unop) }

/-- The fiber component of a morphism of the data. -/
def natTransFromFibNat {dataG dataH : FunctorFromData G T} (nat : dataG ⟶ dataH) :
    NatTransFromFib G dataG dataH :=
  fun c ↦ NatTrans.unop (nat.unop.fibNat (Opposite.op c))

/-- The coherence satisfied by the fiber component of a morphism of the data. -/
theorem natTransFromCoherence {dataG dataH : FunctorFromData G T}
    (nat : dataG ⟶ dataH) :
    NatTransFromCoherence G dataG dataH (natTransFromFibNat nat) :=
  fun {_ _} f ↦ congrArg NatTrans.unop (nat.unop.coherence f.op)

/-- `natTransFromMk` recovers the fiber component on the nose. -/
@[simp]
theorem natTransFromFibNat_mk {dataG dataH : FunctorFromData G T}
    (fibNat : NatTransFromFib G dataG dataH)
    (coherence : NatTransFromCoherence G dataG dataH fibNat) (c : C) :
    natTransFromFibNat (natTransFromMk fibNat coherence) c = fibNat c :=
  rfl

/-- Every morphism of the data is assembled from its own fiber component. -/
theorem natTransFromMk_fibNat {dataG dataH : FunctorFromData G T}
    (nat : dataG ⟶ dataH)
    (coherence : NatTransFromCoherence G dataG dataH (natTransFromFibNat nat)) :
    natTransFromMk (natTransFromFibNat nat) coherence = nat :=
  rfl

/-- The functor `CoGrothendieck G ⥤ T` determined by a `FunctorFromData`. -/
def functorFromData (data : FunctorFromData G T) : CoGrothendieck G ⥤ T :=
  (Grothendieck.functorFromData data.unop).leftOp

/-- The `FunctorFromData` determined by a functor `CoGrothendieck G ⥤ T`. -/
def ofFunctorFrom (H : CoGrothendieck G ⥤ T) : FunctorFromData G T :=
  Opposite.op (Grothendieck.ofFunctorFrom H.rightOp)

variable (G T)

/-- The category of data determining functors `CoGrothendieck G ⥤ T` is
equivalent to that functor category. -/
def functorFromDataEquivCat : FunctorFromData G T ≌ (CoGrothendieck G ⥤ T) :=
  (Grothendieck.functorFromDataEquivCat (G ⋙ Cat.opFunctor) Tᵒᵖ).op.trans
    (Functor.leftOpEquiv (Grothendieck (G ⋙ Cat.opFunctor)) T)

variable {G T}


end CoGrothendieck

end CategoryTheory
