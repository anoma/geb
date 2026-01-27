import GebLean.Utilities.Elements
import GebLean.Utilities.Grothendieck
import GebLean.Utilities.Presheaf
import GebLean.Utilities.Slice
import GebLean.Utilities.TwistedArrow
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic

/-!
# Functor categories on twisted arrow categories

This module defines functor categories from the four twisted arrow category
variants to `Type v`:

- `TwArrCopresheaf C` = `TwistedArrow' C ⥤ Type v` (copresheaves on Tw)
- `TwArrPresheaf C` = `OpTwistedArrow' C ⥤ Type v` (presheaves on Tw)
- `TwArrOpCopresheaf C` = `TwistedArrowOp' C ⥤ Type v` (copresheaves on TwOp)
- `TwArrOpPresheaf C` = `CoTwistedArrow' C ⥤ Type v` (presheaves on TwOp)

Since `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`, functors from `OpTwistedArrow'`
are presheaves on `TwistedArrow'`. Similarly, since
`CoTwistedArrow' C ≅ (TwistedArrowOp' C)ᵒᵖ'`, functors from `CoTwistedArrow'`
are presheaves on `TwistedArrowOp'`.

Two of these have direct slice equivalences via `sliceEquivCopresheaf`:
- `Over hom' ≌ TwArrCopresheaf C`
- `Over homOp' ≌ TwArrOpCopresheaf C`
-/

universe v u

namespace GebLean

open CategoryTheory

variable (C : Type u) [CInst : Category.{v} C]

section TwArrCopresheaf

/--
Copresheaves on the twisted arrow category: covariant functors from
`TwistedArrow' C` to `Type v`.
-/
def TwArrCopresheaf := TwistedArrow' C ⥤ Type v

instance : Category (TwArrCopresheaf C) := by
  unfold TwArrCopresheaf
  infer_instance

/--
The slice category over `hom'` is equivalent to the category of copresheaves
on the twisted arrow category.
-/
def sliceEquivTwArrCopresheaf : Over (hom' (C := C)) ≌ TwArrCopresheaf C :=
  sliceEquivCopresheaf (hom' (C := C))

/--
Object map for the slice presheaf induced by a `TwArrCopresheaf`.

Given `F : TwArrCopresheaf C`, the object map takes a twisted arrow `(x, y, f)`
to a type. In curried form: `y` first (covariant), then `x` (contravariant),
then `f : x ⟶ y`. This lets us view `f` as a slice over `y`.

- `y : C` (covariant in the functor category)
- `x : C` (contravariant in the functor category)
- `f : x ⟶ y`
- Returns: `F.obj (twObjMk' f) : Type v`
-/
def TwArrCopresheaf.opSliceObj (F : TwArrCopresheaf C) (y : C) (x : C)
    (f : x ⟶ y) : Type v :=
  F.obj (twObjMk' f)

/--
Contravariant morphism map for the slice presheaf induced by a `TwArrCopresheaf`.

Given a morphism in `Over y` from `(f' : x' ⟶ y)` to `(f : x ⟶ y)`, i.e.,
`g : x' ⟶ x` with `g ≫ f = f'`, we get a twisted-arrow morphism from
`twObjMk' f` to `twObjMk' f'` with `domArr = g` and `codArr = 𝟙 y`.

This induces a map `F.opSliceObj C y x f → F.opSliceObj C y x' f'` via `F.map`.
-/
def TwArrCopresheaf.sliceContramap (F : TwArrCopresheaf C) {y : C} {x x' : C}
    {f : x ⟶ y} {f' : x' ⟶ y} (g : x' ⟶ x) (comm : g ≫ f = f') :
    F.opSliceObj C y x f → F.opSliceObj C y x' f' :=
  F.map (twHomMk' g (𝟙 y) (by
    simp only [twObjMk'_arr]
    rw [show f ≫ 𝟙 y = f from Category.comp_id f, comm]))

/--
For a fixed `y : C`, a `TwArrCopresheaf` induces a presheaf on `Over y`, i.e.,
a functor from `(Over y)ᵒᵖ'` to `Type v`. Objects `(f : x ⟶ y)` in `Over y`
map to `F.opSliceObj C y x f`, and morphisms in the opposite direction induce
maps via `sliceContramap`.
-/
def TwArrCopresheaf.slicePresheaf (F : TwArrCopresheaf C) (y : C) :
    (Over y)ᵒᵖ' ⥤ Type v where
  obj f := F.opSliceObj C y f.left f.hom
  map {f f'} g := F.sliceContramap C (Over.leftOp' g) (Over.w g)
  map_id f := by apply F.map_id
  map_comp {f f' f''} g g' := by
    unfold sliceContramap
    -- (g ≫ g') in (Over y)ᵒᵖ' is (g' ≫ g) in Over y
    have hcomp : (g ≫ g').left = g'.left ≫ g.left := op_comp_eq _ _
    -- Use F.map_comp and show the morphisms are equal
    rw [← F.map_comp]
    congr 1
    apply twHom'_ext
    · -- domArr: composition in TwistedArrow' reverses domain arrows
      simp only [hcomp, twDomArr']
      rfl
    · -- codArr: Both sides reduce to 𝟙 y
      simp only
        [twCodArr', twHomMk', CategoryOfElements.homMk,
         CategoryStruct.comp, Category.toCategoryStruct,
         instCategoryTwistedArrow']
      unfold id
      simp only [categoryOfElements]
      simp only [prod_comp]
      simp

/--
For a `TwArrCopresheaf F` and object `y : C`, this gives the object in the
contravariant Grothendieck construction over `overOpCopresheafFunctor` with
base `y` and fiber `F.slicePresheaf C y`.
-/
def TwArrCopresheaf.sliceGrothendieckObj (F : TwArrCopresheaf C) (y : C) :
    GrothendieckContra' (overOpCopresheafFunctor C) where
  base := y
  fiber := (F.slicePresheaf C y : OverOpPresheaf C y)

/--
Given a morphism `h : y ⟶ y'` in `C`, we get a natural transformation from
`F.slicePresheaf y` to `(overOpMapFunctor C).map h ⋙ F.slicePresheaf y'`.

For an object `(f : x ⟶ y)` in `(Over y)ᵒᵖ'`, the component maps
`F.obj (twObjMk' f.hom)` to `F.obj (twObjMk' (f.hom ≫ h))` via the twisted arrow
morphism with `domArr = 𝟙 x` and `codArr = h`.
-/
def TwArrCopresheaf.sliceNatTrans (F : TwArrCopresheaf C) {y y' : C}
    (h : y ⟶ y') :
    F.slicePresheaf C y ⟶
    (precompOverOpMap C h).obj (F.slicePresheaf C y') where
  app f := F.map (twHomMk'
    (x := twObjMk' f.hom)
    (y := twObjMk' (f.hom ≫ h))
    (𝟙 f.left) h (by simp only [twObjMk'_arr]; exact Category.id_comp _))
  naturality {f f'} g := by
    simp only [slicePresheaf, precompOverOpMap, Functor.whiskeringLeft,
      Functor.comp_obj, overOpMapFunctor,
      Cat.postCompOpFunctor', Functor.whiskeringRight, Over.mapFunctor,
      Functor.comp_map, Cat.opFunctor', sliceContramap]
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    apply twHom'_ext
    · simp only
        [twDomArr', twHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryTwistedArrow']
      unfold id
      simp only [categoryOfElements]
      simp only [prod_comp]
      simp
    · simp only
        [twCodArr', twHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryTwistedArrow']
      unfold id
      simp only [categoryOfElements]
      simp only [prod_comp]
      simp

/--
Given a morphism `h : y ⟶ y'` in `C`, we get a morphism in
`GrothendieckContra' (overOpCopresheafFunctor C)` from
`F.sliceGrothendieckObj y` to `F.sliceGrothendieckObj y'`.

The base morphism is `h`, and the fiber morphism is `F.sliceNatTrans h`.
-/
def TwArrCopresheaf.sliceGrothendieckHom (F : TwArrCopresheaf C) {y y' : C}
    (h : y ⟶ y') :
    F.sliceGrothendieckObj C y ⟶ F.sliceGrothendieckObj C y' where
  base := h
  fiber := F.sliceNatTrans C h

/--
The fiber function for the slice Grothendieck functor (contravariant case).
-/
def TwArrCopresheaf.sliceGrothendieckFib (F : TwArrCopresheaf C) :
    GrothendieckContra'.FunctorToFib (F' := overOpCopresheafFunctor C) (𝟭 C) :=
  fun y => F.slicePresheaf C y

/--
The morphism function for the slice Grothendieck functor (contravariant case).
For `h : y ⟶ y'` in `C`, produces the fiber morphism.
-/
def TwArrCopresheaf.sliceGrothendieckHomFiber (F : TwArrCopresheaf C) :
    GrothendieckContra'.FunctorToHom (𝟭 C) (F.sliceGrothendieckFib C) :=
  fun h => F.sliceNatTrans C h

private lemma TwArrCopresheaf.twObjMk'_comp_id {y : C} (f : Over y) :
    twObjMk' (f.hom ≫ 𝟙 y) = twObjMk' f.hom := by
  unfold twObjMk'
  congr 1
  exact Category.comp_id f.hom

private lemma twHomMk'_id_id_eq_eqToHom' {dom cod : C} (arr arr' : dom ⟶ cod)
    (h : arr = arr') (comm : 𝟙 dom ≫ arr ≫ 𝟙 cod = arr') :
    twHomMk'
      (x := twObjMk' arr)
      (y := twObjMk' arr')
      (𝟙 dom) (𝟙 cod) (by simp only [twObjMk'_arr]; exact comm) =
    eqToHom (congrArg twObjMk' h) := by
  subst h
  simp only [eqToHom_refl']
  apply twHom'_ext
  · simp only [twHomMk'_domArr]
    rfl
  · simp only [twHomMk'_codArr]
    rfl

private lemma TwArrCopresheaf.sliceNatTrans_id_app_is_id
    (F : TwArrCopresheaf C) (y : C) (f : Over y) :
    (F.sliceNatTrans C (@CategoryStruct.id C _ y)).app f =
    eqToHom (congrArg F.obj (twObjMk'_comp_id C f).symm) := by
  simp only [sliceNatTrans]
  have harr : f.hom ≫ 𝟙 y = f.hom := Category.comp_id f.hom
  have hcomm : 𝟙 f.left ≫ f.hom ≫ 𝟙 y = f.hom ≫ 𝟙 y := Category.id_comp _
  have hmor : twHomMk'
      (x := twObjMk' f.hom)
      (y := twObjMk' (f.hom ≫ 𝟙 y))
      (𝟙 f.left) (𝟙 y) (by simp only [twObjMk'_arr]; exact Category.id_comp _) =
      eqToHom (twObjMk'_comp_id C f).symm := by
    have h := twHomMk'_id_id_eq_eqToHom' C f.hom (f.hom ≫ 𝟙 y) harr.symm hcomm
    exact h
  rw [hmor, eqToHom_map]

/--
Identity coherence for sliceGrothendieckHomFiber (contravariant case).
-/
lemma TwArrCopresheaf.sliceGrothendieck_hom_id (F : TwArrCopresheaf C) :
    GrothendieckContra'.FunctorToHomId (overOpCopresheafFunctor C) (𝟭 C)
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro y
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, Functor.id_obj, Functor.id_map]
  have h := sliceNatTrans_id_app_is_id C F y f
  simp only [sliceNatTrans] at h ⊢
  rw [eqToHom_app]
  refine Eq.trans h ?_
  congr 1

/--
Composition coherence for sliceGrothendieckHomFiber (contravariant case).
-/
lemma TwArrCopresheaf.sliceGrothendieck_hom_comp (F : TwArrCopresheaf C) :
    GrothendieckContra'.FunctorToHomComp (overOpCopresheafFunctor C) (𝟭 C)
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro y y' y'' g h
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, Functor.id_obj, Functor.id_map]
  simp only [sliceNatTrans]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [overOpCopresheafFunctor, copresheafConstruction,
    Functor.op', Functor.comp_map,
    Functor.whiskeringLeft, overOpMapFunctor, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.toCatHom_toFunctor]
  rw [eqToHom_app]
  funext x
  simp only [types_comp_apply]
  have hassoc : f.hom ≫ g ≫ h = (f.hom ≫ g) ≫ h := (Category.assoc _ _ _).symm
  have htgt_type : twObjMk' (f.hom ≫ g ≫ h) = twObjMk' ((f.hom ≫ g) ≫ h) :=
    congrArg twObjMk' hassoc
  conv_rhs =>
    rw [← types_comp_apply (F.map _) (F.map _)]
    rw [← types_comp_apply _ (eqToHom _)]
    rw [← functor_map_eqToHom (p := htgt_type.symm)]
    rw [← F.map_comp, ← F.map_comp]
  refine congrFun (congrArg F.map ?_) x
  apply CategoryOfElements.ext
  simp only [twHomMk', CategoryOfElements.homMk]
  rw [CategoryOfElements.comp_val, CategoryOfElements.comp_val]
  rw [CategoryOfElements.eqToHom_val]
  have hfst_rfl : congrArg Sigma.fst htgt_type = rfl := proof_irrel _ _
  rw [hfst_rfl, eqToHom_refl, prod_id]
  simp only [twObjMk', functorOp'Obj]
  have hleft_eq :
      (((Cat.postCompOpFunctor'.obj (Over.mapFunctor C)).map g).toFunctor.obj f).left =
        f.left := rfl
  apply Prod.ext
  · simp only [CategoryOp'Inst, prod_comp]
    change 𝟙 f.left = 𝟙 f.left ≫ 𝟙 f.left ≫ 𝟙 f.left
    simp only [Category.comp_id]
  · simp only [prod_comp, Category.comp_id]

/--
Bundled data for constructing a functor from `C` into the contravariant
Grothendieck construction over `overOpCopresheafFunctor` (for TwArrCopresheaf).
-/
def TwArrCopresheaf.sliceGrothendieckData (F : TwArrCopresheaf C) :
    GrothendieckContra'.FunctorToData (E := C) (overOpCopresheafFunctor C) where
  baseFunc := 𝟭 C
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
Alternative section data representation using `SectionDataContra`.

Since `sliceGrothendieckData` has `baseFunc = 𝟭 C`, the data can equivalently
be viewed as section data for `overOpCopresheafFunctor C`. This provides a
cleaner mathematical interpretation: the functor is a section of the forgetful
functor `GrothendieckContra' (overOpCopresheafFunctor C) ⥤ C`.
-/
def TwArrCopresheaf.sliceSectionData (F : TwArrCopresheaf C) :
    GrothendieckContra'.SectionDataContra (overOpCopresheafFunctor C) where
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
The slice construction for a `TwArrCopresheaf` assembles into a functor from
`C` to the contravariant Grothendieck construction over `overOpCopresheafFunctor`.

For each object `y : C`, we get `(y, F.slicePresheaf y)` in the
Grothendieck construction. For each morphism `h : y ⟶ y'` in `C`, we get a
Grothendieck morphism from `(y, F.slicePresheaf y)` to `(y', F.slicePresheaf y')`.

This functor is a section of the forgetful functor:
`sliceGrothendieckFunctor ⋙ GrothendieckContra'.forget = 𝟭 C`.
-/
def TwArrCopresheaf.sliceGrothendieckFunctor (F : TwArrCopresheaf C) :
    C ⥤ GrothendieckContra' (overOpCopresheafFunctor C) :=
  (F.sliceSectionData C).toFunctor

/-! ### Reverse Construction: From Grothendieck Data to TwArrCopresheaf

Given data for a functor into the contravariant Grothendieck construction over
`overOpCopresheafFunctor C` with identity base functor, we construct a
twisted-arrow copresheaf.
-/

/--
The fiber type for a slice Grothendieck section: assigns to each `y : C` a
presheaf on `(Over y)ᵒᵖ'`.

Since the base functor is `𝟭 C`, this is equivalent to
`SectionFibContra (overOpCopresheafFunctor C)`.
-/
abbrev SliceGrothendieckFib :=
  GrothendieckContra'.FunctorToFib (F' := overOpCopresheafFunctor C) (𝟭 C)

/--
The morphism type for a slice Grothendieck section: assigns to each morphism
`h : y ⟶ y'` a natural transformation between the fibers.

Since the base functor is `𝟭 C`, this is equivalent to `SectionHomContra fib`.
-/
abbrev SliceGrothendieckHom (fib : SliceGrothendieckFib C) :=
  GrothendieckContra'.FunctorToHom (𝟭 C) fib

/--
Object map for the twisted-arrow copresheaf induced by slice Grothendieck data.
Given a twisted arrow `(f : x ⟶ y)`, we evaluate the fiber presheaf at `y`
on the over-object `Over.mk f`.
-/
def sliceGrothendieckFibObj (fib : SliceGrothendieckFib C)
    (tw : TwistedArrow' C) : Type v :=
  (fib (twCod' tw)).obj (Over.mk (twArr' tw))

/--
The Over morphism induced by a domain arrow in a twisted arrow morphism.
Given `domArr : x' ⟶ x` and arrows `f : x ⟶ y`, `f' : x' ⟶ y` with
`domArr ≫ f = f'`, we get a morphism in `Over y` from `Over.mk f'` to
`Over.mk f`.
-/
def overHomFromDomArr {y x x' : C} {f : x ⟶ y} {f' : x' ⟶ y}
    (domArr : x' ⟶ x) (hcomm : domArr ≫ f = f') :
    Over.mk f' ⟶ Over.mk f :=
  Over.homMk domArr hcomm

/--
Two `overHomFromDomArr` morphisms with the same underlying arrow are equal,
regardless of the commutativity proof used.
-/
lemma overHomFromDomArr_proof_irrel {y x x' : C} {f : x ⟶ y} {f' : x' ⟶ y}
    (domArr : x' ⟶ x) (hcomm hcomm' : domArr ≫ f = f') :
    overHomFromDomArr C domArr hcomm = overHomFromDomArr C domArr hcomm' := by
  apply CommaMorphism.ext <;> rfl

/--
When `domArr = 𝟙 x`, the `overHomFromDomArr` is the identity morphism.
-/
@[simp]
lemma overHomFromDomArr_id {y x : C} {f : x ⟶ y} (hcomm : 𝟙 x ≫ f = f) :
    overHomFromDomArr C (𝟙 x) hcomm = 𝟙 (Over.mk f) := by
  apply CommaMorphism.ext <;> rfl

/--
The `overHomFromDomArr` with identity domain arrow is `eqToHom` of a
commutativity-derived equality between the target Over objects.
-/
lemma overHomFromDomArr_id_eq_eqToHom {y x : C} {f : x ⟶ y} {g : x ⟶ y}
    (hcomm : 𝟙 x ≫ g = f) :
    overHomFromDomArr C (𝟙 x) hcomm = eqToHom (by simp [Category.id_comp] at hcomm
                                                  exact congrArg Over.mk hcomm.symm) := by
  simp only [Category.id_comp] at hcomm
  cases hcomm
  simp only [overHomFromDomArr, Over.homMk, Over.mk, eqToHom_refl]
  rfl

/--
Morphism map for the twisted-arrow copresheaf induced by slice Grothendieck data.

Given a twisted arrow morphism with domain arrow `domArr` and codomain arrow
`codArr`, we compose:
1. The fiber morphism from `hom codArr` (changing which slice we're over)
2. The presheaf functoriality via `domArr` (moving within the target slice)
-/
def sliceGrothendieckFibMap (fib : SliceGrothendieckFib C)
    (hom : SliceGrothendieckHom C fib)
    {tw tw' : TwistedArrow' C} (m : tw ⟶ tw') :
    sliceGrothendieckFibObj C fib tw → sliceGrothendieckFibObj C fib tw' := by
  intro a
  let domArr := twDomArr' m
  let codArr := twCodArr' m
  let y := twCod' tw
  let y' := twCod' tw'
  let f := twArr' tw
  let f' := twArr' tw'
  have hcommTw : domArr ≫ f ≫ codArr = f' := twHomComm' m
  let step1 : (fib y').obj ((Over.map codArr).obj (Over.mk f)) :=
    (hom codArr).app (Over.mk f) a
  have hOverMap : (Over.map codArr).obj (Over.mk f) = Over.mk (f ≫ codArr) := rfl
  let step1' : (fib y').obj (Over.mk (f ≫ codArr)) := hOverMap ▸ step1
  have hcommOver : domArr ≫ (f ≫ codArr) = f' := hcommTw
  let overMor : Over.mk f' ⟶ Over.mk (f ≫ codArr) :=
    overHomFromDomArr C domArr hcommOver
  exact (fib y').map overMor step1'

/-!
### Reconstructing TwArrCopresheaf from Section Data

The object and morphism maps `sliceGrothendieckFibObj` and `sliceGrothendieckFibMap`
can be assembled into a functor `TwistedArrow' C ⥤ Type v`. The functor laws
(`map_id`, `map_comp`) follow from the section data coherence conditions
(`hom_id`, `hom_comp`).

The direct proof of these laws involves managing multiple `eqToHom` transports
arising from:
1. The identity/composition coherence in section data
2. The composition of natural transformation application with presheaf functoriality

An alternative approach is to use the existing `sliceEquivCopresheaf` equivalence,
which provides the functor structure through the equivalence
`Over hom' ≌ TwArrCopresheaf C`.

The relationship between these approaches is:
- Forward: `F : TwArrCopresheaf C` → `F.sliceSectionData C : SectionDataContra`
- Backward: Using `sliceEquivCopresheaf` to reconstruct `F` from section data
- The round-trip preserves the functor up to natural isomorphism
-/

end TwArrCopresheaf

section TwArrPresheaf

/--
Presheaves on the twisted arrow category: covariant functors from
`OpTwistedArrow' C` to `Type v`.

Since `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrow' C`, i.e., presheaves.
-/
def TwArrPresheaf := OpTwistedArrow' C ⥤ Type v

instance : Category (TwArrPresheaf C) := by
  unfold TwArrPresheaf
  infer_instance

/--
Object map for the slice copresheaf induced by a `TwArrPresheaf`.

Given `F : TwArrPresheaf C`, the object map takes an opposite-twisted arrow
`(x, y, f)` to a type. In curried form: `y` first (covariant), then `x`
(contravariant), then `f : x ⟶ y`. This lets us view `f` as a slice over `y`.

- `y : C` (contravariant in the functor category)
- `x : C` (covariant in the functor category)
- `f : x ⟶ y`
- Returns: `F.obj (opTwObjMk' f) : Type v`
-/
def TwArrPresheaf.sliceObj (F : TwArrPresheaf C) (y : C) (x : C)
    (f : x ⟶ y) : Type v :=
  F.obj (opTwObjMk' f)

/--
Covariant morphism map for the slice copresheaf induced by a `TwArrPresheaf`.

Given a morphism in `Over y` from `(f : x ⟶ y)` to `(f' : x' ⟶ y)`, i.e.,
`g : x ⟶ x'` with `g ≫ f' = f`, we get an opposite-twisted-arrow morphism from
`opTwObjMk' f` to `opTwObjMk' f'` with `domArr = g` and `codArr = 𝟙 y`.

This induces a map `F.sliceObj C y x f → F.sliceObj C y x' f'` via `F.map`.
-/
def TwArrPresheaf.sliceMap (F : TwArrPresheaf C) {y : C} {x x' : C}
    {f : x ⟶ y} {f' : x' ⟶ y} (g : x ⟶ x') (comm : g ≫ f' = f) :
    F.sliceObj C y x f → F.sliceObj C y x' f' :=
  F.map (opTwHomMk' g (𝟙 y) (by
    simp only [opTwObjMk'_arr]
    rw [show f' ≫ 𝟙 y = f' from Category.comp_id f', comm]))

/--
For a fixed `y : C`, a `TwArrPresheaf` induces a copresheaf on `Over y`, i.e.,
a functor from `Over y` to `Type v`. Objects `(f : x ⟶ y)` in `Over y` map to
`F.sliceObj C y x f`, and morphisms induce maps via `sliceMap`.
-/
def TwArrPresheaf.sliceCopresheaf (F : TwArrPresheaf C) (y : C) :
    Over y ⥤ Type v where
  obj f := F.sliceObj C y f.left f.hom
  map {f f'} g := F.sliceMap C (Over.left g) (Over.w g)
  map_id f := by apply F.map_id
  map_comp {f f' f''} g g' := by
    unfold sliceMap
    rw [← F.map_comp]
    congr 1
    apply opTwHom'_ext
    · simp only [opTwDomArr']
      rfl
    · simp only
        [opTwCodArr', opTwObjMk', opTwHomMk', CategoryOfElements.homMk,
         CategoryStruct.comp, Category.toCategoryStruct,
         instCategoryOpTwistedArrow', OpProdInst']
      unfold id CategoryStruct.id
      simp only [CategoryOp'.eq_1, CategoryOp'Inst.eq_1, CategoryOpQuivInst.eq_1,
        prod_Hom, OpTwistedArrow'.eq_1, CategoryOfElementsContra'.comp_val]
      unfold OpProdInst'
      simp only [CategoryOp'.eq_1, CategoryOp'Inst.eq_1, CategoryOpQuivInst.eq_1]
      unfold
        CategoryStruct.id CategoryStruct.comp Category.toCategoryStruct
        opProd' uniformProd
      simp only [CategoryOp'.eq_1]
      exact (Category.id_comp (𝟙 y)).symm

/--
For a `TwArrPresheaf F` and object `y : C`, this gives the object in the
Grothendieck construction over `overCopresheafFunctor` with base `y` and
fiber `F.sliceCopresheaf C y`.
-/
def TwArrPresheaf.sliceGrothendieckObj (F : TwArrPresheaf C) (y : C) :
    Grothendieck (overCopresheafFunctor C) where
  base := y
  fiber := (F.sliceCopresheaf C y : OverCopresheaf C y)

/--
Given a morphism `h : y ⟶ y'` in `C`, we get a natural transformation from
`(precompOverMap C h).obj (F.sliceCopresheaf y')` to `F.sliceCopresheaf y`.

For an object `(f : x ⟶ y)` in `Over y`, the component maps
`F.obj (opTwObjMk' (f.hom ≫ h))` to `F.obj (opTwObjMk' f.hom)` via the opposite
twisted arrow morphism with `domArr = 𝟙 x` and `codArr = h`.
-/
def TwArrPresheaf.sliceNatTrans (F : TwArrPresheaf C) {y y' : C}
    (h : y ⟶ y') :
    (precompOverMap C h).obj (F.sliceCopresheaf C y') ⟶
    F.sliceCopresheaf C y where
  app f := F.map (opTwHomMk'
    (x := opTwObjMk' (f.hom ≫ h))
    (y := opTwObjMk' f.hom)
    (𝟙 f.left) h (by simp only [opTwObjMk'_arr]; exact Category.id_comp _))
  naturality {f f'} g := by
    simp only [sliceCopresheaf, precompOverMap, sliceMap]
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    apply opTwHom'_ext
    · simp only
        [opTwDomArr', opTwHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryOpTwistedArrow', OpProdInst']
      change (h ≫ 𝟙 y', g.left ≫ 𝟙 f'.left).2 = (𝟙 y ≫ h, 𝟙 f.left ≫ g.left).2
      simp only [Category.id_comp, Category.comp_id]
    · simp only
        [opTwCodArr', opTwHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryOpTwistedArrow', OpProdInst']
      change (h ≫ 𝟙 y', g.left ≫ 𝟙 f'.left).1 = (𝟙 y ≫ h, 𝟙 f.left ≫ g.left).1
      simp only [Category.id_comp, Category.comp_id]

/--
Given a morphism `h : y ⟶ y'` in `Cᵒᵖ'` (which is `h : y' ⟶ y` in C), we get
a morphism in `Grothendieck (overCopresheafFunctor C)` from
`F.sliceGrothendieckObj y` to `F.sliceGrothendieckObj y'`.

The base morphism is `h`, and the fiber morphism is `F.sliceNatTrans h` (viewing
`h` as a C-morphism `y' ⟶ y`).
-/
def TwArrPresheaf.sliceGrothendieckHom (F : TwArrPresheaf C) {y y' : Cᵒᵖ'}
    (h : @Quiver.Hom Cᵒᵖ' _ y y') :
    F.sliceGrothendieckObj C y ⟶ F.sliceGrothendieckObj C y' where
  base := h
  fiber := F.sliceNatTrans C (h : @Quiver.Hom C _ y' y)

/--
The fiber function for the slice Grothendieck functor.
-/
def TwArrPresheaf.sliceGrothendieckFib (F : TwArrPresheaf C) :
    Grothendieck.FunctorToFib (overCopresheafFunctor C) (𝟭 Cᵒᵖ') :=
  fun y => F.sliceCopresheaf C y

/--
The morphism function for the slice Grothendieck functor.
For `h : y ⟶ y'` in `Cᵒᵖ'`, produces the fiber morphism.
-/
def TwArrPresheaf.sliceGrothendieckHomFiber (F : TwArrPresheaf C) :
    Grothendieck.FunctorToHom (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) :=
  fun h => F.sliceNatTrans C h

private lemma TwArrPresheaf.opTwObjMk'_comp_id {y : C} (f : Over y) :
    opTwObjMk' (f.hom ≫ 𝟙 y) = opTwObjMk' f.hom := by
  unfold opTwObjMk'
  congr 1
  exact Category.comp_id f.hom

private lemma opTwHomMk'_id_id_eq_eqToHom {dom cod : C} (arr arr' : dom ⟶ cod)
    (h : arr = arr') (comm : 𝟙 dom ≫ arr' ≫ 𝟙 cod = arr) :
    opTwHomMk'
      (x := opTwObjMk' arr)
      (y := opTwObjMk' arr')
      (𝟙 dom) (𝟙 cod) comm =
    eqToHom (congrArg opTwObjMk' h) := by
  subst h
  simp only [eqToHom_refl']
  apply opTwHom'_ext
  · simp only [opTwHomMk'_domArr]
    rfl
  · simp only [opTwHomMk'_codArr]
    rfl

private lemma TwArrPresheaf.sliceNatTrans_id_app_is_id
    (F : TwArrPresheaf C) (y : C) (f : Over y) :
    (F.sliceNatTrans C (@CategoryStruct.id C _ y)).app f =
    eqToHom (congrArg F.obj (opTwObjMk'_comp_id C f)) := by
  simp only [sliceNatTrans]
  have harr : f.hom ≫ 𝟙 y = f.hom := Category.comp_id f.hom
  have hmor : opTwHomMk'
      (x := opTwObjMk' (f.hom ≫ 𝟙 y))
      (y := opTwObjMk' f.hom)
      (𝟙 f.left) (𝟙 y) (sliceNatTrans._proof_1 C (𝟙 y) f) =
      eqToHom (opTwObjMk'_comp_id C f) := by
    have h := opTwHomMk'_id_id_eq_eqToHom C (f.hom ≫ 𝟙 y) f.hom harr
        (sliceNatTrans._proof_1 C (𝟙 y) f)
    convert h using 1
  rw [hmor, eqToHom_map]

/--
Identity coherence for sliceGrothendieckHomFiber.
-/
lemma TwArrPresheaf.sliceGrothendieck_hom_id (F : TwArrPresheaf C) :
    Grothendieck.FunctorToHomId (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro y
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, Functor.id_obj, Functor.id_map]
  have h := sliceNatTrans_id_app_is_id C F y f
  simp only [sliceNatTrans] at h ⊢
  rw [eqToHom_app]
  refine Eq.trans h ?_
  congr 1

/--
Composition coherence for sliceGrothendieckHomFiber.
-/
lemma TwArrPresheaf.sliceGrothendieck_hom_comp (F : TwArrPresheaf C) :
    Grothendieck.FunctorToHomComp (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro y y' y'' g h
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, sliceNatTrans, Functor.id_obj, Functor.id_map]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [overCopresheafFunctor, copresheafConstruction,
    Functor.op', Functor.comp_map,
    Functor.whiskeringLeft, Over.mapFunctor, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.toCatHom_toFunctor]
  rw [eqToHom_app]
  funext x
  simp only [types_comp_apply]
  rw [← types_comp_apply (F.map _) (F.map _)]
  rw [← F.map_comp]
  have hassoc : f.hom ≫ h ≫ g = (f.hom ≫ h) ≫ g := (Category.assoc _ _ _).symm
  have hsrc_type : opTwObjMk' (f.hom ≫ h ≫ g) = opTwObjMk' ((f.hom ≫ h) ≫ g) :=
    congrArg opTwObjMk' hassoc
  conv_rhs => rw [← types_comp_apply (eqToHom _) (F.map _)]
  conv_rhs => rw [← functor_map_eqToHom (p := hsrc_type), ← F.map_comp]
  refine congrFun (congrArg F.map ?_) x
  apply CategoryOfElementsContra'.hom_ext
  simp only [opTwHomMk', CategoryOfElements.homMk]
  rw [CategoryOfElementsContra'.comp_val, CategoryOfElementsContra'.comp_val]
  rw [CategoryOfElementsContra'.eqToHom_val]
  have hfst_rfl : (congrArg Sigma.fst hsrc_type).symm = rfl := by
    apply proof_irrel
  rw [hfst_rfl, eqToHom_refl]
  simp only [Category.comp_id]
  unfold functorOp'Obj at *
  simp only [Over.map_obj_left]
  apply Prod.ext
  · rfl
  · simp only [CategoryOp'Inst, prod_comp]
    simp [opTwObjMk', CategoryStruct.id, CategoryStruct.comp]

/--
Bundled data for constructing a functor from `Cᵒᵖ'` into the Grothendieck
construction over `overCopresheafFunctor`.
-/
def TwArrPresheaf.sliceGrothendieckData (F : TwArrPresheaf C) :
    Grothendieck.FunctorToData (D := Cᵒᵖ') (overCopresheafFunctor C) where
  baseFunc := 𝟭 Cᵒᵖ'
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
Alternative section data representation using `SectionData`.

Since `sliceGrothendieckData` has `baseFunc = 𝟭 Cᵒᵖ'`, the data can equivalently
be viewed as section data for `overCopresheafFunctor C`.
-/
def TwArrPresheaf.sliceSectionData (F : TwArrPresheaf C) :
    Grothendieck.SectionData (overCopresheafFunctor C) where
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
The slice construction for a `TwArrPresheaf` assembles into a functor from
`Cᵒᵖ'` to the Grothendieck construction over `overCopresheafFunctor`.

For each object `y : Cᵒᵖ'`, we get `(y, F.sliceCopresheaf y)` in the
Grothendieck construction. For each morphism `h : y ⟶ y'` in `Cᵒᵖ'` (which is
`h : y' ⟶ y` in C), we get a Grothendieck morphism from
`(y, F.sliceCopresheaf y)` to `(y', F.sliceCopresheaf y')`.

This functor is a section of the forgetful functor:
`sliceGrothendieckFunctor ⋙ Grothendieck.forget = 𝟭 Cᵒᵖ'`.
-/
def TwArrPresheaf.sliceGrothendieckFunctor (F : TwArrPresheaf C) :
    Cᵒᵖ' ⥤ Grothendieck (overCopresheafFunctor C) :=
  (F.sliceSectionData C).toFunctor

/-! ### Reverse Construction: From Grothendieck Data to TwArrPresheaf

Given data for a functor into the (covariant) Grothendieck construction over
`overCopresheafFunctor C` with identity base functor on `Cᵒᵖ'`, we construct an
opposite-twisted-arrow presheaf.
-/

/--
The fiber type for a slice Grothendieck section: assigns to each `y : C` a
copresheaf on `Over y`.
-/
abbrev SliceGrothendieckFibPresheaf :=
  Grothendieck.FunctorToFib (overCopresheafFunctor C) (𝟭 Cᵒᵖ')

/--
The morphism type for a slice Grothendieck section: assigns to each morphism
`h : y ⟶ y'` in `Cᵒᵖ'` (i.e., `h : y' ⟶ y` in C) a natural transformation
between the fibers.
-/
abbrev SliceGrothendieckHomPresheaf (fib : SliceGrothendieckFibPresheaf C) :=
  Grothendieck.FunctorToHom (overCopresheafFunctor C) (𝟭 Cᵒᵖ') fib

/--
Object map for the opposite-twisted-arrow presheaf induced by slice
Grothendieck data. Given an opposite twisted arrow `(f : x ⟶ y)`, we evaluate
the fiber copresheaf at `y` on the over-object `Over.mk f`.

Note: `fib` takes objects of `Cᵒᵖ'` which have the same carrier as `C`, so
`fib (opTwCod' tw)` works by treating `opTwCod' tw : C` as an object of `Cᵒᵖ'`.
-/
def sliceGrothendieckFibObjPresheaf (fib : SliceGrothendieckFibPresheaf C)
    (tw : OpTwistedArrow' C) : Type v :=
  let y : C := opTwCod' tw
  (fib y).obj (Over.mk (opTwArr' tw))

/--
The Over morphism induced by a domain arrow in an opposite twisted arrow
morphism. Given `domArr : x ⟶ x'` and arrows `f : x ⟶ y`, `f' : x' ⟶ y` with
`domArr ≫ f' = f`, we get a morphism in `Over y` from `Over.mk f` to
`Over.mk f'`.
-/
def overHomFromDomArrPresheaf {y : C} {x x' : C} {f : x ⟶ y} {f' : x' ⟶ y}
    (domArr : x ⟶ x') (hcomm : domArr ≫ f' = f) :
    Over.mk f ⟶ Over.mk f' :=
  Over.homMk domArr hcomm

/--
Morphism map for the opposite-twisted-arrow presheaf induced by slice
Grothendieck data.

Given an opposite twisted arrow morphism `m : tw ⟶ tw'` with:
- `domArr : opTwDom' tw ⟶ opTwDom' tw'` (domain arrow, going forward)
- `codArr : opTwCod' tw' ⟶ opTwCod' tw` (codomain arrow, going backward in C,
  which is forward in Cᵒᵖ' from `opTwCod' tw` to `opTwCod' tw'`)

We compose:
1. The fiber morphism from `hom codArr` (changing which slice we're over)
2. The copresheaf functoriality via `domArr` (moving within the target slice)
-/
def sliceGrothendieckFibMapPresheaf (fib : SliceGrothendieckFibPresheaf C)
    (hom : SliceGrothendieckHomPresheaf C fib)
    {tw tw' : OpTwistedArrow' C} (m : tw ⟶ tw') :
    sliceGrothendieckFibObjPresheaf C fib tw →
      sliceGrothendieckFibObjPresheaf C fib tw' := by
  intro a
  let domArr := opTwDomArr' m
  let codArrC : (opTwCod' tw' : C) ⟶ (opTwCod' tw : C) := opTwCodArr' m
  let y : C := opTwCod' tw
  let y' : C := opTwCod' tw'
  let f := opTwArr' tw
  let f' := opTwArr' tw'
  have hcommTw : domArr ≫ f' ≫ codArrC = f := opTwHomComm' m
  have hcommOver : domArr ≫ (f' ≫ codArrC) = f := hcommTw
  let overMor : Over.mk f ⟶ Over.mk (f' ≫ codArrC) :=
    overHomFromDomArrPresheaf C domArr hcommOver
  let step1 : (fib y).obj (Over.mk (f' ≫ codArrC)) := (fib y).map overMor a
  have hOverMap : (Over.map codArrC).obj (Over.mk f') = Over.mk (f' ≫ codArrC) := rfl
  let step1' : (fib y).obj ((Over.map codArrC).obj (Over.mk f')) := hOverMap ▸ step1
  exact (hom codArrC).app (Over.mk f') step1'

end TwArrPresheaf

section TwArrOpCopresheaf

/--
Copresheaves on the opposite-variant twisted arrow category: covariant functors
from `TwistedArrowOp' C` to `Type v`.
-/
def TwArrOpCopresheaf := TwistedArrowOp' C ⥤ Type v

instance : Category (TwArrOpCopresheaf C) := by
  unfold TwArrOpCopresheaf
  infer_instance

/--
The slice category over `homOp'` is equivalent to the category of copresheaves
on the opposite-variant twisted arrow category.
-/
def sliceEquivTwArrOpCopresheaf : Over (homOp' (C := C)) ≌ TwArrOpCopresheaf C :=
  sliceEquivCopresheaf (homOp' (C := C))

/--
Object map for the slice presheaf induced by a `TwArrOpCopresheaf`.

Given `F : TwArrOpCopresheaf C`, the object map takes a twisted arrow of `Cᵒᵖ'`,
i.e., `(x, y, f : y ⟶ x)`, to a type. In curried form: `x` first (covariant),
then `y` (contravariant), then `f : y ⟶ x`. This lets us view `f` as a slice
over `x`.

- `x : C` (covariant in the functor category)
- `y : C` (contravariant in the functor category)
- `f : y ⟶ x`
- Returns: `F.obj (twOpObjMk' f) : Type v`
-/
def TwArrOpCopresheaf.opSliceObj (F : TwArrOpCopresheaf C) (x : C) (y : C)
    (f : y ⟶ x) : Type v :=
  F.obj (twOpObjMk' f)

/--
Contravariant morphism map for the slice presheaf induced by a
`TwArrOpCopresheaf`.

Given a morphism in `Over x` from `(f' : y' ⟶ x)` to `(f : y ⟶ x)`, i.e.,
`g : y' ⟶ y` with `g ≫ f = f'`, we get a twisted-arrow-op morphism from
`twOpObjMk' f` to `twOpObjMk' f'` with `domArr = 𝟙 x` and `codArr = g`.

This induces a map `F.opSliceObj C x y f → F.opSliceObj C x y' f'` via `F.map`.
-/
def TwArrOpCopresheaf.sliceContramap (F : TwArrOpCopresheaf C) {x : C} {y y' : C}
    {f : y ⟶ x} {f' : y' ⟶ x} (g : y' ⟶ y) (comm : g ≫ f = f') :
    F.opSliceObj C x y f → F.opSliceObj C x y' f' :=
  F.map (twOpHomMk' (𝟙 x) g (by
    simp only [twOpObjMk'_arr]
    rw [show f ≫ 𝟙 x = f from Category.comp_id f, comm]))

/--
For a fixed `x : C`, a `TwArrOpCopresheaf` induces a presheaf on `Over x`, i.e.,
a functor from `(Over x)ᵒᵖ'` to `Type v`. Objects `(f : y ⟶ x)` in `Over x` map
to `F.opSliceObj C x y f`, and morphisms in the opposite direction induce maps
via `sliceContramap`.
-/
def TwArrOpCopresheaf.slicePresheaf (F : TwArrOpCopresheaf C) (x : C) :
    (Over x)ᵒᵖ' ⥤ Type v where
  obj f := F.opSliceObj C x f.left f.hom
  map {f f'} g := F.sliceContramap C (Over.leftOp' g) (Over.w g)
  map_id f := by apply F.map_id
  map_comp {f f' f''} g g' := by
    unfold sliceContramap
    have hcomp : (g ≫ g').left = g'.left ≫ g.left := op_comp_eq _ _
    rw [← F.map_comp]
    congr 1
    apply twOpHom'_ext
    · simp only
        [twOpDomArr', twOpHomMk', CategoryOfElements.homMk,
         CategoryStruct.comp, Category.toCategoryStruct,
         instCategoryTwistedArrowOp']
      unfold id
      simp only [categoryOfElements]
      simp only [prod_comp]
      simp
    · simp only [hcomp, twOpCodArr']
      rfl

/--
For a `TwArrOpCopresheaf F` and object `x : C`, this gives the object in the
contravariant Grothendieck construction over `overOpCopresheafFunctor` with
base `x` and fiber `F.slicePresheaf C x`.
-/
def TwArrOpCopresheaf.sliceGrothendieckObj (F : TwArrOpCopresheaf C) (x : C) :
    GrothendieckContra' (overOpCopresheafFunctor C) where
  base := x
  fiber := (F.slicePresheaf C x : OverOpPresheaf C x)

/--
Given a morphism `h : x ⟶ x'` in `C`, we get a natural transformation from
`F.slicePresheaf x` to `(overOpMapFunctor C).map h ⋙ F.slicePresheaf x'`.

For an object `(f : y ⟶ x)` in `(Over x)ᵒᵖ'`, the component maps
`F.obj (twOpObjMk' f.hom)` to `F.obj (twOpObjMk' (f.hom ≫ h))` via the twisted
arrow op morphism with `domArr = h` and `codArr = 𝟙 y`.
-/
def TwArrOpCopresheaf.sliceNatTrans (F : TwArrOpCopresheaf C) {x x' : C}
    (h : x ⟶ x') :
    F.slicePresheaf C x ⟶
    (precompOverOpMap C h).obj (F.slicePresheaf C x') where
  app f := F.map (twOpHomMk'
    (x := twOpObjMk' f.hom)
    (y := twOpObjMk' (f.hom ≫ h))
    h (𝟙 f.left) (by simp only [twOpObjMk'_arr]; exact Category.id_comp _))
  naturality {f f'} g := by
    simp only [slicePresheaf, precompOverOpMap, Functor.whiskeringLeft,
      Functor.comp_obj, overOpMapFunctor,
      Cat.postCompOpFunctor', Functor.whiskeringRight, Over.mapFunctor,
      Functor.comp_map, Cat.opFunctor', sliceContramap]
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    apply twOpHom'_ext
    · simp only
        [twOpDomArr', twOpHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryTwistedArrowOp']
      unfold id
      simp only [categoryOfElements]
      simp only [prod_comp]
      simp
    · simp only
        [twOpCodArr', twOpHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryTwistedArrowOp']
      unfold id
      simp only [categoryOfElements]
      simp only [prod_comp]
      simp

/--
Given a morphism `h : x ⟶ x'` in `C`, we get a morphism in
`GrothendieckContra' (overOpCopresheafFunctor C)` from
`F.sliceGrothendieckObj x` to `F.sliceGrothendieckObj x'`.

The base morphism is `h`, and the fiber morphism is `F.sliceNatTrans h`.
-/
def TwArrOpCopresheaf.sliceGrothendieckHom (F : TwArrOpCopresheaf C) {x x' : C}
    (h : x ⟶ x') :
    F.sliceGrothendieckObj C x ⟶ F.sliceGrothendieckObj C x' where
  base := h
  fiber := F.sliceNatTrans C h

/--
The fiber function for the slice Grothendieck functor (contravariant case).
-/
def TwArrOpCopresheaf.sliceGrothendieckFib (F : TwArrOpCopresheaf C) :
    GrothendieckContra'.FunctorToFib (F' := overOpCopresheafFunctor C) (𝟭 C) :=
  fun x => F.slicePresheaf C x

/--
The morphism function for the slice Grothendieck functor (contravariant case).
For `h : x ⟶ x'` in `C`, produces the fiber morphism.
-/
def TwArrOpCopresheaf.sliceGrothendieckHomFiber (F : TwArrOpCopresheaf C) :
    GrothendieckContra'.FunctorToHom (𝟭 C) (F.sliceGrothendieckFib C) :=
  fun h => F.sliceNatTrans C h

private lemma TwArrOpCopresheaf.twOpObjMk'_id_comp {x : C} (f : Over x) :
    twOpObjMk' f.hom = twOpObjMk' (f.hom ≫ 𝟙 x) := by
  unfold twOpObjMk'
  congr 1
  exact (Category.comp_id f.hom).symm

private lemma twOpHomMk'_id_id_eq_eqToHom' {dom cod : C} (arr arr' : cod ⟶ dom)
    (h : arr = arr') (comm : 𝟙 cod ≫ arr ≫ 𝟙 dom = arr') :
    twOpHomMk'
      (x := twOpObjMk' arr)
      (y := twOpObjMk' arr')
      (𝟙 dom) (𝟙 cod) (by simp only [twOpObjMk'_arr]; exact comm) =
    eqToHom (congrArg twOpObjMk' h) := by
  subst h
  simp only [eqToHom_refl']
  apply twOpHom'_ext
  · simp only [twOpHomMk'_domArr]
    rfl
  · simp only [twOpHomMk'_codArr]
    rfl

private lemma TwArrOpCopresheaf.sliceNatTrans_id_app_is_id
    (F : TwArrOpCopresheaf C) (x : C) (f : Over x) :
    (F.sliceNatTrans C (@CategoryStruct.id C _ x)).app f =
    eqToHom (congrArg F.obj (twOpObjMk'_id_comp C f)) := by
  simp only [sliceNatTrans]
  have harr : f.hom = f.hom ≫ 𝟙 x := (Category.comp_id f.hom).symm
  have hcomm : 𝟙 f.left ≫ f.hom ≫ 𝟙 x = f.hom ≫ 𝟙 x := Category.id_comp _
  have hmor : twOpHomMk'
      (x := twOpObjMk' f.hom)
      (y := twOpObjMk' (f.hom ≫ 𝟙 x))
      (𝟙 x) (𝟙 f.left) (by simp only [twOpObjMk'_arr]; exact Category.id_comp _) =
      eqToHom (twOpObjMk'_id_comp C f) := by
    have h := twOpHomMk'_id_id_eq_eqToHom' C f.hom (f.hom ≫ 𝟙 x) harr hcomm
    exact h
  rw [hmor, eqToHom_map]

/--
Identity coherence for sliceGrothendieckHomFiber (contravariant case).
-/
lemma TwArrOpCopresheaf.sliceGrothendieck_hom_id (F : TwArrOpCopresheaf C) :
    GrothendieckContra'.FunctorToHomId (overOpCopresheafFunctor C) (𝟭 C)
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro x
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, Functor.id_obj, Functor.id_map]
  have h := sliceNatTrans_id_app_is_id C F x f
  simp only [sliceNatTrans] at h ⊢
  rw [eqToHom_app]
  refine Eq.trans h ?_
  congr 1

/--
Composition coherence for sliceGrothendieckHomFiber (contravariant case).
-/
lemma TwArrOpCopresheaf.sliceGrothendieck_hom_comp (F : TwArrOpCopresheaf C) :
    GrothendieckContra'.FunctorToHomComp (overOpCopresheafFunctor C) (𝟭 C)
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro x x' x'' g h
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, Functor.id_obj, Functor.id_map]
  simp only [sliceNatTrans]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [overOpCopresheafFunctor, copresheafConstruction,
    Functor.op', Functor.comp_map,
    Functor.whiskeringLeft, overOpMapFunctor, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.toCatHom_toFunctor]
  rw [eqToHom_app]
  funext a
  simp only [types_comp_apply]
  have hassoc : f.hom ≫ g ≫ h = (f.hom ≫ g) ≫ h := (Category.assoc _ _ _).symm
  have htgt_type : twOpObjMk' (f.hom ≫ g ≫ h) = twOpObjMk' ((f.hom ≫ g) ≫ h) :=
    congrArg twOpObjMk' hassoc
  conv_rhs =>
    rw [← types_comp_apply (F.map _) (F.map _)]
    rw [← types_comp_apply _ (eqToHom _)]
    rw [← functor_map_eqToHom (p := htgt_type.symm)]
    rw [← F.map_comp, ← F.map_comp]
  refine congrFun (congrArg F.map ?_) a
  apply CategoryOfElements.ext
  simp only [twOpHomMk', CategoryOfElements.homMk]
  rw [CategoryOfElements.comp_val, CategoryOfElements.comp_val]
  rw [CategoryOfElements.eqToHom_val]
  have hfst_rfl : congrArg Sigma.fst htgt_type = rfl := proof_irrel _ _
  rw [hfst_rfl, eqToHom_refl, prod_id]
  simp only [twOpObjMk', functorOp'Obj]
  have hleft_eq :
      (((Cat.postCompOpFunctor'.obj (Over.mapFunctor C)).map g).toFunctor.obj f).left =
        f.left := rfl
  apply Prod.ext
  · simp only [prod_comp, Category.comp_id]
  · simp only [CategoryOp'Inst, prod_comp]
    change 𝟙 f.left = 𝟙 f.left ≫ 𝟙 f.left ≫ 𝟙 f.left
    simp only [Category.comp_id]

/--
Bundled data for constructing a functor from `C` into the contravariant
Grothendieck construction over `overOpCopresheafFunctor` (for TwArrOpCopresheaf).
-/
def TwArrOpCopresheaf.sliceGrothendieckData (F : TwArrOpCopresheaf C) :
    GrothendieckContra'.FunctorToData (E := C) (overOpCopresheafFunctor C) where
  baseFunc := 𝟭 C
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
Alternative section data representation using `SectionDataContra`.

Since `sliceGrothendieckData` has `baseFunc = 𝟭 C`, the data can equivalently
be viewed as section data for `overOpCopresheafFunctor C`.
-/
def TwArrOpCopresheaf.sliceSectionData (F : TwArrOpCopresheaf C) :
    GrothendieckContra'.SectionDataContra (overOpCopresheafFunctor C) where
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
The slice construction for a `TwArrOpCopresheaf` assembles into a functor from
`C` to the contravariant Grothendieck construction over `overOpCopresheafFunctor`.

For each object `x : C`, we get `(x, F.slicePresheaf x)` in the Grothendieck
construction. For each morphism `h : x ⟶ x'` in `C`, we get a Grothendieck
morphism from `(x, F.slicePresheaf x)` to `(x', F.slicePresheaf x')`.

This functor is a section of the forgetful functor:
`sliceGrothendieckFunctor ⋙ GrothendieckContra'.forget = 𝟭 C`.
-/
def TwArrOpCopresheaf.sliceGrothendieckFunctor (F : TwArrOpCopresheaf C) :
    C ⥤ GrothendieckContra' (overOpCopresheafFunctor C) :=
  (F.sliceSectionData C).toFunctor

/-! ### Reverse Construction: From Grothendieck Data to TwArrOpCopresheaf

Given data for a functor into the contravariant Grothendieck construction over
`overOpCopresheafFunctor C` with identity base functor, we construct an
opposite-variant twisted-arrow copresheaf.
-/

/--
The fiber type for a slice Grothendieck section (TwArrOpCopresheaf variant):
assigns to each `x : C` a presheaf on `(Over x)ᵒᵖ'`.
-/
abbrev SliceGrothendieckFibOpCopresheaf :=
  GrothendieckContra'.FunctorToFib (F' := overOpCopresheafFunctor C) (𝟭 C)

/--
The morphism type for a slice Grothendieck section (TwArrOpCopresheaf variant):
assigns to each morphism `h : x ⟶ x'` a natural transformation between the
fibers.
-/
abbrev SliceGrothendieckHomOpCopresheaf
    (fib : SliceGrothendieckFibOpCopresheaf C) :=
  GrothendieckContra'.FunctorToHom (𝟭 C) fib

/--
Object map for the opposite-variant twisted-arrow copresheaf induced by slice
Grothendieck data. Given a twisted arrow of `Cᵒᵖ'` (i.e., `f : y ⟶ x`), we
evaluate the fiber presheaf at `x` on the over-object `Over.mk f`.
-/
def sliceGrothendieckFibObjOpCopresheaf
    (fib : SliceGrothendieckFibOpCopresheaf C) (tw : TwistedArrowOp' C) :
    Type v :=
  let x : C := twOpDom' tw
  (fib x).obj (Over.mk (twOpArr' tw))

/--
The Over morphism induced by a codomain arrow in an opposite-variant twisted
arrow morphism. Given `codArr : y' ⟶ y` and arrows `f : y ⟶ x`, `f' : y' ⟶ x`
with `codArr ≫ f = f'`, we get a morphism in `(Over x)ᵒᵖ'` from `Over.mk f`
to `Over.mk f'`.
-/
def overHomFromCodArrOpCopresheaf {x y y' : C} {f : y ⟶ x} {f' : y' ⟶ x}
    (codArr : y' ⟶ y) (hcomm : codArr ≫ f = f') :
    @Quiver.Hom (Over x)ᵒᵖ' _ (Over.mk f) (Over.mk f') :=
  Over.homMk codArr hcomm

/--
Morphism map for the opposite-variant twisted-arrow copresheaf induced by
slice Grothendieck data.

Given a twisted arrow op morphism `m : tw ⟶ tw'` with:
- `domArr : twOpDom' tw ⟶ twOpDom' tw'` (domain arrow, forward)
- `codArr : twOpCod' tw' ⟶ twOpCod' tw` (codomain arrow, backward)

We compose:
1. The fiber morphism from `hom domArr` (changing which slice we're over)
2. The presheaf functoriality via `codArr` (moving within the target slice,
   contravariantly)
-/
def sliceGrothendieckFibMapOpCopresheaf
    (fib : SliceGrothendieckFibOpCopresheaf C)
    (hom : SliceGrothendieckHomOpCopresheaf C fib)
    {tw tw' : TwistedArrowOp' C} (m : tw ⟶ tw') :
    sliceGrothendieckFibObjOpCopresheaf C fib tw →
      sliceGrothendieckFibObjOpCopresheaf C fib tw' := by
  intro a
  let domArr := twOpDomArr' m
  let codArr := twOpCodArr' m
  let x : C := twOpDom' tw
  let x' : C := twOpDom' tw'
  let f := twOpArr' tw
  let f' := twOpArr' tw'
  have hcommTw : codArr ≫ f ≫ domArr = f' := twOpHomComm' m
  let step1 : (fib x').obj ((Over.map domArr).obj (Over.mk f)) :=
    (hom domArr).app (Over.mk f) a
  have hOverMap : (Over.map domArr).obj (Over.mk f) = Over.mk (f ≫ domArr) := rfl
  let step1' : (fib x').obj (Over.mk (f ≫ domArr)) := hOverMap ▸ step1
  have hcommOver : codArr ≫ (f ≫ domArr) = f' := hcommTw
  let overMor : @Quiver.Hom (Over x')ᵒᵖ' _ (Over.mk (f ≫ domArr)) (Over.mk f') :=
    overHomFromCodArrOpCopresheaf C codArr hcommOver
  exact (fib x').map overMor step1'

end TwArrOpCopresheaf

section TwArrOpPresheaf

/--
Presheaves on the opposite-variant twisted arrow category: covariant functors
from `CoTwistedArrow' C` to `Type v`.

Since `CoTwistedArrow' C ≅ (TwistedArrowOp' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrowOp' C`, i.e., presheaves.
-/
def TwArrOpPresheaf := CoTwistedArrow' C ⥤ Type v

instance : Category (TwArrOpPresheaf C) := by
  unfold TwArrOpPresheaf
  infer_instance

/--
Object map for the slice copresheaf induced by a `TwArrOpPresheaf`.

Given `F : TwArrOpPresheaf C`, the object map takes a co-twisted arrow, i.e.,
`(x, y, f : y ⟶ x)`, to a type. In curried form: `x` first (contravariant),
then `y` (covariant), then `f : y ⟶ x`. This lets us view `f` as a slice
over `x`.

- `x : C` (contravariant in the functor category)
- `y : C` (covariant in the functor category)
- `f : y ⟶ x`
- Returns: `F.obj (coTwObjMk' f) : Type v`
-/
def TwArrOpPresheaf.sliceObj (F : TwArrOpPresheaf C) (x : C) (y : C)
    (f : y ⟶ x) : Type v :=
  F.obj (coTwObjMk' f)

/--
Covariant morphism map for the slice copresheaf induced by a `TwArrOpPresheaf`.

Given a morphism in `Over x` from `(f : y ⟶ x)` to `(f' : y' ⟶ x)`, i.e.,
`g : y ⟶ y'` with `g ≫ f' = f`, we get a co-twisted-arrow morphism from
`coTwObjMk' f` to `coTwObjMk' f'` with `domArr = 𝟙 x` and `codArr = g`.

This induces a map `F.sliceObj C x y f → F.sliceObj C x y' f'` via `F.map`.
-/
def TwArrOpPresheaf.sliceMap (F : TwArrOpPresheaf C) {x : C} {y y' : C}
    {f : y ⟶ x} {f' : y' ⟶ x} (g : y ⟶ y') (comm : g ≫ f' = f) :
    F.sliceObj C x y f → F.sliceObj C x y' f' :=
  F.map (coTwHomMk' (𝟙 x) g (by
    simp only [coTwObjMk'_arr]
    rw [show f' ≫ 𝟙 x = f' from Category.comp_id f', comm]))

/--
For a fixed `x : C`, a `TwArrOpPresheaf` induces a copresheaf on `Over x`, i.e.,
a functor from `Over x` to `Type v`. Objects `(f : y ⟶ x)` in `Over x` map to
`F.sliceObj C x y f`, and morphisms induce maps via `sliceMap`.
-/
def TwArrOpPresheaf.sliceCopresheaf (F : TwArrOpPresheaf C) (x : C) :
    Over x ⥤ Type v where
  obj f := F.sliceObj C x f.left f.hom
  map {f f'} g := F.sliceMap C (Over.left g) (Over.w g)
  map_id f := by apply F.map_id
  map_comp {f f' f''} g g' := by
    unfold sliceMap
    rw [← F.map_comp]
    congr 1
    apply coTwHom'_ext
    · simp only
        [coTwDomArr', coTwHomMk', CategoryOfElements.homMk,
         CategoryStruct.comp, Category.toCategoryStruct,
         CategoryOp'Inst, prod_comp]
      simp only [CategoryOp'.eq_1, CategoryOpQuivInst.eq_1, prod_Hom,
        CoTwistedArrow'.eq_1, CategoryOfElementsContra'.comp_val]
      exact (Category.id_comp (𝟙 x)).symm
    · simp only [coTwCodArr']
      rfl

/--
For a `TwArrOpPresheaf F` and object `x : C`, this gives the object in the
Grothendieck construction over `overCopresheafFunctor` with base `x` and
fiber `F.sliceCopresheaf C x`.
-/
def TwArrOpPresheaf.sliceGrothendieckObj (F : TwArrOpPresheaf C) (x : C) :
    Grothendieck (overCopresheafFunctor C) where
  base := x
  fiber := (F.sliceCopresheaf C x : OverCopresheaf C x)

/--
Given a morphism `h : x ⟶ x'` in `C`, we get a natural transformation from
`(precompOverMap h).obj (F.sliceCopresheaf x')` to `F.sliceCopresheaf x`.

For an object `(f : y ⟶ x)` in `Over x`, the component maps
`F.obj (coTwObjMk' (f ≫ h))` to `F.obj (coTwObjMk' f)` via the co-twisted
arrow morphism with `domArr = h` and `codArr = 𝟙 y`.
-/
def TwArrOpPresheaf.sliceNatTrans (F : TwArrOpPresheaf C) {x x' : C}
    (h : x ⟶ x') :
    (precompOverMap C h).obj (F.sliceCopresheaf C x') ⟶
    F.sliceCopresheaf C x where
  app f := F.map (coTwHomMk'
    (x := coTwObjMk' (f.hom ≫ h))
    (y := coTwObjMk' f.hom)
    h (𝟙 f.left) (by simp only [coTwObjMk'_arr]; exact Category.id_comp _))
  naturality {f f'} g := by
    simp only [sliceCopresheaf, precompOverMap, Functor.whiskeringLeft,
      Functor.comp_obj, Over.mapFunctor, Functor.comp_map, sliceMap]
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    apply coTwHom'_ext
    · simp only
        [coTwDomArr', coTwHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryCoTwistedArrow', CategoryOp'Inst]
      change (h ≫ 𝟙 x', g.left ≫ 𝟙 f'.left).1 = (𝟙 x ≫ h, 𝟙 f.left ≫ g.left).1
      simp only [Category.id_comp, Category.comp_id]
    · simp only
        [coTwCodArr', coTwHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryCoTwistedArrow', CategoryOp'Inst]
      change (h ≫ 𝟙 x', g.left ≫ 𝟙 f'.left).2 = (𝟙 x ≫ h, 𝟙 f.left ≫ g.left).2
      simp only [Category.id_comp, Category.comp_id]

/--
Given a morphism `h : x ⟶ x'` in `Cᵒᵖ'` (which is `h : x' ⟶ x` in C), we get
a morphism in `Grothendieck (overCopresheafFunctor C)` from
`F.sliceGrothendieckObj x` to `F.sliceGrothendieckObj x'`.

The base morphism is `h`, and the fiber morphism is `F.sliceNatTrans h` (viewing
`h` as a C-morphism `x' ⟶ x`).
-/
def TwArrOpPresheaf.sliceGrothendieckHom (F : TwArrOpPresheaf C) {x x' : Cᵒᵖ'}
    (h : @Quiver.Hom Cᵒᵖ' _ x x') :
    F.sliceGrothendieckObj C x ⟶ F.sliceGrothendieckObj C x' where
  base := h
  fiber := F.sliceNatTrans C (h : @Quiver.Hom C _ x' x)

/--
The fiber function for the slice Grothendieck functor.
-/
def TwArrOpPresheaf.sliceGrothendieckFib (F : TwArrOpPresheaf C) :
    Grothendieck.FunctorToFib (overCopresheafFunctor C) (𝟭 Cᵒᵖ') :=
  fun x => F.sliceCopresheaf C x

/--
The morphism function for the slice Grothendieck functor.
For `h : x ⟶ x'` in `Cᵒᵖ'`, produces the fiber morphism.
-/
def TwArrOpPresheaf.sliceGrothendieckHomFiber (F : TwArrOpPresheaf C) :
    Grothendieck.FunctorToHom (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) :=
  fun h => F.sliceNatTrans C h

private lemma TwArrOpPresheaf.coTwObjMk'_comp_id {x : C} (f : Over x) :
    coTwObjMk' (f.hom ≫ 𝟙 x) = coTwObjMk' f.hom := by
  unfold coTwObjMk'
  congr 1
  exact Category.comp_id f.hom

private lemma coTwHomMk'_id_id_eq_eqToHom {cod dom : C} (arr arr' : cod ⟶ dom)
    (h : arr = arr') (comm : 𝟙 cod ≫ arr' ≫ 𝟙 dom = arr) :
    coTwHomMk'
      (x := coTwObjMk' arr)
      (y := coTwObjMk' arr')
      (𝟙 dom) (𝟙 cod) (by simp only [coTwObjMk'_arr]; exact comm) =
    eqToHom (congrArg coTwObjMk' h) := by
  subst h
  simp only [eqToHom_refl']
  apply coTwHom'_ext
  · simp only [coTwHomMk'_domArr]
    rfl
  · simp only [coTwHomMk'_codArr]
    rfl

private lemma TwArrOpPresheaf.sliceNatTrans_id_app_is_id
    (F : TwArrOpPresheaf C) (x : C) (f : Over x) :
    (F.sliceNatTrans C (@CategoryStruct.id C _ x)).app f =
    eqToHom (congrArg F.obj (coTwObjMk'_comp_id C f)) := by
  simp only [sliceNatTrans]
  have harr : f.hom ≫ 𝟙 x = f.hom := Category.comp_id f.hom
  have hcomm : 𝟙 f.left ≫ f.hom ≫ 𝟙 x = f.hom ≫ 𝟙 x := Category.id_comp _
  have hmor : coTwHomMk'
      (x := coTwObjMk' (f.hom ≫ 𝟙 x))
      (y := coTwObjMk' f.hom)
      (𝟙 x) (𝟙 f.left) (by simp only [coTwObjMk'_arr]; exact Category.id_comp _) =
      eqToHom (coTwObjMk'_comp_id C f) := by
    have h := coTwHomMk'_id_id_eq_eqToHom C (f.hom ≫ 𝟙 x) f.hom harr hcomm
    exact h
  rw [hmor, eqToHom_map]

/--
Identity coherence for sliceGrothendieckHomFiber.
-/
lemma TwArrOpPresheaf.sliceGrothendieck_hom_id (F : TwArrOpPresheaf C) :
    Grothendieck.FunctorToHomId (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro x
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, Functor.id_obj, Functor.id_map]
  have h := sliceNatTrans_id_app_is_id C F x f
  simp only [sliceNatTrans] at h ⊢
  rw [eqToHom_app]
  refine Eq.trans h ?_
  congr 1

/--
Composition coherence for sliceGrothendieckHomFiber.
-/
lemma TwArrOpPresheaf.sliceGrothendieck_hom_comp (F : TwArrOpPresheaf C) :
    Grothendieck.FunctorToHomComp (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C) := by
  intro x x' x'' g h
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, sliceNatTrans, Functor.id_obj, Functor.id_map]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [overCopresheafFunctor, copresheafConstruction,
    Functor.op', Functor.comp_map,
    Functor.whiskeringLeft, Over.mapFunctor, Functor.comp_obj,
    Functor.toCatHom_toFunctor, Functor.whiskerLeft_app]
  rw [eqToHom_app]
  funext a
  simp only [types_comp_apply]
  rw [← types_comp_apply (F.map _) (F.map _)]
  rw [← F.map_comp]
  have hassoc : f.hom ≫ h ≫ g = (f.hom ≫ h) ≫ g := (Category.assoc _ _ _).symm
  have hsrc_type : coTwObjMk' (f.hom ≫ h ≫ g) = coTwObjMk' ((f.hom ≫ h) ≫ g) :=
    congrArg coTwObjMk' hassoc
  conv_rhs => rw [← types_comp_apply (eqToHom _) (F.map _)]
  conv_rhs => rw [← functor_map_eqToHom (p := hsrc_type), ← F.map_comp]
  refine congrFun (congrArg F.map ?_) a
  apply CategoryOfElementsContra'.hom_ext
  simp only [coTwHomMk', CategoryOfElements.homMk]
  rw [CategoryOfElementsContra'.comp_val, CategoryOfElementsContra'.comp_val]
  rw [CategoryOfElementsContra'.eqToHom_val]
  have hfst_rfl : (congrArg Sigma.fst hsrc_type).symm = rfl := by
    apply proof_irrel
  rw [hfst_rfl, eqToHom_refl]
  simp only [Category.comp_id]
  unfold functorOp'Obj at *
  simp only [Over.map_obj_left]
  apply Prod.ext
  · simp only [CategoryOp'Inst, prod_comp]
    exact (Category.id_comp _).symm
  · rfl

/--
Bundled data for constructing a functor from `Cᵒᵖ'` into the Grothendieck
construction over `overCopresheafFunctor`.
-/
def TwArrOpPresheaf.sliceGrothendieckData (F : TwArrOpPresheaf C) :
    Grothendieck.FunctorToData (D := Cᵒᵖ') (overCopresheafFunctor C) where
  baseFunc := 𝟭 Cᵒᵖ'
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
Alternative section data representation using `SectionData`.

Since `sliceGrothendieckData` has `baseFunc = 𝟭 Cᵒᵖ'`, the data can equivalently
be viewed as section data for `overCopresheafFunctor C`.
-/
def TwArrOpPresheaf.sliceSectionData (F : TwArrOpPresheaf C) :
    Grothendieck.SectionData (overCopresheafFunctor C) where
  fib := F.sliceGrothendieckFib C
  hom := fun h => F.sliceGrothendieckHomFiber C h
  hom_id := F.sliceGrothendieck_hom_id C
  hom_comp := fun g h => F.sliceGrothendieck_hom_comp C g h

/--
The slice construction for a `TwArrOpPresheaf` assembles into a functor from
`Cᵒᵖ'` to the Grothendieck construction over `overCopresheafFunctor`.

For each object `x : Cᵒᵖ'`, we get `(x, F.sliceCopresheaf x)` in the
Grothendieck construction. For each morphism `h : x ⟶ x'` in `Cᵒᵖ'` (which is
`h : x' ⟶ x` in C), we get a Grothendieck morphism from
`(x, F.sliceCopresheaf x)` to `(x', F.sliceCopresheaf x')`.

This functor is a section of the forgetful functor:
`sliceGrothendieckFunctor ⋙ Grothendieck.forget = 𝟭 Cᵒᵖ'`.
-/
def TwArrOpPresheaf.sliceGrothendieckFunctor (F : TwArrOpPresheaf C) :
    Cᵒᵖ' ⥤ Grothendieck (overCopresheafFunctor C) :=
  (F.sliceSectionData C).toFunctor

/--
Fiber data for the slice Grothendieck construction over `overCopresheafFunctor`.
This assigns to each `x : Cᵒᵖ'` an `OverCopresheaf C x = (Over x ⥤ Type v)`.
-/
abbrev SliceGrothendieckFibOpPresheaf :=
  Grothendieck.FunctorToFib (overCopresheafFunctor C) (𝟭 Cᵒᵖ')

/--
Morphism data for the slice Grothendieck construction.
For each `h : x ⟶ x'` in `Cᵒᵖ'` (which is `h : x' ⟶ x` in C), provides a
natural transformation `(fib x').obj ∘ Over.map h ⟹ (fib x).obj`.
-/
abbrev SliceGrothendieckHomOpPresheaf (fib : SliceGrothendieckFibOpPresheaf C) :=
  Grothendieck.FunctorToHom (overCopresheafFunctor C) (𝟭 Cᵒᵖ') fib

/--
Object map for the co-twisted-arrow presheaf induced by slice Grothendieck data.

For a co-twisted arrow `tw = (cod, dom, f : cod ⟶ dom)`, the object is
`(fib dom).obj (Over.mk f)` where `f : cod ⟶ dom` is viewed as an object
of `Over dom`.
-/
def sliceGrothendieckFibObjOpPresheaf (fib : SliceGrothendieckFibOpPresheaf C)
    (tw : CoTwistedArrow' C) : Type v :=
  let x : C := coTwDom' tw
  (fib x).obj (Over.mk (coTwArr' tw))

/--
Helper for constructing Over morphisms from the codomain arrow component.
Given `codArr : cod ⟶ cod'` and commutativity `codArr ≫ arr' = arr ≫ domArr⁻¹`,
we can construct an Over morphism from `Over.mk arr` to `Over.mk (codArr ≫ arr')`
over `dom`.
-/
def overHomFromCodArrOpPresheaf {cod cod' dom : C}
    (arr : cod ⟶ dom) (arr' : cod' ⟶ dom)
    (codArr : cod ⟶ cod') (comm : codArr ≫ arr' = arr) :
    Over.mk arr ⟶ Over.mk arr' :=
  Over.homMk codArr (by
    simp only [Over.mk_left, Over.mk_hom]
    exact comm)

/--
Morphism map for the co-twisted-arrow presheaf induced by slice Grothendieck
data.

For a morphism `m : tw ⟶ tw'` with `domArr : dom' ⟶ dom` and
`codArr : cod ⟶ cod'` satisfying `codArr ≫ arr' ≫ domArr = arr`:

1. Apply `(fib dom).map` with the Over morphism from `codArr`
2. Apply `(hom domArr).app` to transport along the base morphism

Maps from `(fib dom).obj (Over.mk arr)` to `(fib dom').obj (Over.mk arr')`.
-/
def sliceGrothendieckFibMapOpPresheaf (fib : SliceGrothendieckFibOpPresheaf C)
    (hom : SliceGrothendieckHomOpPresheaf C fib)
    {tw tw' : CoTwistedArrow' C} (m : tw ⟶ tw') :
    sliceGrothendieckFibObjOpPresheaf C fib tw →
      sliceGrothendieckFibObjOpPresheaf C fib tw' := by
  intro a
  let domArr := coTwDomArr' m
  let codArr := coTwCodArr' m
  let dom : C := coTwDom' tw
  let dom' : C := coTwDom' tw'
  let f := coTwArr' tw
  let f' := coTwArr' tw'
  have hcommTw : codArr ≫ f' ≫ domArr = f := coTwHomComm' m
  have hcommOver : codArr ≫ (f' ≫ domArr) = f := hcommTw
  let overMor : Over.mk f ⟶ Over.mk (f' ≫ domArr) :=
    overHomFromCodArrOpPresheaf C f (f' ≫ domArr) codArr hcommOver
  let step1 : (fib dom).obj (Over.mk (f' ≫ domArr)) := (fib dom).map overMor a
  have hOverMap : (Over.map domArr).obj (Over.mk f') = Over.mk (f' ≫ domArr) := rfl
  let step1' : (fib dom).obj ((Over.map domArr).obj (Over.mk f')) := hOverMap ▸ step1
  exact (hom domArr).app (Over.mk f') step1'

end TwArrOpPresheaf

section ProfunctorOnTwistedArrow

/-!
## Profunctors composed with forgetful functors

Given a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, we can compose with the forgetful
functor to get a functor from a twisted arrow category to `D`.
-/

variable {D : Type*} [Category.{v} D]

/--
Given a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, compose with the forgetful functor
to get a functor from `TwistedArrow C` to `D`.

For a twisted arrow `(dom, cod, f)`, this evaluates to `(P.obj (op dom)).obj cod`.
-/
def profunctorOnTwistedArrow (P : Cᵒᵖ ⥤ C ⥤ D) : TwistedArrow C ⥤ D :=
  twistedArrowForget C ⋙ CategoryTheory.Functor.uncurry.obj P

@[simp]
theorem profunctorOnTwistedArrow_obj (P : Cᵒᵖ ⥤ C ⥤ D) (tw : TwistedArrow C) :
    (profunctorOnTwistedArrow C P).obj tw =
    (P.obj (Opposite.op (twDom tw))).obj (twCod tw) := rfl

@[simp]
theorem profunctorOnTwistedArrow_map (P : Cᵒᵖ ⥤ C ⥤ D)
    {x y : TwistedArrow C} (f : x ⟶ y) :
    (profunctorOnTwistedArrow C P).map f =
    (P.map (twDomArr f).op).app (twCod x) ≫
    (P.obj (Opposite.op (twDom y))).map (twCodArr f) := rfl

/--
Functorial version of `profunctorOnTwistedArrow`: a functor from profunctors
to functors on `TwistedArrow C`.
-/
def profunctorOnTwistedArrowFunctor : (Cᵒᵖ ⥤ C ⥤ D) ⥤ (TwistedArrow C ⥤ D) :=
  Functor.uncurry ⋙
  (Functor.whiskeringLeft (TwistedArrow C) (Cᵒᵖ × C) D).obj (twistedArrowForget C)

theorem profunctorOnTwistedArrow_eq_functor_obj (P : Cᵒᵖ ⥤ C ⥤ D) :
    profunctorOnTwistedArrow C P =
      (profunctorOnTwistedArrowFunctor (C := C)).obj P := rfl

/--
The equivalence from `Cᵒᵖᵒᵖ × Cᵒᵖ` to `Cᵒᵖ × C` via swap and `opOpEquivalence`.
-/
def coTwistedArrowProdEquiv :
    Cᵒᵖᵒᵖ × Cᵒᵖ ≌ Cᵒᵖ × C :=
  (CategoryTheory.Equivalence.prod
    (opOpEquivalence C)
    (CategoryTheory.Equivalence.refl (C := Cᵒᵖ))).trans
    (Prod.braiding C Cᵒᵖ)

/--
Given a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, compose with the forgetful functor
and equivalence to get a functor from `CoTwistedArrow C` to `D`.

For a co-twisted arrow with `coTwDom = a` and `coTwCod = b`, this evaluates to
`(P.obj (op a)).obj b`. The dom/cod are swapped relative to the arrow direction
because of how the equivalence and braiding compose.
-/
def profunctorOnCoTwistedArrow (P : Cᵒᵖ ⥤ C ⥤ D) : CoTwistedArrow C ⥤ D :=
  coTwistedArrowForget C ⋙
    (coTwistedArrowProdEquiv C).functor ⋙
    CategoryTheory.Functor.uncurry.obj P

@[simp]
theorem profunctorOnCoTwistedArrow_obj (P : Cᵒᵖ ⥤ C ⥤ D) (tw : CoTwistedArrow C) :
    (profunctorOnCoTwistedArrow C P).obj tw =
    (P.obj (Opposite.op (coTwDom tw))).obj (coTwCod tw) := rfl

/-- The first component of the equivalence composition is `op (coTwDom tw)`. -/
@[simp]
theorem coTwistedArrowProdEquiv_forget_fst (tw : CoTwistedArrow C) :
    ((coTwistedArrowProdEquiv C).functor.obj
      ((coTwistedArrowForget C).obj tw)).1 = Opposite.op (coTwDom tw) := rfl

/-- The second component of the equivalence composition is `coTwCod tw`. -/
@[simp]
theorem coTwistedArrowProdEquiv_forget_snd (tw : CoTwistedArrow C) :
    ((coTwistedArrowProdEquiv C).functor.obj
      ((coTwistedArrowForget C).obj tw)).2 = coTwCod tw := rfl

/--
The functor map formula for `profunctorOnCoTwistedArrow`.

For a morphism `m : x ⟶ y` in `CoTwistedArrow C`, the profunctor functor maps it
to the composition of the contravariant action (via `coTwDomArr`) followed by
the covariant action (via `coTwCodArr`).
-/
theorem profunctorOnCoTwistedArrow_map (P : Cᵒᵖ ⥤ C ⥤ D)
    {x y : CoTwistedArrow C} (m : x ⟶ y) :
    (profunctorOnCoTwistedArrow C P).map m =
    (P.map (coTwDomArr m).op).app (coTwCod x) ≫
    (P.obj (Opposite.op (coTwDom y))).map (coTwCodArr m) := rfl

/--
The functor map from a general arrow to the domain identity via contravariant.

For `f : i ⟶ j`, there is a morphism in `CoTwistedArrow` from `coTwObjMk f`
to `coTwObjMk (𝟙 i)`, and the profunctor functor maps this via the
contravariant action: `(P.map f.op).app i : P(j, i) → P(i, i)`.
-/
theorem profunctorOnCoTwistedArrow_map_to_dom (P : Cᵒᵖ ⥤ C ⥤ D)
    {i j : C} (f : i ⟶ j) :
    let morph_to_i : coTwObjMk f ⟶ coTwObjMk (𝟙 i) := coTwHomMk
      (domArr := f) (codArr := 𝟙 i)
      (by simp [Category.id_comp])
    (profunctorOnCoTwistedArrow C P).map morph_to_i =
      (P.map f.op).app i := by
  intro morph_to_i
  rw [profunctorOnCoTwistedArrow_map]
  simp only [morph_to_i, coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk,
    coTwObjMk_cod, coTwObjMk_dom, Functor.map_id, Category.comp_id]

/--
The functor map from a general arrow to the codomain identity via covariant.

For `f : i ⟶ j`, there is a morphism in `CoTwistedArrow` from `coTwObjMk f`
to `coTwObjMk (𝟙 j)`, and the profunctor functor maps this via the
covariant action: `(P.obj (op j)).map f : P(j, i) → P(j, j)`.
-/
theorem profunctorOnCoTwistedArrow_map_to_cod (P : Cᵒᵖ ⥤ C ⥤ D)
    {i j : C} (f : i ⟶ j) :
    let morph_to_j : coTwObjMk f ⟶ coTwObjMk (𝟙 j) := coTwHomMk
      (domArr := 𝟙 j) (codArr := f)
      (by simp [Category.comp_id])
    (profunctorOnCoTwistedArrow C P).map morph_to_j =
      (P.obj (Opposite.op j)).map f := by
  intro morph_to_j
  rw [profunctorOnCoTwistedArrow_map]
  simp only [morph_to_j, coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk,
    coTwObjMk_cod, coTwObjMk_dom, op_id, Functor.map_id, NatTrans.id_app,
    Category.id_comp]

/--
Functorial version of `profunctorOnCoTwistedArrow`: a functor from profunctors
to functors on `CoTwistedArrow C`.
-/
def profunctorOnCoTwistedArrowFunctor : (Cᵒᵖ ⥤ C ⥤ D) ⥤ (CoTwistedArrow C ⥤ D) :=
  Functor.uncurry ⋙
  (Functor.whiskeringLeft (CoTwistedArrow C) (Cᵒᵖ × C) D).obj
    (coTwistedArrowForget C ⋙ (coTwistedArrowProdEquiv C).functor)

theorem profunctorOnCoTwistedArrow_eq_functor_obj (P : Cᵒᵖ ⥤ C ⥤ D) :
    profunctorOnCoTwistedArrow C P =
      (profunctorOnCoTwistedArrowFunctor (C := C)).obj P := rfl

/--
Given a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, compose with the equivalence
`(TwistedArrow C)ᵒᵖ ≌ CoTwistedArrow C` and the forgetful functor to get
a functor from `(TwistedArrow C)ᵒᵖ` to `D`.

This is a presheaf on `TwistedArrow C` when `D = Type v`, making it
suitable as a weight for weighted cocones over `TwistedArrow C`.
-/
def profunctorOnOpTwistedArrow (P : Cᵒᵖ ⥤ C ⥤ D) : (TwistedArrow C)ᵒᵖ ⥤ D :=
  twistedArrowOpEquivCoTwistedArrow.functor ⋙ profunctorOnCoTwistedArrow C P

theorem profunctorOnOpTwistedArrow_obj (P : Cᵒᵖ ⥤ C ⥤ D)
    (tw : (TwistedArrow C)ᵒᵖ) :
    (profunctorOnOpTwistedArrow C P).obj tw =
    (profunctorOnCoTwistedArrow C P).obj
      (twistedArrowOpEquivCoTwistedArrow.functor.obj tw) := rfl

theorem profunctorOnOpTwistedArrow_map (P : Cᵒᵖ ⥤ C ⥤ D)
    {x y : (TwistedArrow C)ᵒᵖ} (f : x ⟶ y) :
    (profunctorOnOpTwistedArrow C P).map f =
    (profunctorOnCoTwistedArrow C P).map
      (twistedArrowOpEquivCoTwistedArrow.functor.map f) := rfl

/--
The functor evaluating a profunctor on the opposite of the co-twisted arrow
category.

For `P : Cᵒᵖ ⥤ C ⥤ D`, this produces `(CoTwistedArrow C)ᵒᵖ ⥤ D` by composing
the equivalence `(CoTwistedArrow C)ᵒᵖ ≌ TwistedArrow C` with evaluation on
`TwistedArrow C`.
-/
def profunctorOnOpCoTwistedArrow (P : Cᵒᵖ ⥤ C ⥤ D) : (CoTwistedArrow C)ᵒᵖ ⥤ D :=
  coTwistedArrowOpEquivTwistedArrow.functor ⋙ profunctorOnTwistedArrow C P

theorem profunctorOnOpCoTwistedArrow_obj (P : Cᵒᵖ ⥤ C ⥤ D)
    (cotw : (CoTwistedArrow C)ᵒᵖ) :
    (profunctorOnOpCoTwistedArrow C P).obj cotw =
    (profunctorOnTwistedArrow C P).obj
      (coTwistedArrowOpEquivTwistedArrow.functor.obj cotw) := rfl

theorem profunctorOnOpCoTwistedArrow_map (P : Cᵒᵖ ⥤ C ⥤ D)
    {x y : (CoTwistedArrow C)ᵒᵖ} (f : x ⟶ y) :
    (profunctorOnOpCoTwistedArrow C P).map f =
    (profunctorOnTwistedArrow C P).map
      (coTwistedArrowOpEquivTwistedArrow.functor.map f) := rfl

/--
Functorial version of `profunctorOnOpCoTwistedArrow`: a functor from profunctors
to presheaves on `CoTwistedArrow C`.
-/
def profunctorOnOpCoTwistedArrowFunctor :
    (Cᵒᵖ ⥤ C ⥤ D) ⥤ ((CoTwistedArrow C)ᵒᵖ ⥤ D) :=
  (profunctorOnTwistedArrowFunctor (C := C)) ⋙
  (Functor.whiskeringLeft (CoTwistedArrow C)ᵒᵖ (TwistedArrow C) D).obj
    coTwistedArrowOpEquivTwistedArrow.functor

theorem profunctorOnOpCoTwistedArrow_eq_functor_obj (P : Cᵒᵖ ⥤ C ⥤ D) :
    profunctorOnOpCoTwistedArrow C P =
      (profunctorOnOpCoTwistedArrowFunctor (C := C)).obj P := rfl

end ProfunctorOnTwistedArrow

end GebLean
