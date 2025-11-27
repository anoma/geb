import GebLean.Utilities.Elements
import GebLean.Utilities.Grothendieck
import GebLean.Utilities.Presheaf
import GebLean.Utilities.Slice
import GebLean.Utilities.TwistedArrow

/-!
# Functor categories on twisted arrow categories

This module defines functor categories from the four twisted arrow category
variants to `Type v`:

- `TwArrCopresheaf C` = `TwistedArrow' C ⥤ Type v` (copresheaves on Tw)
- `TwArrPresheaf C` = `OpTwistedArrow' C ⥤ Type v` (presheaves on Tw)
- `TwArrOpCopresheaf C` = `TwistedArrowOp' C ⥤ Type v` (copresheaves on TwOp)
- `TwArrOpPresheaf C` = `CoTwistedArrow C ⥤ Type v` (presheaves on TwOp)

Since `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`, functors from `OpTwistedArrow'`
are presheaves on `TwistedArrow'`. Similarly, since
`CoTwistedArrow C ≅ (TwistedArrowOp' C)ᵒᵖ'`, functors from `CoTwistedArrow`
are presheaves on `TwistedArrowOp'`.

Two of these have direct slice equivalences via `sliceEquivCopresheaf`:
- `Over hom' ≌ TwArrCopresheaf C`
- `Over homOp' ≌ TwArrOpCopresheaf C`
-/

universe v u

namespace GebLean

open CategoryTheory

variable (C : Type u) [Category.{v} C]

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
      simp
      unfold OpProdInst'
      simp
      unfold
        CategoryStruct.id CategoryStruct.comp Category.toCategoryStruct
        opProd' uniformProd
      simp
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

/--
Equality proof for identity: the fiber after applying identity equals the fiber.
-/
def TwArrPresheaf.sliceGrothendieckEqId (F : TwArrPresheaf C) :
    Grothendieck.FunctorToEqId (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) := by
  intro y
  simp only [sliceGrothendieckFib, Functor.id_map]
  exact congrFun (congrArg Functor.obj ((overCopresheafFunctor C).map_id y)) _

/--
Equality proof for composition: the fiber after applying composite equals
applying them sequentially.
-/
def TwArrPresheaf.sliceGrothendieckEqComp (F : TwArrPresheaf C) :
    Grothendieck.FunctorToEqComp (overCopresheafFunctor C) (𝟭 Cᵒᵖ')
      (F.sliceGrothendieckFib C) := by
  intro y y' y'' g h
  simp only [sliceGrothendieckFib, Functor.id_map]
  exact congrFun (congrArg Functor.obj ((overCopresheafFunctor C).map_comp g h)) _

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
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C)
      (F.sliceGrothendieckEqId C) := by
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
      (F.sliceGrothendieckFib C) (F.sliceGrothendieckHomFiber C)
      (F.sliceGrothendieckEqComp C) := by
  intro y y' y'' g h
  apply NatTrans.ext
  funext f
  simp only [sliceGrothendieckHomFiber, sliceNatTrans, Functor.id_obj, Functor.id_map]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [overCopresheafFunctor, copresheafConstruction,
    copresheafConstructionMap, Functor.op', Functor.comp_map,
    Functor.whiskeringLeft, Over.mapFunctor, Functor.comp_obj,
    Functor.whiskerLeft_app]
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
The slice construction for a `TwArrPresheaf` assembles into a functor from
`Cᵒᵖ'` to the Grothendieck construction over `overCopresheafFunctor`.

For each object `y : Cᵒᵖ'`, we get `(y, F.sliceCopresheaf y)` in the
Grothendieck construction. For each morphism `h : y ⟶ y'` in `Cᵒᵖ'` (which is
`h : y' ⟶ y` in C), we get a Grothendieck morphism from
`(y, F.sliceCopresheaf y)` to `(y', F.sliceCopresheaf y')`.
-/
def TwArrPresheaf.sliceGrothendieckFunctor (F : TwArrPresheaf C) :
    Cᵒᵖ' ⥤ Grothendieck (overCopresheafFunctor C) :=
  Grothendieck.functorTo
    (overCopresheafFunctor C)
    (𝟭 Cᵒᵖ')
    (F.sliceGrothendieckFib C)
    (fun h => F.sliceGrothendieckHomFiber C h)
    (F.sliceGrothendieckEqId C)
    (F.sliceGrothendieckEqComp C)
    (F.sliceGrothendieck_hom_id C)
    (fun g h => F.sliceGrothendieck_hom_comp C g h)

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

end TwArrOpCopresheaf

section TwArrOpPresheaf

/--
Presheaves on the opposite-variant twisted arrow category: covariant functors
from `CoTwistedArrow C` to `Type v`.

Since `CoTwistedArrow C ≅ (TwistedArrowOp' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrowOp' C`, i.e., presheaves.
-/
def TwArrOpPresheaf := CoTwistedArrow C ⥤ Type v

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
      simp
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
         Category.toCategoryStruct, instCategoryCoTwistedArrow, CategoryOp'Inst]
      change (h ≫ 𝟙 x', g.left ≫ 𝟙 f'.left).1 = (𝟙 x ≫ h, 𝟙 f.left ≫ g.left).1
      simp only [Category.id_comp, Category.comp_id]
    · simp only
        [coTwCodArr', coTwHomMk', CategoryOfElements.homMk,
         Category.toCategoryStruct, instCategoryCoTwistedArrow, CategoryOp'Inst]
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

end TwArrOpPresheaf

end GebLean
