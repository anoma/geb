module LanguageDef.IntUFamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

-- This is just an `IntArena` with names.
public export
record IntUFamObj (c : Type) where
  constructor IFO
  ifoIdx : Type
  ifoObj : ifoIdx -> c

export
IFOtoArena : {c : Type} -> IntUFamObj c -> IntArena c
IFOtoArena {c} ifo = (ifoIdx ifo ** ifoObj ifo)

export
IFOfromArena : {c : Type} -> IntArena c -> IntUFamObj c
IFOfromArena {c} ar = IFO (fst ar) (snd ar)

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

-- Morphisms of the category of families of objects from a given category.
-- See for example the definition preceding Theorem 2.5 at
-- https://ncatlab.org/nlab/show/multi-adjoint#definition , which
-- notes that this category may be viewed as the free cartesian monoidal
-- category on `c`.
--
-- Note also from this definition of morphism that the category of families
-- is the opposite of the category of polynomial functors.
--
-- Also, contrast it with the category of covariant bundles, which is equivalent
-- to the category of Dirichlet functors -- that category's morphisms are
-- covariant on both indexes and objects.
public export
record IntUFamMor {c : Type} (mor : IntDifunctorSig c) (dom, cod : IntUFamObj c)
    where
  constructor IFUM
  ifumOnIdx : ifoIdx cod -> ifoIdx dom -- Contravariant on indexes
  ifumOnObj : (i : ifoIdx cod) -> mor (ifoObj dom (ifumOnIdx i)) (ifoObj cod i)

public export
ifumId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntUFamObj c) -> IntUFamMor mor obj obj
ifumId {c} mor cid obj = IFUM id (\i => cid $ ifoObj obj i)

public export
ifumComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntComp c mor) ->
  {x, y, z : IntUFamObj c} ->
  IntUFamMor mor y z ->
  IntUFamMor mor x y ->
  IntUFamMor mor x z
ifumComp {c} mor comp {x} {y} {z} g f =
  IFUM
    (ifumOnIdx f . ifumOnIdx g)
    (\i =>
      comp
        (ifoObj x $ ifumOnIdx f $ ifumOnIdx g i)
        (ifoObj y $ ifumOnIdx g i)
        (ifoObj z i)
        (ifumOnObj g i)
        (ifumOnObj f $ ifumOnIdx g i))

-- The unit of the free cartesian monoidal category monad.
public export
fcmUnit : {c : Type} -> (mor : IntDifunctorSig c) -> c -> IntUFamObj c
fcmUnit {c} mor x = IFO Unit (const x)

-------------------------------
-------------------------------
---- Metalanguage families ----
-------------------------------
-------------------------------

--------------------
---- Definition ----
--------------------

public export
MLUFamObj : Type
MLUFamObj = IntUFamObj Type

public export
MLUFamMor : MLUFamObj -> MLUFamObj -> Type
MLUFamMor = IntUFamMor $ HomProf

public export
mlfmId : (x : MLUFamObj) -> MLUFamMor x x
mlfmId = ifumId HomProf typeId

public export
mlfmComp : {x, y, z : MLUFamObj} ->
  MLUFamMor y z -> MLUFamMor x y -> MLUFamMor x z
mlfmComp = ifumComp HomProf (\_, _, _ => (.))

public export
mluFamUnit : Type -> MLUFamObj
mluFamUnit = fcmUnit HomProf

------------------------
---- Interpretation ----
------------------------

-- In a category with products, such as `Type`, we can interpret an
-- `IntUFamObj` as a product with morphisms restricted to factorizations
-- into morphisms on indexes and morphisms on components.

export
InterpMLUFamObj : MLUFamObj -> Type
InterpMLUFamObj ifo = Pi {a=(ifoIdx ifo)} $ ifoObj ifo

export
InterpMLUFamMorph : {0 x, y : MLUFamObj} ->
  MLUFamMor x y -> InterpMLUFamObj x -> InterpMLUFamObj y
InterpMLUFamMorph {x} {y} m pix iy = ifumOnObj m iy $ pix $ ifumOnIdx m iy

-------------------------------------
-------------------------------------
---- Metalanguage-slice families ----
-------------------------------------
-------------------------------------

--------------------
---- Definition ----
--------------------

public export
SliceFamObj : Type -> Type
SliceFamObj = IntUFamObj . SliceObj

public export
SliceUFamMor : {c : Type} -> SliceFamObj c -> SliceFamObj c -> Type
SliceUFamMor {c} = IntUFamMor {c=(SliceObj c)} $ SliceMorphism {a=c}

public export
slufmId : {c : Type} ->
  (x : SliceFamObj c) -> SliceUFamMor x x
slufmId {c} = ifumId {c=(SliceObj c)} (SliceMorphism {a=c}) sliceId

public export
slufmComp : {c : Type} -> {x, y, z : SliceFamObj c} ->
  SliceUFamMor y z -> SliceUFamMor x y -> SliceUFamMor x z
slufmComp {c} =
  ifumComp (SliceMorphism {a=c}) $ \x, y, z => sliceComp {x} {y} {z}

public export
slUFamUnit : {c : Type} -> SliceObj c -> SliceFamObj c
slUFamUnit {c} = fcmUnit {c=(SliceObj c)} (SliceMorphism {a=c})
