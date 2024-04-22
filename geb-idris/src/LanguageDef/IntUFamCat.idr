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
record IntFamObj (c : Type) where
  constructor IFO
  ifoIdx : Type
  ifoObj : ifoIdx -> c

export
IFOtoArena : {c : Type} -> IntFamObj c -> IntArena c
IFOtoArena {c} ifo = (ifoIdx ifo ** ifoObj ifo)

export
IFOfromArena : {c : Type} -> IntArena c -> IntFamObj c
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
record IntUFamMor {c : Type} (mor : IntDifunctorSig c) (dom, cod : IntFamObj c)
    where
  constructor IFUM
  ifumOnIdx : ifoIdx cod -> ifoIdx dom -- Contravariant on indexes
  ifumOnObj : (i : ifoIdx cod) -> mor (ifoObj dom (ifumOnIdx i)) (ifoObj cod i)

public export
ifumId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntFamObj c) -> IntUFamMor mor obj obj
ifumId {c} mor cid obj = IFUM id (\i => cid $ ifoObj obj i)

public export
ifumComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntComp c mor) ->
  {x, y, z : IntFamObj c} ->
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
fcmUnit : {c : Type} -> (mor : IntDifunctorSig c) -> c -> IntFamObj c
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
MLFamObj : Type
MLFamObj = IntFamObj Type

public export
MLUFamMor : MLFamObj -> MLFamObj -> Type
MLUFamMor = IntUFamMor $ HomProf

public export
mlfmId : (x : MLFamObj) -> MLUFamMor x x
mlfmId = ifumId HomProf typeId

public export
mlfmComp : {x, y, z : MLFamObj} ->
  MLUFamMor y z -> MLUFamMor x y -> MLUFamMor x z
mlfmComp = ifumComp HomProf (\_, _, _ => (.))

public export
mliceUFamUnit : Type -> MLFamObj
mliceUFamUnit = fcmUnit HomProf

------------------------
---- Interpretation ----
------------------------

-- In a category with products, such as `Type`, we can interpret an
-- `IntFamObj` as a product with morphisms restricted to factorizations
-- into morphisms on indexes and morphisms on components.

export
InterpMLFamObj : MLFamObj -> Type
InterpMLFamObj ifo = Pi {a=(ifoIdx ifo)} $ ifoObj ifo

export
InterpMLUFamMorph : {0 x, y : MLFamObj} ->
  MLUFamMor x y -> InterpMLFamObj x -> InterpMLFamObj y
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
SliceFamObj = IntFamObj . SliceObj

public export
SliceUFamMor : {c : Type} -> SliceFamObj c -> SliceFamObj c -> Type
SliceUFamMor {c} = IntUFamMor {c=(SliceObj c)} $ SliceMorphism {a=c}

public export
slfmId : {c : Type} ->
  (x : SliceFamObj c) -> SliceUFamMor x x
slfmId {c} = ifumId {c=(SliceObj c)} (SliceMorphism {a=c}) sliceId

public export
slfmComp : {c : Type} -> {x, y, z : SliceFamObj c} ->
  SliceUFamMor y z -> SliceUFamMor x y -> SliceUFamMor x z
slfmComp {c} = ifumComp (SliceMorphism {a=c}) $ \x, y, z => sliceComp {x} {y} {z}

public export
sliceUFamUnit : {c : Type} -> SliceObj c -> SliceFamObj c
sliceUFamUnit {c} = fcmUnit {c=(SliceObj c)} (SliceMorphism {a=c})
