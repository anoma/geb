module LanguageDef.IntFamCat

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
record IntFamMor {c : Type} (mor : IntDifunctorSig c) (dom, cod : IntFamObj c)
    where
  constructor IFM
  ifmOnIdx : ifoIdx cod -> ifoIdx dom -- Contravariant on indexes
  ifmOnObj : (i : ifoIdx cod) -> mor (ifoObj dom (ifmOnIdx i)) (ifoObj cod i)

export
ifmId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntFamObj c) -> IntFamMor mor obj obj
ifmId {c} mor cid obj = IFM id (\i => cid $ ifoObj obj i)

export
ifmComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntComp c mor) ->
  {x, y, z : IntFamObj c} ->
  IntFamMor mor y z ->
  IntFamMor mor x y ->
  IntFamMor mor x z
ifmComp {c} mor comp {x} {y} {z} g f =
  IFM
    (ifmOnIdx f . ifmOnIdx g)
    (\i =>
      comp
        (ifoObj x $ ifmOnIdx f $ ifmOnIdx g i)
        (ifoObj y $ ifmOnIdx g i)
        (ifoObj z i)
        (ifmOnObj g i)
        (ifmOnObj f $ ifmOnIdx g i))

-- The unit of the free cartesian monoidal category monad.
export
fcmUnit : {c : Type} -> (mor : IntDifunctorSig c) -> c -> IntFamObj c
fcmUnit {c} mor x = IFO Unit (const x)

-------------------------------------
-------------------------------------
---- Metalanguage-slice families ----
-------------------------------------
-------------------------------------

public export
SliceFamObj : Type -> Type
SliceFamObj = IntFamObj . SliceObj

public export
SliceFamMor : {c : Type} -> SliceFamObj c -> SliceFamObj c -> Type
SliceFamMor {c} = IntFamMor {c=(SliceObj c)} $ SliceMorphism {a=c}

public export
slfmId : {c : Type} ->
  (x : SliceFamObj c) -> SliceFamMor x x
slfmId {c} = ifmId {c=(SliceObj c)} (SliceMorphism {a=c}) sliceId

public export
slfmComp : {c : Type} -> {x, y, z : SliceFamObj c} ->
  SliceFamMor y z -> SliceFamMor x y -> SliceFamMor x z
slfmComp {c} = ifmComp (SliceMorphism {a=c}) $ \x, y, z => sliceComp {x} {y} {z}

public export
sliceFamUnit : {c : Type} -> SliceObj c -> SliceFamObj c
sliceFamUnit {c} = fcmUnit {c=(SliceObj c)} (SliceMorphism {a=c})
