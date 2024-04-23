module LanguageDef.IntEFamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

-- The objects of the category of existential families (AKA the
-- free coproduct completion) of a given category are the same
-- as those of the category of universal families (`IntEFamObj`);
-- it's in the morphisms that the two differ.  The structure
-- is also the same as that of an internal arena (`IntArena`).

public export
IntEFamObj : Type -> Type
IntEFamObj = IntArena

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

-- The free coproduct completion of a category has the same morphisms as (and
-- hence is equivalent to) the category of Dirichlet functors on the category;
-- we just interpret them differently (meaning, herein we will define a functor
-- from them to `Type`, rather than to `Type -> Type`).

public export
IntEFamMor : {c : Type} -> IntDifunctorSig c ->
  IntEFamObj c -> IntEFamObj c -> Type
IntEFamMor {c} = IntDirichCatMor c

public export
ifemId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntEFamObj c) -> IntEFamMor mor obj obj
ifemId {c} mor cid (pos ** dir) = (id ** \ep => cid $ dir ep)

public export
ifemComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntComp c mor) ->
  {x, y, z : IntEFamObj c} ->
  IntEFamMor mor y z ->
  IntEFamMor mor x y ->
  IntEFamMor mor x z
ifemComp {c} mor comp {x=(xpos ** xdir)} {y=(ypos ** ydir)} {z=(zpos ** zdir)}
  (gonpos ** gondir) (fonpos ** fondir) =
    (gonpos . fonpos **
     \exp =>
      comp
        (xdir exp)
        (ydir $ fonpos exp)
        (zdir $ gonpos $ fonpos exp)
        (gondir $ fonpos exp)
        (fondir exp))

-- The unit of the free coproduct completion monad.
public export
fccUnit : {c : Type} -> (mor : IntDifunctorSig c) -> c -> IntEFamObj c
fccUnit {c} mor x = (Unit ** const x)

-------------------------------
-------------------------------
---- Metalanguage families ----
-------------------------------
-------------------------------

--------------------
---- Definition ----
--------------------

public export
MLEFamObj : Type
MLEFamObj = IntEFamObj Type

public export
MLEFamMor : MLEFamObj -> MLEFamObj -> Type
MLEFamMor = IntEFamMor $ HomProf

public export
mlfmId : (x : MLEFamObj) -> MLEFamMor x x
mlfmId = ifemId HomProf typeId

public export
mlfmComp : {x, y, z : MLEFamObj} ->
  MLEFamMor y z -> MLEFamMor x y -> MLEFamMor x z
mlfmComp = ifemComp HomProf (\_, _, _ => (.))

public export
mlEFamUnit : Type -> MLEFamObj
mlEFamUnit = fccUnit HomProf

------------------------
---- Interpretation ----
------------------------

-- In a category with coproducts, such as `Type`, we can interpret an
-- `IntEFamObj` as a coproduct with morphisms restricted to factorizations
-- into morphisms on indexes and morphisms on components.

export
InterpMLEFamObj : MLEFamObj -> Type
InterpMLEFamObj ifo = Sigma {a=(fst ifo)} $ snd ifo

export
InterpMLEFamMorph : {0 x, y : MLEFamObj} ->
  MLEFamMor x y -> InterpMLEFamObj x -> InterpMLEFamObj y
InterpMLEFamMorph {x=(xpos ** xdir)} {y=(ypos ** ydir)} (onpos ** ondir) =
  dpBimap onpos ondir

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
SliceFamObj = IntEFamObj . SliceObj

public export
SliceEFamMor : {c : Type} -> SliceFamObj c -> SliceFamObj c -> Type
SliceEFamMor {c} = IntEFamMor {c=(SliceObj c)} $ SliceMorphism {a=c}

public export
slefmId : {c : Type} ->
  (x : SliceFamObj c) -> SliceEFamMor x x
slefmId {c} = ifemId {c=(SliceObj c)} (SliceMorphism {a=c}) sliceId

public export
slefmComp : {c : Type} -> {x, y, z : SliceFamObj c} ->
  SliceEFamMor y z -> SliceEFamMor x y -> SliceEFamMor x z
slefmComp {c} = ifemComp (SliceMorphism {a=c}) $ \x, y, z => sliceComp {x} {y} {z}

public export
slEFamUnit : {c : Type} -> SliceObj c -> SliceFamObj c
slEFamUnit {c} = fccUnit {c=(SliceObj c)} (SliceMorphism {a=c})

-- `InterpSLEFamObj` and `InterpSLEFamMor` comprise a functor from
-- `SliceFamObj c` to `SliceObj c` (for any `c : Type`).

export
InterpSLEFamObj : {c : Type} -> SliceFamObj c -> SliceObj c
InterpSLEFamObj {c} (xpos ** xdir) = Sigma {a=xpos} . flip xdir

export
InterpSLEFamMor : {c : Type} -> {0 x, y : SliceFamObj c} ->
  SliceEFamMor {c} x y ->
  SliceMorphism {a=c} (InterpSLEFamObj x) (InterpSLEFamObj y)
InterpSLEFamMor {c} {x=(xpos ** xdir)} {y=(ypos ** ydir)} (onpos ** ondir) ec =
  dpBimap onpos (\exp => ondir exp ec)
