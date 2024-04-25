module LanguageDef.IntEFamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntArena

-----------------
-----------------
---- Objects ----
-----------------
-----------------

-- The objects of the category of existential families (AKA the
-- free coproduct completion) of a given category are the same
-- as those of the category of universal families (`IntUFamObj`);
-- it's in the morphisms that the two differ.  The structure
-- is also the same as that of an internal arena (`IntArena`).

public export
IntEFamObj : Type -> Type
IntEFamObj = IntArena

public export
IFEO : {0 c : Type} -> (idx : Type) -> (idx -> c) -> IntEFamObj c
IFEO {c} idx obj = (idx ** obj)

public export
ifeoIdx : {0 c : Type} -> IntEFamObj c -> Type
ifeoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
ifeoObj : {0 c : Type} -> (ef : IntEFamObj c) -> ifeoIdx {c} ef -> c
ifeoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

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
IFEM : {c : Type} -> {mor : IntDifunctorSig c} -> {dom, cod : IntEFamObj c} ->
  (onidx : ifeoIdx dom -> ifeoIdx cod) ->
  (onobj : (di : ifeoIdx dom) ->
    mor (ifeoObj dom di) (ifeoObj cod (onidx di))) ->
  IntEFamMor {c} mor dom cod
IFEM {c} {mor} {dom} {cod} onidx onobj = (onidx ** onobj)

public export
ifemOnIdx : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntEFamObj c} -> IntEFamMor {c} mor dom cod ->
  (ifeoIdx dom -> ifeoIdx cod)
ifemOnIdx = DPair.fst

public export
ifemOnObj : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntEFamObj c} -> (m : IntEFamMor {c} mor dom cod) ->
  (di : ifeoIdx dom) ->
  mor (ifeoObj dom di) (ifeoObj cod $ ifemOnIdx {mor} {dom} {cod} m di)
ifemOnObj = DPair.snd

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

---------------------------------------
---------------------------------------
---- Element existential families -----
---------------------------------------
---------------------------------------

-- Given categories `c` and `d`, a copresheaf `f` on `c`, and a functor
-- to `d` from the category of elements of `f`, we can form a functor
-- from `c` to `IntEFamObj d`.

public export
IntElemEFamMor : {c, d : Type} ->
  (dmor : IntDifunctorSig d) ->
  (f : IntCopreshfSig c) ->
  (g : (cobj : c) -> f cobj -> d) ->
  c -> c -> Type
IntElemEFamMor {c} {d} dmor f g x y =
  IntEFamMor {c=d} dmor (f x ** g x) (f y ** g y)

public export
IntElemEFamOMap : {c, d : Type} -> (f : IntCopreshfSig c) ->
  ((cobj : c) -> f cobj -> d) -> (c -> IntEFamObj d)
IntElemEFamOMap {c} {d} f g cobj = (f cobj ** g cobj)

public export
IntElemEFamFMap : {c, d : Type} ->
  (cmor : IntDifunctorSig c) -> (dmor : IntDifunctorSig d) ->
  (f : IntCopreshfSig c) -> (fm : IntCopreshfMapSig c cmor f) ->
  (g : (cobj : c) -> f cobj -> d) ->
  (gm :
    (x : c) -> (y : c) -> (efx : f x) ->
    (mxy : cmor x y) -> dmor (g x efx) (g y $ fm x y mxy efx)) ->
  (x, y : c) -> cmor x y ->
  IntEFamMor {c=d} dmor
    (IntElemEFamOMap {c} {d} f g x)
    (IntElemEFamOMap {c} {d} f g y)
IntElemEFamFMap {c} {d} cmor dmor f fm g gm x y mxy =
  (fm x y mxy ** \efy => gm x y efy mxy)

--------------------------------------------
--------------------------------------------
---- Existential families as presheaves ----
--------------------------------------------
--------------------------------------------

-- Existential families can be interpreted as presheaves, in which
-- form they are precisely the Dirichlet functors.

public export
InterpEFamPreshfOMap : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEFamObj c -> IntPreshfSig c
InterpEFamPreshfOMap c mor x a = Sigma {a=(ifeoIdx x)} $ mor a . ifeoObj x

export
IntEFamPreshfOMapIsInterpDirichObj : (c : Type) -> (mor : IntDifunctorSig c) ->
  (x : IntEFamObj c) -> (y : c) ->
  InterpEFamPreshfOMap c mor x y = InterpIDFobj c mor x y
IntEFamPreshfOMapIsInterpDirichObj c mor (xidx ** xobj) y = Refl

public export
InterpEFamPreshfFMap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (a : IntEFamObj c) -> IntPreshfMapSig c mor (InterpEFamPreshfOMap c mor a)
InterpEFamPreshfFMap c mor comp a xobj yobj myx =
  dpMapSnd $ \ei, mxi => comp yobj xobj (ifeoObj a ei) mxi myx

export
IntEFamPreshfFMapIsInterpDirichMap : FunExt ->
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (a : IntEFamObj c) -> (x, y : c) -> (m : mor y x) ->
  InterpEFamPreshfFMap c mor comp a x y m = InterpIDFmap c mor comp a x y m
IntEFamPreshfFMapIsInterpDirichMap fext c mor comp a x y m = funExt $ \_ => Refl

public export
InterpEFamPreshfNT :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x, y : IntEFamObj c) -> (m : IntEFamMor {c} mor x y) ->
  IntPreshfNTSig c (InterpEFamPreshfOMap c mor x) (InterpEFamPreshfOMap c mor y)
InterpEFamPreshfNT c mor comp x y m cobj =
  dpBimap (ifemOnIdx {mor} m)
    $ \exi, mcx =>
      comp cobj (ifeoObj x exi) (ifeoObj y $ ifemOnIdx {mor} m exi)
        (ifemOnObj {mor} m exi)
        mcx

public export
IntEFamPreshfNTisInterpDirichNT : FunExt ->
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x, y : IntEFamObj c) -> (m : IntEFamMor {c} mor x y) -> (cobj : c) ->
  InterpEFamPreshfNT c mor comp x y m cobj = InterpIDnt c mor comp x y m cobj
IntEFamPreshfNTisInterpDirichNT c mor comp x y m cobj fext = funExt $ \_ => Refl

public export
InterpEFamPreshfNaturality :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (assoc : IntAssocSig c mor comp) ->
  (x, y : IntEFamObj c) -> (m : IntEFamMor {c} mor x y) ->
  IntPreshfNTNaturality c mor
    (InterpEFamPreshfOMap c mor x)
    (InterpEFamPreshfOMap c mor y)
    (InterpEFamPreshfFMap c mor comp x)
    (InterpEFamPreshfFMap c mor comp y)
    (InterpEFamPreshfNT c mor comp x y m)
InterpEFamPreshfNaturality c mor comp assoc
  (xidx ** xobj) (yidx ** yobj) (midx ** mobj) a b mba (exi ** max) =
    dpEq12 Refl
      $ assoc b a (xobj exi) (yobj (midx exi)) (mobj exi) max mba

-------------------------------------------
-------------------------------------------
---- Metalanguage existential families ----
-------------------------------------------
-------------------------------------------

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
-- This interpretation takes the form of a functor from `MLEFamObj` to `Type`.

export
InterpMLEFamObj : MLEFamObj -> Type
InterpMLEFamObj ifuo = Sigma {a=(fst ifuo)} $ snd ifuo

export
InterpMLEFamMorph : {0 x, y : MLEFamObj} ->
  MLEFamMor x y -> InterpMLEFamObj x -> InterpMLEFamObj y
InterpMLEFamMorph {x=(xpos ** xdir)} {y=(ypos ** ydir)} (onpos ** ondir) =
  dpBimap onpos ondir

-------------------------------------------------
-------------------------------------------------
---- Metalanguage-slice existential families ----
-------------------------------------------------
-------------------------------------------------

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