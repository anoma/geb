module LanguageDef.IntUFamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntEFamCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

public export
IntUFamObj : Type -> Type
IntUFamObj = IntArena

public export
IFUO : {c : Type} -> (idx : Type) -> (idx -> c) -> IntUFamObj c
IFUO {c} idx obj = (idx ** obj)

public export
ifuoIdx : {c : Type} -> IntUFamObj c -> Type
ifuoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
ifuoObj : {c : Type} -> (uf : IntUFamObj c) -> ifuoIdx {c} uf -> c
ifuoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

-- Morphisms of the category of universal families of objects from a given
-- category.  See for example the definition preceding Theorem 2.5 at
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
IntUFamMor : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntUFamObj c) -> Type
IntUFamMor {c} mor dom cod =
  (onidx : ifuoIdx cod -> ifuoIdx dom **
   (ci : ifuoIdx cod) -> mor (ifuoObj dom $ onidx ci) (ifuoObj cod ci))

-- The category of universal families of objects from a category `c`
-- is equivalent to the opposite category of the category of existential
-- families of `op(c)`.
export
IntUFamIsOpEFamOp : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntUFamObj c) ->
  IntUFamMor {c} mor dom cod =
  IntOpCatMor (IntEFamObj c) (IntEFamMor {c} $ IntOpCatMor c mor) dom cod
IntUFamIsOpEFamOp {c} mor dom cod = Refl

public export
IFUM :
  {c : Type} -> {mor : IntDifunctorSig c} -> {dom, cod : IntUFamObj c} ->
  (onidx : ifuoIdx cod -> ifuoIdx dom) ->
  (onobj : (ci : ifuoIdx cod) ->
    mor (ifuoObj dom $ onidx ci) (ifuoObj cod ci)) ->
  IntUFamMor {c} mor dom cod
IFUM {c} {mor} {dom} {cod} onidx onobj = (onidx ** onobj)

public export
ifumOnIdx : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntUFamObj c} -> IntUFamMor {c} mor dom cod ->
  (ifuoIdx cod -> ifuoIdx dom)
ifumOnIdx = DPair.fst

public export
ifumOnObj : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntUFamObj c} -> (m : IntUFamMor {c} mor dom cod) ->
  (ci : ifuoIdx cod) ->
  mor (ifuoObj dom $ ifumOnIdx {mor} {dom} {cod} m ci) (ifuoObj cod ci)
ifumOnObj = DPair.snd

public export
ifumId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntUFamObj c) -> IntUFamMor mor obj obj
ifumId {c} mor cid obj = IFUM {mor} id (\i => cid $ ifuoObj obj i)

public export
ifumComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  {x, y, z : IntUFamObj c} ->
  IntUFamMor mor y z ->
  IntUFamMor mor x y ->
  IntUFamMor mor x z
ifumComp {c} mor comp {x} {y} {z} g f =
  IFUM {mor}
    (ifumOnIdx {mor} f . ifumOnIdx {mor} g)
    (\i =>
      comp
        (ifuoObj x $ ifumOnIdx {mor} f $ ifumOnIdx {mor} g i)
        (ifuoObj y $ ifumOnIdx {mor} g i)
        (ifuoObj z i)
        (ifumOnObj {mor} g i)
        (ifumOnObj {mor} f $ ifumOnIdx {mor} g i))

public export
UFamCatSig : IntCatSig -> IntCatSig
UFamCatSig c =
  ICat
    (IntUFamObj $ icObj c)
  $ MICS
    (IntUFamMor {c=(icObj c)} $ icMor c)
  $ ICS
    (ifumId {c=(icObj c)} (icMor c) (icId c))
    (\x, y, z => ifumComp {c=(icObj c)} (icMor c) (icComp c) {x} {y} {z})

-- The unit of the free cartesian monoidal category monad.
public export
fcmUnit : {c : Type} -> (mor : IntDifunctorSig c) -> c -> IntUFamObj c
fcmUnit {c} mor x = IFUO Unit (const x)

-------------------------------------
-------------------------------------
---- Element universal families -----
-------------------------------------
-------------------------------------

-- Given categories `c` and `d`, a presheaf `f` on `c`, and a functor
-- from the category of elements of `f` to `d`, we can form a functor
-- from `c` to `IntUFamObj d`.
--
-- Note that those inputs comprise precisely the data which define a
-- left multi-adjoint in the formulation of Theorem 2.4 at
-- https://ncatlab.org/nlab/show/multi-adjoint#definition --
-- `f` and `g` here are what are there called `I` and `L`.
--
-- The output functor is the one called `K` in Theorem 2.5 on the same
-- page.  So we might view this functor as translating from the Theorem 2.4
-- formulation of "left multi-adjoint" to the Theorem 2.5 formulation.

public export
IntElemUFamOMap : {c, d : Type} -> (f : IntPreshfSig c) ->
  ((cobj : c) -> f cobj -> d) -> (c -> IntUFamObj d)
IntElemUFamOMap {c} {d} f g cobj = IFUO (f cobj) (g cobj)

public export
IntElemUFamFMap : {c, d : Type} ->
  (cmor : IntDifunctorSig c) -> (dmor : IntDifunctorSig d) ->
  (f : IntPreshfSig c) -> (fcm : IntPreshfMapSig c cmor f) ->
  (g : (cobj : c) -> f cobj -> d) ->
  (gm :
    (x : c) -> (y : c) -> (efy : f y) ->
    (mxy : cmor x y) -> dmor (g x $ fcm y x mxy efy) (g y efy)) ->
  (x, y : c) ->
  cmor x y ->
  IntUFamMor {c=d} dmor
    (IntElemUFamOMap {c} {d} f g x)
    (IntElemUFamOMap {c} {d} f g y)
IntElemUFamFMap {c} {d} cmor dmor f fcm g gm x y mxy =
  IFUM {mor=dmor} {dom=(IntElemUFamOMap f g x)} {cod=(IntElemUFamOMap f g y)}
    (fcm y x mxy) (\efy => gm x y efy mxy)

------------------------------------------
------------------------------------------
---- Universal families as presheaves ----
------------------------------------------
------------------------------------------

public export
InterpUFamPreshfOMap : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntUFamObj c -> IntPreshfSig c
InterpUFamPreshfOMap c mor (idx ** obj) a = Pi {a=idx} $ mor a . obj

public export
InterpUFamPreshfFMap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x : IntUFamObj c) -> IntPreshfMapSig c mor (InterpUFamPreshfOMap c mor x)
InterpUFamPreshfFMap c mor comp (idx ** obj) xobj yobj myx pix =
  \ei : idx => comp yobj xobj (obj ei) (pix ei) myx

public export
InterpUFamPreshfNT :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x, y : IntUFamObj c) -> (m : IntUFamMor {c} mor x y) ->
  IntPreshfNTSig c (InterpUFamPreshfOMap c mor x) (InterpUFamPreshfOMap c mor y)
InterpUFamPreshfNT c mor comp
  (xidx ** xobj) (yidx ** yobj) (midx ** mobj) cobj pix =
    \eyi : yidx =>
     comp cobj (xobj $ midx eyi) (yobj eyi) (mobj eyi) (pix $ midx eyi)

public export
InterpUFamPreshfNaturality : FunExt ->
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (assoc : IntAssocSig c mor comp) ->
  (x, y : IntUFamObj c) -> (m : IntUFamMor {c} mor x y) ->
  IntPreshfNTNaturality c mor
    (InterpUFamPreshfOMap c mor x)
    (InterpUFamPreshfOMap c mor y)
    (InterpUFamPreshfFMap c mor comp x)
    (InterpUFamPreshfFMap c mor comp y)
    (InterpUFamPreshfNT c mor comp x y m)
InterpUFamPreshfNaturality fext c mor comp assoc
  (xidx ** xobj) (yidx ** yobj) (midx ** mobj) a b mba pix =
    funExt $
      \eyi =>
        assoc b a (xobj $ midx eyi) (yobj eyi) (mobj eyi) (pix $ midx eyi) mba

-----------------------------------------
-----------------------------------------
---- Metalanguage universal families ----
-----------------------------------------
-----------------------------------------

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
-- This interpretation takes the form of a functor from `MLUFamObj` to `Type`.

export
InterpMLUFamObj : MLUFamObj -> Type
InterpMLUFamObj ifuo = Pi {a=(ifuoIdx ifuo)} $ ifuoObj ifuo

export
InterpMLUFamMorph : {x, y : MLUFamObj} ->
  MLUFamMor x y -> InterpMLUFamObj x -> InterpMLUFamObj y
InterpMLUFamMorph {x} {y} m pix iy =
  ifumOnObj {mor=HomProf} m iy $ pix $ ifumOnIdx {mor=HomProf} m iy

-----------------------------------------------
-----------------------------------------------
---- Metalanguage-slice universal families ----
-----------------------------------------------
-----------------------------------------------

--------------------
---- Definition ----
--------------------

public export
SliceUFamObj : Type -> Type
SliceUFamObj = IntUFamObj . SliceObj

public export
SliceUFamMor : {c : Type} -> SliceUFamObj c -> SliceUFamObj c -> Type
SliceUFamMor {c} = IntUFamMor {c=(SliceObj c)} $ SliceMorphism {a=c}

public export
slufmId : {c : Type} ->
  (x : SliceUFamObj c) -> SliceUFamMor x x
slufmId {c} = ifumId {c=(SliceObj c)} (SliceMorphism {a=c}) (SliceId c)

public export
slufmComp : {c : Type} -> {x, y, z : SliceUFamObj c} ->
  SliceUFamMor y z -> SliceUFamMor x y -> SliceUFamMor x z
slufmComp {c} =
  ifumComp (SliceMor c) $ \x, y, z => SliceComp c x y z

public export
slUFamUnit : {c : Type} -> SliceObj c -> SliceUFamObj c
slUFamUnit {c} = fcmUnit {c=(SliceObj c)} (SliceMorphism {a=c})

-- `InterpSLUFamObj` and `InterpSLUFamMor` comprise a functor from
-- `SliceUFamObj c` to `SliceObj c` (for any `c : Type`).

export
InterpSLUFamObj : {c : Type} -> SliceUFamObj c -> SliceObj c
InterpSLUFamObj {c} x = Pi {a=(ifuoIdx x)} . flip (ifuoObj x)

export
InterpSLUFamMor : {c : Type} -> {x, y : SliceUFamObj c} ->
  SliceUFamMor {c} x y ->
  SliceMorphism {a=c} (InterpSLUFamObj x) (InterpSLUFamObj y)
InterpSLUFamMor {c} {x} {y} m ec pix eiy =
  ifumOnObj {mor=SliceMorphism} m eiy ec
  $ pix
  $ ifumOnIdx {mor=SliceMorphism} m eiy

------------------------------------------------------------
------------------------------------------------------------
---- Universal families of slices as slices of products ----
------------------------------------------------------------
------------------------------------------------------------

export
SLUFamToProdObj : {c: Type} ->
  (ufo : SliceUFamObj c) -> SliceObj (ifuoIdx ufo, c)
SLUFamToProdObj {c} ufo = uncurry $ DPair.snd ufo

export
SlProdBaseChange : {a, b, c : Type} -> (b -> a) -> SliceFunctor (a, c) (b, c)
SlProdBaseChange {a} {b} {c} m slac ebc = slac (m $ fst ebc, snd ebc)

export
SLUFamToProdMor : {c: Type} ->
  {ufo, ufo' : SliceUFamObj c} ->
  (mor : SliceUFamMor {c} ufo ufo') ->
  SliceMor (ifuoIdx ufo', c)
    (SlProdBaseChange (ifumOnIdx {dom=ufo} {cod=ufo'} {mor=(SliceMor c)} mor) $ SLUFamToProdObj ufo)
    (SLUFamToProdObj ufo')
SLUFamToProdMor mor eac esla = case eac of (ea, ec) => snd mor ea ec esla
