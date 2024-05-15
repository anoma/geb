module LanguageDef.IntUCofamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntUFamCat
import public LanguageDef.IntEFamCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

public export
IntUCofamObj : Type -> Type
IntUCofamObj = IntArena

public export
ICFUO : {c : Type} -> (idx : Type) -> (idx -> c) -> IntUCofamObj c
ICFUO {c} idx obj = (idx ** obj)

public export
icfuoIdx : {c : Type} -> IntUCofamObj c -> Type
icfuoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
icfuoObj : {c : Type} -> (uf : IntUCofamObj c) -> icfuoIdx {c} uf -> c
icfuoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

-- Morphisms of the category of universal cofamilies of objects from a given
-- category.  (A "cofamily" of objects from `c` is simply a family of objects
-- from the opposite of `c`; see `IntUFamCat` for the notion of "universal
-- family".)
public export
IntUCofamMor : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntUCofamObj c) -> Type
IntUCofamMor {c} mor dom cod =
  (onidx : icfuoIdx cod -> icfuoIdx dom **
   (ci : icfuoIdx cod) -> mor (icfuoObj cod ci) (icfuoObj dom $ onidx ci))

-- Note that this category is the opposite category of
-- the category of existential families (AKA Dirichlet functors).
export
IntUCofamIsOpEFam : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntUCofamObj c) ->
  IntUCofamMor {c} mor dom cod =
  IntOpCatMor (IntEFamObj c) (IntEFamMor {c} mor) dom cod
IntUCofamIsOpEFam {c} mor dom cod = Refl

-- Another way of viewing a universal cofamily is as a universal
-- family on an opposite category.
export
IntUCofamIsUFamOp : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntUCofamObj c) ->
  IntUCofamMor {c} mor dom cod = IntUFamMor {c} (IntOpCatMor c mor) dom cod
IntUCofamIsUFamOp {c} mor dom cod = Refl

public export
icfum : {c : Type} -> {mor : IntDifunctorSig c} -> {dom, cod : IntUCofamObj c} ->
  (onidx : icfuoIdx cod -> icfuoIdx dom) ->
  (onobj : (ci : icfuoIdx cod) ->
    mor (icfuoObj cod ci) (icfuoObj dom $ onidx ci)) ->
  IntUCofamMor {c} mor dom cod
icfum {c} {mor} {dom} {cod} onidx onobj = (onidx ** onobj)

public export
icfumOnIdx : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntUCofamObj c} -> IntUCofamMor {c} mor dom cod ->
  (icfuoIdx cod -> icfuoIdx dom)
icfumOnIdx = DPair.fst

public export
icfumOnObj : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntUCofamObj c} -> (m : IntUCofamMor {c} mor dom cod) ->
  (ci : icfuoIdx cod) ->
  mor (icfuoObj cod ci) (icfuoObj dom $ icfumOnIdx {mor} {dom} {cod} m ci)
icfumOnObj = DPair.snd

public export
icfumId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntUCofamObj c) -> IntUCofamMor mor obj obj
icfumId {c} mor cid =
  IntOpCatId (IntEFamObj c) (IntEFamMor {c} mor) (ifemId {c} mor cid)

public export
icfumComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  {x, y, z : IntUCofamObj c} ->
  IntUCofamMor mor y z ->
  IntUCofamMor mor x y ->
  IntUCofamMor mor x z
icfumComp {c} mor comp {x} {y} {z} =
  IntOpCatComp
    (IntEFamObj c)
    (IntEFamMor {c} mor)
    (\_, _, _ => ifemComp {c} mor comp)
    x y z

public export
UCofamCatSig : IntCatSig -> IntCatSig
UCofamCatSig c =
  ICat
    (IntUCofamObj $ icObj c)
  $ MICS
    (IntUCofamMor {c=(icObj c)} $ icMor c)
  $ ICS
    (icfumId {c=(icObj c)} (icMor c) (icId c))
    (\x, y, z => icfumComp {c=(icObj c)} (icMor c) (icComp c) {x} {y} {z})

---------------------------------------
---------------------------------------
---- Element universal cofamilies -----
---------------------------------------
---------------------------------------

-- Given categories `c` and `d`, a presheaf `f` on `c`, and a functor
-- from the category of elements of `f` to `op(d)`, we can form a functor
-- from `c` to `IntUCofamObj d`.

public export
IntElemUCofamOMap : {c, d : Type} -> (f : IntPreshfSig c) ->
  ((cobj : c) -> f cobj -> d) -> (c -> IntUCofamObj d)
IntElemUCofamOMap {c} {d} f g cobj = (f cobj ** g cobj)

public export
IntElemUCofamFMap : {c, d : Type} ->
  (cmor : IntDifunctorSig c) -> (dmor : IntDifunctorSig d) ->
  (f : IntPreshfSig c) -> (fcm : IntPreshfMapSig c cmor f) ->
  (g : (cobj : c) -> f cobj -> d) ->
  (gm :
    (x : c) -> (y : c) -> (efy : f y) ->
    (mxy : cmor x y) -> dmor (g y efy) (g x $ fcm y x mxy efy)) ->
  (x, y : c) ->
  cmor x y ->
  IntUCofamMor {c=d} dmor
    (IntElemUCofamOMap {c} {d} f g x)
    (IntElemUCofamOMap {c} {d} f g y)
IntElemUCofamFMap {c} {d} cmor dmor f fm g gm x y mxy =
  (fm y x mxy ** \efy => gm x y efy mxy)

----------------------------------------------
----------------------------------------------
---- Universal cofamilies as copresheaves ----
----------------------------------------------
----------------------------------------------

public export
InterpUCofamCopreshfOMap : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntUCofamObj c -> IntCopreshfSig c
InterpUCofamCopreshfOMap c mor (idx ** obj) a = Pi {a=idx} $ flip mor a . obj

public export
InterpUCofamCopreshfFMap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x : IntUCofamObj c) -> IntCopreshfMapSig c mor (InterpUCofamCopreshfOMap c mor x)
InterpUCofamCopreshfFMap c mor comp (idx ** obj) xobj yobj mxy pix =
  \ei : idx => comp (obj ei) xobj yobj mxy (pix ei)

public export
InterpUCofamCopreshfNT :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x, y : IntUCofamObj c) -> (m : IntUCofamMor {c} mor x y) ->
  IntCopreshfNTSig c (InterpUCofamCopreshfOMap c mor x) (InterpUCofamCopreshfOMap c mor y)
InterpUCofamCopreshfNT c mor comp
  (xidx ** xobj) (yidx ** yobj) (midx ** mobj) cobj pix =
    \eyi : yidx =>
     comp (yobj eyi) (xobj $ midx eyi) cobj (pix $ midx eyi) (mobj eyi)

public export
InterpUCofamCopreshfNaturality : FunExt ->
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (assoc : IntAssocSig c mor comp) ->
  (x, y : IntUCofamObj c) -> (m : IntUCofamMor {c} mor x y) ->
  IntCopreshfNTNaturality c mor
    (InterpUCofamCopreshfOMap c mor x)
    (InterpUCofamCopreshfOMap c mor y)
    (InterpUCofamCopreshfFMap c mor comp x)
    (InterpUCofamCopreshfFMap c mor comp y)
    (InterpUCofamCopreshfNT c mor comp x y m)
InterpUCofamCopreshfNaturality fext c mor comp assoc
  (xidx ** xobj) (yidx ** yobj) (midx ** mobj) a b mab pix =
    funExt $
      \eyi =>
        sym $ assoc (yobj eyi) (xobj $ midx eyi) a b
          mab
          (pix $ midx eyi)
          (mobj eyi)

-------------------------------------------
-------------------------------------------
---- Metalanguage universal cofamilies ----
-------------------------------------------
-------------------------------------------

--------------------
---- Definition ----
--------------------

public export
MLUCofamObj : Type
MLUCofamObj = IntUCofamObj Type

public export
MLUCofamMor : MLUCofamObj -> MLUCofamObj -> Type
MLUCofamMor = IntUCofamMor $ HomProf

public export
mlfmId : (x : MLUCofamObj) -> MLUCofamMor x x
mlfmId = icfumId HomProf typeId

public export
mlfmComp : {x, y, z : MLUCofamObj} ->
  MLUCofamMor y z -> MLUCofamMor x y -> MLUCofamMor x z
mlfmComp = icfumComp HomProf (\_, _, _ => (.))

------------------------
---- Interpretation ----
------------------------

-- `InterpMLUCofamObj` and `InterpMLUCofamMorph` comprise a functor from
-- `MLUComfamObj` to `op(Type)`.  It is the opposite functor of
-- `InterpMLEFamObj`/`InterpMLEFamMorph`.

export
InterpMLUCofamObj : MLUCofamObj -> OpTypeObj
InterpMLUCofamObj = InterpMLEFamObj

export
InterpMLUCofamMorph : {x, y : MLUCofamObj} ->
  MLUCofamMor x y -> OpTypeMor (InterpMLUCofamObj x) (InterpMLUCofamObj y)
InterpMLUCofamMorph {x} {y} = InterpMLEFamMorph {x=y} {y=x}

-------------------------------------------------
-------------------------------------------------
---- Metalanguage-slice universal cofamilies ----
-------------------------------------------------
-------------------------------------------------

--------------------
---- Definition ----
--------------------

public export
SliceCofamObj : Type -> Type
SliceCofamObj = IntUCofamObj . SliceObj

public export
SliceUCofamMor : {c : Type} -> SliceCofamObj c -> SliceCofamObj c -> Type
SliceUCofamMor {c} = IntUCofamMor {c=(SliceObj c)} $ SliceMor c

public export
slufmId : {c : Type} ->
  (x : SliceCofamObj c) -> SliceUCofamMor x x
slufmId {c} = icfumId {c=(SliceObj c)} (SliceMor c) (SliceId c)

public export
slufmComp : {c : Type} -> {x, y, z : SliceCofamObj c} ->
  SliceUCofamMor y z -> SliceUCofamMor x y -> SliceUCofamMor x z
slufmComp {c} = icfumComp {c=(SliceObj c)} (SliceMor c) (SliceComp c)

-- `InterpSLUCofamObj` and `InterpSLUCofamMor` comprise a functor from
-- `SliceCofamObj c` to `op(SliceObj c)` (for any `c : Type`).  It is the
-- opposite functor of `InterpSLEFamObj`/`InterpSLEFamMor`.

export
InterpSLUCofamObj : {c : Type} -> SliceCofamObj c -> OpSliceObj c
InterpSLUCofamObj {c} = InterpSLEFamObj {c}

export
InterpSLUCofamMor : {c : Type} -> {x, y : SliceCofamObj c} ->
  SliceUCofamMor {c} x y ->
  OpSliceMor c (InterpSLUCofamObj x) (InterpSLUCofamObj y)
InterpSLUCofamMor {c} {x} {y} = InterpSLEFamMor {c} {x=y} {y=x}
