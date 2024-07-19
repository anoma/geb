module LanguageDef.IntECofamCat

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
IntECofamObj : Type -> Type
IntECofamObj = IntArena

public export
ICFEO : {c : Type} -> (idx : Type) -> (idx -> c) -> IntECofamObj c
ICFEO {c} idx obj = (idx ** obj)

public export
icfeoIdx : {c : Type} -> IntECofamObj c -> Type
icfeoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
icfeoObj : {c : Type} -> (uf : IntECofamObj c) -> icfeoIdx {c} uf -> c
icfeoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

public export
IntECofamMorOnIdx : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) -> Type
IntECofamMorOnIdx {c} mor dom cod = icfeoIdx dom -> icfeoIdx cod

public export
IntECofamMorOnMor : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) -> IntECofamMorOnIdx {c} mor dom cod -> Type
IntECofamMorOnMor {c} mor dom cod onidx =
  (di : icfeoIdx dom) -> mor (icfeoObj cod $ onidx di) (icfeoObj dom di)

-- Morphisms of the category of existential cofamilies of objects from a given
-- category.  (A "cofamily" of objects from `c` is simply a family of objects
-- from the opposite of `c`; see `IntEFamCat` for the notion of "existential
-- family".)
public export
IntECofamMor : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) -> Type
IntECofamMor {c} mor dom cod =
  DPair
    (IntECofamMorOnIdx {c} mor dom cod)
    (IntECofamMorOnMor {c} mor dom cod)

-- Note that this category is the opposite category of
-- the category of universal families (AKA the free cartesian monoidal
-- category).
export
IntECofamIsOpUFam : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) ->
  IntECofamMor {c} mor dom cod =
  IntOpCatMor (IntUFamObj c) (IntUFamMor {c} mor) dom cod
IntECofamIsOpUFam {c} mor dom cod = Refl

-- Another way of viewing an existential cofamily is as an existential
-- family on an opposite category.
export
IntECofamIsEFamOp : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) ->
  IntECofamMor {c} mor dom cod = IntEFamMor {c} (IntOpCatMor c mor) dom cod
IntECofamIsEFamOp {c} mor dom cod = Refl

-- The category of existential cofamilies of existential cofamilies of
-- a given category is the same as the category of existential families
-- of universal families of that category.
export
IntECofamECofamIsEFamUFam : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj (IntECofamObj c)) ->
  IntECofamMor {c=(IntECofamObj c)} (IntECofamMor {c} mor) dom cod =
  IntEFamMor {c=(IntUFamObj c)} (IntUFamMor {c} mor) dom cod
IntECofamECofamIsEFamUFam {c} mor dom cod = Refl

public export
IntPolyCatObj : Type -> Type
IntPolyCatObj = IntArena

-- Another way of viewing an existential cofamily is as a category
-- of polynomial functors (coproducts of representable copresheaves).
public export
IntPolyCatMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntDifunctorSig (IntPolyCatObj c)
IntPolyCatMor c = IntECofamMor {c}

public export
icfem : {c : Type} -> {mor : IntDifunctorSig c} -> {dom, cod : IntECofamObj c} ->
  (onidx : icfeoIdx dom -> icfeoIdx cod) ->
  (onobj : (di : icfeoIdx dom) ->
    mor (icfeoObj cod $ onidx di) (icfeoObj dom di)) ->
  IntECofamMor {c} mor dom cod
icfem {c} {mor} {dom} {cod} onidx onobj = (onidx ** onobj)

public export
icfemOnIdx : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntECofamObj c} -> IntECofamMor {c} mor dom cod ->
  (icfeoIdx dom -> icfeoIdx cod)
icfemOnIdx = DPair.fst

public export
icfemOnObj : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntECofamObj c} -> (m : IntECofamMor {c} mor dom cod) ->
  (di : icfeoIdx dom) ->
  mor (icfeoObj cod $ icfemOnIdx {mor} {dom} {cod} m di) (icfeoObj dom di)
icfemOnObj = DPair.snd

public export
icfemId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntECofamObj c) -> IntECofamMor mor obj obj
icfemId {c} mor cid =
  IntOpCatId (IntUFamObj c) (IntUFamMor {c} mor) (ifumId {c} mor cid)

public export
icfemComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  {x, y, z : IntECofamObj c} ->
  IntECofamMor mor y z ->
  IntECofamMor mor x y ->
  IntECofamMor mor x z
icfemComp {c} mor comp {x} {y} {z} =
  IntOpCatComp
    (IntUFamObj c)
    (IntUFamMor {c} mor)
    (\_, _, _ => ifumComp {c} mor comp)
    x y z

public export
ECofamCatSig : IntCatSig -> IntCatSig
ECofamCatSig c =
  ICat
    (IntECofamObj $ icObj c)
  $ MICS
    (IntECofamMor {c=(icObj c)} $ icMor c)
  $ ICS
    (icfemId {c=(icObj c)} (icMor c) (icId c))
    (\x, y, z => icfemComp {c=(icObj c)} (icMor c) (icComp c) {x} {y} {z})

-----------------------------------------
-----------------------------------------
---- Element existential cofamilies -----
-----------------------------------------
-----------------------------------------

-- Given categories `c` and `d`, a copresheaf `f` on `c`, and a functor
-- from the category of elements of `f` to `op(d)`, we can form a functor
-- from `c` to `IntECofamObj d`.

public export
IntElemECofamOMap : {c, d : Type} -> (f : IntCopreshfSig c) ->
  ((cobj : c) -> f cobj -> d) -> (c -> IntECofamObj d)
IntElemECofamOMap {c} {d} f g cobj = (f cobj ** g cobj)

public export
IntElemECofamFMap : {c, d : Type} ->
  (cmor : IntDifunctorSig c) -> (dmor : IntDifunctorSig d) ->
  (f : IntCopreshfSig c) -> (fm : IntCopreshfMapSig c cmor f) ->
  (g : (cobj : c) -> f cobj -> d) ->
  (gm :
    (x : c) -> (y : c) -> (efx : f x) ->
    (mxy : cmor x y) -> dmor (g y $ fm x y mxy efx) (g x efx)) ->
  (x, y : c) ->
  cmor x y ->
  IntECofamMor {c=d} dmor
    (IntElemECofamOMap {c} {d} f g x)
    (IntElemECofamOMap {c} {d} f g y)
IntElemECofamFMap {c} {d} cmor dmor f fm g gm x y mxy =
  (fm x y mxy ** \efy => gm x y efy mxy)

------------------------------------------------
------------------------------------------------
---- Existential cofamilies as copresheaves ----
------------------------------------------------
------------------------------------------------

-- Existential cofamilies can be interpreted as copresheaves, in which
-- form they are precisely the polynomial functors.

public export
InterpECofamCopreshfOMap : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntECofamObj c -> IntCopreshfSig c
InterpECofamCopreshfOMap c mor x a =
  Sigma {a=(icfeoIdx x)} $ flip mor a . icfeoObj x

public export
InterpIPFobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> c -> Type
InterpIPFobj = InterpECofamCopreshfOMap

public export
InterpECofamCopreshfFMap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (a : IntECofamObj c) ->
  IntCopreshfMapSig c mor (InterpECofamCopreshfOMap c mor a)
InterpECofamCopreshfFMap c mor comp a xobj yobj myx =
  dpMapSnd $ \ei, mxi => comp (icfeoObj a ei) xobj yobj myx mxi

public export
InterpIPFmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntArena c) -> IntCopreshfMapSig c mor (InterpIPFobj c mor ar)
InterpIPFmap = InterpECofamCopreshfFMap

public export
InterpECofamCopreshfNT :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x, y : IntECofamObj c) -> (m : IntECofamMor {c} mor x y) ->
  IntCopreshfNTSig c
    (InterpECofamCopreshfOMap c mor x)
    (InterpECofamCopreshfOMap c mor y)
InterpECofamCopreshfNT c mor comp x y m cobj =
  dpBimap (icfemOnIdx {mor} m)
    $ \exi, mcx =>
      comp (icfeoObj y $ icfemOnIdx {mor} m exi) (icfeoObj x exi) cobj
        mcx
        (icfemOnObj {mor} m exi)

public export
IntPNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> IntArena c -> Type
IntPNTar c = IntECofamMor {c}

public export
InterpIPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntArena c) -> IntPNTar c mor p q ->
  IntCopreshfNTSig c (InterpIPFobj c mor p) (InterpIPFobj c mor q)
InterpIPnt = InterpECofamCopreshfNT

public export
InterpECofamCopreshfNaturality :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (assoc : IntAssocSig c mor comp) ->
  (x, y : IntECofamObj c) -> (m : IntECofamMor {c} mor x y) ->
  IntCopreshfNTNaturality c mor
    (InterpECofamCopreshfOMap c mor x)
    (InterpECofamCopreshfOMap c mor y)
    (InterpECofamCopreshfFMap c mor comp x)
    (InterpECofamCopreshfFMap c mor comp y)
    (InterpECofamCopreshfNT c mor comp x y m)
InterpECofamCopreshfNaturality c mor comp assoc
  (xidx ** xobj) (yidx ** yobj) (midx ** mobj) a b mab (exi ** mxa) =
    dpEq12 Refl
      $ sym $ assoc (yobj (midx exi)) (xobj exi) a b mab mxa (mobj exi)

---------------------------------------------
---------------------------------------------
---- Metalanguage existential cofamilies ----
---------------------------------------------
---------------------------------------------

--------------------
---- Definition ----
--------------------

public export
MLECofamObj : Type
MLECofamObj = IntECofamObj Type

public export
MLECofamMor : MLECofamObj -> MLECofamObj -> Type
MLECofamMor = IntECofamMor $ HomProf

public export
mlfmId : (x : MLECofamObj) -> MLECofamMor x x
mlfmId = icfemId HomProf typeId

public export
mlfmComp : {x, y, z : MLECofamObj} ->
  MLECofamMor y z -> MLECofamMor x y -> MLECofamMor x z
mlfmComp = icfemComp HomProf (\_, _, _ => (.))

------------------------
---- Interpretation ----
------------------------

-- `InterpMLECofamObj` and `InterpMLECofamMorph` comprise a functor from
-- `MLEComfamObj` to `op(Type)`.  It is the opposite functor of
-- `InterpMLUFamObj`/`InterpMLUFamMorph`.

export
InterpMLECofamObj : MLECofamObj -> OpTypeObj
InterpMLECofamObj = InterpMLUFamObj

export
InterpMLECofamMorph : {x, y : MLECofamObj} ->
  MLECofamMor x y -> OpTypeMor (InterpMLECofamObj x) (InterpMLECofamObj y)
InterpMLECofamMorph {x} {y} = InterpMLUFamMorph {x=y} {y=x}

---------------------------------------------------
---------------------------------------------------
---- Metalanguage-slice existential cofamilies ----
---------------------------------------------------
---------------------------------------------------

--------------------
---- Definition ----
--------------------

public export
SliceECofamObj : Type -> Type
SliceECofamObj = IntECofamObj . SliceObj

public export
SliceECofamMor : {c : Type} -> SliceECofamObj c -> SliceECofamObj c -> Type
SliceECofamMor {c} = IntECofamMor {c=(SliceObj c)} $ SliceMorphism {a=c}

public export
slufmId : {c : Type} ->
  (x : SliceECofamObj c) -> SliceECofamMor x x
slufmId {c} = icfemId {c=(SliceObj c)} (SliceMorphism {a=c}) (SliceId c)

public export
slufmComp : {c : Type} -> {x, y, z : SliceECofamObj c} ->
  SliceECofamMor y z -> SliceECofamMor x y -> SliceECofamMor x z
slufmComp {c} {x} {y} {z} =
  icfemComp {x} {y} {z} (SliceMorphism {a=c}) $ SliceComp c

-- `InterpSLECofamObj` and `InterpSLECofamMor` comprise a functor from
-- `SliceECofamObj c` to `op(SliceObj c)` (for any `c : Type`).  It is the
-- opposite functor of `InterpSLUFamObj`/`InterpSLEUFamMor`.

export
InterpSLECofamObj : {c : Type} -> SliceECofamObj c -> OpSliceObj c
InterpSLECofamObj {c} = InterpSLUFamObj {c}

export
InterpSLECofamMor : {c : Type} -> {x, y : SliceECofamObj c} ->
  SliceECofamMor {c} x y ->
  OpSliceMor c (InterpSLECofamObj x) (InterpSLECofamObj y)
InterpSLECofamMor {c} {x} {y} = InterpSLUFamMor {c} {x=y} {y=x}

-------------------------------------------
-------------------------------------------
---- Polynomial categories of elements ----
-------------------------------------------
-------------------------------------------

public export
PolyCatElemObj : (c : Type) -> (mor : IntDifunctorSig c) -> IntArena c -> Type
PolyCatElemObj c mor p = (x : c ** InterpIPFobj c mor p x)

-- Unfolding the definition of a morphism in the category of elements
-- specifically of a polynomial endofunctor on `Type` yields the following:
--
--  - A position `i` of the polynomial functor
--  - A pair of types `x`, `y`
--  - An assignment of the directions of `p` at `i` to `x` (together with the
--    type `x`, this can be viewed as an object of the coslice category of
--    the direction-set)
--  - A morphism in `Type` (a function) from `x` to `y`
--
-- One way of looking at all of that together is, if we view a polynomial
-- functor `p` as representing open terms of a data structure, then a morphism
-- of its category of elements is a closed term with elements of `x`
-- substituted for its variables (comprising the type `x` which we then view
-- as a type of variables together with the choice of a position and and
-- assignment of its directions to `x`), together with a function from `x`
-- to `y`, which uniquely determines a closed term with elements of `y`
-- substituted for its variables, by mapping the elements of `x` in the
-- closed term with the chosen function to elements of `y`, while preserving the
-- structure of the term.
--
-- Because of that unique determination, we do not need explicitly to choose
-- the element component of the codomain object, as in the general definition
-- of the category of elements -- the choice of both components of the domain
-- object together with a morphism from its underlying object to some other
-- object of `Type` between them uniquely determine the one codomain object to
-- which there is a corresponding morphism in the category of elements.
public export
data PolyCatElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntArena c) ->
    PolyCatElemObj c mor p -> PolyCatElemObj c mor p -> Type where
  PCEM : {c : Type} -> {mor : IntDifunctorSig c} ->
    (comp : IntCompSig c mor) ->
    -- `pos` and `dir` together form an `IntArena c`.
    (pos : Type) -> (dir : pos -> c) ->
    -- `i` and `dm` comprise a term of `InterpIPFobj c mor (pos ** dir) x`;
    -- `x` and `dm` together comprise an object of the coslice category
    -- of `dir i`.  `x`, `i`, and `dm` all together comprise an object of
    -- the category of elements of `(pos ** dir)`.
    (x : c) -> (i : pos) -> (dm : mor (dir i) x) ->
    -- `y` and `m` together form an object of the coslice category of `x`.
    (y : c) -> (m : mor x y) ->
    PolyCatElemMor c mor comp (pos ** dir)
      (x ** (i ** dm))
      (y ** (i ** comp (dir i) x y m dm))

public export
pcemMor :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (p : IntArena c) ->
  (x, y : PolyCatElemObj c mor p) ->
  PolyCatElemMor c mor comp p x y ->
  mor (fst x) (fst y)
pcemMor _ _ _ _ _ _ (PCEM _ _ _ _ _ _ _ m) = m

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Categories of elements of polynomial endofunctors on `Type` ----
---------------------------------------------------------------------
---------------------------------------------------------------------

public export
MLPolyCatObj : Type
MLPolyCatObj = IntPolyCatObj Type

public export
MLPolyCatMor : MLPolyCatObj -> MLPolyCatObj -> Type
MLPolyCatMor = IntPolyCatMor Type HomProf

public export
MLPolyCatElemObj : MLPolyCatObj -> Type
MLPolyCatElemObj = PolyCatElemObj Type HomProf

public export
MLPolyCatElemMor : (p : MLPolyCatObj) -> (x, y : MLPolyCatElemObj p) -> Type
MLPolyCatElemMor = PolyCatElemMor Type HomProf typeComp
