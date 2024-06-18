module LanguageDef.IntEFamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.IntArena
import public LanguageDef.IntUFamCat

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
IFEO : {c : Type} -> (idx : Type) -> (idx -> c) -> IntEFamObj c
IFEO {c} idx obj = (idx ** obj)

public export
ifeoIdx : {c : Type} -> IntEFamObj c -> Type
ifeoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
ifeoObj : {c : Type} -> (ef : IntEFamObj c) -> ifeoIdx {c} ef -> c
ifeoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

public export
IntEFamMorOnIdx : {c : Type} -> IntDifunctorSig c ->
  IntEFamObj c -> IntEFamObj c -> Type
IntEFamMorOnIdx {c} mor dom cod = ifeoIdx dom -> ifeoIdx cod

public export
IntEFamMorOnMor : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntEFamObj c) -> IntEFamMorOnIdx {c} mor dom cod -> Type
IntEFamMorOnMor {c} mor dom cod imor =
   (di : ifeoIdx dom) -> mor (ifeoObj dom di) (ifeoObj cod $ imor di)

-- The free coproduct completion of a category has the same morphisms as (and
-- hence is equivalent to) the category of Dirichlet functors on the category;
-- we just interpret them differently (meaning, herein we will define a functor
-- from them to `Type`, rather than to `Type -> Type`).

public export
IntEFamMor : {c : Type} -> IntDifunctorSig c ->
  IntEFamObj c -> IntEFamObj c -> Type
IntEFamMor {c} mor dom cod =
  Sigma {a=(IntEFamMorOnIdx {c} mor dom cod)} $ IntEFamMorOnMor {c} mor dom cod

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
IntDirichCatObj : Type -> Type
IntDirichCatObj = IntArena

public export
IntDirichCatMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntDifunctorSig (IntDirichCatObj c)
IntDirichCatMor c = IntEFamMor {c}

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
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
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

public export
EFamCatSig : IntCatSig -> IntCatSig
EFamCatSig c =
  ICat
    (IntEFamObj $ icObj c)
  $ MICS
    (IntEFamMor {c=(icObj c)} $ icMor c)
  $ ICS
    (ifemId {c=(icObj c)} (icMor c) (icId c))
    (\x, y, z => ifemComp {c=(icObj c)} (icMor c) (icComp c) {x} {y} {z})

---------------------------------------
---------------------------------------
---- Element existential families -----
---------------------------------------
---------------------------------------

-- Given categories `c` and `d`, a copresheaf `f` on `c`, and a functor
-- from the category of elements of `f` to `d`, we can form a functor
-- from `c` to `IntEFamObj d`.
--
-- Note that we could dualize the notion of "left multi-adjoint"
-- (and hence "parametric right adjoint") to "right multi-adjoint"
-- (and hence "parametric left adjoint") by treating the inputs
-- here as the data which define a right multi-adjoint, analogously
-- to how we may treat the inputs to `IntElemUFamOMap`/`IntElemUFamFMap`
-- as defining a left multi-adjoint.

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
  (x, y : c) ->
  cmor x y ->
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
IntDNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> IntArena c -> Type
IntDNTar c = IntEFamMor {c}

public export
InterpEFamPreshfOMap : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEFamObj c -> IntPreshfSig c
InterpEFamPreshfOMap c mor x a = Sigma {a=(ifeoIdx x)} $ mor a . ifeoObj x

public export
InterpIDFobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> c -> Type
InterpIDFobj c = InterpEFamPreshfOMap {c}

public export
InterpEFamPreshfFMap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (a : IntEFamObj c) -> IntPreshfMapSig c mor (InterpEFamPreshfOMap c mor a)
InterpEFamPreshfFMap c mor comp a xobj yobj myx =
  dpMapSnd $ \ei, mxi => comp yobj xobj (ifeoObj a ei) mxi myx

public export
InterpIDFmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntArena c) -> IntPreshfMapSig c mor (InterpIDFobj c mor ar)
InterpIDFmap = InterpEFamPreshfFMap

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
InterpIDnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntArena c) -> IntDNTar c mor p q ->
  IntPreshfNTSig c (InterpIDFobj c mor p) (InterpIDFobj c mor q)
InterpIDnt = InterpEFamPreshfNT

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
InterpMLEFamMorph : {x, y : MLEFamObj} ->
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
SliceEFamObj : Type -> Type
SliceEFamObj = IntEFamObj . SliceObj

public export
SliceEFamMor : {c : Type} -> SliceEFamObj c -> SliceEFamObj c -> Type
SliceEFamMor {c} = IntEFamMor {c=(SliceObj c)} $ SliceMorphism {a=c}

public export
slefmId : {c : Type} ->
  (x : SliceEFamObj c) -> SliceEFamMor x x
slefmId {c} = ifemId {c=(SliceObj c)} (SliceMorphism {a=c}) (SliceId c)

public export
slefmComp : {c : Type} -> {x, y, z : SliceEFamObj c} ->
  SliceEFamMor y z -> SliceEFamMor x y -> SliceEFamMor x z
slefmComp {c} = ifemComp (SliceMor c) $ \x, y, z => SliceComp c x y z

-- `InterpSLEFamObj` and `InterpSLEFamMor` comprise a functor from
-- `SliceEFamObj c` to `SliceObj c` (for any `c : Type`).

export
InterpSLEFamObj : {c : Type} -> SliceEFamObj c -> SliceObj c
InterpSLEFamObj {c} (xpos ** xdir) = Sigma {a=xpos} . flip xdir

export
InterpSLEFamMor : {c : Type} -> {x, y : SliceEFamObj c} ->
  SliceEFamMor {c} x y ->
  SliceMorphism {a=c} (InterpSLEFamObj x) (InterpSLEFamObj y)
InterpSLEFamMor {c} {x=(xpos ** xdir)} {y=(ypos ** ydir)} (onpos ** ondir) ec =
  dpBimap onpos (\exp => ondir exp ec)

-------------------------------------
-------------------------------------
---- Dirichlet-functor embedding ----
-------------------------------------
-------------------------------------

-- We can embed a category `c/mor` into its category of Dirichlet functors
-- (sums of representable presheaves) with natural transformations.
public export
IntDirichEmbedObj : (c : Type) -> (a : c) -> IntDirichCatObj c
IntDirichEmbedObj c a = (() ** (\_ : Unit => a))

-- Note that we can _not_ embed a category into its category of polynomial
-- functors (sums of representable copresheaves) with natural transformations,
-- because trying to define this with `IntPNTar` substituted for `IntDNTar`
-- would require us to define a morphism in the opposite direction from `m`.
-- There is no guarantee that such a morphism exists in `c/mor`.
public export
IntDirichEmbedMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  (a, b : c) ->
  mor a b ->
  IntDirichCatMor c mor (IntDirichEmbedObj c a) (IntDirichEmbedObj c b)
IntDirichEmbedMor c mor a b m = ((\_ : Unit => ()) ** (\_ : Unit => m))

-- The inverse of the embedding of a category into its category of
-- Dirichlet functors.  The existence of this inverse shows that
-- the embedding is full and faithful.
public export
IntDirichEmbedMorInv : (c : Type) -> (mor : IntDifunctorSig c) ->
  (a, b : c) ->
  IntDirichCatMor c mor (IntDirichEmbedObj c a) (IntDirichEmbedObj c b) ->
  mor a b
IntDirichEmbedMorInv c mor a b (pos ** dir) =
  -- Note that `pos` has type `Unit -> Unit`, so there is only one thing
  -- it can be, which is the identity on `Unit` (equivalently, the constant
  -- function returning `()`).
  dir ()

------------------------------------------
------------------------------------------
---- Dirichlet categories of elements ----
------------------------------------------
------------------------------------------

public export
DirichCatElemObj : (c : Type) -> (mor : IntDifunctorSig c) -> IntArena c -> Type
DirichCatElemObj c mor p = (x : c ** InterpIDFobj c mor p x)

public export
data DirichCatElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntArena c) ->
    DirichCatElemObj c mor p -> DirichCatElemObj c mor p -> Type where
  DCEM : {c : Type} -> {mor : IntDifunctorSig c} ->
    (comp : IntCompSig c mor) ->
    -- `pos` and `dir` together form an `IntArena c`.
    (pos : Type) -> (dir : pos -> c) ->
    -- `i` and `dm` comprise a term of `InterpIDFobj c mor (pos ** dir) x`;
    -- `x` and `dm` together comprise an object of the slice category
    -- of `dir i`.  `x`, `i`, and `dm` all together comprise an object of
    -- the category of elements of `(pos ** dir)`.
    (x : c) -> (i : pos) -> (dm : mor x (dir i)) ->
    -- `y` and `m` together form an object of the slice category of `x`.
    (y : c) -> (m : mor y x) ->
    DirichCatElemMor c mor comp (pos ** dir)
      (y ** (i ** comp y x (dir i) dm m))
      (x ** (i ** dm))

--------------------------------------------------------------------
--------------------------------------------------------------------
---- Categories of elements of Dirichlet endofunctors on `Type` ----
--------------------------------------------------------------------
--------------------------------------------------------------------

public export
MLDirichCatObj : Type
MLDirichCatObj = IntDirichCatObj Type

public export
MLDirichCatMor : MLDirichCatObj -> MLDirichCatObj -> Type
MLDirichCatMor = IntDirichCatMor Type HomProf

public export
MLDirichCatElemObj : MLDirichCatObj -> Type
MLDirichCatElemObj = DirichCatElemObj Type HomProf

public export
MLDirichCatElemMor : (ar : MLDirichCatObj) ->
  MLDirichCatElemObj ar -> MLDirichCatElemObj ar -> Type
MLDirichCatElemMor = DirichCatElemMor Type HomProf typeComp
