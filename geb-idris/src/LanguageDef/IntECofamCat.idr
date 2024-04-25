module LanguageDef.IntECofamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntUFamCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

public export
IntECofamObj : Type -> Type
IntECofamObj = IntArena

public export
ICFEO : {0 c : Type} -> (idx : Type) -> (idx -> c) -> IntECofamObj c
ICFEO {c} idx obj = (idx ** obj)

public export
icfeoIdx : {0 c : Type} -> IntECofamObj c -> Type
icfeoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
icfeoObj : {0 c : Type} -> (uf : IntECofamObj c) -> icfeoIdx {c} uf -> c
icfeoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

-- Morphisms of the category of existential cofamilies of objects from a given
-- category.  (A "cofamily" of objects from `c` is simply a family of objects
-- from the opposite of `c`; see `IntEFamCat` for the notion of "existential
-- family".)
public export
IntECofamMor : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) -> Type
IntECofamMor {c} mor dom cod =
  (onidx : icfeoIdx dom -> icfeoIdx cod **
   (di : icfeoIdx dom) -> mor (icfeoObj cod $ onidx di) (icfeoObj dom di))

-- Note that this category is the opposite category of
-- the category of universal families (AKA the free cartesian monoidal
-- category).
export
IntECofamIsOpUFam : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) ->
  IntECofamMor {c} mor dom cod =
  IntOpCatMor (IntUFamObj c) (IntUFamMor {c} mor) dom cod
IntECofamIsOpUFam {c} mor dom cod = Refl

-- Note that this category is equivalent to the category of polynomial
-- functors (coproducts of representable copresheaves).
export
IntECofamIsPolyFunc : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntECofamObj c) ->
  IntECofamMor {c} mor dom cod = IntPolyCatMor c mor dom cod
IntECofamIsPolyFunc {c} mor dom cod = Refl

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
  (mor : IntDifunctorSig c) -> (comp : IntComp c mor) ->
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

-----------------------------------------
-----------------------------------------
---- Element existential cofamilies -----
-----------------------------------------
-----------------------------------------

-- Given categories `c` and `d`, a copresheaf `f` on `c`, and a functor
-- to `op(d)` from the category of elements of `f`, we can form a functor
-- from `c` to `IntECofamObj d`.

public export
IntElemECofamMor : {c, d : Type} ->
  (dmor : IntDifunctorSig d) ->
  (f : IntCopreshfSig c) ->
  (g : (cobj : c) -> f cobj -> d) ->
  c -> c -> Type
IntElemECofamMor {c} {d} dmor f g x y =
  IntECofamMor {c=d} dmor (f x ** g x) (f y ** g y)

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
  (x, y : c) -> cmor x y ->
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

export
IntECofamCopreshfOMapIsInterpPolyObj : (c : Type) ->
  (mor : IntDifunctorSig c) ->
  (x : IntECofamObj c) -> (y : c) ->
  InterpECofamCopreshfOMap c mor x y = InterpIPFobj c mor x y
IntECofamCopreshfOMapIsInterpPolyObj c mor (xidx ** xobj) y = Refl

public export
InterpECofamCopreshfFMap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (a : IntECofamObj c) ->
  IntCopreshfMapSig c mor (InterpECofamCopreshfOMap c mor a)
InterpECofamCopreshfFMap c mor comp a xobj yobj myx =
  dpMapSnd $ \ei, mxi => comp (icfeoObj a ei) xobj yobj myx mxi

export
IntECofamCopreshfFMapIsInterpPolyMap : FunExt ->
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (a : IntECofamObj c) -> (x, y : c) -> (m : mor x y) ->
  InterpECofamCopreshfFMap c mor comp a x y m = InterpIPFmap c mor comp a x y m
IntECofamCopreshfFMapIsInterpPolyMap fext c mor comp a x y m =
  funExt $ \_ => Refl

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
IntECofamCopreshfNTisInterpPolyNT : FunExt ->
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (x, y : IntECofamObj c) -> (m : IntECofamMor {c} mor x y) -> (cobj : c) ->
  InterpECofamCopreshfNT c mor comp x y m cobj = InterpIPnt c mor comp x y m cobj
IntECofamCopreshfNTisInterpPolyNT c mor comp x y m cobj fext =
  funExt $ \_ => Refl

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
