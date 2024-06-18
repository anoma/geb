module LanguageDef.GenPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.QType
import public LanguageDef.PolyCat
import public LanguageDef.SliceFuncCat
import public LanguageDef.SlicePolyCat
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntUFamCat
import public LanguageDef.IntUCofamCat
import public LanguageDef.IntEFamCat
import public LanguageDef.IntECofamCat
import public LanguageDef.PolySliceCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-----------------------------------------
-----------------------------------------
---- Polynomial double-Yoneda lemmas ----
-----------------------------------------
-----------------------------------------

----------------------------------------
---- Polynomial-polynomial category ----
----------------------------------------

public export
PolyPolyCat : IntCatSig -> IntCatSig
PolyPolyCat cat = ECofamCatSig (ECofamCatSig cat)

public export
PolyPolyObj : IntCatSig -> Type
PolyPolyObj cat = icObj (PolyPolyCat cat)

public export
PolyPolyMorOnIdx : (cat : IntCatSig) -> IntMorSig (PolyPolyObj cat)
PolyPolyMorOnIdx cat = IntECofamMorOnIdx (icMor $ ECofamCatSig cat)

public export
PolyPolyMorOnMor : (cat : IntCatSig) -> (dom, cod : PolyPolyObj cat) ->
  PolyPolyMorOnIdx cat dom cod -> Type
PolyPolyMorOnMor cat = IntECofamMorOnMor (icMor $ ECofamCatSig cat)

public export
PolyPolyMor : (cat : IntCatSig) -> IntMorSig (PolyPolyObj cat)
PolyPolyMor cat = icMor (PolyPolyCat cat)

----------------------------------
---- Polynomial apply functor ----
----------------------------------

public export
PolyAppFunc : (cat : IntCatSig) -> icObj cat -> (PolyPolyObj cat)
PolyAppFunc cat a =
  ((b : icObj cat ** icMor cat b a) ** \ai => (() ** \() => fst ai))

public export
PolyAppToInterp : (cat : IntCatSig) ->
  (a : icObj cat) -> (p : IntECofamObj $ icObj cat) ->
  InterpECofamCopreshfOMap
    (IntECofamObj $ icObj cat)
    (IntECofamMor $ icMor cat)
    (PolyAppFunc cat a) p ->
  InterpECofamCopreshfOMap (icObj cat) (icMor cat) p a
PolyAppToInterp cat a (pos ** dir) (appPos ** onPos ** onDir) =
  (onPos () **
   icComp cat (dir $ onPos ()) (fst appPos) a (snd appPos) (onDir ()))

public export
PolyAppFromInterp : (cat : IntCatSig) ->
  (a : icObj cat) -> (p : IntECofamObj $ icObj cat) ->
  InterpECofamCopreshfOMap (icObj cat) (icMor cat) p a ->
  InterpECofamCopreshfOMap
    (IntECofamObj $ icObj cat)
    (IntECofamMor $ icMor cat)
    (PolyAppFunc cat a) p
PolyAppFromInterp cat a (pos ** dir) (i ** dm) =
  ((dir i ** dm) ** (const i ** \() => icId cat $ dir i))

--------------------------------------------------
---- Polynomial covariant double-Yoneda lemma ----
--------------------------------------------------

public export
record PolyDoubleYo (cat : IntCatSig) (a, b : icObj cat) where
  constructor MkPolyDoubleYo
  PolyDoubleYoEmbed :
    PolyPolyMor cat (PolyAppFunc cat a) (PolyAppFunc cat b)

public export
PolyDoubleYoOnIdx : {cat : IntCatSig} -> {a, b : icObj cat} ->
  PolyDoubleYo cat a b ->
  PolyPolyMorOnIdx cat (PolyAppFunc cat a) (PolyAppFunc cat b)
PolyDoubleYoOnIdx {cat} {a} {b} (MkPolyDoubleYo (onpos ** ondir)) = onpos

public export
PolyDoubleYoOnMor : {cat : IntCatSig} -> {a, b : icObj cat} ->
  (y : PolyDoubleYo cat a b) ->
  PolyPolyMorOnMor cat (PolyAppFunc cat a) (PolyAppFunc cat b)
    (PolyDoubleYoOnIdx {cat} {a} {b} y)
PolyDoubleYoOnMor {cat} {a} {b} (MkPolyDoubleYo (onpos ** ondir)) = ondir

public export
PolyDoubleYoDimapOnIdx : (cat : IntCatSig) ->
  (s, t, a, b : icObj cat) -> icMor cat a s -> icMor cat t b ->
  PolyDoubleYo cat s t ->
  PolyPolyMorOnIdx cat (PolyAppFunc cat a) (PolyAppFunc cat b)
PolyDoubleYoDimapOnIdx cat s t a b mas mtb (MkPolyDoubleYo (onpos ** ondir))
  (i ** mia) =
    case (onpos (i ** icComp cat i a s mas mia)) of
      (op1 ** op2) => (op1 ** icComp cat op1 t b mtb op2)

public export
PolyDoubleYoDimapOnMor : (cat : IntCatSig) ->
  (s, t, a, b : icObj cat) -> (mas : icMor cat a s) -> (mtb : icMor cat t b) ->
  (y : PolyDoubleYo cat s t) ->
  PolyPolyMorOnMor cat (PolyAppFunc cat a) (PolyAppFunc cat b)
    (PolyDoubleYoDimapOnIdx cat s t a b mas mtb y)
PolyDoubleYoDimapOnMor cat s t a b mas mtb (MkPolyDoubleYo (onpos ** ondir))
    (i ** mia) with
    (onpos (i ** icComp cat i a s mas mia),
     ondir (i ** icComp cat i a s mas mia)) proof odeq
  PolyDoubleYoDimapOnMor cat s t a b mas mtb (MkPolyDoubleYo (onpos ** ondir))
    (i ** mia) | ((op1 ** op2), (od1 ** od2)) with (od2 ()) proof ueq
      PolyDoubleYoDimapOnMor cat s t a b mas mtb
          (MkPolyDoubleYo (onpos ** ondir)) (i ** mia)
          | ((op1 ** op2), (od1 ** od2)) | od2u with (od1 ())
        PolyDoubleYoDimapOnMor cat s t a b mas mtb
          (MkPolyDoubleYo (onpos ** ondir)) (i ** mia)
          | ((op1 ** op2), (od1 ** od2)) | od2u | () =
            (\() => () **
             \() =>
              rewrite fstEq odeq in rewrite sym (dpeq1 (fstEq odeq)) in od2u)

public export
PolyDoubleYoDimap : (cat : IntCatSig) ->
  IntEndoDimapSig (icObj cat) (icMor cat) (PolyDoubleYo cat)
PolyDoubleYoDimap cat s t a b mas mtb y =
  MkPolyDoubleYo
    (PolyDoubleYoDimapOnIdx cat s t a b mas mtb y **
     PolyDoubleYoDimapOnMor cat s t a b mas mtb y)

public export
toDoubleYo : (cat : IntCatSig) ->
  IntEndoProfNTSig (icObj cat) (icMor cat) (PolyDoubleYo cat)
toDoubleYo cat x y mxy =
  MkPolyDoubleYo
    (\(i ** mix) => (i ** icComp cat i x y mxy mix) **
     \(i ** mix) => (\() => () ** \() => icId cat i))

public export
fromDoubleYo : (cat : IntCatSig) ->
  IntEndoProfNTSig (icObj cat) (PolyDoubleYo cat) (icMor cat)
fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) with
    (ondir (x ** icId cat x))
  fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
      ((od1 ** od2)) with (od2 ())
    fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
        ((od1 ** od2)) | od2u with (od1 ())
      fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
          ((od1 ** od2)) | od2u | () with (onpos (x ** icId cat x))
        fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
          (od1 ** od2) | od2u | () | (op1 ** op2) =
            icComp cat x op1 y op2 od2u

------------------------------------------------------------
---- Polynomial covariant double-Yoneda lemma in `Type` ----
------------------------------------------------------------

public export
ECofamType : IntCatSig
ECofamType = ECofamCatSig TypeCat

public export
ECofamPolyType : IntCatSig
ECofamPolyType = ECofamCatSig ECofamType

public export
PolyTypeDoubleYo : Type -> Type -> Type
PolyTypeDoubleYo = PolyDoubleYo TypeCat

public export
PolyTypeDoubleYoDimap : IntEndoDimapSig Type TypeMor PolyTypeDoubleYo
PolyTypeDoubleYoDimap = PolyDoubleYoDimap TypeCat

public export
toDoubleYoType : ProfNT HomProf PolyTypeDoubleYo
toDoubleYoType {a} {b} = toDoubleYo TypeCat a b

public export
fromDoubleYoType : ProfNT PolyTypeDoubleYo HomProf
fromDoubleYoType {a} {b} = fromDoubleYo TypeCat a b

------------------------------------------------------
------------------------------------------------------
---- Categories of elements of Dirichlet functors ----
------------------------------------------------------
------------------------------------------------------

-- This definition makes it explicit that that the category of elements of a
-- Dirichlet endofunctor on `Type` is (equivalent to) the (indexed) coproduct
-- category over the positions of the slice categories over the directions.
-- (For a polynomial endofunctor on `Type`, the corresponding statement would
-- hold with "slice" replaced by "coslice".)

public export
DirichCatElObj : PolyFunc -> Type
DirichCatElObj p = (i : pfPos p ** SliceObj $ pfDir {p} i)

public export
DirichCatElBaseT : (p : PolyFunc) -> DirichCatElObj p -> Type
DirichCatElBaseT p el = Sigma {a=(pfDir {p} (fst el))} (snd el)

public export
DirichCatElPosMor : (p : PolyFunc) -> (i : pfPos p) ->
  IntMorSig (SliceObj $ pfDir {p} i)
DirichCatElPosMor p i = SliceMorphism {a=(pfDir {p} i)}

public export
DirichCatElMorTot : PolyFunc -> Type
DirichCatElMorTot p =
  (i : pfPos p **
   xy : ProductMonad $ SliceObj $ pfDir {p} i **
   DirichCatElPosMor p i (fst xy) (snd xy))

public export
DirichCatElMorPos : {p : PolyFunc} -> DirichCatElMorTot p -> pfPos p
DirichCatElMorPos {p} m = fst m

public export
DirichCatElMorSig : {p : PolyFunc} ->
  (m : DirichCatElMorTot p) ->
  ProductMonad (SliceObj $ pfDir {p} $ DirichCatElMorPos {p} m)
DirichCatElMorSig {p} m = fst $ snd m

public export
DirichCatElMorDom : {p : PolyFunc} ->
  (m : DirichCatElMorTot p) -> SliceObj $ pfDir {p} $ DirichCatElMorPos {p} m
DirichCatElMorDom {p} m = fst $ DirichCatElMorSig {p} m

public export
DirichCatElMorCod : {p : PolyFunc} ->
  (m : DirichCatElMorTot p) -> SliceObj $ pfDir {p} $ DirichCatElMorPos {p} m
DirichCatElMorCod {p} m = snd $ DirichCatElMorSig {p} m

public export
DirichCatElMorMor : {p : PolyFunc} ->
  (m : DirichCatElMorTot p) ->
  SliceMorphism {a=(pfDir {p} $ DirichCatElMorPos {p} m)}
    (DirichCatElMorDom {p} m)
    (DirichCatElMorCod {p} m)
DirichCatElMorMor {p} m = snd $ snd m

public export
data DirichCatElMor : (p : PolyFunc) -> IntMorSig (DirichCatElObj p) where
  DCEM : {p : PolyFunc} ->
    (m : DirichCatElMorTot p) ->
    DirichCatElMor p
      (DirichCatElMorPos {p} m ** DirichCatElMorDom {p} m)
      (DirichCatElMorPos {p} m ** DirichCatElMorCod {p} m)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- PRA functors between slice categories of Dirichlet/polynomial functors ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

------------------------------------------------------
---- Polynomial-functor slice functor definitions ----
------------------------------------------------------

public export
0 MlDirichSlFunc : MLArena -> MLArena -> Type
MlDirichSlFunc p q = MlDirichSlObj p -> MlDirichSlObj q

public export
0 MlDirichSlFMap : {ar, ar' : MLArena} -> MlDirichSlFunc ar ar' -> Type
MlDirichSlFMap {ar} {ar'} f =
  (0 sl, sl' : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} sl sl' -> MlDirichSlMor {ar=ar'} (f sl) (f sl')

public export
0 MlPolySlFunc : MLArena -> MLArena -> Type
MlPolySlFunc p q = MlPolySlObj p -> MlPolySlObj q

public export
0 MlPolySlFMap : {ar, ar' : MLArena} -> MlPolySlFunc ar ar' -> Type
MlPolySlFMap {ar} {ar'} f =
  (0 sl, sl' : MlPolySlObj ar) ->
  MlPolySlMor {ar} sl sl' -> MlPolySlMor {ar=ar'} (f sl) (f sl')

---------------------
---- Base change ----
---------------------

public export
mlDirichSlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlDirichSlFunc p q
mlDirichSlBaseChange {p} {q} (onpos ** ondir) (MDSobj slpos sldir) =
  MDSobj (slpos . onpos) (\qp, sp, qd => sldir (onpos qp) sp $ ondir qp qd)

public export
mlDirichSlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlDirichSlFMap {ar=p} {ar'=q} (mlDirichSlBaseChange {p} {q} nt)
mlDirichSlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MDSobj dpos ddir) (MDSobj cpos cdir) (MDSM monpos mondir) =
    MDSM
      (\qp, dp => monpos (ntonpos qp) dp)
      (\qp, dp, qd, dd => mondir (ntonpos qp) dp (ntondir qp qd) dd)

-- When we express slice objects over a polynomial functor as fibrations
-- rather than total-space objects with projection morphisms, we can perform
-- base changes by specifying the data not of a polynomial natural
-- transformation, but of a Dirichlet natural transformation.
public export
mlPolySlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlPolySlFunc p q
mlPolySlBaseChange {p} {q} (onpos ** ondir) (MPSobj slonpos sldir slondir) =
  MPSobj
    (slonpos . onpos)
    (\i => sldir $ onpos i)
    (\i, j, qd => slondir (onpos i) j $ ondir i qd)

public export
mlPolySlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlPolySlFMap {ar=p} {ar'=q} (mlPolySlBaseChange {p} {q} nt)
mlPolySlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MPSobj dpos ddir dondir) (MPSobj cpos cdir condir) m =
    MPSM
      (\qp => mpsmOnPos m (ntonpos qp))
      (\qp, dp, cd => mpsmOnDir m (ntonpos qp) dp cd)
      (\qp, dp, bd => mpsmOnDirCommutes m (ntonpos qp) dp (ntondir qp bd))

-------------------------------
---- Sigma (dependent sum) ----
-------------------------------

public export
MLPolySlSigma : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> MlPolySlObj p -> MlPolySlObj q
MLPolySlSigma q {p} beta sl with (mlPolySlObjToC p sl)
  MLPolySlSigma q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    mlPolySlObjFromC q csigma

----------------------------
---- General polynomial ----
----------------------------

-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms
-- describes how a PRA functor between presheaf categories is determined
-- by two pieces of data which it calls `T1` and `E_T`.  It refers to
-- general presheaf categories over categories it calls `I` and `J`.
--
-- Here we are considering PRA functors between slice categories of Dirichlet
-- functors.  The slice category of Dirichlet functors over a Dirichlet
-- functor `p` is equivalent to the category of presheaves over its category
-- of elements.  Hence, we can determine a PRA (polynomial) functor between
-- slice categories over Dirichlet functors `p` and `q` by specifying `T1`
-- and `E_T` where `I` is the category of elements of `p` and `J` is the
-- category of elements of `q`.
--
-- `T1` is simply an object of the codomain (specifically, the presheaf over
-- `J` to which we shall map the terminal presheaf over `I`), so it is an
-- object of the category of Dirichlet functors sliced over `q` (equivalently,
-- an object of the category of presheaves over the category of elements of
-- `q`).
--
-- `E_T`, given a `T1`, is a functor from the category of elements of `T1`
-- (which makes sense because `T1` is itself a presheaf) to the category of
-- presheaves over `I` (which is the domain of the PRA functor).
