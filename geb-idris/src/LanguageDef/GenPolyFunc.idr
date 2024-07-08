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
import public LanguageDef.IntDisheafCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-------------------------------------------------
-------------------------------------------------
---- Dirichlet slices as polynomial functors ----
-------------------------------------------------
-------------------------------------------------

-- We now show that `MlDirichSlObj` is a (special case of a) signature that
-- we have developed previously: `SPFdepDirType`.
public export
MlDirichSlToSPFDD : {ar : MLArena} ->
  MlDirichSlObj ar -> SPFdepData {b=(pfPos ar)} (pfDir {p=ar}) (const Unit)
MlDirichSlToSPFDD {ar} sl =
  SPFDD (\i, () => mdsOnPos sl i) (\ei, () => mdsDir sl ei)

public export
MlDirichSlFromSPFDD : (ar : MLArena) ->
  SPFdepData {b=(pfPos ar)} (pfDir {p=ar}) (const Unit) -> MlDirichSlObj ar
MlDirichSlFromSPFDD ar spfdd =
  MDSobj (flip (spfddPos spfdd) ()) $ \ep => spfddDir spfdd ep ()

-- From the above two translations, we can conclude that for `ar : MLArena`
-- representing a Dirichlet functor, an `MlDirichSlObj ar` -- an object in the
-- slice category of Dirichlet functors over `ar` -- is precisely a polynomial
-- (parametric right adjoint) functor from the slice category of `Type` over
-- the directions of `ar` to `Type` itself (which is equivalent to `Type`
-- sliced over `Unit`), or, put another way, a polynomial copresheaf on the
-- directions of `ar`.

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
  (sl, sl' : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} sl sl' -> MlDirichSlMor {ar=ar'} (f sl) (f sl')

public export
0 MlPolySlFunc : MLArena -> MLArena -> Type
MlPolySlFunc p q = MlPolySlObj p -> MlPolySlObj q

public export
0 MlPolySlFMap : {ar, ar' : MLArena} -> MlPolySlFunc ar ar' -> Type
MlPolySlFMap {ar} {ar'} f =
  (sl, sl' : MlPolySlObj ar) ->
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

public export
mlDirichSlSigmaPiFL : {p, q : PolyFunc} ->
  (d : MlDirichSlObj (pfParProductArena p q)) -> MlDirichSlFunc q p
mlDirichSlSigmaPiFL {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) =
    MDSobj
      (SliceSigmaPiFL prodpos slpos)
      (\pp, ((qp ** prodp) ** slp), pd =>
        (qd : qdir qp ** (sldir qp slp qd, proddir (pp, qp) prodp (pd, qd))))

public export
mlDirichSlSigmaPiFLMap : {p, q : PolyFunc} ->
  (d : MlDirichSlObj (pfParProductArena p q)) ->
  MlDirichSlFMap {ar=q} {ar'=p} (mlDirichSlSigmaPiFL {p} {q} d)
mlDirichSlSigmaPiFLMap {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) (MDSobj slpos' sldir')
  (MDSM monpos mondir) =
    MDSM
      (ssplMap prodpos slpos slpos' monpos)
      (\pp, ((qp ** prodp) ** slp), pd, (qd ** (sld, prodd)) =>
        (qd ** (mondir qp slp qd sld, prodd)))

--------------------------------
---- Pi (dependent product) ----
--------------------------------

public export
mlDirichSlSigmaPiFR : {p, q : PolyFunc} ->
  (d : MlDirichSlObj (pfParProductArena p q)) -> MlDirichSlFunc p q
mlDirichSlSigmaPiFR {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) =
    MDSobj
      (SliceSigmaPiFR prodpos slpos)
      (\qp, slp, qd =>
        (pp : ppos) -> (prodp : prodpos (pp, qp)) -> (pd : pdir pp) ->
        (sldir pp (slp (pp ** prodp)) pd, proddir (pp, qp) prodp (pd, qd)))

public export
mlDirichSlSigmaPiFRMap : {p, q : PolyFunc} ->
  (d : MlDirichSlObj (pfParProductArena p q)) ->
  MlDirichSlFMap {ar=p} {ar'=q} (mlDirichSlSigmaPiFR {p} {q} d)
mlDirichSlSigmaPiFRMap {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) (MDSobj slpos' sldir')
  (MDSM monpos mondir) =
    MDSM
      (ssprMap prodpos slpos slpos' monpos)
      (\qp, slp, qd, dirs, pp, prodp, pd =>
        mapFst (mondir pp (slp (pp ** prodp)) pd) $ dirs pp prodp pd)

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
--
-- We can view this as the generalization of `SPFdirType` in `SlicePolyCat`
-- from slice categories to categories of elements of Dirichlet functors.
-- It is precisely the parameter that we pass to
-- `mlDirichSlSigmaPiFL`/`mlDirichSlSigmaPiFR` to produce the right-adjoint
-- component of the factorization of a PRA functor into a right adjoint
-- followed by a dependent sum.
public export
0 PRAdirType : (0 dom, cod : MLDirichCatObj) ->
  (0 pos : MlDirichSlObj cod) -> Type
PRAdirType dom cod pos =
  MlDirichSlObj (dfParProductArena (mlDirichSlObjTot {ar=cod} pos) dom)

public export
record PRAData (dom, cod : MLDirichCatObj) where
  constructor SPFD
  pradPos : MlDirichSlObj cod
  pradDir : PRAdirType dom cod pradPos

-- As with `SPFdirType`, we can make a more dependent version of `PRAdirType`.
public export
0 PRAdepDirType : {0 b : MLDirichCatObj} ->
  (0 domsl, codsl : MlDirichSlObj b) -> (0 pos : MlDirichSlOfSl {ar=b} codsl) ->
  Type
PRAdepDirType {b} domsl codsl pos =
  MlDirichSlObj
  $ mlDirichSlObjTot {ar=b}
  $ dfSlParProductArena (MlDirichSlFromSlOfSl {ar=b} codsl pos) domsl
