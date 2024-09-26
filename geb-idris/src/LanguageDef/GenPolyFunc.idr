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

-------------------------------------------
-------------------------------------------
---- Dirichlet/polynomial interactions ----
-------------------------------------------
-------------------------------------------

-----------------------------
---- Left Kan extensions ----
-----------------------------

public export
pdfPrecomp : (q : MLDirichCatObj) -> MLPolyCatObj -> MLDirichCatObj
pdfPrecomp = flip pdfCompositionArena

public export
pdfLKanExtPos : (q : MLDirichCatObj) -> MLDirichCatObj -> Type
pdfLKanExtPos q p = dfPos p

public export
pdfLKanExtDir : (q, p : MLDirichCatObj) -> SliceObj (pdfLKanExtPos q p)
pdfLKanExtDir q p pi = InterpDirichFunc q (pfDir {p} pi)

public export
pdfLKanExt : (q : MLDirichCatObj) -> MLDirichCatObj -> MLPolyCatObj
pdfLKanExt q p = (pdfLKanExtPos q p ** pdfLKanExtDir q p)

public export
pdfLKanUnit : (q : MLDirichCatObj) ->
  (p : MLDirichCatObj) -> DirichNatTrans p (pdfPrecomp q $ pdfLKanExt q p)
pdfLKanUnit q p = (\pi => (pi ** fst) ** \pi, pd, pdqd => snd pdqd pd)

public export
pdfLKanCounit : (q : MLDirichCatObj) ->
  (p : MLPolyCatObj) -> PolyNatTrans (pdfLKanExt q $ pdfPrecomp q p) p
pdfLKanCounit q p = (fst ** \pdqp, qd => (snd pdqp qd ** \pdqd => pdqd qd))

---------------------------------------
---------------------------------------
---- Opposite-category adjunctions ----
---------------------------------------
---------------------------------------

-- The hom-profunctor of `(op(Type), Type)`.
public export
opProdHom : Type -> Type -> Type -> Type -> Type
opProdHom s t a b = (a -> s, t -> b)

public export
opProdHomDimap : {s, t, a, b, s', t', a', b' : Type} ->
  (s -> s') -> (t' -> t) -> (a' -> a) -> (b -> b') ->
  opProdHom s t a b -> opProdHom s' t' a' b'
opProdHomDimap mss' mt't ma'a mbb' (mas, mtb) =
  (mss' . mas . ma'a, mbb' . mtb . mt't)

-- The covariant representable of an object of `(op(Type), Type)`.
public export
opProdCovarRep : Type -> Type -> Type -> Type -> Type
opProdCovarRep = opProdHom

public export
opProdCovarRepMap : {s, t, a, b, a', b' : Type} ->
  (a' -> a) -> (b -> b') ->
  opProdCovarRep s t a b -> opProdCovarRep s t a' b'
opProdCovarRepMap = opProdHomDimap id id

-- The contravariant representable of an object of `(op(Type), Type)`.
public export
opProdContravarRep : Type -> Type -> Type -> Type -> Type
opProdContravarRep s t a b = opProdHom a b s t

public export
opProdContravarRepMap : {s, t, a, b, a', b' : Type} ->
  (a -> a') -> (b' -> b) ->
  opProdContravarRep s t a b -> opProdContravarRep s t a' b'
opProdContravarRepMap maa' mb'b = opProdHomDimap maa' mb'b id id

-------------------------------------------------
-------------------------------------------------
---- Dirichlet slices as polynomial functors ----
-------------------------------------------------
-------------------------------------------------

-- We now show that `MlDirichSlObj` is a (special case of a) signature that
-- we have developed previously: `SPFdepDirType`.
public export
MlDirichSlToSPFDD : {ar : MLArena} ->
  MlDirichSlObj ar -> SPFdepData {b=(pfPos ar)} (snd ar) (const Unit)
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
MLPolySlFibSigma : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> MlPolySlObj p -> MlPolySlObj q
MLPolySlFibSigma q {p} beta sl with (mlPolySlObjToC p sl)
  MLPolySlFibSigma q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    mlPolySlObjFromC q csigma

public export
mlDirichSlSigma : {p : MLDirichCatObj} ->
  (sl : MlDirichSlObj p) -> MlDirichSlFunc (mlDirichSlObjTot {ar=p} sl) p
mlDirichSlSigma {p=(ppos ** pdir)} (MDSobj slpos sldir) (MDSobj totpos totdir) =
  MDSobj
    (\pi => Sigma {a=(slpos pi)} $ curry totpos pi)
    (\pi, pst, pd =>
      Sigma {a=(sldir pi (fst pst) pd)} $ \sld =>
        totdir (pi ** fst pst) (snd pst) (pd ** sld))

public export
mlDirichSlSigmaMap : {p : MLDirichCatObj} ->
  (sl : MlDirichSlObj p) ->
  MlDirichSlFMap {ar=(mlDirichSlObjTot {ar=p} sl)} {ar'=p}
    (mlDirichSlSigma {p} sl)
mlDirichSlSigmaMap {p=(ppos ** pdir)} (MDSobj slpos sldir)
  (MDSobj xpos xdir) (MDSobj ypos ydir) (MDSM monpos mdir) =
    MDSM
      (\pi, psx =>
        (fst psx ** monpos (pi ** fst psx) (snd psx)))
      (\pi, psx, pd, sxd =>
        (fst sxd ** mdir (pi ** fst psx) (snd psx) (pd ** fst sxd) (snd sxd)))

public export
mlDirichSlSigmaPiFL : {p, q : MLDirichCatObj} ->
  (d : MlDirichSlObj (dfParProductArena p q)) -> MlDirichSlFunc q p
mlDirichSlSigmaPiFL {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) =
    MDSobj
      (SliceSigmaPiFL prodpos slpos)
      (\pp, ((qp ** prodp) ** slp), pd =>
        (qd : qdir qp ** (sldir qp slp qd, proddir (pp, qp) prodp (pd, qd))))

public export
mlDirichSlSigmaPiFLMap : {p, q : MLDirichCatObj} ->
  (d : MlDirichSlObj (dfParProductArena p q)) ->
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
  (d : MlDirichSlObj (dfParProductArena p q)) -> MlDirichSlFunc p q
mlDirichSlSigmaPiFR {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) =
    MDSobj
      (SliceSigmaPiFR prodpos slpos)
      (\qp, slp, qd =>
        (pp : ppos) -> (prodp : prodpos (pp, qp)) -> (pd : pdir pp) ->
        (sldir pp (slp (pp ** prodp)) pd, proddir (pp, qp) prodp (pd, qd)))

public export
mlDirichSlSigmaPiFRMap : {p, q : PolyFunc} ->
  (d : MlDirichSlObj (dfParProductArena p q)) ->
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
PRAbase : (cod : MLDirichCatObj) ->
  (pos : MlDirichSlObj cod) -> MLDirichCatObj
PRAbase cod = mlDirichSlObjTot {ar=cod}

public export
PRAdirDom : (dom, cod : MLDirichCatObj) ->
  (pos : MlDirichSlObj cod) -> MLDirichCatObj
PRAdirDom dom cod pos = dfParProductArena dom (PRAbase cod pos)

public export
0 PRAdirType : (0 dom, cod : MLDirichCatObj) ->
  (0 pos : MlDirichSlObj cod) -> Type
PRAdirType dom cod pos = MlDirichSlObj (PRAdirDom dom cod pos)

public export
record PRAData (dom, cod : MLDirichCatObj) where
  constructor PRAD
  pradT1 : MlDirichSlObj cod
  pradET : PRAdirType dom cod pradT1

public export
PRADbase : {dom, cod : MLDirichCatObj} -> PRAData dom cod -> MLDirichCatObj
PRADbase {dom} {cod} prad = PRAbase cod $ pradT1 prad

-- See the formula for `T` in the `Proposition 2.10` section of
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms .
public export
InterpPRAdataOmap : {dom, cod : MLDirichCatObj} ->
  PRAData dom cod -> MlDirichSlFunc dom cod
InterpPRAdataOmap {dom} {cod} prad =
  mlDirichSlSigma {p=cod} (pradT1 prad)
  . mlDirichSlSigmaPiFR {p=dom} {q=(PRADbase {dom} {cod} prad)} (pradET prad)

public export
InterpPRAdataFmap : {dom, cod : MLDirichCatObj} ->
  (prad : PRAData dom cod) ->
  MlDirichSlFMap {ar=dom} {ar'=cod} (InterpPRAdataOmap prad)
InterpPRAdataFmap {dom} {cod} prad x y =
  mlDirichSlSigmaMap {p=cod} (pradT1 prad)
    (mlDirichSlSigmaPiFR (pradET prad) x)
    (mlDirichSlSigmaPiFR (pradET prad) y)
  . mlDirichSlSigmaPiFRMap {p=dom} {q=(PRADbase {dom} {cod} prad)}
    (pradET prad)
    x
    y

-- As with `SPFdirType`, we can make a more dependent version of `PRAdirType`.

public export
PRAdepBase : {b : MLDirichCatObj} -> (codsl : MlDirichSlObj b) ->
  (pos : MlDirichSlOfSl {ar=b} codsl) -> MlDirichSlObj b
PRAdepBase {b} codsl pos = MlDirichBaseSlFromSlOfSl {ar=b} codsl pos

public export
PRAdepDirDom : {b : MLDirichCatObj} -> (domsl, codsl : MlDirichSlObj b) ->
  (pos : MlDirichSlOfSl {ar=b} codsl) -> MlDirichSlObj b
PRAdepDirDom {b} domsl codsl pos =
  dfSlParProduct domsl (PRAdepBase {b} codsl pos)

public export
0 PRAdepDirType : {0 b : MLDirichCatObj} ->
  (0 domsl, codsl : MlDirichSlObj b) -> (0 pos : MlDirichSlOfSl {ar=b} codsl) ->
  Type
PRAdepDirType {b} domsl codsl pos =
  MlDirichSlOfSl {ar=b} $ PRAdepDirDom {b} domsl codsl pos

public export
PRAdirFromDep : {0 b : MLDirichCatObj} ->
  {0 domsl, codsl : MlDirichSlObj b} -> {0 pos : MlDirichSlOfSl {ar=b} codsl} ->
  PRAdepDirType {b} domsl codsl pos ->
  PRAdirType (mlDirichSlObjTot {ar=b} domsl) (mlDirichSlObjTot {ar=b} codsl) pos
PRAdirFromDep {b=(bpos ** bdir)}
  {domsl=(MDSobj dompos domdir)} {codsl=(MDSobj codpos coddir)}
  {pos=(MDSobj pospos posdir)}
  (MDSobj deponpos depdir) =
    MDSobj
      (\((bi ** di), ((bi' ** ci) ** pi)) =>
        Exists {type=(WDiagElem (bi, bi'))} $ \eqb =>
          deponpos (bi ** (di, rewrite WDiagElemEqualizes eqb in (ci ** pi))))
      (\((bi ** di), ((bi' ** ci) ** pi)), (Evidence weqb cpi),
        ((bd ** dd), ((bd' ** cd) ** pd)) =>
          let 0 eqb = WDiagElemEqualizes weqb in
          Exists {type=(WDiagElem (bd, rewrite eqb in bd'))} $ \weqd =>
            let 0 eqd = WDiagElemEqualizes weqd in
            depdir
              (bi ** (di, rewrite eqb in (ci ** pi)))
              cpi
              (bd ** (dd, rewrite eqb in rewrite eqd in (cd ** pd))))

public export
record PRAdepData {b : MLDirichCatObj} (domsl, codsl : MlDirichSlObj b) where
  constructor PRADD
  praddPos : MlDirichSlOfSl {ar=b} codsl
  praddDir : PRAdepDirType {b} domsl codsl praddPos

public export
PRADdepBase : {b : MLDirichCatObj} -> {domsl, codsl : MlDirichSlObj b} ->
  PRAdepData {b} domsl codsl -> MlDirichSlObj b
PRADdepBase {b} {domsl} {codsl} pradd = PRAdepBase {b} codsl $ praddPos pradd

public export
PRAdataFromDep : {b : MLDirichCatObj} -> {domsl, codsl : MlDirichSlObj b} ->
  PRAdepData {b} domsl codsl ->
  PRAData (mlDirichSlObjTot {ar=b} domsl) (mlDirichSlObjTot {ar=b} codsl)
PRAdataFromDep {b} {domsl} {codsl} pradd =
  PRAD
    (praddPos pradd)
    (PRAdirFromDep {b} {domsl} {codsl} {pos=(praddPos pradd)} (praddDir pradd))

public export
InterpPRAdepDataOmap : {b : MLDirichCatObj} ->
  {domsl, codsl : MlDirichSlObj b} ->
  PRAdepData {b} domsl codsl ->
  MlDirichSlFunc (mlDirichSlObjTot {ar=b} domsl) (mlDirichSlObjTot {ar=b} codsl)
InterpPRAdepDataOmap {b} {domsl} {codsl} pradd =
  InterpPRAdataOmap
    {dom=(mlDirichSlObjTot {ar=b} domsl)}
    {cod=(mlDirichSlObjTot {ar=b} codsl)}
    $ PRAdataFromDep {b} {domsl} {codsl} pradd

public export
InterpPRAdepDataFmap : {b : MLDirichCatObj} ->
  {domsl, codsl : MlDirichSlObj b} ->
  (pradd : PRAdepData {b} domsl codsl) ->
  MlDirichSlFMap
    {ar=(mlDirichSlObjTot {ar=b} domsl)}
    {ar'=(mlDirichSlObjTot {ar=b} codsl)}
    (InterpPRAdepDataOmap {b} {domsl} {codsl} pradd)
InterpPRAdepDataFmap {b} {domsl} {codsl} pradd =
  InterpPRAdataFmap
    {dom=(mlDirichSlObjTot {ar=b} domsl)}
    {cod=(mlDirichSlObjTot {ar=b} codsl)}
    $ PRAdataFromDep {b} {domsl} {codsl} pradd
