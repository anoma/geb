module LanguageDef.MLDiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.SlicePolyCat
import public LanguageDef.DiPolyFunc

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-- Dipolynomial functors in Idris's metalanguage(s).

-------------------------------
-------------------------------
---- Objects and morphisms ----
-------------------------------
-------------------------------

public export
MLPolyDiSig : Type
MLPolyDiSig = PolyDiSig Type

public export
mlpdPos : MLPolyDiSig -> Type
mlpdPos = pdPos {c=Type}

public export
mlpdDirL : (pd : MLPolyDiSig) -> mlpdPos pd -> Type
mlpdDirL = pdDirL {c=Type}

public export
mlpdDirR : (pd : MLPolyDiSig) -> mlpdPos pd -> Type
mlpdDirR = pdDirR {c=Type}

public export
RepMLPolyDi : (x, y : Type) -> MLPolyDiSig
RepMLPolyDi = RepPolyDi {c=Type}

public export
InterpMLPolyDi : MLPolyDiSig -> IntDifunctorSig Type
InterpMLPolyDi = InterpPolyDi {c=Type} TypeMor

public export
InterpMLPolyDiDiag : MLPolyDiSig -> Type -> Type
InterpMLPolyDiDiag = InterpPolyDiDiag {c=Type} TypeMor

public export
mlipdPos : {p : MLPolyDiSig} ->
  {x, y : Type} -> InterpMLPolyDi p x y -> mlpdPos p
mlipdPos = ipdPos {c=Type} {mor=TypeMor}

public export
mlipdDirL : {p : MLPolyDiSig} ->
  {x, y : Type} -> (ipd : InterpMLPolyDi p x y) ->
  x -> mlpdDirL p (mlipdPos {p} {x} {y} ipd)
mlipdDirL = ipdDirL {c=Type} {mor=TypeMor}

public export
mlipdDirR : {p : MLPolyDiSig} ->
  {x, y : Type} -> (ipd : InterpMLPolyDi p x y) ->
  mlpdDirR p (mlipdPos {p} {x} {y} ipd) -> y
mlipdDirR = ipdDirR {c=Type} {mor=TypeMor}

public export
MLPDiagObj : MLPolyDiSig -> Type
MLPDiagObj = PolyDiagElemObj {c=Type} TypeMor

public export
mlpdeObj : {p : MLPolyDiSig} -> MLPDiagObj p -> Type
mlpdeObj = pdeObj {c=Type} {mor=TypeMor}

public export
mlpdeEl : {p : MLPolyDiSig} -> (el : MLPDiagObj p) ->
  InterpMLPolyDiDiag p (mlpdeObj {p} el)
mlpdeEl = pdeEl {c=Type} {mor=TypeMor}

public export
MLPDiagMor : {p : MLPolyDiSig} -> IntMorSig (MLPDiagObj p)
MLPDiagMor {p} = PolyDiagElemMor {c=Type} {mor=TypeMor} {comp=typeComp} {p}

public export
mlpdeMor : {p : MLPolyDiSig} -> {x, y : MLPDiagObj p} ->
  MLPDiagMor {p} x y -> mlpdeObj {p} x -> mlpdeObj {p} y
mlpdeMor = pdeMor {c=Type} {mor=TypeMor}

public export
mlpdeCrossEl :
  {p : MLPolyDiSig} -> {x, y : MLPDiagObj p} ->
  MLPDiagMor {p} x y -> InterpMLPolyDi p (mlpdeObj {p} y) (mlpdeObj {p} x)
mlpdeCrossEl = pdeCrossEl {c=Type} {mor=TypeMor}

public export
InterpMLPolyLmap : (p : MLPolyDiSig) ->
  IntEndoLmapSig Type TypeMor (InterpMLPolyDi p)
InterpMLPolyLmap = InterpPolyLmap {c=Type} {mor=TypeMor} typeComp

public export
InterpMLPolyRmap : (p : MLPolyDiSig) ->
  IntEndoRmapSig Type TypeMor (InterpMLPolyDi p)
InterpMLPolyRmap = InterpPolyRmap {c=Type} {mor=TypeMor} typeComp

public export
InterpMLPolyDimap : (p : MLPolyDiSig) ->
  IntEndoDimapSig Type TypeMor (InterpMLPolyDi p)
InterpMLPolyDimap = InterpPolyDimap {c=Type} {mor=TypeMor} typeComp

public export
MLPPNTonPos : (p, q : MLPolyDiSig) -> Type
MLPPNTonPos = PPNTonPos {c=Type} {mor=TypeMor}

public export
MLPPNTonL : (p, q : MLPolyDiSig) -> MLPPNTonPos p q -> Type
MLPPNTonL = PPNTonL {c=Type} {mor=TypeMor}

public export
MLPPNTonR : (p, q : MLPolyDiSig) -> MLPPNTonPos p q -> Type
MLPPNTonR = PPNTonR {c=Type} {mor=TypeMor}

public export
MLPolyParaNT : IntMorSig MLPolyDiSig
MLPolyParaNT = PolyParaNT {c=Type} TypeMor

public export
mlppntOnPos : {p, q : MLPolyDiSig} -> MLPolyParaNT p q -> MLPPNTonPos p q
mlppntOnPos = ppntOnPos {c=Type} {mor=TypeMor}

public export
mlppntOnL : {p, q : MLPolyDiSig} -> (nt : MLPolyParaNT p q) ->
  MLPPNTonL p q (mlppntOnPos {p} {q} nt)
mlppntOnL = ppntOnL {c=Type} {mor=TypeMor}

public export
mlppntOnR : {p, q : MLPolyDiSig} -> (nt : MLPolyParaNT p q) ->
  MLPPNTonR p q (mlppntOnPos {p} {q} nt)
mlppntOnR = ppntOnR {c=Type} {mor=TypeMor}

public export
0 MLParaNTinterp : (p, q : MLPolyDiSig) -> Type
MLParaNTinterp p q = TypeProfDiNT (InterpMLPolyDi p) (InterpMLPolyDi q)

public export
InterpMLPolyParaNT : {p, q : MLPolyDiSig} ->
  MLPolyParaNT p q -> MLParaNTinterp p q
InterpMLPolyParaNT = InterpPolyParaNT {c=Type} {mor=TypeMor} typeComp

-----------------------------------------
-----------------------------------------
---- Correctness/completeness proofs ----
-----------------------------------------
-----------------------------------------

------------------------
---- Paranaturality ----
------------------------

-- Here we show that our interpretation of a polynomial "paranatural" arena
-- is indeed paranatural.

public export
0 MLPolyParanaturality : {p, q : MLPolyDiSig} ->
  (nt : MLParaNTinterp p q) -> Type
MLPolyParanaturality {p} {q} =
  IntParaNTCond Type TypeMor
    (InterpMLPolyDi p) (InterpMLPolyDi q)
    (InterpMLPolyLmap p) (InterpMLPolyRmap p)
    (InterpMLPolyLmap q) (InterpMLPolyRmap q)

public export
0 MLPolyParaNTisParanatural : {p, q : MLPolyDiSig} ->
  (nt : MLPolyParaNT p q) ->
  MLPolyParanaturality {p} {q} (InterpMLPolyParaNT {p} {q} nt)
MLPolyParaNTisParanatural =
  PolyParaNTisParanatural {c=Type} {mor=TypeMor} typeComp typeAssoc

-- Here we show that our representation of paranatural transformations
-- as arenas is complete -- that is, for any paranatural transformation
-- that we can write in the metalanguage, we can derive an arena whose
-- interpretation is the given transformation.

public export
0 MLPolyParaArFromParaNT : (p, q : MLPolyDiSig) ->
  (gamma : MLParaNTinterp p q) ->
  MLPolyParanaturality {p} {q} gamma -> MLPolyParaNT p q
MLPolyParaArFromParaNT p@(ppos ** (pdirL, pdirR)) q@(qpos ** (qdirL, qdirR))
  gamma cond =
    (\pi, asn =>
      mlipdPos {p=q} (gamma (pdirL pi) (pi ** (asn, id))) **
     (\pi, asn, pdr =>
        rewrite
          sym $ dpeq1 $ cond (pdirL pi) (pdirR pi) asn
            (pi ** (asn, id))
            (pi ** (id, asn))
            Refl
        in
        mlipdDirL {p=q} (gamma (pdirR pi) (pi ** (id, asn))) pdr,
      \pi, asn =>
        mlipdDirR {p=q} (gamma (pdirL pi) (pi ** (asn, id)))))

public export
0 MLPolyParaArCompleteFst :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  (i : InterpMLPolyDiDiag p x) ->
    mlipdPos {p=q} (gamma x i) =
    mlipdPos {p=q}
      (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x i)
MLPolyParaArCompleteFst (ppos ** (pdirL, pdirR)) (qpos ** (qdirL, qdirR))
  gamma cond x (pi ** (dmr, dml)) =
    rewrite
      dpeq1 $
        cond (pdirL pi) x dml (pi ** (dmr . dml, id)) (pi ** (dmr, dml)) Refl
    in
    Refl

public export
0 MLPolyParaArCompleteL :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  (i : InterpMLPolyDiDiag p x) ->
    (mlipdDirL {p=q} (gamma x i)) =
    (rewrite MLPolyParaArCompleteFst p q gamma cond x i in
     mlipdDirL {p=q}
      (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x i))
MLPolyParaArCompleteL (ppos ** (pdirL, pdirR)) (qpos ** (qdirL, qdirR))
  gamma cond x (pi ** (dmr, dml)) =
    let
      condapp =
        cond x (pdirR pi) dmr (pi ** (dmr, dml)) (pi ** (id, dmr . dml)) Refl
    in
    trans
      (sym $
        bimapIdL1 {g=((.) dmr)} {eac=(((gamma x (pi ** (dmr, dml))) .snd))})
    $ rewrite sym (fstEqHetTy $ dpeq2 condapp) in
      trans (sym $ fstEqHet $ dpeq2 condapp) bimapIdR1

public export
0 MLPolyParaArCompleteR :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  (i : InterpMLPolyDiDiag p x) ->
    (mlipdDirR {p=q} (gamma x i)) =
    (rewrite MLPolyParaArCompleteFst p q gamma cond x i in
     mlipdDirR {p=q}
      (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x i))
MLPolyParaArCompleteR (ppos ** (pdirL, pdirR)) (qpos ** (qdirL, qdirR))
  gamma cond x (pi ** (dmr, dml)) =
    let
      condapp =
        cond (pdirL pi) x dml (pi ** (dmr . dml, id)) (pi ** (dmr, dml)) Refl
    in
    trans (sym $
      bimapIdR2 {f=((|>) dml)} {ead=(((gamma x (pi ** (dmr, dml))) .snd))})
    $
      trans
        (sndEqHet $ dpeq2 condapp)
        (rewrite (sndEqHetTy $ dpeq2 condapp) in
         bimapIdL2
          {g=((.) dml)}
          {eac=((gamma (pdirL pi) (pi ** (\x => dmr (dml x), id))) .snd)})

public export
0 MLPolyParaArComplete :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  ExtEq {a=(InterpMLPolyDiDiag p x)} {b=(InterpMLPolyDiDiag q x)}
    (gamma x)
    (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x)
MLPolyParaArComplete p@(ppos ** (pdirL, pdirR)) q@(qpos ** (qdirL, qdirR))
  gamma cond x i@(pi ** (dmr, dml)) =
    rewrite sym $ MLPolyParaArCompleteFst p q gamma cond x i in
    rewrite sym $ MLPolyParaArCompleteL p q gamma cond x i in
    rewrite dpEqPat {dp=(gamma x (pi ** (dmr, dml)))} in
    dpEq12
      Refl
    $ rewrite pairFstSnd (snd $ gamma x (pi ** (dmr, dml))) in
      pairEqCong Refl (MLPolyParaArCompleteR p q gamma cond x i)

----------------------------------------------------------------
----------------------------------------------------------------
---- Paranatural transformations as natural transformations ----
----------------------------------------------------------------
----------------------------------------------------------------

public export
MLPolyParaAsNatTrans :
  {p, q : MLPolyDiSig} -> (gamma : MLPolyParaNT p q) ->
  TwArrPreshfEmbeddingNT (InterpMLPolyDi p) (InterpMLPolyDi q)
MLPolyParaAsNatTrans {p=(ppos ** (pdirL, pdirR))} {q=(qpos ** (qdirL, qdirR))}
  (onpos ** (onL, onR)) x y myx (pi ** (pdmR, pdmL)) =
    let asn = pdmR . myx . pdmL in
    (onpos pi asn **
     (onL pi asn . pdmR,
      pdmL . onR pi asn))

public export
0 MLPolyParaAsNatTransIsNatural :
  (p, q : MLPolyDiSig) -> (gamma : MLPolyParaNT p q) ->
  TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ InterpMLPolyDi p)}
    {q=(TwArrPreshfEmbedProf $ InterpMLPolyDi q)}
    (TwArrPreshfEmbedProfMap (InterpMLPolyDi p) $
      MkProfunctor $ \mca, mbd => InterpMLPolyDimap p _ _ _ _ mca mbd)
    (TwArrPreshfEmbedProfMap (InterpMLPolyDi q) $
      MkProfunctor $ \mca, mbd => InterpMLPolyDimap q _ _ _ _ mca mbd)
    (MLPolyParaAsNatTrans {p} {q} gamma)
MLPolyParaAsNatTransIsNatural
  (ppos ** (pdirL, pdirR)) (qpos ** (qdirL, qdirR))
  (onpos ** (onR, onL)) s t a b mba mas mtb (i ** (dcont, dcovar)) =
    Refl

public export
MLPolyDiSigFromNatTrans : (p, q : MLPolyDiSig) ->
  (gamma : TwArrPreshfEmbeddingNT (InterpMLPolyDi p) (InterpMLPolyDi q)) ->
  TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ InterpMLPolyDi p)}
    {q=(TwArrPreshfEmbedProf $ InterpMLPolyDi q)}
    (TwArrPreshfEmbedProfMap (InterpMLPolyDi p) $
      MkProfunctor $ \mca, mbd => InterpMLPolyDimap p _ _ _ _ mca mbd)
    (TwArrPreshfEmbedProfMap (InterpMLPolyDi q) $
      MkProfunctor $ \mca, mbd => InterpMLPolyDimap q _ _ _ _ mca mbd)
    gamma ->
  MLPolyParaNT p q
MLPolyDiSigFromNatTrans
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma isnat =
    (\pi, asn =>
      fst $ gamma (pcontra pi) (pcovar pi) asn (pi ** (id, id)) **
     (\pi, asn, pdcont =>
        fst (snd $ gamma (pcontra pi) (pcovar pi) asn (pi ** (id, id))) pdcont,
      \pi, asn, qdcov =>
        snd (snd $ gamma (pcontra pi) (pcovar pi) asn (pi ** (id, id))) qdcov))

public export
MLPolyDiSigFromNatTransComplete : (p, q : MLPolyDiSig) ->
  (gamma : TwArrPreshfEmbeddingNT (InterpMLPolyDi p) (InterpMLPolyDi q)) ->
  (isnat : TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ InterpMLPolyDi p)}
    {q=(TwArrPreshfEmbedProf $ InterpMLPolyDi q)}
    (TwArrPreshfEmbedProfMap (InterpMLPolyDi p) $
      MkProfunctor $ \mca, mbd => InterpMLPolyDimap p _ _ _ _ mca mbd)
    (TwArrPreshfEmbedProfMap (InterpMLPolyDi q) $
      MkProfunctor $ \mca, mbd => InterpMLPolyDimap q _ _ _ _ mca mbd)
    gamma) ->
  (x : Type) ->
  ExtEq {a=(InterpMLPolyDiDiag p x)} {b=(InterpMLPolyDiDiag q x)}
    (TwArrPreshfEmbeddingNTtoProfParaNT
      {p=(InterpMLPolyDi p)} {q=(InterpMLPolyDi q)} gamma x)
    (InterpMLPolyParaNT {p} {q} (MLPolyDiSigFromNatTrans p q gamma isnat) x)
MLPolyDiSigFromNatTransComplete
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma isnat x
  (pi ** (dcont, dcovar)) =
    trans
      (sym
       $ isnat (pcontra pi) (pcovar pi) x x id dcovar dcont (pi ** (id, id)))
    $ dpEq12
      Refl
    $ pairEqCong
      (trans
        (bimapIdR1 {f=(IdrisUtils.(|>) dcont)})
        (cong (IdrisUtils.(|>) dcont)
         $ bimapIdL1
          {g=((.) dcovar)}
          {eac=(
            DPair.snd
              (gamma (pcontra pi) (pcovar pi)
               (dcont . dcovar) (pi ** (id, id))))}))
      (trans
        (bimapIdR2 {f=(IdrisUtils.(|>) dcont)})
        (bimapIdL2 {g=((.) dcovar)}))

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Paranaturals as functors on categories of diagonal elements ----
---------------------------------------------------------------------
---------------------------------------------------------------------

public export
MLPolyParaToCatElemObjMap : {p, q : MLPolyDiSig} -> MLPolyParaNT p q ->
  MLPDiagObj p -> MLPDiagObj q
MLPolyParaToCatElemObjMap =
  PolyParaToCatElemObjMap {c=Type} {mor=TypeMor} {comp=typeComp}

public export
MLPolyParaToCatElemFMap : {p, q : MLPolyDiSig} -> (gamma : MLPolyParaNT p q) ->
  (x, y : MLPDiagObj p) ->
  MLPDiagMor {p} x y ->
  MLPDiagMor {p=q}
    (MLPolyParaToCatElemObjMap {p} {q} gamma x)
    (MLPolyParaToCatElemObjMap {p} {q} gamma y)
MLPolyParaToCatElemFMap =
  PolyParaToCatElemFMap {c=Type} {mor=TypeMor} {comp=typeComp} {assoc=typeAssoc}

--------------------------------------------
--------------------------------------------
---- Polynomial-specific diYoneda lemma ----
--------------------------------------------
--------------------------------------------

public export
MLPolyDiYonedaL : (a, b : Type) -> (p : MLPolyDiSig) ->
  TypeProfDiNT
    (InterpMLPolyDi p)
    (\i, j =>
      TypeProfDiNT (IntDiYonedaEmbedObj Type TypeMor j i) (InterpMLPolyDi p))
MLPolyDiYonedaL a b (ppos ** (pdirL, pdirR)) x (pi ** (pdmR, pdmL)) y
  (myx, mxy) =
    (pi ** (pdmR . myx, mxy . pdmL))

public export
MLPolyDiYonedaR : (a, b : Type) -> (p : MLPolyDiSig) ->
  TypeProfDiNT
    (\i, j =>
      TypeProfDiNT (IntDiYonedaEmbedObj Type TypeMor j i) (InterpMLPolyDi p))
    (InterpMLPolyDi p)
MLPolyDiYonedaR a b (ppos ** (pdirL, pdirR)) x gamma = gamma x (id, id)

--------------------------------------------------------
--------------------------------------------------------
---- Monoidal composition product on di-polynomials ----
--------------------------------------------------------
--------------------------------------------------------

public export
mlpdId : MLPolyDiSig
mlpdId = pdId Type

public export
mlpdComp : MLPolyDiSig -> MLPolyDiSig -> MLPolyDiSig
mlpdComp = pdComp {c=Type} {mor=TypeMor}

public export
mlpIdToInterp : TypeProfDiNT (InterpMLPolyDi MLDiPolyFunc.mlpdId) HomProf
mlpIdToInterp x (pi ** (dmR, dmL)) = dmL . dmR

public export
mlpIdFromInterp : TypeProfDiNT HomProf (InterpMLPolyDi MLDiPolyFunc.mlpdId)
mlpIdFromInterp x m = (x ** (m , m))

public export
mlpIdToTwInterp :
  TwArrPreshfNatTrans
    (TwArrPreshfEmbedProf $ InterpMLPolyDi MLDiPolyFunc.mlpdId)
    (TwArrPreshfEmbedProf HomProf)
mlpIdToTwInterp x y m el = snd (snd el) . fst (snd el)

public export
mlpIdFromTwInterp :
  TwArrPreshfNatTrans
    (TwArrPreshfEmbedProf HomProf)
    (TwArrPreshfEmbedProf $ InterpMLPolyDi MLDiPolyFunc.mlpdId)
mlpIdFromTwInterp x y mxy myx = (y ** (id {a=y}, myx))

public export
mlpdCompToInterp :
  (q, p : MLPolyDiSig) ->
  TypeProfDiNT
    (InterpMLPolyDi (mlpdComp q p))
    (EndoProfCompose (InterpMLPolyDi q) (InterpMLPolyDi p))
mlpdCompToInterp (qpos ** (qdirL, qdirR)) (ppos ** (pdirL, pdirR)) x
  ((pi ** qi ** qlpr) ** (dmR, dmL)) =
    (qdirL qi ** ((qi ** (dmR, id {a=(qdirL qi)})), (pi ** (qlpr, dmL))))

public export
mlpdCompFromInterp :
  (q, p : MLPolyDiSig) ->
  TypeProfDiNT
    (EndoProfCompose (InterpMLPolyDi q) (InterpMLPolyDi p))
    (InterpMLPolyDi (mlpdComp q p))
mlpdCompFromInterp (qpos ** (qdirL, qdirR)) (ppos ** (pdirL, pdirR)) x
  (b ** ((qi ** (qdmR, qdmL)), (pi ** (pdmR, pdmL)))) =
    ((pi ** qi ** pdmR . qdmL) ** (qdmR, pdmL))

-----------------------------------------------
-----------------------------------------------
---- Categorical structure of paranaturals ----
-----------------------------------------------
-----------------------------------------------

public export
mlpId : (p : MLPolyDiSig) -> MLPolyParaNT p p
mlpId = polyParaNTid {c=Type} {mor=TypeMor} {cid=typeId}

public export
mlpVcomp : {p, q, r : MLPolyDiSig} ->
  MLPolyParaNT q r -> MLPolyParaNT p q -> MLPolyParaNT p r
mlpVcomp = polyParaNTvcomp {c=Type} {mor=TypeMor} {comp=typeComp}
