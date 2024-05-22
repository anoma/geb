module LanguageDef.IntDisheafCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntECofamCat

-------------------------------------
-------------------------------------
---- Disheaf category definition ----
-------------------------------------
-------------------------------------

-- The disheaf category of a category is the category of existential
-- families (AKA polynomial functors) on its twisted-arrow category.

public export
IntDisheafCat : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntCatSig
IntDisheafCat c mapId mapComp = ECofamCatSig $ TwArrCat c mapId mapComp

public export
IntDisheafObj : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  Type
IntDisheafObj c mapId mapComp = icObj $ IntDisheafCat c mapId mapComp

public export
IntDisheafMor : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntMorSig (IntDisheafObj c mapId mapComp)
IntDisheafMor c mapId mapComp = icMor $ IntDisheafCat c mapId mapComp

public export
IntDisheafId : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntIdSig (IntDisheafObj c mapId mapComp) (IntDisheafMor c mapId mapComp)
IntDisheafId c mapId mapComp = icId $ IntDisheafCat c mapId mapComp

public export
IntDisheafComp : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntCompSig (IntDisheafObj c mapId mapComp) (IntDisheafMor c mapId mapComp)
IntDisheafComp c mapId mapComp = icComp $ IntDisheafCat c mapId mapComp

--------------------------------------------------------
--------------------------------------------------------
---- Interpretation of disheaf objects into `QType` ----
--------------------------------------------------------
--------------------------------------------------------

public export
IntDisheafSig : IntCatSig -> Type
IntDisheafSig c = (x, y : icObj c) -> icMor c x y -> QType

public export
IntDisheafFromProfunctorSig : {c : IntCatSig} ->
  (icObj c -> icObj c -> QType) -> IntDisheafSig c
IntDisheafFromProfunctorSig {c} p x y m = p x y

public export
IntDisheafMapBaseSig : {c : IntCatSig} -> IntDisheafSig c -> Type
IntDisheafMapBaseSig {c} p =
  (s, t : icObj c) -> (mst : icMor c s t) ->
  (a, b : icObj c) -> (mas : icMor c a s) -> (mtb : icMor c t b) ->
  fst0 (p s t mst) ->
  fst0
    (p a b $
      icComp c a t b
        mtb
      $ icComp c a s t
        mst
        mas)

public export
IntDisheafMapSig : {c : IntCatSig} -> IntDisheafSig c -> Type
IntDisheafMapSig {c} p =
  (s, t : icObj c) -> (mst : icMor c s t) ->
  (a, b : icObj c) -> (mas : icMor c a s) -> (mtb : icMor c t b) ->
  QMorph
    (p s t mst)
    (p a b $
      icComp c a t b
        mtb
      $ icComp c a s t
        mst
        mas)

public export
IntDisheafFromDimapSig : {c : IntCatSig} -> (p : icObj c -> icObj c -> QType) ->
  ((s, t, a, b : icObj c) -> icMor c a s -> icMor c t b ->
   QMorph (p s t) (p a b)) ->
  IntDisheafMapSig {c} (IntDisheafFromProfunctorSig {c} p)
IntDisheafFromDimapSig {c} p dm s t mst a b mas mtb = dm s t a b mas mtb

public export
IntDisheafInterp : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  IntDisheafObj c mapId mapComp ->
  IntDisheafSig c
IntDisheafInterp {c} {mapId} {mapComp} p x y f =
  QTypeFromType
  $ InterpECofamCopreshfOMap
    (TwArrObj c mapId mapComp) (TwArrMor c mapId mapComp)
    p ((x, y) ** f)

public export
IntDisheafInterpMapBase : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  IntDisheafMapBaseSig {c} (IntDisheafInterp {c} {mapId} {mapComp} p)
IntDisheafInterpMapBase {c} {mapId} {mapComp} p s t mst a b mas mtb =
  InterpECofamCopreshfFMap
    (TwArrObj c mapId mapComp)
    (TwArrMor c mapId mapComp)
    (TwArrComp c mapId mapComp)
    p
    ((s, t) ** mst)
    ((a, b) ** icComp c _ _ _ mtb $ icComp c _ _ _ mst mas)
    (CElMor (mas, mtb) Refl)

public export
IntDisheafInterpMap : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  IntDisheafMapSig {c} (IntDisheafInterp {c} {mapId} {mapComp} p)
IntDisheafInterpMap {c} {mapId} {mapComp} p s t mst a b mas mtb =
  QMorphFromMorph $
    IntDisheafInterpMapBase {c} {mapId} {mapComp} p s t mst a b mas mtb

-------------------------------------
-------------------------------------
---- Disheaf composition product ----
-------------------------------------
-------------------------------------

-- The identity of the composition product on disheaves, which is analogous
-- to that on profunctors.
public export
IntDisheafMonUnit : {c : IntCatSig} ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntDisheafObj c mapId mapComp
IntDisheafMonUnit {c} mapId mapComp = (TwArrObj c mapId mapComp ** id)

public export
IntDisheafMonProdPosMor : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (q, p : IntDisheafObj c mapId mapComp) ->
  fst q -> fst p -> Type
IntDisheafMonProdPosMor {c} {mapId} {mapComp} q p qi pi =
   icMor c (snd $ fst $ snd q qi) (fst $ fst $ snd p pi)

public export
IntDisheafMonProdDir : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (q, p : IntDisheafObj c mapId mapComp) ->
  (qi : fst q) -> (pi : fst p) ->
  IntDisheafMonProdPosMor {c} {mapId} {mapComp} q p qi pi ->
  TwArrObj c mapId mapComp
IntDisheafMonProdDir {c} {mapId} {mapComp} q p qi pi qcpd =
  ((fst $ fst $ snd q qi, snd $ fst $ snd p pi) **
   icComp c
    (fst $ fst $ snd q qi) (fst $ fst $ snd p pi) (snd $ fst $ snd p pi)
    (replace {p=(uncurry $ icMor c)}
      (pairFstSnd (DPair.fst $ DPair.snd p pi))
      (snd $ snd p pi)) $
   icComp c
    (fst $ fst $ snd q qi) (snd $ fst $ snd q qi) (fst $ fst $ snd p pi)
    qcpd
    (replace {p=(uncurry $ icMor c)}
      (pairFstSnd (DPair.fst $ DPair.snd q qi))
      (snd $ snd q qi)))

public export
IntDisheafMonProd : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  IntDisheafObj c mapId mapComp ->
  IntDisheafObj c mapId mapComp ->
  IntDisheafObj c mapId mapComp
IntDisheafMonProd {c} {mapId} {mapComp} q p =
  ((qpi : (fst q, fst p) **
    IntDisheafMonProdPosMor {c} {mapId} {mapComp} q p (fst qpi) (snd qpi)) **
   \qpim =>
    IntDisheafMonProdDir {c} {mapId} {mapComp} q p
      (fst $ fst qpim) (snd $ fst qpim) (snd qpim))

-- The composition monoid on disheaves.
public export
IntDisheafCompMon : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntCatSig
IntDisheafCompMon c mapId mapComp =
  ICat
    Unit
  $ MICS
    (\_, _ => IntDisheafObj c mapId mapComp)
  $ ICS
    (\_ => IntDisheafMonUnit {c} mapId mapComp)
    (\_, _, _ => IntDisheafMonProd {c} {mapId} {mapComp})

----------------------------------------------------
----------------------------------------------------
---- Precomposition functor in disheaf category ----
----------------------------------------------------
----------------------------------------------------

public export
IntDisheafPrecompOmap : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  IntDisheafObj c mapId mapComp ->
  IntEndoOMapSig (IntDisheafObj c mapId mapComp)
IntDisheafPrecompOmap {c} {mapId} {mapComp} =
  flip $ IntDisheafMonProd {c} {mapId} {mapComp}

public export
IntDisheafPrecompFmapOnIdx : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  (q, r : IntDisheafObj c mapId mapComp) ->
  (m : IntDisheafMor c mapId mapComp q r) ->
  (qi : icfeoIdx q) -> (pi : icfeoIdx p) ->
  icMor c (snd $ fst $ snd q qi) (fst $ fst $ snd p pi) ->
  icMor c (snd $ fst $ snd r $ fst m qi) (fst $ fst $ snd p pi)
IntDisheafPrecompFmapOnIdx {c} {mapId} {mapComp} p q r
  (onidx ** onobj) qi pi qcpd =
    icComp c _ _ _ qcpd (snd $ cemMor $ onobj qi)

public export
IntDisheafPrecompFmapOnObjMor : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  (q, r : IntDisheafObj c mapId mapComp) ->
  (m : IntDisheafMor c mapId mapComp q r) ->
  (qi : icfeoIdx q) -> (pi : icfeoIdx p) ->
  icMor c (snd $ fst $ snd q qi) (fst $ fst $ snd p pi) ->
  icMor (IntEndoOpProdCat c)
    (fst $ fst $ snd r $ fst m qi, snd $ fst $ snd p pi)
    (fst $ fst $ snd q qi, snd $ fst $ snd p pi)
IntDisheafPrecompFmapOnObjMor {c} {mapId} {mapComp} p q r
  (onidx ** onobj) qi pi qcpd =
    (fst $ cemMor $ onobj qi, icId c $ snd $ fst $ snd p pi)

public export
IntDisheafPrecompFmapOnObjEq : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  (q, r : IntDisheafObj c mapId mapComp) ->
  (m : IntDisheafMor c mapId mapComp q r) ->
  (qi : icfeoIdx q) -> (pi : icfeoIdx p) ->
  (qcpd : icMor c (snd $ fst $ snd q qi) (fst $ fst $ snd p pi)) ->
  CopreCatElemEq
    {c=(icObj $ IntEndoOpProdCat c)}
    {mor=(icMor $ IntEndoOpProdCat c)}
    {cid=(icId $ IntEndoOpProdCat c)}
    {comp=(icComp $ IntEndoOpProdCat c)}
    {p=(IntHomProfObj (icId c) (icComp c) mapId mapComp)}
    ((fst $ fst $ snd r $ fst m qi, snd $ fst $ snd p pi) **
     ?IntDisheafPrecompFmapOnObjEq_type_hole)
    ((fst $ fst $ snd q qi, snd $ fst $ snd p pi) **
     icComp c
      (fst $ fst $ snd q qi)
      (fst $ fst $ snd p pi)
      (snd $ fst $ snd p pi)
      (snd $ snd p pi)
     $ icComp c
      (fst $ fst $ snd q qi)
      (snd $ fst $ snd q qi)
      (fst $ fst $ snd p pi)
      qcpd
      (snd $ snd q qi))
    (IntDisheafPrecompFmapOnObjMor {c} {mapId} {mapComp} p q r m qi pi qcpd)
IntDisheafPrecompFmapOnObjEq {c} {mapId} {mapComp} p q r
  (onidx ** onobj) qi pi qcpd =
    ?IntDisheafPrecompFmapOnObjEq_hole

public export
IntDisheafPrecompFmap : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  IntEndoFMapSig
    {c=(IntDisheafObj c mapId mapComp)}
    (IntDisheafMor c mapId mapComp)
    (IntDisheafPrecompOmap {c} {mapId} {mapComp} p)
IntDisheafPrecompFmap {c} {mapId} {mapComp} p q r (onidx ** onobj) =
  (\((qi, pi) ** qcpd) =>
    ((onidx qi, pi) **
     IntDisheafPrecompFmapOnIdx p q r (onidx ** onobj) qi pi qcpd) **
   \((qi, pi) ** qcpd) =>
    CElMor
      (IntDisheafPrecompFmapOnObjMor {c} {mapId} {mapComp} p q r
        (onidx ** onobj) qi pi qcpd)
      (IntDisheafPrecompFmapOnObjEq {c} {mapId} {mapComp} p q r
        (onidx ** onobj) qi pi qcpd))

-----------------------------------------------------
-----------------------------------------------------
---- Postcomposition functor in disheaf category ----
-----------------------------------------------------
-----------------------------------------------------

public export
IntDisheafPostcompOmap : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  IntDisheafObj c mapId mapComp ->
  IntEndoOMapSig (IntDisheafObj c mapId mapComp)
IntDisheafPostcompOmap {c} {mapId} {mapComp} =
  IntDisheafMonProd {c} {mapId} {mapComp}

public export
IntDisheafPostcompFmap : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  IntEndoFMapSig
    {c=(IntDisheafObj c mapId mapComp)}
    (IntDisheafMor c mapId mapComp)
    (IntDisheafPostcompOmap {c} {mapId} {mapComp} p)
IntDisheafPostcompFmap {c} {mapId} {mapComp} p q r (onidx ** onobj) =
  (\((pi, qi) ** pcqd) =>
    ((pi, onidx qi) ** icComp c _ _ _ (fst $ cemMor $ onobj qi) pcqd) **
   \((pi, qi) ** pcqd) =>
    let (qdrd, rcqc) = cemMor (onobj qi) in
    CElMor
      (icId c $ fst $ fst $ snd p pi, rcqc)
      ?IntDisheafPostcompFmap_hole_eq)
