module LanguageDef.PolySliceCat

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
import public LanguageDef.MLBundleCat
import public LanguageDef.MLDirichCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-----------------------------------------------------------------------
-----------------------------------------------------------------------
---- Slice categories of polynomial functors (in categorial style) ----
-----------------------------------------------------------------------
-----------------------------------------------------------------------

public export
CPFSliceObj : MLPolyCatObj -> Type
CPFSliceObj p = (q : MLPolyCatObj ** PolyNatTrans q p)

public export
0 CPFNatTransEq :
  (p, q : MLPolyCatObj) -> (alpha, beta : PolyNatTrans p q) -> Type
CPFNatTransEq (ppos ** pdir) (qpos ** qdir)
  (aonpos ** aondir) (bonpos ** bondir) =
    Exists0
      (ExtEq {a=ppos} {b=qpos} aonpos bonpos)
      $ \onposeq =>
        (i : ppos) -> (d : qdir (aonpos i)) ->
        bondir i (replace {p=qdir} (onposeq i) d) = aondir i d

public export
CPFSliceMorph : (p : MLPolyCatObj) -> CPFSliceObj p -> CPFSliceObj p -> Type
CPFSliceMorph p (q ** qp) (r ** rp) =
  Subset0 (PolyNatTrans q r) (\qr => CPFNatTransEq q p qp (pntVCatComp rp qr))

-- In any slice category, we can infer a slice morphism from a slice object
-- and a morphism from any object of the base category to the domain of the
-- slice object, by taking the codomain of the slice morphism to be the given
-- slice object, the domain of the domain of the slice morphism to be the
-- given object of the base category, and the projection of the domain of the
-- slice morphism to be composition of the given morphism followed by the
-- projection of the codomain of the slice morphism.  All slice morphisms
-- take this form, so that can function as an alternate definition of slice
-- morphism, which does not require any explicit proof content (of
-- commutativity).
public export
PFSliceMorph : {0 p : PolyFunc} -> CPFSliceObj p -> Type
PFSliceMorph {p} (ctot ** alpha) = (dtot : PolyFunc ** PolyNatTrans dtot ctot)

public export
PFSliceMorphDom : {0 p : PolyFunc} -> {cod : CPFSliceObj p} ->
  PFSliceMorph {p} cod -> CPFSliceObj p
PFSliceMorphDom {p} {cod=(ctot ** alpha)} (dtot ** beta) =
  (dtot ** pntVCatComp alpha beta)

public export
data PFSliceMorphDep : {0 p : PolyFunc} -> CPFSliceObj p -> CPFSliceObj p ->
    Type where
  PSMD : {0 p : PolyFunc} -> {0 dom, cod : CPFSliceObj p} ->
    (mor : PFSliceMorph {p} cod) ->
    PFSliceMorphDep {p} (PFSliceMorphDom {p} {cod} mor) cod

public export
PFSliceMorphToC : {0 p : PolyFunc} -> {cod : CPFSliceObj p} ->
  (mor : PFSliceMorph {p} cod) ->
  CPFSliceMorph p (PFSliceMorphDom {p} {cod} mor) cod
PFSliceMorphToC {p=(ppos ** pdir)} {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((dtot ** dproj) ** (donpos ** dondir)) =
    Element0
      (donpos ** dondir)
      (Evidence0
        (\_ => Refl)
        (\_, _ => Refl))

public export
PFSliceMorphFromC : {0 p : PolyFunc} -> {dom, cod : CPFSliceObj p} ->
  CPFSliceMorph p dom cod -> PFSliceMorph {p} cod
PFSliceMorphFromC {p=(ppos ** pdir)} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
  (Element0 alpha nteq) =
    (dtot ** alpha)

public export
PFSliceMorphFromCDomObjEq : {0 p : PolyFunc} -> {dom, cod : CPFSliceObj p} ->
  (mor : CPFSliceMorph p dom cod) ->
  fst (PFSliceMorphDom {p} {cod} (PFSliceMorphFromC {p} {dom} {cod} mor)) =
  fst dom
PFSliceMorphFromCDomObjEq {p=(ppos ** pdir)}
  {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} (Element0 alpha nteq) =
    Refl

public export
0 PFSliceMorphFromCDomMorEq : {0 p : PolyFunc} ->
  {dtot, ctot : PolyFunc} ->
  {dproj : PolyNatTrans dtot p} ->
  {cproj : PolyNatTrans ctot p} ->
  (mor : CPFSliceMorph p (dtot ** dproj) (ctot ** cproj)) ->
  CPFNatTransEq
    dtot p
    dproj
    (replace {p=(flip PolyNatTrans p)}
      (PFSliceMorphFromCDomObjEq {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
       mor)
     $ snd $ PFSliceMorphDom {p} {cod=(ctot ** cproj)}
     $ PFSliceMorphFromC {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} mor)
PFSliceMorphFromCDomMorEq {p=(ppos ** pdir)}
  {dtot} {dproj} {ctot} {cproj} (Element0 alpha nteq) =
    nteq

------------------------------------------------------------
------------------------------------------------------------
---- Factorized slice categories of polynomial functors ----
------------------------------------------------------------
------------------------------------------------------------

-------------------------------------------
---- Polynomial vertical-slice objects ----
-------------------------------------------

public export
PolyVertSlObj : MLPolyCatObj -> Type
PolyVertSlObj b =
  (sldir : SliceObj (dfPos b) ** SliceMorphism {a=(dfPos b)} (dfDir b) sldir)

public export
PolyVertSlTotPos : {b : MLPolyCatObj} -> PolyVertSlObj b -> Type
PolyVertSlTotPos {b} p = dfPos b

public export
PolyVertSlOnPos : {b : MLPolyCatObj} -> (p : PolyVertSlObj b) ->
  PolyVertSlTotPos {b} p -> dfPos b
PolyVertSlOnPos {b} p = id

public export
PolyVertSlDir : {b : MLPolyCatObj} ->
  (p : PolyVertSlObj b) -> PolyVertSlTotPos {b} p -> Type
PolyVertSlDir {b} p = DPair.fst p

public export
PolyVertSlOnDir : {b : MLPolyCatObj} ->
  (p : PolyVertSlObj b) ->
  SliceMorphism {a=(PolyVertSlTotPos {b} p)}
    (dfDir b . PolyVertSlOnPos {b} p)
    (PolyVertSlDir {b} p)
PolyVertSlOnDir {b} p i = snd p i

public export
PolyVertSlEmbed : {b : MLPolyCatObj} -> PolyVertSlObj b -> MLPolyCatObj
PolyVertSlEmbed {b} p = (PolyVertSlTotPos {b} p ** PolyVertSlDir {b} p)

public export
PolyVertSlTot : {b : MLPolyCatObj} -> PolyVertSlObj b -> Type
PolyVertSlTot {b} p = dfTot (PolyVertSlEmbed {b} p)

public export
PolyVertSlProj : {b : MLPolyCatObj} -> (p : PolyVertSlObj b) ->
  PolyNatTrans (PolyVertSlEmbed {b} p) b
PolyVertSlProj {b} p = (PolyVertSlOnPos {b} p ** PolyVertSlOnDir {b} p)

---------------------------------------------
---- Polynomial vertical-slice morphisms ----
---------------------------------------------

public export
PolyVertSlMor : {b : MLPolyCatObj} ->
  PolyVertSlObj b -> PolyVertSlObj b -> Type
PolyVertSlMor {b} p q =
  (bi : dfPos b) ->
  (ondir : fst q bi -> fst p bi **
   (bd : dfDir b bi) -> snd p bi bd = ondir (snd q bi bd))

public export
PolyVertSlId : {b : MLPolyCatObj} ->
  (p : PolyVertSlObj b) -> PolyVertSlMor {b} p p
PolyVertSlId {b} p bi = (Prelude.id ** \_ => Refl)

public export
PolyVertSlComp : {b : MLPolyCatObj} ->
  {p, q, r : PolyVertSlObj b} ->
  PolyVertSlMor {b} q r -> PolyVertSlMor {b} p q -> PolyVertSlMor {b} p r
PolyVertSlComp {b} {p} {q} {r} beta alpha bi =
  (fst (alpha bi) . fst (beta bi) **
   \bd => trans
    (snd (alpha bi) bd)
    (cong (fst $ alpha bi) (snd (beta bi) bd)))

------------------------------------------------------
------------------------------------------------------
---- Slices over arenas (in dependent-type style) ----
------------------------------------------------------
------------------------------------------------------

-- In the case of polynomial functors, the directions of the slice object's
-- domain are slices of its positions only, since its on-directions function
-- can not be viewed as a fibration of them, and we therefore require an
-- explicit on-directions function (rather than making it implicit as a
-- fibration in the definition of the type of directions).
public export
MlPolySlDir : (ar : MLArena) -> MlSlArProjOnPos ar -> Type
MlPolySlDir ar onpos = (i : pfPos ar) -> onpos i -> Type

public export
MlPolySlOnDir : {ar : MLArena} ->
  (onpos : MlSlArProjOnPos ar) -> MlPolySlDir ar onpos -> Type
MlPolySlOnDir {ar} onpos dir =
  (i : pfPos ar) -> (j : onpos i) -> pfDir {p=ar} i -> dir i j

public export
record MlPolySlObj (ar : MLArena) where
  constructor MPSobj
  mpsOnPos : MlSlArProjOnPos ar
  mpsDir : MlPolySlDir ar mpsOnPos
  mpsOnDir : MlPolySlOnDir {ar} mpsOnPos mpsDir

--------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style objects ----
--------------------------------------------------------------------

public export
mlPolySlObjTotPos : {ar : MLArena} -> MlPolySlObj ar -> Type
mlPolySlObjTotPos {ar} p = MlSlArTotPos {ar} $ mpsOnPos p

public export
mlPolySlObjTotDir : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  mlPolySlObjTotPos {ar} sl -> Type
mlPolySlObjTotDir {ar} sl ij = mpsDir sl (fst ij) (snd ij)

public export
mlPolySlObjTot : {ar : MLArena} -> MlPolySlObj ar -> MLArena
mlPolySlObjTot {ar} sl =
  (mlPolySlObjTotPos {ar} sl ** mlPolySlObjTotDir {ar} sl)

public export
mlPolySlObjProjOnPos : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  mlPolySlObjTotPos sl -> pfPos ar
mlPolySlObjProjOnPos {ar} sl = DPair.fst

public export
mlPolySlObjProjOnDir : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (i : mlPolySlObjTotPos sl) ->
  pfDir {p=ar} (mlPolySlObjProjOnPos sl i) -> mlPolySlObjTotDir {ar} sl i
mlPolySlObjProjOnDir {ar} sl ij d = mpsOnDir sl (fst ij) (snd ij) d

public export
mlPolySlObjProj : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  PolyNatTrans (mlPolySlObjTot {ar} sl) ar
mlPolySlObjProj {ar} sl =
  (mlPolySlObjProjOnPos {ar} sl ** mlPolySlObjProjOnDir {ar} sl)

public export
mlPolySlObjToC : (ar : PolyFunc) -> MlPolySlObj ar -> CPFSliceObj ar
mlPolySlObjToC ar sl@(MPSobj onpos dir ondir) =
  (mlPolySlObjTot {ar} sl ** mlPolySlObjProj {ar} sl)

public export
mlPolySlOnPosFromC : {ar : MLArena} -> CPFSliceObj ar -> MlSlArProjOnPos ar
mlPolySlOnPosFromC {ar} sl i = PreImage (fst $ snd sl) i

public export
mlPolySlDirFromC : {ar : MLArena} -> (sl : CPFSliceObj ar) ->
  MlPolySlDir ar (mlPolySlOnPosFromC {ar} sl)
mlPolySlDirFromC {ar} sl i j = snd (fst sl) $ fst0 j

public export
mlPolySlOnDirFromC : {ar : MLArena} -> (sl : CPFSliceObj ar) ->
  MlPolySlOnDir {ar} (mlPolySlOnPosFromC {ar} sl) (mlPolySlDirFromC {ar} sl)
mlPolySlOnDirFromC {ar} sl i j d = snd (snd sl) (fst0 j) $ rewrite (snd0 j) in d

public export
mlPolySlObjFromC : (p : PolyFunc) -> CPFSliceObj p -> MlPolySlObj p
mlPolySlObjFromC ar sl =
  MPSobj
    (mlPolySlOnPosFromC {ar} sl)
    (mlPolySlDirFromC {ar} sl)
    (mlPolySlOnDirFromC {ar} sl)

------------------------------------------------
---- Slices of slices of Dirichlet functors ----
------------------------------------------------

public export
MlDirichSlOfSl : {ar : MLArena} -> MlDirichSlObj ar -> Type
MlDirichSlOfSl {ar} sl = MlDirichSlObj $ mlDirichSlObjTot {ar} sl

public export
MlDirichSlPosFromSlOfSl : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  MlDirichSlOfSl {ar} sl -> MlSlArProjOnPos ar
MlDirichSlPosFromSlOfSl {ar} sl slsl i =
  DPair (mdsOnPos sl i) $ DPair.curry (mdsOnPos slsl) i

public export
MlDirichSlDirFromSlOfSl : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  (slsl : MlDirichSlOfSl {ar} sl) ->
  MlDirichSlDir ar (MlDirichSlPosFromSlOfSl {ar} sl slsl)
MlDirichSlDirFromSlOfSl {ar} sl slsl i jk d =
  (sld : mdsDir sl i (fst jk) d **
   mdsDir slsl (i ** fst jk) (snd jk) (d ** sld))

public export
MlDirichSlFromSlOfSl : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  MlDirichSlOfSl {ar} sl -> MlDirichSlObj ar
MlDirichSlFromSlOfSl {ar} sl slsl =
  MDSobj
    (MlDirichSlPosFromSlOfSl {ar} sl slsl)
    (MlDirichSlDirFromSlOfSl {ar} sl slsl)

public export
mlDirichSlOfSlFromP : {ar : MLArena} -> {cod : MlDirichSlObj ar} ->
  DFSliceMorph {p=ar} (mlDirichSlObjToC {ar} cod) -> MlDirichSlOfSl {ar} cod
mlDirichSlOfSlFromP {ar} {cod=cod@(MDSobj _ _)} =
  mlDirichSlObjFromC {ar=(mlDirichSlObjTot {ar} cod)}

-------------------------------------------------
---- Slices of slices of polynomial functors ----
-------------------------------------------------

public export
MlPolySlOfSl : {ar : MLArena} -> MlPolySlObj ar -> Type
MlPolySlOfSl {ar} sl = MlPolySlObj $ mlPolySlObjTot {ar} sl

public export
MlPolySlPosFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  MlPolySlOfSl {ar} sl -> MlSlArProjOnPos ar
MlPolySlPosFromSlOfSl {ar} sl slsl i =
  DPair (mpsOnPos sl i) $ DPair.curry (mpsOnPos slsl) i

public export
MlPolySlDirFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (slsl : MlPolySlOfSl {ar} sl) ->
  MlPolySlDir ar (MlPolySlPosFromSlOfSl {ar} sl slsl)
MlPolySlDirFromSlOfSl {ar} sl slsl i jk =
  (mpsDir sl i (fst jk), mpsDir slsl (i ** fst jk) (snd jk))

public export
MlPolySlOnDirFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (slsl : MlPolySlOfSl {ar} sl) ->
  MlPolySlOnDir {ar}
    (MlPolySlPosFromSlOfSl {ar} sl slsl)
    (MlPolySlDirFromSlOfSl {ar} sl slsl)
MlPolySlOnDirFromSlOfSl {ar} sl slsl i jk bd =
  let sldir = mpsOnDir sl i (fst jk) bd in
  (sldir, mpsOnDir slsl (i ** fst jk) (snd jk) sldir)

public export
MlPolySlFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  MlPolySlOfSl {ar} sl -> MlPolySlObj ar
MlPolySlFromSlOfSl {ar} sl slsl =
  MPSobj
    (MlPolySlPosFromSlOfSl {ar} sl slsl)
    (MlPolySlDirFromSlOfSl {ar} sl slsl)
    (MlPolySlOnDirFromSlOfSl {ar} sl slsl)

public export
mlPolySlOfSlFromP : {ar : MLArena} -> {cod : MlPolySlObj ar} ->
  PFSliceMorph {p=ar} (mlPolySlObjToC ar cod) -> MlPolySlOfSl {ar} cod
mlPolySlOfSlFromP {ar} {cod=cod@(MPSobj _ _ _)} m =
  mlPolySlObjFromC (mlPolySlObjTot {ar} cod) m

-----------------------------------
---- Slice morphism definition ----
-----------------------------------

public export
MlPolySlMorOnPos : {ar : MLArena} ->
  MlPolySlObj ar -> MlPolySlObj ar -> Type
MlPolySlMorOnPos {ar} dom cod =
  SliceMorphism {a=(pfPos ar)} (mpsOnPos dom) (mpsOnPos cod)

public export
MlPolySlMorOnDir : {ar : MLArena} -> (dom, cod : MlPolySlObj ar) ->
  MlPolySlMorOnPos {ar} dom cod -> Type
MlPolySlMorOnDir {ar} dom cod monpos =
  (i : pfPos ar) -> (j : mpsOnPos dom i) ->
  mpsDir cod i (monpos i j) -> mpsDir dom i j

public export
0 MlPolySlMorOnDirCommutes : {ar : MLArena} -> (dom, cod : MlPolySlObj ar) ->
  (onpos : MlPolySlMorOnPos {ar} dom cod) ->
  MlPolySlMorOnDir {ar} dom cod onpos -> Type
MlPolySlMorOnDirCommutes {ar} dom cod monpos mdir =
  (i : pfPos ar) -> (j : mpsOnPos dom i) -> (bd : pfDir {p=ar} i) ->
  mdir i j (mpsOnDir cod i (monpos i j) bd) = mpsOnDir dom i j bd

public export
record MlPolySlMor {ar : MLArena} (dom, cod : MlPolySlObj ar) where
  constructor MPSM
  mpsmOnPos : MlPolySlMorOnPos {ar} dom cod
  mpsmOnDir : MlPolySlMorOnDir {ar} dom cod mpsmOnPos
  mpsmOnDirCommutes : MlPolySlMorOnDirCommutes {ar} dom cod mpsmOnPos mpsmOnDir

------------------------------------------------------------------------
---- Categorial operations in polynomial/Dirichlet slice categories ----
------------------------------------------------------------------------

public export
mlPolySlMorId : {ar : MLArena} -> (p : MlPolySlObj ar) ->
  MlPolySlMor {ar} p p
mlPolySlMorId {ar} p =
  MPSM
    (sliceId {a=(pfPos ar)} $ mpsOnPos p)
    (\i => sliceId {a=(mpsOnPos p i)} (mpsDir p i))
    (\i, j, bd => Refl)

public export
mlPolySlMorComp : {ar : MLArena} -> {p, q, r : MlPolySlObj ar} ->
  MlPolySlMor {ar} q r -> MlPolySlMor {ar} p q -> MlPolySlMor {ar} p r
mlPolySlMorComp {ar} {p} {q} {r} m' m =
  MPSM
    (sliceComp (mpsmOnPos m') (mpsmOnPos m))
    (\i, j, rd => mpsmOnDir m i j $ mpsmOnDir m' i (mpsmOnPos m i j) rd)
    (\i, j, bd =>
      trans
        (cong (mpsmOnDir m i j) $ mpsmOnDirCommutes m' i (mpsmOnPos m i j) bd)
        (mpsmOnDirCommutes m i j bd))

----------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style morphisms ----
----------------------------------------------------------------------

public export
mlPolySlMorOnPos : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  mlPolySlObjTotPos {ar} dom -> mlPolySlObjTotPos {ar} cod
mlPolySlMorOnPos {ar} {dom} {cod} m i = (fst i ** mpsmOnPos m (fst i) (snd i))

public export
mlPolySlMorOnDir : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  (m : MlPolySlMor {ar} dom cod) ->
  (i : mlPolySlObjTotPos {ar} dom) ->
  mlPolySlObjTotDir {ar} cod (mlPolySlMorOnPos {ar} {dom} {cod} m i) ->
  mlPolySlObjTotDir {ar} dom i
mlPolySlMorOnDir {ar} {dom} {cod} m i = mpsmOnDir m (fst i) (snd i)

public export
mlPolySlMorNT : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  PolyNatTrans (mlPolySlObjTot {ar} dom) (mlPolySlObjTot {ar} cod)
mlPolySlMorNT {ar} {dom} {cod} m =
  (mlPolySlMorOnPos {ar} {dom} {cod} m ** mlPolySlMorOnDir {ar} {dom} {cod} m)

public export
0 mlPolySlMorToCP : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  CPFSliceMorph ar (mlPolySlObjToC ar dom) (mlPolySlObjToC ar cod)
mlPolySlMorToCP {ar=ar@(bpos ** bdir)}
  {dom=dom@(MPSobj dpos ddir dondir)} {cod=cod@(MPSobj cpos cdir condir)}
  m@(MPSM monpos mondir mondirc) =
    Element0
      (mlPolySlMorNT {ar} {dom} {cod} m)
      (Evidence0
        (\_ => Refl)
        (\ij, bd => mondirc (fst ij) (snd ij) bd))

public export
0 mlPolySlMorFromCP : {ar : MLArena} -> {dom, cod : CPFSliceObj ar} ->
  CPFSliceMorph ar dom cod ->
  MlPolySlMor {ar} (mlPolySlObjFromC ar dom) (mlPolySlObjFromC ar cod)
mlPolySlMorFromCP {ar=(bpos ** bdir)}
  {dom=dom@((dpos ** ddir) ** (donpos ** dondir))}
  {cod=cod@((cpos ** cdir) ** (conpos ** condir))}
  m@(Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MPSM
      (\i, (Element0 j poseq) =>
        Element0 (monpos j) $ trans (sym (opeq j)) poseq)
      (\i, (Element0 j poseq), cd => mondir j cd)
      (\i, (Element0 j poseq), bd => odeq j $ rewrite poseq in bd)

public export
0 mlPolySlMorToP : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  PFSliceMorph {p=ar} (mlPolySlObjToC ar cod)
mlPolySlMorToP {ar} {dom} {cod} =
  PFSliceMorphFromC {p=ar}
    {dom=(mlPolySlObjToC ar dom)} {cod=(mlPolySlObjToC ar cod)}
  . mlPolySlMorToCP {ar} {dom} {cod}

public export
0 mlPolySlMorFromP : {ar : MLArena} -> {cod : CPFSliceObj ar} ->
  (m : PFSliceMorph {p=ar} cod) ->
  MlPolySlMor {ar}
    (mlPolySlObjFromC ar $ PFSliceMorphDom {p=ar} {cod} m)
    (mlPolySlObjFromC ar cod)
mlPolySlMorFromP {ar} {cod} m =
  mlPolySlMorFromCP {ar} {dom=(PFSliceMorphDom {p=ar} m)} {cod}
  $ PFSliceMorphToC {p=ar} {cod} m

------------------------------------------------------------------
---- Translation between slice morphisms and slices-of-slices ----
------------------------------------------------------------------

public export
MlPolySlMorFromSlOfSl : {ar : MLArena} ->
  (cod : MlPolySlObj ar) -> (slsl : MlPolySlOfSl {ar} cod) ->
  MlPolySlMor {ar} (MlPolySlFromSlOfSl {ar} cod slsl) cod
MlPolySlMorFromSlOfSl {ar=(_ ** _)} (MPSobj _ _ _) slsl =
  MPSM
    (\i, jk => fst jk)
    (\i, jk, cd => (cd, mpsOnDir slsl (i ** fst jk) (snd jk) cd))
    (\i, jk, cd => Refl)

public export
MlPolySlMorToSlOfSl : {ar : MLArena} ->
  {dom, cod : MlPolySlObj ar} -> MlPolySlMor {ar} dom cod ->
  MlPolySlOfSl {ar} cod
MlPolySlMorToSlOfSl {ar} {dom} {cod} m =
  mlPolySlObjFromC
    (mlPolySlObjTot {ar} cod)
    (mlPolySlObjTot {ar} dom ** mlPolySlMorNT m)

public export
mlPolySlMorToObj : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> MlPolySlObj ar
mlPolySlMorToObj {ar} {dom} {cod} =
  MlPolySlFromSlOfSl {ar} cod . MlPolySlMorToSlOfSl {ar}

public export
mlPolySlMorTot : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> PolyFunc
mlPolySlMorTot {ar} {dom} {cod} =
  mlPolySlObjTot {ar=(mlPolySlObjTot {ar} cod)}
  . MlPolySlMorToSlOfSl {dom} {ar}

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Interpretation of polynomial/Dirichlet slice objects/morphisms ----
------------------------------------------------------------------------
------------------------------------------------------------------------

public export
InterpMlDirichSlObjGenElBase : {ar : MLDirichCatObj} ->
  (sl : MlDirichSlObj ar) -> (ty : Type) -> (idf : InterpDirichFunc ar ty) ->
  mdsOnPos sl (idfPos {p=ar} idf) -> SliceObj ty
InterpMlDirichSlObjGenElBase {ar} sl ty idf =
  BaseChangeF (snd idf) . mdsDir sl (fst idf)

public export
InterpMlDirichSlObjGenElPullback : {ar : MLDirichCatObj} ->
  (sl : MlDirichSlObj ar) -> (ty : Type) -> (idf : InterpDirichFunc ar ty) ->
  mdsOnPos sl (idfPos {p=ar} idf) -> SliceObj ty
InterpMlDirichSlObjGenElPullback {ar} sl ty idf j el =
  PullbackToSl ty (InterpMlDirichSlObjGenElBase {ar} sl ty idf j el) el

-- This interprets an object in a slice category of Dirichlet functors
-- as an object in the category of presheaves over the category of elements
-- of the base functor.
--
-- As described in https://ncatlab.org/nlab/show/generalized+element#in_toposes,
-- this global element (i.e. morphism from the terminal object) of the slice
-- category of `Type` over `ty` corresponds to a generalized element of
-- `InterpMlDirichSlObjGenElPullback {ar} sl ty j`, with domain `ty`.
public export
InterpMlDirichSlObjDirMap : {ar : MLDirichCatObj} ->
  (sl : MlDirichSlObj ar) -> (ty : Type) -> (idf : InterpDirichFunc ar ty) ->
  SliceObj (mdsOnPos sl (idfPos {p=ar} idf))
InterpMlDirichSlObjDirMap {ar} sl ty idf j =
  SliceMorphism {a=ty}
    (SliceObjTerminal ty)
    (InterpMlDirichSlObjGenElPullback {ar} sl ty idf j)

public export
InterpMlDirichSlObj : {ar : MLDirichCatObj} ->
  MlDirichSlObj ar -> (ty : Type) -> SliceObj $ InterpDirichFunc ar ty
InterpMlDirichSlObj {ar} sl ty idf =
  Sigma {a=(mdsOnPos sl (idfPos {p=ar} idf))} $
    InterpMlDirichSlObjDirMap {ar} sl ty idf

public export
InterpMlDirichSlObjF : {ar : MLDirichCatObj} ->
  MlDirichSlObj ar -> MLDirichCatElemObj ar -> Type
InterpMlDirichSlObjF {ar=ar@(_ ** _)} sl (ty ** el) =
  InterpMlDirichSlObj {ar} sl ty el

public export
InterpMlDirichSlObjFMap : {bpos : Type} -> {bdir : bpos -> Type} ->
  (sl : MlDirichSlObj (bpos ** bdir)) ->
  (dom, cod : MLDirichCatElemObj (bpos ** bdir)) ->
  -- The functor is contravariant, hence the `cod dom` rather than `dom cod`.
  MLDirichCatElemMor (bpos ** bdir) cod dom ->
  InterpMlDirichSlObjF {ar=(bpos ** bdir)} sl dom ->
  InterpMlDirichSlObjF {ar=(bpos ** bdir)} sl cod
InterpMlDirichSlObjFMap {bpos} {bdir} (MDSobj slpos sldir)
  (dty ** i ** sldty) (cty ** _ ** _) (DCEM _ _ _ _ _ _ _ mm) =
    \(j ** sld) => (j ** \ec => sld $ mm ec)

public export
InterpMlDirichSlObjFMapAr : {ar : MLDirichCatObj} ->
  (sl : MlDirichSlObj ar) ->
  (dom, cod : MLDirichCatElemObj ar) ->
  MLDirichCatElemMor ar cod dom ->
  InterpMlDirichSlObjF {ar} sl dom ->
  InterpMlDirichSlObjF {ar} sl cod
InterpMlDirichSlObjFMapAr {ar=(bpos ** bdir)} =
  InterpMlDirichSlObjFMap {bpos} {bdir}

-- This interprets a morphism in a slice category of Dirichlet functors
-- as a morphism in the category of presheaves over the category of elements
-- of the base functor (the latter is a natural transformation).
--
-- This implements a proof, in the particular case of Dirichlet functors,
-- that a slice category over a presheaf `p` is a presheaf over the category
-- of elements of `p`.
--
-- We may view this as the morphism component of a functor, whose object
-- component is `InterpMlDirichSlObj`, from the slice category of Dirichlet
-- functors over `ar` to the category of presheaves over the category of
-- elements of `ar`.
public export
InterpMlDirichSlMor : {ar : MLDirichCatObj} ->
  {dom, cod : MlDirichSlObj ar} -> MlDirichSlMor dom cod ->
  (ty : Type) ->
  SliceMorphism {a=(InterpDirichFunc ar ty)}
    (InterpMlDirichSlObj {ar} dom ty)
    (InterpMlDirichSlObj {ar} cod ty)
InterpMlDirichSlMor {ar=(bpos ** bdir)}
  {dom=(MDSobj dpos ddir)} {cod=(MDSobj cpos cdir)}
  (MDSM monpos mondir) ty (i ** bd) dpd =
    (monpos i (fst dpd) **
     \elty, _ => mondir i (fst dpd) (bd elty) $ snd dpd elty ())

-- This interprets an object in a slice category of polynomial functors
-- as an object in the category of copresheaves over the category of elements
-- of the base functor.
public export
InterpMlPolySlObj : {ar : PolyFunc} ->
  MlPolySlObj ar -> (ty : Type) -> SliceObj $ InterpPolyFunc ar ty
InterpMlPolySlObj {ar} sl ty el with (mlPolySlObjToC ar sl)
  InterpMlPolySlObj {ar} sl ty el | (q ** alpha) =
    PreImage {a=(InterpPolyFunc q ty)} {b=(InterpPolyFunc ar ty)}
      (InterpPolyNT alpha ty) el

public export
InterpMlPolySlObjF : {ar : PolyFunc} ->
  MlPolySlObj ar -> MLPolyCatElemObj ar -> Type
InterpMlPolySlObjF {ar=ar@(_ ** _)} sl (ty ** el) =
  InterpMlPolySlObj {ar} sl ty el

public export
InterpMlPolySlObjFMap : {bpos : Type} -> {bdir : bpos -> Type} ->
  (sl : MlPolySlObj (bpos ** bdir)) ->
  (dom, cod : MLPolyCatElemObj (bpos ** bdir)) ->
  MLPolyCatElemMor (bpos ** bdir) dom cod ->
  InterpMlPolySlObjF {ar=(bpos ** bdir)} sl dom ->
  InterpMlPolySlObjF {ar=(bpos ** bdir)} sl cod
InterpMlPolySlObjFMap {bpos} {bdir} (MPSobj slpos sldir slondir)
  (dty ** i ** sldty) (cty ** _ ** _) (PCEM _ _ _ _ _ _ _ mm) =
    \(Element0 ((j ** k) ** sldi) eq) =>
      Element0
        ((j ** k) ** mm . sldi)
        $ case eq of Refl => Refl

public export
InterpMlPolySlObjFMapAr : {ar : PolyFunc} ->
  (sl : MlPolySlObj ar) ->
  (dom, cod : MLPolyCatElemObj ar) ->
  MLPolyCatElemMor ar dom cod ->
  InterpMlPolySlObjF {ar} sl dom ->
  InterpMlPolySlObjF {ar} sl cod
InterpMlPolySlObjFMapAr {ar=(bpos ** bdir)} =
  InterpMlPolySlObjFMap {bpos} {bdir}

-- This interprets a morphism in a slice category of polynomial functors
-- as a morphism in the category of copresheaves over the category of elements
-- of the base functor (the latter is a natural transformation).
--
-- This implements a proof, in the particular case of polynomial functors,
-- that a slice category over a copresheaf `p` is a copresheaf over the category
-- of elements of `p`.
--
-- We may view this as the morphism component of a functor, whose object
-- component is `InterpMlPolySlObj`, from the slice category of polynomial
-- functors over `ar` to the category of copresheaves over the category of
-- elements of `ar`.
public export
InterpMlPolySlMor : FunExt -> {ar : PolyFunc} ->
  {dom, cod : MlPolySlObj ar} -> MlPolySlMor dom cod ->
  (ty : Type) -> (el : InterpPolyFunc ar ty) ->
  InterpMlPolySlObj {ar} dom ty el ->
  InterpMlPolySlObj {ar} cod ty el
InterpMlPolySlMor fext {ar=(bpos ** bdir)}
  {dom=(MPSobj dpos ddir dondir)} {cod=(MPSobj cpos cdir condir)}
  (MPSM monpos mondir mondircomm) ty el (Element0 (i ** dd) eleq) =
    Element0
      ((fst i ** monpos (fst i) (snd i)) **
       \cd => dd $ mondir (fst i) (snd i) cd)
      $ trans
        (dpEq12 Refl $ funExt $ \bd => cong dd $ mondircomm (fst i) (snd i) bd)
        eleq
