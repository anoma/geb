module LanguageDef.PolyDifunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.DisliceCat
import public LanguageDef.PolyCat
import public LanguageDef.DislicePolyCat
import public LanguageDef.IntECofamCat
import public LanguageDef.GenPolyFunc
import public LanguageDef.IntDisheafCat

%default total
%hide Library.IdrisCategories.BaseChangeF
%hide Prelude.Ops.infixl.(|>)

----------------------------------------------------
----------------------------------------------------
---- PRA functors from `PolyFunc` to `PolyFunc` ----
----------------------------------------------------
----------------------------------------------------

-- The data which determine a parametric right adjoint endofunctor on
-- the category of polynomial functors on `Type`.
public export
PolyEndoPRA : Type
PolyEndoPRA = (pp : Type ** dp : SliceObj pp ** (pi : pp) -> SliceObj (dp pi))

public export
InterpPolyEndoPRApos : PolyEndoPRA -> PolyFunc -> Type
InterpPolyEndoPRApos (pp ** dp ** dd) (qpos ** qdir) =
  InterpPolyFunc (pp ** dp) qpos

public export
InterpPolyEndoPRAposMap : (pra : PolyEndoPRA) -> (q, r : PolyFunc) ->
  PolyNatTrans q r -> InterpPolyEndoPRApos pra q -> InterpPolyEndoPRApos pra r
InterpPolyEndoPRAposMap (pp ** dp ** dd) (qpos ** qdir) (rpos ** rdir)
  (onpos ** ondir) (pi ** pm) =
    (pi ** onpos . pm)

public export
InterpPolyEndoPRAdir : (pra : PolyEndoPRA) -> (q : PolyFunc) ->
  InterpPolyEndoPRApos pra q -> Type
InterpPolyEndoPRAdir (pp ** dp ** dd) (qpos ** qdir) (pi ** pm) =
  (dp : dp pi ** Either (qdir $ pm dp) (dd pi dp))

public export
InterpPolyEndoPRAdirMap : (pra : PolyEndoPRA) -> (q, r : PolyFunc) ->
  (alpha : PolyNatTrans q r) ->
  (qi : InterpPolyEndoPRApos pra q) ->
  InterpPolyEndoPRAdir pra r (InterpPolyEndoPRAposMap pra q r alpha qi) ->
  InterpPolyEndoPRAdir pra q qi
InterpPolyEndoPRAdirMap (pp ** dp ** dd) (qpos ** qdir) (rpos ** rdir)
  (onpos ** ondir) (pi ** qpm) (dpi ** dpd) =
    (dpi ** mapFst (ondir $ qpm dpi) dpd)

public export
InterpPolyEndoPRA : PolyEndoPRA -> PolyFunc -> PolyFunc
InterpPolyEndoPRA pra q =
  (InterpPolyEndoPRApos pra q ** InterpPolyEndoPRAdir pra q)

public export
InterpPolyEndoPRAmap : (pra : PolyEndoPRA) -> (q, r : PolyFunc) ->
  PolyNatTrans q r ->
  PolyNatTrans (InterpPolyEndoPRA pra q) (InterpPolyEndoPRA pra r)
InterpPolyEndoPRAmap pra q r alpha =
  (InterpPolyEndoPRAposMap pra q r alpha **
   InterpPolyEndoPRAdirMap pra q r alpha)

-------------------------------------
---- In the style of `MLDirichF` ----
-------------------------------------

public export
MLPolyF1 : Type
MLPolyF1 = MLDirichF1

public export
InterpMLPolyF1 : MLDirichF1 -> MLPolyCatObj -> Type
InterpMLPolyF1 f1 p = (i : mldPos1 f1 ** PolyNatTrans (mldET1 f1 i) p)

public export
0 MLPF1elExtEq : {f1 : MLPolyF1} -> {p : MLPolyCatObj} ->
  IntMorSig (InterpMLPolyF1 f1 p)
MLPF1elExtEq {f1} {p} el el' =
  (fsteq :
    fst el = fst el' **
   onposeq :
    (i : mldET1Pos f1 (fst el)) ->
      fst (snd el) i = fst (snd el') (rewrite sym fsteq in i) **
   (i : mldET1Pos f1 (fst el)) -> (d : pfDir {p} (fst (snd el) i)) ->
      snd (snd el) i d =
      (rewrite fsteq in
       snd (snd el') (rewrite sym fsteq in i) $ rewrite sym (onposeq i) in d))

public export
InterpMLPolyF1map : (f1 : MLPolyF1) -> {p, q : MLPolyCatObj} ->
  PolyNatTrans p q -> InterpMLPolyF1 f1 p -> InterpMLPolyF1 f1 q
InterpMLPolyF1map f1 {p} {q} alpha =
  dpMapSnd $ \pi => pntVCatComp {p=(mldET1 f1 pi)} alpha

public export
MLPolyF1NT : IntMorSig MLPolyF1
MLPolyF1NT p q =
  (onpos1 : mldPos1 p -> mldPos1 q **
   onpos2 : (pi : mldPos1 p) -> mldET1Pos q (onpos1 pi) -> mldET1Pos p pi **
   (pi : mldPos1 p) -> (qi : mldET1Pos q (onpos1 pi)) ->
    mldET1Dir p pi (onpos2 pi qi) -> mldET1Dir q (onpos1 pi) qi)

-------------------------------------------
-------------------------------------------
---- PRA endofunctors on `TwArr(Type)` ----
-------------------------------------------
-------------------------------------------

-- The data which determine a parametric right adjoint endofunctor on
-- the category of polynomial functors on `Type`.
public export
TwArrEndoPRA : Type
TwArrEndoPRA =
  (pp : Type **
   dp : SliceObj pp **
   dd : (pi : pp) -> SliceObj (dp pi) **
   (pi : pp) -> (di : dp pi) -> SliceObj (dd pi di))

public export
taepPosPos : TwArrEndoPRA -> Type
taepPosPos = DPair.fst

public export
taepDirPos : (taep : TwArrEndoPRA) -> SliceObj (taepPosPos taep)
taepDirPos taep = DPair.fst (DPair.snd taep)

public export
taepDirPosTot : TwArrEndoPRA -> Type
taepDirPosTot taep = Sigma {a=(taepPosPos taep)} (taepDirPos taep)

public export
taepDirDir : (taep : TwArrEndoPRA) ->
  (pi : taepPosPos taep) -> SliceObj (taepDirPos taep pi)
taepDirDir taep = DPair.fst (DPair.snd $ DPair.snd taep)

public export
taepDirDirDep : (taep : TwArrEndoPRA) -> SliceObj (taepDirPosTot taep)
taepDirDirDep taep = DPair.uncurry (taepDirDir taep)

public export
taepDirDirTot : TwArrEndoPRA -> Type
taepDirDirTot taep = Sigma {a=(taepDirPosTot taep)} (taepDirDirDep taep)

public export
taepPosDir : (taep : TwArrEndoPRA) ->
  (pi : taepPosPos taep) -> (di : taepDirPos taep pi) ->
  SliceObj (taepDirDir taep pi di)
taepPosDir taep = DPair.snd (DPair.snd $ DPair.snd taep)

public export
taepPosDirDep : (taep : TwArrEndoPRA) -> SliceObj (taepPosPos taep)
taepPosDirDep taep pi =
  (di : taepDirPos taep pi **
   dd : taepDirDir taep pi di **
   taepPosDir taep pi di dd)

public export
taepPos : TwArrEndoPRA -> PolyFunc
taepPos taep = (taepPosPos taep ** taepPosDirDep taep)

public export
taepDir : TwArrEndoPRA -> PolyFunc
taepDir taep = (taepDirPosTot taep ** taepDirDirDep taep)

public export
taepToTwArrM : (taep : TwArrEndoPRA) ->
  TwArrMsl
    {b=(taepDirPosTot taep)}
    {b'=(taepPosPos taep)}
    (taepDirDirDep taep)
    (taepPosDirDep taep)
taepToTwArrM (pp ** dp ** dd ** pd) =
  (DPair.fst **
   \pi, (di ** dd ** pd) => Element0 (pi ** di) Refl **
   \pi, (di ** dd ** pd) => dd)

public export
taepFromTwArrM :
  {dp, pp : Type} -> (dd : SliceObj dp) -> (pd : SliceObj pp) ->
  TwArrMsl {b=dp} {b'=pp} dd pd ->
  TwArrEndoPRA
taepFromTwArrM {dp} {pp} dd pd (mcov ** mcont1 ** mcont2) =
  (pp **
   \pi =>
    PreImage {a=dp} {b=pp} mcov pi **
   \pi, (Element0 di pcov) =>
    dd di **
   \pi, (Element0 di pcov), dd =>
    Subset0
      (pd pi)
      (\pdd =>
        (eq1 : fst0 (mcont1 pi pdd) = di **
         mcont2 pi pdd = (rewrite eq1 in dd))))

------------------------------------------
------------------------------------------
---- Slices of covariant hom-functors ----
------------------------------------------
------------------------------------------

-- A slice over the covariant hom-functor of `a` is a polynomial
-- functor together with an `a`-way selection of its directions.
public export
CovHomSlice : Type -> Type
CovHomSlice a = (pos : Type ** dir : SliceObj pos ** (i : pos) -> a -> dir i)

public export
CovHomCoslice : Type -> Type
CovHomCoslice a =
  (pos : Type ** dir : SliceObj pos ** InterpPolyFunc (pos ** dir) a)

public export
chsPos : {a : Type} -> CovHomSlice a -> Type
chsPos {a} = DPair.fst

public export
chsDir : {a : Type} -> (sl : CovHomSlice a) -> SliceObj (chsPos {a} sl)
chsDir {a} sl = DPair.fst (DPair.snd sl)

public export
chsOnDir : {a : Type} -> (sl : CovHomSlice a) ->
  (i : chsPos {a} sl) -> a -> chsDir {a} sl i
chsOnDir {a} sl = DPair.snd (DPair.snd sl)

public export
chsTot : {a : Type} -> CovHomSlice a -> PolyFunc
chsTot {a} sl = (chsPos sl ** chsDir sl)

public export
chsTotInterp : {a : Type} -> CovHomSlice a -> Type -> Type
chsTotInterp {a} sl = InterpPolyFunc (chsTot {a} sl)

public export
chsProj : {a : Type} -> (sl : CovHomSlice a) ->
  PolyNatTrans (chsTot {a} sl) (PFHomArena a)
chsProj {a} sl = (\_ => () ** chsOnDir {a} sl)

public export
chsProjInterp : {a : Type} -> (sl : CovHomSlice a) ->
  NaturalTransformation (chsTotInterp {a} sl) (CovarHomFunc a)
chsProjInterp {a} sl x =
  DPair.snd
  . InterpPolyNT {p=(chsTot {a} sl)} {q=(PFHomArena a)} (chsProj {a} sl) x

public export
0 chiProjInterpExplicit : {a : Type} -> (sl : CovHomSlice a) -> (x : Type) ->
  (i : chsPos sl) -> (dm : chsDir {a} sl i -> x) ->
  chsProjInterp {a} sl x (i ** dm) = dm . chsOnDir {a} sl i
chiProjInterpExplicit {a} sl x i dm = Refl

-- A slice over a copresheaf is a copresheaf on its category of
-- elements.  Here is the specific case in which we compute a
-- copresheaf on the category of elements of a covariant hom-functor
-- from a slice over it.
public export
CovHomElemCopr : (a : Type) -> CovHomSlice a -> (x : Type) -> (a -> x) -> Type
CovHomElemCopr a sl x max =
  (i : chsPos {a} sl **
   dm : chsDir {a} sl i -> x **
   ExtEq {a=a} {b=x} (dm . chsOnDir {a} sl i) max)

public export
CovHomElemCoprMap : (a : Type) -> (sl : CovHomSlice a) ->
  (x, y : Type) -> (max : a -> x) -> (mxy : x -> y) ->
  CovHomElemCopr a sl x max ->
  CovHomElemCopr a sl y (mxy . max)
CovHomElemCoprMap a sl x y max mxy =
  dpMapSnd $ \sli => dpBimap ((.) mxy) $ \dmx, comm, ea => cong mxy $ comm ea

-- A morphism between slices of a given covariant hom-functor
-- is a natural transformation between the total spaces which
-- commutes with the projections.
public export
CovHomSliceMor : {a : Type} -> IntMorSig (CovHomSlice a)
CovHomSliceMor {a} sl sl' =
  (onpos : chsPos sl -> chsPos sl' **
   ondir : (i : chsPos sl) -> chsDir sl' (onpos i) -> chsDir sl i **
   (i : chsPos sl) ->
      ExtEq {a=a} {b=(chsDir sl i)}
        (ondir i . chsOnDir sl' (onpos i))
        (chsOnDir sl i))

public export
chsmOnPos : {a : Type} -> {sl, sl' : CovHomSlice a} ->
  CovHomSliceMor {a} sl sl' -> chsPos sl -> chsPos sl'
chsmOnPos {a} {sl} {sl'} = DPair.fst

public export
chsmOnDir : {a : Type} -> {sl, sl' : CovHomSlice a} ->
  (m : CovHomSliceMor {a} sl sl') -> (i : chsPos sl) ->
  chsDir sl' (chsmOnPos {a} {sl} {sl'} m i) -> chsDir sl i
chsmOnDir {a} {sl} {sl'} m = DPair.fst (DPair.snd m)

public export
chsmComm : {a : Type} -> {sl, sl' : CovHomSlice a} ->
  (m : CovHomSliceMor {a} sl sl') -> (i : chsPos sl) ->
  ExtEq {a=a} {b=(chsDir sl i)}
    (chsmOnDir {sl} {sl'} m i . chsOnDir sl' (chsmOnPos {sl} {sl'} m i))
    (chsOnDir sl i)
chsmComm {a} {sl} {sl'} m = DPair.snd (DPair.snd m)

-- As slice objects induce copresheaves, slice morphisms induce
-- natural transformations between copresheaves.
public export
CovHomElemCoprNT : {a : Type} -> {sl, sl' : CovHomSlice a} ->
  CovHomSliceMor {a} sl sl' ->
  (x : Type) -> (max : a -> x) ->
  CovHomElemCopr a sl x max -> CovHomElemCopr a sl' x max
CovHomElemCoprNT {a} {sl} {sl'} slm x max =
  dpBimap (chsmOnPos slm) $ \i =>
    dpBimap
      ((|>) (chsmOnDir slm i))
      (\dm, comm, ea => trans (cong dm $ chsmComm slm i ea) (comm ea))

--------------------------------------------
--------------------------------------------
---- Coslices of covariant hom-functors ----
--------------------------------------------
--------------------------------------------

public export
chcsPos : {a : Type} -> CovHomCoslice a -> Type
chcsPos {a} = DPair.fst

public export
chcsDir : {a : Type} -> (sl : CovHomCoslice a) -> SliceObj (chcsPos {a} sl)
chcsDir {a} sl = DPair.fst (DPair.snd sl)

public export
chcsCotot : {a : Type} -> (sl : CovHomCoslice a) -> PolyFunc
chcsCotot {a} sl = (chcsPos {a} sl ** chcsDir {a} sl)

public export
chcsEl : {a : Type} -> (sl : CovHomCoslice a) ->
  InterpPolyFunc (chcsCotot {a} sl) a
chcsEl {a} sl = DPair.snd (DPair.snd sl)

public export
chcsElPos : {a : Type} -> (sl : CovHomCoslice a) -> chcsPos {a} sl
chcsElPos {a} sl = DPair.fst (chcsEl {a} sl)

public export
chcsElDirMap : {a : Type} -> (sl : CovHomCoslice a) ->
  chcsDir {a} sl (chcsElPos {a} sl) -> a
chcsElDirMap {a} sl = DPair.snd (chcsEl {a} sl)

public export
chcsCototInterp : {a : Type} -> CovHomCoslice a -> Type -> Type
chcsCototInterp {a} sl = InterpPolyFunc (chcsCotot {a} sl)

public export
chcsCoproj : {a : Type} -> (sl : CovHomCoslice a) ->
  PolyNatTrans (PFHomArena a) (chcsCotot {a} sl)
chcsCoproj {a} sl =
  dpBimap (flip $ \_ => id) (\_ => flip $ \_ => id) (chcsEl {a} sl)

public export
chcsCoprojInterp : {a : Type} -> (sl : CovHomCoslice a) ->
  NaturalTransformation (CovarHomFunc a) (chcsCototInterp {a} sl)
chcsCoprojInterp {a} sl x =
  InterpPolyNT {p=(PFHomArena a)} {q=(chcsCotot {a} sl)} (chcsCoproj {a} sl) x
  . MkDPair ()

public export
0 chciCoprojInterpExplicit : {a : Type} -> (sl : CovHomCoslice a) ->
  (x : Type) -> (max : a -> x) ->
  chcsCoprojInterp {a} sl x max =
    InterpPFMap {a=a} {b=x} (chcsCotot {a} sl) max (chcsEl {a} sl)
chciCoprojInterpExplicit {a} sl x max = Refl

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Polynomial difunctors on `Type` as coproducts of dialgebras ----
---------------------------------------------------------------------
---------------------------------------------------------------------

public export
PolyDiProf : Type
PolyDiProf =
  (polyPos : Type **
   contraPos : SliceObj polyPos **
   contraDir : Pi {a=polyPos} (SliceObj . contraPos) **
   covarPos : Pi {a=polyPos} (SliceObj . contraPos) **
   {-covarDir:-} (i : polyPos) -> (j : contraPos i) -> SliceObj (covarPos i j))

public export
InterpPDP : PolyDiProf -> Type -> Type -> Type
InterpPDP (polyPos ** contraPos ** contraDir ** covarPos ** covarDir) j z =
  (i : polyPos **
   (el : InterpPolyFunc (contraPos i ** contraDir i) j) ->
    InterpPolyFunc (covarPos i (fst el) ** covarDir i (fst el)) z)

public export
InterpPDPtw : PolyDiProf -> TwArrCoprSig
InterpPDPtw
  (polyPos ** contraPos ** contraDir ** covarPos ** covarDir) j z mjz =
    (i : polyPos **
     (el : InterpPolyFunc (contraPos i ** contraDir i) j) ->
      InterpPolyFunc (covarPos i (fst el) ** covarDir i (fst el)) z)

public export
InterpPDPdimap : (pdp : PolyDiProf) -> (s, t, a, b : Type) ->
  (a -> s) -> (t -> b) -> InterpPDP pdp s t -> InterpPDP pdp a b
InterpPDPdimap (polyPos ** contraPos ** contraDir ** covarPos ** covarDir)
  s t a b mas mtb (ipoly ** dialg) =
    (ipoly ** \ic =>
      let idm = dialg (fst ic ** mas . snd ic) in
      (fst idm ** mtb . snd idm))

public export
PDPnt : IntMorSig PolyDiProf
PDPnt
  (ppolyPos ** pcontraPos ** pcontraDir ** pcovarPos ** pcovarDir)
  (qpolyPos ** qcontraPos ** qcontraDir ** qcovarPos ** qcovarDir) =
    (onpoly : ppolyPos -> qpolyPos **
     oncontraPos : (i : ppolyPos) -> qcontraPos (onpoly i) -> pcontraPos i **
     oncontraDir : (i : ppolyPos) -> (j : qcontraPos (onpoly i)) ->
      pcontraDir i (oncontraPos i j) -> qcontraDir (onpoly i) j **
     oncovarPos : (i : ppolyPos) -> (j : qcontraPos (onpoly i)) ->
      pcovarPos i (oncontraPos i j) -> qcovarPos (onpoly i) j **
     (i : ppolyPos) -> (j : qcontraPos (onpoly i)) ->
      (k : pcovarPos i (oncontraPos i j)) ->
      qcovarDir (onpoly i) j (oncovarPos i j k) ->
      pcovarDir i (oncontraPos i j) k)

public export
InterpPDPnt : {p, q : PolyDiProf} -> PDPnt p q ->
  TypeProfNT (InterpPDP p) (InterpPDP q)
InterpPDPnt
  {p=(ppolyPos ** pcontraPos ** pcontraDir ** pcovarPos ** pcovarDir)}
  {q=(qpolyPos ** qcontraPos ** qcontraDir ** qcovarPos ** qcovarDir)}
  (onpoly ** onContraPos ** onContraDir ** onCovarPos ** onCovarDir)
  x y (pipoly ** dialg) =
    (onpoly pipoly **
     \qidmcontra =>
      let
        pidmcovar =
          dialg
            (onContraPos pipoly (fst qidmcontra) **
             snd qidmcontra . onContraDir pipoly (fst qidmcontra))
      in
      (onCovarPos pipoly (fst qidmcontra) (fst pidmcovar) **
       snd pidmcovar . onCovarDir pipoly (fst qidmcontra) (fst pidmcovar)))

public export
PDPcoprod : PolyDiProf -> PolyDiProf -> PolyDiProf
PDPcoprod
  (polyPos1 ** contraPos1 ** contraDir1 ** covarPos1 ** covarDir1)
  (polyPos2 ** contraPos2 ** contraDir2 ** covarPos2 ** covarDir2) =
    (Either polyPos1 polyPos2 **
     \ipoly => case ipoly of
      Left ipoly1 => contraPos1 ipoly1
      Right ipoly2 => contraPos2 ipoly2 **
     \ipoly => case ipoly of
      Left ipoly1 => contraDir1 ipoly1
      Right ipoly2 => contraDir2 ipoly2 **
     \ipoly => case ipoly of
      Left ipoly1 => covarPos1 ipoly1
      Right ipoly2 => covarPos2 ipoly2 **
     \ipoly => case ipoly of
      Left ipoly1 => covarDir1 ipoly1
      Right ipoly2 => covarDir2 ipoly2)

public export
PDPtoCoprod : (p, q : PolyDiProf) -> (j, z : Type) ->
  InterpPDP (PDPcoprod p q) j z -> Either (InterpPDP p j z) (InterpPDP q j z)
PDPtoCoprod
  (polyPos1 ** contraPos1 ** contraDir1 ** covarPos1 ** covarDir1)
  (polyPos2 ** contraPos2 ** contraDir2 ** covarPos2 ** covarDir2)
  j z (ipoly ** dialg) =
    case ipoly of
      Left ipoly1 => Left (ipoly1 ** dialg)
      Right ipoly2 => Right (ipoly2 ** dialg)

public export
PDPfromCoprod : (p, q : PolyDiProf) -> (j, z : Type) ->
  Either (InterpPDP p j z) (InterpPDP q j z) -> InterpPDP (PDPcoprod p q) j z
PDPfromCoprod
  (polyPos1 ** contraPos1 ** contraDir1 ** covarPos1 ** covarDir1)
  (polyPos2 ** contraPos2 ** contraDir2 ** covarPos2 ** covarDir2)
  j z ipd =
    case ipd of
      Left (ipoly1 ** dialg) => (Left ipoly1 ** dialg)
      Right (ipoly2 ** dialg) => (Right ipoly2 ** dialg)

public export
PDPprod : PolyDiProf -> PolyDiProf -> PolyDiProf
PDPprod
  (polyPos1 ** contraPos1 ** contraDir1 ** covarPos1 ** covarDir1)
  (polyPos2 ** contraPos2 ** contraDir2 ** covarPos2 ** covarDir2) =
    ((polyPos1, polyPos2) **
     \(ipoly1, ipoly2) =>
      Either (contraPos1 ipoly1) (contraPos2 ipoly2) **
     \(ipoly1, ipoly2) =>
      eitherElim (contraDir1 ipoly1) (contraDir2 ipoly2) **
     \(ipoly1, ipoly2) =>
      eitherElim (covarPos1 ipoly1) (covarPos2 ipoly2) **
     \(ipoly1, ipoly2), icontra, icovar => case icontra of
        Left icontra1 => covarDir1 ipoly1 icontra1 icovar
        Right icontra2 => covarDir2 ipoly2 icontra2 icovar)

public export
PDPtoProd : (p, q : PolyDiProf) -> (j, z : Type) ->
  InterpPDP (PDPprod p q) j z -> (InterpPDP p j z, InterpPDP q j z)
PDPtoProd
  (polyPos1 ** contraPos1 ** contraDir1 ** covarPos1 ** covarDir1)
  (polyPos2 ** contraPos2 ** contraDir2 ** covarPos2 ** covarDir2)
  j z ((ipoly1, ipoly2) ** dialg) =
    ((ipoly1 ** \(icontra1 ** dmcontra1) =>
      dialg (Left icontra1 ** dmcontra1)),
     (ipoly2 ** \(icontra2 ** dmcontra2) =>
      dialg (Right icontra2 ** dmcontra2)))

public export
PDPfromProd : (p, q : PolyDiProf) -> (j, z : Type) ->
  (InterpPDP p j z, InterpPDP q j z) ->
  InterpPDP (PDPprod p q) j z
PDPfromProd
  (polyPos1 ** contraPos1 ** contraDir1 ** covarPos1 ** covarDir1)
  (polyPos2 ** contraPos2 ** contraDir2 ** covarPos2 ** covarDir2)
  j z ((ipoly1 ** dialg1), (ipoly2 ** dialg2)) =
    ((ipoly1, ipoly2) **
     \(i ** dm) => case i of
      Left i1 => dialg1 (i1 ** dm)
      Right i2 => dialg2 (i2 ** dm))

----------------------------------------------------------------
---- Polynomial dialgebras as special cases of `PolyDiProf` ----
----------------------------------------------------------------

public export
PolyDialgToPDP : PolyFunc -> PolyFunc -> PolyDiProf
PolyDialgToPDP p q =
  (Unit **
   \_ => pfPos p **
   \_ => pfDir {p} **
   \_, _ => pfPos q **
   \_, _ => pfDir {p=q})

public export
InterpPolyDialgToPDP : (p, q : PolyFunc) ->
  (x, y : Type) ->
  (InterpPolyFunc p x -> InterpPolyFunc q y) ->
  InterpPDP (PolyDialgToPDP p q) x y
InterpPolyDialgToPDP p q x y = MkDPair ()

public export
InterpPolyDialgFromPDP : (p, q : PolyFunc) ->
  (x, y : Type) ->
  InterpPDP (PolyDialgToPDP p q) x y ->
  (InterpPolyFunc p x -> InterpPolyFunc q y)
InterpPolyDialgFromPDP p q x y = DPair.snd

----------------------------------------
---- `PolyDiProf` as `PolyPolyFunc` ----
----------------------------------------

public export
PolyPolyFunctorExp : PolyFunc -> PolyPolyFunc
PolyPolyFunctorExp = flip pfFunctorExpArena

public export
PolyDiProfToPP : PolyDiProf -> PolyPolyFunc
PolyDiProfToPP
  (polypos ** contrapos ** contradir ** covarpos ** covardir) a =
    pfSetCoproductArena {a=polypos}
      $ \ipoly => pfSetProductArena {a=(contrapos ipoly)}
        $ \icontra => pfFunctorExpArena
          (contradir ipoly icontra -> a)
          (covarpos ipoly icontra ** covardir ipoly icontra)

public export
PolyDiProfToPPposFormula : PolyDiProf -> Type -> Type
PolyDiProfToPPposFormula
  (polypos ** contrapos ** contradir ** covarpos ** covardir) a =
    (ipoly : polypos **
     (icontra : contrapos ipoly) ->
      (contradir ipoly icontra -> a) -> covarpos ipoly icontra)

public export
PolyDiProfToPPposToFormula : (pdp : PolyDiProf) -> (a : Type) ->
  pfPos (PolyDiProfToPP pdp a) -> PolyDiProfToPPposFormula pdp a
PolyDiProfToPPposToFormula
  (polypos ** contrapos ** contradir ** covarpos ** covardir) a ppi =
    ppi

public export
PolyDiProfToPPposFromFormula : (pdp : PolyDiProf) -> (a : Type) ->
  PolyDiProfToPPposFormula pdp a -> pfPos (PolyDiProfToPP pdp a)
PolyDiProfToPPposFromFormula
  (polypos ** contrapos ** contradir ** covarpos ** covardir) a ppfi =
    ppfi

public export
InterpPolyDiProfToPP : (p : PolyDiProf) ->
  (x, y : Type) -> InterpPDP p x y -> InterpPolyFunc (PolyDiProfToPP p x) y
InterpPolyDiProfToPP
  (polypos ** contrapos ** contradir ** covarpos ** covardir) x y
  (ipoly ** f) =
    ((ipoly ** \icontra, dmcontra => fst (f (icontra ** dmcontra))) **
     \(icontra ** dmcontra ** dcovar) => snd (f (icontra ** dmcontra)) dcovar)

public export
InterpPolyDiProfFromPP : (p : PolyDiProf) ->
  (x, y : Type) -> InterpPolyFunc (PolyDiProfToPP p x) y -> InterpPDP p x y
InterpPolyDiProfFromPP
  (polypos ** contrapos ** contradir ** covarpos ** covardir) x y
  ((ipoly ** dmp) ** dmy) =
    (ipoly ** \(icontra ** dmcontra) =>
      (dmp icontra dmcontra **
       \dcovar => dmy (icontra ** dmcontra ** dcovar)))

public export
PolyDiProfToPPcontramap : (p : PolyDiProf) ->
  PolyPolyFuncContramap (PolyDiProfToPP p)
PolyDiProfToPPcontramap
  (polypos ** contrapos ** contradir ** covarpos ** covardir) a b mba =
    (dpMapSnd $ \ipoly, dmp, icontra, dmb => dmp icontra (mba . dmb) **
     \(ipoly ** dmp), (icontra ** dmcontra ** dcovar) =>
      (icontra ** mba . dmcontra ** dcovar))

public export
PDPparamFix : PolyDiProf -> Type -> Type
PDPparamFix p = ProfToParamFix (PolyDiProfToPP p)

public export
PolyDiAlg : PolyDiProf -> Type -> Type -> Type
PolyDiAlg p a = PFAlg (PolyDiProfToPP p a)

public export
polyDiParamCata : (p : PolyDiProf) -> (a, b : Type) ->
  PolyDiAlg p a b -> PDPparamFix p a -> b
polyDiParamCata p = profToParamCata (PolyDiProfToPP p)

public export
PDPsquareFix : PolyDiProf -> Type -> Type
PDPsquareFix = SquareParamFix . PolyDiProfToPP

public export
PolyDiProfFix : PolyDiProf -> Type
PolyDiProfFix = Mu . PDPsquareFix

-----------------------------------------------------
---- Dirichlet functors embedded into PolyDiProf ----
-----------------------------------------------------

public export
DirichToPDP : MLDirichCatObj -> PolyDiProf
DirichToPDP p =
  (dfPos p ** \_ => () ** \_, _ => () ** \i, _ => dfDir p i ** \_, _, _ => Void)

public export
InterpDirichToPDP : (p : MLDirichCatObj) -> (a, b : Type) ->
  InterpDirichFunc p a -> InterpPDP (DirichToPDP p) a b
InterpDirichToPDP p a b idm =
  (fst idm ** \ufa => (snd idm (snd ufa ()) ** \ev => void ev))

public export
InterpDirichFromPDP : (p : MLDirichCatObj) -> (a, b : Type) ->
  InterpPDP (DirichToPDP p) a b -> InterpDirichFunc p a
InterpDirichFromPDP p a b idm =
  (fst idm ** \ea => fst $ snd idm (() ** \_ => ea))

public export
InterpDirichToPDPdimap : FunExt ->
  (p : MLDirichCatObj) -> (s, t, a, b : Type) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  (el : InterpPDP (DirichToPDP p) s t) ->
  InterpPDPdimap (DirichToPDP p) s t a b mas mtb el =
  InterpDirichToPDP p a b (InterpDFMap p mas $ InterpDirichFromPDP p s t el)
InterpDirichToPDPdimap fext (pos ** dir) s t a b mas mtb (i ** dm) =
  dpEq12
    Refl
    (funExt $ \(() ** fa) =>
      dpEq12
        (let
          eq : ((\x => mas (fa x)) = (\_ => mas (fa ()))) = funExt $ \() => Refl
         in
         rewrite eq in
         Refl)
        (funExt $ \ev => void ev))

public export
InterpDirichFromPDPdimap : FunExt ->
  (p : MLDirichCatObj) -> (s, t, a, b : Type) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  (el : InterpDirichFunc p s) ->
  InterpDFMap p mas el =
  InterpDirichFromPDP p a b
    (InterpPDPdimap (DirichToPDP p) s t a b mas mtb
      (InterpDirichToPDP p s t el))
InterpDirichFromPDPdimap fext (pos ** dir) s t a b mas mtb (i ** dm) = Refl

public export
DirichNatTransToPDP :
  (p, q : MLDirichCatObj) -> MLDirichCatMor p q ->
  PDPnt (DirichToPDP p) (DirichToPDP q)
DirichNatTransToPDP (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  (onpos **
   \_ => id **
   \_, _ => id **
   \pi, _ => ondir pi **
   \_, _, _, ev => void ev)

public export
DirichNatTransToPDPeq :
  FunExt ->
  (p, q : MLDirichCatObj) -> (alpha : MLDirichCatMor p q) ->
  (a, b : Type) ->
  ExtEq
    (InterpPDPnt {p=(DirichToPDP p)} {q=(DirichToPDP q)}
      (DirichNatTransToPDP p q alpha) a b)
    (InterpDirichToPDP q a b
     . InterpDirichNT {p} {q} alpha a
     . InterpDirichFromPDP p a b)
DirichNatTransToPDPeq fext (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) a b
  (i ** dm) =
    dpEq12
      Refl
      (funExt $ \(() ** fa) =>
        (let eq : (fa = (\_ => fa ())) = funExt $ \() => Refl in
         rewrite eq in
         dpEq12
          Refl
          (funExt $ \ev => void ev)))

----------------------------------------------------------
---- Profunctor-iterated fixed points of `PolyDiProf` ----
----------------------------------------------------------

public export
PDPopmu : PolyDiProf -> Type
PDPopmu = ProfOpMu . InterpPDP

public export
PDPmu : PolyDiProf -> Type
PDPmu = ProfMu . InterpPDP

mutual
  public export
  partial
  pdpCata : (p : PolyDiProf) -> (a, b : Type) ->
    (InterpPDP p b a -> a) -> (b -> InterpPDP p a b) -> PDPmu p -> a
  pdpCata
    (polypos ** contrapos ** contradir ** covarpos ** covardir)
    a b alg coalg (InPrF (FS FZ) (InPTv vu)) =
      void vu
  pdpCata
    (polypos ** contrapos ** contradir ** covarpos ** covardir)
    a b alg coalg (InPrF (FS FZ) (InPTc (ipoly ** dm))) =
      alg
        (ipoly **
         \(icontra ** dmcontra) =>
          let
            idmcovar = dm (icontra ** (pdpCocata
              (polypos ** contrapos ** contradir ** covarpos ** covardir)
              a b alg coalg . dmcontra))
          in
          (fst idmcovar **
           pdpCata
            (polypos ** contrapos ** contradir ** covarpos ** covardir)
            a b alg coalg
           . snd idmcovar))

  public export
  partial
  pdpCocata : (p : PolyDiProf) -> (a, b : Type) ->
    (InterpPDP p b a -> a) -> (b -> InterpPDP p a b) -> b -> PDPopmu p
  pdpCocata
    (polypos ** contrapos ** contradir ** covarpos ** covardir)
    a b alg coalg eb =
      InPrF FZ $ InPTn () $ let (ipoly ** dm) = coalg eb in
        (ipoly **
         \(icontra ** dmcontra) =>
          let
            idmcovar = dm (icontra ** pdpCata
              (polypos ** contrapos ** contradir ** covarpos ** covardir)
              a b alg coalg . dmcontra)
          in
          (fst idmcovar **
           pdpCocata
            (polypos ** contrapos ** contradir ** covarpos ** covardir)
            a b alg coalg
           . snd idmcovar))

public export
partial
pdpDiCata : (p : PolyDiProf) -> ProfDiCata (InterpPDP p)
pdpDiCata p a b alg coalg = (pdpCata p a b alg coalg, pdpCocata p a b alg coalg)

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Dual-variance data structures as polynomial profunctors ----
-----------------------------------------------------------------
-----------------------------------------------------------------

public export
TypePolyDifunc : Type
TypePolyDifunc =
  (pos1 : Type **
   dir1 : SliceObj pos1 **
   pos2 : SliceObj pos1 **
   (i1 : pos1) -> dir1 i1 -> SliceObj (pos2 i1))

public export
tpdfPos1 : TypePolyDifunc -> Type
tpdfPos1 tpdf = DPair.fst tpdf

public export
tpdfDir1 : (tpdf : TypePolyDifunc) -> SliceObj (tpdfPos1 tpdf)
tpdfDir1 tpdf = DPair.fst $ DPair.snd tpdf

public export
tpdfPos2 : (tpdf : TypePolyDifunc) -> SliceObj (tpdfPos1 tpdf)
tpdfPos2 tpdf = DPair.fst $ DPair.snd $ DPair.snd tpdf

public export
tpdfDir2 : (tpdf : TypePolyDifunc) ->
  (i1 : tpdfPos1 tpdf) -> tpdfDir1 tpdf i1 -> SliceObj (tpdfPos2 tpdf i1)
tpdfDir2 tpdf = DPair.snd $ DPair.snd $ DPair.snd tpdf

public export
InterpTPDF : TypePolyDifunc -> ProfunctorSig
InterpTPDF tpdf x y =
  (i1 : tpdfPos1 tpdf **
   dm1 : x -> tpdfDir1 tpdf i1 **
   (i2 : tpdfPos2 tpdf i1) ->
    ((d1 : tpdfDir1 tpdf i1) ->
     tpdfDir2 tpdf i1 d1 i2 ->
     (ex : x ** dm1 ex = d1)) ->
    y)

public export
itpdfDimap : (tpdf : TypePolyDifunc) -> TypeDimapSig (InterpTPDF tpdf)
itpdfDimap tpdf s t a b mas mtb =
  dpMapSnd
    $ \i1 => dpBimap ((|>) mas)
    $ \dms, dmt, i2, dma => mtb
    $ dmt i2 $ \d1, d2 => (mas (fst $ dma d1 d2) ** snd $ dma d1 d2)

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Polynomial profunctors as PRA functors `[Type, MlDirichCatObj]` ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-------------------------------
---- Objects (profunctors) ----
-------------------------------

public export
MlPolyProf : Type
MlPolyProf =
  (pos : Type **
   contra : SliceObj pos **
   (i : pos) -> SliceObj (contra i))

public export
mlpPos : MlPolyProf -> Type
mlpPos = DPair.fst

public export
mlpContra : (mlp : MlPolyProf) -> SliceObj (mlpPos mlp)
mlpContra mlp = DPair.fst (DPair.snd mlp)

public export
mlpCovar : (mlp : MlPolyProf) -> (i : mlpPos mlp) -> SliceObj (mlpContra mlp i)
mlpCovar mlp = DPair.snd (DPair.snd mlp)

public export
mlpT1 : MlPolyProf -> MLDirichCatObj
mlpT1 mlp = (mlpPos mlp ** mlpContra mlp)

public export
mlpET : (mlp : MlPolyProf) -> mlpPos mlp -> MLPolyCatObj
mlpET mlp i = (mlpContra mlp i ** mlpCovar mlp i)

public export
InterpMLPradjFact :
  (mlp : MlPolyProf) -> Type -> MlDirichSlObj (mlpT1 mlp)
InterpMLPradjFact mlp z =
  MDSobj (\i => Unit) (\i, u_, dcont => mlpCovar mlp i dcont -> z)

public export
InterpMLPradjFactMap : (mlp : MlPolyProf) ->
  (z, z' : Type) -> (z -> z') ->
  MlDirichSlMor {ar=(mlpT1 mlp)}
    (InterpMLPradjFact mlp z)
    (InterpMLPradjFact mlp z')
InterpMLPradjFactMap mlp z z' mz =
  MDSM (\i1, u_ => ()) (\i1, u_, dcont => (.) mz)

public export
InterpMLPsigma : (mlp : MlPolyProf) ->
  MlDirichSlObj (mlpT1 mlp) -> MLDirichCatObj
InterpMLPsigma mlp = mlDirichSlObjTot {ar=(mlpT1 mlp)}

public export
InterpMLPsigmaMap : (mlp : MlPolyProf) ->
  (sl, sl' : MlDirichSlObj (mlpT1 mlp)) ->
  MlDirichSlMor {ar=(mlpT1 mlp)} sl sl' ->
  MLDirichCatMor (InterpMLPsigma mlp sl) (InterpMLPsigma mlp sl')
InterpMLPsigmaMap mlp sl sl' (MDSM onpos ondir) =
  (\(i ** eslp) => (i ** onpos i eslp) **
   \(i ** eslp), (dcont ** esld) => (dcont ** ondir i eslp dcont esld))

public export
InterpMLPcurried : (mlp : MlPolyProf) -> Type -> MLDirichCatObj
InterpMLPcurried mlp = InterpMLPsigma mlp . InterpMLPradjFact mlp

public export
InterpMLPcurriedMap : (mlp : MlPolyProf) -> (x, y : Type) ->
  (x -> y) ->
  MLDirichCatMor (InterpMLPcurried mlp x) (InterpMLPcurried mlp y)
InterpMLPcurriedMap mlp x y m =
  InterpMLPsigmaMap
    mlp
    (InterpMLPradjFact mlp x)
    (InterpMLPradjFact mlp y)
    (InterpMLPradjFactMap mlp x y m)

public export
InterpMLP : (mlp : MlPolyProf) -> (j, z : Type) -> Type
InterpMLP mlp = (|>) (InterpMLPcurried mlp) . flip InterpDirichFunc

public export
InterpMLPlmap : (mlp : MlPolyProf) -> (j, j', z : Type) ->
  (j' -> j) -> InterpMLP mlp j z -> InterpMLP mlp j' z
InterpMLPlmap mlp j j' z = InterpDFMap {a=j'} {b=j} (InterpMLPcurried mlp z)

public export
InterpMLPrmap : (mlp : MlPolyProf) -> (j, z, z' : Type) ->
  (z -> z') -> InterpMLP mlp j z -> InterpMLP mlp j z'
InterpMLPrmap mlp j z z' mz (i ** dmcov) =
  InterpDFMap
    ((DPair (mlpPos mlp) (const Unit)) **
     (\i' =>
      DPair
        (mlpContra mlp (fst i'))
        (\dcont => mlpCovar mlp (fst i') dcont -> z')))
    dmcov
    (i ** InterpPFMap {a=z} {b=z'} (mlpET mlp (fst i)) mz)

public export
InterpMLPdimap : (mlp : MlPolyProf) -> (j, z, j', z' : Type) ->
  (j' -> j) -> (z -> z') -> InterpMLP mlp j z -> InterpMLP mlp j' z'
InterpMLPdimap mlp j z j' z' mj mz =
  InterpMLPlmap mlp j j' z' mj . InterpMLPrmap mlp j z z' mz

public export
InterpMLPladjFact : (mlp : MlPolyProf) -> MlDirichSlObj (mlpT1 mlp) -> Type
InterpMLPladjFact mlp (MDSobj apos adir) =
  (pi : mlpPos mlp ** ai : apos pi **
   dcont : mlpContra mlp pi **
   (mlpCovar mlp pi dcont, adir pi ai dcont))

public export
InterpMLPladjFactMap : (mlp : MlPolyProf) ->
  (sl, sl' : MlDirichSlObj (mlpT1 mlp)) ->
  MlDirichSlMor {ar=(mlpT1 mlp)} sl sl' ->
  InterpMLPladjFact mlp sl -> InterpMLPladjFact mlp sl'
InterpMLPladjFactMap mlp
  (MDSobj slpos sldir) (MDSobj slpos' sldir') (MDSM monpos mondir)
  (pi ** ai ** dcont ** (dcov, ad)) =
    (pi ** monpos pi ai ** dcont ** (dcov, mondir pi ai dcont ad))

public export
InterpMLPladjunct : (mlp : MlPolyProf) ->
  (a : MlDirichSlObj (mlpT1 mlp)) -> (b : Type) ->
  (InterpMLPladjFact mlp a -> b) ->
  MlDirichSlMor {ar=(mlpT1 mlp)} a (InterpMLPradjFact mlp b)
InterpMLPladjunct mlp (MDSobj apos adir) b m =
  MDSM
    (\pi, ai => ())
    (\pi, ai, dcont, ad, dcov => m (pi ** ai ** dcont ** (dcov, ad)))

public export
InterpMLPradjunct : (mlp : MlPolyProf) ->
  (a : MlDirichSlObj (mlpT1 mlp)) -> (b : Type) ->
  MlDirichSlMor {ar=(mlpT1 mlp)} a (InterpMLPradjFact mlp b) ->
  (InterpMLPladjFact mlp a -> b)
InterpMLPradjunct mlp (MDSobj apos adir) b
  (MDSM monpos_ mondir) (pi ** ai ** dcont ** (dcov, ad)) =
    mondir pi ai dcont ad dcov

public export
InterpMLPlradjunctId : (mlp : MlPolyProf) ->
  (a : MlDirichSlObj (mlpT1 mlp)) -> (b : Type) ->
  (m : InterpMLPladjFact mlp a -> b) ->
  ExtEq m (InterpMLPradjunct mlp a b $ InterpMLPladjunct mlp a b m)
InterpMLPlradjunctId mlp
  (MDSobj apos adir) b m (pi ** ai ** dcont ** (dcov, ad)) =
    Refl

public export
InterpMLPrladjunctId : FunExt -> (mlp : MlPolyProf) ->
  (a : MlDirichSlObj (mlpT1 mlp)) -> (b : Type) ->
  (m : MlDirichSlMor {ar=(mlpT1 mlp)} a (InterpMLPradjFact mlp b)) ->
  m = (InterpMLPladjunct mlp a b $ InterpMLPradjunct mlp a b m)
InterpMLPrladjunctId fext mlp (MDSobj apos adir) b (MDSM monpos mondir) =
  let
    onposeq : (monpos = (\pi, ai => ())) =
      funExt (\pi => funExt $ \ai => unitUnique (monpos pi ai) ())
  in
  rewrite onposeq in
  Refl

-- An explicit formulation of `InterpMLP` which presents it as a
-- coproduct of representable presheaves on the category of polynomial
-- functors.
public export
InterpMLPasNT : (mlp : MlPolyProf) -> (j, z : Type) -> Type
InterpMLPasNT mlp j z =
  (i : mlpPos mlp ** MLPolyCatMor (pfMonomialArena j z) (mlpET mlp i))

public export
InterpMLPfromNT : (mlp : MlPolyProf) -> (j, z : Type) ->
  InterpMLPasNT mlp j z -> InterpMLP mlp j z
InterpMLPfromNT mlp j z (i ** onpos ** ondir) =
  ((i ** ()) ** \ej => (onpos ej ** ondir ej))

public export
InterpMLPtoNT : (mlp : MlPolyProf) -> (j, z : Type) ->
  InterpMLP mlp j z -> InterpMLPasNT mlp j z
InterpMLPtoNT mlp j z ((i ** ()) ** dm) = (i ** fst . dm ** \ej => snd (dm ej))

public export
InterpMLPasNTlmap : (mlp : MlPolyProf) -> (j, j', z : Type) ->
  (j' -> j) -> InterpMLPasNT mlp j z -> InterpMLPasNT mlp j' z
InterpMLPasNTlmap mlp j j' z mj =
  dpMapSnd $
    \i => dpBimap ((|>) mj) (\dmcont, dmcov, ej', dcov => dmcov (mj ej') dcov)

public export
InterpMLPasNTrmap : (mlp : MlPolyProf) -> (j, z, z' : Type) ->
  (z -> z') -> InterpMLPasNT mlp j z -> InterpMLPasNT mlp j z'
InterpMLPasNTrmap mlp j z z' mz =
  dpMapSnd $
    \i => dpMapSnd $ \dmcont, dmcov, ej => mz . dmcov ej

public export
InterpMLPasNTdimap : (mlp : MlPolyProf) -> (j, z, j', z' : Type) ->
  (j' -> j) -> (z -> z') -> InterpMLPasNT mlp j z -> InterpMLPasNT mlp j' z'
InterpMLPasNTdimap mlp j z j' z' mj mz =
  InterpMLPasNTlmap mlp j j' z' mj . InterpMLPasNTrmap mlp j z z' mz

-- An explicit formulation of `InterpMLP` which presents it as a
-- coproduct of morphisms into the images of polynomial functors --
-- which are also covariant-representable profunctors represented
-- by polynomial functors.
public export
InterpMLPcovarRep : (mlp : MlPolyProf) -> (j, z : Type) -> Type
InterpMLPcovarRep mlp j z =
  (i : mlpPos mlp ** j -> InterpPolyFunc (mlpET mlp i) z)

public export
InterpMLPfromCovarRep : (mlp : MlPolyProf) -> (j, z : Type) ->
  InterpMLPcovarRep mlp j z -> InterpMLP mlp j z
InterpMLPfromCovarRep mlp j z (i ** dm) = ((i ** ()) ** dm)

public export
InterpMLPtoCovarRep : (mlp : MlPolyProf) -> (j, z : Type) ->
  InterpMLP mlp j z -> InterpMLPcovarRep mlp j z
InterpMLPtoCovarRep mlp j z ((i ** ()) ** dm) = (i ** dm)

---------------------------------------------
---- Morphisms (natural transformations) ----
---------------------------------------------

public export
MlPolyProfNT : IntMorSig MlPolyProf
MlPolyProfNT p q =
  (onpos : mlpPos p -> mlpPos q **
   oncontra : (i : mlpPos p) -> mlpContra p i -> mlpContra q (onpos i) **
   (i : mlpPos p) -> (dcont : mlpContra p i) ->
    mlpCovar q (onpos i) (oncontra i dcont) ->
    mlpCovar p i dcont)

public export
mlpNTonPos : {0 p, q : MlPolyProf} ->
  MlPolyProfNT p q -> mlpPos p -> mlpPos q
mlpNTonPos {p} {q} = DPair.fst

public export
mlpNTonContra : {0 p, q : MlPolyProf} ->
  (mlp : MlPolyProfNT p q) -> (i : mlpPos p) ->
  mlpContra p i -> mlpContra q (mlpNTonPos {p} {q} mlp i)
mlpNTonContra {p} {q} mlp = DPair.fst (DPair.snd mlp)

public export
mlpNTonCovar : {0 p, q : MlPolyProf} ->
  (mlp : MlPolyProfNT p q) -> (i : mlpPos p) -> (dcont : mlpContra p i) ->
  mlpCovar q (mlpNTonPos {p} {q} mlp i) (mlpNTonContra {p} {q} mlp i dcont) ->
  mlpCovar p i dcont
mlpNTonCovar {p} {q} mlp = DPair.snd (DPair.snd mlp)

public export
InterpMLPnt : {p, q : MlPolyProf} ->
  MlPolyProfNT p q -> TypeProfNT (InterpMLPasNT p) (InterpMLPasNT q)
InterpMLPnt {p} {q} (onpos ** oncontra ** oncovar) j z (i ** dmcont ** dmcov) =
  (onpos i **
   oncontra i . dmcont **
   sliceComp {a=j} dmcov (\ej => oncovar i $ dmcont ej))

-------------------------------------------------
---- Morphisms (paranatural transformations) ----
-------------------------------------------------

---------------------------------------------
---------------------------------------------
---- Twisted-arrow category PRA functors ----
---------------------------------------------
---------------------------------------------

public export
TwArrPolyF : Type
TwArrPolyF =
  (pos : Type **
   d1 : SliceObj pos **
   d2 : SliceObj pos **
   (i : pos) -> d2 i -> d1 i)

public export
TwArrPolyFRAdjFact :
  (twp : TwArrPolyF) -> (x, y : Type) -> (y -> x) -> SliceObj (fst twp)
TwArrPolyFRAdjFact twp x y m i =
  (dms : (x -> fst (snd twp) i, fst (snd (snd twp)) i -> y) **
   ExtEq {a=(fst (snd (snd twp)) i)} {b=(fst (snd twp) i)}
    (snd (snd (snd twp)) i)
    (fst dms . m . snd dms))

public export
TwArrPolyFRAdjFactMap :
  (twp : TwArrPolyF) ->
  (s, t, a, b : Type) ->
  (mts : t -> s) -> (mba : b -> a) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  ExtEq {a=t} {b=s} (mas . mba . mtb) mts ->
  SliceMorphism {a=(fst twp)}
    (TwArrPolyFRAdjFact twp s t mts)
    (TwArrPolyFRAdjFact twp a b mba)
TwArrPolyFRAdjFactMap twp s t a b mts mba mas mtb comm i el =
  let elcomm = snd el in
  ((fst (fst el) . mas, mtb . snd (fst el)) **
   \edcov => rewrite comm (snd (fst el) edcov) in elcomm edcov)

public export
InterpTwArrPoly : (twp : TwArrPolyF) -> (x, y : Type) -> (y -> x) -> Type
InterpTwArrPoly twp x y m = Sigma {a=(fst twp)} (TwArrPolyFRAdjFact twp x y m)

--------------------------------------
--------------------------------------
---- Polynomial slice profunctors ----
--------------------------------------
--------------------------------------

public export
SPProf : Type -> Type -> Type
SPProf x y =
  (pos : Type **
   dir1 : pos -> SliceObj x **
   (elp : pos) -> (elx : x) -> dir1 elp elx -> SliceObj y)

public export
sppPos : {0 x, y : Type} -> SPProf x y ->
  Type
sppPos {x} {y} = DPair.fst

public export
sppDir1 : {0 x, y : Type} -> (spp : SPProf x y) ->
  sppPos spp -> SliceObj x
sppDir1 {x} {y} spp = DPair.fst (DPair.snd spp)

public export
sppDir2 : {0 x, y : Type} -> (spp : SPProf x y) ->
  (elp : sppPos spp) -> (elx : x) -> (eld1 : sppDir1 {x} {y} spp elp elx) ->
  SliceObj y
sppDir2 {x} {y} spp = DPair.snd (DPair.snd spp)

public export
InterpSPP : {x, y : Type} -> (spp : SPProf x y) ->
  SliceObj x -> SliceObj y -> Type
InterpSPP {x} {y} spp slx sly =
  (elp : sppPos spp **
   dm1 : SliceMorphism {a=x} slx (sppDir1 {x} {y} spp elp) **
   (elx : x) -> (eslx : slx elx) ->
    SliceMorphism {a=y} (sppDir2 {x} {y} spp elp elx (dm1 elx eslx)) sly)

public export
InterpSPPdimap : {x, y : Type} -> (spp : SPProf x y) ->
  (slx, slx' : SliceObj x) -> (sly, sly' : SliceObj y) ->
  (mx : SliceMorphism {a=x} slx' slx) -> (my : SliceMorphism {a=y} sly sly') ->
  InterpSPP {x} {y} spp slx sly -> InterpSPP {x} {y} spp slx' sly'
InterpSPPdimap {x} {y} spp slx slx' sly sly' mx my (elp ** dm1 ** dm2) =
  (elp **
   \elx, eslx' => dm1 elx (mx elx eslx') **
   \elx, eslx', ely, d2 => my ely $ dm2 elx (mx elx eslx') ely d2)

-------------------------------------
-------------------------------------
---- Simple difunctors on `Type` ----
-------------------------------------
-------------------------------------

------------------------------------------------------------------
---- Aliases for polynomial difunctors specifically on `Type` ----
------------------------------------------------------------------

public export
0 TypeProDimap : ProfunctorSig -> Type
TypeProDimap = IntEndoDimapSig Type TypeMor

public export
0 TypeProLmap : ProfunctorSig -> Type
TypeProLmap = IntEndoLmapSig Type TypeMor

public export
0 TypeProRmap : ProfunctorSig -> Type
TypeProRmap = IntEndoRmapSig Type TypeMor

public export
TypeProAr : Type
TypeProAr = IntEndoProAr Type

public export
InterpTypeProAr : TypeProAr -> Type -> Type -> Type
InterpTypeProAr = InterpIEPPobj Type TypeMor

public export
0 TypeProDimapSig : TypeProAr -> Type
TypeProDimapSig = TypeProDimap . InterpTypeProAr

public export
0 TypeProLmapSig : TypeProAr -> Type
TypeProLmapSig = TypeProLmap . InterpTypeProAr

public export
0 TypeProRmapSig : TypeProAr -> Type
TypeProRmapSig = TypeProRmap . InterpTypeProAr

public export
TypeProArDimap : (ar : TypeProAr) -> TypeProDimapSig ar
TypeProArDimap = InterpIEPPdimap Type TypeMor typeComp

public export
0 TypeProArLmap : (ar : TypeProAr) -> TypeProLmapSig ar
TypeProArLmap ar = TypeLmapFromDimap (InterpTypeProAr ar) (TypeProArDimap ar)

public export
0 TypeProArRmap : (ar : TypeProAr) -> TypeProRmapSig ar
TypeProArRmap ar = TypeRmapFromDimap (InterpTypeProAr ar) (TypeProArDimap ar)

public export
0 TypeProNTSig : IntMorSig TypeProAr
TypeProNTSig p q = TypeProfNT (InterpTypeProAr p) (InterpTypeProAr q)

public export
0 TypeDiNTSig : IntMorSig TypeProAr
TypeDiNTSig p q = TypeProfDiNT (InterpTypeProAr p) (InterpTypeProAr q)

public export
TypeProNTar : IntMorSig TypeProAr
TypeProNTar = IntEPPNTar Type TypeMor

public export
TypeProNTid : IntIdSig TypeProAr TypeProNTar
TypeProNTid = intPPNTid Type Type TypeMor TypeMor typeId typeId

public export
TypeProNTvcomp : IntCompSig TypeProAr TypeProNTar
TypeProNTvcomp = intPPNTvcomp Type Type TypeMor TypeMor typeComp typeComp

public export
InterpTypeProNT : (p, q : TypeProAr) -> TypeProNTar p q -> TypeProNTSig p q
InterpTypeProNT = InterpIEPPnt Type TypeMor typeComp

public export
TypeDiNTar : IntMorSig TypeProAr
TypeDiNTar = IntPDiNTar Type TypeMor

public export
TypeDiNTid : IntIdSig TypeProAr TypeDiNTar
TypeDiNTid = intPDiNTid Type TypeMor typeId

public export
TypeDiNTvcomp : IntCompSig TypeProAr TypeDiNTar
TypeDiNTvcomp = intPDiNTvcomp Type TypeMor typeComp

public export
InterpTypeDiNT : (p, q : TypeProAr) -> TypeDiNTar p q -> TypeDiNTSig p q
InterpTypeDiNT = InterpIEPPdint Type TypeMor typeComp

public export
0 TypeProArNaturality : (p, q : TypeProAr) -> TypeProNTSig p q -> Type
TypeProArNaturality p q =
  TypeNTNaturality (InterpTypeProAr p) (InterpTypeProAr q)
    (TypeProArDimap p) (TypeProArDimap q)

public export
0 TypeProArParanaturality : (p, q : TypeProAr) -> TypeDiNTSig p q -> Type
TypeProArParanaturality p q =
  TypeNTParanaturality (InterpTypeProAr p) (InterpTypeProAr q)
    (TypeProArDimap p) (TypeProArDimap q)

public export
TypeParaDomFunc : TypeProAr -> TypeProAr
TypeParaDomFunc = IntParaDomFunc {c=Type} {mor=TypeMor}

public export
TypeParaAsNT : {p, q : TypeProAr} ->
  TypeDiNTar p q -> TypeProNTar (TypeParaDomFunc p) q
TypeParaAsNT = IntParaAsNT {c=Type} {mor=TypeMor}

public export
TypeParaFromNT : {p, q : TypeProAr} ->
  TypeProNTar (TypeParaDomFunc p) q -> TypeDiNTar p q
TypeParaFromNT = IntParaFromNT {c=Type} {mor=TypeMor}

-------------------------------------
---- Utility types and functions ----
-------------------------------------

public export
TypeProNTpos : (p, q : TypeProAr) -> Type
TypeProNTpos = IntPPNTpos {d=Type} {c=Type} {dmor=TypeMor} {cmor=TypeMor}

public export
TypeProNTcontra : (p, q : TypeProAr) -> TypeProNTpos p q -> Type
TypeProNTcontra = IntPPNTcontra {d=Type} {c=Type} {dmor=TypeMor} {cmor=TypeMor}

public export
TypeProNTcovar : (p, q : TypeProAr) -> TypeProNTpos p q -> Type
TypeProNTcovar = IntPPNTcovar {d=Type} {c=Type} {dmor=TypeMor} {cmor=TypeMor}

public export
typeProNTpos : {p, q : TypeProAr} -> TypeProNTar p q -> TypeProNTpos p q
typeProNTpos = intPPNTpos {c=Type} {cmor=TypeMor} {d=Type} {dmor=TypeMor}

public export
typeProNTcontra : {p, q : TypeProAr} -> (ar : TypeProNTar p q) ->
  TypeProNTcontra p q (typeProNTpos {p} {q} ar)
typeProNTcontra = intPPNTcontra {c=Type} {cmor=TypeMor} {d=Type} {dmor=TypeMor}

public export
typeProNTcovar : {p, q : TypeProAr} -> (ar : TypeProNTar p q) ->
  TypeProNTcovar p q (typeProNTpos {p} {q} ar)
typeProNTcovar = intPPNTcovar {c=Type} {cmor=TypeMor} {d=Type} {dmor=TypeMor}

public export
TypeDiNTpos : (p, q : TypeProAr) -> Type
TypeDiNTpos = IntPDiNTpos {c=Type} {mor=TypeMor}

public export
TypeDiNTcontra : (p, q : TypeProAr) -> TypeDiNTpos p q -> Type
TypeDiNTcontra = IntPDiNTcontra {c=Type} {mor=TypeMor}

public export
TypeDiNTcovar : (p, q : TypeProAr) -> TypeDiNTpos p q -> Type
TypeDiNTcovar = IntPDiNTcovar {c=Type} {mor=TypeMor}

public export
TypeProNTrestrict : (p, q : TypeProAr) -> TypeProNTar p q -> TypeDiNTar p q
TypeProNTrestrict p q = intPPNTrestrict {c=Type} {cmor=TypeMor} {p} {q}

public export
typeDiNTpos : {p, q : TypeProAr} -> TypeDiNTar p q -> TypeDiNTpos p q
typeDiNTpos = intPDiNTpos {c=Type} {mor=TypeMor}

public export
typeDiNTcontra : {p, q : TypeProAr} -> (ar : TypeDiNTar p q) ->
  TypeDiNTcontra p q (typeDiNTpos {p} {q} ar)
typeDiNTcontra = intPDiNTcontra {c=Type} {mor=TypeMor}

public export
typeDiNTcovar : {p, q : TypeProAr} -> (ar : TypeDiNTar p q) ->
  TypeDiNTcovar p q (typeDiNTpos {p} {q} ar)
typeDiNTcovar = intPDiNTcovar {c=Type} {mor=TypeMor}

public export
TypeProCatElemObj : TypeProAr -> Type
TypeProCatElemObj = PProfCatElemObj Type Type TypeMor TypeMor

public export
TypeProCatElemMor : {ar : TypeProAr} -> IntMorSig (TypeProCatElemObj ar)
TypeProCatElemMor {ar} =
  PProfCatElemMor Type Type TypeMor TypeMor typeComp typeComp ar

public export
TypeProCatDiagElemObj : TypeProAr -> Type
TypeProCatDiagElemObj = PProfCatDiagElemObj Type TypeMor

public export
TypeProCatDiagElemMor : {ar : TypeProAr} -> IntMorSig (TypeProCatDiagElemObj ar)
TypeProCatDiagElemMor {ar} =
  PProfCatDiagElemMor Type TypeMor typeComp ar

-------------------------------------------------
---- Completeness of natural transformations ----
-------------------------------------------------

public export
TypeProArFromNT : (p, q : TypeProAr) -> TypeProNTSig p q -> TypeProNTar p q
TypeProArFromNT (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) alpha =
  let nti = \pi : ppos => alpha (pcontra pi) (pcovar pi) (pi ** (id, id)) in
  (\pi => fst (nti pi) **
   (\pi => fst (snd $ nti pi),
    \pi => snd (snd $ nti pi)))

public export
0 TypeProArComplete : (p, q : TypeProAr) -> (alpha : TypeProNTSig p q) ->
  (cond : TypeProArNaturality p q alpha) ->
  (x, y : Type) ->
  ExtEq {a=(InterpTypeProAr p x y)} {b=(InterpTypeProAr q x y)}
    (alpha x y)
    (InterpTypeProNT p q (TypeProArFromNT p q alpha) x y)
TypeProArComplete (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) alpha
  cond x y (pi ** (dmx, dmy)) =
    sym $ cond (pcontra pi) (pcovar pi) x y dmx dmy (pi ** (id, id))

-----------------------------------------------------
---- Completeness of paranatural transformations ----
-----------------------------------------------------

public export
TypeDiArIsPara : (p, q : TypeProAr) -> (ar : TypeDiNTar p q) ->
  TypeProArParanaturality p q (InterpTypeDiNT p q ar)
TypeDiArIsPara p q ar =
  IntPDiNTPara Type TypeMor typeId typeComp typeIdL typeIdR typeAssoc p q ar

public export
TypeDiArFromDi: (p, q : TypeProAr) ->
  (gamma : TypeDiNTSig p q) -> TypeProArParanaturality p q gamma ->
  TypeDiNTar p q
TypeDiArFromDi (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma
  cond =
    (\pi, asn =>
      fst $ gamma (pcovar pi) (pi ** (asn, id)) **
     (\pi, asn, pcont =>
        rewrite
          sym (dpeq1 $
            cond (pcovar pi) (pcontra pi) asn
              (pi ** (asn, id))
              (pi ** (id, asn))
              Refl)
        in
        fst (snd $ gamma (pcontra pi) (pi ** (id, asn))) pcont,
      \pi, asn =>
        snd $ snd $ gamma (pcovar pi) (pi ** (asn, id))))

public export
0 TypeDiArCompleteFst :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  (i : InterpTypeProAr p x x) ->
    fst (gamma x i) =
    (fst $ InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x i)
TypeDiArCompleteFst (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  gamma cond x (pi ** (dmx, dmy)) =
    rewrite dpeq1 $
      cond (pcovar pi) x dmy (pi ** (dmx . dmy, id)) (pi ** (dmx, dmy)) Refl in
    Refl

public export
0 TypeDiArCompleteFstSnd :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  (i : InterpTypeProAr p x x) ->
    fst (snd $ gamma x i) =
    (rewrite TypeDiArCompleteFst p q gamma cond x i in
     fst (snd $ InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x i))
TypeDiArCompleteFstSnd
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  gamma cond x (pi ** (dmx, dmy)) =
    let
      condapp =
        cond x (pcontra pi) dmx (pi ** (dmx, dmy)) (pi ** (id, dmx . dmy)) Refl
    in
    rewrite sym $ dpeq1 condapp in
    sym $ fstEqHet $ dpeq2 condapp

public export
0 TypeDiArCompleteSndSnd :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  (i : InterpTypeProAr p x x) ->
    snd (snd $ gamma x i) =
    (rewrite TypeDiArCompleteFst p q gamma cond x i in
     snd (snd $ InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x i))
TypeDiArCompleteSndSnd
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  gamma cond x (pi ** (dmx, dmy)) =
    sndEqHet $ dpeq2 $
      cond (pcovar pi) x dmy (pi ** (dmx . dmy, id)) (pi ** (dmx, dmy)) Refl

public export
0 TypeDiArComplete :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  ExtEq {a=(InterpTypeProAr p x x)} {b=(InterpTypeProAr q x x)}
    (gamma x)
    (InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x)
TypeDiArComplete
  p@(ppos ** (pcontra, pcovar)) q@(qpos ** (qcontra, qcovar))
  gamma cond x i@(pi ** (dmx, dmy)) =
    rewrite sym $ TypeDiArCompleteFst p q gamma cond x i in
    rewrite sym $ TypeDiArCompleteFstSnd p q gamma cond x i in
    rewrite dpEqPat {dp=(gamma x (pi ** (dmx, dmy)))} in
    dpEq12
      Refl
    $ rewrite pairFstSnd (snd $ gamma x (pi ** (dmx, dmy))) in
      pairEqCong Refl (TypeDiArCompleteSndSnd p q gamma cond x i)

----------------------------------------------------------------
---- Paranatural transformations as natural transformations ----
----------------------------------------------------------------

public export
TypeDiArAsPreshfNatTrans :
  {p, q : TypeProAr} -> (gamma : TypeDiNTar p q) ->
  TwArrPreshfEmbeddingNT (InterpTypeProAr p) (InterpTypeProAr q)
TypeDiArAsPreshfNatTrans {p} {q} gamma x y myx (i ** (dcont, dcov)) =
  let asn = dcont . myx . dcov in
  (typeDiNTpos gamma i asn **
   (typeDiNTcontra gamma i asn . dcont,
    dcov . typeDiNTcovar gamma i asn))

public export
0 TypeDiArAsPreshfNatTransIsNatural :
  (p, q : TypeProAr) -> (gamma : TypeDiNTar p q) ->
  TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ InterpTypeProAr p)}
    {q=(TwArrPreshfEmbedProf $ InterpTypeProAr q)}
    (TwArrPreshfEmbedProfMap (InterpTypeProAr p) $
      MkProfunctor $ \mca, mbd => TypeProArDimap p _ _ _ _ mca mbd)
    (TwArrPreshfEmbedProfMap (InterpTypeProAr q) $
      MkProfunctor $ \mca, mbd => TypeProArDimap q _ _ _ _ mca mbd)
    (TypeDiArAsPreshfNatTrans {p} {q} gamma)
TypeDiArAsPreshfNatTransIsNatural
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (oncontra, oncovar)) s t a b mba mas mtb (i ** (dcont, dcovar)) =
    Refl

public export
TypeDiArFromPreshfNatTrans : (p, q : TypeProAr) ->
  (gamma : TwArrPreshfEmbeddingNT (InterpTypeProAr p) (InterpTypeProAr q)) ->
  TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ InterpTypeProAr p)}
    {q=(TwArrPreshfEmbedProf $ InterpTypeProAr q)}
    (TwArrPreshfEmbedProfMap (InterpTypeProAr p) $
      MkProfunctor $ \mca, mbd => TypeProArDimap p _ _ _ _ mca mbd)
    (TwArrPreshfEmbedProfMap (InterpTypeProAr q) $
      MkProfunctor $ \mca, mbd => TypeProArDimap q _ _ _ _ mca mbd)
    gamma ->
  TypeDiNTar p q
TypeDiArFromPreshfNatTrans
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma isnat =
    (\pi, asn =>
      fst $ gamma (pcovar pi) (pcontra pi) asn (pi ** (id, id)) **
     (\pi, asn, pdcont =>
        fst (snd $ gamma (pcovar pi) (pcontra pi) asn (pi ** (id, id))) pdcont,
      \pi, asn, qdcov =>
        snd (snd $ gamma (pcovar pi) (pcontra pi) asn (pi ** (id, id))) qdcov))

public export
TypeDiArFromPreshfNatTransComplete : (p, q : TypeProAr) ->
  (gamma : TwArrPreshfEmbeddingNT (InterpTypeProAr p) (InterpTypeProAr q)) ->
  (isnat : TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ InterpTypeProAr p)}
    {q=(TwArrPreshfEmbedProf $ InterpTypeProAr q)}
    (TwArrPreshfEmbedProfMap (InterpTypeProAr p) $
      MkProfunctor $ \mca, mbd => TypeProArDimap p _ _ _ _ mca mbd)
    (TwArrPreshfEmbedProfMap (InterpTypeProAr q) $
      MkProfunctor $ \mca, mbd => TypeProArDimap q _ _ _ _ mca mbd)
    gamma) ->
  (x : Type) ->
  ExtEq {a=(InterpTypeProAr p x x)} {b=(InterpTypeProAr q x x)}
    (TwArrPreshfEmbeddingNTtoProfParaNT
      {p=(InterpTypeProAr p)} {q=(InterpTypeProAr q)} gamma x)
    (InterpTypeDiNT p q (TypeDiArFromPreshfNatTrans p q gamma isnat) x)
TypeDiArFromPreshfNatTransComplete
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma isnat x
  (pi ** (dcont, dcovar)) =
    sym $ isnat (pcovar pi) (pcontra pi) x x id dcovar dcont (pi ** (id, id))

public export
TypeDiArAsPreshfOpNatTrans :
  {p, q : TypeProAr} -> (gamma : TypeDiNTar p q) ->
  TwArrPreshfOpEmbeddingNT (InterpTypeProAr p) (InterpTypeProAr q)
TypeDiArAsPreshfOpNatTrans {p} {q} gamma x y myx (i ** (dcont, dcov)) =
  let asn = dcont . myx . dcov in
  (typeDiNTpos gamma i asn **
   (typeDiNTcontra gamma i asn . dcont,
    dcov . typeDiNTcovar gamma i asn))

public export
0 TypeDiArAsPreshfOpNatTransIsNatural :
  (p, q : TypeProAr) -> (gamma : TypeDiNTar p q) ->
  TwArrPreshfOpNaturality
    {p=(TwArrPreshfOpEmbedProf $ InterpTypeProAr p)}
    {q=(TwArrPreshfOpEmbedProf $ InterpTypeProAr q)}
    (TwArrPreshfOpEmbedProfMap (InterpTypeProAr p) $
      MkProfunctor $ \mca, mbd => TypeProArDimap p _ _ _ _ mca mbd)
    (TwArrPreshfOpEmbedProfMap (InterpTypeProAr q) $
      MkProfunctor $ \mca, mbd => TypeProArDimap q _ _ _ _ mca mbd)
    (TypeDiArAsPreshfOpNatTrans {p} {q} gamma)
TypeDiArAsPreshfOpNatTransIsNatural
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (oncontra, oncovar)) s t a b mba mas mtb (i ** (dcont, dcovar)) =
    Refl

public export
TypeDiArFromPreshfOpNatTrans : (p, q : TypeProAr) ->
  (gamma : TwArrPreshfOpEmbeddingNT (InterpTypeProAr p) (InterpTypeProAr q)) ->
  TwArrPreshfOpNaturality
    {p=(TwArrPreshfOpEmbedProf $ InterpTypeProAr p)}
    {q=(TwArrPreshfOpEmbedProf $ InterpTypeProAr q)}
    (TwArrPreshfOpEmbedProfMap (InterpTypeProAr p) $
      MkProfunctor $ \mca, mbd => TypeProArDimap p _ _ _ _ mca mbd)
    (TwArrPreshfOpEmbedProfMap (InterpTypeProAr q) $
      MkProfunctor $ \mca, mbd => TypeProArDimap q _ _ _ _ mca mbd)
    gamma ->
  TypeDiNTar p q
TypeDiArFromPreshfOpNatTrans
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma isnat =
    (\pi, asn =>
      fst $ gamma (pcontra pi) (pcovar pi) asn (pi ** (id, id)) **
     (\pi, asn, pdcont =>
        fst (snd $ gamma (pcontra pi) (pcovar pi) asn (pi ** (id, id))) pdcont,
      \pi, asn, qdcov =>
        snd (snd $ gamma (pcontra pi) (pcovar pi) asn (pi ** (id, id))) qdcov))

public export
TypeDiArFromPreshfOpNatTransComplete : (p, q : TypeProAr) ->
  (gamma : TwArrPreshfOpEmbeddingNT (InterpTypeProAr p) (InterpTypeProAr q)) ->
  (isnat : TwArrPreshfOpNaturality
    {p=(TwArrPreshfOpEmbedProf $ InterpTypeProAr p)}
    {q=(TwArrPreshfOpEmbedProf $ InterpTypeProAr q)}
    (TwArrPreshfOpEmbedProfMap (InterpTypeProAr p) $
      MkProfunctor $ \mca, mbd => TypeProArDimap p _ _ _ _ mca mbd)
    (TwArrPreshfOpEmbedProfMap (InterpTypeProAr q) $
      MkProfunctor $ \mca, mbd => TypeProArDimap q _ _ _ _ mca mbd)
    gamma) ->
  (x : Type) ->
  ExtEq {a=(InterpTypeProAr p x x)} {b=(InterpTypeProAr q x x)}
    (TwArrPreshfOpEmbeddingNTtoProfParaNT
      {p=(InterpTypeProAr p)} {q=(InterpTypeProAr q)} gamma x)
    (InterpTypeDiNT p q (TypeDiArFromPreshfOpNatTrans p q gamma isnat) x)
TypeDiArFromPreshfOpNatTransComplete
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma isnat x
  (pi ** (dcont, dcovar)) =
    sym $ isnat (pcontra pi) (pcovar pi) x x id dcont dcovar (pi ** (id, id))

---------------------------------------------------------
---- Categorical laws of paranatural transformations ----
---------------------------------------------------------

public export
TypeDiNTcompIdL : {p, q : TypeProAr} ->
  (gamma : TypeDiNTar p q) ->
  TypeDiNTvcomp p q q (TypeDiNTid q) gamma = gamma
TypeDiNTcompIdL
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncontra, oncovar)) =
    Refl

public export
TypeDiNTcompIdR : {p, q : TypeProAr} ->
  (gamma : TypeDiNTar p q) ->
  TypeDiNTvcomp p p q gamma (TypeDiNTid p) = gamma
TypeDiNTcompIdR
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncontra, oncovar)) =
    Refl

public export
TypeDiNTcompAssoc : {p, q, r, s : TypeProAr} ->
  (gamma : TypeDiNTar r s) ->
  (beta : TypeDiNTar q r) ->
  (alpha : TypeDiNTar p q) ->
  TypeDiNTvcomp p r s gamma (TypeDiNTvcomp p q r beta alpha) =
  TypeDiNTvcomp p q s (TypeDiNTvcomp q r s gamma beta) alpha
TypeDiNTcompAssoc
  {p=(ppos ** (pcontra, pcovar))}
  {q=(qpos ** (qcontra, qcovar))}
  {r=(rpos ** (rcontra, rcovar))}
  (gonpos ** (goncontra, goncovar))
  (bonpos ** (boncontra, boncovar))
  (aonpos ** (aoncontra, aoncovar)) =
    Refl

------------------------------------
---- Laws of composition monoid ----
------------------------------------

public export
TypeProArId : TypeProAr
TypeProArId = IntProArId Type

public export
TypeProArComp : TypeProAr -> TypeProAr -> TypeProAr
TypeProArComp = IntEndoProArComp Type TypeMor

public export
TypeProCompToIdL : (p : TypeProAr) ->
  TypeProNTar p (TypeProArComp TypeProArId p)
TypeProCompToIdL (ppos ** (pcontra, pcovar)) =
  (\pi => (pi ** pcontra pi ** id) **
   (\_ => id,
    \_ => id))

public export
TypeProCompFromIdL : (p : TypeProAr) ->
  TypeProNTar (TypeProArComp TypeProArId p) p
TypeProCompFromIdL (ppos ** (pcontra, pcovar)) =
  (fst **
   (\(pi ** qi ** mqp) => mqp,
    \(pi ** qi ** mqp) => id))

public export
TypeProCompToIdR : (p : TypeProAr) ->
  TypeProNTar p (TypeProArComp p TypeProArId)
TypeProCompToIdR (ppos ** (pcontra, pcovar)) =
  (\pi => (pcovar pi ** pi ** id) **
   (\pi => id,
    \pi => id))

public export
TypeProCompFromIdR : (p : TypeProAr) ->
  TypeProNTar (TypeProArComp p TypeProArId) p
TypeProCompFromIdR (ppos ** (pcontra, pcovar)) =
  (\(x ** pi ** dmcov) => pi **
   (\(x ** pi ** dmcov) => id,
    \(x ** pi ** dmcov) => dmcov))

public export
TypeProCompAssocL : (p, q, r : TypeProAr) ->
  TypeProNTar
    (TypeProArComp r (TypeProArComp q p))
    (TypeProArComp (TypeProArComp r q) p)
TypeProCompAssocL
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\((ri ** qi ** mqr) ** pi ** mpq) =>
      (ri ** (qi ** pi ** mpq) ** mqr) **
     (\((ri ** qi ** mqr) ** pi ** mpq) => id,
      \((ri ** qi ** mqr) ** pi ** mpq) => id))

public export
TypeProCompAssocR : (p, q, r : TypeProAr) ->
  TypeProNTar
    (TypeProArComp (TypeProArComp r q) p)
    (TypeProArComp r (TypeProArComp q p))
TypeProCompAssocR
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\(ri ** (qi ** pi ** mpq) ** mqr) => ((ri ** qi ** mqr) ** (pi ** mpq)) **
     (\(ri ** (qi ** pi ** mpq) ** mqr) => id,
      \(ri ** (qi ** pi ** mpq) ** mqr) => id))

public export
TypeProCompRelToInterp : (q, p : TypeProAr) -> (s, t, x : Type) ->
  InterpTypeProAr q s x -> InterpTypeProAr p x t ->
  InterpTypeProAr (TypeProArComp q p) s t
TypeProCompRelToInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) =
    ((pi ** qi ** pdmcont . qdmcovar) ** (qdmcont, pdmcovar))

public export
TypeProDimapDistrib : (q, p : TypeProAr) -> (s, t, a, b, x : Type) ->
  (qsx : InterpTypeProAr q s x) -> (pxt : InterpTypeProAr p x t) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  TypeProArDimap (TypeProArComp q p) s t a b mas mtb
    (TypeProCompRelToInterp q p s t x qsx pxt) =
  TypeProCompRelToInterp q p a b x
    (TypeProArDimap q s x a x mas Prelude.id qsx)
    (TypeProArDimap p x t x b Prelude.id mtb pxt)
TypeProDimapDistrib
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  qsx pst (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) mas mtb =
    Refl

public export
TypeProCompIntObj : (q, p : TypeProAr) -> (s, t : Type) ->
  InterpTypeProAr (TypeProArComp q p) s t -> Type
TypeProCompIntObj
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    pcontra pi

public export
TypeProCompFactFst : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeProArComp q p) s t) ->
  InterpTypeProAr p (TypeProCompIntObj q p s t qpst) t
TypeProCompFactFst
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (pi ** (id, dmcov))

public export
TypeProCompFactSnd : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeProArComp q p) s t) ->
  InterpTypeProAr q s (TypeProCompIntObj q p s t qpst)
TypeProCompFactSnd
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (qi ** (dmcont, mqp))

public export
TypeDiArId : TypeProAr
TypeDiArId = IntProArId Type

public export
TypeDiArComp : TypeProAr -> TypeProAr -> TypeProAr
TypeDiArComp = IntDiArComp Type TypeMor

public export
TypeDiCompToIdL : (p : TypeProAr) ->
  TypeDiNTar p (TypeDiArComp TypeDiArId p)
TypeDiCompToIdL (ppos ** (pcontra, pcovar)) =
  ((\pi, asn =>
    (pi **
     pcontra pi **
     id)) **
   (\_, _ => id,
    \_, _ => id))

public export
TypeDiCompFromIdL : (p : TypeProAr) ->
  TypeDiNTar (TypeDiArComp TypeDiArId p) p
TypeDiCompFromIdL (ppos ** (pcontra, pcovar)) =
  ((\pi, asn => fst pi) **
   (\(pi ** x ** dmcont), dmcov => dmcont,
    \(pi ** x ** dmcont), dmcov => id))

public export
TypeDiCompToIdR : (p : TypeProAr) ->
  TypeDiNTar p (TypeDiArComp p TypeDiArId)
TypeDiCompToIdR (ppos ** (pcontra, pcovar)) =
  (\pi, asn => (pcovar pi ** pi ** id) **
   (\_, _ => id,
    \_, _ => id))

public export
TypeDiCompFromIdR : (p : TypeProAr) ->
  TypeDiNTar (TypeDiArComp p TypeDiArId) p
TypeDiCompFromIdR (ppos ** (pcontra, pcovar)) =
  (\(x ** pi ** dmcov), dmcont => pi **
   (\(x ** pi ** dmcov), dmcont => id,
    \(x ** pi ** dmcov), dmcont => dmcov))

public export
TypeDiCompAssocL : (p, q, r : TypeProAr) ->
  TypeDiNTar
    (TypeDiArComp r (TypeDiArComp q p))
    (TypeDiArComp (TypeDiArComp r q) p)
TypeDiCompAssocL
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\((ri ** qi ** mqr) ** (pi ** mpq)), mrp =>
      (ri ** (qi ** pi ** mpq) ** mqr) **
     (\((ri ** qi ** mqr) ** (pi ** mpq)), mrp => id,
      \((ri ** qi ** mqr) ** (pi ** mpq)), mrp => id))

public export
TypeDiCompAssocR : (p, q, r : TypeProAr) ->
  TypeDiNTar
    (TypeDiArComp (TypeDiArComp r q) p)
    (TypeDiArComp r (TypeDiArComp q p))
TypeDiCompAssocR
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\(ri ** (qi ** pi ** mpq) ** mqr), mrp =>
      ((ri ** qi ** mqr) ** (pi ** mpq)) **
     (\(ri ** (qi ** pi ** mpq) ** mqr), mrp => id,
      \(ri ** (qi ** pi ** mpq) ** mqr), mrp => id))

public export
TypeDiCompRelToInterp : (q, p : TypeProAr) -> (s, t, x : Type) ->
  InterpTypeProAr q s x -> InterpTypeProAr p x t ->
  InterpTypeProAr (TypeDiArComp q p) s t
TypeDiCompRelToInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) =
    ((pi ** qi ** pdmcont . qdmcovar) ** (qdmcont, pdmcovar))

public export
TypeDiDimapDistrib : (q, p : TypeProAr) -> (s, t, a, b, x : Type) ->
  (qsx : InterpTypeProAr q s x) -> (pxt : InterpTypeProAr p x t) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  TypeProArDimap (TypeDiArComp q p) s t a b mas mtb
    (TypeDiCompRelToInterp q p s t x qsx pxt) =
  TypeDiCompRelToInterp q p a b x
    (TypeProArDimap q s x a x mas Prelude.id qsx)
    (TypeProArDimap p x t x b Prelude.id mtb pxt)
TypeDiDimapDistrib
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  qsx pst (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) mas mtb =
    Refl

public export
TypeDiCompIntObj : (q, p : TypeProAr) -> (s, t : Type) ->
  InterpTypeProAr (TypeDiArComp q p) s t -> Type
TypeDiCompIntObj
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    pcontra pi

public export
TypeDiCompFactFst : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeDiArComp q p) s t) ->
  InterpTypeProAr p (TypeDiCompIntObj q p s t qpst) t
TypeDiCompFactFst
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (pi ** (id, dmcov))

public export
TypeDiCompFactSnd : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeDiArComp q p) s t) ->
  InterpTypeProAr q s (TypeDiCompIntObj q p s t qpst)
TypeDiCompFactSnd
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (qi ** (dmcont, mqp))

----------------------------------------------
---- Interpretation of composition monoid ----
----------------------------------------------

public export
TypeProIdToIdInterp :
  TypeProfNT (InterpTypeProAr (IntProArId Type)) HomProf
TypeProIdToIdInterp x y (i ** (mxi, miy)) = miy . mxi

public export
TypeIdInterpToProId :
  TypeProfNT HomProf (InterpTypeProAr (IntProArId Type))
TypeIdInterpToProId x y mxy = (x ** (id, mxy))

public export
TypeProInterpCompToCompInterp : (q, p : TypeProAr) ->
  TypeProfNT
    (InterpTypeProAr (IntEndoProArComp Type TypeMor q p))
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
TypeProInterpCompToCompInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x y
  ((pi ** qi ** mqp) ** (dmx, dmy)) =
    (pcontra pi ** ((qi ** (dmx, mqp)), (pi ** (id, dmy))))

public export
TypeProCompInterpToInterpComp : (q, p : TypeProAr) ->
  TypeProfNT
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
    (InterpTypeProAr (IntEndoProArComp Type TypeMor q p))
TypeProCompInterpToInterpComp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x y
  (b ** ((qi ** (qcontm, qcovm)), (pi ** (pcontm, pcovm)))) =
    ((pi ** qi ** pcontm . qcovm) ** (qcontm, pcovm))

public export
TypeDiIdToIdInterp :
  TypeProfDiNT (InterpTypeProAr (IntProArId Type)) HomProf
TypeDiIdToIdInterp x (i ** (mxi, mix)) = mix . mxi

public export
TypeIdInterpToDiId :
  TypeProfDiNT HomProf (InterpTypeProAr (IntProArId Type))
TypeIdInterpToDiId x mxx = (x ** (id, mxx))

public export
TypeDiInterpCompToCompInterp : (q, p : TypeProAr) ->
  TypeProfDiNT
    (InterpTypeProAr (TypeDiArComp q p))
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
TypeDiInterpCompToCompInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x
  ((pi ** qi ** asn) ** (dmx, dmy)) =
    (pcontra pi ** ((qi ** (dmx, asn)), (pi ** (id, dmy))))

public export
TypeDiCompInterpToInterpComp : (q, p : TypeProAr) ->
  TypeProfDiNT
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
    (InterpTypeProAr (TypeDiArComp q p))
TypeDiCompInterpToInterpComp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x
  (b ** ((qi ** (xqc, qcb)), (pi ** (mbp, pcx)))) =
    ((pi ** qi ** mbp . qcb) ** (xqc, pcx))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Universal morphisms of poly-(para)natural transformations on `Type` ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-------------------------
---- Initial object ----
-------------------------

public export
TypeParaInitialPos : Type
TypeParaInitialPos = Void

public export
TypeParaInitialContra : TypeParaInitialPos -> Type
TypeParaInitialContra v = void v

public export
TypeParaInitialCovar : TypeParaInitialPos -> Type
TypeParaInitialCovar v = void v

public export
TypeParaInitial : TypeProAr
TypeParaInitial =
  (TypeParaInitialPos ** (TypeParaInitialContra, TypeParaInitialCovar))

public export
typeProFromInitialPos : (p : TypeProAr) -> TypeProNTpos TypeParaInitial p
typeProFromInitialPos p v = void v

public export
typeProFromInitialContra : (p : TypeProAr) ->
  TypeProNTcontra TypeParaInitial p (typeProFromInitialPos p)
typeProFromInitialContra p v = void v

public export
typeProFromInitialCovar : (p : TypeProAr) ->
  TypeProNTcovar TypeParaInitial p (typeProFromInitialPos p)
typeProFromInitialCovar p v = void v

public export
typeProFromInitial : (p : TypeProAr) -> TypeProNTar TypeParaInitial p
typeProFromInitial p =
  (typeProFromInitialPos p **
   (typeProFromInitialContra p,
    typeProFromInitialCovar p))

public export
typeParaFromInitial : (p : TypeProAr) -> TypeDiNTar TypeParaInitial p
typeParaFromInitial p =
  TypeProNTrestrict TypeParaInitial p $ typeProFromInitial p

public export
typeParaFromInitialPos : (p : TypeProAr) -> TypeDiNTpos TypeParaInitial p
typeParaFromInitialPos p =
  typeDiNTpos {p=TypeParaInitial} {q=p} $ typeParaFromInitial p

public export
typeParaFromInitialContra : (p : TypeProAr) ->
  TypeDiNTcontra TypeParaInitial p (typeParaFromInitialPos p)
typeParaFromInitialContra p =
  typeDiNTcontra {p=TypeParaInitial} {q=p} $ typeParaFromInitial p

public export
typeParaFromInitialCovar : (p : TypeProAr) ->
  TypeDiNTcovar TypeParaInitial p (typeParaFromInitialPos p)
typeParaFromInitialCovar p =
  typeDiNTcovar {p=TypeParaInitial} {q=p} $ typeParaFromInitial p

-------------------------
---- Terminal object ----
-------------------------

public export
TypeParaTerminalPos : Type
TypeParaTerminalPos = Unit

public export
TypeParaTerminalContra : TypeParaTerminalPos -> Type
TypeParaTerminalContra u = Unit

public export
TypeParaTerminalCovar : TypeParaTerminalPos -> Type
TypeParaTerminalCovar u = Void

public export
TypeParaTerminal : TypeProAr
TypeParaTerminal =
  (TypeParaTerminalPos ** (TypeParaTerminalContra, TypeParaTerminalCovar))

public export
typeProToTerminalPos : (p : TypeProAr) -> TypeProNTpos p TypeParaTerminal
typeProToTerminalPos p i = ()

public export
typeProToTerminalContra : (p : TypeProAr) ->
  TypeProNTcontra p TypeParaTerminal (typeProToTerminalPos p)
typeProToTerminalContra p i asn = ()

public export
typeProToTerminalCovar : (p : TypeProAr) ->
  TypeProNTcovar p TypeParaTerminal (typeProToTerminalPos p)
typeProToTerminalCovar p i v = void v

public export
typeProToTerminal : (p : TypeProAr) -> TypeProNTar p TypeParaTerminal
typeProToTerminal p =
  (typeProToTerminalPos p **
   (typeProToTerminalContra p,
    typeProToTerminalCovar p))

public export
typeParaToTerminal : (p : TypeProAr) -> TypeDiNTar p TypeParaTerminal
typeParaToTerminal p =
  TypeProNTrestrict p TypeParaTerminal $ typeProToTerminal p

public export
typeParaToTerminalPos : (p : TypeProAr) -> TypeDiNTpos p TypeParaTerminal
typeParaToTerminalPos p =
  typeDiNTpos {p} {q=TypeParaTerminal} $ typeParaToTerminal p

public export
typeParaToTerminalContra : (p : TypeProAr) ->
  TypeDiNTcontra p TypeParaTerminal (typeParaToTerminalPos p)
typeParaToTerminalContra p =
  typeDiNTcontra {p} {q=TypeParaTerminal} $ typeParaToTerminal p

public export
typeParaToTerminalCovar : (p : TypeProAr) ->
  TypeDiNTcovar p TypeParaTerminal (typeParaToTerminalPos p)
typeParaToTerminalCovar p =
  typeDiNTcovar {p} {q=TypeParaTerminal} $ typeParaToTerminal p

-------------------
---- Constants ----
-------------------

public export
TypeParaConst : Type -> TypeProAr
TypeParaConst x = (x ** (\_ => Unit, \_ => Void))

------------------------
---- Representables ----
------------------------

public export
TypeParaRepPos : Type -> Type -> Type
TypeParaRepPos x y = Unit

public export
TypeParaRepContra : (x, y : Type) -> TypeParaRepPos x y -> Type
TypeParaRepContra x y _ = x

public export
TypeParaRepCovar : (x, y : Type) -> TypeParaRepPos x y -> Type
TypeParaRepCovar x y _ = y

public export
TypeParaRep : Type -> Type -> TypeProAr
TypeParaRep x y =
  (TypeParaRepPos x y ** (TypeParaRepContra x y, TypeParaRepCovar x y))

public export
TypeParaContraRep : Type -> TypeProAr
TypeParaContraRep x = TypeParaRep x Void

public export
TypeParaCovarRep : Type -> TypeProAr
TypeParaCovarRep y = TypeParaRep Unit y

public export
TypeParaCovarId : TypeProAr
TypeParaCovarId = TypeParaCovarRep Unit

-- Given a polynomial functor, we can create a polynomial profunctor which
-- ignores its contravariant argument.
public export
TypeParaCovarPro : MLPolyCatObj -> TypeProAr
TypeParaCovarPro p = (pfPos p ** (\_ => Unit, pfDir {p}))

-- Given a Dirichlet functor, we can create a polynomial profunctor which
-- ignores its covariant argument.
public export
TypeParaContravarPro : MLDirichCatObj -> TypeProAr
TypeParaContravarPro p = (dfPos p ** (dfDir p, \_ => Void))

-------------------
---- Constants ----
-------------------

public export
TypeProConst : Type -> TypeProAr
TypeProConst x = (x ** (\_ => Unit, \_ => Void))

public export
TypeProConstCorrectL : (x, y, z : Type) ->
  x -> InterpTypeProAr (TypeProConst x) y z
TypeProConstCorrectL x y z ex = (ex ** (\_ => (), \v => void v))

public export
TypeProConstCorrectR : (x, y, z : Type) ->
  InterpTypeProAr (TypeProConst x) y z -> x
TypeProConstCorrectR x y z = DPair.fst

---------------------------
---- Hom-functor forms ----
---------------------------

-- This form of the hom-functor is the left adjoint of an adjunction
-- with the end functor.
public export
TypeProEndLAdj : Type -> TypeProAr
TypeProEndLAdj y = ((y ** Type) ** (\(ey ** ty) => ty, \(ey ** ty) => ty))

public export
TypeProEndLAdjCorrectL : (y : Type) ->
  TypeProfNT (TypeEndLAdj y) (InterpTypeProAr $ TypeProEndLAdj y)
TypeProEndLAdjCorrectL y a b (mab, ey) =
  ((ey ** a) ** (id {a}, mab))

public export
TypeProEndLAdjCorrectR : (y : Type) ->
  TypeProfNT (InterpTypeProAr $ TypeProEndLAdj y) (TypeEndLAdj y)
TypeProEndLAdjCorrectR y a b ((ey ** ty) ** (contra, covar)) =
  (covar . contra, ey)

-----------------------------
---- Partial application ----
-----------------------------

public export
typeProAppContra : TypeProAr -> Type -> MLPolyCatObj
typeProAppContra = ipaAppContra {d=Type} {c=Type} TypeMor

public export
typeProAppCovar : TypeProAr -> Type -> MLDirichCatObj
typeProAppCovar = ipaAppCovar {d=Type} {c=Type} TypeMor

public export
typeProAppContraToInterp : (ar : TypeProAr) -> (x, y : Type) ->
  InterpPolyFunc (typeProAppContra ar x) y ->
  InterpTypeProAr ar x y
typeProAppContraToInterp (pos ** (contra, covar)) x y ((i ** dmx) ** dmy) =
  (i ** (dmx, dmy))

public export
typeProAppContraFromInterp : (ar : TypeProAr) -> (x, y : Type) ->
  InterpTypeProAr ar x y ->
  InterpPolyFunc (typeProAppContra ar x) y
typeProAppContraFromInterp (pos ** (contra, covar)) x y (i ** (dmx, dmy)) =
  ((i ** dmx) ** dmy)

public export
typeProAppCovarToInterp : (ar : TypeProAr) -> (x, y : Type) ->
  InterpDirichFunc (typeProAppCovar ar y) x ->
  InterpTypeProAr ar x y
typeProAppCovarToInterp (pos ** (contra, covar)) x y ((i ** dmy) ** dmx) =
  (i ** (dmx, dmy))

public export
typeProAppCovarFromInterp : (ar : TypeProAr) -> (x, y : Type) ->
  InterpTypeProAr ar x y ->
  InterpDirichFunc (typeProAppCovar ar y) x
typeProAppCovarFromInterp (pos ** (contra, covar)) x y (i ** (dmx, dmy)) =
  ((i ** dmy) ** dmx)

---------------------------
---- Binary coproducts ----
---------------------------

public export
TypeParaCoproductPos : TypeProAr -> TypeProAr -> Type
TypeParaCoproductPos p q = Either (ipaPos p) (ipaPos q)

public export
TypeParaCoproductContra : (p, q : TypeProAr) ->
  TypeParaCoproductPos p q -> Type
TypeParaCoproductContra p q i =
  case i of
    Left pi => ipaContra p pi
    Right qi => ipaContra q qi

public export
TypeParaCoproductCovar : (p, q : TypeProAr) ->
  TypeParaCoproductPos p q -> Type
TypeParaCoproductCovar p q i =
  case i of
    Left pi => ipaCovar p pi
    Right qi => ipaCovar q qi

public export
TypeParaCoproduct : TypeProAr -> TypeProAr -> TypeProAr
TypeParaCoproduct p q =
  (TypeParaCoproductPos p q **
   (TypeParaCoproductContra p q,
    TypeParaCoproductCovar p q))

public export
typeProInjLpos : (p, q : TypeProAr) -> TypeProNTpos p (TypeParaCoproduct p q)
typeProInjLpos p q = Left

public export
typeProInjLcontra : (p, q : TypeProAr) ->
  TypeProNTcontra p (TypeParaCoproduct p q) (typeProInjLpos p q)
typeProInjLcontra p q = sliceId (ipaContra p)

public export
typeProInjLcovar : (p, q : TypeProAr) ->
  TypeProNTcovar p (TypeParaCoproduct p q) (typeProInjLpos p q)
typeProInjLcovar p q = sliceId (ipaCovar p)

public export
typeProInjL : (p, q : TypeProAr) -> TypeProNTar p (TypeParaCoproduct p q)
typeProInjL p q =
  (typeProInjLpos p q **
   (typeProInjLcontra p q,
    typeProInjLcovar p q))

public export
typeParaInjL : (p, q : TypeProAr) -> TypeDiNTar p (TypeParaCoproduct p q)
typeParaInjL p q = TypeProNTrestrict p (TypeParaCoproduct p q) $ typeProInjL p q

public export
typeParaInjLpos : (p, q : TypeProAr) -> TypeDiNTpos p (TypeParaCoproduct p q)
typeParaInjLpos p q =
  typeDiNTpos {p} {q=(TypeParaCoproduct p q)} $ typeParaInjL p q

public export
typeParaInjLcontra : (p, q : TypeProAr) ->
  TypeDiNTcontra p (TypeParaCoproduct p q) (typeParaInjLpos p q)
typeParaInjLcontra p q =
  typeDiNTcontra {p} {q=(TypeParaCoproduct p q)} $ typeParaInjL p q

public export
typeParaInjLcovar : (p, q : TypeProAr) ->
  TypeDiNTcovar p (TypeParaCoproduct p q) (typeParaInjLpos p q)
typeParaInjLcovar p q =
  typeDiNTcovar {p} {q=(TypeParaCoproduct p q)} $ typeParaInjL p q

public export
typeProInjRpos : (p, q : TypeProAr) -> TypeProNTpos q (TypeParaCoproduct p q)
typeProInjRpos p q = Right

public export
typeProInjRcontra : (p, q : TypeProAr) ->
  TypeProNTcontra q (TypeParaCoproduct p q) (typeProInjRpos p q)
typeProInjRcontra p q = sliceId (ipaContra q)

public export
typeProInjRcovar : (p, q : TypeProAr) ->
  TypeProNTcovar q (TypeParaCoproduct p q) (typeProInjRpos p q)
typeProInjRcovar p q = sliceId (ipaCovar q)

public export
typeProInjR : (p, q : TypeProAr) -> TypeProNTar q (TypeParaCoproduct p q)
typeProInjR p q =
  (typeProInjRpos p q **
   (typeProInjRcontra p q,
    typeProInjRcovar p q))

public export
typeParaInjR : (p, q : TypeProAr) -> TypeDiNTar q (TypeParaCoproduct p q)
typeParaInjR p q = TypeProNTrestrict q (TypeParaCoproduct p q) $ typeProInjR p q

public export
typeParaInjRpos : (p, q : TypeProAr) -> TypeDiNTpos q (TypeParaCoproduct p q)
typeParaInjRpos p q =
  typeDiNTpos {p=q} {q=(TypeParaCoproduct p q)} $ typeParaInjR p q

public export
typeParaInjRcontra : (p, q : TypeProAr) ->
  TypeDiNTcontra q (TypeParaCoproduct p q) (typeParaInjRpos p q)
typeParaInjRcontra p q =
  typeDiNTcontra {p=q} {q=(TypeParaCoproduct p q)} $ typeParaInjR p q

public export
typeParaInjRcovar : (p, q : TypeProAr) ->
  TypeDiNTcovar q (TypeParaCoproduct p q) (typeParaInjRpos p q)
typeParaInjRcovar p q =
  typeDiNTcovar {p=q} {q=(TypeParaCoproduct p q)} $ typeParaInjR p q

public export
typeDiCasePos : {p, q, r : TypeProAr} ->
  TypeDiNTar p r -> TypeDiNTar q r ->
  TypeDiNTpos (TypeParaCoproduct p q) r
typeDiCasePos {p} {q} {r} pr qr i asn with (i)
  typeDiCasePos {p} {q} {r} pr qr i asn | Left pi = typeDiNTpos pr pi asn
  typeDiCasePos {p} {q} {r} pr qr i asn | Right qi = typeDiNTpos qr qi asn

public export
typeDiCaseContra : {p, q, r : TypeProAr} ->
  (pr : TypeDiNTar p r) -> (qr : TypeDiNTar q r) ->
  TypeDiNTcontra (TypeParaCoproduct p q) r (typeDiCasePos {p} {q} {r} pr qr)
typeDiCaseContra {p} {q} {r} pr qr i asn with (i)
  typeDiCaseContra {p} {q} {r} pr qr i asn | Left pi = typeDiNTcontra pr pi asn
  typeDiCaseContra {p} {q} {r} pr qr i asn | Right qi = typeDiNTcontra qr qi asn

public export
typeDiCaseCovar : {p, q, r : TypeProAr} ->
  (pr : TypeDiNTar p r) -> (qr : TypeDiNTar q r) ->
  TypeDiNTcovar (TypeParaCoproduct p q) r (typeDiCasePos {p} {q} {r} pr qr)
typeDiCaseCovar {p} {q} {r} pr qr i asn with (i)
  typeDiCaseCovar {p} {q} {r} pr qr i asn | Left pi = typeDiNTcovar pr pi asn
  typeDiCaseCovar {p} {q} {r} pr qr i asn | Right qi = typeDiNTcovar qr qi asn

public export
typeDiCase : {p, q, r : TypeProAr} ->
  TypeDiNTar p r -> TypeDiNTar q r -> TypeDiNTar (TypeParaCoproduct p q) r
typeDiCase {p} {q} {r} pr qr =
  (typeDiCasePos pr qr **
   (typeDiCaseContra pr qr,
    typeDiCaseCovar pr qr))

-------------------------
---- Binary products ----
-------------------------

public export
TypeParaProductPos : TypeProAr -> TypeProAr -> Type
TypeParaProductPos p q = Pair (ipaPos p) (ipaPos q)

public export
TypeParaProductContra : (p, q : TypeProAr) ->
  TypeParaProductPos p q -> Type
TypeParaProductContra p q i = Pair (ipaContra p (fst i)) (ipaContra q (snd i))

public export
TypeParaProductCovar : (p, q : TypeProAr) ->
  TypeParaProductPos p q -> Type
TypeParaProductCovar p q i = Either (ipaCovar p (fst i)) (ipaCovar q (snd i))

public export
TypeParaProduct : TypeProAr -> TypeProAr -> TypeProAr
TypeParaProduct p q =
  (TypeParaProductPos p q **
   (TypeParaProductContra p q,
    TypeParaProductCovar p q))

public export
typeDiProdIntroPos : {p, q, r : TypeProAr} ->
  TypeDiNTar p q -> TypeDiNTar p r ->
  TypeDiNTpos p (TypeParaProduct q r)
typeDiProdIntroPos {p} {q} {r} pq pr i asn =
  (typeDiNTpos pq i asn, typeDiNTpos pr i asn)

public export
typeDiProdIntroContra : {p, q, r : TypeProAr} ->
  (pq : TypeDiNTar p q) -> (pr : TypeDiNTar p r) ->
  TypeDiNTcontra p (TypeParaProduct q r) (typeDiProdIntroPos {p} {q} {r} pq pr)
typeDiProdIntroContra {p} {q} {r} pq pr i asn d =
  (typeDiNTcontra pq i asn d, typeDiNTcontra pr i asn d)

public export
typeDiProdIntroCovar : {p, q, r : TypeProAr} ->
  (pq : TypeDiNTar p q) -> (pr : TypeDiNTar p r) ->
  TypeDiNTcovar p (TypeParaProduct q r) (typeDiProdIntroPos {p} {q} {r} pq pr)
typeDiProdIntroCovar {p} {q} {r} pq pr i asn d with (d)
  typeDiProdIntroCovar {p} {q} {r} pq pr i asn d | Left pd =
    typeDiNTcovar pq i asn pd
  typeDiProdIntroCovar {p} {q} {r} pq pr i asn d | Right qd =
    typeDiNTcovar pr i asn qd

public export
typeDiProdIntro : {p, q, r : TypeProAr} ->
  TypeDiNTar p q -> TypeDiNTar p r -> TypeDiNTar p (TypeParaProduct q r)
typeDiProdIntro {p} {q} {r} pq pr =
  (typeDiProdIntroPos pq pr **
   (typeDiProdIntroContra pq pr,
    typeDiProdIntroCovar pq pr))

public export
typeParaProj1pos : (p, q : TypeProAr) -> TypeDiNTpos (TypeParaProduct p q) p
typeParaProj1pos p q i asn = fst i

public export
typeParaProj1contra : (p, q : TypeProAr) ->
  TypeDiNTcontra (TypeParaProduct p q) p (typeParaProj1pos p q)
typeParaProj1contra p q i asn d = fst d

public export
typeParaProj1covar : (p, q : TypeProAr) ->
  TypeDiNTcovar (TypeParaProduct p q) p (typeParaProj1pos p q)
typeParaProj1covar p q i asn d = Left d

public export
typeParaProj1 : (p, q : TypeProAr) ->
  TypeDiNTar (TypeParaProduct p q) p
typeParaProj1 p q =
  (typeParaProj1pos p q **
   (typeParaProj1contra p q,
    typeParaProj1covar p q))

public export
typeParaProj2pos : (p, q : TypeProAr) -> TypeDiNTpos (TypeParaProduct p q) q
typeParaProj2pos p q i asn = snd i

public export
typeParaProj2contra : (p, q : TypeProAr) ->
  TypeDiNTcontra (TypeParaProduct p q) q (typeParaProj2pos p q)
typeParaProj2contra p q i asn d = snd d

public export
typeParaProj2covar : (p, q : TypeProAr) ->
  TypeDiNTcovar (TypeParaProduct p q) q (typeParaProj2pos p q)
typeParaProj2covar p q i asn d = Right d

public export
typeParaProj2 : (p, q : TypeProAr) ->
  TypeDiNTar (TypeParaProduct p q) q
typeParaProj2 p q =
  (typeParaProj2pos p q **
   (typeParaProj2contra p q,
    typeParaProj2covar p q))

----------------------------------
---- Binary parallel products ----
----------------------------------

public export
TypeParaParProductPos : TypeProAr -> TypeProAr -> Type
TypeParaParProductPos p q =
  Pair (ipaPos p) (ipaPos q)

public export
TypeParaParProductContra : (p, q : TypeProAr) ->
  TypeParaParProductPos p q -> Type
TypeParaParProductContra p q i =
  Pair (ipaContra p (fst i)) (ipaContra q (snd i))

public export
TypeParaParProductCovar : (p, q : TypeProAr) ->
  TypeParaParProductPos p q -> Type
TypeParaParProductCovar p q i =
  Pair (ipaCovar p (fst i)) (ipaCovar q (snd i))

public export
TypeParaParProduct : TypeProAr -> TypeProAr -> TypeProAr
TypeParaParProduct p q =
  (TypeParaParProductPos p q **
   (TypeParaParProductContra p q,
    TypeParaParProductCovar p q))

----------------------
---- Set products ----
----------------------

public export
TypeParaSetProductPos : {a : Type} -> (a -> TypeProAr) -> Type
TypeParaSetProductPos {a} ps = Pi {a} (ipaPos . ps)

public export
TypeParaSetProductContra : {a : Type} -> (ps : a -> TypeProAr) ->
  TypeParaSetProductPos {a} ps -> Type
TypeParaSetProductContra {a} ps i = (ea : a) -> ipaContra (ps ea) (i ea)

public export
TypeParaSetProductCovar : {a : Type} -> (ps : a -> TypeProAr) ->
  TypeParaSetProductPos {a} ps -> Type
TypeParaSetProductCovar {a} ps i = (ea : a ** ipaCovar (ps ea) (i ea))

public export
TypeParaSetProduct : {a : Type} -> (a -> TypeProAr) -> TypeProAr
TypeParaSetProduct {a} ps =
  (TypeParaSetProductPos {a} ps **
   (TypeParaSetProductContra {a} ps,
    TypeParaSetProductCovar {a} ps))

public export
typeDiSetProdIntroPos :
  {a : Type} -> {p : TypeProAr} -> {qs : a -> TypeProAr} ->
  ((ea : a) -> TypeDiNTar p (qs ea)) ->
  TypeDiNTpos p (TypeParaSetProduct {a} qs)
typeDiSetProdIntroPos {a} {p} {qs} arfam i asn ea =
  typeDiNTpos (arfam ea) i asn

public export
typeDiSetProdIntroContra :
  {a : Type} -> {p : TypeProAr} -> {qs : a -> TypeProAr} ->
  (arfam : (ea : a) -> TypeDiNTar p (qs ea)) ->
  TypeDiNTcontra
    p
    (TypeParaSetProduct {a} qs)
    (typeDiSetProdIntroPos {a} {p} {qs} arfam)
typeDiSetProdIntroContra {a} {p} {qs} arfam i asn d ea =
  typeDiNTcontra (arfam ea) i asn d

public export
typeDiSetProdIntroCovar :
  {a : Type} -> {p : TypeProAr} -> {qs : a -> TypeProAr} ->
  (arfam : (ea : a) -> TypeDiNTar p (qs ea)) ->
  TypeDiNTcovar
    p
    (TypeParaSetProduct {a} qs)
    (typeDiSetProdIntroPos {a} {p} {qs} arfam)
typeDiSetProdIntroCovar {a} {p} {qs} arfam i asn d =
  typeDiNTcovar (arfam $ fst d) i asn (snd d)

public export
typeDiSetProdIntro : {a : Type} -> {p : TypeProAr} -> {qs : a -> TypeProAr} ->
  ((ea : a) -> TypeDiNTar p (qs ea)) ->
  TypeDiNTar p (TypeParaSetProduct {a} qs)
typeDiSetProdIntro {a} {p} {qs} arfam =
  (typeDiSetProdIntroPos arfam **
   (typeDiSetProdIntroContra arfam,
    typeDiSetProdIntroCovar arfam))

public export
typeDiSetProjPos :
  {a : Type} -> (qs : a -> TypeProAr) ->
  (ea : a) -> TypeDiNTpos (TypeParaSetProduct {a} qs) (qs ea)
typeDiSetProjPos {a} qs ea i asn = i ea

public export
typeDiSetProjContra :
  {a : Type} -> (qs : a -> TypeProAr) ->
  (ea : a) ->
  TypeDiNTcontra
    (TypeParaSetProduct {a} qs)
    (qs ea)
    (typeDiSetProjPos {a} qs ea)
typeDiSetProjContra {a} qs ea i asn d = d ea

public export
typeDiSetProjCovar :
  {a : Type} -> (qs : a -> TypeProAr) ->
  (ea : a) ->
  TypeDiNTcovar
    (TypeParaSetProduct {a} qs)
    (qs ea)
    (typeDiSetProjPos {a} qs ea)
typeDiSetProjCovar {a} qs ea i asn d = (ea ** d)

public export
typeDiSetProj : {a : Type} -> (qs : a -> TypeProAr) ->
  (ea : a) -> TypeDiNTar (TypeParaSetProduct {a} qs) (qs ea)
typeDiSetProj {a} qs ea =
  (typeDiSetProjPos {a} qs ea **
   (typeDiSetProjContra {a} qs ea,
    typeDiSetProjCovar {a} qs ea))

----------------------------------------------------
---- Distributivity of products over coproducts ----
----------------------------------------------------

public export
typeParaDistribPos : (p, q, r : TypeProAr) ->
  TypeDiNTpos
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
typeParaDistribPos p q r i asn with (i)
  typeParaDistribPos p q r i asn | (pi, Left qi) = Left (pi, qi)
  typeParaDistribPos p q r i asn | (pi, Right ri) = Right (pi, ri)

public export
typeParaDistribContra : (p, q, r : TypeProAr) ->
  TypeDiNTcontra
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
    (typeParaDistribPos p q r)
typeParaDistribContra p q r i asn d with (i)
  typeParaDistribContra p q r i asn d | (pi, Left qi) = d
  typeParaDistribContra p q r i asn d | (pi, Right ri) = d

public export
typeParaDistribCovar : (p, q, r : TypeProAr) ->
  TypeDiNTcovar
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
    (typeParaDistribPos p q r)
typeParaDistribCovar p q r i asn d with (i)
  typeParaDistribCovar p q r i asn d | (pi, Left qi) = d
  typeParaDistribCovar p q r i asn d | (pi, Right ri) = d

public export
typeParaDistrib : (p, q, r : TypeProAr) ->
  TypeDiNTar
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
typeParaDistrib p q r =
  (typeParaDistribPos p q r **
   (typeParaDistribContra p q r,
    typeParaDistribCovar p q r))

---------------------
---- Hom-objects ----
---------------------

-- We compute hom-objects in steps, beginning with representable domains.

-- First we consider hom-objects whose domains are covariant representables --
-- that is, they ignore their contravariant arguments (in other words, they
-- are representables represened by pairs with contravariant component `Unit`).

public export
TypeParaCovarRepHomObjPos : Type -> TypeProAr -> Type
TypeParaCovarRepHomObjPos p q = (qi : ipaPos q ** ipaCovar q qi -> Either () p)

public export
TypeParaCovarRepHomObjContra : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepHomObjPos p q) -> Type
TypeParaCovarRepHomObjContra p q i = ipaContra q $ fst i

public export
TypeParaCovarRepHomObjCovarSnd : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepHomObjPos p q) -> ipaCovar q (fst i) -> Type
TypeParaCovarRepHomObjCovarSnd p q i qcov with (snd i qcov)
  TypeParaCovarRepHomObjCovarSnd p q i qcov | Left () = Unit
  TypeParaCovarRepHomObjCovarSnd p q i qcov | Right ep = Void

public export
TypeParaCovarRepHomObjCovar : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepHomObjPos p q) -> Type
TypeParaCovarRepHomObjCovar p q i =
  DPair (ipaCovar q $ fst i) (TypeParaCovarRepHomObjCovarSnd p q i)

public export
TypeParaCovarRepHomObj : Type -> TypeProAr -> TypeProAr
TypeParaCovarRepHomObj p q =
  (TypeParaCovarRepHomObjPos p q **
   (TypeParaCovarRepHomObjContra p q,
    TypeParaCovarRepHomObjCovar p q))

public export
typeParaCovarRepEvalPos : (p : Type) -> (q : TypeProAr) ->
  TypeProNTpos
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
typeParaCovarRepEvalPos p q i = fst $ fst i

public export
typeParaCovarRepEvalContra : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcontra
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
    (typeParaCovarRepEvalPos p q)
typeParaCovarRepEvalContra p q i d = fst d

public export
typeParaCovarRepEvalCovar : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcovar
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
    (typeParaCovarRepEvalPos p q)
typeParaCovarRepEvalCovar p q i d with (snd (fst i) d) proof eq
  typeParaCovarRepEvalCovar p q i d | Left () = Left (d ** rewrite eq in ())
  typeParaCovarRepEvalCovar p q i d | Right ep = Right ep

public export
typeParaCovarRepEval : (p : Type) -> (q : TypeProAr) ->
  TypeProNTar
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
typeParaCovarRepEval p q =
  (typeParaCovarRepEvalPos p q **
   (typeParaCovarRepEvalContra p q,
    typeParaCovarRepEvalCovar p q))

public export
typeParaCovarRepCurryPos : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r ->
  TypeProNTpos p (TypeParaCovarRepHomObj q r)
typeParaCovarRepCurryPos {q} {p} {r} (onpos ** (oncontra, oncovar)) i =
  (onpos (i, ()) **
   \rcov => case oncovar (i, ()) rcov of
    Left pcov => Left ()
    Right elq => Right elq)

public export
typeParaCovarRepCurryContra : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r) ->
  TypeProNTcontra
    p
    (TypeParaCovarRepHomObj q r)
    (typeParaCovarRepCurryPos {q} {p} {r} ar)
typeParaCovarRepCurryContra (onpos ** (oncontra, oncovar)) pi pcont =
  oncontra (pi, ()) (pcont, ())

public export
typeParaCovarRepCurryCovar : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r) ->
  TypeProNTcovar
    p
    (TypeParaCovarRepHomObj q r)
    (typeParaCovarRepCurryPos {q} {p} {r} ar)
typeParaCovarRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    with (oncovar (pi, ()) rcov1) proof eq
  typeParaCovarRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    | Left pcov = pcov
  typeParaCovarRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    | Right elq = void rcov2

public export
typeParaCovarRepCurry : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r ->
  TypeProNTar p (TypeParaCovarRepHomObj q r)
typeParaCovarRepCurry {q} {p} {r} ar =
  (typeParaCovarRepCurryPos {q} {p} {r} ar **
   (typeParaCovarRepCurryContra {q} {p} {r} ar,
    typeParaCovarRepCurryCovar {q} {p} {r} ar))

-- Next we consider hom-objects whose domains are contravariant
-- representables -- that is, they ignore their covariant arguments (in other
-- words, they are representables represened by pairs with covariant component
-- `Void`).

public export
TypeParaContraRepHomObjPos : Type -> TypeProAr -> Type
TypeParaContraRepHomObjPos p q = ipaPos q

public export
TypeParaContraRepHomObjContra : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaContraRepHomObjPos p q) -> Type
TypeParaContraRepHomObjContra p q i = p -> ipaContra q i

public export
TypeParaContraRepHomObjCovar : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaContraRepHomObjPos p q) -> Type
TypeParaContraRepHomObjCovar p q i = ipaCovar q i

public export
TypeParaContraRepHomObj : Type -> TypeProAr -> TypeProAr
TypeParaContraRepHomObj p q =
  (TypeParaContraRepHomObjPos p q **
   (TypeParaContraRepHomObjContra p q,
    TypeParaContraRepHomObjCovar p q))

public export
typeParaContraRepEvalPos : (p : Type) -> (q : TypeProAr) ->
  TypeProNTpos
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
typeParaContraRepEvalPos p q i = fst i

public export
typeParaContraRepEvalContra : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcontra
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
    (typeParaContraRepEvalPos p q)
typeParaContraRepEvalContra p q i d = fst d (snd d)

public export
typeParaContraRepEvalCovar : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcovar
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
    (typeParaContraRepEvalPos p q)
typeParaContraRepEvalCovar p q i d = Left d

public export
typeParaContraRepEval : (p : Type) -> (q : TypeProAr) ->
  TypeProNTar
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
typeParaContraRepEval p q =
  (typeParaContraRepEvalPos p q **
   (typeParaContraRepEvalContra p q,
    typeParaContraRepEvalCovar p q))

public export
typeParaContraRepCurryPos : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r ->
  TypeProNTpos p (TypeParaContraRepHomObj q r)
typeParaContraRepCurryPos {q} {p} {r} (onpos ** (oncontra, oncovar)) i =
  onpos (i, ())

public export
typeParaContraRepCurryContra : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r) ->
  TypeProNTcontra
    p
    (TypeParaContraRepHomObj q r)
    (typeParaContraRepCurryPos {q} {p} {r} ar)
typeParaContraRepCurryContra (onpos ** (oncontra, oncovar)) pi pcont elq =
  oncontra (pi, ()) (pcont, elq)

public export
typeParaContraRepCurryCovar : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r) ->
  TypeProNTcovar
    p
    (TypeParaContraRepHomObj q r)
    (typeParaContraRepCurryPos {q} {p} {r} ar)
typeParaContraRepCurryCovar (onpos ** (oncontra, oncovar)) pi rcov =
  case oncovar (pi, ()) rcov of
    Left pcov => pcov
    Right v => void v

public export
typeParaContraRepCurry : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r ->
  TypeProNTar p (TypeParaContraRepHomObj q r)
typeParaContraRepCurry {q} {p} {r} ar =
  (typeParaContraRepCurryPos {q} {p} {r} ar **
   (typeParaContraRepCurryContra {q} {p} {r} ar,
    typeParaContraRepCurryCovar {q} {p} {r} ar))

-- Now we can put the two forms of representables together to obtain
-- the hom-object out of a representable which potentially uses both
-- its covariant and contravariant arguments:  a general representable
-- is a product of a contravariant and a covariant representable, so
-- a hom-object out of it is equivalent to a hom-object out of one of
-- them into a hom-object out of the other.  Thus we can define the
-- hom-object of a general representable by composition.

public export
TypeParaRepHomObj : Type -> Type -> TypeProAr -> TypeProAr
TypeParaRepHomObj p p' q =
  TypeParaContraRepHomObj p (TypeParaCovarRepHomObj p' q)

public export
typeProRepEvalPos : (p, p' : Type) -> (q : TypeProAr) ->
  TypeProNTpos
    (TypeParaProduct (TypeParaRepHomObj p p' q) (TypeParaRep p p'))
    q
typeProRepEvalPos p p' q i = fst $ fst i

public export
typeProRepEvalContra : (p, p' : Type) -> (q : TypeProAr) ->
  TypeProNTcontra
    (TypeParaProduct (TypeParaRepHomObj p p' q) (TypeParaRep p p'))
    q
    (typeProRepEvalPos p p' q)
typeProRepEvalContra p p' q i d = fst d $ snd d

public export
typeProRepEvalCovar : (p, p' : Type) -> (q : TypeProAr) ->
  TypeProNTcovar
    (TypeParaProduct (TypeParaRepHomObj p p' q) (TypeParaRep p p'))
    q
    (typeProRepEvalPos p p' q)
typeProRepEvalCovar p p' q i d with (snd (fst i) d) proof eq
  typeProRepEvalCovar p p' q i d | Left () = Left (d ** rewrite eq in ())
  typeProRepEvalCovar p p' q i d | Right ep = Right ep

public export
typeProRepEval : (p, p' : Type) -> (q : TypeProAr) ->
  TypeProNTar
    (TypeParaProduct (TypeParaRepHomObj p p' q) (TypeParaRep p p'))
    q
typeProRepEval p p' q =
  (typeProRepEvalPos p p' q **
   (typeProRepEvalContra p p' q,
    typeProRepEvalCovar p p' q))

public export
typeProRepCurryPos : {q, q' : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaRep q q')) r ->
  TypeProNTpos p (TypeParaRepHomObj q q' r)
typeProRepCurryPos {q} {q'} {p} {r} (onpos ** (oncontra, oncovar)) i =
  (onpos (i, ()) **
   \rcov => case oncovar (i, ()) rcov of
    Left pcov => Left ()
    Right elq => Right elq)

public export
typeProRepCurryContra : {q, q' : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaRep q q')) r) ->
  TypeProNTcontra
    p
    (TypeParaRepHomObj q q' r)
    (typeProRepCurryPos {q} {q'} {p} {r} ar)
typeProRepCurryContra (onpos ** (oncontra, oncovar)) pi pcont elq =
  oncontra (pi, ()) (pcont, elq)

public export
typeProRepCurryCovar : {q, q' : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaRep q q')) r) ->
  TypeProNTcovar
    p
    (TypeParaRepHomObj q q' r)
    (typeProRepCurryPos {q} {q'} {p} {r} ar)
typeProRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    with (oncovar (pi, ()) rcov1) proof eq
  typeProRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    | Left pcov = pcov
  typeProRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    | Right elq = void rcov2

public export
typeProRepCurry : {q, q' : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaRep q q')) r ->
  TypeProNTar p (TypeParaRepHomObj q q' r)
typeProRepCurry {q} {q'} {p} {r} ar =
  (typeProRepCurryPos {q} {q'} {p} {r} ar **
   (typeProRepCurryContra {q} {q'} {p} {r} ar,
    typeProRepCurryCovar {q} {q'} {p} {r} ar))

-- Finally, we can write general hom-objects:  a polynomial profunctor
-- is a coproduct of (general -- that is, potentially depending on both
-- contravariant and covariant arguments) representables, so a morphism
-- out of it is a product of morphisms out of general representables.

public export
TypeProHomObj : TypeProAr -> TypeProAr -> TypeProAr
TypeProHomObj p q =
  TypeParaSetProduct
    {a=(ipaPos p)}
    (\pi => TypeParaRepHomObj (ipaContra p pi) (ipaCovar p pi) q)

public export
typeProEvalPos : (p, q : TypeProAr) ->
  TypeProNTpos (TypeParaProduct (TypeProHomObj p q) p) q
typeProEvalPos p q i = fst $ fst i $ snd i

public export
typeProEvalContra : (p, q : TypeProAr) ->
  TypeProNTcontra (TypeParaProduct (TypeProHomObj p q) p) q (typeProEvalPos p q)
typeProEvalContra p q i d = fst d (snd i) (snd d)

public export
typeProEvalCovar : (p, q : TypeProAr) ->
  TypeProNTcovar (TypeParaProduct (TypeProHomObj p q) p) q (typeProEvalPos p q)
typeProEvalCovar p q i d with (snd (fst i $ snd i) d) proof eq
  typeProEvalCovar p q i d | Left () = Left (snd i ** d ** rewrite eq in ())
  typeProEvalCovar p q i d | Right pcov = Right pcov

public export
typeProEval : (p, q : TypeProAr) ->
  TypeProNTar (TypeParaProduct (TypeProHomObj p q) p) q
typeProEval p q =
  (typeProEvalPos p q **
   (typeProEvalContra p q,
    typeProEvalCovar p q))

public export
typeProCurryPos : {p, q, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p q) r ->
  TypeProNTpos p (TypeProHomObj q r)
typeProCurryPos {p} {q} {r} (onpos ** (oncontra, oncovar)) pi qi =
  (onpos (pi, qi) **
   \rcov => case oncovar (pi, qi) rcov of
    Left pcov => Left ()
    Right qcov => Right qcov)

public export
typeProCurryContra : {p, q, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p q) r) ->
  TypeProNTcontra p (TypeProHomObj q r) (typeProCurryPos {p} {q} {r} ar)
typeProCurryContra (onpos ** (oncontra, oncovar)) pi pcont qi qcont =
  oncontra (pi, qi) (pcont, qcont)

public export
typeProCurryCovar : {p, q, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p q) r) ->
  TypeProNTcovar p (TypeProHomObj q r) (typeProCurryPos {p} {q} {r} ar)
typeProCurryCovar (onpos ** (oncontra, oncovar)) pi (qi ** rcov1 ** rcov2)
    with (oncovar (pi, qi) rcov1) proof eq
  typeProCurryCovar (onpos ** (oncontra, oncovar)) pi (qi ** rcov1 ** rcov2)
    | Left pcov = pcov
  typeProCurryCovar (onpos ** (oncontra, oncovar)) pi (qi ** rcov1 ** rcov2)
    | Right qcov = void rcov2

public export
typeProCurry : {p, q, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p q) r ->
  TypeProNTar p (TypeProHomObj q r)
typeProCurry {p} {q} {r} ar =
  (typeProCurryPos {p} {q} {r} ar **
   (typeProCurryContra {p} {q} {r} ar,
    typeProCurryCovar {p} {q} {r} ar))

----------------------------------
---- Parallel product closure ----
----------------------------------

-- As with hom-objects, we compute the parallel product closure in steps.

-- First we consider parallel-closure-objects whose domains are covariant
-- representables -- that is, they ignore their contravariant arguments (in
-- other words, they are representables represened by pairs with contravariant
-- component `Unit`).

public export
TypeParaCovarRepParClosPos : Type -> TypeProAr -> Type
TypeParaCovarRepParClosPos p q = (qi : ipaPos q ** ipaCovar q qi -> p)

public export
TypeParaCovarRepParClosContra : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepParClosPos p q) -> Type
TypeParaCovarRepParClosContra p q i = ipaContra q $ fst i

public export
TypeParaCovarRepParClosCovar : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepParClosPos p q) -> Type
TypeParaCovarRepParClosCovar p q i = ipaCovar q $ fst i

public export
TypeParaCovarRepParClos : Type -> TypeProAr -> TypeProAr
TypeParaCovarRepParClos p q =
  (TypeParaCovarRepParClosPos p q **
   (TypeParaCovarRepParClosContra p q,
    TypeParaCovarRepParClosCovar p q))

public export
typeParaCovarRepParEvalPos : (p : Type) -> (q : TypeProAr) ->
  TypeProNTpos
    (TypeParaParProduct (TypeParaCovarRepParClos p q) (TypeParaCovarRep p))
    q
typeParaCovarRepParEvalPos p q i = fst $ fst i

public export
typeParaCovarRepParEvalContra : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcontra
    (TypeParaParProduct (TypeParaCovarRepParClos p q) (TypeParaCovarRep p))
    q
    (typeParaCovarRepParEvalPos p q)
typeParaCovarRepParEvalContra p q i d = fst d

public export
typeParaCovarRepParEvalCovar : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcovar
    (TypeParaParProduct (TypeParaCovarRepParClos p q) (TypeParaCovarRep p))
    q
    (typeParaCovarRepParEvalPos p q)
typeParaCovarRepParEvalCovar p q i d = (d, snd (fst i) d)

public export
typeParaCovarRepParEval : (p : Type) -> (q : TypeProAr) ->
  TypeProNTar
    (TypeParaParProduct (TypeParaCovarRepParClos p q) (TypeParaCovarRep p))
    q
typeParaCovarRepParEval p q =
  (typeParaCovarRepParEvalPos p q **
   (typeParaCovarRepParEvalContra p q,
    typeParaCovarRepParEvalCovar p q))

public export
typeParaCovarRepParCurryPos : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaParProduct p (TypeParaCovarRep q)) r ->
  TypeProNTpos p (TypeParaCovarRepParClos q r)
typeParaCovarRepParCurryPos {q} {p} {r} (onpos ** (oncontra, oncovar)) i =
  (onpos (i, ()) ** snd . oncovar (i, ()))

public export
typeParaCovarRepParCurryContra : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaParProduct p (TypeParaCovarRep q)) r) ->
  TypeProNTcontra
    p
    (TypeParaCovarRepParClos q r)
    (typeParaCovarRepParCurryPos {q} {p} {r} ar)
typeParaCovarRepParCurryContra (onpos ** (oncontra, oncovar)) pi pcont =
  oncontra (pi, ()) (pcont, ())

public export
typeParaCovarRepParCurryCovar : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaParProduct p (TypeParaCovarRep q)) r) ->
  TypeProNTcovar
    p
    (TypeParaCovarRepParClos q r)
    (typeParaCovarRepParCurryPos {q} {p} {r} ar)
typeParaCovarRepParCurryCovar (onpos ** (oncontra, oncovar)) pi =
  fst . oncovar (pi, ())

public export
typeParaCovarRepParCurry : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaParProduct p (TypeParaCovarRep q)) r ->
  TypeProNTar p (TypeParaCovarRepParClos q r)
typeParaCovarRepParCurry {q} {p} {r} ar =
  (typeParaCovarRepParCurryPos {q} {p} {r} ar **
   (typeParaCovarRepParCurryContra {q} {p} {r} ar,
    typeParaCovarRepParCurryCovar {q} {p} {r} ar))

---------------
---------------
---- Ends ----
---------------
---------------

public export
EndRAdj : TypeProAr -> Type
EndRAdj p = TypeDiNTar (TypeProConst Unit) p

public export
0 EndRAdjCorrectR : FunExt -> (p : TypeProAr) ->
  EndRAdj p -> TypeEnd (InterpTypeProAr p) (TypeProArLmap p) (TypeProArRmap p)
EndRAdjCorrectR fext p e =
  ProfParaNTtoEnd
    fext
    (InterpTypeProAr p)
    (TypeProArLmap p)
    (TypeProArRmap p)
    (\a, () =>
      InterpTypeDiNT (TypeProConst Unit) p e a (() ** (\_ => (), \v => void v)))
    (\i0, i1, i2, (), (), Refl =>
      TypeDiArIsPara (TypeProConst Unit) p e i0 i1 i2
        (() ** (\_ => (), \v => void v)) (() ** (\_ => (), \v => void v))
        (dpEq12 Refl (pairEqCong Refl (funExt $ \v => void v))))

public export
0 EndRAdjCorrectL : FunExt -> (p : TypeProAr) ->
  TypeEnd (InterpTypeProAr p) (TypeProArLmap p) (TypeProArRmap p) -> EndRAdj p
EndRAdjCorrectL fext p e =
  TypeDiArFromDi (TypeProConst Unit) p
    (\x, _ =>
      ProfParaNTfromEnd fext
        (InterpTypeProAr p) (TypeProArLmap p) (TypeProArRmap p) e x ())
    (\i0, i1, i2, (() ** (uf, vf)), (() ** (uf', vf')), cond =>
      ProfParaNTfromEndisPara fext
        (InterpTypeProAr p) (TypeProArLmap p) (TypeProArRmap p) e i0 i1 i2
        () () Refl)

public export
EndLAdj : Type -> TypeProAr
EndLAdj = TypeProEndLAdj

public export
EndCounit : (p : TypeProAr) -> TypeProNTar (EndLAdj $ EndRAdj p) p
EndCounit (pos ** (contra, covar)) =
  (\((ip ** (icont, icov)) ** ty) => ip () (\_ => ()) **
   (\((ip ** (icont, icov)) ** ty), ety => icont () (\_ => ()) (),
    \((ip ** (icont, icov)) ** ty), dcov => void $ icov () (\_ => ()) dcov))

--------------------------------------
--------------------------------------
---- Composition with polynomials ----
--------------------------------------
--------------------------------------

-- A polynomial profunctor goes from `(op(Type), Type)` to `Type`, so we can
-- postcompose an endofunctor on `Type` and obtain another profunctor.  In
-- particular, we can postcompose a _polynomial_ endofunctor and obtain another
-- _polynomial_ profunctor.
--
-- This composition turns out to have the same on-positions function as the
-- composition of polynomials and the post-composition of polynomials after
-- Dirichlet functors, both of which have the same on-positions function.
-- Furthermore, it has the same on-covariant-directions function as the
-- on-directions function of the composition of polynomials, and the same
-- on-contravariant-directions function of the post-composition of polynomials
-- after Dirichlets.
public export
TypeProPostcompPoly : MLPolyCatObj -> TypeProAr -> TypeProAr
TypeProPostcompPoly q p =
  ((qi : pfPos q ** pfDir {p=q} qi -> ipaPos p) **
   (\qiqm => (qd : pfDir {p=q} (fst qiqm)) -> ipaContra p $ snd qiqm qd,
    \qiqm => (qd : pfDir {p=q} (fst qiqm) ** ipaCovar p $ snd qiqm qd)))

-- We show that that produces the expected composition.
public export
TypeProPostcompPolyFromInterp : (q : MLPolyCatObj) -> (p : TypeProAr) ->
  (x, y : Type) ->
  InterpPolyFunc q (InterpTypeProAr p x y) ->
  InterpTypeProAr (TypeProPostcompPoly q p) x y
TypeProPostcompPolyFromInterp q p x y
  (i ** dm) =
    ((i ** \qd => fst (dm qd)) **
     (\ex, qd => fst (snd $ dm qd) ex,
      \(qd ** pcov) => snd (snd $ dm qd) pcov))

public export
TypeProPostcompPolyToInterp : (q : MLPolyCatObj) -> (p : TypeProAr) ->
  (x, y : Type) ->
  InterpTypeProAr (TypeProPostcompPoly q p) x y ->
  InterpPolyFunc q (InterpTypeProAr p x y)
TypeProPostcompPolyToInterp q p x y
  ((qi ** qm) ** (dmx, dmy)) =
    (qi **
     \qd => (qm qd ** (\ex => dmx ex qd, \pcov => dmy (qd ** pcov))))

public export
PolyPrecompTypePro : TypeProAr -> MLPolyCatObj -> TypeProAr
PolyPrecompTypePro = flip TypeProPostcompPoly

------------------------------
------------------------------
---- Kan extensions/lifts ----
------------------------------
------------------------------

-----------------------------
---- Left Kan extensions ----
-----------------------------

public export
typeProArLKanExt : TypeProAr -> TypeProAr -> PolyFunc
typeProArLKanExt q p =
  (ipaPos p ** \pi => InterpTypeProAr q (ipaContra p pi) (ipaCovar p pi))

public export
typeProLKanExtUnit : (q : TypeProAr) -> (p : TypeProAr) ->
  TypeProNTar p (PolyPrecompTypePro q $ typeProArLKanExt q p)
typeProLKanExtUnit q p =
  (\pi => (pi ** \qi => fst qi) **
   (\pi, pcont, qd => fst (snd qd) pcont,
    \pi, qdpcov => snd (snd $ fst qdpcov) (snd qdpcov)))

public export
typeProLKanExtCounit : (q : TypeProAr) -> (p : MLPolyCatObj) ->
  PolyNatTrans (typeProArLKanExt q $ PolyPrecompTypePro q p) p
typeProLKanExtCounit q p =
  (fst **
   \mpqpos, pd =>
    (snd mpqpos pd ** (\mpqcont => mpqcont pd, \qcov => (pd ** qcov))))

public export
typeDiLKanExtUnit : (q : TypeProAr) -> (p : TypeProAr) ->
  TypeDiNTar p (PolyPrecompTypePro q $ typeProArLKanExt q p)
typeDiLKanExtUnit q p =
  TypeProNTrestrict p
    (PolyPrecompTypePro q $ typeProArLKanExt q p)
    (typeProLKanExtUnit q p)

public export
typeDiLKanExtCounit : (q : TypeProAr) -> (p : MLPolyCatObj) ->
  PolyNatTrans (typeProArLKanExt q $ PolyPrecompTypePro q p) p
typeDiLKanExtCounit = typeProLKanExtCounit

----------------------------------------------------
----------------------------------------------------
---- Polynomial algebras as profunctor algebras ----
----------------------------------------------------
----------------------------------------------------

public export
typeProPolyAlg : MLPolyCatObj -> TypeProAr
typeProPolyAlg p = (Type ** (id, InterpPolyFunc p))

public export
typeProPolyAlgToProAlgCarrier : (p : MLPolyCatObj) -> (x, y : Type) ->
  InterpTypeProAr (typeProPolyAlg p) x y ->
  (InterpPolyFunc p x -> y)
typeProPolyAlgToProAlgCarrier p x y
  (arpos ** (arcont, arcov)) (pi ** dmx) =
    arcov (pi ** arcont . dmx)

public export
typeProPolyAlgFromProAlgCarrier : (p : MLPolyCatObj) -> (x, y : Type) ->
  (InterpPolyFunc p x -> y) ->
  InterpTypeProAr (typeProPolyAlg p) x y
typeProPolyAlgFromProAlgCarrier p x y dmxy = (x ** (id, dmxy))

------------------------------------------------------
------------------------------------------------------
---- Polynomial coalgebras as profunctor algebras ----
------------------------------------------------------
------------------------------------------------------

public export
typeProPolyCoalg : MLPolyCatObj -> TypeProAr
typeProPolyCoalg p = (Type ** (InterpPolyFunc p, id))

public export
typeProPolyCoalgToProCoalgCarrier : (p : MLPolyCatObj) -> (x, y : Type) ->
  InterpTypeProAr (typeProPolyCoalg p) x y ->
  (x -> InterpPolyFunc p y)
typeProPolyCoalgToProCoalgCarrier p x y
  (arpos ** (arcont, arcov)) elx =
    (fst (arcont elx) ** arcov . snd (arcont elx))

public export
typeProPolyCoalgFromProCoalgCarrier : (p : MLPolyCatObj) -> (x, y : Type) ->
  (x -> InterpPolyFunc p y) ->
  InterpTypeProAr (typeProPolyCoalg p) x y
typeProPolyCoalgFromProCoalgCarrier p x y dmxy = (y ** (dmxy, id))

-- Note that the profunctor `(x, y) -> x -> p y` is
-- precisely what we have earlier called `FunctorExp p`,
-- which we use as a utility function to define `RKanExt p`.

public export
typeProPolyCoalgToFunctorExp : (p : MLPolyCatObj) -> (x, y : Type) ->
  InterpTypeProAr (typeProPolyCoalg p) x y ->
  FunctorExp (InterpPolyFunc p) x y
typeProPolyCoalgToFunctorExp = typeProPolyCoalgToProCoalgCarrier

public export
typeProPolyCoalgFromFunctorExp : (p : MLPolyCatObj) -> (x, y : Type) ->
  FunctorExp (InterpPolyFunc p) x y ->
  InterpTypeProAr (typeProPolyCoalg p) x y
typeProPolyCoalgFromFunctorExp = typeProPolyCoalgFromProCoalgCarrier

------------------------------------------
------------------------------------------
---- Dialgebra-generating profunctors ----
------------------------------------------
------------------------------------------

public export
InterpPolyDialg : PolyFunc -> PolyFunc -> Type -> Type -> Type
InterpPolyDialg f g x y = InterpPolyFunc f x -> InterpPolyFunc g y

public export
PolyDialgPos : (f, g : PolyFunc) -> Type
PolyDialgPos f g =
  (xy : (Type, Type) ** InterpPolyFunc f (fst xy) -> InterpPolyFunc g (snd xy))

public export
PolyDialgContra : (f, g : PolyFunc) -> PolyDialgPos f g -> Type
PolyDialgContra f g = Builtin.fst . DPair.fst

public export
PolyDialgCovar : (f, g : PolyFunc) -> PolyDialgPos f g -> Type
PolyDialgCovar f g = Builtin.snd . DPair.fst

public export
PolyDialg : (f, g : PolyFunc) -> TypeProAr
PolyDialg f g =
  (PolyDialgPos f g ** (PolyDialgContra f g, PolyDialgCovar f g))

public export
PolyDialgToInterp : (f, g : PolyFunc) -> (x, y : Type) ->
  InterpTypeProAr (PolyDialg f g) x y ->
  (InterpPolyFunc f x -> InterpPolyFunc g y)
PolyDialgToInterp (fpos ** fdir) (gpos ** gdir) x y
  (((c, d) ** pm) ** (dmcont, dmcov)) (fi ** fdm) =
    let pmel = pm (fi ** dmcont . fdm) in
    (fst pmel ** dmcov . snd pmel)

public export
PolyDialgFromInterp : (f, g : PolyFunc) -> (x, y : Type) ->
  (InterpPolyFunc f x -> InterpPolyFunc g y) ->
  InterpTypeProAr (PolyDialg f g) x y
PolyDialgFromInterp (fpos ** fdir) (gpos ** gdir) x y dialg =
  (((x, y) ** dialg) ** (id, id))

------------------------------------------------------
------------------------------------------------------
---- Polynomial dialgebras as profunctor algebras ----
------------------------------------------------------
------------------------------------------------------

-- First, we compute dialgebras where the domain functor is a (covariant)
-- representable.

public export
typeProRepPolyDialg : Type -> MLPolyCatObj -> TypeProAr
typeProRepPolyDialg p q =
  ((ty : Type ** (p -> ty) -> pfPos q) **
   (\(ty ** m1) => ty,
    \(ty ** m1) => (idx : p -> ty ** pfDir {p=q} $ m1 idx)))

public export
typeProRepPolyDialgToDialgCarrier : (p : Type) -> (q : MLPolyCatObj) ->
  (x : Type) ->
  InterpTypeProAr (typeProRepPolyDialg p q) x x ->
  (CovarHomFunc p x -> InterpPolyFunc q x)
typeProRepPolyDialgToDialgCarrier p q x
  ((ty ** m1) ** (arcont, arcov)) idx =
    (m1 (arcont . idx) ** \qd => arcov (arcont . idx ** qd))

public export
typeProRepPolyDialgFromDialgCarrier : (p : Type) -> (q : MLPolyCatObj) ->
  (x : Type) ->
  (CovarHomFunc p x -> InterpPolyFunc q x) ->
  InterpTypeProAr (typeProRepPolyDialg p q) x x
typeProRepPolyDialgFromDialgCarrier p q x mqdm =
  ((x ** fst . mqdm) ** (id, \(m1 ** idx) => snd (mqdm m1) idx))

-- Then, we compute general dialgebras where the domain functor is any
-- (covariant) polynomial functor, given that such a functor is a coproduct
-- over its positions of (covariant) representables.

public export
typeProPolyDialg : MLPolyCatObj -> MLPolyCatObj -> TypeProAr
typeProPolyDialg p q =
  TypeParaSetProduct {a=(pfPos p)} (\i => typeProRepPolyDialg (pfDir {p} i) q)

public export
typeProPolyDialgToDialgCarrier : (p, q : MLPolyCatObj) ->
  (x : Type) ->
  InterpTypeProAr (typeProPolyDialg p q) x x ->
  (InterpPolyFunc p x -> InterpPolyFunc q x)
typeProPolyDialgToDialgCarrier p q x (aridx ** (arcont, arconv)) (pi ** pdm)
    with (aridx pi) proof eq
  typeProPolyDialgToDialgCarrier p q x (aridx ** (arcont, arconv)) (pi ** pdm)
    | (ty ** m1) =
      let
        arcomp =
          \pd : pfDir {p} pi =>
            replace eq {p=(\aridxpi => let (ty ** m1) = aridxpi in ty)} $
              arcont (pdm pd) pi
      in
      (m1 arcomp **
       \qd => arconv (pi ** rewrite eq in (arcomp ** qd)))

public export
typeProPolyDialgFromDialgCarrier : (p, q : MLPolyCatObj) ->
  (x : Type) ->
  (InterpPolyFunc p x -> InterpPolyFunc q x) ->
  InterpTypeProAr (typeProPolyDialg p q) x x
typeProPolyDialgFromDialgCarrier p q x mqdm =
  (\pi => (x ** \pdm => fst $ mqdm (pi ** pdm)) **
   (\ex, pi => ex,
    \(pi ** pdm ** qd) => snd (mqdm (pi ** pdm)) qd))

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Category of pi types, viewed as a subcategory of the category of monos ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
PiMonCatObj : Type
PiMonCatObj = (dom : Type ** cod : SliceObj dom ** Pi {a=dom} cod)

public export
PiMonCatMor : IntMorSig PiMonCatObj
PiMonCatMor (d ** c ** m) (d' ** c' ** m') =
  (l : d' -> d **
   r1 : (ed' : d') -> c' ed' -> d **
   comm1 : (ed' : d') -> r1 ed' (m' ed') = l ed' **
   r2 : (ed' : d') -> (ec' : c' ed') -> c (r1 ed' ec') **
   (ed' : d') -> m (l ed') = replace {p=c} (comm1 ed') (r2 ed' (m' ed')))

-------------------------------------------
-------------------------------------------
---- Polydifunctors as enriched arenas ----
-------------------------------------------
-------------------------------------------

-------------------------------
---- Polydifunctor objects ----
-------------------------------

{-
 - We might view a polydifunctor as a functor from
 - `Type` to `[op(Type), Type`]`.  As such, we could define it as a parametric
 - right adjoint from the category of presheaves (into `Type`) over the
 - terminal category -- which is equivalent to `Type` itself -- to the
 - category of presheaves over `Type`.  Examining the formula for PRA
 - functors between presheaf categories at
 - https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms ,
 - we set `I := 1` and `J := Type`, and thus determine that the PRA functor
 - is determined by the following data:
 -
 -  - An object `T1` in `[op(J), Type]`, i.e. a presheaf over `Type`,
 -    which, because we are trying to define a polynomial _difunctor_,
 -    we treat as a Dirichlet functor
 -  - A functor `el_op(T1) -> [op(I), Type]`; since `I` is the terminal
 -    category, this reduces to a functor in `[el_op(T1), Type]`.
 -    And because that is a presheaf on a category of elements, it is
 -    equivalently a slice over `T1`.
 -}
public export
record PDiData where
  constructor PDiD
  pdiT1 : MLDirichCatObj
  pdiF : MlDirichSlObj pdiT1

public export
PDiPos1 : PDiData -> Type
PDiPos1 = dfPos . pdiT1

public export
PDiPos2 : (pdid : PDiData) -> PDiPos1 pdid -> Type
PDiPos2 pdid = mdsOnPos (pdiF pdid)

public export
PDiDir1 : (pdid : PDiData) -> PDiPos1 pdid -> Type
PDiDir1 pdid = dfDir (pdiT1 pdid)

public export
PDiDir2 : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> PDiPos2 pdid i -> PDiDir1 pdid i -> Type
PDiDir2 pdid = mdsDir (pdiF pdid)

public export
PDiTot1 : (pdid : PDiData) -> Type
PDiTot1 = dfTot . pdiT1

public export
PDiTot2 : (pdid : PDiData) -> Type
PDiTot2 pdid = mlDirichSlObjTotTot {ar=(pdiT1 pdid)} $ pdiF pdid

-----------------------------------------------------------------
---- Polydifunctors as families of slice polynomial functors ----
-----------------------------------------------------------------

public export
PDiToSPFdepData : (pdid : PDiData) ->
  SPFdepData {b=(PDiPos1 pdid)} (PDiDir1 pdid) (const Unit)
PDiToSPFdepData pdid = MlDirichSlToSPFDD {ar=(pdiT1 pdid)} $ pdiF pdid

-- For each position of `T1`, we have a dependent polynomial functor from
-- the slice category of that position's direction to `Type` (which is
-- equivalent to the slice category of `Type` over `Unit`).
public export
PDiToSPFData : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> SPFData (PDiDir1 pdid i) Unit
PDiToSPFData pdid = SPFDataFamFromDep (PDiToSPFdepData pdid)

------------------------------------------
---- Interpretation of polydifunctors ----
------------------------------------------

public export
InterpPDiET0 : (pdid : PDiData) -> PDiPos1 pdid -> Type
InterpPDiET0 = PDiPos2

public export
InterpPDiET1dep : (pdid : PDiData) ->
  (d1 : Sigma {a=(PDiPos1 pdid)} (PDiDir1 pdid)) ->
  InterpPDiET0 pdid (fst d1) ->
  Type
InterpPDiET1dep pdid d1 = flip (PDiDir2 pdid (fst d1)) (snd d1)

public export
InterpPDiET1 : (pdid : PDiData) ->
  Sigma {a=(PDiPos1 pdid)} (PDiDir1 pdid) -> Type
InterpPDiET1 pdid d1 =
  Sigma {a=(InterpPDiET0 pdid $ fst d1)} $ InterpPDiET1dep pdid d1

-- `MLDirichCatObj` is a presheaf category over the walking arrow `0 -> 1`,
-- so in the notation of
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms,
-- we have for a given `z` a `T(z)(0)`, a `T(z)(1)`, and a morphism from
-- the latter to the former, which in turn we may express in dependent-type
-- form as making `T(z)(1)` dependent on `T(z)(0)`.  Note that
-- `T1(0)` is `pos(T1)` and `T1(1)` is `dir(T1)`.
public export
InterpPDiT0 : PDiData -> Type -> Type
InterpPDiT0 pdid z = (i1 : PDiPos1 pdid ** InterpPDiET0 pdid i1 -> z)

public export
0 InterpPDiT0isPoly : (pdid : PDiData) -> (z : Type) ->
  InterpPDiT0 pdid z = InterpPolyFunc (PDiPos1 pdid ** PDiPos2 pdid) z
InterpPDiT0isPoly pdid z = Refl

public export
InterpPDiT1dep : (pdid : PDiData) -> (z : Type) -> PDiPos1 pdid -> Type
InterpPDiT1dep pdid z i1 =
  (d1 : PDiDir1 pdid i1 ** InterpPDiET1 pdid (i1 ** d1) -> z)

public export
InterpPDiT1 : (pdid : PDiData) -> (z : Type) -> Type
InterpPDiT1 pdid z = Sigma {a=(PDiPos1 pdid)} $ InterpPDiT1dep pdid z

public export
InterpPDiEradjFact : (pdid : PDiData) -> Type -> MlDirichSlObj (pdiT1 pdid)
InterpPDiEradjFact pdid z =
  MDSobj
    (\i1 => Unit)
    (\i1, u_, d1 => (i2 : PDiPos2 pdid i1) -> PDiDir2 pdid i1 i2 d1 -> z)

public export
InterpPDiEradjFactMap : (pdid : PDiData) ->
  (z, z' : Type) -> (z -> z') ->
  MlDirichSlMor {ar=(pdiT1 pdid)}
    (InterpPDiEradjFact pdid z)
    (InterpPDiEradjFact pdid z')
InterpPDiEradjFactMap pdid z z' mz =
  MDSM (\i1, u_ => ()) (\i1, (), d1, dm, i2 => mz . dm i2)

public export
InterpPDiEsigma : (pdid : PDiData) ->
  MlDirichSlObj (pdiT1 pdid) -> MLDirichCatObj
InterpPDiEsigma pdid = mlDirichSlObjTot {ar=(pdiT1 pdid)}

public export
InterpPDiEsigmaMap : (pdid : PDiData) ->
  (sl, sl' : MlDirichSlObj (pdiT1 pdid)) ->
  MlDirichSlMor {ar=(pdiT1 pdid)} sl sl' ->
  MLDirichCatMor (InterpPDiEsigma pdid sl) (InterpPDiEsigma pdid sl')
InterpPDiEsigmaMap pdid sl sl' (MDSM onpos ondir) =
  (\(i1 ** eslp) => (i1 ** onpos i1 eslp) **
   \(i1 ** eslp), (i2 ** esld) => (i2 ** ondir i1 eslp i2 esld))

public export
InterpPDiE : (pdid : PDiData) ->
  (j : Type) -> (i1 : PDiPos1 pdid) -> (d1 : j -> PDiDir1 pdid i1) -> Type
InterpPDiE pdid j i1 d1 =
  (i2 : PDiPos2 pdid i1 ** Sigma {a=j} (PDiDir2 pdid i1 i2 . d1))

public export
InterpPolyDiCurried : (pdid : PDiData) -> Type -> MLDirichCatObj
InterpPolyDiCurried pdid z = InterpPDiEsigma pdid (InterpPDiEradjFact pdid z)

public export
InterpPolyDiCurriedMap : (pdid : PDiData) -> (x, y : Type) ->
  (x -> y) ->
  MLDirichCatMor (InterpPolyDiCurried pdid x) (InterpPolyDiCurried pdid y)
InterpPolyDiCurriedMap pdid x y m =
  InterpPDiEsigmaMap
    pdid
    (InterpPDiEradjFact pdid x)
    (InterpPDiEradjFact pdid y)
    (InterpPDiEradjFactMap pdid x y m)

public export
InterpPolyDi' : (pdid : PDiData) -> (j, z : Type) -> Type
InterpPolyDi' pdid j z = InterpDirichFunc (InterpPolyDiCurried pdid z) j

public export
InterpPolyDiLmap : (pdid : PDiData) -> (j, j', z : Type) ->
  (j' -> j) -> InterpPolyDi' pdid j z -> InterpPolyDi' pdid j' z
InterpPolyDiLmap pdid j j' z =
  InterpDFMap {a=j'} {b=j} (InterpPolyDiCurried pdid z)

public export
InterpPolyDiRmap : (pdid : PDiData) -> (j, z, z' : Type) ->
  (z -> z') -> InterpPolyDi' pdid j z -> InterpPolyDi' pdid j z'
InterpPolyDiRmap pdid j z z' mz ((i1 ** ()) ** dm) =
  ((i1 ** ()) ** \ej => (fst (dm ej) ** \i2 => mz . snd (dm ej) i2))

public export
InterpPolyDi'Map : (pdid : PDiData) -> (j, z, j', z' : Type) ->
  (j' -> j) -> (z -> z') -> InterpPolyDi' pdid j z -> InterpPolyDi' pdid j' z'
InterpPolyDi'Map pdid j z j' z' mj mz =
  InterpPolyDiLmap pdid j j' z' mj . InterpPolyDiRmap pdid j z z' mz

-- Here we show that `PDiData` is more complicated than necessary:
-- we can convert any `PDiData` to an `MlPolyProf` which is naturally
-- isomorphic to it.
public export
PDiToMLP : PDiData -> MlPolyProf
PDiToMLP (PDiD (tpos ** tdir) (MDSobj epos edir)) =
  (tpos ** tdir ** \ti, td => Sigma {a=(epos ti)} (flip (edir ti) td))

public export
InterpPDi'ToMLP : (pdid : PDiData) -> (x, y : Type) ->
  InterpPolyDi' pdid x y -> InterpMLP (PDiToMLP pdid) x y
InterpPDi'ToMLP (PDiD (tpos ** tdir) (MDSobj epos edir)) x y
  ((i ** ()) ** dm) =
    ((i ** ()) ** \ex => (fst (dm ex) ** DPair.uncurry $ snd $ dm ex))

public export
InterpPDi'FromMLP : (pdid : PDiData) -> (x, y : Type) ->
  InterpMLP (PDiToMLP pdid) x y -> InterpPolyDi' pdid x y
InterpPDi'FromMLP (PDiD (tpos ** tdir) (MDSobj epos edir)) x y
  ((i ** ()) ** dm) =
    ((i ** ()) ** \ex => (fst (dm ex) ** DPair.curry $ snd $ dm ex))

public export
InterpPDiEladjFact : (pdid : PDiData) -> MlDirichSlObj (pdiT1 pdid) -> Type
InterpPDiEladjFact (PDiD (tpos ** tdir) (MDSobj epos edir)) (MDSobj apos adir) =
  (ti : tpos ** ei : epos ti ** ai : apos ti **
   td : tdir ti ** (edir ti ei td, adir ti ai td))

public export
InterpPDiEladjFactMap : (pdid : PDiData) ->
  (sl, sl' : MlDirichSlObj (pdiT1 pdid)) ->
  MlDirichSlMor {ar=(pdiT1 pdid)} sl sl' ->
  InterpPDiEladjFact pdid sl -> InterpPDiEladjFact pdid sl'
InterpPDiEladjFactMap (PDiD (tpos ** tdir) (MDSobj epos edir))
  (MDSobj slpos sldir) (MDSobj slpos' sldir') (MDSM monpos mondir)
  (ti ** ei ** ai ** td ** (ed, ad)) =
    (ti ** ei ** monpos ti ai ** td ** (ed, mondir ti ai td ad))

public export
InterpPDiELadjunct : (pdid : PDiData) ->
  (a : MlDirichSlObj (pdiT1 pdid)) -> (b : Type) ->
  (InterpPDiEladjFact pdid a -> b) ->
  MlDirichSlMor {ar=(pdiT1 pdid)} a (InterpPDiEradjFact pdid b)
InterpPDiELadjunct (PDiD (tpos ** tdir) (MDSobj epos edir))
  (MDSobj apos adir) b m =
    MDSM
      (\ti, ai => ())
      (\ti, ai, td, ad, ei, ed => m (ti ** ei ** ai ** td ** (ed, ad)))

public export
InterpPDiERadjunct : (pdid : PDiData) ->
  (a : MlDirichSlObj (pdiT1 pdid)) -> (b : Type) ->
  MlDirichSlMor {ar=(pdiT1 pdid)} a (InterpPDiEradjFact pdid b) ->
  (InterpPDiEladjFact pdid a -> b)
InterpPDiERadjunct (PDiD (tpos ** tdir) (MDSobj epos edir))
  (MDSobj apos adir) b (MDSM monpos mondir) (ti ** ei ** ai ** td ** (ed, ad)) =
    mondir ti ai td ad ei ed

public export
InterpPDiELRadjunctId : (pdid : PDiData) ->
  (a : MlDirichSlObj (pdiT1 pdid)) -> (b : Type) ->
  (m : InterpPDiEladjFact pdid a -> b) ->
  ExtEq m (InterpPDiERadjunct pdid a b $ InterpPDiELadjunct pdid a b m)
InterpPDiELRadjunctId (PDiD (tpos ** tdir) (MDSobj epos edir))
  (MDSobj apos adir) b m (ti ** ei ** ai ** td ** (ed, ad)) =
    Refl

public export
InterpPDiERLadjunctId : FunExt -> (pdid : PDiData) ->
  (a : MlDirichSlObj (pdiT1 pdid)) -> (b : Type) ->
  (m : MlDirichSlMor {ar=(pdiT1 pdid)} a (InterpPDiEradjFact pdid b)) ->
  m = (InterpPDiELadjunct pdid a b $ InterpPDiERadjunct pdid a b m)
InterpPDiERLadjunctId fext (PDiD (tpos ** tdir) (MDSobj epos edir))
  (MDSobj apos adir) b (MDSM monpos mondir) =
    let
      onposeq : (monpos = (\ti, ai => ())) =
        funExt (\ti => funExt $ \ai => unitUnique (monpos ti ai) ())
    in
    rewrite onposeq in
    Refl

public export
InterpPolyDi : (pdid : PDiData) -> (j, z : Type) -> Type
InterpPolyDi pdid j z =
  (x : InterpDirichFunc (pdiT1 pdid) j **
   InterpPDiE pdid j (idfPos x) (idfDirMap x) -> z)

public export
InterpPolyDiForm : (pdid : PDiData) -> (j, z : Type) -> Type
InterpPolyDiForm pdid j z =
  (i1 : PDiPos1 pdid **
   d1 : j -> PDiDir1 pdid i1 **
   (i2 : PDiPos2 pdid i1) ->
    SliceMorphism {a=j} (PDiDir2 pdid i1 i2 . d1) (const z))

public export
InterpPolyDiToForm : (pdid : PDiData) -> (j, z : Type) ->
  InterpPolyDi pdid j z -> InterpPolyDiForm pdid j z
InterpPolyDiToForm pdid j z ((i1 ** d1) ** d2) =
  (i1 ** d1 ** \i2, ej, dd => d2 (i2 ** ej ** dd))

public export
InterpPolyDiFromForm : (pdid : PDiData) -> (j, z : Type) ->
  InterpPolyDiForm pdid j z -> InterpPolyDi pdid j z
InterpPolyDiFromForm pdid j z (i1 ** (d1 ** d2)) =
  ((i1 ** d1) ** \(i2 ** ej ** dd) => d2 i2 ej dd)

public export
InterpPolyDi'ToForm : (pdid : PDiData) -> (j, z : Type) ->
  InterpPolyDi' pdid j z -> InterpPolyDiForm pdid j z
InterpPolyDi'ToForm pdid j z ((i ** ()) ** dm) =
  (i ** DPair.fst . dm ** \i2, ej => snd (dm ej) i2)

public export
InterpPolyDi'FromForm : (pdid : PDiData) -> (j, z : Type) ->
  InterpPolyDiForm pdid j z -> InterpPolyDi' pdid j z
InterpPolyDi'FromForm pdid j z (i1 ** dm1 ** dm2) =
  ((i1 ** ()) ** \ej => (dm1 ej ** \i2 => dm2 i2 ej))

public export
InterpPolyDimap : (pdid : PDiData) -> TypeDimapSig (InterpPolyDi pdid)
InterpPolyDimap (PDiD pt1 (MDSobj possl dirsl)) s t a b mas mtb
  ((i1 ** dm1) ** dm2) =
    ((i1 ** dm1 . mas) ** \(i2 ** ea ** esl) => mtb $ dm2 (i2 ** mas ea ** esl))

public export
InterpPolyDiDepForm : (pdid : PDiData) -> (j : Type) -> (z : SliceObj j) -> Type
InterpPolyDiDepForm pdid j z =
  (i1 : PDiPos1 pdid **
   d1 : j -> PDiDir1 pdid i1 **
   (i2 : PDiPos2 pdid i1) -> SliceMorphism {a=j} (PDiDir2 pdid i1 i2 . d1) z)

-- This is the interpretation of the above family of `SPFData`s.
public export
InterpPDiSPF : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> SliceObj (PDiDir1 pdid i) -> Type
InterpPDiSPF pdid i sl = InterpSPFdepDataEl (PDiToSPFdepData pdid) i sl ()

-- The interpretation of the application to the first parameter of the
-- curried form of the dependent profunctor (AKA presheaf on the
-- twisted-arrow category) specified by a `PDiData`, returning a
-- slice polynomial functor over the selected direction.
public export
InterpPDi1SPF : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SPFData (idfDir {p=(pdiT1 pdid)} idf) Unit
InterpPDi1SPF pdid x idf = PDiToSPFData pdid (idfPos {p=(pdiT1 pdid)} idf)

public export
InterpPDi1 : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  idfDirSl {p=(pdiT1 pdid)} idf -> Type
InterpPDi1 pdid x idf = InterpPDiSPF pdid (idfPos {p=(pdiT1 pdid)} idf)

public export
InterpPDi2SPF : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SPFData x Unit
InterpPDi2SPF pdid x idf = spfdPrecompSigma (snd idf) (InterpPDi1SPF pdid x idf)

public export
InterpPDi2u : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceFunctor x Unit
InterpPDi2u pdid x idf = InterpSPFData $ InterpPDi2SPF pdid x idf

public export
InterpPDi2SPFmap : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceFMap (InterpPDi2u pdid x idf)
InterpPDi2SPFmap pdid x idf = InterpSPFDataMap $ InterpPDi2SPF pdid x idf

public export
InterpPDi2 : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceObj x -> Type
InterpPDi2 pdid x idf y = InterpPDi2u pdid x idf y ()

public export
InterpPDi2map : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  (y, y' : SliceObj x) ->
  SliceMorphism {a=x} y y' ->
  InterpPDi2 pdid x idf y -> InterpPDi2 pdid x idf y'
InterpPDi2map pdid x idf y y' m = InterpPDi2SPFmap pdid x idf y y' m ()

public export
InterpPDi : (pdid : PDiData) -> (x : Type) -> (y : SliceObj x) -> Type
InterpPDi pdid x =
  Sigma {a=(InterpDirichFunc (pdiT1 pdid) x)} . flip (InterpPDi2 pdid x)

public export
InterpPDiu : (pdid : PDiData) -> (x : Type) -> SliceFunctor x Unit
InterpPDiu pdid x y () = InterpPDi pdid x y

---------------------------------------------------
---- Morphism-map components of polydifunctors ----
---------------------------------------------------

public export
PDiLmapu : (pdid : PDiData) -> (x, x' : Type) -> (m : x' -> x) ->
  SliceNatTrans {x=x'} {y=Unit}
    (InterpPDiu pdid x . SliceFibSigmaF m)
    (InterpPDiu pdid x')
PDiLmapu pdid x x' m y' () =
  dpBimap (InterpDFMap (pdiT1 pdid) m)
  $ \(i1 ** i2), ((ep ** dm1) ** dm2) =>
    ((ep **
     \ex, d1 =>
        let sfs = dm2 (sfsFst $ dm1 ex d1) ((ex ** d1) ** Refl) in
        rewrite sym (sfsEq $ dm1 ex d1) in
        rewrite sym (sfsEq sfs) in
        SFS (sfsFst sfs) ()) **
     \ex', ((ex ** d1) ** xeq) =>
      rewrite sym xeq in
      sfsSnd $ dm2 (sfsFst $ dm1 ex d1) ((ex ** d1) ** Refl))

public export
PDiLmap : (pdid : PDiData) -> (x, x' : Type) -> (m : x' -> x) ->
  (y' : SliceObj x') ->
  InterpPDi pdid x (SliceFibSigmaF m y') -> InterpPDi pdid x' y'
PDiLmap pdid x x' m y' = PDiLmapu pdid x x' m y' ()

public export
PDiRmap : (pdid : PDiData) -> (x : Type) -> (y, y' : SliceObj x) ->
  SliceMorphism {a=x} y y' ->
  InterpPDi pdid x y -> InterpPDi pdid x y'
PDiRmap pdid x y y' m =
  dpMapSnd $ \i1 => dpMapSnd $ \p2, i2, d1, d2 => m d1 $ i2 d1 d2

public export
PDiDimap : (pdid : PDiData) ->
  (x, x' : Type) -> (y : SliceObj x) -> (y' : SliceObj x') ->
  (mx : x' -> x) -> (my : SliceMorphism {a=x} y (SliceFibSigmaF mx y')) ->
  InterpPDi pdid x y -> InterpPDi pdid x' y'
PDiDimap pdid x x' y y' mx my =
  PDiLmap pdid x x' mx y' . PDiRmap pdid x y (SliceFibSigmaF mx y') my

public export
PDiDimapDP : (pdid : PDiData) ->
  (x : Type) -> (y, x' : SliceObj x) ->
  (y' : SliceObj $ Sigma {a=x} x') ->
  (lm : (ex : x) -> y ex -> x' ex) ->
  (rm : (ex : x) -> (ey : y ex) -> y' (ex ** lm ex ey)) ->
  InterpPDi pdid x y -> InterpPDi pdid (Sigma {a=x} x') y'
PDiDimapDP pdid x y x' y' lm rm =
  PDiDimap pdid x (Sigma x') y y' DPair.fst $
    \ex, ey => SFS (ex ** lm ex ey) (rm ex ey)

-----------------------------------------------------------
---- Categories of diagonal elements of polydifunctors ----
-----------------------------------------------------------

-- Suppose we want to write a restricted version of `dimap` that is only
-- required to operate on diagonal elements.  Diagonal elements are those
-- where `x ~=~ y` and `x' ~=~ y'`, which may be represented either by
-- the `y`s being slices whose values are `const Unit` (the terminal objects
-- of the slice category over `x`, which is the `id` morphism on `x` in
-- categorial style), or, if we take a twisted-arrow viewpoint, the morphism
-- being the identity.
--
-- Note that the parameters `x`, `x'`, and `m` constitute a monomorphism
-- from `x` to `Sigma {a=x} x'`, where the proof that it is a monomorphism
-- is the exhibition of a left inverse, namely the projection from
-- `Sigma {a=x} x'` to `x`.
--
-- Note also that `Pi {a=x} x'` may equivalently be viewed as
-- `SliceMorphism {a=x} (SliceObjTerminal x) x'` -- that is, it is
-- a section, or global element (or "point"), of `x'`.  See
-- https://ncatlab.org/nlab/show/generalized+element#in_toposes.

public export
InterpPDiDiag : (pdid : PDiData) -> (x : Type) -> Type
InterpPDiDiag pdid x = InterpPDi pdid x (SliceObjTerminal x)

public export
PDiDiagMap : (pdid : PDiData) ->
  (x : Type) -> (x' : SliceObj x) -> Pi {a=x} x' ->
  InterpPDiDiag pdid x -> InterpPDiDiag pdid (Sigma {a=x} x')
PDiDiagMap pdid x x' m =
  PDiDimapDP pdid
    x (SliceObjTerminal x) x' (SliceObjTerminal $ Sigma {a=x} x')
    (\ex, u => m ex)
    (\_, _ => ())

public export
PDiDiagElemObj : PDiData -> Type
PDiDiagElemObj = Sigma {a=Type} . InterpPDiDiag

public export
data PDiDiagElemMor : (pdid : PDiData) -> IntMorSig (PDiDiagElemObj pdid) where
  PDEM' : {pdid : PDiData} -> {x : Type} -> {x' : SliceObj x} ->
    (el : InterpPDiDiag pdid x) -> (m : Pi {a=x} x') ->
    PDiDiagElemMor pdid
      (x ** el)
      (Sigma {a=x} x' ** PDiDiagMap pdid x x' m el)

---------------------------------------------------
---------------------------------------------------
---- Self-representation of Dirichlet functors ----
---------------------------------------------------
---------------------------------------------------

-- We can define a functor from `Type` to the category of Dirichlet
-- functors by defining a slice functor between the Dirichlet-functor
-- slice categories over `dfRepVoid` and `dfRepUnit`, because, as explained
-- in the comments to their definitions, those functors' categories of
-- elements are (equivalent to) `Type` and the category of Dirichlet functors
-- on `Type`, respectively.
public export
TypeDirichData : Type
TypeDirichData = PRAData MLDirichCat.dfRepVoid MLDirichCat.dfRepUnit

public export
InterpPRAdataOmapFromPDi : TypeDirichData ->
  MlDirichSlFunc MLDirichCat.dfRepVoid MLDirichCat.dfRepUnit
InterpPRAdataOmapFromPDi = InterpPRAdataOmap

public export
InterpPDiPRAdataOmap : (tdd : TypeDirichData) -> Type -> MLDirichCatObj
InterpPDiPRAdataOmap tdd =
  dfSlRepUnitToDirich . InterpPRAdataOmapFromPDi tdd . dfTypeToSlRepVoid

public export
InterpPDiDataOmap : (tdd : TypeDirichData) -> Type -> Type -> Type
InterpPDiDataOmap tdd x y = InterpDirichFunc (InterpPDiPRAdataOmap tdd y) x

public export
InterpPDiDataDimap : (tdd : TypeDirichData) ->
  IntEndoDimapSig TypeObj TypeMor (InterpPDiDataOmap tdd)
InterpPDiDataDimap (PRAD (MDSobj x slx) (MDSobj slsx _)) s t a b mas mtb
  ((ex ** mxt) ** msx) =
    ((ex ** \(() ** eslx) => mtb $ mxt (() ** eslx)) **
     \ea => (fst (msx $ mas ea) ** \_, _, v => void v))

----------------------------------------------
----------------------------------------------
---- Universal families as twisted arrows ----
----------------------------------------------
----------------------------------------------

public export
TwistArrArType : Type
TwistArrArType = TwistArrAr TypeCat

public export
TwistArrMorType : IntMorSig TwistArrArType
TwistArrMorType = TwistArrMor TypeCat

public export
twarDomType : TwistArrArType -> Type
twarDomType = twarDom {cat=TypeCat}

public export
twarCodType : (twar : TwistArrArType) -> SliceObj (twarDomType twar)
twarCodType = twarCod {cat=TypeCat}

public export
TwistPolyFuncType : Type
TwistPolyFuncType = TwistPolyFunc TypeCat

public export
tpfPosType : TwistPolyFuncType -> Type
tpfPosType = tpfPos {cat=TypeCat}

public export
tpfArType : (tpf : TwistPolyFuncType) -> tpfPosType tpf -> TwistArrArType
tpfArType = tpfAr {cat=TypeCat}

public export
tpfDomType : (tpf : TwistPolyFuncType) -> SliceObj (tpfPosType tpf)
tpfDomType = tpfDom {cat=TypeCat}

public export
tpfCodType : (tpf : TwistPolyFuncType) ->
  (i : tpfPosType tpf) -> SliceObj (tpfDomType tpf i)
tpfCodType = tpfCod {cat=TypeCat}

public export
TwistNTType : IntMorSig TwistPolyFuncType
TwistNTType = TwistNT TypeCat

public export
InterpTPFType : TwistPolyFuncType -> TwistArrArType -> Type
InterpTPFType = InterpTPF {cat=TypeCat}

public export
itpfOnCod : {tpf : TwistPolyFuncType} -> {twar : TwistArrArType} ->
  (itpf : InterpTPFType tpf twar) ->
  SliceMorphism {a=(twarDomType twar)}
    (BaseChangeF
      (itpfOnDom {cat=TypeCat} {tpf} {twar} itpf)
      (tpfCodType tpf $ itpfPos {cat=TypeCat} {tpf} {twar} itpf))
    (twarCodType twar)
itpfOnCod {tpf} {twar} itpf = DPair.snd (itpfDir {cat=TypeCat} itpf)

public export
twntOnCovar : {p, q : TwistPolyFuncType} ->
  (twnt : TwistNTType p q) ->
  (i : tpfPosType p) ->
    SliceMorphism {a=(tpfDomType p i)}
      (BaseChangeF
        (twntOnContra {cat=TypeCat} {p} {q} twnt i)
          (tpfCodType q $ twntOnPos {cat=TypeCat} {p} {q} twnt i))
      (tpfCodType p i)
twntOnCovar {p} {q} twnt i = DPair.snd (twntOnDir {cat=TypeCat} twnt i)

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Metalanguage twisted-arrow ("di") arenas and polynomial functors ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

public export
record MLDiArena where
  constructor MLDiAr
  mdaAr : MLArena
  mdaPred :
    Pi {a=(pfPos mdaAr)} (SliceObj . pfDir {p=mdaAr})

public export
mdaPos : MLDiArena -> Type
mdaPos = pfPos . mdaAr

public export
mdaStruct : (mda : MLDiArena) -> SliceObj (mdaPos mda)
mdaStruct mda = pfDir {p=(mdaAr mda)}

public export
MDAterm : (mda : MLDiArena) -> SliceObj (mdaPos mda)
MDAterm mda i = Sigma {a=(mdaStruct mda i)} (mdaPred mda i)

public export
record MLDiNatTrans (dom, cod : MLDiArena) where
  constructor MLDiNT
  mdntOnPos :
    mdaPos dom -> mdaPos cod
  mdntOnTerm :
    SliceMorphism {a=(mdaPos dom)} (MDAterm cod . mdntOnPos) (MDAterm dom)

public export
record InterpMDA (mda : MLDiArena) (struct : Type) (pred : SliceObj struct)
    where
  constructor IMDA
  imdaPos : mdaPos mda
  imdaAssign : MDAterm mda imdaPos -> Sigma {a=struct} pred

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Polydifunctors subject to polydinatural transformations ----
-----------------------------------------------------------------
-----------------------------------------------------------------

-------------------------------------
---- Arena form of polydifunctor ----
-------------------------------------

-- The positions of a polydifunctor map not to directions which are not
-- objects of `Type`, but morphisms (of `Type`).  In light of the
-- interpretation below, we can view these morphisms as the heteromorphisms
-- of a difunctor on `Type`, and also as the objects of the twisted-arrow
-- category on `Type`.  (Thus far they could also be objects of the arrow
-- category, but the interpretation below uses twisted-arrow morphisms,
-- not arrow morphisms.)
public export
record PolyDifunc where
  constructor PDF
  pdfPos : Type
  pdfCobase : SliceObj pdfPos
  pdfBase : SliceObj pdfPos
  pdfProj : SliceMorphism {a=pdfPos} pdfCobase pdfBase

-- The interpretation of a polydifunctor takes an object of the
-- twisted arrow category (of `Type`) and, as with polynomial
-- functors on other categories, comprises a choice of one of the
-- directions of the difunctor together with a (twisted-arrow)
-- morphism from that direction to the (twisted-arrow) object
-- that the functor is being applied to.
--
-- The difference between this and a general difunctor is the twisted-arrow
-- morphism:  without that, this would just determine a general profunctor
-- by its collage.  The twisted-arrow morphism constrains the profunctor
-- so that it only contains elements that can be "diagonalized" by the
-- morphism.
--
-- Note that when `y` is `x` and `m` is `id`, then this amounts to
-- a factorization of the identity on `x` through `pdfCobase` and
-- `pdfBase` via three morphisms.  If furthermore we choose a position
-- where `pdfCobase` is `pdfBase` and `pdfProj` is `id`, then this
-- interpretation becomes a factorization of the identity on `x` through
-- `pdfBase`, the type of directions at that position.  Such a factorization
-- is an epi (surjective) assignment of directions to `x`, together with
-- a mono (injective) assignment from `x` to the directions which effectively
-- constitutes a proof that `x` -- the type of variables -- contains no
-- "unused variables".
public export
record InterpPDF (pdf : PolyDifunc) (x, y : Type) (m : x -> y) where
  constructor IPDF
  ipdfPos : pdfPos pdf
  ipdfContraMor : x -> pdfCobase pdf ipdfPos
  ipdfCovarMor : pdfBase pdf ipdfPos -> y
  0 ipdfComm :
    FunExtEq (ipdfCovarMor . pdfProj pdf ipdfPos . ipdfContraMor) m

public export
InterpPDFdiag : (pdf : PolyDifunc) -> Type -> Type
InterpPDFdiag pdf x = InterpPDF pdf x x (Prelude.id {a=x})

public export
IPDFc : {pdf : PolyDifunc} -> {x, y : Type} ->
  (i : pdfPos pdf) ->
  (cnm : x -> pdfCobase pdf i) -> (cvm : pdfBase pdf i -> y) ->
  InterpPDF pdf x y (cvm . pdfProj pdf i . cnm)
IPDFc {pdf} {x} {y} i cnm cvm = IPDF i cnm cvm $ \fext => Refl

export
0 ipdfEqPos : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfPos ip ~=~ ipdfPos iq
ipdfEqPos {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqDom : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfContraMor ip ~=~ ipdfContraMor iq
ipdfEqDom {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqCod : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfCovarMor ip ~=~ ipdfCovarMor iq
ipdfEqCod {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqComm : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfComm ip ~=~ ipdfComm iq
ipdfEqComm {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfUip : FunExt ->
  {0 p : PolyDifunc} ->
  {0 x, y : Type} -> {0 m : x -> y} ->
  {ip, iq : InterpPDF p x y m} ->
  ipdfPos ip ~=~ ipdfPos iq ->
  ipdfContraMor ip ~=~ ipdfContraMor iq ->
  ipdfCovarMor ip ~=~ ipdfCovarMor iq ->
  ip = iq
ipdfUip fext {p=(PDF pp pd pc pm)} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF _ _ _ qcomm)}
    Refl Refl Refl =
      let eqComm : (pcomm = qcomm) = (funExt $ \fext' => uip) in
      case eqComm of Refl => Refl

public export
InterpPDFlmap : (pdf : PolyDifunc) ->
  (0 s, t, a : Type) -> (mst : s -> t) -> (mas : a -> s) ->
  InterpPDF pdf s t mst -> InterpPDF pdf a t (mst . mas)
InterpPDFlmap (PDF pos dom cod proj) s t a mst mas (IPDF i msi mit comm) =
  IPDF i (msi . mas) mit
    $ \fext => funExt $ \ea => fcong {x=(mas ea)} (comm fext)

public export
InterpPDFrmap : (pdf : PolyDifunc) ->
  (0 s, t, b : Type) -> (mst : s -> t) -> (mtb : t -> b) ->
  InterpPDF pdf s t mst -> InterpPDF pdf s b (mtb . mst)
InterpPDFrmap (PDF pos dom cod proj) s t b mst mtb (IPDF i msi mit comm) =
  IPDF i msi (mtb . mit)
    $ \fext => funExt $ \es => cong mtb $ fcong {x=es} (comm fext)

public export
InterpPDFdimap : (pdf : PolyDifunc) ->
  (0 s, t, a, b : Type) -> (mst : s -> t) -> (mas : a -> s) -> (mtb : t -> b) ->
  InterpPDF pdf s t mst -> InterpPDF pdf a b (mtb . mst . mas)
InterpPDFdimap pdf s t a b mst mas mtb =
  InterpPDFlmap pdf s b a (mtb . mst) mas . InterpPDFrmap pdf s t b mst mtb

--------------------------------------------------
---- Categories of elements of polydifunctors ----
--------------------------------------------------

public export
record PDFelemCatObj (pdf : PolyDifunc) where
  constructor PDFElObj
  pdfElPos : pdfPos pdf
  pdfElPred : SliceObj (pdfCobase pdf pdfElPos)
  pdfElStruct : Type
  pdfElAssign : pdfBase pdf pdfElPos -> pdfElStruct

public export
pdfElProj : {pdf : PolyDifunc} -> (el : PDFelemCatObj pdf) ->
  Sigma {a=(pdfCobase pdf $ pdfElPos el)} (pdfElPred el) -> pdfElStruct el
pdfElProj {pdf} el = pdfElAssign el . pdfProj pdf (pdfElPos el) . DPair.fst

public export
data PDFelemCatMor : {pdf : PolyDifunc} -> (dom, cod : PDFelemCatObj pdf) ->
    Type where
  PDFElMor : {0 pdf : PolyDifunc} ->
    {i : pdfPos pdf} ->
    {dpred, cpred : SliceObj $ pdfCobase pdf i} ->
    {dstruct, cstruct : Type} ->
    {dassign : pdfBase pdf i -> dstruct} ->
    (contra : SliceMorphism {a=(pdfCobase pdf i)} dpred cpred) ->
    (covar : dstruct -> cstruct) ->
    PDFelemCatMor {pdf}
      (PDFElObj i dpred dstruct dassign)
      (PDFElObj i cpred cstruct (covar . dassign))

----------------------------------
---- Monoid of polydifunctors ----
----------------------------------

-- Polydifunctors form a monoid -- a one-object category, with
-- the polydifunctors as morphisms -- whose identity is the hom-profunctor,
-- and whose composition resembles that of profunctors, but with the
-- additional morphism (since the objects are twisted arrows rather than
-- just objects of `op(Type) x Type`) to compose.

-- We represent the hom-profunctor, which is the identity of the monoid of
-- polydifunctors, with one position per morphism of `Type`.

public export
PdfHomProfId : PolyDifunc
PdfHomProfId =
  PDF
    (dom : Type ** cod : Type ** dom -> cod)
    (\i => fst i)
    (\i => fst $ snd i)
    (\i => snd $ snd i)

export
InterpToIdPDF : (x, y : Type) -> (m : x -> y) -> InterpPDF PdfHomProfId x y m
InterpToIdPDF x y m = IPDF (x ** y ** m) id id $ \fext => Refl

export
InterpFromIdPDF : (x, y : Type) -> (m : x -> y) ->
  InterpPDF PdfHomProfId x y m -> x -> y
InterpFromIdPDF x y mxy (IPDF (i ** j ** mij) mxi mjy comm) =
  -- There are two ways of getting from `x` to `y` -- `mxy` and
  -- `mjy . mij . mxi`. But `comm` shows them to be equal.
  -- We make that explicit here to make sure, and to document, that
  -- `mjy`, `mij`, and `mxi` are not "unused", but rather are an
  -- alternative to the `mxy` which we do use.
  let 0 eqm : (FunExtEq (mjy . mij . mxi) mxy) = comm in
  mxy

-- The arena form of polydifunctors is closed under composition.
public export
pdfComp : PolyDifunc -> PolyDifunc -> PolyDifunc
pdfComp (PDF qp qd qc qm) (PDF pp pd pc pm) =
  PDF
    (qi : qp ** pi : pp ** qc qi -> pd pi)
    (\(qi ** pi ** qcpd) => qd qi)
    (\(qi ** pi ** qcpd) => pc pi)
    (\(qi ** pi ** qcpd), qdi => pm pi $ qcpd $ qm qi qdi)

export
PDFcomposeInterpToInterpCompose :
  (q, p : PolyDifunc) -> (x, z : Type) -> (mxz : x -> z) ->
  TwArrCoprCompose (InterpPDF q) (InterpPDF p) x z mxz ->
  InterpPDF (pdfComp q p) x z mxz
PDFcomposeInterpToInterpCompose (PDF qp qd qc qm) (PDF pp pd pc pm) x z mxz
  (y **
   (mxy, myz) **
   (comm, IPDF qi mxqd mqcy qcomm, IPDF pi mypd mpcz pcomm)) =
    IPDF
      (qi ** pi ** mypd . mqcy)
      mxqd
      mpcz
      (\fext => funExt $ \ex =>
        trans
          (rewrite fcong {x=ex} (qcomm fext) in fcong {x=(mxy ex)} (pcomm fext))
          (fcong {x=ex} (comm fext)))

0 PDFinterpComposeToComposeInterp :
  (q, p : PolyDifunc) -> (x, z : Type) -> (mxz : x -> z) ->
  InterpPDF (pdfComp q p) x z mxz ->
  TwArrCoprCompose (InterpPDF q) (InterpPDF p) x z mxz
PDFinterpComposeToComposeInterp (PDF qp qd qc qm) (PDF pp pd pc pm) x z mxz
  (IPDF (qi ** pi ** mqcpd) mxqd mpcz comm) =
    (pd pi **
     (mqcpd . qm qi . mxqd, mpcz . pm pi) **
     (comm,
      IPDF qi mxqd mqcpd (\fext => Refl),
      IPDF pi Prelude.id mpcz (\fext => Refl)))

public export
PDiMonoidCat : IntCatSig
PDiMonoidCat =
  ICat
    Unit
  $ MICS
    (\_, _ => PolyDifunc)
  $ ICS
    (\_ => PdfHomProfId)
    (\_, _, _ => pdfComp)

-----------------------------------------------------------------------
---- Polydinatural transformations between metalanguage difunctors ----
-----------------------------------------------------------------------

-- A polydinatural transformation comprises an on-positions function from
-- the positions (collage objects) of the domain polydifunctor to those of
-- the codomain polydifunctor, and for each position, a twisted-arrow
-- morphism between the collage objects from the one at the output of the
-- on-positions function in the codomain polydifunctor to the one at the
-- input of the on-positions in the domain polydifunctor.
public export
record PolyDiNT (p, q : PolyDifunc) where
  constructor PDNT
  pdntOnPos : pdfPos p -> pdfPos q
  -- Per position, this is a twisted-arrow morphism from `q` to `p`.
  pdntOnBase :
    (i : pdfPos p) -> pdfBase q (pdntOnPos i) -> pdfBase p i
  pdntOnCobase :
    (i : pdfPos p) -> pdfCobase p i -> pdfCobase q (pdntOnPos i)
  pdntComm :
    (i : pdfPos p) ->
      FunExtEq
        (pdntOnBase i . pdfProj q (pdntOnPos i) . pdntOnCobase i)
        (pdfProj p i)

export
InterpPDNTnat : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x, y : Type) -> (m : x -> y) -> InterpPDF p x y m -> InterpPDF q x y m
InterpPDNTnat {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc ntcomm) x y m (IPDF pi mxpd mpcx pcomm) =
    IPDF
      (oni pi)
      (onc pi . mxpd)
      (mpcx . onb pi)
      (\fext => funExt $ \ex =>
        rewrite fcong {x=(mxpd ex)} $ ntcomm pi fext in
        fcong {x=ex} $ pcomm fext)

export
InterpPDNT : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x : Type) -> InterpPDFdiag p x -> InterpPDFdiag q x
InterpPDNT {p} {q} pdnt x = InterpPDNTnat {p} {q} pdnt x x Prelude.id

export
0 InterpPDFisPara : FunExt ->
  {0 p, q : PolyDifunc} -> (pdnt : PolyDiNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpPDFdiag p i0) -> (d1 : InterpPDFdiag p i1) ->
  (InterpPDFlmap p i1 i1 i0 Prelude.id i2 d1 ~=~
   InterpPDFrmap p i0 i0 i1 Prelude.id i2 d0) ->
  (InterpPDFlmap q i1 i1 i0 Prelude.id i2 (InterpPDNT {p} {q} pdnt i1 d1) ~=~
   InterpPDFrmap q i0 i0 i1 Prelude.id i2 (InterpPDNT {p} {q} pdnt i0 d0))
InterpPDFisPara fext {p=p@(PDF pp pd pc pm)} {q=q@(PDF qp qd qc qm)}
  pdnt@(PDNT onidx onb onc ntcomm) i0 i1 i2
  ip@(IPDF pi0 mi0pd mpci0 pcomm) iq@(IPDF pi1 mi1pd mpci1 qcomm) cond =
    case ipdfEqPos cond of
      Refl => case ipdfEqDom cond of
        Refl => case ipdfEqCod cond of
          Refl =>
            ipdfUip fext Refl Refl Refl

--------------------------------------------------------------------------------
---- Category of metalanguage difunctors with paranatural transformations ----
--------------------------------------------------------------------------------

export
pdNTid : (pdf : PolyDifunc) -> PolyDiNT pdf pdf
pdNTid pdf =
  PDNT id (\_ => id) (\i => id) $ \i, fext => Refl

export
pdNTvcomp : {0 r, q, p : PolyDifunc} -> PolyDiNT q r -> PolyDiNT p q ->
  PolyDiNT p r
pdNTvcomp {r=(PDF rp rd rc rm)} {q=(PDF qp qd qc qm)} {p=(PDF pp pd pc pm)}
  (PDNT oniqr onbqr oncqr qrcomm) (PDNT onipq onbpq oncpq pqcomm) =
    PDNT
      (oniqr . onipq)
      (\pi => onbpq pi . onbqr (onipq pi))
      (\pi => (oncqr $ onipq pi) . oncpq pi)
      $ \pi, fext => funExt $ \pd =>
        trans
          (rewrite (fcong {x=(oncpq pi pd)} $ qrcomm (onipq pi) fext) in Refl)
          (fcong {x=pd} $ pqcomm pi fext)

public export
PolyDiMICS : MorIdCompSig PolyDifunc
PolyDiMICS =
  MICS
    PolyDiNT
  $ ICS
    pdNTid
    (\p, q, r => pdNTvcomp {r} {q} {p})

public export
PolyDiCat : IntCatSig
PolyDiCat = ICat PolyDifunc PolyDiMICS

--------------------------------------------------------------------
---- Two-categorical structure of polydinatural transformations ----
--------------------------------------------------------------------

-- The polydinatural transformations of difunctors form a two-category:
-- polydinatural transformations have horizontal composition and whiskering.

export
pdNTwhiskerL : {0 q, r : PolyDifunc} -> PolyDiNT q r -> (p : PolyDifunc) ->
  PolyDiNT (pdfComp q p) (pdfComp r p)
pdNTwhiskerL {q=(PDF qp qd qc qm)} {r=(PDF rp rd rc rm)}
  (PDNT oni onb onc ntcomm) (PDF pp pd pc pm) =
    PDNT
      (\(qi ** pi ** qcpd) => (oni qi ** pi ** qcpd . onb qi))
      (\(qi ** pi ** qcpd) => id)
      (\(qi ** pi ** qcpd) => onc qi)
      (\(qi ** pi ** qcpd), fext =>
        funExt $ \qd => rewrite fcong {x=qd} (ntcomm qi fext) in Refl)

export
pdNTwhiskerR : {0 p, q : PolyDifunc} -> PolyDiNT p q -> (r : PolyDifunc) ->
  PolyDiNT (pdfComp r p) (pdfComp r q)
pdNTwhiskerR {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc ntcomm) (PDF rp rd rc rm) =
    PDNT
      (\(ri ** pi ** rcpd) => (ri ** oni pi ** onc pi . rcpd))
      (\(ri ** pi ** rcpd) => onb pi)
      (\(ri ** pi ** rcpd) => id)
      (\(ri ** pi ** rcpd), fext =>
        funExt $ \rd => fcong $ ntcomm pi fext)

export
pdNThcomp : {0 p, q' : PolyDifunc} -> {p', q : PolyDifunc} ->
  PolyDiNT q q' -> PolyDiNT p p' -> PolyDiNT (pdfComp q p) (pdfComp q' p')
pdNThcomp {p} {p'} {q} {q'} beta alpha =
  pdNTvcomp (pdNTwhiskerL {q} {r=q'} beta p') (pdNTwhiskerR {p} {q=p'} alpha q)

public export
PolyDiGHS : GlobalHomStruct PDiMonoidCat
PolyDiGHS () () = PolyDiMICS

public export
PolyDiLWS : GlobalLeftWhiskerHomStruct PDiMonoidCat PolyDiGHS
PolyDiLWS () () () f g g' alpha = pdNTwhiskerL {q=g} {r=g'} alpha f

public export
PolyDiRWS : GlobalRightWhiskerHomStruct PDiMonoidCat PolyDiGHS
PolyDiRWS () () () g f f' alpha = pdNTwhiskerR {p=f} {q=f'} alpha g

public export
PolyDi2CatS : Int2CatStruct PDiMonoidCat
PolyDi2CatS =
  I2CS
    PolyDiGHS
    PolyDiLWS
    PolyDiRWS

public export
PolyDi2Cat : Int2CatSig
PolyDi2Cat = I2Cat PDiMonoidCat PolyDi2CatS

---------------------------------------
---- Polynomial/Dirichlet functors ----
---------------------------------------

-- Twisted polynomials subsume both polynomial and Dirichlet functors.

export
PdfFromPoly : PolyFunc -> PolyDifunc
PdfFromPoly p = PDF (pfPos p) (\_ => Void) (pfDir {p}) (\i, v => void v)

export
PdfFromPolyNT : (p, q : PolyFunc) ->
  PolyNatTrans p q -> PolyDiNT (PdfFromPoly p) (PdfFromPoly q)
PdfFromPolyNT (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  PDNT
    onpos
    ondir
    (\_ => Prelude.id {a=Void})
    (\pi, fext => funExt $ \v => void v)

export
PdfToPolyNT : (p, q : PolyFunc) ->
  PolyDiNT (PdfFromPoly p) (PdfFromPoly q) -> PolyNatTrans p q
PdfToPolyNT (ppos ** pdir) (qpos ** qdir) (PDNT onpos onbase oncobase comm) =
  (onpos ** onbase)

export
InterpPdfFromPoly : (p : PolyFunc) -> (y : Type) ->
  InterpPolyFunc p y -> InterpPDF (PdfFromPoly p) Void y (\v => void v)
InterpPdfFromPoly (pos ** dir) y (i ** dm) =
  IPDF i (\v => void v) dm $ \fext => funExt $ \v => void v

export
InterpPdfToPoly : (p : PolyFunc) -> (y : Type) ->
  InterpPDF (PdfFromPoly p) Void y (\v => void v) -> InterpPolyFunc p y
InterpPdfToPoly (pos ** dir) y (IPDF i mx my comm) = (i ** my)

export
PdfFromDirich : PolyFunc -> PolyDifunc
PdfFromDirich p = PDF (pfPos p) (pfDir {p}) (\_ => Unit) (\_, _ => ())

export
PdfFromDirichNT : (p, q : MLDirichCatObj) ->
  DirichNatTrans p q -> PolyDiNT (PdfFromDirich p) (PdfFromDirich q)
PdfFromDirichNT (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  PDNT
    onpos
    (\_ => Prelude.id {a=Unit})
    ondir
    (\_, _ => Refl)

export
PdfToDirichNT : (p, q : MLDirichCatObj) ->
  PolyDiNT (PdfFromDirich p) (PdfFromDirich q) -> DirichNatTrans p q
PdfToDirichNT (ppos ** pdir) (qpos ** qdir) (PDNT onpos onbase oncobase comm) =
  (onpos ** oncobase)

export
InterpPdfFromDirich : (p : PolyFunc) -> (x : Type) ->
  InterpDirichFunc p x -> InterpPDF (PdfFromDirich p) x Unit (\_ => ())
InterpPdfFromDirich (pos ** dir) x (i ** dm) =
  IPDF i dm (\_ => ()) $ \fext => funExt $ \_ => Refl

export
InterpPdfToDirich : (p : PolyFunc) -> (x : Type) ->
  InterpPDF (PdfFromDirich p) x Unit (\_ => ()) -> InterpDirichFunc p x
InterpPdfToDirich (pos ** dir) x (IPDF i mx my comm) = (i ** mx)

----------------------------------------------
----------------------------------------------
---- Embedding of PolyDifunc into PolyFunc ---
----------------------------------------------
----------------------------------------------

public export
PDiToPoly : PolyDifunc -> PolyFunc
PDiToPoly (PDF pos cobase base proj) =
  (Sigma {a=pos} cobase ** base . DPair.fst)

public export
PDiToPolyNT : (p, q : PolyDifunc) ->
  PolyDiNT p q -> PolyNatTrans (PDiToPoly p) (PDiToPoly q)
PDiToPolyNT (PDF ppos pcobase pbase pproj) (PDF qpos qcobase qbase qproj)
  (PDNT onpos onbase oncobase ntcomm) =
    (dpBimap onpos oncobase ** \(pi ** pcb), qb => onbase pi qb)

---------------------------------------------
---------------------------------------------
---- Universal morphisms in `PolyDifunc` ----
---------------------------------------------
---------------------------------------------

------------------------
---- Initial object ----
------------------------

public export
PDIinitial : PolyDifunc
PDIinitial = PDF Void (\v => void v) (\v => void v) (\v => void v)

public export
pdiFromInitial : (p : PolyDifunc) -> PolyDiNT PDIinitial p
pdiFromInitial p =
  PDNT
    (\v => void v)
    (\v => void v)
    (\v => void v)
    (\v => void v)

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Polynomial presheaves (Dirichlet functors) on `TwArr(op(Type))` ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-----------------------------------------------
---- General op-twisted Dirichlet functors ----
-----------------------------------------------

public export
TwArrOpDirich : Type
TwArrOpDirich =
  (pos : Type **
   contra : pos -> Type **
   covar : pos -> Type **
   (i : pos) -> covar i -> contra i)

public export
InterpTwArrOpDirich : TwArrOpDirich -> TwArrPreshfOpSig
InterpTwArrOpDirich (pos ** contra ** covar ** proj) x y myx =
  (i : pos **
   dmcont : x -> contra i **
   dmcov : covar i -> y **
   ExtEq {a=(covar i)} {b=(contra i)} (proj i) (dmcont . myx . dmcov))

public export
InterpTwArrOpDirichDimap :
  (p : TwArrOpDirich) -> TwArrPreshfOpDimapSig (InterpTwArrOpDirich p)
InterpTwArrOpDirichDimap (pos ** contra ** covar ** proj) s t a b mba mas mtb
  (i ** dmcont ** dmcov ** comm) =
    (i ** dmcont . mas ** mtb . dmcov ** comm)

public export
TwArrOpDirichRep : (x, y : Type) -> (y -> x) -> TwArrOpDirich
TwArrOpDirichRep x y myx = (Unit ** \_ => x ** \_ => y ** \_ => myx)

public export
TwArrOpDirichNTfromRepFromYoneda :
  (x, y : Type) -> (y -> x) -> TwArrOpDirich -> Type
TwArrOpDirichNTfromRepFromYoneda x y myx p = InterpTwArrOpDirich p x y myx

public export
InterpTwArrOpDirichNTfromRep :
  (x, y : Type) -> (myx : y -> x) -> (p : TwArrOpDirich) ->
  TwArrOpDirichNTfromRepFromYoneda x y myx p ->
  (a, b : Type) -> (mba : b -> a) ->
  InterpTwArrOpDirich (TwArrOpDirichRep x y myx) a b mba ->
  InterpTwArrOpDirich p a b mba
InterpTwArrOpDirichNTfromRep x y myx (pos ** contra ** covar ** proj)
  (i ** dmcont ** dmcov ** pcomm) a b mba (() ** max ** myb ** mcomm) =
    (i ** dmcont . max ** myb . dmcov **
     \el => trans (pcomm el) (cong dmcont $ mcomm $ dmcov el))

public export
TwArrOpDirichNTfromYoneda : IntMorSig TwArrOpDirich
TwArrOpDirichNTfromYoneda (ppos ** pcontra ** pcovar ** pproj) q =
  (pi : ppos) ->
  TwArrOpDirichNTfromRepFromYoneda (pcontra pi) (pcovar pi) (pproj pi) q

public export
TwArrOpDirichNT : IntMorSig TwArrOpDirich
TwArrOpDirichNT
  (ppos ** pcontra ** pcovar ** pproj)
  (qpos ** qcontra ** qcovar ** qproj) =
    (onpos : ppos -> qpos **
     oncont : (pi : ppos) -> pcontra pi -> qcontra (onpos pi) **
     oncov : (pi : ppos) -> qcovar (onpos pi) -> pcovar pi **
     (pi : ppos) ->
      ExtEq {a=(qcovar $ onpos pi)} {b=(qcontra $ onpos pi)}
        (qproj (onpos pi))
        (oncont pi . pproj pi . oncov pi))

public export
TwArrOpDirichNTtoYonedaVersion :
  (p, q : TwArrOpDirich) ->
  TwArrOpDirichNT p q ->
  TwArrOpDirichNTfromYoneda p q
TwArrOpDirichNTtoYonedaVersion
  (ppos ** pcontra ** pcovar ** pproj)
  (qpos ** qcontra ** qcovar ** qproj)
  (onpos ** oncont ** oncov ** alpha) =
    \pi => (onpos pi ** oncont pi ** oncov pi ** alpha pi)

public export
TwArrOpDirichNTfromYonedaVersion :
  (p, q : TwArrOpDirich) ->
  TwArrOpDirichNTfromYoneda p q ->
  TwArrOpDirichNT p q
TwArrOpDirichNTfromYonedaVersion
  (ppos ** pcontra ** pcovar ** pproj)
  (qpos ** qcontra ** qcovar ** qproj)
  alpha =
    (\pi => fst (alpha pi) **
     \pi => fst (snd $ alpha pi) **
     \pi => fst (snd $ snd $ alpha pi) **
     \pi => snd (snd $ snd $ alpha pi))
