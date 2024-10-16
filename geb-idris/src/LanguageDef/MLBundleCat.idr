module LanguageDef.MLBundleCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.InternalCat
import public LanguageDef.IntEFamCat
import public LanguageDef.IntTwistedArrowCat
import public LanguageDef.IntParamCat
import public LanguageDef.IntArena
import public LanguageDef.PolyCat
import public LanguageDef.MLDirichCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

------------------------------------------------------------------
------------------------------------------------------------------
---- Objects of category of covariant fiber bundles of `Type` ----
------------------------------------------------------------------
------------------------------------------------------------------

---------------------
---- Arena-style ----
---------------------

public export
ABundleObj : Type
ABundleObj = IntEFamObj Type

public export
abBase : ABundleObj -> Type
abBase = ifeoIdx {c=Type}

public export
abCobase : (ab : ABundleObj) -> SliceObj (abBase ab)
abCobase = ifeoObj {c=Type}

public export
ABSliceBase : ABundleObj -> Type
ABSliceBase = SliceObj . abBase

public export
abTot : ABundleObj -> Type
abTot cat = Sigma {a=(abBase cat)} (abCobase cat)

public export
ABinj : (cat : ABundleObj) -> ABSliceBase cat -> Type
ABinj cat = SliceMorphism {a=(abBase cat)} (abCobase cat)

-- `ABundleObj` is just a metalanguage arena with names.

export
BcoAtoArena : {c : Type} -> ABundleObj -> MLArena
BcoAtoArena {c} ab = (abBase ab ** abCobase ab)

export
BcoAfromArena : {c : Type} -> MLArena -> ABundleObj
BcoAfromArena {c} ar = (fst ar ** snd ar)

--------------------------
---- Categorial-style ----
--------------------------

-- A bundle is an arrow whose morphisms comprise a (covariant) morphism between
-- codomains together with (covariant) morphisms on fibrations of the domains by
-- the codomain morphisms.
--
-- (This could be implemented in terms of `IntBundleObj`.)
public export
record CBundleObj where
  constructor CBO
  cbBase : Type
  cbTot : Type
  cbProj : cbTot -> cbBase

public export
CBOtoIBO : CBundleObj -> IntBundle {c=Type} HomProf
CBOtoIBO cb = IBundle (cbTot cb) (cbBase cb) (cbProj cb)

public export
CBOfromIBO : IntBundle {c=Type} HomProf -> CBundleObj
CBOfromIBO ib = CBO (ibCod ib) (ibDom ib) (ibMor ib)

public export
CBOsl : (cb : CBundleObj) -> CSliceObj (cbBase cb)
CBOsl cb = (cbTot cb ** cbProj cb)

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

public export
BcoCtoA : CBundleObj -> ABundleObj
BcoCtoA cb =
  (cbBase cb **
    \ea => PreImage {a=(cbTot cb)} {b=(cbBase cb)} (cbProj cb) ea)

public export
BcoAtoC : ABundleObj -> CBundleObj
BcoAtoC ab =
  CBO (abBase ab) (Sigma {a=(abBase ab)} $ abCobase ab) DPair.fst

---------------------------------------------
---- Equivalence with Dirichlet functors ----
---------------------------------------------

public export
BcoAtoDirich : ABundleObj -> PolyFunc
BcoAtoDirich = id

public export
BcoCtoDirich : CBundleObj -> PolyFunc
BcoCtoDirich = BcoAtoDirich . BcoCtoA

public export
BcoDirichToA : PolyFunc -> ABundleObj
BcoDirichToA = id

public export
BcoDirichToC : PolyFunc -> CBundleObj
BcoDirichToC = BcoAtoC . BcoDirichToA

--------------------------------------------------------------------
--------------------------------------------------------------------
---- Morphisms of category of covariant fiber bundles of `Type` ----
--------------------------------------------------------------------
--------------------------------------------------------------------

---------------------
---- Arena-style ----
---------------------

-- These morphisms make the `ABundleMor` category equivalent to the
-- category of Dirichlet functors, which, as noted at
-- https://ncatlab.org/nlab/show/free+coproduct+completion#ViaIndexedSetsOfObjects ,
-- may also be viewed as the free coproduct completion (here of `Type`).
-- Another equivalent formation is that of "existential families"
-- (`IntEFamCat`).
public export
0 ABundleMor : (dom, cod : ABundleObj) -> Type
ABundleMor = IntEFamMor {c=Type} HomProf

public export
abmBase : {dom, cod : ABundleObj} ->
  ABundleMor dom cod -> abBase dom -> abBase cod
abmBase = ifemOnIdx {c=Type} {mor=HomProf}

public export
abmCobase : {dom, cod : ABundleObj} ->
  (ab : ABundleMor dom cod) ->
  ABinj dom (BaseChangeF (abmBase {dom} {cod} ab) $ abCobase cod)
abmCobase = ifemOnObj {c=Type} {mor=HomProf}

--------------------------
---- Categorial-style ----
--------------------------

public export
record CBundleMor (dom, cod : CBundleObj) where
  constructor CBM
  cbmBase : cbBase dom -> cbBase cod
  cbmTot :
    CSliceMorphism {c=(cbBase dom)}
      (CBOsl dom)
      (CSBaseChange cbmBase (CBOsl cod))

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

export
BcmCtoA : {0 dom, cod : CBundleObj} ->
  CBundleMor dom cod -> ABundleMor (BcoCtoA dom) (BcoCtoA cod)
BcmCtoA {dom} {cod} (CBM mbase (Element0 mtot mcomm)) =
  (mbase **
   \edb, (Element0 edt deq) =>
    Element0
      (snd $ fst0 $ mtot edt)
       $ trans (sym $ snd0 $ mtot edt) $ rewrite sym (mcomm edt) in
       rewrite deq in Refl)

export
BcmCfromA : {dom, cod : CBundleObj} ->
  ABundleMor (BcoCtoA dom) (BcoCtoA cod) -> CBundleMor dom cod
BcmCfromA {dom} {cod} (mbase ** mcobase) =
  CBM
    mbase $
    Element0
      (\edt =>
        let
          mcb = mcobase (cbProj dom edt) $ Element0 edt Refl
        in
        Element0 (cbProj dom edt, fst0 mcb) $ sym $ snd0 mcb)
      $ \_ => Refl

export
BcmAtoC : {0 dom, cod : ABundleObj} ->
  ABundleMor dom cod -> CBundleMor (BcoAtoC dom) (BcoAtoC cod)
BcmAtoC {dom} {cod} (mbase ** mcobase) =
  CBM
    mbase
    $ Element0
      (\(edb ** edcb) => Element0 (edb, (mbase edb ** mcobase edb edcb)) Refl)
      (\(edb ** edcb) => Refl)

export
BcmAfromC : {0 dom, cod : ABundleObj} ->
  CBundleMor (BcoAtoC dom) (BcoAtoC cod) -> ABundleMor dom cod
BcmAfromC {dom} {cod} (CBM mbase (Element0 mtot mcomm)) =
  (mbase **
   \edb, edcb =>
    rewrite
      trans
        (cong mbase $ mcomm (edb ** edcb))
        (snd0 (mtot (edb ** edcb)))
    in
    snd $ snd $ fst0 $ mtot (edb ** edcb))

---------------------------------------------
---- Equivalence with Dirichlet functors ----
---------------------------------------------

export
BcmAtoDirich : {0 dom, cod : ABundleObj} ->
  ABundleMor dom cod -> DirichNatTrans (BcoAtoDirich dom) (BcoAtoDirich cod)
BcmAtoDirich {dom=(dbase ** dcobase)} {cod=(cbase ** ccobase)}
  (mbase ** mcobase) =
    (mbase ** mcobase)

export
BcmAfromDirich : {0 dom, cod : ABundleObj} ->
  DirichNatTrans (BcoAtoDirich dom) (BcoAtoDirich cod) -> ABundleMor dom cod
BcmAfromDirich {dom=(dbase ** dcobase)} {cod=(cbase ** ccobase)}
  (mbase ** mcobase) =
    (mbase ** mcobase)

export
BcmDirichToA : {0 dom, cod : PolyFunc} ->
  DirichNatTrans dom cod -> ABundleMor (BcoDirichToA dom) (BcoDirichToA cod)
BcmDirichToA {dom=(dpos ** ddir)} {cod=(cpos ** cdir)} (onpos ** ondir) =
  (onpos ** ondir)

export
BcmDirichFromA : {0 dom, cod : PolyFunc} ->
  ABundleMor (BcoDirichToA dom) (BcoDirichToA cod) ->
  DirichNatTrans dom cod
BcmDirichFromA {dom=(dpos ** ddir)} {cod=(cpos ** cdir)} (base ** cobase) =
  (base ** cobase)

export
BcmCtoDirich : {0 dom, cod : CBundleObj} ->
  CBundleMor dom cod -> DirichNatTrans (BcoCtoDirich dom) (BcoCtoDirich cod)
BcmCtoDirich {dom} {cod} =
  BcmAtoDirich {dom=(BcoCtoDirich dom)} {cod=(BcoCtoDirich cod)}
  . BcmCtoA {dom} {cod}

export
BcmCfromDirich : {dom, cod : CBundleObj} ->
  DirichNatTrans (BcoCtoDirich dom) (BcoCtoDirich cod) -> CBundleMor dom cod
BcmCfromDirich {dom} {cod} =
  BcmCfromA . BcmAfromDirich {dom=(BcoCtoDirich dom)} {cod=(BcoCtoDirich cod)}

export
BcmDirichToC : {0 dom, cod : PolyFunc} ->
  DirichNatTrans dom cod -> CBundleMor (BcoDirichToC dom) (BcoDirichToC cod)
BcmDirichToC = BcmAtoC . BcmDirichToA

export
BcmDirichFromC : {0 dom, cod : PolyFunc} ->
  CBundleMor (BcoDirichToC dom) (BcoDirichToC cod) -> DirichNatTrans dom cod
BcmDirichFromC = BcmDirichFromA . BcmAfromC

------------------------------------------
------------------------------------------
---- Categorical structure on bundles ----
------------------------------------------
------------------------------------------

----------------------------------
---- Identity and composition ----
----------------------------------

export
0 abId : (abo : ABundleObj) -> ABundleMor abo abo
abId = ifemId {c=TypeObj} TypeMor typeId

export
0 abComp : {0 x, y, z : ABundleObj} ->
  ABundleMor y z -> ABundleMor x y -> ABundleMor x z
abComp = ifemComp {c=TypeObj} TypeMor typeComp

export
0 cbId : (cbo : CBundleObj) -> CBundleMor cbo cbo
cbId cbo = BcmCfromA $ abId (BcoCtoA cbo)

export
0 cbComp : {x, y, z : CBundleObj} ->
  CBundleMor y z -> CBundleMor x y -> CBundleMor x z
cbComp {x} {y} {z} g f =
  BcmCfromA $
  abComp {x=(BcoCtoA x)} {y=(BcoCtoA y)} {z=(BcoCtoA z)} (BcmCtoA g) (BcmCtoA f)

----------------------------------------
----------------------------------------
---- Universal morphisms on bundles ----
----------------------------------------
----------------------------------------

public export
abPullback : (ab : ABundleObj) -> {b' : Type} ->
  (b' -> abBase ab) -> ABundleObj
abPullback ab {b'} m = (b' ** abCobase ab . m)

public export
cbPullback : (cb : CBundleObj) -> {b' : Type} ->
  (b' -> cbBase cb) -> CBundleObj
cbPullback cbo {b'} m with (CSBaseChange m (CBOsl cbo))
  cbPullback cbo {b'} m | (cb' ** proj') =
    CBO b' cb' proj'

-----------------------------------
-----------------------------------
---- (Co)presheaves on bundles ----
-----------------------------------
-----------------------------------

-- The signature of a copresheaf on the bundle category of `Type`
-- recall that the bundle category of `Type` is equivalent to the category
-- of Dirichlet functors on `Type`, so this is also the signature of a
-- copresheaf on the category of Dirichlet functors on `Type`).
public export
BundleCoprSig : Type
BundleCoprSig = (x, y : Type) -> (y -> x) -> Type

-- The signature of the fmap of a presheaf on the bundle/Dirichlet category
-- of `Type`.
public export
BundleCoprDimapSig : BundleCoprSig -> Type
BundleCoprDimapSig p =
  -- `mts` and `mba` are bundles.
  (s, t, a, b : Type) -> (mts : t -> s) -> (mba : b -> a) ->
  -- `msa` and `mtb` comprise a bundle morphism from `mts` to `mba`.
  (msa : s -> a) ->
  (mtb :
    CSliceMorphism {c=s}
      (t ** mts)
      (CSBaseChange {c=a} {d=s} msa (b ** mba))) ->
  p s t mts -> p a b mba

-- This computes the requirement to build a `(q . p) a b mba`
-- in the style of profunctor composition -- starting from an
-- `(s, t, mts)` with a `(u, v, mvu)` as an intermediate object.
public export
data BundleCoprComposeSig :
    BundleCoprSig -> BundleCoprSig -> BundleCoprSig where
  BunCC : (q, p : BundleCoprSig) ->
    (s, t, u, v, a, b : Type) ->
    -- `mts`, `mvu`, and `mba` are bundles.
    (mts : t -> s) -> (mvu : v -> u) -> (mba : b -> a) ->
    -- `mua` and `mvb` comprise a bundle morphism from `mvu` to `mba`.
    (mua : u -> a) ->
    (mvb :
      CSliceMorphism {c=u}
        (v ** mvu)
        (CSBaseChange {c=a} {d=u} mua (b ** mba))) ->
    q u v mvu ->
    -- `msu` and `mtv` comprise a bundle morphism from `mts` to `mvu`.
    (msu : s -> u) ->
    (mtv :
      CSliceMorphism {c=s}
        (t ** mts)
        (CSBaseChange {c=u} {d=s} msu (v ** mvu))) ->
    p s t mts ->
    BundleCoprComposeSig q p a b mba
