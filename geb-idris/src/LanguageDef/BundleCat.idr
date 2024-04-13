module LanguageDef.BundleCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.InternalCat
import LanguageDef.IntFamCat
import LanguageDef.IntBundle
import LanguageDef.PolyCat

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Objects of category of bundles (with covariant fiber morphisms) ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

---------------------
---- Arena-style ----
---------------------

public export
record ABundleObj where
  constructor ABO
  abBase : Type
  abCobase : SliceObj abBase

public export
ABSliceBase : ABundleObj -> Type
ABSliceBase = SliceObj . abBase

public export
abTot : ABundleObj -> Type
abTot cat = Sigma {a=(abBase cat)} (abCobase cat)

public export
ABinj : (cat : ABundleObj) -> ABSliceBase cat -> Type
ABinj cat = SliceMorphism {a=(abBase cat)} (abCobase cat)

--------------------------
---- Categorial-style ----
--------------------------

-- A bundle is an arrow whose morphisms comprise a (covariant) morphism between
-- codomains together with (covariant) morphisms on fibrations of the domains by
-- the codomain morphisms.
public export
record CBundleObj where
  constructor CBO
  cbBase : Type
  cbTot : Type
  cbProj : cbTot -> cbBase

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

public export
BcoCtoA : CBundleObj -> ABundleObj
BcoCtoA cb =
  ABO (cbBase cb) $
    \ea => PreImage {a=(cbTot cb)} {b=(cbBase cb)} (cbProj cb) ea

public export
BcoAtoC : ABundleObj -> CBundleObj
BcoAtoC ab =
  CBO (abBase ab) (Sigma {a=(abBase ab)} $ abCobase ab) DPair.fst

---------------------------------------------
---- Equivalence with Dirichlet functors ----
---------------------------------------------

public export
BcoAtoDirich : ABundleObj -> PolyFunc
BcoAtoDirich (ABO base cobase) = (base ** cobase)

public export
BcoCtoDirich : CBundleObj -> PolyFunc
BcoCtoDirich = BcoAtoDirich . BcoCtoA

public export
BcoDirichToA : PolyFunc -> ABundleObj
BcoDirichToA (base ** cobase) = ABO base cobase

public export
BcoDirichToC : PolyFunc -> CBundleObj
BcoDirichToC = BcoAtoC . BcoDirichToA

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Morphisms of category of bundles (with covariant fiber morphisms) ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

---------------------
---- Arena-style ----
---------------------

-- These morphisms make the `ABundleMor` category equivalent to the
-- category of Dirichlet functors, which, as noted at
-- https://ncatlab.org/nlab/show/free+coproduct+completion#ViaIndexedSetsOfObjects ,
-- may also be viewed as the free coproduct completion (here of `Type`).
public export
record ABundleMor (dom, cod : ABundleObj) where
  constructor ABM
  abmBase : abBase dom -> abBase cod
  abmCobase :
    SliceMorphism {a=(abBase dom)} (abCobase dom) (abCobase cod . abmBase)

--------------------------
---- Categorial-style ----
--------------------------

public export
record CBundleMor (dom, cod : CBundleObj) where
  constructor CBM
  cbmBase : cbBase dom -> cbBase cod
  cbmTot :
    CSliceMorphism
      {c=(cbBase dom)}
      (cbTot dom ** cbProj dom)
      (Pullback (cbProj cod) cbmBase ** pbProj2 {f=(cbProj cod)} {g=cbmBase})

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

export
BcmCtoA : {0 dom, cod : CBundleObj} ->
  CBundleMor dom cod -> ABundleMor (BcoCtoA dom) (BcoCtoA cod)
BcmCtoA {dom} {cod} (CBM mbase (Element0 mtot mcomm)) =
  ABM
    mbase
    $ \edb, (Element0 edt deq) =>
        Element0
          (fst $ fst0 $ mtot edt)
          $ trans (snd0 $ mtot edt) $ rewrite sym (mcomm edt) in
            rewrite deq in Refl

export
BcmCfromA : {dom, cod : CBundleObj} ->
  ABundleMor (BcoCtoA dom) (BcoCtoA cod) -> CBundleMor dom cod
BcmCfromA {dom} {cod} (ABM mbase mcobase) =
  CBM
    mbase $
    Element0
      (\edt =>
        let
          mcb = mcobase (cbProj dom edt) $ Element0 edt Refl
        in
        Element0 (fst0 mcb, cbProj dom edt) $ snd0 mcb)
      $ \_ => Refl

export
BcmAtoC : {0 dom, cod : ABundleObj} ->
  ABundleMor dom cod -> CBundleMor (BcoAtoC dom) (BcoAtoC cod)
BcmAtoC {dom} {cod} (ABM mbase mcobase) =
  CBM
    mbase
    $ Element0
      (\(edb ** edcb) => Element0 ((mbase edb ** mcobase edb edcb), edb) Refl)
      (\(edb ** edcb) => Refl)

export
BcmAfromC : {0 dom, cod : ABundleObj} ->
  CBundleMor (BcoAtoC dom) (BcoAtoC cod) -> ABundleMor dom cod
BcmAfromC {dom} {cod} (CBM mbase (Element0 mtot mcomm)) =
  ABM
    mbase
    $ \edb, edcb =>
      rewrite sym $ trans (snd0 (mtot (edb ** edcb))) $ sym $ cong mbase
        $ mcomm (edb ** edcb) in
      snd $ fst $ fst0 $ mtot (edb ** edcb)

---------------------------------------------
---- Equivalence with Dirichlet functors ----
---------------------------------------------

export
BcmAtoDirich : {0 dom, cod : ABundleObj} ->
  ABundleMor dom cod -> DirichNatTrans (BcoAtoDirich dom) (BcoAtoDirich cod)
BcmAtoDirich {dom=(ABO dbase dcobase)} {cod=(ABO cbase ccobase)}
  (ABM mbase mcobase) =
    (mbase ** mcobase)

export
BcmAfromDirich : {0 dom, cod : ABundleObj} ->
  DirichNatTrans (BcoAtoDirich dom) (BcoAtoDirich cod) -> ABundleMor dom cod
BcmAfromDirich {dom=(ABO dbase dcobase)} {cod=(ABO cbase ccobase)}
  (mbase ** mcobase) =
    ABM mbase mcobase

export
BcmDirichToA : {0 dom, cod : PolyFunc} ->
  DirichNatTrans dom cod -> ABundleMor (BcoDirichToA dom) (BcoDirichToA cod)
BcmDirichToA {dom=(dpos ** ddir)} {cod=(cpos ** cdir)} (onpos ** ondir) =
  ABM onpos ondir

export
BcmDirichFromA : {0 dom, cod : PolyFunc} ->
  ABundleMor (BcoDirichToA dom) (BcoDirichToA cod) ->
  DirichNatTrans dom cod
BcmDirichFromA {dom=(dpos ** ddir)} {cod=(cpos ** cdir)} (ABM base cobase) =
  (base ** cobase)

export
BcmCtoDirich : {0 dom, cod : CBundleObj} ->
  CBundleMor dom cod -> DirichNatTrans (BcoCtoDirich dom) (BcoCtoDirich cod)
BcmCtoDirich = BcmAtoDirich . BcmCtoA

export
BcmCfromDirich : {dom, cod : CBundleObj} ->
  DirichNatTrans (BcoCtoDirich dom) (BcoCtoDirich cod) -> CBundleMor dom cod
BcmCfromDirich = BcmCfromA . BcmAfromDirich

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
abId : (abo : ABundleObj) -> ABundleMor abo abo
abId abo@(ABO b cb) =
  BcmDirichToA {dom=(BcoAtoDirich abo)} {cod=(BcoAtoDirich abo)}
  $ dntId {p=(BcoAtoDirich abo)}

export
abComp : {x, y, z : ABundleObj} ->
  ABundleMor y z -> ABundleMor x y -> ABundleMor x z
abComp {x=x@(ABO xb xcb)} {y} {z=z@(ABO zb zcb)} g f =
  BcmDirichToA {dom=(BcoAtoDirich x)} {cod=(BcoAtoDirich z)}
  $ dntVCatComp {p=(BcoAtoDirich x)} {r=(BcoAtoDirich z)}
    (BcmAtoDirich g) (BcmAtoDirich f)

export
cbId : (cbo : CBundleObj) -> CBundleMor cbo cbo
cbId cbo = BcmCfromA $ abId (BcoCtoA cbo)

export
cbComp : {x, y, z : CBundleObj} ->
  CBundleMor y z -> CBundleMor x y -> CBundleMor x z
cbComp g f = BcmCfromA $ abComp (BcmCtoA g) (BcmCtoA f)
