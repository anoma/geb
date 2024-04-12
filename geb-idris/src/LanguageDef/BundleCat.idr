module LanguageDef.BundleCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.InternalCat
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
  cbTot : Type
  cbBase : Type
  cbProj : cbBase -> cbTot

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

public export
BcoCtoA : CBundleObj -> ABundleObj
BcoCtoA cb =
  ABO (cbTot cb) $
    \ea => PreImage {a=(cbBase cb)} {b=(cbTot cb)} (cbProj cb) ea

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
  cbmBase : cbTot dom -> cbTot cod
  cbmTot :
    CSliceMorphism
      {c=(cbTot dom)}
      (cbBase dom ** cbProj dom)
      (Pullback (cbProj cod) cbmBase ** pbProj2 {f=(cbProj cod)} {g=cbmBase})

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

---------------------------------------------
---- Equivalence with Dirichlet functors ----
---------------------------------------------
