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
BcoCtoA cat =
  ABO (cbTot cat) $
    \ea => PreImage {a=(cbBase cat)} {b=(cbTot cat)} (cbProj cat) ea

public export
BcoAtoC : ABundleObj -> CBundleObj
BcoAtoC cat =
  CBO (abBase cat) (Sigma {a=(abBase cat)} $ abCobase cat) DPair.fst

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

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Objects of category of bundles (with covariant fiber morphisms) ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------
