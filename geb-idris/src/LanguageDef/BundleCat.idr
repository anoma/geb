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

--------------------------
---- Categorial-style ----
--------------------------

-- A bundle is an arrow whose morphisms comprise a (covariant) morphism between
-- codomains together with (covariant) morphisms on fibrations of the domains by
-- the codomain morphisms.
public export
record CBundleObj where
  constructor CDSC
  cbTot : Type
  cbBase : Type
  cbProj : cbBase -> cbTot

---------------------
---- Arena-style ----
---------------------

public export
record ABundleObj where
  constructor ADSC
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

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

public export
DscCtoA : CBundleObj -> ABundleObj
DscCtoA cat =
  ADSC (cbTot cat) $
    \ea => PreImage {a=(cbBase cat)} {b=(cbTot cat)} (cbProj cat) ea

public export
DscAtoC : ABundleObj -> CBundleObj
DscAtoC cat =
  CDSC (abBase cat) (Sigma {a=(abBase cat)} $ abCobase cat) DPair.fst
