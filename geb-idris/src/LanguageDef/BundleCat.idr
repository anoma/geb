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
record ADisliceCat where
  constructor ADSC
  adscBase : Type
  adscCobase : SliceObj adscBase

public export
ASliceBase : ADisliceCat -> Type
ASliceBase = SliceObj . adscBase

public export
adscCotot : ADisliceCat -> Type
adscCotot cat = Sigma {a=(adscBase cat)} (adscCobase cat)

public export
ADSOinj : (cat : ADisliceCat) -> ASliceBase cat -> Type
ADSOinj cat = SliceMorphism {a=(adscBase cat)} (adscCobase cat)
