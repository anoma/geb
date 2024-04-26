module LanguageDef.IntBundleCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntEFamCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

public export
record IntBundleObj {c : Type} (mor : IntDifunctorSig c) where
  constructor IBO
  iboDom : c
  iboCod : c
  iboMor : mor iboDom iboCod
