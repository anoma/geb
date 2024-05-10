module LanguageDef.IntBundleCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntEFamCat

-----------------
-----------------
---- Bundles ----
-----------------
-----------------

public export
record IntBundleObj {0 c : Type} (0 mor : IntMorSig c) where
  constructor IBO
  iboDom : c
  iboCod : c
  iboMor : mor iboDom iboCod
