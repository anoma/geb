module LanguageDef.IntBundle

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat

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
