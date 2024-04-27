module LanguageDef.IntParamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntEFamCat
import public LanguageDef.IntECofamCat
import public LanguageDef.IntUFamCat
import public LanguageDef.IntUCofamCat

-------------------------------
-------------------------------
---- Parameterized bundles ----
-------------------------------
-------------------------------

public export
PBundleObj : Type -> Type
PBundleObj x = x -> IntEFamObj TypeObj

public export
PBundleMor : {x, y : Type} ->
  (dom : PBundleObj x) -> (cod : PBundleObj y) -> Type
PBundleMor {x} {y} dom cod =
  IntEFamMor {c=(IntEFamObj TypeObj)} (IntEFamMor {c=TypeObj} TypeMor)
    (x ** dom)
    (y ** cod)
