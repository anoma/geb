module LanguageDef.IntEFamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.BundleCat

------------------------------------------------------------------
------------------------------------------------------------------
---- Metalanguage interpretation of free coproduct completion ----
------------------------------------------------------------------
------------------------------------------------------------------

--------------------
---- Definition ----
--------------------

public export
MLEFamObj : Type
MLEFamObj = ABundleObj

public export
MLEFamMor : MLEFamObj -> MLEFamObj -> Type
MLEFamMor = ABundleMor

public export
mlfmId : (x : MLEFamObj) -> MLEFamMor x x
mlfmId = abId

public export
mlfmComp : {x, y, z : MLEFamObj} ->
  MLEFamMor y z -> MLEFamMor x y -> MLEFamMor x z
mlfmComp = abComp

public export
mliceEFamUnit : Type -> MLEFamObj
mliceEFamUnit = BcoDirichToA . PFHomArena

------------------------
---- Interpretation ----
------------------------

-- In a category with products, such as `Type`, we can interpret an
-- `IntFamObj` as a product with morphisms restricted to factorizations
-- into morphisms on indexes and morphisms on components.

export
InterpMLEFamObj : MLEFamObj -> Type
InterpMLEFamObj = abTot

export
InterpMLEFamMorph : {0 x, y : MLEFamObj} ->
  MLEFamMor x y -> InterpMLEFamObj x -> InterpMLEFamObj y
InterpMLEFamMorph m = dpBimap (abmBase m) (abmCobase m)
