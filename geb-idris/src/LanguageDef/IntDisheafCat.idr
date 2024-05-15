module LanguageDef.IntDisheafCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntECofamCat

-------------------------------------
-------------------------------------
---- Disheaf category definition ----
-------------------------------------
-------------------------------------

-- The disheaf category of a category is the category of existential
-- cofamilies (AKA polynomial functors) on its twisted-arrow category.

public export
IntDisheafCat : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntCatSig
IntDisheafCat c mapId mapComp = ECofamCatSig $ TwArrCat c mapId mapComp
