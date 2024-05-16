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
-- families (AKA polynomial functors) on its twisted-arrow category.

public export
IntDisheafCat : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntCatSig
IntDisheafCat c mapId mapComp = ECofamCatSig $ TwArrCat c mapId mapComp

public export
IntDisheafObj : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  Type
IntDisheafObj c mapId mapComp = icObj $ IntDisheafCat c mapId mapComp

public export
IntDisheafMor : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntMorSig (IntDisheafObj c mapId mapComp)
IntDisheafMor c mapId mapComp = icMor $ IntDisheafCat c mapId mapComp

public export
IntDisheafComp : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntCompSig (IntDisheafObj c mapId mapComp) (IntDisheafMor c mapId mapComp)
IntDisheafComp c mapId mapComp = icComp $ IntDisheafCat c mapId mapComp

public export
IntDisheafId : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntIdSig (IntDisheafObj c mapId mapComp) (IntDisheafMor c mapId mapComp)
IntDisheafId c mapId mapComp = icId $ IntDisheafCat c mapId mapComp

-------------------------------------
-------------------------------------
---- Disheaf composition product ----
-------------------------------------
-------------------------------------

public export
IntDisheafInterp : {c : IntCatSig} ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntDisheafObj c mapId mapComp ->
  (x, y : icObj c) -> icMor c x y -> QType
IntDisheafInterp {c} mapId mapComp p x y f =
  QTypeFromType
  $ InterpECofamCopreshfOMap
    (TwArrObj c mapId mapComp) (TwArrMor c mapId mapComp)
    p ((x, y) ** f)
