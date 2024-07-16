module LanguageDef.SlPolyIntCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.InternalCat
import LanguageDef.SlicePolyCat
import LanguageDef.IntEFamCat
import LanguageDef.IntUFamCat
import LanguageDef.IntECofamCat
import LanguageDef.IntUCofamCat

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Embedding of internal categories into dependent polynomial functors ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-- A "generalized element" of an object of a category is simply
-- a morphism into that category.
public export
IntGenEl : (cat : IntCatSig) -> SliceObj (icObj cat)
IntGenEl cat = Sigma {a=(icObj cat)} . flip (icMor cat)

-- The above definition turns out to be precisely
-- `InterpSLEFamObj {c=(icObj cat)} (icObj cat ** icMor cat)`.
public export
IntGenElAsSLEFam : (cat : IntCatSig) ->
  (IntGenEl cat = InterpSLEFamObj {c=(icObj cat)} (icObj cat ** icMor cat))
IntGenElAsSLEFam cat = Refl

-- A (metalanguage) function on generalized elements of an internal category.
public export
IntGenElF : (cat : IntCatSig) -> IntMorSig (icObj cat)
IntGenElF cat x y = IntGenEl cat x -> IntGenEl cat y

-- A codomain change is a function on generalized elements which leaves
-- the domain unchanged.
public export
IntCodChangeF : (cat : IntCatSig) -> IntMorSig (icObj cat)
IntCodChangeF cat x y =
  SliceMorphism {a=(icObj cat)} (flip (icMor cat) x) (flip (icMor cat) y)

public export
IntCodChangeFAsGenElF : {cat : IntCatSig} -> {x, y : icObj cat} ->
  IntCodChangeF cat x y -> IntGenElF cat x y
IntCodChangeFAsGenElF {cat} {x} {y} = dpMapSnd
