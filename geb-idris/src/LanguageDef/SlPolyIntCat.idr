module LanguageDef.SlPolyIntCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.InternalCat
import LanguageDef.SlicePolyCat
import LanguageDef.PolySliceCat
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
-- a morphism into that object.
public export
IntGenEl : (cat : IntCatSig) -> SliceObj (icObj cat)
IntGenEl cat = Sigma {a=(icObj cat)} . flip (icMor cat)

-- A "generalized quantity" over an object of a category is simply
-- a morphism out of that object.
public export
IntGenQuant : (cat : IntCatSig) -> SliceObj (icObj cat)
IntGenQuant cat = Sigma {a=(icObj cat)} . icMor cat

-- The above definition turns out to be precisely
-- `InterpSLEFamObj {c=(icObj cat)} (icObj cat ** icMor cat)`.
public export
IntGenElAsSLEFamObj : (cat : IntCatSig) ->
  (IntGenEl cat = InterpSLEFamObj {c=(icObj cat)} (icObj cat ** icMor cat))
IntGenElAsSLEFamObj cat = Refl

-- A (metalanguage) function on generalized elements of an internal category.
public export
IntGenElF : (cat : IntCatSig) -> IntMorSig (icObj cat)
IntGenElF cat x y = IntGenEl cat x -> IntGenEl cat y

-- A (metalanguage) function on generalized quantities of an internal category.
public export
IntGenQuantF : (cat : IntCatSig) -> IntMorSig (icObj cat)
IntGenQuantF cat x y = IntGenQuant cat x -> IntGenQuant cat y

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

-- A domain change is a function on generalized quantities which leaves
-- the codomain unchanged.
public export
IntDomChangeF : (cat : IntCatSig) -> IntMorSig (icObj cat)
IntDomChangeF cat x y =
  SliceMorphism {a=(icObj cat)} (icMor cat x) (icMor cat y)

public export
IntDomChangeFAsGenQuantF : {cat : IntCatSig} -> {x, y : icObj cat} ->
  IntDomChangeF cat x y -> IntGenQuantF cat x y
IntDomChangeFAsGenQuantF {cat} {x} {y} = dpMapSnd

-- We can define a notion of "commutation with reparameterization" on
-- a codomain-change function.  See for example
-- https://arbital.com/p/gen_elt/ .
public export
IntCodChangeFCommutes : {cat : IntCatSig} -> {x, y : icObj cat} ->
  IntCodChangeF cat x y -> Type
IntCodChangeFCommutes {cat} {x} {y} f =
  (a, b : icObj cat) -> (elx : icMor cat a x) ->
  ExtEq {a=(icMor cat b a)} {b=(icMor cat b y)}
    (f b . icComp cat b a x elx)
    (icComp cat b a y (f a elx))

public export
CommutingCodChangeF : (cat : IntCatSig) -> IntMorSig (icObj cat)
CommutingCodChangeF cat x y =
  Sigma {a=(IntCodChangeF cat x y)} (IntCodChangeFCommutes {cat} {x} {y})

public export
IntDomChangeFCommutes : {cat : IntCatSig} -> {x, y : icObj cat} ->
  IntDomChangeF cat x y -> Type
IntDomChangeFCommutes {cat} {x} {y} f =
  (a, b : icObj cat) -> (qx : icMor cat x a) ->
  ExtEq {a=(icMor cat a b)} {b=(icMor cat y b)}
    (f b . flip (icComp cat x a b) qx)
    (flip (icComp cat y a b) (f a qx))

public export
CommutingDomChangeF : (cat : IntCatSig) -> IntMorSig (icObj cat)
CommutingDomChangeF cat x y =
  Sigma {a=(IntDomChangeF cat x y)} (IntDomChangeFCommutes {cat} {x} {y})

public export
TypeMorFromCodChangeF : {x, y : Type} ->
  CommutingCodChangeF TypeCat x y -> x -> y
TypeMorFromCodChangeF {x} {y} f = fst f x id

public export
TypeMorToCodChangeF : {x, y : Type} ->
  (x -> y) -> CommutingCodChangeF TypeCat x y
TypeMorToCodChangeF f = (\_ => (.) f ** \_, _, _, _ => Refl)

public export
TypeMorFromDomChangeF : {x, y : Type} ->
  CommutingDomChangeF TypeCat x y -> y -> x
TypeMorFromDomChangeF {x} {y} f = fst f x id

public export
TypeMorToDomChangeF : {x, y : Type} ->
  (y -> x) -> CommutingDomChangeF TypeCat x y
TypeMorToDomChangeF f = (\_ => (|>) f ** \_, _, _, _ => Refl)
