module LanguageDef.Adjunctions

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.ProgFinSet
import public LanguageDef.PolyCat
import public LanguageDef.Syntax
import public LanguageDef.DiagramCat

%default total

------------------------------------
------------------------------------
---- Left and right adjunctions ----
------------------------------------
------------------------------------

public export
AdjObjF : Type
AdjObjF = SCat -> Type

public export
LeftAdjUnitF : AdjObjF -> Type
LeftAdjUnitF objf = (sc : SCat) -> SliceObj (sc.scObj, objf sc)

public export
RightAdjCounitF : AdjObjF -> Type
RightAdjCounitF objf = (sc : SCat) -> SliceObj (objf sc, sc.scObj)

------------------
------------------
---- Examples ----
------------------
------------------

public export
data InitObjF : AdjObjF where
  InitObj : InitObjF sc

public export
data InitUnitF : LeftAdjUnitF InitObjF where

public export
data TermObjF : AdjObjF where
  TermObj : TermObjF sc

public export
data TermCounitF : RightAdjCounitF InitObjF where

public export
data CoprodObjF : AdjObjF where
  CopObj : sc.scObj -> sc.scObj -> CoprodObjF sc

public export
data CoprodUnitF : LeftAdjUnitF CoprodObjF where
  CopInjL : (x, y : sc.scObj) -> CoprodUnitF sc (x, CopObj x y)
  CopInjR : (x, y : sc.scObj) -> CoprodUnitF sc (y, CopObj x y)

public export
data ProdObjF : AdjObjF where
  PrObj : sc.scObj -> sc.scObj -> ProdObjF sc

public export
data ProdCounitF : RightAdjCounitF ProdObjF where
  PrProjL : (x, y : sc.scObj) -> ProdCounitF sc (PrObj x y, x)
  PrProjR : (x, y : sc.scObj) -> ProdCounitF sc (PrObj x y, y)

public export
data CoeqObjF : AdjObjF where
  CoeqObj :
    {x, y : sc.scObj} -> sc.scHom (x, y) -> sc.scHom (x, y) -> CoeqObjF sc

public export
data CoeqUnitF : LeftAdjUnitF CoeqObjF where
  CoeqInj : {x, y : sc.scObj} ->
    (f, g : sc.scHom (x, y)) -> CoeqUnitF sc (y, CoeqObj {x} {y} f g)

public export
data EqObjF : AdjObjF where
  EqObj :
    {x, y : sc.scObj} -> sc.scHom (x, y) -> sc.scHom (x, y) -> EqObjF sc

public export
data EqCounitF : RightAdjCounitF EqObjF where
  EqInj : {x, y : sc.scObj} ->
    (f, g : sc.scHom (x, y)) -> EqCounitF sc (EqObj {x} {y} f g, x)
