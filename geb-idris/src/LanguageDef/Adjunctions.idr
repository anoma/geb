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
AdjObjF = Diagram -> Type

public export
DgmObjP : Type
DgmObjP = (Diagram, AdjObjF)

public export
data ObjApplyObj : SliceObj DgmObjP where
  OAppV : dgm.dVert -> ObjApplyObj (dgm, objf)
  OAppC : objf dgm -> ObjApplyObj (dgm, objf)

public export
data ObjApplyHom : (dop : DgmObjP) -> HomSlice (ObjApplyObj dop) where
  OAppH : {x, y : dgm.dVert} ->
    dgm.dEdge (x, y) -> ObjApplyHom (dgm, objf) (OAppV x, OAppV y)

public export
data ObjApplyRel : (dop : DgmObjP) -> SigRelT (ObjApplyHom dop) where
  OAppR : {x, y : dgm.dVert} -> {f, g : dgm.dEdge (x, y)} ->
    dgm.dRel ((x, y) ** (f, g)) ->
    ObjApplyRel (dgm, objf) ((OAppV x, OAppV y) ** (OAppH f, OAppH g))

-- This extends only the object part of the diagram.
public export
objApply : DgmObjP -> Diagram
objApply dop = MkDiagram (ObjApplyObj dop) (ObjApplyHom dop) (ObjApplyRel dop)

public export
LeftAdjUnitF : AdjObjF -> Type
LeftAdjUnitF objf = (dgm : Diagram) -> SliceObj (dgm.dVert, objf dgm)

public export
LAUnitP : Type
LAUnitP = (dop : DgmObjP ** LeftAdjUnitF (snd dop))

-- The unit extends only the morphisms, not the objects.
public export
LAUApplyObj : SliceObj LAUnitP
LAUApplyObj dop = ObjApplyObj (fst dop)

public export
RightAdjCounitF : AdjObjF -> Type
RightAdjCounitF objf = (dgm : Diagram) -> SliceObj (objf dgm, dgm.dVert)

public export
RACounitP : Type
RACounitP = (dop : DgmObjP ** RightAdjCounitF (snd dop))

-- The counit extends only the morphisms, not the objects.
public export
RACApplyObj : SliceObj RACounitP
RACApplyObj dop = ObjApplyObj (fst dop)

public export
LARightAdjunctF : {objf : AdjObjF} -> LeftAdjUnitF objf -> Type
LARightAdjunctF {objf} counit =
  (dgm, dgm' : Diagram) -> SliceObj (objf dgm, dgm'.dVert)

public export
RALeftAdjunctF : {objf : AdjObjF} -> RightAdjCounitF objf -> Type
RALeftAdjunctF {objf} unit =
  (dgm, dgm' : Diagram) -> SliceObj (dgm.dVert, objf dgm')

------------------
------------------
---- Examples ----
------------------
------------------

public export
data InitObjF : AdjObjF where
  InitObj : InitObjF dgm

public export
data InitUnitF : LeftAdjUnitF InitObjF where

public export
data InitRightAdjunctF : LARightAdjunctF InitUnitF where
  InitMorph : (a : dgm'.dVert) -> InitRightAdjunctF dgm dgm' (InitObj, a)

public export
data TermObjF : AdjObjF where
  TermObj : TermObjF dgm

public export
data TermCounitF : RightAdjCounitF TermObjF where

public export
data TermLeftAdjunctF : RALeftAdjunctF TermCounitF where
  TermMorph : (a : dgm.dVert) -> TermLeftAdjunctF dgm dgm' (a, TermObj)

public export
data CoprodObjF : AdjObjF where
  CopObj : dgm.dVert -> dgm.dVert -> CoprodObjF dgm

public export
data CoprodUnitF : LeftAdjUnitF CoprodObjF where
  CopInjL : (x, y : dgm.dVert) -> CoprodUnitF dgm (x, CopObj x y)
  CopInjR : (x, y : dgm.dVert) -> CoprodUnitF dgm (y, CopObj x y)

public export
data CoprodRightAdjunctF : LARightAdjunctF CoprodUnitF where

public export
data ProdObjF : AdjObjF where
  PrObj : dgm.dVert -> dgm.dVert -> ProdObjF dgm

public export
data ProdCounitF : RightAdjCounitF ProdObjF where
  PrProjL : (x, y : dgm.dVert) -> ProdCounitF dgm (PrObj x y, x)
  PrProjR : (x, y : dgm.dVert) -> ProdCounitF dgm (PrObj x y, y)

public export
data ProdLeftAdjunctF : RALeftAdjunctF ProdCounitF where

public export
data CoeqObjF : AdjObjF where
  CoeqObj : {x, y : dgm.dVert} ->
    dgm.dEdge (x, y) -> dgm.dEdge (x, y) -> CoeqObjF dgm

public export
data CoeqUnitF : LeftAdjUnitF CoeqObjF where
  CoeqInj : {x, y : dgm.dVert} ->
    (f, g : dgm.dEdge (x, y)) -> CoeqUnitF dgm (y, CoeqObj {x} {y} f g)

public export
data CoeqRightAdjunctF : LARightAdjunctF CoeqUnitF where

public export
data EqObjF : AdjObjF where
  EqObj : {x, y : dgm.dVert} ->
    dgm.dEdge (x, y) -> dgm.dEdge (x, y) -> EqObjF dgm

public export
data EqCounitF : RightAdjCounitF EqObjF where
  EqInj : {x, y : dgm.dVert} ->
    (f, g : dgm.dEdge (x, y)) -> EqCounitF dgm (EqObj {x} {y} f g, x)

public export
data EqLeftAdjunctF : RALeftAdjunctF EqCounitF where
