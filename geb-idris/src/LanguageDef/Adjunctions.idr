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
  OAppRv : {x, y : dgm.dVert} -> {f, g : dgm.dEdge (x, y)} ->
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

-- For a left adjoint, the unit provides the constructors.  These we
-- treat as injective, like any typical datatype constructor -- hence
-- the unit introduces no equalities, only new morphisms.  Furthermore,
-- because these are only constructors, they only introduce new morphisms
-- into the new objects, not out of them.
public export
data LAUApplyHom : (lup : LAUnitP) -> HomSlice (LAUApplyObj lup) where
  LAUHv : {0 dgm : Diagram} -> {objf : AdjObjF} -> {lau : LeftAdjUnitF objf} ->
    {x, y : dgm.dVert} ->
    dgm.dEdge (x, y) -> LAUApplyHom ((dgm, objf) ** lau) (OAppV x, OAppV y)
  LAUHc : {0 dgm : Diagram} -> {objf : AdjObjF} -> {lau : LeftAdjUnitF objf} ->
    {x : dgm.dVert} -> {y : objf dgm} ->
    lau dgm (x, y) -> LAUApplyHom ((dgm, objf) ** lau) (OAppV x, OAppC y)

-- We treat the constructors (which, for a left adjoint, come from the unit)
-- treat as injective, like any typical datatype constructor -- hence
-- the unit introduces no equalities, only new morphisms.
public export
data LAUApplyRel : (lup : LAUnitP) -> SigRelT (LAUApplyHom dop) where
  LAURv : {0 dgm : Diagram} -> {objf : AdjObjF} -> {lau : LeftAdjUnitF objf} ->
    {x, y : dgm.dVert} -> {f, g : dgm.dEdge (x, y)} ->
    -- dgm.dRel ((x, y) ** (f, g)) ->
    ObjApplyRel (dgm, objf) ((OAppV x, OAppV y) ** (OAppH f, OAppH g)) ->
    LAUApplyRel
      ((dgm, objf) ** lau) ((OAppV x, OAppV y) **
       (LAUHv {dgm} {lau} {x} {y} f, LAUHv {dgm} {lau} {x} {y} g))

public export
lauApply : LAUnitP -> Diagram
lauApply lup = MkDiagram (LAUApplyObj lup) (LAUApplyHom lup) (LAUApplyRel lup)

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

-- For a right adjoint, the counit provides the constructors.  These we
-- treat as injective, like any typical datatype constructor -- hence
-- the counit introduces no equalities, only new morphisms.  Furthermore,
-- because these are only constructors, they only introduce new morphisms
-- into the new objects, not out of them.
public export
data RACApplyHom : (rcp : RACounitP) -> HomSlice (RACApplyObj rcp) where
  RACHv : {0 dgm : Diagram} -> {objf : AdjObjF} ->
    {rac : RightAdjCounitF objf} ->
    {x, y : dgm.dVert} ->
    dgm.dEdge (x, y) -> RACApplyHom ((dgm, objf) ** rac) (OAppV x, OAppV y)
  RACHc : {0 dgm : Diagram} -> {objf : AdjObjF} ->
    {rac : RightAdjCounitF objf} ->
    {x : objf dgm} -> {y : dgm.dVert} ->
    rac dgm (x, y) -> RACApplyHom ((dgm, objf) ** rac) (OAppC x, OAppV y)

-- We treat the constructors (which, for a right adjoint, come from the counit)
-- treat as injective, like any typical datatype constructor -- hence
-- the counit introduces no equalities, only new morphisms.
public export
data RACApplyRel : (rcp : RACounitP) -> SigRelT (RACApplyHom dop) where
  RACRv : {0 dgm : Diagram} -> {objf : AdjObjF} ->
    {rac : RightAdjCounitF objf} ->
    {x, y : dgm.dVert} -> {f, g : dgm.dEdge (x, y)} ->
    -- dgm.dRel ((x, y) ** (f, g)) ->
    ObjApplyRel (dgm, objf) ((OAppV x, OAppV y) ** (OAppH f, OAppH g)) ->
    RACApplyRel
      ((dgm, objf) ** rac) ((OAppV x, OAppV y) **
       (RACHv {dgm} {rac} {x} {y} f, RACHv {dgm} {rac} {x} {y} g))

public export
racApply : RACounitP -> Diagram
racApply rcp = MkDiagram (RACApplyObj rcp) (RACApplyHom rcp) (RACApplyRel rcp)

public export
LARightAdjunctHomF : {objf : AdjObjF} -> LeftAdjUnitF objf -> Type
LARightAdjunctHomF {objf} unit =
  (dgm : Diagram) -> HomSlice (LAUApplyObj ((dgm, objf) ** unit))

public export
RALeftAdjunctHomF : {objf : AdjObjF} -> RightAdjCounitF objf -> Type
RALeftAdjunctHomF {objf} counit =
  (dgm : Diagram) -> HomSlice (RACApplyObj ((dgm, objf) ** counit))

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
data InitRightAdjunctHomF : LARightAdjunctHomF InitUnitF where
  InitMorph : (a : dgm.dVert) ->
    InitRightAdjunctHomF dgm (OAppC InitObj, OAppV a)

public export
data TermObjF : AdjObjF where
  TermObj : TermObjF dgm

public export
data TermCounitF : RightAdjCounitF TermObjF where

public export
data TermLeftAdjunctHomF : RALeftAdjunctHomF TermCounitF where
  TermMorph : (a : dgm.dVert) ->
    TermLeftAdjunctHomF dgm (OAppV a, OAppC TermObj)

public export
data CoprodObjF : AdjObjF where
  CopObj : dgm.dVert -> dgm.dVert -> CoprodObjF dgm

public export
data CoprodUnitF : LeftAdjUnitF CoprodObjF where
  CopInjL : (x, y : dgm.dVert) -> CoprodUnitF dgm (x, CopObj x y)
  CopInjR : (x, y : dgm.dVert) -> CoprodUnitF dgm (y, CopObj x y)

public export
data CoprodRightAdjunctHomF : LARightAdjunctHomF CoprodUnitF where
  CopCase :
    {a, b : dgm.dVert} -> {c : ObjApplyObj (dgm, CoprodObjF)} ->
    LAUApplyHom ((dgm, CoprodObjF) ** CoprodUnitF) (OAppV a, c) ->
    LAUApplyHom ((dgm, CoprodObjF) ** CoprodUnitF) (OAppV b, c) ->
    CoprodRightAdjunctHomF dgm (OAppC (CopObj a b), c)

public export
data ProdObjF : AdjObjF where
  PrObj : dgm.dVert -> dgm.dVert -> ProdObjF dgm

public export
data ProdCounitF : RightAdjCounitF ProdObjF where
  PrProjL : (x, y : dgm.dVert) -> ProdCounitF dgm (PrObj x y, x)
  PrProjR : (x, y : dgm.dVert) -> ProdCounitF dgm (PrObj x y, y)

public export
data ProdLeftAdjunctHomF : RALeftAdjunctHomF ProdCounitF where
  ProdBi :
    {a : ObjApplyObj (dgm, ProdObjF)} -> {b, c : dgm.dVert} ->
    RACApplyHom ((dgm, ProdObjF) ** ProdCounitF) (a, OAppV b) ->
    RACApplyHom ((dgm, ProdObjF) ** ProdCounitF) (a, OAppV c) ->
    ProdLeftAdjunctHomF dgm (a, OAppC (PrObj b c))

public export
data CoeqObjF : AdjObjF where
  CoeqObj : {x, y : dgm.dVert} ->
    dgm.dEdge (x, y) -> dgm.dEdge (x, y) -> CoeqObjF dgm

public export
data CoeqUnitF : LeftAdjUnitF CoeqObjF where
  CoeqInj : {x, y : dgm.dVert} ->
    (f, g : dgm.dEdge (x, y)) -> CoeqUnitF dgm (y, CoeqObj {x} {y} f g)

public export
data CoeqRightAdjunctHomF : LARightAdjunctHomF CoeqUnitF where

public export
data EqObjF : AdjObjF where
  EqObj : {x, y : dgm.dVert} ->
    dgm.dEdge (x, y) -> dgm.dEdge (x, y) -> EqObjF dgm

public export
data EqCounitF : RightAdjCounitF EqObjF where
  EqInj : {x, y : dgm.dVert} ->
    (f, g : dgm.dEdge (x, y)) -> EqCounitF dgm (EqObj {x} {y} f g, x)

public export
data EqLeftAdjunctHomF : RALeftAdjunctHomF EqCounitF where
