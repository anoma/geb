module LanguageDef.Adjunctions

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.PolyCat
import public LanguageDef.Syntax
import public LanguageDef.DiagramCat

%default total

------------------------------------------------
------------------------------------------------
---- Finite polynomial functors on diagrams ----
------------------------------------------------
------------------------------------------------

-- The simplest form of polynomial functor on diagrams simply chooses from
-- among a finite number of vertices in a diagram and produces a finite number
-- of vertices from them.  So we call it a "vertex-vertex" functor.
public export
record FinDiagPolyFuncFromVert where
  constructor MkFinDPFVV
  fvvDom : Nat
  fvvCod : Nat

public export
data DPFInterpFinVVvert : FinDiagPolyFuncFromVert -> Diagram -> Type where
  FinVVv :
    Fin fvv.fvvCod -> Vect fvv.fvvDom (dVert dgm) -> DPFInterpFinVVvert fvv dgm

public export
data DPFInterpFinVVedge : (fvv : FinDiagPolyFuncFromVert) -> (dgm : Diagram) ->
  HomSlice (DPFInterpFinVVvert fvv dgm) where

public export
data DPFInterpFinVVrel : (fvv : FinDiagPolyFuncFromVert) -> (dgm : Diagram) ->
  CatRelT (DPFInterpFinVVedge fvv dgm) where

public export
DPFInterpFinVV : (fvv : FinDiagPolyFuncFromVert) -> Diagram -> Diagram
DPFInterpFinVV fvv dgm =
  MkDiagram
    (DPFInterpFinVVvert fvv dgm)
    (DPFInterpFinVVedge fvv dgm)
    (DPFInterpFinVVrel fvv dgm)

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
  OAppV : dVert dgm -> ObjApplyObj (dgm, objf)
  OAppC : objf dgm -> ObjApplyObj (dgm, objf)

public export
data ObjApplyHom : (dop : DgmObjP) -> HomSlice (ObjApplyObj dop) where
  OAppH : {x, y : dVert dgm} ->
    dEdge dgm (x, y) -> ObjApplyHom (dgm, objf) (OAppV x, OAppV y)

public export
data ObjApplyRel : (dop : DgmObjP) -> CatRelT (ObjApplyHom dop) where
  OAppRv : {x, y : dVert dgm} -> {f, g : dEdge dgm (x, y)} ->
    ?ObjApplyRel_rel_hole -> -- dgm.dRel ((x, y) ** (f, g)) ->
    ObjApplyRel (dgm, objf) ((OAppV x, OAppV y) ** ?ObjApplyRel_param_ole) -- (OAppH f, OAppH g)

-- This extends only the object part of the diagram.
public export
objApply : DgmObjP -> Diagram
objApply dop = MkDiagram (ObjApplyObj dop) (ObjApplyHom dop) (ObjApplyRel dop)

public export
LeftAdjUnitHomF : AdjObjF -> Type
LeftAdjUnitHomF objf = (dgm : Diagram) -> SliceObj (dVert dgm, objf dgm)

public export
LAUnitP : Type
LAUnitP = (dop : DgmObjP ** LeftAdjUnitHomF (snd dop))

-- The unit extends the morphisms, but not the objects.
public export
LAUApplyObj : SliceObj LAUnitP
LAUApplyObj dop = ObjApplyObj (fst dop)

-- For a left adjoint, the unit provides the constructors.
-- Because these are only constructors, they only introduce new morphisms
-- into the new objects, not out of them.
public export
data LAUApplyHom : (lup : LAUnitP) -> HomSlice (LAUApplyObj lup) where
  LAUHv :
    {0 dgm : Diagram} -> {objf : AdjObjF} -> {lau : LeftAdjUnitHomF objf} ->
    {x, y : dVert dgm} ->
    dEdge dgm (x, y) -> LAUApplyHom ((dgm, objf) ** lau) (OAppV x, OAppV y)
  LAUHc :
    {0 dgm : Diagram} -> {objf : AdjObjF} -> {lau : LeftAdjUnitHomF objf} ->
    {x : dVert dgm} -> {y : objf dgm} ->
    lau dgm (x, y) -> LAUApplyHom ((dgm, objf) ** lau) (OAppV x, OAppC y)

-- We treat the constructors (which, for a left adjoint, come from the unit)
-- treat as injective, like a typical datatype constructor.
-- XXX add equalities here
public export
data LAUApplyRel : (lup : LAUnitP) -> SigRelT (LAUApplyHom lup) where
  LAURv :
    {0 dgm : Diagram} -> {objf : AdjObjF} -> {lau : LeftAdjUnitHomF objf} ->
    {x, y : dVert dgm} -> {f, g : dEdge dgm (x, y)} ->
    ObjApplyRel (dgm, objf) ((OAppV x, OAppV y) ** ?LAUApplyRel_objrel_hole) -> -- (OAppH f, OAppH g) ->
    LAUApplyRel
      ((dgm, objf) ** lau) ((OAppV x, OAppV y) **
       (LAUHv {dgm} {lau} {x} {y} f, LAUHv {dgm} {lau} {x} {y} g))

public export
lauApply : LAUnitP -> Diagram
lauApply lup = MkDiagram (LAUApplyObj lup) (LAUApplyHom lup) ?lauApply_hole -- (LAUApplyRel lup)

public export
RightAdjCounitHomF : AdjObjF -> Type
RightAdjCounitHomF objf = (dgm : Diagram) -> SliceObj (objf dgm, dVert dgm)

public export
RACounitP : Type
RACounitP = (dop : DgmObjP ** RightAdjCounitHomF (snd dop))

-- The counit extends the morphisms, but not the objects.
public export
RACApplyObj : SliceObj RACounitP
RACApplyObj dop = ObjApplyObj (fst dop)

-- For a right adjoint, the counit provides the destructors.
public export
data RACApplyHom : (rcp : RACounitP) -> HomSlice (RACApplyObj rcp) where
  RACHv : {0 dgm : Diagram} -> {objf : AdjObjF} ->
    {rac : RightAdjCounitHomF objf} ->
    {x, y : dVert dgm} ->
    dEdge dgm (x, y) -> RACApplyHom ((dgm, objf) ** rac) (OAppV x, OAppV y)
  RACHc : {0 dgm : Diagram} -> {objf : AdjObjF} ->
    {rac : RightAdjCounitHomF objf} ->
    {x : objf dgm} -> {y : dVert dgm} ->
    rac dgm (x, y) -> RACApplyHom ((dgm, objf) ** rac) (OAppC x, OAppV y)

-- XXX add equalities here
public export
data RACApplyRel : (rcp : RACounitP) -> SigRelT (RACApplyHom rcp) where
  RACRv : {0 dgm : Diagram} -> {objf : AdjObjF} ->
    {rac : RightAdjCounitHomF objf} ->
    {x, y : dVert dgm} -> {f, g : dEdge dgm (x, y)} ->
    ObjApplyRel (dgm, objf) ((OAppV x, OAppV y) ** ?RACApplyRel_param_hole) ->
    -- (OAppH f, OAppH g) ->
    RACApplyRel
      ((dgm, objf) ** rac) ((OAppV x, OAppV y) **
       (RACHv {dgm} {rac} {x} {y} f, RACHv {dgm} {rac} {x} {y} g))

public export
racApply : RACounitP -> Diagram
racApply rcp = MkDiagram (RACApplyObj rcp) (RACApplyHom rcp) ?racApply_rel_hole -- (RACApplyRel rcp)

-- For a left adjoint, the right adjunct provides the destructors.
public export
LARightAdjunctHomF : {objf : AdjObjF} -> LeftAdjUnitHomF objf -> Type
LARightAdjunctHomF {objf} unit =
  (dgm : Diagram) -> HomSlice (LAUApplyObj ((dgm, objf) ** unit))

public export
LARAdjunctP : Type
LARAdjunctP = (lup : LAUnitP ** LARightAdjunctHomF (snd lup))

-- The adjunct doesn't introduce new objects, just new morphisms.
public export
LRAPApplyObj : LARAdjunctP -> Type
LRAPApplyObj lrap = LAUApplyObj (fst lrap)

public export
LRAPApplyHom : (lrap : LARAdjunctP) -> HomSlice (LRAPApplyObj lrap)
LRAPApplyHom = ?LRAPApplyHom_hole
{-
LRAPApplyHom (((dgm, objf) ** lau) ** lara) (OAppV x, OAppV y) = ?Lrapapplyhom_hole --dgm.dEdge (x, y)
LRAPApplyHom (((dgm, objf) ** lau) ** lara) (OAppV x, OAppV y) = dgm.dEdge (x, y)
LRAPApplyHom (((dgm, objf) ** lau) ** lara) (OAppV x, OAppC y) = lau dgm (x, y)
LRAPApplyHom (((dgm, objf) ** lau) ** lara) (OAppC x, OAppV y) = ?lrapApplyHom_hole_2
LRAPApplyHom (((dgm, objf) ** lau) ** lara) (OAppC x, OAppC y) = ?lrapApplyHom_hole_2'
-}

public export
LRAPApplyRel : (lrap : LARAdjunctP) -> SigRelT (LRAPApplyHom lrap)
LRAPApplyRel lrap = ?lrapApplyRel_hole

public export
lrapApply : LARAdjunctP -> Diagram
lrapApply lrap =
  MkDiagram (LRAPApplyObj lrap) (LRAPApplyHom lrap) ?lrapapply_hole -- (LRAPApplyRel lrap)

-- For a right adjoint, the left adjunct provides the constructors.
public export
RALeftAdjunctHomF : {objf : AdjObjF} -> RightAdjCounitHomF objf -> Type
RALeftAdjunctHomF {objf} counit =
  (dgm : Diagram) -> HomSlice (RACApplyObj ((dgm, objf) ** counit))

public export
RALAdjunctP : Type
RALAdjunctP = (rcp : RACounitP ** RALeftAdjunctHomF (snd rcp))

-- The adjunct doesn't introduce new objects, just new morphisms.
public export
RLAPApplyObj : RALAdjunctP -> Type
RLAPApplyObj rlap = RACApplyObj (fst rlap)

public export
RLAPApplyHom : (rlap : RALAdjunctP) -> HomSlice (RLAPApplyObj rlap)
RLAPApplyHom rlap = ?rlapApplyHom_hole

public export
RLAPApplyRel : (rlap : RALAdjunctP) -> SigRelT (RLAPApplyHom rlap)
RLAPApplyRel rlap = ?rlapApplyRel_hole

public export
rlapApply : RALAdjunctP -> Diagram
rlapApply rlap =
  MkDiagram (RLAPApplyObj rlap) (RLAPApplyHom rlap) ?rlapApply_hole -- (RLAPApplyRel rlap)

------------------
------------------
---- Examples ----
------------------
------------------

public export
data InitObjF : AdjObjF where
  InitObj : InitObjF dgm

public export
data InitUnitF : LeftAdjUnitHomF InitObjF where

public export
data InitRightAdjunctHomF : LARightAdjunctHomF InitUnitF where
  InitMorph : (a : dVert dgm) ->
    InitRightAdjunctHomF dgm (OAppC InitObj, OAppV a)

public export
data TermObjF : AdjObjF where
  TermObj : TermObjF dgm

public export
data TermCounitF : RightAdjCounitHomF TermObjF where

public export
data TermLeftAdjunctHomF : RALeftAdjunctHomF TermCounitF where
  TermMorph : (a : dVert dgm) ->
    TermLeftAdjunctHomF dgm (OAppV a, OAppC TermObj)

public export
data CoprodObjF : AdjObjF where
  CopObj : dVert dgm -> dVert dgm -> CoprodObjF dgm

public export
data CoprodUnitF : LeftAdjUnitHomF CoprodObjF where
  CopInjL : (x, y : dVert dgm) -> CoprodUnitF dgm (x, CopObj x y)
  CopInjR : (x, y : dVert dgm) -> CoprodUnitF dgm (y, CopObj x y)

public export
data CoprodRightAdjunctHomF : LARightAdjunctHomF CoprodUnitF where
  CopCase :
    {a, b : dVert dgm} -> {c : ObjApplyObj (dgm, CoprodObjF)} ->
    LAUApplyHom ((dgm, CoprodObjF) ** CoprodUnitF) (OAppV a, c) ->
    LAUApplyHom ((dgm, CoprodObjF) ** CoprodUnitF) (OAppV b, c) ->
    CoprodRightAdjunctHomF dgm (OAppC (CopObj a b), c)

public export
data ProdObjF : AdjObjF where
  PrObj : dVert dgm -> dVert dgm -> ProdObjF dgm

public export
data ProdCounitF : RightAdjCounitHomF ProdObjF where
  PrProjL : (x, y : dVert dgm) -> ProdCounitF dgm (PrObj x y, x)
  PrProjR : (x, y : dVert dgm) -> ProdCounitF dgm (PrObj x y, y)

public export
data ProdLeftAdjunctHomF : RALeftAdjunctHomF ProdCounitF where
  ProdBi :
    {a : ObjApplyObj (dgm, ProdObjF)} -> {b, c : dVert dgm} ->
    RACApplyHom ((dgm, ProdObjF) ** ProdCounitF) (a, OAppV b) ->
    RACApplyHom ((dgm, ProdObjF) ** ProdCounitF) (a, OAppV c) ->
    ProdLeftAdjunctHomF dgm (a, OAppC (PrObj b c))

public export
data CoeqObjF : AdjObjF where
  CoeqObj : {x, y : dVert dgm} ->
    dEdge dgm (x, y) -> dEdge dgm (x, y) -> CoeqObjF dgm

public export
data CoeqUnitF : LeftAdjUnitHomF CoeqObjF where
  CoeqIntroInj : {x, y : dVert dgm} ->
    (f, g : dEdge dgm (x, y)) -> CoeqUnitF dgm (y, CoeqObj {x} {y} f g)

public export
data CoeqRightAdjunctHomF : LARightAdjunctHomF CoeqUnitF where
{-
  CoeqElim : {dgm : Diagram} ->
    {x, y : dgm.dVert} -> {z : ObjApplyObj (dgm, CoeqObjF)} ->
    {f, g : dgm.dEdge (x, y)} ->
    (h : LAUApplyHom ((dgm, CoeqObjF) ** CoeqUnitF) (OAppV y, z)) ->
    -- Eliminating a coequalizer requires proof content: h . f = h . g
    CatFreeEq ?CoeqRightAdjunctHomF_hole -- (LAUApplyRel ((dgm, CoeqObjF) ** CoeqUnitF))
      ((OAppV {dgm} x, z) **
       (InSlFc $ CHComp (InSlFv h) (InSlFv $ LAUHv f),
        InSlFc $ CHComp (InSlFv h) (InSlFv $ LAUHv g))) ->
    CoeqRightAdjunctHomF dgm (OAppC (CoeqObj {x} {y} f g), z)
    -}

public export
data EqObjF : AdjObjF where
  EqObj : {x, y : dVert dgm} ->
    dEdge dgm (x, y) -> dEdge dgm (x, y) -> EqObjF dgm

public export
data EqCounitF : RightAdjCounitHomF EqObjF where
  EqElimInj : {x, y : dVert dgm} ->
    (f, g : dEdge dgm (x, y)) -> EqCounitF dgm (EqObj {x} {y} f g, x)

public export
data EqLeftAdjunctHomF : RALeftAdjunctHomF EqCounitF where
{-
  EqIntro :
    {a : ObjApplyObj (dgm, EqObjF)} -> {x, y : dgm.dVert} ->
    {f, g : dgm.dEdge (x, y)} ->
    (h : RACApplyHom ((dgm, EqObjF) ** EqCounitF) (a, OAppV x)) ->
    -- Introducing an equalizer requires proof content: f . h = g . h
    CatFreeEq ?EqLeftAdjunctHomF_hole -- (RACApplyRel ((dgm, EqObjF) ** EqCounitF))
      ((a, OAppV {dgm} y) **
       (InSlFc $ CHComp (InSlFv $ RACHv f) (InSlFv h),
        InSlFc $ CHComp (InSlFv $ RACHv g) (InSlFv h))) ->
    EqLeftAdjunctHomF dgm (a, OAppC (EqObj {x} {y} f g))
    -}

----------------------
----------------------
---- Finite topos ----
----------------------
----------------------

---------------------------------------------------
---- Unchecked (mutually recursive) expression ----
---------------------------------------------------

public export
data Geb0Slice : Type where
  G0OBJ : Geb0Slice
  G0MORPH : Geb0Slice
  G0OEQ : Geb0Slice
  G0MEQ : Geb0Slice

public export
Show Geb0Slice where
  show G0OBJ = "G0OBJ"
  show G0MORPH = "G0MORPH"
  show G0OEQ = "G0OEQ"
  show G0MEQ = "G0MEQ"

public export
Geb0SliceSz : Nat
Geb0SliceSz = 4

public export
G0SlFinDecoder : FinDecoder Geb0Slice Geb0SliceSz
G0SlFinDecoder FZ = G0OBJ
G0SlFinDecoder (FS FZ) = G0MORPH
G0SlFinDecoder (FS (FS FZ)) = G0OEQ
G0SlFinDecoder (FS (FS (FS FZ))) = G0MEQ

public export
G0SlNatEncoder : NatEncoder G0SlFinDecoder
G0SlNatEncoder G0OBJ = (0 ** Refl ** Refl)
G0SlNatEncoder G0MORPH = (1 ** Refl ** Refl)
G0SlNatEncoder G0OEQ = (2 ** Refl ** Refl)
G0SlNatEncoder G0MEQ = (3 ** Refl ** Refl)

public export
G0SlFinDecEncoding : FinDecEncoding Geb0Slice Geb0SliceSz
G0SlFinDecEncoding = NatDecEncoding G0SlFinDecoder G0SlNatEncoder

public export
DecEq Geb0Slice where
  decEq = fdeDecEq G0SlFinDecEncoding

public export
data G0ExpF : SliceEndofunctor Geb0Slice where
  G0ObjRefl : carrier G0OBJ -> G0ExpF carrier G0OEQ

public export
G0ExpFM : SliceEndofunctor Geb0Slice
G0ExpFM = SliceFreeM G0ExpF

public export
G0Exp : SliceObj Geb0Slice
G0Exp = SliceMu G0ExpF

public export
G0Obj : Type
G0Obj = G0Exp G0OBJ

public export
G0Morph : Type
G0Morph = G0Exp G0MORPH

public export
G0OEq : Type
G0OEq = G0Exp G0OEQ

public export
G0MEq : Type
G0MEq = G0Exp G0MEQ

public export
g0ExpFreeCata : SliceFreeFEval G0ExpF
g0ExpFreeCata sv sa subst alg sl (InSlF sl x) = case x of
  InSlV v => subst sl v
  InSlC c => alg sl $ case sl of
    G0OBJ => case c of
      _ impossible
    G0MORPH => case c of
      _ impossible
    G0OEQ => case c of
      G0ObjRefl a => G0ObjRefl $ g0ExpFreeCata sv sa subst alg G0OBJ a
    G0MEQ => case c of
      _ impossible

public export
g0ExpCata : SliceCata G0ExpF
g0ExpCata sa = g0ExpFreeCata (const Void) sa (\_, v => void v)

public export
G0ExpShowAlg : SliceAlg G0ExpF (const String)
G0ExpShowAlg G0OEQ (G0ObjRefl a) = "orefl(" ++ a ++ ")"

public export
g0ExpShow : SliceMorphism G0Exp (const String)
g0ExpShow = g0ExpCata (const String) G0ExpShowAlg

public export
Show G0Obj where
  show = g0ExpShow G0OBJ

public export
Show G0Morph where
  show = g0ExpShow G0MORPH

public export
Show G0OEq where
  show = g0ExpShow G0OEQ

public export
Show G0MEq where
  show = g0ExpShow G0MEQ
