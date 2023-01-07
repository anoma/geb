module LanguageDef.ProgFinSet

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.PolyCat
import public LanguageDef.Atom

%default total

--------------------------------
--------------------------------
---- Bicartesian categories ----
--------------------------------
--------------------------------

public export
data BicartObjF : Type -> Type where
  BCOInitial : BicartObjF a
  BCOTerminal : BicartObjF a
  BCOCoproduct : a -> a -> BicartObjF a
  BCOProduct : a -> a -> BicartObjF a

public export
data BicartObj : Type where
  InBCO : BicartObjF BicartObj -> BicartObj

public export
BCO0 : BicartObj
BCO0 = InBCO BCOInitial

public export
BCO1 : BicartObj
BCO1 = InBCO BCOInitial

public export
BCOC : BicartObj -> BicartObj -> BicartObj
BCOC = InBCO .* BCOCoproduct

public export
BCOP : BicartObj -> BicartObj -> BicartObj
BCOP = InBCO .* BCOProduct

public export
record BCOAlg (a : Type) where
  constructor MkBCOAlg
  bcoAlg0 : a
  bcoAlg1 : a
  bcoAlgC : a -> a -> a
  bcoAlgP : a -> a -> a

public export
bcoCata : BCOAlg a -> BicartObj -> a
bcoCata alg (InBCO BCOInitial) = alg.bcoAlg0
bcoCata alg (InBCO BCOTerminal) = alg.bcoAlg1
bcoCata alg (InBCO (BCOCoproduct x y)) =
  alg.bcoAlgC (bcoCata alg x) (bcoCata alg y)
bcoCata alg (InBCO (BCOProduct x y)) =
  alg.bcoAlgP (bcoCata alg x) (bcoCata alg y)

public export
record BCOCompAlg (a : Type) where
  constructor MkBCOCompAlg
  bcoCompAlg0 : a
  bcoCompAlg1 : a
  bcoCompAlgC : a -> a -> a

public export
bcoCompAlg : BCOCompAlg (a -> a) -> BCOAlg (a -> a)
bcoCompAlg (MkBCOCompAlg a0 a1 ac) =
  MkBCOAlg a0 a1 ac (.)

public export
bcoCompCata : BCOCompAlg (a -> a) -> BicartObj -> a -> a
bcoCompCata = bcoCata . bcoCompAlg

public export
BCOTermAlg : BCOAlg Type
BCOTermAlg = MkBCOAlg Void Unit Either Pair

public export
BCOTerm : BicartObj -> Type
BCOTerm = bcoCata BCOTermAlg

public export
BCOHomAlg : BCOCompAlg (BicartObj -> BicartObj)
BCOHomAlg = MkBCOCompAlg (const BCO1) id (biapp BCOP)

public export
bcoHomObj : BicartObj -> BicartObj -> BicartObj
bcoHomObj = bcoCompCata BCOHomAlg

public export
data PFSObjF : Type -> Type where
  PFSObjBC : BicartObjF a -> PFSObjF a
  PFSHomObj : a -> a -> PFSObjF a

public export
data PFSObj : Type where
  InPFSO : PFSObjF PFSObj -> PFSObj

public export
InPFSBC : BicartObjF PFSObj -> PFSObj
InPFSBC = InPFSO . PFSObjBC

public export
PSF0 : PFSObj
PSF0 = InPFSBC BCOInitial

public export
PSF1 : PFSObj
PSF1 = InPFSBC BCOTerminal

public export
PFSC : PFSObj -> PFSObj -> PFSObj
PFSC = InPFSBC .* BCOCoproduct

public export
PFSP : PFSObj -> PFSObj -> PFSObj
PFSP = InPFSBC .* BCOProduct

-- Endofunctors on the initial bicartesian distributive category (equivalently,
-- the initial bicartesian closed category).
public export
data PFSEFPosBase : Type where
  PPBObj : PFSEFPosBase
  PPBFunc : PFSEFPosBase

public export
data PFSEFF : (PFSEFPosBase -> Type) -> PFSEFPosBase -> Type where
  PPFObj : PFSObjF (a PPBObj) -> PFSEFF a PPBObj
  PPFCovarRep : a PPBObj -> PFSEFF a PPBFunc
  PPFFunc : PFSObjF (a PPBFunc) -> PFSEFF a PPBFunc

public export
data PFSEndoFuncMut : PFSEFPosBase -> Type where
  InPEFM : {0 i : PFSEFPosBase} -> PFSEFF PFSEndoFuncMut i -> PFSEndoFuncMut i

public export
PFSEndoFunc : Type
PFSEndoFunc = PFSEndoFuncMut PPBFunc
