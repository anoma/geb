module LanguageDef.ProgFinSet

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.PolyCat
import public LanguageDef.Atom

%default total

----------------------------------------
----------------------------------------
---- Categories as initial algebras ----
----------------------------------------
----------------------------------------

public export
data CatObj : (obj : Type) -> (obj -> obj -> Type) -> Type where

public export
data CatMorph : (obj : Type) -> (morph : obj -> obj -> Type) ->
    Either obj (CatObj obj morph) ->
    Either obj (CatObj obj morph) ->
    Type where
  CatMorphId :
    (x : obj) -> CatMorph obj morph (Left x) (Left x)
  CatMorphComp :
    {x, y, z : obj} ->
    CatMorph obj morph (Left y) (Left z) ->
    CatMorph obj morph (Left x) (Left y) ->
    CatMorph obj morph (Left x) (Left z)

public export
data InitialObj : (obj : Type) -> (obj -> obj -> Type) -> Type where
  InitialObjSelf : InitialObj obj morph

public export
InitialCatObj : (obj : Type) -> (obj -> obj -> Type) -> Type
InitialCatObj obj morph =
  Either obj (Either (CatObj obj morph) (InitialObj obj morph))

public export
data InitialMorph : (obj : Type) -> (morph : obj -> obj -> Type) ->
    InitialCatObj obj morph -> InitialCatObj obj morph -> Type where
  InitialMorphExFalso :
    (x : obj) ->
    InitialMorph obj morph (Right (Right InitialObjSelf)) (Left x)

public export
data TerminalObj : (obj : Type) -> (obj -> obj -> Type) -> Type where
  TerminalObjSelf : TerminalObj obj morph

public export
TerminalCatObj : (obj : Type) -> (obj -> obj -> Type) -> Type
TerminalCatObj obj morph =
  Either obj (Either (CatObj obj morph) (TerminalObj obj morph))

public export
data TerminalMorph : (obj : Type) -> (morph : obj -> obj -> Type) ->
    TerminalCatObj obj morph -> TerminalCatObj obj morph -> Type where
  TerminalMorphUnique :
    (x : obj) ->
    TerminalMorph obj morph (Left x) (Right (Right TerminalObjSelf))

public export
data InitTermCatObj : (obj : Type) -> (obj -> obj -> Type) -> Type where
  ITCObjSelf : obj -> InitTermCatObj obj morph
  ITCObjCat : CatObj obj morph -> InitTermCatObj obj morph
  ITCObjInit : InitialObj obj morph -> InitTermCatObj obj morph
  ITCObjTerm : TerminalObj obj morph -> InitTermCatObj obj morph

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Interpretation of morphisms as metalanguage natural transformations ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

public export
MorphCovarNT : {obj : Type} -> (obj -> obj -> Type) -> obj -> obj -> Type
MorphCovarNT {obj} morph a b = (x : obj) -> morph b x -> morph a x

public export
MorphContravarNT : {obj : Type} -> (obj -> obj -> Type) -> obj -> obj -> Type
MorphContravarNT {obj} morph a b = (x : obj) -> morph x a -> morph x b

public export
MorphNT : {obj : Type} -> (obj -> obj -> Type) -> obj -> obj -> Type
MorphNT {obj} morph a b =
  Pair (MorphContravarNT {obj} morph a b) (MorphCovarNT {obj} morph a b)

public export
morphComposeNT :
  {obj : Type} -> {morph : obj -> obj -> Type} -> {a, b, c : obj} ->
  MorphNT {obj} morph b c -> MorphNT {obj} morph a b -> MorphNT {obj} morph a c
morphComposeNT {obj} {morph} {a} {b} {c} (g, g') (f, f') =
  (\x => g x . f x, \x => f' x . g' x)

public export
morphNTId :
  {obj : Type} -> {morph : obj -> obj -> Type} ->
  (a : obj) -> MorphNT {obj} morph a a
morphNTId {obj} {morph} a = (\_ => id, \_ => id)

-------------------------------
-------------------------------
---- Types with predicates ----
-------------------------------
-------------------------------

public export
PType : Type
PType = Subset0 Type SliceObj

public export
PBase : PType -> Type
PBase = fst0

public export
0 PPred : (x : PType) -> SliceObj (PBase x)
PPred = snd0

public export
PFunc : PType -> PType -> Type
PFunc x y = PBase x -> PBase y

public export
0 PPres : (x, y : PType) -> SliceObj (PFunc x y)
PPres x y f = (b : PBase x) -> PPred x b -> PPred y (f b)

public export
PMorph : PType -> PType -> Type
PMorph x y = Subset0 (PFunc x y) (PPres x y)

public export
PSigma : PType -> Type
PSigma x = Subset0 (PBase x) (PPred x)

------------------------
------------------------
---- Quotient types ----
------------------------
------------------------

public export
QType : Type
QType = Subset0 Type RelationOn

public export
QBase : QType -> Type
QBase = fst0

public export
0 QRel : (x : QType) -> RelationOn (QBase x)
QRel = snd0

public export
QFunc : QType -> QType -> Type
QFunc x y = QBase x -> QBase y

public export
0 QPres : (x, y : QType) -> SliceObj (QFunc x y)
QPres x y f = (b, b' : QBase x) -> QRel x b b' -> QRel y (f b) (f b')

public export
QMorph : QType -> QType -> Type
QMorph x y = Subset0 (QFunc x y) (QPres x y)

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
PFS0 : PFSObj
PFS0 = InPFSBC BCOInitial

public export
PFS1 : PFSObj
PFS1 = InPFSBC BCOTerminal

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

-- Endofunctors in the initial bicartesian category, indexed by the
-- type of their positions.
public export
data PFSDepObj : PFSObj -> Type where
  PFSDO0 : PFSDepObj PFS0
  PFSDOy : PFSObj -> PFSDepObj PFS1
  PFSDOC : PFSDepObj a -> PFSDepObj b -> PFSDepObj (PFSC a b)
  PFSDOP : PFSDepObj a -> PFSDepObj b -> PFSDepObj (PFSP a b)
