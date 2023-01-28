module LanguageDef.ProgFinSet

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.PolyCat
import public LanguageDef.Atom

%default total

-----------------------------------------------------
-----------------------------------------------------
---- Minimal bicartesian distributive categories ----
-----------------------------------------------------
-----------------------------------------------------

------------------------------------------------------
---- Objects included in any bicartesian category ----
------------------------------------------------------

public export
data BicartDistObjPos : Type where
  BCDObjInitial : BicartDistObjPos
  BCDObjTerminal : BicartDistObjPos
  BCDObjCoproduct : BicartDistObjPos
  BCDObjProduct : BicartDistObjPos

public export
Show BicartDistObjPos where
  show BCDObjInitial = "0"
  show BCDObjTerminal = "1"
  show BCDObjCoproduct = "+"
  show BCDObjProduct = "*"

public export
BCDOPosSz : Nat
BCDOPosSz = 4

public export
BCDOFinDecoder : FinDecoder BicartDistObjPos BCDOPosSz
BCDOFinDecoder FZ = BCDObjInitial
BCDOFinDecoder (FS FZ) = BCDObjTerminal
BCDOFinDecoder (FS (FS FZ)) = BCDObjCoproduct
BCDOFinDecoder (FS (FS (FS FZ))) = BCDObjProduct

public export
BCDONatEncoder : NatEncoder BCDOFinDecoder
BCDONatEncoder BCDObjInitial = (0 ** Refl ** Refl)
BCDONatEncoder BCDObjTerminal = (1 ** Refl ** Refl)
BCDONatEncoder BCDObjCoproduct = (2 ** Refl ** Refl)
BCDONatEncoder BCDObjProduct = (3 ** Refl ** Refl)

public export
BCDOFinDecEncoding : FinDecEncoding BicartDistObjPos BCDOPosSz
BCDOFinDecEncoding = NatDecEncoding BCDOFinDecoder BCDONatEncoder

public export
DecEq BicartDistObjPos where
  decEq = fdeDecEq BCDOFinDecEncoding

public export
BicartDistInitialDir : Type
BicartDistInitialDir = Void

public export
BicartDistTerminalDir : Type
BicartDistTerminalDir = Void

public export
data BicartDistCoproductDir : Type where
  BCDCopL : BicartDistCoproductDir
  BCDCopR : BicartDistCoproductDir

public export
Show BicartDistCoproductDir where
  show BCDCopL = "l"
  show BCDCopR = "r"

public export
Eq BicartDistCoproductDir where
  BCDCopL == BCDCopL = True
  BCDCopR == BCDCopR = True
  _ == _ = False

public export
data BicartDistProductDir : Type where
  BCDProd1 : BicartDistProductDir
  BCDProd2 : BicartDistProductDir

public export
Show BicartDistProductDir where
  show BCDProd1 = "fst"
  show BCDProd2 = "snd"

public export
Eq BicartDistProductDir where
  BCDProd1 == BCDProd1 = True
  BCDProd2 == BCDProd2 = True
  _ == _ = False

public export
BicartDistObjDir : SliceObj BicartDistObjPos
BicartDistObjDir BCDObjInitial = BicartDistInitialDir
BicartDistObjDir BCDObjTerminal = BicartDistTerminalDir
BicartDistObjDir BCDObjCoproduct = BicartDistCoproductDir
BicartDistObjDir BCDObjProduct = BicartDistProductDir

public export
BicartDistObjF : PolyFunc
BicartDistObjF = (BicartDistObjPos ** BicartDistObjDir)

public export
BicartDistObj : Type
BicartDistObj = PolyFuncMu BicartDistObjF

public export
BCDOAlg : SliceObj Type
BCDOAlg = PFAlg BicartDistObjF

public export
bcdoCata : {0 a : Type} -> BCDOAlg a -> BicartDistObj -> a
bcdoCata = pfCata {p=BicartDistObjF}

public export
BCDOShowAlg : BCDOAlg String
BCDOShowAlg BCDObjInitial dir = show BCDObjInitial
BCDOShowAlg BCDObjTerminal dir = show BCDObjTerminal
BCDOShowAlg BCDObjCoproduct dir =
  "[" ++ dir BCDCopL ++ " " ++ show BCDObjCoproduct ++ " " ++ dir BCDCopR ++ "]"
BCDOShowAlg BCDObjProduct dir =
  "(" ++ dir BCDProd1 ++ " " ++ show BCDObjProduct ++ " " ++ dir BCDProd2 ++ ")"

public export
bcdoShow : BicartDistObj -> String
bcdoShow = bcdoCata BCDOShowAlg

public export
Show BicartDistObj where
  show = bcdoShow

public export
BCDOProductAlg : SliceObj Type
BCDOProductAlg = PFProductAlg BicartDistObjF BicartDistObjF

public export
bcdoProductCata : {0 a : Type} ->
  BCDOProductAlg a -> BicartDistObj -> BicartDistObj -> a
bcdoProductCata = pfProductCata {p=BicartDistObjF}

public export
BCDOEqAlg : PFProductBoolAlg BicartDistObjF BicartDistObjF
BCDOEqAlg =
  [
    ((BCDObjInitial, BCDObjInitial) **
     [])
  , ((BCDObjTerminal, BCDObjTerminal) **
     [])
  , ((BCDObjCoproduct, BCDObjCoproduct) **
     [ (BCDCopL, BCDCopL), (BCDCopR, BCDCopR) ])
  , ((BCDObjProduct, BCDObjProduct) **
     [ (BCDProd1, BCDProd1), (BCDProd2, BCDProd2) ]
    )
  ]

public export
bcdoEq : BicartDistObj -> BicartDistObj -> Bool
bcdoEq = pfProductBoolCata decEq decEq BCDOEqAlg

public export
Eq BicartDistObj where
  (==) = bcdoEq

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Terms (global elements) of objects of bicartesian categories ----
----------------------------------------------------------------------
----------------------------------------------------------------------

public export
data BicartDistTermPos : Type where
  BCDTermUnit : BicartDistTermPos
  BCDTermLeft : BicartDistTermPos
  BCDTermRight : BicartDistTermPos
  BCDTermPair : BicartDistTermPos

public export
Show BicartDistTermPos where
  show BCDTermUnit = "_"
  show BCDTermLeft = "l"
  show BCDTermRight = "r"
  show BCDTermPair = ","

public export
BCDTPosSz : Nat
BCDTPosSz = 4

public export
BCDTFinDecoder : FinDecoder BicartDistTermPos BCDTPosSz
BCDTFinDecoder FZ = BCDTermUnit
BCDTFinDecoder (FS FZ) = BCDTermLeft
BCDTFinDecoder (FS (FS FZ)) = BCDTermRight
BCDTFinDecoder (FS (FS (FS FZ))) = BCDTermPair

public export
BCDTNatEncoder : NatEncoder BCDTFinDecoder
BCDTNatEncoder BCDTermUnit = (0 ** Refl ** Refl)
BCDTNatEncoder BCDTermLeft = (1 ** Refl ** Refl)
BCDTNatEncoder BCDTermRight = (2 ** Refl ** Refl)
BCDTNatEncoder BCDTermPair = (3 ** Refl ** Refl)

public export
BCDTFinDecEncoding : FinDecEncoding BicartDistTermPos BCDTPosSz
BCDTFinDecEncoding = NatDecEncoding BCDTFinDecoder BCDTNatEncoder

public export
DecEq BicartDistTermPos where
  decEq = fdeDecEq BCDTFinDecEncoding

public export
BicartDistTermUnitDir : Type
BicartDistTermUnitDir = Void

public export
data BicartDistTermLeftDir : Type where
  BCDTermL : BicartDistTermLeftDir

public export
Show BicartDistTermLeftDir where
  show BCDTermL = show BCDTermLeft

public export
Eq BicartDistTermLeftDir where
  BCDTermL == BCDTermL = True

public export
data BicartDistTermRightDir : Type where
  BCDTermR : BicartDistTermRightDir

public export
Show BicartDistTermRightDir where
  show BCDTermR = show BCDTermRight

public export
Eq BicartDistTermRightDir where
  BCDTermR == BCDTermR = True

public export
data BicartDistTermPairDir : Type where
  BCDTerm1 : BicartDistTermPairDir
  BCDTerm2 : BicartDistTermPairDir

public export
Show BicartDistTermPairDir where
  show BCDTerm1 = show BCDProd1
  show BCDTerm2 = show BCDProd2

public export
Eq BicartDistTermPairDir where
  BCDTerm1 == BCDTerm1 = True
  BCDTerm2 == BCDTerm2 = True
  _ == _ = False

public export
BicartDistTermDir : SliceObj BicartDistTermPos
BicartDistTermDir BCDTermUnit = BicartDistTermUnitDir
BicartDistTermDir BCDTermLeft = BicartDistTermLeftDir
BicartDistTermDir BCDTermRight = BicartDistTermRightDir
BicartDistTermDir BCDTermPair = BicartDistTermPairDir

public export
BicartDistTermF : PolyFunc
BicartDistTermF = (BicartDistTermPos ** BicartDistTermDir)

public export
BicartDistTerm : Type
BicartDistTerm = PolyFuncMu BicartDistTermF

public export
BicartDistTermAlg : SliceObj Type
BicartDistTermAlg = PFAlg BicartDistTermF

public export
bicartDistTermCata : {0 a : Type} -> BicartDistTermAlg a -> BicartDistTerm -> a
bicartDistTermCata = pfCata {p=BicartDistTermF}

public export
BCDTShowAlg : BicartDistTermAlg String
BCDTShowAlg BCDTermUnit dir =
  show BCDTermUnit
BCDTShowAlg BCDTermLeft dir =
  show BCDTermLeft ++ "[" ++ dir BCDTermL ++ "]"
BCDTShowAlg BCDTermRight dir =
  show BCDTermRight ++ "[" ++ dir BCDTermR ++ "]"
BCDTShowAlg BCDTermPair dir =
  "(" ++ dir BCDTerm1 ++ " " ++ show BCDTermPair ++ " " ++ dir BCDTerm2 ++ ")"

public export
bcdtShow : BicartDistTerm -> String
bcdtShow = bicartDistTermCata BCDTShowAlg

public export
Show BicartDistTerm where
  show = bcdtShow

public export
BCDTProductAlg : SliceObj Type
BCDTProductAlg = PFProductAlg BicartDistTermF BicartDistTermF

public export
bcdtProductCata : {0 a : Type} ->
  BCDTProductAlg a -> BicartDistTerm -> BicartDistTerm -> a
bcdtProductCata = pfProductCata {p=BicartDistTermF}

public export
BCDTEqAlg : PFProductBoolAlg BicartDistTermF BicartDistTermF
BCDTEqAlg =
  [
    ((BCDTermUnit, BCDTermUnit) **
     [])
  , ((BCDTermLeft, BCDTermLeft) **
     [ (BCDTermL, BCDTermL) ])
  , ((BCDTermRight, BCDTermRight) **
     [ (BCDTermR, BCDTermR) ])
  , ((BCDTermPair, BCDTermPair) **
     [ (BCDTerm1, BCDTerm1), (BCDTerm2, BCDTerm2) ]
    )
  ]

public export
bcdtEq : BicartDistTerm -> BicartDistTerm -> Bool
bcdtEq = pfProductBoolCata decEq decEq BCDTEqAlg

public export
Eq BicartDistTerm where
  (==) = bcdtEq

public export
BCDObjTermAlg : SliceObj Type
BCDObjTermAlg = PFProductAlg BicartDistTermF BicartDistObjF

public export
bcdObjTermCata : {0 a : Type} ->
  BCDObjTermAlg a -> BicartDistTerm -> BicartDistObj -> a
bcdObjTermCata = pfProductCata {p=BicartDistTermF} {q=BicartDistObjF}

-- Type-checking for terms against objects (determing whether a given general
-- term is a term of a given object).
public export
BicartDistTermCheckAlg : PFProductBoolAlg BicartDistTermF BicartDistObjF
BicartDistTermCheckAlg =
  [
    ((BCDTermUnit, BCDObjTerminal) **
     [])
  , ((BCDTermLeft, BCDObjCoproduct) **
     [(BCDTermL, BCDCopL)])
  , ((BCDTermRight, BCDObjCoproduct) **
     [(BCDTermR, BCDCopR)])
  , ((BCDTermPair, BCDObjProduct) **
     [ (BCDTerm1, BCDProd1), (BCDTerm2, BCDProd2) ]
    )
  ]

public export
bicartDistTermCheck : BicartDistTerm -> BicartDistObj -> Bool
bicartDistTermCheck = pfProductBoolCata decEq decEq BicartDistTermCheckAlg

-- The type-checking allows us to view a checked term as a slice object.
public export
BicartDistTypedTerm : SliceObj BicartDistObj
BicartDistTypedTerm a =
  Refinement {a=BicartDistTerm} (flip bicartDistTermCheck a)

public export
MkBicartDistTypedTerm : {0 o : BicartDistObj} -> (t : BicartDistTerm) ->
  {auto 0 checks : IsTrue (bicartDistTermCheck t o)} -> BicartDistTypedTerm o
MkBicartDistTypedTerm t {checks} = MkRefinement {a=BicartDistTerm} t

-------------------
---- Utilities ----
-------------------

public export
BCDTNumLeavesAlg : BicartDistTermAlg Nat
BCDTNumLeavesAlg BCDTermUnit d = 1
BCDTNumLeavesAlg BCDTermLeft d = d BCDTermL
BCDTNumLeavesAlg BCDTermRight d = d BCDTermR
BCDTNumLeavesAlg BCDTermPair d = d BCDTerm1 + d BCDTerm2

public export
bcdtNumLeaves : BicartDistTerm -> Nat
bcdtNumLeaves = bicartDistTermCata BCDTNumLeavesAlg

public export
BCDTNumInternalNodesAlg : BicartDistTermAlg Nat
BCDTNumInternalNodesAlg BCDTermUnit d = 0
BCDTNumInternalNodesAlg BCDTermLeft d = 1 + d BCDTermL
BCDTNumInternalNodesAlg BCDTermRight d = 1 + d BCDTermR
BCDTNumInternalNodesAlg BCDTermPair d = 1 + d BCDTerm1 + d BCDTerm2

public export
bcdtNumInternalNodes : BicartDistTerm -> Nat
bcdtNumInternalNodes = bicartDistTermCata BCDTNumInternalNodesAlg

public export
BCDTSizeAlg : BicartDistTermAlg Nat
BCDTSizeAlg BCDTermUnit d = 1
BCDTSizeAlg BCDTermLeft d = 1 + d BCDTermL
BCDTSizeAlg BCDTermRight d = 1 + d BCDTermR
BCDTSizeAlg BCDTermPair d = 1 + d BCDTerm1 + d BCDTerm2

public export
bcdtSize : BicartDistTerm -> Nat
bcdtSize = bicartDistTermCata BCDTSizeAlg

public export
BCDTDepthAlg : BicartDistTermAlg Nat
BCDTDepthAlg BCDTermUnit d = 0
BCDTDepthAlg BCDTermLeft d = 1 + d BCDTermL
BCDTDepthAlg BCDTermRight d = 1 + d BCDTermR
BCDTDepthAlg BCDTermPair d = 1 + maximum (d BCDTerm1) (d BCDTerm2)

public export
bcdtDepth : BicartDistTerm -> Nat
bcdtDepth = bicartDistTermCata BCDTDepthAlg

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Morphisms included in any bicartesian distributive category ----
---------------------------------------------------------------------
---------------------------------------------------------------------

public export
data BicartDistReducedMorphPos : Type where
  BCDRMorphId : BicartDistReducedMorphPos
  BCDRMorphAbsurd : BicartDistReducedMorphPos
  BCDRMorphConst : BicartDistReducedMorphPos
  BCDRMorphInjL : BicartDistReducedMorphPos
  BCDRMorphInjR : BicartDistReducedMorphPos
  BCDRMorphCase : BicartDistReducedMorphPos
  BCDRMorphBi : BicartDistReducedMorphPos
  BCDRMorphProj1 : BicartDistReducedMorphPos
  BCDRMorphProj2 : BicartDistReducedMorphPos
  BCDRMorphDist : BicartDistReducedMorphPos

public export
Eq BicartDistReducedMorphPos where
  BCDRMorphId == BCDRMorphId = True
  BCDRMorphAbsurd == BCDRMorphAbsurd = True
  BCDRMorphConst == BCDRMorphConst = True
  BCDRMorphInjL == BCDRMorphInjL = True
  BCDRMorphInjR == BCDRMorphInjR = True
  BCDRMorphCase == BCDRMorphCase = True
  BCDRMorphBi == BCDRMorphBi = True
  BCDRMorphProj1 == BCDRMorphProj1 = True
  BCDRMorphProj2 == BCDRMorphProj2 = True
  BCDRMorphDist == BCDRMorphDist = True
  _ == _ = False

public export
data BicartDistReducedMorphDirObj : SliceObj BicartDistReducedMorphPos where
  BCDRMorphIdDir : BicartDistReducedMorphDirObj BCDRMorphId
  BCDRMorphAbsurdDom : BicartDistReducedMorphDirObj BCDRMorphAbsurd
  BCDRMorphAbsurdCod : BicartDistReducedMorphDirObj BCDRMorphAbsurd
  BCDRMorphConstDom : BicartDistReducedMorphDirObj BCDRMorphConst
  BCDRMorphConstCod : BicartDistReducedMorphDirObj BCDRMorphConst
  BCDRMorphInjLDom : BicartDistReducedMorphDirObj BCDRMorphInjL
  BCDRMorphInjLCodR : BicartDistReducedMorphDirObj BCDRMorphInjL
  BCDRMorphInjRDom : BicartDistReducedMorphDirObj BCDRMorphInjR
  BCDRMorphInjRCodL : BicartDistReducedMorphDirObj BCDRMorphInjR
  BCDRMorphCaseDomL : BicartDistReducedMorphDirObj BCDRMorphCase
  BCDRMorphCaseDomR : BicartDistReducedMorphDirObj BCDRMorphCase
  BCDRMorphCaseCod : BicartDistReducedMorphDirObj BCDRMorphCase
  BCDRMorphBiDom : BicartDistReducedMorphDirObj BCDRMorphBi
  BCDRMorphBiCodL : BicartDistReducedMorphDirObj BCDRMorphBi
  BCDRMorphBiCodR : BicartDistReducedMorphDirObj BCDRMorphBi
  BCDRMorphProj1DomR : BicartDistReducedMorphDirObj BCDRMorphProj1
  BCDRMorphProj1Cod : BicartDistReducedMorphDirObj BCDRMorphProj1
  BCDRMorphProj2DomL : BicartDistReducedMorphDirObj BCDRMorphProj2
  BCDRMorphProj2Cod : BicartDistReducedMorphDirObj BCDRMorphProj2
  BCDRMorphDistDom1 : BicartDistReducedMorphDirObj BCDRMorphDist
  BCDRMorphDistDom2L : BicartDistReducedMorphDirObj BCDRMorphDist
  BCDRMorphDistDom2R : BicartDistReducedMorphDirObj BCDRMorphDist

public export
data BicartDistReducedMorphDirTerm : SliceObj BicartDistReducedMorphPos where
  BCDRMorphTerm : BicartDistReducedMorphDirTerm BCDRMorphConst

public export
data BicartDistReducedMorphDirMorph : SliceObj BicartDistReducedMorphPos where
  BCDRMorphContra : BicartDistReducedMorphDirMorph BCDRMorphAbsurd
  BCDRMorphCases : BicartDistReducedMorphDirMorph BCDRMorphCase
  BCDRMorphComponents : BicartDistReducedMorphDirMorph BCDRMorphBi

public export
data BicartDistReducedMorphPosBase : Type where
  BCDRMorphPosMorph : BicartDistReducedMorphPosBase
  BCDRMorphPosObj : BicartDistReducedMorphPosBase
  BCDRMorphPosTerm : BicartDistReducedMorphPosBase

public export
BicartDistReducedMorphPosDep : SliceObj BicartDistReducedMorphPosBase
BicartDistReducedMorphPosDep BCDRMorphPosMorph = BicartDistReducedMorphPos
BicartDistReducedMorphPosDep BCDRMorphPosObj = BicartDistObjPos
BicartDistReducedMorphPosDep BCDRMorphPosTerm = BicartDistTermPos

public export
BicartDistReducedMorphDirDep : SliceObj (Sigma BicartDistReducedMorphPosDep)
BicartDistReducedMorphDirDep (BCDRMorphPosMorph ** i) =
  BicartDistReducedMorphDirMorph i
BicartDistReducedMorphDirDep (BCDRMorphPosObj ** i) =
  BicartDistObjDir i
BicartDistReducedMorphDirDep (BCDRMorphPosTerm ** i) =
  BicartDistTermDir i

public export
BicartDistReducedMorphIdSlice :
  SlicePolyEndoFuncId BicartDistReducedMorphPosBase
BicartDistReducedMorphIdSlice =
  (BicartDistReducedMorphPosDep ** BicartDistReducedMorphDirDep)

public export
BicartDistUnrefinedReducedMorphSPF :
  SlicePolyEndoFunc BicartDistReducedMorphPosBase
BicartDistUnrefinedReducedMorphSPF =
  SlicePolyEndoFuncFromId BicartDistReducedMorphIdSlice

public export
BicartDistUnrefinedReducedMorphSlice : SliceObj BicartDistReducedMorphPosBase
BicartDistUnrefinedReducedMorphSlice = SPFMu BicartDistUnrefinedReducedMorphSPF

public export
BicartDistUnrefinedReducedMorph : Type
BicartDistUnrefinedReducedMorph =
  BicartDistUnrefinedReducedMorphSlice BCDRMorphPosMorph

----------------------------------------------------------------------------
----------------------------------------------------------------------------
---- Polynomial functors in locally bicartesian distributive categories ----
----------------------------------------------------------------------------
----------------------------------------------------------------------------

public export
data PolyBCDPosPoly : Type where
  PolyBCDPosPF : BicartDistObjPos -> PolyBCDPosPoly
  PolyBCDPosSlice : BicartDistObjPos -> PolyBCDPosPoly

public export
data PolyBCDPosBase : Type where
  PolyBCDSourceObj : PolyBCDPosBase
  PolyBCDPoly : PolyBCDPosBase

public export
PolyBCDPosDep : SliceObj PolyBCDPosBase
PolyBCDPosDep PolyBCDSourceObj = BicartDistObjPos
PolyBCDPosDep PolyBCDPoly = PolyBCDPosPoly

public export
PolyBCDPos : Type
PolyBCDPos = DPair PolyBCDPosBase PolyBCDPosDep

---------------------------------
---------------------------------
---- Programmer's finite set ----
---------------------------------
---------------------------------

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

---------------------
---------------------
---- Experiments ----
---------------------
---------------------

public export
data OmType : Type where
  OmObj : OmType
  OmObjPair : OmType
  OmMorph : OmType

public export
data OmObjPos : Type where
  Om0 : OmObjPos
  Om1 : OmObjPos
  OmP : OmObjPos
  OmC : OmObjPos

public export
data OmObjDir : SliceObj (OmType, OmObjPos) where
  OmObj1 : OmObjDir (OmObj, OmP)
  OmObj2 : OmObjDir (OmObj, OmP)
  OmObjL : OmObjDir (OmObj, OmC)
  OmObjR : OmObjDir (OmObj, OmC)

public export
data OmObjPairPos : Type where
  OmOPP : OmObjPairPos

public export
data OmObjPairDir : SliceObj (OmType, OmObjPairPos) where
  OmOPP1 : OmObjPairDir (OmObj, OmOPP)
  OmOPP2 : OmObjPairDir (OmObj, OmOPP)

public export
data OmMorphPosMorph : Type where
  OmId : OmMorphPosMorph
  OmComp : OmMorphPosMorph
  OmCase : OmMorphPosMorph

public export
record OmMorphPos where
  constructor MkOmMorphPos
  OMPParam : OmObjPairPos
  OMPMorph : OmMorphPosMorph

public export
OmMorphDirParam : SliceObj (OmType, OmObjPairPos)
OmMorphDirParam = OmObjPairDir

public export
data OmMorphDirMorph : SliceObj (OmType, OmMorphPosMorph) where
  OmIdObj : OmMorphDirMorph (OmObj, OmId)
  OmMorphPrec : OmMorphDirMorph (OmMorph, OmComp)
  OmMorphMid : OmMorphDirMorph (OmObj, OmComp)
  OmMorphAnt : OmMorphDirMorph (OmMorph, OmComp)
  OmMorphL : OmMorphDirMorph (OmMorph, OmCase)
  OmMorphR : OmMorphDirMorph (OmMorph, OmCase)

public export
OmMorphDir : SliceObj (OmType, OmMorphPos)
OmMorphDir (ty, i) =
  (OmMorphDirParam (ty, OMPParam i), OmMorphDirMorph (ty, OMPMorph i))

public export
OmPos : OmType -> Type
OmPos OmObj = OmObjPos
OmPos OmObjPair = OmObjPairPos
OmPos OmMorph = OmMorphPos

public export
OmDirDep : (ty : OmType) -> SliceObj (OmType, OmPos ty)
OmDirDep OmObj = OmObjDir
OmDirDep OmObjPair = OmObjPairDir
OmDirDep OmMorph = OmMorphDir

public export
OmDir : SliceObj (DPair OmType OmPos, OmType)
OmDir ((posty ** i), dirty) = OmDirDep posty (dirty, i)

public export
OmSPF'' : SlicePolyEndoFunc'' OmType
OmSPF'' = (OmPos ** OmDir .* MkPair)

public export
OmSPF : SlicePolyEndoFunc OmType
OmSPF = SPFFromPrimes OmSPF''

public export
OmMu : SliceObj OmType
OmMu = SPFMu OmSPF

public export
OmObjMu : Type
OmObjMu = OmMu OmObj

public export
OmObjPairMu : Type
OmObjPairMu = OmMu OmObjPair

public export
OmMorphMu : Type
OmMorphMu = OmMu OmMorph

public export
OmCheckAlgCtx : SliceObj OmType
OmCheckAlgCtx OmObj = Bool
OmCheckAlgCtx OmObjPair = Bool
OmCheckAlgCtx OmMorph = Bool

public export
OmCheckAlg : SPFAlg OmSPF OmCheckAlgCtx
OmCheckAlg OmObj (Om0 ** d) = True
OmCheckAlg OmObj (Om1 ** d) = True
OmCheckAlg OmObj (OmP ** d) = d (OmObj ** OmObj1) && d (OmObj ** OmObj2)
OmCheckAlg OmObj (OmC ** d) = d (OmObj ** OmObjL) && d (OmObj ** OmObjR)
OmCheckAlg OmObjPair (OmOPP ** d) = d (OmObj ** OmOPP1) && d (OmObj ** OmOPP2)
OmCheckAlg OmMorph (MkOmMorphPos OmOPP OmId ** d) =
  -- d (OmObj ** OmIdObj) &&
  -- dom/cod equals params
  ?OmCheckAlg_hole_id
OmCheckAlg OmMorph (MkOmMorphPos OmOPP OmComp ** d) =
  -- d (OmMorph ** OmMorphPrec) &&
{-
  d (OmMorph ** OmMorphAnt) &&
  d (OmObj ** OmMorphMid) &&
  -- XXX dom/cod match mid; cod/dom match params
  -}
  ?OmCheckAlg_hole_comp
OmCheckAlg OmMorph (MkOmMorphPos OmOPP OmCase ** d) =
{-
  d (OmMorph ** OmMorphL) &&
  d (OmMorph ** OmMorphR) &&
  -- XXX doms match param; cods match each other and param
  -}
  ?OmCheckAlg_hole_case

public export
omCheck : (i : OmType) -> OmMu i -> Bool
omCheck OmObj = spfCata OmCheckAlg OmObj
omCheck OmObjPair = spfCata OmCheckAlg OmObjPair
omCheck OmMorph = spfCata OmCheckAlg OmMorph
