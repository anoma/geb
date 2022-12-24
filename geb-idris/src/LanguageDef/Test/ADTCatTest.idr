module LanguageDef.Test.ADTCatTest

import Test.TestLibrary
import LanguageDef.ADTCat

%default total

---------------
---------------
---- PolyF ----
---------------
---------------

polybool : PolyMu
polybool = Poly1 $+ Poly1

polyfnat : PolyMu
polyfnat = Poly1 $+ PolyI

polyf0 : PolyMu
polyf0 = (polyfnat $. Poly1) $*^ 5

polyf1 : PolyMu
polyf1 = (Poly1 $+ PolyI $*^ 2) $.^ 3

polyf2 : PolyMu
polyf2 = polyf0 $.^ 0

Polyf0f : Type -> Type
Polyf0f = MetaPolyFMetaF polyf0

Polyf1f : Type -> Type
Polyf1f = MetaPolyFMetaF polyf1

Polyf2f : Type -> Type
Polyf2f = MetaPolyFMetaF polyf2

Polyf0t : Type
Polyf0t = ConstComponent polyf0

Polyf1t : Type
Polyf1t = ConstComponent polyf1

Polyf2t : Type
Polyf2t = ConstComponent polyf2

polyf0i : Polyf0t
polyf0i = (Left (), Left (), Right (), Left (), Right ())

polyf2i : Not Polyf2t
polyf2i = id

PolyFreeNat : (0 _ : Type) -> Type
PolyFreeNat = MetaPolyFreeM polyfnat

PolyNat : Type
PolyNat = MetaPolyMu polyfnat

polyFNatT0 : PolyFreeNat Nat
polyFNatT0 = InFVar 7

polyFNatT1 : PolyFreeNat Nat
polyFNatT1 = InFCom $ Left ()

polyFNatT2 : PolyFreeNat Nat
polyFNatT2 = InFCom $ Right $ InFVar 5

polyFNatT3 : PolyFreeNat Nat
polyFNatT3 = InFCom $ Right $ InFCom $ Left ()

polyFNatT4 : PolyFreeNat Nat
polyFNatT4 = InFCom $ Right $ InFCom $ Right $ InFVar 3

polyFNatT5 : PolyFreeNat Nat
polyFNatT5 = InFCom $ Right $ InFCom $ Right $ InFCom $ Left ()

polyFNatT6 : PolyFreeNat Nat
polyFNatT6 = InFCom $ Right $ InFCom $ Right $ InFCom $ Right $ InFCom $ Left ()

polynatT0 : PolyNat
polynatT0 = InFCom $ Left ()

polynatT1 : PolyNat
polynatT1 = InFCom $ Right $ InFCom $ Left ()

polynatT2 : PolyNat
polynatT2 = InFCom $ Right $ InFCom $ Right $ InFCom $ Left ()

polyNatIter : Nat -> PolyMu
polyNatIter = ($.^) polyfnat

polyNatIterFixed : Nat -> PolyMu
polyNatIterFixed n = polyNatIter n $. Poly0

PolyNatIter : Nat -> Type
PolyNatIter = ConstComponent . polyNatIter

pniterT0 : Not $ PolyNatIter 0
pniterT0 = id

pniterT1 : PolyNatIter 1
pniterT1 = ()

pniterT2 : PolyNatIter 2
pniterT2 = Left ()

pniterT3 : PolyNatIter 2
pniterT3 = Right ()

pniterT4 : PolyNatIter 3
pniterT4 = Left ()

pniterT5 : PolyNatIter 3
pniterT5 = Right $ Left ()

pniterT6 : PolyNatIter 3
pniterT6 = Right $ Right ()

pniterT7 : PolyNatIter 4
pniterT7 = Left ()

pniterT8 : PolyNatIter 4
pniterT8 = Right $ Left ()

pniterT9 : PolyNatIter 4
pniterT9 = Right $ Right $ Left ()

pniterT10 : PolyNatIter 4
pniterT10 = Right $ Right $ Right ()

polyfeqT0 : Assertion
polyfeqT0 = Assert $ polyfnat /= polyNatIter 0

polyfeqT1 : Assertion
polyfeqT1 = Assert $ polyfnat == polyNatIter 1

polyfeqT2 : Assertion
polyfeqT2 = Assert $ polyfnat /= polyNatIter 2

polyHomBoolF0 : PolyMu
polyHomBoolF0 = PolyHomObj polybool polyf0

polyCardT0 : Assertion
polyCardT0 = Assert $
  polyTCard polyHomBoolF0 == power (polyTCard polyf0) (polyTCard polybool)

polyHomId4Id : PolyMu
polyHomId4Id = PolyHomObj PolyI (4 $:* PolyI)

twoBits : PolyMu
twoBits = polybool $* polybool

polyHomId4Id' : PolyMu
polyHomId4Id' = PolyHomObj PolyI (twoBits $* PolyI)

polyHom4IdId : PolyMu
polyHom4IdId = PolyHomObj (4 $:* PolyI) PolyI

polyHom4IdId' : PolyMu
polyHom4IdId' = PolyHomObj (twoBits $* PolyI) PolyI

polyDepth3BinTree : PolyMu
polyDepth3BinTree = polyf1

polyDepth3BinTreeFixed : PolyMu
polyDepth3BinTreeFixed = polyDepth3BinTree $. Poly0

pmMaybe : PolyMu
pmMaybe = Poly1 $+ PolyI

pmMaybeSq : PolyMu
pmMaybeSq = pmMaybe $*^ 2

pmMaybeSqFactored : PolyMu
pmMaybeSqFactored = Poly1 $+ PolyI $+ PolyI $+ PolyI $*^ 2

pmMaybeSqAppBool : PolyMu
pmMaybeSqAppBool = pmMaybeSq $. polybool

pmMaybeSqBoolAlg : PolyMu
pmMaybeSqBoolAlg = PolyHomObj pmMaybeSqAppBool polybool

pmFinObj : PolyMu
pmFinObj = 2 $:* Poly1 $+ 2 $:* PolyI

pmFinObjTermPair : PolyMu
pmFinObjTermPair = pmFinObj $* pmMaybeSq

pmFinObjTermPairToBool : PolyMu
pmFinObjTermPairToBool = PolyHomObj pmFinObjTermPair polybool

pmMaybeSqIter : Nat -> PolyMu
pmMaybeSqIter = ($.^) pmMaybeSq

showPMIter : Nat -> IO ()
showPMIter n = do
  putStrLn $ "pmMaybeSqIter " ++ show n ++ " = " ++
    show (pmMaybeSqIter n)
  putStrLn $ "shape(pmMaybeSqIter " ++ show n ++ ") = " ++
    showPolyShape (pmMaybeSqIter n)
  putStrLn $ "npos(pmMaybeSqIter " ++ show n ++ ") = " ++
    show (polyNPos $ pmMaybeSqIter n)

pmMaybeSqRaise : Nat -> PolyMu
pmMaybeSqRaise = ($*^) pmMaybeSq

showPMRaise : Nat -> IO ()
showPMRaise n = do
  putStrLn $ "pmMaybeSqRaise " ++ show n ++ " = " ++
    show (pmMaybeSqRaise n)
  putStrLn $ "shape(pmMaybeSqRaise " ++ show n ++ ") = " ++
    showPolyShape (pmMaybeSqRaise n)
  putStrLn $ "npos(pmMaybeSqRaise " ++ show n ++ ") = " ++
    show (polyNPos $ pmMaybeSqRaise n)

---------------------------
---------------------------
---- Monads / comonads ----
---------------------------
---------------------------

-----------------------
---- Free identity ----
-----------------------

WriterNatString : Type
WriterNatString = pfFreeIdF String

MkWNS : Nat -> String -> WriterNatString
MkWNS Z s = (InPVar () ** const s)
MkWNS (S n) s with (MkWNS n s)
  MkWNS (S n) s | (i ** strs) = (InPCom () (const i) ** strs . snd)

wns3 : WriterNatString
wns3 = MkWNS 3 "wns3"

wnsNatAlg : PFTranslateAlg PFIdentityArena String Nat
wnsNatAlg (PFVar s) dn = 0
wnsNatAlg (PFCom ()) dn = S $ dn ()

wnsNat : WriterNatString -> Nat
wnsNat = pfFreeCata wnsNatAlg

wnsStrAlg : PFTranslateAlg PFIdentityArena String String
wnsStrAlg (PFVar s) ds = s
wnsStrAlg (PFCom ()) ds = ds ()

wnsStr : WriterNatString -> String
wnsStr = pfFreeCata wnsStrAlg

Show WriterNatString where
  show wns = "(" ++ show (wnsNat wns) ++ ", " ++ wnsStr wns ++ ")"

wns3s : String
wns3s = show wns3

-------------------------
---- Cofree identity ----
-------------------------

StreamNatGen : PolyFunc
StreamNatGen = PFIdentityArena

StreamNatGenPos : Type
StreamNatGenPos = pfPos StreamNatGen

StreamNatGenDir : StreamNatGenPos -> Type
StreamNatGenDir = pfDir {p=StreamNatGen}

StreamNatF : PolyFunc
StreamNatF = PolyFuncCofreeCM PFIdentityArena

StreamNatFPos : Type
StreamNatFPos = pfPos StreamNatF

StreamNatFDir : StreamNatFPos -> Type
StreamNatFDir = pfDir {p=StreamNatF}

StreamType : Type
StreamType = Nat

StreamNat : Type
StreamNat = InterpPolyFunc StreamNatF StreamType

StreamRet : Type
StreamRet = (StreamType, StreamNat)

mutual
  partial
  sn0 : StreamNat
  sn0 = (InPFM (PFNode () ()) (const $ fst sn0) ** sn0Dir sn0)

  partial
  sn0Dir :
    (sn : StreamNat) ->
    Either () (d : () ** StreamNatFDir (fst sn)) ->
    StreamType
  sn0Dir sn (Left ()) = 0
  sn0Dir (InPFM (PFNode () ()) sn' ** d') (Right (() ** x)) =
    S $ sn0Dir (sn' () ** \x => d' $ Right (() ** x)) $
      case x of
        Left () => Left ()
        Right (() ** x') => Right (() ** x')

partial
getSN : StreamNat -> StreamNatGenPos -> StreamRet
getSN (InPFM (PFNode () ()) di' ** d') =
  \u => case u of
    () => getSN (di' () ** \pfc => d' $ Right (() ** pfc)) ()

partial
sn0_0 : StreamRet
sn0_0 = getSN sn0 ()

------------------------
------------------------
---- Test utilities ----
------------------------
------------------------

showTerminated :
  {0 a : Type} -> (String -> a -> IO ()) -> (String, a) -> IO ()
showTerminated showFull (name, t) = do
  showFull name t
  putStrLn "----"

showList :
  {0 a : Type} -> (String -> a -> IO ()) -> List (String, a) -> IO ()
showList showFull [] = pure ()
showList showFull ts@(_ :: _) = do
  putStrLn "----"
  foldlM (const $ showTerminated showFull) () ts

-------------------------------
-------------------------------
---- Generalized ADT terms ----
-------------------------------
-------------------------------

termShowFull : String -> TermMu -> IO ()
termShowFull name term = do
  putStrLn $ name ++ " = " ++ show term
  putStrLn $ "size[" ++ name ++ "] = " ++ show (termSize term)
  putStrLn $ "depth[" ++ name ++ "] = " ++ show (termDepth term)

termShowFullTerminated : (String, TermMu) -> IO ()
termShowFullTerminated = showTerminated termShowFull

termShowFullList : List (String, TermMu) -> IO ()
termShowFullList = showList termShowFull

adtT1 : TermMu
adtT1 = InProd []

adtT2 : TermMu
adtT2 = InNat 0 adtT1

adtT3 : TermMu
adtT3 = InProd [adtT1, adtT2]

adtT4 : TermMu
adtT4 = InAtom PRODUCT 1 adtT3

adtT5 : TermMu
adtT5 = InNat 2 adtT3

adtT6 : TermMu
adtT6 = InProd [adtT4, adtT5]

--------------
--------------
---- STMu ----
--------------
--------------

stShowFull : String -> STMu -> IO ()
stShowFull name st = do
  putStrLn $ name ++ " = " ++ show st
  putStrLn $ "numLeaves[" ++ name ++ "] = " ++
    show (stNumLeaves st)
  putStrLn $ "numInternalNodes[" ++ name ++ "] = " ++
    show (stNumInternalNodes st)
  putStrLn $ "size[" ++ name ++ "] = " ++ show (stSize st)
  putStrLn $ "depth[" ++ name ++ "] = " ++ show (stDepth st)

stShowFullSTerminated : (String, STMu) -> IO ()
stShowFullSTerminated = showTerminated stShowFull

stShowFullList : List (String, STMu) -> IO ()
stShowFullList = showList stShowFull

stMu1 : STMu
stMu1 = InSTPair (InSTLeft InSTUnit) (InSTRight InSTUnit)

stMu2 : STMu
stMu2 = InSTPair (InSTLeft InSTUnit) (InSTRight $ InSTLeft $ InSTUnit)

stMu3 : STMu
stMu3 = InSTPair InSTUnit (InSTPair (InSTRight (InSTLeft InSTUnit)) InSTUnit)

stMu1EqSelf : Assertion
stMu1EqSelf = Assert $ stMu1 == stMu1

stMu2EqSelf : Assertion
stMu2EqSelf = Assert $ stMu2 == stMu2

stMu1NotEq2 : Assertion
stMu1NotEq2 = Assert $ stMu1 /= stMu2

--------------
--------------
---- SOMu ----
--------------
--------------

soShowFull : String -> SOMu -> IO ()
soShowFull name so = do
  putStrLn $ name ++ " = " ++ show so
  putStrLn $ "size[" ++ name ++ "] = " ++ show (soSize so)
  putStrLn $ "depth[" ++ name ++ "] = " ++ show (soDepth so)
  putStrLn $ "card[" ++ name ++ "] = " ++ show (soCard so)

soShowFullTerminated : (String, SOMu) -> IO ()
soShowFullTerminated = showTerminated soShowFull

soShowFullList : List (String, SOMu) -> IO ()
soShowFullList = showList soShowFull

soMu1 : SOMu
soMu1 = InSO0

soMu2 : SOMu
soMu2 = InSO1

soMu3 : SOMu
soMu3 = InSOC soMu1 soMu2

soMu4 : SOMu
soMu4 = InSOP soMu1 soMu2

soMu5 : SOMu
soMu5 = InSOP InSO1 (InSOP (InSOC InSO1 (InSOC InSO1 InSO1)) InSO1)

soMu1EqSelf : Assertion
soMu1EqSelf = Assert $ soMu1 == soMu1

soMu2EqSelf : Assertion
soMu2EqSelf = Assert $ soMu2 == soMu2

soMu3EqSelf : Assertion
soMu3EqSelf = Assert $ soMu3 == soMu3

soMu4EqSelf : Assertion
soMu4EqSelf = Assert $ soMu4 == soMu4

soMu1Neq2 : Assertion
soMu1Neq2 = Assert $ soMu1 /= soMu2

soMu3Neq4 : Assertion
soMu3Neq4 = Assert $ soMu3 /= soMu4

--------------------------------
--------------------------------
---- Term/type interactions ----
--------------------------------
--------------------------------

public export
soTermCheck1 : Assertion
soTermCheck1 = Assert $ not $ soTermCheck InSO0 InSTUnit

public export
soTermCheck2 : Assertion
soTermCheck2 = Assert $ not $ soTermCheck InSO0 (InSTLeft InSTUnit)

public export
soTermCheck3 : Assertion
soTermCheck3 = Assert $ not $ soTermCheck InSO0 (InSTRight InSTUnit)

public export
soTermCheck4 : Assertion
soTermCheck4 = Assert $ not $ soTermCheck InSO0 (InSTPair InSTUnit InSTUnit)

public export
soTermCheck5 : Assertion
soTermCheck5 = Assert $ soTermCheck InSO1 InSTUnit

public export
soTermCheck6 : Assertion
soTermCheck6 = Assert $ not $ soTermCheck InSO1 (InSTLeft InSTUnit)

public export
soTermCheck7 : Assertion
soTermCheck7 = Assert $ not $ soTermCheck InSO1 (InSTRight InSTUnit)

public export
soTermCheck8 : Assertion
soTermCheck8 = Assert $ not $ soTermCheck InSO1 (InSTPair InSTUnit InSTUnit)

public export
soTermCheck9 : Assertion
soTermCheck9 = Assert $ not $ soTermCheck (InSOC InSO1 InSO0) InSTUnit

public export
soTermCheck10 : Assertion
soTermCheck10 =
  Assert $ soTermCheck (InSOC InSO1 InSO0) (InSTLeft InSTUnit)

public export
soTermCheck11 : Assertion
soTermCheck11 =
  Assert $ not $ soTermCheck (InSOC InSO1 InSO0) (InSTRight InSTUnit)

public export
soTermCheck12 : Assertion
soTermCheck12 =
  Assert $ not $ soTermCheck (InSOC InSO1 InSO0) (InSTPair InSTUnit InSTUnit)

public export
soTermCheck13 : Assertion
soTermCheck13 = Assert $ not $ soTermCheck (InSOP InSO1 InSO1) InSTUnit

public export
soTermCheck14 : Assertion
soTermCheck14 =
  Assert $ not $ soTermCheck (InSOP InSO1 InSO1) (InSTLeft InSTUnit)

public export
soTermCheck15 : Assertion
soTermCheck15 =
  Assert $ not $ soTermCheck (InSOP InSO1 InSO1) (InSTRight InSTUnit)

public export
soTermCheck16 : Assertion
soTermCheck16 =
  Assert $ soTermCheck (InSOP InSO1 InSO1) (InSTPair InSTUnit InSTUnit)

public export
soTermCheck17 : Assertion
soTermCheck17 =
  Assert $ not $ soTermCheck
    (InSOP InSO1 InSO1) (InSTPair (InSTLeft InSTUnit) InSTUnit)

public export
soTermCheck18 : Assertion
soTermCheck18 =
  Assert $ not $ soTermCheck
    (InSOP InSO1 InSO1) (InSTPair (InSTLeft InSTUnit) InSTUnit)

public export
soTermCheck19 : Assertion
soTermCheck19 =
  Assert $ not $ soTermCheck
    soMu5
    (InSTPair (InSTLeft InSTUnit) InSTUnit)

public export
soTermCheck20 : Assertion
soTermCheck20 = Assert $ soTermCheck soMu5 stMu3

public export
stt3 : STTyped ADTCatTest.soMu5
stt3 = MkSTTyped {so=soMu5} stMu3

public export
soMuBool : SOMu
soMuBool = InSOC InSO1 InSO1

public export
soMuThree : SOMu
soMuThree = InSOC InSO1 soMuBool

public export
soMuBinFour : SOMu
soMuBinFour = InSOP soMuBool soMuBool

public export
soMuBinFive : SOMu
soMuBinFive = InSOC InSO1 soMuBinFour

public export
soHomBoolBool : SOMu
soHomBoolBool = soHomObj soMuBool soMuBool

public export
soHomThreeThree : SOMu
soHomThreeThree = soHomObj soMuThree soMuThree

public export
soHomFourFive : SOMu
soHomFourFive = soHomObj soMuBinFour soMuBinFive

public export
soHomFiveFour : SOMu
soHomFiveFour = soHomObj soMuBinFive soMuBinFour

public export
soHomFourFiveCardCorrect : Assertion
soHomFourFiveCardCorrect = Assert $ soCard soHomFourFive == 625

public export
soHomFiveFourCardCorrect : Assertion
soHomFiveFourCardCorrect = Assert $ soCard soHomFiveFour == 1024

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
adtCatTest : IO ()
adtCatTest = do
  putStrLn ""
  putStrLn "================="
  putStrLn "Begin ADTCatTest:"
  putStrLn "-----------------"
  putStrLn ""
  putStrLn "---------------"
  putStrLn "---- PolyF ----"
  putStrLn "---------------"
  putStrLn $ "polyf0 = " ++ show polyf0
  putStrLn $ "distrib[polyf0] = " ++ show (polyDistrib polyf0)
  putStrLn $ "position-list[polyf0] = " ++ polyPosShow polyf0
  putStrLn $ "poly-list[polyf0] = " ++ show (toPolyShape polyf0)
  putStrLn $ "poly-list[polyf1] = " ++ show (toPolyShape polyf1)
  putStrLn $ "pnitert10 = " ++ show pniterT10
  putStrLn $ "card[polyf0] = " ++ show (polyTCard polyf0)
  putStrLn $ "card[polybool] = " ++ show (polyTCard polybool)
  putStrLn $ "(polybool -> polyf0) = " ++ show polyHomBoolF0
  putStrLn $ "card[polybool -> polyf0] = " ++ show (polyTCard polyHomBoolF0)
  putStrLn $ "(id -> 4 * id) = " ++ show polyHomId4Id
  putStrLn $ "(id -> (2 * 2) * id) = " ++ show polyHomId4Id'
  putStrLn $ "(4 * id -> id) = " ++ show polyHom4IdId
  putStrLn $ "((2 * 2) * id -> id) = " ++ show polyHom4IdId'
  putStrLn $ "polyDepth3BT = " ++ show (toPolyShape polyDepth3BinTree)
  putStrLn $ "card[polyDepth3BT,0] = " ++ show (polyTCard polyDepth3BinTree)
  putStrLn $ "depth4Nat = " ++ show (polyNatIter 4)
  putStrLn $ "card[depth4Nat] = " ++ show (polyTCard (polyNatIter 4))
  putStrLn $ "card[depth4Nat -> polyDepth3BT] = " ++
    show (polyTCard $ PolyHomObj (polyNatIter 4) (polyDepth3BinTree))
  putStrLn $ "card[polyDepth3BT -> depth4Nat] = " ++
    show (polyTCard $ PolyHomObj (polyDepth3BinTree) (polyNatIter 4))
  putStrLn $ "hom[polyDepth3BT -> depth4Nat] = " ++
    showPolyShape (PolyHomObj (polyDepth3BinTree) (polyNatIter 4))
  putStrLn $ "polyDepth3BTFixed = " ++ show polyDepth3BinTreeFixed
  putStrLn $ "card[polyDepth3BTFixed,0] = "
    ++ show (polyTCard polyDepth3BinTreeFixed)
  putStrLn $ "depth4NatFixed = " ++ show (polyNatIterFixed 4)
  putStrLn $ "card[depth4NatFixed] = " ++ show (polyTCard (polyNatIterFixed 4))
  putStrLn $ "card[depth4NatFixed -> polyDepth3BTFixed] = " ++
    show (polyTCard $ PolyHomObj (polyNatIterFixed 4) (polyDepth3BinTreeFixed))
  putStrLn $ "card[polyDepth3BTFixed -> depth4NatFixed] = " ++
    show (polyTCard $ PolyHomObj (polyDepth3BinTreeFixed) (polyNatIterFixed 4))
  putStrLn $ "first compose = " ++ show ((4 $:* PolyI) $. (PolyI $+ Poly1))
  putStrLn $ "second compose = " ++
    show ((twoBits $* PolyI) $. (PolyI $+ Poly1))
  putStrLn $ "exercise 5.8.3 first part unformatted = " ++
    show (((PolyI $* PolyI) $. (PolyI $*^ 3 $+ Poly1)))
  putStrLn $ "exercise 5.8.3 first part distributed = " ++
    show (polyDistrib (((PolyI $* PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 first part = " ++
    show (toPolyShape (((PolyI $* PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 second part = " ++
    show (toPolyShape (((PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 composite unformatted = " ++
    show (((PolyI $* PolyI $+ PolyI) $. (PolyI $*^ 3 $+ Poly1)))
  putStrLn $ "exercise 5.8.3 composite distributed = " ++
    show (polyDistrib (((PolyI $* PolyI $+ PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn $ "exercise 5.8.3 composite = " ++
    show (toPolyShape (((PolyI $* PolyI $+ PolyI) $. (PolyI $*^ 3 $+ Poly1))))
  putStrLn ""
  putStrLn $ "maybeSq(bool) = " ++ show pmMaybeSqAppBool
  putStrLn $ "shape(maybeSq(bool)) = " ++ showPolyShape pmMaybeSqAppBool
  putStrLn $ "maybeSqBoolAlg = " ++ show pmMaybeSqBoolAlg
  putStrLn $ "shape(maybeSqBoolAlg) = " ++ showPolyShape pmMaybeSqBoolAlg
  putStrLn $ "pmFinObj = " ++ show pmFinObj
  putStrLn $ "shape(pmFinObj) = " ++ showPolyShape pmFinObj
  putStrLn $ "pmFinObjTermPair = " ++ show pmFinObjTermPair
  putStrLn $ "shape(pmFinObjTermPair) = " ++ showPolyShape pmFinObjTermPair
  putStrLn $ "pmFinObjTermPairToBool = " ++ show pmFinObjTermPairToBool
  putStrLn $ "shape(pmFinObjTermPairToBool) = " ++
    showPolyShape pmFinObjTermPairToBool
  putStrLn ""
  showPMIter 0
  showPMIter 1
  showPMIter 2
  showPMIter 3
  showPMIter 4
  putStrLn ""
  showPMRaise 0
  showPMRaise 1
  showPMRaise 2
  showPMRaise 3
  showPMRaise 4
  showPMRaise 5
  showPMRaise 6
  showPMRaise 7
  showPMRaise 8
  putStrLn ""
  putStrLn "-------------------------"
  putStrLn "---- Monads/comonads ----"
  putStrLn "-------------------------"
  putStrLn ""
  putStrLn $ "wns3 = " ++ wns3s
  -- putStrLn $ "sn0_0 = " ++ show (fst sn0_0)
  putStrLn ""
  putStrLn "-------------------------------"
  putStrLn "-------------------------------"
  putStrLn "---- Generalized ADT terms ----"
  putStrLn "-------------------------------"
  putStrLn "-------------------------------"
  putStrLn ""
  termShowFullList [
      ("adtT1", adtT1)
    , ("adtT2", adtT2)
    , ("adtT3", adtT3)
    , ("adtT4", adtT4)
    , ("adtT5", adtT5)
    , ("adtT6", adtT6)
    ]
  putStrLn ""
  putStrLn "--------------"
  putStrLn "---- STMu ----"
  putStrLn "--------------"
  putStrLn ""
  stShowFullList [
      ("stMu1", stMu1)
    , ("stMu2", stMu2)
    , ("stMu3", stMu3)
    ]
  putStrLn ""
  putStrLn "---------------"
  putStrLn ""
  putStrLn "--------------"
  putStrLn "---- SOMu ----"
  putStrLn "--------------"
  putStrLn ""
  soShowFullList [
      ("soMu1", soMu1)
    , ("soMu2", soMu2)
    , ("soMu3", soMu3)
    , ("soMu4", soMu4)
    , ("soMu5", soMu5)
    , ("soMuBool", soMuBool)
    , ("soMuThree", soMuThree)
    , ("soMuBinFour", soMuBinFour)
    , ("soMuBinFive", soMuBinFive)
    , ("soHomBoolBool", soHomBoolBool)
    , ("soHomThreeThree", soHomThreeThree)
    , ("soHomFourFive", soHomFourFive)
    , ("soHomFiveFour", soHomFiveFour)
    ]
  putStrLn $ "stt3 = " ++ show stt3
  putStrLn "---------------"
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End ADTCatTest."
  putStrLn "==============="
  pure ()
