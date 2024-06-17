module LanguageDef.Test.GebTest

import Test.TestLibrary
import LanguageDef.BinTree
import LanguageDef.Test.BinTreeTest
import LanguageDef.Test.DiagramCatTest
import LanguageDef.Geb
import LanguageDef.PolyCat
import LanguageDef.ProgFinSet

%default total

----------------------
----------------------
---- Reachability ----
----------------------
----------------------

data DCtxIter : PolyFunc -> Type where
  DCtxNil : {0 p : PolyFunc} -> DCtxIter p
  DCtxCons : {0 p : PolyFunc} -> (i : pfPos p) -> pfDir {p} i -> DCtxIter p

data DTypeIter : (p : PolyFunc) -> SliceObj (DCtxIter p) where
  DTypeBase : {0 p : PolyFunc} -> (ctx : DCtxIter p) -> DTypeIter p ctx
  DTypePi : {0 p : PolyFunc} -> (ctx : DCtxIter p) ->
    Pi {a=(pfPDir p)} (\(i ** d) => DTypeIter p $ DCtxCons {p} i d) ->
    DTypeIter p ctx

data DTypeIterFPos : (p : PolyFunc) -> SliceObj (DCtxIter p) where
  DTIPbase : {0 p : PolyFunc} -> (ctx : DCtxIter p) -> DTypeIterFPos p ctx
  DTIPpi : {0 p : PolyFunc} -> (ctx : DCtxIter p) -> DTypeIterFPos p ctx

DTypeIterFDir : (p : PolyFunc) -> SliceObj (Sigma (DTypeIterFPos p))
DTypeIterFDir p (ctx ** DTIPbase ctx) = Void
DTypeIterFDir p (ctx ** DTIPpi ctx) = pfPDir p

DTypeIterFAssign : (p : PolyFunc) -> Sigma (DTypeIterFDir p) -> DCtxIter p
DTypeIterFAssign (pos ** dir) ((ctx ** (DTIPbase ctx)) ** d) = void d
DTypeIterFAssign (pos ** dir) ((ctx ** (DTIPpi ctx)) ** d) =
  DCtxCons {p=(pos ** dir)} (fst d) (snd d)

DTypeIterF : (p : PolyFunc) -> SlicePolyEndoFunc (DCtxIter p)
DTypeIterF p = (DTypeIterFPos p ** DTypeIterFDir p ** DTypeIterFAssign p)

DCtxTypeIter : ArenaArena
DCtxTypeIter p = (DCtxIter p ** DTypeIter p)

DCtxMu : Type
DCtxMu = PolyFuncMu DCtxTypeIter

---------------------------------------------------------
---------------------------------------------------------
---- Experiments with slice categories of `PolyFunc` ----
---------------------------------------------------------
---------------------------------------------------------

-- A polynomial slice operation maps a slice object to `Type` as a sum
-- of representables.
PSliceOp : (a : Type) -> Type
PSliceOp a = (pos : Type ** pos -> SliceObj a)

InterpPSliceOp : {a : Type} -> PSliceOp a -> SliceObj a -> Type
InterpPSliceOp {a} (pos ** dir) sla = (i : pos ** SliceMorphism (dir i) sla)

PSliceF : Type -> Type -> Type
PSliceF a b = b -> PSliceOp a

InterpPSliceF : {a, b : Type} -> PSliceF a b -> SliceObj a -> SliceObj b
InterpPSliceF {a} {b} pf sla eb = InterpPSliceOp {a} (pf eb) sla

public export
ListArPos : Type
ListArPos = Nat

public export
ListArDir : Nat -> Type
ListArDir = Fin

public export
ListPF : PolyFunc
ListPF = (ListArPos ** ListArDir)

public export
BoolPF : PolyFunc
BoolPF = PFConstArena Bool

public export
ListTest : PolyFunc
ListTest = pfHomObj ListPF BoolPF

pfIsEmpty : (a : Type) -> InterpPolyFunc ListTest a
pfIsEmpty a = (\n => (n == 0 ** \v => void v) ** \(n ** (v ** _)) => void v)

pfIsEmpty' : PolyNatTrans PFIdentityArena ListTest
pfIsEmpty' =
  (\(), n => (n == 0 ** \v => void v) ** \(), (_ ** v ** _) => void v)

--------------------
--------------------
---- FinMatrixT ----
--------------------
--------------------

public export
NM1 : NatMatrix
NM1 = [ [ 10 , 3 ] , [] , [ 1, 5, 9 ] ]

public export
TFM1 : Type
TFM1 = FinMatrixT NM1

public export
tfm1t1 : TFM1
tfm1t1 = MkFinMatrixT NM1 2 [0, 2, 7]

------------------
------------------
---- BinTreeF ----
------------------
------------------

-- A binary tree with a finite, `n`-cardinality atom type has one position with
-- two directions and `n` positions with zero directions.
btPolyShape : Nat -> PolyShape
btPolyShape n = [(2, 1), (0, n)]

-------------------------------------
-------------------------------------
---- BinTree as Tuple-expression ----
-------------------------------------
-------------------------------------

BTT : Type
BTT = BinTreeMu Nat

btt0 : BTT
btt0 = $: [ $:! [ 82, 17 ] , $! 34, $! 52, $! 74 ]

btt1 : BTT
btt1 = $:! [ 4, 5 ] $* $:! [ 6, 14, 15 ]

btt2 : BTT
btt2 = $: [ $:! [ 4, 5 ] , $! 6, $! 14, $! 15 ]

btt0neq1 : Assertion
btt0neq1 = Assert $ not $ binTreeEq decEq btt0 btt1

btt1eq2 : Assertion
btt1eq2 = Assert $ binTreeEq decEq btt1 btt2

-------------------
-------------------
---- FPFunctor ----
-------------------
-------------------

public export
BCDOnPos : Nat
BCDOnPos = 4

public export
BCDOpos0 : Nat
BCDOpos0 = 0

public export
BCDOdir0 : Nat
BCDOdir0 = 0

public export
BCDOpos1 : Nat
BCDOpos1 = 1

public export
BCDOdir1 : Nat
BCDOdir1 = 0

public export
BCDOposP : Nat
BCDOposP = 2

public export
BCDOdirP : Nat
BCDOdirP = 2

public export
BCDOposC : Nat
BCDOposC = 3

public export
BCDOdirC : Nat
BCDOdirC = 2

public export
BCDOfpf : FPFunctor
BCDOfpf = FPF BCDOnPos [ BCDOdir0, BCDOdir1, BCDOdirC, BCDOdirP ]

public export
BTbcdObj : Type
BTbcdObj = FPFTerm BCDOfpf

public export
btInitObj : BTbcdObj
btInitObj = MkFPFn BCDOfpf $ $! BCDOpos0

public export
btTermObj : BTbcdObj
btTermObj = MkFPFn BCDOfpf $ $! BCDOpos1

public export
btProd01 : BTbcdObj
btProd01 = MkFPFn BCDOfpf $ $:! [ BCDOposP, BCDOpos0, BCDOpos1 ]

public export
btCoprod10bt : BTT
btCoprod10bt = $:! [ BCDOposC, BCDOpos1, BCDOpos0 ]

public export
btCoprod10 : BTbcdObj
btCoprod10 = MkFPFn BCDOfpf btCoprod10bt

public export
btInvalidBoundsTest : Assertion
btInvalidBoundsTest = Assert $
  validFPFbounds BCDOfpf ($:! [ BCDOnPos , BCDOpos1, BCDOposC ]) == False

public export
btCoprod1CvalidBounds : Assertion
btCoprod1CvalidBounds =
  Assert $ validFPFbounds BCDOfpf ($:! [ BCDOposC, BCDOpos1, BCDOposC ]) == True

public export
btCoprod1Cinvalid : Assertion
btCoprod1Cinvalid =
  Assert $ validFPFn BCDOfpf ($:! [ BCDOposC, BCDOpos1, BCDOposC ]) == False

public export
btCoprod10hdBounds : Assertion
btCoprod10hdBounds = Assert $
  validFPFbounds BCDOfpf $ $: [ btCoprod10bt, $! BCDOpos0 ]

public export
btCoprod10hd : Assertion
btCoprod10hd = Assert $
  validFPFn BCDOfpf ($: [ btCoprod10bt, $! BCDOpos0 ]) == False

public export
btCoprod1Invalid : Assertion
btCoprod1Invalid = Assert $
  validFPFn BCDOfpf ($:! [ BCDOposC, BCDOpos0 ]) == False

public export
btCP001bt : BTT
btCP001bt =
  $: [ $! BCDOposC, $:! [ BCDOposP, BCDOpos0, BCDOpos0 ] , $! BCDOpos1 ]

public export
btCP001btb : BinTreeMu (FPFatom BCDOfpf)
btCP001btb = MkFPFbounded BCDOfpf btCP001bt

public export
btCP001 : BTbcdObj
btCP001 = MkFPFn BCDOfpf btCP001bt

public export
btC1P00bt : BTT
btC1P00bt =
  $: [ $! BCDOposC, $! BCDOpos1, $:! [ BCDOposP, BCDOpos0, BCDOpos0 ] ]

public export
btC1P00btb : BinTreeMu (FPFatom BCDOfpf)
btC1P00btb = MkFPFbounded BCDOfpf btC1P00bt

--------------------
--------------------
---- BTMPolyDep ----
--------------------
--------------------

BCDObt : Type
BCDObt = BinTreeMu BCDOPos

bcdo0 : BCDObt
bcdo0 = $! BCDO_0

bcdo1 : BCDObt
bcdo1 = $! BCDO_1

bcdoc : BCDObt
bcdoc = $! BCDO_C

bcdop : BCDObt
bcdop = $! BCDO_P

bcdoC : BCDObt -> BCDObt -> BCDObt
bcdoC x y = $: [ bcdoc, x, y ]

bcdoC01 : BCDObt
bcdoC01 = bcdoC bcdo0 bcdo1

BcdoPosParam : SliceObj BCDOPos
BcdoPosParam = BicartDistObjDir

bcdoPosCod : Pi {a=BCDOPos} $ BinTreeFM BCDOPos . BcdoPosParam
bcdoPosCod BCDO_0 = $!> BCDO_0
bcdoPosCod BCDO_1 = $!> BCDO_1
bcdoPosCod BCDO_C = $: [ $!> BCDO_C, $!< BCDCopL, $!< BCDCopR ]
bcdoPosCod BCDO_P = $: [ $!> BCDO_P, $!< BCDProd1, $!< BCDProd2 ]

BcdoDir : SliceObj BCDOPos
BcdoDir = BicartDistObjDir

bcdoDirDom :
  SliceMorphism {a=BCDOPos} BcdoDir (BinTreeFM BCDOPos . BcdoDir)
bcdoDirDom i d = InBTv d

BCDObtm : BTMPolyDep BCDOPos
BCDObtm = BTMPD BCDOPos BcdoPosParam bcdoPosCod BcdoDir bcdoDirDom

BCDOvalid : SliceObj (BinTreeMu BCDOPos)
BCDOvalid = BinTreeDepMu BCDObtm

Bcdo0valid : BCDOvalid GebTest.bcdo0
Bcdo0valid = InSPFM (bcdo0 ** BCDO_0 ** voidF _ ** Refl) $ \v => void v

Bcdo1valid : BCDOvalid GebTest.bcdo1
Bcdo1valid = InSPFM (bcdo1 ** BCDO_1 ** voidF _ ** Refl) $ \v => void v

BcdoC01valid : BCDOvalid GebTest.bcdoC01
BcdoC01valid =
  InSPFM
    (bcdoC01 **
     BCDO_C **
     (\d => case d of BCDCopL => bcdo0 ; BCDCopR => bcdo1) **
     Refl) $
    \d => case d of
      BCDCopL => Bcdo0valid
      BCDCopR => Bcdo1valid

BcdoShouldntBeValid : BCDObt
BcdoShouldntBeValid = bcdoC bcdo0 bcdoc

bcdoDeep : BCDObt
bcdoDeep =
  $: [
      $: [ $: [ bcdoC bcdo1 bcdo0, bcdo0 ], bcdo1 ],
      $: [ $: [ bcdo0, bcdo1 ], $: [ bcdo1, bcdo0 ] ]
     ]

-------------------------------------------
-------------------------------------------
---- Lawvere/profunctor representation ----
-------------------------------------------
-------------------------------------------

T0StarterExp : List Nat
T0StarterExp = []

T0Starter : RawOp 0 0
T0Starter = rawOpFromList T0StarterExp

T0MakerExp : List Nat
T0MakerExp = [0, 0]

T0Maker : RawOp 1 2
T0Maker = rawOpFromList T0MakerExp

T0DepMakerExp : List Nat
T0DepMakerExp = [0, 1, 1]

T0DepMaker : RawOp 2 3
T0DepMaker = rawOpFromList T0DepMakerExp

T1StarterExp : List Nat
T1StarterExp = []

T1Starter : RawOp 0 0
T1Starter = rawOpFromList T1StarterExp

T1IdExp : List Nat
T1IdExp = [0]

T1Id : RawOp 1 1
T1Id = rawOpFromList T1IdExp

T1MakerExp : List Nat
T1MakerExp = [0, 0, 1, 1]

T1Maker : RawOp 2 4
T1Maker = rawOpFromList T1MakerExp

T1Maker1dom : SortInterpretation 2
T1Maker1dom = [DiagramCatTest.Test0, Sigma DiagramCatTest.Test1]

T1Maker1t1 : InterpRawOpProd T1Maker T1Maker1dom
T1Maker1t1 =
  [T0Starter,
   T0Maker T0Starter T0Starter,
   (T0Starter ** T1Starter),
   (T0Maker T0Starter T0Starter ** T1Id $ T0Maker T0Starter T0Starter)]

T1ComposerExp : List Nat
T1ComposerExp = [0, 0, 0, 1, 1]

T1Composer : RawOp 2 5
T1Composer = rawOpFromList T1ComposerExp

T1DistribExp : List Nat
T1DistribExp = [0, 0, 0, 1]

T1Distrib : RawOp 2 4
T1Distrib = rawOpFromList T1DistribExp

T1DepComposerExp : List Nat
T1DepComposerExp = [0, 1, 1, 1, 1, 1]

T1DepComposer : RawOp 2 6
T1DepComposer = rawOpFromList T1DepComposerExp

T1TelescopeExp : List Nat
T1TelescopeExp = [0, 1, 1, 1, 1, 1, 1]

T1Telescope : RawOp 2 7
T1Telescope = rawOpFromList T1TelescopeExp

T1SortOpListExp : List (List Nat)
T1SortOpListExp =
  [ T1StarterExp
  , T1IdExp
  , T1MakerExp
  , T1ComposerExp
  , T1DistribExp
  , T1DepComposerExp
  , T1TelescopeExp
  ]

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
gebTest : IO ()
gebTest = do
  putStrLn ""
  putStrLn "=============="
  putStrLn "Begin GebTest:"
  putStrLn "--------------"
  putStrLn ""
  putStrLn "----------"
  putStrLn "FinMatrixT"
  putStrLn "----------"
  putStrLn ""
  putStrLn $ "NM1 = " ++ show NM1
  putStrLn $ "tfm1t1 = " ++ showFinMatrixT tfm1t1
  putStrLn ""
  putStrLn "--------"
  putStrLn "BinTreeF"
  putStrLn "--------"
  putStrLn ""
  putStrLn $ "btPolyShape 3 = " ++ (show $ btPolyShape 3)
  putStrLn $ "btPolyShape 3 * btPolyShape 5 = " ++
    (show $ mulPolyShape (btPolyShape 3) (btPolyShape 5))
  putStrLn $ "btPolyShape 3 |*| btPolyShape 5 = " ++
    (show $ parProdPolyShape (btPolyShape 3) (btPolyShape 5))
  putStrLn $ "btPolyShape 3 . btPolyShape 5 = " ++
    (show $ composePolyShape (btPolyShape 3) (btPolyShape 5))
  putStrLn $ "btPolyShape 3 -> btPolyShape 5 = " ++
    (show $ polyShapeHomObj (btPolyShape 3) (btPolyShape 5))
  putStrLn $ "btPolyShape 3 ^ btPolyShape 5 = " ++
    (show $ polyShapeExponential (btPolyShape 3) (btPolyShape 5))
  putStrLn $ "btPolyShape 3 -> 5 = " ++
    (show $ polyShapeHomObj (btPolyShape 3) (constPolyShape 5))
  putStrLn $ "3 -> btPolyShape 5 = " ++
    (show $ polyShapeHomObj (constPolyShape 3) (btPolyShape 5))
  putStrLn $ "btPolyShape 3 -> 7 = " ++
    (show $ polyShapeHomObj (btPolyShape 3) (constPolyShape 7))
  putStrLn $ "parProdClosure/dirichHom(btPolyShape 3, btPolyShape 5) = " ++
    (show $ parProdClosureShape (btPolyShape 3) (btPolyShape 5))
  putStrLn $ "parProdClosure/dirichHom(btPolyShape 5, btPolyShape 3) = " ++
    (show $ parProdClosureShape (btPolyShape 5) (btPolyShape 3))
  putStrLn $ "parProdClosure/dirichHom(btPolyShape 2, btPolyShape 3) = " ++
    (show $ parProdClosureShape (btPolyShape 2) (btPolyShape 3))
  putStrLn $ "parProdClosure/dirichHom(btPolyShape 3, btPolyShape 2) = " ++
    (show $ parProdClosureShape (btPolyShape 3) (btPolyShape 2))
  putStrLn $ "leftCoclosure(btPolyShape 3, btPolyShape 5) = " ++
    (show $ leftCoclosureShape (btPolyShape 3) (btPolyShape 5))
  putStrLn $ "leftCoclosure(btPolyShape 5, btPolyShape 3) = " ++
    (show $ leftCoclosureShape (btPolyShape 5) (btPolyShape 3))
  putStrLn ""
  putStrLn "---------------------------"
  putStrLn "BinTree as Tuple-expression"
  putStrLn "---------------------------"
  putStrLn ""
  putStrLn $ "btt0 as pairs = " ++ btShowI btt0
  putStrLn $ "btt0 as tuples = " ++ btTexpShowI btt0
  putStrLn $ "btt1 as pairs = " ++ btShowI btt1
  putStrLn $ "btt1 as tuples = " ++ btTexpShowI btt1
  putStrLn ""
  putStrLn "----------"
  putStrLn "BTMPolyDep"
  putStrLn "----------"
  putStrLn ""
  putStrLn $ "bcdo0 = " ++ btShowLinesI bcdo0
  putStrLn $ "(alternate show = " ++ btShowI bcdo0 ++ ")"
  putStrLn $ "(alternate show = " ++ btTexpShowI bcdo0 ++ ")"
  putStrLn $ "bcdoC01 = "
  putStrLn $ btShowLinesI bcdoC01
  putStrLn $ "(alternate show)"
  putStrLn $ btShowI bcdoC01
  putStrLn $ "(alternate show)"
  putStrLn $ btTexpShowI bcdoC01
  putStrLn $ "bcdoDeep = " ++ btShowLinesI bcdoDeep
  putStrLn $ "(alternate show = " ++ btShowI bcdoDeep ++ ")"
  putStrLn $ "(alternate show = " ++ btTexpShowI bcdoDeep ++ ")"
  putStrLn ""
  putStrLn "---------"
  putStrLn "FPFunctor"
  putStrLn "---------"
  putStrLn ""
  putStrLn $ "btInitObj = " ++ show btInitObj
  putStrLn $ "btTermObj = " ++ show btTermObj
  putStrLn $ "btProd01 = " ++ show btProd01
  putStrLn $ "btCoprod10 = " ++ show btCoprod10
  putStrLn $ "check(btCP001bt) = " ++ show (fpfCheck {fpf=BCDOfpf} btCP001btb)
  putStrLn $ "check(btC1P00bt) = " ++ show (fpfCheck {fpf=BCDOfpf} btC1P00btb)
  putStrLn ""
  putStrLn "------------"
  putStrLn "End GebTest."
  putStrLn "============"
  pure ()

export
partial
gebTestPotentiallyNonTerminating : IO ()
gebTestPotentiallyNonTerminating = pure ()
