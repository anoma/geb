module LanguageDef.Test.GebTest

import Test.TestLibrary
import LanguageDef.Geb
import LanguageDef.PolyCat
import LanguageDef.ProgFinSet

%default total

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
  putStrLn "----------"
  putStrLn "BTMPolyDep"
  putStrLn "----------"
  putStrLn ""
  putStrLn $ "bcdo0 = " ++ show bcdo0
  putStrLn $ "bcdoC01 = "
  putStrLn $ show bcdoC01
  putStrLn ""
  putStrLn "------------"
  putStrLn "End GebTest."
  putStrLn "============"
  pure ()

export
partial
gebTestPotentiallyNonTerminating : IO ()
gebTestPotentiallyNonTerminating = pure ()
