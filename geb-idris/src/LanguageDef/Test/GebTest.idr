module LanguageDef.Test.GebTest

import Test.TestLibrary
import LanguageDef.Geb
import LanguageDef.PolyCat

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
  putStrLn "------------"
  putStrLn "End GebTest."
  putStrLn "============"
  pure ()

export
partial
gebTestPotentiallyNonTerminating : IO ()
gebTestPotentiallyNonTerminating = pure ()
