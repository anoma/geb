module LanguageDef.Test.ProgFinSetTest

import Test.TestLibrary
import LanguageDef.ProgFinSet
import LanguageDef.PolyCat

%default total

--------------
--------------
---- STMu ----
--------------
--------------

bcdtShowFull : String -> BicartDistTerm -> IO ()
bcdtShowFull name x = do
  putStrLn $ name ++ " = " ++ bcdtShow x
  putStrLn $ "numLeaves[" ++ name ++ "] = " ++
    show (bcdtNumLeaves x)
  putStrLn $ "numInternalNodes[" ++ name ++ "] = " ++
    show (bcdtNumInternalNodes x)
  putStrLn $ "size[" ++ name ++ "] = " ++ show (bcdtSize x)
  putStrLn $ "depth[" ++ name ++ "] = " ++ show (bcdtDepth x)

bcdtShowFullSTerminated : (String, BicartDistTerm) -> IO ()
bcdtShowFullSTerminated = showTerminated bcdtShowFull

bcdtShowFullList : List (String, BicartDistTerm) -> IO ()
bcdtShowFullList = showList bcdtShowFull

--------------
--------------
---- OmMu ----
--------------
--------------

omobj1 : OmMu OmObj
omobj1 = InSPFM (OmObj ** OmC) $ \(i ** d) => case i of
  OmObj => case d of
    OmObjL => InSPFM (OmObj ** Om0) $ \(i ** d) => case d of _ impossible
    OmObjR => InSPFM (OmObj ** Om1) $ \(i ** d) => case d of _ impossible

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
progFinSetTest : IO ()
progFinSetTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin ProgFinSetTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End ProgFinSetTest."
  putStrLn "==================="
  pure ()
