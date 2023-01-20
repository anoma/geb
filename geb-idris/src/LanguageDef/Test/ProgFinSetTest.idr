module LanguageDef.Test.ProgFinSetTest

import Test.TestLibrary
import LanguageDef.ProgFinSet

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

bcdtShowFullLibcdt : List (String, BicartDistTerm) -> IO ()
bcdtShowFullLibcdt = showList bcdtShowFull

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
