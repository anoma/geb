module LanguageDef.Test.IntUCofamCatTest

import Test.TestLibrary
import LanguageDef.IntUCofamCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intUCofamCatTest : IO ()
intUCofamCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin IntUCofamCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End IntUCofamCatTest."
  putStrLn "====================="
  pure ()
