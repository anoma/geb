module LanguageDef.Test.DislicePolyCatTest

import Test.TestLibrary
import LanguageDef.DislicePolyCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
dislicePolyCatTest : IO ()
dislicePolyCatTest = do
  putStrLn ""
  putStrLn "========================="
  putStrLn "Begin DislicePolyCatTest:"
  putStrLn "-------------------------"
  putStrLn ""
  putStrLn "-----------------------"
  putStrLn "End DislicePolyCatTest."
  putStrLn "======================="
  pure ()
