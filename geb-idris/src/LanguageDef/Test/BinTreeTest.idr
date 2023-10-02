module LanguageDef.Test.BinTreeTest

import Test.TestLibrary
import LanguageDef.BinTree

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
binTreeTest : IO ()
binTreeTest = do
  putStrLn ""
  putStrLn "=================="
  putStrLn "Begin BinTreeTest:"
  putStrLn "------------------"
  putStrLn ""
  putStrLn "------------"
  putStrLn "End BinTreeTest."
  putStrLn "============"
  pure ()
