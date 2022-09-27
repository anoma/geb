module LanguageDef.Test.NatPrefixCatTest

import Test.TestLibrary
import LanguageDef.NatPrefixCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
natPrefixCatTest : IO ()
natPrefixCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin NatPrefixCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "-----------------------"
  putStrLn "End NatPrefixCatTest."
  putStrLn "======================="
  pure ()
