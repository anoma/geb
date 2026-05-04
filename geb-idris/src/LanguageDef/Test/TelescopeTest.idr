module LanguageDef.Test.TelescopeTest

import Test.TestLibrary
import LanguageDef.Telescope

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
telescopeTest : IO ()
telescopeTest = do
  putStrLn ""
  putStrLn "===================="
  putStrLn "Begin TelescopeTest:"
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------"
  putStrLn "End TelescopeTest."
  putStrLn "=================="
  pure ()
