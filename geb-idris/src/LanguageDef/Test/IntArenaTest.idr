module LanguageDef.Test.IntArenaTest

import Test.TestLibrary
import LanguageDef.IntArena

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intArenaTest : IO ()
intArenaTest = do
  putStrLn ""
  putStrLn "==================="
  putStrLn "Begin IntArenaTest:"
  putStrLn "-------------------"
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "End IntArenaTest."
  putStrLn "================="
  pure ()
