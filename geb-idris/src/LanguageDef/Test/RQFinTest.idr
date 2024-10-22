module LanguageDef.Test.RQFinTest

import Test.TestLibrary
import LanguageDef.RQFin

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
rqFinTest : IO ()
rqFinTest = do
  putStrLn ""
  putStrLn "================"
  putStrLn "Begin RQFinTest:"
  putStrLn "----------------"
  putStrLn ""
  putStrLn "--------------"
  putStrLn "End RQFinTest."
  putStrLn "=============="
  pure ()
