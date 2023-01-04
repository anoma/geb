module LanguageDef.Test.PolyProfunctorTest

import Test.TestLibrary
import LanguageDef.PolyProfunctor

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polyProfunctorTest : IO ()
polyProfunctorTest = do
  putStrLn ""
  putStrLn "========================="
  putStrLn "Begin PolyProfunctorTest:"
  putStrLn "-------------------------"
  putStrLn ""
  putStrLn "-----------------------"
  putStrLn "End PolyProfunctorTest."
  putStrLn "======================="
  pure ()
