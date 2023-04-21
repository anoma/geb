module LanguageDef.Test.FiguresTest

import Test.TestLibrary
import LanguageDef.Figures

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
figuresTest : IO ()
figuresTest = do
  putStrLn ""
  putStrLn "=================="
  putStrLn "Begin FiguresTest:"
  putStrLn "------------------"
  putStrLn ""
  putStrLn "----------------"
  putStrLn "End FiguresTest."
  putStrLn "================"
  pure ()
