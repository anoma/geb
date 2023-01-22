module LanguageDef.Test.SyntaxTest

import Test.TestLibrary
import LanguageDef.Syntax

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
languageDefSyntaxTest : IO ()
languageDefSyntaxTest = do
  putStrLn ""
  putStrLn "================="
  putStrLn "Begin SyntaxTest:"
  putStrLn "-----------------"
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End SyntaxTest."
  putStrLn "==============="
  pure ()
