module LanguageDef.Test.SyntaxTest

import Test.TestLibrary
import LanguageDef.Syntax

%default total

----------------
----------------
---- SymSet ----
----------------
----------------

finSS : SymSet
finSS = SS (Fin 10) _ (FinIdDecEncoding _) show

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
  putStrLn $ "finSS = " ++ show finSS
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End SyntaxTest."
  putStrLn "==============="
  pure ()
