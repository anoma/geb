module LanguageDef.Test.SyntaxTest

import Test.TestLibrary
import LanguageDef.Syntax

%default total

----------------
----------------
---- SymSet ----
----------------
----------------

showSS : String -> SymSet -> IO ()
showSS str ss = putStrLn $ str ++ " = " ++ show ss

finSS : SymSet
finSS = SS (Fin 10) _ (FinIdDecEncoding _) show

data Enum1 : Type where
  E1a : Enum1
  E1b : Enum1
  E1c : Enum1

Show Enum1 where
  show E1a = "e1a"
  show E1b = "e1b"
  show E1c = "e1c"

Enum1sz : Nat
Enum1sz = 3

FD1 : FinDecoder Enum1 Enum1sz
FD1 FZ = E1a
FD1 (FS FZ) = E1b
FD1 (FS (FS FZ)) = E1c

FE1 : FinEncoder FD1
FE1 E1a = (0 ** Refl)
FE1 E1b = (1 ** Refl)
FE1 E1c = (2 ** Refl)

FDE1 : FinDecEncoding Enum1 Enum1sz
FDE1 = (FD1 ** FE1)

eSS1 : SymSet
eSS1 = SS Enum1 Enum1sz FDE1 show

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
  showSS "finSS" finSS
  showSS "eSS1" eSS1
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End SyntaxTest."
  putStrLn "==============="
  pure ()
