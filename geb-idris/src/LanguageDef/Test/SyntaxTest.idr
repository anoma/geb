module LanguageDef.Test.SyntaxTest

import Test.TestLibrary
import LanguageDef.Syntax

%default total

----------------
----------------
---- SymSet ----
----------------
----------------

-------------------
---- Utilities ----
-------------------

showSS : String -> SymSet -> IO ()
showSS str ss = putStrLn $ str ++ " = " ++ show ss

showSSList : List (String, SymSet) -> IO ()
showSSList = showList showSS

--------------------
---- Test cases ----
--------------------

finSS10 : SymSet
finSS10 = FinSS 10

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

data Enum2 : Type where
  E2a : Enum2
  E2b : Enum2
  E2c : Enum2

Show Enum2 where
  show E2a = "e2a"
  show E2b = "e2b"
  show E2c = "e2c"

Enum2sz : Nat
Enum2sz = 3

FD2 : FinDecoder Enum2 Enum2sz
FD2 FZ = E2a
FD2 (FS FZ) = E2b
FD2 (FS (FS FZ)) = E2c

FE2 : FinEncoder FD2
FE2 E2a = (0 ** Refl)
FE2 E2b = (1 ** Refl)
FE2 E2c = (2 ** Refl)

FDE2 : FinDecEncoding Enum2 Enum2sz
FDE2 = (FD2 ** FE2)

eSS2 : SymSet
eSS2 = SS Enum2 Enum2sz FDE2 show

----------------
----------------
---- SymSet ----
----------------
----------------

-------------------
---- Utilities ----
-------------------

showNS : String -> Namespace -> IO ()
showNS str ns = do
  putStrLn $ str ++ ":"
  putStrLn $ show ns

showNSList : List (String, Namespace) -> IO ()
showNSList = showList showNS

--------------------
---- Test cases ----
--------------------

finNS10 : Namespace
finNS10 = LeafNS finSS10

eNS1 : Namespace
eNS1 = LeafNS eSS1

eNS2 : Namespace
eNS2 = LeafNS eSS2

ssfv2 : SymSet
ssfv2 = FinSS 3

ns1fv2 : Namespace
ns1fv2 = NS eSS1 ssfv2 [finNS10, VoidNS, eNS2]

nstree : Namespace
nstree =
  FinNS 5 [
    ns1fv2,
    FinNS 3 [],
    ns1fv2,
    FinNS 7
      [FinNS 1
        [FinNS 1 []],
        FinNS 3 []
      ]
    ]

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
  putStrLn "-------"
  putStrLn "SymSet:"
  putStrLn "-------"
  showSSList [
      ("VoidSS", VoidSS)
    , ("finSS10", finSS10)
    , ("eSS1", eSS1)
    , ("eSS2", eSS2)
  ]
  putStrLn ""
  putStrLn "----------"
  putStrLn "Namespace:"
  putStrLn "----------"
  showNSList [
      ("VoidNS", VoidNS)
    , ("finNS10", finNS10)
    , ("eNS1", eNS1)
    , ("eNS2", eNS2)
    , ("ns1fv2", ns1fv2)
    , ("nstree", nstree)
  ]
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End SyntaxTest."
  putStrLn "==============="
  pure ()
