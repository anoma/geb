module LanguageDef.Test.TheoriesTest

import Test.TestLibrary
import LanguageDef.Theories

%default total

-----------------------
-----------------------
---- Bool category ----
-----------------------
-----------------------

-----------------
-----------------
---- CompCat ----
-----------------
-----------------

cco1 : CompCatObj
cco1 = CCP (CCP CCB (CCP CCB CC1)) CCB

ccBinN : Nat -> CompCatObj
ccBinN Z = CC1
ccBinN (S Z) = CCB
ccBinN (S (S n)) = CCP CCB $ ccBinN (S n)

ccBin4 : CompCatObj
ccBin4 = ccBinN 4

ccBin4Chi : CompCatObj
ccBin4Chi = ccHomObj ccBin4 CCB

ccBin4ChiF : CompCatMorph TheoriesTest.ccBin4 CCB
ccBin4ChiF = CCconst ccBin4 CCf

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
theoriesTest : IO ()
theoriesTest = do
  putStrLn ""
  putStrLn "==================="
  putStrLn "Begin TheoriesTest:"
  putStrLn "-------------------"
  putStrLn ""
  putStrLn "-------"
  putStrLn "CompCat"
  putStrLn "-------"
  putStrLn ""
  putStrLn $ "cco1 = " ++ show cco1
  putStrLn $ "cco1 ^ 2 = " ++ show (ccHomObj CCB cco1)
  putStrLn $ "2 ^ cco1 = " ++ show (ccHomObj cco1 CCB)
  putStrLn ""
  putStrLn $ "ev(2 -> cco1) = " ++ show (ccEval CCB cco1)
  putStrLn ""
  putStrLn $ "ev(cco1 -> 2) = " ++ show (ccEval cco1 CCB)
  putStrLn ""
  putStrLn $ "ccBin4 = " ++ show ccBin4
  putStrLn $ "ccBin4Chi = " ++ show ccBin4Chi
  putStrLn $ "const-f[ccBin4Chi] = " ++ show ccBin4ChiF
  putStrLn $ "quote(const-f[ccBin4Chi]) = " ++ show (ccQuote ccBin4ChiF)
  putStrLn $ "unquote(quote(const-f[ccBin4Chi])) = " ++
    show (ccUnquote {a=ccBin4} {b=CCB} (ccQuote ccBin4ChiF))
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "End TheoriesTest."
  putStrLn "================="
  pure ()
