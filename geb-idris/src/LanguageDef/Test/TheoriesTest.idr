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

ccBin4t : CompCatMorph CC1 TheoriesTest.ccBin4
ccBin4t = CCconst _ $ CCp CCt $ CCconst _ $ CCp CCf $ CCp CCt CCf

ccBin4tEv : CompCatMorph CC1 CCB
ccBin4tEv = ccComp (ccEval ccBin4 CCB) (CCp (ccQuote ccBin4ChiF) ccBin4t)

CCBig : CompCatObj
CCBig = ccHomObj (ccHomObj (ccHomObj CCB CCB) CCB) CCB

ccBigId : CompCatMorph CCBig CCBig
ccBigId = CCid CCBig

ccQB : CompCatMorph CC1 (ccHomObj CCBig CCBig)
ccQB = ccQuote ccBigId

ccBigTrue : CompCatMorph (ccHomObj CCBig CCBig) CCB
ccBigTrue = CCconst _ CCt

ccThroughCompose : CompCatMorph CC1 CCB
ccThroughCompose = ccComp ccBigTrue ccQB

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
  putStrLn $ "eval(ccBin4->CCB) = " ++ show (ccEval ccBin4 CCB)
  putStrLn $ "ccBin4tEv = " ++ show ccBin4tEv
  putStrLn $ "CCBig = " ++ show CCBig
  putStrLn $ "ccThroughCompose = " ++ show ccThroughCompose
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "End TheoriesTest."
  putStrLn "================="
  pure ()
