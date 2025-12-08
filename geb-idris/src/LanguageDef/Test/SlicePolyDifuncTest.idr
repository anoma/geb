module LanguageDef.Test.SlicePolyDifuncTest

import Test.TestLibrary
import LanguageDef.SlicePolyDifunc
import LanguageDef.DislicePolyCat
import LanguageDef.InternalProfunctor

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slicePolyDifuncTest : IO ()
slicePolyDifuncTest = do
  putStrLn ""
  putStrLn "==========================="
  putStrLn "Begin SlicePolyDifuncTest:"
  putStrLn "--------------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "End SlicePolyDifuncTest."
  putStrLn "========================="

public export
EndoHomTwArrPreshfOpToPara : EndoHomTwArrPreshfOpNatSig -> EndoHomParaSig
EndoHomTwArrPreshfOpToPara gamma x f = gamma x x f Prelude.id

public export
EndoHomTwArrPreshfOpToParaCond : FunExt ->
  (gamma : EndoHomTwArrPreshfOpNatSig) ->
  EndoHomTwArrPreshfOpNatCond gamma ->
  EndoHomParaCond (EndoHomTwArrPreshfOpToPara gamma)
EndoHomTwArrPreshfOpToParaCond fext gamma cond i0 i1 i2 d0 d1 i2dcomm =
  funExt $ \ei0 =>
    sym $
      let commapp = fcong {x=ei0} i2dcomm in
      let condapp = cond i0 i0 i1 i1 id (const ei0) i2 id in
      ?EndoHomTwArrPreshfOpToParaCond_hole

public export
EndoHomTwArrPreshfOpToNatEqIterSym : FunExt ->
  (x : Type) -> (f : x -> x) ->
  (gamma : EndoHomTwArrPreshfOpNatSig) ->
  EndoHomTwArrPreshfOpNatCond gamma ->
  ExtEq
    (gamma x x f Prelude.id)
    (iterNpnt (gamma Nat Nat S Prelude.id 0) x f)
EndoHomTwArrPreshfOpToNatEqIterSym fext x f gamma cond =
  EndoHomParaToNatEqIter
    fext
    (EndoHomTwArrPreshfOpToPara gamma)
    (EndoHomTwArrPreshfOpToParaCond fext gamma cond)
    x f

public export
EndoHomTwArrPreshfOpToNatEqIter : FunExt ->
  (gamma : EndoHomTwArrPreshfOpNatSig) -> EndoHomTwArrPreshfOpNatCond gamma ->
  (x, y : Type) -> (g : y -> x) -> (f : x -> y) ->
  ExtEq
    (gamma x y g f)
    (iterNnt (gamma Nat Nat S Prelude.id 0) x y f g)
EndoHomTwArrPreshfOpToNatEqIter fext gamma cond x y g f ex =
  trans
    (sym $ fcong {x=ex} $ cond x x x y g id f id)
    (cong f $ EndoHomTwArrPreshfOpToNatEqIterSym fext x (g . f) gamma cond ex)

public export
EndoHomTwArrPreshfOpToNatComplete : FunExt ->
  (gamma : EndoHomTwArrPreshfOpNatSig) -> EndoHomTwArrPreshfOpNatCond gamma ->
  (x, y : Type) -> (g : y -> x) -> (f : x -> y) ->
  ExtEq
    (gamma x y g f)
    (EndoHomTwArrPreshfOpNatFromNat (EndoHomTwArrPreshfOpToNat gamma) x y g f)
EndoHomTwArrPreshfOpToNatComplete = EndoHomTwArrPreshfOpToNatEqIter
