module LanguageDef.Test.PolyProfEndTest

import Test.TestLibrary
import LanguageDef.PolyProfEnd

%default total

------------------------------------------------------------
------------------------------------------------------------
---- HOAS as a Polynomial Profunctor ----
------------------------------------------------------------
------------------------------------------------------------

-- The HOAS class from
-- blog.functorial.com/posts/2017-10-08-HOAS-CCCs.html :
--
--   class HOAS rep where
--     app :: rep (a -> b) -> rep a -> rep b
--     lam :: (rep a -> rep b) -> rep (a -> b)
--
-- Encoding as a polynomial profunctor
-- P(x, y) = Sigma(i : I)(Dir_i(x) -> y):
--
--   app: Dir(x) = x * x  (pair functor, Bool -> x)
--     P_app(x, y) = (x * x) -> y
--
--   lam: Dir(x) = x  (identity functor, Unit -> x)
--     P_lam(x, y) = x -> y

------------------------------------------------------------
---- Direction polynomial functors ----
------------------------------------------------------------

-- InterpPolyFunc AppDirPF x
--   = (j : Unit ** Bool -> x) ~ Bool -> x ~ x * x
public export
AppDirPF : PolyFunc
AppDirPF = (Unit ** \() => Bool)

-- InterpPolyFunc LamDirPF x
--   = (j : Unit ** Unit -> x) ~ Unit -> x ~ x
public export
LamDirPF : PolyFunc
LamDirPF = (Unit ** \() => Unit)

------------------------------------------------------------
---- HOAS polynomial profunctor ----
------------------------------------------------------------

public export
HOASProfDirPF : Bool -> PolyFunc
HOASProfDirPF True = AppDirPF
HOASProfDirPF False = LamDirPF

public export
HOASProf : PolyProf
HOASProf = MkPolyProf Bool HOASProfDirPF

------------------------------------------------------------
------------------------------------------------------------
---- End of HOAS Polynomial Profunctor ----
------------------------------------------------------------
------------------------------------------------------------

-- PolyProfEnd HOASProf
--   = (i : Bool ** PolySection (HOASProfDirPF i))
--
-- For app (True):
--   PolySection AppDirPF = (() -> Bool) ~ Bool
-- For lam (False):
--   PolySection LamDirPF = (() -> Unit) ~ Unit
--
-- Three canonical elements:
--   (True ** \() => True)  -- first projection
--   (True ** \() => False) -- second projection
--   (False ** \() => ())   -- identity

public export
HOASEndFst : PolyProfEnd HOASProf
HOASEndFst = (True ** \() => True)

public export
HOASEndSnd : PolyProfEnd HOASProf
HOASEndSnd = (True ** \() => False)

public export
HOASEndId : PolyProfEnd HOASProf
HOASEndId = (False ** \() => ())

------------------------------------------------------------
---- Compile-time tests ----
------------------------------------------------------------

-- endToPolyFamily converts an end element (i ** sec)
-- to (i ** sectionApply sec x) at each type x.
-- We test sectionApply directly, since Idris has
-- difficulty reducing snd of the endToPolyFamily
-- dependent pair.

-- First projection: sectionApply picks f True.
public export
0 TestFstSection :
  (x : Type) -> (f : Bool -> x) ->
  sectionApply {pf=AppDirPF}
    (\() => True) x (() ** f) = f True
TestFstSection x f = Refl

-- Second projection: sectionApply picks f False.
public export
0 TestSndSection :
  (x : Type) -> (f : Bool -> x) ->
  sectionApply {pf=AppDirPF}
    (\() => False) x (() ** f) = f False
TestSndSection x f = Refl

-- Identity: sectionApply picks f ().
public export
0 TestIdSection :
  (x : Type) -> (f : Unit -> x) ->
  sectionApply {pf=LamDirPF}
    (\() => ()) x (() ** f) = f ()
TestIdSection x f = Refl

------------------------------------------------------------
---- Runtime test helpers ----
------------------------------------------------------------

-- Encode a pair (a, b) via the app direction PF.
-- A pair is (() ** g) where g True = a, g False = b.
public export
HOASPairFn : Nat -> Nat -> Bool -> Nat
HOASPairFn a b True = a
HOASPairFn a b False = b

------------------------------------------------------------
---- Runtime tests ----
------------------------------------------------------------

export
polyProfEndTest : IO ()
polyProfEndTest = do
  putStrLn ""
  putStrLn "========================="
  putStrLn "Begin PolyProfEndTest:"
  putStrLn "-------------------------"
  -- Pair (42, 7) as (() ** HOASPairFn 42 7).
  let fstR = sectionApply {pf=AppDirPF}
        (snd HOASEndFst) Nat
        (() ** HOASPairFn 42 7)
  putStrLn $
    "fst (42, 7) = " ++ show fstR
  let sndR = sectionApply {pf=AppDirPF}
        (snd HOASEndSnd) Nat
        (() ** HOASPairFn 42 7)
  putStrLn $
    "snd (42, 7) = " ++ show sndR
  -- Value 99 as (() ** const 99).
  let idR = sectionApply {pf=LamDirPF}
        (snd HOASEndId) Nat
        (() ** \() => 99)
  putStrLn $
    "id 99 = " ++ show idR
  putStrLn "-------------------------"
  putStrLn "End PolyProfEndTest."
  putStrLn "========================="
  pure ()
