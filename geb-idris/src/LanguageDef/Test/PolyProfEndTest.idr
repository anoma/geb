module LanguageDef.Test.PolyProfEndTest

import Test.TestLibrary
import LanguageDef.PolyProfEnd

%default total

------------------------------------------------------------
------------------------------------------------------------
---- ExpF as a Polynomial Profunctor ----
------------------------------------------------------------
------------------------------------------------------------

-- ExpF from Kmett's PHOAS
-- (schoolofhaskell.com/user/edwardk/phoas):
--
--   data ExpF a b = App b b | Lam (a -> b)
--
-- As a type alias:
public export
ExpF : Type -> Type -> Type
ExpF a b = Either (b, b) (a -> b)

------------------------------------------------------------
---- Direction polynomial functors for ExpF ----
------------------------------------------------------------

-- For App b b: no dependence on a; produces a
-- pair of b's.  The direction functor is the
-- constant-Bool functor:
--   InterpPolyFunc ExpAppDirPF a
--     = (j : Bool ** Void -> a) ~ Bool
-- Then (Bool -> b) ~ (b, b).
public export
ExpAppDirPF : PolyFunc
ExpAppDirPF = (Bool ** \_ => Void)

-- For Lam (a -> b): one a in, one b out.
-- The direction functor is the identity:
--   InterpPolyFunc ExpLamDirPF a
--     = (j : Unit ** Unit -> a) ~ a
-- Then (a -> b).
public export
ExpLamDirPF : PolyFunc
ExpLamDirPF = (Unit ** \() => Unit)

------------------------------------------------------------
---- ExpF polynomial profunctor ----
------------------------------------------------------------

public export
ExpProfDirPF : Bool -> PolyFunc
ExpProfDirPF True = ExpAppDirPF
ExpProfDirPF False = ExpLamDirPF

public export
ExpProf : PolyProf
ExpProf = MkPolyProf Bool ExpProfDirPF

------------------------------------------------------------
------------------------------------------------------------
---- Isomorphism: InterpPolyProf ExpProf ~ ExpF ----
------------------------------------------------------------
------------------------------------------------------------

-- Forward: profunctor representation -> ExpF.
-- App: extract (b, b) by applying at both Bool
--   positions with the trivial Void -> a function.
-- Lam: curry (Unit ** Unit -> a) -> b into a -> b.
public export
ExpProfToExpF : {a, b : Type} ->
  InterpPolyProf ExpProf a b -> ExpF a b
ExpProfToExpF (True ** g) =
  Left
    (g (True ** absurd), g (False ** absurd))
ExpProfToExpF (False ** g) =
  Right (\x => g (() ** \() => x))

-- Helper for backward App case: dispatch on
-- the Bool position, ignoring the Void -> a proof.
public export
ExpAppBackward : {a, b : Type} ->
  b -> b -> InterpPolyFunc ExpAppDirPF a -> b
ExpAppBackward b1 b2 (True ** _) = b1
ExpAppBackward b1 b2 (False ** _) = b2

-- Helper for backward Lam case: apply h to the
-- extracted a value.
public export
ExpLamBackward : {a, b : Type} ->
  (a -> b) -> InterpPolyFunc ExpLamDirPF a -> b
ExpLamBackward h (() ** f) = h (f ())

-- Backward: ExpF -> profunctor representation.
public export
ExpFToExpProf : {a, b : Type} ->
  ExpF a b -> InterpPolyProf ExpProf a b
ExpFToExpProf (Left (b1, b2)) =
  (True ** ExpAppBackward b1 b2)
ExpFToExpProf (Right h) =
  (False ** ExpLamBackward h)

------------------------------------------------------------
---- Round trip: ExpF -> Prof -> ExpF = id ----
------------------------------------------------------------

-- The Left case reduces by case-split on the Bool
-- positions.  The Right case reduces by beta
-- and eta.
public export
0 ExpFRoundTrip : {a, b : Type} ->
  (ef : ExpF a b) ->
  ExpProfToExpF (ExpFToExpProf ef) = ef
ExpFRoundTrip (Left (b1, b2)) = Refl
ExpFRoundTrip (Right h) = Refl

------------------------------------------------------------
---- Round trip: Prof -> ExpF -> Prof = id ----
------------------------------------------------------------

-- The reverse direction needs FunExt because:
-- App case: any (Void -> a) function equals absurd,
--   so each (j ** f) collapses to (j ** absurd).
-- Lam case: (\() => f ()) = f (eta for Unit).
public export
0 ExpProfRoundTrip : FunExt -> {a, b : Type} ->
  (ep : InterpPolyProf ExpProf a b) ->
  ExpFToExpProf (ExpProfToExpF ep) = ep
ExpProfRoundTrip fext (True ** g) =
  dpEq12 Refl
    (funExt (\(j ** f) => case j of
      True => cong g
        (dpEq12 Refl (funExt (\v => absurd v)))
      False => cong g
        (dpEq12 Refl (funExt (\v => absurd v)))))
ExpProfRoundTrip fext (False ** g) =
  dpEq12 Refl
    (funExt (\(() ** f) =>
      cong g
        (dpEq12 Refl (funExt (\() => Refl)))))

------------------------------------------------------------
---- Runtime test helpers ----
------------------------------------------------------------

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
  -- ExpF isomorphism: App round-trip
  let appProf =
        ExpFToExpProf {a=Nat} {b=Nat}
          (Left (42, 7))
  case ExpProfToExpF appProf of
    Left (x, y) => putStrLn $
      "App (42,7) round-trip: (" ++
        show x ++ ", " ++ show y ++ ")"
    Right _ => pure ()
  -- ExpF isomorphism: Lam round-trip
  let lamProf =
        ExpFToExpProf {a=Nat} {b=Nat}
          (Right (+ 1))
  case ExpProfToExpF lamProf of
    Left _ => pure ()
    Right f => putStrLn $
      "Lam (+1) round-trip at 9: " ++
        show (f 9)
  putStrLn "-------------------------"
  putStrLn "End PolyProfEndTest."
  putStrLn "========================="
  pure ()
