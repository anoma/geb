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
------------------------------------------------------------
---- Free monad and initial algebra of ExpProf ----
------------------------------------------------------------
------------------------------------------------------------

public export
ExpFreeM : Type -> PolyFunc
ExpFreeM = ppFreeM ExpProf

public export
ExpMu : Type
ExpMu = PolyProfMu ExpProf

------------------------------------------------------------
---- Constructors (roll) ----
------------------------------------------------------------

-- polyProfMuRollSec {pp=ExpProf} i subTerms
--   expects subTerms : pfPos (ppDirPF ExpProf i) -> ExpMu
--
-- App (i = True):
--   pfPos ExpAppDirPF = Bool
--   subTerms : Bool -> ExpMu (two sub-terms)
--
-- Lam (i = False):
--   pfPos ExpLamDirPF = Unit
--   subTerms : Unit -> ExpMu (one sub-term)

-- Helper: dispatch two sub-terms by Bool.
public export
ExpAppSubTerms : ExpMu -> ExpMu ->
  Bool -> ExpMu
ExpAppSubTerms t1 t2 True = t1
ExpAppSubTerms t1 t2 False = t2

-- App: wraps two sub-terms.
public export
ExpApp : ExpMu -> ExpMu -> ExpMu
ExpApp t1 t2 =
  polyProfMuRollSec True
    (ExpAppSubTerms t1 t2)

-- Lam: wraps one sub-term (the body).
-- Note: polyProfMuRollSec composes existing
-- terms but cannot introduce variable bindings.
-- For terms with binding, construct (pos ** sec)
-- directly (see ExpIdent below).
public export
ExpLam : ExpMu -> ExpMu
ExpLam body =
  polyProfMuRollSec False (\() => body)

-- Lam(x.x): the identity function.
-- Built manually because the body is a bound
-- variable, not an existing ExpMu sub-term.
--
-- Position tree: a Lam node (PFCom False) whose
-- single child is a variable leaf (PFVar).
--
-- Section: Left () at the only direction,
-- meaning "this variable is bound to the
-- enclosing lambda's input."
public export
ExpIdentPos : ppFreeMPosUnit ExpProf
ExpIdentPos = InPFM (PFCom False)
  (\_ => InPFM (PFVar ()) absurd)

public export
ExpIdentSec :
  PolySection (FreeMDirPF ExpProf ExpIdentPos)
ExpIdentSec (() ** ()) = Left ()

public export
ExpIdent : ExpMu
ExpIdent = (ExpIdentPos ** ExpIdentSec)

------------------------------------------------------------
---- Catamorphism (cata) ----
------------------------------------------------------------

-- PolyProfAlg ExpProf a
--   = InterpPolyProf ExpProf a a -> a
--   = (i : Bool **
--      InterpPolyFunc (ExpProfDirPF i) a -> a)
--     -> a
--
-- App (i = True):
--   InterpPolyFunc ExpAppDirPF a
--     = (j : Bool ** Void -> a) ~ Bool
--   Handler f provides two recursive results:
--     f (True ** absurd), f (False ** absurd).
--   Simplified algebra: a -> a -> a.
--
-- Lam (i = False):
--   InterpPolyFunc ExpLamDirPF a
--     = (j : Unit ** Unit -> a) ~ a
--   The cata substitutes id for variables, so
--     (\v => f (() ** \() => v)) : a -> a
--   gives the body result at each variable value.
--   Simplified algebra: (a -> a) -> a.

public export
ExpAlg : {a : Type} ->
  (a -> a -> a) -> ((a -> a) -> a) ->
  PolyProfAlg ExpProf a
ExpAlg appAlg lamAlg (True ** f) =
  appAlg
    (f (True ** absurd))
    (f (False ** absurd))
ExpAlg appAlg lamAlg (False ** f) =
  lamAlg (\v => f (() ** \() => v))

public export
ExpCata : {a : Type} ->
  (a -> a -> a) -> ((a -> a) -> a) ->
  ExpMu -> a
ExpCata appAlg lamAlg =
  polyProfCata (ExpAlg appAlg lamAlg)

------------------------------------------------------------
---- Example: node count via catamorphism ----
------------------------------------------------------------

-- Count nodes:
-- App contributes 1 + children.
-- Lam contributes 1 + body (variable = 0).
public export
ExpNodeCount : ExpMu -> Nat
ExpNodeCount = ExpCata
  (\n1, n2 => 1 + n1 + n2)
  (\f => 1 + f 0)

------------------------------------------------------------
------------------------------------------------------------
---- Pretty printing via catamorphism ----
------------------------------------------------------------
------------------------------------------------------------

-- Variable name from binding depth.
public export
ExpVarName : Nat -> String
ExpVarName 0 = "x"
ExpVarName 1 = "y"
ExpVarName 2 = "z"
ExpVarName n = "v" ++ show n

-- Pretty-print a closed term.
-- Carrier: Nat -> String (depth -> output).
-- App: parenthesize application.
-- Lam: name variable by depth, pass name to
--   body, increment depth for body evaluation.
public export
ExpPretty : ExpMu -> String
ExpPretty t = ExpCata
  (\s1, s2 => \d =>
    "(" ++ s1 d ++ " " ++ s2 d ++ ")")
  (\body => \d =>
    "(lam " ++ ExpVarName d ++ ". " ++
    body (\_ => ExpVarName d) (S d) ++ ")")
  t 0

------------------------------------------------------------
------------------------------------------------------------
---- K and K* combinators ----
------------------------------------------------------------
------------------------------------------------------------

-- K and K* share a position tree: two nested
-- lambdas wrapping a single variable leaf.
-- They differ only in the section, which
-- determines which lambda the variable binds
-- to.  This demonstrates that the section
-- encodes binding structure independently of
-- tree shape.

-- Shared position tree: Lam( Lam( Var ) ).
public export
ExpConstPos : ppFreeMPosUnit ExpProf
ExpConstPos = InPFM (PFCom False)
  (\_ => InPFM (PFCom False)
    (\_ => InPFM (PFVar ()) absurd))

-- K = Lam(x. Lam(y. x)):
-- Variable binds to outer lambda.
-- Section maps the single direction to Left (),
-- meaning "bind here at the outer Lam".
public export
ExpConstSec :
  PolySection
    (FreeMDirPF ExpProf ExpConstPos)
ExpConstSec (() ** (() ** ())) = Left ()

public export
ExpConst : ExpMu
ExpConst = (ExpConstPos ** ExpConstSec)

-- K* = Lam(x. Lam(y. y)):
-- Variable binds to inner lambda.
-- Section maps direction to Right (Left ()),
-- meaning "skip outer Lam (Right), bind at
-- inner Lam (Left ())".
public export
ExpConstFlipSec :
  PolySection
    (FreeMDirPF ExpProf ExpConstPos)
ExpConstFlipSec (() ** (() ** ())) =
  Right (Left ())

public export
ExpConstFlip : ExpMu
ExpConstFlip =
  (ExpConstPos ** ExpConstFlipSec)

------------------------------------------------------------
------------------------------------------------------------
---- Open terms (free monad vs initial algebra) ----
------------------------------------------------------------
------------------------------------------------------------

-- The initial algebra ExpMu contains only closed
-- terms: every variable is bound by some lambda.
--
-- The free monad parametrized by a type v gives
-- open terms with free variables of type v.
-- This is the "diagonal" of the profunctor:
-- plugging one type in for both parameters.
--
-- PolyProfFreeMPHOAS pp v
--   = (x : Type) -> (v -> x) ->
--     InterpPolyFuncFreeM
--       (ppToPolyFunc pp x) x
--
-- Hierarchy:
--   ExpOpen Void  ~ ExpMu  (closed, no vars)
--   ExpOpen v              (one type param)
--   Full profunctor        (two type params)
--
-- The monad structure on ExpOpen is
-- substitution: bind replaces free variables
-- with terms.

public export
ExpOpen : Type -> Type
ExpOpen = PolyProfFreeMPHOAS ExpProf

-- Embed a free variable.
public export
ExpOpenVar : {v : Type} -> v -> ExpOpen v
ExpOpenVar =
  polyProfFreeMVar {pp=ExpProf}

-- Application of two open terms.
public export
ExpOpenApp : {v : Type} ->
  ExpOpen v -> ExpOpen v -> ExpOpen v
ExpOpenApp t1 t2 =
  polyProfFreeMRoll {pp=ExpProf} True
    (\x, subst, d => case fst d of
      True => t1 x subst
      False => t2 x subst)

-- Lambda abstraction.  The body receives the
-- bound variable as a value of the
-- instantiation type x (not v).  This is the
-- PHOAS pattern: bound variables are
-- metalanguage values, distinct from the free
-- variables of type v.
public export
ExpOpenLam : {v : Type} ->
  ((x : Type) -> (v -> x) -> x ->
    InterpPolyFuncFreeM
      (ppToPolyFunc ExpProf x) x) ->
  ExpOpen v
ExpOpenLam body =
  polyProfFreeMRoll {pp=ExpProf} False
    (\x, subst, (() ** f) =>
      body x subst (f ()))

-- Helper: a free monad variable leaf at any
-- instantiation type.  Position is PFVar (a
-- leaf), section maps Unit direction to the
-- given value.
public export
expFreeMLeaf : {x : Type} -> x ->
  InterpPolyFuncFreeM
    (ppToPolyFunc ExpProf x) x
expFreeMLeaf val =
  (InPFM (PFVar ()) absurd ** \() => val)

------------------------------------------------------------
---- Open term examples ----
------------------------------------------------------------

-- Identity as an open term (no free vars).
-- Lam(x. x): body returns the bound variable
-- as a leaf node.
public export
expOpenIdent : {v : Type} -> ExpOpen v
expOpenIdent = ExpOpenLam
  (\_, _, val => expFreeMLeaf val)

-- Self-application of free variable: App(a,a).
public export
expSelfApp : ExpOpen String
expSelfApp =
  ExpOpenApp
    (ExpOpenVar "a") (ExpOpenVar "a")

-- Application of two free variables: App(a,b).
public export
expAppAB : ExpOpen String
expAppAB =
  ExpOpenApp
    (ExpOpenVar "a") (ExpOpenVar "b")

------------------------------------------------------------
---- Folding open terms ----
------------------------------------------------------------

-- To fold an open term, instantiate the PHOAS
-- at a concrete type and use pfSubstCata.
-- For pretty-printing, instantiate at String.

-- Algebra for pretty-printing open terms at
-- type String.  App: parenthesize.  Lam: the
-- bound variable gets the name chosen by the
-- algebra.
public export
ExpOpenPrintAlg :
  PFAlg (ppToPolyFunc ExpProf String) String
ExpOpenPrintAlg True f =
  "(" ++ f (True ** absurd) ++
  " " ++ f (False ** absurd) ++ ")"
ExpOpenPrintAlg False f =
  "(lam _. " ++
  f (() ** \() => "_") ++ ")"

-- Pretty-print an open term with String-named
-- free variables.  Free variables appear as
-- their names; bound variables as "_".
public export
ExpOpenPretty : ExpOpen String -> String
ExpOpenPretty t =
  pfSubstCata
    {p=ppToPolyFunc ExpProf String}
    id ExpOpenPrintAlg (t String id)

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
  -- Initial algebra: node counts
  putStrLn $
    "nodes(I) = " ++
      show (ExpNodeCount ExpIdent)
  putStrLn $
    "nodes(K) = " ++
      show (ExpNodeCount ExpConst)
  putStrLn $
    "nodes(K*) = " ++
      show (ExpNodeCount ExpConstFlip)
  putStrLn $
    "nodes(I I) = " ++
      show (ExpNodeCount
        (ExpApp ExpIdent ExpIdent))
  putStrLn "-------------------------"
  -- Pretty printing: closed terms
  putStrLn $ "I  = " ++ ExpPretty ExpIdent
  putStrLn $ "K  = " ++ ExpPretty ExpConst
  putStrLn $
    "K* = " ++ ExpPretty ExpConstFlip
  putStrLn $
    "I I = " ++
      ExpPretty (ExpApp ExpIdent ExpIdent)
  putStrLn $
    "K I = " ++
      ExpPretty (ExpApp ExpConst ExpIdent)
  putStrLn "-------------------------"
  -- Open terms: free variables appear by name
  putStrLn $
    "App(a,a) = " ++
      ExpOpenPretty expSelfApp
  putStrLn $
    "App(a,b) = " ++
      ExpOpenPretty expAppAB
  putStrLn $
    "open I = " ++
      ExpOpenPretty
        (expOpenIdent {v=String})
  putStrLn "-------------------------"
  putStrLn "End PolyProfEndTest."
  putStrLn "========================="
  pure ()
