module LanguageDef.Theories

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.Atom
import public LanguageDef.RefinedADT

%default total

---------------------------------------------------
---------------------------------------------------
---- Refined `Fin` using algebras of `BinNatF` ----
---------------------------------------------------
---------------------------------------------------

-- Given an implementation of the `BinNatF` interface -- that is, an
-- algebra of `BinNatF` -- we can treat the carrier of the algebra as
-- a type of objects of a category by constructing a type of morphisms
-- between objects.
--
-- We do this by defining contravariant and covariant components of the
-- hom-functor.
--
-- The contravariant component comes from `[True]`'s being a terminal object.
public export
data BinNatFinContravar : (alg : BinNatAlgObj) ->
    (fst alg -> Type) -> (BinNatF (fst alg) -> Type) where
  -- There's no contravariant component into `NilF`, because `NilF` is
  -- an initial object, which is represented by a covariant functor, not
  -- a contravariant one.  For the same reason, there's no contravariant
  -- component into `ConsF False NilF` -- that is also an initial object.
  --
  -- There's no contravariant component into `ConsF _ $ ConsF _ _` either,
  -- as that is a coproduct, which is represented by a covariant functor.
  -- `ConsF True NilF` is also a terminal object, which is represented by a
  -- contravariant const-`Unit`-valued functor.
  BNFterm : {0 a : Type} -> {0 m : BinNatAlg a} -> {0 f : a -> Type} ->
    BinNatFinContravar (a ** m) f (ConsF True $ m NilF)

-- The covariant component comes from `List Bool`'s being a coproduct
-- in this context (and from the empty list, or a list of `False`s, being
-- an initial object).
public export
data BinNatFinCovar : (alg : BinNatAlgObj) ->
    (fst alg -> Type) -> (BinNatF (fst alg) -> Type) where
  -- `NilF` is an initial object, which is represented by a covariant
  -- const-`Unit`-valued functor.
  BNFinitN : {0 a : Type} -> {0 m : BinNatAlg a} -> {0 f : a -> Type} ->
    BinNatFinCovar (a ** m) f NilF
  -- `ConsF False NilF` is also an initial object, which is represented by a
  -- covariant const-`Unit`-valued functor.
  BNFinitF : {0 a : Type} -> {0 m : BinNatAlg a} -> {0 f : a -> Type} ->
    BinNatFinCovar (a ** m) f (ConsF False $ m NilF)
  -- The covariant component out of `ConsF` is the product of the
  -- covariant components out of the `Bool` at the head and the `List Bool`
  -- at the tail.
  BNFcoprod : {0 a : Type} -> {0 m : BinNatAlg a} -> {0 f : a -> Type} ->
    {0 b : Bool} -> {0 ela : a} -> f (m (ConsF b (m NilF))) -> f ela ->
    BinNatFinCovar (a ** m) f (ConsF b ela)

public export
data BinNatMorph : (alg : BinNatAlgObj) -> fst alg -> fst alg -> Type where
  BNMid : {0 a : Type} -> {0 m : BinNatAlg a} ->
    (ela : a) -> BinNatMorph (a ** m) ela ela

-------------------------------------------------------
-------------------------------------------------------
---- Mutually-recursive family of slice categories ----
-------------------------------------------------------
-------------------------------------------------------

mutual
  public export
  data MinMLCat : Type where
    MMCbase : MinMLCat
    MMCslice : {0 cat : MinMLCat} -> MinMLObj cat -> MinMLCat

  public export
  data MinMLObj : MinMLCat -> Type where

  public export
  data MinMLMorph : {0 cat : MinMLCat} ->
      MinMLObj cat -> MinMLObj cat -> Type where

---------------------------------
---------------------------------
---- Computational substrate ----
---------------------------------
---------------------------------

-----------------------------------------------
---- Objects of category closest to `bitc` ----
-----------------------------------------------

public export
data CompCatObj : Type where
  CC1 : CompCatObj
  CCB : CompCatObj
  CCP : CompCatObj -> CompCatObj -> CompCatObj

public export
Show CompCatObj where
  show CC1 = "1"
  show CCB = "B"
  show (CCP a b) = "(" ++ show a ++ "*" ++ show b ++ ")"

public export
DecEq CompCatObj where
  decEq CC1 CC1 = Yes Refl
  decEq CCB CCB = Yes Refl
  decEq (CCP a b) (CCP a' b') =
    case decEq a a' of
      Yes Refl =>
        case decEq b b' of
          Yes Refl => Yes Refl
          No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
  decEq CC1 CCB = No $ \eq => case eq of Refl impossible
  decEq CC1 (CCP a b) = No $ \eq => case eq of Refl impossible
  decEq CCB CC1 = No $ \eq => case eq of Refl impossible
  decEq CCB (CCP a b) = No $ \eq => case eq of Refl impossible
  decEq (CCP a b) CC1 = No $ \eq => case eq of Refl impossible
  decEq (CCP a b) CCB = No $ \eq => case eq of Refl impossible

public export
Eq CompCatObj where
  a == b = isYes $ decEq a b

public export
CCInterpObj : CompCatObj -> Type
CCInterpObj CC1 = Unit
CCInterpObj CCB = Bool
CCInterpObj (CCP a b) = Pair (CCInterpObj a) (CCInterpObj b)

-------------------------------------------------
---- Morphisms of category closest to `bitc` ----
-------------------------------------------------

public export
data CompCatMorph : CompCatObj -> CompCatObj -> Type where
  CCid : (a : CompCatObj) -> CompCatMorph a a
  CCconst : (a : CompCatObj) -> {0 b : CompCatObj} ->
    CompCatMorph CC1 b -> CompCatMorph a b
  CCif : {0 a, b : CompCatObj} ->
    CompCatMorph a CCB -> CompCatMorph a b -> CompCatMorph a b ->
    CompCatMorph a b
  CCt : CompCatMorph CC1 CCB
  CCf : CompCatMorph CC1 CCB
  CCp : {0 a, b, c : CompCatObj} ->
    CompCatMorph a b -> CompCatMorph a c -> CompCatMorph a (CCP b c)
  CCp1 : {a, b, c : CompCatObj} ->
    CompCatMorph a (CCP b c) -> CompCatMorph a b
  CCp2 : {a, b, c : CompCatObj} ->
    CompCatMorph a (CCP b c) -> CompCatMorph a c

public export
Show (CompCatMorph a b) where
  show (CCid a) = "id"
  show (CCconst a t) = "![" ++ show t ++ "]"
  show (CCif cond tb fb) =
    "(" ++ show cond ++ " => " ++ show tb ++ " | " ++ show fb ++ ")"
  show CCt = "t"
  show CCf = "f"
  show (CCp f g) = "(" ++ show f ++ "*" ++ show g ++ ")"
  show (CCp1 f) = "p1(" ++ show f ++ ")"
  show (CCp2 f) = "p2(" ++ show f ++ ")"

public export
DecEq (CompCatMorph a b) where
  decEq (CCid a) (CCid a) = Yes Refl
  decEq (CCid _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCid _) (CCif _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCid _) (CCp _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCid _) (CCp1 _) = No $ \eq => case eq of Refl impossible
  decEq (CCid _) (CCp2 _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) (CCid _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst a t) (CCconst a t') = case decEq t t' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
  decEq (CCconst _ _) (CCif _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) CCt = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) CCf = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) (CCp _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) (CCp1 _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) (CCp2 _) = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _ _) (CCid _) = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _ _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCif cond tb fb) (CCif cond' tb' fb') =
    case (decEq cond cond', decEq tb tb', decEq fb fb') of
      (Yes Refl, Yes Refl, Yes Refl) => Yes Refl
      (No neq, _, _) => No $ \eq => case eq of Refl => neq Refl
      (_, No neq, _) => No $ \eq => case eq of Refl => neq Refl
      (_, _, No neq) => No $ \eq => case eq of Refl => neq Refl
  decEq (CCif _ _ _) CCt = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _ _) CCf = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _ _) (CCp _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _ _) (CCp1 _) = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _ _) (CCp2 _) = No $ \eq => case eq of Refl impossible
  decEq CCt (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq CCt (CCif _ _ _) = No $ \eq => case eq of Refl impossible
  decEq CCt CCt = Yes Refl
  decEq CCt CCf = No $ \eq => case eq of Refl impossible
  decEq CCt (CCp1 _) = No $ \eq => case eq of Refl impossible
  decEq CCt (CCp2 _) = No $ \eq => case eq of Refl impossible
  decEq CCf (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq CCf (CCif _ _ _) = No $ \eq => case eq of Refl impossible
  decEq CCf CCt = No $ \eq => case eq of Refl impossible
  decEq CCf CCf = Yes Refl
  decEq CCf (CCp1 _) = No $ \eq => case eq of Refl impossible
  decEq CCf (CCp2 _) = No $ \eq => case eq of Refl impossible
  decEq (CCp _ _) (CCid _ ) = No $ \eq => case eq of Refl impossible
  decEq (CCp _ _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp _ _) (CCif _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp f g) (CCp f' g') = case (decEq f f', decEq g g') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No neq, _) => No $ \eq => case eq of Refl => neq Refl
      (_, No neq) => No $ \eq => case eq of Refl => neq Refl
  decEq (CCp _ _) (CCp1 _) = No $ \eq => case eq of Refl impossible
  decEq (CCp _ _) (CCp2 _) = No $ \eq => case eq of Refl impossible
  decEq (CCp1 _) (CCid _) = No $ \eq => case eq of Refl impossible
  decEq (CCp1 _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp1 _) (CCif _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp1 _) CCt = No $ \eq => case eq of Refl impossible
  decEq (CCp1 _) CCf = No $ \eq => case eq of Refl impossible
  decEq (CCp1 _) (CCp _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp1 {a} {b} {c} f) (CCp1 {a} {b} {c=c'} g) =
    case decEq c c' of
      Yes Refl => case decEq f g of
        Yes Refl => Yes Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
  decEq (CCp1 _) (CCp2 _) = No $ \eq => case eq of Refl impossible
  decEq (CCp2 _) (CCid _) = No $ \eq => case eq of Refl impossible
  decEq (CCp2 _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp2 _) (CCif _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp2 _) CCt = No $ \eq => case eq of Refl impossible
  decEq (CCp2 _) CCf = No $ \eq => case eq of Refl impossible
  decEq (CCp2 _) (CCp _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCp2 _) (CCp1 _) = No $ \eq => case eq of Refl impossible
  decEq (CCp2 {a} {b} {c} f) (CCp2 {a} {b=b'} {c} g) =
    case decEq b b' of
      Yes Refl => case decEq f g of
        Yes Refl => Yes Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl

public export
Eq (CompCatMorph a b) where
  f == g = isYes $ decEq f g

-------------------------------------
---- Metalanguage interpretation ----
-------------------------------------

public export
ccInterpMorph : {a, b : CompCatObj} ->
  CompCatMorph a b -> CCInterpObj a -> CCInterpObj b
ccInterpMorph (CCid a) x = x
ccInterpMorph (CCconst _ t) _ = ccInterpMorph t ()
ccInterpMorph (CCif cond tb fb) x = case ccInterpMorph cond x of
  True => ccInterpMorph tb x
  False => ccInterpMorph fb x
ccInterpMorph CCt () = True
ccInterpMorph CCf () = False
ccInterpMorph (CCp f g) x = (ccInterpMorph f x, ccInterpMorph g x)
ccInterpMorph (CCp1 f) x = fst $ ccInterpMorph f x
ccInterpMorph (CCp2 f) x = snd $ ccInterpMorph f x

public export
ccInterpTerm : {a : CompCatObj} -> CompCatMorph CC1 a -> CCInterpObj a
ccInterpTerm t = ccInterpMorph t ()

-----------------------------------------------------
---- Composition (defined, not explicit in term) ----
-----------------------------------------------------

public export
ccComp : {a, b, c : CompCatObj} ->
  CompCatMorph b c -> CompCatMorph a b -> CompCatMorph a c
ccComp (CCid _) f = f
ccComp g (CCid _) = g
ccComp {a} (CCconst b {b=b'} t) f = CCconst a {b=b'} t
ccComp {a} {b} {c} (CCif {a=b} {b=c} cond g g') f =
  case ccComp cond f of
    CCt => ccComp g f
    CCf => ccComp g' f
    CCconst _ cond => case ccInterpTerm cond of
      True => ccComp g f
      False => ccComp g' f
    compcond => case a of
      CC1 => case ccInterpTerm compcond of
        True => ccComp g f
        False => ccComp g' f
      a' => CCif compcond (ccComp g f) (ccComp g' f)
ccComp {a} CCt _ = CCconst a {b=CCB} CCt
ccComp {a} CCf _ = CCconst a {b=CCB} CCf
ccComp (CCp g g') f = CCp (ccComp g f) (ccComp g' f)
ccComp {a} {b} {c} (CCp1 {a=b} {b=c} {c=c'} g) f =
  case g of
    CCp g1 g2 => ccComp g1 f
    g' => case ccComp g' f of
      CCp g'f1 g'f2 => g'f1
      g'f => CCp1 {a} {b=c} {c=c'} g'f
ccComp {a} {b} {c} (CCp2 {a=b} {b=b'} {c} g) f =
  case g of
    CCp g1 g2 => ccComp g2 f
    g' => case ccComp g' f of
      CCp g'f1 g'f2 => g'f2
      g'f => CCp2 {a} {b=b'} {c} g'f

-----------------------------
---- Universal morphisms ----
-----------------------------

public export
cm1 : (a : CompCatObj) -> CompCatMorph a CC1
cm1 a = CCconst a {b=CC1} $ CCid CC1

public export
cct : (a : CompCatObj) -> CompCatMorph a CCB
cct a = CCconst a {b=CCB} CCt

public export
cct1 : CompCatMorph CC1 CCB
cct1 = cct CC1

public export
ccf : (a : CompCatObj) -> CompCatMorph a CCB
ccf a = CCconst a {b=CCB} CCf

public export
ccf1 : CompCatMorph CC1 CCB
ccf1 = ccf CC1

public export
cmp1 : (a, b : CompCatObj) -> CompCatMorph (CCP a b) a
cmp1 a b = CCp1 {a=(CCP a b)} {b=a} {c=b} $ CCid $ CCP a b

public export
cmp2 : (a, b : CompCatObj) -> CompCatMorph (CCP a b) b
cmp2 a b = CCp2 {a=(CCP a b)} {b=a} {c=b} $ CCid $ CCP a b

public export
cmu : CompCatMorph CC1 CC1
cmu = CCid CC1

---------------------------
---- Cartesian closure ----
---------------------------

public export
ccHomObj : CompCatObj -> CompCatObj -> CompCatObj
ccHomObj CC1 b = b
ccHomObj CCB b = CCP b b
ccHomObj (CCP a b) c = ccHomObj a (ccHomObj b c)

public export
ccCurry : {a, b, c : CompCatObj} ->
  CompCatMorph (CCP a b) c -> CompCatMorph a (ccHomObj b c)
ccCurry {a} {b=CC1} {c} f = ccComp f $ CCp (CCid a) $ cm1 a
ccCurry {a} {b=CCB} {c} f =
  CCp (ccComp f $ CCp (CCid a) $ cct a) (ccComp f $ CCp (CCid a) $ ccf a)
ccCurry {a} {b=(CCP b b')} {c} f =
  ccCurry {a} {b} {c=(ccHomObj b' c)} $ ccCurry {a=(CCP a b)} {b=b'} {c} $
    ccComp f $
      CCp
        (ccComp (cmp1 a b) (cmp1 (CCP a b) b'))
        (CCp
          (ccComp (cmp2 a b) (cmp1 (CCP a b) b'))
          (cmp2 (CCP a b) b'))

public export
ccEval1 : (a : CompCatObj) -> CompCatMorph (CCP (ccHomObj CC1 a) CC1) a
ccEval1 a = cmp1 a CC1

public export
ccEval : (a, b : CompCatObj) -> CompCatMorph (CCP (ccHomObj a b) a) b
ccEval CC1 b = ccEval1 b
ccEval CCB b =
  CCif
    -- Second parameter to `eval` is condition
    (cmp2 (CCP b b) CCB)
    -- First half of first parameter to `eval` is true branch
    (ccComp (cmp1 b b) (cmp1 (CCP b b) CCB))
    -- Second half of first parameter to `eval` is false branch
    (ccComp (cmp2 b b) (cmp1 (CCP b b) CCB))
ccEval (CCP a a') b =
  ccComp
    (ccEval a' b) $
    CCp
      (ccComp
        (ccEval a $ ccHomObj a' b)
        (CCp
          (cmp1 (ccHomObj a (ccHomObj a' b)) (CCP a a'))
          (ccComp
            (cmp1 a a')
            (cmp2 (ccHomObj a (ccHomObj a' b)) (CCP a a')))))
      (ccComp (cmp2 a a') (cmp2 (ccHomObj a (ccHomObj a' b)) (CCP a a')))

public export
ccUncurry : {a, b, c : CompCatObj} ->
  CompCatMorph a (ccHomObj b c) -> CompCatMorph (CCP a b) c
ccUncurry {a} {b} {c} f =
  ccComp (ccEval b c) $ CCp (ccComp f (cmp1 a b)) (cmp2 a b)

-----------------
---- Quoting ----
-----------------

public export
CCHomTerm : CompCatObj -> CompCatObj -> Type
CCHomTerm a b = CompCatMorph CC1 (ccHomObj a b)

public export
ccUnquote : {a, b : CompCatObj} -> CCHomTerm a b -> CompCatMorph a b
ccUnquote {a} {b} t =
  ccComp (ccUncurry {a=CC1} {b=a} {c=b} t) $ CCp (cm1 a) (CCid a)

public export
ccQuote : {a, b : CompCatObj} -> CompCatMorph a b -> CCHomTerm a b
ccQuote {a} {b} f = ccCurry {a=CC1} {b=a} {c=b} $ ccComp f $ cmp2 CC1 a

---------------------------
---- Internal language ----
---------------------------

public export
CCGenTerm : {a : CompCatObj} -> CCInterpObj a -> CompCatMorph CC1 a
CCGenTerm {a=CC1} () = cmu
CCGenTerm {a=CCB} True = cct1
CCGenTerm {a=CCB} False = ccf1
CCGenTerm {a=(CCP a b)} (x, x') =
  CCp {a=CC1} {b=a} {c=b} (CCGenTerm x) (CCGenTerm x')

public export
CCMetaReduceTerm : {a : CompCatObj} -> CompCatMorph CC1 a -> CompCatMorph CC1 a
CCMetaReduceTerm t = CCGenTerm $ ccInterpTerm t

public export
CCHomInterpInv : (a, b : CompCatObj) ->
  (CCInterpObj a -> CCInterpObj b) -> CCInterpObj (ccHomObj a b)
CCHomInterpInv CC1 b f = f ()
CCHomInterpInv CCB b f = (f True, f False)
CCHomInterpInv (CCP a a') b f = CCHomInterpInv a (ccHomObj a' b) $
  CCHomInterpInv a' b . curry f

public export
CCGenMorph : {a, b : CompCatObj} ->
  (CCInterpObj a -> CCInterpObj b) -> CompCatMorph a b
CCGenMorph {a=CC1} {b} f = CCGenTerm {a=b} $ f ()
CCGenMorph {a=CCB} {b} f =
  CCif
    (CCid CCB)
    (CCconst CCB $ CCGenTerm $ f True)
    (CCconst CCB $ CCGenTerm $ f False)
CCGenMorph {a=(CCP a a')} {b} f =
  ccUncurry $ CCGenMorph {a} {b=(ccHomObj a' b)} $
  CCHomInterpInv a' b . curry f

-- Left adjunct of the boolean-defining adjunction.
public export
CCbla : {a : CompCatObj} ->
  CompCatMorph CC1 a -> CompCatMorph CC1 a -> CompCatMorph CCB a
CCbla f g = CCGenMorph $ \b => case b of
  True => ccInterpTerm f
  False => ccInterpTerm g

-- "True" branch of the right adjunct of the boolean-defining adjunction.
public export
CCbrat : {a : CompCatObj} -> CompCatMorph CCB a -> CompCatMorph CC1 a
CCbrat f = CCGenTerm $ ccInterpMorph f True

-- "False" branch of the right adjunct of the boolean-defining adjunction.
public export
CCbraf : {a : CompCatObj} -> CompCatMorph CCB a -> CompCatMorph CC1 a
CCbraf f = CCGenTerm $ ccInterpMorph f False

---------------------------------
---------------------------------
---- Minimal topos interface ----
---------------------------------
---------------------------------

{-
mutual
  public export
  data MinToposCat : Type where
    MTCb : MinToposCat
    MTCs : (cat : MinToposCat) -> MinToposObj cat -> MinToposCat

  public export
  data MinToposObj : MinToposCat -> Type where
    MT1 : (cat : MinToposCat) -> MinToposObj cat
    MTB : (cat : MinToposCat) -> MinToposObj cat
    MTP : {0 cat : MinToposCat} -> {0 x, y, z : MinToposObj cat} ->
      MinToposMorph {cat} x z -> MinToposMorph {cat} y z -> MinToposObj cat
    MTS : {0 cat : MinToposCat} -> {0 x : MinToposObj cat} ->
      MinToposMorph {cat} x z -> MinToposMorph {cat} y z -> MinToposObj cat
    MTT : {0 cat : MinToposCat} -> MinToposObj cat -> MinToposObj cat

  public export
  data MinToposMorph : {0 cat : MinToposCat} ->
      MinToposObj cat -> MinToposObj cat -> Type where
  public export
  data MinToposObj : Type where
    MTP : MinToposObj -> MinToposObj -> MinToposObj
    MTE : {0 a, b : MinToposObj} ->
      MinToposMorph a b -> MinToposMorph a b -> MinToposObj
    MTT : MinToposObj -> MinToposObj

  public export
  data MinToposMorph : MinToposObj -> MinToposObj -> Type where
    MTid : (a : MinToposObj) -> MinToposMorph a a
    MTcomp : {0 a, b, c : MinToposObj} ->
      MinToposMorph b c -> MinToposMorph a b -> MinToposMorph a c
    MTterm : (a : MinToposObj) -> MinToposMorph a MT1
    Mtif : {0 a : MinToposObj} ->
      MinToposMorph MT1 a -> MinToposMorph MT1 a -> MinToposMorph MTB a
    Mtbt : {0 a : MinToposObj} -> MinToposMorph MTB a -> MinToposMorph MT1 a
    Mtbf : {0 a : MinToposObj} -> MinToposMorph MTB a -> MinToposMorph MT1 a

  public export
  data MinToposEq : {0 a, b : MinToposObj} ->
      MinToposMorph a b -> MinToposMorph a b -> Type where

mutual
  public export
  interpMinToposObj : MinToposObj -> Type
  interpMinToposObj x = ?interpMinToposObj_hole

  public export
  interpMinToposMorph : {0 a, b : MinToposObj} ->
    MinToposMorph a b -> interpMinToposObj a -> interpMinToposObj b
  interpMinToposMorph f = ?interpMinToposMorph_hole

  public export
  interpMinToposEq : {0 a, b : MinToposObj} -> {0 f, g : MinToposMorph a b} ->
    MinToposEq {a} {b} f g ->
    ExtEq (interpMinToposMorph {a} {b} f) (interpMinToposMorph {a} {b} g)
  interpMinToposEq {a} {b} {f} {g} eq = ?interpMinToposEq_hole
    -}

-----------------------------------------
-----------------------------------------
---- FinSet as minimal digital topos ----
-----------------------------------------
-----------------------------------------

-- Unrefined version:  finite products of Booleans (the free Lawvere
-- theory with generic object `Bool`).
public export
data LawBoolObj : Type where
  -- The number of bits in the object.
  LBOn : Nat -> LawBoolObj

public export
DecEq LawBoolObj where
  decEq (LBOn m) (LBOn n) = case decEq m n of
    Yes Refl => Yes Refl
    No neq => case neq of Refl impossible

public export
Eq LawBoolObj where
  x == y = isYes $ decEq x y

public export
Show LawBoolObj where
  show (LBOn n) = "2^" ++ show n

public export
LawBoolSig : Type
LawBoolSig = ProductMonad LawBoolObj

public export
LBOTerminal : LawBoolObj
LBOTerminal = LBOn 0

public export
LBOBool : LawBoolObj
LBOBool = LBOn 1

public export
LawBoolMorphDom : Type
LawBoolMorphDom = LawBoolSig

public export
LawBoolMorphCod : Type
LawBoolMorphCod = LawBoolSig

public export
data LawBoolMorphPos : Type where
  LBMPosId : LawBoolObj -> LawBoolMorphPos
  LBMPosConst : LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosBranch : LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosProd : LawBoolObj -> LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosProj1 : LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosProj2 : LawBoolObj -> LawBoolObj -> LawBoolMorphPos

public export
data LawBoolMorphDir : Type where
  LBMDirId : LawBoolObj -> LawBoolMorphDir

public export
lbmSigma : LawBoolMorphPos -> LawBoolMorphCod
lbmSigma (LBMPosId x) = (x, x)
lbmSigma (LBMPosConst x y) = (x, y)
lbmSigma (LBMPosBranch (LBOn n) y) = (LBOn (S n), y)
lbmSigma (LBMPosProd x (LBOn m) (LBOn n)) = (x, LBOn (m + n))
lbmSigma (LBMPosProj1 (LBOn m) (LBOn n)) = (LBOn (m + n), LBOn m)
lbmSigma (LBMPosProj2 (LBOn m) (LBOn n)) = (LBOn (m + n), LBOn n)

public export
lbmPi : LawBoolMorphDir -> LawBoolMorphPos
lbmPi (LBMDirId x) = LBMPosId x

public export
lbmBaseChange : LawBoolMorphDir -> LawBoolMorphDom
lbmBaseChange (LBMDirId x) = (x, x)

public export
LawBoolMorphF : CSliceObj LawBoolSig -> CSliceObj LawBoolSig
LawBoolMorphF = CSPolyF lbmBaseChange lbmPi lbmSigma

---------------------------------------
---------------------------------------
---- Bool as (one-object) category ----
---------------------------------------
---------------------------------------

-------------------------------
---- Objects and morphisms ----
-------------------------------

public export
data BoolObj : Type where
  BOBool : BoolObj

public export
DecEq BoolObj where
  decEq BOBool BOBool = Yes Refl

public export
Eq BoolObj where
  b == b' = isYes (decEq b b')

public export
Show BoolObj where
  show BOBool = "Bool"

public export
data BoolMorph : Type where
  BMid : BoolMorph
  BMnot : BoolMorph
  BMtrue : BoolMorph
  BMfalse : BoolMorph

public export
DecEq BoolMorph where
  decEq BMid BMid = Yes Refl
  decEq BMid BMnot = No $ \eq => case eq of Refl impossible
  decEq BMid BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMid BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMnot BMid = No $ \eq => case eq of Refl impossible
  decEq BMnot BMnot = Yes Refl
  decEq BMnot BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMnot BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMid = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMnot = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMtrue = Yes Refl
  decEq BMtrue BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMid = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMnot = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMfalse = Yes Refl

public export
Eq BoolMorph where
  bm == bm' = isYes (decEq bm bm')

public export
Show BoolMorph where
  show BMid = "id"
  show BMnot = "not"
  show BMtrue = "t"
  show BMfalse = "f"

public export
bmDom : BoolMorph -> BoolObj
bmDom _ = BOBool

public export
bmCod : BoolMorph -> BoolObj
bmCod _ = BOBool

public export
bmId : (a : BoolObj) -> BoolMorph
bmId BOBool = BMid

public export
0 bmIdDom : (0 a : BoolObj) -> bmDom (bmId a) = a
bmIdDom BOBool = Refl

public export
0 bmIdCod : (0 a : BoolObj) -> bmCod (bmId a) = a
bmIdCod BOBool = Refl

public export
bmComp : (g, f : BoolMorph) -> bmCod f = bmDom g -> BoolMorph
bmComp BMid f Refl = f
bmComp BMnot BMid Refl = BMnot
bmComp BMnot BMnot Refl = BMid
bmComp BMnot BMtrue Refl = BMfalse
bmComp BMnot BMfalse Refl = BMtrue
bmComp BMtrue _ Refl = BMtrue
bmComp BMfalse _ Refl = BMfalse

public export
0 bmCompDom :
  (0 g, f : BoolMorph) -> {0 eq : bmCod f = bmDom g} ->
  bmDom (bmComp g f eq) = bmDom f
bmCompDom g f {eq} = Refl

public export
0 bmCompCod :
  (0 g, f : BoolMorph) -> {0 eq : bmCod f = bmDom g} ->
  bmCod (bmComp g f eq) = bmCod g
bmCompCod g f {eq} = Refl

------------------------------------
---- Interpretation into `Type` ----
------------------------------------

public export
interpBoolObj : BoolObj -> Type
interpBoolObj BOBool = Bool

public export
RefinedBoolMorph : BoolObj -> BoolObj -> Type
RefinedBoolMorph b b' =
  Refinement {a=BoolMorph} $ (\m => bmDom m == b && bmCod m == b')

public export
interpBoolMorph : {0 b, b' : BoolObj} -> RefinedBoolMorph b b' ->
  interpBoolObj b -> interpBoolObj b'
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMid eq) = id
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMnot eq) = not
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMtrue eq) = const True
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMfalse eq) = const False

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Boolean circuits (such as modeled by BITC) as a Lawvere theory ----
------------------------------------------------------------------------
------------------------------------------------------------------------

--------------------
---- Definition ----
--------------------

-- Every object of this category is some natural number of bits.
public export
data BCLawObj : Type where
  BCLOnbits : Nat -> BCLawObj

public export
DecEq BCLawObj where
  decEq (BCLOnbits m) (BCLOnbits n) = case decEq m n of
    Yes Refl => Yes Refl
    No neq => case neq of Refl impossible

public export
Eq BCLawObj where
  x == y = isYes $ decEq x y

public export
Show BCLawObj where
  show (BCLOnbits n) = "2^" ++ show n

public export
BCLawSig : Type
BCLawSig = (BCLawObj, BCLawObj)

-- The total space of morphisms in the boolean-Lawvere category.
-- Slices of this provide the morphisms indexed by signature
-- (domain and codomain).  These should compile very directly to BITC.
public export
data BCLawMorph : Type where
  -- The identity which is present in all categories.  Composition
  -- is not explicit here, but derived.
  BCLMid : BCLawObj -> BCLawMorph

  -- Every object of of the BCLaw category is a finite product (of Bool).
  --
  -- This is the left adjunct, which provides the product introduction rule.
  BCLMprodAdjL : List BCLawMorph -> BCLawMorph
  --
  -- This is the right adjunct, which provides the product elimination rule
  -- (in particular when applied to `id`, in which case it becomes the counit).
  -- The `Nat` parameter is an index into the returned list.
  BCLMprodAdjR : BCLawMorph -> Nat -> BCLawMorph

  -- Every BCLawObj with a non-zero number of bits may also be viewed as a
  -- product of the first bit (which itself is a coproduct of two terminal
  -- objects, which in turn are products of zero bits) with a BCLawObj with
  -- one fewer bit.  This is the right adjunct which distributes the product
  -- of the first bit with the rest of the bits over the coproduct which
  -- comprises the first bit, traverses the isomorphism between `1 * a` and `a`,
  -- and then applies the coproduct elimination rule (to produce from two
  -- morphisms of the same signature a morphism whose domain is one bit longer).
  BCLMbranchAdjR : BCLawMorph -> BCLawMorph -> BCLawMorph

  -- The left adjunct which inverts `BCLMbranchAdjR` -- a morphism from
  -- `1 + a` bits to `b` bits can be decomposed into two morphisms from
  -- `a` bits to `b` bits.
  BCLMbranchAdjL1 : BCLawMorph -> BCLawMorph
  BCLMbranchAdjL2 : BCLawMorph -> BCLawMorph

public export
DecEq BCLawMorph where
  decEq = decEqOne where
    mutual
      public export
      decEqOne : DecEqPred BCLawMorph
      decEqOne (BCLMid m) (BCLMid n) = case decEq m n of
        Yes Refl => Yes Refl
        No neq => case neq of Refl impossible
      decEqOne (BCLMid _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL fs) (BCLMprodAdjL gs) = case decEqList fs gs of
        Yes Refl => Yes Refl
        No neq => case neq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR f m) (BCLMprodAdjR g n) =
        case decEqOne f g of
          Yes Refl => case decEq m n of
            Yes Refl => Yes Refl
            No neq => case neq of Refl impossible
          No neq => case neq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR f g) (BCLMbranchAdjR f' g') =
        case (decEqOne f f', decEqOne g g') of
          (Yes Refl, Yes Refl) => Yes Refl
          (No neq, _) => No $ \eq => case eq of Refl => neq Refl
          (_, No neq) => No $ \eq => case eq of Refl => neq Refl
      decEqOne (BCLMbranchAdjR _ _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 f) (BCLMbranchAdjL1 g) =
        case decEqOne f g of
          Yes Refl => Yes Refl
          No neq => case neq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 f) (BCLMbranchAdjL2 g) =
        case decEqOne f g of
          Yes Refl => Yes Refl
          No neq => case neq of Refl impossible

      public export
      decEqList : DecEqPred (List BCLawMorph)
      decEqList [] [] = Yes Refl
      decEqList [] (_ :: _) = No $ \eq => case eq of Refl impossible
      decEqList (_ :: _) [] = No $ \eq => case eq of Refl impossible
      decEqList (f :: fs) (g :: gs) = case (decEqOne f g, decEqList fs gs) of
        (Yes Refl, Yes Refl) => Yes Refl
        (No neq, _) => No $ \eq => case eq of Refl => neq Refl
        (_, No neq) => No $ \eq => case eq of Refl => neq Refl

public export
Eq BCLawMorph where
  f == g = isYes $ decEq f g

public export
Show BCLawMorph where
  show = showOne where
    mutual
      public export
      showOne : BCLawMorph -> String
      showOne (BCLMid n) = "id[" ++ show n ++ "]"
      showOne (BCLMprodAdjL fs) = "prodAdjL[" ++ showList fs ++ "]"
      showOne (BCLMprodAdjR f n) =
        "prodAdjR[" ++ showOne f ++ ":" ++ show n ++ "]"
      showOne (BCLMbranchAdjR f g) =
        "branchAdjR[" ++ showOne f ++ "/" ++ showOne g ++ "]"
      showOne (BCLMbranchAdjL1 f) = "branchAdjL1[" ++ showOne f ++ "]"
      showOne (BCLMbranchAdjL2 f) = "branchAdjL2[" ++ showOne f ++ "]"

      public export
      showList : List BCLawMorph -> String
      showList fs = "[" ++ showListRec fs ++ "]"

      public export
      showListRec : List BCLawMorph -> String
      showListRec [] = ""
      showListRec (f :: []) = showOne f
      showListRec (f :: fs@(g :: gs)) = showOne f ++ ", " ++ showListRec fs

mutual
  public export
  checkBCLMOne : BCLawObj -> BCLawObj -> BCLawMorph -> Bool
  checkBCLMOne m n (BCLMid k) =
    m == k && n == k
  checkBCLMOne m (BCLOnbits n) (BCLMprodAdjL fs) =
    length fs == n && checkBCLMList m (BCLOnbits 1) fs
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMprodAdjR f k) =
    k < m && n == 1
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMbranchAdjR f g) =
    case m of
      S m' =>
        checkBCLMOne (BCLOnbits m') (BCLOnbits n) f &&
        checkBCLMOne (BCLOnbits m') (BCLOnbits n) g
      Z => False
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMbranchAdjL1 f) =
    checkBCLMOne (BCLOnbits (S m)) (BCLOnbits n) f
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMbranchAdjL2 f) =
    checkBCLMOne (BCLOnbits (S m)) (BCLOnbits n) f

  public export
  checkBCLMList : BCLawObj -> BCLawObj -> List BCLawMorph -> Bool
  checkBCLMList m n [] = True
  checkBCLMList m n (f :: fs) = checkBCLMOne m n f && checkBCLMList m n fs

public export
checkBCLM : BCLawSig -> BCLawMorph -> Bool
checkBCLM = uncurry checkBCLMOne

public export
checkBCLMs : BCLawSig -> List BCLawMorph -> Bool
checkBCLMs = uncurry checkBCLMList

public export
checkSignedBCLM : (BCLawSig, BCLawMorph) -> Bool
checkSignedBCLM = uncurry checkBCLM

public export
checkSignedBCLMs : (BCLawSig, List BCLawMorph) -> Bool
checkSignedBCLMs = uncurry checkBCLMs

public export
SignedBCLM : Type
SignedBCLM = PullbackDec {a=BCLawSig} {b=BCLawMorph} checkSignedBCLM

public export
SignedBCLMList : Type
SignedBCLMList = PullbackDec {a=BCLawSig} {b=(List BCLawMorph)} checkSignedBCLMs

---------------------
---- Composition ----
---------------------

------------------------------
---- Universal properties ----
------------------------------

--------------------------------------
--------------------------------------
---- Single-sorted Lawvere theory ----
--------------------------------------
--------------------------------------

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Single-sorted Lawvere theory with generic object `Bool` ----
-----------------------------------------------------------------
-----------------------------------------------------------------
