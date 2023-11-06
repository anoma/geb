module LanguageDef.NatPrefixCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

-------------------------------------------------------------
-------------------------------------------------------------
---- Natural numbers as objects representing finite sets ----
-------------------------------------------------------------
-------------------------------------------------------------

-- Define and translate two ways of interpreting natural numbers.

---------------------------------------
---- Bounded unary natural numbers ----
---------------------------------------

-- First, as coproducts of Unit.  As such, they are the first non-trivial
-- objects that can be formed in a category which is inductively defined as
-- the smallest one containing only (all) finite coproducts and finite products.
-- In this form, they are unary natural numbers, often suited as indexes.

public export
BUNat : Nat -> Type
BUNat Z = Void
BUNat (S n) = Either Unit (BUNat n)

public export
BUNatDepAlg :
  {0 p : (n : Nat) -> BUNat n -> Type} ->
  ((n : Nat) -> p (S n) (Left ())) ->
  ((n : Nat) ->
   ((bu : BUNat n) -> p n bu) ->
   (bu : BUNat n) -> p (S n) (Right bu)) ->
  NatDepAlgebra (\n => (bu : BUNat n) -> p n bu)
BUNatDepAlg {p} z s =
  (\bu => void bu,
   \n, hyp, bu => case bu of
    Left () => z n
    Right bu' => s n hyp bu')

public export
buNatDepCata :
  {0 p : (n : Nat) -> BUNat n -> Type} ->
  ((n : Nat) -> p (S n) (Left ())) ->
  ((n : Nat) ->
   ((bu : BUNat n) -> p n bu) ->
   (bu : BUNat n) -> p (S n) (Right bu)) ->
  (n : Nat) -> (bu : BUNat n) -> p n bu
buNatDepCata {p} z s = natDepCata (BUNatDepAlg {p} z s)

--------------------------------------------
---- Bounded arithmetic natural numbers ----
--------------------------------------------

-- Second, as bounds, which allow us to do bounded arithmetic,
-- or arithmetic modulo a given number.

public export
BoundedBy : Nat -> DecPred Nat
BoundedBy = gt

public export
NotBoundedBy : Nat -> DecPred Nat
NotBoundedBy = not .* BoundedBy

public export
IsBoundedBy : Nat -> Nat -> Type
IsBoundedBy = Satisfies . BoundedBy

public export
BANat : (0 _ : Nat) -> Type
BANat n = Refinement {a=Nat} (BoundedBy n)

public export
MkBANat : {0 n : Nat} -> (m : Nat) -> {auto 0 satisfies : IsBoundedBy n m} ->
  BANat n
MkBANat = MkRefinement

public export
baS : {0 n : Nat} -> BANat n -> BANat (S n)
baS (Element0 m lt) = Element0 (S m) lt

public export
baShowLong : {n : Nat} -> BANat n -> String
baShowLong {n} m = show m ++ "[<" ++ show n ++ "]"

public export
baNatDepCata :
  {0 p : (n : Nat) -> BANat n -> Type} ->
  ((n : Nat) -> p (S n) (Element0 0 Refl)) ->
  ((n : Nat) ->
   ((ba : BANat n) -> p n ba) ->
   (ba : BANat n) -> p (S n) (baS {n} ba)) ->
  (n : Nat) -> (ba : BANat n) -> p n ba
baNatDepCata {p} z s =
  natDepCata {p=(\n' => (ba' : BANat n') -> p n' ba')}
    (\ba => case ba of Element0 ba' Refl impossible,
     \n, hyp, ba => case ba of
      Element0 Z lt => rewrite uip {eq=lt} {eq'=Refl} in z n
      Element0 (S ba') lt => s n hyp (Element0 ba' lt))

-------------------------------------------------------------------
---- Translation between unary and arithmetic bounded naturals ----
-------------------------------------------------------------------

public export
u2a : {n : Nat} -> BUNat n -> BANat n
u2a {n=Z} v = void v
u2a {n=(S n)} (Left ()) = Element0 0 Refl
u2a {n=(S n)} (Right bu) with (u2a bu)
  u2a {n=(S n)} (Right bu) | Element0 bu' lt = Element0 (S bu') lt

public export
a2u : {n : Nat} -> BANat n -> BUNat n
a2u {n=Z} (Element0 ba Refl) impossible
a2u {n=(S n)} (Element0 Z lt) = Left ()
a2u {n=(S n)} (Element0 (S ba) lt) = Right $ a2u $ Element0 ba lt

public export
u2a2u_correct : {n : Nat} -> {bu : BUNat n} -> bu = a2u {n} (u2a {n} bu)
u2a2u_correct {n=Z} {bu} = void bu
u2a2u_correct {n=(S n)} {bu=(Left ())} = Refl
u2a2u_correct {n=(S n)} {bu=(Right bu)} with (u2a bu) proof eq
  u2a2u_correct {n=(S n)} {bu=(Right bu)} | Element0 m lt =
    rewrite (sym eq) in cong Right $ u2a2u_correct {n} {bu}

public export
a2u2a_fst_correct : {n : Nat} -> {ba : BANat n} ->
  fst0 ba = fst0 (u2a {n} (a2u {n} ba))
a2u2a_fst_correct {n=Z} {ba=(Element0 ba Refl)} impossible
a2u2a_fst_correct {n=(S n)} {ba=(Element0 Z lt)} = Refl
a2u2a_fst_correct {n=(S n)} {ba=(Element0 (S ba) lt)}
  with (u2a (a2u (Element0 ba lt))) proof p
    a2u2a_fst_correct {n=(S n)} {ba=(Element0 (S ba) lt)} | Element0 ba' lt' =
      cong S $ trans (a2u2a_fst_correct {ba=(Element0 ba lt)}) $ cong fst0 p

public export
a2u2a_correct : {n : Nat} -> {ba : BANat n} -> ba = u2a {n} (a2u {n} ba)
a2u2a_correct {n} {ba} = refinementFstEq $ a2u2a_fst_correct {n} {ba}

public export
MkBUNat : {n : Nat} -> (m : Nat) -> {auto 0 satisfies : IsBoundedBy n m} ->
  BUNat n
MkBUNat m {satisfies} = a2u (MkBANat m {satisfies})

public export
up2a : {n : Nat} -> (BUNat n -> Type) -> BANat n -> Type
up2a p ba = p (a2u ba)

public export
ap2u : {n : Nat} -> (BANat n -> Type) -> BUNat n -> Type
ap2u p bu = p (u2a bu)

public export
up2a_rewrite : {0 n : Nat} -> {0 p : BUNat n -> Type} ->
  {0 bu : BUNat n} -> p bu -> up2a {n} p (u2a {n} bu)
up2a_rewrite {p} t = replace {p} u2a2u_correct t

public export
ap2u_rewrite : {0 n : Nat} -> {0 p : BANat n -> Type} ->
  {0 ba : BANat n} -> p ba -> ap2u {n} p (a2u {n} ba)
ap2u_rewrite {p} t = replace {p} a2u2a_correct t

----------------------------------------
---- Bounded-natural-number objects ----
----------------------------------------

-- The bounded natural numbers can be interpreted as a category whose
-- objects are simply natural numbers (which give the bounds) and whose
-- morphisms are the polynomial circuit operations modulo the bounds.
-- An object is therefore specified simply by a natural number, and
-- interpreted as a Nat-bounded set.

public export
BNCatObj : Type
BNCatObj = Nat

-- We can interpret objects of the natural-number-bounded category as
-- bounded unary representations of Nat.
public export
bncInterpU : BNCatObj -> Type
bncInterpU = BUNat

-- We can also interpreted a `BNCatObj` as an arithmetic Nat-bounded set.
-- bounded unary representations of Nat.
public export
bncObjA : (0 _ : BNCatObj) -> Type
bncObjA = BANat

-- The simplest morphisms of the Nat-bounded-set category are specified
-- by spelling out, for each term of the domain, which term of the codomain
-- it maps to.
public export
BNCListMorph : Type
BNCListMorph = List Nat

-- For a given BNCListMorph, we can check whether it is a valid morphism
-- between a given pair of objects.
public export
checkVBNCLM : BNCatObj -> BNCatObj -> DecPred BNCListMorph
checkVBNCLM Z _ [] = True
checkVBNCLM Z _ (_ :: _) = False
checkVBNCLM (S _) _ [] = False
checkVBNCLM (S m') n (k :: ks) = BoundedBy n k && checkVBNCLM m' n ks

public export
isVBNCLM : BNCatObj -> BNCatObj -> BNCListMorph -> Type
isVBNCLM = Satisfies .* checkVBNCLM

-- Given a pair of objects, we can define a type dependent on those
-- objects representing just those BNCListMorphs which are valid
-- morphisms between those particular objects.

public export
VBNCLM : BNCatObj -> BNCatObj -> Type
VBNCLM m n = Refinement {a=BNCListMorph} $ checkVBNCLM m n

public export
MkVBNCLM : {0 m, n : BNCatObj} -> (l : BNCListMorph) ->
  {auto 0 satisfies : isVBNCLM m n l} -> VBNCLM m n
MkVBNCLM l {satisfies} = MkRefinement l {satisfies}

-- We can interpret a valid list-specified morphism as a function
-- of the metalanguage.
public export
bncLMA : {m, n : BNCatObj} -> VBNCLM m n -> BANat m -> BANat n
bncLMA {m=Z} {n} (Element0 [] kvalid) (Element0 p pvalid) = exfalsoFT pvalid
bncLMA {m=(S _)} {n} (Element0 [] kvalid) vp = exfalsoFT kvalid
bncLMA {m=(S m)} {n} (Element0 (k :: ks) kvalid) (Element0 Z pvalid) =
  Element0 k (andLeft kvalid)
bncLMA {m=(S m)} {n} (Element0 (k :: ks) kvalid) (Element0 (S p) pvalid) =
  bncLMA {m} {n} (Element0 ks (andRight kvalid)) (Element0 p pvalid)

-- Utility function for applying a bncLMA to a Nat that can be
-- validated at compile time as satisfying the bounds.
public export
bncLMAN : {m, n : BNCatObj} -> VBNCLM m n -> (k : Nat) ->
  {auto 0 satisfies : IsBoundedBy m k} -> BANat n
bncLMAN lm k {satisfies} = bncLMA lm $ MkBANat k {satisfies}

-- Utility function for applying bncLMAN and then forgetting the
-- constraint on the output.
public export
bncLMANN : {m, n : BNCatObj} -> VBNCLM m n -> (k : Nat) ->
  {auto 0 satisfies : IsBoundedBy m k} -> Nat
bncLMANN l k {satisfies} = fst0 $ bncLMAN l k {satisfies}

-- Another class of morphism in the category of bounded arithmetic
-- natural numbers is the polynomial functions -- constants, addition,
-- multiplication.  Because we are so far defining only a "single-variable"
-- category, we can make all such morphisms valid (as opposed to invalid if
-- they fail bound checks) by performing the arithmetic modulo the sizes
-- of the domain and codomain.

-- Thus we can in particular interpret any metalanguage function on the
-- natural numbers as a function from any BANat object to any non-empty
-- BANat object by post-composing with modulus.

public export
metaToNatToBNC : {n : Nat} -> (Integer -> Integer) -> Nat -> BANat (S n)
metaToNatToBNC {n} f k =
  let
    k' = natToInteger k
    fk = integerToNat $ f k'
  in
  Element0 (modNatNZ fk (S n) SIsNonZero) (modLtDivisor fk n)

public export
metaToBNCToBNC : {m, n : Nat} -> (Integer -> Integer) -> BANat m -> BANat (S n)
metaToBNCToBNC f (Element0 k _) = metaToNatToBNC {n} f k

-- Object-language representation of polynomial morphisms.

prefix 11 #|
infixr 8 #+
infix 8 #-
infixr 9 #*
infix 9 #/
infix 9 #%
infixr 2 #.

public export
data BNCPolyM : Type where
  -- Polynomial operations --

  -- Constant
  (#|) : Nat -> BNCPolyM

  -- Identity
  PI : BNCPolyM

  -- Compose
  (#.) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Add
  (#+) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Multiply
  (#*) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Inverse operations --

  -- Subtract
  (#-) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Divide (division by zero returns zero)
  (#/) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Modulus (modulus by zero returns zero)
  (#%) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Branch operation(s)

  -- Compare with zero: equal takes first branch; not-equal takes second branch
  IfZero : BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM

  -- If the first argument is strictly less than the second, then
  -- take the first branch (which is the third argument); otherwise,
  -- take the second branch (which is the fourth argument)
  IfLT : BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM

public export
record BNCPolyMAlg (0 a : BNCPolyM -> Type) where
  constructor MkBNCPolyAlg
  bncaConst : (n : Nat) -> a (#| n)
  bncaId : a PI
  bncaCompose : (q, p : BNCPolyM) -> a q -> a p -> a (q #. p)
  bncaAdd : (p, q : BNCPolyM) -> a p -> a q -> a (p #+ q)
  bncaMul : (p, q : BNCPolyM) -> a p -> a q -> a (p #* q)
  bncaSub : (p, q : BNCPolyM) -> a p -> a q -> a (p #- q)
  bncaDiv : (p, q : BNCPolyM) -> a p -> a q -> a (p #/ q)
  bncaMod : (p, q : BNCPolyM) -> a p -> a q -> a (p #% q)
  bncaIfZ : (p, q, r : BNCPolyM) -> a p -> a q -> a r -> a (IfZero p q r)
  bncaIfLT :
     (p, q, r, s : BNCPolyM) -> a p -> a q -> a r -> a s -> a (IfLT p q r s)

public export
bncPolyMInd : {0 a : BNCPolyM -> Type} -> BNCPolyMAlg a -> (p : BNCPolyM) -> a p
bncPolyMInd alg (#| k) = bncaConst alg k
bncPolyMInd alg PI = bncaId alg
bncPolyMInd alg (q #. p) =
  bncaCompose alg q p (bncPolyMInd alg q) (bncPolyMInd alg p)
bncPolyMInd alg (p #+ q) =
  bncaAdd alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #* q) =
  bncaMul alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #- q) =
  bncaSub alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #/ q) =
  bncaDiv alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #% q) =
  bncaMod alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (IfZero p q r) =
  bncaIfZ alg p q r (bncPolyMInd alg p) (bncPolyMInd alg q) (bncPolyMInd alg r)
bncPolyMInd alg (IfLT p q r s) =
  bncaIfLT alg p q r s
    (bncPolyMInd alg p) (bncPolyMInd alg q)
    (bncPolyMInd alg r) (bncPolyMInd alg s)

public export
showInfix : (is, ls, rs : String) -> String
showInfix is ls rs = "(" ++ ls ++ ") " ++ is ++ " (" ++ rs ++ ")"

public export
const2ShowInfix : {0 a, b : Type} ->
  (is : String) -> a -> b -> (ls, rs : String) -> String
const2ShowInfix is _ _ = showInfix is

public export
BNCPMshowAlg : BNCPolyMAlg (const String)
BNCPMshowAlg = MkBNCPolyAlg
  show
  "PI"
  (const2ShowInfix ".")
  (const2ShowInfix "+")
  (const2ShowInfix "*")
  (const2ShowInfix "-")
  (const2ShowInfix "/")
  (const2ShowInfix "%")
  (\_, _, _, ps, qs, rs =>
    "(" ++ ps ++ " == 0 ? " ++ qs ++ " : " ++ rs ++ ")")
  (\_, _, _, _, ps, qs, rs, ss =>
    "(" ++ ps ++ " < " ++ qs ++ " ? " ++ rs ++ " : " ++ ss ++ ")")

public export
Show BNCPolyM where
  show  = bncPolyMInd BNCPMshowAlg

public export
P0 : BNCPolyM
P0 = #| 0

public export
P1 : BNCPolyM
P1 = #| 1

public export
powerAcc : BNCPolyM -> Nat -> BNCPolyM -> BNCPolyM
powerAcc p Z acc = acc
powerAcc p (S n) acc = powerAcc p n (p #* acc)

infixl 10 #^
public export
(#^) : BNCPolyM -> Nat -> BNCPolyM
(#^) p n = powerAcc p n P1

-- Interpret a BNCPolyM into the metalanguage.
public export
MetaBNCPolyMAlg : BNCPolyMAlg (\_ => Integer -> Integer)
MetaBNCPolyMAlg = MkBNCPolyAlg
  (\n, _ => natToInteger n)
  id
  (\q, p, qf, pf, k => qf (pf k))
  (\p, q, pf, qf, k => pf k + qf k)
  (\p, q, pf, qf, k => pf k * qf k)
  (\p, q, pf, qf, k => pf k - qf k)
  (\p, q, pf, qf, k => divWithZtoZ (pf k) (qf k))
  (\p, q, pf, qf, k => modWithZtoZ (pf k) (qf k))
  (\p, q, r, pf, qf, rf, k => if pf k == 0 then qf k else rf k)
  (\p, q, r, s, pf, qf, rf, sf, k => if pf k < qf k then rf k else sf k)

public export
metaBNCPolyM : (modpred : Integer) -> BNCPolyM -> Integer -> Integer
metaBNCPolyM modpred p n = modSucc (bncPolyMInd MetaBNCPolyMAlg p n) modpred

-- Interpret a BNCPolyM as a function between BANat objects.
public export
baPolyM : {m, n : Nat} -> BNCPolyM -> BANat m -> BANat (S n)
baPolyM {n} p = metaToBNCToBNC (metaBNCPolyM (natToInteger n) p)

--------------------------------------
--------------------------------------
---- Objects and morphisms of Fin ----
--------------------------------------
--------------------------------------

-- Interpreted as the cardinality of a set.
public export
FSObj : Type
FSObj = Nat

public export
FSElem : FSObj -> Type
FSElem = Fin

-- Morphisms between finite sets.
public export
FSMorph : FSObj -> FSObj -> Type
FSMorph m n = Vect m (Fin n)

public export
FSId : (a : FSObj) -> FSMorph a a
FSId a = finFToVect id

public export
FSApply : {a, b : FSObj} -> FSMorph a b -> FSElem a -> FSElem b
FSApply = flip index

public export
FSCompose : {a, b, c : FSObj} -> FSMorph b c -> FSMorph a b -> FSMorph a c
FSCompose g f = finFToVect (FSApply g . FSApply f)

public export
FSInitial : FSObj
FSInitial = 0

public export
fsFromInitial : (a : FSObj) -> FSMorph FSInitial a
fsFromInitial _ = []

public export
FSTerminal : FSObj
FSTerminal = 1

public export
FSToTerminal : (a : FSObj) -> FSMorph a FSTerminal
FSToTerminal a = finFToVect (const FZ)

public export
FSCoproduct : FSObj -> FSObj -> FSObj
FSCoproduct = (+)

public export
fsCopIntroLeft : (a, b : FSObj) -> FSMorph a (FSCoproduct a b)
fsCopIntroLeft a b = finFToVect (weakenN b)

public export
fsCopIntroRight : (a, b : FSObj) -> FSMorph b (FSCoproduct a b)
fsCopIntroRight a b = finFToVect (shift a)

public export
fsCopElim : {a, b, c : FSObj} ->
  FSMorph a c -> FSMorph b c -> FSMorph (FSCoproduct a b) c
fsCopElim f g = f ++ g

public export
FSProduct : FSObj -> FSObj -> FSObj
FSProduct = (*)

public export
fsProdIntro : {a, b, c : FSObj} ->
  FSMorph a b -> FSMorph a c -> FSMorph a (FSProduct b c)
fsProdIntro {a} {b} {c} f g =
  finFToVect $ \i =>
    natToFinLT
      {prf=(multAddLT (finToNatLT (FSApply f i)) (finToNatLT (FSApply g i)))}
      (c * finToNat (FSApply f i) + finToNat (FSApply g i))

public export
fsProdElimLeft : (a, b : FSObj) -> FSMorph (FSProduct a b) a
fsProdElimLeft a Z = rewrite multZeroRightZero a in []
fsProdElimLeft a (S b) =
  finFToVect $ \i =>
    natToFinLT
      {prf=(multDivLT (finToNatLT i) SIsNonZero)}
      (divNatNZ (finToNat i) (S b) SIsNonZero)

public export
fsProdElimRight : (a, b : FSObj) -> FSMorph (FSProduct a b) b
fsProdElimRight a Z = rewrite multZeroRightZero a in []
fsProdElimRight a (S b) =
  finFToVect $ \i =>
    natToFinLT
      {prf=(modLTDivisor (finToNat i) b)}
      (modNatNZ (finToNat i) (S b) SIsNonZero)

public export
FSExpObj : FSObj -> FSObj -> FSObj
FSExpObj = power

public export
FSHomObj : FSObj -> FSObj -> FSObj
FSHomObj = flip FSExpObj

public export
fsPowerElimRight : (a, b : FSObj) -> FSMorph (FSHomObj a (S b)) (S b)
fsPowerElimRight a b =
  finFToVect $ \i =>
    natToFinLT
      {prf=(modLTDivisor (finToNat i) b)}
      (modNatNZ (finToNat i) (S b) SIsNonZero)

public export
fsEval : (a, b : FSObj) -> FSMorph (FSProduct (FSHomObj a b) a) b
fsEval Z b = []
fsEval (S a) Z = []
fsEval (S a) (S b) =
  rewrite multRightSuccPlus (mult (S b) (power (S b) a)) a in
  rewrite sym (multAssociative (S b) (power (S b) a) a) in
  rewrite sym (multDistributesOverPlusRight
    (S b) (power (S b) a) (mult (power (S b) a) a)) in
  vectRepeat (S b) (fsPowerElimRight a b ++ fsEval a (S b))

public export
fsCurry : {a, b, c : FSObj} ->
  FSMorph (FSProduct a b) c -> FSMorph a (FSHomObj b c)
fsCurry {a} {b=Z} {c} f =
  rewrite sym (multOneRightNeutral a) in vectRepeat a [FZ]
fsCurry {a=Z} {b=(S b)} {c=Z} [] = []
fsCurry {a=(S a)} {b=(S b)} {c=Z} (x :: _) = absurd x
fsCurry {a} {b=(S b)} {c=(S Z)} f =
  finFToVect $ \i =>
    rewrite powerOneIsOne b in
    rewrite plusZeroRightNeutral 1 in
    FZ
fsCurry {a} {b=(S b)} {c=(S (S c))} f =
  let
    f' = replace {p=(flip Vect (Fin (S (S c))))} (multRightSuccPlus a b) f
    (fhd, ftl) = splitAt _ f'
    cftl = fsCurry {a} {b} {c=(S (S c))} ftl
  in
  finFToVect $ \i =>
    let
      fhdi = FSApply fhd i
      ftli = FSApply cftl i
    in
    finPlus (finPow _ b fhdi) (finMul _ c ftli)

public export
fsUncurry : {a, b, c : FSObj} ->
  FSMorph a (FSHomObj b c) -> FSMorph (FSProduct a b) c
fsUncurry {a} {b} {c} f =
  FSCompose
    (fsEval b c)
    (fsProdIntro (FSCompose f $ fsProdElimLeft _ _) (fsProdElimRight _ _))

public export
FSHomElem : FSObj -> FSObj -> Type
FSHomElem = FSElem .* FSHomObj

public export
FSHomElemToMorph : {x, y : FSObj} -> FSHomElem x y -> FSMorph x y
FSHomElemToMorph {x} {y} t =
  rewrite sym (plusZeroRightNeutral x) in
  fsUncurry {a=FSTerminal} {b=x} {c=y} [t]

public export
FSMorphToHomElem : {x, y : FSObj} -> FSMorph x y -> FSHomElem x y
FSMorphToHomElem {x} {y} t =
  let
    t' = rewrite plusZeroRightNeutral x in t
    ct = fsCurry {a=FSTerminal} {b=x} {c=y} t'
  in
  case ct of [t''] => t''

-----------------------------------
-----------------------------------
---- Dependent types in FinSet ----
-----------------------------------
-----------------------------------

public export
FSTypeFam : FSObj -> Type
FSTypeFam n = Vect n FSObj

public export
FSTypeFamObj : {n : FSObj} -> FSTypeFam n -> FSElem n -> FSObj
FSTypeFamObj fam i = index i fam

public export
FSTypeFamType : {n : FSObj} -> FSTypeFam n -> FSElem n -> Type
FSTypeFamType fam i = FSElem (FSTypeFamObj fam i)

public export
FSTypeFamTypes : {n : FSObj} -> FSTypeFam n -> Vect n Type
FSTypeFamTypes {n} = finFToVect . FSTypeFamType {n}

public export
FSBaseChange : {m, n : FSObj} -> FSTypeFam m -> FSMorph n m -> FSTypeFam n
FSBaseChange {m} {n} fam f = finFToVect $ FSTypeFamObj fam . FSApply f

public export
FSIndexedPair : {m, n : FSObj} ->
  FSTypeFam m -> FSMorph m n -> FSElem n -> Type
FSIndexedPair fam f i =
  (j : Fin m ** (FSApply f j = i, FSElem $ FSTypeFamObj fam j))

public export
FSDepCoproductTypes : {m, n : FSObj} ->
  FSTypeFam m -> FSMorph m n -> Vect n Type
FSDepCoproductTypes {m} {n} fam f = finFToVect $ FSIndexedPair fam f

public export
FSIndexedMorph : {m, n : FSObj} ->
  FSTypeFam m -> FSMorph m n -> FSElem n -> Type
FSIndexedMorph {m} {n} fam f i =
  (j : Fin m) -> FSApply f j = i -> FSElem $ FSTypeFamObj fam j

public export
FSDepProductTypes : {m, n : FSObj} ->
  FSTypeFam m -> FSMorph m n -> Vect n Type
FSDepProductTypes {m} {n} fam f = finFToVect $ FSIndexedMorph fam f

---------------------------------
---------------------------------
---- Derived types in FinSet ----
---------------------------------
---------------------------------

------------------
---- Booleans ----
------------------

public export
FSBool : FSObj
FSBool = FSCoproduct FSTerminal FSTerminal

public export
FSFalse : FSElem FSBool
FSFalse = FZ

public export
FSTrue : FSElem FSBool
FSTrue = FS FZ

public export
fsToBool : FSElem FSBool -> Bool
fsToBool FZ = False
fsToBool (FS FZ) = True

public export
boolToFS : Bool -> FSElem FSBool
boolToFS False = FSFalse
boolToFS True = FSTrue

public export
FSPred : FSObj -> Type
FSPred a = FSMorph a FSBool

public export
FSPredObj : FSObj -> FSObj
FSPredObj a = FSHomObj a FSBool

public export
FSEqualizerPred : {a, b : FSObj} -> FSMorph a b -> FSMorph a b -> FSPred a
FSEqualizerPred {a} {b} f g =
  finFToVect $ \i => if FSApply f i == FSApply g i then FSTrue else FSFalse

--------------
---- ADTs ----
--------------

public export
FSCoproductList : List FSObj -> FSObj
FSCoproductList = foldr FSCoproduct FSInitial

public export
FSProductList : List FSObj -> FSObj
FSProductList = foldr FSProduct FSTerminal

public export
FSFoldConstructor : FSObj -> FSObj -> FSObj -> FSObj
FSFoldConstructor type adt nfields = FSCoproduct adt (FSExpObj type nfields)

------------------------
------------------------
---- Fin as a topos ----
------------------------
------------------------

public export
RefinedFSObj : Type
RefinedFSObj = DPair FSObj FSPred

public export
RFSElem : RefinedFSObj -> Type
RFSElem = FSElem . fst

public export
isRFSElem : (bv : RefinedFSObj) -> RFSElem bv -> Bool
isRFSElem (n ** pred) t = fsToBool (index t pred)

public export
RFSIsElem : (bv : RefinedFSObj) -> RFSElem bv -> Type
RFSIsElem bv i = IsTrue (isRFSElem bv i)

public export
RefinedFSObjFromFunc : {n : Nat} -> (Fin n -> Bool) -> RefinedFSObj
RefinedFSObjFromFunc {n} f = (n ** finFToVect $ boolToFS . f)

public export
RefinedFin : RefinedFSObj -> Type
RefinedFin bv = Subset0 (RFSElem bv) (RFSIsElem bv)

public export
MaybeRefinedFin : RefinedFSObj -> Bool -> Type
MaybeRefinedFin nv True = RefinedFin nv
MaybeRefinedFin nv False = Unit

public export
RefinedFinMorphElemType : (dom, cod : RefinedFSObj) -> RFSElem dom -> Type
RefinedFinMorphElemType mv nv i = MaybeRefinedFin nv (isRFSElem mv i)

public export
getRFElem : {dom, cod : RefinedFSObj} -> {i : RFSElem dom} ->
  RefinedFinMorphElemType dom cod i -> isRFSElem dom i = True -> RefinedFin cod
getRFElem {dom} {cod} {i} t eq with (isRFSElem dom i)
  getRFElem {dom} {cod} {i} t eq | True = t
  getRFElem {dom} {cod} {i} t Refl | False impossible

public export
RefinedFinMorphTypes : (dom, cod : RefinedFSObj) -> Vect (fst dom) Type
RefinedFinMorphTypes mv nv = finFToVect $ RefinedFinMorphElemType mv nv

public export
RefinedFinMorph : RefinedFSObj -> RefinedFSObj -> Type
RefinedFinMorph mv nv = HVect (RefinedFinMorphTypes mv nv)

public export
RFMIdElem : (bv : RefinedFSObj) -> (i : Fin (fst bv)) ->
  MaybeRefinedFin bv (isRFSElem bv i)
RFMIdElem bv i with (isRFSElem bv i) proof isElem
  RFMIdElem bv i | True = Element0 i isElem
  RFMIdElem bv i | False = ()

public export
RFMId : (bv : RefinedFSObj) -> RefinedFinMorph bv bv
RFMId bv = finHFToHVect (RFMIdElem bv)

public export
RFMApply : {dom, cod : RefinedFSObj} ->
  RefinedFinMorph dom cod -> RefinedFin dom -> RefinedFin cod
RFMApply {dom} {cod} m (Element0 i ok) with (isRFSElem dom i) proof prf
  RFMApply {dom} {cod} m (Element0 i Refl) | True =
    replace {p=(MaybeRefinedFin cod)} prf $ finFGet i m
  RFMApply {dom} {cod} m (Element0 i Refl) | False impossible

public export
RFMComposeElem : {a, b, c : RefinedFSObj} ->
  (g : RefinedFinMorph b c) -> (f : RefinedFinMorph a b) ->
  (i : RFSElem a) -> MaybeRefinedFin c (isRFSElem a i)
RFMComposeElem {a} {b} {c} g f i with (isRFSElem a i) proof isElem
  RFMComposeElem {a} {b} {c} g f i | True =
    RFMApply g $ getRFElem (finFGet i f) isElem
  RFMComposeElem {a} {b} {c} g f i | False = ()

public export
RFMCompose : {a, b, c : RefinedFSObj} ->
  RefinedFinMorph b c -> RefinedFinMorph a b -> RefinedFinMorph a c
RFMCompose g f = finHFToHVect (RFMComposeElem g f)

-------------------------------------------
-------------------------------------------
---- Polynomial endofunctors in FinSet ----
-------------------------------------------
-------------------------------------------

---------------------------------------------------
---- Polynomial endofunctors as dependent sets ----
---------------------------------------------------

-- We will use polynomial endofunctors of FinSet to define our first
-- recursive types.

public export
FSPolyF : Type
-- The length of the list is the number of positions (so the position set
-- is the set of natural numbers less than the length of the list),
-- and each element is the number of directions at the corresponding position
-- (so the direction set is the set of natural numbers less than the element).
FSPolyF = List FSObj

public export
fsPolyNPos : FSPolyF -> FSObj
fsPolyNPos = length

public export
fsPolyPos : FSPolyF -> Type
fsPolyPos p = FSElem (fsPolyNPos p)

public export
fsPolyNDir : (p : FSPolyF) -> fsPolyPos p -> FSObj
fsPolyNDir a i = index' a i

public export
fsPolyDir : (p : FSPolyF) -> fsPolyPos p -> Type
fsPolyDir p i = FSElem (fsPolyNDir p i)

public export
FSExpMap : FSObj -> List FSObj -> List FSObj
FSExpMap n l = map (FSExpObj n) l

public export
FSPolyApply : FSPolyF -> FSObj -> FSObj
FSPolyApply a n = FSCoproductList (FSExpMap n a)

public export
FSPolyFunc : Type
FSPolyFunc = (pos : Type ** pos -> Type)

public export
fspPF : FSPolyF -> FSPolyFunc
fspPF p = (fsPolyPos p ** fsPolyDir p)

public export
fsPolyProd : (p : FSPolyF) -> fsPolyPos p -> Type -> Type
fsPolyProd p i = Vect (fsPolyNDir p i)

public export
FSRepresentableMap : {m, n, x : Nat} ->
  FSMorph m n -> FSMorph (power m x) (power n x)
FSRepresentableMap {m} {n} {x=Z} f = [FZ]
FSRepresentableMap {m} {n} {x=(S x)} f =
  let
    l = fsProdElimLeft m (power m x)
    r = fsProdElimRight m (power m x)
  in
  fsProdIntro {a=(mult m (power m x))} {b=n} {c=(power n x)}
    (FSCompose f l)
    (FSCompose (FSRepresentableMap {m} {n} {x} f) r)

public export
FSPolyMapList : (l : List Nat) -> {m, n : FSObj} ->
  FSMorph m n ->
  FSMorph (FSPolyApply l m) (FSPolyApply l n)
FSPolyMapList [] {m} {n} v = []
FSPolyMapList (x :: xs) {m} {n} v =
  map (weakenN (FSCoproductList (FSExpMap n xs))) (FSRepresentableMap v) ++
  map (shift (power n x)) (FSPolyMapList xs {m} {n} v)

public export
FSPolyMap : (p : FSPolyF) -> {m, n : FSObj} ->
  FSMorph m n -> FSMorph (FSPolyApply p m) (FSPolyApply p n)
FSPolyMap l v = FSPolyMapList l v

public export
InterpFSPolyF : FSPolyF -> Type -> Type
InterpFSPolyF p x = (i : fsPolyPos p ** fsPolyProd p i x)

public export
InterpFSPolyFMap : (p : FSPolyF) -> {0 a, b : Type} ->
  (a -> b) -> InterpFSPolyF p a -> InterpFSPolyF p b
InterpFSPolyFMap p m (i ** d) = (i ** map m d)

public export
(p : FSPolyF) => Functor (InterpFSPolyF p) where
  map {p} = InterpFSPolyFMap p

----------------------------------------------
---- Polynomial functors as slice objects ----
----------------------------------------------

-- A polynomial endofunctor may also be viewed as a slice object
-- (in the slice category over its type of positions).
-- (Similarly, it may also be viewed as an object of the
-- arrow category.)

public export
FSSlice : FSObj -> Type
FSSlice = FSTypeFam

public export
FSSliceToType : {n : FSObj} -> FSSlice n -> SliceObj (FSElem n)
FSSliceToType = FSTypeFamType

public export
FSPolyFToSlice : (p : FSPolyF) -> FSSlice (fsPolyNPos p)
FSPolyFToSlice = fromList

public export
SliceToFSPolyF : {n : FSObj} -> FSSlice n -> FSPolyF
SliceToFSPolyF {n} = toList

public export
FSSliceFiberMap : {n : FSObj} -> FSSlice n -> FSSlice n -> FSElem n -> Type
FSSliceFiberMap sl sl' i = FSMorph (index i sl) (index i sl')

public export
FSSliceMorphism : {n : FSObj} -> FSSlice n -> FSSlice n -> Type
FSSliceMorphism {n} sl sl' = HVect $ finFToVect (FSSliceFiberMap sl sl')

public export
FSSliceMorphToType : {n : FSObj} -> {sl, sl' : FSSlice n} ->
  FSSliceMorphism sl sl' -> SliceMorphism (FSSliceToType sl) (FSSliceToType sl')
FSSliceMorphToType {n} {sl} {sl'} m i d = Vect.index d $ finFGet i m

------------------------------------------------------------------
---- FinSet slices, and polynomial endofunctors, as morphisms ----
------------------------------------------------------------------

-- A slice object over `Fin n` in the category of finite prefixes of the natural
-- numbers may be viewed as a morphism in that category from `Fin n` to another
-- prefix of the natural numbers `Fin m` for some natural number `m` --
-- specifically, where `m` is the successor of the maximum cardinality of the
-- types in the type family which corresponds to the dependent-type view of the
-- slice object.  (The dependent-type view is that a slice object over `Fin n`
-- is a type family indexed by `Fin n`, where the dependent sum of the family is
-- the "total space" -- the domain of the morphism which defines the slice
-- object -- in the category-theoretic view.)  Note that the category-theoretic
-- definition of "slice object" uses a morphism _to_ `Fin n`, whereas this
-- type-theoretic view gives us an interpretation of that same slice object
-- as a morphism _from_ `Fin n`.

public export
FSSliceToMorph : {n : FSObj} -> (sl : FSSlice n) -> FSMorph n (S (vectMax sl))
FSSliceToMorph {n} sl = finFToVect $ vectMaxGet sl

public export
FSMorphToSlice : {m, n : FSObj} -> FSMorph m n -> FSSlice m
FSMorphToSlice {m} {n} v = map finToNat v

-- Because we may view a slice object in the category of finite prefixes of the
-- natural numbers as a morphism in that category, and we may view a
-- polynomial endofunctor on that category as a slice object over that
-- endofunctor's positions, we may view a polynomial endofunctor as a morphism.

public export
FSPolyDirMax : FSPolyF -> Nat
FSPolyDirMax p = vectMax (FSPolyFToSlice p)

public export
FSPolyToMorph : (p : FSPolyF) -> FSMorph (fsPolyNPos p) (S (FSPolyDirMax p))
FSPolyToMorph p = FSSliceToMorph (FSPolyFToSlice p)

public export
FSMorphToPoly : {m, n : FSObj} -> FSMorph m n -> FSPolyF
FSMorphToPoly v = SliceToFSPolyF (FSMorphToSlice v)

---------------------------------------------------------------------------
---- Natural transformations between polynomial endofunctors on FinSet ----
---------------------------------------------------------------------------

public export
FSPosMap : FSPolyF -> FSPolyF -> Type
FSPosMap p q = FSMorph (fsPolyNPos p) (fsPolyNPos q)

public export
FSPosDirMap : (p, q : FSPolyF) -> FSPosMap p q -> fsPolyPos p -> Type
FSPosDirMap p q onPos i =
  FSMorph (fsPolyNDir q $ FSApply onPos i) (fsPolyNDir p i)

public export
FSDirMap : (p, q : FSPolyF) -> FSPosMap p q -> Vect (fsPolyNPos p) Type
FSDirMap p q onPos = finFToVect $ FSPosDirMap p q onPos

public export
FSOnDirT : (p, q : FSPolyF) -> FSPosMap p q -> Type
FSOnDirT p q onPos = HVect $ FSDirMap p q onPos

public export
FSPNatTrans : FSPolyF -> FSPolyF -> Type
FSPNatTrans p q = (onPos : FSPosMap p q ** FSOnDirT p q onPos)

public export
fspOnPos : {0 p, q : FSPolyF} -> FSPNatTrans p q -> FSPosMap p q
fspOnPos = fst

public export
fspOnDir : {0 p, q : FSPolyF} -> (alpha : FSPNatTrans p q) ->
  FSOnDirT p q (fspOnPos {p} {q} alpha)
fspOnDir = snd

public export
fspOnPosF : {p, q : FSPolyF} -> FSPNatTrans p q -> fsPolyPos p -> fsPolyPos q
fspOnPosF (onPos ** onDir) = FSApply onPos

public export
fspOnDirF : {p, q : FSPolyF} -> (alpha : FSPNatTrans p q) ->
  (i : fsPolyPos p) -> fsPolyDir q (fspOnPosF {p} {q} alpha i) -> fsPolyDir p i
fspOnDirF (onPos ** onDir) i = FSApply $ finFGet i onDir

public export
FSPolyNatTrans : FSPolyFunc -> FSPolyFunc -> Type
FSPolyNatTrans p q =
  (onPos : fst p -> fst q ** SliceMorphism (snd q . onPos) (snd p))

public export
fspNT : {p, q : FSPolyF} ->
  FSPNatTrans p q -> FSPolyNatTrans (fspPF p) (fspPF q)
fspNT alpha = (fspOnPosF alpha ** fspOnDirF alpha)

-- A polymorphic function in FinSet, or equivalently, a family of functions,
-- one for each `FSObj`, with the domain and codomain given by the
-- application of `p` and `q` respectively.
--
-- The data required to generate this family of functions constitute precisely
-- an `FSPNatTrans`.
public export
FSPolyMorph : (p, q : FSPolyF) -> Type
FSPolyMorph p q = (n : FSObj) -> FSMorph (FSPolyApply p n) (FSPolyApply q n)

public export
FSProjM : (n : Nat) -> {m : Nat} -> FSElem m -> FSMorph (power n m) n
FSProjM n {m=(S m)} FZ = fsProdElimLeft n (power n m)
FSProjM n {m=(S m)} (FS i) =
  FSCompose (FSProjM n {m} i) (fsProdElimRight n (power n m))

public export
FSConstructorMap : {k, m, n : Nat} ->
  FSMorph k m -> FSMorph (power n m) (power n k)
FSConstructorMap {k=Z} {m} {n} [] =
  rewrite sym (multOneRightNeutral (power n m)) in
  vectRepeat {b=1} {c=1} (power n m) [FZ]
FSConstructorMap {k=(S k)} {m} {n} (i :: v) =
  fsProdIntro (FSProjM n i) (FSConstructorMap {k} {m} {n} v)

public export
FSPosApply : {m, n : Nat} -> (aq : List Nat) ->
  (hd : Fin (length aq)) -> FSMorph (index' aq hd) m ->
  FSMorph (power n m) (FSPolyApply aq n)
FSPosApply {m} {n} [] hd v = absurd hd
FSPosApply {m} {n} (k :: aq') FZ v =
  map (weakenN (FSCoproductList (FSExpMap n aq'))) (FSConstructorMap {n} v)
FSPosApply {m} {n} (k :: aq') (FS hd') v =
  map (shift (power n k)) (FSPosApply {m} {n} aq' hd' v)

public export
FSPNTApplyList : {ap, aq : List Nat} ->
  FSPNatTrans ap aq -> FSPolyMorph ap aq
FSPNTApplyList {ap=[]} {aq}
    ([] ** []) n =
  []
FSPNTApplyList {ap=(m :: ap')} {aq}
    (onPosHd :: onPosTl ** onDirHd :: onDirTl) n =
  fsCopElim
    (FSPosApply {m} {n} aq onPosHd onDirHd)
    (FSPNTApplyList {ap=ap'} {aq} (onPosTl ** onDirTl) n)

public export
FSPNTApply : {p, q : FSPolyF} -> FSPNatTrans p q -> FSPolyMorph p q
FSPNTApply {p=ap} {q=aq} = FSPNTApplyList {ap} {aq}

public export
InterpFSPNT : {p, q : FSPolyF} -> FSPNatTrans p q ->
  SliceMorphism {a=Type} (InterpFSPolyF p) (InterpFSPolyF q)
InterpFSPNT {p=ap} {q=aq} (onPos ** onDir) x (i ** v) =
  (FSApply onPos i ** finFToVect $ \j => index (FSApply (finFGet i onDir) j) v)

-- A slice morphism can be viewed as a special case of a natural transformation
-- between the polynomial endofunctors as which the codomain and domain slices
-- may be viewed.  (The special case is that the on-positions function is the
-- identity.)

public export
FSSliceMorphismToFSNT : {n : FSObj} -> {0 s, s' : FSSlice n} ->
  FSSliceMorphism s s' -> FSPNatTrans (SliceToFSPolyF s') (SliceToFSPolyF s)
FSSliceMorphismToFSNT {n} {s} {s'} m =
  (?FSSliceMorphismToFSNT_hole_onpos (FSId n) **
   ?FSSliceMorphismToFSNT_hole_ondir)

public export
FSNTToFSSliceMorph : {0 p, q : FSPolyF} ->
  {eqpos : fsPolyNPos p = fsPolyNPos q} ->
  (alpha : FSPNatTrans p q) ->
  (fspOnPos {p} {q} alpha =
   replace {p=(Vect (fsPolyNPos p) . Fin)} eqpos (FSId (fsPolyNPos p))) ->
  FSSliceMorphism
    {n=(fsPolyNPos p)}
    (replace {p=(flip Vect FSObj)} (sym eqpos) (FSPolyFToSlice q))
    (FSPolyFToSlice p)
FSNTToFSSliceMorph {p} {q} {eqpos} (onPos ** onDir) isId =
  ?FSNTToFSSliceMorph_hole

------------------------------------------------
---- Algebras of FinSet polynomial functors ----
------------------------------------------------

public export
FSPAlg : FSPolyF -> FSObj -> Type
FSPAlg p n = FSMorph (FSPolyApply p n) n

public export
FSPolyAlg : FSPolyFunc -> Type -> Type
FSPolyAlg p a = (i : fst p) -> (snd p i -> a) -> a

public export
FSListToPFAlg : {n : FSObj} -> {l : List Nat} ->
  FSPAlg l n -> FSPolyAlg (fspPF l) (FSElem n)
FSListToPFAlg {n} {l=[]} alg i f = absurd i
FSListToPFAlg {n} {l=(x :: l')} alg FZ f =
  FSApply (take (power n x) alg) $ finPowFin $ finFToVect f
FSListToPFAlg {n} {l=(x :: l')} alg (FS i) f =
  FSListToPFAlg {n} {l=l'} (drop (power n x) alg) i f

public export
FSPToPFAlg : {n : FSObj} -> {p : FSPolyF} ->
  FSPAlg p n -> FSPolyAlg (fspPF p) (FSElem n)
FSPToPFAlg {n} {p=l} alg i = FSListToPFAlg {n} {l} alg i

--------------------------------------------------------
---- Initial algebras of FinSet polynomial functors ----
--------------------------------------------------------

public export
data FSPolyFMu : FSPolyF -> Type where
  InFSP : {0 p : FSPolyF} ->
    (i : fsPolyPos p) -> Vect (fsPolyNDir p i) (FSPolyFMu p) -> FSPolyFMu p

-----------------------------------------------------
---- Catamorphisms of FinSet polynomial functors ----
-----------------------------------------------------

public export
fspCata : {p : FSPolyF} -> {0 a : FSObj} ->
  FSPAlg p a -> FSPolyFMu p -> FSElem a
fspCata {p=l} {a} alg (InFSP i v) =
  ?fspCata_hole
