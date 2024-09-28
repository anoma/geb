module Library.IdrisUtils

import public Data.Maybe
import public Data.Either
import public Data.Contravariant
import public Data.List
import public Data.List.Equalities
import public Data.List.Reverse
import public Data.List.Quantifiers
import public Data.Vect.Quantifiers
import public Data.Nat
import public Data.Nat.Order.Properties
import public Data.Nat.Division
import public Data.Vect
import public Data.Vect.Properties.Foldr
import public Data.Fin
import public Data.Fin.Order
import public Data.DPair
import public Data.Bool
import public Decidable.Decidable
import public Decidable.Equality
import public Control.Function
import public Control.Function.FunExt
import public Control.Relation
import public Control.Order
import public Control.Monad.Identity
import public Control.Monad.Trans
import public Control.Monad.Reader
import public Control.Monad.Either
import public Data.Binary
import public Data.Nat.Properties
import public Data.Nat.Exponentiation
import public Data.Binary.Digit
import public Data.String
import public Syntax.PreorderReasoning

%default total

%hide Prelude.(|>)

export infixr 1 |>
public export
(|>) : {0 a, b, c : Type} -> (a -> b) -> (b -> c) -> (a -> c)
(|>) = flip (.)

export infixr 1 .*
public export
(.*) : {0 a, b, c, d : Type} -> (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.*) = (.) . (.)

export infixr 1 .**
public export
(.**) : {0 a, b, c, d, e : Type} ->
  (d -> e) -> (a -> b -> c -> d) -> (a -> b -> c -> e)
(.**) = (.) . (.) . (.)

public export
flipApp : {0 a, b : Type} -> a -> (a -> b) -> b
flipApp = flip apply

public export
preCompFlipApp : {0 a, b, c : Type} -> (((a -> b) -> b) -> c) -> a -> c
preCompFlipApp {a} {b} {c} = (|>) {a} {b=((a -> b) -> b)} {c} (flipApp {a} {b})

public export
[IdFunctor] Functor Prelude.id where
  map = id

public export
[IdApplicative] Applicative Prelude.id using IdFunctor where
  pure = id
  (<*>) = apply

public export
[IdMonad] Monad Prelude.id using IdApplicative where
  (>>=) = flip apply

public export
[MaybeFunctor] Functor Maybe where
  map f (Just x) = Just (f x)
  map f Nothing  = Nothing

public export
[MaybeApplicative] Applicative Maybe using MaybeFunctor where
  pure = Just
  Just f <*> Just a = Just (f a)
  _      <*> _      = Nothing

public export
[MaybeMonad] Monad Maybe using MaybeApplicative where
  Nothing  >>= k = Nothing
  (Just x) >>= k = k x

public export
[EitherFunctor] Functor (Either a) where
  map f (Left x) = Left x
  map f (Right x) = Right (f x)

public export
[EitherApplicative] Semigroup x =>
    Applicative (Either x) using EitherFunctor where
  pure = Right
  Left f  <*> Left i = Left (f <+> i)
  Left f  <*> Right i = Left f
  Right f <*> Left i = Left i
  Right f <*> Right i = Right (f i)

public export
[EitherMonad] Semigroup x => Monad (Either x) using MaybeApplicative where
  (Left x)  >>= k = Left x
  (Right x) >>= k = k x

public export
fcong : {0 a, b : Type} -> {0 f, g : a -> b} ->
  (f ~=~ g) -> {x : a} -> f x = g x
fcong Refl = Refl

public export
fcongdep : {0 a : Type} -> {0 b : a -> Type} -> {0 f, g : (ea : a) -> b ea} ->
  (f ~=~ g) -> {x : a} -> f x = g x
fcongdep Refl = Refl

public export
fcompeq : {0 a, b, c : Type} -> {0 g, g' : b -> c} -> {0 f, f' : a -> b} ->
  (g ~=~ g') -> (f ~=~ f') -> g . f = g' . f'
fcompeq Refl Refl = Refl

public export
fprecompeq : {0 a, b, c : Type} -> {0 f, g : b -> c} -> {0 h : a -> b} ->
  (f ~=~ g) -> f . h = g . h
fprecompeq eq = fcompeq eq Refl

public export
fpostcompeq : {0 a, b, c : Type} -> {0 f, g : a -> b} -> {0 h : b -> c} ->
  (f ~=~ g) -> h . f = h . g
fpostcompeq eq = fcompeq {g=h} Refl eq

public export
dpBimap : {0 a, b : Type} -> {0 p : a -> Type} -> {0 q : b -> Type} ->
  (f : a -> b) -> ((ea : a) -> p ea -> q (f ea)) -> DPair a p -> DPair b q
dpBimap {a} {b} {p} {q} f m eap = (f (fst eap) ** m (fst eap) (snd eap))

public export
dpMapSnd : {0 a : Type} -> {0 p : a -> Type} -> {0 q : a -> Type} ->
  ((ea : a) -> p ea -> q ea) -> DPair a p -> DPair a q
dpMapSnd {a} {p} {q} = dpBimap {a} {b=a} {p} {q} (id {a})

public export
dpEq12 : {0 a : Type} -> {0 p : a -> Type} -> {x, y : a} ->
  {0 px : p x} -> {0 py : p y} ->
  x = y -> px = py -> MkDPair {p} x px = MkDPair {p} y py
dpEq12 {a} {p} {x} {y=x} {px} {py=px} Refl Refl = Refl

public export
dpEqPat : {0 a : Type} -> {0 p : a -> Type} ->
  {0 dp : DPair a p} -> dp = (fst dp ** snd dp)
dpEqPat {a} {p} {dp=(_ ** _)} = Refl

export
mkDPairInjectiveFstHet :
  {0 a, b : Type} -> {0 p : a -> Type} -> {0 q : b -> Type} ->
  {x : a} -> {y : b} -> {f : p x} -> {g : q y} ->
  MkDPair {a} {p} x f = MkDPair {a=b} {p=q} y g -> x = y
mkDPairInjectiveFstHet Refl = Refl

export
mkDPairInjectiveSndHet :
  {0 a, b : Type} -> {0 p : a -> Type} -> {0 q : b -> Type} ->
  {x : a} -> {y : b} -> {f : p x} -> {g : q y} ->
  (dpeq : MkDPair {a} {p} x f = MkDPair {a=b} {p=q} y g) ->
  f ~=~ g
mkDPairInjectiveSndHet Refl = Refl

export
dpeq1 : {0 a : Type} -> {0 b : a -> Type} -> {0 dp, dp' : DPair a b} ->
  dp = dp' -> fst dp = fst dp'
dpeq1 Refl = Refl

export
dpeq2 : {0 a : Type} -> {0 b : a -> Type} -> {0 dp, dp' : DPair a b} ->
  dp = dp' -> snd dp ~=~ snd dp'
dpeq2 Refl = Refl

-- A predicate on a dependent pair which only holds when the first
-- element of the pair matches a given one.
public export
MatchingSnd : {0 a : Type} -> {0 b : a -> Type} ->
  (ea : a) -> (b ea -> Type) -> (DPair a b -> Type)
MatchingSnd {a} {b} ea sl dp =
  Exists {type=(fst dp = ea)} $ \eqa => sl $ replace {p=b} eqa $ snd dp

public export
showDP : {0 a : Type} -> {0 p : a -> Type} ->
  (a -> String) -> ((x : a) -> p x -> String) ->
  DPair a p -> String
showDP {a} {p} showA showP (x ** l) =
  -- Copied from the Idris standard libraries because I can't figure out
  -- how to get Idris to infer (Show DPair).
  "(" ++ showA x ++ " ** " ++ showP x l ++ ")"

public export
maybeElim : {0 a, b : Type} -> (a -> b) -> b -> Maybe a -> b
maybeElim f g (Just e) = f e
maybeElim f g Nothing = g

public export
eitherElim : {0 a, b, c : Type} -> (a -> c) -> (b -> c) -> Either a b -> c
eitherElim f g (Left e) = f e
eitherElim f g (Right e) = g e

public export
eitherSym : {0 a, b : Type} -> Either a b -> Either b a
eitherSym {a} {b} (Left x) = Right x
eitherSym {a} {b} (Right x) = Left x

public export
codiag : {0 a : Type} -> Either a a -> a
codiag {a} = eitherElim {a} {b=a} {c=a} id id

-- Like Idris's standard `Subset`, but with even the `pred` type
-- parameter erased.
public export
record Subset0 (type : Type) (0 dep : type -> Type) where
  constructor Element0
  fst0 : type
  0 snd0 : dep fst0

public export
curry : {0 p : a -> Type} -> (Subset0 a p -> c) -> (x : a) -> (0 _ : p x) -> c
curry f x y = f $ Element0 x y

public export
uncurry : {0 p : a -> Type} -> ((x : a) -> (0 _ : p x) -> c) -> Subset0 a p -> c
uncurry f s = f s.fst0 s.snd0

export
elementInjectiveFst : Element0 x p = Element0 y q -> x = y
elementInjectiveFst Refl = Refl

export
elementInjectiveSnd : Element0 x p = Element0 x q -> p = q
elementInjectiveSnd Refl = Refl

public export
bimap : (f : a -> b) -> (0 _ : forall x. p x -> q (f x)) ->
  Subset0 a p -> Subset0 b q
bimap f g e = Element0 (f $ fst0 e) (g $ snd0 e)

public export
s0Bimap : {0 a, b : Type} -> {0 p : a -> Type} -> {0 q : b -> Type} ->
  (f : a -> b) -> (0 _ : (ea : a) -> p ea -> q (f ea)) ->
  Subset0 a p -> Subset0 b q
s0Bimap {a} {b} {p} {q} f m eap =
  Element0 (f (fst0 eap)) (m (fst0 eap) (snd0 eap))

public export
s0MapSnd : {0 a : Type} -> {0 p : a -> Type} -> {0 q : a -> Type} ->
  (0 _ : (ea : a) -> p ea -> q ea) -> Subset0 a p -> Subset0 a q
s0MapSnd {a} {p} {q} = s0Bimap {a} {b=a} {p} {q} (id {a})

public export
Eq type => Eq (Subset0 type dep) where
  (==) = (==) `on` fst0

public export
Ord type => Ord (Subset0 type dep) where
  compare = compare `on` fst0

public export
Show type => Show (Subset0 type dep) where
  show = show . fst0

public export
s0Eq1 : {0 a : Type} -> {0 p : a -> Type} -> {s0, s0' : Subset0 a p} ->
  (0 _ : s0 = s0') -> fst0 s0 = fst0 s0'
s0Eq1 {a} {p} Refl = Refl

public export
s0Eq2 : {0 a : Type} -> {0 p : a -> Type} -> {s0, s0' : Subset0 a p} ->
  (0 _ : s0 = s0') -> snd0 s0 ~=~ snd0 s0'
s0Eq2 {a} {p} Refl = Refl

public export
s0Eq12 : {0 a : Type} -> {0 p : a -> Type} -> {x, y : a} ->
  {0 px : p x} -> {0 py : p y} ->
  x = y -> px ~=~ py ->
  Element0 {type=a} {dep=p} x px = Element0 {type=a} {dep=p} y py
s0Eq12 {a} {p} {x} {y=x} {px} {py=px} Refl Refl = Refl

-- Like Idris's standard `Exists`, but with the `this` dependent type
-- taking a zero-usage type parameter.
public export
record Exists0 (0 type : Type) (0 this : (0 _ : type) -> Type) where
  constructor Evidence0
  0 fst0 : type
  0 snd0 : this fst0

public export
e0Bimap : {0 a, b : Type} ->
  {0 p : (0 _ : a) -> Type} -> {0 q : (0 _ : b) -> Type} ->
  (0 f : a -> b) -> (0 _ : (0 ea : a) -> p ea -> q (f ea)) ->
  Exists0 a p -> Exists0 b q
e0Bimap {a} {b} {p} {q} f m eap =
  Evidence0 (f (fst0 eap)) (m (fst0 eap) (snd0 eap))

public export
e0MapSnd : {0 a : Type} ->
  {0 p : (0 _ : a) -> Type} -> {0 q : (0 _ : a) -> Type} ->
  (0 _ : (0 ea : a) -> p ea -> q ea) -> Exists0 a p -> Exists0 a q
e0MapSnd {a} {p} {q} = e0Bimap {a} {b=a} {p} {q} (id {a})

public export
exists0inj1 :
  {0 type, type' : Type} ->
  {0 this : (0 _ : type) -> Type} ->
  {0 this' : (0 _ : type') -> Type} ->
  {e0 : Exists0 type this} ->
  {e0' : Exists0 type' this'} ->
  e0 = e0' ->
  fst0 e0 = fst0 e0'
exists0inj1 {e0} {e0'=e0} Refl = Refl

public export
exists0inj2 :
  {0 type, type' : Type} ->
  {0 this : (0 _ : type) -> Type} ->
  {0 this' : (0 _ : type') -> Type} ->
  {e0 : Exists0 type this} ->
  {e0' : Exists0 type' this'} ->
  e0 = e0' ->
  snd0 e0 ~=~ snd0 e0'
exists0inj2 {e0} {e0'=e0} Refl = Refl

public export
const0 : {0 a, b : Type} -> b -> (0 _ : a) -> b
const0 x _ = x

-- Non-dependent `Exists0`.
public export
CExists0 : (0 a: Type) -> Type -> Type
CExists0 a b = Exists0 a (const0 b)

public export
DecNonZero : (n : Nat) -> Dec (NonZero n)
DecNonZero Z = No $ \nzz => case nzz of SIsNonZero impossible
DecNonZero (S n) = Yes SIsNonZero

public export
divMaybe : Nat -> Nat -> Maybe Nat
divMaybe n m with (DecNonZero m)
  divMaybe n m | Yes nz = Just $ divNatNZ n m nz
  divMaybe n m | No _ = Nothing

public export
modMaybe : Nat -> Nat -> Maybe Nat
modMaybe n m with (DecNonZero m)
  modMaybe n m | Yes nz = Just $ modNatNZ n m nz
  modMaybe n m | No _ = Nothing

public export
divWithZtoZ : Integer -> Integer -> Integer
divWithZtoZ n m = if m == 0 then 0 else div n m

public export
modWithZtoZ : Integer -> Integer -> Integer
modWithZtoZ n m = if m == 0 then 0 else mod n m

public export
divSucc : Integer -> Integer -> Integer
divSucc n m = div n (m + 1)

public export
modSucc : Integer -> Integer -> Integer
modSucc n m = mod n (m + 1)

public export
boolToDigit : Bool -> Digit
boolToDigit True = I
boolToDigit False = O

public export
exfalsoFT : {0 a : Type} -> (0 ft : False = True) -> a
exfalsoFT Refl impossible

public export
exfalsoTF : {0 a : Type} -> (0 tf : True = False) -> a
exfalsoTF Refl impossible

public export
uip : {0 a, a' : Type} -> {0 x : a} -> {0 x' : a'} ->
  {eq, eq' : x = x'} -> eq = eq'
uip {eq=Refl} {eq'=Refl} = Refl

public export
uipHet : {0 a, a' : Type} -> {0 x, y : a} -> {0 x', y' : a'} ->
  {eq : x = y} -> {eq' : x' = y'} -> {eq'' : x = x'} -> eq ~=~ eq'
uipHet {a} {a'=a} {x} {y=x} {x'=x} {y'=x} {eq=Refl} {eq'=Refl} {eq''=Refl} =
  Refl

public export
lteTolt : {m, n : Nat} -> LTE m n -> Not (m = n) -> LT m n
lteTolt {m=0} {n=Z} LTEZero neq = void $ neq Refl
lteTolt {m=0} {n=(S n)} LTEZero neq = LTESucc LTEZero
lteTolt {m=(S m)} {n=(S n)} (LTESucc x) neq =
  LTESucc $ lteTolt {m} {n} x (\eq => case eq of Refl => neq Refl)

public export
lteAddLeft : (m, n : Nat) -> LTE n (m + n)
lteAddLeft m n = rewrite plusCommutative m n in lteAddRight {m} n

public export
compareNatSucc : (n : Nat) -> compareNat n (S n) = LT
compareNatSucc Z = Refl
compareNatSucc (S n) = compareNatSucc n

public export
lteZeroIsZero : {n : Nat} -> LTE n 0 -> 0 = n
lteZeroIsZero {n=Z} _ = Refl
lteZeroIsZero {n=(S _)} lt = void $ succNotLTEzero lt

public export
lteSuccEitherEqLte : {m, n : Nat} -> LTE m (S n) -> Either (m = S n) (LTE m n)
lteSuccEitherEqLte {m} {n} lte with (decEq m (S n))
  lteSuccEitherEqLte {m} {n} lte | Yes eq =
    Left eq
  lteSuccEitherEqLte {m} {n} lte | No neq =
    Right $ fromLteSucc $ lteTolt lte neq

public export
maxLTE : {m, n, k : Nat} -> LTE m k -> LTE n k -> LTE (maximum m n) k
maxLTE {m=Z} {n} {k} ltmk ltnk = ltnk
maxLTE {m=(S m)} {n=Z} {k} ltmk ltnk = ltmk
maxLTE {m=(S m)} {n=(S n)} {k=Z} ltmk ltnk = void $ succNotLTEzero ltmk
maxLTE {m=(S m)} {n=(S n)} {k=(S k)} ltmk ltnk =
  LTESucc $ maxLTE {m} {n} {k} (fromLteSucc ltmk) (fromLteSucc ltnk)

public export
maxLTELeft : (m, n : Nat) -> LTE m (maximum m n)
maxLTELeft = maximumLeftUpperBound

public export
maxLTERight : (m, n : Nat) -> LTE n (maximum m n)
maxLTERight = maximumRightUpperBound

public export
smax : Nat -> Nat -> Nat
smax = S .* maximum

public export
smaxLTLeft : (m, n : Nat) -> LT m (smax m n)
smaxLTLeft m n = LTESucc $ maxLTELeft m n

public export
smaxLTRight : (m, n : Nat) -> LT n (smax m n)
smaxLTRight m n = LTESucc $ maxLTERight m n

public export
smaxLTMax : (m, n : Nat) -> LT (maximum m n) (smax m n)
smaxLTMax m n = LTESucc reflexive

public export
voidF : (0 a : Type) -> Void -> a
voidF _ x = void x

public export
IsTrue : Bool -> Type
IsTrue b = b = True

public export
IsFalse : Bool -> Type
IsFalse b = b = False

public export
IsJustTrue : {a : Type} -> Maybe a -> Type
IsJustTrue x = isJust x = True

public export
IsNothingTrue : {a : Type} -> Maybe a -> Type
IsNothingTrue x = isJust x = False

public export
0 ReturnsJust : {0 a, b : Type} -> (f : a -> Maybe b) -> (x : a) -> Type
ReturnsJust {a} {b} f x = IsJust (f x)

public export
MkMaybe : {0 a, b : Type} ->
  (f : a -> Maybe b) -> (x : a) -> {auto 0 j : ReturnsJust f x} -> b
MkMaybe {a} {b} f x {j} with (f x)
  MkMaybe {a} {b} f x {j=ItIsJust} | (Just x') = x'

public export
fromIsTrueNat : (m, n : Nat) -> m == n = True -> m = n
fromIsTrueNat 0 0 Refl = Refl
fromIsTrueNat 0 (S n) Refl impossible
fromIsTrueNat (S m) 0 Refl impossible
fromIsTrueNat (S m) (S n) eq = cong S $ fromIsTrueNat m n eq

public export
fromIsTrueMaybeNat : (m, n : Maybe Nat) -> m == n = True -> m = n
fromIsTrueMaybeNat Nothing Nothing Refl = Refl
fromIsTrueMaybeNat Nothing (Just n) Refl impossible
fromIsTrueMaybeNat (Just m) Nothing Refl impossible
fromIsTrueMaybeNat (Just m) (Just n) eq = cong Just $ fromIsTrueNat m n eq

public export
andLeft : {p, q : Bool} -> IsTrue (p && q) -> IsTrue p
andLeft {p=True} {q=True} Refl = Refl
andLeft {p=True} {q=False} Refl impossible
andLeft {p=False} {q=True} Refl impossible
andLeft {p=False} {q=False} Refl impossible

public export
andRight : {p, q : Bool} -> IsTrue (p && q) -> IsTrue q
andRight {p=True} {q=True} Refl = Refl
andRight {p=True} {q=False} Refl impossible
andRight {p=False} {q=True} Refl impossible
andRight {p=False} {q=False} Refl impossible

public export
andBoth : {p, q : Bool} -> IsTrue p -> IsTrue q -> IsTrue (p && q)
andBoth {p=True} {q=True} Refl Refl = Refl
andBoth {p=True} {q=False} Refl Refl impossible
andBoth {p=False} {q=True} Refl Refl impossible
andBoth {p=False} {q=False} Refl Refl impossible

public export
foldTrueInit : (b : Bool) -> (bs : List Bool) ->
  foldl (\x, y => x && Delay y) b bs = True -> b = True
foldTrueInit b [] eq = eq
foldTrueInit b (b' :: bs) eq = andLeft $ foldTrueInit (b && b') bs eq

public export
foldTrueList : (b : Bool) -> (bs : List Bool) ->
  foldl (\x, y => x && Delay y) b bs = True -> all Prelude.id bs = True
foldTrueList b [] eq = Refl
foldTrueList b (b' :: bs) eq with (andRight (foldTrueInit (b && b') bs eq))
  foldTrueList b (True :: bs) eq | Refl =
    let al = andLeft (foldTrueInit (b && True) bs eq) in
    replace {p=(\b'' => foldl (\x, y => x && Delay y) b'' (True :: bs) = True)}
      (andLeft (foldTrueInit (b && True) bs eq)) eq

public export
foldTrueBoth : (b : Bool) -> (bs : List Bool) ->
  b = True -> all Prelude.id bs = True ->
  foldl (\x, y => x && Delay y) b bs = True
foldTrueBoth b [] beq bseq = beq
foldTrueBoth b (b' :: bs) beq bseq =
  let fti = foldTrueInit b' bs bseq in
  foldTrueBoth (b && b') bs
    (rewrite beq in fti)
    (replace {p=(\b'' => all id (b'' :: bs) = True)} fti bseq)

public export
repeatIdx : {0 x : Type} -> (Nat -> x -> x) -> Nat -> Nat -> x -> x
repeatIdx f Z i e = e
repeatIdx f (S n) i e = repeatIdx f n (S i) (f i e)

public export
repeat : {0 x : Type} -> (x -> x) -> Nat -> x -> x
repeat f Z e = e
repeat f (S n) e = repeat f n (f e)

public export
fromIsJust : {a : Type} -> {x : Maybe a} -> (0 _ : IsJustTrue x) -> a
fromIsJust {x=(Just x)} Refl = x
fromIsJust {x=Nothing} Refl impossible

public export
IsLeftTrue : {0 a, b : Type} -> Either a b -> Type
IsLeftTrue x = isLeft x = True

public export
fromIsLeft : {0 a, b : Type} -> {x : Either a b} -> (0 _ : IsLeftTrue x) -> a
fromIsLeft {x=(Left x)} Refl = x
fromIsLeft {x=(Right _)} Refl impossible

public export
IsRightTrue : {0 a, b : Type} -> Either a b -> Type
IsRightTrue x = isRight x = True

public export
fromIsRight : {0 a, b : Type} -> {x : Either a b} -> (0 _ : IsRightTrue x) -> b
fromIsRight {x=(Left _)} Refl impossible
fromIsRight {x=(Right x)} Refl = x

public export
IsYesTrue : {a : Type} -> Dec a -> Type
IsYesTrue x = isYes x = True

public export
fromIsYes : {a : Type} -> {x : Dec a} -> IsYesTrue x -> a
fromIsYes {x=(Yes x)} Refl = x
fromIsYes {x=(No n)} Refl impossible

public export
toIsYes : {a : Type} -> (x : a) -> {dx : Dec a} -> IsYesTrue dx
toIsYes x {dx=(Yes y)} = Refl
toIsYes x {dx=(No n)} = void $ n x

public export
fstEq : {a, b : Type} -> {x, y : (a, b)} -> x = y -> fst x = fst y
fstEq Refl = Refl

public export
sndEq : {a, b : Type} -> {x, y : (a, b)} -> x = y -> snd x = snd y
sndEq Refl = Refl

public export
fstEqHetTy : {a, a', b, b' : Type} -> {x : (a, b)} -> {y : (a', b')} ->
  x = y -> a = a'
fstEqHetTy Refl = Refl

public export
sndEqHetTy : {a, a', b, b' : Type} -> {x : (a, b)} -> {y : (a', b')} ->
  x = y -> b = b'
sndEqHetTy Refl = Refl

public export
fstEqHet : {a, a', b, b' : Type} -> {x : (a, b)} -> {y : (a', b')} ->
  (eq : x = y) -> fst x = (rewrite fstEqHetTy eq in fst y)
fstEqHet Refl = Refl

public export
sndEqHet : {a, a', b, b' : Type} -> {x : (a, b)} -> {y : (a', b')} ->
  (eq : x = y) -> snd x = (rewrite sndEqHetTy eq in snd y)
sndEqHet Refl = Refl

public export
fromLteSuccYes : {m, n : Nat} ->
  IsYesTrue (isLT (S m) (S n)) -> IsYesTrue (isLT m n)
fromLteSuccYes y = toIsYes (fromLteSucc $ fromIsYes y)

public export
lindexN : {0 a : Type} -> (i : Nat) -> (l : List a) ->
  {auto 0 ok : IsTrue (i < length l)} -> a
lindexN {a} Z [] {ok=Refl} impossible
lindexN {a} (S i) [] {ok=Refl} impossible
lindexN {a} Z (x :: xs) {ok=Refl} = x
lindexN {a} (S i) (x :: xs) {ok} = lindexN {a} i xs {ok}

public export
finToNatLT : {m : Nat} -> (i : Fin m) -> LT (finToNat i) m
finToNatLT {m=Z} i = absurd i
finToNatLT {m=(S m)} FZ = LTESucc LTEZero
finToNatLT {m=(S m)} (FS i) = LTESucc $ finToNatLT {m} i

public export
finToFin : {n : Nat} -> {i : Fin n} -> Fin (finToNat i) -> Fin n
finToFin {n} {i} j = weakenLTE j $ lteSuccLeft $ finToNatLT {m=n} i

-- Nothing but an alias with a shorter name, in anticipation of using this
-- one a lot.
public export
nf : {0 n : Nat} -> (x : Nat) -> {auto 0 ok : LT x n} -> Fin n
nf {n} x {ok} = natToFinLT {n} x

public export
fromListMaybe : {0 a : Type} -> {n : Nat} -> List a -> Maybe (Vect n a)
fromListMaybe {a} {n} l with (decEq n $ length l)
  fromListMaybe {a} {n=(length l)} l | Yes Refl = Just $ Data.Vect.fromList l
  fromListMaybe {a} {n} l | No _ = Nothing

public export
indexN : {0 a : Type} -> {n : Nat} ->
  (i : Nat) -> {auto ok : IsJustTrue (natToFin i n)} -> Vect n a -> a
indexN _ {ok} = index (fromIsJust ok)

public export
indexNL : {0 a : Type} -> {n : Nat} ->
  (i : Nat) -> {auto ok : IsYesTrue (isLT i n)} -> Vect n a -> a
indexNL i {ok} v = index (natToFinLT i {prf=(fromIsYes ok)}) v

public export
natToFinLTS : {m, n : Nat} -> {lt : LT m n} -> {ltS : LT (S m) n'} ->
  natToFinLT {n=(S n)} (S m) = FS (natToFinLT {n} m)
natToFinLTS = Refl

public export
indexToFinS : {a : Type} -> {m, n : Nat} ->
  {ltS : LT (S m) (S n)} -> {lt : LT m n} ->
  {x : a} -> {v : Vect n a} ->
  index (natToFinLT (S m)) (x :: v) = index (natToFinLT m) v
indexToFinS {a} {m} {n=Z} {ltS} {lt} {x} {v} = void $ succNotLTEzero lt
indexToFinS {a} {m=Z} {n=(S n)} {ltS} {lt=LTEZero} {x} {v} impossible
indexToFinS {a} {m=Z} {n=(S n)} {ltS=LTEZero} {lt} {x} {v} impossible
indexToFinS {a} {m=Z} {n=(S n)} {ltS=(LTESucc ltS)} {lt=(LTESucc lt)} {x} {v} =
  case ltS of
    LTEZero impossible
    LTESucc ltS' => Refl
indexToFinS {a} {m=(S m)} {n=(S n)} {ltS=LTEZero} {lt} {x} {v} impossible
indexToFinS {a} {m=(S m)} {n=(S n)} {ltS} {lt=LTEZero} {x} {v} impossible
indexToFinS {a} {m=(S m)} {n=(S n)}
  {ltS=(LTESucc ltS)} {lt=(LTESucc lt)} {x} {v} =
    case v of
      [] impossible
      (x' :: v') => indexToFinS {m} {n} {ltS} {lt} {x=x'} {v=v'}

public export
indexToFinLTS : {a : Type} -> {n : Nat} ->
  {i : Nat} ->
  {auto okS : IsYesTrue (isLT (S i) (S n))} ->
  {auto ok : IsYesTrue (isLT i n)} ->
  {x : a} -> {v : Vect n a} ->
  indexNL (S i) {ok=okS} (x :: v) = indexNL i {ok} v
indexToFinLTS {n} {i} {okS} {ok} {x} {v} =
  indexToFinS {a} {m=i} {n=n} {ltS=(fromIsYes okS)} {lt=(fromIsYes ok)} {x} {v}

public export
finFTail : {0 a : Type} -> {n : Nat} -> (Fin (S n) -> a) -> (Fin n -> a)
finFTail {a} {n} f = f . FS

public export
finFToVectOnto : {0 a : Type} -> {m, n : Nat} ->
  (Fin m -> a) -> Vect n a -> Vect (m + n) a
finFToVectOnto {a} {m=Z} {n} f v = v
finFToVectOnto {a} {m=(S m)} {n} f v =
  rewrite plusSuccRightSucc m n in
  finFToVectOnto {a} {m} {n=(S n)} (finFTail f) (f FZ :: v)

public export
finFToVectTR : {0 a : Type} -> {m : Nat} -> (Fin m -> a) -> Vect m a
finFToVectTR {a} {m} f =
  rewrite sym (plusZeroRightNeutral m) in
  reverse $ finFToVectOnto {a} {m} {n=Z} f []

public export
finFToVect : {0 a : Type} -> {n : Nat} -> (Fin n -> a) -> Vect n a
finFToVect {a} {n=Z} f = []
finFToVect {a} {n=(S n)} f = f FZ :: finFToVect {n} (f . FS)

public export
finFToVectIdx : {0 a : Type} -> {n : Nat} -> (f : Fin n -> a) -> (i : Fin n) ->
  index i (finFToVect f) = f i
finFToVectIdx {a} {n=(S _)} f FZ = Refl
finFToVectIdx {a} {n=(S n)} f (FS i) = finFToVectIdx {a} {n} (f . FS) i

public export
finHFToHVect : {n : Nat} -> {t : Fin n -> Type} -> ((i : Fin n) -> t i) ->
  HVect (finFToVect t)
finHFToHVect {n=Z} {t} f = []
finHFToHVect {n=(S n)} {t} f = f FZ :: finHFToHVect {n} (\i => f (FS i))

public export
finFGet : {0 n : Nat} ->
  (i : Fin n) -> {f : Fin n -> Type} -> HVect (finFToVect f) -> f i
finFGet {n=Z} i {f} [] = absurd i
finFGet {n=(S n)} FZ {f} (ty :: hv) = ty
finFGet {n=(S n)} (FS i) {f} (ty :: hv) = finFGet {n} i {f=(f . FS)} hv

public export
showHVv : {0 n : Nat} -> {0 a : Type} ->
  (sl : a -> Type) -> (sh : (x : a) -> sl x -> String) ->
  (v : Vect n a) -> (hv : HVect (map sl v)) -> Vect n String
showHVv {n=Z} {a} sl sh [] Nil = []
showHVv {n=(S n)} {a} sl sh (k :: ks) (x :: xs) = sh k x :: showHVv sl sh ks xs

public export
showHV : {0 n : Nat} -> {0 a : Type} ->
  (sl : a -> Type) -> (sh : (x : a) -> sl x -> String) ->
  (v : Vect n a) -> (hv : HVect (map sl v)) -> String
showHV {n} {a} sl sh v hv = show $ showHVv {n} {a} sl sh v hv

public export
hvDecEq : {0 n : Nat} -> {0 a : Type} ->
  (sl : a -> Type) -> (deq : (x : a) -> (y, y' : sl x) -> Dec (y = y')) ->
  (v : Vect n a) -> (hv, hv' : HVect (map sl v)) -> Dec (hv = hv')
hvDecEq {n=Z} {a} sl deq [] [] [] = Yes Refl
hvDecEq {n=(S n)} {a} sl deq (x :: xs) (y :: hv) (y' :: hv') =
  case deq x y y' of
    Yes Refl => case hvDecEq {n} sl deq xs hv hv' of
      Yes Refl => Yes Refl
      No neq => No (\Refl => neq Refl)
    No neq => No (\Refl => neq Refl)

public export
hvMap : {n : Nat} -> (ts, ts' : Vect n Type) ->
  (f : (i : Fin n) -> index i ts -> index i ts') ->
   HVect ts -> HVect ts'
hvMap {n=Z} [] [] f [] = []
hvMap {n=(S n)} (t :: ts) (t' :: ts') f (x :: hv) =
  f FZ x :: hvMap {n} ts ts' (\i, u => f (FS i) u) hv

public export
HMatrix : {0 k : Nat} -> Vect k Nat -> Vect k Type -> Type
HMatrix {k} ns tys = HVect {n=k} $ map (uncurry Vect) $ zip ns tys

public export
hmindex : {0 k : Nat} -> {ns : Vect k Nat} -> {tys : Vect k Type} ->
  (i : Fin k) -> Fin (index i ns) -> HMatrix {k} ns tys -> index i tys
hmindex {k=(S k)} {ns=(S n :: ns)} {tys=(ty :: tys)} FZ j (v :: hm) = index j v
hmindex {k=(S k)} {ns=(n :: ns)} {tys=(ty :: tys)} (FS i) j (v :: hm) =
  hmindex {k} {ns} {tys} i j hm

public export
mapIndex : {0 n : Nat} -> {0 a, b : Type} -> {0 f : a -> b} ->
  (v : Vect n a) -> (i : Fin n) -> index i (map f v) = f (index i v)
mapIndex {n=(S n)} {a} {b} {f} (x :: v) FZ = Refl
mapIndex {n=(S n)} {a} {b} {f} (x :: v) (FS i) = mapIndex v i

public export
vectRepeat : (a : Nat) -> {b, c : Nat} ->
  Vect b (Fin c) -> Vect (mult a b) (Fin c)
vectRepeat Z {b} {c} v = []
vectRepeat (S a) {b} {c} v = v ++ vectRepeat a {b} {c} v

public export
vectMaxAcc : {0 n : Nat} -> Nat -> Vect n Nat -> Nat
vectMaxAcc m [] = m
vectMaxAcc m (x :: xs) = vectMaxAcc (maximum m x) xs

public export
vectMax : {0 n : Nat} -> Vect n Nat -> Nat
vectMax = vectMaxAcc 0

public export
0 maximumMonotoneRight : (x, m, m' : Nat) -> LTE m m' ->
  LTE (maximum x m) (maximum x m')
maximumMonotoneRight Z m m' lte = lte
maximumMonotoneRight (S x) Z m' lte = maximumLeftUpperBound (S x) m'
maximumMonotoneRight (S x) (S m) Z lte = void $ succNotLTEzero lte
maximumMonotoneRight (S x) (S m) (S m') (LTESucc lte) =
  LTESucc $ maximumMonotoneRight x m m' lte

public export
0 maximumMonotoneLeft : (m, m', x : Nat) -> LTE m m' ->
  LTE (maximum m x) (maximum m' x)
maximumMonotoneLeft m m' x lte =
  rewrite maximumCommutative m x in
  rewrite maximumCommutative m' x in
  maximumMonotoneRight x m m' lte

public export
0 vectMaxGetAccMonotoneMax : {n : Nat} -> (m : Nat) -> (v : Vect n Nat) ->
  LTE m (vectMaxAcc {n} m v)
vectMaxGetAccMonotoneMax {n=Z} m [] = reflexive
vectMaxGetAccMonotoneMax {n=(S n)} m (x :: xs) =
  transitive
    (maximumLeftUpperBound m x)
    (vectMaxGetAccMonotoneMax {n} (maximum m x) xs)

public export
0 vectMaxGetAccMonotoneVect : {n : Nat} -> (m, m' : Nat) -> (v : Vect n Nat) ->
  LTE m m' -> LTE (vectMaxAcc {n} m v) (vectMaxAcc {n} m' v)
vectMaxGetAccMonotoneVect {n=Z} m m' [] lte = lte
vectMaxGetAccMonotoneVect {n=(S n)} m m' (x :: xs) lte =
  vectMaxGetAccMonotoneVect
    {n} (maximum m x) (maximum m' x) xs (maximumMonotoneLeft m m' x lte)

public export
0 vectMaxGetAccBoundHead : {n : Nat} -> (m : Nat) ->
  (x : Nat) -> (v : Vect n Nat) ->
  LTE x (vectMaxAcc {n=(S n)} m (x :: v))
vectMaxGetAccBoundHead {n} m x v =
  transitive
    (maximumRightUpperBound m x)
    (vectMaxGetAccMonotoneMax {n} (maximum m x) v)

public export
0 vectMaxGetAccBoundTail : {n : Nat} -> (m : Nat) ->
  (x : Nat) -> (v : Vect n Nat) ->
  LTE (vectMaxAcc {n} m v) (vectMaxAcc {n=(S n)} m (x :: v))
vectMaxGetAccBoundTail {n} m x v =
  vectMaxGetAccMonotoneVect {n} m (maximum m x) v (maximumLeftUpperBound m x)

public export
0 vectMaxGetAccCorrect : {n : Nat} -> (m : Nat) -> (v : Vect n Nat) ->
  (i : Fin n) -> LTE (index i v) (vectMaxAcc m v)
vectMaxGetAccCorrect {n=Z} m [] i = absurd i
vectMaxGetAccCorrect {n=(S n)} m (x :: xs) FZ =
  vectMaxGetAccBoundHead {n} m x xs
vectMaxGetAccCorrect {n=(S n)} m (x :: xs) (FS i) =
  transitive
    (vectMaxGetAccCorrect {n} m xs i)
    (vectMaxGetAccBoundTail {n} m x xs)

public export
vectMaxGetAcc : {0 n : Nat} ->
  (0 m : Nat) -> (v : Vect n Nat) -> Fin n -> Fin (S (vectMaxAcc m v))
vectMaxGetAcc {n} m v i =
  natToFinLT
    {n=(S (vectMaxAcc m v))}
    {prf=(LTESucc $ vectMaxGetAccCorrect {n} m v i)}
    (index i v)

public export
vectMaxGet : {0 n : Nat} -> (v : Vect n Nat) -> Fin n -> Fin (S (vectMax v))
vectMaxGet {n} v i = vectMaxGetAcc {n} 0 v i

public export
powerOneIsOne : (n : Nat) -> power 1 n = 1
powerOneIsOne Z = Refl
powerOneIsOne (S n) = rewrite powerOneIsOne n in Refl

public export
finPlus : {m, n : Nat} -> Fin m -> Fin n -> Fin (m + n)
finPlus {m=Z} {n} FZ j impossible
finPlus {m=(S m)} {n} FZ j =
  rewrite plusCommutative m n in
  rewrite plusSuccRightSucc n m in
  weakenN (S m) j
finPlus {m=(S m)} {n} (FS i) j = FS $ finPlus i j

public export
finMul : (m, n : Nat) -> Fin m -> Fin (S n * m)
finMul Z n i = absurd i
finMul (S m) Z i = rewrite plusZeroRightNeutral (S m) in i
finMul (S m) (S n) i =
  weaken $ replace {p=Fin} (plusCommutative (mult (S n) (S m)) m) $
    weakenN m $ finMul (S m) n i

public export
finPow : (m, n : Nat) -> Fin m -> Fin (power m n)
finPow m Z i = FZ
finPow Z (S n) i = absurd i
finPow (S Z) (S n) FZ = rewrite powerOneIsOne n in FZ
finPow (S (S m)) (S n) i =
  let fp = finPow (S (S m)) n i in
  finPlus fp $ finMul _ m fp

public export
finMulFin : {m, n : Nat} -> Fin m -> Fin n -> Fin (m * n)
finMulFin {m=Z} {n} i j = absurd i
finMulFin {m} {n=Z} i j = absurd j
finMulFin {m=(S m)} {n=(S n)} FZ j = FZ
finMulFin {m=(S m)} {n=(S n)} (FS i) FZ = FZ
finMulFin {m=(S m)} {n=(S n)} (FS i) (FS j) =
  rewrite multRightSuccPlus m n in
  -- (1 + i) * (1 + j) = 1 + j + i + i * j
  FS $ finPlus j $ finPlus i $ finMulFin {m} {n} i j

public export
finPowFin : {m, n : Nat} -> Vect m (Fin n) -> Fin (power n m)
finPowFin {m=Z} {n} [] = FZ
finPowFin {m=(S m)} {n} (x :: v) = finMulFin x $ finPowFin {m} {n} v

public export
foldrNat : (a -> a) -> a -> Nat -> a
foldrNat f acc Z = acc
foldrNat f acc (S n) = foldrNat f (f acc) n

public export
foldrNatNoUnit : (a -> a) -> a -> a -> Nat -> a
foldrNatNoUnit f unit acc Z = unit
foldrNatNoUnit f unit acc (S n) = foldrNat f acc n

public export
collectPairsAcc : List Nat -> List (Nat, Nat) -> List (Nat, Nat)
collectPairsAcc [] acc = acc
collectPairsAcc (n :: ns) [] = collectPairsAcc ns [(n, 1)]
collectPairsAcc (n :: ns) ps@((n', c) :: ps') =
  if n == n' then
    collectPairsAcc ns ((n', S c) :: ps')
  else
    collectPairsAcc ns $ (n, 1) :: ps

public export
collectPairs : List Nat -> List (Nat, Nat)
collectPairs l = collectPairsAcc l []

public export
equalNatCorrect : {m : Nat} -> equalNat m m = True
equalNatCorrect {m=Z} = Refl
equalNatCorrect {m=(S m')} = equalNatCorrect {m=m'}

public export
toIsTrueNat : (m, n : Nat) -> m = n -> m == n = True
toIsTrueNat m m Refl = equalNatCorrect {m}

public export
toIsTrueMaybeNat : (m, n : Maybe Nat) -> m = n -> m == n = True
toIsTrueMaybeNat Nothing Nothing Refl = Refl
toIsTrueMaybeNat (Just m) (Just m) Refl = equalNatCorrect {m}

public export
0 foldAppendExtensional : {0 a : Type} -> {n : Nat} ->
  (l : List a) -> (v : Vect n a) ->
  foldrImpl (::) [] ((++) l) v = l ++ foldrImpl (::) [] (id {a=(List a)}) v
foldAppendExtensional {a} {n} l v = ?foldAppendExtensional_hole

public export
0 foldLengthAppend : {0 a : Type} -> {n : Nat} ->
  (l : List a) -> (v : Vect n a) ->
  List.length (foldrImpl (::) [] ((++) l) v) =
    length l + (List.length (foldrImpl (::) [] (id {a=(List a)}) v))
foldLengthAppend {a} {n} l v =
  let h = foldrVectHomomorphism in
  trans
    ?foldLengthAppend_hole
    (lengthDistributesOverAppend _ _)

public export
toListLength : {n : Nat} -> {0 a : Type} ->
  (v : Vect n a) -> length (toList v) = n
toListLength {n=Z} {a} [] = Refl
toListLength {n=(S n)} {a} (x :: v) =
  trans (foldLengthAppend [x] v) (cong S $ toListLength {n} {a} v)

public export
predLen : {0 a : Type} -> List a -> Nat
predLen = pred . length

public export
powerZeroOne : (0 n : Nat) -> power n 0 = 1
powerZeroOne n = Refl

public export
powerOneOne : (n : Nat) -> power 1 n = 1
powerOneOne Z = Refl
powerOneOne (S n) = rewrite powerOneOne n in Refl

public export
mulPowerZeroRightNeutral : {0 m, n : Nat} -> m * (power n 0) = m
mulPowerZeroRightNeutral {m} {n} = rewrite multOneRightNeutral m in Refl

public export
powerOfSum : (x, y, z : Nat) -> power x (y + z) = power x y * power x z
powerOfSum x Z z = rewrite plusZeroRightNeutral (power x z) in Refl
powerOfSum x (S y) z =
  trans (cong (mult x) (powerOfSum x y z)) $
    multAssociative x (power x y) (power x z)

public export
mulToPower : (x, y, z : Nat) -> power (x * y) z = power x z * power y z
mulToPower x y Z = Refl
mulToPower x y (S z) =
  rewrite mulToPower x y z in
  rewrite sym (multAssociative x y (mult (power x z) (power y z))) in
  rewrite sym (multAssociative x (power x z) (mult y (power y z))) in
  cong (mult x) $
    trans
      (trans
        (multAssociative y (power x z) (power y z))
        (rewrite multCommutative y (power x z) in Refl))
      (sym $ multAssociative (power x z) y (power y z))

public export
powerOfMul : (x, y, z : Nat) -> power x (y * z) = power (power x y) z
powerOfMul x Z z = sym (powerOneOne z)
powerOfMul x (S y) Z = rewrite multZeroRightZero y in Refl
powerOfMul x (S y) (S z) =
  rewrite powerOfSum x (S z) (y * (S z)) in
  rewrite multRightSuccPlus y z in
  rewrite powerOfSum x y (y * z) in
  rewrite sym
    (multAssociative x (power x z) (mult (power x y) (power x (mult y z)))) in
  rewrite sym (multAssociative x (power x y) (power (mult x (power x y)) z)) in
  rewrite powerOfMul x y z in
  rewrite multAssociative (power x z) (power x y) (power (power x y) z) in
  rewrite multCommutative (power x z) (power x y) in
  rewrite sym (multAssociative (power x y) (power x z) (power (power x y) z)) in
  cong (mult x) $ cong (mult (power x y)) $
    sym $ mulToPower x (power x y) z

public export
powerOfMulSym : (x, y, z : Nat) -> power x (y * z) = power (power x z) y
powerOfMulSym x y z = rewrite multCommutative y z in powerOfMul x z y

public export
LTEReflectsLte : {k, n : Nat} -> k `LTE` n -> lte k n = True
LTEReflectsLte LTEZero = Refl
LTEReflectsLte (LTESucc lte) = LTEReflectsLte lte

public export
notLTEReflectsLte : {k, n : Nat} -> Not (k `LTE` n) -> lte k n = False
notLTEReflectsLte nlte with (lte k n) proof ltekn
  notLTEReflectsLte nlte | True = void $ nlte $ lteReflectsLTE _ _ ltekn
  notLTEReflectsLte nlte | False = Refl

public export
notLteReflectsLTE : {k, n : Nat} -> lte k n = False -> Not (k `LTE` n)
notLteReflectsLTE nlte with (isLTE k n)
  notLteReflectsLTE nlte | Yes yLTE =
    case trans (sym nlte) (LTEReflectsLte yLTE) of Refl impossible
  notLteReflectsLTE nlte | No notLTE = notLTE

public export
gteTogt : {m, n : Nat} -> Not (LTE (S m) n) -> Not (m = n) -> Not (LT m (S n))
gteTogt {m} {n=Z} gt neq (LTESucc lte) = neq $ sym (lteZeroIsZero lte)
gteTogt {m=Z} {n=(S n)} gt neq (LTESucc lte) = gt $ LTESucc LTEZero
gteTogt {m=(S m)} {n=(S n)} gt neq (LTESucc lte) =
  gt $ LTESucc $ lteTolt (fromLteSucc lte) $ \ eqmn => neq $ cong S eqmn

public export
mod'Z : (m : Nat) -> mod' m m Z = Z
mod'Z Z = Refl
mod'Z (S m) = rewrite minusZeroRight m in mod'Z m

public export
div'One : (k : Nat) -> div' k k 0 = k
div'One Z = Refl
div'One (S k) = rewrite minusZeroRight k in cong S (div'One k)

public export
div'LT : (k, k' : Nat) -> LTE (div' k k' 0) k
div'LT Z Z = LTEZero
div'LT (S k) Z = LTEZero
div'LT Z (S k') = LTEZero
div'LT (S k) (S k') = LTESucc $ rewrite minusZeroRight k' in div'LT k k'

public export
divMinusMono : (fuel, k, n : Nat) ->
  lte k n = False -> LT (div' fuel (minus k (S n)) n) (div' (S fuel) k n)
divMinusMono fuel k n gtkn = rewrite gtkn in reflexive

public export
lteToDiff : {m, n : Nat} -> LTE m n -> (k : Nat ** k + m = n)
lteToDiff {m} {n} lte = (minus n m ** plusMinusLte m n lte)

public export
diffToLte : {m, n, k : Nat} -> k + m = n -> LTE m n
diffToLte {m} {k=Z} Refl = reflexive
diffToLte {m} {n} {k=(S k)} pleq =
  lteSuccLeft $ diffToLte {m=(S m)} {n} {k} $
    rewrite sym (plusSuccRightSucc k m) in
    pleq

public export
0 multDivLTLemma : (k, m, n, diffmsnsk : Nat) ->
  diffmsnsk + S k = m * S n ->
  (diffmdivksn : Nat ** diffmdivksn + S (divNatNZ k (S n) SIsNonZero) = m)
multDivLTLemma k m n diffmsnsk diffmsnskeq = ?multDivLTLemma_hole

public export
0 multDivLT : {k, m, n : Nat} ->
  LT k (m * n) -> (nz : NonZero n) -> LT (divNatNZ k n nz) m
multDivLT {k} {m} {n=(S n)} lt SIsNonZero =
  let
    (diffmsnsk ** diffmsnskeq) = lteToDiff lt
    (diffmdivksn ** diffmdivksneq) = multDivLTLemma k m n diffmsnsk diffmsnskeq
  in
  diffToLte
    {m=(S (divNatNZ k (S n) SIsNonZero))} {n=m} {k=diffmdivksn} diffmdivksneq

public export
multAddLT : {k, m, n, p : Nat} ->
  LT k n -> LT m p -> LT (p * k + m) (n * p)
multAddLT {k} {m} {n=Z} {p} ltkn ltmp = void $ succNotLTEzero ltkn
multAddLT {k} {m} {n=(S n)} {p=Z} ltkn ltmp = void $ succNotLTEzero ltmp
multAddLT {k} {m} {n=(S n)} {p=(S p)} (LTESucc ltkn) (LTESucc ltmp) =
  LTESucc $
    rewrite multRightSuccPlus n p in
    rewrite plusCommutative p (plus n (mult n p)) in
    let mpk = multCommutative k p in
    plusLteMonotone
      (plusLteMonotone ltkn $
        replace {p=(\q => LTE q (n * p))} mpk $ multLteMonotoneLeft _ _ _ ltkn)
      ltmp

public export
modLTDivisor : (m, n : Nat) -> LT (modNatNZ m (S n) SIsNonZero) (S n)
modLTDivisor m n = boundModNatNZ m (S n) SIsNonZero

public export
modLtDivisor : (m, n : Nat) -> IsTrue $ gt (S n) $ modNatNZ m (S n) SIsNonZero
modLtDivisor m n = LTEReflectsLte $ fromLteSucc $ modLTDivisor m n

public export
minusModulo : (modulus, m, n : Integer) -> Integer
minusModulo modulus m n =
  if modulus == 0 then
    0
  else
    if m >= n then
      mod (m - n) modulus
    else
      let r = mod (n - m) modulus in
      if r == 0 then 0 else modulus - r

public export
magmaFromNonEmptyList : {a : Type} -> (a -> a -> a) -> a -> List a -> a
magmaFromNonEmptyList f x [] = x
magmaFromNonEmptyList f x (x' :: l) = f x $ magmaFromNonEmptyList f x' l

public export
monoidFromList : {a : Type} -> a -> (a -> a -> a) -> List a -> a
monoidFromList id compose [] = id
monoidFromList id compose (x :: l) = magmaFromNonEmptyList compose x l

public export
mapNonEmpty : {0 a, b : Type} -> {0 f : a -> b} -> {0 l : List a} ->
  {0 ne : NonEmpty l} -> NonEmpty (map f l)
mapNonEmpty {a} {b} {f} {l=(x :: xs)} {ne=IsNonEmpty} = IsNonEmpty

public export
pairInj1 : {a, b : Type} -> {p, p' : (a, b)} -> p = p' -> fst p = fst p'
pairInj1 Refl = Refl

public export
pairInj2 : {a, b : Type} -> {p, p' : (a, b)} -> p = p' -> snd p = snd p'
pairInj2 Refl = Refl

public export
pairFstSnd : {0 a, b : Type} -> (p : (a, b)) -> p = (fst p, snd p)
pairFstSnd {a} {b} (ela, elb) = Refl

public export
pairEqCong : {0 a, b : Type} -> {p, p' : (a, b)} ->
  fst p = fst p' -> snd p = snd p' -> p = p'
pairEqCong {a} {b} {p=(ela, elb)} {p'=(ela', elb')} eq eq' =
  rewrite eq in rewrite eq' in Refl

public export
DecEqPred : (a: Type) -> Type
DecEqPred a = (x, x': a) -> Dec (x = x')

export
encodingDecEq : {a, b : Type} ->
  (encode : a -> b) -> (decode : b -> Maybe a) ->
  (encodingIsCorrect : (x : a) -> decode (encode x) = Just x) ->
  (bDecEq : DecEqPred b) ->
  DecEqPred a
encodingDecEq encode decode encodingIsCorrect bDecEq x x' with
  (bDecEq (encode x) (encode x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | Yes eq = Yes $
      injective $
        trans
          (sym (encodingIsCorrect x))
          (trans
            (cong decode eq)
            (encodingIsCorrect x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | No neq =
      No $ \xeq => neq $ cong encode xeq

public export
finEncodingDecEq : {a : Type} -> {size : Nat} ->
  (encode : a -> Fin size) -> (decode : Fin size -> a) ->
  (encodingIsCorrect : (x : a) -> decode (encode x) = x) ->
  DecEqPred a
finEncodingDecEq {a} {size} encode decode encodingIsCorrect =
  encodingDecEq {a} {b=(Fin size)}
    encode (Just . decode) (\x => rewrite encodingIsCorrect x in Refl) decEq

public export
finDecPred : {n : Nat} -> (p : Fin n -> Type) -> ((x : Fin n) -> Dec (p x)) ->
  Dec ((x : Fin n) -> p x)
finDecPred {n=Z} p d = Yes $ \x => case x of _ impossible
finDecPred {n=(S n)} p d =
  case d FZ of
    Yes yes => case finDecPred {n} (p . FS) (\x => d $ FS x) of
      Yes yes' => Yes $ \x => case x of
        FZ => yes
        FS x' => yes' x'
      No no' => No $ \yes' => no' $ \x => yes' $ FS x
    No no => No $ \yes => no $ yes FZ

public export
FinDecoder : Type -> Nat -> Type
FinDecoder a size = Fin size -> a

public export
VectDecoder : Type -> Nat -> Type
VectDecoder = flip Vect

public export
VectToFinDecoder : {0 a : Type} -> {0 size : Nat} ->
  VectDecoder a size -> FinDecoder a size
VectToFinDecoder {a} {size} = flip $ index {len=size} {elem=a}

public export
FinEncoder : {a : Type} -> {size : Nat} -> FinDecoder a size -> Type
FinEncoder {a} {size} decoder = (e : a) -> (x : Fin size ** decoder x = e)

public export
NatEncoder : {a : Type} -> {size : Nat} -> FinDecoder a size -> Type
NatEncoder {a} {size} decoder =
  (e : a) ->
    (n : Nat ** x : IsJustTrue (natToFin n size) ** decoder (fromIsJust x) = e)

public export
VectEncoder : {a : Type} -> {size : Nat} -> VectDecoder a size -> Type
VectEncoder {a} {size} vd = NatEncoder {a} {size} (VectToFinDecoder vd)

public export
NatToFinEncoder : {a : Type} -> {size : Nat} -> {d : FinDecoder a size} ->
  NatEncoder {a} {size} d -> FinEncoder {a} {size} d
NatToFinEncoder {a} {size} {d} enc e with (enc e)
  NatToFinEncoder {a} {size} {d} enc e | (n ** x ** eq) = (fromIsJust x ** eq)

public export
VectToFinEncoder : {a : Type} -> {size : Nat} -> {vd : VectDecoder a size} ->
  VectEncoder {a} {size} vd -> FinEncoder {a} {size} (VectToFinDecoder vd)
VectToFinEncoder {a} {size} {vd} ve ea with (ve ea)
  VectToFinEncoder {a} {size} {vd} ve ea | (n ** islt ** eq) =
    (fromIsJust islt ** eq)

public export
FinDecEncoding : (a : Type) -> (size : Nat) -> Type
FinDecEncoding a size = DPair (FinDecoder a size) FinEncoder

public export
NatDecEncoding : {a : Type} -> {size : Nat} ->
  (d : FinDecoder a size) -> NatEncoder {a} {size} d -> FinDecEncoding a size
NatDecEncoding {a} {size} d enc = (d ** NatToFinEncoder enc)

public export
VectDecEncoding : {a : Type} -> {size : Nat} ->
  (d : VectDecoder a size) -> VectEncoder {a} {size} d -> FinDecEncoding a size
VectDecEncoding {a} {size} d e = (flip index d ** VectToFinEncoder e)

public export
fdeEq : {0 a : Type} -> {n : Nat} -> FinDecEncoding a n -> a -> a -> Bool
fdeEq enc x x' = fst (snd enc x) == fst (snd enc x')

public export
(a : Type) => (n : Nat) => (enc : FinDecEncoding a n) => Eq a where
  (==) = fdeEq {a} {n} enc

public export
fdeLt : {0 a : Type} -> {n : Nat} -> FinDecEncoding a n -> a -> a -> Bool
fdeLt enc x x' = fst (snd enc x) < fst (snd enc x')

public export
(a : Type) => (n : Nat) => (enc : FinDecEncoding a n) => Ord a where
  (<) = fdeLt {a} {n} enc

public export
fdeDecEq : {0 a : Type} -> {n : Nat} -> FinDecEncoding a n -> DecEqPred a
fdeDecEq (decode ** encode) e e' =
  case (decEq (fst $ encode e) (fst $ encode e')) of
    Yes eq => Yes $
      trans (sym (snd $ encode e)) (trans (cong decode eq) (snd $ encode e'))
    No neq => No $ \yes => neq $ case yes of Refl => Refl

public export
(a : Type) => (n : Nat) => Show a => Show (FinDecoder a n) where
  show = show . finFToVect

public export
(a : Type) => (n : Nat) => Show a => Show (FinDecEncoding a n) where
  show = show . fst

public export
(a : Type) => (n : Nat) => (enc : FinDecEncoding a n) => DecEq a where
  decEq = fdeDecEq {a} {n} enc

public export
FinVoidDecoder : FinDecoder Void 0
FinVoidDecoder FZ impossible
FinVoidDecoder (FS _) impossible

public export
FinVoidEncoder : FinEncoder FinVoidDecoder
FinVoidEncoder i = void i

public export
FinVoidDecEncoding : FinDecEncoding Void 0
FinVoidDecEncoding = (FinVoidDecoder ** FinVoidEncoder)

public export
FinUnitDecoder : FinDecoder Unit 1
FinUnitDecoder FZ = ()

public export
FinUnitEncoder : FinEncoder FinUnitDecoder
FinUnitEncoder () = (FZ ** Refl)

public export
FinUnitDecEncoding : FinDecEncoding Unit 1
FinUnitDecEncoding = (FinUnitDecoder ** FinUnitEncoder)

public export
0 FinSumDecoder : {m, n : Nat} -> {ty, ty' : Type} ->
  FinDecoder ty m -> FinDecoder ty' n -> FinDecoder (Either ty ty') (m + n)
FinSumDecoder {m} {n} {ty} {ty'} fde fde' i with (finToNat i) proof prf
  FinSumDecoder {m} {n} {ty} {ty'} fde fde' i | idx with (isLT idx m)
    FinSumDecoder {m} {n} {ty} {ty'} fde fde' i | idx | Yes islt =
      Left $ fde $ natToFinLT {n=m} idx
    FinSumDecoder {m} {n} {ty} {ty'} fde fde' i | idx | No isgte =
      Right $ fde' $
      let islte : LTE (S (minus idx m)) n = ?FinSumDecoder_islte_hole in
      natToFinLT {n} (minus idx m)

public export
0 FinSumEncoder : {m, n : Nat} -> {ty, ty' : Type} ->
  {dec : FinDecoder ty m} -> {dec' : FinDecoder ty' n} ->
  (enc : FinEncoder {a=ty} {size=m} dec) ->
  (enc' : FinEncoder {a=ty'} {size=n} dec') ->
  NatEncoder (FinSumDecoder {m} {n} {ty} {ty'} dec dec')
FinSumEncoder {m} {n} {dec} {dec'} enc enc' (Left e) with (enc e) proof eqe
  FinSumEncoder {m} {n} {dec} {dec'} enc enc' (Left _) | (ence ** Refl)
    with (finToNat ence) proof eqf
      FinSumEncoder {m} {n} {dec} {dec'} enc enc' (Left _) | (ence ** Refl) |
        idx =
          (finToNat ence **
           ?finSumEncoder_hole_left_islte **
           ?finSumEncoder_hole_left_isinv)
FinSumEncoder {m} {n} {dec} {dec'} enc enc' (Right e') with (enc' e') proof eqe
  FinSumEncoder {m} {n} {dec} {dec'} enc enc' (Right _) | (ence' ** Refl)
    with (finToNat ence') proof eqf
      FinSumEncoder {m} {n} {dec} {dec'} enc enc' (Right _) | (ence' ** Refl) |
        idx =
          (m + finToNat ence' **
           ?finSumEncoder_hole_right_islte **
           ?finSumEncoder_hole_right_isinv)

public export
0 FinSumDecEncoding : {m, n : Nat} -> {ty, ty' : Type} ->
  {dec : FinDecoder ty m} -> {dec' : FinDecoder ty' n} ->
  (enc : FinEncoder {a=ty} {size=m} dec) ->
  (enc' : FinEncoder {a=ty'} {size=n} dec') ->
  FinDecEncoding (Either ty ty') (m + n)
FinSumDecEncoding {dec} {dec'} enc enc' =
  NatDecEncoding (FinSumDecoder dec dec') (FinSumEncoder enc enc')

public export
FinIdDecoder : (size : Nat) -> FinDecoder (Fin size) size
FinIdDecoder size = id

public export
FinIdEncoder : (size : Nat) -> FinEncoder (FinIdDecoder size)
FinIdEncoder size i = (i ** Refl)

public export
FinIdDecEncoding : (size : Nat) -> FinDecEncoding (Fin size) size
FinIdDecEncoding size = (FinIdDecoder size ** FinIdEncoder size)

public export
FDEnc : Type -> Type
FDEnc = DPair Nat . FinDecEncoding

public export
fdeSize : {0 a : Type} -> FDEnc a -> Nat
fdeSize = fst

public export
FinType : Type
FinType = DPair Type FDEnc

public export
ftType : FinType -> Type
ftType = DPair.fst

public export
ftEnc : (ft : FinType) -> FDEnc (ftType ft)
ftEnc = DPair.snd

public export
ftSize : FinType -> Nat
ftSize ft = fdeSize (ftEnc ft)

-- A pair of terms of a finite type.
public export
FTPair : FinType -> FinType -> Type
FTPair ft ft' = Pair (ftType ft) (ftType ft')

-- A list of terms of a finite type.
public export
FTList : FinType -> Type
FTList ft = List (ftType ft)

-- A vector of terms of a finite type.
public export
FTVect : Nat -> FinType -> Type
FTVect k ft = Vect k (ftType ft)

-- A vector _indexed_ by a finite type -- that is, a tuple of elements
-- of some (other) type whose length is the size of the finite type.
-- The "I" is for "indexed".
public export
FTIVect : FinType -> Type -> Type
FTIVect ft t = Vect (ftSize ft) t

-- A vector of types indexed by some finite type.
FTITyVect : FinType -> Type
FTITyVect ft = FTIVect ft Type

-- An object of the slice category of `Type` over some `FinType`'s
-- underlying type (i.e. a finite type, or more explicitly, a type
-- with a finite number of terms).
public export
FSlice : FinType -> Type
FSlice ft = ftType ft -> Type

-- A dependent list indexed by terms of a finite type.
public export
FHList : (ft : FinType) -> FTITyVect ft -> Type
FHList ft tys = HVect {n=(ftSize ft)} tys

public export
ListContains : {a : Type} -> List a -> a -> Type
ListContains [] x = Void
ListContains (x :: xs) x' = Either (x = x') (ListContains xs x')

public export
listContainsDec : {a : Type} -> DecEqPred a -> (l : List a) -> (x : a) ->
  Dec (ListContains l x)
listContainsDec deq [] x = No $ \v => void v
listContainsDec deq (x :: xs) x' =
  case deq x x' of
    Yes Refl => Yes $ Left Refl
    No neqx => case listContainsDec deq xs x' of
      Yes c => Yes $ Right c
      No nc => No $ \yes => case yes of
        Left eqx => neqx eqx
        Right c => nc c

public export
ListContainsTrue : {a : Type} -> DecEqPred a -> (l : List a) -> (x : a) -> Type
ListContainsTrue deq l x = IsYesTrue $ listContainsDec deq l x

public export
ListContainsTrueUIP : {a : Type} ->
  (deq : DecEqPred a) -> (l : List a) -> (x : a) ->
  (c, c' : ListContainsTrue deq l x) ->
  c = c'
ListContainsTrueUIP deq l x c c' = uip

public export
ListMember : {a : Type} -> List a -> Type
ListMember {a} l = Subset0 a (ListContains l)

public export
listGet : {a : Type} -> {l : List a} -> ListMember {a} l -> a
listGet {a} {l} = fst0

public export
ListMemberDec : {a : Type} -> DecEqPred a -> List a -> Type
ListMemberDec {a} deq l = Subset0 a (ListContainsTrue deq l)

public export
ListMemberDecInj : {a : Type} ->
  (deq : DecEqPred a) -> (l : List a) -> (m, m' : ListMemberDec deq l) ->
  fst0 m = fst0 m' -> m = m'
ListMemberDecInj {a} deq l (Element0 x c) (Element0 x' c') eq =
  case eq of
    Refl => rewrite ListContainsTrueUIP deq l x c c' in Refl

public export
FinSubEncoding : Type -> Nat -> Type
FinSubEncoding a size = (FinDecEncoding a size, List a)

public export
fseEnc : {a : Type} -> {n : Nat} -> FinSubEncoding a n -> FinDecEncoding a n
fseEnc = fst

public export
fseList : {a : Type} -> {n : Nat} -> FinSubEncoding a n -> List a
fseList = snd

public export
FSEMember : {a : Type} -> {n : Nat} -> FinSubEncoding a n -> Type
FSEMember enc = ListMemberDec decEq (fseList enc)

public export
FSEMemberInj : {a : Type} -> {n : Nat} -> (fse : FinSubEncoding a n) ->
  (x, x' : FSEMember fse) -> fst0 x = fst0 x' -> x = x'
FSEMemberInj enc = ListMemberDecInj decEq (fseList enc)

public export
fseEq : {a : Type} -> {n : Nat} -> (enc : FinSubEncoding a n) ->
  FSEMember enc -> FSEMember enc -> Bool
fseEq enc x x' = fdeEq (fseEnc enc) (fst0 x) (fst0 x')

public export
fseLt : {a : Type} -> {n : Nat} ->
  (enc : FinSubEncoding a n) -> FSEMember enc -> FSEMember enc -> Bool
fseLt enc x x' = fdeLt (fseEnc enc) (fst0 x) (fst0 x')

public export
fseDecEq : {a : Type} -> {  n : Nat} -> (enc : FinSubEncoding a n) ->
  DecEqPred (FSEMember enc)
fseDecEq enc x x' = case fdeDecEq (fseEnc enc) (fst0 x) (fst0 x') of
  Yes eq => Yes $ FSEMemberInj enc x x' eq
  No neq => No $ \eq => case eq of Refl => neq Refl

-- A list with a length stored together with it at run time.
public export
record LList (a : Type) (len : Nat) where
  constructor MkLList
  llList : List a
  llValid : length llList = len

public export
Show a => (len : Nat) => Show (LList a len) where
  show (MkLList l _) = show l ++ "(len=" ++ show len ++ ")"

public export
record LLAlg (a, b : Type) where
  constructor MkLLAlg
  llZ : b
  llS : Nat -> a -> b -> b

public export
llCata : {len : Nat} -> LLAlg a b -> LList a len -> b
llCata {len} (MkLLAlg z s) (MkLList l valid) = llCataInternal z s len l valid
  where
  llCataInternal :
    b ->
    (Nat -> a -> b -> b) ->
    (len : Nat) ->
    (l : List a) ->
    length l = len ->
    b
  llCataInternal z s Z [] Refl = z
  llCataInternal z s (S n) (x :: xs) valid =
    s n x $ llCataInternal z s n xs $ injective valid

public export
InitLList : {a : Type} -> (l : List a) -> LList a (length l)
InitLList l = MkLList l Refl

public export
blockIndent : Nat -> String -> String
blockIndent n = unlines . map (indent n) . lines

public export
mapExtEq : {0 a, b : Type} -> (f, g : a -> b) -> (l : List a) ->
  ((x : a) -> f x = g x) -> map f l = map g l
mapExtEq f g [] eq = Refl
mapExtEq f g (x :: xs) eq = rewrite eq x in cong ((::) _) $ mapExtEq f g xs eq

public export
DecEq Void where
  decEq _ _ impossible

public export
Eq Void where
  _ == _ impossible

public export
BoolCP : Type
BoolCP = Either Unit Unit

public export
BCPFalse : BoolCP
BCPFalse = Left ()

public export
BCPTrue : BoolCP
BCPTrue = Right ()

public export
FS3CP : Type
FS3CP = Either Unit BoolCP

public export
FS3CP0 : FS3CP
FS3CP0 = Left ()

public export
FS3CP1 : FS3CP
FS3CP1 = Right BCPFalse

public export
FS3CP2 : FS3CP
FS3CP2 = Right BCPTrue

public export
zipLen : {0 a, b, c : Type} -> (a -> b -> c) -> (l : List a) -> (l' : List b) ->
  length l = length l' -> List c
zipLen f [] [] Refl = []
zipLen f [] (x :: xs) Refl impossible
zipLen f (x :: xs) [] Refl impossible
zipLen f (x :: xs) (y :: ys) eq = f x y :: zipLen f xs ys (injective eq)

public export
nzUnique : {n : Nat} -> (nz, nz' : NonZero n) -> nz = nz'
nzUnique {n=(S n)} SIsNonZero SIsNonZero = Refl

-- The number of bits required to store a natural number less than or equal to
-- the input.  (Note that we don't need any bits to store a number less than
-- or equal to 0, because it can only be zero, so we know what it is from the
-- type alone.)
public export
bitsNeededFuel : (bits, target, fuel : Nat) -> Nat
bitsNeededFuel bits target Z = bits
bitsNeededFuel bits target (S n) =
  if power 2 bits > target then bits else bitsNeededFuel (S bits) target n

public export
bitsNeeded : Nat -> Nat
bitsNeeded n = bitsNeededFuel 0 n n

public export
succNonZero : {n : Nat} -> Not (S n = 0)
succNonZero {n=Z} Refl impossible
succNonZero {n=(S n)} Refl impossible

public export
plusZeroLeftZero : {m, n : Nat} -> m + n = 0 -> m = 0
plusZeroLeftZero {m=Z} {n} _ = Refl
plusZeroLeftZero {m=(S m)} {n} Refl impossible

public export
plusZeroRightZero : {m, n : Nat} -> m + n = 0 -> n = 0
plusZeroRightZero {m} {n} eq =
  plusZeroLeftZero {m=n} {n=m} $ trans (sym $ plusCommutative m n) eq

-- Idris's `last'`, but with its internals exported to allow things to
-- be proven about it.
public export
maybeLast : List a -> Maybe a
maybeLast [] = Nothing
maybeLast xs@(_::_) = Just (last xs)

public export
applyPure : Applicative f => {0 a, b : Type} -> f (a -> b) -> a -> f b
applyPure = (|>) pure . (<*>)

public export
unitUnique : (x, y : Unit) -> x = y
unitUnique () () = Refl
