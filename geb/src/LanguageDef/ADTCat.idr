module LanguageDef.ADTCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

-----------------------------------
-----------------------------------
---- Geb terms (S-expressions) ----
-----------------------------------
-----------------------------------

-----------------------------
---- Nameless definition ----
---- Nameless definition ----

public export
MaybeSq : Type -> Type
MaybeSq = ProductF Maybe Maybe

public export
data FreeMaybeSq : Type -> Type where
  InTV : {0 a : Type} -> a -> FreeMaybeSq a
  InTC : {0 a : Type} -> MaybeSq (FreeMaybeSq a) -> FreeMaybeSq a

public export
MuMaybeSq : Type
MuMaybeSq = FreeMaybeSq Void

public export
PosFreeMaybeSq : Type
PosFreeMaybeSq = FreeMaybeSq Unit

public export
data CofreeMaybeSq : Type -> Type where
  InTN : {0 a : Type} -> a -> Inf (MaybeSq (FreeMaybeSq a)) -> CofreeMaybeSq a

public export
NuMaybeSq : Type
NuMaybeSq = CofreeMaybeSq Unit

-------------------------------------
---- Definition and constructors ----
-------------------------------------

-- A functor which generates, through its initial algebra, a
-- category-theoretic analogue of an S-expression, or generic
-- term of any ADT.
--
-- This functor may be written anonymously as `1 + 2 * I + I ^ 2`.
-- That is isomorphic to `(1 + I) ^ 2`, which provides another way
-- of looking at it:  as a tree node with up to two children.

public export
data ADTTermF : Type -> Type where
  ADTUnit : {0 carrier : Type} -> ADTTermF carrier
  ADTLeft : {0 carrier : Type} -> carrier -> ADTTermF carrier
  ADTRight : {0 carrier : Type} -> carrier -> ADTTermF carrier
  ADTPair : {0 carrier : Type} -> carrier -> carrier -> ADTTermF carrier

public export
Functor ADTTermF where
  map f ADTUnit = ADTUnit
  map f (ADTLeft x) = ADTLeft (f x)
  map f (ADTRight x) = ADTRight (f x)
  map f (ADTPair x y) = ADTPair (f x) (f y)

-- The initial algebra of ADTTermF, a type whose terms are
-- category-theoretic S-expressions.  This is the only recursive
-- type definition in the core logic of Geb.
public export
data ADTTerm : Type where
  InADTT : ADTTermF ADTTerm -> ADTTerm

-- Convenience constructors for `ADTTerm`.

public export
($!) : ADTTerm
($!) = InADTT ADTUnit

prefix 10 $<
public export
($<) : ADTTerm -> ADTTerm
($<) t = InADTT (ADTLeft t)

prefix 10 $>
public export
($>) : ADTTerm -> ADTTerm
($>) t = InADTT (ADTRight t)

infixr 12 $$
public export
($$) : ADTTerm -> ADTTerm -> ADTTerm
t $$ t' = InADTT (ADTPair t t')

----------------------
---- Term algebra ----
----------------------

public export
TermAlg : Type -> Type
TermAlg a = ADTTermF a -> a

public export
TermEndoAlg : Type
TermEndoAlg = TermAlg ADTTerm

----------------------------------------------------------
---- Zero-usage (compile-time-only) term catamorphism ----
----------------------------------------------------------

public export
0 termCataZeroUsage : {0 a : Type} -> (0 _ : TermAlg a) -> (0 _ : ADTTerm) -> a
termCataZeroUsage alg (InADTT t) = alg $ case t of
  ADTUnit => ADTUnit
  ADTLeft t => ADTLeft (termCataZeroUsage alg t)
  ADTRight t => ADTRight (termCataZeroUsage alg t)
  ADTPair t t' => ADTPair (termCataZeroUsage alg t) (termCataZeroUsage alg t')

--------------------------------------
---- Compile-time term properties ----
--------------------------------------

public export
TermSizeAlg : TermAlg Nat
TermSizeAlg ADTUnit = 1
TermSizeAlg (ADTLeft t) = S t
TermSizeAlg (ADTRight t) = S t
TermSizeAlg (ADTPair t t') = S (t + t')

public export
0 termSize : (0 _ : ADTTerm) -> Nat
termSize = termCataZeroUsage TermSizeAlg

public export
TermDepthAlg : TermAlg Nat
TermDepthAlg ADTUnit = 1
TermDepthAlg (ADTLeft t) = S t
TermDepthAlg (ADTRight t) = S t
TermDepthAlg (ADTPair t t') = smax t t'

public export
0 termDepth : (0 _ : ADTTerm) -> Nat
termDepth = termCataZeroUsage TermDepthAlg

----------------------------------------------
---- Continuation-passing-style term fold ----
----------------------------------------------

mutual
  public export
  termFold : {0 a : Type} -> TermAlg a -> (a -> a) -> ADTTerm -> a
  termFold alg cont (InADTT t) = case t of
    ADTUnit => cont (alg ADTUnit)
    ADTLeft l => termFold alg (cont . alg . ADTLeft) l
    ADTRight r => termFold alg (cont . alg . ADTRight) r
    ADTPair l r => termFold alg (termFoldPair alg cont r) l

  public export
  termFoldPair : {0 a : Type} -> TermAlg a -> (a -> a) -> ADTTerm -> a -> a
  termFoldPair alg cont r l = termFold alg (cont . alg . ADTPair l) r

---------------------------------------
---- Term-processing stack machine ----
---------------------------------------

-- `TermStack` is a concrete data-structure representation of the continuation
-- function `a -> a` in `termFold`/`termFoldPair`.

public export
data TermStackElem : (0 _ : Type) -> Type where
  TSELeft : {0 a : Type} -> TermStackElem a
  TSERight : {0 a : Type} -> TermStackElem a
  TSEPairWithRightTerm : {0 a : Type} -> ADTTerm -> TermStackElem a
  TSEPairWithLeftResult : {0 a : Type} -> a -> TermStackElem a

public export
TermStack : (0 _ : Type) -> Type
TermStack a = List (TermStackElem a)

mutual
  public export
  partial
  termStackRun : {0 a : Type} ->
    TermAlg a -> TermStack a -> ADTTerm -> a
  termStackRun alg stack (InADTT t) = case t of
    ADTUnit => termContRun alg stack (alg ADTUnit)
    ADTLeft l => termStackRun alg (TSELeft :: stack) l
    ADTRight r => termStackRun alg (TSERight :: stack) r
    ADTPair l r => termStackRun alg (TSEPairWithRightTerm r :: stack) l

  public export
  partial
  termContRun : {0 a : Type} -> TermAlg a -> TermStack a -> a -> a
  termContRun {a} alg [] result = result
  termContRun {a} alg (elem :: stack) result = case elem of
    TSELeft => termContRun alg stack (alg $ ADTLeft result)
    TSERight => termContRun alg stack (alg $ ADTRight result)
    TSEPairWithRightTerm r =>
      termStackRun alg (TSEPairWithLeftResult result :: stack) r
    TSEPairWithLeftResult l => termContRun alg stack (alg $ ADTPair l result)

------------------------------------------
---- Tail-recursive term catamorphism ----
------------------------------------------

public export
termCata : {0 a : Type} -> TermAlg a -> ADTTerm -> a
termCata alg = termFold alg id
