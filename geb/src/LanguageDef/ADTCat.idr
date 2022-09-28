module LanguageDef.ADTCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

-----------------------------------
-----------------------------------
---- Geb terms (S-expressions) ----
-----------------------------------
-----------------------------------

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

---------------------------------------
---- Term-processing stack machine ----
---------------------------------------

-- A stack-machine implementation of term processing by a metalanguage
-- function.
public export
termFold : {0 a : Type} -> TermAlg a -> (a -> a) -> ADTTerm -> a
termFold alg cont (InADTT t) = case t of
  ADTUnit =>
    cont (alg ADTUnit)
  ADTLeft l =>
    termFold alg (cont . alg . ADTLeft) l
  ADTRight r =>
    termFold alg (cont . alg . ADTRight) r
  ADTPair l r =>
    termFold alg (\l' => termFold alg (cont . alg . ADTPair l') r) l

----------------------------
---- Term catamorphisms ----
----------------------------

public export
termCata : {0 a : Type} -> TermAlg a -> ADTTerm -> a
termCata alg = termFold alg id
