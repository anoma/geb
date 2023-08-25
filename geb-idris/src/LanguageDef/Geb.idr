module LanguageDef.Geb

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.PolyCat
import LanguageDef.Theories
import LanguageDef.Figures
import LanguageDef.DiagramCat
import LanguageDef.RefinedADT
import LanguageDef.Adjunctions
import LanguageDef.NatPrefixCat
import LanguageDef.ProgFinSet
import LanguageDef.PolyIndTypes
import LanguageDef.Syntax

%default total

--------------------------------------------------
--------------------------------------------------
---- Binary trees and types dependent on them ----
--------------------------------------------------
--------------------------------------------------

--------------------------------------------------------
---- Binary trees as free monads over product monad ----
--------------------------------------------------------

public export
ProdAlg : Type -> Type
ProdAlg = Algebra ProductMonad

public export
ProdCoalg : Type -> Type
ProdCoalg = Coalgebra ProductMonad

-- A binary tree may be viewed as the free monad over the product monad
-- (which is the monad of the product adjunction; it takes `a` to `(a, a)`).
--
-- `BinTreeF` is the bifunctor such that for each `A : Type`,
-- `Mu[BinTreeF(A)]` == FreeMonad[ProductMonad](A).  It is what we
-- call the "translate functor" (see below, where we define the translate
-- functor of `BinTreeF` itself) of the product monad.
--
-- Using `|>` rather than `.` is insignificant up to isomorphism; it just
-- establishes the convention that an atom is `Left` and a pair is `Right`,
-- rather than the other way around.
public export
BinTreeF : Type -> Type -> Type
BinTreeF = (|>) ProductMonad . Either

public export
Bifunctor BinTreeF where
  bimap = (|>) (mapHom {f=Pair}) . bimap {f=Either}

prefix 11 $$!
public export
($$!) : {0 atom, ty : Type} -> atom -> BinTreeF atom ty
($$!) = Left

infixr 10 $$>
public export
($$>) : {0 atom, ty : Type} -> (ty, ty) -> BinTreeF atom ty
($$>) = Right

%hide LanguageDef.ADTCat.infixr.($$*)
infixr 10 $$*
public export
($$*) : {0 atom, ty : Type} -> ty -> ty -> BinTreeF atom ty
($$*) = ($$>) .* MkPair

public export
BinTreeAlg : Type -> Type -> Type
BinTreeAlg = Algebra . BinTreeF

public export
BinTreeCoalg : Type -> Type -> Type
BinTreeCoalg = Coalgebra . BinTreeF

-- The initial algebra (least fixed point) of `BinTreeF`.
public export
data BinTreeMu : Type -> Type where
  InBTm : {0 atom : Type} -> BinTreeAlg atom (BinTreeMu atom)

public export
outBTm : {0 atom : Type} -> BinTreeCoalg atom (BinTreeMu atom)
outBTm {atom} (InBTm {atom} x) = x

-- The initial algebra of `BinTreeF` is also the free monad of the
-- product monad.
public export
ProdFM : Type -> Type
ProdFM = BinTreeMu

public export
ProdFMAlg : Type -> Type
ProdFMAlg = Algebra ProdFM

prefix 11 $!
public export
($!) : {0 atom : Type} -> atom -> BinTreeMu atom
($!) = InBTm . ($$!)

infixr 10 $>
public export
($>) : {0 atom : Type} -> ProdAlg (BinTreeMu atom)
($>) = InBTm . ($$>)

%hide LanguageDef.ADTCat.infixr.($*)
infixr 10 $*
public export
($*) : {0 atom : Type} -> BinTreeMu atom -> BinTreeMu atom -> BinTreeMu atom
($*) = InBTm .* ($$*)

prefix 11 $:
public export
($:) : {0 atom : Type} ->
  (l : List (BinTreeMu atom)) -> {auto 0 ne : NonEmpty l} -> BinTreeMu atom
($:) {atom} (x :: []) {ne=IsNonEmpty} = x
($:) {atom} (x :: xs@(x' :: xs')) {ne=IsNonEmpty} = x $* $: xs

prefix 11 $:!
public export
($:!) : {0 atom : Type} ->
  (l : List atom) -> {auto 0 ne : NonEmpty l} -> BinTreeMu atom
($:!) {atom} l {ne} = ($:) (map ($!) l) {ne=(mapNonEmpty {l} {ne})}

-- The universal "catamorphism" morphism of the initial algebra `Mu[BinTreeF]`.
public export
binTreeCata : {0 atom, a : Type} -> BinTreeAlg atom a -> BinTreeMu atom -> a
binTreeCata {atom} {a} alg (InBTm x) = alg $ case x of
  Left ea => ($$!) ea
  Right (x1, x2) => binTreeCata alg x1 $$* binTreeCata alg x2

-- The (universal) catamorphism of `Mu[BinTreeF]` is also the universal "eval"
-- morphism for the free monad of the product monad (with a slight
-- rearrangement of parameters via `eitherElim`).  The eval morphism is the
-- right adjunct of the free/forgetful adjunction between the category of
-- F-algebras of `ProductMonad` and `Type`.
public export
prodFMEval : {0 v, a : Type} -> (v -> a) -> ProdAlg a -> ProdFM v -> a
prodFMEval = binTreeCata {atom=v} {a} .* eitherElim

-- The left adjunct of the free/forgetful adjunction between the category of
-- F-algebras of `ProductMonad` and `Type` (the right adjunct is `prodFMEVal`).
public export
prodFMleftAdj : {0 v, a : Type} -> (ProdFM v -> a) -> v -> a
prodFMleftAdj {v} {a} = (|>) ($!)

public export
prodFMBind : {0 a, b : Type} -> (a -> ProdFM b) -> ProdFM a -> ProdFM b
prodFMBind {a} {b} = flip (prodFMEval {v=a} {a=(ProdFM b)}) $ ($>) {atom=b}

-- Evaluate the free monad of the product monad -- equivalently, `BinTreeMu` --
-- to the type of its variables (atoms), using a monoid on the variables.
public export
prodFMEvalMon : {0 v : Type} -> ProdAlg v -> ProdFM v -> v
prodFMEvalMon = prodFMEval {v} id

public export
prodFMvar : {0 atom : Type} -> atom -> ProdFM atom
prodFMvar = ($!)

public export
prodFMcom : {0 atom : Type} -> ProductMonad (ProdFM atom) -> ProdFM atom
prodFMcom = ($>)

public export
prodFMmap : {0 a, b : Type} -> (a -> b) -> ProdFM a -> ProdFM b
prodFMmap = prodFMBind {a} {b} . (.) ($!)

public export
Functor ProdFM where
  map = prodFMmap

public export
prodFMjoin : {0 a : Type} -> ProdFM (ProdFM a) -> ProdFM a
prodFMjoin = prodFMBind {a=(ProdFM a)} {b=a} id

public export
applyHomFM : {0 a, b : Type} ->
  ProductMonad (ProdFM a -> ProdFM b) -> ProdFM a -> ProdFM b
applyHomFM {a} {b} = ($>) .* applyHom {a=(ProdFM a)} {b=(ProdFM b)}

public export
prodFMpure : {0 a : Type} -> a -> ProdFM a
prodFMpure {a} = ($!) {atom=a}

public export
prodFMapp : {0 a, b : Type} -> ProdFM (a -> b) -> ProdFM a -> ProdFM b
prodFMapp {a} {b} =
  prodFMEval {v=(a -> b)} {a=(ProdFM a -> ProdFM b)} prodFMmap applyHomFM

public export
Applicative ProdFM where
  pure = prodFMpure
  (<*>) = prodFMapp

public export
Monad ProdFM where
  (>>=) = flip prodFMBind

public export
prodFMunit : NaturalTransformation Prelude.id ProdFM
prodFMunit atom = ($!) {atom}

public export
prodFMmul : NaturalTransformation (ProdFM . ProdFM) ProdFM
prodFMmul a = prodFMjoin {a}

public export
ProdAlgToFree : {0 a : Type} -> ProdAlg a -> ProdFMAlg a
ProdAlgToFree {a} = prodFMEvalMon {v=a}

public export
ProdAlgFromFree : {0 a : Type} -> ProdFMAlg a -> ProdAlg a
ProdAlgFromFree {a} = (|>) (($>) . mapHom ($!))

-- Like `prodFMapp` but with a monoid on the output factored out.
-- Should have the same input-output behavior as, but perhaps building
-- smaller intermediate structures than:
-- (|>) (prodFMEvalMon {v=a}) . ((|>) . prodFMapp {a=v} {b=a})
public export
prodFMappMon : {0 v, a : Type} -> ProdFM (v -> a) -> ProdAlg a -> ProdFM v -> a
prodFMappMon {v} {a} pat alg =
  prodFMEval {v} {a} (prodFMEvalMon {v=(v -> a)} ((.) alg . applyHom) pat) alg

-- Like `prodFMappMon` but making explicit use of the output being
-- another binary tree.
public export
prodFMappMonTree : {0 v, a : Type} ->
  ProdFM (v -> ProdFM a) -> ProdFM v -> ProdFM a
prodFMappMonTree {v} {a} =
  prodFMEval {v=(v -> ProdFM a)} {a=(ProdFM v -> ProdFM a)}
    (prodFMBind {a=v} {b=a})
    (applyHomFM {a=v} {b=a})

-- Performs more substitutions than `prodFMappMonTree` on the fly by composition
-- in the metalanguage.
public export
prodFMsubstTree : {0 v : Type} ->
  ProdFM (v -> ProdFM v) -> ProdFM v -> ProdFM v
prodFMsubstTree {v} =
  prodFMEval {v=(v -> ProdFM v)} {a=(ProdFM v -> ProdFM v)}
    (prodFMBind {a=v} {b=v})
    (uncurry (|>))

-----------------------------------------------
---- Various forms of product catamorphism ----
-----------------------------------------------

-- An algebra for catamorphisms on pairs of `BinTreeMu`s that uses the
-- product-hom adjunction.
public export
BinTreeProdHomAlg : Type -> Type -> Type -> Type
BinTreeProdHomAlg = (|>) BinTreeAlg . (.) . BinTreeAlg

public export
binTreeProdHomCata : {0 atom, atom', a : Type} ->
  BinTreeProdHomAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeProdHomCata {atom} {atom'} =
  binTreeCata {atom=atom'} {a} .* binTreeCata {atom} {a=(BinTreeAlg atom' a)}

-- The polynomial product of two `BinTreeF` functors -- that is, the product
-- in the category of polynomial endofunctors on `Type`.
--
-- In the polynomial product, the positions are products of those of the
-- individual functors, while the directions are the corresponding coproducts.
public export
BinTreeProdF : Type -> Type -> Type -> Type
BinTreeProdF atom atom' = ProductF (BinTreeF atom) (BinTreeF atom')

-- An algebra of `BinTreeProdF` provides simultaneous induction on a
-- pair of `BinTreeMu`s.  This means that:
--  - The result for a pair of atoms takes into account both atoms
--  - The result for an atom and a pair takes into account both the atom and
--    the result of simultaneous induction on the two branches of the pair
--  - The result for pairs of pairs takes into account the results of
--    simultaneous induction for each of the four pairs of branches of
--    the input trees
public export
BinTreeProdAlg : Type -> Type -> Type -> Type
BinTreeProdAlg = Algebra .* BinTreeProdF

public export
btApplyPure : {0 atom, v, a : Type} ->
  BinTreeF atom (v -> a) -> v -> BinTreeF atom a
btApplyPure {atom} {v} {a} = (|>) (flip applyHom) . flip mapSnd

public export
BinTreeProdHomAlgArgToProdAlgArg : {atom, atom', a : Type} ->
  BinTreeF atom (BinTreeAlg atom' a) ->
  BinTreeF atom' a ->
  (BinTreeF atom a, BinTreeF atom' a)
BinTreeProdHomAlgArgToProdAlgArg {atom} {atom'} {a} =
  (|>) ProductNTUnit . mapFst . btApplyPure {atom} {v=(BinTreeF atom' a)} {a}

public export
binTreeProdCata : {atom, atom', a : Type} ->
  BinTreeProdAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeProdCata =
  binTreeProdHomCata . flip (.*) BinTreeProdHomAlgArgToProdAlgArg

-- The parallel product of two `BinTreeF` functors -- that is, the product
-- in the category of Dirichlet endofunctors on `Type`.
--
-- In the parallel product, the positions and directions are both products
-- of those of the individual functors.  The positions of `BinTreeF atom`
-- are `atom + 1` and the corresponding directions are `Void` for each
-- `atom` and `2` for the `1`, so the positions of `BinTreeParProdF atom atom'`
-- are `atom * atom' + atom' + atom + 1` and the corresponding directions
-- are `Void` for each combination involving `atom` and `4` for the `1`.
public export
BinTreeParProdF : Type -> Type -> Type -> Type
BinTreeParProdF atom atom' =
  BinTreeF (Either (atom, atom') (Either atom atom')) . ProductMonad

-- An algebra of `BinTreeParProdF` provides parallel induction on a
-- pair of `BinTreeMu`s.  This means that:
--  - The result for a pair of atoms takes into account both atoms
--  - The result for an atom and a pair takes into account only the atom
--  - The result for pairs of pairs takes into account the results of parallel
--    induction for each of the four combinations of parallel inductions on one
--    branch of the first input tree with one branch of the second input tree
public export
BinTreeParProdAlg : Type -> Type -> Type -> Type
BinTreeParProdAlg = Algebra .* BinTreeParProdF

public export
BinTreeProdHomAlgArgToParProdAlgArg : {0 atom, atom', a : Type} ->
  BinTreeF atom (BinTreeAlg atom' a) ->
  BinTreeF atom' a ->
  BinTreeParProdF atom atom' a
BinTreeProdHomAlgArgToParProdAlgArg (Left x) (Left x') =
  Left $ Left (x, x')
BinTreeProdHomAlgArgToParProdAlgArg (Left x) (Right (_, _)) =
  Left $ Right $ Left x
BinTreeProdHomAlgArgToParProdAlgArg (Right (_, _)) (Left x') =
  Left $ Right $ Right x'
BinTreeProdHomAlgArgToParProdAlgArg (Right alg) (Right p) =
  Right (applyHom alg (Right p), p)

public export
binTreeParProdCata : {0 atom, atom', a : Type} ->
  BinTreeParProdAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeParProdCata =
  binTreeProdHomCata . flip (.*) BinTreeProdHomAlgArgToParProdAlgArg

-------------------
---- Utilities ----
-------------------

public export
BtShowAlg : {0 atom : Type} ->
  (atom -> String) -> BinTreeAlg atom String
BtShowAlg sha = eitherElim sha $ \(x, x') => "[" ++ x ++ " " ++ x' ++ "]"

public export
btShow : {0 atom : Type} -> (atom -> String) -> BinTreeMu atom -> String
btShow = binTreeCata . BtShowAlg

public export
btShowI : {0 atom : Type} -> Show atom => BinTreeMu atom -> String
btShowI {atom} = btShow show

public export
Show atom => Show (BinTreeMu atom) where
  show = btShowI

public export
BinTreeShowLinesAlg : {0 atom : Type} ->
  (atom -> String) -> BinTreeAlg atom (List String)
BinTreeShowLinesAlg sha (Left ea) =
  [sha ea]
BinTreeShowLinesAlg sha (Right (xs, ys)) =
  ["::"] ++ indentLines xs ++ indentLines ys

public export
binTreeLines : {0 atom : Type} ->
  (atom -> String) -> BinTreeMu atom -> List String
binTreeLines = binTreeCata . BinTreeShowLinesAlg

public export
btShowLines : {0 atom : Type} -> (atom -> String) -> BinTreeMu atom -> String
btShowLines = showLines . binTreeLines

public export
btShowLinesI : {0 atom : Type} -> Show atom => BinTreeMu atom -> String
btShowLinesI {atom} = btShowLines show

public export
BinTreeEqAlg : {0 atom : Type} ->
  DecEqPred atom -> BinTreeParProdAlg atom atom Bool
BinTreeEqAlg deq (Left (Left (ea, ea'))) = isYes $ deq ea ea'
BinTreeEqAlg deq (Left (Right (Left _))) = False
BinTreeEqAlg deq (Left (Right (Right _))) = False
BinTreeEqAlg deq (Right ((eq11, eq12), (eq21, eq22))) = eq11 && eq22

public export
binTreeEq : {0 atom : Type} ->
  DecEqPred atom -> BinTreeMu atom -> BinTreeMu atom -> Bool
binTreeEq = binTreeParProdCata . BinTreeEqAlg

public export
DecEq atom => Eq (BinTreeMu atom) where
  (==) = binTreeEq decEq

----------------------------------
---- Free monad of `BinTreeF` ----
----------------------------------

-- The "translate" functor: `BinTreeTrF[atom, A, X] == A + BinTreeF[atom, X]`.
-- Note, however, that since `BinTreeF[atom, X]` itself is
-- `atom + X * X`, `BinTreeTrF[atom, A, X]` is `A + atom + X * X`, which
-- can also be written `BinTreeF[A + atom, X]`.  So
-- `BinTreeTrF[atom, A] == BinTreeF[A + atom]`.
--
-- The `flip` is insignificant up to ismorphism; we simply use it to make
-- the convention that an `A`-atom of `BinTreeTrF[atom, A, X]` is `Left`
-- whereas an `atom`-atom is `Right`.
public export
BinTreeTrF : Type -> Type -> Type -> Type
BinTreeTrF = BinTreeF .* flip Either

-- A "translated" term.
public export
BTFt : {0 atom, a, x : Type} -> a -> BinTreeTrF atom a x
BTFt = ($$!) . Left

-- An "atom" term.
public export
BTFa : {0 atom, a, x : Type} -> atom -> BinTreeTrF atom a x
BTFa = ($$!) . Right

-- A "pair" term.
public export
BTFp : {0 atom, a, x : Type} -> x -> x -> BinTreeTrF atom a x
BTFp = ($$*)

-- Because for any functor `f`, `FreeMonad[f][a] == Mu[Translate[f,a]]`,
-- and for a binary tree in particular,
-- `Translate[BinTreeF[atom],a] == BinTreeF[A + atom]`, we have
-- `FreeMonad[BinTreeF[atom]][a] == Mu[Translate[BinTreeF[atom],a]] ==
-- Mu[BinTreeF[A + atom]] == BinTreeMu[A + atom]`.
--
-- As with `BinTreeTrF`, the `flip` is insignificant up to ismorphism; we
-- simply use it to make the convention that a variable term of
-- `BinTreeFM[atom, A]` is `Left`, whereas a compound term is `Right`.
public export
BinTreeFM : Type -> Type -> Type
BinTreeFM = BinTreeMu .* flip Either

public export
BinTreeFMAlg : Type -> Type -> Type
BinTreeFMAlg = Algebra . BinTreeFM

-- A "variable" term.
public export
InBTv : {0 atom, a : Type} -> a -> BinTreeFM atom a
InBTv {atom} {a} =
  InBTm {atom=(Either a atom)} . BTFt {atom} {a} {x=(BinTreeFM atom a)}

prefix 11 $!<
public export
($!<) : {0 atom, a : Type} -> a -> BinTreeFM atom a
($!<) = InBTv

-- A "compound" atom term.
public export
InBTa : {0 atom, a : Type} -> atom -> BinTreeFM atom a
InBTa {atom} {a} = ($!) {atom=(Either a atom)} . Right

prefix 11 $!>
public export
($!>) : {0 atom, a : Type} -> atom -> BinTreeFM atom a
($!>) = InBTa

-- A "compound" term.
public export
InBTc : {0 atom, a : Type} ->
  BinTreeF atom (BinTreeFM atom a) -> BinTreeFM atom a
InBTc {atom} {a} = eitherElim InBTa ($>)

-- A "compound" pair term.
public export
InBTp : {0 atom, a : Type} ->
  BinTreeFM atom a -> BinTreeFM atom a -> BinTreeFM atom a
InBTp {atom} {a} = ($*) {atom=(Either a atom)}

-- The universal `eval` morphism for `BinTreeFM`.
-- Because the free monad of a binary tree is isomorphic to a binary
-- tree with an `Either` atom type, this is just a binary tree
-- catamorphism.
public export
binTreeFMEval : {0 atom, v, a : Type} ->
  (v -> a) -> BinTreeAlg atom a -> BinTreeFM atom v -> a
binTreeFMEval {atom} {v} {a} subst alg =
  prodFMEval {v=(Either v atom)} {a}
    (eitherElim subst (alg . ($$!)))
    (alg . ($$>))

public export
binTreeFMBind : {0 atom : Type} -> {0 a, b : Type} ->
  (a -> BinTreeFM atom b) -> BinTreeFM atom a -> BinTreeFM atom b
binTreeFMBind {atom} =
  flip (binTreeFMEval {atom} {v=a} {a=(BinTreeFM atom b)}) $ InBTc {atom} {a=b}

-- Substitute for all "variable" terms in a `BinTreeFM` to produce
-- a term with no variables (`BinTreeMu`).
public export
btFullSubst : {0 atom, v : Type} ->
  (v -> BinTreeMu atom) -> BinTreeFM atom v -> BinTreeMu atom
btFullSubst {atom} {v} subst =
  prodFMBind {a=(Either v atom)} {b=atom} (eitherElim subst ($!))

public export
binTreeFMEvalMon : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeFM atom a -> a
binTreeFMEvalMon {atom} {a} = binTreeFMEval {atom} {v=a} {a} id

public export
binTreeFMvar : {0 atom, a: Type} -> a -> BinTreeFM atom a
binTreeFMvar = InBTv

public export
binTreeFMcom : {0 atom , a: Type} ->
  BinTreeF atom (BinTreeFM atom a) -> BinTreeFM atom a
binTreeFMcom = InBTc

public export
binTreeFMmap : {0 atom, a, b : Type} ->
  (a -> b) -> BinTreeFM atom a -> BinTreeFM atom b
binTreeFMmap = binTreeFMBind . (.) InBTv

public export
Functor (BinTreeFM atom) where
  map = binTreeFMmap

public export
binTreeFMjoin : {0 atom, a : Type} ->
  BinTreeFM atom (BinTreeFM atom a) -> BinTreeFM atom a
binTreeFMjoin = binTreeFMBind {atom} {a=(BinTreeFM atom a)} {b=a} id

public export
binTreeFMpure : {0 atom, a : Type} -> a -> BinTreeFM atom a
binTreeFMpure = InBTv

public export
btApplyHom : {0 atom, a, b : Type} ->
  BinTreeF atom (BinTreeFM atom a -> BinTreeFM atom b) ->
  BinTreeFM atom a -> BinTreeFM atom b
btApplyHom = flip (eitherElim InBTa . flip applyHomFM)

public export
binTreeFMapp : {0 atom, a, b : Type} ->
  BinTreeFM atom (a -> b) -> BinTreeFM atom a -> BinTreeFM atom b
binTreeFMapp {atom} {a} {b} =
  binTreeFMEval {atom} {v=(a -> b)} {a=(BinTreeFM atom a -> BinTreeFM atom b)}
    binTreeFMmap
    btApplyHom

public export
Applicative (BinTreeFM atom) where
  pure = binTreeFMpure
  (<*>) = binTreeFMapp

public export
Monad (BinTreeFM atom) where
  (>>=) = flip binTreeFMBind

public export
binTreeFMunit : {0 atom : Type} ->
  NaturalTransformation Prelude.id (BinTreeFM atom)
binTreeFMunit {atom} a = InBTv {atom} {a}

public export
binTreeFMmul : {0 atom : Type} ->
  NaturalTransformation (BinTreeFM atom . BinTreeFM atom) (BinTreeFM atom)
binTreeFMmul {atom} a = binTreeFMjoin {atom} {a}

public export
BinTreeAlgToFree : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeFMAlg atom a
BinTreeAlgToFree = binTreeFMEvalMon

public export
BinTreeAlgFromFree : {0 atom, a : Type} ->
  BinTreeFMAlg atom a -> BinTreeAlg atom a
BinTreeAlgFromFree {atom} {a} =
  (|>) (InBTc {atom} {a} . mapSnd {f=Either} (mapHom InBTv))

-- Like `binTreeFMapp` but with a monoid on the output factored out.
-- Should have the same input-output behavior as, but perhaps building
-- smaller intermediate structures than:
--  (|>) (binTreeFMEvalMon {a}) . ((|>) . binTreeFMapp {a=v} {b=a})
public export
binTreeFMappMon : {0 atom, v, a : Type} ->
  BinTreeFM atom (v -> a) -> BinTreeAlg atom a -> BinTreeFM atom v -> a
binTreeFMappMon {atom} {v} {a} pat alg =
  binTreeFMEval {atom} {v} {a}
    (binTreeFMEvalMon {atom} {a=(v -> a)} ((.) alg . btApplyPure) pat) alg

-- Like `binTreeFMappMon` but making explicit use of the output being
-- another binary tree.
public export
binTreeFMappMonTree : {0 atom, v, a : Type} ->
  BinTreeFM atom (v -> BinTreeFM atom a) -> BinTreeFM atom v -> BinTreeFM atom a
binTreeFMappMonTree {atom} {v} {a} =
  binTreeFMEval {atom}
    {v=(v -> BinTreeFM atom a)} {a=(BinTreeFM atom v -> BinTreeFM atom a)}
    (binTreeFMBind {atom} {a=v} {b=a})
    (btApplyHom {atom} {a=v} {b=a})

-- Performs more substitutions than `binTreeFMappMonTree` on the fly by
-- composition in the metalanguage.
public export
binTreeFMsubstTree : {0 atom, v : Type} ->
  BinTreeFM atom (v -> BinTreeFM atom v) -> BinTreeFM atom v -> BinTreeFM atom v
binTreeFMsubstTree {atom} {v} =
  binTreeFMEval {atom}
    {v=(v -> BinTreeFM atom v)} {a=(BinTreeFM atom v -> BinTreeFM atom v)}
    (binTreeFMBind {a=v} {b=v})
    (eitherElim (const . InBTa) (uncurry (|>)))

---------------------------------------------------
---------------------------------------------------
---- Partial interpretations as `Maybe`-slices ----
---------------------------------------------------
---------------------------------------------------

-- For a given object `a`, a category-theory-style slice object over `Maybe a`
-- maybe viewed as an object together with an interpretation of that object
-- as a representation of `a`, which may be partial both in the sense that
-- the object may have more structure than is determined solely by its
-- representing `a` and in the sense that it might represent only part of the
-- structure of `a`.
--
-- One specific application of this is that if we imagine that `a` is a type
-- whose terms some interface knows how to interpret, then given a slice
-- `(b : Type ** f : b -> Maybe a)` over `Maybe a`, we could build an
-- interpretation of some type of structure containing terms of `b` which knows
-- how to interpret a given structure of that type whenever all the terms
-- of `b` contained in that structure have interpretations as `Just a` under
-- `f`.
public export
MaybeCS : Type -> Type
MaybeCS = CSliceObj . Maybe

----------------------------------------------
----------------------------------------------
---- Typechecked terms as `Either`-slices ----
----------------------------------------------
----------------------------------------------

-- For given objects `a` and `b`, a category-theory-style slice object over
-- `Either a b` maybe viewed as an object with a type `b` whose typechecking
-- might fail with an error from `a`.
--
-- `Either Void b` is isomorphic to `b`; `Either Unit b` is isomorphic to
-- `Maybe b`.
public export
EitherCS : Type -> Type -> Type
EitherCS = CSliceObj .* Either

---------------------------------------
---------------------------------------
---- Binary trees as S-expressions ----
---------------------------------------
---------------------------------------

--------------------------------------------------------
---- Binary trees as "atom-or-pair"-style S-expressions
--------------------------------------------------------

-- We can distinguish "pair of binary trees" as a polynomial-fixed-point
-- type of its own by defining the notion together with that of "binary tree"
-- itself with a _dependent_ polynomial endofunctor on the slice category of
-- `Type` over `2`, of which we treat one term as "binary tree" and the other
-- as "pair of binary trees".
--
-- Another view is to use the equivalence between the slice category of `Type`
-- over `2` and the product category `Type x Type`.

public export
BTSexp1 : Type -> Type -> Type
BTSexp1 = Either

public export
BTSexp2 : Type -> Type
BTSexp2 = ProductMonad

public export
BTSexpF : Type -> (Type, Type) -> (Type, Type)
BTSexpF atom (x, p) = (BTSexp1 atom p, BTSexp2 x)

-- Using this equivalence, we can write a binary tree algebra in terms of
-- a slice algebra.  This definition of a "BTSexp" algebra is another way
-- of writing a morphism in the slice category of `Type` over `2`.
--
-- What this allows as an expressive (not logical) extension to the notion
-- of a binary-tree algebra is a catamorphism that returns different types
-- for induction on expressions and pairs.
public export
BTSexpAlg : Type -> Type -> Type -> Type
BTSexpAlg atom x p = (BTSexp1 atom p -> x, BTSexp2 x -> p)

public export
BTSexpAlgToBTAlg : {0 atom, x, p : Type} ->
  BTSexpAlg atom x p -> BinTreeAlg atom x
BTSexpAlgToBTAlg {atom} {x} {p} (xalg, palg) (Left ea) =
  xalg $ Left ea
BTSexpAlgToBTAlg {atom} {x} {p} (xalg, palg) (Right ep) =
  xalg $ Right $ palg ep

public export
btSexpCata : {0 atom, x, p : Type} ->
  BTSexpAlg atom x p -> BinTreeMu atom -> x
btSexpCata {atom} {x} {p} = binTreeCata . BTSexpAlgToBTAlg

public export
btPairCata : {0 atom, x, p : Type} ->
  BTSexpAlg atom x p -> BinTreeMu atom -> BinTreeMu atom -> p
btPairCata {atom} {x} {p} alg bt bt' =
  snd alg (btSexpCata alg bt, btSexpCata alg bt')

------------------------------------
---- S-exp as `atom` or `tuple` ----
------------------------------------

-- Another equivalent way we can view binary trees is "either an atom or
-- a tuple of at least two expressions".  As with the "atom-or-pair" view,
-- we can express this as a dependent-polynomial-functor algebra.
-- We call this a `Texp` for "tuple-expression".

public export
BTTexp1 : Type -> Type -> Type
BTTexp1 = Either

public export
BTTexp2 : Type -> Type
BTTexp2 x = (n : Nat ** Vect (S (S n)) x)

public export
BTTexpF : Type -> (Type, Type) -> (Type, Type)
BTTexpF atom (x, t) = (BTTexp1 atom t, BTTexp2 x)

public export
BTTexpAlg : Type -> Type -> Type -> Type
BTTexpAlg atom x t = (BTTexp1 atom t -> x, BTTexp2 x -> t)

mutual
  public export
  btTexpCata : {0 atom, x, t : Type} ->
    BTTexpAlg atom x t -> BinTreeMu atom -> x
  btTexpCata (xalg, talg) (InBTm (Left ea)) = xalg $ Left ea
  btTexpCata (xalg, talg) (InBTm (Right (bt, bt'))) =
    let
      x = btTexpCata (xalg, talg) bt
      (n ** xs) = btTexpCataToVec (xalg, talg) bt'
    in
    xalg $ Right $ talg (n ** x :: xs)

  public export
  btTexpCataToVec : {0 atom, x, t : Type} ->
    BTTexpAlg atom x t -> BinTreeMu atom -> (n : Nat ** Vect (S n) x)
  btTexpCataToVec (xalg, talg) (InBTm (Left ea)) = (0 ** [xalg $ Left ea])
  btTexpCataToVec (xalg, talg) (InBTm (Right (bt, bt'))) =
    let
      x = btTexpCata (xalg, talg) bt
      (n ** xs) = btTexpCataToVec (xalg, talg) bt'
    in
    (S n ** x :: xs)

public export
btTupleMapCata : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> (n : Nat) -> Vect (S (S n)) (BinTreeMu atom) ->
  Vect (S (S n)) x
btTupleMapCata alg 0 [x, x'] =
  [btTexpCata alg x, btTexpCata alg x']
btTupleMapCata alg (S n) (x :: xs) =
  btTexpCata alg x :: btTupleMapCata alg n xs

public export
btTupleCata : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> (n : Nat) -> Vect (S (S n)) (BinTreeMu atom) -> t
btTupleCata (xalg, talg) n xs = talg (n ** btTupleMapCata (xalg, talg) n xs)

-------------------
---- Utilities ----
-------------------

public export
BtTexpShowAlg : {0 atom : Type} ->
  (atom -> String) -> BTTexpAlg atom String String
BtTexpShowAlg sha =
  (eitherElim sha id, \(n ** sv) => "[" ++ unwords (toList sv) ++ "]")

-- Show a binary tree as a tuple-expression.
public export
btTexpShow : {0 atom : Type} -> (atom -> String) -> BinTreeMu atom -> String
btTexpShow = btTexpCata . BtTexpShowAlg

-- Show a binary tree as a tuple-expression.
public export
btTexpShowI : {0 atom : Type} -> Show atom => BinTreeMu atom -> String
btTexpShowI {atom} = btTexpShow show

-----------------------------------------
-----------------------------------------
---- Either algebras of binary trees ----
-----------------------------------------
-----------------------------------------

public export
HomEither : Type -> Type -> Type
HomEither a e = a -> Either e a

public export
heMap : {0 a, e, e' : Type} -> (e -> e') -> HomEither a e -> HomEither a e'
heMap = (.) . mapFst {f=Either}

public export
Functor (HomEither a) where
  map = heMap

public export
hePure : {0 a, e : Type} -> e -> HomEither a e
hePure {a} {e} = const . Left

public export
EitherHom : Type -> Type -> Type
EitherHom = flip HomEither

public export
ehPure : {0 e, a : Type} -> a -> EitherHom e a
ehPure {a} {e} = const . Right

public export
ehBindHom : {0 e, a : Type} ->
  EitherHom e a -> (a -> EitherHom e a) -> EitherHom e a
ehBindHom {e} {a} = flip $ biapp (eitherElim Left)

public export
BinTreeBindAlg :
  {0 m : Type -> Type} -> {0 atom, a : Type} ->
  (alg : atom -> a -> m a) -> (bind : m a -> (a -> m a) -> m a) ->
  BinTreeAlg atom (a -> m a)
BinTreeBindAlg {m} alg bind (Left x) ea = alg x ea
BinTreeBindAlg {m} alg bind (Right (bt, bt')) ea = bind (bt ea) bt'

public export
BinTreeMonadAlg :
  {0 m : Type -> Type} -> {isMonad : Monad m} -> {0 atom, a : Type} ->
  (atom -> a -> m a) -> BinTreeAlg atom (a -> m a)
BinTreeMonadAlg {m} {isMonad} alg = BinTreeBindAlg {m} alg (>>=)

-------------------------------------------------------------
-------------------------------------------------------------
---- Unrefined finitary polynomial types as binary trees ----
-------------------------------------------------------------
-------------------------------------------------------------

-- The simplest form of finitary polynomial types is just a finite
-- set of constructors each of which has a finite set of arguments (of
-- the type itself).  A finite type is a type whose argument sets are
-- all empty (zero-size).
public export
record FPFunctor where
  constructor FPF
  fpfNpos : Nat
  fpfNdir : Vect fpfNpos Nat

public export
FPFatom : FPFunctor -> Type
FPFatom = Fin . fpfNpos

public export
FPFbt : FPFunctor -> Type
FPFbt = BinTreeMu . FPFatom

public export
FPFpred : FPFunctor -> Type
FPFpred = DecPred . FPFbt

-- If the context is `Nothing`, we expect not to find anything --
-- we should have been a term at the end of a tuple.  Thus we _always_
-- fail if we check a term with a context of `Nothing`.
--
-- If the context is `Just 0`, we expect to find a constructor, and
-- we return the number of arguments that constructor expects.
--
-- If the context is `Just (S n)`, we expect a tuple of `S n` terms.
-- There are no tuples with 0 terms.  A tuple of 1 term is a term.
-- A tuple of `S (S n))` terms is a pair of a term and a tuple of `S n` terms.
--
-- A term (which is also a tuple of 1 term) is either an atom
-- representing a constructor with no parameters, or a pair of an atom
-- representing a constructor with `S n` parameters together with a
-- tuple of `S n` terms.
public export
CheckFPFctx : FPFunctor -> Type
CheckFPFctx fpf = Maybe Nat

public export
initFPFctx : (fpf : FPFunctor) -> CheckFPFctx fpf
initFPFctx fpf = Just 1

public export
CheckFPFAlg : (fpf : FPFunctor) ->
  BinTreeAlg (FPFatom fpf) (CheckFPFctx fpf -> Maybe (CheckFPFctx fpf))
CheckFPFAlg _ _ Nothing =
  -- We did not expect to find any term paired with the most recent
  -- one that we checked, but we have found one.
  Nothing
CheckFPFAlg fpf (Left c) (Just 0) =
  -- We expected to find a constructor, and we have found one, so we return
  -- the number of arguments that we expect to find paired with it.
  Just $ Just $ index c (fpfNdir fpf)
CheckFPFAlg fpf (Right (_, _)) (Just 0) =
  -- We expected to find a constructor, but we found a pair, so we fail.
  Nothing
CheckFPFAlg fpf (Left ea) (Just (S 0)) =
  -- We expected to find a single term, and we have found a lone constructor.
  -- A lone constructor is a valid (single) term if and only if it has no
  -- parameters.  So if this term is a lone constructor, we succeed, but
  -- return a context of `Nothing`, because we expect a constructor with no
  -- parameters to not be paired with anything.
  case (index ea (fpfNdir fpf)) of
    0 => Just Nothing
    (S _) => Nothing
CheckFPFAlg fpf (Left _) (Just (S (S n))) =
  -- We expected to find a tuple of at least two terms, but we found
  -- a lone constructor, which at most can be a single term, so we fail.
  Nothing
CheckFPFAlg fpf (Right (bt, bt')) (Just (S 0)) =
  -- We expected to find a single term, and we have found a pair of terms.
  -- A pair of terms is a single term if and only if the left term is
  -- a constructor and the right term is a tuple of terms with the number
  -- of arguments that the constructor expects.
  case bt (Just 0) of
    Just Nothing =>
      -- Checking the left tree as a constructor succeeded, but we
      -- expected no further terms.  This case is actually impossible
      -- given the way the rest of the algebra is written.
      Nothing
    Just (Just 0) =>
      -- Checking the left tree as a constructor succeeded, but we
      -- expected no further terms, and we have found at least one.
      Nothing
    Just (Just (S n)) =>
      -- Checking the left tree as a constructor succeeded, and that
      -- particular constructor expects to be paired with `S n` terms.
      bt' $ Just $ S n
    Nothing =>
      -- Checking the left tree as a constructor failed.
      Nothing
CheckFPFAlg fpf (Right (bt, bt')) (Just (S (S n))) =
  -- We expected to find a tuple of `S (S n))` terms.  That means
  -- that we expected to find a pair of a term with a tuple of `S n` terms.
  case bt (Just (S 0)) of
    Just Nothing =>
      -- Checking the left tree as a term succeeded, and we
      -- expected no further terms.  That is the expected
      -- result for the left tree, since we are expecting a
      -- list of terms, so now we check the right tree.
      bt' (Just (S n))
    Just (Just _) =>
      -- This case is actually impossible given the way the rest of
      -- the algebra is written -- a term never expects further terms;
      -- only a constructor does.
      Nothing
    Nothing =>
      -- Checking the left tree as a term failed.
      Nothing

public export
checkFPF : (fpf : FPFunctor) -> FPFpred fpf
checkFPF fpf x = case
  (binTreeCata
    {atom=(FPFatom fpf)}
    {a=(CheckFPFctx fpf -> Maybe (CheckFPFctx fpf))}
    (CheckFPFAlg fpf)
    x
    (initFPFctx fpf)) of
      Just Nothing =>
        -- We returned successes to all steps of checking the algebra, and
        -- we expect no further terms precisely when we found no further
        -- terms, so the check has passed.
        True
      Just (Just _) =>
        -- We returned successes to all steps of checking the algebra, but
        -- we expected further terms and have not found any, so the check
        -- has failed.
        False
      Nothing =>
        -- One of the steps of checking the algebra failed.
        False

------------------------------------------------
------------------------------------------------
------------------------------------------------
---- Polynomial binary-tree-dependent types ----
------------------------------------------------
------------------------------------------------

public export
record BTMPolyDep (atom : Type) where
  constructor BTMPD
  btmPosCtor : Type
  btmPosParam : SliceObj btmPosCtor
  btmPosCod : Pi {a=btmPosCtor} $ BinTreeFM atom . btmPosParam
  btmDir : SliceObj btmPosCtor
  btmDirDom : SliceMorphism {a=btmPosCtor} btmDir (BinTreeFM atom . btmPosParam)

public export
btmpdPos : {atom : Type} -> BTMPolyDep atom -> SliceObj (BinTreeMu atom)
btmpdPos {atom} btmpd bt =
  (c : btmPosCtor btmpd **
   p : btmPosParam btmpd c -> BinTreeMu atom **
   Equal (btFullSubst p (btmPosCod btmpd c)) bt)

public export
btmpdDir : {atom : Type} -> (btmpd : BTMPolyDep atom) ->
  SliceObj (Sigma {a=(BinTreeMu atom)} $ btmpdPos {atom} btmpd)
btmpdDir {atom} btmpd pos = btmDir btmpd (fst (snd pos))

public export
btmpdAssign : {atom : Type} -> (btmpd : BTMPolyDep atom) ->
  (Sigma {a=(Sigma {a=(BinTreeMu atom)} $ btmpdPos {atom} btmpd)} $
    btmpdDir {atom} btmpd) ->
  BinTreeMu atom
btmpdAssign {atom} btmpd posdir =
  btFullSubst
    (fst $ snd $ snd $ fst posdir)
    (btmDirDom btmpd (fst $ snd $ fst posdir) $ snd posdir)

public export
btmpdToSPF : {atom : Type} ->
  BTMPolyDep atom -> SlicePolyFunc (BinTreeMu atom) (BinTreeMu atom)
btmpdToSPF {atom} btmpd =
  (btmpdPos {atom} btmpd **
   btmpdDir {atom} btmpd **
   btmpdAssign {atom} btmpd)

public export
InterpBTMPolyDep : {atom : Type} ->
  BTMPolyDep atom -> SliceEndofunctor (BinTreeMu atom)
InterpBTMPolyDep = InterpSPFunc . btmpdToSPF

public export
BinTreeDepFM : {atom : Type} ->
  BTMPolyDep atom -> SliceEndofunctor (BinTreeMu atom)
BinTreeDepFM = SlicePolyFree . btmpdToSPF

public export
BinTreeDepMu : {atom : Type} -> BTMPolyDep atom -> SliceObj (BinTreeMu atom)
BinTreeDepMu = SPFMu . btmpdToSPF

public export
binTreeDepEval : {atom : Type} -> (btmpd : BTMPolyDep atom) ->
  SPFMeval {a=(BinTreeMu atom)} (btmpdToSPF {atom} btmpd)
binTreeDepEval btmpd = spfmEval (btmpdToSPF btmpd)

-------------------------------------
---- Binary-tree-dependent types ----
-------------------------------------

public export
BinTreeF1 : Type -> IndIndF1
BinTreeF1 = (|>) pfPos . BinTreeF

public export
BinTreeIndIndAlg : Type -> IndIndF1
BinTreeIndIndAlg = IndIndAlg . BinTreeF1

public export
BinTreeF2 : Type -> Type
BinTreeF2 = IndIndF2 . BinTreeF1

public export
BinTreeIndInd : {atom : Type} -> BinTreeF2 atom -> IndInd
BinTreeIndInd {atom} f2 = (BinTreeF1 atom ** f2)

public export
BinTreeFreeM1 : Type -> PolyFunc -> Type
BinTreeFreeM1 = (|>) pfPos . BinTreeFM

public export
partial
data BinTreeFreeM2 : {0 atom : Type} -> (f2 : BinTreeF2 atom) ->
    (p : PolyFunc) -> BinTreeFreeM1 atom p -> Type where
  InBT2v : {0 atom : Type} -> {0 f2 : BinTreeF2 atom} -> {0 p : PolyFunc} ->
    (i : pfPos p) -> pfDir {p} i ->
    BinTreeFreeM2 {atom} f2 p (InBTv i)
  InBT2c : {0 atom : Type} -> {0 f2 : BinTreeF2 atom} -> {0 p : PolyFunc} ->
    (i1 : BinTreeF atom (BinTreeFreeM1 atom p)) ->
    f2 (BinTreeFreeM1 atom p ** BinTreeFreeM2 {atom} f2 p)
      InBTc i1 ->
    BinTreeFreeM2 {atom} f2 p (InBTc i1)

public export
BinTreeFreeIndIndM : {atom : Type} -> BinTreeF2 atom -> PolyFunc -> PolyFunc
BinTreeFreeIndIndM {atom} f2 p =
  (BinTreeFreeM1 atom p ** BinTreeFreeM2 {atom} f2 p)

public export
BinTreeF2' : Type -> Type
BinTreeF2' atom = (a : Type) -> (p : a -> Type) ->
  BinTreeAlg atom a -> BinTreeF atom a -> Type

public export
partial
data BinTreeFreeM2' : {0 atom : Type} -> (f2 : BinTreeF2' atom) ->
    {0 atom' : Type} -> (p : atom' -> Type) ->
    BinTreeFM atom atom' -> Type where
  InBT2v' : {0 atom, atom' : Type} ->
    {0 f2 : BinTreeF2' atom} -> {0 p : atom' -> Type} ->
    (i : atom') -> p i ->
    BinTreeFreeM2' {atom} {atom'} f2 p (InBTv i)
  InBT2c' : {0 atom, atom' : Type} ->
    {0 f2 : BinTreeF2' atom} -> {0 p : atom' -> Type} ->
    (i1 : BinTreeF atom (BinTreeFM atom atom')) ->
    f2 (BinTreeFM atom atom') (BinTreeFreeM2' {atom} f2 {atom'} p)
      InBTc i1 ->
    BinTreeFreeM2' {atom} {atom'} f2 p (InBTc i1)

public export
record PolyBTDep (atom : Type) where
  constructor PBTD
  pbtdPos : Type
  pbtdDir1 : pbtdPos -> Type
  pbtdDir2 : pbtdPos -> Type
  pbtdAssign : SliceMorphism {a=pbtdPos} pbtdDir2 (BinTreeFM atom . pbtdDir1)
  pbtdCod : Pi {a=pbtdPos} $ BinTreeFM atom . pbtdDir1

public export
data BinTreeFreeM2'' : {0 atom : Type} -> (f2 : PolyBTDep atom) ->
    {0 atom' : Type} -> (p : atom' -> Type) ->
    SliceObj (BinTreeFM atom atom') where
  InBTF2v : {0 atom : Type} -> {0 f2 : PolyBTDep atom} ->
    {0 atom' : Type} -> {0 p : atom' -> Type} ->
    (i : atom') -> p i ->
    BinTreeFreeM2'' {atom} f2 {atom'} p (InBTv i)
  InBTF2c : {0 atom : Type} -> {0 f2 : PolyBTDep atom} ->
    {0 atom' : Type} -> {0 p : atom' -> Type} ->
    (i : pbtdPos f2) ->
    (d1 : pbtdDir1 f2 i -> BinTreeFM atom atom') ->
    ((d2 : pbtdDir2 f2 i) -> BinTreeFreeM2'' {atom} f2 {atom'} p $
      binTreeFMBind d1 $ pbtdAssign f2 i d2) ->
    BinTreeFreeM2'' {atom} f2 {atom'} p $ binTreeFMBind d1 $ pbtdCod f2 i

--------------------------------------
---- Correctness of equality test ----
--------------------------------------

public export
binTreeEqCorrect : {0 atom : Type} -> (deq : DecEqPred atom) ->
  (x, x' : BinTreeMu atom) -> IsTrue (binTreeEq deq x x') -> x = x'
binTreeEqCorrect deq x x' eq = ?binTreeEqCorrect_hole

public export
binTreeNeqCorrect : {0 atom : Type} -> (deq : DecEqPred atom) ->
  (x, x' : BinTreeMu atom) -> IsFalse (binTreeEq deq x x') -> Not (x = x')
binTreeNeqCorrect deq x x' neq = ?binTreeNeqCorrect_hole

public export
binTreeDecEq : {0 atom : Type} -> DecEqPred atom -> DecEqPred (BinTreeMu atom)
binTreeDecEq deq x x' with (binTreeEq deq x x') proof prf
  binTreeDecEq deq x x' | True = Yes $ binTreeEqCorrect deq x x' prf
  binTreeDecEq deq x x' | False = No $ binTreeNeqCorrect deq x x' prf

public export
DecEq atom => DecEq (BinTreeMu atom) where
  decEq = binTreeDecEq decEq

------------------------------------------------
------------------------------------------------
---- Finitary dependent polynomial functors ----
------------------------------------------------
------------------------------------------------

FinSliceProdS : Type
FinSliceProdS = List Nat

0 FinProdBounded : Nat -> SliceObj FinSliceProdS
FinProdBounded n = All (GT n)

0 IsFinProdBounded :
  (n : Nat) -> DecSlice {a=FinSliceProdS} (FinProdBounded n)
IsFinProdBounded n = all (isGT n)

0 isFinProdBounded : (n : Nat) -> DecPred FinSliceProdS
isFinProdBounded n = SliceDecPred $ IsFinProdBounded n

FinSliceProd : Nat -> Type
FinSliceProd n = Refinement {a=FinSliceProdS} (isFinProdBounded n)

InterpFSPP : {n : Nat} -> (p : FinSliceProdS) -> (0 _ : FinProdBounded n p) ->
  SliceObj (Fin n) -> Type
InterpFSPP {n} [] i sl = Unit
InterpFSPP {n=Z} (_ :: _) (gt :: _) sl = void $ succNotLTEzero gt
InterpFSPP {n=(S n)} (k :: ks) (_ :: gt) sl =
  (sl $ natToFinLT k, InterpFSPP {n=(S n)} ks gt sl)

InterpFSP : {n : Nat} -> FinSliceProd n -> SliceObj (Fin n) -> Type
InterpFSP {n} p = InterpFSPP {n} (fst0 p) (fromIsYes $ snd0 p)

FinMatrixS : Type
FinMatrixS = List FinSliceProdS

0 FinMatrixBounded : Nat -> SliceObj FinMatrixS
FinMatrixBounded n = All (FinProdBounded n)

0 IsFinMatrixBounded :
  (n : Nat) -> DecSlice {a=FinMatrixS} (FinMatrixBounded n)
IsFinMatrixBounded n = all (IsFinProdBounded n)

0 isFinMatrixBounded : (n : Nat) -> DecPred FinMatrixS
isFinMatrixBounded n = SliceDecPred $ IsFinMatrixBounded n

FinMatrix : Nat -> Type
FinMatrix n = Refinement {a=FinMatrixS} (isFinMatrixBounded n)

InterpFSMP : {n : Nat} -> (p : FinMatrixS) -> (0 _ : FinMatrixBounded n p) ->
  SliceObj (Fin n) -> Type
InterpFSMP {n} ps bounded sl =
  Subset0 (Nat, List Nat) $
    \(i, p) =>
      (b : LT i (length ps) **
       InterpFSP {n} (Element0 (index' ps $ natToFinLT i) $
        ?InterpFSMP_hole_pred $ indexAll ?InterpFSMP_hole_elem bounded) sl)

InterpFSM : {n : Nat} ->
  (sl : FinMatrix n) -> SliceObj (Fin n) -> Type
InterpFSM {n} sl = InterpFSMP {n} (fst0 sl) (fromIsYes $ snd0 sl)

----------------------------------------
----------------------------------------
---- Finite directed acyclic graphs ----
----------------------------------------
----------------------------------------

public export
FinTopoSort : SliceObj FSObj
FinTopoSort n = Vect n FSObj

public export
record TopoSortedFin where
  constructor TSFin
  tsfVert : FSObj
  tsfSort : FinTopoSort tsfVert

public export
TSFVert : TopoSortedFin -> Type
TSFVert = FSElem . tsfVert

public export
0 tsfOrd : (0 tsf : TopoSortedFin) -> (0 _ : TSFVert tsf) -> FSObj
tsfOrd tsf v = Vect.index v (tsfSort tsf)

public export
0 TSFlt : (0 tsf : TopoSortedFin) -> (0 _, _ : TSFVert tsf) -> Type
TSFlt tsf v v' = LT (tsfOrd tsf v) (tsfOrd tsf v')

-- An edge incoming to the given vertex of a topologically sorted finite graph.
public export
record DAGincE (tsf : TopoSortedFin) (tgt : TSFVert tsf) where
  constructor DAGie
  diSrc : TSFVert tsf
  0 diLT : TSFlt tsf diSrc tgt

public export
record DAGedge (tsf : TopoSortedFin) where
  constructor DAGe
  deTgt : TSFVert tsf
  deEdge : DAGincE tsf deTgt

-- A set of edges incoming to the given vertex of a topologically sorted
-- finite graph.
public export
record DAGincSet (tsf : TopoSortedFin) (tgt : TSFVert tsf) where
  constructor DAGis
  disE : List $ DAGincE tsf tgt

public export
DAGieTV : (tsf : TopoSortedFin) -> Vect (tsfVert tsf) Type
DAGieTV tsf = finFToVect $ DAGincSet tsf

public export
DAGedgeSet : TopoSortedFin -> Type
DAGedgeSet tsf = HVect {k=(tsfVert tsf)} (DAGieTV tsf)

public export
record FinDAG where
  constructor FDAG
  fdagVert : TopoSortedFin
  fdagEdge : DAGedgeSet fdagVert

-----------------------------------
-----------------------------------
---- Parameterizations of DAGs ----
-----------------------------------
-----------------------------------

mutual
  public export
  record TSFParam (tssf : TopoSortedFin) where
    constructor TSFP
    -- tsfpV : HVect {k=(tsfVert tsf)} TFSParam_hole

  public export
  data TSFVertParam : (tsf : TopoSortedFin) -> TSFParam tsf -> Type where

------------------------------
------------------------------
---- List-dependent types ----
------------------------------
------------------------------

public export
partial
data ListIndInd2 : {atom : Type} -> ListF2 atom ->
    (pos : Type) -> (pos -> Type) -> FreeList atom pos -> Type where
  LI2v : {0 atom : Type} -> {0 f2 : ListF2 atom} ->
    {0 pos : Type} -> {0 dir : pos -> Type} ->
    (i : pos) -> dir i ->
    ListIndInd2 {atom} f2 pos dir (IdrisCategories.inFV i)
  LI2c : {0 atom : Type} -> {0 f2 : ListF2 atom} ->
    {0 pos : Type} -> {0 dir : pos -> Type} ->
    (i1 : ListF1 atom $ FreeList atom pos) ->
    f2 (FreeList atom pos) (ListIndInd2 f2 pos dir) IdrisCategories.inFC i1 ->
    ListIndInd2 {atom} f2 pos dir (IdrisCategories.inFC i1)

public export
AListF : Type -> Type -> Type
AListF = Either () .* Pair

public export
AListAlg : Type -> Type -> Type
AListAlg atom x = AListF atom x -> x

public export
AListTypeAlg : Type -> Type
AListTypeAlg atom = AListAlg atom Type

public export
MuAList : Type -> Type
MuAList = Mu . AListF

public export
cataAListF : {0 atom : Type} -> FreeFEval $ AListF atom
cataAListF v a subst alg (InFree x) = case x of
  TFV var => subst var
  TFC l => alg $ case l of
    Left () => Left ()
    Right (MkPair x l') => Right $ MkPair x $ cataAListF v a subst alg l'

public export
AListMuSlice : Type -> Type
AListMuSlice = SliceObj . MuAList

public export
AListTypeMuSlice : {0 atom : Type} -> AListTypeAlg atom -> AListMuSlice atom
AListTypeMuSlice {atom} = cataAListF {atom} Void Type (voidF Type)

public export
AListMuPiAlg : {atom : Type} -> AListTypeAlg atom -> Type
AListMuPiAlg = ?AListMuPiAlg_hole

public export
alistMuPi' : {atom : Type} -> (tyalg : AListTypeAlg atom) ->
  (() -> tyalg (Left ())) ->
  ((x : atom) -> (ty : Type) -> ty -> tyalg (Right $ MkPair x ty)) ->
  Pi {a=(MuAList atom)} $ AListTypeMuSlice {atom} tyalg
alistMuPi' {atom} tyalg nalg calg (InFree (TFV v)) = void v
alistMuPi' {atom} tyalg nalg calg (InFree (TFC l)) = case l of
  Left () => nalg ()
  Right (MkPair x l') =>
    calg x (AListTypeMuSlice tyalg l') $ alistMuPi' tyalg nalg calg l'

public export
listMuPi' : {atom : Type} -> (tyalg : ListTypeAlg atom) ->
  tyalg NilF ->
  ((x : atom) -> (ty : Type) -> ty -> tyalg (ConsF x ty)) ->
  Pi {a=(MuList atom)} $ ListTypeMuSlice {atom} tyalg
listMuPi' {atom} tyalg nalg calg (InFree (TFV v)) = void v
listMuPi' {atom} tyalg nalg calg (InFree (TFC l)) = case l of
  NilF => nalg
  ConsF x l' =>
    calg x (ListTypeMuSlice tyalg l') $ listMuPi' tyalg nalg calg l'

public export
listMuSliceCata' : {atom : Type} -> (dom, cod : ListTypeAlg atom) ->
  SliceMorphism {a=(MuList atom)} (ListTypeMuSlice dom) (ListTypeMuSlice cod)
listMuSliceCata' {atom} dom cod = ?listMuSliceCata'_hole

--------------------------
--------------------------
---- Matrix interface ----
--------------------------
--------------------------

-- Bounded natural numbers used as list indexes.
public export
ListNI : {0 a : Type} -> List a -> Type
ListNI {a} = Fin . length {a}

-- For any type `a`, given a functor assigning types to terms of `a`,
-- produce a functor assigning types to terms of type `Coproduct (List a)`.
--
-- A functor assigning types to terms of a type `a` may be viewed as an
-- object of the slice category of `Type` over `a`.  Consequently, this
-- assignment itself may be viewed as a natural transformation between functors
-- from `Type` to the two-category of slice categories of `Type`.
public export
CoproductT : NaturalTransformation SliceObj (SliceObj . List)
CoproductT a ta l = Sigma {a=(ListNI l)} (ta . index' {a} l)

public export
showCoprod : {0 a : Type} -> {0 p : a -> Type} -> {l : List a} ->
  ((x : a) -> p x -> String) -> Show (CoproductT a p l)
showCoprod {a} {p} {l} sh = shfc where
  sfp : {x : a} -> Show (p x)
  sfp {x} = shfp where
    [shfp] Show (p x) where
      show = sh x

  sfpi : {i : ListNI l} -> Show (p (index' l i))
  sfpi {i} = sfp {x=(index' l i)}

  [shfc] Show (CoproductT a p l) where
    show = showDP show $ \i => let _ = sfpi {i} in show

-- For any type `a`, given a functor assigning types to terms of `a`,
-- produce a functor assigning types to terms of type `Product (List a)`.
--
-- A functor assigning types to terms of a type `a` may be viewed as an
-- object of the slice category of `Type` over `a`.  Consequently, this
-- assignment itself may be viewed as a natural transformation between functors
-- from `Type` to the two-category of slice categories of `Type`.
public export
ProductT : NaturalTransformation SliceObj (SliceObj . List)
ProductT a ta = All {a} ta

public export
showAll : {0 a : Type} -> {0 p : a -> Type} -> ((x : a) -> p x -> String) ->
  (l : List a) -> All (Show . p) l
showAll {a} {p} sh [] = Nil
showAll {a} {p} sh (x :: l') = shf :: showAll sh l' where
  [shf] Show (p x) where
    show = sh x

public export
showProd : {0 a : Type} -> {0 p : a -> Type} -> {l : List a} ->
  ((x : a) -> p x -> String) -> Show (ProductT a p l)
showProd {a} {p} {l} sh = shfp where
  sfp : All p l -> String
  sfp = let _ : All (Show . p) l = showAll {a} {p} sh l in show

  [shfp] Show (All p l) where
    show = sfp

-- Functor which takes a type to a (two-dimensional) matrix of terms of
-- that type.
public export
MatrixF : Type -> Type
MatrixF = List . List

-- For any type `a`, given a functor assigning types to terms of `a`, produce
-- a functor assigning types to terms of type `MatrixF a`.
--
-- A functor assigning types to terms of a type `a` may be viewed as an
-- object of the slice category of `Type` over `a`.  Consequently, this
-- functor itself may be viewed as a natural transformation between functors
-- from `Type` to the two-category of slice categories of `Type`.
public export
MatrixT : NaturalTransformation SliceObj (SliceObj . MatrixF)
MatrixT = vcompNT (whiskerLeft CoproductT List) ProductT

public export
showMatrixT : {0 a : Type} -> {0 p : a -> Type} -> {m : MatrixF a} ->
  ((x : a) -> p x -> String) -> MatrixT a p m -> String
showMatrixT {m} shp = shm where
  sh : {n : ListNI m} -> Show (All p (index' m n))
  sh {n} = showProd {a} {p} {l=(index' m n)} shp

  [shdp] Show (DPair (ListNI m) (All p . index' m)) where
    show = showDP show $ \n => let _ = sh {n} in show

  shm : MatrixT a p m -> String
  shm = let _ = shdp in show

public export
NatMatrix : Type
NatMatrix = MatrixF Nat

-- Given a matrix of natural numbers, produce a type whose terms are
-- coproducts-of-products-of-`Fin n` (where the matrix determines the `n`s).
public export
FinMatrixT : NatMatrix -> Type
FinMatrixT = MatrixT Nat Fin

public export
showFinMatrixT : {m : NatMatrix} -> FinMatrixT m -> String
showFinMatrixT {m} = showMatrixT {a=Nat} {p=Fin} {m} (\_ => show)

public export
(m : NatMatrix) => Show (FinMatrixT m) where
  show {m} = showFinMatrixT {m}

public export
MkMaybeAllFin : List Nat -> (l : List Nat) -> Maybe (All Fin l)
MkMaybeAllFin ns [] = Just Nil
MkMaybeAllFin [] (_ :: _) = Nothing
MkMaybeAllFin (n :: ns) (k :: ks) = case (natToFin n k, MkMaybeAllFin ns ks) of
  (Just i, Just ks') => Just (i :: ks')
  _ => Nothing

public export
MkMaybeFinMatrixT : (m : NatMatrix) -> Nat -> List Nat -> Maybe (FinMatrixT m)
MkMaybeFinMatrixT m n l = case natToFin n (length m) of
  Just i => case MkMaybeAllFin l (index' m i) of
    Just l' => Just (i ** l')
    Nothing => Nothing
  Nothing => Nothing

public export
MkFinMatrixT : (m : NatMatrix) -> (n : Nat) -> (l : List Nat) ->
  {auto ok : IsJustTrue (MkMaybeFinMatrixT m n l)} -> FinMatrixT m
MkFinMatrixT m n l {ok} = fromIsJust ok

----------------------------------------
----------------------------------------
---- Finite directed acyclic graphs ----
----------------------------------------
----------------------------------------

-- A representation of a finite topologically-sorted set -- a list of
-- equivalence classes, each represented by its cardinality.
public export
FinTSort : Type
FinTSort = List Nat

-- A level of the given topological sort.
public export
FinTSLevel : FinTSort -> Type
FinTSLevel = ListNI {a=Nat}

-- A level other than the lowest of the given topological sort.
public export
FinTSInnerLevel : FinTSort -> Type
FinTSInnerLevel = Fin . pred . length

-- An inner (non-lowest) level of a topological sort viewed as an
-- unconstrained level.
public export
FinTSWeaken : SliceMorphism {a=FinTSort} FinTSInnerLevel FinTSLevel
FinTSWeaken [] lev = absurd lev
FinTSWeaken (_ :: _) lev = weaken lev

-- A node of a DAG at the given level of a topological sort.
public export
FinSortNode : (ts : FinTSort) -> FinTSLevel ts -> Type
FinSortNode ts lev = Fin $ index' ts lev

-- A node of a DAG at the given level, which is not the lowest, of the given
-- topological sort.
public export
FinSortInnerNode : (ts : FinTSort) -> FinTSInnerLevel ts -> Type
FinSortInnerNode ts = FinSortNode ts . FinTSWeaken ts

-- A node of a DAG whose representation uses the above representation of
-- a topological sort.
public export
FinDAGNode : FinTSort -> Type
FinDAGNode ts = Sigma {a=(FinTSLevel ts)} $ FinSortNode ts

-- A representation of an edge of a DAG, pointing from a lower-numbered level
-- to a higher-numbered level in the given topological sort.  The parameter
-- is the lower-numbered level.
public export
FinDAGEdge : (ts : FinTSort) -> FinTSInnerLevel ts -> Type
FinDAGEdge ts lev = ?FinDAGEdge_hole

-- A representation of a finite directed acyclic (multi)graph (DAG) -- a list of
-- edges each of which points from a lower-numbered level to a higher-numbered
-- level in the given topological sort.
public export
FinDAG' : FinTSort -> Type
FinDAG' = ?FinDAG_hole


----------------------------------------------------
----------------------------------------------------
---- Coproduct-of-product types (finitary ADTs) ----
----------------------------------------------------
----------------------------------------------------

-- A family of `n` finite ADTs.
public export
FinPCTfam : FSObj -> Type
FinPCTfam Z = Unit
FinPCTfam (S n) = List $ List $ Either Nat $ Fin n

-- A family of `n` potentially-infinite ADTs.
public export
PCTfam : FSObj -> Type
PCTfam n = Vect n $ List $ Fin n

public export
FSSlicePF : FSObj -> FSObj -> Type
FSSlicePF dom cod = Vect cod (List $ List $ Fin dom)

---------------------------------
---------------------------------
---- Terms of core Geb logic ----
---------------------------------
---------------------------------

-------------------
---- Structure ----
-------------------

mutual
  public export
  data GebCatTerm : Type where

  public export
  data GebObjTerm : Type where

  public export
  data GebMorphTerm : Type where

-------------------
---- Utilities ----
-------------------

mutual
  public export
  Show GebCatTerm where
    show _ impossible

  public export
  Show GebObjTerm where
    show _ impossible

  public export
  Show GebMorphTerm where
    show _ impossible

---------------------
---- Typechecker ----
---------------------

mutual
  public export
  0 checkGebCatTerm :
    GebCatTerm -> Bool
  checkGebCatTerm _ impossible

  public export
  0 checkGebObjTerm :
    GebCatTerm -> GebObjTerm -> Bool
  checkGebObjTerm _ impossible

  public export
  0 checkGebMorphTerm :
    GebCatTerm -> GebObjTerm -> GebObjTerm -> GebMorphTerm -> Bool
  checkGebMorphTerm _ impossible

-------------------------------------------------------
-------------------------------------------------------
---- Idris denotational semantics and verification ----
-------------------------------------------------------
-------------------------------------------------------

--------------------------------------
---- Typechecker self-consistency ----
--------------------------------------

mutual
  public export
  0 goSigConsis : (c : GebCatTerm) -> (o : GebObjTerm) ->
    IsTrue (checkGebObjTerm c o) -> IsTrue (checkGebCatTerm c)
  goSigConsis _ _ _ impossible

  public export
  0 gmSigConsisCat :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebMorphTerm c dom cod m) -> IsTrue (checkGebCatTerm c)
  gmSigConsisCat _ _ _ impossible

  public export
  0 gmSigConsisDom :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebMorphTerm c dom cod m) -> IsTrue (checkGebObjTerm c dom)
  gmSigConsisDom _ _ _ impossible

  public export
  0 gmSigConsisCod :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebMorphTerm c dom cod m) -> IsTrue (checkGebObjTerm c cod)
  gmSigConsisCod _ _ _ impossible

  public export
  0 gmSigConsisDomCod :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebObjTerm c dom) -> IsTrue (checkGebObjTerm c cod)
  gmSigConsisDomCod _ _ _ impossible

  public export
  0 gmSigConsisCodDom :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebObjTerm c cod) -> IsTrue (checkGebObjTerm c dom)
  gmSigConsisCodDom _ _ _ impossible

---------------------------
---- Typechecked terms ----
---------------------------

public export
GebCat : Type
GebCat = Refinement {a=GebCatTerm} checkGebCatTerm

public export
gcTerm : GebCat -> GebCatTerm
gcTerm = shape

public export
GebObjSigTerm : Type
GebObjSigTerm = (GebCatTerm, GebObjTerm)

public export
0 checkGebObjSigTerm : GebObjSigTerm -> Bool
checkGebObjSigTerm = uncurry checkGebObjTerm

public export
GebObj : Type
GebObj = Refinement {a=GebObjSigTerm} checkGebObjSigTerm

public export
goSigTerm : GebObj -> GebObjSigTerm
goSigTerm = shape

public export
goObjTerm : GebObj -> GebObjTerm
goObjTerm = snd . goSigTerm

public export
goCatTerm : GebObj -> GebCatTerm
goCatTerm = fst . goSigTerm

public export
GebMorphSigTerm : Type
GebMorphSigTerm = (GebCatTerm, GebObjTerm, GebObjTerm, GebMorphTerm)

public export
0 checkGebMorphSigTerm : GebMorphSigTerm -> Bool
checkGebMorphSigTerm (c, dom, cod, m) = checkGebMorphTerm c dom cod m

public export
GebMorph : Type
GebMorph = Refinement {a=GebMorphSigTerm} checkGebMorphSigTerm

public export
goCat : GebObj -> GebCat
goCat (Element0 (c, o) p) = Element0 c $ goSigConsis c o p

public export
gmCat : GebMorph -> GebCat
gmCat (Element0 (c, dom, cod, m) p) = Element0 c $ gmSigConsisCat c dom cod m p

public export
gmDom : GebMorph -> GebObj
gmDom (Element0 (c, dom, cod, m) p) =
  Element0 (c, dom) $ gmSigConsisDom c dom cod m p

public export
gmCod : GebMorph -> GebObj
gmCod (Element0 (c, dom, cod, m) p) =
  Element0 (c, cod) $ gmSigConsisCod c dom cod m p

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Idris evaluator (operational semantics) -- for some categories only ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
