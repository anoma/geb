module LanguageDef.BinTree

import Library.IdrisUtils
import Library.IdrisCategories
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

export prefix 11 $$!
public export
($$!) : {0 atom, ty : Type} -> atom -> BinTreeF atom ty
($$!) = Left

export infixr 10 $$>
public export
($$>) : {0 atom, ty : Type} -> (ty, ty) -> BinTreeF atom ty
($$>) = Right

export infixr 10 $$*
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

export prefix 11 $!
public export
($!) : {0 atom : Type} -> atom -> BinTreeMu atom
($!) = InBTm . ($$!)

export infixr 10 $>
public export
($>) : {0 atom : Type} -> ProdAlg (BinTreeMu atom)
($>) = InBTm . ($$>)

export infixr 10 $*
public export
($*) : {0 atom : Type} -> BinTreeMu atom -> BinTreeMu atom -> BinTreeMu atom
($*) = InBTm .* ($$*)

export prefix 11 $:
public export
($:) : {0 atom : Type} ->
  (l : List (BinTreeMu atom)) -> {auto 0 ne : NonEmpty l} -> BinTreeMu atom
($:) {atom} (x :: []) {ne=IsNonEmpty} = x
($:) {atom} (x :: xs@(x' :: xs')) {ne=IsNonEmpty} = x $* $: xs

export prefix 11 $:!
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

public export
btOpaqueCata : {a, b : Type} ->
  ((c, d : Type) -> (BinTreeCoalg a c, BinTreeAlg b d) -> (c -> d)) ->
  BinTreeMu a -> BinTreeMu b
btOpaqueCata {a} {b} alg = alg (BinTreeMu a) (BinTreeMu b) (outBTm, InBTm)

-- The (universal) catamorphism of `Mu[BinTreeF]` is also the universal "eval"
-- morphism for the free monad of the product monad (with a slight
-- rearrangement of parameters via `eitherElim`).  The eval morphism is the
-- right adjunct of the free/forgetful adjunction between the category of
-- F-algebras of `ProductMonad` and `Type`.
public export
prodFMEval : {0 v, a : Type} -> (v -> a) -> ProdAlg a -> ProdFM v -> a
prodFMEval = binTreeCata {atom=v} {a} .* eitherElim

-- The left adjunct of the free/forgetful adjunction between the category of
-- F-algebras of `ProductMonad` and `Type` (the right adjunct is `prodFMEval`).
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
prodFMfold : {0 elem, acc : Type} ->
  (elem -> acc -> acc) -> acc -> ProdFM elem -> acc
prodFMfold {elem} {acc} func =
  flip $ prodFMEval {a=(acc -> acc)} func (uncurry (|>))

public export
Foldable ProdFM where
  foldr = prodFMfold

public export
prodFMsequence : {0 f : Type -> Type} ->
  {func : Functor f} -> {app : Applicative f} ->
  {0 a : Type} -> ProdFM (f a) -> f (ProdFM a)
prodFMsequence {f} {func} {app} {a} =
  prodFMEval (map {f} prodFMpure) (map {f} ($>) . sequence {t=ProductMonad} {f})

public export
prodFMtraverse : {0 f : Type -> Type} ->
  {func : Functor f} -> {app : Applicative f} ->
  {0 a, b : Type} -> (a -> f b) -> ProdFM a -> f (ProdFM b)
prodFMtraverse {f} {func} {app} {a} {b} =
  (.) (prodFMsequence {f} {func} {app} {a=b}) . prodFMmap

public export
Traversable ProdFM where
  traverse {f} =
    prodFMtraverse
      {func=(MkFunctor $ map {f})}
      {app=(MkApplicative (pure {f}) ((<*>) {f}))}

public export
ProdAlgToFree : {0 a : Type} -> ProdAlg a -> ProdFMAlg a
ProdAlgToFree {a} = prodFMEvalMon {v=a}

public export
ProdAlgFromFree : {0 a : Type} -> ProdFMAlg a -> ProdAlg a
ProdAlgFromFree {a} = (|>) (($>) . map {f=ProductMonad} ($!))

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

export prefix 11 $!<
public export
($!<) : {0 atom, a : Type} -> a -> BinTreeFM atom a
($!<) = InBTv

-- A "compound" atom term.
public export
InBTa : {0 atom, a : Type} -> atom -> BinTreeFM atom a
InBTa {atom} {a} = ($!) {atom=(Either a atom)} . Right

export prefix 11 $!>
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
binTreeFMfold : {0 atom, elem, acc : Type} ->
  (elem -> acc -> acc) -> acc -> BinTreeFM atom elem -> acc
binTreeFMfold {elem} {acc} func =
  flip $ binTreeFMEval {atom} {a=(acc -> acc)} func $
    eitherElim (const id) (uncurry (|>))

public export
Foldable (BinTreeFM atom) where
  foldr = binTreeFMfold

public export
binTreeFMsequence : {0 f : Type -> Type} ->
  {func : Functor f} -> {app : Applicative f} ->
  {0 atom, a : Type} -> BinTreeFM atom (f a) -> f (BinTreeFM atom a)
binTreeFMsequence {f} {func} {app} {atom} {a} =
  binTreeFMEval (map {f} binTreeFMpure) $
    eitherElim
      (pure {f} . InBTa)
      (map {f} ($>) . sequence {t=ProductMonad} {f})

public export
binTreeFMtraverse : {0 f : Type -> Type} ->
  {func : Functor f} -> {app : Applicative f} ->
  {0 atom, a, b : Type} ->
  (a -> f b) -> BinTreeFM atom a -> f (BinTreeFM atom b)
binTreeFMtraverse {f} {func} {app} {a} {b} =
  (.) (binTreeFMsequence {f} {func} {app} {a=b}) . binTreeFMmap

public export
Traversable (BinTreeFM atom) where
  traverse {f} =
    binTreeFMtraverse
      {func=(MkFunctor $ map {f})}
      {app=(MkApplicative (pure {f}) ((<*>) {f}))}

public export
BinTreeAlgToFree : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeFMAlg atom a
BinTreeAlgToFree = binTreeFMEvalMon

public export
BinTreeAlgFromFree : {0 atom, a : Type} ->
  BinTreeFMAlg atom a -> BinTreeAlg atom a
BinTreeAlgFromFree {atom} {a} =
  (|>) (InBTc {atom} {a} . mapSnd {f=Either} (mapHom InBTv))

public export
btApplyPure : {0 atom, v, a : Type} ->
  BinTreeF atom (v -> a) -> v -> BinTreeF atom a
btApplyPure {atom} {v} {a} = (|>) (flip applyHom) . flip mapSnd

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

---------------------------------------
---------------------------------------
---- Binary trees as S-expressions ----
---------------------------------------
---------------------------------------

--------------------------------------------------------------
---- Binary trees as "list-of-S-expression" S-expressions ----
--------------------------------------------------------------

-- First we use a slice-functor formulation to define a form
-- of S-expression defined as "atom together with list of S-expression".
-- We shall see that this is equivalent to `BinTreeFM`, but with a
-- richer default algebra since that lives in a slice category.

public export
SLSs : Nat
SLSs = 0

public export
SLSne : Nat
SLSne = S SLSs

public export
SLSl : Nat
SLSl = S SLSne

public export
SLSa : Nat
SLSa = S SLSl

public export
SLSn : Nat
SLSn = S SLSa

public export
SLSsl : Type
SLSsl = Fin SLSn

public export
SLSSs : SLSsl
SLSSs = natToFinLT SLSs

public export
SLSSne : SLSsl
SLSSne = natToFinLT SLSne

public export
SLSSl : SLSsl
SLSSl = natToFinLT SLSl

public export
SLSSa : SLSsl
SLSSa = natToFinLT SLSa

public export
SLSslF : (atom : Type) -> FinSliceEndofunctor SLSn
-- An S-expression (`SLSs`) is an atom together with a list of S-expressions.
SLSslF atom sl FZ = Pair (sl SLSSa) (sl SLSSl)
-- A non-empty list of S-expressions (`SLSne`) is an S-expression together
-- with a list of S-expressions.
SLSslF atom sl (FS FZ) = Pair (sl SLSSs) (sl SLSSl)
-- A list of S-expressions (`SLSl`) is either `nil` (`Unit`) or a non-empty
-- list of S-expressions.
SLSslF atom sl (FS $ FS FZ) = Either Unit (sl SLSSne)
SLSslF atom sl (FS $ FS $ FS FZ) = atom

public export
SLSslFM : (atom : Type) -> FinSliceEndofunctor SLSn
SLSslFM = SliceFreeM . SLSslF

public export
SLSslMu : (atom : Type) -> FinSliceObj SLSn
SLSslMu = SliceMu . SLSslF

-- We can generate a functor which is naturally isomorphic to the
-- `Type`-free-monad formulation from the slice-free-monad formulation
-- by restricting variables to be only of S-expression type -- that is,
-- by making `Void` the type of other variables -- by precomposition,
-- and then projecting out the S-expression component of the output type
-- by post-composition.

public export
SLSvarF : Type -> SliceObj (Fin SLSn)
SLSvarF ty FZ = ty
SLSvarF ty (FS FZ) = Void
SLSvarF ty (FS (FS FZ)) = Void
SLSvarF ty (FS (FS (FS FZ))) = Void

public export
SLSprojF : SLSsl -> SliceObj SLSsl -> Type
SLSprojF = flip apply

public export
SLSFM : (atom : Type) -> Type -> Type
SLSFM atom = SLSprojF SLSSs . SLSslFM atom . SLSvarF

public export
SLSFMl : (atom : Type) -> Type -> Type
SLSFMl atom = SLSprojF SLSSl . SLSslFM atom . SLSvarF

public export
SLSFMne : (atom : Type) -> Type -> Type
SLSFMne atom = SLSprojF SLSSne . SLSslFM atom . SLSvarF

mutual
  public export
  slsSlEval : {0 atom : Type} -> SliceFreeFEval (SLSslF atom)
  slsSlEval {atom} sv sa subst alg i (InSlF i el) = case el of
    InSlV v => subst i v
    InSlC t => slsSlEvalF {atom} sv sa subst alg i t

  public export
  slsSlEvalF : {0 atom : Type} -> SliceFreeFEvalF (SLSslF atom)
  slsSlEvalF {atom} sv sa subst alg FZ (a, l) =
    alg
      FZ
      (slsSlEval {atom} sv sa subst alg (FS $ FS $ FS FZ) a,
       slsSlEval {atom} sv sa subst alg (FS $ FS FZ) l)
  slsSlEvalF {atom} sv sa subst alg (FS FZ) (x, l) =
    alg
      (FS FZ)
      (slsSlEval {atom} sv sa subst alg FZ x,
       slsSlEval {atom} sv sa subst alg (FS $ FS FZ) l)
  slsSlEvalF {atom} sv sa subst alg (FS $ FS FZ) (Left ()) =
    alg
      (FS $ FS FZ)
      (Left ())
  slsSlEvalF {atom} sv sa subst alg (FS $ FS FZ) (Right ne) =
    alg
      (FS $ FS FZ)
      (Right $ slsSlEval {atom} sv sa subst alg (FS FZ) ne)
  slsSlEvalF {atom} sv sa subst alg (FS $ FS $ FS FZ) ea =
    alg
      (FS $ FS $ FS FZ)
      ea

-- Now we show that the slice-functor version of `SLSFM` is
-- indeed naturally isomorphic to a version defined purely
-- within `Type` using `SnocList`.

public export
SLSF : Type -> Type -> Type
SLSF atom x = (atom, SnocList x)

public export
SLSFmu : Type -> Type
SLSFmu = Mu . SLSF

public export
SLSFMnonSl : Type -> Type -> Type
SLSFMnonSl = FreeMonad . SLSF

-- Here we show how to define algebras and substitutions for
-- `SLSFmu`/`SLSFMnonSl` in the style of those for `SLSslMu`/`SLSslFM`.
public export
SLSFnonSlAlg : Type -> Type -> Type -> Type -> Type -> Type
SLSFnonSlAlg atom xty nety lty aty =
  (aty -> lty -> xty, xty -> lty -> nety, lty, nety -> lty, atom -> aty)

mutual
  public export
  slsfCata : {atom, xty, nety, lty, aty : Type} ->
    SLSFnonSlAlg atom xty nety lty aty ->
    SLSFmu atom -> xty
  slsfCata alg@(algx, algne, alge, algl, alga) (InFree (TFV ev)) =
    void ev
  slsfCata alg@(algx, algne, alge, algl, alga) (InFree (TFC (ea, l))) =
    algx (slsfAtomCata alg ea) (slsfLCata alg l)

  public export
  slsfNeCata : {atom, xty, nety, lty, aty : Type} ->
    SLSFnonSlAlg atom xty nety lty aty ->
    SLSFmu atom -> SnocList (SLSFmu atom) -> nety
  slsfNeCata alg@(algx, algne, alge, algl, alga) ex el =
    algne (slsfCata alg ex) (slsfLCata alg el)

  public export
  slsfLCata : {atom, xty, nety, lty, aty : Type} ->
    SLSFnonSlAlg atom xty nety lty aty ->
    SnocList (SLSFmu atom) -> lty
  slsfLCata alg@(algx, algne, alge, algl, alga) [<] =
    alge
  slsfLCata alg@(algx, algne, alge, algl, alga) (el :< ex) =
    algl (slsfNeCata alg ex el)

  public export
  slsfAtomCata : {atom, xty, nety, lty, aty : Type} ->
    SLSFnonSlAlg atom xty nety lty aty ->
    atom -> aty
  slsfAtomCata alg@(algx, algne, alge, algl, alga) ea = alga ea

public export
SLSfromSlSl : Type -> Type -> FinSliceObj SLSn
SLSfromSlSl atom ty FZ = ty
SLSfromSlSl atom ty (FS FZ) = Pair ty (SnocList ty)
SLSfromSlSl atom ty (FS (FS FZ)) = SnocList ty
SLSfromSlSl atom ty (FS (FS (FS FZ))) = atom

public export
SLSFMfromSlSl : (atom, var : Type) -> FinSliceObj SLSn
SLSFMfromSlSl atom var = SLSfromSlSl atom (SLSFMnonSl atom var)

public export
SLSFMfromSlSlSubst : (atom, var : Type) ->
  SliceMorphism {a=SLSsl}
    (SLSvarF var)
    (SLSFMfromSlSl atom var)
SLSFMfromSlSlSubst atom var FZ v = inFV v
SLSFMfromSlSlSubst atom var (FS FZ) v = void v
SLSFMfromSlSlSubst atom var (FS (FS FZ)) v = void v
SLSFMfromSlSlSubst atom var (FS (FS (FS FZ))) v = void v

public export
SLSFMfromSlSlAlg : (atom, var : Type) ->
  SliceMorphism {a=SLSsl}
    (SLSslF atom $ SLSFMfromSlSl atom var)
    (SLSFMfromSlSl atom var)
SLSFMfromSlSlAlg atom var FZ (a, l) = inFC (a, l)
SLSFMfromSlSlAlg atom var (FS FZ) (x, l) = (x, l)
SLSFMfromSlSlAlg atom var (FS (FS FZ)) (Left ()) = Lin
SLSFMfromSlSlAlg atom var (FS (FS FZ)) (Right (x, l)) = l :< x
SLSFMfromSlSlAlg atom var (FS (FS (FS FZ))) ea = ea

public export
SLSFMfromSl : (atom, var : Type) -> SLSFM atom var -> SLSFMnonSl atom var
SLSFMfromSl atom var =
  slsSlEval
    {atom}
    (SLSvarF var)
    (SLSFMfromSlSl atom var)
    (SLSFMfromSlSlSubst atom var)
    (SLSFMfromSlSlAlg atom var)
    FZ

mutual
  public export
  SLSFMtoSl : (atom, var : Type) ->
    SLSFMnonSl atom var -> SLSFM atom var
  SLSFMtoSl atom var (InFree (TFV ev)) =
    InSlFv ev
  SLSFMtoSl atom var (InFree (TFC (a, l))) =
    InSlFc (InSlFc a, SLSFMtoSlL atom var l)

  public export
  SLSFMtoSlL : (atom, var : Type) ->
    SnocList (SLSFMnonSl atom var) -> SLSFMl atom var
  SLSFMtoSlL atom var Lin = InSlFc (Left ())
  SLSFMtoSlL atom var (l :< x) = InSlFc (Right $ SLSFMtoSlNE atom var l x)

  public export
  SLSFMtoSlNE : (atom, var : Type) ->
    SnocList (SLSFMnonSl atom var) -> SLSFMnonSl atom var -> SLSFMne atom var
  SLSFMtoSlNE atom var l x =
    InSlFc (SLSFMtoSl atom var x, SLSFMtoSlL atom var l)

-- Now we can use the isomorphism between the slice (`SLSFM`) and
-- non-slice (`SLSFMnonSl`) versions of S-expressions to define the
-- evaluation of the latter in terms of the evaluation of the former.

public export
slsSubstFromSlSl : {atom : Type} -> (v, a : Type) ->
  (v -> a) ->
  SliceMorphism {a=SLSsl} (SLSvarF v) (SLSfromSlSl atom a)
slsSubstFromSlSl {atom} v a subst FZ ev = subst ev
slsSubstFromSlSl {atom} v a subst (FS FZ) ev = void ev
slsSubstFromSlSl {atom} v a subst (FS (FS FZ)) ev = void ev
slsSubstFromSlSl {atom} v a subst (FS (FS (FS FZ))) ev = void ev

public export
slsAlgFromSlSl : {atom : Type} -> (v, a : Type) ->
  (SLSF atom a -> a) ->
  SliceMorphism {a=SLSsl}
    (SLSslF atom (SLSfromSlSl atom a))
    (SLSfromSlSl atom a)
slsAlgFromSlSl {atom} v a alg FZ x = alg x
slsAlgFromSlSl {atom} v a alg (FS FZ) x = x
slsAlgFromSlSl {atom} v a alg (FS (FS FZ)) (Left ()) = Lin
slsAlgFromSlSl {atom} v a alg (FS (FS FZ)) (Right (ea, el)) = el :< ea
slsAlgFromSlSl {atom} v a alg (FS (FS (FS FZ))) ea = ea

public export
slsFMeval : {atom : Type} -> FreeFEval (SLSF atom)
slsFMeval {atom} v a subst alg el =
  slsSlEval {atom} (SLSvarF v) (SLSfromSlSl atom a)
    (slsSubstFromSlSl {atom} v a subst)
    (slsAlgFromSlSl {atom} v a alg)
    FZ
    (SLSFMtoSl atom v el)

public export
slsFMevalL : {atom : Type} -> (v, a : Type) ->
  (v -> a) -> (SLSF atom a -> a) -> SnocList (SLSFMnonSl atom v) -> SnocList a
slsFMevalL {atom} v a subst alg = map (slsFMeval {atom} v a subst alg)

-- Now we show that the slice-functor version of `SLSFM` can
-- indeed be represented by a `BinTreeFM`.
--
-- However, it is only a subset of `BinTreeFM`s which represent
-- `SLSFM`s, so `SLSFM` can be viewed as a refinement of `BinTreeFM`.
-- The reason is that a `BinTreeFM` term can only be seen as a valid
-- `SLSFM` term if variable terms are never _applied_ to other terms --
-- that is, if it has subterms of the form `Pair(var, tree)`.  Because
-- a variable term is always a leaf, we could not meaningfully interpret
-- its application to another term.

public export
BTisSLSret : Type
BTisSLSret = Fin 3

public export
BTisVarN : Nat
BTisVarN = Z

public export
BTisVar : BTisSLSret
BTisVar = natToFinLT BTisVarN

public export
BTisCompoundSLSN : Nat
BTisCompoundSLSN = S BTisVarN

public export
BTisCompoundSLS : BTisSLSret
BTisCompoundSLS = natToFinLT BTisCompoundSLSN

public export
BTisNotSLSN : Nat
BTisNotSLSN = S BTisCompoundSLSN

public export
BTisNotSLS : BTisSLSret
BTisNotSLS = natToFinLT BTisNotSLSN

public export
btSLStypeSubst : (var : Type) -> var -> BTisSLSret
btSLStypeSubst var _ = BTisVar

public export
btSLSpairType : BTisSLSret -> BTisSLSret -> BTisSLSret
btSLSpairType l r = case l of
  FZ => BTisNotSLS
  FS FZ => case r of
    FZ => BTisCompoundSLS
    FS FZ => BTisCompoundSLS
    FS (FS FZ) => BTisNotSLS
  FS (FS FZ) => BTisNotSLS

public export
btRetIsCompoundSLS : BTisSLSret -> Bool
btRetIsCompoundSLS sls = sls == BTisCompoundSLS

public export
btRetIsSLS : BTisSLSret -> Bool
btRetIsSLS sls = btRetIsCompoundSLS sls || (sls == BTisVar)

public export
btSLSappType : (l, r : BTisSLSret) ->
  IsTrue (btRetIsCompoundSLS l) ->
  IsTrue (btRetIsSLS r) ->
  IsTrue (btRetIsCompoundSLS $ btSLSpairType l r)
btSLSappType FZ r eql eqr = case eql of Refl impossible
btSLSappType (FS FZ) FZ eql eqr = Refl
btSLSappType (FS FZ) (FS FZ) eql eqr = Refl
btSLSappType (FS FZ) (FS (FS FZ)) eql eqr = case eqr of Refl impossible
btSLSappType (FS (FS FZ)) r eql eqr = case eql of Refl impossible

public export
btSLStypeAlg : (atom : Type) -> BinTreeAlg atom BTisSLSret
btSLStypeAlg atom (Left ea) = BTisCompoundSLS
btSLStypeAlg atom (Right (l, r)) = btSLSpairType l r

public export
btSLStype : (atom, var : Type) -> BinTreeFM atom var -> BTisSLSret
btSLStype atom var =
  binTreeFMEval {atom} {v=var} {a=BTisSLSret}
    (btSLStypeSubst var)
    (btSLStypeAlg atom)

public export
btIsCompoundSLS : (atom, var : Type) -> BinTreeFM atom var -> Bool
btIsCompoundSLS atom var = btRetIsCompoundSLS . btSLStype atom var

public export
btIsSLS : (atom, var : Type) -> BinTreeFM atom var -> Bool
btIsSLS atom var = btRetIsSLS . btSLStype atom var

public export
BinTreeSLS : Type -> Type -> Type
BinTreeSLS atom var =
  Refinement {a=(BinTreeFM atom var)} (btIsSLS atom var)

public export
BinTreeCompoundSLS : Type -> Type -> Type
BinTreeCompoundSLS atom var =
  Refinement {a=(BinTreeFM atom var)} (btIsCompoundSLS atom var)

public export
btAppCompoundSLS : {atom, var : Type} ->
  (tl, tr : BinTreeFM atom var) ->
  IsTrue (btIsCompoundSLS atom var tl) ->
  IsTrue (btIsSLS atom var tr) ->
  IsTrue (btIsCompoundSLS atom var (InBTm $ Right (tl, tr)))
btAppCompoundSLS {atom} {var} tl tr = btSLSappType _ _

public export
btAppCompound : {atom, var : Type} ->
  BinTreeCompoundSLS atom var -> BinTreeSLS atom var ->
  BinTreeCompoundSLS atom var
btAppCompound {atom} {var} tl tr =
  Element0
    (InBTm $ Right (fst0 tl, fst0 tr))
    (btAppCompoundSLS {atom} {var} (fst0 tl) (fst0 tr) (snd0 tl) (snd0 tr))

public export
btIsSLSfromCompound : {atom, var : Type} -> (t : BinTreeFM atom var) ->
  IsTrue (btIsCompoundSLS atom var t) -> IsTrue (btIsSLS atom var t)
btIsSLSfromCompound {atom} {var} t = orLeft

public export
btSLSfromCompound : {atom, var : Type} ->
  BinTreeCompoundSLS atom var -> BinTreeSLS atom var
btSLSfromCompound {atom} {var} = s0MapSnd $ btIsSLSfromCompound {atom} {var}

public export
BinTreeFMfromSlSl : (atom, var : Type) -> FinSliceObj SLSn
BinTreeFMfromSlSl atom var FZ =
  BinTreeSLS atom var
BinTreeFMfromSlSl atom var (FS FZ) =
  (BinTreeSLS atom var, atom -> BinTreeCompoundSLS atom var)
BinTreeFMfromSlSl atom var (FS (FS FZ)) =
  atom -> BinTreeCompoundSLS atom var
BinTreeFMfromSlSl atom var (FS (FS (FS FZ))) =
  atom

public export
BinTreeFMfromSlSlSubst : (atom, var : Type) ->
  SliceMorphism {a=SLSsl}
    (SLSvarF var)
    (BinTreeFMfromSlSl atom var)
BinTreeFMfromSlSlSubst atom var FZ v = Element0 (InBTm $ Left $ Left v) Refl
BinTreeFMfromSlSlSubst atom var (FS FZ) v = void v
BinTreeFMfromSlSlSubst atom var (FS (FS FZ)) v = void v
BinTreeFMfromSlSlSubst atom var (FS (FS (FS FZ))) v = void v

public export
BinTreeFMfromSlSlAlg : (atom, var : Type) ->
  SliceMorphism {a=SLSsl}
    (SLSslF atom $ BinTreeFMfromSlSl atom var)
    (BinTreeFMfromSlSl atom var)
BinTreeFMfromSlSlAlg atom var FZ (a, l) = btSLSfromCompound $ l a
BinTreeFMfromSlSlAlg atom var (FS FZ) (tl, tr) = (tl, tr)
BinTreeFMfromSlSlAlg atom var (FS (FS FZ))
  (Left ()) =
    \ea => Element0 (InBTm $ Left $ Right ea) Refl
BinTreeFMfromSlSlAlg atom var (FS (FS FZ))
  (Right (tr, tlv)) = \ea => (btAppCompound {atom} {var} (tlv ea) tr)
BinTreeFMfromSlSlAlg atom var (FS (FS (FS FZ))) ea = ea

public export
BinTreeSLSfromSl : (atom, var : Type) -> SLSFM atom var -> BinTreeSLS atom var
BinTreeSLSfromSl atom var =
  slsSlEval
    {atom}
    (SLSvarF var)
    (BinTreeFMfromSlSl atom var)
    (BinTreeFMfromSlSlSubst atom var)
    (BinTreeFMfromSlSlAlg atom var)
    FZ

public export
BinTreeFMfromSl : (atom, var : Type) -> SLSFM atom var -> BinTreeFM atom var
BinTreeFMfromSl atom var el = fst0 $ BinTreeSLSfromSl atom var el

----------------------------------------------
---- Dependent predicates on binary trees ----
----------------------------------------------

public export
data BTisSLSty : {atom, var : Type} -> BinTreeFM atom var -> BTisSLSret -> Type
    where
  BTtyVar : {atom, var : Type} ->
    (ev : var) -> BTisSLSty (InBTv ev) BTisVar
  BTtyAtom : {atom, var : Type} ->
    (ea : atom) -> BTisSLSty (InBTa ea) BTisCompoundSLS
  BTtyAppVar : {atom, var : Type} ->
    (l, r : BinTreeFM atom var) ->
    BTisSLSty l BTisVar -> BTisSLSty (InBTp l r) BTisNotSLS
  BTtyNonSLSl : {atom, var : Type} ->
    (l, r : BinTreeFM atom var) ->
    BTisSLSty l BTisNotSLS -> BTisSLSty (InBTp l r) BTisNotSLS
  BTtyNonSLSr : {atom, var : Type} ->
    (l, r : BinTreeFM atom var) ->
    BTisSLSty r BTisNotSLS -> BTisSLSty (InBTp l r) BTisNotSLS
  BTtyCompAppVar : {atom, var : Type} ->
    (l, r : BinTreeFM atom var) ->
    BTisSLSty l BTisCompoundSLS -> BTisSLSty r BTisVar ->
    BTisSLSty (InBTp l r) BTisCompoundSLS
  BTtyCompAppComp : {atom, var : Type} ->
    (l, r : BinTreeFM atom var) ->
    BTisSLSty l BTisCompoundSLS -> BTisSLSty r BTisCompoundSLS ->
    BTisSLSty (InBTp l r) BTisCompoundSLS

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
-- What this allows is an expressive (not logical) extension to the notion
-- of a binary-tree algebra as a catamorphism that returns different types
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

public export
BTTexpAlgToBTAlg : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> BinTreeAlg atom (x, (n : Nat ** Vect (S n) x))
BTTexpAlgToBTAlg {atom} {x} {t} (xalg, talg) (Left ea) with (xalg $ Left ea)
  BTTexpAlgToBTAlg {atom} {x} {t} (xalg, talg) (Left ea) | ex =
    (ex, (0 ** [ex]))
BTTexpAlgToBTAlg {atom} {x} {t} (xalg, talg) (Right ((hd, _), (_, (n ** tl)))) =
  let vx = hd :: tl in
  (xalg $ Right $ talg (n ** vx), (S n ** vx))

public export
btTexpCatas : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> BinTreeMu atom -> (x, (n : Nat ** Vect (S n) x))
btTexpCatas = binTreeCata . BTTexpAlgToBTAlg

public export
btTexpCata : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> BinTreeMu atom -> x
btTexpCata = fst .* btTexpCatas

public export
btTexpCataToVec : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> BinTreeMu atom -> (n : Nat ** Vect (S n) x)
btTexpCataToVec = snd .* btTexpCatas

public export
btTupleMapCata : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> {0 n : Nat} -> Vect (S (S n)) (BinTreeMu atom) ->
  Vect (S (S n)) x
btTupleMapCata alg {t} = map $ btTexpCata {t} alg

public export
btTupleCata : {0 atom, x, t : Type} ->
  BTTexpAlg atom x t -> {n : Nat} -> Vect (S (S n)) (BinTreeMu atom) -> t
btTupleCata (xalg, talg) {n} xs = talg (n ** btTupleMapCata (xalg, talg) {n} xs)

-- A convenience version of `btTexpCata` which takes only one type
-- (a return value for expressions), combining the induction hypotheses for
-- expressions and tuples.
public export
BTbyTupleAlg : (atom, x : Type) -> Type
BTbyTupleAlg atom x = (atom -> x, BTTexp2 x -> x)

public export
btCataByTuple : {0 atom, x : Type} -> BTbyTupleAlg atom x -> BinTreeMu atom -> x
btCataByTuple {atom} {x} (aalg, talg) =
  btTexpCata {atom} {x} {t=(BTTexp2 x)} (eitherElim aalg talg, id)

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

public export
Show atom => Show (BinTreeMu atom) where
  show = btTexpShowI

-----------------------------------------------
-----------------------------------------------
---- Various forms of product catamorphism ----
-----------------------------------------------
-----------------------------------------------

-- An algebra for paramorphisms on `BinTreeMu`.
public export
BinTreeParaAlg : Type -> Type -> Type
BinTreeParaAlg atom a = BinTreeF atom (BinTreeMu atom, a) -> a

public export
BinTreeParaToCataAlg : {0 atom, a : Type} ->
  BinTreeParaAlg atom a -> BinTreeAlg atom (BinTreeMu atom, a)
BinTreeParaToCataAlg {atom} {a} alg el =
  (InBTm (mapSnd {f=Either} (mapHom {f=Pair} fst) el), alg el)

public export
binTreePara : {0 atom, a : Type} -> BinTreeParaAlg atom a -> BinTreeMu atom -> a
binTreePara {atom} {a} alg =
  snd . binTreeCata {atom} {a=(BinTreeMu atom, a)} (BinTreeParaToCataAlg alg)

-- An algebra for catamorphisms on pairs of `BinTreeMu`s that uses the
-- product-hom adjunction.
public export
BinTreeProdHomAlg : Type -> Type -> Type -> Type
BinTreeProdHomAlg atom atom' a = BinTreeAlg atom (BinTreeMu atom' -> a)

public export
binTreeProdHomCata : {0 atom, atom', a : Type} ->
  BinTreeProdHomAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeProdHomCata {atom} {atom'} =
  binTreeCata {atom} {a=(BinTreeMu atom' -> a)}

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
--  - The result for pairs of pairs takes into account the results of parallel
--    induction for each of the four combinations of parallel inductions on one
--    branch of the first input tree with one branch of the second input tree
public export
BinTreeProdAlg : Type -> Type -> Type -> Type
BinTreeProdAlg = Algebra .* BinTreeProdF

public export
BinTreeProdAlgToProdHomAlg : {0 atom, atom', a : Type} ->
  BinTreeProdAlg atom atom' a -> BinTreeProdHomAlg atom atom' a
BinTreeProdAlgToProdHomAlg alg
  (Left ea) x' =
    binTreeCata {atom=atom'} {a} (curry alg $ Left ea) x'
BinTreeProdAlgToProdHomAlg alg
  (Right (alg1', alg2')) x' =
    case outBTm x' of
      Left ea' =>
        alg (Right (alg1' $ $! ea', alg2' $ $! ea'), Left ea')
      Right (bt1', bt2') =>
        alg (Right (alg1' bt1', alg1' bt2'), Right (alg2' bt1', alg2' bt2'))

public export
binTreeProdCata : {0 atom, atom', a : Type} ->
  BinTreeProdAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeProdCata = binTreeProdHomCata . BinTreeProdAlgToProdHomAlg

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
-- This amounts to a special case of the product where atom/pair combinations
-- depend only on the atom.
public export
BinTreeParProdAlg : Type -> Type -> Type -> Type
BinTreeParProdAlg = Algebra .* BinTreeParProdF

public export
BinTreeParProdAlgToProdAlg : {0 atom, atom', a : Type} ->
  BinTreeParProdAlg atom atom' a -> BinTreeProdAlg atom atom' a
BinTreeParProdAlgToProdAlg alg (Left ea, Left ea') =
  alg $ Left $ Left (ea, ea')
BinTreeParProdAlgToProdAlg alg (Left ea, Right (_, _)) =
  alg $ Left $ Right $ Left ea
BinTreeParProdAlgToProdAlg alg (Right (_, _), Left ea') =
  alg $ Left $ Right $ Right ea'
BinTreeParProdAlgToProdAlg alg (Right (x1, x2), Right (x1', x2')) =
  alg $ Right ((x1, x2), (x1', x2'))

public export
binTreeParProdCata : {0 atom, atom', a : Type} ->
  BinTreeParProdAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeParProdCata = binTreeProdCata . BinTreeParProdAlgToProdAlg

-----------------------------------------------
---- Algebras for products of binary trees ----
-----------------------------------------------

public export
BTFpos : Type -> Type
BTFpos atom = Either atom Unit

public export
btfPosA : {atom : Type} -> atom -> BTFpos atom
btfPosA {atom} = Left

public export
btfPosP : (atom : Type) -> BTFpos atom
btfPosP atom = Right ()

public export
BTFdir : (atom : Type) -> BTFpos atom -> Type
BTFdir atom (Left ea) = Void
BTFdir atom (Right ()) = Fin 2

public export
BTFradj : (atom : Type) -> Type -> SliceObj (BTFpos atom)
BTFradj atom x (Left ea) = Unit
BTFradj atom x (Right ()) = (x, x)

public export
BTFsl : Type -> Type
BTFsl atom = Either (BTFpos atom) Unit

public export
BTFradjEither : (atom : Type) -> Type -> SliceObj (BTFsl atom)
BTFradjEither atom x (Left i) = BTFradj atom x i
BTFradjEither atom x (Right ()) = (i : BTFpos atom ** BTFradj atom x i)

public export
BTFslF : (atom : Type) -> SliceEndofunctor (BTFsl atom)
BTFslF atom sl = BTFradjEither atom (sl $ Right ())

public export
BTSslMu : (atom : Type) -> SliceObj (BTFsl atom)
BTSslMu atom = SliceMu $ BTFslF atom

public export
BTSslFM : (atom : Type) -> SliceEndofunctor (BTFsl atom)
BTSslFM atom = SliceFreeM $ BTFslF atom

public export
BinTreeProdHomAlgAlt : (atom, atom', x : Type) -> Type
BinTreeProdHomAlgAlt atom atom' x =
  (atom -> BinTreeMu atom' -> x,
   BinTreeMu atom' -> (BinTreeMu atom' -> x) -> (BinTreeMu atom' -> x) -> x)

public export
BinTreeProdHomAlgFromAlt : (atom, atom', x : Type) ->
  BinTreeProdHomAlgAlt atom atom' x -> BinTreeProdHomAlg atom atom' x
BinTreeProdHomAlgFromAlt atom atom' x (algl, algr) (Left ea) el' =
  algl ea el'
BinTreeProdHomAlgFromAlt atom atom' x (algl, algr) (Right (algl', algr')) el' =
  algr el' algl' algr'

public export
BinTreeProdHomAlgToAlt : (atom, atom', x : Type) ->
  BinTreeProdHomAlg atom atom' x -> BinTreeProdHomAlgAlt atom atom' x
BinTreeProdHomAlgToAlt atom atom' x alg =
  (alg . Left, Prelude.curry . flip (alg . Right))

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

--------------------------------------------------------------------
--------------------------------------------------------------------
---- Generalized pattern-matching using combinators on algebras ----
--------------------------------------------------------------------
--------------------------------------------------------------------

------------------------------------------
---- Combinators on `ProdFM` algebras ----
------------------------------------------

public export
prodFMAlgInjectLeft : {0 a : Type} ->
  ProdAlg a -> ProdAlg a -> Algebra (BinTreeF a . ProdFM) a
prodFMAlgInjectLeft {a} alg algl =
  eitherElim id (alg . bimap (prodFMEvalMon algl) (prodFMEvalMon alg))

public export
prodFMAlgInjectRight : {0 a : Type} ->
  ProdAlg a -> ProdAlg a -> Algebra (BinTreeF a . ProdFM) a
prodFMAlgInjectRight {a} alg algr =
  eitherElim id (alg . bimap (prodFMEvalMon alg) (prodFMEvalMon algr))

public export
prodFMSpecializeLeft : {0 a : Type} ->
  ProdAlg a -> ProdAlg a -> ProdFMAlg a
prodFMSpecializeLeft {a} = (|>) (outBTm {atom=a}) .* prodFMAlgInjectLeft

public export
prodFMSpecializeRight : {0 a : Type} ->
  ProdAlg a -> ProdAlg a -> ProdFMAlg a
prodFMSpecializeRight {a} = (|>) (outBTm {atom=a}) .* prodFMAlgInjectRight

public export
prodSpecializeLeft : {0 a : Type} ->
  ProdAlg a -> ProdAlg a -> ProdAlg a
prodSpecializeLeft = ProdAlgFromFree .* prodFMSpecializeLeft

public export
prodSpecializeRight : {0 a : Type} ->
  ProdAlg a -> ProdAlg a -> ProdAlg a
prodSpecializeRight = ProdAlgFromFree .* prodFMSpecializeRight

---------------------------------------------
---- Combinators on `BinTreeFM` algebras ----
---------------------------------------------

public export
binTreeFMAlgInjectLeft : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeAlg atom a ->
  Algebra (BinTreeF (Either a atom) . BinTreeFM atom) a
binTreeFMAlgInjectLeft {atom} {a} alg algl =
  eitherElim
    (eitherElim id (alg . Left))
    (alg . Right . bimap (binTreeFMEvalMon algl) (binTreeFMEvalMon alg))

public export
binTreeFMSpecializeLeft : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeAlg atom a -> BinTreeFMAlg atom a
binTreeFMSpecializeLeft {atom} {a} =
  (|>) (outBTm {atom=(Either a atom)}) .* binTreeFMAlgInjectLeft

public export
binTreeSpecializeLeft : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeAlg atom a -> BinTreeAlg atom a
binTreeSpecializeLeft = BinTreeAlgFromFree .* binTreeFMSpecializeLeft

public export
binTreeFMAlgInjectRight : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeAlg atom a ->
  Algebra (BinTreeF (Either a atom) . BinTreeFM atom) a
binTreeFMAlgInjectRight {atom} {a} alg algr =
  eitherElim
    (eitherElim id (alg . Left))
    (alg . Right . bimap (binTreeFMEvalMon alg) (binTreeFMEvalMon algr))

public export
binTreeFMSpecializeRight : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeAlg atom a -> BinTreeFMAlg atom a
binTreeFMSpecializeRight {atom} {a} =
  (|>) (outBTm {atom=(Either a atom)}) .* binTreeFMAlgInjectRight

public export
binTreeSpecializeRight : {0 atom, a : Type} ->
  BinTreeAlg atom a -> BinTreeAlg atom a -> BinTreeAlg atom a
binTreeSpecializeRight = BinTreeAlgFromFree .* binTreeFMSpecializeRight
