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
Functor ProductMonad where
  map = mapHom

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

-- The polynomial product of two `BinTreeF` functors -- that is, the product
-- in the category of polynomial endofunctors on `Type`.
--
-- In the polynomial product, the positions are products of those of the
-- individual functors, while the directions are the corresponding coproducts.
public export
BinTreeProdF : Type -> Type -> Type -> Type
BinTreeProdF atom atom' = ProductF (BinTreeF atom) (BinTreeF atom')

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
  Either (Either (atom, atom') (Either atom atom')) .
  (ProductMonad .  ProductMonad)

prefix 1 $$!
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

-- The initial algebra (least fixed point) of `BinTreeF`.
public export
data BinTreeMu : Type -> Type where
  InBTm : {0 atom : Type} -> BinTreeF atom (BinTreeMu atom) -> BinTreeMu atom

-- The initial algebra of `BinTreeF` is also the free monad of the
-- product monad.
public export
ProdFM : Type -> Type
ProdFM = BinTreeMu

prefix 1 $!
public export
($!) : {0 atom : Type} -> atom -> BinTreeMu atom
($!) = InBTm . ($$!)

infixr 10 $>
public export
($>) : {0 atom : Type} -> (BinTreeMu atom, BinTreeMu atom) -> BinTreeMu atom
($>) = InBTm . ($$>)

%hide LanguageDef.ADTCat.infixr.($*)
infixr 10 $*
public export
($*) : {0 atom : Type} -> BinTreeMu atom -> BinTreeMu atom -> BinTreeMu atom
($*) = InBTm .* ($$*)

prefix 1 $:
public export
($:) : {0 atom : Type} ->
  (l : List (BinTreeMu atom)) -> {auto 0 ne : NonEmpty l} -> BinTreeMu atom
($:) {atom} (x :: xs) {ne=IsNonEmpty} = foldl {t=List} ($*) x xs

prefix 1 $:
public export
($:!) : {0 atom : Type} ->
  (l : List atom) -> {auto 0 ne : NonEmpty l} -> BinTreeMu atom
($:!) {atom} l {ne} = ($:) (map ($!) l) {ne=(mapNonEmpty {l} {ne})}

public export
BinTreeAlg : Type -> Type -> Type
BinTreeAlg = Algebra . BinTreeF

-- The universal "catamorphism" morphism of the initial algebra `Mu[BinTreeF]`.
public export
binTreeCata : {0 atom, a : Type} -> BinTreeAlg atom a -> BinTreeMu atom -> a
binTreeCata {atom} {a} alg (InBTm x) = alg $ case x of
  Left ea => ($$!) ea
  Right (x1, x2) => binTreeCata alg x1 $$* binTreeCata alg x2

-- The (universal) catamorphism of `Mu[BinTreeF]` is also the universal "eval"
-- morphism for the free monad of the product monad.
public export
prodFMEval : {0 atom, a : Type} -> BinTreeAlg atom a -> ProdFM atom -> a
prodFMEval = binTreeCata

public export
prodFMBind : {0 atom : Type} -> {0 a : Type} ->
  (atom -> ProdFM a) -> ProdFM atom -> ProdFM a
prodFMBind {atom} {a} = prodFMEval {atom} {a=(ProdFM a)} . flip eitherElim ($>)

-- XXX Functor, Applicative, Monad

-----------------------------------------------
---- Various forms of product catamorphism ----
-----------------------------------------------

-- An algebra for catamorphisms on pairs of `BinTreeMu`s that uses the
-- product-hom adjunction.
public export
BinTreeProdHomAlg : Type -> Type -> Type -> Type
BinTreeProdHomAlg = (|>) BinTreeAlg . (.) . BinTreeAlg

public export
BinTreeProdHomAlgArg : Type -> Type -> Type -> Type
BinTreeProdHomAlgArg atom atom' a =
 (Either atom (ProductMonad (Either atom' (a, a) -> a)),
  Either atom' (ProductMonad a))

public export
binTreeProdHomCata : {0 atom, atom', a : Type} ->
  BinTreeProdHomAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeProdHomCata {atom} {atom'} =
  binTreeCata {atom=atom'} {a} .* binTreeCata {atom} {a=(BinTreeAlg atom' a)}

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
BinTreeProdHomAlgArgToProdAlgArg : {0 atom, atom', a : Type} ->
  BinTreeProdHomAlgArg atom atom' a ->
  (Either atom (ProductMonad a), Either atom' (ProductMonad a))
BinTreeProdHomAlgArgToProdAlgArg (Left x, x') =
  (Left x, x')
BinTreeProdHomAlgArgToProdAlgArg (Right (alg1, alg2), x') =
  (Right (alg1 x', alg2 x'), x')

public export
binTreeProdCata : {atom, atom', a : Type} ->
  BinTreeProdAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeProdCata alg =
  binTreeProdHomCata (alg .* BinTreeProdHomAlgArgToProdAlgArg .* MkPair)

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
  BinTreeProdHomAlgArg atom atom' a ->
  Either
    (Either
      (atom, atom')
      (Either
        atom
        atom'))
    (ProductMonad $ ProductMonad a)
BinTreeProdHomAlgArgToParProdAlgArg (Left x, Left x') =
  Left $ Left (x, x')
BinTreeProdHomAlgArgToParProdAlgArg (Left x, Right (_, _)) =
  Left $ Right $ Left x
BinTreeProdHomAlgArgToParProdAlgArg (Right (_, _), Left x') =
  Left $ Right $ Right x'
BinTreeProdHomAlgArgToParProdAlgArg (Right (alg1, alg2), Right p) =
  Right ((alg1 $ Right p, alg2 $ Right p), p)

public export
binTreeParProdCata : {0 atom, atom', a : Type} ->
  BinTreeParProdAlg atom atom' a -> BinTreeMu atom -> BinTreeMu atom' -> a
binTreeParProdCata alg =
  binTreeProdHomCata (alg . BinTreeProdHomAlgArgToParProdAlgArg .* MkPair)

-------------------
---- Utilities ----
-------------------

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
binTreeShow : {0 atom : Type} -> (atom -> String) -> BinTreeMu atom -> String
binTreeShow = showLines . binTreeLines

public export
Show atom => Show (BinTreeMu atom) where
  show = binTreeShow show

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

-- A "variable" term.
public export
InBTv : {0 atom, a : Type} -> a -> BinTreeFM atom a
InBTv {atom} {a} =
  InBTm {atom=(Either a atom)} . BTFt {atom} {a} {x=(BinTreeFM atom a)}

-- A "compound" atom term.
public export
InBTa : {0 atom, a : Type} -> atom -> BinTreeFM atom a
InBTa {atom} {a} = ($!) {atom=(Either a atom)} . Right

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

public export
BinTreeEitherAlgFromSubstAlg : {0 atom, v, a : Type} ->
  (v -> a) -> BinTreeAlg atom a -> BinTreeAlg (Either v atom) a
BinTreeEitherAlgFromSubstAlg {atom} {v} {a} subst alg =
  eitherElim (eitherElim subst (alg . ($$!))) (alg . ($$>))

-- The universal `eval` morphism for `BinTreeFM`.
-- Because the free monad of a binary tree is isomorphic to a binary
-- tree with an `Either` atom type, this is just a binary tree
-- catamorphism.
public export
binTreeFMEval : {0 atom, v, a : Type} ->
  (v -> a) -> BinTreeAlg atom a -> BinTreeFM atom v -> a
binTreeFMEval {atom} {v} {a} =
  binTreeCata {atom=(Either v atom)} {a} .*
    BinTreeEitherAlgFromSubstAlg {atom} {v} {a}

public export
binTreeFMBind : {0 atom : Type} -> {0 a, b : Type} ->
  (a -> BinTreeFM atom b) -> BinTreeFM atom a -> BinTreeFM atom b
binTreeFMBind {atom} =
  flip (binTreeFMEval {atom} {v=a} {a=(BinTreeFM atom b)}) $ InBTc {atom} {a=b}

-- XXX Functor, Applicative, Monad

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
