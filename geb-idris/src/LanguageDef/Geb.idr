module LanguageDef.Geb

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.BinTree
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

-------------------------------------------------
-------------------------------------------------
---- Functors in `Cat` as internal to `Type` ----
-------------------------------------------------
-------------------------------------------------

-------------------------------------------------------------------------------
---- Product `Cat`-functor (the functor which produces a product category) ----
-------------------------------------------------------------------------------

-- A functor in the category of categories, which produces the product category.
-- This is the first component of the object map of a polynomial endofunctor in
-- the category of presheaves over the walking quiver.
public export
ProdCatOMap1 : (o : Type) -> (m : o -> o -> Type) -> Type
ProdCatOMap1 o m = (o, o)

-- This is the second component.
public export
ProdCatOMap2 : (o : Type) -> (m : o -> o -> Type) ->
  ProdCatOMap1 o m -> ProdCatOMap1 o m -> Type
ProdCatOMap2 o m x y = (m (fst x) (fst y), m (snd x) (snd y))

public export
ProdCatOMap : (o : Type) -> (m : o -> o -> Type) ->
  (o' : Type ** o' -> o' -> Type)
ProdCatOMap o m = (ProdCatOMap1 o m ** ProdCatOMap2 o m)

-- The morphism map of an endofunctor in the category of presheaves over the
-- walking quiver is a map from morphisms to morphisms of the category of
-- presheaves, and the morphisms of the category of presheaves are natural
-- transformations.  So the morphism map takes natural transformations to
-- natural transformations (in the presheaf category).  This is the morphism
-- map of the functor which produces the product category of the input category.
public export
ProdCatFMap :
  (o, o' : Type) -> (m : o -> o -> Type) -> (m' : o' -> o' -> Type) ->
  (ont : o -> o') -> (mnt : (x, y : o) -> m x y -> m' (ont x) (ont y)) ->
  (font : ProdCatOMap1 o m -> ProdCatOMap1 o' m' **
   (x, y :  ProdCatOMap1 o m) ->
    ProdCatOMap2 o m x y -> ProdCatOMap2 o' m' (font x) (font y))
ProdCatFMap o o' m m' ont mnt =
  (\xy => (ont (fst xy), ont (snd xy)) **
   \xx', yy', mm' =>
    (mnt (fst xx') (fst yy') (fst mm'), (mnt (snd xx') (snd yy') (snd mm'))))

-- The diagonal functor from a category to its product category.  This is
-- a natural transformation in the category of presheaves over the walking
-- quiver, from the identity functor to the `ProdCatOMap` functor.
-- That means that for each object of the category of presheaves over the
-- walking quiver, we specify a morphism from that object to its image under
-- `ProdCatOMap`.
--
-- An object in a category of presheaves is a functor from the index category
-- (in this case, the walking quiver) to `Type`, and a morphism in that
-- category is a natural transformation between those functors.
--
-- So, the diagonal functor in this formulation -- a polymorphic one in which
-- the input category could be any category -- consists of, for each presheaf
-- on the walking quiver, a natural transformation from the identity functor
-- to `ProdCatOMap`/`ProdCatFMap`.
public export
InternalDiagOMap : (o : Type) -> (m : o -> o -> Type) -> o -> ProdCatOMap1 o m
InternalDiagOMap o m x = (x, x)

public export
InternalDiagFMap : (o : Type) -> (m : o -> o -> Type) -> (x, y : o) ->
  m x y -> ProdCatOMap2 o m (InternalDiagOMap o m x) (InternalDiagOMap o m y)
InternalDiagFMap o m x y f = (f, f)

---------------------------------------------------------
---- Adjunction with the product category: coproduct ----
---------------------------------------------------------

public export
CopROMap : (o : Type) -> (m : o -> o -> Type) -> o -> ProdCatOMap1 o m
CopROMap = InternalDiagOMap

public export
CopRFMap : (o : Type) -> (m : o -> o -> Type) -> (x, y : o) ->
  m x y -> ProdCatOMap2 o m (CopROMap o m x) (CopROMap o m y)
CopRFMap = InternalDiagFMap

public export
CopFreeRAdj : (o : Type) -> (m : o -> o -> Type) ->
  (a : ProdCatOMap1 o m) -> (b : o) -> Type
CopFreeRAdj o m = flip $ (.) (uncurry Pair) . (mapHom {f=Pair} . flip m)

-------------------------------------------------------
---- Adjunction with the product category: product ----
-------------------------------------------------------

public export
ProdLOMap : (o : Type) -> (m : o -> o -> Type) -> o -> ProdCatOMap1 o m
ProdLOMap = InternalDiagOMap

public export
ProdLFMap : (o : Type) -> (m : o -> o -> Type) -> (x, y : o) ->
  m x y -> ProdCatOMap2 o m (ProdLOMap o m x) (ProdLOMap o m y)
ProdLFMap = InternalDiagFMap

public export
ProdFreeLAdj : (o : Type) -> (m : o -> o -> Type) ->
  (a : ProdCatOMap1 o m) -> (b : o) -> Type
ProdFreeLAdj o m = flip $ (.) (uncurry Pair) . (mapHom {f=Pair} . m)

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

-----------------------------------------
-----------------------------------------
---- Either algebras of binary trees ----
-----------------------------------------
-----------------------------------------

-- Simply an alias for `btCataByTuple` which specializes `btCataByTuple`'s
-- output type to a `HomEither`.
public export
binTreeHomEitherCataByTuple :
  {0 atom, a, e, b : Type} ->
  (aalg : atom -> HomEither a e b) ->
  (talg : BTTexp2 (HomEither a e b) -> HomEither a e b) ->
  BinTreeMu atom -> HomEither a e b
binTreeHomEitherCataByTuple {atom} {a} {e} {b} =
  btCataByTuple {atom} {x=(HomEither a e b)} .* MkPair

public export
BinTreeBindAlg :
  {0 m : Type -> Type} -> (fm : {0 a, b : Type} -> (a -> b) -> m a -> m b) ->
  (pu : {0 a : Type} -> a -> m a) ->
  (app : {0 a, b : Type} -> m (a -> b) -> m a -> m b) ->
  (bind : {0 a, b : Type} -> m a -> (a -> m b) -> m b) ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeAlg atom (a -> m b)
BinTreeBindAlg {m} fm pu app bind alg cons (Left x) ea =
  alg x ea
BinTreeBindAlg {m} fm pu app bind alg cons (Right (bt, bt')) ea =
  bind (app {a=b} {b=a} (fm {a} {b=(b -> a)} cons (pu ea)) $ bt ea) bt'

public export
BinTreeMonadAlg :
  {0 m : Type -> Type} -> {auto isMonad : Monad m} ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeAlg atom (a -> m b)
BinTreeMonadAlg {m} {isMonad} =
  BinTreeBindAlg {m} (map {f=m}) (pure {f=m}) ((<*>) {f=m}) ((>>=) {m})

public export
binTreeBindCata :
  {0 m : Type -> Type} -> (fm : {0 a, b : Type} -> (a -> b) -> m a -> m b) ->
  (pu : {0 a : Type} -> a -> m a) ->
  (app : {0 a, b : Type} -> m (a -> b) -> m a -> m b) ->
  (bind : {0 a, b : Type} -> m a -> (a -> m b) -> m b) ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> a -> m b
binTreeBindCata {m} fm pu app bind {atom} {a} {b} alg cons =
  binTreeCata {atom} {a=(a -> m b)}
    (BinTreeBindAlg {m} fm pu app bind {atom} {a} {b} alg cons)

public export
binTreeMonadCata :
  {0 m : Type -> Type} -> {auto isMonad : Monad m} ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> a -> m b
binTreeMonadCata {m} {isMonad} =
  binTreeBindCata {m} (map {f=m}) (pure {f=m}) ((<*>) {f=m}) ((>>=) {m})

public export
binTreeHomEitherCata :
  {0 atom, a, e, b : Type} ->
  (alg : atom -> HomEither a e b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> HomEither a e b
binTreeHomEitherCata {atom} {a} {e} {b} =
  binTreeMonadCata {m=(Either e)} {atom} {a} {b}

public export
binTreeMaybeCata :
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> Maybe b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> a -> Maybe b
binTreeMaybeCata {atom} {a} {b} =
  binTreeMonadCata {m=Maybe} {atom} {a} {b}

public export
BinTreeAutoBindAlg :
  {0 m : Type -> Type} -> {0 atom, a : Type} ->
  (alg : atom -> a -> m a) -> (autobind : m a -> (a -> m a) -> m a) ->
  BinTreeAlg atom (a -> m a)
BinTreeAutoBindAlg {m} alg autobind (Left x) ea = alg x ea
BinTreeAutoBindAlg {m} alg autobind (Right (bt, bt')) ea = autobind (bt ea) bt'

public export
BinTreeMonadAutoAlg :
  {0 m : Type -> Type} -> {auto isMonad : Monad m} -> {0 atom, a : Type} ->
  (atom -> a -> m a) -> BinTreeAlg atom (a -> m a)
BinTreeMonadAutoAlg {m} {a} {isMonad} alg =
  BinTreeAutoBindAlg {m} alg ((>>=) {a} {b=a})

public export
AutoHomEither : Type -> Type -> Type
AutoHomEither a e = HomEither a e a

public export
aheMap : {0 a, e, e' : Type} ->
  (e -> e') -> AutoHomEither a e -> AutoHomEither a e'
aheMap = (.) . mapFst {f=Either} {a=e} {b=a} {c=e'}

public export
Functor (AutoHomEither a) where
  map = aheMap

public export
ahePure : {0 a, e : Type} -> e -> AutoHomEither a e
ahePure {a} {e} = const . Left

public export
EitherAutoHom : Type -> Type -> Type
EitherAutoHom = flip AutoHomEither

public export
ehaPure : {0 e, a : Type} -> a -> EitherAutoHom e a
ehaPure {a} {e} = const . Right

public export
eahBindHom : {0 e, a : Type} ->
  EitherAutoHom e a -> (a -> EitherAutoHom e a) -> EitherAutoHom e a
eahBindHom {e} {a} = flip $ biapp (eitherElim Left)

public export
BinTreeEitherAutoHomAlg : {0 atom, a, e : Type} ->
  (alg : atom -> a -> EitherAutoHom e a) ->
  BinTreeAlg atom (a -> EitherAutoHom e a)
BinTreeEitherAutoHomAlg {atom} {a} {e} =
  flip (BinTreeAutoBindAlg {m=(EitherAutoHom e)} {atom} {a}) eahBindHom

public export
binTreeEitherAutoHomCata : {0 atom, a, e : Type} ->
  (alg : atom -> a -> EitherAutoHom e a) ->
  BinTreeMu atom -> a -> EitherAutoHom e a
binTreeEitherAutoHomCata {atom} {a} {e} =
  binTreeCata {atom} {a=(a -> a -> Either e a)} . BinTreeEitherAutoHomAlg

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

public export
data FPFCheck : Type where
  FPFconstr : Nat -> FPFCheck
  FPFterm : FPFCheck

public export
Show FPFCheck where
  show (FPFconstr n) = "(constr[" ++ show n ++ "])"
  show FPFterm = "(term)"

public export
data FPFErr : Type where
  FPFnonConstrHd : FPFErr
  FPFwrongNarg : Nat -> Nat -> FPFErr

public export
Show FPFErr where
  show FPFnonConstrHd = "(non-constructor head)"
  show (FPFwrongNarg n n') = "(wrong number of arguments: expected " ++
    show n ++ "; got " ++ show n' ++ ")"

public export
fpfCheckTermVec : {0 n : Nat} -> Vect n FPFCheck -> Either FPFErr ()
fpfCheckTermVec {n} =
  foldr {t=(Vect n)}
    (\x => eitherElim Left $ \() =>
      case x of
        FPFconstr n' => Left $ FPFwrongNarg 0 n'
        FPFterm => Right ())
    (Right ())

public export
fpfCheck : {fpf : FPFunctor} ->
  BinTreeMu (FPFatom fpf) -> Either FPFErr FPFCheck
fpfCheck {fpf} = btCataByTuple {atom=(FPFatom fpf)} {x=(Either FPFErr FPFCheck)}
  (\i =>
    let ndir = index i (fpfNdir fpf) in
    Right $ if ndir == 0 then FPFterm else FPFconstr ndir,
   \(n ** v) =>
    eitherElim
      Left
      (\v' => case index FZ v' of
        FPFconstr n' =>
          if n' == S n then
            eitherElim
              Left
              (const $ Right FPFterm)
              (fpfCheckTermVec $ tail v')
          else
            Left $ FPFwrongNarg n' (S n)
        FPFterm => Left FPFnonConstrHd)
      $ sequence v)

public export
fpfValid : {fpf : FPFunctor} -> DecPred $ BinTreeMu (FPFatom fpf)
fpfValid = isRight . fpfCheck

public export
FPFTerm : FPFunctor -> Type
FPFTerm fpf = Refinement {a=(BinTreeMu (FPFatom fpf))} (fpfValid {fpf})

public export
MkFPF : (fpf : FPFunctor) -> (bt : BinTreeMu (FPFatom fpf)) ->
  {auto 0 valid : IsTrue $ fpfValid {fpf} bt} -> FPFTerm fpf
MkFPF fpf bt {valid} = MkRefinement {p=(fpfValid {fpf})} bt

public export
checkFPFbounds : (fpf : FPFunctor) ->
  BinTreeMu Nat -> Maybe $ BinTreeMu $ FPFatom fpf
checkFPFbounds fpf =
  traverse {f=Maybe} {b=(FPFatom fpf)} $ \n => natToFin n (fpfNpos fpf)

public export
validFPFbounds : (fpf : FPFunctor) -> DecPred $ BinTreeMu Nat
validFPFbounds fpf = isJust . checkFPFbounds fpf

public export
MkFPFbounded : (fpf : FPFunctor) -> (bt : BinTreeMu Nat) ->
  {auto 0 bounded : IsTrue $ validFPFbounds fpf bt} ->
  BinTreeMu (FPFatom fpf)
MkFPFbounded fpf bt {bounded} with (checkFPFbounds fpf bt)
  MkFPFbounded fpf bt {bounded} | Just bt' = bt'
  MkFPFbounded fpf bt {bounded} | Nothing =
    void $ case bounded of Refl impossible

public export
checkFPFn : (fpf : FPFunctor) ->
  BinTreeMu Nat -> Maybe $ FPFTerm fpf
checkFPFn fpf bt with (checkFPFbounds fpf bt)
  checkFPFn fpf bt | Just bt' = case decEq (fpfValid {fpf} bt') True of
    Yes valid => Just $ Element0 bt' valid
    No _ => Nothing
  checkFPFn fpf bt | Nothing = Nothing

public export
validFPFn : (fpf : FPFunctor) -> DecPred $ BinTreeMu Nat
validFPFn fpf = isJust . checkFPFn fpf

public export
MkFPFn : (fpf : FPFunctor) -> (bt : BinTreeMu Nat) ->
  {auto 0 valid : IsTrue $ validFPFn fpf bt} ->
  FPFTerm fpf
MkFPFn fpf bt {valid} with (checkFPFn fpf bt)
  MkFPFn fpf bt {valid} | Just t = t
  MkFPFn fpf bt {valid} | Nothing = void $ case valid of Refl impossible

-------------------------------------------------------
-------------------------------------------------------
---- Experiments with generalized pattern matching ----
-------------------------------------------------------
-------------------------------------------------------

------------------------------------------------------------------
---- Using an explicit structure representing a pattern-match ----
------------------------------------------------------------------

public export
BinTreeGenAlgF : Type -> Type -> Type -> Type
BinTreeGenAlgF atom a x = (BinTreeAlg atom a, Maybe x, Maybe x)

public export
BinTreeGenAlgAlg : Type -> Type -> Type -> Type
BinTreeGenAlgAlg = Algebra .* BinTreeGenAlgF

public export
data BinTreeGenAlg : Type -> Type -> Type where
  InBTGA : {0 atom, a : Type} ->
    BinTreeGenAlgF atom a (BinTreeGenAlg atom a) -> BinTreeGenAlg atom a

public export
binTreeGenCata :
  {0 atom, a : Type} -> BinTreeMu atom -> BinTreeGenAlg atom a -> a
binTreeGenCata (InBTm (Left ea)) (InBTGA (alg, _, _)) =
  alg $ Left ea
binTreeGenCata (InBTm (Right (bt1, bt2))) galg@(InBTGA (alg, m1, m2)) =
  let
    (alg1, alg2) = case (m1, m2) of
      (Nothing, Nothing) => (galg, galg)
      (Nothing, Just mt2) => (galg, mt2)
      (Just mt1, Nothing) => (mt1, galg)
      (Just mt1, Just mt2) => (mt1, mt2)
  in
  alg $ Right (binTreeGenCata bt1 alg1, binTreeGenCata bt2 alg2)

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

----------------------------------------------
----------------------------------------------
---- Dependent bifunctors and profunctors ----
----------------------------------------------
----------------------------------------------

public export
SliceBifunctor : Type -> Type -> Type -> Type
SliceBifunctor c d e = SliceObj c -> SliceObj d -> SliceObj e

public export
SliceEndoBifunctor : Type -> Type
SliceEndoBifunctor e = SliceBifunctor e e e

public export
SliceProfunctor : Type -> Type -> Type -> Type
SliceProfunctor = SliceBifunctor

public export
SliceEndoProfunctor : Type -> Type
SliceEndoProfunctor = SliceEndoBifunctor

---------------------------------------------------------
---------------------------------------------------------
---- Dependent polynomial bifunctors and profunctors ----
---------------------------------------------------------
---------------------------------------------------------

-- A dependent polynomial functor is defined between slice categories --
-- `Type/dom` -> `Type/cod`.  A dependent polynomial (non-enriched)
-- profunctor, therefore, should be from `Type/dom -> Type/cod -> Type`.
--
-- However, because a plain `Type` is now involved, we can add more
-- dependency in the profunctor case -- we could parameterize the whole
-- profunctor on a type `param`, so that `dom` and `cod` are now themselves
-- slices over `param`.
public export
DepProfunctor : {param : Type} -> (dom, cod : SliceObj param) -> Type
DepProfunctor {param} dom cod =
  (p : param) -> SliceObj (dom p) -> SliceObj (cod p) -> Type

public export
record DepArena (0 dom, cod : Type) where
  constructor DepAr
  darPos : SliceObj cod
  darDir : (elcod : cod) -> darPos elcod -> SliceObj dom

public export
InterpDepArGen : {dom, cod : Type} ->
  SliceBifunctor dom dom cod ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepArGen {dom} {cod} bf dar domsl elcod =
  (pos : darPos dar elcod ** bf (darDir dar elcod pos) domsl elcod)

public export
InterpDepAr : {dom, cod : Type} ->
  (dom -> cod -> Type -> Type -> Type) ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepAr {dom} {cod} bf dar domsl elcod =
  (pos : darPos dar elcod **
  (eldom : dom) -> bf eldom elcod (darDir dar elcod pos eldom) (domsl eldom))

public export
InterpDepArPoly : {dom, cod : Type} ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepArPoly = InterpDepAr $ \_, _ => ArrowT

public export
depArPolyMap : {dom, cod : Type} -> (dar : DepArena dom cod) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} x y ->
  SliceMorphism {a=cod}
    (InterpDepArPoly {dom} {cod} dar x) (InterpDepArPoly {dom} {cod} dar y)
depArPolyMap {dom} {cod} dar {x} {y} m elcod fx =
  (fst fx ** sliceComp m (snd fx))

public export
InterpDepArDirich : {dom, cod : Type} ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepArDirich = InterpDepAr $ \_, _ => OpArrowT

public export
depArDirichContramap : {dom, cod : Type} -> (dar : DepArena dom cod) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} y x ->
  SliceMorphism {a=cod}
    (InterpDepArDirich {dom} {cod} dar x) (InterpDepArDirich {dom} {cod} dar y)
depArDirichContramap {dom} {cod} dar {x} {y} m elcod fx =
  (fst fx ** sliceComp (snd fx) m)

public export
DepCopArena : (0 dom1, dom2, cod : Type) -> Type
DepCopArena dom1 dom2 cod = DepArena (Either dom1 dom2) cod

public export
InterpDepCopAr : {dom1, dom2, cod : Type} ->
  (dom1 -> cod -> Type -> Type -> Type) ->
  (dom2 -> cod -> Type -> Type -> Type) ->
  DepCopArena dom1 dom2 cod -> SliceBifunctor dom1 dom2 cod
InterpDepCopAr {dom1} {dom2} {cod} bf1 bf2 dbar dom1sl dom2sl =
  InterpDepAr {dom=(Either dom1 dom2)} {cod} (eitherElim bf1 bf2) dbar $
    eitherElim dom1sl dom2sl

public export
InterpDepCopArCovarPoly : {dom1, dom2, cod : Type} ->
  DepCopArena dom1 dom2 cod -> SliceBifunctor dom1 dom2 cod
InterpDepCopArCovarPoly {dom1} {dom2} {cod} =
  InterpDepCopAr (\_, _ => ArrowT) (\_, _ => ArrowT)

public export
depCopArCovarPolyMap : {dom1, dom2, cod : Type} ->
  (dar : DepCopArena dom1 dom2 cod) ->
  {x1, y1 : SliceObj dom1} ->
  {x2, y2 : SliceObj dom2} ->
  SliceMorphism {a=(Either dom1 dom2)} (eitherElim x1 x2) (eitherElim y1 y2) ->
  SliceMorphism {a=cod}
    (InterpDepCopArCovarPoly {dom1} {dom2} {cod} dar x1 x2)
    (InterpDepCopArCovarPoly {dom1} {dom2} {cod} dar y1 y2)
depCopArCovarPolyMap {dom1} {dom2} {cod} dar m elcod (pos ** dirmap) =
  (pos **
   \eldom => case eldom of
    Left ell => m (Left ell) . dirmap (Left ell)
    Right elr => m (Right elr) . dirmap (Right elr))

public export
InterpDepCopArPolyProf : {dom1, dom2, cod : Type} ->
  DepCopArena dom1 dom2 cod -> SliceProfunctor dom1 dom2 cod
InterpDepCopArPolyProf {dom1} {dom2} {cod} =
  InterpDepCopAr (\_, _ => OpArrowT) (\_, _ => ArrowT)

public export
depCopArPolyProfDimap : {dom1, dom2, cod : Type} ->
  (dar : DepCopArena dom1 dom2 cod) ->
  {x1, y1 : SliceObj dom1} ->
  {x2, y2 : SliceObj dom2} ->
  SliceMorphism {a=(Either dom1 dom2)} (eitherElim y1 x2) (eitherElim x1 y2) ->
  SliceMorphism {a=cod}
    (InterpDepCopArPolyProf {dom1} {dom2} {cod} dar x1 x2)
    (InterpDepCopArPolyProf {dom1} {dom2} {cod} dar y1 y2)
depCopArPolyProfDimap {dom1} {dom2} {cod} dar m elcod (pos ** dirmap) =
  (pos **
   \eldom => case eldom of
    Left ell => dirmap (Left ell) . m (Left ell)
    Right elr => m (Right elr) . dirmap (Right elr))

public export
DepProdArena : (0 dom, cod1, cod2 : Type) -> Type
DepProdArena dom cod1 cod2 = DepArena dom (Pair cod1 cod2)

public export
InterpDepProdAr : {dom, cod1, cod2 : Type} ->
  (dom -> (cod1, cod2) -> Type -> Type -> Type) ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdAr {dom} {cod1} {cod2} pf dbar =
  InterpDepAr {dom} {cod=(Pair cod1 cod2)} pf dbar

public export
InterpDepProdArPair : {dom, cod1, cod2 : Type} ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdArPair {dom} {cod1} {cod2} =
  InterpDepProdAr (\_, (_, _) => Pair)

public export
depProdArPairMap : {dom, cod1, cod2 : Type} ->
  (dar : DepProdArena dom cod1 cod2) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} x y ->
  SliceMorphism {a=(cod1, cod2)}
    (InterpDepProdArPair {dom} {cod1} {cod2} dar x)
    (InterpDepProdArPair {dom} {cod1} {cod2} dar y)
depProdArPairMap {dom} {cod1} {cod2} dar m (elcod1, elcod2) fx =
  (fst fx ** \eldom => mapSnd (m eldom) (snd fx eldom))

public export
InterpDepProdArCovarHom : {dom, cod1, cod2 : Type} ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdArCovarHom {dom} {cod1} {cod2} =
  InterpDepProdAr (\_, (_, _) => ArrowT)

public export
depProdArHomMap : {dom, cod1, cod2 : Type} ->
  (dar : DepProdArena dom cod1 cod2) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} x y ->
  SliceMorphism {a=(cod1, cod2)}
    (InterpDepProdArCovarHom {dom} {cod1} {cod2} dar x)
    (InterpDepProdArCovarHom {dom} {cod1} {cod2} dar y)
depProdArHomMap {dom} {cod1} {cod2} dar m (elcod1, elcod2) fx =
  (fst fx ** \eldom, ely => m eldom $ snd fx eldom ely)

public export
InterpDepProdArContraHom : {dom, cod1, cod2 : Type} ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdArContraHom {dom} {cod1} {cod2} =
  InterpDepProdAr (\_, (_, _) => OpArrowT)

public export
depProdArHomContramap : {dom, cod1, cod2 : Type} ->
  (dar : DepProdArena dom cod1 cod2) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} y x ->
  SliceMorphism {a=(cod1, cod2)}
    (InterpDepProdArContraHom {dom} {cod1} {cod2} dar x)
    (InterpDepProdArContraHom {dom} {cod1} {cod2} dar y)
depProdArHomContramap {dom} {cod1} {cod2} dar m (elcod1, elcod2) fx =
  (fst fx ** \eldom, ely => snd fx eldom $ m eldom ely)

------------------------
------------------------
---- Quotient types ----
------------------------
------------------------

-- A quotient type is a type together with a relation which we shall
-- implicitly treat (when defining the morphisms of the category of
-- quotientable types) as an equivalence relation.
public export
QType : Type
QType = Subset0 Type RelationOn

public export
QBase : QType -> Type
QBase = fst0

public export
0 QBaseRel : (0 x : QType) -> RelationOn (QBase x)
QBaseRel x = snd0 x

public export
0 QEffRel : (0 x : QType) -> RelationOn (QBase x)
QEffRel x = curry $ FreePrEquivF (uncurry $ QBaseRel x)

public export
QFunc : QType -> QType -> Type
QFunc x y = QBase x -> QBase y

public export
0 QPres : (0 x, y : QType) -> SliceObj (QFunc x y)
QPres x y f =
  PrERelPres {a=(QBase x)} {b=(QBase y)}
    f (uncurry $ QEffRel x) (uncurry $ QEffRel y)

public export
QMorph : QType -> QType -> Type
QMorph x y = Subset0 (QFunc x y) (QPres x y)

public export
QMorphBase : {0 x, y : QType} -> QMorph x y -> QBase x -> QBase y
QMorphBase = fst0

public export
0 QMorphPres : {0 x, y : QType} ->
  (f : QMorph x y) -> QPres x y (QMorphBase {x} {y} f)
QMorphPres = snd0

public export
0 QKPres : (0 x, y : QType) -> SliceObj (QFunc x y)
QKPres x y f =
  PrERelPres {a=(QBase x)} {b=(QBase y)}
    f (uncurry $ QBaseRel x) (uncurry $ QEffRel y)

-- Using the Kleisli category of the free equivalence monad, we can generate
-- quotientable-type morphisms by showing only that _base_-related elements
-- are mapped to _closure_-related elements (we do not have to show explicitly
-- that all _closure_-related elements are mapped to closure-related elements).
public export
0 QKBind : {0 x, y : QType} -> {0 f : QFunc x y} -> QKPres x y f -> QPres x y f
QKBind {x=(Element0 x rx)} {y=(Element0 y ry)} {f} =
  freeEquivBindPres {a=x} {b=y} {ra=(uncurry rx)} {rb=(uncurry ry)} {f}

public export
QMkMorph : {0 x, y : QType} -> {f : QFunc x y} -> (0 _ : QKPres x y f) ->
  QMorph x y
QMkMorph {x} {y} {f} pres = Element0 f (QKBind {x} {y} {f} pres)

-- We can form an equivalence relation on `QType` itself which states that
-- two `QType`s are equivalent if they have the same underlying type and
-- their equivalence relations are equivalent.  This equivalence relation is
-- therefore using the notion of equivalence relation to "hide" the witnesses
-- of equivalence relations themselves.  (It is introducing a proof-irrelevant
-- layer on top of proof-relevant relations.)
public export
data QTEquiv : RelationOn QType where
  QTE : {0 x : Type} -> {0 r, r' : RelationOn x} ->
    PrRelBiImp (uncurry r) (uncurry r') ->
    QTEquiv (Element0 x r) (Element0 x r')

-- Using `QTEquiv`, we can make `QType` itself a `QType`.
public export
QTypeQT : QType
QTypeQT = Element0 QType QTEquiv

-- We can also define an extensional equality on morphisms of `QType`.
public export
0 QMExtEq : {0 x, y : QType} -> QMorph x y -> QMorph x y -> Type
QMExtEq {x} {y} f g =
  PrERelBiPres {a=(QBase x)} {b=(QBase y)}
    (QMorphBase f) (QMorphBase g) (uncurry $ QEffRel x) (uncurry $ QEffRel y)

-- This type represents that two `QType` morphisms agree (up to codomain
-- equivalence) on intensionally equal elements of the domain.
public export
0 QMIntExt : {0 x, y : QType} -> (f, g : QMorph x y) -> Type
QMIntExt {x} {y} f g =
  (ex : QBase x) ->
    QEffRel y (QMorphBase {x} {y} f ex) (QMorphBase {x} {y} g ex)

-- To show that `QType` morphisms are extensionally equal, we only need to
-- show that they agree (up to codomain equivalence) on _intensionally_
-- equal elements of the domain.
public export
0 MkQMExtEq : {0 x, y : QType} -> {f, g : QMorph x y} ->
  QMIntExt {x} {y} f g -> QMExtEq {x} {y} f g
MkQMExtEq {x} {y} {f} {g} exteq =
  PresEqRel
    {a=(QBase x)} {b=(QBase y)} {f=(QMorphBase f)} {g=(QMorphBase g)}
    {ra=(uncurry $ QBaseRel x)} {rb=(uncurry $ QBaseRel y)}
    (\ea, ea', eqa => QMorphPres g ea ea' $ InSlFv eqa)
    (\ea, ea', Refl => exteq ea)

-- Using the notion of extensional equality on QType morphisms (up to the
-- equivalences embedded within the types), we can define the hom-set of
-- of any two `QType`s within `QType` itself, thus making `QType` Cartesian
-- closed.
public export
QMHom : QType -> QType -> QType
QMHom x y = Element0 (QMorph x y) (QMExtEq {x} {y})

public export
QMExp : QType -> QType -> QType
QMExp = flip QMHom
