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

-----------------------------------------------
-----------------------------------------------
---- Categories defined via slice algebras ----
-----------------------------------------------
-----------------------------------------------

-----------------
---- Quivers ----
-----------------

public export
Quiver : Type
Quiver = PreDiagram

public export
qVert : SliceObj Quiver
qVert = pdVert

public export
qSig : SliceObj Quiver
qSig = SignatureT . qVert

public export
QHomSlice : SliceObj Quiver
QHomSlice = HomSlice . qVert

public export
qEdge : Pi {a=Quiver} QHomSlice
qEdge = pdEdge

-- A notion of identity and composition on a quiver.
public export
QuiverIC : SliceObj Quiver
QuiverIC q = SliceAlg CatHomF (qEdge q)

-- A notion of a relation on the edges of a quiver.
public export
QuivEdgeRel : SliceObj Quiver
QuivEdgeRel q = Pi {a=(qSig q)} (PrERel . qEdge q)

--------------------
---- Categories ----
--------------------

-- A quiver with notions of identity, composition, and congruence --
-- which suffice to form the data of a category, but does not contain
-- proofs of the category laws.
public export
record CatData where
  constructor CatD
  cdQuiv : Quiver
  cdIdComp : QuiverIC cdQuiv
  cdCong : QuivEdgeRel cdQuiv

public export
cdObj : SliceObj CatData
cdObj = qVert . cdQuiv

public export
cdSig : SliceObj CatData
cdSig = qSig . cdQuiv

public export
CDHomSlice : SliceObj CatData
CDHomSlice = QHomSlice . cdQuiv

public export
cdHom : Pi {a=CatData} CDHomSlice
cdHom cd = qEdge $ cdQuiv cd

public export
CDIC : SliceObj CatData
CDIC = QuiverIC . cdQuiv

public export
cdIdSig : SliceObj CatData
cdIdSig cd = (x : cdObj cd) -> cdHom cd (x, x)

public export
cdId : (cd : CatData) -> cdIdSig cd
cdId cd x = cdIdComp cd (x, x) $ CHId {hom=(cdHom cd)} x

public export
cdCompSig : SliceObj CatData
cdCompSig cd = (x, y, z : cdObj cd) ->
  cdHom cd (y, z) -> cdHom cd (x, y) -> cdHom cd (x, z)

public export
cdComp : (cd : CatData) -> cdCompSig cd
cdComp cd x y z g f = cdIdComp cd (x, z) $ CHComp {hom=(cdHom cd)} g f

public export
cdPipeSig : SliceObj CatData
cdPipeSig cd = (x, y, z : cdObj cd) ->
  cdHom cd (x, y) -> cdHom cd (y, z) -> cdHom cd (x, z)

public export
cdPipe : (cd : CatData) -> cdPipeSig cd
cdPipe cd x y z = flip (cdComp cd x y z)

infixr 1 <#
public export
(<#) : {cd : CatData} -> {x, y, z : cdObj cd} ->
  cdHom cd (y, z) -> cdHom cd (x, y) -> cdHom cd (x, z)
(<#) {cd} {x} {y} {z} = cdComp cd x y z

infixr 1 |>
public export
(#>) : {cd : CatData} -> {x, y, z : cdObj cd} ->
  cdHom cd (x, y) -> cdHom cd (y, z) -> cdHom cd (x, z)
(#>) {cd} {x} {y} {z} = cdPipe cd x y z

public export
0 CatEquivLaw : SliceObj CatData
CatEquivLaw cd = (xy : cdSig cd) -> PrEquivRelI (cdHom cd xy) (cdCong cd xy)

public export
0 CatLeftIdLaw : SliceObj CatData
CatLeftIdLaw cd =
  (x, y : cdObj cd) -> (f : cdHom cd (x, y)) ->
  cdCong cd (x, y) (cdComp cd x y y (cdId cd y) f, f)

public export
0 CatRightIdLaw : SliceObj CatData
CatRightIdLaw cd =
  (x, y : cdObj cd) -> (f : cdHom cd (x, y)) ->
  cdCong cd (x, y) (cdComp cd x x y f (cdId cd x), f)

public export
0 CatAssocLaw : SliceObj CatData
CatAssocLaw cd =
  (w, x, y, z : cdObj cd) ->
  (f : cdHom cd (w, x)) -> (g : cdHom cd (x, y)) -> (h : cdHom cd (y, z)) ->
  cdCong cd (w, z)
    (cdComp cd w x z (cdComp cd x y z h g) f,
     cdComp cd w y z h (cdComp cd w x y g f))

-- A type representing that a given `CatData` obeys the laws of a category.
-- This could be viewed as stating that the relation on the edges is a
-- congruence.
public export
record CatDataLawful (cd : CatData) where
  constructor CatLaws
  0 catLawEquiv : CatEquivLaw cd
  0 catLawIdL : CatLeftIdLaw cd
  0 catLawIdR : CatRightIdLaw cd
  0 catLawIdAssoc : CatAssocLaw cd

-- A proven category, with underlying data and proofs of the laws.
public export
record LawfulCat where
  constructor LCat
  lcData : CatData
  0 lcLawful : CatDataLawful lcData

public export
lcObj : SliceObj LawfulCat
lcObj = cdObj . lcData

public export
lcSig : SliceObj LawfulCat
lcSig = cdSig . lcData

public export
LCHomSlice : SliceObj LawfulCat
LCHomSlice = CDHomSlice . lcData

public export
lcHom : Pi {a=LawfulCat} LCHomSlice
lcHom lc = cdHom $ lcData lc

public export
LCIC : SliceObj LawfulCat
LCIC = CDIC . lcData

public export
lcIdSig : SliceObj LawfulCat
lcIdSig = cdIdSig . lcData

public export
lcId : (lc : LawfulCat) -> lcIdSig lc
lcId lc = cdId (lcData lc)

public export
lcCompSig : SliceObj LawfulCat
lcCompSig = cdCompSig . lcData

public export
lcComp : (lc : LawfulCat) -> lcCompSig lc
lcComp lc = cdComp (lcData lc)

public export
lcPipeSig : SliceObj LawfulCat
lcPipeSig = cdPipeSig . lcData

public export
lcPipe : (lc : LawfulCat) -> lcPipeSig lc
lcPipe lc x y z = flip (lcComp lc x y z)

infixr 1 <!
public export
(<!) : {lc : LawfulCat} -> {x, y, z : lcObj lc} ->
  lcHom lc (y, z) -> lcHom lc (x, y) -> lcHom lc (x, z)
(<!) {lc} {x} {y} {z} = lcComp lc x y z

infixr 1 !>
public export
(!>) : {lc : LawfulCat} -> {x, y, z : lcObj lc} ->
  lcHom lc (x, y) -> lcHom lc (y, z) -> lcHom lc (x, z)
(!>) {lc} {x} {y} {z} = lcPipe lc x y z

------------------
---- Functors ----
------------------

public export
FunctorSig : Type
FunctorSig = SignatureT CatData

public export
ObjMap : SliceObj FunctorSig
ObjMap sig = cdObj (fst sig) -> cdObj (snd sig)

public export
MorphMap : (sig : FunctorSig) -> SliceObj (ObjMap sig)
MorphMap sig fo = (x, y : cdObj $ fst sig) ->
  cdHom (fst sig) (x, y) -> cdHom (snd sig) (fo x, fo y)

public export
record FunctorData (sig : FunctorSig) where
  constructor FunctorD
  fdOmap : ObjMap sig
  fdMmap : MorphMap sig fdOmap

public export
0 FunctorIdLaw : (sig : FunctorSig) -> SliceObj (FunctorData sig)
FunctorIdLaw sig fd =
  (x : cdObj $ fst sig) ->
  cdCong (snd sig) (fdOmap fd x, fdOmap fd x)
    (cdId (snd sig) (fdOmap fd x), fdMmap fd x x (cdId (fst sig) x))

public export
0 FunctorCompLaw : (sig : FunctorSig) -> SliceObj (FunctorData sig)
FunctorCompLaw sig fd = (x, y, z : cdObj $ fst sig) ->
  (g : cdHom (fst sig) (y, z)) -> (f : cdHom (fst sig) (x, y)) ->
  cdCong (snd sig) (fdOmap fd x, fdOmap fd z)
    (fdMmap fd x z (g <# f), fdMmap fd y z g <# fdMmap fd x y f)

public export
record FunctorDataLawful {sig : FunctorSig} (fd : FunctorData sig) where
  constructor FunctorLaws
  0 funcLawId : FunctorIdLaw sig fd
  0 funcLawComp : FunctorCompLaw sig fd

public export
record LawfulFunctor (sig : FunctorSig) where
  constructor LFunc
  lfData : FunctorData sig
  0 lfLawful : FunctorDataLawful lfData

---------------------------------------------------
---- Two-categories with functors as morphisms ----
---------------------------------------------------

---------------------------------
---- Natural transformations ----
---------------------------------

public export
NTSig : Type
NTSig = DPair FunctorSig (SignatureT . FunctorData)

public export
NTcdata : NTSig -> SignatureT CatData
NTcdata = fst

public export
NTcdom : NTSig -> CatData
NTcdom = fst . NTcdata

public export
NTccod : NTSig -> CatData
NTccod = snd . NTcdata

public export
NTfdom : (sig : NTSig) -> FunctorData $ NTcdata sig
NTfdom sig = fst $ snd sig

public export
NTfcod : (sig : NTSig) -> FunctorData $ NTcdata sig
NTfcod sig = snd $ snd sig

public export
NTComponentSig : SliceObj NTSig
NTComponentSig sig = (x : cdObj $ NTcdom sig) ->
  cdHom (NTccod sig) (fdOmap (NTfdom sig) x, fdOmap (NTfcod sig) x)

public export
record NTData (sig : NTSig) where
  constructor NTD
  ntdC : NTComponentSig sig

public export
0 NaturalityLaw : (sig : NTSig) -> SliceObj (NTData sig)
NaturalityLaw sig ntd =
  (x, y : cdObj $ NTcdom sig) -> (m : cdHom (NTcdom sig) (x, y)) ->
  cdCong (NTccod sig) (fdOmap (NTfdom sig) x, fdOmap (NTfcod sig) y)
    (fdMmap (NTfcod sig) x y m <# ntdC ntd x,
     ntdC ntd y <# fdMmap (NTfdom sig) x y m)

public export
record NTDataLawful {sig : NTSig} (ntd : NTData sig) where
  constructor NTLaws
  0 ntLawNatural : NaturalityLaw sig ntd

public export
record LawfulNT (sig : NTSig) where
  constructor LNT
  lntData : NTData sig
  0 lntLawful : NTDataLawful lntData

-----------------------------------------
-----------------------------------------
---- Internal representable functors ----
-----------------------------------------
-----------------------------------------

public export
algLift :
  (0 f : Type -> Type) -> (fm : (0 x, y : Type) -> (x -> y) -> f x -> f y) ->
  {0 a, b : Type} -> (m : Algebra f b) -> (h : a -> b) -> f a -> b
algLift f fm {a} {b} = (|>) (fm a b) . (.)

{-
  Suppose the following:

    - `f` is an endofunctor in `Type`
    - `c` and `p` form an algebra of `f` (`c` is the object; `m`
      is the morphism)
    - `a` and `b` are the types of objects of two categories (we shall also
      refer to the those categories themselves as `a` and `b`)
    - `h` is a profunctor `a |-> b` enriched over a third category, whose
      objects are of type `c` (we shall also refer to that category itself
      as `c`) -- that is, a functor from `(op(b), a)` to `c` (the `h` is meant
      to suggest `hom-(pro)functor`)

  Under those conditions, we can produce a hom-profunctor `a |-> f(b)` where
  `f(b)` is the image of `b` under `f`.

  In particular, for example, if `f` is `ProductMonad` and `b` is `a`, then
  this takes an endoprofunctor `h` on `a` and generates a hom-functor internal
  to `c` extended by a covariant hom-functor represented by a pairwise
  coproduct in `a`.
-}
public export
covarHomProfuncLift :
  (0 f : Type -> Type) -> (fm : (0 x, y : Type) -> (x -> y) -> f x -> f y) ->
  {0 a, b, c : Type} -> (m : Algebra f c) -> (h : b -> a -> c) -> f b -> a -> c
covarHomProfuncLift f fm {a} {b} {c} =
  (|>) ((|>) . flip) . (|>) . flip . algLift f fm {a=b} {b=c}

{-
  Dually to `covarHomLift`, this produces a hom-profunctor `f(a) |-> b`
  by extending the contravariant component.
-}
public export
contravarHomProfuncLift :
  (0 f : Type -> Type) -> (fm : (0 x, y : Type) -> (x -> y) -> f x -> f y) ->
  {0 a, b, c : Type} -> (m : Algebra f c) -> (h : b -> a -> c) -> b -> f a -> c
contravarHomProfuncLift f fm {a} {b} {c} =
  (.) . algLift f fm {a} {b=c}

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

public export
SliceObjEither : {0 param : Type} ->
  (dom, cod : SliceObj param) -> SliceObj param
SliceObjEither {param} dom cod ep = SliceObj (Either (dom ep) (cod ep))

-- A dependent polynomial functor is defined between slice categories --
-- `Type/dom` -> `Type/cod`.  A dependent polynomial (non-enriched)
-- profunctor, therefore, should be from `Type/dom -> Type/cod -> Type`.
--
-- However, we can add further dependency by defining in effect a family
-- of profunctors indexed by a type `param`, where each of the domain, codomain,
-- and enriching categories depend on `param`.
public export
DepProfunctor : {param : Type} -> (dom, cod, enr : SliceObj param) -> Type
DepProfunctor {param} dom cod enr =
  SliceMorphism {a=param} (SliceObjEither {param} dom cod) enr

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
InterpDepArPoly = InterpDepAr $ \_, _ => HomProf

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
InterpDepArDirich = InterpDepAr $ \_, _ => OpHomProf

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
  InterpDepCopAr (\_, _ => HomProf) (\_, _ => HomProf)

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
  InterpDepCopAr (\_, _ => OpHomProf) (\_, _ => HomProf)

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
  InterpDepProdAr (\_, (_, _) => HomProf)

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
  InterpDepProdAr (\_, (_, _) => OpHomProf)

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

---------------------
---- Definitions ----
---------------------

-- A quotient type is a type together with an equivalence relation.
public export
QType : Type
QType = Subset0 Type PrEquivRel

public export
QBase : QType -> Type
QBase = fst0

public export
0 QRel : (0 x : QType) -> PrEquivRel (QBase x)
QRel x = snd0 x

public export
0 QBaseRel : (0 x : QType) -> PrERel (QBase x)
QBaseRel x = fst (QRel x)

public export
0 QRelEquivI : (0 x : QType) -> PrEquivRelI (QBase x) (QBaseRel x)
QRelEquivI x = snd (QRel x)

public export
QFunc : QType -> QType -> Type
QFunc x y = QBase x -> QBase y

public export
0 QPres : (0 x, y : QType) -> SliceObj (QFunc x y)
QPres x y f = PrERelPres {a=(QBase x)} {b=(QBase y)} f (QBaseRel x) (QBaseRel y)

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


-----------------------------------------
---- Self-internalization of `QType` ----
-----------------------------------------

-- We can form an equivalence relation on `QType` itself which states that
-- two `QType`s are equivalent if they have the same underlying type and
-- their equivalence relations are equivalent.  This equivalence relation is
-- therefore using the notion of equivalence relation to "hide" the witnesses
-- of equivalence relations themselves.  (It is introducing a proof-irrelevant
-- layer on top of proof-relevant relations.)
public export
data QTEquiv : PrERel QType where
  QTE : {0 x : Type} -> {0 r, r' : PrEquivRel x} ->
    (0 _ : PrRelBiImp (fst r) (fst r')) -> QTEquiv (Element0 x r, Element0 x r')

-- `QTEquiv` is an equivalence relation.
public export
QTEquivEquivI : PrEquivRelI QType QTEquiv
QTEquivEquivI
  (Element0 x r, Element0 x r) (PrErefl _) =
    QTE $ PrEquivRefl (BiImpEquivERel x) (fst r)
QTEquivEquivI
  (Element0 x r, Element0 x r') (PrEsym _ _ (QTE eq)) =
    QTE $ PrEquivSym {ea=(fst r')} {ea'=(fst r)} (BiImpEquivERel x) eq
QTEquivEquivI
  (Element0 x r, Element0 x r')
  (PrEtrans (Element0 x r) (Element0 x r'') (Element0 x r')
    (QTE eq) (QTE eq')) =
      QTE $ PrEquivTrans {ea=(fst r)} {ea'=(fst r'')} {ea''=(fst r')}
        (BiImpEquivERel x) eq eq'

public export
QTEquivEquiv : PrEquivRel QType
QTEquivEquiv = (QTEquiv ** QTEquivEquivI)

-- Between any two `QTEquiv`-equivalent types, there is an isomorphism
-- whose underlying function is the identity.
public export
QTEqIso : {0 x, y : QType} -> QTEquiv (x, y) -> QMorph x y
QTEqIso (QTE imp) = Element0 id $ fst imp

-- Using `QTEquiv`, we can make `QType` itself a `QType`.
public export
QTypeQT : QType
QTypeQT = Element0 QType QTEquivEquiv

-- We can also define an extensional equality on morphisms of `QType`.
public export
0 QMExtEq : {0 x, y : QType} -> PrERel (QMorph x y)
QMExtEq {x} {y} (f, g) =
  PrERelBiPres {a=(QBase x)} {b=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

-- `QMExtEq` is an equivalence relation.
public export
0 QMExtEqEquivI : {0 x, y : QType} -> PrEquivRelI (QMorph x y) (QMExtEq {x} {y})
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 f fpres) (PrErefl _) =
    fpres
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 g gpres) (PrEsym _ _ r) =
    \ex, ex', rex =>
      eqy (f ex, g ex') $ PrEtrans (f ex) (g ex) (g ex') (gpres ex ex' rex)
      $ eqy (f ex, g ex) $ PrEtrans (f ex) (f ex') (g ex)
      (eqy (f ex', g ex) $ PrEsym (g ex) (f ex') $ r ex ex' rex)
      $ fpres ex ex' rex
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 g gpres) (PrEtrans _ (Element0 h hpres) _ r r') =
    \ex, ex', rex =>
      eqy (f ex, g ex') $ PrEtrans (f ex) (g ex) (g ex') (gpres ex ex' rex)
      $ eqy (f ex, g ex) $ PrEtrans (f ex) (h ex') (g ex)
      (eqy (h ex', g ex) $ PrEtrans (h ex') (g ex') (g ex)
        (eqy (g ex', g ex) $ PrEsym (g ex) (g ex') $ gpres ex ex' rex)
        (eqy (h ex', g ex') $ PrEtrans (h ex') (h ex) (g ex')
          (r ex ex' rex)
          $ eqy (h ex', h ex) $ PrEsym (h ex) (h ex') $ hpres ex ex' rex))
      $ r' ex ex' rex

public export
0 QMExtEqEquiv : (0 x, y : QType) -> PrEquivRel (QMorph x y)
QMExtEqEquiv x y = (QMExtEq {x} {y} ** QMExtEqEquivI {x} {y})

-- This type represents that two `QType` morphisms agree (up to codomain
-- equivalence) on intensionally equal elements of the domain.
public export
0 QMIntExt : {0 x, y : QType} -> PrERel (QMorph x y)
QMIntExt {x} {y} (f, g) = PrERelIntExt {a=(QBase x)} {b=(QBase y)}
  (QMorphBase f) (QMorphBase g) (QBaseRel y)

-- To show that `QType` morphisms are extensionally equal, we only need to
-- show that they agree (up to codomain equivalence) on _intensionally_
-- equal elements of the domain.
public export
0 MkQMExtEq : {0 x, y : QType} -> {f, g : QMorph x y} ->
  QMIntExt {x} {y} (f, g) -> QMExtEq {x} {y} (f, g)
MkQMExtEq {x} {y} {f} {g} intext =
  PresEqRel
    {a=(QBase x)} {b=(QBase y)}
    {f=(QMorphBase f)} {g=(QMorphBase g)}
    {ra=(QBaseRel x)} {rb=(QRel y)}
    (QMorphPres g) intext

-- In particular, if two `QType` morphisms' base morphisms are extensionally
-- equal, then the `QType` morphisms are equivalent under `QMExtEq`.
public export
0 QMEqFromExt : {0 x, y : QType} -> {f, g : QMorph x y} ->
  ExtEq {a=(QBase x)} {b=(QBase y)}
    (QMorphBase {x} {y} f) (QMorphBase {x} {y} g) ->
  QMExtEq {x} {y} (f, g)
QMEqFromExt {x} {y} {f} {g} eq = MkQMExtEq {x} {y} {f} {g} $
  \_, ea, Refl => rewrite eq ea in PrEquivRefl (snd0 y) $ fst0 g ea

public export
qmId : (a : QType) -> QMorph a a
qmId a = Element0 (id {a=(QBase a)}) $ \_, _ => id

public export
qmComp : {a, b, c : QType} -> QMorph b c -> QMorph a b -> QMorph a c
qmComp {a} {b} {c} g f =
  Element0 (QMorphBase g . QMorphBase f) $ \ea, ea', aeq =>
    QMorphPres g (QMorphBase f ea) (QMorphBase f ea') $ QMorphPres f ea ea' aeq

public export
qmPipe : {a, b, c : QType} -> QMorph a b -> QMorph b c -> QMorph a c
qmPipe {a} {b} {c} = flip $ qmComp {a} {b} {c}

----------------------------------------------------------------------------
---- `QType` as category (with explicit equivalence) internal to `Type` ----
----------------------------------------------------------------------------

public export
0 QTFreeEqRel : (sig : SignatureT QType) -> EqRel (uncurry QMorph sig)
QTFreeEqRel (_, _) =
  MkEq (curry QMExtEq) $ EquivItoIsEquiv QMExtEq QMExtEqEquivI

public export
0 QTidL : {0 a, b : QType} -> (f : QMorph a b) ->
  eqRel (QTFreeEqRel (a, b)) f (qmComp {a} {b} {c=b} (qmId b) f)
QTidL = snd0

public export
0 QTidR : {0 a, b : QType} -> (f : QMorph a b) ->
  eqRel (QTFreeEqRel (a, b)) f (qmComp {a} {b=a} {c=b} f (qmId a))
QTidR = snd0

public export
0 QTassoc : {0 a, b, c, d : QType} ->
  (f : QMorph a b) -> (g : QMorph b c) -> (h : QMorph c d) ->
  eqRel (QTFreeEqRel (a, d))
    (qmComp {a} {b=c} {c=d} h $ qmComp {a} {b} {c} g f)
    (qmComp {a} {b} {c=d} (qmComp {a=b} {b=c} {c=d} h g) f)
QTassoc (Element0 f fpres) (Element0 g gpres) (Element0 h hpres) ea ea' =
  hpres (g $ f ea) (g $ f ea') . gpres (f ea) (f ea') . fpres ea ea'

-- This definition shows that the objects of `QType` with the morphisms
-- of `QMorph` quotiented by `QMExtEq` form a category, with identity and
-- composition given by `qmId` and `qmComp`.

public export
0 QTSCat : SCat
QTSCat = SC
  QType
  (uncurry QMorph)
  qmId
  qmComp
  QTFreeEqRel
  QTidL
  QTidR
  QTassoc

public export
0 QTDCat : Diagram
QTDCat = catToDiagForget QTSCat

----------------------------------------------------
----------------------------------------------------
---- Universal objects and morphisms in `QType` ----
----------------------------------------------------
----------------------------------------------------

-----------------
---- Initial ----
-----------------

public export
QInitBase : Type
QInitBase = Void

public export
0 QInitBaseRel : PrERel QInitBase
QInitBaseRel (v, v') = void v

public export
0 QInitBaseRelEquivI : PrEquivRelI QInitBase QInitBaseRel
QInitBaseRelEquivI (v, v') _ = void v

public export
0 QInitRel : PrEquivRel QInitBase
QInitRel = (QInitBaseRel ** QInitBaseRelEquivI)

public export
QInit : QType
QInit = Element0 QInitBase QInitRel

public export
qInitBase : (x : QType) -> QInitBase -> QBase x
qInitBase x v = void v

public export
QInitPres : (x : QType) -> QPres QInit x (qInitBase x)
QInitPres x v = void v

public export
qInit : (x : QType) -> QMorph QInit x
qInit x = Element0 (qInitBase x) (QInitPres x)

------------------
---- Terminal ----
------------------

public export
QTermBase : Type
QTermBase = Unit

public export
0 QTermBaseRel : PrERel QTermBase
QTermBaseRel ((), ()) = Unit

public export
0 QTermBaseRelEquivI : PrEquivRelI QTermBase QTermBaseRel
QTermBaseRelEquivI ((), ()) eq = ()

public export
0 QTermRel : PrEquivRel QTermBase
QTermRel = (QTermBaseRel ** QTermBaseRelEquivI)

public export
QTerm : QType
QTerm = Element0 QTermBase QTermRel

public export
qTermBase : (x : QType) -> QBase x -> QTermBase
qTermBase x ex = ()

public export
0 QTermPres : (x : QType) -> QPres x QTerm (qTermBase x)
QTermPres x ex ex' eqx = ()

public export
qTerm : (x : QType) -> QMorph x QTerm
qTerm x = Element0 (qTermBase x) (QTermPres x)

-------------------
---- Coproduct ----
-------------------

public export
QCoproductBase : (x, y : QType) -> Type
QCoproductBase x y = Either (QBase x) (QBase y)

public export
0 QCoproductBaseRel : (x, y : QType) -> PrERel (QCoproductBase x y)
QCoproductBaseRel x y exy =
  case exy of
    (Left ex, Left ex') => QBaseRel x (ex, ex')
    (Right ey, Right ey') => QBaseRel y (ey, ey')
    _ => Void

public export
0 QCoproductBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QCoproductBase x y) (QCoproductBaseRel x y)
QCoproductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) exyp exypeq =
  case exyp of
    (Left ex, Left ex') => case exypeq of
      PrErefl _ => PrEquivRefl xeq ex
      PrEsym _ _ r => PrEquivSym xeq r
      PrEtrans _ (Left ex'') _ r r' => PrEquivTrans xeq r r'
      PrEtrans _ (Right ey) _ r r' => void r
    (Left ex, Right ey) => case exypeq of
      PrErefl _ impossible
      PrEsym _ _ r => void r
      PrEtrans _ (Left ex'') _ r r' => void r
      PrEtrans _ (Right ey) _ r r' => void r'
    (Right ey, Left ex) => case exypeq of
      PrErefl _ impossible
      PrEsym _ _ r => void r
      PrEtrans _ (Left ex'') _ r r' => void r'
      PrEtrans _ (Right ey) _ r r' => void r
    (Right ey, Right ey') => case exypeq of
      PrErefl _ => PrEquivRefl yeq ey
      PrEsym _ _ r => PrEquivSym yeq r
      PrEtrans _ (Left ex'') _ r r' => void r'
      PrEtrans _ (Right ey) _ r r' => PrEquivTrans yeq r r'

public export
0 QCoproductRel : (x, y : QType) -> PrEquivRel (QCoproductBase x y)
QCoproductRel x y = (QCoproductBaseRel x y ** QCoproductBaseRelEquivI x y)

public export
QCoproduct : QType -> QType -> QType
QCoproduct x y = Element0 (QCoproductBase x y) (QCoproductRel x y)

public export
qInjLBase : (0 x, y : QType) -> QBase x -> QCoproductBase x y
qInjLBase x y = Left

public export
0 QInjLPres : (0 x, y : QType) -> QPres x (QCoproduct x y) (qInjLBase x y)
QInjLPres x y _ _ = id

public export
qInjL : (0 x, y : QType) -> QMorph x (QCoproduct x y)
qInjL x y = Element0 (qInjLBase x y) (QInjLPres x y)

public export
qInjRBase : (0 x, y : QType) -> QBase y -> QCoproductBase x y
qInjRBase x y = Right

public export
0 QInjRPres : (0 x, y : QType) -> QPres y (QCoproduct x y) (qInjRBase x y)
QInjRPres x y _ _ = id

public export
qInjR : (0 x, y : QType) -> QMorph y (QCoproduct x y)
qInjR x y = Element0 (qInjRBase x y) (QInjRPres x y)

public export
qCaseBase : {0 x, y, z : QType} ->
   QMorph x z -> QMorph y z -> QCoproductBase x y -> QBase z
qCaseBase f g = eitherElim (QMorphBase f) (QMorphBase g)

public export
0 QCasePres : {0 x, y, z : QType} ->
   (f : QMorph x z) -> (g : QMorph y z) ->
   QPres (QCoproduct x y) z (qCaseBase {x} {y} {z} f g)
QCasePres f g (Left ex) (Left ex') = QMorphPres f ex ex'
QCasePres f g (Left ex) (Right ey) = \v => void v
QCasePres f g (Right ey) (Left ex) = \v => void v
QCasePres f g (Right ey) (Right ey') = QMorphPres g ey ey'

public export
qCase : {0 x, y, z : QType} ->
  QMorph x z -> QMorph y z -> QMorph (QCoproduct x y) z
qCase f g = Element0 (qCaseBase f g) (QCasePres f g)

public export
qCoproductBimap : {w, x, y, z : QType} ->
  QMorph w y -> QMorph x z -> QMorph (QCoproduct w x) (QCoproduct y z)
qCoproductBimap {w} {x} {y} {z} f g =
  qCase {x=w} {y=x} {z=(QCoproduct y z)}
    (qmComp (qInjL y z) f) (qmComp (qInjR y z) g)

public export
qCoproductMapFst : {w, x, y : QType} ->
  QMorph w y -> QMorph (QCoproduct w x) (QCoproduct y x)
qCoproductMapFst {w} {x} {y} = flip (qCoproductBimap {w} {x} {y} {z=x}) (qmId x)

public export
qCoproductMapSnd : {w, x, y : QType} ->
  QMorph w x -> QMorph (QCoproduct y w) (QCoproduct y x)
qCoproductMapSnd {w} {x} {y} = qCoproductBimap {w=y} {x=w} {y} {z=x} (qmId y)

-----------------
---- Product ----
-----------------

public export
QProductBase : (x, y : QType) -> Type
QProductBase x y = (QBase x, QBase y)

public export
0 QProductBaseRel : (x, y : QType) -> PrERel (QProductBase x y)
QProductBaseRel x y (pxy, pxy') =
  (QBaseRel x (fst pxy, fst pxy'), QBaseRel y (snd pxy, snd pxy'))

public export
0 QProductBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QProductBase x y) (QProductBaseRel x y)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex, ey))
  (PrErefl _) =
    (PrEquivRefl xeq ex, PrEquivRefl yeq ey)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex', ey'))
  (PrEsym _ _ (rx, ry)) =
    (PrEquivSym xeq rx, PrEquivSym yeq ry)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex', ey'))
  (PrEtrans _ (ex'', ey'') _ (rx, ry) (rx', ry')) =
    (PrEquivTrans xeq rx rx', PrEquivTrans yeq ry ry')

public export
0 QProductRel : (x, y : QType) -> PrEquivRel (QProductBase x y)
QProductRel x y = (QProductBaseRel x y ** QProductBaseRelEquivI x y)

public export
QProduct : QType -> QType -> QType
QProduct x y = Element0 (QBase x, QBase y) (QProductRel x y)

public export
qProdIntroBase : {0 x, y, z : QType} ->
  QMorph x y -> QMorph x z -> QBase x -> QProductBase y z
qProdIntroBase {x} {y} {z} f g ex = (QMorphBase f ex, QMorphBase g ex)

public export
0 QProductIntroPres : {0 x, y, z : QType} ->
   (f : QMorph x y) -> (g : QMorph x z) ->
   QPres x (QProduct y z) (qProdIntroBase {x} {y} {z} f g)
QProductIntroPres {x} {y} {z} f g ea ea' rx =
  (snd0 f ea ea' rx, snd0 g ea ea' rx)

public export
qProdIntro : {0 x, y, z : QType} ->
  QMorph x y -> QMorph x z -> QMorph x (QProduct y z)
qProdIntro {x} {y} {z} f g =
  Element0 (qProdIntroBase f g) (QProductIntroPres f g)

public export
qProj1Base : (0 x, y : QType) -> QProductBase x y -> QBase x
qProj1Base x y = fst

public export
0 QProj1Pres : (0 x, y : QType) -> QPres (QProduct x y) x (qProj1Base x y)
QProj1Pres x y _ _ = fst

public export
qProj1 : (0 x, y : QType) -> QMorph (QProduct x y) x
qProj1 x y = Element0 (qProj1Base x y) (QProj1Pres x y)

public export
qProj2Base : (0 x, y : QType) -> QProductBase x y -> QBase y
qProj2Base x y = snd

public export
0 QProj2Pres : (0 x, y : QType) -> QPres (QProduct x y) y (qProj2Base x y)
QProj2Pres x y _ _ = snd

public export
qProj2 : (0 x, y : QType) -> QMorph (QProduct x y) y
qProj2 x y = Element0 (qProj2Base x y) (QProj2Pres x y)

public export
qProductBimap : {w, x, y, z : QType} ->
  QMorph w y -> QMorph x z -> QMorph (QProduct w x) (QProduct y z)
qProductBimap {w} {x} {y} {z} f g =
  qProdIntro (qmComp f (qProj1 w x)) (qmComp g (qProj2 w x))

public export
qProductMapFst : {w, x, y : QType} ->
  QMorph w y -> QMorph (QProduct w x) (QProduct y x)
qProductMapFst {w} {x} {y} = flip (qProductBimap {w} {x} {y} {z=x}) (qmId x)

public export
qProductMapSnd : {w, x, y : QType} ->
  QMorph w x -> QMorph (QProduct y w) (QProduct y x)
qProductMapSnd {w} {x} {y} = qProductBimap {w=y} {x=w} {y} {z=x} (qmId y)

------------------------------------
---- Hom-objects (exponentials) ----
------------------------------------

-- Using the notion of extensional equality on QType morphisms (up to the
-- equivalences embedded within the types), we can define the hom-set of
-- of any two `QType`s within `QType` itself, thus making `QType` Cartesian
-- closed.
public export
QHomBase : (x, y : QType) -> Type
QHomBase = QMorph

public export
0 QHomBaseRel : (x, y : QType) -> PrERel (QHomBase x y)
QHomBaseRel x y = QMExtEq {x} {y}

public export
0 QHomBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QHomBase x y) (QHomBaseRel x y)
QHomBaseRelEquivI x y = QMExtEqEquivI {x} {y}

public export
0 QHomRel : (x, y : QType) -> PrEquivRel (QHomBase x y)
QHomRel x y = (QHomBaseRel x y ** QHomBaseRelEquivI x y)

public export
QHom : QType -> QType -> QType
QHom x y = Element0 (QHomBase x y) (QHomRel x y)

public export
QExp : QType -> QType -> QType
QExp = flip QHom

public export
qHomEvalBase : (x, y : QType) -> QBase (QProduct (QHom x y) x) -> QBase y
qHomEvalBase x y (Element0 f fpres, ex) = f ex

public export
0 QHomEvalPres : (x, y : QType) ->
  QPres (QProduct (QHom x y) x) y (qHomEvalBase x y)
QHomEvalPres (Element0 x xeq) (Element0 y yeq)
  (Element0 f fpres, ex) (Element0 g gpres, ex') (fgpres, rx) =
    fgpres ex ex' rx

public export
qHomEval : (x, y : QType) -> QMorph (QProduct (QHom x y) x) y
qHomEval x y = Element0 (qHomEvalBase x y) (QHomEvalPres x y)

public export
qHomCurryBase : {0 x, y, z : QType} ->
  QMorph (QProduct x y) z -> QBase x -> QBase (QHom y z)
qHomCurryBase {x=(Element0 x xeq)} {y=(Element0 y yeq)} {z=(Element0 z zeq)}
  (Element0 f fpres) ex =
    Element0
      (curry f ex)
      $ \ey, ey', ry => fpres (ex, ey) (ex, ey') (PrEquivRefl xeq ex, ry)

public export
0 QHomCurryPres : {0 x, y, z : QType} ->
  (f : QMorph (QProduct x y) z) ->
  QPres x (QHom y z) (qHomCurryBase {x} {y} {z} f)
QHomCurryPres {x=(Element0 x xeq)} {y=(Element0 y yeq)} {z=(Element0 z zeq)}
  (Element0 f fpres) ex ex' rx ey ey' ry =
    fpres (ex, ey) (ex', ey') (rx, ry)

public export
qHomCurry : {0 x, y, z : QType} ->
  QMorph (QProduct x y) z -> QMorph x (QHom y z)
qHomCurry {x} {y} {z} f = Element0 (qHomCurryBase f) (QHomCurryPres f)

public export
qHomUncurry : {x, y, z : QType} ->
  QMorph x (QHom y z) -> QMorph (QProduct x y) z
qHomUncurry {x} {y} {z} f = qmComp (qHomEval y z) (qProductMapFst f)

----------------------------------------------
---- Quotation (derived from hom-objects) ----
----------------------------------------------

-- A global element of a `QType` is a morphism from the terminal object.
public export
QGElem : QType -> Type
QGElem = QMorph QTerm

-- We shall refer to a global element of a hom-object as a "quotation".
public export
QQuotation : QType -> QType -> Type
QQuotation = QGElem .* QHom

public export
qQuote : {x, y : QType} -> QMorph x y -> QQuotation x y
qQuote {x} {y} = qHomCurry {x=QTerm} . flip qmComp (qProj2 QTerm x)

public export
qUnquote : {x, y : QType} -> QQuotation x y -> QMorph x y
qUnquote {x} {y} =
  qmPipe {b=(QProduct QTerm x)} (qProdIntro (qTerm x) (qmId x))
  .  qHomUncurry {x=QTerm}

--------------------
---- Equalizers ----
--------------------

public export
QEqualizerBase : {x : QType} -> {0 y : QType} ->
  QMorph x y -> QMorph x y -> Type
QEqualizerBase {x} {y} f g =
  Subset0 (QBase x) $ \ex => QBaseRel y (QMorphBase f ex, QMorphBase g ex)

public export
0 QEqualizerBaseRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrERel (QEqualizerBase {x} {y} f g)
QEqualizerBaseRel {x} {y} f g (Element0 ex fgeq, Element0 ex' fgeq') =
  QBaseRel x (ex, ex')

public export
0 QEqualizerBaseRelEquivI : {0 x, y : QType} ->
  (f, g : QMorph x y) ->
  PrEquivRelI (QEqualizerBase {x} {y} f g) (QEqualizerBaseRel {x} {y} f g)
QEqualizerBaseRelEquivI {x} {y} f g (Element0 ex fgeq, Element0 ex' fgeq') xeq =
  case xeq of
    PrErefl _ => PrEquivRefl (QRel x) ex
    PrEsym _ _ r => PrEquivSym (QRel x) r
    PrEtrans _ (Element0 ex'' rfg) _ r r' => PrEquivTrans (QRel x) r r'

public export
0 QEqualizerRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrEquivRel (QEqualizerBase {x} {y} f g)
QEqualizerRel {x} {y} f g =
  (QEqualizerBaseRel {x} {y} f g ** QEqualizerBaseRelEquivI {x} {y} f g)

public export
QEqualizer : {x : QType} -> {0 y : QType} ->
  QMorph x y -> QMorph x y -> QType
QEqualizer {x} {y} f g =
  Element0 (QEqualizerBase {x} {y} f g) (QEqualizerRel {x} {y} f g)

public export
qEqIntroBase : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h) ->
  QBase w -> QEqualizerBase {x} {y} f g
qEqIntroBase {w} {x} {y} {f} {g} h eq ew =
  Element0 (fst0 h ew) $ eq ew ew $ PrEquivRefl (QRel w) ew

public export
0 QEqIntroPres : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  (eq : QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h)) ->
  QPres w (QEqualizer {x} {y} f g) (qEqIntroBase {w} {x} {y} {f} {g} h eq)
QEqIntroPres {w} {x} {y} {f} {g} h eq ew ew' rw = snd0 h ew ew' rw

public export
qEqIntro : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h) ->
  QMorph w (QEqualizer {x} {y} f g)
qEqIntro {f} {g} h eq =
  Element0 (qEqIntroBase {f} {g} h eq) (QEqIntroPres {f} {g} h eq)

public export
qEqElimBase : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QEqualizerBase {x} {y} f g -> QBase x
qEqElimBase {x} {y} f g = fst0

public export
0 QEqElimPres : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QPres (QEqualizer {x} {y} f g) x (qEqElimBase {x} {y} f g)
QEqElimPres f g (Element0 ex fgeq) (Element0 ex' fgeq') = id

public export
qEqElim : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMorph (QEqualizer {x} {y} f g) x
qEqElim f g = Element0 (qEqElimBase f g) (QEqElimPres f g)

public export
0 QEqElimEq : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMExtEq {x=(QEqualizer {x} {y} f g)} {y}
    (qmComp {a=(QEqualizer {x} {y} f g)} {b=x} {c=y} f (qEqElim {x} {y} f g),
     qmComp {a=(QEqualizer {x} {y} f g)} {b=x} {c=y} g (qEqElim {x} {y} f g))
QEqElimEq {x} {y} f g (Element0 ex fgeq) (Element0 ex' fgeq') rx =
  PrEquivTrans (snd0 y) fgeq' $ snd0 f ex ex' rx

----------------------
---- Coequalizers ----
----------------------

public export
QCoequalizerBase : {0 x : QType} -> {y : QType} ->
  QMorph x y -> QMorph x y -> Type
QCoequalizerBase {x} {y} f g = QBase y

public export
0 QCoequalizerBaseRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrERel (QCoequalizerBase {x} {y} f g)
QCoequalizerBaseRel {x} {y} f g =
  CoeqFreeEquivRelF {x=(QBase x)} {y=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

public export
0 QCoequalizerBaseRelEquivI : {0 x, y : QType} ->
  (f, g : QMorph x y) ->
  PrEquivRelI (QCoequalizerBase {x} {y} f g) (QCoequalizerBaseRel {x} {y} f g)
QCoequalizerBaseRelEquivI {x} {y} f g =
  CoeqFreeEquivRelI {x=(QBase x)} {y=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

public export
0 QCoequalizerRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrEquivRel (QCoequalizerBase {x} {y} f g)
QCoequalizerRel {x} {y} f g =
  (QCoequalizerBaseRel {x} {y} f g ** QCoequalizerBaseRelEquivI {x} {y} f g)

public export
QCoequalizer : {0 x : QType} -> {y : QType} ->
  QMorph x y -> QMorph x y -> QType
QCoequalizer {x} {y} f g =
  Element0 (QCoequalizerBase {x} {y} f g) (QCoequalizerRel {x} {y} f g)

public export
qCoeqIntroBase : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QBase y -> QCoequalizerBase {x} {y} f g
qCoeqIntroBase {x} {y} f g = id

public export
0 QCoeqIntroPres : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QPres y (QCoequalizer {x} {y} f g) (qCoeqIntroBase {x} {y} f g)
QCoeqIntroPres {x} {y} f g ew ew' = InSlFv . Right

public export
qCoeqIntro : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMorph y (QCoequalizer {x} {y} f g)
qCoeqIntro f g = Element0 (qCoeqIntroBase f g) (QCoeqIntroPres f g)

public export
qCoeqElimBase : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g) ->
  QCoequalizerBase {x} {y} f g -> QBase z
qCoeqElimBase {x} {y} {z} {f} {g} h eq ey = fst0 h ey

public export
0 QCoeqElimPresSubst : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  SliceMorphism {a=(ProductMonad $ QBase y)}
    (CoeqRelF
      (QMorphBase {x} {y} f) (QMorphBase {x} {y} g) (QBaseRel x) (QBaseRel y))
    (QBaseRel z . mapHom (QMorphBase {x=y} {y=z} h))
QCoeqElimPresSubst {x} {y} {z} {f} {g} h hcoeq (ey, ey')
  (Left (Evidence0 (ex, ex') (rx, feq, geq))) =
    rewrite sym feq in rewrite sym geq in
    hcoeq ex ex' rx
QCoeqElimPresSubst {x} {y} {z} {f} {g} h hcoeq (ey, ey')
  (Right yeq) =
    QMorphPres h ey ey' yeq

public export
0 QCoeqElimPresAlg : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  SliceAlg {a=(ProductMonad $ QBase y)} (PrEquivF {a=(QBase y)})
    (QBaseRel z . mapHom (QMorphBase {x=y} {y=z} h))
QCoeqElimPresAlg {x} {y} {z} {f} {g} h hcoeq (ey, ey') eqy =
  QRelEquivI z (mapHom (QMorphBase {x=y} {y=z} h) (ey, ey')) $
    prEquivMapHom {r=(QBaseRel z)} {f=(QMorphBase h)} (ey, ey') eqy

public export
0 QCoeqElimPres : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  QPres (QCoequalizer {x} {y} f g) z (qCoeqElimBase {x} {y} {z} {f} {g} h eq)
QCoeqElimPres {x} {y} {z} {f} {g} h hcoeq ey ey' =
  freePrEquivEval {a=(QBase y)}
    (CoeqRelF (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y))
    (QBaseRel z . mapHom (QMorphBase h))
    (QCoeqElimPresSubst h hcoeq)
    (QCoeqElimPresAlg h hcoeq)
    (ey, ey')

public export
qCoeqElim : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g) ->
  QMorph (QCoequalizer {x} {y} f g) z
qCoeqElim {x} {y} {z} {f} {g} h eq =
  Element0 (qCoeqElimBase {f} {g} h eq) (QCoeqElimPres {f} {g} h eq)

---------------------------------------------
---------------------------------------------
---- Predicates on and slices of `QType` ----
---------------------------------------------
---------------------------------------------

-----------------------------
---- In categorial style ----
-----------------------------

public export
QSliceObjBase : QType -> Type
QSliceObjBase a = Subset0 QType (flip QMorph a)

public export
0 QSliceTotRel : {a : QType} -> PrERel (QSliceObjBase a)
QSliceTotRel (sl, sl') = QTEquiv (fst0 sl, fst0 sl')

public export
0 QSliceProjRel : {a : QType} -> (sl, sl' : QSliceObjBase a) ->
  (0 _ : QSliceTotRel {a} (sl, sl')) -> Type
QSliceProjRel sl sl' qte = QMExtEq (snd0 sl, qmComp (snd0 sl') $ QTEqIso qte)

public export
0 QSliceObjRel : {a : QType} -> PrERel (QSliceObjBase a)
QSliceObjRel (sl, sl') = Exists0 (QSliceTotRel (sl, sl')) (QSliceProjRel sl sl')

public export
0 QSliceObjRelEquivI : {a : QType} ->
  PrEquivRelI (QSliceObjBase a) (QSliceObjRel {a})
QSliceObjRelEquivI {a=(Element0 a (aeq ** aequiv))}
  (Element0 (Element0 x (xeq ** xequiv)) (Element0 f fpres),
   Element0 (Element0 x' (xeq' ** xequiv')) (Element0 f' fpres'))
  eq =
    case eq of
      PrErefl _ =>
        Evidence0
          (QTE (\_, _ => id, \_, _ => id))
          fpres
      PrEsym _ _ (Evidence0 (QTE (impl, impr)) gpres) =>
        Evidence0
          (QTE (impr, impl))
          $ \ea, ea', eaeq =>
            aequiv (f ea, f' ea') $
              PrEtrans (f ea) (f' ea) (f' ea')
                (fpres' ea ea' $ impr ea ea' eaeq)
                $ aequiv (f ea, f' ea) $
                  PrEtrans (f ea) (f ea') (f' ea)
                    (aequiv (f ea', f' ea) $ PrEsym (f' ea) (f ea') $
                      gpres ea ea' $ impr ea ea' eaeq)
                    (fpres ea ea' eaeq)
      PrEtrans _ (Element0 (Element0 z (zeq ** zequiv)) (Element0 g gpres)) _
        (Evidence0 (QTE (impl, impr)) gfpres)
        (Evidence0 (QTE (impl', impr')) fgpres) =>
          Evidence0
            (QTE
              (\ea, ea' => impl ea ea' . impl' ea ea',
               \ea, ea' => impr' ea ea' . impr ea ea'))
            $ \ea, ea', eaeq =>
              aequiv (f ea, f' ea') $
                PrEtrans (f ea) (g ea) (f' ea')
                  (gfpres ea ea' $ impl' ea ea' eaeq)
                  $ aequiv (f ea, g ea) $
                    PrEtrans (f ea) (g ea') (g ea)
                      (aequiv (g ea', g ea) $ PrEsym (g ea) (g ea') $
                        gpres ea ea' $ impl' ea ea' eaeq)
                      $ fgpres ea ea' eaeq

public export
0 QSliceObjRelEquiv : {a : QType} -> PrEquivRel (QSliceObjBase a)
QSliceObjRelEquiv {a} = (QSliceObjRel {a} ** QSliceObjRelEquivI {a})

public export
QSliceObj : QType -> QType
QSliceObj a = Element0 (QSliceObjBase a) (QSliceObjRelEquiv {a})

---------------------------------
---- In dependent-type style ----
---------------------------------

-- A predicate is a dependent type in the type-theoretic view.  In the
-- categorial view, it is a discrete presheaf, which is the opposite category
-- of a discrete copresheaf, which is equivalent to a slice category.
-- So the category of predicates on a `QType` is equivalent to the opposite
-- of the slice category of `QType` over that `QType`.
public export
QPred : QType -> QType
QPred a = QHom a QTypeQT

----------------------------
----------------------------
---- Quivers in `QType` ----
----------------------------
----------------------------

-- A quiver in `QType` is a functor from the walking quiver -- a generic
-- figure with two objects and two parallel non-identity morphisms -- to
-- `QType`.  Such a functor is determined by a choice of two `QType`s and
-- two parallel `QMorph`s between them.
--
-- However, there is another way of looking at this:  when we view the
-- functor as contravariant, so that it is a presheaf rather than a
-- copresheaf -- a functor from the _opposite_ category of the walking quiver
-- to `QType` -- it is equivalent to a `QType` together with a `QType`
-- dependent on pairs of the first `QType`, or, to put it another way, a
-- `QType` together with a slice over its product.
public export
QQuivEdge : QType -> QType
QQuivEdge vert = QPred $ QProduct vert vert

-----------------------------------------------
-----------------------------------------------
---- Polynomial profunctors and categories ----
-----------------------------------------------
-----------------------------------------------

-----------------------------------------------
---- Polynomial endo-profunctors on `Type` ----
-----------------------------------------------

public export
PolyProfData : Type
PolyProfData = (pos : Type ** Either pos pos -> Type)

public export
InterpPolyProfData : PolyProfData -> ProfunctorSig
InterpPolyProfData ppd x y =
  (p : fst ppd ** PrePostPair (snd ppd $ Left p) (snd ppd $ Right p) x y)

public export
ppdDimap : (ppd : PolyProfData) -> DimapSig (InterpPolyProfData ppd)
ppdDimap ppd mca mbd pab =
  (fst pab ** (fst (snd pab) . mca, mbd . snd (snd pab)))

-- This position (together with the direction below) makes `HomProf` into a
-- polynomial by turning its interpretation into `CoProYo`.
--
-- These positions are, I believe, the objects of the category of elements
-- of `HomProf`.
public export
HomProfPolyPos : Type
HomProfPolyPos = (ab : (Type, Type) ** fst ab -> snd ab)

public export
HomProfPolyDir1 : HomProfPolyPos -> Type
HomProfPolyDir1 = fst . fst

public export
HomProfPolyDir2 : HomProfPolyPos -> Type
HomProfPolyDir2 = snd . fst

public export
HomProfPolyDir : Either HomProfPolyPos HomProfPolyPos -> Type
HomProfPolyDir = eitherElim HomProfPolyDir1 HomProfPolyDir2

public export
HomProfPolyData : PolyProfData
HomProfPolyData = (HomProfPolyPos ** HomProfPolyDir)

public export
HomProfToPoly : ProfNT HomProf (InterpPolyProfData HomProfPolyData)
HomProfToPoly {a} {b} mab = (((a, b) ** mab) ** (id, id))

public export
HomProfFromPoly : ProfNT (InterpPolyProfData HomProfPolyData) HomProf
HomProfFromPoly {a} {b} pab = snd (snd pab) . snd (fst pab) . fst (snd pab)

public export
HomProfToFromPolyId : {a, b : Type} ->
  (mab : HomProf a b) ->
  ProfNTcomp
     {p=HomProf}
     {q=(InterpPolyProfData HomProfPolyData)}
     {r=HomProf}
    HomProfFromPoly HomProfToPoly {a} {b}
    mab =
  mab
HomProfToFromPolyId {a} {b} mab = Refl

{- This dictates an equivalence relation that we could use in a logic
 - with quotient types.
public export
HomProfFromToPolyId : {a, b : Type} ->
  (mab : InterpPolyProfData HomProfPolyData a b) ->
  ProfNTcomp
     {p=(InterpPolyProfData HomProfPolyData)}
     {q=HomProf}
     {r=(InterpPolyProfData HomProfPolyData)}
    HomProfToPoly HomProfFromPoly {a} {b}
    mab =
  mab
HomProfFromToPolyId {a} {b} ((cd ** mcd) ** (mac, mdb)) =
  HomProfFromToPolyId_hole
-}

public export
CatToPolyProfPos : SCat -> Type
CatToPolyProfPos = scObj

public export
CatToPolyProfDir :
  (sc : SCat) -> Either (CatToPolyProfPos sc) (CatToPolyProfPos sc) -> Type
CatToPolyProfDir sc = eitherElim
  (Sigma {a=(scObj sc)} . curry (scHom sc))
  (Sigma {a=(scObj sc)} . flip (curry (scHom sc)))

public export
CatToPolyProf : SCat -> PolyProfData
CatToPolyProf sc = (CatToPolyProfPos sc ** CatToPolyProfDir sc)

-----------------------------------------------------
---- Category/polynomial-promonad correspondence ----
-----------------------------------------------------

public export
0 FMapSig : (Type -> Type) -> Type
FMapSig f = {0 a, b : Type} -> (a -> b) -> f a -> f b

public export
0 FContramapSig : (Type -> Type) -> Type
FContramapSig f = {0 a, b : Type} -> (b -> a) -> f a -> f b

-- See https://ncatlab.org/nlab/show/profunctor#definition

-- The representable profunctor from `Type^op x Type` to `Type` (also
-- written `Type -|-> Type`) induced by the given functor from `Type` to
-- `Type`.  Called `D(1, f)` on the above page.
public export
RepProf : (Type -> Type) -> ProfunctorSig
RepProf f d c = d -> f c

public export
repProfDimap : {0 f : Type -> Type} -> FMapSig f -> DimapSig (RepProf f)
repProfDimap {f} fm mca mbd mafb = fm mbd . mafb . mca

public export
Functor f => Profunctor (RepProf f) where
  dimap = repProfDimap {f} (map {f})

-- The (co-)representable profunctor from `Type x Type^op` to `Type`
-- (also written `Type^op -|-> Type^op`) induced by the given functor from
-- `Type` to `Type`.  Called `D(f, 1)` on the above page.
public export
CorepProf : (Type -> Type) -> ProfunctorSig
CorepProf f c d = f c -> d

public export
corepProfDimap : {0 f : Type -> Type} -> FMapSig f -> DimapSig (CorepProf f)
corepProfDimap {f} fm mca mbd mfab = mbd . mfab . fm mca

public export
Functor f => Profunctor (CorepProf f) where
  dimap = corepProfDimap {f} (map {f})

public export
FunctorFam : Type
FunctorFam = (pos : Type ** pos -> Type -> Type)

public export
FFPos : FunctorFam -> Type
FFPos = fst

public export
FFDir : (ff : FunctorFam) -> FFPos ff -> Type -> Type
FFDir = snd

public export
0 FFMapSig : FunctorFam -> Type
FFMapSig ff = (pos : FFPos ff) -> FMapSig (FFDir ff pos)

public export
SumRepProf : FunctorFam -> ProfunctorSig
SumRepProf ff d c = (pos : FFPos ff ** RepProf (FFDir ff pos) d c)

public export
sumRepProfDimap : {0 ff : FunctorFam} ->
  FFMapSig ff -> DimapSig (SumRepProf ff)
sumRepProfDimap {ff} ffm mca mbd (pos ** mafb) =
  (pos ** repProfDimap {f=(FFDir ff pos)} (ffm pos) mca mbd mafb)

public export
SumRepProfunctor : {0 ff : FunctorFam} -> (ffm : FFMapSig ff) ->
  Profunctor (SumRepProf ff)
SumRepProfunctor {ff} ffm = MkProfunctor $ sumRepProfDimap {ff} ffm

public export
SumCorepProf : FunctorFam -> ProfunctorSig
SumCorepProf ff c d = (pos : FFPos ff ** CorepProf (FFDir ff pos) c d)

public export
sumCorepProfDimap : {0 ff : FunctorFam} ->
  FFMapSig ff -> DimapSig (SumCorepProf ff)
sumCorepProfDimap {ff} ffm mca mbd (pos ** mfab) =
  (pos ** corepProfDimap {f=(FFDir ff pos)} (ffm pos) mca mbd mfab)

public export
SumCorepProfunctor : {0 ff : FunctorFam} -> (ffm : FFMapSig ff) ->
  Profunctor (SumCorepProf ff)
SumCorepProfunctor {ff} ffm = MkProfunctor $ sumCorepProfDimap {ff} ffm

public export
FunctorFamPair : Type
FunctorFamPair = (FunctorFam, FunctorFam)

public export
FFPcorep : FunctorFamPair -> FunctorFam
FFPcorep = fst

public export
FFPrep : FunctorFamPair -> FunctorFam
FFPrep = snd

public export
0 FFPMapSig : FunctorFamPair -> Type
FFPMapSig ffp = (FFMapSig $ FFPcorep ffp, FFMapSig $ FFPrep ffp)

public export
FFPMcorep : {0 ffp : FunctorFamPair} ->
  FFPMapSig ffp -> FFMapSig (FFPcorep ffp)
FFPMcorep = fst

public export
FFPMrep : {0 ffp : FunctorFamPair} ->
  FFPMapSig ffp -> FFMapSig (FFPrep ffp)
FFPMrep = snd

public export
SumRepCorepProf : FunctorFamPair -> ProfunctorSig
SumRepCorepProf ffp d c =
  Either (SumCorepProf (FFPcorep ffp) d c) (SumRepProf (FFPrep ffp) d c)

public export
sumRepCorepProfDimap : {0 ffp : FunctorFamPair} ->
  FFPMapSig ffp -> DimapSig (SumRepCorepProf ffp)
sumRepCorepProfDimap {ffp} ffpm mca mbd (Left (pos ** mfab)) =
  Left $
    sumCorepProfDimap {ff=(FFPcorep ffp)} (FFPMcorep ffpm) mca mbd (pos ** mfab)
sumRepCorepProfDimap {ffp} ffpm mca mbd (Right (pos ** mafb)) =
  Right $
    sumRepProfDimap {ff=(FFPrep ffp)} (FFPMrep ffpm) mca mbd (pos ** mafb)

public export
SumRepCorepProfunctor : {0 ffp : FunctorFamPair} -> (ffpm : FFPMapSig ffp) ->
  Profunctor (SumRepCorepProf ffp)
SumRepCorepProfunctor {ffp} ffpm =
  MkProfunctor $ sumRepCorepProfDimap {ffp} ffpm

-------------------------------
-------------------------------
---- Finitary copresheaves ----
-------------------------------
-------------------------------

------------------------
---- Finite quivers ----
------------------------

-- A quiver (directed multigraph) internal to FinSet.
record FSQuiv where
  constructor FSQ
  fsqVert : Nat
  fsqEdge : Nat
  fsqSrc : Vect fsqEdge (Fin fsqVert)
  fsqTgt : Vect fsqEdge (Fin fsqVert)

-- The signature of endpoints of an edge in or a path through a finite quiver.
record FSQSig (fsq : FSQuiv) where
  constructor FSQS
  fsqsDom : Fin (fsqVert fsq)
  fsqsCod : Fin (fsqVert fsq)

-- An edge in a finite quiver with the given endpoints.
record FSQEdge (sig : Sigma FSQSig) where
  constructor FSQE
  fsqeE : Fin (fsqEdge (fst sig))
  0 fsqeDom : index fsqeE (fsqSrc (fst sig)) = fsqsDom (snd sig)
  0 fsqeCod : index fsqeE (fsqTgt (fst sig)) = fsqsCod (snd sig)

-- A path through a finite quiver (ordered starting from the target)
-- with the given endpoints.
data FSQPath : SliceObj (Sigma FSQSig) where
  FSQPid : (0 fsq : FSQuiv) -> (0 v : Fin (fsqVert fsq)) ->
    FSQPath (fsq ** FSQS v v)
  FSQPcomp : (0 fsq : FSQuiv) -> {0 s, v, t : Fin (fsqVert fsq)} ->
    FSQEdge (fsq ** FSQS v t) -> FSQPath (fsq ** FSQS s v) ->
    FSQPath (fsq ** FSQS s t)

------------------------------------------------
------------------------------------------------
---- Discrete dependent polynomial functors ----
------------------------------------------------
------------------------------------------------

---------------------
---- Definitions ----
---------------------

public export
DiscBaseChange : {dom : Type} -> {0 cod : Type} ->
  (cod -> dom) -> SliceFunctor dom cod
DiscBaseChange {dom} {cod} = (|>)

-- In general, the left Kan extension of `SliceObj dom` (viewed as a functor
-- to `Type` from a discrete category formed from `dom`) along `f` (viewed
-- as a functor between discrete categories formed from `dom` and `cod`).
public export
DiscSigma : {dom : Type} -> {0 cod : Type} ->
  (dom -> cod) -> SliceFunctor dom cod
DiscSigma {dom} {cod} f sld elc = (eld : PreImage f elc ** sld $ fst0 eld)

-- In general, the right Kan extension of `SliceObj dom` (viewed as a functor
-- to `Type` from a discrete category formed from `dom`) along `f` (viewed
-- as a functor between discrete categories formed from `dom` and `cod`).
public export
GenPi : {dom : Type} -> {0 cod : Type} ->
  (dom -> cod) -> SliceFunctor dom cod
GenPi {dom} {cod} f sld elc = (eld : PreImage f elc) -> sld $ fst0 eld

-- We define a discrete dependent product as one which factors through
-- a type of (finite) dependent vectors.
public export
DiscPi : {pos : Type} -> (nfield : pos -> Nat) ->
  SliceFunctor (Sigma {a=pos} (Fin . nfield)) pos
DiscPi {pos} nfield sld i = HVect {k=(nfield i)} $ finFToVect $ sld . MkDPair i

public export
record DiscSlicePolyFunc (dom, cod : Type) where
  constructor MkDSPF
  dspfPos : SliceObj cod
  dspfNField : Sigma {a=cod} dspfPos -> Nat
  dspfFieldTypes : Sigma {a=(Sigma {a=cod} dspfPos)} (Fin . dspfNField) -> dom

public export
interpDSPF : {dom, cod : Type} ->
  DiscSlicePolyFunc dom cod -> SliceObj dom -> SliceObj cod
interpDSPF {dom} {cod} (MkDSPF pos nfield ftypes) =
  DiscBaseChange {dom} {cod=(Sigma {a=(Sigma {a=cod} pos)} (Fin . nfield))}
    ftypes
  |> DiscPi {pos=(Sigma {a=cod} pos)} nfield
  |> DiscSigma {dom=(Sigma {a=cod} pos)} {cod} DPair.fst

-----------------------------------------------------------
---- Relationships with other polynomial-functor forms ----
-----------------------------------------------------------

public export
dspfToWType : {dom, cod : Type} ->
  DiscSlicePolyFunc dom cod -> WTypeFunc dom cod
dspfToWType {dom} {cod} (MkDSPF pos nfield ftypes) =
  MkWTF
    (Sigma {a=cod} pos)
    (Sigma {a=(Sigma {a=cod} pos)} (Fin . nfield))
    ftypes
    DPair.fst
    DPair.fst

public export
dspfToSpf : {dom, cod : Type} ->
  DiscSlicePolyFunc dom cod -> SlicePolyFunc dom cod
dspfToSpf {dom} {cod} (MkDSPF pos nfield ftypes) =
  (pos ** (Fin . nfield) ** ftypes)

----------------------
---- Fixed points ----
----------------------

-----------------------------------------
-----------------------------------------
---- Finitary quivers and categories ----
-----------------------------------------
-----------------------------------------

-- A quiver enriched over `FinSet` is one whose edge-objects are drawn
-- from `FinSet` -- in other words, whose edge-sets are all finite.
-- Such a quiver need not necessarily have a finite number of _vertices_.
public export
FinEnrQuiv : Type -> Type
FinEnrQuiv v = (v, v) -> Nat

---------------------------------------
---------------------------------------
---- Polynomial functors on FinSet ----
---------------------------------------
---------------------------------------

-- A slice category is identified by a category together with one of its
-- objects.  In particular, a slice of `FinSet` is identified by an object
-- of `FinSet`, i.e. a natural number.  Similarly, the _opposite_ of a slice
-- category may be identified by the object whose slice category it is the
-- opposite of.  Note that the opposite of a slice category is not (necessarily)
-- equivalent to the coslice category, nor is it (necessarily) equivalent to
-- a slice of the opposite of the base category (although those latter two are
-- equivalent to _each other_) -- although it is equivalent to a coslice of the
-- opposite of the base category!
--
-- The equivalences of categories with the opposite of a slice category in
-- which we are most intereseted are:
--
--  - The subcategory of the polynomial endofunctors on `FinSet` whose
--    position-sets (when we view endofunctors as `FinSet`s dependent on
--    `FinSet`s) are the same as the object being sliced over
--  - The opposite of the subcategory of the Dirichlet endofunctors on `FinSet`
--    whose position-sets (when we view endofunctors as `FinSet`s dependent on
--    `FinSet`s) are the same as the object being sliced over
--  - The (contravariant) presheaf category into `FinSet` resulting from
--    treating the object being sliced over as a discrete category (presheaves
--    in general are sometimes called "generic figures" or "C-sets")
public export
record FinOpSlCat where
  constructor FinOSC
  finOSbase : FSObj

-- A dependent product between opposites of slices of `FinSet` is determined
-- by a morphism from the codomain to the domain.
public export
record FSOpPi (dom, cod : FinOpSlCat) where
  constructor MkFSPi
  fspiMorph : FSMorph (finOSbase cod) (finOSbase dom)

public export
DiscOpFactorization : {pos : Type} -> (nfield : pos -> Nat) -> Type
DiscOpFactorization {pos} = Sigma {a=pos} . (.) Fin

-- We define a discrete dependent product as one which factors through
-- a type of (finite) dependent vectors.  So we insert a discrete-factorization
-- functor into the polynomial-functor "pipeline".
public export
DiscOpFactorize : {pos : Type} -> (nfield : pos -> Nat) ->
  SliceFunctor (DiscOpFactorization {pos} nfield) pos
DiscOpFactorize {pos} nfield sld i =
  HVect {k=(nfield i)} $ finFToVect $ sld . MkDPair i

---------------------------
---------------------------
---- Splices of `Type` ----
---------------------------
---------------------------

Type2Obj : Type
Type2Obj = ProductMonad Type

Type2Sig : Type
Type2Sig = ProductMonad Type2Obj

Type2Morph : SliceObj Type2Sig
Type2Morph ab = (fst (fst ab) -> fst (snd ab), snd (fst ab) -> snd (snd ab))

SpliceCat : Type
SpliceCat = Type2Obj

SpliceBase : SpliceCat -> Type
SpliceBase = snd

SpliceCobase : SpliceCat -> Type
SpliceCobase = fst

SpliceBaseObj : SpliceCat -> Type
SpliceBaseObj = SliceObj . SpliceBase

SpliceBaseSlice : (cat : SpliceCat) -> SliceObj (SpliceBaseObj cat)
SpliceBaseSlice cat = Sigma {a=(SpliceBase cat)}

SpliceBaseFst : {cat : SpliceCat} -> {base : SpliceBaseObj cat} ->
  SpliceBaseSlice cat base -> SpliceBase cat
SpliceBaseFst {cat} {base} = fst

SpliceBaseSnd : {cat : SpliceCat} -> {base : SpliceBaseObj cat} ->
  (spl : SpliceBaseSlice cat base) -> base (SpliceBaseFst {cat} spl)
SpliceBaseSnd {cat} {base} = snd

SpliceCobaseObj : (cat : SpliceCat) -> SliceObj (SpliceBaseObj cat)
SpliceCobaseObj cat = HomProf (SpliceCobase cat) . SpliceBaseSlice cat

SpliceObj : SpliceCat -> Type
SpliceObj cat = Subset0 (SpliceBaseObj cat) (SpliceCobaseObj cat)

SpliceObjBase : {cat : SpliceCat} -> SpliceObj cat -> SpliceBaseObj cat
SpliceObjBase {cat} = fst0

0 SpliceObjCobase : {cat : SpliceCat} -> (spl : SpliceObj cat) ->
  SpliceCobaseObj cat (SpliceObjBase {cat} spl)
SpliceObjCobase {cat} = snd0

SpliceObjTot : {cat : SpliceCat} -> SpliceObj cat -> Type
SpliceObjTot {cat} spl = SpliceBaseSlice cat (SpliceObjBase spl)

SpliceSig : SpliceCat -> Type
SpliceSig = SignatureT . SpliceObj

SpliceDom : {cat : SpliceCat} -> SpliceSig cat -> SpliceObj cat
SpliceDom = fst

SpliceCod : {cat : SpliceCat} -> SpliceSig cat -> SpliceObj cat
SpliceCod = snd

SpliceDomTot : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceDomTot {cat} sig = SpliceObjTot $ SpliceDom {cat} sig

SpliceCodTot : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceCodTot {cat} sig = SpliceObjTot $ SpliceCod {cat} sig

SpliceDomBase : {cat : SpliceCat} -> SpliceSig cat -> SpliceBaseObj cat
SpliceDomBase {cat} sig = SpliceObjBase $ SpliceDom {cat} sig

SpliceCodBase : {cat : SpliceCat} -> SpliceSig cat -> SpliceBaseObj cat
SpliceCodBase {cat} sig = SpliceObjBase $ SpliceCod {cat} sig

0 SpliceDomCobase : {cat : SpliceCat} ->
  (sig : SpliceSig cat) -> SpliceCobaseObj cat (SpliceDomBase {cat} sig)
SpliceDomCobase {cat} sig = SpliceObjCobase $ SpliceDom {cat} sig

0 SpliceCodCobase : {cat : SpliceCat} ->
  (sig : SpliceSig cat) -> SpliceCobaseObj cat (SpliceCodBase {cat} sig)
SpliceCodCobase {cat} sig = SpliceObjCobase $ SpliceCod {cat} sig

SpliceBaseMorph : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceBaseMorph {cat} sig =
  SliceMorphism {a=(SpliceBase cat)}
    (SpliceDomBase {cat} sig)
    (SpliceCodBase {cat} sig)

0 SpliceCobaseMorph : {cat : SpliceCat} -> {sig : SpliceSig cat} ->
  SpliceBaseMorph {cat} sig -> Type
SpliceCobaseMorph {cat} {sig} m =
  (elb : SpliceBase cat) -> (elc : SpliceCobase cat) ->
  (0 eqdb : SpliceBaseFst (SpliceDomCobase sig elc) = elb) ->
  (0 eqcb : SpliceBaseFst (SpliceCodCobase sig elc) = elb) ->
  m elb
    (replace {p=(SpliceDomBase sig)} eqdb
     (SpliceBaseSnd $ SpliceDomCobase sig elc)) =
  replace {p=(SpliceCodBase sig)} eqcb
    (SpliceBaseSnd $ SpliceCodCobase sig elc)

SpliceMorph : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceMorph {cat} sig =
  Subset0 (SpliceBaseMorph {cat} sig) (SpliceCobaseMorph {cat} {sig})

SpliceMorphBase : {cat : SpliceCat} -> {sig : SpliceSig cat} ->
  SpliceMorph {cat} sig -> SpliceBaseMorph {cat} sig
SpliceMorphBase = fst0

0 SpliceMorphCobase : {cat : SpliceCat} -> {sig : SpliceSig cat} ->
  (m : SpliceMorph {cat} sig) ->
  SpliceCobaseMorph {cat} {sig} (SpliceMorphBase {cat} {sig} m)
SpliceMorphCobase = snd0
