module LanguageDef.DiagramCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.PolyCat
import public LanguageDef.Syntax
import public LanguageDef.Figures

%default total

public export
data CatSortObj : Type where
  CSOobj : CatSortObj
  CSOmorph : CatSortObj
  CSOcomp : CatSortObj -- pairs of "composable" or "compatible" morphisms
  CSO1 : CatSortObj
  CSOprod : CatSortObj -> CatSortObj -> CatSortObj

public export
data CatSortMorph : CatSortObj -> CatSortObj -> Type where
  CSMid : (a : CatSortObj) -> CatSortMorph a a
  CSMdom : CatSortMorph CSOmorph CSOobj
  CSMcod : CatSortMorph CSOmorph CSOobj
  CSMcomp : CatSortMorph CSOcomp CSOmorph
  CSM1 : (a : CatSortObj) -> CatSortMorph a CSO1
  CSMprod : {0 a, b, c : CatSortObj} ->
    CatSortMorph a b -> CatSortMorph a c -> CatSortMorph a (CSOprod b c)
  CSMproj1 : {0 a, b : CatSortObj} -> CatSortMorph (CSOprod a b) a
  CSMproj2 : {0 a, b : CatSortObj} -> CatSortMorph (CSOprod a b) b

public export
csmComp : {a, b, c : CatSortObj} ->
  CatSortMorph b c -> CatSortMorph a b -> CatSortMorph a c
csmComp {a} {b} {c=b} (CSMid b) f = f
csmComp {a} {b=a} {c} g (CSMid a) = g
csmComp {a} {b=CSOobj} {c=CSO1} (CSM1 CSOobj) f = CSM1 a
csmComp {a=CSOmorph} {b=CSOobj} {c=(CSOprod c c')} (CSMprod d d') CSMdom = ?CSMcomp_hole_5a_0
csmComp {a=CSOmorph} {b=CSOobj} {c=(CSOprod c c')} (CSMprod d d') CSMcod = ?CSMcomp_hole_5a_1
csmComp {a=(CSOprod CSOobj b)} {b=CSOobj} {c=(CSOprod c c')} (CSMprod d d') CSMproj1 = ?CSMcomp_hole_5a_2
csmComp {a=(CSOprod a CSOobj)} {b=CSOobj} {c=(CSOprod c c')} (CSMprod d d') CSMproj2 = ?CSMcomp_hole_5a_3
csmComp {a} {b=CSOmorph} {c} g f = ?CSMcomp_hole_1
csmComp {a} {b=CSOcomp} {c} g f = ?CSMcomp_hole_2
csmComp {a} {b=CSO1} {c} g f = ?CSMcomp_hole_3
csmComp {a} {b=(CSOprod x y)} {c} g f = ?CSMcomp_hole_4

public export
csmEq : {0 a, b : CatSortObj} ->
  CatSortMorph a b -> CatSortMorph a b -> CatSortObj
csmEq {a} {b} f g = ?csmEq_hole

----------------------------------------------
----------------------------------------------
---- Variably-parameterized-type families ----
----------------------------------------------
----------------------------------------------
public export
record VPTSig where
  constructor VPTS
  -- The types may have mutual dependencies.  Each type takes a telescope
  -- parameter.  The order is the length of the telescope.
  vptMaxOrder : Nat
  -- The number of types of each order.
  vptIdx : Vect (S vptMaxOrder) Nat
  -- The number of parameters to each type.
  vptParam : HVect (map Fin vptIdx)

-- This by itself generates an "erased" family of types without
-- internal parameterization.
public export
VPTEFunc : VPTSig -> VPTSig -> Type
VPTEFunc dom cod =
  SlicePolyFunc (HVect $ map Fin dom.vptIdx) (HVect $ map Fin cod.vptIdx)

public export
VPTEndoEFunc : VPTSig -> Type
VPTEndoEFunc base = VPTEFunc base base

-- The data required to layer internal parameterization on the types.
public export
record VPTFunc (0 base : Type) (0 ef : SlicePolyEndoFunc base) where
  constructor VPTF

-----------------------------------------------------
-----------------------------------------------------
---- The category of dependent sets (AKA arenas) ----
-----------------------------------------------------
-----------------------------------------------------

-- An object of the category of dependent sets in `Type`.  This resembles the
-- product category `Type x Type` (which is equivalent to the slice category
-- `2 -> Type`), but the morphisms must be coherent with each other.
public export
DSCatObj : Type
DSCatObj = Sigma {a=Type} SliceObj

-- When the dependent set is viewed as an arena, this may be viewed as
-- a direction at any position, or put another way, a pair of a position
-- with a direction at that position.
public export
DSCatSigma : DSCatObj -> Type
DSCatSigma ds = Sigma {a=(fst ds)} (snd ds)

-- This shows that this is another way of looking at the category of
-- Dirichlet endofunctors on `Type`:  it's the same as a natural transformation
-- between Dirichlet endofunctors.
public export
DSCatMorph : DSCatObj -> DSCatObj -> Type
DSCatMorph a b =
  (m : fst a -> fst b ** SliceMorphism {a=(fst a)} (snd a) (snd b . m))

public export
DSCatMorphApp : {dom, cod : DSCatObj} ->
  DSCatMorph dom cod -> DSCatSigma dom -> DSCatSigma cod
DSCatMorphApp {dom} {cod} (m ** sm) (x ** dx) = (m x ** sm x dx)

-- An endofunctor on the category of dependent sets in `Type`.
public export
DSCatEndofunctorOMap : Type
DSCatEndofunctorOMap = DSCatObj -> DSCatObj

public export
DSCatEndofunctorFMap : DSCatEndofunctorOMap -> Type
DSCatEndofunctorFMap f =
  (a, b : DSCatObj) -> DSCatMorph a b -> DSCatMorph (f a) (f b)

-- The data which determine a polynomial functor from the category of
-- dependent sets in `Type` to `Type`.
public export
record DSToType where
  constructor DS21
  -- Each position may be viewed as a constructor.
  ds2tpos : Type
  -- Each position has a type of directions representing inputs of the
  -- left (non-dependent) part of the dependent sum, together with, for each
  -- such direction a type of directions representing inputs of the right
  -- (dependent) part of the sum, where those inputs have a type coming from
  -- the corresponding non-dependent direction.
  ds2tdir : ds2tpos -> DSCatObj

{-
public export
interpDSToType : DSToType -> DSCatObj -> Type
interpDSToType ds2t ds = (i : ds2tpos ds2t ** DSCatMorph (ds2tdir ds2t i) ds)

-- The input to this functor is some arbitrary type together with
-- some arbitrary type dependent upon it.  Its output is a dependent
-- type which depends upon the output of the interpretation of
-- `ds2t` applied to the original arbitrary input type.
--
-- Consequently, it may be viewed as "for any type `A`, a dependent polynomial
-- functor from the slice category `Type/A` to the slice category
-- `Type/(interpDSToType A)`".

public export
interpDSToDep : {pos : Type} -> (pos -> DSToType) -> DSCatObj -> pos -> Type
interpDSToDep {pos} ds2dr ds i =
  (j : ds2tpos (ds2dr i) ** DSCatMorph (ds2tdir (ds2dr i) j) ds)

public export
DSPF : Type
DSPF = Sigma {a=DSToType} $ \ds2t => ds2tpos ds2t -> DSToType

public export
interpDStoDS : DSPF -> DSCatEndofunctorOMap
interpDStoDS dspf ds =
  (interpDSToType (fst dspf) ds ** interpDSToDep (snd dspf) ds . fst)

public export
interpDStoDSFMap : (dspf : DSPF) -> DSCatEndofunctorFMap (interpDStoDS dspf)
interpDStoDSFMap (DS21 pos dir ** ds2dr) (a ** sa) (b ** sb) (m ** sm) =
  (\(i ** mi ** smi) =>
    (i ** m . mi ** \di1, di2 => sm (mi di1) $ smi di1 di2) **
   \(i ** mi ** smi), (j ** mj ** smj) =>
    (j ** m . mj ** \dj1, dj2 => sm (mj dj1) $ smj dj1 dj2))

public export
DSCatTr : DSCatObj -> DSCatObj -> DSCatObj
DSCatTr (v1 ** v2) (a1 ** a2) =
  (Either v1 a1 ** \x => case x of Left v => v2 v ; Right a => a2 a)

public export
DSCatFMN : Nat -> DSPF -> DSCatEndofunctorOMap
DSCatFMN Z dspf ds = ds
DSCatFMN (S n) dspf ds with (DSCatFMN n dspf ds)
  DSCatFMN (S n) dspf ds | dsn = DSCatTr dsn (interpDStoDS dspf dsn)

public export
DSCatFMN1 : Nat -> DSPF -> DSCatObj -> Type
DSCatFMN1 n dspf ds = fst (DSCatFMN n dspf ds)

public export
DSCatFMN2 : {n : Nat} -> {dspf : DSPF} ->
  (ds : DSCatObj) -> DSCatFMN1 n dspf ds -> Type
DSCatFMN2 {n} {dspf} ds = snd (DSCatFMN n dspf ds)
-}

-----------------------------------------
-----------------------------------------
---- Telescopes and functors on them ----
-----------------------------------------
-----------------------------------------

public export
TelSigN : Nat -> (ty : Type ** ty -> Type)
TelSigN Z = (Type ** id)
TelSigN (S n) with (TelSigN n)
  TelSigN (S n) | (tel ** sig) =
    ((pos : tel ** sig pos -> Type) ** \(pos ** dir) => Sigma {a=(sig pos)} dir)

public export
TelN : Nat -> Type
TelN = fst . TelSigN

public export
Tel : Type
Tel = DPair Nat TelN

public export
SigN : {n : Nat} -> TelN n -> Type
SigN {n} = snd (TelSigN n)

public export
TSig : Tel -> Type
TSig tel = SigN {n=(fst tel)} (snd tel)

public export
SlTelSigN : {n : Nat} -> (base : Fin (S n) -> Type) ->
  (ty : SliceObj (base Fin.last) ** Sigma ty -> Type)
SlTelSigN {n=Z} base = (const Type ** snd)
SlTelSigN {n=(S n)} base with (SlTelSigN {n} (base . FS))
  SlTelSigN {n=(S n)} base | (tel ** sig) =
    (\b => (pos : tel b ** sig (b ** pos) -> Type) **
     \(b ** (pos ** dir)) => Sigma {a=(sig (b ** pos))} dir)

{-
public export
TelNMorph : {n : Nat} -> TelN n -> TelN n -> Type
TelNMorph {n=Z} pos pos' = pos -> pos'
TelNMorph {n=(S n)} (pos ** dir) (pos' ** dir') =
  (onPos : pos -> pos' ** (i : pos) -> TelNMorph (dir i) (dir' (onPos i)))

public export
TelNSliceMorph : {n : Nat} -> {pos : Type} ->
  (dir, dir' : pos -> TelN n) -> Type
TelNSliceMorph {n} {pos} dir dir' = (i : pos) -> TelNMorph (dir i) (dir' i)

public export
TelNOMap : Nat -> Type
TelNOMap n = TelN n -> TelN n

public export
TelNFMap : {n : Nat} -> TelNOMap n -> Type
TelNFMap {n} f =
  (a, b : TelN n) -> TelNMorph {n} a b -> TelNMorph {n} (f a) (f b)

-- An `S n`-depth telescope is a type dependent on an `n`-depth telescope,
-- and as such may be treated as an arena which may be interpreted as either
-- a polynomial functor or a Dirichlet functor from `n`-depth telescopes
-- to `Type`.
public export
telSnAsPolyNtoType : {n : Nat} -> TelN (S n) -> TelN n -> Type
telSnAsPolyNtoType (pos ** dir) tel = (i : pos ** TelNMorph (dir i) tel)

public export
telSnAsDirichNtoType : {n : Nat} -> TelN (S n) -> TelN n -> Type
telSnAsDirichNtoType (pos ** dir) tel = (i : pos ** TelNMorph tel (dir i))

public export
TelSnToSn : {n : Nat} -> TelN (S n) -> Type
TelSnToSn {n} tel = fst tel -> TelN (S n)

public export
telSnToSnPolySnd : {n : Nat} -> {tsn : TelN (S (S n))} ->
  TelSnToSn {n=(S n)} tsn ->
  (tn : TelN (S n)) -> telSnAsPolyNtoType {n=(S n)} tsn tn -> TelN n
telSnToSnPolySnd {n=Z} {tsn=(posS ** dirS)} tsndep tn (i ** _) =
  (j : fst (tsndep i) ** TelNMorph {n=(S Z)} (snd (tsndep i) j) tn)
telSnToSnPolySnd {n=(S n)} {tsn=(posS ** dirS)} tsndep tn (i ** _) =
  ?telSnToSnPolySnd_hole_s

public export
telSnToSnDirichSnd : {n : Nat} -> {tsn : TelN (S (S n))} ->
  TelSnToSn {n=(S n)} tsn ->
  (tn : TelN (S n)) -> telSnAsDirichNtoType {n=(S n)} tsn tn -> TelN n
telSnToSnDirichSnd {n=Z} {tsn=(posS ** dirS)} tsndep tn (i ** _) =
  (j : fst (tsndep i) ** TelNMorph {n=(S Z)} tn (snd (tsndep i) j))
telSnToSnDirichSnd {n=(S n)} {tsn=(posS ** dirS)} tsndep tn (i ** _) =
  ?telSnToSnDirichSnd_hole_s

public export
TelNtoN : Nat -> Type
TelNtoN n = Sigma {a=(TelN (S n))} (TelSnToSn {n})

public export
telNtoNPoly : {n : Nat} -> TelNtoN (S n) -> TelNOMap (S n)
telNtoNPoly {n} (tsn ** tsndep) tn =
  (telSnAsPolyNtoType {n=(S n)} tsn tn **
   telSnToSnPolySnd {n} {tsn} tsndep tn)

public export
telNtoNDirich : {n : Nat} -> TelNtoN (S n) -> TelNOMap (S n)
telNtoNDirich {n} (tsn ** tsndep) tn =
  (telSnAsDirichNtoType {n=(S n)} tsn tn **
   telSnToSnDirichSnd {n} {tsn} tsndep tn)
  -}

----------------------------------------
----------------------------------------
---- Category-signature definitions ----
----------------------------------------
----------------------------------------

public export
SignatureT : Type -> Type
SignatureT = ProductMonad

public export
HomSlice : Type -> Type
HomSlice = SliceObj . SignatureT

-- The domain of the type of dependent signature-respecting relations on
-- morphisms over a given type of objects.
public export
SigRelObj : {obj : Type} -> SliceObj (HomSlice obj)
SigRelObj {obj} hom = DepRelObj {a=(SignatureT obj)} (hom, hom)

-- The type of dependent signature-respecting relations on
-- morphisms over a given type of objects.
public export
SigRelT : {obj : Type} -> SliceObj (HomSlice obj)
SigRelT {obj} hom = DepRelOn {a=(SignatureT obj)} (hom, hom)

public export
HomEndofunctor : Type -> Type
HomEndofunctor = SliceEndofunctor . SignatureT

public export
InternalCopresheaf : Type -> Type
InternalCopresheaf = SliceObj

public export
InternalCopresheafNT : {obj : Type} -> SliceObj obj -> SliceObj obj -> Type
InternalCopresheafNT {obj} = SliceMorphism {a=obj}

public export
CopresheafNTExtEq : {obj : Type} -> {f, g : InternalCopresheaf obj} ->
  (alpha, beta : InternalCopresheafNT f g) -> Type
CopresheafNTExtEq {obj} {f} {g} = SliceExtEq {a=obj} {s=f} {s'=g}

public export
InternalCovarHom : HomSlice obj -> obj -> SliceObj obj
InternalCovarHom hom = hom .* MkPair

public export
InternalContravarHom : HomSlice obj -> obj -> SliceObj obj
InternalContravarHom = flip . InternalCovarHom

public export
HomUncurry : (obj -> obj -> Type) -> HomSlice obj
HomUncurry hom (x, y) = hom x y

public export
InternalNTFromCovarHom : {obj : Type} ->
  (hom : HomSlice obj) -> obj -> SliceObj obj -> Type
InternalNTFromCovarHom {obj} hom =
  SliceMorphism {a=obj} . InternalCovarHom hom

public export
InternalNTFromContravarHom : {obj : Type} ->
  (hom : HomSlice obj) -> obj -> SliceObj obj -> Type
InternalNTFromContravarHom {obj} hom =
  SliceMorphism {a=obj} . InternalContravarHom hom

---------------------------------------------------------------
---------------------------------------------------------------
---- Standard (Mac Lane / Eilenberg) internal categories ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
record SCat where
  constructor SC
  scObj : Type
  scHom : HomSlice scObj
  scId : (a : scObj) -> scHom (a, a)
  scComp : {a, b, c : scObj} -> scHom (b, c) -> scHom (a, b) -> scHom (a, c)
  scEq : (sig : SignatureT scObj) -> EqRel (scHom sig)
  0 scIdL : {0 a, b : scObj} -> (f : scHom (a, b)) ->
    (scEq (a, b)).eqRel f (scComp {a} {b} {c=b} (scId b) f)
  0 scIdR : {0 a, b : scObj} -> (f : scHom (a, b)) ->
    (scEq (a, b)).eqRel f (scComp {a} {b=a} {c=b} f (scId a))
  0 scIdAssoc : {0 a, b, c, d : scObj} ->
    (f : scHom (a, b)) -> (g : scHom (b, c)) -> (h : scHom (c, d)) ->
    (scEq (a, d)).eqRel
      (scComp {a} {b=c} {c=d} h (scComp {a} {b} {c} g f))
      (scComp {a} {b} {c=d} (scComp {a=b} {b=c} {c=d} h g) f)

----------------------------------------
---- Standard-category Yoneda lemma ----
----------------------------------------

public export
SCCovarHomYonedaR :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  InternalNTFromCovarHom {obj=sc.scObj} sc.scHom a f -> f a
SCCovarHomYonedaR sc a f alpha = alpha a $ sc.scId a

public export
SCCovarHomYonedaL : (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  (fmap : (a, b : sc.scObj) -> sc.scHom (a, b) -> f a -> f b) ->
  f a -> InternalNTFromCovarHom {obj=sc.scObj} sc.scHom a f
SCCovarHomYonedaL sc a f fmap fa b mab = fmap a b mab fa

public export
SCContravarHomYonedaR :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  InternalNTFromContravarHom {obj=sc.scObj} sc.scHom a f -> f a
SCContravarHomYonedaR sc a f alpha = alpha a $ sc.scId a

public export
SCContravarHomYonedaL :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  -- f is contravariant
  (fmap : (a, b : sc.scObj) -> sc.scHom (a, b) -> f b -> f a) ->
  f a -> InternalNTFromContravarHom {obj=sc.scObj} sc.scHom a f
SCContravarHomYonedaL sc a f fmap fa b mba = fmap b a mba fa

-------------------------
-------------------------
---- Free categories ----
-------------------------
-------------------------

-- The (free-forgetful) adjunction which can be used to define a category
-- has the following data:
--
--  - Left category C: two-category of categories
--  - Right category D: category of diagrams
--  - Left functor L: free functor which adds identities (loop edges) for
--    each vertex and paths to represent compositions, and equalities for
--    left identity, right identity, and associativity
--  - Right functor R: forgetful functor which drops identity, composition,
--    and equalities, leaving just vertices and edges
--  - R . L (D -> D): Functor which closes a diagram with loops labeled
--    as identities and paths labeled as compositions
--  - L . R (C -> C): Identity functor
--  - Unit (id -> R . L): injection of diagram into its closure
--  - Counit (L . R -> id): identity natural transformation
--  - Adjuncts: (Hom(L A, B) == Hom(A, R B), for A : D and B : C):
--    functors from a free category generated from a diagram A to an arbitrary
--    category B are in bijection with graph homomorphisms from A to the
--    diagram underlying B (i.e. the diagram whose vertices are objects of B
--    and whose edges are morphisms of B)
--  - Left triangle identity: (counit . L) . (L . unit) = id(L):
--    expanded, for all A : D, counit(L(A)) . L(unit(A)) = id(L(A))
--    (which goes from L(A) to L(A) in C via L(R(L(A)))):
--      id(L(A)) . L(inj(A)) = id(L(A))
--    -- this reflects preservation of identities by functors
--  - Right triangle identity: (R . counit) . (unit . R) = id(R):
--    expanded, for all B : C, R(counit(B)) . unit(R(B)) = id(R(B))
--    (which goes from R(B) to R(B) in D via R(L(R(B)))):
--      id(forget(B)) . inj(forget(B)) = id(forget(B))
--    -- this reflects the definition of the injection

public export
data CatHomF : {0 obj : Type} -> HomEndofunctor obj where
  CHId :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    (x : obj) -> CatHomF {obj} hom (x, x)
  CHComp :
    {0 obj : Type} -> {0 hom : HomSlice obj} -> {x, y, z : obj} ->
    hom (y, z) -> hom (x, y) -> CatHomF {obj} hom (x, z)

public export
HomTranslateF : (obj : Type) -> HomSlice obj -> HomEndofunctor obj
HomTranslateF obj = SliceTranslateF {a=(SignatureT obj)} (CatHomF {obj})

public export
CatEitherF : {obj : Type} -> HomEndofunctor obj
CatEitherF {obj} = SliceTrEitherF {a=(SignatureT obj)} (CatHomF {obj})

public export
CEid : {obj : Type} -> {0 hom : HomSlice obj} ->
  (x : obj) -> CatEitherF {obj} hom (x, x)
CEid x = InSlC $ CHId x

public export
CEcomp : {obj : Type} -> {0 hom : HomSlice obj} ->
  {x, y, z: obj} -> hom (y, z) -> hom (x, y) -> CatEitherF {obj} hom (x, z)
CEcomp f g = InSlC $ CHComp f g

public export
FreeHomM : (obj : Type) -> HomEndofunctor obj
FreeHomM obj = SliceFreeM {a=(SignatureT obj)} (CatHomF {obj})

public export
TrHomF : (obj : Type) -> HomSlice obj -> HomEndofunctor obj
TrHomF obj = SliceTranslateF {a=(SignatureT obj)} (CatHomF {obj})

public export
chId : {obj : Type} ->
  (hom : HomSlice obj) -> (a : obj) -> FreeHomM obj hom (a, a)
chId {obj} hom a = InSlFc $ CHId a

public export
chComp : {obj : Type} -> {a, b, c : obj} -> {hom : HomSlice obj} ->
  FreeHomM obj hom (b, c) -> FreeHomM obj hom (a, b) -> FreeHomM obj hom (a, c)
chComp {obj} {a} {b} {c} {hom} g f = InSlFc $ CHComp g f

public export
HomSliceCata : Type -> Type
HomSliceCata obj = SliceFreeCata {a=(SignatureT obj)} (CatHomF {obj})

public export
homSliceCata : {obj : Type} -> HomSliceCata obj
homSliceCata {obj} sv sa subst alg (a, b) (InSlF (a, b) (InSlV v)) =
  subst (a, b) v
homSliceCata {obj} sv sa subst alg (a, b) (InSlF (a, b) (InSlC m)) =
  alg (a, b) $ case m of
    CHId c => CHId c
    CHComp {x} {y} {z} g f =>
      CHComp {x} {y} {z}
        (homSliceCata {obj} sv sa subst alg (y, z) g)
        (homSliceCata {obj} sv sa subst alg (x, y) f)

public export
InternalIdComp : {obj : Type} -> HomSlice obj -> Type
InternalIdComp {obj} hom = (a, b : obj) -> CatHomF hom (a, b) -> hom (a, b)

-- If a relation is already closed under identity and composition, then
-- we can replace freely-generated identities and compositions with the
-- internal ones.
public export
reduceHomSlice : {obj : Type} -> {hom : HomSlice obj} ->
  InternalIdComp {obj} hom ->
  {a, b : obj} -> FreeHomM obj hom (a, b) -> hom (a, b)
reduceHomSlice {obj} {hom} intIC {a} {b} =
  homSliceCata
    hom
    hom
    (\(x, y), m => m)
    (\(x, y), m => intIC x y m)
    (a, b)

public export
chFreeFMap : {obj : Type} -> {hom : HomSlice obj} -> {f : SliceObj obj} ->
  ((a, b : obj) -> hom (a, b) -> f a -> f b) ->
  ((a, b : obj) -> FreeHomM obj hom (a, b) -> f a -> f b)
chFreeFMap {obj} {hom} {f} fmap a b =
  homSliceCata hom (\(x, y) => f x -> f y)
    (\(x, y) => fmap x y)
    (\(x, z), m => case m of CHId z => id ; CHComp g f => g . f)
    (a, b)

public export
chFreeFContramap : {obj : Type} -> {hom : HomSlice obj} -> {f : SliceObj obj} ->
  ((a, b : obj) -> hom (a, b) -> f b -> f a) ->
  ((a, b : obj) -> FreeHomM obj hom (a, b) -> f b -> f a)
chFreeFContramap {obj} {hom} {f} fmap a b =
  homSliceCata hom (\(x, y) => f y -> f x)
    (\(x, y) => fmap x y)
    (\(x, z), m => case m of CHId z => id ; CHComp g f => f . g)
    (a, b)

public export
FreeHomRel : {obj : Type} -> SliceObj (HomSlice obj)
FreeHomRel {obj} hom =
  DepRelOn {a=(SignatureT obj)} (FreeHomM obj hom, FreeHomM obj hom)

public export
FreeHomEqF : {obj : Type} -> (hom : HomSlice obj) ->
  FreeHomRel {obj} hom -> FreeHomRel {obj} hom
FreeHomEqF {obj} hom = DepFreeEqF {a=(SignatureT obj)} {sl=(FreeHomM obj hom)}

public export
CatRelObj : {obj : Type} -> SliceObj (HomSlice obj)
CatRelObj {obj} hom = SigRelObj {obj} (FreeHomM obj hom)

public export
CatRelT : {obj : Type} -> SliceObj (HomSlice obj)
CatRelT {obj} hom = SigRelT {obj} (FreeHomM obj hom)

public export
data SigToCatRel : {obj : Type} -> {hom : HomSlice obj} ->
    SigRelT {obj} hom -> CatRelT {obj} hom where
  StoCR : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 rv : SigRelT hom} ->
    {0 a, b : obj} -> {0 f, g : hom (a, b)} ->
    rv ((a, b) ** (f, g)) ->
    SigToCatRel {obj} {hom} rv ((a, b) ** (InSlFv f, InSlFv g))

public export
SigToCatRelToSigRel : {obj : Type} -> {hom : HomSlice obj} ->
  (rel : SigRelT {obj} hom) -> {0 a, b : obj} ->
  {0 f, g : hom (a, b)} ->
  SigToCatRel rel ((a, b) ** (InSlFv f, InSlFv g)) ->
  rel ((a, b) ** (f, g))
SigToCatRelToSigRel rel (StoCR relobj) = relobj

public export
FreeHomJoin : Type -> Type
FreeHomJoin obj = SliceFreeJoin {a=(SignatureT obj)} (CatHomF {obj})

public export
freeHomJoin : {obj : Type} -> FreeHomJoin obj
freeHomJoin = sliceFreeJoin homSliceCata

public export
data CatEqAx : {obj : Type} -> {hom : HomSlice obj} -> CatRelT hom where
  CEidL :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 a, b : obj} -> (0 f : FreeHomM obj hom (a, b)) ->
    CatEqAx {obj} {hom} ((a, b) ** (f, chComp (chId hom b) f))
  CEidR :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 a, b : obj} -> (0 f : FreeHomM obj hom (a, b)) ->
    CatEqAx {obj} {hom} ((a, b) ** (f, chComp f (chId hom a)))
  CEassoc :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 a, b, c, d : obj} ->
    (0 f : FreeHomM obj hom (a, b)) ->
    (0 g : FreeHomM obj hom (b, c)) ->
    (0 h : FreeHomM obj hom (c, d)) ->
    CatEqAx {obj} {hom}
      ((a, d) ** (chComp h (chComp g f), chComp (chComp h g) f))

public export
data CatFreeEqF : {obj : Type} -> {hom : HomSlice obj} ->
    CatRelT hom -> CatRelT hom where
  CEax : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 ra : CatRelT hom} ->
    {0 a, b : obj} -> {0 f, g : FreeHomM obj hom (a, b)} ->
    CatEqAx {obj} {hom} ((a, b) ** (f, g)) ->
    CatFreeEqF {obj} {hom} ra ((a, b) ** (f, g))
  CErewL : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 ra : CatRelT hom} ->
    {0 a, b, c : obj} -> {0 f, g : FreeHomM obj hom (b, c)} ->
    (0 _ : ra ((b, c) ** (f, g))) ->
    (0 h : FreeHomM obj hom (a, b)) ->
    CatFreeEqF {obj} {hom} ra ((a, c) ** (chComp f h, chComp g h))
  CErewR : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 ra : CatRelT hom} ->
    {0 a, b, c : obj} -> {0 f, g : FreeHomM obj hom (a, b)} ->
    (0 _ : ra ((a, b) ** (f, g))) ->
    (0 h : FreeHomM obj hom (b, c)) ->
    CatFreeEqF {obj} {hom} ra ((a, c) ** (chComp h f, chComp h g))
  CEeq : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 ra : CatRelT hom} ->
    {0 a, b : obj} -> {0 f, g : FreeHomM obj hom (a, b)} ->
    FreeHomEqF {obj} hom ra ((a, b) ** (f, g)) ->
    CatFreeEqF {obj} {hom} ra ((a, b) ** (f, g))

-- Extend a relation on a freely-generated hom-slice to a congruence:
-- that is, close it under equivalence, and propagate equivalence
-- through composition.
public export
CatFreeEq : {obj : Type} -> {hom : HomSlice obj} -> (rel : CatRelT hom) ->
  CatRelT hom
CatFreeEq {obj} {hom} rel =
  SliceFreeM
    {a=(CatRelObj {obj} hom)}
    (CatFreeEqF {obj} {hom})
    rel

public export
CatEqToFree : {obj : Type} -> {hom : HomSlice obj} ->
  CatRelT hom -> CatRelT (FreeHomM obj hom)
CatEqToFree {obj} {hom} rel = CatFreeEq $ \((x, y) ** (eqx, eqy)) =>
  rel ((x, y) ** (freeHomJoin hom (x, y) eqx, freeHomJoin hom (x, y) eqy))

public export
CatEqFromFree : {obj : Type} -> {hom : HomSlice obj} ->
  CatRelT (FreeHomM obj hom) -> CatRelT hom
CatEqFromFree {obj} {hom} rel ((x, y) ** (f, g)) =
  rel ((x, y) ** (InSlFv f, InSlFv g))

-- Extend a relation on a hom-slice to a congruence on its freely-generated
-- hom-slice:  that is, close it under equivalence, and propagate equivalence
-- through composition.
public export
SigCatFreeEq : {obj : Type} -> {hom : HomSlice obj} -> (rel : SigRelT hom) ->
  CatRelT hom
SigCatFreeEq {obj} {hom} rel = CatFreeEq {obj} {hom} (SigToCatRel rel)

public export
CatFreeEqCata : {obj : Type} -> HomSlice obj -> Type
CatFreeEqCata {obj} hom =
  SliceFreeCata {a=(CatRelObj {obj} hom)} (CatFreeEqF {obj} {hom})

public export
CatFreeEqCataF : {obj : Type} -> HomSlice obj -> Type
CatFreeEqCataF {obj} hom =
  SliceFreeCataF {a=(CatRelObj {obj} hom)} (CatFreeEqF {obj} {hom})

mutual
  public export
  catFreeEqCata : {obj : Type} -> {hom : HomSlice obj} ->
    CatFreeEqCata {obj} hom
  catFreeEqCata {obj} {hom} sv sa subst alg m (InSlF m (InSlV v)) =
    subst m v
  catFreeEqCata {obj} {hom} sv sa subst alg m (InSlF m (InSlC eq)) =
    catFreeEqCataF sv sa subst alg m eq

  public export
  catFreeEqCataF : {obj : Type} -> {hom : HomSlice obj} ->
    CatFreeEqCataF {obj} hom
  catFreeEqCataF {obj} {hom} sv sa subst alg m eq =
    alg m $ case eq of
      CEax ax => CEax ax
      CErewL feq f => CErewL (catFreeEqCata {obj} {hom} sv sa subst alg _ feq) f
      CErewR feq f => CErewR (catFreeEqCata {obj} {hom} sv sa subst alg _ feq) f
      CEeq feq => CEeq $ case feq of
        DFErefl f => DFErefl f
        DFEsym eq => DFEsym $ catFreeEqCata {obj} {hom} sv sa subst alg _ eq
        DFEtrans eq eq' =>
          DFEtrans
            (catFreeEqCata {obj} {hom} sv sa subst alg _ eq)
            (catFreeEqCata {obj} {hom} sv sa subst alg _ eq')

public export
CatFreeEqJoin : {obj : Type} -> HomSlice obj -> Type
CatFreeEqJoin {obj} hom =
  SliceFreeJoin {a=(CatRelObj {obj} hom)} (CatFreeEqF {obj} {hom})

public export
catFreeEqJoin : {obj : Type} -> {hom : HomSlice obj} -> CatFreeEqJoin {obj} hom
catFreeEqJoin = sliceFreeJoin catFreeEqCata

public export
IsCongruence : {obj : Type} -> {hom : HomSlice obj} -> CatRelT hom -> Type
IsCongruence {obj} {hom} rel =
  (x, y : obj) -> (f, g : FreeHomM obj hom (x, y)) ->
  CatFreeEqF {obj} {hom} rel ((x, y) ** (f, g)) -> rel ((x, y) ** (f, g))

public export
reduceCatFreeEq : {obj : Type} -> {hom : HomSlice obj} -> {rel : CatRelT hom} ->
  IsCongruence rel ->
  {x, y : obj} -> {f, g : FreeHomM obj hom (x, y)} ->
  CatFreeEq {obj} {hom} rel ((x, y) ** (f, g)) -> rel ((x, y) ** (f, g))
reduceCatFreeEq {obj} {hom} {rel} cong {x} {y} {f} {g} =
  catFreeEqCata
    rel
    rel
    (\_ => id)
    (\((x, y) ** (f, g)), eq => cong x y f g eq)
    ((x, y) ** (f, g))

public export
record PreDiagram where
  constructor MkPreDiag
  pdVert : Type
  pdEdge : HomSlice pdVert

public export
PreDiagFreeHom : (diag : PreDiagram) -> HomSlice (pdVert diag)
PreDiagFreeHom diag = FreeHomM (pdVert diag) (pdEdge diag)

public export
preDiagFreeId :
  (diag : PreDiagram) -> (a : pdVert diag) -> PreDiagFreeHom diag (a, a)
preDiagFreeId diag a = chId (pdEdge diag) a

public export
preDiagFreeComp : {diag : PreDiagram} -> {a, b, c : pdVert diag} ->
  PreDiagFreeHom diag (b, c) -> PreDiagFreeHom diag (a, b) ->
  PreDiagFreeHom diag (a, c)
preDiagFreeComp {diag} g f = chComp {hom=(pdEdge diag)} g f

public export
record Diagram where
  constructor MkDiag
  dPre : PreDiagram
  -- `dRel` is a relation which, when we freely generate a category from
  -- the diagram, will freely generate an equivalence relation, but `dRel`
  -- itself does not promise to be an equivalence relation.
  dRel : CatRelT dPre.pdEdge

public export
MkDiagram :
  (vert : Type) -> (edge : HomSlice vert) -> (rel : CatRelT edge) -> Diagram
MkDiagram vert edge rel = MkDiag (MkPreDiag vert edge) rel

public export
dVert : Diagram -> Type
dVert = pdVert . dPre

public export
dEdge : (dgm : Diagram) -> HomSlice (dVert dgm)
dEdge dgm = pdEdge (dPre dgm)

public export
catToDiagForgetRel : (sc : SCat) -> CatRelT {obj=sc.scObj} sc.scHom
catToDiagForgetRel sc (sig ** (InSlF sig f, InSlF sig g)) =
  case f of
    InSlV f' => case g of
      InSlV g' => eqRel (sc.scEq sig) f' g'
      InSlC g' => Void
    InSlC f' => Void

public export
catToDiagForget : SCat -> Diagram
catToDiagForget sc =
  MkDiagram sc.scObj sc.scHom (catToDiagForgetRel sc)

public export
DiagFreeObj : Diagram -> Type
DiagFreeObj diag = dVert diag

public export
DiagFreeSig : Diagram -> Type
DiagFreeSig = SignatureT . DiagFreeObj

public export
DiagFreeHom : (diag : Diagram) -> HomSlice (DiagFreeObj diag)
DiagFreeHom diag = PreDiagFreeHom (dPre diag)

public export
diagFreeId :
  (diag : Diagram) -> (a : DiagFreeObj diag) -> DiagFreeHom diag (a, a)
diagFreeId diag a = preDiagFreeId (dPre diag) a

public export
diagFreeComp : {diag : Diagram} -> {a, b, c : DiagFreeObj diag} ->
  DiagFreeHom diag (b, c) -> DiagFreeHom diag (a, b) -> DiagFreeHom diag (a, c)
diagFreeComp {diag} g f = chComp {hom=(dEdge diag)} g f

public export
DiagFreeCatRel : (diag : Diagram) -> CatRelT (dEdge diag)
DiagFreeCatRel diag =
  CatFreeEq {obj=(dVert diag)} {hom=(dEdge diag)} diag.dRel

public export
DiagFreeRel : (diag : Diagram) -> (sig : DiagFreeSig diag) ->
  RelationOn (DiagFreeHom diag sig)
DiagFreeRel diag sig f g = DiagFreeCatRel diag (sig ** (f, g))

public export
DiagFreeRelIsRefl : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsReflexive (DiagFreeRel diag (a, b))
DiagFreeRelIsRefl diag a b f =
  InSlFc $ CEeq $ DFErefl f

public export
DiagFreeRelIsSym : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsSymmetric (DiagFreeRel diag (a, b))
DiagFreeRelIsSym diag a b {x=f} {y=g} eq =
  InSlFc $ CEeq $ DFEsym eq

public export
DiagFreeRelIsTrans : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsTransitive (DiagFreeRel diag (a, b))
DiagFreeRelIsTrans diag a b {x=f} {y=g} {z=h} eqfg eqgh =
  InSlFc $ CEeq $ DFEtrans eqgh eqfg

public export
DiagFreeRelIsEquiv : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsEquivalence (DiagFreeRel diag (a, b))
DiagFreeRelIsEquiv diag a b =
  MkEquivalence
    (DiagFreeRelIsRefl diag a b)
    (DiagFreeRelIsSym diag a b)
    (DiagFreeRelIsTrans diag a b)

public export
DiagFreeEqRel : (diag : Diagram) -> (sig : DiagFreeSig diag) ->
  EqRel (DiagFreeHom diag sig)
DiagFreeEqRel diag (a, b) =
  MkEq (DiagFreeRel diag (a, b)) (DiagFreeRelIsEquiv diag a b)

public export
DiagFreeIdL : (diag : Diagram) -> {a, b : DiagFreeObj diag} ->
  (f : DiagFreeHom diag (a, b)) ->
  DiagFreeRel diag (a, b) f (diagFreeComp {diag} (diagFreeId diag b) f)
DiagFreeIdL diag {a} {b} f =
  InSlF ((a, b) ** (f, diagFreeComp (diagFreeId diag b) f)) $
    InSlC $ CEax $ CEidL f

public export
DiagFreeIdR : (diag : Diagram) -> {a, b : DiagFreeObj diag} ->
  (f : DiagFreeHom diag (a, b)) ->
  DiagFreeRel diag (a, b) f (diagFreeComp {diag} f (diagFreeId diag a))
DiagFreeIdR diag {a} {b} f =
  InSlF ((a, b) ** (f, diagFreeComp f (diagFreeId diag a))) $
    InSlC $ CEax $ CEidR f

public export
DiagFreeAssoc : (diag : Diagram) -> {a, b, c, d : DiagFreeObj diag} ->
  (f : DiagFreeHom diag (a, b)) ->
  (g : DiagFreeHom diag (b, c)) ->
  (h : DiagFreeHom diag (c, d)) ->
  DiagFreeRel diag (a, d)
    (diagFreeComp {diag} h (diagFreeComp {diag} g f))
    (diagFreeComp {diag} (diagFreeComp {diag} h g) f)
DiagFreeAssoc diag {a} {b} {c} {d} f g h =
  InSlF
    ((a, d) **
     (diagFreeComp {diag} h (diagFreeComp {diag} g f),
      diagFreeComp {diag} (diagFreeComp {diag} h g) f)) $
    InSlC $ CEax $ CEassoc f g h

public export
DiagToFreeCat : Diagram -> SCat
DiagToFreeCat diag =
  SC
    (DiagFreeObj diag)
    (DiagFreeHom diag)
    (diagFreeId diag)
    (diagFreeComp {diag})
    (DiagFreeEqRel diag)
    (DiagFreeIdL diag)
    (DiagFreeIdR diag)
    (DiagFreeAssoc diag)

--------------------------------------------
--------------------------------------------
---- Functors as morphisms of diagrams ----
--------------------------------------------
--------------------------------------------

public export
sigMap : (obj -> obj') -> SignatureT obj -> SignatureT obj'
sigMap m (a, b) = (m a, m b)

public export
HomMap : {obj, obj' : Type} ->
  (m : obj -> obj') -> HomSlice obj -> HomSlice obj' -> Type
HomMap {obj} m sl sl' = SliceMorphism {a=(SignatureT obj)} sl (sl' . sigMap m)

-- This converts the domain of the type of witnesses to a relation on the
-- domain of a given hom-map to the domain of the type of witnesses to the
-- relation induced in the codomain of the hom-map by the hom-map itself:
-- that is, the relation which relates any two morphisms `hm(f)` and `hm(g)`
-- in the codomain of the hom-map if if `f` and `g` are related in the domain
-- of the hom-map.  (Note that if a given morphism of the codomain is not in the
-- range of the hom-map, then it is not related to any morphisms in the
-- induced relation.)
public export
homSigObjMap : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  HomMap {obj} {obj'} m sl sl' -> SigRelObj sl -> SigRelObj sl'
homSigObjMap {obj} {obj'} {m} {sl} {sl'} hm ((a, b) ** (f, g)) =
  ((m a, m b) ** (hm (a, b) f, hm (a, b) g))

public export
FreeHomMap : {obj, obj' : Type} ->
  (m : obj -> obj') -> HomSlice obj -> HomSlice obj' -> Type
FreeHomMap {obj} {obj'} m sl sl' = HomMap {obj} {obj'} m sl (FreeHomM obj' sl')

public export
CatHomMap : {obj, obj' : Type} ->
  (m : obj -> obj') -> HomSlice obj -> HomSlice obj' -> Type
CatHomMap {obj} {obj'} m sl sl' =
  FreeHomMap {obj} {obj'} m (FreeHomM obj sl) sl'

public export
homMapExtendRight : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  HomMap m sl sl' -> FreeHomMap m sl sl'
homMapExtendRight {obj} {obj'} {m} {sl} {sl'} hm sig f = InSlFv $ hm sig f

public export
sigMapCommute : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  {sig : (obj, obj)} ->
  CatHomF (FreeHomM obj' sl' . sigMap m) sig ->
  CatHomF (FreeHomM obj' sl') (sigMap m sig)
sigMapCommute {m} (CHId x) = CHId $ m x
sigMapCommute {m} (CHComp {x} {y} {z} g f) =
  CHComp {x=(m x)} {y=(m y)} {z=(m z)} g f

public export
sigMapCompose : {obj, obj', obj'' : Type} ->
  {m : obj -> obj'} -> {m' : obj' -> obj''} ->
  {sl : HomSlice obj} -> {sl' : HomSlice obj'} -> {sl'' : HomSlice obj''} ->
  {sig : (obj, obj)} ->
  (FreeHomM obj'' sl'' . sigMap m' . sigMap m) sig ->
  (FreeHomM obj'' sl'' . sigMap (m' . m)) sig
sigMapCompose {sig=(x, y)} (InSlF _ f) = InSlF _ f

public export
freeHomMapExtendLeft : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  FreeHomMap m sl sl' -> CatHomMap m sl sl'
freeHomMapExtendLeft {obj} {obj'} {m} {sl} {sl'} hm =
  homSliceCata sl (FreeHomM obj' sl' . sigMap m) hm
    (\sig', f' => InSlFc $ sigMapCommute {sl} f')

public export
homMapExtendBoth : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  HomMap m sl sl' -> CatHomMap m sl sl'
homMapExtendBoth = freeHomMapExtendLeft . homMapExtendRight

-- This converts the domain of the type of witnesses to a relation on the
-- domain of a given free hom-map (that is, a hom-map whose codomain is a
-- freely-generated category) to the domain of the type of witnesses to the
-- relation induced in the codomain of the hom-map by the left extension of
-- the hom-map itself.
public export
freeRelObjMap : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  FreeHomMap {obj} {obj'} m sl sl' ->
  CatRelObj sl -> CatRelObj sl'
freeRelObjMap {obj} {obj'} {m} {sl} {sl'} = homSigObjMap . freeHomMapExtendLeft

-- A term of this type is a proof that a `HomMap` respects a
-- relation on morphisms.
public export
HomRelMapCorrect : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  HomMap {obj} {obj'} m sl sl' -> SigRelT sl -> SigRelT sl' -> Type
HomRelMapCorrect {obj} {obj'} {m} {sl} {sl'} hm rel rel' =
  SliceMorphism {a=(SigRelObj sl)} rel (rel' . homSigObjMap hm)

-- A term of this type is a proof that the left extension of a `FreeHomMap`
-- respects a morphism-equivalence relation.
public export
FreeHomRelMapLeftExtensionCorrect : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  FreeHomMap {obj} {obj'} m sl sl' ->
  CatRelT sl -> CatRelT sl' ->
  Type
FreeHomRelMapLeftExtensionCorrect {obj} {obj'} {m} {sl} {sl'} hm rel rel' =
  HomRelMapCorrect {sl=(FreeHomM obj sl)} {sl'=(FreeHomM obj' sl')}
    (freeHomMapExtendLeft hm) (CatFreeEq rel) (CatFreeEq rel')

-- A morphism between diagrams induces a functor between the categories
-- represented by the diagrams.  We call this a "pre-morphism" because it
-- does not contain a proof that it preserves the morphism equivalence
-- relations.
public export
record PreDiagMorphism (dom, cod : PreDiagram) where
  constructor MkPreDiagM
  dfpVmap : pdVert dom -> pdVert cod
  dfpEmap : FreeHomMap {obj=(pdVert dom)} dfpVmap (pdEdge dom) (pdEdge cod)

public export
DiagPreMorphism : (dom, cod : Diagram) -> Type
DiagPreMorphism dom cod = PreDiagMorphism (dPre dom) (dPre cod)

public export
MkDiagPreM : {dom, cod : Diagram} ->
  (vmap : dVert dom -> dVert cod) ->
  (emap : FreeHomMap vmap (dEdge dom) (dEdge cod)) ->
  DiagPreMorphism dom cod
MkDiagPreM = MkPreDiagM

-- A pre-morphism together with a proof that it preserves the morphism
-- equivalence relations (that is, two equivalent morphisms in the domain
-- are mapped to equivalent morphisms in the codomain).
public export
record DiagMorphism (dom, cod : Diagram) where
  constructor MkDiagM
  dmPreM : DiagPreMorphism dom cod
  0 dmRmapCorrect :
    FreeHomRelMapLeftExtensionCorrect
      {m=dmPreM.dfpVmap} dmPreM.dfpEmap dom.dRel cod.dRel

public export
MkDiagMorph : {dom, cod : Diagram} ->
  (vmap : dVert dom -> dVert cod) ->
  (emap : FreeHomMap vmap (dEdge dom) (dEdge cod)) ->
  FreeHomRelMapLeftExtensionCorrect {m=vmap} emap dom.dRel cod.dRel ->
  DiagMorphism dom cod
MkDiagMorph {dom} {cod} vmap emap rmap = MkDiagM (MkDiagPreM vmap emap) rmap

public export
dpVmap : {dom, cod : Diagram} -> DiagMorphism dom cod ->
  dVert dom -> dVert cod
dpVmap m = m.dmPreM.dfpVmap

public export
dpEmap : {dom, cod : Diagram} -> (m : DiagMorphism dom cod) ->
  FreeHomMap {obj=(dVert dom)} (dpVmap m) (dEdge dom) (dEdge cod)
dpEmap m = m.dmPreM.dfpEmap

-- Given a hom-map between diagrams, we can generate a closure of the
-- codomain's equivalence relation which includes equivalences between
-- all pairs of morphisms which are mapped from equivalent morphisms
-- in the domain -- in other words, we coequalize the codomain relation
-- using the hom-map.
public export
HomRelImage : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  CatHomMap {obj} {obj'} m sl sl' ->
  CatRelT sl -> CatRelT sl'
HomRelImage {obj} {obj'} {m} {sl} {sl'} hm rel o@((x', y') ** (f', g')) =
  (x : obj ** y : obj **
   f : FreeHomM obj sl (x, y) ** g : FreeHomM obj sl (x, y) **
   eqx : m x = x' ** eqy : m y = y' **
   eqf : hm (x, y) f = (rewrite eqx in rewrite eqy in f') **
   hm (x, y) g = (rewrite eqx in rewrite eqy in g'))

public export
FreeHomRelCoeq : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  FreeHomMap {obj} {obj'} m sl sl' ->
  CatRelT sl -> CatRelT sl' -> CatRelT sl'
FreeHomRelCoeq {obj} {obj'} {m} {sl} {sl'} hm rel rel' =
  SliceTranslateF Prelude.id rel' (HomRelImage (freeHomMapExtendLeft hm) rel)

public export
FreeHomRelCoeqClosure : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  FreeHomMap {obj} {obj'} m sl sl' ->
  CatRelT sl -> CatRelT sl' -> CatRelT sl'
FreeHomRelCoeqClosure hm rel rel' = CatFreeEq (FreeHomRelCoeq hm rel rel')

public export
FreeHomRelCoeqClosureIncludesRel : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  (hm : FreeHomMap {obj} {obj'} m sl sl') ->
  (rel : CatRelT sl) -> (rel' : CatRelT sl') ->
  (o' : CatRelObj sl') -> rel' o' -> FreeHomRelCoeqClosure {m} hm rel rel' o'
FreeHomRelCoeqClosureIncludesRel {obj} {obj'} {m} {sl} {sl'} hm rel rel' _ =
  InSlFv . InSlV

-- A hom-map maps equivalences from its domain to equivalences in the
-- closure of the coequalizer of its codomain.
public export
FreeHomRelCoeqClosureCorrect : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  (hm : FreeHomMap {obj} {obj'} m sl sl') ->
  (rel : CatRelT sl) -> (rel' : CatRelT sl') ->
  FreeHomRelMapLeftExtensionCorrect
    {m} hm rel (FreeHomRelCoeqClosure {m} hm rel rel')
FreeHomRelCoeqClosureCorrect {obj} {obj'} {m} {sl} {sl'} hm rel rel' =
  catFreeEqCata
    rel
    (CatFreeEq (FreeHomRelCoeqClosure hm rel rel') . freeRelObjMap hm)
    (\((x, y) ** (f, g)), relfg => InSlFv $ InSlFv $ InSlC
      (x ** y ** f ** g ** Refl ** Refl ** Refl ** Refl))
    (\((x, y) ** (f, g)), relfg => InSlFv $ InSlFv $ InSlC
      (x ** y ** f ** g ** Refl ** Refl ** Refl ** Refl))

-- Given a diagram pre-morphism, we can generate a diagram morphism
-- from the domain to the coequalized codomain.
public export
DiagCoeq : {dom, cod : Diagram} -> DiagPreMorphism dom cod -> Diagram
DiagCoeq {dom} {cod} m =
  MkDiagram
    (dVert cod)
    (dEdge cod)
    (FreeHomRelCoeqClosure {m=m.dfpVmap} m.dfpEmap dom.dRel cod.dRel)

public export
DiagPreMorphismClosure : {dom, cod : Diagram} ->
  (m : DiagPreMorphism dom cod) -> DiagMorphism dom (DiagCoeq {dom} {cod} m)
DiagPreMorphismClosure {dom} {cod} m =
  case cod of
    MkDiag (MkPreDiag codVert codEdge) codRel =>
      MkDiagMorph {dom} {cod=(DiagCoeq {dom} {cod} m)}
        m.dfpVmap
        m.dfpEmap
        (FreeHomRelCoeqClosureCorrect m.dfpEmap dom.dRel codRel)

public export
PreDiagId : (c : PreDiagram) -> PreDiagMorphism c c
PreDiagId c = MkPreDiagM id $ \(_, _) => InSlFv

public export
0 DiagIdPreservesRel : (c : Diagram) ->
  FreeHomRelMapLeftExtensionCorrect {m=Prelude.id}
    (dfpEmap $ PreDiagId $ dPre c) c.dRel c.dRel
DiagIdPreservesRel c = ?DiagId_preserves_rel_hole

public export
DiagId : (c : Diagram) -> DiagMorphism c c
DiagId c = MkDiagM (PreDiagId $ dPre c) (DiagIdPreservesRel c)

public export
PreDiagComposeVert : {c, d, e : PreDiagram} ->
  PreDiagMorphism d e -> PreDiagMorphism c d -> (pdVert c -> pdVert e)
PreDiagComposeVert {c} {d} {e} g f = dfpVmap g . dfpVmap f

public export
PreDiagComposeEdge : {c, d, e : PreDiagram} ->
  (g : PreDiagMorphism d e) -> (f: PreDiagMorphism c d) ->
  FreeHomMap (PreDiagComposeVert g f) (pdEdge c) (pdEdge e)
PreDiagComposeEdge {c} {d} {e} g f sig =
  sigMapCompose
    {m=(dfpVmap f)} {m'=(dfpVmap g)}
    {sl=(pdEdge c)} {sl'=(pdEdge d)} {sl''=(pdEdge e)} .
    freeHomMapExtendLeft (dfpEmap g) (sigMap (dfpVmap f) sig) . dfpEmap f sig

public export
PreDiagCompose : {c, d, e : PreDiagram} ->
  PreDiagMorphism d e -> PreDiagMorphism c d -> PreDiagMorphism c e
PreDiagCompose g f =
  MkPreDiagM (PreDiagComposeVert g f) (PreDiagComposeEdge g f)

public export
0 PreDiagComposePreservesRelMap : {c, d, e : PreDiagram} ->
  (g : PreDiagMorphism d e) -> (f: PreDiagMorphism c d) ->
  {relc : CatRelT (pdEdge c)} ->
  {reld : CatRelT (pdEdge d)} ->
  {rele : CatRelT (pdEdge e)} ->
  FreeHomRelMapLeftExtensionCorrect {m=(dfpVmap g)} (dfpEmap g) reld rele ->
  FreeHomRelMapLeftExtensionCorrect {m=(dfpVmap f)} (dfpEmap f) relc reld ->
  FreeHomRelMapLeftExtensionCorrect {m=(PreDiagComposeVert g f)}
    (PreDiagComposeEdge g f) relc rele
PreDiagComposePreservesRelMap {c} {d} {e} g f {relc} {reld} {rele} grel frel =
  ?PreDiagComposePreservesRelMap_hole

public export
DiagCompose : {c, d, e : Diagram} ->
  DiagMorphism d e -> DiagMorphism c d -> DiagMorphism c e
DiagCompose g f =
  MkDiagM
    (PreDiagCompose (dmPreM g) (dmPreM f))
    (PreDiagComposePreservesRelMap
      (dmPreM g) (dmPreM f) (dmRmapCorrect g) (dmRmapCorrect f))

--------------------------------------------------------
--------------------------------------------------------
---- Category of diagrams and diagram pre-morphisms ----
--------------------------------------------------------
--------------------------------------------------------

public export
0 IsId : {0 c : Diagram} -> {0 x : DiagFreeObj c} ->
  (0 m : DiagFreeHom c (x, x)) -> Type
IsId {c} {x} m = DiagFreeCatRel c ((x, x) ** (m, diagFreeId c x))

public export
0 CompIsId : {0 c : Diagram} -> {0 x, y : DiagFreeObj c} ->
  (0 g : DiagFreeHom c (y, x)) -> (0 f : DiagFreeHom c (x, y)) ->
  Type
CompIsId {c} {x} {y} g f = IsId {c} {x} (diagFreeComp g f)

public export
0 AreInverses : {0 c : Diagram} -> {0 x, y : DiagFreeObj c} ->
  (0 g : DiagFreeHom c (y, x)) -> (0 f : DiagFreeHom c (x, y)) ->
  Type
AreInverses {c} {x} {y} g f =
  (CompIsId {c} {x} {y} g f, CompIsId {c} {x=y} {y=x} f g)

public export
IsIso : {0 c : Diagram} -> {0 x, y : DiagFreeObj c} ->
  (0 f : DiagFreeHom c (x, y)) -> Type
IsIso {c} {x} {y} f = Exists0 (DiagFreeHom c (y, x)) (AreInverses f)

-- A two-morphism in the two-category of pre-diagrams is a natural
-- transformation between the functors represented by two pre-morphisms.
public export
record PreDiagTwoMorph {c, d : PreDiagram} (f, g : PreDiagMorphism c d) where
  constructor MkPD2Morph
  pd2Component : (x : pdVert c) -> PreDiagFreeHom d (dfpVmap f x, dfpVmap g x)

public export
PreDiagTwoId : {c, d : PreDiagram} -> (f : PreDiagMorphism c d) ->
  PreDiagTwoMorph f f
PreDiagTwoId {c} {d} f = MkPD2Morph $ \x => preDiagFreeId d (dfpVmap f x)

public export
record DiagTwoMorph {c, d : Diagram} (f, g : DiagMorphism c d) where
  constructor MkD2Morph
  d2Pre : PreDiagTwoMorph {c=(dPre c)} {d=(dPre d)} (dmPreM f) (dmPreM g)
  0 d2IsNatural : (x, y : DiagFreeObj c) -> (m : DiagFreeHom c (x, y)) ->
    DiagFreeCatRel d
      ((dpVmap f x, dpVmap g y) **
       (diagFreeComp {diag=d}
        (freeHomMapExtendLeft {m=(dpVmap g)} (dpEmap g) (x, y) m)
        (pd2Component d2Pre x),
        diagFreeComp {diag=d}
          (pd2Component d2Pre y)
          (freeHomMapExtendLeft {m=(dpVmap f)} (dpEmap f) (x, y) m)))

public export
d2Component : {c, d : Diagram} -> {f, g : DiagMorphism c d} ->
  DiagTwoMorph {c} {d} f g ->
  (x : DiagFreeObj c) -> DiagFreeHom d (dpVmap f x, dpVmap g x)
d2Component {c} {d} {f} {g} alpha = pd2Component (d2Pre alpha)

public export
DiagTwoId : {c, d : Diagram} -> (f : DiagMorphism c d) -> DiagTwoMorph f f
DiagTwoId {c} {d} f =
  MkD2Morph (PreDiagTwoId $ dmPreM f) ?DiagTwoId_isNatural_hole

public export
DiagTwoMorphEquiv : {c, d : Diagram} -> {f, g : DiagMorphism c d} ->
  DiagTwoMorph {c} {d} f g -> DiagTwoMorph {c} {d} f g -> Type
DiagTwoMorphEquiv {c} {d} {f} {g} alpha beta =
  (x : DiagFreeObj c) ->
    DiagFreeCatRel d
      ((dpVmap f x, dpVmap g x) ** (d2Component alpha x, d2Component beta x))

public export
PreDiagTwoMorphVComp : {c, d : PreDiagram} -> {f, g, h : PreDiagMorphism c d} ->
  PreDiagTwoMorph {c} {d} g h -> PreDiagTwoMorph {c} {d} f g ->
  PreDiagTwoMorph {c} {d} f h
PreDiagTwoMorphVComp {c} {d} {f} {g} {h} beta alpha =
  MkPD2Morph $ \x : pdVert c =>
    preDiagFreeComp (pd2Component beta x) (pd2Component alpha x)

public export
PreDiagTwoMorphHComp : {c, d, e : PreDiagram} ->
  {f, g : PreDiagMorphism c d} -> {h, k : PreDiagMorphism d e} ->
  PreDiagTwoMorph {c=d} {d=e} h k -> PreDiagTwoMorph {c} {d} f g ->
  PreDiagTwoMorph {c} {d=e} (PreDiagCompose h f) (PreDiagCompose k g)
PreDiagTwoMorphHComp {c} {d} {e} {f} {g} {h} {k} beta alpha =
  MkPD2Morph $ \x : pdVert c =>
    preDiagFreeComp
      (pd2Component beta $ dfpVmap g x)
      (freeHomMapExtendLeft (dfpEmap h) (dfpVmap f x, dfpVmap g x) $
        pd2Component alpha x)

public export
PreDiagWhiskerLeft : {c, d, e : PreDiagram} ->
  {h, k : PreDiagMorphism d e} ->
  (nu : PreDiagTwoMorph {c=d} {d=e} h k) -> (f : PreDiagMorphism c d) ->
  PreDiagTwoMorph {c} {d=e} (PreDiagCompose h f) (PreDiagCompose k f)
PreDiagWhiskerLeft {c} {d} {e} {h} {k} nu f =
  MkPD2Morph $ \x : pdVert c => pd2Component nu $ dfpVmap f x

public export
PreDiagWhiskerRight : {c, d, e : PreDiagram} ->
  {h, k : PreDiagMorphism c d} ->
  (f : PreDiagMorphism d e) -> (nu : PreDiagTwoMorph {c} {d} h k) ->
  PreDiagTwoMorph {c} {d=e} (PreDiagCompose f h) (PreDiagCompose f k)
PreDiagWhiskerRight {c} {d} {e} {h} {k} f nu =
  MkPD2Morph $
    \x : pdVert c =>
      freeHomMapExtendLeft (dfpEmap f) (dfpVmap h x, dfpVmap k x) $
        pd2Component nu x

public export
IsD2Iso : {c, d : Diagram} -> {f, g : DiagMorphism c d} ->
  (alpha : DiagTwoMorph {c} {d} f g) -> Type
IsD2Iso {c} {d} {f} {g} alpha =
  (x : DiagFreeObj c) -> IsIso (d2Component alpha x)

public export
IsDiagEquiv : {0 c, d : Diagram} -> (0 f, g : DiagMorphism c d) ->
  Type
IsDiagEquiv {c} {d} f g =
  Exists0 (DiagTwoMorph {c} {d} f g) (\alpha => IsD2Iso {c} {d} {f} {g} alpha)

public export
DiagTwoMorphVComp : {c, d : Diagram} -> {f, g, h : DiagMorphism c d} ->
  DiagTwoMorph {c} {d} g h -> DiagTwoMorph {c} {d} f g ->
  DiagTwoMorph {c} {d} f h
DiagTwoMorphVComp {c} {d} {f} {g} {h} beta alpha =
  MkD2Morph (PreDiagTwoMorphVComp (d2Pre beta) (d2Pre alpha))
    ?DiagTwoMorphVComp_isNatural_hole

public export
DiagWhiskerLeft : {c, d, e : Diagram} ->
  {h, k : DiagMorphism d e} ->
  (nu : DiagTwoMorph {c=d} {d=e} h k) -> (f : DiagMorphism c d) ->
  DiagTwoMorph {c} {d=e} (DiagCompose h f) (DiagCompose k f)
DiagWhiskerLeft {c} {d} {e} {h} {k} nu f =
  MkD2Morph (PreDiagWhiskerLeft (d2Pre nu) (dmPreM f))
    ?DiagWhiskerLeft_isNatural_hole

public export
DiagWhiskerRight : {c, d, e : Diagram} ->
  {h, k : DiagMorphism c d} ->
  (f : DiagMorphism d e) -> (nu : DiagTwoMorph {c} {d} h k) ->
  DiagTwoMorph {c} {d=e} (DiagCompose f h) (DiagCompose f k)
DiagWhiskerRight {c} {d} {e} {h} {k} f nu =
  MkD2Morph (PreDiagWhiskerRight (dmPreM f) (d2Pre nu))
    ?DiagWhiskerRight_isNatural_hole

public export
record PreAdjunction (c, d : PreDiagram) where
  constructor MkPreAdj
  preAdjL : PreDiagMorphism d c
  preAdjR : PreDiagMorphism c d
  preAdjUnit :
    PreDiagTwoMorph {d} {c=d} (PreDiagId d) (PreDiagCompose preAdjR preAdjL)
  preAdjCounit :
    PreDiagTwoMorph {c} {d=c} (PreDiagCompose preAdjL preAdjR) (PreDiagId c)

public export
preAdjLeftAdjunct : {c, d : PreDiagram} -> (adj : PreAdjunction c d) ->
  (a : pdVert d) -> (b : pdVert c) ->
  PreDiagFreeHom c (dfpVmap (preAdjL adj) a, b) ->
  PreDiagFreeHom d (a, dfpVmap (preAdjR adj) b)
preAdjLeftAdjunct {c} {d} adj a b m =
  preDiagFreeComp
    (freeHomMapExtendLeft (dfpEmap (preAdjR adj)) _ m)
    (pd2Component (preAdjUnit adj) a)

public export
preAdjRightAdjunct : {c, d : PreDiagram} -> (adj : PreAdjunction c d) ->
  (a : pdVert d) -> (b : pdVert c) ->
  PreDiagFreeHom d (a, dfpVmap (preAdjR adj) b) ->
  PreDiagFreeHom c (dfpVmap (preAdjL adj) a, b)
preAdjRightAdjunct {c} {d} adj a b m =
  preDiagFreeComp
    (pd2Component (preAdjCounit adj) b)
    (freeHomMapExtendLeft (dfpEmap (preAdjL adj)) _ m)

public export
record Adjunction (c, d : Diagram) where
  constructor MkAdj
  adjL : DiagMorphism d c
  adjR : DiagMorphism c d
  adjUnit :
    DiagTwoMorph {d} {c=d} (DiagId d) (DiagCompose adjR adjL)
  adjCounit :
    DiagTwoMorph {c} {d=c} (DiagCompose adjL adjR) (DiagId c)
  {-
  0 adjTriangleL :
    DiagTwoMorphEquiv
      (DiagTwoMorphVComp
        (DiagWhiskerLeft adjCounit adjL)
        (DiagWhiskerRight adjL adjUnit))
      (DiagTwoId adjL)
  0 adjTriangleR :
    DiagTwoMorphEquiv
      (DiagTwoMorphVComp
        (DiagWhiskerRight adjR adjCounit))
        (DiagWhiskerLeft adjUnit adjR)
      (DiagTwoId adjR)
  -}

public export
adjPre : {c, d : Diagram} -> Adjunction c d -> PreAdjunction (dPre c) (dPre d)
adjPre {c} {d} adj =
  MkPreAdj
    (dmPreM $ adjL adj)
    (dmPreM $ adjR adj)
    (d2Pre $ adjUnit adj)
    (d2Pre $ adjCounit adj)

public export
0 AdjIsEquiv : {0 c, d : Diagram} -> (0 adj : Adjunction c d) -> Type
AdjIsEquiv {c} {d} adj = (IsD2Iso $ adjUnit adj, IsD2Iso $ adjCounit adj)

public export
AdjointEquivalence : (Diagram, Diagram) -> Type
AdjointEquivalence (c, d) = Exists0 (Adjunction c d) AdjIsEquiv

public export
PREDIAGsig : Type
PREDIAGsig = SignatureT PreDiagram

public export
PREDIAGvert : Type
PREDIAGvert = PreDiagram

public export
PREDIAGedge : HomSlice PREDIAGvert
PREDIAGedge (x, y) = PreDiagMorphism x y

public export
PREDIAG : PreDiagram
PREDIAG = MkPreDiag PREDIAGvert PREDIAGedge

public export
InitialPreDiag : PreDiagram
InitialPreDiag = MkPreDiag Void (\(v, _) => void v)

public export
preDiagFMap : {c, d : PreDiagram} -> {x, y : pdVert c} ->
  (f : PreDiagMorphism c d) ->
  PreDiagFreeHom c (x, y) -> PreDiagFreeHom d (dfpVmap f x, dfpVmap f y)
preDiagFMap {c} {x} {y} f = freeHomMapExtendLeft (dfpEmap f) (x, y)

public export
DIAGsig : Type
DIAGsig = SignatureT Diagram

public export
DIAGvert : Type
DIAGvert = Diagram

public export
DIAGedge : HomSlice DIAGvert
DIAGedge (x, y) = DiagMorphism x y

public export
DIAGsigrel : SigRelT DIAGedge
DIAGsigrel ((c, d) ** (f, g)) = IsDiagEquiv {c} {d} f g

public export
DIAGrel : CatRelT DIAGedge
DIAGrel = SigToCatRel DIAGsigrel

public export
DIAGrelCong : IsCongruence DIAGrel
DIAGrelCong = ?DiagRelCong_hole

public export
DIAG : Diagram
DIAG = MkDiagram DIAGvert DIAGedge DIAGrel

public export
diagFMap : {c, d : Diagram} -> {x, y : dVert c} ->
  (f : DiagMorphism c d) ->
  DiagFreeHom c (x, y) -> DiagFreeHom d (dpVmap f x, dpVmap f y)
diagFMap {c} {x} {y} f = freeHomMapExtendLeft (dpEmap f) (x, y)

-- Here we define some objects in two-categories whose categories are
-- represented by diagrams.

public export
InitialDiag : Diagram
InitialDiag = MkDiagram Void (\(v, _) => void v) (\((v, _) ** _) => void v)

-- The terminal diagram does not require any explicit morphisms,
-- because the only one in the category that it represents, the identity
-- on the only object, is implicitly generated by `FreeHomM`.
public export
TerminalDiag : Diagram
TerminalDiag = MkDiagram Unit (const Void) (const Void)

------------------------------
------------------------------
---- W-types in (PRE)DIAG ----
------------------------------
------------------------------

public export
PreDiagIdComp : InternalIdComp {obj=PREDIAGvert} PREDIAGedge
PreDiagIdComp c c (CHId c) = PreDiagId c
PreDiagIdComp c d (CHComp g f) = PreDiagCompose g f

public export
reducePreDiagEdge : {x, y : PREDIAGvert} ->
  FreeHomM PREDIAGvert PREDIAGedge (x, y) -> PREDIAGedge (x, y)
reducePreDiagEdge = reduceHomSlice PreDiagIdComp

public export
preDiagCovarPresheafFMap : {c : PreDiagram} -> {x, y : pdVert c} ->
  (f : PreDiagMorphism c PREDIAG) ->
  PreDiagFreeHom c (x, y) -> PREDIAGedge (dfpVmap f x, dfpVmap f y)
preDiagCovarPresheafFMap {c} {x} {y} f = reducePreDiagEdge . preDiagFMap f

public export
preDiagCovarPresheafVmap : {c : PreDiagram} -> {x, y : pdVert c} ->
  (f : PreDiagMorphism c PREDIAG) ->
  PreDiagFreeHom c (x, y) -> pdVert (dfpVmap f x) -> pdVert (dfpVmap f y)
preDiagCovarPresheafVmap {c} {x} {y} f = dfpVmap . preDiagCovarPresheafFMap f

-- A pre-diagram together with a pre-functor from that pre-diagram
-- to the pre-diagram of pre-diagrams (`PRE`) determine another
-- pre-diagram which we call its Sigma pre-diagram by analogy with
-- a Sigma type which can be determined by a type together with a
-- function from that type to `Type`.

public export
SigmaPreDiagObj : (c : PreDiagram) -> PreDiagMorphism c PREDIAG -> Type
SigmaPreDiagObj c f = Sigma {a=(pdVert c)} (pdVert . dfpVmap f)

public export
SigmaPreDiagMorph : (c : PreDiagram) -> (f : PreDiagMorphism c PREDIAG) ->
  HomSlice (SigmaPreDiagObj c f)
SigmaPreDiagMorph c f ((x ** fx), (y ** fy)) =
  (m : PreDiagFreeHom c (x, y) **
   FreeHomM
    (pdVert $ dfpVmap f y)
    (pdEdge $ dfpVmap f y)
    (preDiagCovarPresheafVmap f m fx, fy))

public export
SigmaPreDiag : (c : PreDiagram) -> PreDiagMorphism c PREDIAG -> PreDiagram
SigmaPreDiag c f = MkPreDiag (SigmaPreDiagObj c f) (SigmaPreDiagMorph c f)

public export
DiagIdComp : InternalIdComp {obj=DIAGvert} DIAGedge
DiagIdComp c c (CHId c) = DiagId c
DiagIdComp c d (CHComp g f) = DiagCompose g f

public export
reduceDiagEdge : {x, y : DIAGvert} ->
  FreeHomM DIAGvert DIAGedge (x, y) -> DIAGedge (x, y)
reduceDiagEdge = reduceHomSlice DiagIdComp

public export
diagCovarPresheafFMap : {c : Diagram} -> {x, y : dVert c} ->
  (f : DiagMorphism c DIAG) ->
  DiagFreeHom c (x, y) -> DiagMorphism (dpVmap f x) (dpVmap f y)
diagCovarPresheafFMap {c} {x} {y} f = reduceDiagEdge . diagFMap f

public export
diagCovarPresheafVmap : {c : Diagram} -> {x, y : dVert c} ->
  (f : DiagMorphism c DIAG) ->
  DiagFreeHom c (x, y) -> dVert (dpVmap f x) -> dVert (dpVmap f y)
diagCovarPresheafVmap {c} {x} {y} f = dpVmap . diagCovarPresheafFMap f

public export
SigmaDiagObj : (c : Diagram) -> DiagMorphism c DIAG -> Type
SigmaDiagObj c f = Sigma {a=(dVert c)} (dVert . dpVmap f)

public export
SigmaDiagMorph : (c : Diagram) -> (f : DiagMorphism c DIAG) ->
  HomSlice (SigmaDiagObj c f)
SigmaDiagMorph c f ((x ** fx), (y ** fy)) =
  (m : DiagFreeHom c (x, y) **
   FreeHomM
    (dVert $ dpVmap f y)
    (dEdge $ dpVmap f y)
    (diagCovarPresheafVmap f m fx, fy))

public export
SigmaDiagSigRel : (c : Diagram) -> (f : DiagMorphism c DIAG) ->
  SigRelT (SigmaDiagMorph c f)
SigmaDiagSigRel c f (((x ** fx), (y ** fy)) ** ((mc ** mf), (mc' ** mf'))) =
  Exists0
    (DiagFreeCatRel c ((x, y) ** (mc, mc')))
    (\rel =>
      let
        rmcf = dmRmapCorrect f ((x, y) ** (mc, mc')) rel
        red = reduceCatFreeEq DIAGrelCong rmcf
        -- sigred = SigToCatRelToSigRel DIAGrel red
      in
      ?SigmaDiagRel_hole_snd)

public export
SigmaDiagCatRel : (c : Diagram) -> (f : DiagMorphism c DIAG) ->
  CatRelT (SigmaDiagMorph c f)
SigmaDiagCatRel c f = SigToCatRel $ SigmaDiagSigRel c f

public export
SigmaDiag : (c : Diagram) -> DiagMorphism c DIAG -> Diagram
SigmaDiag c f =
  MkDiagram (SigmaDiagObj c f) (SigmaDiagMorph c f) (SigmaDiagCatRel c f)

----------------------------------------------
----------------------------------------------
---- Free polynomial functors on diagrams ----
----------------------------------------------
----------------------------------------------

-- To define a generator for a universal property, the first thing we do is
-- choose the input required to generate a new diagram.  That input is a
-- diagram itself, which will be used to specify a subdiagram from which to
-- choose inputs when building the output diagram.
--
-- The next thing we must do is specify the output -- first, the universal
-- object(s) which we will generate with each application.
public export
UObj : Type
UObj = SliceObj Diagram

public export
data UPObj : Diagram -> UObj -> Type where
  UPOv : dVert dgm -> UPObj dgm upo
  UPOc : upo dgm -> UPObj dgm upo

public export
upoV : {dgm : Diagram} -> {uo : UObj} ->
  SignatureT (dVert dgm) -> SignatureT (UPObj dgm uo)
upoV {dgm} {uo} = sigMap UPOv

public export
UPMorphGen : Diagram -> UObj -> Type
UPMorphGen dgm uo = HomSlice (UPObj dgm uo)

public export
data UPMorph : {dgm : Diagram} -> {uo : UObj} -> UPMorphGen dgm uo ->
    HomSlice (UPObj dgm uo) where
  UPMv : {0 dgm : Diagram} -> {0 uo : UObj} -> {0 upm : UPMorphGen dgm uo} ->
    {0 sig : SignatureT (dVert dgm)} ->
    dEdge dgm sig -> UPMorph {dgm} {uo} upm (upoV sig)
  UPMc : {0 dgm : Diagram} -> {0 uo : UObj} -> {0 upm : UPMorphGen dgm uo} ->
    {0 sig : SignatureT (UPObj dgm uo)} ->
    upm sig -> UPMorph {dgm} {uo} upm sig

public export
FreeUPMorph : {dgm : Diagram} -> {uo : UObj} ->
  UPMorphGen dgm uo -> HomSlice (UPObj dgm uo)
FreeUPMorph {dgm} {uo} upm = FreeHomM (UPObj dgm uo) (UPMorph {dgm} {uo} upm)

public export
upmV : {dgm : Diagram} -> {uo : UObj} -> {upm : UPMorphGen dgm uo} ->
  {sig : SignatureT (dVert dgm)} ->
  FreeHomM (dVert dgm) (dEdge dgm) sig ->
  FreeUPMorph {dgm} {uo} upm (upoV sig)
upmV {dgm} {uo} {upm} {sig} =
  homSliceCata
    (dEdge dgm)
    (FreeUPMorph upm . upoV)
    (\sig, f => InSlFv $ UPMv f)
    (\sig, f =>
      InSlFc $ sigMapCommute {sl=(dEdge dgm)} {sl'=(UPMorph upm)} {m=UPOv} f)
    sig

public export
UPEqGen : {dgm : Diagram} -> {uo : UObj} -> UPMorphGen dgm uo -> Type
UPEqGen {dgm} {uo} upm = CatRelT (UPMorph {dgm} {uo} upm)

public export
data UPEq : {dgm : Diagram} -> {uo : UObj} -> {upm : UPMorphGen dgm uo} ->
    UPEqGen upm -> CatRelT (UPMorph {dgm} {uo} upm) where
  UPEv : {0 dgm : Diagram} -> {0 uo : UObj} -> {0 upm : UPMorphGen dgm uo} ->
    {0 upe : UPEqGen {dgm} {uo} upm} ->
    {0 sig : SignatureT (dVert dgm)} ->
    {0 f, g : FreeHomM (dVert dgm) (dEdge dgm) sig} ->
    dRel dgm (sig ** (f, g)) ->
    UPEq {dgm} {uo} {upm} upe (upoV sig ** (upmV f, upmV g))
  UPEc : {0 dgm : Diagram} -> {0 uo : UObj} -> {0 upm : UPMorphGen dgm uo} ->
    {0 upe : UPEqGen {dgm} {uo} upm} ->
    {0 sig : SignatureT (UPObj dgm uo)} ->
    {0 f, g : FreeHomM (UPObj dgm uo) (UPMorph {dgm} {uo} upm) sig} ->
    upe (sig ** (f, g)) -> UPEq {dgm} {uo} {upm} upe (sig ** (f, g))

public export
record UPGen (upInput : Diagram) where
  constructor MkUP
  upObj : UObj
  upMorph : UPMorphGen upInput upObj
  upEq : UPEqGen {dgm=upInput} {uo=upObj} upMorph

-- A UPGen is itself a (dependent) diagram.
public export
upGenDiag : {upInput : Diagram} -> UPGen upInput -> Diagram
upGenDiag {upInput} up =
  MkDiagram
    (UPObj upInput (upObj up))
    (UPMorph (upMorph up))
    (UPEq (upEq up))

public export
interpUPGenObj : {upInput : Diagram} -> UPGen upInput -> Diagram -> Type
interpUPGenObj up dgm = UPObj dgm (upObj up)

public export
interpUPGenMorph : {upInput : Diagram} -> (up : UPGen upInput) ->
  (dgm : Diagram) -> HomSlice (interpUPGenObj {upInput} up dgm)
interpUPGenMorph up dgm = UPMorph ?interpUPGenMorph_hole

public export
interpUPGenEq : {upInput : Diagram} -> (up : UPGen upInput) ->
  (dgm : Diagram) -> CatRelT (interpUPGenMorph up dgm)
interpUPGenEq up dgm = ?interpUPGenEq_hole

public export
interpUPF : {upInput : Diagram} -> (up : UPGen upInput) -> Diagram -> Diagram
interpUPF up dgm = ?interpUPF_hole

public export
interpUPFMap :
  {upInput : Diagram} -> (up : UPGen upInput) -> {c, d : Diagram} ->
  DiagMorphism c d -> DiagMorphism (interpUPF up c) (interpUPF up d)
interpUPFMap up {c} {d} f = ?interpUPFMap_hole


------------------------------------------
------------------------------------------
---- Polynomial functors on diagrams -----
------------------------------------------
------------------------------------------

-- Here we define not the diagrammatic representation of functors between
-- categories as represented by diagrams (that's `DiagMorphism`), but rather
-- functors in two-categories whose categories are represented by diagrams.

-- A functor from the category of diagrams to the base category `Type`.
-- The first form does not include functor correctness conditions, but
-- only the type signature of the operations.
public export
record PreDiagToTypeFunctor where
  constructor PreDiagToTypeF
  pdtfOmap : PreDiagram -> Type
  pdtfFmap : {0 c, d : PreDiagram} ->
    (m : PreDiagMorphism c d) -> pdtfOmap c -> pdtfOmap d

-- The second form includes functor correctness conditions.
public export
record DiagToTypeFunctor where
  constructor DiagToTypeF
  dtfPre : PreDiagToTypeFunctor
  dtfId : {0 c : PreDiagram} ->
    (x : pdtfOmap dtfPre c) -> pdtfFmap {c} {d=c} dtfPre (PreDiagId c) x = x

-- To build a polynomial functor on categories freely generated from diagrams,
-- we begin by specifying a collection of diagrams, where each diagram
-- represents the input to some universal property -- that is, the sub-diagram
-- of a category which must exist to adjoin some universal object and morphism
-- to it.
public export
record DiagToTypeArena where
  constructor DiagToTypeAr
  dttaPos : Type
  dttaDir : dttaPos -> Diagram

-- A polynomial functor from the category of diagrams to `Type` is a sum
-- of covariant representables.
public export
InterpDiagToTypePF : DiagToTypeArena -> SliceObj Diagram
InterpDiagToTypePF dtta dgm =
  (i : dttaPos dtta ** DiagMorphism (dttaDir dtta i) dgm)

-- A Dirichlet functor from the category of diagrams to `Type` is a sum
-- of contravariant representables.
public export
InterpDiagToTypeDF : DiagToTypeArena -> SliceObj Diagram
InterpDiagToTypeDF dtta dgm =
  (i : dttaPos dtta ** DiagMorphism dgm (dttaDir dtta i))

-- A given representable functor from diagrams to pre-diagrams consists of a
-- diagram representing a (representable) functor from diagrams to `Type`,
-- a type of new objects, and some morphisms on the combined diagram.
public export
record DiagToHomSliceRep (dgm : Diagram) where
  constructor DiagToHSR
  dthsrObj : Type
  dthsrMorph : Type
  dthsrSig : dthsrMorph -> SignatureT (Either (dVert dgm) dthsrObj)

-- A polynomial functor from diagrams to pre-diagrams is a sum of
-- representables, dependent on a polynomial functor from diagrams
-- to `Type`.
public export
record DiagToHomSliceArena (dtta : DiagToTypeArena) where
  constructor DiagToHSAr
  dthsDir : (i : dttaPos dtta) -> DiagToHomSliceRep (dttaDir dtta i)

public export
InterpDiagToHSPFObj : {dtta : DiagToTypeArena} -> DiagToHomSliceArena dtta ->
  (dgm : Diagram) -> SliceObj (InterpDiagToTypePF dtta dgm)
InterpDiagToHSPFObj {dtta} dthsa dgm (i ** m) =
  Either (dVert (dttaDir dtta i)) (dthsrObj $ dthsDir dthsa i)

public export
InterpDiagToHSPFMorph : {dtta : DiagToTypeArena} ->
  (dthsa : DiagToHomSliceArena dtta) ->
  (dgm : Diagram) -> (ty : InterpDiagToTypePF dtta dgm) ->
  HomSlice (InterpDiagToHSPFObj {dtta} dthsa dgm ty)
InterpDiagToHSPFMorph {dtta} dthsa dgm (i ** m) sig =
  (j : dthsrMorph (dthsDir dthsa i) ** dthsrSig (dthsDir dthsa i) j = sig)

-----------------------------------
-----------------------------------
---- Prafunctors (Bicomodules) ----
-----------------------------------
-----------------------------------

-- See https://topos.site/blog/2022/08/imagining-bicomodules-with-type-theory/ .

public export
record PRAFunctor (dom, cod : PreDiagram) where
  constructor PRAf
  prafPos : pdVert cod -> Type
  prafDir : (i : pdVert cod) -> prafPos i -> pdVert dom -> Type
  prafOnPos : (i, i' : pdVert cod) ->
    pdEdge cod (i, i') -> prafPos i -> prafPos i'
  prafOnDir : (i : pdVert cod) -> (p : prafPos i) -> (j, j' : pdVert dom) ->
    pdEdge dom (j, j') -> prafDir i p j -> prafDir i p j'
  prafComp : (i, i' : pdVert cod) -> (j : pdVert dom) ->
    (f : pdEdge cod (i, i')) -> (p : prafPos i) ->
    (d' : prafDir i' (prafOnPos i i' f p) j) -> prafDir i p j

-------------------------
-------------------------
---- Finite diagrams ----
-------------------------
-------------------------
