module LanguageDef.InternalCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Internal category signatures (morphisms, identity, composition) ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

public export
0 IntMorSig : Type -> Type
IntMorSig c = c -> c -> Type

public export
0 IntIdSig : (c : Type) -> (mor : IntMorSig c) -> Type
IntIdSig c mor = (0 x : c) -> mor x x

public export
0 IntCompSig : (c : Type) -> (mor : IntMorSig c) -> Type
IntCompSig c mor = (0 x, y, z : c) -> mor y z -> mor x y -> mor x z

public export
record IdCompSig (obj : Type) (mor : IntMorSig obj) where
  constructor ICS
  0 icsId : IntIdSig obj mor
  0 icsComp : IntCompSig obj mor

public export
record MorIdCompSig (obj : Type) where
  constructor MICS
  0 micsMor : IntMorSig obj
  0 micsICS : IdCompSig obj micsMor

public export
0 micsId : {obj : Type} ->
  (mics : MorIdCompSig obj) -> IntIdSig obj (micsMor mics)
micsId {obj} mics = icsId $ micsICS mics

public export
0 micsComp : {obj : Type} ->
  (mics : MorIdCompSig obj) -> IntCompSig obj (micsMor mics)
micsComp {obj} mics = icsComp $ micsICS mics

public export
record IntCatSig where
  constructor ICat
  icObj : Type
  0 icMICS : MorIdCompSig icObj

public export
0 icMor : (cat : IntCatSig) -> IntMorSig (icObj cat)
icMor cat = micsMor $ icMICS cat

public export
0 icId : (cat : IntCatSig) -> IntIdSig (icObj cat) (icMor cat)
icId cat = micsId {obj=(icObj cat)} $ icMICS cat

public export
0 icComp : (cat : IntCatSig) -> IntCompSig (icObj cat) (icMor cat)
icComp cat = micsComp {obj=(icObj cat)} $ icMICS cat

------------------
------------------
---- Functors ----
------------------
------------------

public export
0 IntIdFunctor : (0 c : Type) -> c -> c
IntIdFunctor c = Prelude.id {a=c}

public export
0 IntFunctorComp : (0 c, d, e : Type) -> (d -> e) -> (c -> d) -> c -> e
IntFunctorComp c d e = (.)

public export
0 IntFMapSig : {0 c, d : Type} -> (0 _ : IntMorSig c) -> (0 _ : IntMorSig d) ->
  (c -> d) -> Type
IntFMapSig {c} {d} cmor dmor omap =
  (0 x, y : c) -> cmor x y -> dmor (omap x) (omap y)

public export
0 IntEndoFMapSig : {0 c : Type} -> (0 _ : IntMorSig c) ->
  (c -> c) -> Type
IntEndoFMapSig {c} cmor = IntFMapSig {c} {d=c} cmor cmor

public export
0 intFMapId : {0 c : Type} -> (0 cmor : IntMorSig c) ->
  IntFMapSig {c} {d=c} cmor cmor (IntIdFunctor c)
intFMapId {c} cmor x y = Prelude.id {a=(cmor x y)}

public export
intFmapComp : {0 c, d, e : Type} ->
  {0 cmor : IntMorSig c} -> {0 dmor : IntMorSig d} -> {0 emor : IntMorSig e} ->
  {0 g : d -> e} -> {0 f : c -> d} ->
  IntFMapSig {c=d} {d=e} dmor emor g ->
  IntFMapSig {c} {d} cmor dmor f ->
  IntFMapSig {c} {d=e} cmor emor (IntFunctorComp c d e g f)
intFmapComp {c} {d} {e} {cmor} {dmor} {emor} {g} {f} gm fm x y =
  gm (f x) (f y) . fm x y

public export
record IntFunctorSig (dom, cod : IntCatSig) where
  constructor IFunctor
  0 ifOmap : icObj dom -> icObj cod
  0 ifMmap :
    IntFMapSig {c=(icObj dom)} {d=(icObj cod)} (icMor dom) (icMor cod) ifOmap

--------------------------------
--------------------------------
---- Category of categories ----
--------------------------------
--------------------------------

public export
IntFunctorSigId : IntIdSig IntCatSig IntFunctorSig
IntFunctorSigId cat =
  IFunctor (IntIdFunctor $ icObj cat) (intFMapId $ icMor cat)

public export
IntFunctorSigComp : IntCompSig IntCatSig IntFunctorSig
IntFunctorSigComp c d e g f =
  IFunctor
    (IntFunctorComp (icObj c) (icObj d) (icObj e) (ifOmap g) (ifOmap f))
    (intFmapComp
      {cmor=(icMor c)}
      {dmor=(icMor d)}
      {emor=(icMor e)}
      (ifMmap g) (ifMmap f))

public export
IntCatCat : IntCatSig
IntCatCat =
  ICat
    IntCatSig
  $ MICS
    IntFunctorSig
  $ ICS
    IntFunctorSigId
    IntFunctorSigComp

-----------------------------
-----------------------------
---- Structured hom-sets ----
-----------------------------
-----------------------------

-----------------------------------------
---- Local and global hom-structures ----
-----------------------------------------

-- A structure on a hom-set of a category is the imposition of a
-- categorical structure on that hom-set.
public export
0 HomStruct : (0 c : IntCatSig) -> IntMorSig (icObj c)
HomStruct c x y = MorIdCompSig $ icMor c x y

-- A global hom-set structure is the imposition of a (categorical)
-- structure on every hom-set of a category.
public export
0 GlobalHomStruct : IntCatSig -> Type
GlobalHomStruct c = (0 x, y : icObj c) -> HomStruct c x y

-- By itself, imposing a global hom-set structure defines a category
-- whose objects are the morphisms of the underlying category, but
-- which only has 2-morphisms (i.e. morphisms between (1-)morphisms) between
-- 1-morphisms (i.e. morphisms of the underlying category) which have the same
-- domain and codomain in the underlying category.  In other words, that
-- category can be divided into zero or more connected components per pair of
-- objects of the underlying category.

public export
ghsObj : {0 c : IntCatSig} -> GlobalHomStruct c -> Type
ghsObj {c} ghs =
  Exists0 (ProductMonad $ icObj c) (\xy => icMor c (fst xy) (snd xy))

public export
data GHSmor : {0 c : IntCatSig} ->
    (ghs : GlobalHomStruct c) -> IntMorSig (ghsObj {c} ghs) where
  Gh2m : {0 c : IntCatSig} -> {0 ghs : GlobalHomStruct c} ->
    {0 x, y : icObj c} -> {f, g : icMor c x y} ->
    micsMor {obj=(icMor c x y)} (ghs x y) f g ->
    GHSmor {c} ghs (Evidence0 (x, y) f) (Evidence0 (x, y) g)

public export
0 ghsId : {0 c : IntCatSig} ->
 (ghs : GlobalHomStruct c) -> IntIdSig (ghsObj {c} ghs) (GHSmor {c} ghs)
ghsId {c} ghs m = case m of
  Evidence0 (x, y) f =>
    Gh2m {c} {ghs} {x} {y} {f} {g=f} $ micsId {obj=(icMor c x y)} (ghs x y) f

public export
0 ghsComp : {0 c : IntCatSig} ->
  (ghs : GlobalHomStruct c) -> IntCompSig (ghsObj {c} ghs) (GHSmor {c} ghs)
ghsComp {c} ghs m'' m' m beta alpha with (m'', m', m, beta, alpha)
  ghsComp {c} ghs _ _ _ beta alpha |
    (Evidence0 (w, x) f,
     Evidence0 (x', y) g,
     Evidence0 (y', z) h,
     Gh2m {c} {ghs} {x=x''} {y=y''} {f=g'} {g=h'} bm,
     Gh2m {c} {ghs} {x=x''} {y=y''} {f=f'} {g=g'} am) =
      Gh2m $ micsComp {obj=(icMor c x'' y'')} (ghs x'' y'') f' g' h' bm am

public export
ghsICS : {0 c : IntCatSig} ->
  (ghs : GlobalHomStruct c) -> IdCompSig (ghsObj {c} ghs) (GHSmor {c} ghs)
ghsICS {c} ghs =
  ICS
    {obj=(ghsObj {c} ghs)}
    {mor=(GHSmor {c} ghs)}
    (ghsId {c} ghs)
    (ghsComp {c} ghs)

public export
ghsMICS : {0 c : IntCatSig} ->
  (ghs : GlobalHomStruct c) -> MorIdCompSig (ghsObj {c} ghs)
ghsMICS {c} ghs = MICS {obj=(ghsObj {c} ghs)} (GHSmor {c} ghs) (ghsICS {c} ghs)

public export
ghsCat : {0 c : IntCatSig} -> GlobalHomStruct c -> IntCatSig
ghsCat {c} ghs = ICat (ghsObj {c} ghs) (ghsMICS {c} ghs)

-- Adding further structure to hom-set structures means defining 2-morphisms
-- whose domain and codomain, which are 1-morphisms, might potentially differ
-- in their own domains and/or codomains (which are objects of the underlying
-- category).  So we now define some such examples of further structure.

--------------------
---- Whiskering ----
--------------------

-- One form of further structure that we can impose on top of a
-- hom-set structure is a whisker structure.  To have a whisker
-- structure on a particular morphism (of the indexing category) means
-- that that morphism induces a mapping across hom-set structures which
-- follows the composition of the indexing category.  We can define
-- such a structure for either precomposition or postcomposition, which
-- we call "left" and "right" whiskering.

public export
0 LeftWhiskerMorphStruct : (0 ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic d e -> icMor ic c d -> Type
LeftWhiskerMorphStruct ic c d e hsce hsde f =
  (0 g, g' : icMor ic d e) ->
  micsMor hsde g g' ->
  micsMor hsce (icComp ic c d e g f) (icComp ic c d e g' f)

public export
0 RightWhiskerMorphStruct : (0 ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic c d -> icMor ic d e -> Type
RightWhiskerMorphStruct ic c d e hsce hscd g =
  (0 f, f' : icMor ic c d) ->
  micsMor hscd f f' ->
  micsMor hsce (icComp ic c d e g f) (icComp ic c d e g f')

-- We may further define notions that _all_ morphisms in a given hom-set
-- may be left- or right-whiskered.

public export
0 LeftWhiskerHomStruct : (0 ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic d e -> Type
LeftWhiskerHomStruct ic c d e hsce hsde =
  (0 f : icMor ic c d) -> LeftWhiskerMorphStruct ic c d e hsce hsde f

public export
0 RightWhiskerHomStruct : (0 ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic c d -> Type
RightWhiskerHomStruct ic c d e hsce hscd =
  (0 g : icMor ic d e) -> RightWhiskerMorphStruct ic c d e hsce hscd g

-- We may further define notions that all morphisms in _all_ hom-sets
-- may be left- or right-whiskered.

public export
0 GlobalLeftWhiskerHomStruct : (0 ic : IntCatSig) -> GlobalHomStruct ic -> Type
GlobalLeftWhiskerHomStruct ic ghs =
  (0 c, d, e : icObj ic) -> LeftWhiskerHomStruct ic c d e (ghs c e) (ghs d e)

public export
0 GlobalRightWhiskerHomStruct : (0 ic : IntCatSig) -> GlobalHomStruct ic -> Type
GlobalRightWhiskerHomStruct ic ghs =
  (0 c, d, e : icObj ic) -> RightWhiskerHomStruct ic c d e (ghs c e) (ghs c d)

-- We may also define notions of having both left _and_ right whisker
-- structures.

public export
record WhiskerPairHomStruct (0 ic : IntCatSig) (c, d, e : icObj ic)
  (hsce : HomStruct ic c e) (hscd : HomStruct ic c d) (hsde : HomStruct ic d e)
  where
    constructor WPHS
    wphsL : LeftWhiskerHomStruct ic c d e hsce hsde
    wphsR : RightWhiskerHomStruct ic c d e hsce hscd

public export
0 GlobalWhiskerPairHomStruct : (0 ic : IntCatSig) -> GlobalHomStruct ic -> Type
GlobalWhiskerPairHomStruct ic ghs =
  (0 c, d, e : icObj ic) ->
  WhiskerPairHomStruct ic c d e (ghs c e) (ghs c d) (ghs d e)

public export
0 MkGlobalWhiskerPairHomStruct : (0 ic : IntCatSig) ->
  (ghs : GlobalHomStruct ic) ->
  GlobalLeftWhiskerHomStruct ic ghs ->
  GlobalRightWhiskerHomStruct ic ghs ->
  GlobalWhiskerPairHomStruct ic ghs
MkGlobalWhiskerPairHomStruct ic ghs wl wr c d e = WPHS (wl c d e) (wr c d e)

--------------------------------
---- Horizontal composition ----
--------------------------------

-- Another form of further structure that we can impose on top of a
-- hom-set structure is a horizontal composition structure.
--
-- When there is a horizontal composition, we refer to the composition
-- of the hom-set structure as "vertical composition".

public export
0 HcompHomStruct : (0 ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic c d -> HomStruct ic d e -> Type
HcompHomStruct ic c d e hsce hscd hsde =
  (0 f, f' : icMor ic c d) -> (0 g, g' : icMor ic d e) ->
  (0 beta : micsMor hsde g g') -> (0 alpha : micsMor hscd f f') ->
  micsMor hsce (icComp ic c d e g f) (icComp ic c d e g' f')

public export
0 GlobalHcompHomStruct : (0 ic : IntCatSig) -> GlobalHomStruct ic -> Type
GlobalHcompHomStruct ic ghs =
  (c, d, e : icObj ic) ->
  HcompHomStruct ic c d e (ghs c e) (ghs c d) (ghs d e)

-- When we have both left- and right-whiskering structures, we can define
-- a horizontal-composition structure by composing whiskering operations.
-- Note that we could do so in two different ways -- left then right, or
-- right then left.  Thus, in order for this definition to be unambiguous,
-- the whiskering operations with compatible type signatures must always
-- commute.
public export
0 HcompFromWhiskers : (0 ic : IntCatSig) ->
  (c, d, e : icObj ic) ->
  (hsce : HomStruct ic c e) ->
  (hscd : HomStruct ic c d) ->
  (hsde : HomStruct ic d e) ->
  WhiskerPairHomStruct ic c d e hsce hscd hsde ->
  HcompHomStruct ic c d e hsce hscd hsde
HcompFromWhiskers ic c d e hsce hscd hsde wphs f f' g g' beta alpha =
  micsComp hsce
    (icComp ic c d e g f)
    (icComp ic c d e g f')
    (icComp ic c d e g' f')
    (wphsL wphs f' g g' beta)
    (wphsR wphs g f f' alpha)

public export
0 GlobalHcompFromWhiskers : (0 ic : IntCatSig) -> (ghs : GlobalHomStruct ic) ->
  GlobalWhiskerPairHomStruct ic ghs ->
  GlobalHcompHomStruct ic ghs
GlobalHcompFromWhiskers ic ghs wphs c d e =
  HcompFromWhiskers ic c d e (ghs c e) (ghs c d) (ghs d e) (wphs c d e)

---------------------------------
---------------------------------
---- Natural transformations ----
---------------------------------
---------------------------------

-- For every pair of categories, we may define a category of
-- natural transformations between the functors between them.

public export
0 IntNTSig : {0 c, d : Type} -> (0 dmor : IntMorSig d) ->
  (f, g : c -> d) -> Type
IntNTSig {c} {d} dmor f g = (0 x : c) -> dmor (f x) (g x)

public export
0 intNTid : {0 c, d : Type} -> (0 dmor : IntMorSig d) ->
  (0 _ : IntIdSig d dmor) ->
  (0 f : c -> d) -> IntNTSig {c} {d} dmor f f
intNTid {c} {d} dmor did f x = did $ f x

public export
intNTvcomp : {0 c, d : Type} -> {0 dmor : IntMorSig d} ->
  IntCompSig d dmor ->
  {0 f, g, h : c -> d} ->
  IntNTSig {c} {d} dmor g h ->
  IntNTSig {c} {d} dmor f g ->
  IntNTSig {c} {d} dmor f h
intNTvcomp {c} {d} {dmor} dcomp {f} {g} {h} beta alpha x =
  dcomp (f x) (g x) (h x) (beta x) (alpha x)

0 IntOmapCatSig : (dom, cod : IntCatSig) ->
  {obj : Type} -> (obj -> icObj dom -> icObj cod) -> MorIdCompSig obj
IntOmapCatSig dom cod {obj} omap =
  MICS
    (\f, g => IntNTSig (icMor cod) (omap f) (omap g))
  $ ICS
    (\f => intNTid (icMor cod) (icId cod) (omap f))
    (\f, g, h => intNTvcomp {f=(omap f)} {g=(omap g)} {h=(omap h)} (icComp cod))

0 IntFunctorOmapCatSig : IntCatSig -> IntCatSig -> IntCatSig
IntFunctorOmapCatSig dom cod =
  ICat (icObj dom -> icObj cod) $ IntOmapCatSig dom cod id

-- Given a pair of categories, we can form a "functor category",
-- whose objects are the functors from one to the other and whose
-- morphisms are the natural transformations among those functors.
public export
0 IntFunctorCatSig : IntCatSig -> IntCatSig -> IntCatSig
IntFunctorCatSig dom cod =
  ICat (IntFunctorSig dom cod) $ IntOmapCatSig dom cod ifOmap

-- The functor category (whose morphisms are natural transformations)
-- imposes a categorical structure on the set of functors between a pair
-- of categories.  In particular this means it imposes a global hom-struct
-- on the category of categories.
public export
0 FunctorCatHomStruct : GlobalHomStruct IntCatCat
FunctorCatHomStruct c d = icMICS $ IntFunctorCatSig c d

-- We can also whisker natural transformations.

public export
intNTwhiskerL : {0 c, d, e : Type} ->
  {0 emor : IntMorSig e} ->
  {0 g, h : d -> e} ->
  IntNTSig {c=d} {d=e} emor g h ->
  (0 f : c -> d) ->
  IntNTSig {c} {d=e} emor
    (IntFunctorComp c d e g f)
    (IntFunctorComp c d e h f)
intNTwhiskerL {c} {d} {e} {emor} {g} {h} alpha f x = alpha (f x)

public export
intNTwhiskerR : {0 c, d, e : Type} ->
  {0 dmor : IntMorSig d} -> {0 emor : IntMorSig e} ->
  {0 f, g : c -> d} ->
  {0 h : d -> e} ->
  IntFMapSig {c=d} {d=e} dmor emor h ->
  IntNTSig {c} {d} dmor f g ->
  IntNTSig {c} {d=e} emor
    (IntFunctorComp c d e h f)
    (IntFunctorComp c d e h g)
intNTwhiskerR {c} {d} {e} {dmor} {emor} {f} {g} {h} hm nu x =
  hm (f x) (g x) (nu x)

public export
0 FunctorCatWhiskerL :
  GlobalLeftWhiskerHomStruct IntCatCat FunctorCatHomStruct
FunctorCatWhiskerL c d e f g g' alpha =
  intNTwhiskerL
    {c=(icObj c)} {d=(icObj d)} {e=(icObj e)}
    {emor=(icMor e)}
    {g=(ifOmap g)} {h=(ifOmap g')}
    alpha (ifOmap f)

public export
0 FunctorCatWhiskerR :
  GlobalRightWhiskerHomStruct IntCatCat FunctorCatHomStruct
FunctorCatWhiskerR c d e g f f' beta =
  intNTwhiskerR
    {c=(icObj c)} {d=(icObj d)} {e=(icObj e)}
    {dmor=(icMor d)} {emor=(icMor e)}
    {f=(ifOmap f)} {g=(ifOmap f')} {h=(ifOmap g)}
    (ifMmap g) beta

public export
0 FunctorCatWhiskerPair :
  GlobalWhiskerPairHomStruct IntCatCat FunctorCatHomStruct
FunctorCatWhiskerPair c d e =
  WPHS (FunctorCatWhiskerL c d e) (FunctorCatWhiskerR c d e)

-- Because we have both directions of whiskering structure on the category
-- of categories, we can compose them to impose a horizontal composition.

public export
intNThcomp : {0 c, d, e : Type} ->
  {0 dmor : IntMorSig d} -> {0 emor : IntMorSig e} ->
  IntCompSig e emor ->
  {0 f, f' : c -> d} ->
  {0 g, g' : d -> e} ->
  IntFMapSig {c=d} {d=e} dmor emor g ->
  IntNTSig {c=d} {d=e} emor g g' ->
  IntNTSig {c} {d} dmor f f' ->
  IntNTSig {c} {d=e} emor
    (IntFunctorComp c d e g f)
    (IntFunctorComp c d e g' f')
intNThcomp {c} {d} {e} {dmor} {emor} ecomp {f} {f'} {g} {g'} gm beta alpha =
  intNTvcomp {c} {d=e} {dmor=emor} ecomp {f=(g . f)} {g=(g . f')} {h=(g' . f')}
    (intNTwhiskerL {c} {d} {e} {emor} {g} {h=g'} beta f')
    (intNTwhiskerR {c} {d} {e} {dmor} {emor} {f} {g=f'} {h=g} gm alpha)

public export
0 FunctorCatHcomp :
  GlobalHcompHomStruct IntCatCat FunctorCatHomStruct
FunctorCatHcomp c d e f f' g g' beta alpha =
  GlobalHcompFromWhiskers
    IntCatCat
    FunctorCatHomStruct
    FunctorCatWhiskerPair
    c d e f f' g g' beta alpha

---------------------------------
---------------------------------
---- Core general categories ----
---------------------------------
---------------------------------

-----------------------------
---- Opposite categories ----
-----------------------------

public export
IntOpCatObj : Type -> Type
IntOpCatObj = id

public export
0 IntOpCatMor : (0 c : Type) -> IntMorSig c -> IntMorSig c
IntOpCatMor c cmor = flip cmor

public export
0 IntOpCatId : (0 c : Type) -> (0 cmor : IntMorSig c) ->
  IntIdSig c cmor -> IntIdSig c (IntOpCatMor c cmor)
IntOpCatId c cmor cid = cid

public export
0 IntOpCatComp : (0 c : Type) -> (0 cmor : IntMorSig c) ->
  IntCompSig c cmor -> IntCompSig c (IntOpCatMor c cmor)
IntOpCatComp c cmor comp x y z mzy myx = comp z y x myx mzy

public export
IntOpCat : IntCatSig -> IntCatSig
IntOpCat c =
  ICat
    (icObj c)
  $ MICS
    (IntOpCatMor (icObj c) (icMor c))
  $ ICS
    (IntOpCatId (icObj c) (icMor c) (icId c))
    (IntOpCatComp (icObj c) (icMor c) (icComp c))

public export
IntOpFunctorSig : IntCatSig -> IntCatSig -> Type
IntOpFunctorSig c d = IntFunctorSig (IntOpCat c) (IntOpCat d)

public export
IntOpFunctor : {0 c, d : IntCatSig} ->
  IntFunctorSig c d -> IntFunctorSig (IntOpCat c) (IntOpCat d)
IntOpFunctor {c} {d} f = IFunctor (ifOmap f) (\x, y => ifMmap f y x)

public export
IntOpFunctorSigComp : (0 c, d, e : IntCatSig) ->
  IntOpFunctorSig d e ->
  IntOpFunctorSig c d ->
  IntOpFunctorSig c e
IntOpFunctorSigComp c d e =
  IntFunctorSigComp (IntOpCat c) (IntOpCat d) (IntOpCat e)

public export
0 IntOpNTSig : {0 c, d : Type} -> (0 dmor : IntMorSig d) ->
  (f, g : c -> d) -> Type
IntOpNTSig {c} {d} dmor = flip $ IntNTSig {c} {d} dmor

public export
0 IntOpNT : {0 c, d : Type} -> {0 dmor : IntMorSig d} ->
  {f, g : c -> d} ->
  IntNTSig {c} {d} dmor g f ->
  IntOpNTSig {c} {d} dmor f g
IntOpNT {c} {d} {dmor} {f} {g} = id

-----------------------------
---- Discrete categories ----
-----------------------------

public export
DiscreteCatObj : Type -> Type
DiscreteCatObj = id

public export
data DiscreteCatMor : {0 obj : Type} ->
    DiscreteCatObj obj -> DiscreteCatObj obj -> Type where
  DCid : {0 obj : Type} -> (0 x : obj) -> DiscreteCatMor {obj} x x

public export
0 DiscreteId : {0 obj : Type} ->
  IntIdSig (DiscreteCatObj obj) (DiscreteCatMor {obj})
DiscreteId {obj} x = DCid x

public export
0 DiscreteComp : {0 obj : Type} ->
  IntCompSig (DiscreteCatObj obj) (DiscreteCatMor {obj})
DiscreteComp _ _ _ x y = case (x, y) of (DCid a, DCid a) => DCid a

public export
DiscreteCat : Type -> IntCatSig
DiscreteCat c =
  ICat
    (DiscreteCatObj c)
  $ MICS
    (DiscreteCatMor {obj=c})
  $ ICS
    (DiscreteId {obj=c})
    (DiscreteComp {obj=c})

--------------------------
---- Initial category ----
--------------------------

public export
InitialCatObj : Type
InitialCatObj = DiscreteCatObj Void

public export
0 InitialCatMor : InitialCatObj -> InitialCatObj -> Type
InitialCatMor = DiscreteCatMor {obj=Void}

public export
0 InitialId : IntIdSig InitialCatObj InitialCatMor
InitialId = DiscreteId {obj=Void}

public export
0 InitialComp : IntCompSig InitialCatObj InitialCatMor
InitialComp = DiscreteComp {obj=Void}

public export
InitialCat : IntCatSig
InitialCat = DiscreteCat Void

---------------------------
---- Terminal category ----
---------------------------

public export
TerminalCatObj : Type
TerminalCatObj = DiscreteCatObj Unit

public export
0 TerminalCatMor : TerminalCatObj -> TerminalCatObj -> Type
TerminalCatMor = DiscreteCatMor {obj=Unit}

public export
0 TerminalId : IntIdSig TerminalCatObj TerminalCatMor
TerminalId = DiscreteId {obj=Unit}

public export
0 TerminalComp : IntCompSig TerminalCatObj TerminalCatMor
TerminalComp = DiscreteComp {obj=Unit}

public export
TerminalCat : IntCatSig
TerminalCat = DiscreteCat Unit

------------------------------
---- Coproduct categories ----
------------------------------

public export
IntCoprodCatObj : Type -> Type -> Type
IntCoprodCatObj c d = Either c d

public export
0 IntCoprodCatMor : (0 c, d : Type) ->
  IntMorSig c -> IntMorSig d -> IntMorSig (IntCoprodCatObj c d)
IntCoprodCatMor c d cmor dmor ab ab' =
  case (ab, ab') of
    (Left a, Left a') => cmor a a'
    (Right b, Right b') => dmor b b'
    _ => Void

public export
IntEndoCoprodCatObj : Type -> Type
IntEndoCoprodCatObj c = IntCoprodCatObj c c

public export
0 IntEndoCoprodCatMor : (0 c : Type) ->
  IntMorSig c -> IntMorSig (IntEndoCoprodCatObj c)
IntEndoCoprodCatMor c mor = IntCoprodCatMor c c mor mor

public export
0 IntCoprodCatId : (0 c, d : Type) ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  IntIdSig c cmor -> IntIdSig d dmor ->
  IntIdSig (IntCoprodCatObj c d) (IntCoprodCatMor c d cmor dmor)
IntCoprodCatId c d cmor dmor cid did cdobj =
  case cdobj of
    Left cobj => cid cobj
    Right dobj => did dobj

public export
0 IntCoprodCatComp : (0 c, d : Type) ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  IntCompSig c cmor -> IntCompSig d dmor ->
  IntCompSig (IntCoprodCatObj c d) (IntCoprodCatMor c d cmor dmor)
IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    with (cdx, cdy, cdz) proof objsig
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Left cx, Left cy, Left cz) =
      case objsig of Refl => ccomp cx cy cz cdmyz cdmxy
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Left _, Left _, Right _) =
      case objsig of Refl => void cdmyz
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Left _, Right _, Left _) =
      case objsig of Refl => void cdmyz
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Left _, Right _, Right _) =
      case objsig of Refl => void cdmxy
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Right _, Left _, Left _) =
      case objsig of Refl => void cdmxy
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Right _, Left _, Right _) =
      case objsig of Refl => void cdmyz
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Right _, Right _, Left _) =
      case objsig of Refl => void cdmyz
  IntCoprodCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy
    | (Right dx, Right dy, Right dz) =
      case objsig of Refl => dcomp dx dy dz cdmyz cdmxy

public export
IntCoprodCat : IntCatSig -> IntCatSig -> IntCatSig
IntCoprodCat c d =
  ICat
    (IntCoprodCatObj (icObj c) (icObj d))
  $ MICS
    (IntCoprodCatMor (icObj c) (icObj d) (icMor c) (icMor d))
  $ ICS
    (IntCoprodCatId
      (icObj c) (icObj d) (icMor c) (icMor d) (icId c) (icId d))
    (IntCoprodCatComp
      (icObj c) (icObj d) (icMor c) (icMor d) (icComp c) (icComp d))

----------------------------
---- Product categories ----
----------------------------

public export
IntProdCatObj : Type -> Type -> Type
IntProdCatObj c d = (c, d)

public export
0 IntProdCatMor : (0 c, d : Type) ->
  IntMorSig c -> IntMorSig d -> IntMorSig (IntProdCatObj c d)
IntProdCatMor c d cmor dmor ab ab' =
  (cmor (fst ab) (fst ab'), dmor (snd ab) (snd ab'))

public export
IntEndoProdCatObj : Type -> Type
IntEndoProdCatObj c = IntProdCatObj c c

public export
0 IntEndoProdCatMor : (0 c : Type) ->
  IntMorSig c -> IntMorSig (IntEndoProdCatObj c)
IntEndoProdCatMor c mor = IntProdCatMor c c mor mor

public export
0 IntProdCatId : (0 c, d : Type) ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  IntIdSig c cmor -> IntIdSig d dmor ->
  IntIdSig (IntProdCatObj c d) (IntProdCatMor c d cmor dmor)
IntProdCatId c d cmor dmor cid did cdobj = (cid $ fst cdobj, did $ snd cdobj)

public export
0 IntProdCatComp : (0 c, d : Type) ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  IntCompSig c cmor -> IntCompSig d dmor ->
  IntCompSig (IntProdCatObj c d) (IntProdCatMor c d cmor dmor)
IntProdCatComp c d cmor dmor ccomp dcomp cdx cdy cdz cdmyz cdmxy =
  (ccomp (fst cdx) (fst cdy) (fst cdz) (fst cdmyz) (fst cdmxy),
   dcomp (snd cdx) (snd cdy) (snd cdz) (snd cdmyz) (snd cdmxy))

public export
IntProdCat : IntCatSig -> IntCatSig -> IntCatSig
IntProdCat c d =
  ICat
    (IntProdCatObj (icObj c) (icObj d))
  $ MICS
    (IntProdCatMor (icObj c) (icObj d) (icMor c) (icMor d))
  $ ICS
    (IntProdCatId
      (icObj c) (icObj d) (icMor c) (icMor d) (icId c) (icId d))
    (IntProdCatComp
      (icObj c) (icObj d) (icMor c) (icMor d) (icComp c) (icComp d))

-------------------------------------
---- Opposite-product categories ----
-------------------------------------

public export
IntOpProdCatObj : Type -> Type -> Type
IntOpProdCatObj d c = IntProdCatObj (IntOpCatObj d) (IntOpCatObj c)

public export
0 IntOpProdCatMor : (0 d, c : Type) ->
  IntMorSig d -> IntMorSig c -> IntMorSig (d, c)
IntOpProdCatMor d c dmor cmor = IntProdCatMor d c (IntOpCatMor d dmor) cmor

public export
0 IntEndoOpProdCatMor :
  (0 c : Type) -> IntMorSig c -> IntMorSig (c, c)
IntEndoOpProdCatMor c mor = IntOpProdCatMor c c mor mor

public export
0 IntOpProdCatId : (0 d, c : Type) ->
  (dmor : IntMorSig d) -> (cmor : IntMorSig c) ->
  IntIdSig d dmor -> IntIdSig c cmor ->
  IntIdSig (d, c) (IntOpProdCatMor d c dmor cmor)
IntOpProdCatId d c dmor cmor = IntProdCatId d c (IntOpCatMor d dmor) cmor

public export
0 IntOpProdCatComp : (0 d, c : Type) ->
  (dmor : IntMorSig d) -> (cmor : IntMorSig c) ->
  IntCompSig d dmor -> IntCompSig c cmor ->
  IntCompSig (d, c) (IntOpProdCatMor d c dmor cmor)
IntOpProdCatComp d c dmor cmor dcomp ccomp =
  IntProdCatComp d c (IntOpCatMor d dmor) cmor (IntOpCatComp d dmor dcomp) ccomp

public export
IntOpProdCat : IntCatSig -> IntCatSig -> IntCatSig
IntOpProdCat d c = IntProdCat (IntOpCat d) c

---------------------------------
---------------------------------
---- Metalanguage categories ----
---------------------------------
---------------------------------

------------------------------------
---- Metalanguage base category ----
------------------------------------

public export
TypeObj : Type
TypeObj = Type

public export
0 TypeMor : TypeObj -> TypeObj -> Type
TypeMor = HomProf

public export
0 typeId : IntIdSig TypeObj TypeMor
typeId _ = Prelude.id

public export
0 typeComp : IntCompSig TypeObj TypeMor
typeComp _ _ _ = (.)

public export
TypeCat : IntCatSig
TypeCat =
  ICat
    TypeObj
  $ MICS
    TypeMor
  $ ICS
    typeId
    typeComp

------------------------------------------------
---- Opposite of metalanguage base category ----
------------------------------------------------

public export
OpTypeObj : Type
OpTypeObj = TypeObj

public export
0 OpTypeMor : OpTypeObj -> OpTypeObj -> Type
OpTypeMor = IntOpCatMor TypeObj TypeMor

public export
0 opTypeId : IntIdSig OpTypeObj OpTypeMor
opTypeId = IntOpCatId TypeObj TypeMor typeId

public export
0 opTypeComp : IntCompSig OpTypeObj OpTypeMor
opTypeComp = IntOpCatComp TypeObj TypeMor typeComp

public export
OpTypeCat : IntCatSig
OpTypeCat =
  ICat
    OpTypeObj
  $ MICS
    OpTypeMor
  $ ICS
    opTypeId
    opTypeComp

---------------------------------------
---- Metalanguage slice categories ----
---------------------------------------

public export
0 SliceMor : (c : Type) -> SliceObj c -> SliceObj c -> Type
SliceMor c x y = (ec : c) -> x ec -> y ec

public export
0 SliceId : (0 c : Type) -> IntIdSig (SliceObj c) (SliceMor c)
SliceId _ _ _ = id

public export
0 SliceComp : (0 c : Type) -> IntCompSig (SliceObj c) (SliceMor c)
SliceComp c x y z = \g, f => \ec => g ec . f ec

public export
SliceCat : Type -> IntCatSig
SliceCat c =
  ICat
    (SliceObj c)
  $ MICS
    (SliceMor c)
  $ ICS
    (SliceId c)
    (SliceComp c)

------------------------------------------
---- Metalanguage op-slice categories ----
------------------------------------------

public export
OpSliceObj : Type -> Type
OpSliceObj = SliceObj

public export
0 OpSliceMor : (c : Type) -> OpSliceObj c -> OpSliceObj c -> Type
OpSliceMor c = IntOpCatMor (SliceObj c) (SliceMor c)

0 OpSliceId : (c : Type) -> IntIdSig (OpSliceObj c) (OpSliceMor c)
OpSliceId c = IntOpCatId (SliceObj c) (SliceMor c) (SliceId c)

public export
0 OpSliceComp : (c : Type) -> IntCompSig (OpSliceObj c) (OpSliceMor c)
OpSliceComp c = IntOpCatComp (SliceObj c) (SliceMor c) (SliceComp c)

public export
OpSliceCat : Type -> IntCatSig
OpSliceCat c = IntOpCat (SliceCat c)

------------------------
------------------------
---- Two-categories ----
------------------------
------------------------

public export
0 Int2MorphParamSig : (0 obj : Type) -> (0 mor : IntMorSig obj) -> IntMorSig obj
Int2MorphParamSig obj mor x y = (0 f, g : mor x y) -> Type

public export
0 Int2MorphSig : (0 obj : Type) -> (0 mor : IntMorSig obj) -> Type
Int2MorphSig obj mor = (0 x, y : obj) -> Int2MorphParamSig obj mor x y

public export
0 Int2IdParamSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 x, y : obj) -> (0 _ : Int2MorphParamSig obj mor x y) -> Type
Int2IdParamSig {obj} {mor} x y mor2 = (0 f : mor x y) -> mor2 f f

public export
0 Int2IdSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 _ : Int2MorphSig obj mor) -> Type
Int2IdSig {obj} {mor} mor2 =
  (0 x, y : obj) -> Int2IdParamSig {obj} {mor} x y (mor2 x y)

public export
0 Int2VCompParamSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 x, y : obj) ->
  (0 mor2 : Int2MorphParamSig obj mor x y) -> Type
Int2VCompParamSig {obj} {mor} x y mor2 =
  (0 f, g, h : mor x y) -> mor2 g h -> mor2 f g -> mor2 f h

public export
0 Int2VCompSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 mor2 : Int2MorphSig obj mor) -> Type
Int2VCompSig {obj} {mor} mor2 =
  (0 x, y : obj) -> Int2VCompParamSig {obj} {mor} x y (mor2 x y)

public export
0 Int2WhiskerLParamSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 comp : IntCompSig obj mor) -> (0 mor2 : Int2MorphSig obj mor) ->
  (x, y : obj) -> mor x y -> Type
Int2WhiskerLParamSig {obj} {mor} comp mor2 x y f =
  (0 z : obj) -> (0 g, g' : mor y z) ->
  mor2 y z g g' -> mor2 x z (comp x y z g f) (comp x y z g' f)

public export
0 Int2WhiskerLSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 comp : IntCompSig obj mor) -> (0 mor2 : Int2MorphSig obj mor) ->
  Type
Int2WhiskerLSig {obj} {mor} comp mor2 =
  (0 x, y : obj) -> (f : mor x y) ->
  Int2WhiskerLParamSig {obj} {mor} comp mor2 x y f

public export
0 Int2WhiskerRParamSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 comp : IntCompSig obj mor) -> (0 mor2 : Int2MorphSig obj mor) ->
  (y, z : obj) -> mor y z -> Type
Int2WhiskerRParamSig {obj} {mor} comp mor2 y z g =
  (0 x : obj) -> (0 f, f' : mor x y) ->
  mor2 x y f f' -> mor2 x z (comp x y z g f) (comp x y z g f')

public export
0 Int2WhiskerRSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 comp : IntCompSig obj mor) -> (0 mor2 : Int2MorphSig obj mor) ->
  Type
Int2WhiskerRSig {obj} {mor} comp mor2 =
  (0 y, z : obj) -> (g : mor y z) ->
  Int2WhiskerRParamSig {obj} {mor} comp mor2 y z g

public export
0 Int2HCompParamSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 comp : IntCompSig obj mor) -> (0 mor2 : Int2MorphSig obj mor) ->
  IntMorSig obj
Int2HCompParamSig {obj} {mor} comp mor2 dom cod =
  (0 mid : obj) ->
  (0 f, f' : mor dom mid) -> (0 g, g' : mor mid cod) ->
  mor2 mid cod g g' -> mor2 dom mid f f' ->
  mor2 dom cod (comp dom mid cod g f) (comp dom mid cod g' f')

public export
0 Int2HCompSig : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 comp : IntCompSig obj mor) -> (0 mor2 : Int2MorphSig obj mor) ->
  Type
Int2HCompSig {obj} {mor} comp mor2 =
  (0 dom, cod : obj) -> Int2HCompParamSig {obj} {mor} comp mor2 dom cod

-- We call a category with whiskering in both directions -- from which we
-- can derive a horizontal composition -- a two-category.
public export
record Int2CatStruct (c1 : IntCatSig) where
  constructor I2CS
  i2Cshs : GlobalHomStruct c1
  i2Cswl : GlobalLeftWhiskerHomStruct c1 i2Cshs
  i2Cswr : GlobalRightWhiskerHomStruct c1 i2Cshs

-- We call a category with whiskering in both directions -- from which we
-- can derive a horizontal composition -- a two-category.
public export
record Int2CatSig where
  constructor I2Cat
  i2c1 : IntCatSig
  i2c2cs : Int2CatStruct i2c1

public export
i2Chs : (c2 : Int2CatSig) -> GlobalHomStruct (i2c1 c2)
i2Chs c2 = i2Cshs (i2c2cs c2)

public export
i2Cwl : (c2 : Int2CatSig) -> GlobalLeftWhiskerHomStruct (i2c1 c2) (i2Chs c2)
i2Cwl c2 = i2Cswl (i2c2cs c2)

public export
i2Cwr : (c2 : Int2CatSig) -> GlobalRightWhiskerHomStruct (i2c1 c2) (i2Chs c2)
i2Cwr c2 = i2Cswr (i2c2cs c2)

public export
0 i2c1Obj : (0 c2 : Int2CatSig) -> Type
i2c1Obj c2 = icObj $ i2c1 c2

public export
0 i2c1Mor : (0 c2 : Int2CatSig) -> (dom, cod : i2c1Obj c2) -> Type
i2c1Mor c2 = icMor $ i2c1 c2

public export
0 i2c1Id : (0 c2 : Int2CatSig) -> IntIdSig (i2c1Obj c2) (i2c1Mor c2)
i2c1Id c2 = icId $ i2c1 c2

public export
0 i2c1comp : (0 c2 : Int2CatSig) -> IntCompSig (i2c1Obj c2) (i2c1Mor c2)
i2c1comp c2 = icComp $ i2c1 c2

public export
0 i2c2Obj : (0 c2 : Int2CatSig) -> (0 dom, cod : i2c1Obj c2) -> Type
i2c2Obj c2 dom cod = i2c1Mor c2 dom cod

public export
0 i2c2Mor : (0 c2 : Int2CatSig) -> Int2MorphSig (i2c1Obj c2) (i2c1Mor c2)
i2c2Mor c2 x y f g = micsMor (i2Chs c2 x y) f g

public export
0 i2c2Id : (0 c2 : Int2CatSig) ->
  Int2IdSig {obj=(i2c1Obj c2)} {mor=(i2c1Mor c2)} (i2c2Mor c2)
i2c2Id c2 x y = micsId (i2Chs c2 x y)

public export
0 i2c2Vcomp : (0 c2 : Int2CatSig) ->
  Int2VCompSig {obj=(i2c1Obj c2)} {mor=(i2c1Mor c2)} (i2c2Mor c2)
i2c2Vcomp c2 x y f g = micsComp (i2Chs c2 x y) f g

-- For any pair of objects of the category underlying a 2-category, there
-- is a category of 2-morphisms among 1-morphisms between the two given objects.
public export
0 i2c1c : (0 c2 : Int2CatSig) -> (0 dom, cod : icObj (i2c1 c2)) -> IntCatSig
i2c1c c2 dom cod = ICat (i2c2Obj c2 dom cod) (i2Chs c2 dom cod)

public export
0 i2Cwp : (c2 : Int2CatSig) -> GlobalWhiskerPairHomStruct (i2c1 c2) (i2Chs c2)
i2Cwp c2 =
  MkGlobalWhiskerPairHomStruct (i2c1 c2) (i2Chs c2) (i2Cwl c2) (i2Cwr c2)

public export
0 i2c2Hcomp : (c2 : Int2CatSig) -> GlobalHcompHomStruct (i2c1 c2) (i2Chs c2)
i2c2Hcomp c2 = GlobalHcompFromWhiskers (i2c1 c2) (i2Chs c2) $ i2Cwp c2

public export
0 IntFunctorHCatSig : {0 idx : Type} -> (idx -> IntCatSig) -> IntCatSig
IntFunctorHCatSig {idx} cat =
  ICat
    idx
  $ MICS
    (\x, y => IntFunctorSig (cat x) (cat y))
  $ ICS
    (\x => IntFunctorSigId $ cat x)
    (\x, y, z => IntFunctorSigComp (cat x) (cat y) (cat z))

public export
0 IntFunctor2WhiskerLSig : {0 idx : Type} -> (cat : idx -> IntCatSig) ->
  Int2WhiskerLSig
    {obj=(icObj $ IntFunctorHCatSig {idx} cat)}
    {mor=(icMor $ IntFunctorHCatSig {idx} cat)}
    (icComp $ IntFunctorHCatSig {idx} cat)
    (\c, d, f, g => IntNTSig (icMor $ cat d) (ifOmap f) (ifOmap g))
IntFunctor2WhiskerLSig {idx} cat x y f z g g' alpha =
  intNTwhiskerL
    {c=(icObj $ cat x)} {d=(icObj $ cat y)} {e=(icObj $ cat z)}
    {emor=(icMor $ cat z)}
    {g=(ifOmap g)} {h=(ifOmap g')}
    alpha
    (ifOmap f)

public export
0 IntFunctor2WhiskerRSig : {0 idx : Type} -> (cat : idx -> IntCatSig) ->
  Int2WhiskerRSig
    {obj=(icObj $ IntFunctorHCatSig {idx} cat)}
    {mor=(icMor $ IntFunctorHCatSig {idx} cat)}
    (icComp $ IntFunctorHCatSig {idx} cat)
    (\c, d, f, g => IntNTSig (icMor $ cat d) (ifOmap f) (ifOmap g))
IntFunctor2WhiskerRSig {idx} cat y z g x f f' alpha =
  intNTwhiskerR
    {c=(icObj $ cat x)} {d=(icObj $ cat y)} {e=(icObj $ cat z)}
    {dmor=(icMor $ cat y)} {emor=(icMor $ cat z)}
    {f=(ifOmap f)} {g=(ifOmap f')}
    {h=(ifOmap g)}
    (ifMmap g)
    alpha

public export
0 IntFunctor2CatSig : {0 idx : Type} -> (idx -> IntCatSig) -> Int2CatSig
IntFunctor2CatSig {idx} cat =
  I2Cat
    (IntFunctorHCatSig {idx} cat)
  $ I2CS
    (\dom, cod => IntOmapCatSig (cat dom) (cat cod) ifOmap)
    (\c, d, e => FunctorCatWhiskerL (cat c) (cat d) (cat e))
    (\c, d, e => FunctorCatWhiskerR (cat c) (cat d) (cat e))

-- The category of all categories in particular is a two-category.
public export
0 IntCat2Cat : Int2CatSig
IntCat2Cat = IntFunctor2CatSig {idx=IntCatSig} id

public export
0 IntFunctor2HCompSig : {0 idx : Type} -> (cat : idx -> IntCatSig) ->
  Int2HCompSig
    {obj=(icObj $ IntFunctorHCatSig {idx} cat)}
    {mor=(icMor $ IntFunctorHCatSig {idx} cat)}
    (icComp $ IntFunctorHCatSig {idx} cat)
    (\c, d, f, g => IntNTSig (icMor $ cat d) (ifOmap f) (ifOmap g))
IntFunctor2HCompSig {idx} cat c d e f f' g g' beta alpha =
  (i2c2Hcomp $ IntFunctor2CatSig {idx} cat) c e d f f' g g' beta alpha

-----------------------------------
-----------------------------------
---- Category-indexed families ----
-----------------------------------
-----------------------------------

---------------------------------
---- Category-indexed arenas ----
---------------------------------

public export
record CIArena (c : IntCatSig) where
  constructor CIAr
  caPos : IntCatSig
  caDir : IntFunctorSig caPos c

--------------------------------------------------------------------
---- Category-indexed existential families (Dirichlet functors) ----
--------------------------------------------------------------------

public export
CIEFamObj : IntCatSig -> Type
CIEFamObj = CIArena

public export
CIEFamPosMor : {0 c : IntCatSig} -> IntMorSig (CIEFamObj c)
CIEFamPosMor {c} i j = IntFunctorSig (caPos i) (caPos j)

public export
0 CIEFamObjMor : {0 c : IntCatSig} ->
  (dom, cod : CIEFamObj c) -> CIEFamPosMor {c} dom cod -> Type
CIEFamObjMor {c} dom cod onpos =
  IntNTSig {c=(icObj $ caPos dom)} {d=(icObj c)} (icMor c)
    (ifOmap $ caDir dom)
    (ifOmap $ IntFunctorSigComp (caPos dom) (caPos cod) c (caDir cod) onpos)

public export
0 CIEFamMor : {0 c : IntCatSig} -> IntMorSig (CIEFamObj c)
CIEFamMor {c} i j = DPair (CIEFamPosMor {c} i j) (CIEFamObjMor {c} i j)

public export
0 cieFamIdPos : {0 c : IntCatSig} -> (x : CIEFamObj c) -> CIEFamPosMor {c} x x
cieFamIdPos {c} x = IntFunctorSigId (caPos x)

public export
0 cieFamIdObj : {0 c : IntCatSig} ->
  (x : CIEFamObj c) -> CIEFamObjMor {c} x x (cieFamIdPos {c} x)
cieFamIdObj {c} x =
  intNTid {c=(icObj $ caPos x)} (icMor c) (icId c) (ifOmap $ caDir x)

public export
0 cieFamId : {0 c : IntCatSig} -> IntIdSig (CIEFamObj c) (CIEFamMor {c})
cieFamId {c} x = (cieFamIdPos {c} x ** cieFamIdObj {c} x)

public export
0 cieFamCompPos : {0 c : IntCatSig} -> (x, y, z : CIEFamObj c) ->
  CIEFamMor {c} y z -> CIEFamMor {c} x y -> CIEFamPosMor {c} x z
cieFamCompPos {c} x y z g f =
  IntFunctorSigComp (caPos x) (caPos y) (caPos z) (fst g) (fst f)

public export
0 cieFamCompObj : {0 c : IntCatSig} -> (x, y, z : CIEFamObj c) ->
  (g : CIEFamMor {c} y z) -> (f : CIEFamMor {c} x y) ->
  CIEFamObjMor {c} x z (cieFamCompPos {c} x y z g f)
cieFamCompObj {c} x y z beta alpha =
  intNTvcomp {dmor=(icMor c)} (icComp c)
    (intNTwhiskerL {emor=(icMor c)}
      {g=(ifOmap $ caDir y)}
      {h=
        (ifOmap $ IntFunctorSigComp (caPos y) (caPos z) c (caDir z) (fst beta))}
      (snd beta) (ifOmap $ fst alpha))
    (snd alpha)

public export
0 cieFamComp : {0 c : IntCatSig} -> IntCompSig (CIEFamObj c) (CIEFamMor {c})
cieFamComp {c} x y z g f =
  (cieFamCompPos {c} x y z g f ** cieFamCompObj {c} x y z g f)

-----------------------------------------------------------------------
---- Category-indexed existential cofamilies (polynomial functors) ----
-----------------------------------------------------------------------

public export
CIECofamObj : IntCatSig -> Type
CIECofamObj = CIEFamObj . IntOpCat

public export
0 CIECofamPosMor : {0 c : IntCatSig} -> IntMorSig (CIECofamObj c)
CIECofamPosMor {c} = CIEFamPosMor {c=(IntOpCat c)}

public export
0 CIECofamObjMor : {0 c : IntCatSig} ->
  (dom, cod : CIECofamObj c) -> CIECofamPosMor {c} dom cod -> Type
CIECofamObjMor {c} = CIEFamObjMor {c=(IntOpCat c)}

public export
0 CIECofamMor : {0 c : IntCatSig} -> IntMorSig (CIECofamObj c)
CIECofamMor {c} = CIEFamMor {c=(IntOpCat c)}

public export
0 cieCofamIdPos : {0 c : IntCatSig} ->
  (x : CIECofamObj c) -> CIECofamPosMor {c} x x
cieCofamIdPos {c} = cieFamIdPos {c=(IntOpCat c)}

public export
0 cieCofamIdObj : {0 c : IntCatSig} ->
  (x : CIECofamObj c) -> CIECofamObjMor {c} x x (cieCofamIdPos {c} x)
cieCofamIdObj {c} = cieFamIdObj {c=(IntOpCat c)}

public export
0 cieCofamId : {0 c : IntCatSig} -> IntIdSig (CIECofamObj c) (CIECofamMor {c})
cieCofamId {c} = cieFamId {c=(IntOpCat c)}

public export
0 cieCofamCompPos : {0 c : IntCatSig} -> (x, y, z : CIECofamObj c) ->
  CIECofamMor {c} y z -> CIECofamMor {c} x y -> CIECofamPosMor {c} x z
cieCofamCompPos {c} = cieFamCompPos {c=(IntOpCat c)}

public export
0 cieCofamCompObj : {0 c : IntCatSig} -> (x, y, z : CIECofamObj c) ->
  (g : CIECofamMor {c} y z) -> (f : CIECofamMor {c} x y) ->
  CIECofamObjMor {c} x z (cieCofamCompPos {c} x y z g f)
cieCofamCompObj {c} = cieFamCompObj {c=(IntOpCat c)}

public export
0 cieCofamComp : {0 c : IntCatSig} ->
  IntCompSig (CIECofamObj c) (CIECofamMor {c})
cieCofamComp {c} = cieFamComp {c=(IntOpCat c)}

---------------------------------------------
---- Category-indexed universal families ----
---------------------------------------------

public export
CIUFamObj : IntCatSig -> Type
CIUFamObj = CIArena

public export
0 CIUFamPosMor : {0 c : IntCatSig} -> IntMorSig (CIUFamObj c)
CIUFamPosMor {c} = IntOpCatMor (CIEFamObj c) $ CIEFamPosMor {c}

public export
0 CIUFamObjMor : {0 c : IntCatSig} ->
  (dom, cod : CIUFamObj c) -> CIUFamPosMor {c} dom cod -> Type
CIUFamObjMor {c} dom cod onpos =
  IntOpNTSig {c=(icObj $ caPos cod)} {d=(icObj c)}
    (icMor c)
    (ifOmap $ caDir cod)
    (ifOmap $ IntFunctorSigComp (caPos cod) (caPos dom) c (caDir dom) onpos)

public export
0 CIUFamMor : {0 c : IntCatSig} -> IntMorSig (CIUFamObj c)
CIUFamMor {c} i j = DPair (CIUFamPosMor {c} i j) (CIUFamObjMor {c} i j)

public export
0 ciuFamIdPos : {0 c : IntCatSig} -> (x : CIUFamObj c) -> CIUFamPosMor {c} x x
ciuFamIdPos {c} x = IntFunctorSigId (caPos x)

public export
0 ciuFamIdObj : {0 c : IntCatSig} ->
  (x : CIUFamObj c) -> CIUFamObjMor {c} x x (ciuFamIdPos {c} x)
ciuFamIdObj {c} x =
  intNTid {c=(icObj $ caPos x)} (icMor c) (icId c) (ifOmap $ caDir x)

public export
0 ciuFamId : {0 c : IntCatSig} -> IntIdSig (CIUFamObj c) (CIUFamMor {c})
ciuFamId {c} x = (ciuFamIdPos {c} x ** ciuFamIdObj {c} x)

public export
0 ciuFamCompPos : {0 c : IntCatSig} -> (x, y, z : CIUFamObj c) ->
  CIUFamMor {c} y z -> CIUFamMor {c} x y -> CIUFamPosMor {c} x z
ciuFamCompPos {c} x y z g f =
  IntFunctorSigComp (caPos z) (caPos y) (caPos x) (fst f) (fst g)

public export
0 ciuFamCompObj : {0 c : IntCatSig} -> (x, y, z : CIUFamObj c) ->
  (g : CIUFamMor {c} y z) -> (f : CIUFamMor {c} x y) ->
  CIUFamObjMor {c} x z (ciuFamCompPos {c} x y z g f)
ciuFamCompObj {c} x y z beta alpha =
  intNTvcomp {dmor=(icMor c)} (icComp c)
    (snd beta)
    (intNTwhiskerL {emor=(icMor c)}
      {g=
        (ifOmap
         $ IntFunctorSigComp (caPos y) (caPos x) c (caDir x) (fst alpha))}
      {h=(ifOmap $ caDir y)}
      (snd alpha) (ifOmap $ fst beta))

public export
0 ciuFamComp : {0 c : IntCatSig} -> IntCompSig (CIUFamObj c) (CIUFamMor {c})
ciuFamComp {c} x y z g f =
  (ciuFamCompPos {c} x y z g f ** ciuFamCompObj {c} x y z g f)

-----------------------------------------------
---- Category-indexed universal cofamilies ----
-----------------------------------------------

public export
CIUCofamObj : IntCatSig -> Type
CIUCofamObj = CIUFamObj . IntOpCat

public export
0 CIUCofamPosMor : {0 c : IntCatSig} -> IntMorSig (CIUCofamObj c)
CIUCofamPosMor {c} = CIUFamPosMor {c=(IntOpCat c)}

public export
0 CIUCofamObjMor : {0 c : IntCatSig} ->
  (dom, cod : CIUCofamObj c) -> CIUCofamPosMor {c} dom cod -> Type
CIUCofamObjMor {c} = CIUFamObjMor {c=(IntOpCat c)}

public export
0 CIUCofamMor : {0 c : IntCatSig} -> IntMorSig (CIUCofamObj c)
CIUCofamMor {c} = CIUFamMor {c=(IntOpCat c)}

public export
0 ciuCofamIdPos : {0 c : IntCatSig} ->
  (x : CIUCofamObj c) -> CIUCofamPosMor {c} x x
ciuCofamIdPos {c} = ciuFamIdPos {c=(IntOpCat c)}

public export
0 ciuCofamIdObj : {0 c : IntCatSig} ->
  (x : CIUCofamObj c) -> CIUCofamObjMor {c} x x (ciuCofamIdPos {c} x)
ciuCofamIdObj {c} = ciuFamIdObj {c=(IntOpCat c)}

public export
0 ciuCofamId : {0 c : IntCatSig} -> IntIdSig (CIUCofamObj c) (CIUCofamMor {c})
ciuCofamId {c} = ciuFamId {c=(IntOpCat c)}

public export
0 ciuCofamCompPos : {0 c : IntCatSig} -> (x, y, z : CIUCofamObj c) ->
  CIUCofamMor {c} y z -> CIUCofamMor {c} x y -> CIUCofamPosMor {c} x z
ciuCofamCompPos {c} = ciuFamCompPos {c=(IntOpCat c)}

public export
0 ciuCofamCompObj : {0 c : IntCatSig} -> (x, y, z : CIUCofamObj c) ->
  (g : CIUCofamMor {c} y z) -> (f : CIUCofamMor {c} x y) ->
  CIUCofamObjMor {c} x z (ciuCofamCompPos {c} x y z g f)
ciuCofamCompObj {c} = ciuFamCompObj {c=(IntOpCat c)}

public export
0 ciuCofamComp : {0 c : IntCatSig} ->
  IntCompSig (CIUCofamObj c) (CIUCofamMor {c})
ciuCofamComp {c} = ciuFamComp {c=(IntOpCat c)}

-------------------------------------------
-------------------------------------------
---- Category-parameterized categories ----
-------------------------------------------
-------------------------------------------

-- A category parameterized over a category is a functor from that category
-- (which we call the "index" category) to the category of categories.  To
-- be explicit, this means that to each object of the index category we assign
-- a category, and to each morphism of the index category we assign a functor.
public export
IntCParamCat : IntCatSig -> Type
IntCParamCat cat = IntFunctorSig cat IntCatCat

-- An arena internal to `Cat`.  This is equivalent to a dependent pair
-- of a category and `IntCParamCat`.
public export
CatArena : Type
CatArena = CIArena IntCatCat

-----------------------------
-----------------------------
---- Monads and comonads ----
-----------------------------
-----------------------------

public export
0 IntUnitSig : {0 c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntUnitSig {c} cmor t = IntNTSig {c} {d=c} cmor id t

public export
intIdMonadUnit : {0 c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntUnitSig {c} cmor (IntIdFunctor c)
intIdMonadUnit {c} cmor cid = cid

public export
0 IntCounitSig : {0 c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntCounitSig {c} cmor t = IntNTSig {c} {d=c} cmor t id

public export
intIdComonadCounit : {0 c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntCounitSig {c} cmor (IntIdFunctor c)
intIdComonadCounit {c} cmor cid = cid

public export
0 IntMultSig : {0 c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntMultSig {c} cmor t =
  IntNTSig {c} {d=c} cmor (IntFunctorComp c c c t t) t

public export
intIdMonadMult : {0 c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntMultSig {c} cmor (IntIdFunctor c)
intIdMonadMult {c} cmor cid = cid

public export
0 IntComultSig : {0 c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntComultSig {c} cmor t =
  IntNTSig {c} {d=c} cmor t (IntFunctorComp c c c t t)

public export
intIdComonadComult : {0 c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntComultSig {c} cmor (IntIdFunctor c)
intIdComonadComult {c} cmor cid = cid

---------------------
---------------------
---- Adjunctions ----
---------------------
---------------------

public export
0 IntAdjLMapSig : {0 c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (l : c -> d) -> Type
IntAdjLMapSig {c} {d} cmor dmor = IntFMapSig {c} {d} cmor dmor

public export
0 IntAdjRMapSig : {0 c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (r : d -> c) -> Type
IntAdjRMapSig {c} {d} cmor dmor = IntFMapSig {c=d} {d=c} dmor cmor

public export
0 IntAdjLAdjunctSig : {0 c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjLAdjunctSig {c} {d} cmor dmor l r =
  (0 a : c) -> (0 b : d) -> dmor (l a) b -> cmor a (r b)

public export
0 IntAdjRAdjunctSig : {0 c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjRAdjunctSig {c} {d} cmor dmor l r =
  (0 a : c) -> (0 b : d) -> cmor a (r b) -> dmor (l a) b

public export
0 IntAdjMonad : {0 c, d : Type} -> (l : c -> d) -> (r : d -> c) -> c -> c
IntAdjMonad {c} {d} l r = IntFunctorComp c d c r l

public export
0 IntAdjMonadSig : {0 c, d : Type} -> (cmor : IntMorSig c) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjMonadSig {c} {d} cmor l r =
  IntEndoFMapSig {c} cmor (IntAdjMonad {c} {d} l r)

public export
IntAdjMonadMap : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjLMapSig {c} {d} cmor dmor l ->
  IntAdjRMapSig {c} {d} cmor dmor r ->
  IntAdjMonadSig {c} {d} cmor l r
IntAdjMonadMap {c} {d} cmor dmor l r =
  flip $ intFmapComp {c} {d} {e=c} {cmor} {dmor} {emor=cmor} {g=r} {f=l}

public export
0 IntAdjComonad : {0 c, d : Type} -> (l : c -> d) -> (r : d -> c) -> d -> d
IntAdjComonad {c} {d} l r = IntFunctorComp d c d l r

public export
0 IntAdjComonadSig : {0 c, d : Type} -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjComonadSig {c} {d} dmor l r =
  IntEndoFMapSig {c=d} dmor (IntAdjComonad {c} {d} l r)

public export
IntAdjComonadMap : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjLMapSig {c} {d} cmor dmor l ->
  IntAdjRMapSig {c} {d} cmor dmor r ->
  IntAdjComonadSig {c} {d} dmor l r
IntAdjComonadMap {c} {d} cmor dmor l r =
  intFmapComp {c=d} {d=c} {e=d} {cmor=dmor} {dmor=cmor} {emor=dmor} {g=l} {f=r}

public export
0 IntAdjUnitSig : {0 c, d : Type} -> (cmor : IntMorSig c) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjUnitSig {c} {d} cmor l r =
  IntUnitSig cmor (IntAdjMonad {c} {d} l r)

public export
0 IntAdjCounitSig : {0 c, d : Type} -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjCounitSig {c} {d} dmor l r =
  IntCounitSig {c=d} dmor (IntAdjComonad {c} {d} l r)

public export
0 IntAdjMultSig : {0 c, d : Type} -> (cmor : IntMorSig c) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjMultSig {c} {d} cmor l r =
  IntMultSig cmor (IntAdjMonad {c} {d} l r)

public export
0 IntAdjComultSig : {0 c, d : Type} -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjComultSig {c} {d} dmor l r =
  IntComultSig {c=d} dmor (IntAdjComonad {c} {d} l r)

public export
IntAdjLAdjunctFromRMapAndUnit : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (ccomp : IntCompSig c cmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjRMapSig {c} {d} cmor dmor r ->
  IntAdjUnitSig {c} {d} cmor l r ->
  IntAdjLAdjunctSig {c} {d} cmor dmor l r
IntAdjLAdjunctFromRMapAndUnit cmor dmor ccomp l r rm unit a b mdlab =
  ccomp a (r (l a)) (r b) (rm (l a) b mdlab) (unit a)

public export
IntAdjRAdjunctFromLMapAndCounit : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (dcomp : IntCompSig d dmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjLMapSig {c} {d} cmor dmor l ->
  IntAdjCounitSig {c} {d} dmor l r ->
  IntAdjRAdjunctSig {c} {d} cmor dmor l r
IntAdjRAdjunctFromLMapAndCounit cmor dmor dcomp l r lm counit a b mcrab =
  dcomp (l a) (l (r b)) b (counit b) (lm a (r b) mcrab)

public export
IntAdjLMapFromRAdjunctAndUnit : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (ccomp : IntCompSig c cmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjRAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjUnitSig {c} {d} cmor l r ->
  IntAdjLMapSig {c} {d} cmor dmor l
IntAdjLMapFromRAdjunctAndUnit cmor dmor ccomp l r radj unit x y cmxy =
  radj x (l y) $ ccomp x y (r (l y)) (unit y) cmxy

public export
IntAdjRMapFromLAdjunctAndCounit : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (dcomp : IntCompSig d dmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjLAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjCounitSig {c} {d} dmor l r ->
  IntAdjRMapSig {c} {d} cmor dmor r
IntAdjRMapFromLAdjunctAndCounit cmor dmor dcomp l r ladj counit x y dmxy =
  ladj (r x) y $ dcomp (l (r x)) x y dmxy (counit x)

public export
IntAdjUnitFromLAdjunct : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (did : IntIdSig d dmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjLAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjUnitSig {c} {d} cmor l r
IntAdjUnitFromLAdjunct {c} {d} cmor dmor did l r ladj a =
  ladj a (l a) (did $ l a)

public export
IntAdjCounitFromRAdjunct : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (cid : IntIdSig c cmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjRAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjCounitSig {c} {d} dmor l r
IntAdjCounitFromRAdjunct {c} {d} cmor dmor cid l r radj b =
  radj (r b) b (cid $ r b)

public export
IntAdjMultFromCounit : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (did : IntIdSig d dmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjRMapSig {c} {d} cmor dmor r ->
  IntAdjCounitSig {c} {d} dmor l r ->
  IntAdjMultSig {c} {d} cmor l r
IntAdjMultFromCounit {c} {d} cmor dmor did l r rm counit =
  intNTwhiskerR {c} {d} {e=c} {dmor} {emor=cmor}
    {f=(IntFunctorComp c d d (IntAdjComonad {c} {d} l r) l)}
    {g=l}
    {h=r}
    rm
  $ intNTwhiskerL {c} {d} {e=d} {emor=dmor}
    {g=(IntAdjComonad {c} {d} l r)}
    {h=(IntIdFunctor d)}
    counit
    l

public export
IntAdjComultFromUnit : {0 c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (cid : IntIdSig c cmor) ->
  (0 l : c -> d) -> (0 r : d -> c) ->
  IntAdjLMapSig {c} {d} cmor dmor l ->
  IntAdjUnitSig {c} {d} cmor l r ->
  IntAdjComultSig {c} {d} dmor l r
IntAdjComultFromUnit {c} {d} cmor dmor cid l r lm unit =
  intNTwhiskerR {c=d} {d=c} {e=d} {dmor=cmor} {emor=dmor}
    {f=r}
    {g=(IntFunctorComp d d c r (IntAdjComonad {c} {d} l r))}
    {h=l}
    lm
  $ intNTwhiskerL {c=d} {d=c} {e=c} {emor=cmor}
    {g=(IntIdFunctor c)}
    {h=(IntAdjMonad {c} {d} l r)}
    unit
    r

public export
record IntAdjointsSig (c, d : IntCatSig) where
  constructor IAdjoints
  iaL : IntFunctorSig c d
  iaR : IntFunctorSig d c

public export
record IntAdjunctsSig {c, d : IntCatSig} (lr : IntAdjointsSig c d) where
  constructor IAdjuncts
  iaLAdj :
    IntAdjLAdjunctSig (icMor c) (icMor d) (ifOmap $ iaL lr) (ifOmap $ iaR lr)
  iaRAdj :
    IntAdjRAdjunctSig (icMor c) (icMor d) (ifOmap $ iaL lr) (ifOmap $ iaR lr)

public export
record IntUnitsSig {c, d : IntCatSig} (lr : IntAdjointsSig c d) where
  constructor IUnits
  iuUnit : IntAdjUnitSig (icMor c) (ifOmap $ iaL lr) (ifOmap $ iaR lr)
  iuCounit : IntAdjCounitSig (icMor d) (ifOmap $ iaL lr) (ifOmap $ iaR lr)

public export
record IntMultsSig {c, d : IntCatSig} (lr : IntAdjointsSig c d) where
  constructor IMults
  imMult : IntAdjMultSig (icMor c) (ifOmap $ iaL lr) (ifOmap $ iaR lr)
  imComult : IntAdjComultSig (icMor d) (ifOmap $ iaL lr) (ifOmap $ iaR lr)

public export
record IntAdjunctionData {c, d : IntCatSig} (adjs : IntAdjointsSig c d) where
  constructor IAdjData
  iadAdjuncts : IntAdjunctsSig adjs
  iadUnits : IntUnitsSig adjs
  iadMults : IntMultsSig adjs

public export
record IntAdjunctionSig (c, d : IntCatSig) where
  constructor IAdjunction
  iaAdjoints : IntAdjointsSig c d
  iaData : IntAdjunctionData {c} {d} iaAdjoints
