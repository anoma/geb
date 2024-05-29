module LanguageDef.InternalCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.QType

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Internal category signatures (morphisms, identity, composition) ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

public export
IntMorSig : Type -> Type
IntMorSig c = c -> c -> Type

public export
IntIdSig : (c : Type) -> (mor : IntMorSig c) -> Type
IntIdSig c mor = (x : c) -> mor x x

public export
IntCompSig : (c : Type) -> (mor : IntMorSig c) -> Type
IntCompSig c mor = (x, y, z : c) -> mor y z -> mor x y -> mor x z

public export
record IdCompSig (obj : Type) (mor : IntMorSig obj) where
  constructor ICS
  icsId : IntIdSig obj mor
  icsComp : IntCompSig obj mor

public export
record MorIdCompSig (obj : Type) where
  constructor MICS
  micsMor : IntMorSig obj
  micsICS : IdCompSig obj micsMor

public export
micsId : {obj : Type} ->
  (mics : MorIdCompSig obj) -> IntIdSig obj (micsMor mics)
micsId {obj} mics = icsId $ micsICS mics

public export
micsComp : {obj : Type} ->
  (mics : MorIdCompSig obj) -> IntCompSig obj (micsMor mics)
micsComp {obj} mics = icsComp $ micsICS mics

public export
record IntCatSig where
  constructor ICat
  icObj : Type
  icMICS : MorIdCompSig icObj

public export
icMor : (cat : IntCatSig) -> IntMorSig (icObj cat)
icMor cat = micsMor $ icMICS cat

public export
icId : (cat : IntCatSig) -> IntIdSig (icObj cat) (icMor cat)
icId cat = micsId {obj=(icObj cat)} $ icMICS cat

public export
icComp : (cat : IntCatSig) -> IntCompSig (icObj cat) (icMor cat)
icComp cat = micsComp {obj=(icObj cat)} $ icMICS cat

-----------------
-----------------
---- Bundles ----
-----------------
-----------------

public export
record IntBundle {c : Type} (mor : IntMorSig c) where
  constructor IBundle
  ibDom : c
  ibCod : c
  ibMor : mor ibDom ibCod

------------------
------------------
---- Functors ----
------------------
------------------

public export
IntIdFunctor : (c : Type) -> c -> c
IntIdFunctor c = Prelude.id {a=c}

public export
IntFunctorComp : (c, d, e : Type) -> (d -> e) -> (c -> d) -> c -> e
IntFunctorComp c d e = (.)

public export
IntOMapSig : (c, d : Type) -> Type
IntOMapSig c d = HomProf c d

public export
IntEndoOMapSig : Type -> Type
IntEndoOMapSig c = IntOMapSig c c

public export
IntFMapSig : {c, d : Type} -> (_ : IntMorSig c) -> (_ : IntMorSig d) ->
  IntOMapSig c d -> Type
IntFMapSig {c} {d} cmor dmor omap =
  (x, y : c) -> cmor x y -> dmor (omap x) (omap y)

public export
IntEndoFMapSig : {c : Type} -> (_ : IntMorSig c) ->
  (c -> c) -> Type
IntEndoFMapSig {c} cmor = IntFMapSig {c} {d=c} cmor cmor

public export
intFMapId : {c : Type} -> (cmor : IntMorSig c) ->
  IntFMapSig {c} {d=c} cmor cmor (IntIdFunctor c)
intFMapId {c} cmor x y = Prelude.id {a=(cmor x y)}

public export
intFmapComp : {c, d, e : Type} ->
  {cmor : IntMorSig c} -> {dmor : IntMorSig d} -> {emor : IntMorSig e} ->
  {g : d -> e} -> {f : c -> d} ->
  IntFMapSig {c=d} {d=e} dmor emor g ->
  IntFMapSig {c} {d} cmor dmor f ->
  IntFMapSig {c} {d=e} cmor emor (IntFunctorComp c d e g f)
intFmapComp {c} {d} {e} {cmor} {dmor} {emor} {g} {f} gm fm x y =
  gm (f x) (f y) . fm x y

public export
record IntFunctorSig (dom, cod : IntCatSig) where
  constructor IFunctor
  ifOmap : icObj dom -> icObj cod
  ifMmap :
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
HomStruct : (c : IntCatSig) -> IntMorSig (icObj c)
HomStruct c x y = MorIdCompSig $ icMor c x y

-- A global hom-set structure is the imposition of a (categorical)
-- structure on every hom-set of a category.
public export
GlobalHomStruct : IntCatSig -> Type
GlobalHomStruct c = (x, y : icObj c) -> HomStruct c x y

-- By itself, imposing a global hom-set structure defines a category
-- whose objects are the morphisms of the underlying category, but
-- which only has 2-morphisms (i.e. morphisms between (1-)morphisms) between
-- 1-morphisms (i.e. morphisms of the underlying category) which have the same
-- domain and codomain in the underlying category.  In other words, that
-- category can be divided into zero or more connected components per pair of
-- objects of the underlying category.

public export
ghsObj : {c : IntCatSig} -> GlobalHomStruct c -> Type
ghsObj {c} ghs =
  Sigma {a=(ProductMonad $ icObj c)} (\xy => icMor c (fst xy) (snd xy))

public export
data GHSmor : {c : IntCatSig} ->
    (ghs : GlobalHomStruct c) -> IntMorSig (ghsObj {c} ghs) where
  Gh2m : {c : IntCatSig} -> {ghs : GlobalHomStruct c} ->
    {x, y : icObj c} -> {f, g : icMor c x y} ->
    micsMor {obj=(icMor c x y)} (ghs x y) f g ->
    GHSmor {c} ghs ((x, y) ** f) ((x, y) ** g)

public export
ghsId : {c : IntCatSig} ->
 (ghs : GlobalHomStruct c) -> IntIdSig (ghsObj {c} ghs) (GHSmor {c} ghs)
ghsId {c} ghs m = case m of
  ((x, y) ** f) =>
    Gh2m {c} {ghs} {x} {y} {f} {g=f} $ micsId {obj=(icMor c x y)} (ghs x y) f

public export
ghsComp : {c : IntCatSig} ->
  (ghs : GlobalHomStruct c) -> IntCompSig (ghsObj {c} ghs) (GHSmor {c} ghs)
ghsComp {c} ghs m'' m' m beta alpha with (m'', m', m, beta, alpha)
  ghsComp {c} ghs _ _ _ beta alpha |
    (((w, x) ** f),
     ((x', y) ** g),
     ((y', z) ** h),
     Gh2m {c} {ghs} {x=x''} {y=y''} {f=g'} {g=h'} bm,
     Gh2m {c} {ghs} {x=x''} {y=y''} {f=f'} {g=g'} am) =
      Gh2m $ micsComp {obj=(icMor c x'' y'')} (ghs x'' y'') f' g' h' bm am

public export
ghsICS : {c : IntCatSig} ->
  (ghs : GlobalHomStruct c) -> IdCompSig (ghsObj {c} ghs) (GHSmor {c} ghs)
ghsICS {c} ghs =
  ICS
    {obj=(ghsObj {c} ghs)}
    {mor=(GHSmor {c} ghs)}
    (ghsId {c} ghs)
    (ghsComp {c} ghs)

public export
ghsMICS : {c : IntCatSig} ->
  (ghs : GlobalHomStruct c) -> MorIdCompSig (ghsObj {c} ghs)
ghsMICS {c} ghs = MICS {obj=(ghsObj {c} ghs)} (GHSmor {c} ghs) (ghsICS {c} ghs)

public export
ghsCat : {c : IntCatSig} -> GlobalHomStruct c -> IntCatSig
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
LeftWhiskerMorphStruct : (ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic d e -> icMor ic c d -> Type
LeftWhiskerMorphStruct ic c d e hsce hsde f =
  (g, g' : icMor ic d e) ->
  micsMor hsde g g' ->
  micsMor hsce (icComp ic c d e g f) (icComp ic c d e g' f)

public export
RightWhiskerMorphStruct : (ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic c d -> icMor ic d e -> Type
RightWhiskerMorphStruct ic c d e hsce hscd g =
  (f, f' : icMor ic c d) ->
  micsMor hscd f f' ->
  micsMor hsce (icComp ic c d e g f) (icComp ic c d e g f')

-- We may further define notions that _all_ morphisms in a given hom-set
-- may be left- or right-whiskered.

public export
LeftWhiskerHomStruct : (ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic d e -> Type
LeftWhiskerHomStruct ic c d e hsce hsde =
  (f : icMor ic c d) -> LeftWhiskerMorphStruct ic c d e hsce hsde f

public export
RightWhiskerHomStruct : (ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic c d -> Type
RightWhiskerHomStruct ic c d e hsce hscd =
  (g : icMor ic d e) -> RightWhiskerMorphStruct ic c d e hsce hscd g

-- We may further define notions that all morphisms in _all_ hom-sets
-- may be left- or right-whiskered.

public export
GlobalLeftWhiskerHomStruct : (ic : IntCatSig) -> GlobalHomStruct ic -> Type
GlobalLeftWhiskerHomStruct ic ghs =
  (c, d, e : icObj ic) -> LeftWhiskerHomStruct ic c d e (ghs c e) (ghs d e)

public export
GlobalRightWhiskerHomStruct : (ic : IntCatSig) -> GlobalHomStruct ic -> Type
GlobalRightWhiskerHomStruct ic ghs =
  (c, d, e : icObj ic) -> RightWhiskerHomStruct ic c d e (ghs c e) (ghs c d)

-- We may also define notions of having both left _and_ right whisker
-- structures.

public export
record WhiskerPairHomStruct (ic : IntCatSig) (c, d, e : icObj ic)
  (hsce : HomStruct ic c e) (hscd : HomStruct ic c d) (hsde : HomStruct ic d e)
  where
    constructor WPHS
    wphsL : LeftWhiskerHomStruct ic c d e hsce hsde
    wphsR : RightWhiskerHomStruct ic c d e hsce hscd

public export
GlobalWhiskerPairHomStruct : (ic : IntCatSig) -> GlobalHomStruct ic -> Type
GlobalWhiskerPairHomStruct ic ghs =
  (c, d, e : icObj ic) ->
  WhiskerPairHomStruct ic c d e (ghs c e) (ghs c d) (ghs d e)

public export
MkGlobalWhiskerPairHomStruct : (ic : IntCatSig) ->
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
HcompHomStruct : (ic : IntCatSig) -> (c, d, e : icObj ic) ->
  HomStruct ic c e -> HomStruct ic c d -> HomStruct ic d e -> Type
HcompHomStruct ic c d e hsce hscd hsde =
  (f, f' : icMor ic c d) -> (g, g' : icMor ic d e) ->
  (beta : micsMor hsde g g') -> (alpha : micsMor hscd f f') ->
  micsMor hsce (icComp ic c d e g f) (icComp ic c d e g' f')

public export
GlobalHcompHomStruct : (ic : IntCatSig) -> GlobalHomStruct ic -> Type
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
HcompFromWhiskers : (ic : IntCatSig) ->
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
GlobalHcompFromWhiskers : (ic : IntCatSig) -> (ghs : GlobalHomStruct ic) ->
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
IntNTSig : {c, d : Type} -> (dmor : IntMorSig d) ->
  (f, g : c -> d) -> Type
IntNTSig {c} {d} dmor f g = (x : c) -> dmor (f x) (g x)

public export
intNTid : {c, d : Type} -> (dmor : IntMorSig d) ->
  (_ : IntIdSig d dmor) ->
  (f : c -> d) -> IntNTSig {c} {d} dmor f f
intNTid {c} {d} dmor did f x = did $ f x

public export
intNTvcomp : {c, d : Type} -> {dmor : IntMorSig d} ->
  IntCompSig d dmor ->
  {f, g, h : c -> d} ->
  IntNTSig {c} {d} dmor g h ->
  IntNTSig {c} {d} dmor f g ->
  IntNTSig {c} {d} dmor f h
intNTvcomp {c} {d} {dmor} dcomp {f} {g} {h} beta alpha x =
  dcomp (f x) (g x) (h x) (beta x) (alpha x)

public export
IntOmapCatSig : (dom, cod : IntCatSig) ->
  {obj : Type} -> (obj -> icObj dom -> icObj cod) -> MorIdCompSig obj
IntOmapCatSig dom cod {obj} omap =
  MICS
    (\f, g => IntNTSig (icMor cod) (omap f) (omap g))
  $ ICS
    (\f => intNTid (icMor cod) (icId cod) (omap f))
    (\f, g, h => intNTvcomp {f=(omap f)} {g=(omap g)} {h=(omap h)} (icComp cod))

public export
IntFunctorOmapCatSig : IntCatSig -> IntCatSig -> IntCatSig
IntFunctorOmapCatSig dom cod =
  ICat (icObj dom -> icObj cod) $ IntOmapCatSig dom cod id

-- Given a pair of categories, we can form a "functor category",
-- whose objects are the functors from one to the other and whose
-- morphisms are the natural transformations among those functors.
public export
IntFunctorCatSig : IntCatSig -> IntCatSig -> IntCatSig
IntFunctorCatSig dom cod =
  ICat (IntFunctorSig dom cod) $ IntOmapCatSig dom cod ifOmap

-- The functor category (whose morphisms are natural transformations)
-- imposes a categorical structure on the set of functors between a pair
-- of categories.  In particular this means it imposes a global hom-struct
-- on the category of categories.
public export
FunctorCatHomStruct : GlobalHomStruct IntCatCat
FunctorCatHomStruct c d = icMICS $ IntFunctorCatSig c d

-- We can also whisker natural transformations.

public export
intNTwhiskerL : {c, d, e : Type} ->
  {emor : IntMorSig e} ->
  {g, h : d -> e} ->
  IntNTSig {c=d} {d=e} emor g h ->
  (f : c -> d) ->
  IntNTSig {c} {d=e} emor
    (IntFunctorComp c d e g f)
    (IntFunctorComp c d e h f)
intNTwhiskerL {c} {d} {e} {emor} {g} {h} alpha f x = alpha (f x)

public export
intNTwhiskerR : {c, d, e : Type} ->
  {dmor : IntMorSig d} -> {emor : IntMorSig e} ->
  {f, g : c -> d} ->
  {h : d -> e} ->
  IntFMapSig {c=d} {d=e} dmor emor h ->
  IntNTSig {c} {d} dmor f g ->
  IntNTSig {c} {d=e} emor
    (IntFunctorComp c d e h f)
    (IntFunctorComp c d e h g)
intNTwhiskerR {c} {d} {e} {dmor} {emor} {f} {g} {h} hm nu x =
  hm (f x) (g x) (nu x)

public export
FunctorCatWhiskerL :
  GlobalLeftWhiskerHomStruct IntCatCat FunctorCatHomStruct
FunctorCatWhiskerL c d e f g g' alpha =
  intNTwhiskerL
    {c=(icObj c)} {d=(icObj d)} {e=(icObj e)}
    {emor=(icMor e)}
    {g=(ifOmap g)} {h=(ifOmap g')}
    alpha (ifOmap f)

public export
FunctorCatWhiskerR :
  GlobalRightWhiskerHomStruct IntCatCat FunctorCatHomStruct
FunctorCatWhiskerR c d e g f f' beta =
  intNTwhiskerR
    {c=(icObj c)} {d=(icObj d)} {e=(icObj e)}
    {dmor=(icMor d)} {emor=(icMor e)}
    {f=(ifOmap f)} {g=(ifOmap f')} {h=(ifOmap g)}
    (ifMmap g) beta

public export
FunctorCatWhiskerPair :
  GlobalWhiskerPairHomStruct IntCatCat FunctorCatHomStruct
FunctorCatWhiskerPair c d e =
  WPHS (FunctorCatWhiskerL c d e) (FunctorCatWhiskerR c d e)

-- Because we have both directions of whiskering structure on the category
-- of categories, we can compose them to impose a horizontal composition.

public export
intNThcomp : {c, d, e : Type} ->
  {dmor : IntMorSig d} -> {emor : IntMorSig e} ->
  IntCompSig e emor ->
  {f, f' : c -> d} ->
  {g, g' : d -> e} ->
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
FunctorCatHcomp :
  GlobalHcompHomStruct IntCatCat FunctorCatHomStruct
FunctorCatHcomp =
  GlobalHcompFromWhiskers
    IntCatCat
    FunctorCatHomStruct
    FunctorCatWhiskerPair

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
IntOpCatMor : (c : Type) -> IntMorSig c -> IntMorSig c
IntOpCatMor c cmor = flip cmor

public export
IntOpCatId : (c : Type) -> (cmor : IntMorSig c) ->
  IntIdSig c cmor -> IntIdSig c (IntOpCatMor c cmor)
IntOpCatId c cmor cid = cid

public export
IntOpCatComp : (c : Type) -> (cmor : IntMorSig c) ->
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
IntOpFunctor : {c, d : IntCatSig} ->
  IntFunctorSig c d -> IntFunctorSig (IntOpCat c) (IntOpCat d)
IntOpFunctor {c} {d} f = IFunctor (ifOmap f) (\x, y => ifMmap f y x)

public export
IntOpFunctorSigComp : (c, d, e : IntCatSig) ->
  IntOpFunctorSig d e ->
  IntOpFunctorSig c d ->
  IntOpFunctorSig c e
IntOpFunctorSigComp c d e =
  IntFunctorSigComp (IntOpCat c) (IntOpCat d) (IntOpCat e)

public export
IntOpNTSig : {c, d : Type} -> (dmor : IntMorSig d) ->
  (f, g : c -> d) -> Type
IntOpNTSig {c} {d} dmor = flip $ IntNTSig {c} {d} dmor

public export
IntOpNT : {c, d : Type} -> {dmor : IntMorSig d} ->
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
data DiscreteCatMor : {obj : Type} ->
    DiscreteCatObj obj -> DiscreteCatObj obj -> Type where
  DCid : {obj : Type} -> (x : obj) -> DiscreteCatMor {obj} x x

public export
DiscreteId : {obj : Type} ->
  IntIdSig (DiscreteCatObj obj) (DiscreteCatMor {obj})
DiscreteId {obj} x = DCid x

public export
DiscreteComp : {obj : Type} ->
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
InitialCatMor : InitialCatObj -> InitialCatObj -> Type
InitialCatMor = DiscreteCatMor {obj=Void}

public export
InitialId : IntIdSig InitialCatObj InitialCatMor
InitialId = DiscreteId {obj=Void}

public export
InitialComp : IntCompSig InitialCatObj InitialCatMor
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
TerminalCatMor : TerminalCatObj -> TerminalCatObj -> Type
TerminalCatMor = DiscreteCatMor {obj=Unit}

public export
TerminalId : IntIdSig TerminalCatObj TerminalCatMor
TerminalId = DiscreteId {obj=Unit}

public export
TerminalComp : IntCompSig TerminalCatObj TerminalCatMor
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
IntCoprodCatMor : (c, d : Type) ->
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
IntEndoCoprodCatMor : (c : Type) ->
  IntMorSig c -> IntMorSig (IntEndoCoprodCatObj c)
IntEndoCoprodCatMor c mor = IntCoprodCatMor c c mor mor

public export
IntCoprodCatId : (c, d : Type) ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  IntIdSig c cmor -> IntIdSig d dmor ->
  IntIdSig (IntCoprodCatObj c d) (IntCoprodCatMor c d cmor dmor)
IntCoprodCatId c d cmor dmor cid did cdobj =
  case cdobj of
    Left cobj => cid cobj
    Right dobj => did dobj

public export
IntCoprodCatComp : (c, d : Type) ->
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
IntProdCatMor : (c, d : Type) ->
  IntMorSig c -> IntMorSig d -> IntMorSig (IntProdCatObj c d)
IntProdCatMor c d cmor dmor ab ab' =
  (cmor (fst ab) (fst ab'), dmor (snd ab) (snd ab'))

public export
IntEndoProdCatObj : Type -> Type
IntEndoProdCatObj c = IntProdCatObj c c

public export
IntEndoProdCatMor : (c : Type) ->
  IntMorSig c -> IntMorSig (IntEndoProdCatObj c)
IntEndoProdCatMor c mor = IntProdCatMor c c mor mor

public export
IntProdCatId : (c, d : Type) ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  IntIdSig c cmor -> IntIdSig d dmor ->
  IntIdSig (IntProdCatObj c d) (IntProdCatMor c d cmor dmor)
IntProdCatId c d cmor dmor cid did cdobj = (cid $ fst cdobj, did $ snd cdobj)

public export
IntProdCatComp : (c, d : Type) ->
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
IntEndoOpProdCatObj : Type -> Type
IntEndoOpProdCatObj c = IntOpProdCatObj c c

public export
IntOpProdCatMor : (d, c : Type) ->
  IntMorSig d -> IntMorSig c -> IntMorSig (d, c)
IntOpProdCatMor d c dmor cmor = IntProdCatMor d c (IntOpCatMor d dmor) cmor

public export
IntEndoOpProdCatMor :
  (c : Type) -> IntMorSig c -> IntMorSig (c, c)
IntEndoOpProdCatMor c mor = IntOpProdCatMor c c mor mor

public export
IntOpProdCatId : (d, c : Type) ->
  (dmor : IntMorSig d) -> (cmor : IntMorSig c) ->
  IntIdSig d dmor -> IntIdSig c cmor ->
  IntIdSig (d, c) (IntOpProdCatMor d c dmor cmor)
IntOpProdCatId d c dmor cmor = IntProdCatId d c (IntOpCatMor d dmor) cmor

public export
IntEndoOpProdCatId : (c : Type) -> (cmor : IntMorSig c) ->
  IntIdSig c cmor -> IntIdSig (c, c) (IntEndoOpProdCatMor c cmor)
IntEndoOpProdCatId c cmor cid = IntOpProdCatId c c cmor cmor cid cid

public export
IntOpProdCatComp : (d, c : Type) ->
  (dmor : IntMorSig d) -> (cmor : IntMorSig c) ->
  IntCompSig d dmor -> IntCompSig c cmor ->
  IntCompSig (d, c) (IntOpProdCatMor d c dmor cmor)
IntOpProdCatComp d c dmor cmor dcomp ccomp =
  IntProdCatComp d c (IntOpCatMor d dmor) cmor (IntOpCatComp d dmor dcomp) ccomp

public export
IntEndoOpProdCatComp : (c : Type) -> (cmor : IntMorSig c) ->
  IntCompSig c cmor -> IntCompSig (c, c) (IntEndoOpProdCatMor c cmor)
IntEndoOpProdCatComp c cmor cid = IntOpProdCatComp c c cmor cmor cid cid

public export
IntOpProdCat : IntCatSig -> IntCatSig -> IntCatSig
IntOpProdCat d c = IntProdCat (IntOpCat d) c

public export
IntEndoOpProdCat : IntCatSig -> IntCatSig
IntEndoOpProdCat c = IntOpProdCat c c

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
TypeMor : TypeObj -> TypeObj -> Type
TypeMor = HomProf

public export
typeId : IntIdSig TypeObj TypeMor
typeId _ = Prelude.id

public export
typeComp : IntCompSig TypeObj TypeMor
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
OpTypeMor : OpTypeObj -> OpTypeObj -> Type
OpTypeMor = IntOpCatMor TypeObj TypeMor

public export
opTypeId : IntIdSig OpTypeObj OpTypeMor
opTypeId = IntOpCatId TypeObj TypeMor typeId

public export
opTypeComp : IntCompSig OpTypeObj OpTypeMor
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

---------------------------------------------------
---- Metalanguage base category with quotients ----
---------------------------------------------------

public export
QTypeObj : Type
QTypeObj = QType

public export
QTypeMor : QTypeObj -> QTypeObj -> Type
QTypeMor = QMorph

public export
qTypeId : IntIdSig QTypeObj QTypeMor
qTypeId = qmId

public export
qTypeComp : IntCompSig QTypeObj QTypeMor
qTypeComp a b c = qmComp {a} {b} {c}

public export
QTypeCat : IntCatSig
QTypeCat =
  ICat
    QTypeObj
  $ MICS
    QTypeMor
  $ ICS
    qTypeId
    qTypeComp

---------------------------------------
---- Metalanguage slice categories ----
---------------------------------------

public export
SliceMor : (c : Type) -> SliceObj c -> SliceObj c -> Type
SliceMor c x y = (ec : c) -> x ec -> y ec

public export
SliceId : (c : Type) -> IntIdSig (SliceObj c) (SliceMor c)
SliceId _ _ _ = id

public export
SliceComp : (c : Type) -> IntCompSig (SliceObj c) (SliceMor c)
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
OpSliceMor : (c : Type) -> OpSliceObj c -> OpSliceObj c -> Type
OpSliceMor c = IntOpCatMor (SliceObj c) (SliceMor c)

OpSliceId : (c : Type) -> IntIdSig (OpSliceObj c) (OpSliceMor c)
OpSliceId c = IntOpCatId (SliceObj c) (SliceMor c) (SliceId c)

public export
OpSliceComp : (c : Type) -> IntCompSig (OpSliceObj c) (OpSliceMor c)
OpSliceComp c = IntOpCatComp (SliceObj c) (SliceMor c) (SliceComp c)

public export
OpSliceCat : Type -> IntCatSig
OpSliceCat c = IntOpCat (SliceCat c)

------------------------
---- (Co)presheaves ----
------------------------

public export
IntCopreshfSig : Type -> Type
IntCopreshfSig c = IntOMapSig c TypeObj

public export
IntQCopreshfSig : Type -> Type
IntQCopreshfSig c = IntOMapSig c QTypeObj

public export
IntPreshfSig : Type -> Type
IntPreshfSig = IntCopreshfSig . IntOpCatObj

public export
IntQPreshfSig : Type -> Type
IntQPreshfSig = IntQCopreshfSig . IntOpCatObj

public export
IntCopreshfMapSig : (c : Type) -> (mor : IntMorSig c) ->
  (objmap : IntCopreshfSig c) -> Type
IntCopreshfMapSig c mor = IntFMapSig mor TypeMor

public export
IntQCopreshfMapSig : (c : Type) -> (mor : IntMorSig c) ->
  (objmap : IntQCopreshfSig c) -> Type
IntQCopreshfMapSig c mor = IntFMapSig mor QTypeMor

public export
0 IntCopreshfMapId :
  {c : Type} -> {mor : IntMorSig c} -> (cid : IntIdSig c mor) ->
  {objmap : IntQCopreshfSig c} -> IntQCopreshfMapSig c mor objmap -> Type
IntCopreshfMapId {c} {mor} cid {objmap} fmap =
  (x : c) ->
  QMExtEqC {x=(objmap x)} {y=(objmap x)} (fmap x x $ cid x) (qTypeId (objmap x))

public export
0 IntCopreshfMapComp :
  {c : Type} -> {mor : IntMorSig c} -> (comp : IntCompSig c mor) ->
  {objmap : IntQCopreshfSig c} -> IntQCopreshfMapSig c mor objmap -> Type
IntCopreshfMapComp {c} {mor} comp {objmap} fmap =
  (x, y, z : c) -> (myz : mor y z) -> (mxy : mor x y) ->
    QMExtEqC {x=(objmap x)} {y=(objmap z)}
      (qmComp (fmap y z myz) (fmap x y mxy))
      (fmap x z $ comp x y z myz mxy)

public export
IntPreshfMapSig : (c : Type) -> (mor : IntMorSig c) ->
  (objmap : IntPreshfSig c) -> Type
IntPreshfMapSig c mor = IntCopreshfMapSig (IntOpCatObj c) (IntOpCatMor c mor)

public export
IntQPreshfMapSig : (c : Type) -> (mor : IntMorSig c) ->
  (objmap : IntQPreshfSig c) -> Type
IntQPreshfMapSig c mor = IntQCopreshfMapSig (IntOpCatObj c) (IntOpCatMor c mor)

public export
0 IntPreshfMapId :
  {c : Type} -> {mor : IntMorSig c} -> (cid : IntIdSig c mor) ->
  {objmap : IntQPreshfSig c} -> IntQPreshfMapSig c mor objmap -> Type
IntPreshfMapId {c} {mor} cid =
  IntCopreshfMapId
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    (IntOpCatId c mor cid)

public export
0 IntPreshfMapComp :
  {c : Type} -> {mor : IntMorSig c} -> (comp : IntCompSig c mor) ->
  {objmap : IntQPreshfSig c} -> IntQPreshfMapSig c mor objmap -> Type
IntPreshfMapComp {c} {mor} comp =
  IntCopreshfMapComp
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    (IntOpCatComp c mor comp)

public export
IntCopreshfNTSig : (c : Type) -> (pobj, qobj : IntCopreshfSig c) -> Type
IntCopreshfNTSig c pobj qobj = SliceMor c pobj qobj

public export
IntQCopreshfNTSig : (c : Type) -> (pobj, qobj : IntQCopreshfSig c) -> Type
IntQCopreshfNTSig c pobj qobj = (ec : c) -> QMorph (pobj ec) (qobj ec)

-- The naturality condition of a natural transformation between copresheaves.
public export
0 IntCopreshfNTNaturality :
  (c : Type) -> (cmor : IntMorSig c) ->
  (0 pobj, qobj : IntCopreshfSig c) ->
  IntCopreshfMapSig c cmor pobj -> IntCopreshfMapSig c cmor qobj ->
  IntCopreshfNTSig c pobj qobj -> Type
IntCopreshfNTNaturality c cmor pobj qobj pmap qmap alpha =
  (x, y : c) -> (m : cmor x y) ->
  ExtEq {a=(pobj x)} {b=(qobj y)}
    (qmap x y m . alpha x)
    (alpha y . pmap x y m)

public export
0 IntQCopreshfNTNaturality :
  (c : Type) -> (cmor : IntMorSig c) ->
  (0 pobj, qobj : IntQCopreshfSig c) ->
  IntQCopreshfMapSig c cmor pobj -> IntQCopreshfMapSig c cmor qobj ->
  IntQCopreshfNTSig c pobj qobj -> Type
IntQCopreshfNTNaturality c cmor pobj qobj pmap qmap alpha =
  (x, y : c) -> (m : cmor x y) ->
  QMExtEqC {x=(pobj x)} {y=(qobj y)}
    (qmComp (qmap x y m) (alpha x))
    (qmComp (alpha y) (pmap x y m))

public export
IntPreshfNTSig : (c : Type) -> (pobj, qobj : IntPreshfSig c) -> Type
IntPreshfNTSig c = IntCopreshfNTSig (IntOpCatObj c)

public export
IntQPreshfNTSig : (c : Type) -> (pobj, qobj : IntQPreshfSig c) -> Type
IntQPreshfNTSig c = IntQCopreshfNTSig (IntOpCatObj c)

-- The naturality condition of a natural transformation between presheaves.
public export
0 IntPreshfNTNaturality :
  (c : Type) -> (cmor : IntMorSig c) ->
  (0 pobj, qobj : IntPreshfSig c) ->
  IntPreshfMapSig c cmor pobj -> IntPreshfMapSig c cmor qobj ->
  IntPreshfNTSig c pobj qobj -> Type
IntPreshfNTNaturality c cmor =
  IntCopreshfNTNaturality (IntOpCatObj c) (IntOpCatMor c cmor)

public export
0 IntQPreshfNTNaturality :
  (c : Type) -> (cmor : IntMorSig c) ->
  (0 pobj, qobj : IntQPreshfSig c) ->
  IntQPreshfMapSig c cmor pobj -> IntQPreshfMapSig c cmor qobj ->
  IntQPreshfNTSig c pobj qobj -> Type
IntQPreshfNTNaturality c cmor =
  IntQCopreshfNTNaturality (IntOpCatObj c) (IntOpCatMor c cmor)

public export
record IntCopreshfObj {c : Type}
    (mor : IntMorSig c) (cid : IntIdSig c mor) (comp : IntCompSig c mor)
    where
  constructor ICopre
  icprOmap : IntQCopreshfSig c
  icprFmap : IntQCopreshfMapSig c mor icprOmap
  icprFid : IntCopreshfMapId {c} {mor} cid {objmap=icprOmap} icprFmap
  icprFcomp : IntCopreshfMapComp {c} {mor} comp {objmap=icprOmap} icprFmap

public export
record IntCopreshfMor {c : Type} {mor : IntMorSig c}
    {cid : IntIdSig c mor} {comp : IntCompSig c mor}
    (p, q : IntCopreshfObj {c} mor cid comp) where
  constructor ICopreM
  icprNT : IntQCopreshfNTSig c (icprOmap p) (icprOmap q)
  0 icprNatural :
    IntQCopreshfNTNaturality c mor (icprOmap p) (icprOmap q)
      (icprFmap p) (icprFmap q) icprNT

public export
IntCopreshfIdNT : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p : IntCopreshfObj {c} mor cid comp) ->
  IntQCopreshfNTSig c
    (icprOmap {c} {mor} {cid} {comp} p)
    (icprOmap {c} {mor} {cid} {comp} p)
IntCopreshfIdNT {c} {mor} {cid} {comp} x ec = qmId $ icprOmap x ec

public export
0 IntCopreshfIdNatural : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p : IntCopreshfObj {c} mor cid comp) ->
  IntQCopreshfNTNaturality c mor
    (icprOmap {c} {mor} {cid} {comp} p) (icprOmap {c} {mor} {cid} {comp} p)
    (icprFmap {c} {mor} {cid} {comp} p) (icprFmap {c} {mor} {cid} {comp} p)
    (IntCopreshfIdNT {c} {mor} {cid} {comp} p)
IntCopreshfIdNatural {c} {mor} {cid} {comp} p x y m =
  QMorphPres (icprFmap p x y m)

public export
IntCopreshfId : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntIdSig
    (IntCopreshfObj {c} mor cid comp)
    (IntCopreshfMor {c} {mor} {cid} {comp})
IntCopreshfId {c} {mor} {cid} {comp} x =
  ICopreM
    (IntCopreshfIdNT {c} {mor} {cid} {comp} x)
    (IntCopreshfIdNatural {c} {mor} {cid} {comp} x)

public export
IntCopreshfCompNT : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p, q, r : IntCopreshfObj {c} mor cid comp) ->
  IntCopreshfMor {c} {mor} {cid} {comp} q r ->
  IntCopreshfMor {c} {mor} {cid} {comp} p q ->
  IntQCopreshfNTSig c (icprOmap p) (icprOmap r)
IntCopreshfCompNT {c} {mor} {cid} {comp} p q r m' m ec =
  qmComp (icprNT m' ec) (icprNT m ec)

public export
0 IntCopreshfCompNatural : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p, q, r : IntCopreshfObj {c} mor cid comp) ->
  (m' : IntCopreshfMor {c} {mor} {cid} {comp} q r) ->
  (m : IntCopreshfMor {c} {mor} {cid} {comp} p q) ->
  IntQCopreshfNTNaturality c mor
    (icprOmap p) (icprOmap r)
    (icprFmap p) (icprFmap r)
    (IntCopreshfCompNT {c} {mor} {cid} {comp} p q r m' m)
IntCopreshfCompNatural {c} {mor} {cid} {comp} p q r m' m x y f epx epx' rpx =
  QRtrans
    (QMorphPres
      (icprNT m' y)
      (QMorphBase (icprFmap q x y f) $ QMorphBase (icprNT m x) epx')
      (QMorphBase (icprNT m y) $ QMorphBase (icprFmap p x y f) epx')
      (icprNatural m x y f epx' epx' $ QRrefl {x=(icprOmap p x)} {ex=epx'}))
    (icprNatural m' x y f
      (QMorphBase (icprNT m x) epx) (QMorphBase (icprNT m x) epx')
      $ QMorphPres (icprNT m x) epx epx' rpx)

public export
IntCopreshfComp : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntCompSig
    (IntCopreshfObj {c} mor cid comp)
    (IntCopreshfMor {c} {mor} {cid} {comp})
IntCopreshfComp {c} {mor} {cid} {comp} p q r m' m =
  ICopreM
    (IntCopreshfCompNT {c} {mor} {cid} {comp} p q r m' m)
    (IntCopreshfCompNatural {c} {mor} {cid} {comp} p q r m' m)

public export
IntCopreshfCat : {c : Type} -> (mor : IntMorSig c) ->
  IntIdSig c mor -> IntCompSig c mor -> IntCatSig
IntCopreshfCat {c} mor cid comp =
  ICat
    (IntCopreshfObj {c} mor cid comp)
  $ MICS
    (IntCopreshfMor {c} {mor} {cid} {comp})
  $ ICS
    (IntCopreshfId {c} {mor} {cid} {comp})
    (IntCopreshfComp {c} {mor} {cid} {comp})

public export
IntPreshfObj : {c : Type} -> (mor : IntMorSig c) ->
  IntIdSig c mor -> IntCompSig c mor -> Type
IntPreshfObj {c} mor cid comp =
  IntCopreshfObj {c=(IntOpCatObj c)}
    (IntOpCatMor c mor) (IntOpCatId c mor cid) (IntOpCatComp c mor comp)

public export
IPre : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (omap : IntQPreshfSig c) -> (cfmap : IntQPreshfMapSig c mor omap) ->
  IntPreshfMapId {c} {mor} cid {objmap=omap} cfmap ->
  IntPreshfMapComp {c} {mor} comp {objmap=omap} cfmap ->
  IntPreshfObj {c} mor cid comp
IPre {c} {mor} {cid} {comp} =
  ICopre
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
iprOmap : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntPreshfObj {c} mor cid comp -> IntQPreshfSig c
iprOmap {c} {mor} {cid} {comp} =
  icprOmap
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
iprFmap : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p : IntPreshfObj {c} mor cid comp) ->
  IntQPreshfMapSig c mor (iprOmap {c} {mor} {cid} {comp} p)
iprFmap {c} {mor} {cid} {comp} =
  icprFmap
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
iprFid : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p : IntPreshfObj {c} mor cid comp) ->
  IntPreshfMapId cid
    {objmap=(iprOmap {c} {mor} {cid} {comp} p)}
    (iprFmap {c} {mor} {cid} {comp} p)
iprFid {c} {mor} {cid} {comp} =
  icprFid
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
iprFcomp : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p : IntPreshfObj {c} mor cid comp) ->
  IntPreshfMapComp comp
    {objmap=(iprOmap {c} {mor} {cid} {comp} p)}
    (iprFmap {c} {mor} {cid} {comp} p)
iprFcomp {c} {mor} {cid} {comp} =
  icprFcomp
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
IntPreshfMor : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p, q : IntPreshfObj {c} mor cid comp) ->
  Type
IntPreshfMor {c} {mor} {cid} {comp} =
  IntCopreshfMor
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
IPreM : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p, q : IntPreshfObj {c} mor cid comp} ->
  (nt : IntQPreshfNTSig c
    (iprOmap {c} {mor} {cid} {comp} p) (iprOmap {c} {mor} {cid} {comp} q)) ->
  (0 _ : IntQPreshfNTNaturality c mor
    (iprOmap {c} {mor} {cid} {comp} p) (iprOmap {c} {mor} {cid} {comp} q)
    (iprFmap {c} {mor} {cid} {comp} p) (iprFmap {c} {mor} {cid} {comp} q)
    nt) ->
  IntPreshfMor {c} {mor} {cid} {comp} p q
IPreM {c} {mor} {cid} {comp} =
  ICopreM
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
iprNT : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p, q : IntPreshfObj {c} mor cid comp} ->
  IntPreshfMor {c} {mor} {cid} {comp} p q ->
  IntQPreshfNTSig c
    (iprOmap {c} {mor} {cid} {comp} p) (iprOmap {c} {mor} {cid} {comp} q)
iprNT {c} {mor} {cid} {comp} =
  icprNT
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
0 iprNatural : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p, q : IntPreshfObj {c} mor cid comp} ->
  (m : IntPreshfMor {c} {mor} {cid} {comp} p q) ->
  IntQPreshfNTNaturality c mor
    (iprOmap {c} {mor} {cid} {comp} p) (iprOmap {c} {mor} {cid} {comp} q)
    (iprFmap {c} {mor} {cid} {comp} p) (iprFmap {c} {mor} {cid} {comp} q)
    (iprNT {c} {mor} {cid} {comp} {p} {q} m)
iprNatural {c} {mor} {cid} {comp} =
  icprNatural
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
IntPreshfIdNT : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p : IntPreshfObj {c} mor cid comp) ->
  IntQPreshfNTSig c
    (iprOmap {c} {mor} {cid} {comp} p)
    (iprOmap {c} {mor} {cid} {comp} p)
IntPreshfIdNT {c} {mor} {cid} {comp} =
  IntCopreshfIdNT
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
0 IntPreshfIdNatural : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p : IntPreshfObj {c} mor cid comp) ->
  IntQPreshfNTNaturality c mor
    (iprOmap {c} {mor} {cid} {comp} p) (iprOmap {c} {mor} {cid} {comp} p)
    (iprFmap {c} {mor} {cid} {comp} p) (iprFmap {c} {mor} {cid} {comp} p)
    (IntPreshfIdNT {c} {mor} {cid} {comp} p)
IntPreshfIdNatural {c} {mor} {cid} {comp} =
  IntCopreshfIdNatural
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
IntPreshfId : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntIdSig
    (IntPreshfObj {c} mor cid comp)
    (IntPreshfMor {c} {mor} {cid} {comp})
IntPreshfId {c} {mor} {cid} {comp} =
  IntCopreshfId
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
IntPreshfCompNT : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p, q, r : IntPreshfObj {c} mor cid comp) ->
  IntPreshfMor {c} {mor} {cid} {comp} q r ->
  IntPreshfMor {c} {mor} {cid} {comp} p q ->
  IntQPreshfNTSig c
    (iprOmap {c} {mor} {cid} {comp} p)
    (iprOmap {c} {mor} {cid} {comp} r)
IntPreshfCompNT {c} {mor} {cid} {comp} =
  IntCopreshfCompNT
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
0 IntPreshfCompNatural : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  (p, q, r : IntPreshfObj {c} mor cid comp) ->
  (m' : IntPreshfMor {c} {mor} {cid} {comp} q r) ->
  (m : IntPreshfMor {c} {mor} {cid} {comp} p q) ->
  IntQPreshfNTNaturality c mor
    (iprOmap {c} {mor} {cid} {comp} p) (iprOmap {c} {mor} {cid} {comp} r)
    (iprFmap {c} {mor} {cid} {comp} p) (iprFmap {c} {mor} {cid} {comp} r)
    (IntPreshfCompNT {c} {mor} {cid} {comp} p q r m' m)
IntPreshfCompNatural {c} {mor} {cid} {comp} =
  IntCopreshfCompNatural
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
IntPreshfComp : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntCompSig
    (IntPreshfObj {c} mor cid comp)
    (IntPreshfMor {c} {mor} {cid} {comp})
IntPreshfComp {c} {mor} {cid} {comp} =
  IntCopreshfComp
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
IntPreshfCat : {c : Type} -> (mor : IntMorSig c) ->
  IntIdSig c mor -> IntCompSig c mor -> IntCatSig
IntPreshfCat {c} mor cid comp =
  IntCopreshfCat
    {c=(IntOpCatObj c)}
    (IntOpCatMor c mor)
    (IntOpCatId c mor cid)
    (IntOpCatComp c mor comp)

------------------------------------------
---- Covariant categories of elements ----
------------------------------------------

public export
CopreSigCatElemObj : {c : Type} -> IntQCopreshfSig c -> Type
CopreSigCatElemObj {c} p = Sigma {a=c} (QBase . p)

public export
CopreCatElemObj : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntCopreshfObj {c} mor cid comp -> Type
CopreCatElemObj {c} {mor} {cid} {comp} = CopreSigCatElemObj {c} . icprOmap

public export
0 CopreCatElemEq : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntCopreshfObj {c} mor cid comp} ->
  (dom, cod : CopreCatElemObj {c} p) ->
  mor (fst dom) (fst cod) -> Type
CopreCatElemEq {c} {mor} {cid} {comp} {p} dom cod m =
  QBaseRel (icprOmap p $ fst cod)
    (QMorphBase {x=(icprOmap p $ fst dom)} {y=(icprOmap p $ fst cod)}
      (icprFmap p (fst dom) (fst cod) m) (snd dom),
     snd cod)

public export
record CopreCatElemMor {c : Type}
    {mor : IntMorSig c} {cid : IntIdSig c mor} {comp : IntCompSig c mor}
    {p : IntCopreshfObj {c} mor cid comp} (dom, cod : CopreCatElemObj {c} p)
    where
  constructor CElMor
  cemMor : mor (fst dom) (fst cod)
  0 cemEq : CopreCatElemEq {c} {mor} {cid} {comp} {p} dom cod cemMor

public export
CElMorC : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntCopreshfObj {c} mor cid comp} ->
  {x : c} -> (ex : QBase $ icprOmap p x) -> {y : c} -> (mxy : mor x y) ->
  CopreCatElemMor {c} {p}
    (x ** ex)
    (y **
     QMorphBase {x=(icprOmap p x)} {y=(icprOmap p y)} (icprFmap p x y mxy) ex)
CElMorC {c} {mor} {cid} {comp} {p} {x} ex {y} mxy =
  CElMor mxy $
    PrEquivRefl (QRel $ icprOmap p y) (QMorphBase (icprFmap p x y mxy) ex)

public export
CopreCatElemId : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntCopreshfObj {c} mor cid comp} ->
  IntIdSig (CopreCatElemObj {c} {mor} p) (CopreCatElemMor {c} {mor} {p})
CopreCatElemId {c} {mor} {cid} {comp} {p} ex =
  CElMor (cid $ fst ex)
  $ icprFid p (fst ex) (snd ex) (snd ex)
  $ PrEquivRefl (QRel $ icprOmap p (fst ex)) (snd ex)

public export
CopreCatElemCompMor : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntCopreshfObj {c} mor cid comp} ->
  (x, y, z : CopreCatElemObj {c} {mor} p) ->
  CopreCatElemMor {c} {mor} {p} y z ->
  CopreCatElemMor {c} {mor} {p} x y ->
  mor (fst x) (fst z)
CopreCatElemCompMor {c} {mor} {cid} {comp} {p} x y z myz mxy =
  comp (fst x) (fst y) (fst z) (cemMor myz) (cemMor mxy)

public export
0 CopreCatElemCompEq : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntCopreshfObj {c} mor cid comp} ->
  (x, y, z : CopreCatElemObj {c} {mor} p) ->
  (myz : CopreCatElemMor {c} {mor} {p} y z) ->
  (mxy : CopreCatElemMor {c} {mor} {p} x y) ->
  CopreCatElemEq {c} {mor} {cid} {comp} {p} x z
    $ CopreCatElemCompMor {p} x y z myz mxy
CopreCatElemCompEq {c} {mor} {cid} {comp} {p} x y z myz mxy =
  QRtrans
    (cemEq myz)
  $ QRtrans
    (QMorphPres
      (icprFmap p (fst y) (fst z) (cemMor myz))
      (QMorphBase (icprFmap p (fst x) (fst y) (cemMor mxy)) (snd x))
      (snd y)
      (cemEq mxy))
  $ QRsym
    (icprFcomp p (fst x) (fst y) (fst z) (cemMor myz) (cemMor mxy)
      (snd x) (snd x) QRrefl)

public export
CopreCatElemComp : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntCopreshfObj {c} mor cid comp} ->
  IntCompSig (CopreCatElemObj {c} {mor} p) (CopreCatElemMor {c} {mor} {p})
CopreCatElemComp {c} {mor} {cid} {comp} {p} x y z myz mxy =
  CElMor
    (CopreCatElemCompMor {c} {mor} {cid} {comp} {p} x y z myz mxy)
    (CopreCatElemCompEq {c} {mor} {cid} {comp} {p} x y z myz mxy)

public export
IntCopreCatElem : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntCopreshfObj {c} mor cid comp -> IntCatSig
IntCopreCatElem {c} {mor} {cid} {comp} p =
  ICat
    (CopreCatElemObj {c} {mor} p)
  $ MICS
    (CopreCatElemMor {c} {mor} {p})
  $ ICS
    (CopreCatElemId {c} {mor} {cid} {comp} {p})
    (CopreCatElemComp {c} {mor} {cid} {comp} {p})

----------------------------------------------
---- Contravariant categories of elements ----
----------------------------------------------

public export
PreSigCatElemObj : {c : Type} -> IntQPreshfSig c -> Type
PreSigCatElemObj {c} = CopreSigCatElemObj {c=(IntOpCatObj c)}

public export
PreCatElemObj : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntPreshfObj {c} mor cid comp -> Type
PreCatElemObj {c} {mor} {cid} {comp} =
  CopreCatElemObj
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
0 PreCatElemEq : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  (dom, cod : PreCatElemObj {c} {mor} {cid} {comp} p) ->
  mor (fst dom) (fst cod) -> Type
PreCatElemEq {c} {mor} {cid} {comp} dom cod =
  CopreCatElemEq
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}
    cod
    dom

public export
PreCatElemMor : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  (dom, cod : PreCatElemObj {c} {mor} {cid} {comp} p) -> Type
PreCatElemMor {c} {mor} {cid} {comp} {p} =
  flip $ CopreCatElemMor
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}
    {p}

public export
PElMor : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  {dom, cod : PreCatElemObj {c} {mor} {cid} {comp} p} ->
  (f : mor (fst dom) (fst cod)) ->
  (0 _ : PreCatElemEq {c} {mor} {cid} {comp} {p} dom cod f) ->
  PreCatElemMor {c} {mor} {cid} {comp} {p} dom cod
PElMor {c} {mor} {cid} {comp} {p} {dom} {cod} =
  CElMor
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}
    {p}
    {cod=dom}
    {dom=cod}

public export
pemMor : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  {dom, cod : PreCatElemObj {c} {mor} {cid} {comp} p} ->
  PreCatElemMor {c} {mor} {cid} {comp} {p} dom cod ->
  mor (fst dom) (fst cod)
pemMor {c} {mor} {cid} {comp} {p} {dom} {cod} =
  cemMor
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}
    {p}

public export
0 pemEq : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  {dom, cod : PreCatElemObj {c} {mor} {cid} {comp} p} ->
  (f : PreCatElemMor {c} {mor} {cid} {comp} {p} dom cod) ->
  PreCatElemEq {c} {mor} {cid} {comp} {p} dom cod
    (pemMor {c} {mor} {cid} {comp} {p} {dom} {cod} f)
pemEq {c} {mor} {cid} {comp} {p} {dom} {cod} =
  cemEq
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}
    {p}

public export
PElMorC : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  {y : c} -> (ey : QBase $ iprOmap {c} {cid} {mor} {comp} p y) ->
  {x : c} -> (mxy : mor x y) ->
  PreCatElemMor {c} {mor} {cid} {comp} {p}
    (x **
     QMorphBase {x=(icprOmap p y)} {y=(icprOmap p x)}
      (iprFmap {c} {cid} {mor} {comp} p y x mxy) ey)
    (y ** ey)
PElMorC {c} {mor} {cid} {comp} =
  CElMorC
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
PreCatElemId : {c : Type} ->
  {mor : IntMorSig c} -> {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  IntIdSig
    (PreCatElemObj {c} {mor} {cid} {comp} p)
    (PreCatElemMor {c} {mor} {cid} {comp} {p})
PreCatElemId {c} {mor} {cid} {comp} =
  CopreCatElemId
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
PreCatElemCompMor : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  (x, y, z : PreCatElemObj {c} {mor} {cid} {comp} p) ->
  PreCatElemMor {c} {mor} {cid} {comp} {p} y z ->
  PreCatElemMor {c} {mor} {cid} {comp} {p} x y ->
  mor (fst x) (fst z)
PreCatElemCompMor {c} {mor} {cid} {comp} {p} {x} {y} {z} =
  flip $ CopreCatElemCompMor
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}
    {x=z}
    {y}
    {z=x}

public export
0 PreCatElemCompEq : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  (x, y, z : PreCatElemObj {c} {mor} {cid} {comp} p) ->
  (myz : PreCatElemMor {c} {mor} {cid} {comp} {p} z y) ->
  (mxy : PreCatElemMor {c} {mor} {cid} {comp} {p} y x) ->
  PreCatElemEq {c} {mor} {cid} {comp} {p} z x
    $ PreCatElemCompMor {c} {mor} {cid} {comp} {p} z y x mxy myz
PreCatElemCompEq {c} {mor} {cid} {comp} {p} =
  CopreCatElemCompEq
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

public export
PreCatElemComp : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  {p : IntPreshfObj {c} mor cid comp} ->
  IntCompSig
    (PreCatElemObj {c} {mor} {cid} {comp} p)
    (PreCatElemMor {c} {mor} {cid} {comp} {p})
PreCatElemComp {c} {mor} {cid} {comp} {p} x y z =
   flip $ CopreCatElemComp
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}
    z y x

public export
IntPreCatElem : {c : Type} -> {mor : IntMorSig c} ->
  {cid : IntIdSig c mor} -> {comp : IntCompSig c mor} ->
  IntPreshfObj {c} mor cid comp -> IntCatSig
IntPreCatElem {c} {mor} {cid} {comp} =
  IntCopreCatElem
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {cid=(IntOpCatId c mor cid)}
    {comp=(IntOpCatComp c mor comp)}

----------------------------------------
----------------------------------------
---- Hom-profunctor as (co)presheaf ----
----------------------------------------
----------------------------------------

public export
IntHomProfOmap : {c : Type} -> (mor : IntMorSig c) ->
  IntQCopreshfSig (IntEndoOpProdCatObj c)
IntHomProfOmap {c} mor ecp = QTypeFromType $ uncurry mor ecp

public export
IntHomProfFmap : {c : Type} -> {mor : IntMorSig c} -> IntCompSig c mor ->
  IntQCopreshfMapSig
    (IntEndoOpProdCatObj c)
    (IntEndoOpProdCatMor c mor)
    (IntHomProfOmap {c} mor)
IntHomProfFmap {c} {mor} comp (s, t) (a, b) (mas, mtb) =
  QMorphFromMorph $ \mst => comp a t b mtb $ comp a s t mst mas

public export
0 IntHomProfMapIdT : {c : Type} -> {mor : IntMorSig c} ->
  (cid : IntIdSig c mor) -> (comp : IntCompSig c mor) ->
  Type
IntHomProfMapIdT {c} {mor} cid comp =
  IntCopreshfMapId
    {c=(IntEndoOpProdCatObj c)}
    {mor=(IntEndoOpProdCatMor c mor)}
    (IntEndoOpProdCatId c mor cid)
    (IntHomProfFmap {c} {mor} comp)

public export
0 IntHomProfMapCompT : {c : Type} -> {mor : IntMorSig c} ->
  (cid : IntIdSig c mor) -> (comp : IntCompSig c mor) ->
  Type
IntHomProfMapCompT {c} {mor} cid comp =
  IntCopreshfMapComp
    {c=(IntEndoOpProdCatObj c)}
    {mor=(IntEndoOpProdCatMor c mor)}
    (IntEndoOpProdCatComp c mor comp)
    (IntHomProfFmap {c} {mor} comp)

public export
IntHomProfObj : {c : Type} -> {mor : IntMorSig c} ->
  (cid : IntIdSig c mor) -> (comp : IntCompSig c mor) ->
  IntHomProfMapIdT {c} {mor} cid comp ->
  IntHomProfMapCompT {c} {mor} cid comp ->
  IntCopreshfObj
    {c=(IntEndoOpProdCatObj c)}
    (IntEndoOpProdCatMor c mor)
    (IntEndoOpProdCatId c mor cid)
    (IntEndoOpProdCatComp c mor comp)
IntHomProfObj {c} {mor} cid comp =
  ICopre
    (IntHomProfOmap {c} mor)
    (IntHomProfFmap {c} {mor} comp)

--------------------------------
--------------------------------
---- Twisted-arrow category ----
--------------------------------
--------------------------------

-- The twisted-arrow category is the category of elements of the hom-profunctor.
public export
TwArrCat : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntCatSig
TwArrCat c mapId mapComp =
  IntCopreCatElem
    {c=(IntEndoOpProdCatObj $ icObj c)}
    {mor=(IntEndoOpProdCatMor (icObj c) (icMor c))}
    {cid=(IntEndoOpProdCatId (icObj c) (icMor c) (icId c))}
    {comp=(IntEndoOpProdCatComp (icObj c) (icMor c) (icComp c))}
  $ IntHomProfObj
    {c=(icObj c)}
    {mor=(icMor c)}
    (icId c)
    (icComp c)
    mapId
    mapComp

public export
TwArrObj : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  Type
TwArrObj c mapId mapComp = icObj $ TwArrCat c mapId mapComp

public export
TwArrMor : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntMorSig (TwArrObj c mapId mapComp)
TwArrMor c mapId mapComp = icMor $ TwArrCat c mapId mapComp

public export
TwArrId : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntIdSig (TwArrObj c mapId mapComp) (TwArrMor c mapId mapComp)
TwArrId c mapId mapComp = icId $ TwArrCat c mapId mapComp

public export
TwArrComp : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntCompSig (TwArrObj c mapId mapComp) (TwArrMor c mapId mapComp)
TwArrComp c mapId mapComp = icComp $ TwArrCat c mapId mapComp

------------------------
------------------------
---- Two-categories ----
------------------------
------------------------

public export
Int2MorphParamSig : (obj : Type) -> (mor : IntMorSig obj) -> IntMorSig obj
Int2MorphParamSig obj mor x y = (f, g : mor x y) -> Type

public export
Int2MorphSig : (obj : Type) -> (mor : IntMorSig obj) -> Type
Int2MorphSig obj mor = (x, y : obj) -> Int2MorphParamSig obj mor x y

public export
Int2IdParamSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (x, y : obj) -> (_ : Int2MorphParamSig obj mor x y) -> Type
Int2IdParamSig {obj} {mor} x y mor2 = (f : mor x y) -> mor2 f f

public export
Int2IdSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (_ : Int2MorphSig obj mor) -> Type
Int2IdSig {obj} {mor} mor2 =
  (x, y : obj) -> Int2IdParamSig {obj} {mor} x y (mor2 x y)

public export
Int2VCompParamSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (x, y : obj) ->
  (mor2 : Int2MorphParamSig obj mor x y) -> Type
Int2VCompParamSig {obj} {mor} x y mor2 =
  (f, g, h : mor x y) -> mor2 g h -> mor2 f g -> mor2 f h

public export
Int2VCompSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (mor2 : Int2MorphSig obj mor) -> Type
Int2VCompSig {obj} {mor} mor2 =
  (x, y : obj) -> Int2VCompParamSig {obj} {mor} x y (mor2 x y)

public export
Int2WhiskerLParamSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (comp : IntCompSig obj mor) -> (mor2 : Int2MorphSig obj mor) ->
  (x, y : obj) -> mor x y -> Type
Int2WhiskerLParamSig {obj} {mor} comp mor2 x y f =
  (z : obj) -> (g, g' : mor y z) ->
  mor2 y z g g' -> mor2 x z (comp x y z g f) (comp x y z g' f)

public export
Int2WhiskerLSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (comp : IntCompSig obj mor) -> (mor2 : Int2MorphSig obj mor) ->
  Type
Int2WhiskerLSig {obj} {mor} comp mor2 =
  (x, y : obj) -> (f : mor x y) ->
  Int2WhiskerLParamSig {obj} {mor} comp mor2 x y f

public export
Int2WhiskerRParamSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (comp : IntCompSig obj mor) -> (mor2 : Int2MorphSig obj mor) ->
  (y, z : obj) -> mor y z -> Type
Int2WhiskerRParamSig {obj} {mor} comp mor2 y z g =
  (x : obj) -> (f, f' : mor x y) ->
  mor2 x y f f' -> mor2 x z (comp x y z g f) (comp x y z g f')

public export
Int2WhiskerRSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (comp : IntCompSig obj mor) -> (mor2 : Int2MorphSig obj mor) ->
  Type
Int2WhiskerRSig {obj} {mor} comp mor2 =
  (y, z : obj) -> (g : mor y z) ->
  Int2WhiskerRParamSig {obj} {mor} comp mor2 y z g

public export
Int2HCompParamSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (comp : IntCompSig obj mor) -> (mor2 : Int2MorphSig obj mor) ->
  IntMorSig obj
Int2HCompParamSig {obj} {mor} comp mor2 dom cod =
  (mid : obj) ->
  (f, f' : mor dom mid) -> (g, g' : mor mid cod) ->
  mor2 mid cod g g' -> mor2 dom mid f f' ->
  mor2 dom cod (comp dom mid cod g f) (comp dom mid cod g' f')

public export
Int2HCompSig : {obj : Type} -> {mor : IntMorSig obj} ->
  (comp : IntCompSig obj mor) -> (mor2 : Int2MorphSig obj mor) ->
  Type
Int2HCompSig {obj} {mor} comp mor2 =
  (dom, cod : obj) -> Int2HCompParamSig {obj} {mor} comp mor2 dom cod

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
i2c1Obj : (c2 : Int2CatSig) -> Type
i2c1Obj c2 = icObj $ i2c1 c2

public export
i2c1Mor : (c2 : Int2CatSig) -> (dom, cod : i2c1Obj c2) -> Type
i2c1Mor c2 = icMor $ i2c1 c2

public export
i2c1Id : (c2 : Int2CatSig) -> IntIdSig (i2c1Obj c2) (i2c1Mor c2)
i2c1Id c2 = icId $ i2c1 c2

public export
i2c1comp : (c2 : Int2CatSig) -> IntCompSig (i2c1Obj c2) (i2c1Mor c2)
i2c1comp c2 = icComp $ i2c1 c2

public export
i2c2Obj : (c2 : Int2CatSig) -> (dom, cod : i2c1Obj c2) -> Type
i2c2Obj c2 dom cod = i2c1Mor c2 dom cod

public export
i2c2Mor : (c2 : Int2CatSig) -> Int2MorphSig (i2c1Obj c2) (i2c1Mor c2)
i2c2Mor c2 x y f g = micsMor (i2Chs c2 x y) f g

public export
i2c2Id : (c2 : Int2CatSig) ->
  Int2IdSig {obj=(i2c1Obj c2)} {mor=(i2c1Mor c2)} (i2c2Mor c2)
i2c2Id c2 x y = micsId (i2Chs c2 x y)

public export
i2c2Vcomp : (c2 : Int2CatSig) ->
  Int2VCompSig {obj=(i2c1Obj c2)} {mor=(i2c1Mor c2)} (i2c2Mor c2)
i2c2Vcomp c2 x y f g = micsComp (i2Chs c2 x y) f g

-- For any pair of objects of the category underlying a 2-category, there
-- is a category of 2-morphisms among 1-morphisms between the two given objects.
public export
i2c1c : (c2 : Int2CatSig) -> (dom, cod : icObj (i2c1 c2)) -> IntCatSig
i2c1c c2 dom cod = ICat (i2c2Obj c2 dom cod) (i2Chs c2 dom cod)

public export
i2Cwp : (c2 : Int2CatSig) -> GlobalWhiskerPairHomStruct (i2c1 c2) (i2Chs c2)
i2Cwp c2 =
  MkGlobalWhiskerPairHomStruct (i2c1 c2) (i2Chs c2) (i2Cwl c2) (i2Cwr c2)

public export
i2c2Hcomp : (c2 : Int2CatSig) -> GlobalHcompHomStruct (i2c1 c2) (i2Chs c2)
i2c2Hcomp c2 = GlobalHcompFromWhiskers (i2c1 c2) (i2Chs c2) $ i2Cwp c2

public export
IntFunctorHCatSig : {idx : Type} -> (idx -> IntCatSig) -> IntCatSig
IntFunctorHCatSig {idx} cat =
  ICat
    idx
  $ MICS
    (\x, y => IntFunctorSig (cat x) (cat y))
  $ ICS
    (\x => IntFunctorSigId $ cat x)
    (\x, y, z => IntFunctorSigComp (cat x) (cat y) (cat z))

public export
IntFunctor2WhiskerLSig : {idx : Type} -> (cat : idx -> IntCatSig) ->
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
IntFunctor2WhiskerRSig : {idx : Type} -> (cat : idx -> IntCatSig) ->
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
IntFunctor2CatSig : {idx : Type} -> (idx -> IntCatSig) -> Int2CatSig
IntFunctor2CatSig {idx} cat =
  I2Cat
    (IntFunctorHCatSig {idx} cat)
  $ I2CS
    (\dom, cod => IntOmapCatSig (cat dom) (cat cod) ifOmap)
    (\c, d, e => FunctorCatWhiskerL (cat c) (cat d) (cat e))
    (\c, d, e => FunctorCatWhiskerR (cat c) (cat d) (cat e))

-- The category of all categories in particular is a two-category.
public export
IntCat2Cat : Int2CatSig
IntCat2Cat = IntFunctor2CatSig {idx=IntCatSig} id

public export
IntFunctor2HCompSig : {idx : Type} -> (cat : idx -> IntCatSig) ->
  Int2HCompSig
    {obj=(icObj $ IntFunctorHCatSig {idx} cat)}
    {mor=(icMor $ IntFunctorHCatSig {idx} cat)}
    (icComp $ IntFunctorHCatSig {idx} cat)
    (\c, d, f, g => IntNTSig (icMor $ cat d) (ifOmap f) (ifOmap g))
IntFunctor2HCompSig {idx} cat c d e f f' g g' beta alpha =
  (i2c2Hcomp $ IntFunctor2CatSig {idx} cat) c e d f f' g g' beta alpha

-----------------------------------
-----------------------------------
---- Metalanguage 2-categories ----
-----------------------------------
-----------------------------------

-----------------------------------------------
---- Metalanguage slice-functor categories ----
-----------------------------------------------

public export
SliceFuncCat : Type -> Type -> IntCatSig
SliceFuncCat x y = IntFunctorCatSig (SliceCat x) (SliceCat y)

public export
SliceFuncSig : Type -> Type -> Type
SliceFuncSig x y = icObj $ SliceFuncCat x y

public export
SliceNTSig : {x, y : Type} -> SliceFuncSig x y -> SliceFuncSig x y -> Type
SliceNTSig {x} {y} = icMor (SliceFuncCat x y)

public export
SliceFunc2Cat : Int2CatSig
SliceFunc2Cat = IntFunctor2CatSig {idx=Type} SliceCat

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
CIEFamPosMor : {c : IntCatSig} -> IntMorSig (CIEFamObj c)
CIEFamPosMor {c} i j = IntFunctorSig (caPos i) (caPos j)

public export
CIEFamObjMor : {c : IntCatSig} ->
  (dom, cod : CIEFamObj c) -> CIEFamPosMor {c} dom cod -> Type
CIEFamObjMor {c} dom cod onpos =
  IntNTSig {c=(icObj $ caPos dom)} {d=(icObj c)} (icMor c)
    (ifOmap $ caDir dom)
    (ifOmap $ IntFunctorSigComp (caPos dom) (caPos cod) c (caDir cod) onpos)

public export
CIEFamMor : {c : IntCatSig} -> IntMorSig (CIEFamObj c)
CIEFamMor {c} i j = DPair (CIEFamPosMor {c} i j) (CIEFamObjMor {c} i j)

public export
cieFamIdPos : {c : IntCatSig} -> (x : CIEFamObj c) -> CIEFamPosMor {c} x x
cieFamIdPos {c} x = IntFunctorSigId (caPos x)

public export
cieFamIdObj : {c : IntCatSig} ->
  (x : CIEFamObj c) -> CIEFamObjMor {c} x x (cieFamIdPos {c} x)
cieFamIdObj {c} x =
  intNTid {c=(icObj $ caPos x)} (icMor c) (icId c) (ifOmap $ caDir x)

public export
cieFamId : {c : IntCatSig} -> IntIdSig (CIEFamObj c) (CIEFamMor {c})
cieFamId {c} x = (cieFamIdPos {c} x ** cieFamIdObj {c} x)

public export
cieFamCompPos : {c : IntCatSig} -> (x, y, z : CIEFamObj c) ->
  CIEFamMor {c} y z -> CIEFamMor {c} x y -> CIEFamPosMor {c} x z
cieFamCompPos {c} x y z g f =
  IntFunctorSigComp (caPos x) (caPos y) (caPos z) (fst g) (fst f)

public export
cieFamCompObj : {c : IntCatSig} -> (x, y, z : CIEFamObj c) ->
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
cieFamComp : {c : IntCatSig} -> IntCompSig (CIEFamObj c) (CIEFamMor {c})
cieFamComp {c} x y z g f =
  (cieFamCompPos {c} x y z g f ** cieFamCompObj {c} x y z g f)

public export
CIEFamCat : IntCatSig -> IntCatSig
CIEFamCat c =
  ICat
    (CIEFamObj c)
  $ MICS
    (CIEFamMor {c})
  $ ICS
    (cieFamId {c})
    (cieFamComp {c})

-----------------------------------------------------------------------
---- Category-indexed existential cofamilies (polynomial functors) ----
-----------------------------------------------------------------------

public export
CIECofamObj : IntCatSig -> Type
CIECofamObj = CIEFamObj . IntOpCat

public export
CIECofamPosMor : {c : IntCatSig} -> IntMorSig (CIECofamObj c)
CIECofamPosMor {c} = CIEFamPosMor {c=(IntOpCat c)}

public export
CIECofamObjMor : {c : IntCatSig} ->
  (dom, cod : CIECofamObj c) -> CIECofamPosMor {c} dom cod -> Type
CIECofamObjMor {c} = CIEFamObjMor {c=(IntOpCat c)}

public export
CIECofamMor : {c : IntCatSig} -> IntMorSig (CIECofamObj c)
CIECofamMor {c} = CIEFamMor {c=(IntOpCat c)}

public export
cieCofamIdPos : {c : IntCatSig} ->
  (x : CIECofamObj c) -> CIECofamPosMor {c} x x
cieCofamIdPos {c} = cieFamIdPos {c=(IntOpCat c)}

public export
cieCofamIdObj : {c : IntCatSig} ->
  (x : CIECofamObj c) -> CIECofamObjMor {c} x x (cieCofamIdPos {c} x)
cieCofamIdObj {c} = cieFamIdObj {c=(IntOpCat c)}

public export
cieCofamId : {c : IntCatSig} -> IntIdSig (CIECofamObj c) (CIECofamMor {c})
cieCofamId {c} = cieFamId {c=(IntOpCat c)}

public export
cieCofamCompPos : {c : IntCatSig} -> (x, y, z : CIECofamObj c) ->
  CIECofamMor {c} y z -> CIECofamMor {c} x y -> CIECofamPosMor {c} x z
cieCofamCompPos {c} = cieFamCompPos {c=(IntOpCat c)}

public export
cieCofamCompObj : {c : IntCatSig} -> (x, y, z : CIECofamObj c) ->
  (g : CIECofamMor {c} y z) -> (f : CIECofamMor {c} x y) ->
  CIECofamObjMor {c} x z (cieCofamCompPos {c} x y z g f)
cieCofamCompObj {c} = cieFamCompObj {c=(IntOpCat c)}

public export
cieCofamComp : {c : IntCatSig} ->
  IntCompSig (CIECofamObj c) (CIECofamMor {c})
cieCofamComp {c} = cieFamComp {c=(IntOpCat c)}

public export
CIECofamCat : IntCatSig -> IntCatSig
CIECofamCat c =
  ICat
    (CIECofamObj c)
  $ MICS
    (CIECofamMor {c})
  $ ICS
    (cieCofamId {c})
    (cieCofamComp {c})

---------------------------------------------
---- Category-indexed universal families ----
---------------------------------------------

public export
CIUFamObj : IntCatSig -> Type
CIUFamObj = CIArena

public export
CIUFamPosMor : {c : IntCatSig} -> IntMorSig (CIUFamObj c)
CIUFamPosMor {c} = IntOpCatMor (CIEFamObj c) $ CIEFamPosMor {c}

public export
CIUFamObjMor : {c : IntCatSig} ->
  (dom, cod : CIUFamObj c) -> CIUFamPosMor {c} dom cod -> Type
CIUFamObjMor {c} dom cod onpos =
  IntOpNTSig {c=(icObj $ caPos cod)} {d=(icObj c)}
    (icMor c)
    (ifOmap $ caDir cod)
    (ifOmap $ IntFunctorSigComp (caPos cod) (caPos dom) c (caDir dom) onpos)

public export
CIUFamMor : {c : IntCatSig} -> IntMorSig (CIUFamObj c)
CIUFamMor {c} i j = DPair (CIUFamPosMor {c} i j) (CIUFamObjMor {c} i j)

public export
ciuFamIdPos : {c : IntCatSig} -> (x : CIUFamObj c) -> CIUFamPosMor {c} x x
ciuFamIdPos {c} x = IntFunctorSigId (caPos x)

public export
ciuFamIdObj : {c : IntCatSig} ->
  (x : CIUFamObj c) -> CIUFamObjMor {c} x x (ciuFamIdPos {c} x)
ciuFamIdObj {c} x =
  intNTid {c=(icObj $ caPos x)} (icMor c) (icId c) (ifOmap $ caDir x)

public export
ciuFamId : {c : IntCatSig} -> IntIdSig (CIUFamObj c) (CIUFamMor {c})
ciuFamId {c} x = (ciuFamIdPos {c} x ** ciuFamIdObj {c} x)

public export
ciuFamCompPos : {c : IntCatSig} -> (x, y, z : CIUFamObj c) ->
  CIUFamMor {c} y z -> CIUFamMor {c} x y -> CIUFamPosMor {c} x z
ciuFamCompPos {c} x y z g f =
  IntFunctorSigComp (caPos z) (caPos y) (caPos x) (fst f) (fst g)

public export
ciuFamCompObj : {c : IntCatSig} -> (x, y, z : CIUFamObj c) ->
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
ciuFamComp : {c : IntCatSig} -> IntCompSig (CIUFamObj c) (CIUFamMor {c})
ciuFamComp {c} x y z g f =
  (ciuFamCompPos {c} x y z g f ** ciuFamCompObj {c} x y z g f)

public export
CIUFamCat : IntCatSig -> IntCatSig
CIUFamCat c =
  ICat
    (CIUFamObj c)
  $ MICS
    (CIUFamMor {c})
  $ ICS
    (ciuFamId {c})
    (ciuFamComp {c})

-----------------------------------------------
---- Category-indexed universal cofamilies ----
-----------------------------------------------

public export
CIUCofamObj : IntCatSig -> Type
CIUCofamObj = CIUFamObj . IntOpCat

public export
CIUCofamPosMor : {c : IntCatSig} -> IntMorSig (CIUCofamObj c)
CIUCofamPosMor {c} = CIUFamPosMor {c=(IntOpCat c)}

public export
CIUCofamObjMor : {c : IntCatSig} ->
  (dom, cod : CIUCofamObj c) -> CIUCofamPosMor {c} dom cod -> Type
CIUCofamObjMor {c} = CIUFamObjMor {c=(IntOpCat c)}

public export
CIUCofamMor : {c : IntCatSig} -> IntMorSig (CIUCofamObj c)
CIUCofamMor {c} = CIUFamMor {c=(IntOpCat c)}

public export
ciuCofamIdPos : {c : IntCatSig} ->
  (x : CIUCofamObj c) -> CIUCofamPosMor {c} x x
ciuCofamIdPos {c} = ciuFamIdPos {c=(IntOpCat c)}

public export
ciuCofamIdObj : {c : IntCatSig} ->
  (x : CIUCofamObj c) -> CIUCofamObjMor {c} x x (ciuCofamIdPos {c} x)
ciuCofamIdObj {c} = ciuFamIdObj {c=(IntOpCat c)}

public export
ciuCofamId : {c : IntCatSig} -> IntIdSig (CIUCofamObj c) (CIUCofamMor {c})
ciuCofamId {c} = ciuFamId {c=(IntOpCat c)}

public export
ciuCofamCompPos : {c : IntCatSig} -> (x, y, z : CIUCofamObj c) ->
  CIUCofamMor {c} y z -> CIUCofamMor {c} x y -> CIUCofamPosMor {c} x z
ciuCofamCompPos {c} = ciuFamCompPos {c=(IntOpCat c)}

public export
ciuCofamCompObj : {c : IntCatSig} -> (x, y, z : CIUCofamObj c) ->
  (g : CIUCofamMor {c} y z) -> (f : CIUCofamMor {c} x y) ->
  CIUCofamObjMor {c} x z (ciuCofamCompPos {c} x y z g f)
ciuCofamCompObj {c} = ciuFamCompObj {c=(IntOpCat c)}

public export
ciuCofamComp : {c : IntCatSig} ->
  IntCompSig (CIUCofamObj c) (CIUCofamMor {c})
ciuCofamComp {c} = ciuFamComp {c=(IntOpCat c)}

public export
CIUCofamCat : IntCatSig -> IntCatSig
CIUCofamCat c =
  ICat
    (CIUCofamObj c)
  $ MICS
    (CIUCofamMor {c})
  $ ICS
    (ciuCofamId {c})
    (ciuCofamComp {c})

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
IntUnitSig : {c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntUnitSig {c} cmor t = IntNTSig {c} {d=c} cmor id t

public export
intIdMonadUnit : {c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntUnitSig {c} cmor (IntIdFunctor c)
intIdMonadUnit {c} cmor cid = cid

public export
IntCounitSig : {c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntCounitSig {c} cmor t = IntNTSig {c} {d=c} cmor t id

public export
intIdComonadCounit : {c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntCounitSig {c} cmor (IntIdFunctor c)
intIdComonadCounit {c} cmor cid = cid

public export
IntMultSig : {c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntMultSig {c} cmor t =
  IntNTSig {c} {d=c} cmor (IntFunctorComp c c c t t) t

public export
intIdMonadMult : {c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntMultSig {c} cmor (IntIdFunctor c)
intIdMonadMult {c} cmor cid = cid

public export
IntComultSig : {c : Type} -> (cmor : IntMorSig c) -> (t : c -> c) -> Type
IntComultSig {c} cmor t =
  IntNTSig {c} {d=c} cmor t (IntFunctorComp c c c t t)

public export
intIdComonadComult : {c : Type} ->
  (cmor : IntMorSig c) -> (cid : IntIdSig c cmor) ->
  IntComultSig {c} cmor (IntIdFunctor c)
intIdComonadComult {c} cmor cid = cid

---------------------
---------------------
---- Adjunctions ----
---------------------
---------------------

public export
IntAdjLMapSig : {c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (l : c -> d) -> Type
IntAdjLMapSig {c} {d} cmor dmor = IntFMapSig {c} {d} cmor dmor

public export
IntAdjRMapSig : {c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (r : d -> c) -> Type
IntAdjRMapSig {c} {d} cmor dmor = IntFMapSig {c=d} {d=c} dmor cmor

public export
IntAdjLAdjunctSig : {c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjLAdjunctSig {c} {d} cmor dmor l r =
  (a : c) -> (b : d) -> dmor (l a) b -> cmor a (r b)

public export
IntAdjRAdjunctSig : {c, d : Type} ->
  IntMorSig c -> IntMorSig d ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjRAdjunctSig {c} {d} cmor dmor l r =
  (a : c) -> (b : d) -> cmor a (r b) -> dmor (l a) b

public export
IntAdjMonad : {c, d : Type} -> (l : c -> d) -> (r : d -> c) -> c -> c
IntAdjMonad {c} {d} l r = IntFunctorComp c d c r l

public export
IntAdjMonadSig : {c, d : Type} -> (cmor : IntMorSig c) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjMonadSig {c} {d} cmor l r =
  IntEndoFMapSig {c} cmor (IntAdjMonad {c} {d} l r)

public export
IntAdjMonadMap : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjLMapSig {c} {d} cmor dmor l ->
  IntAdjRMapSig {c} {d} cmor dmor r ->
  IntAdjMonadSig {c} {d} cmor l r
IntAdjMonadMap {c} {d} cmor dmor l r =
  flip $ intFmapComp {c} {d} {e=c} {cmor} {dmor} {emor=cmor} {g=r} {f=l}

public export
IntAdjComonad : {c, d : Type} -> (l : c -> d) -> (r : d -> c) -> d -> d
IntAdjComonad {c} {d} l r = IntFunctorComp d c d l r

public export
IntAdjComonadSig : {c, d : Type} -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjComonadSig {c} {d} dmor l r =
  IntEndoFMapSig {c=d} dmor (IntAdjComonad {c} {d} l r)

public export
IntAdjComonadMap : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjLMapSig {c} {d} cmor dmor l ->
  IntAdjRMapSig {c} {d} cmor dmor r ->
  IntAdjComonadSig {c} {d} dmor l r
IntAdjComonadMap {c} {d} cmor dmor l r =
  intFmapComp {c=d} {d=c} {e=d} {cmor=dmor} {dmor=cmor} {emor=dmor} {g=l} {f=r}

public export
IntAdjUnitSig : {c, d : Type} -> (cmor : IntMorSig c) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjUnitSig {c} {d} cmor l r =
  IntUnitSig cmor (IntAdjMonad {c} {d} l r)

public export
IntAdjCounitSig : {c, d : Type} -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjCounitSig {c} {d} dmor l r =
  IntCounitSig {c=d} dmor (IntAdjComonad {c} {d} l r)

public export
IntAdjMultSig : {c, d : Type} -> (cmor : IntMorSig c) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjMultSig {c} {d} cmor l r =
  IntMultSig cmor (IntAdjMonad {c} {d} l r)

public export
IntAdjComultSig : {c, d : Type} -> (dmor : IntMorSig d) ->
  (l : c -> d) -> (r : d -> c) -> Type
IntAdjComultSig {c} {d} dmor l r =
  IntComultSig {c=d} dmor (IntAdjComonad {c} {d} l r)

public export
IntAdjLAdjunctFromRMapAndUnit : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (ccomp : IntCompSig c cmor) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjRMapSig {c} {d} cmor dmor r ->
  IntAdjUnitSig {c} {d} cmor l r ->
  IntAdjLAdjunctSig {c} {d} cmor dmor l r
IntAdjLAdjunctFromRMapAndUnit cmor dmor ccomp l r rm unit a b mdlab =
  ccomp a (r (l a)) (r b) (rm (l a) b mdlab) (unit a)

public export
IntAdjRAdjunctFromLMapAndCounit : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (dcomp : IntCompSig d dmor) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjLMapSig {c} {d} cmor dmor l ->
  IntAdjCounitSig {c} {d} dmor l r ->
  IntAdjRAdjunctSig {c} {d} cmor dmor l r
IntAdjRAdjunctFromLMapAndCounit cmor dmor dcomp l r lm counit a b mcrab =
  dcomp (l a) (l (r b)) b (counit b) (lm a (r b) mcrab)

public export
IntAdjLMapFromRAdjunctAndUnit : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (ccomp : IntCompSig c cmor) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjRAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjUnitSig {c} {d} cmor l r ->
  IntAdjLMapSig {c} {d} cmor dmor l
IntAdjLMapFromRAdjunctAndUnit cmor dmor ccomp l r radj unit x y cmxy =
  radj x (l y) $ ccomp x y (r (l y)) (unit y) cmxy

public export
IntAdjRMapFromLAdjunctAndCounit : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (dcomp : IntCompSig d dmor) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjLAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjCounitSig {c} {d} dmor l r ->
  IntAdjRMapSig {c} {d} cmor dmor r
IntAdjRMapFromLAdjunctAndCounit cmor dmor dcomp l r ladj counit x y dmxy =
  ladj (r x) y $ dcomp (l (r x)) x y dmxy (counit x)

public export
IntAdjUnitFromLAdjunct : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (did : IntIdSig d dmor) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjLAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjUnitSig {c} {d} cmor l r
IntAdjUnitFromLAdjunct {c} {d} cmor dmor did l r ladj a =
  ladj a (l a) (did $ l a)

public export
IntAdjCounitFromRAdjunct : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (cid : IntIdSig c cmor) ->
  (l : c -> d) -> (r : d -> c) ->
  IntAdjRAdjunctSig {c} {d} cmor dmor l r ->
  IntAdjCounitSig {c} {d} dmor l r
IntAdjCounitFromRAdjunct {c} {d} cmor dmor cid l r radj b =
  radj (r b) b (cid $ r b)

public export
IntAdjMultFromCounit : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (did : IntIdSig d dmor) ->
  (l : c -> d) -> (r : d -> c) ->
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
IntAdjComultFromUnit : {c, d : Type} ->
  (cmor : IntMorSig c) -> (dmor : IntMorSig d) ->
  (cid : IntIdSig c cmor) ->
  (l : c -> d) -> (r : d -> c) ->
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
iaLOmap : {c, d : IntCatSig} -> IntAdjointsSig c d -> icObj c -> icObj d
iaLOmap = ifOmap . iaL

public export
iaLFmap : {c, d : IntCatSig} -> (adjs : IntAdjointsSig c d) ->
  IntFMapSig (icMor c) (icMor d) (iaLOmap adjs)
iaLFmap adjs = ifMmap $ iaL adjs

public export
iaROmap : {c, d : IntCatSig} -> IntAdjointsSig c d -> icObj d -> icObj c
iaROmap = ifOmap . iaR

public export
iaRFmap : {c, d : IntCatSig} -> (adjs : IntAdjointsSig c d) ->
  IntFMapSig (icMor d) (icMor c) (iaROmap adjs)
iaRFmap adjs = ifMmap $ iaR adjs

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
iadLAdj : {c, d : IntCatSig} -> {adjs : IntAdjointsSig c d} ->
  IntAdjunctionData {c} {d} adjs ->
  IntAdjLAdjunctSig (icMor c) (icMor d) (iaLOmap adjs) (iaROmap adjs)
iadLAdj = iaLAdj . iadAdjuncts

public export
iadRAdj : {c, d : IntCatSig} -> {adjs : IntAdjointsSig c d} ->
  IntAdjunctionData {c} {d} adjs ->
  IntAdjRAdjunctSig (icMor c) (icMor d) (iaLOmap adjs) (iaROmap adjs)
iadRAdj = iaRAdj . iadAdjuncts

public export
iadUnit : {c, d : IntCatSig} -> {adjs : IntAdjointsSig c d} ->
  IntAdjunctionData {c} {d} adjs ->
  IntAdjUnitSig (icMor c) (iaLOmap adjs) (iaROmap adjs)
iadUnit = iuUnit . iadUnits

public export
iadCounit : {c, d : IntCatSig} -> {adjs : IntAdjointsSig c d} ->
  IntAdjunctionData {c} {d} adjs ->
  IntAdjCounitSig (icMor d) (iaLOmap adjs) (iaROmap adjs)
iadCounit = iuCounit . iadUnits

public export
iadMult : {c, d : IntCatSig} -> {adjs : IntAdjointsSig c d} ->
  IntAdjunctionData {c} {d} adjs ->
  IntAdjMultSig (icMor c) (iaLOmap adjs) (iaROmap adjs)
iadMult = imMult . iadMults

public export
iadComult : {c, d : IntCatSig} -> {adjs : IntAdjointsSig c d} ->
  IntAdjunctionData {c} {d} adjs ->
  IntAdjComultSig (icMor d) (iaLOmap adjs) (iaROmap adjs)
iadComult = imComult . iadMults

public export
record IntAdjunctionSig (c, d : IntCatSig) where
  constructor IAdjunction
  iaAdjoints : IntAdjointsSig c d
  iaData : IntAdjunctionData {c} {d} iaAdjoints

public export
iasL : {c, d : IntCatSig} -> IntAdjunctionSig c d -> IntFunctorSig c d
iasL = iaL . iaAdjoints

public export
iasLOmap : {c, d : IntCatSig} -> IntAdjunctionSig c d -> icObj c -> icObj d
iasLOmap = ifOmap . iasL

public export
iasR : {c, d : IntCatSig} -> IntAdjunctionSig c d -> IntFunctorSig d c
iasR = iaR . iaAdjoints

public export
iasROmap : {c, d : IntCatSig} -> IntAdjunctionSig c d -> icObj d -> icObj c
iasROmap = ifOmap . iasR

public export
iasLAdj : {c, d : IntCatSig} ->
  (adj : IntAdjunctionSig c d) ->
  IntAdjLAdjunctSig (icMor c) (icMor d) (iasLOmap adj) (iasROmap adj)
iasLAdj adj = iadLAdj $ iaData adj

public export
iasRAdj : {c, d : IntCatSig} ->
  (adj : IntAdjunctionSig c d) ->
  IntAdjRAdjunctSig (icMor c) (icMor d) (iasLOmap adj) (iasROmap adj)
iasRAdj adj = iadRAdj $ iaData adj

public export
iasUnit : {c, d : IntCatSig} ->
  (adj : IntAdjunctionSig c d) ->
  IntAdjUnitSig (icMor c) (iasLOmap adj) (iasROmap adj)
iasUnit adj = iadUnit $ iaData adj

public export
iasCounit : {c, d : IntCatSig} ->
  (adj : IntAdjunctionSig c d) ->
  IntAdjCounitSig (icMor d) (iasLOmap adj) (iasROmap adj)
iasCounit adj = iadCounit $ iaData adj

public export
iasMult : {c, d : IntCatSig} ->
  (adj : IntAdjunctionSig c d) ->
  IntAdjMultSig (icMor c) (iasLOmap adj) (iasROmap adj)
iasMult adj = iadMult $ iaData adj

public export
iasComult : {c, d : IntCatSig} ->
  (adj : IntAdjunctionSig c d) ->
  IntAdjComultSig (icMor d) (iasLOmap adj) (iasROmap adj)
iasComult adj = iadComult $ iaData adj

public export
IntAdjunctsFromUnits : {c, d : IntCatSig} -> (adjs : IntAdjointsSig c d) ->
  (units : IntUnitsSig adjs) -> IntAdjunctsSig adjs
IntAdjunctsFromUnits {c} {d} adjs units =
  IAdjuncts
    (IntAdjLAdjunctFromRMapAndUnit (icMor c) (icMor d) (icComp c)
      (iaLOmap adjs) (iaROmap adjs) (iaRFmap adjs) (iuUnit units))
    (IntAdjRAdjunctFromLMapAndCounit (icMor c) (icMor d) (icComp d)
      (iaLOmap adjs) (iaROmap adjs) (iaLFmap adjs) (iuCounit units))

public export
IntMultsFromUnits : {c, d : IntCatSig} -> (adjs : IntAdjointsSig c d) ->
  (units : IntUnitsSig adjs) -> IntMultsSig adjs
IntMultsFromUnits {c} {d} adjs units =
  IMults
    (IntAdjMultFromCounit (icMor c) (icMor d) (icId d) (iaLOmap adjs)
      (iaROmap adjs) (iaRFmap adjs) (iuCounit units))
    (IntAdjComultFromUnit (icMor c) (icMor d) (icId c) (iaLOmap adjs)
      (iaROmap adjs) (iaLFmap adjs) (iuUnit units))

public export
IntAdjunctionDataFromUnits : {c, d : IntCatSig} ->
  (adjs : IntAdjointsSig c d) -> IntUnitsSig adjs ->
  IntAdjunctionData adjs
IntAdjunctionDataFromUnits {c} {d} adjs units =
  IAdjData
    (IntAdjunctsFromUnits adjs units)
    units
    (IntMultsFromUnits adjs units)

public export
IntAdjunctionFromUnits : {c, d : IntCatSig} ->
  (adjs : IntAdjointsSig c d) -> IntUnitsSig adjs ->
  IntAdjunctionSig c d
IntAdjunctionFromUnits {c} {d} adjs units =
  IAdjunction adjs (IntAdjunctionDataFromUnits adjs units)
