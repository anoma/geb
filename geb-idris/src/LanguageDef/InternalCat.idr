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

-- By itself, imposing a global hom-set structure on a category only
-- defines a collection of non-interacting categories which happen to
-- be indexed by pairs of objects of some other category, and each
-- of whose morphisms happens to correspond to a morphism of that
-- indexing category.
--
-- Adding distinctiveness (from simply collections of categories)
-- to hom-set structures involves defining interactions among them
-- which correspond in some way to the structure of the indexing category.
-- So we now define some such interactions.

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

----------------------------------
----------------------------------
---- Parameterized categories ----
----------------------------------
----------------------------------

-- A category parameterized over a category is a functor from that category
-- (which we call the "index" category) to the category of categories.  To
-- be explicit, this means that to each object of the index category we assign
-- a category, and to each morphism of the index category we assign a functor.
public export
IntParamCat : IntCatSig -> Type
IntParamCat cat = IntFunctorSig cat IntCatCat

---------------------------------
---------------------------------
---- Natural transformations ----
---------------------------------
---------------------------------

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

public export
0 Int2HCompFromWhiskers : {0 obj : Type} -> {0 mor : IntMorSig obj} ->
  (0 hcomp : IntCompSig obj mor) -> (0 mor2 : Int2MorphSig obj mor) ->
  Int2WhiskerLSig {obj} {mor} hcomp mor2 ->
  Int2WhiskerRSig {obj} {mor} hcomp mor2 ->
  Int2VCompSig {obj} {mor} mor2 ->
  Int2HCompSig {obj} {mor} hcomp mor2
Int2HCompFromWhiskers {obj} {mor} hcomp mor2 wl wr vcomp dom cod mid f f' g g'
  beta alpha =
    vcomp
      dom cod
      (hcomp dom mid cod g f)
      (hcomp dom mid cod g f')
      (hcomp dom mid cod g' f')
      (wl dom mid f' cod g g' beta)
      (wr mid cod g dom f f' alpha)

public export
record Int2CatSig where
  constructor I2Cat
  i2Ch : IntCatSig
  i2Cv : (0 dom, cod : icObj i2Ch) -> MorIdCompSig (icMor i2Ch dom cod)
  0 i2Cwl :
    Int2WhiskerLSig {obj=(icObj i2Ch)} {mor=(icMor i2Ch)}
      (icComp i2Ch) (\x, y, f, g => micsMor (i2Cv x y) f g)
  0 i2Cwr :
    Int2WhiskerRSig {obj=(icObj i2Ch)} {mor=(icMor i2Ch)}
      (icComp i2Ch) (\x, y, f, g => micsMor (i2Cv x y) f g)

public export
0 i2ChObj : (0 c2 : Int2CatSig) -> Type
i2ChObj c2 = icObj $ i2Ch c2

public export
0 i2ChMor : (0 c2 : Int2CatSig) -> (dom, cod : i2ChObj c2) -> Type
i2ChMor c2 = icMor $ i2Ch c2

public export
0 i2C1Id : (0 c2 : Int2CatSig) -> IntIdSig (i2ChObj c2) (i2ChMor c2)
i2C1Id c2 = icId $ i2Ch c2

public export
0 i2C1Comp : (0 c2 : Int2CatSig) -> IntCompSig (i2ChObj c2) (i2ChMor c2)
i2C1Comp c2 = icComp $ i2Ch c2

public export
0 i2CvObj : (0 c2 : Int2CatSig) -> (0 dom, cod : i2ChObj c2) -> Type
i2CvObj c2 dom cod = icMor (i2Ch c2) dom cod

public export
0 i2c2Mor : (0 c2 : Int2CatSig) -> Int2MorphSig (i2ChObj c2) (i2ChMor c2)
i2c2Mor c2 x y f g = micsMor (i2Cv c2 x y) f g

public export
0 i2c2Id : (0 c2 : Int2CatSig) ->
  Int2IdSig {obj=(i2ChObj c2)} {mor=(i2ChMor c2)} (i2c2Mor c2)
i2c2Id c2 x y = micsId (i2Cv c2 x y)

public export
0 i2c2Vcomp : (0 c2 : Int2CatSig) ->
  Int2VCompSig {obj=(i2ChObj c2)} {mor=(i2ChMor c2)} (i2c2Mor c2)
i2c2Vcomp c2 x y f g = micsComp (i2Cv c2 x y) f g

-- For any pair of objects of the category underlying a 2-category, there
-- is a category of 2-morphisms among 1-morphisms between the two given objects.
public export
0 i2cvc : (0 c2 : Int2CatSig) -> (0 dom, cod : icObj (i2Ch c2)) -> IntCatSig
i2cvc c2 dom cod =
  ICat
    (icMor (i2Ch c2) dom cod)
    $ MICS
      (\f, g => i2c2Mor c2 dom cod f g)
    $ ICS
      (i2c2Id c2 dom cod)
      (i2c2Vcomp c2 dom cod)

public export
0 i2cHcomp : (c2 : Int2CatSig) ->
  Int2HCompSig {obj=(i2ChObj c2)} {mor=(i2ChMor c2)}
    (icComp $ i2Ch c2) (\x, y, f, g => micsMor (i2Cv c2 x y) f g)
i2cHcomp c2 =
  Int2HCompFromWhiskers
    (i2C1Comp c2) (i2c2Mor c2) (i2Cwl c2) (i2Cwr c2) (i2c2Vcomp c2)

-- Given a collection of categories, we can form a two-category from all
-- the functor categories on pairs of categories in the collection.

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
0 IntFunctor2HCompSig : {0 idx : Type} -> (cat : idx -> IntCatSig) ->
  Int2HCompSig
    {obj=(icObj $ IntFunctorHCatSig {idx} cat)}
    {mor=(icMor $ IntFunctorHCatSig {idx} cat)}
    (icComp $ IntFunctorHCatSig {idx} cat)
    (\c, d, f, g => IntNTSig (icMor $ cat d) (ifOmap f) (ifOmap g))
IntFunctor2HCompSig {idx} cat c e d f f' g g' =
  intNThcomp
    {dmor=(icMor $ cat d)} {emor=(icMor $ cat e)}
    {f=(ifOmap f)} {g=(ifOmap g)} {f'=(ifOmap f')} {g'=(ifOmap g')}
    (icComp $ cat e)
    (ifMmap g)

public export
0 IntFunctor2CatSig : {0 idx : Type} -> (idx -> IntCatSig) -> Int2CatSig
IntFunctor2CatSig {idx} cat =
  I2Cat
    (IntFunctorHCatSig {idx} cat)
    (\dom, cod => IntOmapCatSig (cat dom) (cat cod) ifOmap)
    (IntFunctor2WhiskerLSig {idx} cat)
    (IntFunctor2WhiskerRSig {idx} cat)

-- The category of all categories in particular is a two-category.
public export
0 IntCat2Cat : Int2CatSig
IntCat2Cat = IntFunctor2CatSig {idx=IntCatSig} id

---------------------------
---------------------------
---- Double categories ----
---------------------------
---------------------------

public export
0 IntCellSig : (0 obj : Type) ->
  (0 vmor : IntMorSig obj) -> (0 hmor : IntMorSig obj) ->
  Type
IntCellSig obj vmor hmor =
  (0 x0, x1, y0, y1 : obj) ->
  (0 _ : vmor x0 y0) -> (0 _ : vmor x1 y1) ->
  (0 _ : hmor x0 x1) -> (0 _ : hmor y0 y1) ->
  Type

public export
0 IntCellTo2Sig : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  (0 _ : IntIdSig obj vmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  Int2MorphSig obj hmor
IntCellTo2Sig {obj} {vmor} {hmor} vid cell x y =
  cell x y x y (vid x) (vid y)

public export
0 IntCellIdSig : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  (0 vid : IntIdSig obj vmor) ->
  IntCellSig obj vmor hmor ->
  Type
IntCellIdSig {obj} {vmor} {hmor} vid cell =
  (0 x, y : obj) -> (0 f : hmor x y) -> cell x y x y (vid x) (vid y) f f

public export
0 IntCellTo2Id : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  (0 vid : IntIdSig obj vmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  IntCellIdSig {obj} {vmor} {hmor} vid cell ->
  Int2IdSig {obj} {mor=hmor} (IntCellTo2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2Id {obj} {vmor} {hmor} vid cell = id

public export
IntCellVHId : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  {0 vid : IntIdSig obj vmor} -> {0 cell : IntCellSig obj vmor hmor} ->
  (0 hid : IntIdSig obj hmor) ->
  (cid : IntCellIdSig {obj} {vmor} {hmor} vid cell) ->
  (0 x : obj) -> cell x x x x (vid x) (vid x) (hid x) (hid x)
IntCellVHId {obj} {vmor} {hmor} {vid} {cell} hid cid x = cid x x (hid x)

public export
0 IntCellVCompSig : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  (0 vcomp : IntCompSig obj vmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  Type
IntCellVCompSig {obj} {vmor} {hmor} vcomp cell =
  {0 x0, x1, y0, y1, z0, z1 : obj} ->
  (0 vmxy0 : vmor x0 y0) -> (0 vmxy1 : vmor x1 y1) ->
  (0 vmyz0 : vmor y0 z0) -> (0 vmyz1 : vmor y1 z1) ->
  (0 hmx : hmor x0 x1) -> (0 hmy : hmor y0 y1) -> (0 hmz : hmor z0 z1) ->
  cell y0 y1 z0 z1
    vmyz0 vmyz1 hmy hmz ->
  cell x0 x1 y0 y1
    vmxy0 vmxy1 hmx hmy ->
  cell x0 x1 z0 z1
    (vcomp x0 y0 z0 vmyz0 vmxy0) (vcomp x1 y1 z1 vmyz1 vmxy1) hmx hmz

public export
0 IntCellHCompSig : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  (0 hcomp : IntCompSig obj hmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  Type
IntCellHCompSig {obj} {vmor} {hmor} hcomp cell =
  {0 x0, x1, x2, y0, y1, y2 : obj} ->
  (0 vmxy0 : vmor x0 y0) -> (0 vmxy1 : vmor x1 y1) -> (0 vmxy2 : vmor x2 y2) ->
  (0 hmx01 : hmor x0 x1) -> (0 hmx12 : hmor x1 x2) ->
  (0 hmy01 : hmor y0 y1) -> (0 hmy12 : hmor y1 y2) ->
  cell x1 x2 y1 y2
    vmxy1 vmxy2 hmx12 hmy12 ->
  cell x0 x1 y0 y1
    vmxy0 vmxy1 hmx01 hmy01 ->
  cell x0 x2 y0 y2
    vmxy0 vmxy2 (hcomp x0 x1 x2 hmx12 hmx01) (hcomp y0 y1 y2 hmy12 hmy01)

public export
0 IntCellTo2MorSig : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  (0 vcomp : IntCompSig obj vmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  (0 vid : IntIdSig obj vmor) ->
  Type
IntCellTo2MorSig {obj} {vmor} {hmor} vcomp cell vid =
  (0 x, y : obj) -> (0 f, g : hmor x y) ->
  cell x y x y
    (vcomp x x x (vid x) (vid x))
    (vcomp y y y (vid y) (vid y))
    f g ->
  cell x y x y
    (vid x)
    (vid y)
    f g

public export
0 IntCellTo2VComp : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  {0 cell : IntCellSig obj vmor hmor} ->
  (0 vid : IntIdSig obj vmor) ->
  (0 vcomp : IntCompSig obj vmor) ->
  (0 c2m : IntCellTo2MorSig {obj} {vmor} {hmor} vcomp cell vid) ->
  (0 _ : IntCellVCompSig {obj} {vmor} {hmor} vcomp cell) ->
  Int2VCompSig {obj} {mor=hmor} (IntCellTo2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2VComp vid vcomp c2m cvcomp x y f g h beta alpha =
  c2m x y f h $ cvcomp (vid x) (vid y) (vid x) (vid y) f g h beta alpha

public export
0 IntCellTo2WhiskerL : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  {0 hcomp : IntCompSig obj hmor} ->
  (0 vid : IntIdSig obj vmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  (0 cid : IntCellIdSig {obj} {vmor} {hmor} vid cell) ->
  (0 _ : IntCellHCompSig {obj} {vmor} {hmor} hcomp cell) ->
  Int2WhiskerLSig {obj} {mor=hmor}
    hcomp (IntCellTo2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2WhiskerL {vmor} {hmor} {hcomp} vid cell cid chcomp x y f z g g' =
  flip (chcomp (vid x) (vid y) (vid z) f g f g') $ cid x y f

public export
0 IntCellTo2WhiskerR : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  {0 hcomp : IntCompSig obj hmor} ->
  (0 vid : IntIdSig obj vmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  (0 cid : IntCellIdSig {obj} {vmor} {hmor} vid cell) ->
  (0 _ : IntCellHCompSig {obj} {vmor} {hmor} hcomp cell) ->
  Int2WhiskerRSig {obj} {mor=hmor}
    hcomp (IntCellTo2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2WhiskerR {vmor} {hmor} {hcomp} vid cell cid chcomp y z g x f f' =
  chcomp (vid x) (vid y) (vid z) f g f' g $ cid y z g

public export
0 IntCellTo2HComp : {0 obj : Type} ->
  {0 vmor : IntMorSig obj} -> {0 hmor : IntMorSig obj} ->
  {0 hcomp : IntCompSig obj hmor} ->
  (0 vid : IntIdSig obj vmor) ->
  (0 cell : IntCellSig obj vmor hmor) ->
  (0 _ : IntCellHCompSig {obj} {vmor} {hmor} hcomp cell) ->
  Int2HCompSig {obj} {mor=hmor}
    hcomp (IntCellTo2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2HComp {obj} {vmor} {hmor} {hcomp} vid cell chcomp x z y f f' g g' =
  chcomp (vid x) (vid y) (vid z) f g f' g'

public export
record IntDblCatSig where
  constructor IDCat
  idcObj : Type
  idcVmics : MorIdCompSig idcObj
  idcHmics : MorIdCompSig idcObj
  idcCell : IntCellSig idcObj (micsMor idcVmics) (micsMor idcHmics)
  idcCid : IntCellIdSig (micsId idcVmics) idcCell
  idcCvcomp : IntCellVCompSig (micsComp idcVmics) idcCell
  idcChcomp : IntCellHCompSig (micsComp idcHmics) idcCell
  idcC2m : IntCellTo2MorSig (micsComp idcVmics) idcCell (micsId idcVmics)

public export
0 idcVcat : IntDblCatSig -> IntCatSig
idcVcat idc = ICat (idcObj idc) (idcVmics idc)

public export
0 idcVmor : (idc : IntDblCatSig) -> IntMorSig (idcObj idc)
idcVmor idc = icMor (idcVcat idc)

public export
0 idcVid : (idc : IntDblCatSig) -> IntIdSig (idcObj idc) (idcVmor idc)
idcVid idc = icId (idcVcat idc)

public export
0 idcVcomp : (idc : IntDblCatSig) -> IntCompSig (idcObj idc) (idcVmor idc)
idcVcomp idc = icComp (idcVcat idc)

public export
0 idcHcat : IntDblCatSig -> IntCatSig
idcHcat idc = ICat (idcObj idc) (idcHmics idc)

public export
0 idcHmor : (idc : IntDblCatSig) -> IntMorSig (idcObj idc)
idcHmor idc = icMor (idcHcat idc)

public export
0 idcHid : (idc : IntDblCatSig) -> IntIdSig (idcObj idc) (idcHmor idc)
idcHid idc = icId (idcHcat idc)

public export
0 idcHcomp : (idc : IntDblCatSig) -> IntCompSig (idcObj idc) (idcHmor idc)
idcHcomp idc = icComp (idcHcat idc)

public export
0 idc2mics : (idc : IntDblCatSig) -> (0 dom, cod : idcObj idc) ->
  MorIdCompSig (idcHmor idc dom cod)
idc2mics idc dom cod =
  MICS
    (\f, g => IntCellTo2Sig (idcVid idc) (idcCell idc) dom cod f g)
  $ ICS
    (IntCellTo2Id (idcVid idc) (idcCell idc) (idcCid idc) dom cod)
    (\f, g, h, beta, alpha =>
      IntCellTo2VComp
        (idcVid idc) (idcVcomp idc) (idcC2m idc) (idcCvcomp idc)
        dom cod f g h beta alpha)

public export
0 idc2cat : IntDblCatSig -> Int2CatSig
idc2cat idc =
  I2Cat
    (idcHcat idc)
    (idc2mics idc)
    (IntCellTo2WhiskerL (idcVid idc) (idcCell idc) (idcCid idc) (idcChcomp idc))
    (IntCellTo2WhiskerR (idcVid idc) (idcCell idc) (idcCid idc) (idcChcomp idc))

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

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Internal pro-/di-functors and (para-)natural transformations ----
----------------------------------------------------------------------
----------------------------------------------------------------------

-----------------------------------------
---- Definitions of pro-/di-functors ----
-----------------------------------------

-- The convention we use is that the first parameter (here, `d`) is the
-- contravariant parameter, and the second parameter (`here, `c`) is
-- the covariant parameter.  This is sometimes written as `c -/-> d`,
-- and sometimes called a "correspondence from" `d` to `c`.
-- Since `Cat` is cartesian closed, it may be viewed as a functor
-- `c -> presheaves(d)`, or equivalently as a functor
-- `op(d) -> copresheaves(c)`.  See
-- https://en.wikipedia.org/wiki/Profunctor#Definition and
-- https://ncatlab.org/nlab/show/profunctor#definition.
public export
IntProfunctorSig : (d, c : Type) -> Type
IntProfunctorSig d c = d -> c -> Type

public export
IntDifunctorSig : (c : Type) -> Type
IntDifunctorSig c = IntProfunctorSig c c

public export
IntComp : (c : Type) -> (mor : IntDifunctorSig c) -> Type
IntComp c mor = (x, y, z : c) -> mor y z -> mor x y -> mor x z

public export
0 IntIdLSig : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) -> IntIdSig c mor -> Type
IntIdLSig c mor comp cid =
  (0 x, y : c) -> (m : mor x y) -> comp x x y m (cid x) = m

public export
0 IntIdRSig : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) -> IntIdSig c mor -> Type
IntIdRSig c mor comp cid =
  (0 x, y : c) -> (m : mor x y) -> comp x y y (cid y) m = m

public export
0 IntAssocSig : (0 c : Type) ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  Type
IntAssocSig c mor comp =
  (w, x, y, z : c) ->
  (h : mor y z) -> (g : mor x y) -> (f : mor w x) ->
  comp w x z (comp x y z h g) f = comp w y z h (comp w x y g f)

public export
0 IntDimapSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntProfunctorSig d c -> Type
IntDimapSig d c dmor cmor p =
  (s : d) -> (t : c) -> (a : d) -> (b : c) ->
  dmor a s -> cmor t b -> p s t -> p a b

public export
0 IntEndoDimapSig : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  IntDifunctorSig c -> Type
IntEndoDimapSig c mor = IntDimapSig c c mor mor

public export
0 IntLmapSig : (d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntProfunctorSig d c -> Type
IntLmapSig d c dmor cmor p =
  (s : d) -> (t : c) -> (a : d) -> dmor a s -> p s t -> p a t

public export
0 IntEndoLmapSig : (c : Type) -> (cmor : IntDifunctorSig c) ->
  IntDifunctorSig c -> Type
IntEndoLmapSig c cmor = IntLmapSig c c cmor cmor

public export
0 IntLmapIdSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (did : IntIdSig d dmor) ->
  (p : IntProfunctorSig d c) ->
  IntLmapSig d c dmor cmor p -> Type
IntLmapIdSig d c dmor cmor did p plm =
  (0 s : d) -> (0 t : c) -> (0 pst : p s t) -> plm s t s (did s) pst = pst

public export
0 IntEndoLmapIdSig : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> Type
IntEndoLmapIdSig c cmor = IntLmapIdSig c c cmor cmor

public export
0 IntRmapSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntProfunctorSig d c -> Type
IntRmapSig d c dmor cmor p =
  (s : d) -> (t : c) -> (b : c) -> cmor t b -> p s t -> p s b

public export
0 IntEndoRmapSig : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  IntDifunctorSig c -> Type
IntEndoRmapSig c cmor = IntRmapSig c c cmor cmor

public export
0 IntRmapIdSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) ->
  (p : IntProfunctorSig d c) ->
  IntRmapSig d c dmor cmor p -> Type
IntRmapIdSig d c dmor cmor cid p prm =
  (0 s : d) -> (0 t : c) -> (0 pst : p s t) -> prm s t t (cid t) pst = pst

public export
0 IntEndoRmapIdSig : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoRmapSig c cmor p -> Type
IntEndoRmapIdSig c cmor = IntRmapIdSig c c cmor cmor

public export
0 IntLmapFromDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (0 cid : IntIdSig c cmor) ->
  (p : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p ->
  IntLmapSig d c dmor cmor p
IntLmapFromDimap d c dmor cmor cid p pdm s t a = flip (pdm s t a t) (cid t)

public export
0 IntEndoLmapFromDimap : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (0 cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoDimapSig c cmor p -> IntEndoLmapSig c cmor p
IntEndoLmapFromDimap c cmor cid = IntLmapFromDimap c c cmor cmor cid

public export
0 IntRmapFromDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (0 did : IntIdSig d dmor) ->
  (p : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p ->
  IntRmapSig d c dmor cmor p
IntRmapFromDimap d c dmor cmor did p pdm s t b = pdm s t s b (did s)

public export
0 IntEndoRmapFromDimap : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (0 cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoDimapSig c cmor p -> IntEndoRmapSig c cmor p
IntEndoRmapFromDimap c cmor cid = IntRmapFromDimap c c cmor cmor cid

public export
0 IntLRmapsCommute : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntProfunctorSig d c) ->
  IntLmapSig d c dmor cmor p ->
  IntRmapSig d c dmor cmor p ->
  Type
IntLRmapsCommute d c dmor cmor p plm prm =
  (0 s : d) -> (0 t : c) -> (0 a : d) -> (0 b : c) ->
  (0 dmas : dmor a s) -> (0 cmtb : cmor t b) ->
  ExtEq {a=(p s t)} {b=(p a b)}
    (plm s b a dmas . prm s t b cmtb)
    (prm a t b cmtb . plm s t a dmas)

public export
0 IntEndoLRmapsCommute : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> IntEndoRmapSig c cmor p ->
  Type
IntEndoLRmapsCommute c cmor p plm prm = IntLRmapsCommute c c cmor cmor p plm prm

public export
IntDimapFromLRmaps : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntProfunctorSig d c) ->
  IntLmapSig d c dmor cmor p ->
  IntRmapSig d c dmor cmor p ->
  IntDimapSig d c dmor cmor p
IntDimapFromLRmaps d c dmor cmor p plm prm s t a b dmas cmtb =
  plm s b a dmas . prm s t b cmtb

public export
IntEndoDimapFromLRmaps : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p ->
  IntEndoRmapSig c cmor p ->
  IntEndoDimapSig c cmor p
IntEndoDimapFromLRmaps c cmor = IntDimapFromLRmaps c c cmor cmor

--------------------------------------------
---- (Di-/Para-)natural transformations ----
--------------------------------------------

-- The signature of a dinatural transformation, without the dinaturality
-- condition.
public export
IntDiNTSig : (c : Type) -> (p, q : IntDifunctorSig c) -> Type
IntDiNTSig c p q = (x : c) -> p x x -> q x x

-- The dinaturality condition.  For our purposes, we will only be interested
-- in _strong_ dinatural transformations, or "paranatural" transformations,
-- which have the same base signature, together with a condition defined below.
-- Therefore, our only use of this condition will be to prove that it follows
-- from the paranaturality condition (so all paranatural transformations are
-- dinatural, but not vice versa).
public export
0 IntDiNTCond : (c : Type) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> IntEndoRmapSig c cmor p ->
  IntEndoLmapSig c cmor q -> IntEndoRmapSig c cmor q ->
  IntDiNTSig c p q -> Type
IntDiNTCond c cmor p q plm prm qlm qrm alpha =
  (i0, i1 : c) -> (i2 : cmor i0 i1) ->
  ExtEq {a=(p i1 i0)} {b=(q i0 i1)}
    (qlm i1 i1 i0 i2 . alpha i1 . prm i1 i0 i1 i2)
    (qrm i0 i0 i1 i2 . alpha i0 . plm i1 i0 i0 i2)

public export
IntDiNTcomp : (c : Type) -> (p, q, r : IntDifunctorSig c) ->
  IntDiNTSig c q r -> IntDiNTSig c p q -> IntDiNTSig c p r
IntDiNTcomp c p q r beta alpha x = beta x . alpha x

-- This could be read as "`alpha` preserves structure-homomorphisms", which
-- in turn means that each such paranatural transformation corresponds to
-- a functor between categories of diagonal elements.
public export
0 IntParaNTCond : (c : Type) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> IntEndoRmapSig c cmor p ->
  IntEndoLmapSig c cmor q -> IntEndoRmapSig c cmor q ->
  IntDiNTSig c p q -> Type
IntParaNTCond c cmor p q plm prm qlm qrm alpha =
  (i0, i1 : c) -> (i2 : cmor i0 i1) -> (d0 : p i0 i0) -> (d1 : p i1 i1) ->
  (plm i1 i1 i0 i2 d1 = prm i0 i0 i1 i2 d0) ->
  (qlm i1 i1 i0 i2 (alpha i1 d1) = qrm i0 i0 i1 i2 (alpha i0 d0))

-- Paranaturality is a (strictly) stronger condition than dinaturality.
0 IntParaNTimpliesDi : (c : Type) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntDifunctorSig c) ->
  (plm : IntEndoLmapSig c cmor p) -> (prm : IntEndoRmapSig c cmor p) ->
  IntEndoLRmapsCommute c cmor p plm prm ->
  (qlm : IntEndoLmapSig c cmor q) -> (qrm : IntEndoRmapSig c cmor q) ->
  (alpha : IntDiNTSig c p q) ->
  IntParaNTCond c cmor p q plm prm qlm qrm alpha ->
  IntDiNTCond c cmor p q plm prm qlm qrm alpha
IntParaNTimpliesDi c cmor p q plm prm comm qlm qrm alpha para i0 i1 i2 pi1i0 =
  para i0 i1 i2 (plm i1 i0 i0 i2 pi1i0) (prm i1 i0 i1 i2 pi1i0) $
    comm i1 i0 i0 i1 i2 i2 pi1i0

-- Paranatural transformations compose (which dinatural transformations
-- do not in general).
public export
IntParaNTcomp : (c : Type) -> (mor : IntDifunctorSig c) ->
  (p, q, r : IntDifunctorSig c) ->
  (plm : IntEndoLmapSig c mor p) -> (prm : IntEndoRmapSig c mor p) ->
  (qlm : IntEndoLmapSig c mor q) -> (qrm : IntEndoRmapSig c mor q) ->
  (rlm : IntEndoLmapSig c mor r) -> (rrm : IntEndoRmapSig c mor r) ->
  (beta : IntDiNTSig c q r) ->
  IntParaNTCond c mor q r qlm qrm rlm rrm beta ->
  (alpha : IntDiNTSig c p q) ->
  IntParaNTCond c mor p q plm prm qlm qrm alpha ->
  IntParaNTCond c mor p r plm prm rlm rrm (IntDiNTcomp c p q r beta alpha)
IntParaNTcomp c mor p q r plm prm qlm qrm rlm rrm beta bcond alpha acond
  i0 i1 mi0i1 p00 p11 pcomm =
    bcond i0 i1 mi0i1 (alpha i0 p00) (alpha i1 p11) $
      acond i0 i1 mi0i1 p00 p11 pcomm

--------------------------------------------
---- Profunctor natural transformations ----
--------------------------------------------

public export
0 IntProfNTSig : (d, c : Type) ->
  (p, q : IntProfunctorSig d c) -> Type
IntProfNTSig d c p q = (x : d) -> (y : c) -> p x y -> q x y

public export
0 IntEndoProfNTSig : (c : Type) ->
  (p, q : IntDifunctorSig c) -> Type
IntEndoProfNTSig c = IntProfNTSig c c

public export
0 IntProfNTNaturality :
  (d, c : Type) -> (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p -> IntDimapSig d c dmor cmor q ->
  IntProfNTSig d c p q -> Type
IntProfNTNaturality d c dmor cmor p q pdm qdm alpha =
  (0 s : d) -> (0 t : c) -> (0 a : d) -> (0 b : c) ->
  (0 dmas : dmor a s) -> (0 cmtb : cmor t b) ->
  ExtEq {a=(p s t)} {b=(q a b)}
    (qdm s t a b dmas cmtb . alpha s t)
    (alpha a b . pdm s t a b dmas cmtb)

public export
0 IntProfNTvComp : (0 d, c : Type) ->
  (0 p, q, r : IntProfunctorSig d c) ->
  IntProfNTSig d c q r -> IntProfNTSig d c p q -> IntProfNTSig d c p r
IntProfNTvComp d c p q r beta alpha x y = beta x y . alpha x y

-------------------------------------------------------------------------------
---- Restriction of natural transformations to paranatural transformations ----
-------------------------------------------------------------------------------

-- Here we show that given a natural transformation between profunctors,
-- its restriction to the diagonal is paranatural.

public export
IntProfNTRestrict : (0 c : Type) ->
  (0 p, q : IntDifunctorSig c) -> IntEndoProfNTSig c p q -> IntDiNTSig c p q
IntProfNTRestrict c p q alpha x = alpha x x

public export
0 IntProfNTRestrictPara :
  (0 c : Type) -> (0 cmor : IntDifunctorSig c) -> (0 cid : IntIdSig c cmor) ->
  (0 p, q : IntDifunctorSig c) ->
  (plm : IntEndoLmapSig c cmor p) -> (prm : IntEndoRmapSig c cmor p) ->
  (qlm : IntEndoLmapSig c cmor q) -> (qrm : IntEndoRmapSig c cmor q) ->
  (plid : IntEndoLmapIdSig c cmor cid p plm) ->
  (prid : IntEndoRmapIdSig c cmor cid p prm) ->
  (qlid : IntEndoLmapIdSig c cmor cid q qlm) ->
  (qrid : IntEndoRmapIdSig c cmor cid q qrm) ->
  (alpha : IntProfNTSig c c p q) ->
  IntProfNTNaturality c c cmor cmor p q
    (IntEndoDimapFromLRmaps c cmor p plm prm)
    (IntEndoDimapFromLRmaps c cmor q qlm qrm)
    alpha ->
  IntParaNTCond c cmor p q plm prm qlm qrm (IntProfNTRestrict c p q alpha)
IntProfNTRestrictPara c cmor cid p q plm prm qlm qrm plid prid qlid qrid
  alpha nat s t cmst pss ptt peq =
    let
      qlrew = qlid s t (qrm s s t cmst (alpha s s pss))
      qrrew = cong (qlm t t s cmst) $ qrid t t (alpha t t ptt)
      plrew = plid s t (prm s s t cmst pss)
      prrew = cong (plm t t s cmst) $ prid t t ptt
      congpeq = cong (alpha s t) $ trans prrew $ trans peq (sym plrew)
      nat_s = trans (sym $ nat s s s t (cid s) cmst pss) qlrew
      nat_t = trans (sym qrrew) $ nat t t s t cmst (cid t) ptt
    in
    trans (trans nat_t congpeq) nat_s

-----------------------------
---- Utility profunctors ----
-----------------------------

public export
constProf : (0 d, c : Type) -> Type -> IntProfunctorSig d c
constProf d c x _ _ = x

public export
constDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (0 x : Type) -> IntDimapSig d c dmor cmor (constProf d c x)
constDimap d c dmor cmor x s t a b dmas cmtb = id {a=x}

public export
terminalProf : (0 d, c : Type) -> IntProfunctorSig d c
terminalProf d c = constProf d c Unit

public export
terminalDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntDimapSig d c dmor cmor (terminalProf d c)
terminalDimap d c dmor cmor = constDimap d c dmor cmor Unit

public export
constDi : (0 c : Type) -> (apex : Type) -> IntDifunctorSig c
constDi c = constProf c c

public export
constEndoDimap : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (0 x : Type) -> IntEndoDimapSig c mor (constDi c x)
constEndoDimap c mor = constDimap c c mor mor

-----------------------------
---- Wedges and cowedges ----
-----------------------------

public export
0 IntGenEndBase : (d, c : Type) -> (p : IntProfunctorSig d c) -> Type
IntGenEndBase d c = IntProfNTSig d c (terminalProf d c)

public export
0 IntGenEndBaseIsGenEnd :
  (d, c : Type) -> (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (0 p : IntProfunctorSig d c) -> (pdm : IntDimapSig d c dmor cmor p) ->
  (endb : IntGenEndBase d c p) -> Type
IntGenEndBaseIsGenEnd d c dmor cmor p =
  IntProfNTNaturality d c dmor cmor
    (terminalProf d c) p (terminalDimap d c dmor cmor)

public export
0 IntEndBase : (c : Type) -> (p : IntDifunctorSig c) -> Type
-- Equivalent to `WedgeBase c Unit`.
-- An `IntGenEndBase c c` can be restricted to an `IntEndBase c p`.
IntEndBase c = IntDiNTSig c (terminalProf c c)

public export
0 WedgeBase :
  (0 c : Type) -> (0 apex : Type) -> (0 p : IntDifunctorSig c) -> Type
WedgeBase c apex p = IntDiNTSig c (constDi c apex) p

public export
0 CowedgeBase :
  (0 c : Type) -> (0 apex : Type) -> (0 p : IntDifunctorSig c) -> Type
CowedgeBase c apex p = IntDiNTSig c p (constDi c apex)

------------------------------------
---- Composition of profunctors ----
------------------------------------

-- The difunctor whose coend is the composition of two profunctors.
public export
IntProCompDi : (0 c, d, e : Type) ->
  (q : IntProfunctorSig e d) ->
  (p : IntProfunctorSig d c) ->
  (i : e) -> (j : c) ->
  IntDifunctorSig d
IntProCompDi c d e q p i j s t = (p s j, q i t)

public export
IntProCompDiDimap : (0 c, d, e : Type) ->
  (cmor : IntDifunctorSig c) ->
  (dmor : IntDifunctorSig d) ->
  (emor : IntDifunctorSig e) ->
  (q : IntProfunctorSig e d) -> (p : IntProfunctorSig d c) ->
  (qrm : IntRmapSig e d emor dmor q) -> (plm : IntLmapSig d c dmor cmor p) ->
  (i : e) -> (j : c) ->
  IntEndoDimapSig d dmor (IntProCompDi c d e q p i j)
IntProCompDiDimap c d e cmor dmor emor q p qrm plm i j s t a b
  dmas dmtb (psj, qit) = (plm s j a dmas psj, qrm i t b dmtb qit)

-- The difunctor whose coend is the composition of two difunctors.
public export
IntDiCompDi : (0 c : Type) -> (q, p : IntDifunctorSig c) -> (a, b : c) ->
  IntDifunctorSig c
IntDiCompDi c = IntProCompDi c c c

public export
IntDiCompDiDimap : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  (q, p : IntDifunctorSig c) ->
  (qrm : IntEndoRmapSig c mor q) -> (plm : IntEndoLmapSig c mor p) ->
  (i, j : c) ->
  IntEndoDimapSig c mor (IntDiCompDi c q p i j)
IntDiCompDiDimap c mor = IntProCompDiDimap c c c mor mor mor

public export
IntProComp : (c, d, e : Type) ->
  (q : IntProfunctorSig e d) ->
  (p : IntProfunctorSig d c) ->
  IntProfunctorSig e c
IntProComp c d e q p i j =
  DPair d $ \x : d => IntProCompDi c d e q p i j x x

public export
IntProCompDimap : (c, d, e : Type) ->
  (cmor : IntDifunctorSig c) ->
  (dmor : IntDifunctorSig d) ->
  (emor : IntDifunctorSig e) ->
  (q : IntProfunctorSig e d) -> (p : IntProfunctorSig d c) ->
  (qlm : IntLmapSig e d emor dmor q) -> (prm : IntRmapSig d c dmor cmor p) ->
  IntDimapSig e c emor cmor (IntProComp c d e q p)
IntProCompDimap c d e cmor dmor emor q p qlm prm s t a b emas cmtb
  (i ** (pit, qsi)) =
    (i ** (prm i t b cmtb pit, qlm s i a emas qsi))

public export
IntDiComp : (c : Type) ->
  (q, p : IntDifunctorSig c) ->
  IntDifunctorSig c
IntDiComp c = IntProComp c c c

public export
IntDiCompDimap : (c : Type) ->
  (cmor : IntDifunctorSig c) ->
  (q, p : IntDifunctorSig c) ->
  (qlm : IntEndoLmapSig c cmor q) -> (prm : IntEndoRmapSig c cmor p) ->
  IntEndoDimapSig c cmor (IntDiComp c q p)
IntDiCompDimap c cmor = IntProCompDimap c c c cmor cmor cmor

-----------------------------------
---- Whiskering of profunctors ----
-----------------------------------

public export
0 IntProfNTwhiskerL : (0 e, d, c : Type) ->
  (0 q, r : IntProfunctorSig e d) ->
  IntProfNTSig e d q r ->
  (p : IntProfunctorSig d c) ->
  IntProfNTSig e c (IntProComp c d e q p) (IntProComp c d e r p)
IntProfNTwhiskerL e d c q r nu p s t (i ** (pit, qsi)) =
  (i ** (pit, nu s i qsi))

public export
0 IntProfNTwhiskerR : (0 e, d, c : Type) ->
  (0 p, q : IntProfunctorSig d c) ->
  (r : IntProfunctorSig e d) ->
  IntProfNTSig d c p q ->
  IntProfNTSig e c (IntProComp c d e r p) (IntProComp c d e r q)
IntProfNTwhiskerR e d c p q r nu s t (i ** (pit, rsi)) =
  (i ** (nu i t pit, rsi))

public export
0 IntProfNThComp : (0 e, d, c : Type) ->
  (0 p, p' : IntProfunctorSig d c) ->
  (0 q, q' : IntProfunctorSig e d) ->
  IntProfNTSig e d q q' ->
  IntProfNTSig d c p p' ->
  IntProfNTSig e c (IntProComp c d e q p) (IntProComp c d e q' p')
IntProfNThComp e d c p p' q q' beta alpha s t =
  IntProfNTwhiskerL e d c q q' beta p' s t .
  IntProfNTwhiskerR e d c p p' q alpha s t

--------------------------------------------------------
--------------------------------------------------------
---- Internal (di/pro-Yoneda) emebddings and lemmas ----
--------------------------------------------------------
--------------------------------------------------------

---------------------------------
---- di-Yoneda (paranatural) ----
---------------------------------

-- Suppose that `c` is a type of objects of a category internal to `Type`,
-- and `mor` is a type dependent on pairs of terms of `c` (we could also
-- express it dually as a `Type` together with morphisms `dom` and `cod` to
-- `c`), which we interpret as _some_ morphisms of the category but not
-- necessarily all.  Then `IntDiYonedaEmbedObj c mor` is the object-map
-- component of the diYoneda embedding (since that embedding is a (di)functor)
-- of the product of the opposite of the internal category and the internal
-- category itself (`op(Type) x Type`) into the category whose objects are
-- difunctors on the internal category -- that is, functors
-- `op(c) -> c -> Type` -- and whose morphisms are paranatural
-- transformations.
public export
IntDiYonedaEmbedObj : (c : Type) ->
  (mor : IntDifunctorSig c) -> c -> c -> IntDifunctorSig c
IntDiYonedaEmbedObj c mor i0 i1 j0 j1 = (mor j0 i1, mor i0 j1)
                       --  d  c  c' d'     c' -> c    d -> d'
                       --  i  j  x  y       x -> j    i -> y
                       --  i0 -> i1 / i -> j  &   j0 -> j1 / x -> y

---  i0/I/d  j0/x/c' j1/y/d'  i1/J/c
-- 1)  --------------------------> (part of graph object in arena)
-- 2)          ------->            (part of graph object in interpretation)
-- 3)          ------------------> (part of di-Yoneda embedding in interpretation)
-- 4)  --------------->            (part of di-Yoneda embedding in interpretation)
                       -- cob ba            x' : j0 -> j1 (x -> y)
-- When x==y, #2 becomes an automorphism, and it becomes possible to compose
-- #3 . #2 . #4 and assert that that equals #1.
-- This is not a graph because the objects have a d->c rather than a c->d
-- (together with a c'->d').  If we flipped the argument order, then the
-- di-Yoneda morphisms would become cross-category.  It's not a cograph either,
-- for the same reason (there are morphisms going in both directions).  That's
-- what makes it dependent on being a difunctor (an _endo_-profunctor as
-- opposed to just any profunctor).
--
-- To make general profunctors, we can use the existing stuff in `PolyDifunc`,
-- and to make difunctors suited to paranatural transformations, we can use
-- the arrangement of morphisms above.  That arrangement ensures that we can
-- always turn "x"s into "y"s, and thereby define difunctors such as that
-- of wild groups with the likes of associativity included.

-- Embed `OpProd(c)` into `Type`.
public export
0 IntDiYonedaFullEmbedObj : (c : Type) ->
  (mor : IntDifunctorSig c) -> IntDifunctorSig c
IntDiYonedaFullEmbedObj c mor i0 i1 =
  IntEndBase c $ IntDiYonedaEmbedObj c mor i0 i1

-- We now show that for a given `(s, t)` in `opProd(c)`, the diYoneda
-- embedding `IntDiYonedaEmbedObj c mor s t` is a difunctor on `c`.
public export
IntDiYonedaEmbedLmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoLmapSig c mor (IntDiYonedaEmbedObj c mor s t)
IntDiYonedaEmbedLmap c mor comp s t a b i cmia (cmat, cmsb) =
  (comp i a t cmat cmia, cmsb)

public export
IntDiYonedaEmbedRmap : (c : Type) -> (0 mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoRmapSig c mor (IntDiYonedaEmbedObj c mor s t)
IntDiYonedaEmbedRmap c mor comp s t a b j cmbj (cmat, cmsb) =
  (cmat, comp s b j cmbj cmsb)

public export
IntDiYonedaEmbedDimap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoDimapSig c mor (IntDiYonedaEmbedObj c mor s t)
IntDiYonedaEmbedDimap c mor comp s t =
  IntEndoDimapFromLRmaps c mor (IntDiYonedaEmbedObj c mor s t)
    (IntDiYonedaEmbedLmap c mor comp s t)
    (IntDiYonedaEmbedRmap c mor comp s t)

public export
IntDiYonedaEmbedMorphNT : (c : Type) ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (s, t, a, b : c) ->
  IntEndoOpProdCatMor c mor (s, t) (a, b) ->
  IntEndoProfNTSig c
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
IntDiYonedaEmbedMorphNT c mor comp s t a b (mas, mtb) i j (mit, msj) =
  (comp i t b mtb mit, comp a s j msj mas)

-- The morphism-map component of the diYoneda embedding.
-- The domain of that embedding is `opProd(c)`, and the codomain
-- is the category of difunctors on `c` with paranatural transformations,
-- so the morphism-map component takes morphisms of `opProd(c)` to
-- paranatural transformations.
public export
IntDiYonedaEmbedMorph : (c : Type) ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (s, t, a, b : c) ->
  IntEndoOpProdCatMor c mor (s, t) (a, b) ->
  IntDiNTSig c (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
IntDiYonedaEmbedMorph c mor comp s t a b (mas, mtb) =
  IntProfNTRestrict c
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntDiYonedaEmbedMorphNT c mor comp s t a b (mas, mtb))

-- The diYoneda embedding of any morphism of `opProd(c)` is a
-- natural transformation.
public export
0 IntDiYonedaEmbedMorphNatural : (0 c : Type) ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (assoc : IntAssocSig c mor comp) ->
  (s, t, a, b : c) ->
  (m : IntEndoOpProdCatMor c mor (s, t) (a, b)) ->
  IntProfNTNaturality c c mor mor
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntEndoDimapFromLRmaps c mor (IntDiYonedaEmbedObj c mor s t)
      (IntDiYonedaEmbedLmap c mor comp s t)
      (IntDiYonedaEmbedRmap c mor comp s t))
    (IntEndoDimapFromLRmaps c mor (IntDiYonedaEmbedObj c mor a b)
      (IntDiYonedaEmbedLmap c mor comp a b)
      (IntDiYonedaEmbedRmap c mor comp a b))
    (IntDiYonedaEmbedMorphNT c mor comp s t a b m)
IntDiYonedaEmbedMorphNatural c mor comp assoc s t a b (mas, mtb) i0 i1 j0 j1
  mj0i0 mi1j1 (mi0t, msi1) =
    pairEqCong
      (rewrite assoc j0 i0 t b mtb mi0t mj0i0 in Refl)
      (rewrite sym (assoc a s i1 j1 mi1j1 msi1 mas) in Refl)

-- The diYoneda embedding of any morphism of `opProd(c)` is a
-- paranatural transformation.
public export
0 IntDiYonedaEmbedMorphPara : (0 c : Type) ->
  (mor : IntDifunctorSig c) -> (0 cid : IntIdSig c mor) ->
  (comp : IntCompSig c mor) ->
  (idl : IntIdLSig c mor comp cid) -> (idr : IntIdRSig c mor comp cid) ->
  (assoc : IntAssocSig c mor comp) ->
  (s, t, a, b : c) ->
  (m : IntEndoOpProdCatMor c mor (s, t) (a, b)) ->
  IntParaNTCond c mor
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntDiYonedaEmbedLmap c mor comp s t)
    (IntDiYonedaEmbedRmap c mor comp s t)
    (IntDiYonedaEmbedLmap c mor comp a b)
    (IntDiYonedaEmbedRmap c mor comp a b)
    (IntDiYonedaEmbedMorph c mor comp s t a b m)
IntDiYonedaEmbedMorphPara c mor cid comp idl idr assoc s t a b (mas, mtb) =
  IntProfNTRestrictPara c mor cid
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntDiYonedaEmbedLmap c mor comp s t) (IntDiYonedaEmbedRmap c mor comp s t)
    (IntDiYonedaEmbedLmap c mor comp a b) (IntDiYonedaEmbedRmap c mor comp a b)
    (\i, j, (mit, msj) => pairEqCong (idl i t mit) Refl)
    (\i, j, (mit, msj) => pairEqCong Refl (idr s j msj))
    (\i, j, (mib, maj) => pairEqCong (idl i b mib) Refl)
    (\i, j, (mib, maj) => pairEqCong Refl (idr a j maj))
    (IntDiYonedaEmbedMorphNT c mor comp s t a b (mas, mtb))
    (IntDiYonedaEmbedMorphNatural c mor comp assoc s t a b (mas, mtb))

-- The diYoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is an object of paranatural
-- transformations.  This type is an explicit name for that object.
-- It is the analogue to the standard form of the Yoneda lemma's "set/object of
-- natural transformations from `Hom(_, a)` to `F`".
--
-- Like any object of natural transformations, this could be expressed
-- as an end.  The end form of this lemma is sometimes called
-- "Yoneda reduction".
public export
IntDiYonedaLemmaNT : (c : Type) -> (mor, p : IntDifunctorSig c) ->
  IntDifunctorSig c
IntDiYonedaLemmaNT c mor p i j =
  IntDiNTSig c (IntDiYonedaEmbedObj c mor i j) (flip p)

-- This shows that for a given difunctor `p` on `c`,
-- `IntDiYonedaLemmaNT c mor p` is itself an argument-flipped difunctor
-- (whose value for any `(s, t)` in `opProd(c)` is an object (in `Type`) of
-- paranatural transformations).  That makes it sensible to speak of paranatural
-- transformations between `IntDiYonedaLemmaNT c mor p` and `p`, and
-- the diYoneda lemma exhibits a specific pair of such paranatural
-- transformations, one in each direction, which are inverses to each other.
--
-- That the arguments to `IntDiYonedaLemmaNT` need to be flipped to make it
-- into a difunctor -- that is, that it's covariant in the _first_ argument
-- and contravariant in the _second_ -- makes it a _presheaf_ on `op(c) x c`,
-- as opposed to the usual ordering of profunctor arguments which would be a
-- _copresheaf_ on `op(c) x c`.
public export
IntDiYonedaLemmaNTDimap : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntEndoDimapSig c mor (flip (IntDiYonedaLemmaNT c mor p))
IntDiYonedaLemmaNTDimap c mor comp p s t a b mas mtb embed i (mia, mbi) =
  embed i (comp i a s mas mia, comp t b i mbi mtb)

-- One direction of the paranatural isomorphism asserted by the diYoneda lemma.
public export
IntDiYonedaLemmaL : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (0 p : IntDifunctorSig c) -> (pdm : IntEndoDimapSig c mor p) ->
  IntDiNTSig c p (IntDiYonedaLemmaNT c mor p)
IntDiYonedaLemmaL c mor p pdm i pii j (mji, mij) = pdm i i j j mji mij pii

-- The other direction of the paranatural isomorphism asserted by the
-- diYoneda lemma.
public export
IntDiYonedaLemmaR : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntDiNTSig c (IntDiYonedaLemmaNT c mor p) p
IntDiYonedaLemmaR c mor cid p i embed = embed i (cid i, cid i)

-- The di-co-Yoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is a coend (existential type).
-- This type is an explicit name for that object.
-- It is the analogue to the standard form of the co-Yoneda lemma's
-- representation of the presheaf embedding of an object as a colimit
-- of representables (the density theorem asserts that such a representation
-- exists for every presheaf).
public export
IntDiCoYonedaLemmaCoendBase : (c : Type) -> (mor : IntDifunctorSig c) ->
  (p : IntDifunctorSig c) -> IntDifunctorSig c
IntDiCoYonedaLemmaCoendBase c mor p i j =
  DPair (c, c) $ \xy =>
    (IntDiYonedaEmbedObj c mor i j (fst xy) (snd xy), flip p (fst xy) (snd xy))

-- This shows that for a given difunctor `p` on `c`,
-- `IntDiCoYonedaLemmaCoendBase c mor p` is itself a difunctor (whose value
-- for any `(s, t)` in `opProd(c)` is a coend representation of a presheaf).
-- That makes it sensible to speak of paranatural transformations between
-- `IntDiCoYonedaLemmaCoendBase c mor p` and `p`, and the di-co-Yoneda lemma
-- exhibits a specific pair of such paranatural transformations, one in each
-- direction, which are inverses to each other.
public export
IntDiYonedaLemmaCoendBaseDimap : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntEndoDimapSig c mor (IntDiCoYonedaLemmaCoendBase c mor p)
IntDiYonedaLemmaCoendBaseDimap c mor comp p s t a b mas mtb
  (ij ** ((mit, msj), pji)) =
    (ij ** ((comp (fst ij) t b mtb mit, comp a s (snd ij) msj mas), pji))

-- One direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma.
public export
IntDiCoYonedaLemmaL : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntDiNTSig c p (IntDiCoYonedaLemmaCoendBase c mor p)
IntDiCoYonedaLemmaL c mor cid p i pii = ((i, i) ** ((cid i, cid i), pii))

-- The other direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma.
public export
IntDiCoYonedaLemmaR : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) ->
  (0 p : IntDifunctorSig c) -> (pdm : IntEndoDimapSig c mor p) ->
  IntDiNTSig c (IntDiCoYonedaLemmaCoendBase c mor p) p
IntDiCoYonedaLemmaR c mor p pdm x (ij ** ((mix, mxj), pji)) =
  pdm (snd ij) (fst ij) x x mxj mix pji

--------------------------------------------
---- Metalanguage profunctor signatures ----
--------------------------------------------

public export
TypeDimap : {0 p : ProfunctorSig} ->
  DimapSig p -> IntEndoDimapSig TypeObj TypeMor p
TypeDimap {p} dm _ _ _ _ = dm

public export
TypeProfDimap : {0 p : ProfunctorSig} ->
  Profunctor p -> IntEndoDimapSig TypeObj TypeMor p
TypeProfDimap {p} isP = TypeDimap {p} (dimap {f=p})

--------------------------------------------------
--------------------------------------------------
---- (Para-)natural transformations on `Type` ----
--------------------------------------------------
--------------------------------------------------

-- The following categories are equivalent:
--
--  1) the splice category of `Type` over `(i, j)`
--  2) the category of profunctors `i -> j`, AKA functors `(op(j), i) -> Type`,
--    where `i` and `j` are viewed as discrete categories, and the morphisms
--    are paranatural transformations
--  3) the category of diagonal elements of the profunctor di-represented by
--    `(i, j)`, i.e. `DiYoneda i j`
--  4) the category of polynomial difunctors (endo-profunctors) on
--     `(op(Type), Type)` with position-set `(j, i)` (i.e. contravariant
--     position-set `j` and covariant position-set `i`), with paranatural
--     transformations as morphisms
--
-- (I expect, but have not proven, that the category of profunctors `j -> i`
-- (AKA functors `(op(i), j) -> Type` where `i` and `j` are viewed as
-- discrete categories) with _natural_ transformations, as opposed to the
-- more general _paranatural_ transformations, as morphisms is equivalent to
-- the category of _elements_, as opposed to the category of _diagonal_
-- elements, of the profunctor _represented_, as opposed to _direpresented_, by
-- `(i, j)`, i.e. `PrePostPair i j` (the (contravariant x covariant) Yoneda
-- embedding of `(i, j)`) or `Iso i j` (the (covariant x contravariant) Yoneda
-- embedding of `(i, j`)).  I further expect that it is probably equivalent to
-- the slice category of `Type` over `(i, j)`, and to the category
-- of polynomial difunctors (endo-profunctors) on `Type` with position-set
-- `(i, j)` with _natural_ (not just paranatural) transformations as morphisms.)
--
-- This is analogous to how the following are equivalent:
--
--  1) the slice category of `Type` over `j`
--  2) the category of presheaves over `j`, AKA functors `op(j) -> Type`,
--    where `j` is viewed as a discrete category, and the morphisms
--    are natural transformations
--  3) the category of elements of the presheaf represented by `j`,
--    i.e. the contravariant Yoneda embedding of `j`
--  4) the category of Dirichlet endofunctors on `Type` with position-set `j`
--  5) the opposite of the category of polynomial endofunctors on `Type` with
--     position-set `j`
--
-- And dually:
--
--  1) the coslice category of `Type` over `i`
--  2) the category of copresheaves over `i`, AKA functors `i -> Type`,
--    where `i` is viewed as a discrete category, and the morphisms
--    are natural transformations
--  3) the category of elements of the copresheaf represented by `i`,
--    i.e. the covariant Yoneda embedding of `i`
--  4) the category of Dirichlet endofunctors on `op(Type)` with
--     position-set `i`
--  5) the opposite of the category of polynomial endofunctors on `op(Type)`
--     with position-set `i`
--
-- The splice version unifies the two duals.
--
-- Given an object in a splice category over `(i, j)`, with intermediate
-- object `k`, injection `into : i -> k`, and projection `from : k -> j`,
-- where we shall refer to the composition `from . into : i -> j` as `comp`,
-- we can form objects of other splice categories in the following ways (which
-- are functorial, so we are saying that there are the following functors
-- between splice categories):
--
--  1) Given morphisms `f : x -> i` and `g : j -> y`, we can form an object
--     of the splice category over `(x, y)` with intermediate object `k` by
--     composing `f` before `into` and `g` after `from`.  Note that
--     `(f, g)` is a morphism from `(i, j)` to `(x, y)` in `(op(Type), Type)`.
--     This is the sigma functor between splice categories.  Note that `(f, g)`
--     may equivalently be seen as `DiYoneda x y j i`, or `PrePostPair i j x y`,
--     or `Iso x y i j`.  The intermediate object is still `k`.

-- See https://arxiv.org/abs/2307.09289 .

-- `DiYonedaEmbed` is sometimes written `yy(i0, i1)` .  It embeds
-- the object `(i0, i1)` of `(op(Type), Type)` into the category
-- whose objects are profunctors `(op(Type), Type) -> Type)` and whose
-- morphisms are _paranatural_ transformations (compare to `DualYonedaEmbed`,
-- where the codomain category's objects are the same, but the morphisms are
-- the more strict _natural_ transformations).
--
-- Note that `DiYonedaEmbed Void i1` is the profunctor which ignores its
-- second argument and acts as `ContravarHomFunc i1` on its first argument,
-- whereas `DiYonedaEmbed i0 Unit` is the profunctor which ignores its first
-- argument and acts as `CovarHomFunc i0` on its second argument.  So
-- `DiYonedaEmbed Void` is effectively the contravariant Yoneda embedding
-- on `Type`, while `flip DiYonedaEmbed Unit` is effectively the covariant
-- Yoneda embedding on `Type`.

---------------------------------
---- di-Yoneda (paranatural) ----
---------------------------------

-- `Type` itself is a category internal to `Type`, so we may define the
-- diYoneda embedding of `Type` as a specialization of the internal diYoneda
-- embedding with `Type` as `obj` and `HomProf` as `mor`.
public export
DiYonedaEmbed : Type -> Type -> ProfunctorSig
DiYonedaEmbed = IntDiYonedaEmbedObj Type HomProf

public export
0 DiYonedaEmbedProf : (i, j : Type) -> Profunctor (DiYonedaEmbed i j)
DiYonedaEmbedProf i j =
  MkProfunctor $ IntDiYonedaEmbedDimap Type HomProf typeComp _ _ _ _ _ _

-- The diYoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is an object of paranatural
-- transformations.  This type is an explicit name for that object on
-- the category `(op(Type), Type)`.
public export
DiYonedaLemmaNT : ProfunctorSig -> ProfunctorSig
DiYonedaLemmaNT = IntDiYonedaLemmaNT Type HomProf

{-
 - The current usages don't work out to define this.
public export
DiYonedaLemmaNTPro : Profunctor (flip $ DiYonedaLemmaNT p)
DiYonedaLemmaNTPro {p} = MkProfunctor $
  IntDiYonedaLemmaNTDimap Type HomProf typeComp p _ _ _ _
 -}

-- One direction of the paranatural isomorphism asserted by the
-- diYoneda lemma on `(op(Type), Type)`.
public export
DiYonedaLemmaL : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfDiNT p (DiYonedaLemmaNT p)
DiYonedaLemmaL p {isP} = IntDiYonedaLemmaL Type HomProf p (TypeProfDimap isP)

-- The other direction of the paranatural isomorphism asserted by the
-- diYoneda lemma on `(op(Type), Type)`.
public export
0 DiYonedaLemmaR : (0 p : ProfunctorSig) ->
  ProfDiNT (DiYonedaLemmaNT p) p
DiYonedaLemmaR = IntDiYonedaLemmaR Type HomProf typeId

-- The di-co-Yoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is a coend (existential type).
-- This type is an explicit name for that object on the category
-- `(op(Type), Type)`.
public export
DiCoYonedaLemmaCoend : ProfunctorSig -> ProfunctorSig
DiCoYonedaLemmaCoend = IntDiCoYonedaLemmaCoendBase Type HomProf

{-
 - The current usages don't work out to define this.
public export
Profunctor (DiCoYonedaLemmaCoend p) where
  dimap {p} = IntDiYonedaLemmaCoendBaseDimap Type HomProf typeComp p _ _ _ _
 -}

-- One direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma on `(op(Type), Type)`.
public export
0 DiCoYonedaLemmaL : (0 p : ProfunctorSig) ->
  ProfDiNT p (DiCoYonedaLemmaCoend p)
DiCoYonedaLemmaL = IntDiCoYonedaLemmaL Type HomProf typeId

-- The other direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma on `(op(Type), Type)`.
public export
DiCoYonedaLemmaR : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfDiNT (DiCoYonedaLemmaCoend p) p
DiCoYonedaLemmaR p {isP} =
  IntDiCoYonedaLemmaR Type HomProf p (TypeProfDimap isP)

-----------------------------------------------
-----------------------------------------------
---- Internal Yoneda emebddings and lemmas ----
-----------------------------------------------
-----------------------------------------------

-- This is the signature of the object-map component of a (covariant)
-- copresheaf on an internal category.
public export
IntCopreshfSig : Type -> Type
IntCopreshfSig = SliceObj

-- This is the signature of the object-map component of a (contravariant)
-- presheaf on an internal category.
public export
IntPreshfSig : Type -> Type
IntPreshfSig = IntCopreshfSig

-- Suppose that `c` is a type of objects of a category internal to `Type`,
-- and `mor` is a type dependent on pairs of terms of `c` (we could also
-- express it dually as a `Type` together with morphisms `dom` and `cod` to
-- `c`), which we interpret as _some_ morphisms of the category but not
-- necessarily all.  Then this is the signature of the morphism-map component
-- of a (covariant) copresheaf on the category, as specified by whichever
-- morphisms are included in `mor`.  (The signature of the object map is
-- simply `c -> Type`.)
public export
0 IntCopreshfMapSig : (c : Type) -> (mor : IntDifunctorSig c) ->
  (objmap : IntCopreshfSig c) -> Type
IntCopreshfMapSig c mor objmap =
  (x, y : c) -> mor x y -> objmap x -> objmap y

-- As `IntCopreshfMapSig`, but for a (contravariant) presheaf.
public export
0 IntPreshfMapSig : (c : Type) -> (mor : IntDifunctorSig c) ->
  (objmap : IntPreshfSig c) -> Type
IntPreshfMapSig c mor = IntCopreshfMapSig c (IntOpCatMor c mor)

-- The signature of a natural transformation between copresheaves.
public export
0 IntCopreshfNTSig : (c : Type) -> (pobj, qobj : IntCopreshfSig c) -> Type
IntCopreshfNTSig c pobj qobj = (x : c) -> pobj x -> qobj x

-- The signature of a natural transformation between presheaves.
public export
0 IntPreshfNTSig : (c : Type) -> (pobj, qobj : IntPreshfSig c) -> Type
IntPreshfNTSig = IntCopreshfNTSig

-- The naturality condition of a natural transformation between copresheaves.
public export
0 IntCopreshfNTNaturality :
  (c : Type) -> (cmor : IntDifunctorSig c) ->
  (0 pobj, qobj : IntCopreshfSig c) ->
  IntCopreshfMapSig c cmor pobj -> IntCopreshfMapSig c cmor qobj ->
  IntCopreshfNTSig c pobj qobj -> Type
IntCopreshfNTNaturality c cmor pobj qobj pmap qmap alpha =
  (x, y : c) -> (m : cmor x y) ->
  ExtEq {a=(pobj x)} {b=(qobj y)}
    (qmap x y m . alpha x)
    (alpha y . pmap x y m)

-- The naturality condition of a natural transformation between presheaves.
public export
0 IntPreshfNTNaturality :
  (c : Type) -> (cmor : IntDifunctorSig c) ->
  (0 pobj, qobj : IntPreshfSig c) ->
  IntPreshfMapSig c cmor pobj -> IntPreshfMapSig c cmor qobj ->
  IntPreshfNTSig c pobj qobj -> Type
IntPreshfNTNaturality c cmor pobj qobj pmap qmap alpha =
  (x, y : c) -> (m : cmor y x) ->
  ExtEq {a=(pobj x)} {b=(qobj y)}
    (qmap x y m . alpha x)
    (alpha y . pmap x y m)

-- The object-map component of the (contravariant) Yoneda embedding of
-- `op(c)` into the category of the (covariant) copresheaves on `c`.
IntCopreshfYonedaEmbedObj : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  c -> (IntCopreshfSig c)
IntCopreshfYonedaEmbedObj c mor = mor

-- The object-map component of the (covariant) Yoneda embedding of
-- `c` into the category of the (contravariant) presheaves on `c`.
IntPreshfYonedaEmbedObj : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  c -> (IntPreshfSig c)
IntPreshfYonedaEmbedObj c mor = flip mor

-- The morphism-map component of the (contravariant) Yoneda embedding of
-- an object of `op(c)` into the category of the (covariant) copresheaves on `c`
-- (since the embedding of that object is a functor, it has a morphism-map
-- component as well as an object-map component).
IntCopreshfYonedaEmbedObjFMap : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (a : c) -> IntCopreshfMapSig c mor (IntCopreshfYonedaEmbedObj c mor a)
IntCopreshfYonedaEmbedObjFMap c mor comp a x y = comp a x y

-- The morphism-map component of the (covariant) Yoneda embedding of
-- an object of `c` into the category of the (contravariant) presheaves on `c`
-- (since the embedding of that object is a functor, it has a morphism-map
-- component as well as an object-map component).
IntPreshfYonedaEmbedObjFMap : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (a : c) -> IntPreshfMapSig c mor (IntPreshfYonedaEmbedObj c mor a)
IntPreshfYonedaEmbedObjFMap c mor comp a x y = flip $ comp y x a

-- The morphism-map component of the (contravariant) Yoneda embedding itself --
-- that is, the embedding of a _morphism_ into the morphisms of the
-- (covariant) copresheaves on `c`, which are natural transformations.
IntCopreshfYonedaEmbedMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (a, b : c) -> mor b a ->
  IntCopreshfNTSig c
    (IntCopreshfYonedaEmbedObj c mor a)
    (IntCopreshfYonedaEmbedObj c mor b)
IntCopreshfYonedaEmbedMor c mor comp a b mba x max = comp b a x max mba

-- The morphism-map component of the (covariant) Yoneda embedding itself --
-- that is, the embedding of a _morphism_ into the morphisms of the
-- (contravariant) presheaves on `c`, which are natural transformations.
IntPreshfYonedaEmbedMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (a, b : c) -> mor a b ->
  IntPreshfNTSig c
    (IntPreshfYonedaEmbedObj c mor a)
    (IntPreshfYonedaEmbedObj c mor b)
IntPreshfYonedaEmbedMor c mor comp a b mab x mxa = comp x a b mab mxa

-- The inverse of the morphism-map component of the (contravariant) Yoneda
-- embedding.  The existence of this inverse shows that the embedding
-- is fully faithful.
IntCopreshfYonedaEmbedMorInv : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  (cid : IntIdSig c mor) ->
  (a, b : c) ->
  IntCopreshfNTSig c
    (IntCopreshfYonedaEmbedObj c mor a)
    (IntCopreshfYonedaEmbedObj c mor b) ->
  mor b a
IntCopreshfYonedaEmbedMorInv c mor cid a b alpha = alpha a (cid a)

-- The inverse of the morphism-map component of the (covariant) Yoneda
-- embedding.  The existence of this inverse shows that the embedding
-- is fully faithful.
IntPreshfYonedaEmbedMorInv : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  (cid : IntIdSig c mor) ->
  (a, b : c) ->
  IntPreshfNTSig c
    (IntPreshfYonedaEmbedObj c mor a)
    (IntPreshfYonedaEmbedObj c mor b) ->
  mor a b
IntPreshfYonedaEmbedMorInv c mor cid a b alpha = alpha a (cid a)

------------------------------------------------
------------------------------------------------
---- (Co)presheaves over various categories ----
------------------------------------------------
------------------------------------------------

---------------------------------------------------------------
---- Over a discrete category (equivalent to `SliceObj c`) ----
---------------------------------------------------------------

public export
DiscretePreshfSig : Type -> Type
DiscretePreshfSig obj = IntPreshfSig $ DiscreteCatObj obj

public export
0 DiscretePreshfMapSig : {0 obj : Type} -> DiscretePreshfSig obj -> Type
DiscretePreshfMapSig {obj} =
  IntPreshfMapSig (DiscreteCatObj obj) (DiscreteCatMor {obj})

public export
0 DiscretePreshfNTSig : {0 obj : Type} -> (f, g : DiscretePreshfSig obj) -> Type
DiscretePreshfNTSig {obj} = IntPreshfNTSig (DiscreteCatObj obj)

public export
0 DiscretePreshfNTNaturality : {0 obj : Type} ->
  (0 f, g : DiscretePreshfSig obj) ->
  (fcm : DiscretePreshfMapSig {obj} f) ->
  (gcm : DiscretePreshfMapSig {obj} g) ->
  (alpha : DiscretePreshfNTSig {obj} f g) -> Type
DiscretePreshfNTNaturality {obj} =
  IntPreshfNTNaturality (DiscreteCatObj obj) (DiscreteCatMor {obj})

-- The category of presheaves over a discrete category with objects
-- drawn from `c` is equivalent to `SliceObj c`.
public export
DiscPreToSl : {0 obj : Type} -> DiscretePreshfSig obj -> SliceObj obj
DiscPreToSl {obj} = id

public export
DiscPreFromSl : {0 obj : Type} -> SliceObj obj -> DiscretePreshfSig obj
DiscPreFromSl {obj} = id

public export
DiscPreUniqueMapSig : {0 obj : Type} -> (0 f : DiscretePreshfSig obj) ->
  DiscretePreshfMapSig {obj} f
DiscPreUniqueMapSig f x x (DCid x) = id

public export
DiscPreNTtoSl : {0 obj : Type} ->
  (0 f, g : DiscretePreshfSig obj) -> DiscretePreshfNTSig {obj} f g ->
  SliceMorphism {a=obj} (DiscPreToSl {obj} f) (DiscPreToSl {obj} g)
DiscPreNTtoSl {obj} f g = id

public export
SlToDiscPreNT : {0 obj : Type} -> (0 x, y : SliceObj obj) ->
  SliceMorphism {a=obj} x y ->
  DiscretePreshfNTSig {obj} (DiscPreFromSl {obj} x) (DiscPreFromSl {obj} y)
SlToDiscPreNT {obj} x y = id

public export
SlToDiscPreNTnaturality : {0 obj : Type} -> (0 x, y : SliceObj obj) ->
  (f : SliceMorphism {a=obj} x y) ->
  DiscretePreshfNTNaturality {obj}
    (DiscPreFromSl {obj} x) (DiscPreFromSl {obj} y)
    (DiscPreUniqueMapSig {obj} $ DiscPreFromSl {obj} x)
    (DiscPreUniqueMapSig {obj} $ DiscPreFromSl {obj} y)
    (SlToDiscPreNT {obj} x y f)
SlToDiscPreNTnaturality {obj} x y f a a (DCid a) ex = Refl

-----------------------------------------------------------
---- Over the terminal category (equivalent to `Type`) ----
-----------------------------------------------------------

public export
TerminalPreshfSig : Type
TerminalPreshfSig = IntPreshfSig TerminalCatObj

public export
0 TerminalPreshfMapSig : TerminalPreshfSig -> Type
TerminalPreshfMapSig = IntPreshfMapSig TerminalCatObj TerminalCatMor

public export
0 TerminalPreshfNTSig : (f, g : TerminalPreshfSig) -> Type
TerminalPreshfNTSig = IntPreshfNTSig TerminalCatObj

public export
0 TerminalPreshfNTNaturality : (0 f, g : TerminalPreshfSig) ->
  (fcm : TerminalPreshfMapSig f) -> (gcm : TerminalPreshfMapSig g) ->
  (alpha : TerminalPreshfNTSig f g) -> Type
TerminalPreshfNTNaturality = IntPreshfNTNaturality TerminalCatObj TerminalCatMor

-- The category of presheaves over the terminal category is equivalent to
-- simply `Type`.
public export
TPreToType : TerminalPreshfSig -> Type
TPreToType p = p ()

public export
TPreFromType : Type -> TerminalPreshfSig
TPreFromType ty = const ty

public export
TPreUniqueMapSig : (0 x : TerminalPreshfSig) -> TerminalPreshfMapSig x
TPreUniqueMapSig x () () (DCid ()) = id

public export
TPreNTtoType : (0 f, g : TerminalPreshfSig) -> TerminalPreshfNTSig f g ->
  TPreToType f -> TPreToType g
TPreNTtoType f g alpha = alpha ()

public export
TypeToTPreNT : (0 x, y : Type) -> (x -> y) ->
  TerminalPreshfNTSig (TPreFromType x) (TPreFromType y)
TypeToTPreNT x y f () = f

public export
TypeToTPreNTnaturality : (0 x, y : Type) -> (f : x -> y) ->
  TerminalPreshfNTNaturality
    (TPreFromType x) (TPreFromType y)
    (TPreUniqueMapSig $ TPreFromType x) (TPreUniqueMapSig $ TPreFromType y)
    (TypeToTPreNT x y f)
TypeToTPreNTnaturality x y f () () (DCid ()) ex = Refl

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Impredicative encodings of universal properties of internal categories ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

IntIsInitCovar : (c : Type) -> (mor : IntDifunctorSig c) -> c -> Type
IntIsInitCovar c mor i =
  (z : c) -> mor i z

IntHasInitCovar : (c : Type) -> (mor : IntDifunctorSig c) -> Type
IntHasInitCovar c mor = (i : c ** IntIsInitCovar c mor i)

-- This follows from `IntIsInitCovar` by post-composition (of the unique
-- morphism after the given morphism).  Note that initial objects come
-- from left adjoints.
IntIsInitContra : (c : Type) -> (mor : IntDifunctorSig c) -> c -> Type
IntIsInitContra c mor i =
  (w, z : c) -> mor w i -> mor w z

-- This follows from `IntIsTermContra` by pre-composition (of the unique
-- morphism before the given morphism).  Note that terminal objects
-- come from right adjoints.
IntIsTermCovar : (c : Type) -> (mor : IntDifunctorSig c) -> c -> Type
IntIsTermCovar c mor t =
  (w, z : c) -> mor t z -> mor w z

IntIsTermContra : (c : Type) -> (mor : IntDifunctorSig c) -> c -> Type
IntIsTermContra c mor t =
  (w : c) -> mor w t

IntHasTermContra : (c : Type) -> (mor : IntDifunctorSig c) -> Type
IntHasTermContra c mor = (i : c ** IntIsTermContra c mor i)

-- Compare `ImpredCoprod`.
IntIsCoprodCovar :
  (c : Type) -> (mor : IntDifunctorSig c) -> c -> c -> c -> Type
IntIsCoprodCovar c mor x y cxy =
  (z : c) -> (mor x z, mor y z) -> mor cxy z

IntHasCoprodCovar : (c : Type) -> (mor : IntDifunctorSig c) -> c -> c -> Type
IntHasCoprodCovar c mor x y = (cxy : c ** IntIsCoprodCovar c mor x y cxy)

IntHasAllCoprodCovar : (c : Type) -> (mor : IntDifunctorSig c) -> Type
IntHasAllCoprodCovar c mor = (x, y : c) -> IntHasCoprodCovar c mor x y

-- This follows from `IntIsCoprodCovar` by post-composition (of the
-- unique morphism after the given morphisms).  Note that coproducts come
-- from left adjoints.
IntIsCoprodContra :
  (c : Type) -> (mor : IntDifunctorSig c) -> c -> c -> c -> Type
IntIsCoprodContra c mor x y cxy =
  (w, z : c) -> mor w cxy -> (mor x z, mor y z) -> mor w z

-- This follows from `IntIsProdContra` by pre-composition (of the unique
-- morphism before the given morphism).  Note that products come from
-- right adjoints.
IntIsProdCovar : (c : Type) -> (mor : IntDifunctorSig c) -> c -> c -> c -> Type
IntIsProdCovar c mor x y pxy =
  (w, z : c) -> mor pxy z -> (mor w x, mor w y) -> mor w z

-- Compare `ImpredProdPar`.
IntIsProdContra : (c : Type) -> (mor : IntDifunctorSig c) -> c -> c -> c -> Type
IntIsProdContra c mor x y pxy =
  (w : c) -> (mor w x, mor w y) -> mor w pxy

IntHasProdContra : (c : Type) -> (mor : IntDifunctorSig c) -> c -> c -> Type
IntHasProdContra c mor x y = (pxy : c ** IntIsProdContra c mor x y pxy)

IntHasAllProdContra : (c : Type) -> (mor : IntDifunctorSig c) -> Type
IntHasAllProdContra c mor = (x, y : c) -> IntHasProdContra c mor x y
