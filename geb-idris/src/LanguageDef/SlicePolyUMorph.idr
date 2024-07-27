module LanguageDef.SlicePolyUMorph

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.InternalCat
import public LanguageDef.SlicePolyCat

------------------------------------------------
------------------------------------------------
---- Limits/colimits of polynomial functors ----
------------------------------------------------
------------------------------------------------

-- Limits and colimits are right and left adjoints respectively to
-- diagonal functors, forming an adjoint triple.
--
-- The following are not limits and colimits within categories of
-- polynomial functors.  Rather, they are limits and colimits within
-- slice categories, but specifically of slice-polynomial _diagrams_
-- (recall that diagrams are simply functors).

public export
SPFDdiagF : (a, b : Type) -> SliceObj b -> SPFData a b
SPFDdiagF a b sb = SPFD sb (\_, _, _ => Void)

public export
InterpSPFDdiagF : (a, b : Type) -> SliceObj b -> SliceFunctor a b
InterpSPFDdiagF a b sb = InterpSPFData $ SPFDdiagF a b sb

public export
InterpSPFDdiagFmap : {a, b : Type} ->
  (sb : SliceObj b) -> SliceFMap (InterpSPFDdiagF a b sb)
InterpSPFDdiagFmap {a} {b} sb = InterpSPFDataMap $ SPFDdiagF a b sb

public export
SPFDdiagToSDF : {a, b : Type} -> (sb : SliceObj b) -> (sa : SliceObj a) ->
  SliceMorphism {a=b} (InterpSPFDdiagF a b sb sa) (SliceDiagF {a} {b} sb sa)
SPFDdiagToSDF {a} {b} sb sa eb = DPair.fst

public export
SPFDdiagFromSDF : {a, b : Type} -> (sb : SliceObj b) -> (sa : SliceObj a) ->
  SliceMorphism {a=b} (SliceDiagF {a} {b} sb sa) (InterpSPFDdiagF a b sb sa)
SPFDdiagFromSDF {a} {b} sb sa eb esb = (esb ** \_, v => void v)

public export
spfdDiagFmap : {a, b : Type} ->
  IntFMapSig (SliceMor b) (SPFnt {dom=a} {cod=b}) (SPFDdiagF a b)
spfdDiagFmap {a} {b} sb sb' m = SPFDm m (\_, _, _, v => void v)

public export
SPFDdiagFSig : (a, b : Type) -> IntFunctorSig (SliceCat b) (SPFDcat a b)
SPFDdiagFSig a b = IFunctor (SPFDdiagF a b) (spfdDiagFmap {a} {b})

public export
SPFDColimit : {a, b : Type} -> SPFData a b -> SliceObj b
SPFDColimit {a} {b} = SliceFColimit {a} {b} . InterpSPFData {dom=a} {cod=b}

public export
spfdColimitMap : {a, b : Type} -> (f, g : SPFData a b) ->
  SPFnt {dom=a} {cod=b} f g ->
  SliceMorphism {a=b} (SPFDColimit f) (SPFDColimit g)
spfdColimitMap {a} {b} f g alpha =
  sliceFColimitMap {a} {b}
    (InterpSPFData f)
    (InterpSPFData g)
    (InterpSPFnt f g alpha)

public export
SPFDColimitFSig : (a, b : Type) -> IntFunctorSig (SPFDcat a b) (SliceCat b)
SPFDColimitFSig a b = IFunctor (SPFDColimit {a} {b}) (spfdColimitMap {a} {b})

public export
SPFDLimit : {a, b : Type} -> SPFData a b -> SliceObj b
SPFDLimit {a} {b} = SliceFLimit {a} {b} . InterpSPFData {dom=a} {cod=b}

public export
spfdLimitMap : {a, b : Type} -> (f, g : SPFData a b) ->
  SPFnt {dom=a} {cod=b} f g ->
  SliceMorphism {a=b} (SPFDLimit f) (SPFDLimit g)
spfdLimitMap {a} {b} f g alpha =
  sliceFLimitMap {a} {b}
    (InterpSPFData f)
    (InterpSPFData g)
    (InterpSPFnt f g alpha)

public export
SPFDLimitFSig : (a, b : Type) -> IntFunctorSig (SPFDcat a b) (SliceCat b)
SPFDLimitFSig a b = IFunctor (SPFDLimit {a} {b}) (spfdLimitMap {a} {b})

public export
SPFDColimitMonad : (a, b : Type) -> SPFData a b -> SPFData a b
SPFDColimitMonad a b = IntAdjMonad {c=(SPFData a b)} {d=(SliceObj b)}
  (SPFDColimit {a} {b}) (SPFDdiagF a b)

public export
SPFDColimitComonad : (a, b : Type) -> SliceEndofunctor b
SPFDColimitComonad a b = IntAdjComonad {c=(SPFData a b)} {d=(SliceObj b)}
  (SPFDColimit {a} {b}) (SPFDdiagF a b)

public export
SPFDLimitMonad : (a, b : Type) -> SliceEndofunctor b
SPFDLimitMonad a b = IntAdjMonad {c=(SliceObj b)} {d=(SPFData a b)}
  (SPFDdiagF a b) (SPFDLimit {a} {b})

public export
SPFDLimitComonad : (a, b : Type) -> SPFData a b -> SPFData a b
SPFDLimitComonad a b = IntAdjComonad {c=(SliceObj b)} {d=(SPFData a b)}
  (SPFDdiagF a b) (SPFDLimit {a} {b})

public export
SPFDColimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SPFData a b)} {d=(SliceObj b)}
    (SPFnt {dom=a} {cod=b}) (SPFDColimit {a} {b}) (SPFDdiagF a b)
SPFDColimitUnit a b f =
  SPFDm
    (\eb, ep => (spfdDir f eb ep ** ep ** \ea, efd => efd))
    (\_, _, _, v => void v)

public export
SPFDColimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SPFData a b)} {d=(SliceObj b)}
    (SliceMor b) (SPFDColimit {a} {b}) (SPFDdiagF a b)
SPFDColimitCounit a b x eb ex = DPair.fst $ DPair.snd ex

public export
SPFDLimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SliceObj b)} {d=(SPFData a b)}
    (SliceMor b) (SPFDdiagF a b) (SPFDLimit {a} {b})
SPFDLimitUnit a b sb eb esb sa = (esb ** \_, v => void v)

public export
SPFDLimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SliceObj b)} {d=(SPFData a b)}
    (SPFnt {dom=a} {cod=b}) (SPFDdiagF a b) (SPFDLimit {a} {b})
SPFDLimitCounit a b (SPFD pos dir) =
  SPFDm
    (\eb, sa => fst $ sa $ \ea => Void)
    (\eb, ep => snd $ ep $ \ea => Void)

public export
SPFDColimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SliceCat b) (SPFDcat a b)
SPFDColimitAdjoints a b =
  IAdjoints (SPFDColimitFSig a b) (SPFDdiagFSig a b)

public export
SPFDLimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SPFDcat a b) (SliceCat b)
SPFDLimitAdjoints a b =
  IAdjoints (SPFDdiagFSig a b) (SPFDLimitFSig a b)

public export
SPFDColimitUnits : (a, b : Type) ->
  IntUnitsSig (SPFDColimitAdjoints a b)
SPFDColimitUnits a b = IUnits (SPFDColimitUnit a b) (SPFDColimitCounit a b)

public export
SPFDLimitUnits : (a, b : Type) ->
  IntUnitsSig (SPFDLimitAdjoints a b)
SPFDLimitUnits a b = IUnits (SPFDLimitUnit a b) (SPFDLimitCounit a b)

public export
SPFDColimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SliceCat b) (SPFDcat a b)
SPFDColimitAdj a b =
  IntAdjunctionFromUnits (SPFDColimitAdjoints a b) (SPFDColimitUnits a b)

public export
SPFDLimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SPFDcat a b) (SliceCat b)
SPFDLimitAdj a b =
  IntAdjunctionFromUnits (SPFDLimitAdjoints a b) (SPFDLimitUnits a b)

public export
SPFDLimitColimitTripleAdjoints : (a, b : Type) ->
  IntTripleAdjointsSig (SPFDcat a b) (SliceCat b)
SPFDLimitColimitTripleAdjoints a b =
  ITripleAdjoints
    (SPFDColimitFSig a b)
    (SPFDdiagFSig a b)
    (SPFDLimitFSig a b)

public export
SPFDLimitTripleUnitsSig : (a, b : Type) ->
  ITAUnitsSig (SPFDLimitColimitTripleAdjoints a b)
SPFDLimitTripleUnitsSig a b =
  ITUnits
    (SPFDColimitUnits a b)
    (SPFDLimitUnits a b)

public export
SPFDLimitTripleAdjunctionSig : (a, b : Type) ->
  ITASig (SPFDcat a b) (SliceCat b)
SPFDLimitTripleAdjunctionSig a b =
  ITAFromUnits
    (SPFDLimitColimitTripleAdjoints a b)
    (SPFDLimitTripleUnitsSig a b)

------------------------
------------------------
---- Representables ----
------------------------
------------------------

-- An `SPFData dom cod` whose position is `const Unit` and whose direction
-- is `const x` for some `x : SliceObj dom` is the `cod`-way product of the
-- covariant representable hom-functor of `x`.
public export
SPFDataRep : {dom : Type} -> SliceObj dom -> (cod : Type) -> SPFData dom cod
SPFDataRep {dom} x cod = SPFD (\_ => Unit) (\_, _ => x)

public export
sliceCovarHom : {dom : Type} ->
  SliceObj dom -> (cod : Type) -> SliceFunctor dom cod
sliceCovarHom {dom} x cod y ec = SliceMorphism {a=dom} x y

public export
spfdRepToHom : {dom, cod : Type} -> {x : SliceObj dom} ->
  SliceNatTrans {x=dom} {y=cod}
    (InterpSPFData {dom} {cod} $ SPFDataRep {dom} x cod)
    (sliceCovarHom {dom} x cod)
spfdRepToHom {dom} {cod} {x} y ec = snd

public export
spfdRepFromHom : {dom, cod : Type} -> {x : SliceObj dom} ->
  SliceNatTrans {x=dom} {y=cod}
    (sliceCovarHom {dom} x cod)
    (InterpSPFData {dom} {cod} $ SPFDataRep {dom} x cod)
spfdRepFromHom {dom} {cod} {x} y ec = MkDPair ()

-- The slice polynomial functor represented by the terminal object is
-- a generalization of the (non-dependent) identity in the sense that it
-- coincides with the identity when `dom` and `cod` are `Unit`.

public export
SPFDRepTerminal : (dom, cod : Type) -> SPFData dom cod
SPFDRepTerminal dom cod = SPFDataRep {dom} (SliceObjTerminal dom) cod

public export
SPFDRepTerminalToId :
  SPFnt {dom=Unit} {cod=Unit} (SPFDRepTerminal Unit Unit) (SPFDid Unit)
SPFDRepTerminalToId = SPFDm (\_ => id) (\_, _, _, _ => ())

public export
SPFDRepTerminalFromId :
  SPFnt {dom=Unit} {cod=Unit} (SPFDid Unit) (SPFDRepTerminal Unit Unit)
SPFDRepTerminalFromId = SPFDm (\_ => id) (\(), (), (), () => Refl)

---------------------
---------------------
---- Set product ----
---------------------
---------------------

-- We can take a set product _within_ a single polynomial-functor category
-- by multiplying the output of the cross-category (family) product.
public export
spfdSetProduct : {b, dom, cod : Type} ->
  (b -> SPFData dom cod) -> SPFData dom cod
spfdSetProduct {b} {dom} {cod} =
  spfdPostcompPi snd . SPFDataFamToProd {b} {dom} {cod}

public export
spfdSetProductIntro : {b, dom, cod : Type} ->
  {x : SPFData dom cod} -> {y : b -> SPFData dom cod} ->
  ((eb : b) -> SPFnt {dom} {cod} x (y eb)) ->
  SPFnt {dom} {cod} x (spfdSetProduct {b} {dom} {cod} y)
spfdSetProductIntro {b} {dom} {cod} {x} {y} ntf =
  SPFDm
    (\ec, ep =>
      (() **
       \ebc, eceq => case ebc of
        (eb, ec') => case eceq of Refl => spOnPos (ntf eb) ec ep))
    (\ec, ep, ed, ebdm => case ebdm of
      (((eb, ec') ** eceq) ** dm) =>
        case eceq of Refl => spOnDir (ntf eb) ec ep ed dm)

public export
spfdSetProductProj : {b, dom, cod : Type} ->
  (sf : b -> SPFData dom cod) -> (eb : b) ->
  SPFnt {dom} {cod} (spfdSetProduct {b} {dom} {cod} sf) (sf eb)
spfdSetProductProj {b} {dom} {cod} sf eb =
  SPFDm
    (\ec, ebc => snd ebc (eb, ec) Refl)
    (\ec, dm, ed, efd => (((eb, ec) ** Refl) ** efd))

-----------------------
-----------------------
---- Set coproduct ----
-----------------------
-----------------------

-- We can take a set coproduct _within_ a single polynomial-functor category
-- by summing the output of the cross-category (family) product.
public export
spfdSetCoproduct : {b, dom, cod : Type} ->
  (b -> SPFData dom cod) -> SPFData dom cod
spfdSetCoproduct {b} {dom} {cod} =
  spfdPostcompSigma snd . SPFDataFamToProd {b} {dom} {cod}

public export
spfdSetCoproductInj : {b, dom, cod : Type} ->
  (sf : b -> SPFData dom cod) -> (eb : b) ->
  SPFnt {dom} {cod} (sf eb) (spfdSetCoproduct {b} {dom} {cod} sf)
spfdSetCoproductInj {b} {dom} {cod} sf eb =
  SPFDm
    (\ec, ep =>
      (SFS (eb, ec) () **
       \ebc, eceq => case ebc of (eb, ec') => case eceq of Refl => ep))
    (\ec, ep, ed, ebcd => case ebcd of
      (((eb, ec) ** Refl) ** efd) => efd)

public export
spfdSetCoproductElim : {b, dom, cod : Type} ->
  {x : b -> SPFData dom cod} -> {y : SPFData dom cod} ->
  ((eb : b) -> SPFnt {dom} {cod} (x eb) y) ->
  SPFnt {dom} {cod} (spfdSetCoproduct {b} {dom} {cod} x) y
spfdSetCoproductElim {b} {dom} {cod} {x} {y} ntf =
  SPFDm
    (\ec, ep => case ep of
      (SFS (eb, ec) () ** epm) => spOnPos (ntf eb) ec $ epm (eb, ec) Refl)
    (\ec, ep, ed, efd => case ep of
      (SFS (eb, ec) () ** epm) =>
        (((eb, ec) ** Refl) ** spOnDir (ntf eb) ec (epm (eb, ec) Refl) ed efd))

-------------------------
-------------------------
---- Terminal object ----
-------------------------
-------------------------

-- A zero-way product is a terminal object.
public export
spfdTerminal : (dom, cod : Type) -> SPFData dom cod
spfdTerminal dom cod = spfdSetProduct {b=Void} {dom} {cod} $ \v => void v

public export
spfdToTerminal : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFnt {dom} {cod} spfd (spfdTerminal dom cod)
spfdToTerminal {dom} {cod} spfd =
  spfdSetProductIntro {b=Void} {dom} {cod} {x=spfd} {y=(\v => void v)} $
    \v => void v

------------------------
------------------------
---- Initial object ----
------------------------
------------------------

-- A zero-way coproduct is an initial object.
public export
spfdInitial : (dom, cod : Type) -> SPFData dom cod
spfdInitial dom cod = spfdSetCoproduct {b=Void} {dom} {cod} $ \v => void v

public export
spfdFromInitial : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFnt {dom} {cod} (spfdInitial dom cod) spfd
spfdFromInitial {dom} {cod} spfd =
  spfdSetCoproductElim {b=Void} {dom} {cod} {x=(\v => void v)} {y=spfd} $
    \v => void v

-------------------------
-------------------------
---- Binary products ----
-------------------------
-------------------------

-- A binary product is a set product indexed by a type of cardinality two.

public export
spfdProduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdProduct {dom} {cod} x y =
  spfdSetProduct {b=(Fin 2)} {dom} {cod} $ flip index [x, y]

public export
spfdProductIntro : {dom, cod : Type} ->
  {x, y, z : SPFData dom cod} ->
  SPFnt {dom} {cod} x y ->
  SPFnt {dom} {cod} x z ->
  SPFnt {dom} {cod} x (spfdProduct {dom} {cod} y z)
spfdProductIntro {dom} {cod} {x} {y} f g =
  spfdSetProductIntro {b=(Fin 2)} {dom} {cod} {x} {y=(flip index [y, z])} $
    \i => case i of FZ => f ; FS FZ => g

public export
spfdProductProj1 : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} x y) x
spfdProductProj1 {dom} {cod} x y =
  spfdSetProductProj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) FZ

public export
spfdProductProj2 : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} x y) y
spfdProductProj2 {dom} {cod} x y =
  spfdSetProductProj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) (FS FZ)

---------------------------
---------------------------
---- Binary coproducts ----
---------------------------
---------------------------

-- A binary coproduct is a set coproduct indexed by a type of cardinality two.

public export
spfdCoproduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdCoproduct {dom} {cod} x y =
  spfdSetCoproduct {b=(Fin 2)} {dom} {cod} $ flip index [x, y]

public export
spfdCoproductInjL : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} x (spfdCoproduct {dom} {cod} x y)
spfdCoproductInjL {dom} {cod} x y =
  spfdSetCoproductInj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) FZ

public export
spfdCoproductInjR : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} y (spfdCoproduct {dom} {cod} x y)
spfdCoproductInjR {dom} {cod} x y =
  spfdSetCoproductInj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) (FS FZ)

public export
spfdCoproductElim : {dom, cod : Type} ->
  {x, y, z : SPFData dom cod} ->
  SPFnt {dom} {cod} x z ->
  SPFnt {dom} {cod} y z ->
  SPFnt {dom} {cod} (spfdCoproduct {dom} {cod} x y) z
spfdCoproductElim {dom} {cod} {x} {y} f g =
  spfdSetCoproductElim {b=(Fin 2)} {dom} {cod} {x=(flip index [x, y])} {y=z} $
    \i => case i of FZ => f ; FS FZ => g

------------------------------------------------
------------------------------------------------
---- Universal slice polynomial 2-morphisms ----
------------------------------------------------
------------------------------------------------

-- Here we define universal objects in the category of all slice
-- polynomial functors, where the universal morphisms are
-- 2-morphisms, also known as cells.
--
-- Note that a universal object in the category of slice polynomial
-- functors between some fixed domain and codomain slice categories
-- is a special case of a universal object in the category of all
-- slice polynomial functors, where the vertical sides of the cell
-- are both identities.
